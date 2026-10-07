/-
`:::premises (claims := "A B …")` — a plain-words list of the premises of
some claims, checked against the claims' statements.

A hand-written summary of a claim's premises can drop one silently: a claim
gains a premise, and the summary still reads well. This block makes that a
build failure. It reads the named premises of each claim from the compiled
development and fails when one of them is not mentioned by a `{decl}` inside
the block, so every named premise has a line that links to it.

**What counts as a named premise.** A constant of this development at the
head of one of the claim's explicit hypotheses, read from its statement: a
hypothesis of the theorem, a non-dependent antecedent of its conclusion, or a
parameter
whose type is a structure or class carrying conditions (a field that is a
proposition) — a schedule, a contract instance. The walk unfolds a
`…Claim` definition of this development the theorem is stated as, so the
premises of the claim's own statement count, and stops at the conclusion.

**What it does not see.** A hypothesis whose head is not a constant of this
development (an equation such as `TA.Δ = sch.Δ`, an existential, a bound on
a count) is not named, so it is not checked; the list states such premises
in words, and its link to the premise ledger is the reference. Hypotheses a
claim takes as type-class instances (`[Archimedean time]`) are not checked
either.

The block renders its contents as they are.

    :::premises (claims := "Composed.liveness Composed.censorship")
    * …, {decl}`Composed.SysSync` …
    :::
-/
import VersoManual
import CadenceGuide.Audit

open Lean Elab Meta
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

/-- Is `c` a constant of this development? -/
def isOwnConst (env : Environment) (c : Name) : Bool :=
  (moduleOf env c).any isOwnModule

/-- Does the structure or class `c` carry a condition, a field that is a
proposition? -/
def carriesConditions (c : Name) : MetaM Bool := do
  let env ← getEnv
  unless isStructure env c do return false
  for f in getStructureFieldsFlattened env c (includeSubobjectFields := false) do
    let some decl := findField? env c f | continue
    if ← isPropertyField' (decl ++ f) then return true
  return false
where
  isPropertyField' (proj : Name) : MetaM Bool := do
    let ci ← getConstInfo proj
    forallTelescope ci.type fun _ body => isProp body

/-- The named premises of a claim's statement `e`: the heads of its
hypotheses that are constants of this development, unfolding a `…Claim`
definition of this development at the head of the conclusion. -/
partial def namedPremises (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let e := e.consumeMData
  match e with
  | .forallE n t b bi =>
    let mut acc := #[]
    if let some c := headSymbol t then
      if bi.isExplicit && isOwnConst env c then
        if !b.hasLooseBVars || (← isProp t) then
          acc := acc.push c
        else if ← carriesConditions c then
          acc := acc.push c
    withLocalDecl n bi t fun x => return acc ++ (← namedPremises (b.instantiate1 x))
  | _ =>
    match e.getAppFn.constName? with
    | some c =>
      if isOwnConst env c && c.toString.endsWith "Claim" then
        match ← unfoldDefinition? e with
        | some e' => namedPremises (← whnfCore e')
        | none => return #[]
      else return #[]
    | none => return #[]

/-- The declarations a `{decl}` names in a piece of guide source. -/
def declMentions (src : String) : Array Name := Id.run do
  let mut out := #[]
  for chunk in (src.splitOn "{decl}`").drop 1 do
    match chunk.splitOn "`" with
    | n :: _ => out := out.push n.trimAscii.toString.toName
    | [] => pure ()
  return out

structure PremisesConfig where
  claims : String

instance : FromArgs PremisesConfig DocElabM :=
  ⟨PremisesConfig.mk <$> .named `claims .string false⟩

/-- `:::premises (claims := "…")` — its contents, checked to mention every
named premise of the listed claims by a `{decl}`. -/
@[directive premises]
def premises : DirectiveExpanderOf PremisesConfig
  | ⟨claims⟩, contents => do
    let fm ← getFileMap
    let src := String.join <| contents.toList.filterMap fun stx => do
      let r ← stx.raw.getRange?
      pure (String.Pos.Raw.extract fm.source r.start r.stop)
    let mentioned := declMentions src
    let mut missing : Array (Name × Name) := #[]
    for c in (claims.splitOn " ").filter (· != "") do
      let some ci := (← getEnv).find? c.toName
        | throwError "premises: {c} is not a declaration"
      let ps ← namedPremises ci.type
      for p in ps.toList.eraseDups do
        unless mentioned.contains p do missing := missing.push (c.toName, p)
    unless missing.isEmpty do
      throwError "premises: the list names no {"{"}decl} for these premises, so a \
        reader of it would not learn of them: {missing.toList.map fun (c, p) => s!"{p} (of {c})"}"
    ``(Verso.Doc.Block.concat #[$[$(← contents.mapM elabBlock)],*])

end CadenceGuide
