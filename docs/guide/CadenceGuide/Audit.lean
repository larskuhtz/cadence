/-
The guide's three project-specific elements. Each one puts a *derived* fact
on the page where the prose would otherwise have to assert it, so the guide
stays a text with no facts of its own.

* `{decl}` — a declaration name, resolved against the compiled development,
  linked to the declaration in the rendered sources.
* `{claim X}` — a theorem or instance as an auditor meets it: the real
  statement, and a status box computed from the environment — the kernel's
  axiom footprint (the build fails on anything beyond Lean's three standard
  axioms), which module contracts the result is *conditional on*, and which
  declarations of this development discharge each of them.
* `{model M "safety [x]"}` — a declaration of a Veil model, quoted from the
  rendered sources rather than retyped. Veil's `safety`, `action` and
  `relation` are not Lean declarations, so no name-based mechanism reaches
  them; the literate renderer's JSON does, and it is the same highlighted
  code the sources pages show. A declaration that disappears or is renamed
  fails this build.

Deliberately small and specific to this project: the classification below
knows this development's contract classes by name, which is the point — it is
the vocabulary an auditor is asked to check.
-/
import VersoManual
import VersoLiterate

open Lean Elab Meta
open Verso Doc Elab ArgParse
open Verso.Genre Manual
open SubVerso.Highlighting

namespace CadenceGuide

/-! ## Where things are -/

/-- The rendered sources, relative to the guide's own page. `scripts/docs.sh`
places the guide at `site/guide/` and the sources at `site/sources/`. -/
def sourcesRoot : String := "../sources/"

/-- The literate renderer's intermediate JSON, one file per module, written by
stage 2 of `scripts/docs.sh`. Relative to the project root, which is where
lake elaborates this library. -/
def literateJsonDir : System.FilePath := ".lake/build/literate/json"

def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

/-- The module a declaration was introduced in. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- The literate page of a module: `Cadence.Chorus.Compose` is rendered at
`sources/Cadence/Chorus/Compose/`. -/
def moduleUrl (m : Name) : String :=
  sourcesRoot ++ String.intercalate "/" (m.components.map toString) ++ "/"

/-- Does `n` have syntax of its own in a source file? Declarations that a
Veil command generates (`#gen_composition`'s `reachable_*` projections,
`invariants_of_reachable`) do not: they carry no declaration range, and the
rendered page has nothing to anchor them to. -/
def hasSource (env : Environment) (n : Name) : Bool :=
  (declRangeExt.find? env n).isSome

/-- The rendered sources give every declaration written in the source the id
`(toString name).sluggify`, so a link can be computed rather than stored. A
generated declaration links to its module's page. -/
def declUrl (env : Environment) (n : Name) : Option String :=
  (moduleOf env n).map fun m =>
    if hasSource env n then moduleUrl m ++ "#" ++ toString (toString n).sluggify
    else moduleUrl m

def declLinkHtml (env : Environment) (n : Name) : String :=
  let gen := if hasSource env n then "" else " <span class=\"cg-note\">(generated)</span>"
  match declUrl env n with
  | some u => s!"<a href=\"{u}\"><code>{esc n.toString}</code></a>{gen}"
  | none => s!"<code>{esc n.toString}</code>"

/-! ## The vocabulary: contracts and primitives -/

/-- The module contracts. The `…Safety` classes are the first-order fragment
that the models consume and the implementations prove; the `…Temporal`
classes carry the timing and liveness obligations. -/
def contractClasses : List Name :=
  [`SlotConsensusSafety, `SlotConsensusTemporal,
   `OrchestratorSafety, `OrchestratorTemporal,
   `MVBASafety, `MVBATemporal,
   `ACSSafety, `ACSTemporal]

/-- Classes stating an assumption about the environment rather than a
protocol property: the cryptographic primitives. -/
def primitiveModules : List Name := [`Cadence.Primitives]

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def isOwnModule (m : Name) : Bool := m == `Cadence || (`Cadence).isPrefixOf m

/-- Head constant of a type after stripping `∀` binders syntactically — no
`whnf`, which over proof-sized types overruns the heartbeat budget. -/
partial def headSymbol : Expr → Option Name
  | .forallE _ _ b _ => headSymbol b
  | e => e.getAppFn.constName?

/-- The classes of a type's instance-implicit binders, in order. -/
partial def instBinderClasses : Expr → List Name
  | .forallE _ t b bi =>
    let rest := instBinderClasses b
    if bi.isInstImplicit then
      match headSymbol t with | some c => c :: rest | none => rest
    else rest
  | _ => []

/-- The classes any binder of a type (instance or explicit) has at its head. -/
partial def binderHeads : Expr → List Name
  | .forallE _ t b _ => (headSymbol t).toList ++ binderHeads b
  | _ => []

/-- A declaration of this development producing a contract, with the
contracts it needs in order to do so. Parent projections (`X.toXSafety`)
are skipped: their type has the class at the head for *any* `X`, so they
witness nothing. -/
structure Provider where
  name : Name
  requires : List Name

def providersOf (env : Environment) (cls : Name) : Array Provider := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail then continue
    if (env.getProjectionFnInfo? n).isSome then continue
    let some m := moduleOf env n | continue
    unless isOwnModule m do continue
    unless ci matches .defnInfo _ | .thmInfo _ | .opaqueInfo _ do continue
    if headSymbol ci.type == some cls then
      let reqs := (binderHeads ci.type).filter contractClasses.contains |>.eraseDups
      out := out.push ⟨n, reqs⟩
  return out.qsort (·.name.toString < ·.name.toString)

/-! ## `{decl}` -/

/-- `{decl}`X`` — a checked declaration name linking into the sources. -/
@[role]
def decl : RoleExpanderOf Unit
  | (), inls => do
    let some s ← oneCodeStr? inls | `(Verso.Doc.Inline.empty)
    let n ← realizeGlobalConstNoOverloadWithInfo (mkIdentFrom s s.getString.toName)
    let some url := declUrl (← getEnv) n
      | throwErrorAt s "{n} is not from a compiled module, so it has no source page"
    ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.code $(quote n.toString)] $(quote url))

/-! ## `{claim X}` -/

block_extension Block.status (html : String) where
  data := .str html
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .str h := data | reportError "status: expected a string" *> pure .empty
      pure (Verso.Output.Html.text false h)
  toTeX := none
  extraCss := [r#"
.cg-status { margin: 0.4rem 0 1.6rem; padding: 0.6rem 0.9rem;
  border-left: 3px solid var(--cg-ok, #1a7f37); background: var(--cg-bg, #f6f8fa);
  font-size: 0.93em; }
.cg-status.cg-conditional { border-left-color: var(--cg-cond, #9a6700); }
.cg-status dl { margin: 0; display: grid; grid-template-columns: max-content 1fr;
  gap: 0.25rem 1rem; }
.cg-status dt { font-weight: 600; }
.cg-status dd { margin: 0; }
.cg-status ul { margin: 0; padding-left: 1.1rem; }
.cg-status .cg-assumed { color: var(--cg-bad, #b3261e); font-weight: 600; }
.cg-note { color: #57606a; font-size: 0.92em; }
.cg-status.cg-plain { border-left-color: var(--cg-rule, #d0d7de); }
.cg-contracts { border-collapse: collapse; margin: 0.8rem 0 1.6rem; font-size: 0.93em; }
.cg-contracts th, .cg-contracts td { text-align: left; padding: 0.35rem 0.7rem;
  border-bottom: 1px solid #8884; vertical-align: top; }
.cg-contracts .cg-assumed { color: var(--cg-bad, #b3261e); font-weight: 600; }
.cg-details { margin: 0 0 1.6rem; }
.cg-details > summary { cursor: pointer; font-size: 0.93em; color: #57606a; }
.cg-prose { margin: 0.8rem 0 0.4rem; }
"#]

structure ClaimConfig where
  name : Ident × Name

instance : FromArgs ClaimConfig DocElabM := ⟨ClaimConfig.mk <$> .positional `name .documentableName⟩

/-- What a contract hypothesis is discharged by, as HTML. -/
def dischargeHtml (env : Environment) (cls : Name) : String :=
  let provs := providersOf env cls
  let direct := provs.filter (·.requires.isEmpty)
  let joins := provs.filter (!·.requires.isEmpty)
  if !direct.isEmpty then
    "discharged by " ++ ", ".intercalate (direct.toList.map (declLinkHtml env ·.name))
  else if !joins.isEmpty then
    "discharged by " ++ ", ".intercalate (joins.toList.map fun p =>
      declLinkHtml env p.name ++ " — given " ++
        ", ".intercalate (p.requires.map (s!"<code>{esc ·.toString}</code>")))
  else "<span class=\"cg-assumed\">no instance in this development — assumed</span>"

def statusHtml (name : Name) (lead : Array String := #[]) (showSource := true) : DocElabM (String × Bool) := do
  let env ← getEnv
  let ci ← getConstInfo name
  let axs ← collectAxioms name
  let extra := axs.filter (!standardAxioms.contains ·)
  unless extra.isEmpty do
    throwError m!"{name} depends on {extra.toList} beyond Lean's three standard axioms"
  let axHtml := ", ".intercalate (axs.toList.map (s!"<code>{esc ·.toString}</code>"))
  let insts := (instBinderClasses ci.type).eraseDups
  let contracts := insts.filter contractClasses.contains
  let prims := insts.filter fun c => (moduleOf env c).any primitiveModules.contains
  let provides := (headSymbol ci.type).filter contractClasses.contains
  let mut rows : Array String := lead
  rows := rows.push s!"<dt>Checked</dt><dd>by Lean's kernel; axioms {axHtml}</dd>"
  if let some c := provides then
    rows := rows.push s!"<dt>Provides</dt><dd>an instance of {declLinkHtml env c}</dd>"
  if contracts.isEmpty then
    rows := rows.push "<dt>Contracts</dt><dd>none assumed — no contract hypothesis</dd>"
  else
    let items := contracts.map fun c => s!"<li>{declLinkHtml env c} — {dischargeHtml env c}</li>"
    rows := rows.push s!"<dt>Conditional on</dt><dd><ul>{String.join items}</ul></dd>"
  unless prims.isEmpty do
    let items := prims.map fun c => s!"<li>{declLinkHtml env c}</li>"
    rows := rows.push s!"<dt>Primitives</dt><dd><ul>{String.join items}</ul></dd>"
  if showSource then if let some u := declUrl env name then
    rows := rows.push s!"<dt>Source</dt><dd><a href=\"{u}\">{esc ((moduleOf env name).map toString |>.getD "")}</a></dd>"
  let cls := if contracts.isEmpty then "cg-status" else "cg-status cg-conditional"
  return (s!"<div class=\"{cls}\"><dl>{String.join rows.toList}</dl></div>", !contracts.isEmpty)

block_extension Block.details (summary : String) where
  data := .str summary
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ data contents => do
      let .str summ := data | reportError "details: expected a string" *> pure .empty
      pure {{<details class="cg-details"><summary>{{summ}}</summary>{{← contents.mapM goB}}</details>}}
  toTeX := none

/-- `{claim X}` — `X` as an auditor meets it: its docstring (what the author
says it means), the derived status box, and the formal statement as the
kernel checked it, collapsed — the signatures of this development's end
results carry every type parameter and instance binder, which is the
generality that makes them strong and the noise that hides the prose.
The signature is the ground truth; the prose is a claim about it. -/
@[block_command]
def claim : BlockCommandOf ClaimConfig
  | ⟨(x, name)⟩ => do
    let prose ← Verso.Genre.Manual.includeDocstring { name, elaborate := true }
    let declType ← Verso.Genre.Manual.Block.Docstring.DeclType.ofName name
    let signature ← Verso.Genre.Manual.Signature.forName name
    let sig ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature) none #[]) #[])
    let (html, _) ← statusHtml name
    Doc.PointOfInterest.save x name.toString (detail? := some "Claim")
    ``(Verso.Doc.Block.concat #[$prose,
        Verso.Doc.Block.other (CadenceGuide.Block.status $(quote html)) #[],
        Verso.Doc.Block.other (CadenceGuide.Block.details "The formal statement, as the kernel checked it") #[$sig]])

/-! ## `{model M "header"}` -/

structure ModelConfig where
  module : Ident
  header : String
  /-- The lemma that proves this declaration, if it is a property. -/
  proven : Option Ident

instance : FromArgs ModelConfig DocElabM :=
  ⟨ModelConfig.mk <$> .positional `module .ident <*> .positional `header .string
    <*> .named `proven .ident true⟩

/-- A module's items, as the literate renderer recorded them. -/
def loadItems (mod : Name) : DocElabM (Array VersoLiterate.ModuleItem') := do
  let path := (mod.components.foldl (init := literateJsonDir) (· / toString ·)).addExtension "json"
  unless ← path.pathExists do
    throwError "{path} is missing: the guide quotes models from the rendered sources, so \
      run `scripts/docs.sh` (its stage 2 writes these files) before building the guide"
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let exported : VersoLiterate.ExportedModuleItems ←
    IO.ofExcept <| fromJson? (json.getObjValD "items")
  IO.ofExcept exported.toModuleItems

/-- The text of an item's code, and its highlighted parts. -/
def itemHighlighted (item : VersoLiterate.ModuleItem') : Array Highlighted :=
  item.code.filterMap fun | .highlighted hl => some hl | _ => none

/-- `{model M "safety [x]"}` — the declaration of module `M` whose source
begins with the given text, quoted as highlighted code. -/
@[block_command]
def model : BlockCommandOf ModelConfig
  | ⟨modId, header, proven⟩ => do
    let mod := modId.getId
    let items ← loadItems mod
    let hits := items.filter fun item =>
      (itemHighlighted item).any fun hl =>
        (hl.toString.splitOn "\n").any (·.trimAsciiStart.startsWith header)
    let #[item] := hits
      | throwErrorAt modId "{hits.size} declarations of {mod} begin with `{header}`; expected one"
    let hl := Highlighted.seq (itemHighlighted item)
    let range := match item.range with
      | some (s, e) => s!"lines {s.line}–{e.line}"
      | none => ""
    let cfg : Verso.Code.External.CodeConfig := { showProofStates := false, defSite := some false }
    let file := "/".intercalate (mod.components.map toString) ++ ".lean"
    let stated := s!"<dt>Stated in</dt><dd><code>{esc file}</code>, {range} — \
      <a href=\"{moduleUrl mod}\">in context</a></dd>"
    let html ← match proven with
      | none => pure s!"<div class=\"cg-status cg-plain\"><dl>{stated}</dl></div>"
      | some p => do
        let n ← realizeGlobalConstNoOverloadWithInfo p
        let row := s!"<dt>Proven as</dt><dd>{declLinkHtml (← getEnv) n}</dd>"
        pure (← statusHtml n #[stated, row] (showSource := false)).1
    ``(Verso.Doc.Block.concat #[
        Verso.Doc.Block.other (Verso.Genre.Manual.Block.lean $(quote hl) $(quote cfg)) #[],
        Verso.Doc.Block.other (CadenceGuide.Block.status $(quote html)) #[]])

/-! ## `{contracts}` -/

/-- `{contracts}` — every module contract, with what provides it. Computed
from the environment: a contract with no providing declaration is exactly an
assumption this development leaves open. -/
@[block_command]
def contracts : BlockCommandOf Unit
  | () => do
    let env ← getEnv
    let rows := contractClasses.filter env.contains |>.map fun c =>
      s!"<tr><td>{declLinkHtml env c}</td><td>{dischargeHtml env c}</td></tr>"
    let html := s!"<table class=\"cg-contracts\"><thead><tr><th>Contract</th>\
      <th>Provided by</th></tr></thead><tbody>{String.join rows}</tbody></table>"
    ``(Verso.Doc.Block.other (CadenceGuide.Block.status $(quote html)) #[])

end CadenceGuide
