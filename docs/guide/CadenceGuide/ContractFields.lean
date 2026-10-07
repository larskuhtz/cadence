/-
`{contractFields C}` — the checklist of one contract: a row per field of the
class `C`, with what the field says, its level, and what proves it.

Every cell is read from the compiled development, so the table is the
contract as Lean has it:

* **Field** — the field's name.
* **Says** — the first sentence of the field's docstring.
* **Level** — *safety fragment* for a field of a `…Safety` class, which the
  models consume and the solver sees; *temporal* for every other level.
* **Proven by** — the declarations that provide the class the field is
  declared in, as `{contracts}` finds them ([Audit.lean](Audit.lean)): a
  protocol model, or, for an assumed module, *assumed*, with the consistency
  witnesses that show it can be met. For an operation rather than a property
  the column says which instance defines it.

The table fails the build when it would mislead:

* a field has no docstring, so the table would have a row it cannot explain;
* a field has no protocol instance and its class is not one of the assumed
  contracts (`assumedContracts`, in [Audit.lean](Audit.lean)), so the
  development leaves an obligation open that the guide does not call an
  assumption;
* a module on the witness list (`witnessModules`, the same list
  `{contracts}` and the trust boundary use) is gone, so the list would
  classify nothing.

The transition-system skeleton every contract extends
(`TransitionSystemSafety`: `init`, `step`, `trans`, `reachable` and their
closure facts) is shared by all four and is left out of each table; the
caption says so.
-/
import VersoManual
import CadenceGuide.Audit

open Lean Elab Meta
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

/-- Structures every contract extends, which no single contract's checklist
repeats. -/
def contractSkeleton : List Name := [`TransitionSystemSafety, `FaultModel]

/-- The first sentence of a docstring, on one line. -/
def firstSentence (doc : String) : String := Id.run do
  let flat := " ".intercalate ((doc.splitOn "\n").map (·.trimAscii.toString) |>.filter (· != ""))
  -- The first paragraph only.
  let para := ((doc.splitOn "\n\n").head!.splitOn "\n").map (·.trimAscii.toString)
    |>.filter (· != "") |> " ".intercalate
  let text := if para.isEmpty then flat else para
  match text.splitOn ". " with
  | first :: _ :: _ => first ++ "."
  | _ => text

/-- The inline Markdown of a docstring sentence as HTML: code spans and
bold. A link keeps its text and drops its target, which is written relative
to the file the docstring is in. -/
partial def inlineMarkdown (s : String) : String :=
  let chars := s.toList
  go chars "" false false
where
  go : List Char → String → Bool → Bool → String
    | [], acc, _, _ => acc
    | '`' :: rest, acc, inCode, bold =>
      go rest (acc ++ if inCode then "</code>" else "<code>") (!inCode) bold
    | '*' :: '*' :: rest, acc, false, bold =>
      go rest (acc ++ if bold then "</strong>" else "<strong>") false (!bold)
    | '[' :: rest, acc, false, bold =>
      -- `[text](target)` → text
      let text := rest.takeWhile (· != ']')
      let after := rest.drop (text.length + 1)
      match after with
      | '(' :: tail =>
        let target := tail.takeWhile (· != ')')
        if tail.length > target.length then
          go (tail.drop (target.length + 1)) (acc ++ esc (String.ofList text)) false bold
        else go rest (acc ++ "[") false bold
      | _ => go rest (acc ++ "[") false bold
    | c :: rest, acc, inCode, bold => go rest (acc ++ esc c.toString) inCode bold

/-- Does every witness module still exist? A module that is gone would leave
the list classifying nothing, silently. -/
def checkWitnessModules (env : Environment) : Except String Unit := do
  let mods := env.header.moduleNames
  for w in witnessModules do
    unless mods.any (w.isPrefixOf ·) do
      throw s!"the witness module {w} (witnessModules, Audit.lean) is not in the development"

/-- Is the field's type a property (a proposition) rather than an operation? -/
def isPropertyField (proj : Name) : MetaM Bool := do
  let ci ← getConstInfo proj
  forallTelescope ci.type fun _ body => isProp body

/-- What proves (or defines) the class `decl`, as HTML; `none` when nothing
does and the class is not an assumed contract. -/
def provenByHtml (env : Environment) (a : Anchors) (decl : Name) (property : Bool) :
    Option String :=
  let provs := providersOf env decl
  let real := provs.filter (!·.witness)
  let wits := provs.filter (·.witness)
  let verb := if property then "" else "defined by "
  let link (p : Provider) :=
    declLinkHtml env a p.name ++
      (if p.requires.isEmpty then ""
       else " — given " ++ ", ".intercalate (p.requires.map (s!"<code>{esc ·.toString}</code>")))
  if !real.isEmpty then
    some (verb ++ ", ".intercalate (real.toList.map link))
  else if assumedContracts.contains decl then
    let w := if wits.isEmpty then "" else
      "; consistency witness: " ++ ", ".intercalate (wits.toList.map (declLinkHtml env a ·.name))
    some ("<span class=\"cg-assumed\">assumed</span>" ++ w)
  else none

structure ContractFieldsConfig where
  cls : Ident

instance : FromArgs ContractFieldsConfig DocElabM :=
  ⟨ContractFieldsConfig.mk <$> .positional `cls .ident⟩

/-- `{contractFields C}` — the checklist of contract class `C`, one row per
field, computed from the environment. -/
@[block_command]
def contractFields : BlockCommandOf ContractFieldsConfig
  | ⟨clsId⟩ => do
    let cls ← realizeGlobalConstNoOverloadWithInfo clsId
    let env ← getEnv
    unless isStructure env cls do throwErrorAt clsId "{cls} is not a class"
    if let .error e := checkWitnessModules env then throwErrorAt clsId e
    let a ← loadAnchors
    let mut rows := #[]
    let mut undocumented := #[]
    let mut unproven := #[]
    for f in getStructureFieldsFlattened env cls (includeSubobjectFields := false) do
      let some decl := findField? env cls f | continue
      if contractSkeleton.contains decl then continue
      let proj := decl ++ f
      let some doc ← findDocString? env proj
        | undocumented := undocumented.push proj; continue
      let property ← isPropertyField proj
      let some proven := provenByHtml env a decl property
        | unproven := unproven.push proj; continue
      let level := if decl.toString.endsWith "Safety" then "safety fragment" else "temporal"
      rows := rows.push s!"<tr><td>{declLinkHtml env a proj}</td>\
        <td>{inlineMarkdown (firstSentence doc)}</td><td>{level}</td><td>{proven}</td></tr>"
    unless undocumented.isEmpty do
      throwErrorAt clsId "{undocumented.size} field(s) of {cls} have no docstring, so the \
        checklist cannot say what they ask for: {undocumented.toList}"
    unless unproven.isEmpty do
      throwErrorAt clsId "no instance provides {unproven.toList}, and the class declaring \
        them is not an assumed contract (assumedContracts, Audit.lean)"
    let caption := s!"<caption>{declLinkHtml env a cls}, field by field. The \
      transition-system skeleton every contract extends, {declLinkHtml env a `TransitionSystemSafety},
      is left out.</caption>"
    let html := s!"<table class=\"cg-contracts cg-fields\">{caption}<thead><tr><th>Field</th>\
      <th>Says</th><th>Level</th><th>Proven by</th></tr></thead>\
      <tbody>{String.join rows.toList}</tbody></table>"
    ``(Verso.Doc.Block.other (CadenceGuide.Block.status $(quote html)) #[])

end CadenceGuide
