/-
`{auditTable M "docs/guide/audit/M.tsv"}` — a model's audit table: one row
per action, saying who acts and what the action reads and writes, in the
state categories of [ChorusDesign.md](../../ChorusDesign.md) §3.5.

The rows are a data file, whose format [Documentation.md](../../Documentation.md)
§ "The guide" documents. The table is checked against the compiled model
while the chapter elaborates, and fails the build when it no longer
describes it:

* an action named in the file is not a constructor of the model's label
  type `M.Label`, or one of those constructors has no row (unless the table
  is marked `+sample`), or an action has two rows;
* a relation named in one of the derived columns is not part of the model:
  the first identifier of every code span there must be a state component
  (`M.State`), an immutable one (`M.Theory`), a declaration of the model
  (a ghost relation, `M.x`), or a field of a class the model instantiates
  (`is_byz`, from `ByzNodeSet`) — or a parameter of the row's action (`j`);
* a paper label is not in the label map, as for `{cite}` ([Cite.lean](Cite.lean)).

The derived columns — actor, the three read columns, the fault pattern and
the writes — are the ones a checker can compute from the action bodies; the
others (paper, note) are a human's. The file names its columns in a header
row, so a checker's output can supply the derived ones later without the
table changing shape.
-/
import VersoManual
import CadenceGuide.Audit
import CadenceGuide.Cite

open Lean Elab Meta
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

/-- The table's columns: the key in the file's header, the heading on the
page, and whether the column is derived from the action bodies (checked
against the model's vocabulary). -/
def auditColumns : List (String × String × Bool) :=
  [("action", "Action", false),
   ("paper", "Paper", false),
   ("actor", "Actor", true),
   ("reads_own", "Reads, own", true),
   ("reads_net", "Reads, network", true),
   ("reads_net_neg", "Negative network reads", true),
   ("fault", "Fault pattern", true),
   ("writes", "Writes", true),
   ("note", "Note", false)]

/-- A row of the file: a group heading, or an action row by column key. -/
inductive AuditLine where
  | group (title : String)
  | row (line : Nat) (cells : Std.HashMap String String)

/-- Parse the data file: `#` lines are comments, the first other line is the
header, `group<TAB>title` starts a group, and every other line is a row. -/
def parseAuditFile (text : String) : Except String (Array AuditLine) := do
  let lines := (text.splitOn "\n").zipIdx.filter fun (l, _) =>
    !l.trimAscii.isEmpty && !l.startsWith "#"
  let some (header, _) := lines.head? | throw "the file has no header row"
  let keys := header.splitOn "\t" |>.map (·.trimAscii.toString)
  let known := auditColumns.map (·.1)
  for k in keys do
    unless known.contains k do throw s!"unknown column `{k}` in the header; the columns are {known}"
  for k in known do
    unless keys.contains k do throw s!"the header has no `{k}` column"
  let mut out := #[]
  for (l, i) in lines.drop 1 do
    let cells := l.splitOn "\t" |>.map (·.trimAscii.toString)
    if cells.head? == some "group" then
      out := out.push (.group ((cells.drop 1).headD ""))
    else
      if cells.length != keys.length then
        throw s!"line {i + 1} has {cells.length} cells, the header {keys.length}"
      out := out.push (.row (i + 1) (Std.HashMap.ofList (keys.zip cells)))
  return out

/-- The code spans of a cell. -/
def codeSpans (cell : String) : List String :=
  (cell.splitOn "`").zipIdx.filterMap fun (s, i) => if i % 2 == 1 then some s else none

/-- The name a code span is about: its first identifier, after a negation,
and the last component of a dotted name (`nset.is_byz` is `is_byz`). -/
def spanHead (span : String) : Option String :=
  let isIdChar (c : Char) := c.isAlphanum || c == '_' || c == '\'' || c == '.'
  let rest := span.toList.dropWhile (fun c => c == '¬' || c == '!' || c == ' ' || c == '(')
  let ident := rest.takeWhile isIdChar
  if ident.isEmpty || !(ident.head!.isAlpha || ident.head! == '_') then none
  else ((String.ofList ident).splitOn ".").getLast?

/-- A cell's text as HTML: escaped, with its code spans as code. -/
def cellHtml (cell : String) : String :=
  String.join <| (cell.splitOn "`").zipIdx.map fun (s, i) =>
    if i % 2 == 1 then s!"<code>{esc s}</code>" else esc s

/-- Every name the model's audit table may cite: its state, immutable state
and declarations, and the fields of the classes it instantiates. -/
def modelVocabulary (env : Environment) (m : Name) : Except String NameSet := do
  let mut vocab : NameSet := {}
  for s in [m ++ `State, m ++ `Theory] do
    unless isStructure env s do throw s!"{s} is not in the development; is {m} a Veil model?"
    for f in getStructureFieldsFlattened env s (includeSubobjectFields := false) do
      vocab := vocab.insert f
  let some rts := env.find? (m ++ `relationalTransitionSystem)
    | throw s!"{m}.relationalTransitionSystem is not in the development"
  for c in instBinderClasses rts.type do
    let foreign := (moduleOf env c).any fun mod =>
      [`Init, `Lean, `Std, `Mathlib, `Batteries].any (·.isPrefixOf mod)
    if isStructure env c && !foreign then
      for f in getStructureFieldsFlattened env c (includeSubobjectFields := false) do
        vocab := vocab.insert f
  return vocab

/-- The binder names of a declaration's type: for an action, its parameters. -/
partial def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

structure AuditTableConfig where
  model : Ident
  file : String
  sample : Bool

instance : FromArgs AuditTableConfig DocElabM :=
  ⟨AuditTableConfig.mk <$> .positional `model .ident <*> .positional `file .string
    <*> .flag `sample false⟩

/-- `{auditTable M "file.tsv"}` — the audit table of model `M`, from its data
file, checked against the model. `+sample` drops the completeness check, for
a table that shows a few rows on purpose. -/
@[block_command]
def auditTable : BlockCommandOf AuditTableConfig
  | ⟨modelId, file, sample⟩ => do
    let m := modelId.getId
    let env ← getEnv
    let path : System.FilePath := file
    unless ← path.pathExists do
      throwError "{file} does not exist (the path is relative to the project root)"
    let lines ← match parseAuditFile (← IO.FS.readFile path) with
      | .ok ls => pure ls
      | .error e => throwError "{file}: {e}"
    let some (.inductInfo label) := env.find? (m ++ `Label)
      | throwErrorAt modelId "{m}.Label is not in the development; is {m} a Veil model?"
    let actions : List String := label.ctors.map (·.componentsRev.head!.toString)
    let vocab ← match modelVocabulary env m with
      | .ok v => pure v
      | .error e => throwErrorAt modelId e
    let labels ← loadPaperLabels
    let a ← loadAnchors
    let mut errors : Array String := #[]
    let mut seen : Array String := #[]
    let mut body : Array String := #[]
    for l in lines do
      match l with
      | .group title =>
        body := body.push s!"<tr class=\"cg-audit-group\"><th colspan=\"{auditColumns.length}\">\
          {cellHtml title}</th></tr>"
      | .row i cells =>
        let names := ((cells.getD "action" "").splitOn ",").map (·.trimAscii.toString)
          |>.filter (· != "")
        let mut cellsHtml : Array String := #[]
        -- A code span may name one of the row's actions' parameters (`j`).
        let params : List Name := names.flatMap fun n =>
          ((env.find? (m ++ n.toName)).map (binderNames ·.type)).getD []
        for n in names do
          unless actions.contains n do
            errors := errors.push s!"line {i}: `{n}` is not an action of {m} (a constructor of {m}.Label)"
          if seen.contains n then errors := errors.push s!"line {i}: `{n}` has a second row"
          seen := seen.push n
        let actionHtml := ", ".intercalate <| names.map fun n =>
          match declUrl env a (m ++ n.toName) with
          | some u => if env.contains (m ++ n.toName) then s!"<a href=\"{u}\"><code>{esc n}</code></a>"
                      else s!"<code>{esc n}</code>"
          | none => s!"<code>{esc n}</code>"
        cellsHtml := cellsHtml.push actionHtml
        for (key, _, derived) in auditColumns.drop 1 do
          let cell := cells.getD key ""
          if key == "paper" then
            let refs := (cell.splitOn ",").map (·.trimAscii.toString) |>.filter (· != "")
            let mut parts := #[]
            for r in refs do
              if r == "—" || r == "-" then parts := parts.push "—"; continue
              match paperReference labels r with
              | .ok ref => parts := parts.push s!"{esc ref} (<code>{esc r}</code>)"
              | .error e => errors := errors.push s!"line {i}: {e}"
            cellsHtml := cellsHtml.push (", ".intercalate parts.toList)
            continue
          if derived then
            for span in codeSpans cell do
              if let some h := spanHead span then
                unless vocab.contains h.toName || env.contains (m ++ h.toName)
                    || params.contains h.toName do
                  errors := errors.push s!"line {i}, column {key}: `{h}` (in `{span}`) is not \
                    a relation, individual or declaration of {m}"
          cellsHtml := cellsHtml.push (cellHtml cell)
        body := body.push ("<tr>" ++ String.join (cellsHtml.toList.map (s!"<td>{·}</td>")) ++ "</tr>")
    unless sample do
      let missing := actions.filter (!seen.contains ·)
      unless missing.isEmpty do
        errors := errors.push s!"no row for {missing.length} action(s) of {m}: {missing} \
          (mark a table that shows a selection on purpose with +sample)"
    unless errors.isEmpty do
      throwErrorAt modelId "{file} does not describe {m}:\n{"\n".intercalate errors.toList}"
    let head := String.join (auditColumns.map fun (_, h, _) => s!"<th>{esc h}</th>")
    let note := if sample then
      s!"<caption>A selection of {m}'s actions.</caption>" else ""
    let html := s!"<div class=\"cg-audit-wrap\"><table class=\"cg-contracts cg-audit\">{note}\
      <thead><tr>{head}</tr></thead><tbody>{String.join body.toList}</tbody></table></div>"
    ``(Verso.Doc.Block.other (CadenceGuide.Block.status $(quote html)) #[])

end CadenceGuide
