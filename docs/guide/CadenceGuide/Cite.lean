/-
`{cite}` — a paper citation, rendered from the label map.

[paper-cites.sh](../../../scripts/paper-cites.sh) checks the citations in Lean
comments and Markdown; the guide's prose is neither, so the guide cites through
this role instead. The author writes the label and the reader sees the
reference as the rendered PDF shows it, with the label in parentheses
([CLAUDE.md](../../../CLAUDE.md), "Documentation rules"): `{cite}`alg:voting``
renders "Algorithm 3 (`alg:voting`)". The reference is read from
[paper-labels.tsv](../../paper-labels.tsv), so it cannot drift from the target
revision, and a label not in the map fails the build.
-/
import VersoManual

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

/-- The label map, relative to the project root, where lake elaborates the guide. -/
def paperLabelsFile : System.FilePath := "docs/paper-labels.tsv"

/-- Every label of the target revision, with its document (`main` or
`supplement`) and its rendered reference. -/
def loadPaperLabels : IO (Std.HashMap String (String × String)) := do
  unless ← paperLabelsFile.pathExists do
    throw <| IO.userError s!"{paperLabelsFile} is missing"
  let mut m := {}
  for line in (← IO.FS.lines paperLabelsFile) do
    if line.startsWith "#" then continue
    match line.splitOn "\t" with
    | label :: doc :: ref :: _ => m := m.insert label (doc, ref)
    | _ => pure ()
  return m

/-- The reference a reader sees for `label`, the supplement named where it is
the supplement: `Lemma 9`, `Supplement, Lemma 13`. -/
def paperReference (labels : Std.HashMap String (String × String)) (label : String) :
    Except String String :=
  match labels.get? label with
  | some (doc, ref) => .ok ((if doc == "supplement" then "Supplement, " else "") ++ ref)
  | none => .error s!"`{label}` is not a label of the target revision \
      (docs/paper-labels.tsv); look the label up there"

/-- `{cite}`label`` — "Lemma 9 (`lemma:chorus-agreement`)", checked against
the label map. -/
@[role]
def cite : RoleExpanderOf Unit
  | (), inls => do
    let some s ← oneCodeStr? inls
      | throwError "write the label as code: {"{"}cite}`lemma:chorus-agreement`"
    let label := s.getString
    let ref ← match paperReference (← loadPaperLabels) label with
      | .ok r => pure r
      | .error e => throwErrorAt s e
    ``(Verso.Doc.Inline.concat #[
        Verso.Doc.Inline.text $(quote (ref ++ " (")),
        Verso.Doc.Inline.code $(quote label),
        Verso.Doc.Inline.text ")"])

end CadenceGuide
