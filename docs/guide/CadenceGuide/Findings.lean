/-
`{findings}` — the findings for the paper's authors, as one table read from
their home, [PaperAlignment.md](../../PaperAlignment.md) §6.

A hand-written summary of the findings falls behind as soon as one is
added, so the table is read from §6's own table when the guide builds:

* **Finding**, **Group** and **Status** are §6's columns of the same names;
* **Supplement** says whether the finding quotes the internal supplement,
  read from the finding's *Quote* line: a reader needs the supplement to
  check exactly those.

The build fails when §6's table or a finding's *Quote* line cannot be
found, so the table cannot silently lose a row.
-/
import VersoManual
import CadenceGuide.ContractFields

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

/-- The findings' home, relative to the project root. -/
def paperAlignmentFile : System.FilePath := "docs/PaperAlignment.md"

/-- The cells of a Markdown table row. -/
def tableCells (line : String) : List String :=
  ((line.splitOn "|").drop 1).dropLast.map (·.trimAscii.toString)

/-- Does finding `p`'s *Quote* line cite the supplement? The line runs from
`**p.` to the finding's next bullet. -/
def quotesSupplement (lines : Array String) (p : String) : Option Bool := do
  let start ← lines.findIdx? (·.startsWith s!"**{p}. ")
  let rest := lines.toList.drop start
  let quote := rest.dropWhile (fun l => !l.startsWith "* *Quote.*")
  let (first, more) ← match quote with
    | l :: more => some (l, more)
    | [] => none
  let body := first :: more.takeWhile (fun l => !l.startsWith "* ")
  return body.any (·.contains "Supplement")

/-- `{findings}` — the findings for the paper's authors, read from
[PaperAlignment.md](../../PaperAlignment.md) §6. -/
@[block_command]
def findings : BlockCommandOf Unit
  | () => do
    let lines ← IO.FS.lines paperAlignmentFile
    let some hdr := lines.findIdx? (·.startsWith "| # | Finding | Group |")
      | throwError "{paperAlignmentFile}: the findings table (`| # | Finding | Group | …`) \
          is missing, so the guide cannot list the findings"
    let rows := (lines.toList.drop (hdr + 2)).takeWhile (·.startsWith "|")
    if rows.isEmpty then throwError "{paperAlignmentFile}: the findings table has no rows"
    let mut html := #[]
    for r in rows do
      match tableCells r with
      | [p, what, group, _kind, status] =>
        let some sup := quotesSupplement lines p
          | throwError "{paperAlignmentFile}: finding {p} has no *Quote* line"
        html := html.push s!"<tr><td>{esc p}</td><td>{inlineMarkdown what}</td>\
          <td>{esc group}</td><td>{if sup then "yes" else "—"}</td>\
          <td>{inlineMarkdown status}</td></tr>"
      | _ => throwError "{paperAlignmentFile}: a findings row does not have five cells: {r}"
    let table := s!"<table class=\"cg-contracts cg-fields\"><thead><tr><th>Finding</th>\
      <th>What</th><th>Group</th><th>Quotes the supplement</th><th>Status</th></tr></thead>\
      <tbody>{String.join html.toList}</tbody></table>"
    ``(Verso.Doc.Block.other (CadenceGuide.Block.status $(quote table)) #[])

end CadenceGuide
