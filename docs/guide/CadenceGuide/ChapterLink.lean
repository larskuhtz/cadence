/-
`{chapter "file"}[text]` — a link to another chapter of the guide, by the
page address its `%%% file := "…" %%%` fixes.

A chapter is a page of the site, not a file of the repository, so a Markdown
link to it would fail the repository's link check
([site-links.sh](../../../scripts/site-links.sh)) and, written anyway, would
go stale silently when a chapter's address changed. This role reads the
addresses from the chapter sources while the guide elaborates and fails the
build on one that no chapter declares. Every guide page carries a
`<base href>` at the guide's root, so the link it writes, `file/`, means the
same on every page.

    see {chapter "reading-a-model"}[chapter 3]
-/
import VersoManual

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

/-- The chapter sources, relative to the project root, where lake elaborates
the guide. -/
def chaptersDir : System.FilePath := "docs/guide/CadenceGuide/Chapters"

/-- Every page address a chapter declares, read from the `file := "…"` line
of its metadata. -/
def chapterFiles : IO (Array String) := do
  let mut out := #[]
  for entry in (← chaptersDir.readDir) do
    unless entry.path.extension == some "lean" do continue
    for line in (← IO.FS.lines entry.path) do
      let l := line.trimAscii.toString
      if l.startsWith "file := \"" then
        out := out.push ((l.drop 9).takeWhile (· != '"')).toString
  return out

structure ChapterConfig where
  file : String

instance : FromArgs ChapterConfig DocElabM := ⟨ChapterConfig.mk <$> .positional `file .string⟩

/-- `{chapter "file"}[text]` — a link to the chapter whose page address is
`file`, checked against the chapter sources. -/
@[role]
def chapter : RoleExpanderOf ChapterConfig
  | ⟨file⟩, inls => do
    let files ← chapterFiles
    unless files.contains file do
      throwError "no chapter declares the page address \"{file}\"; the chapters declare \
        {files.toList}"
    ``(Verso.Doc.Inline.link #[$(← inls.mapM elabInline),*] $(quote (file ++ "/")))

end CadenceGuide
