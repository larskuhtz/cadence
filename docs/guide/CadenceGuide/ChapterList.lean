/-
`{chapterList}` and `{chapter X}` — the front page's chapter list, and links
between chapters.

Both read the chapter files themselves, so neither repeats what a chapter
says about itself:

* a chapter's **title** is its `#doc (Manual) "…"` line;
* its **address** is its `%%% file := "…" %%%`, the page `site/guide/<file>/`;
* its **opener** is the italic paragraph that follows, the one line saying
  what the chapter covers and what it assumes.

`{chapterList}` lists the chapters in the order
[CadenceGuide.lean](../CadenceGuide.lean) includes them, each with its title,
linked, and its opener, and leaves out the appendices (a title starting with
"Appendix"). A chapter the root includes that is missing, or has no title,
address or opener, fails the build, and so does a chapter file under
[Chapters](Chapters) that the root does not include, unless it is an appendix.

`{chapter Claims}[chapter 2]` links its text to the chapter written in
`Chapters/Claims.lean`; with no text, the chapter's title is the text. A
chapter file that does not exist fails the build. The link is written in site
layout, `claims/`, which every guide page resolves from the guide's root
(its `<base href>`), so the link checker of
[site-links.sh](../../../scripts/site-links.sh) never sees it: this role is
the check.
-/
import VersoManual

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

/-- The guide's root file and the chapters' directory, relative to the project
root, where lake elaborates the guide. -/
def guideRootFile : System.FilePath := "docs/guide/CadenceGuide.lean"
def chapterDir : System.FilePath := "docs/guide/CadenceGuide/Chapters"

/-- What a chapter file says about itself. -/
structure ChapterInfo where
  /-- The module's last component, `Claims` for `Chapters/Claims.lean`. -/
  name : String
  title : String
  /-- The page's address under the guide's root, without the slash. -/
  file : String
  opener : String

/-- `s` with leading and trailing blanks removed, as a list of characters. -/
private def trimChars (s : String) : List Char :=
  ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- The text between the first `"` after `pre` and the next `"`, on a line
that starts with `pre` once trimmed. -/
private def quotedAfter? (pre : String) (line : String) : Option String :=
  let l := trimChars line
  if !(String.ofList l).startsWith pre then none else
  match (l.drop pre.length).dropWhile (· != '"') with
  | '"' :: rest => some (String.ofList (rest.takeWhile (· != '"')))
  | _ => none

/-- The title, address and opener of the chapter in `Chapters/<name>.lean`. -/
def readChapter (name : String) : IO (Except String ChapterInfo) := do
  let path := chapterDir / (name ++ ".lean")
  unless ← path.pathExists do
    return .error s!"{path} does not exist"
  let lines := (← IO.FS.lines path).toList
  let some title := lines.findSome? (quotedAfter? "#doc (Manual) ")
    | return .error s!"{path}: no `#doc (Manual) \"…\"` line"
  let some file := lines.findSome? (quotedAfter? "file := ")
    | return .error s!"{path}: no `file := \"…\"` in the chapter's metadata"
  -- The opener: the first paragraph after the metadata block's closing `%%%`.
  let afterDoc := lines.dropWhile (fun l => !(String.ofList (trimChars l)).startsWith "#doc")
  let afterMeta := ((afterDoc.dropWhile (fun l => trimChars l != "%%%".toList)).drop 1).dropWhile
    (fun l => trimChars l != "%%%".toList) |>.drop 1
  let para := (afterMeta.dropWhile (fun l => (trimChars l).isEmpty)).takeWhile
    (fun l => !(trimChars l).isEmpty)
  let text := " ".intercalate (para.map (fun l => String.ofList (trimChars l)))
  let cs := text.toList
  unless cs.length > 2 && cs.head? == some '_' && cs.getLast? == some '_' do
    return .error s!"{path}: the chapter's opener, an italic paragraph `_…_` after the \
      metadata, is missing"
  return .ok { name, title, file, opener := String.ofList ((cs.drop 1).dropLast) }

/-- The chapter modules the root includes, in order. -/
def includedChapters : IO (List String) := do
  let pre := "{include 1 CadenceGuide.Chapters."
  return (← IO.FS.lines guideRootFile).toList.filterMap fun l =>
    let t := String.ofList (trimChars l)
    if t.startsWith pre then
      some (String.ofList ((t.toList.drop pre.length).takeWhile (· != '}')))
    else none

/-- `s` escaped for HTML text, with `` `code` `` spans as `<code>`. -/
private def openerHtml (s : String) : String := Id.run do
  let mut out := ""
  let mut inCode := false
  for c in s.toList do
    if c == '`' then
      out := out ++ (if inCode then "</code>" else "<code>")
      inCode := !inCode
    else
      out := out ++ match c with
        | '<' => "&lt;" | '>' => "&gt;" | '&' => "&amp;" | '"' => "&quot;"
        | c => c.toString
  return out

block_extension Block.chapterList (html : String) where
  data := .str html
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .str h := data | reportError "chapterList: expected a string" *> pure .empty
      pure (Verso.Output.Html.text false h)
  toTeX := none
  -- The list is the front page's navigation, so the table of contents Verso
  -- generates under the front page's text would repeat it; that one is
  -- hidden. The front page is the one page whose section holds the title page.
  extraCss := [r#"
.cg-chapters { list-style: none; padding-left: 0; margin: 1rem 0 1.6rem; }
.cg-chapters li { margin: 0 0 0.85rem; padding-left: 2.2rem; text-indent: -2.2rem; }
.cg-chapters .cg-chapter-num { display: inline-block; width: 2.2rem; text-indent: 0;
  font-family: var(--verso-structure-font-family); color: #57606a; }
.cg-chapters a { font-family: var(--verso-structure-font-family); font-weight: 600; }
.cg-chapters .cg-opener { display: block; text-indent: 0; font-style: italic; color: #3d444d; }
main section:has(> .titlepage) > section:has(> ol.section-toc) { display: none; }
"#]

/-- `{chapterList}` — the chapters the root includes, appendices aside, each
with its title, linked to its page, and its opener. -/
@[block_command]
def chapterList : BlockCommandOf Unit
  | () => do
    let names ← includedChapters
    let mut items := #[]
    let mut n := 0
    for name in names do
      let info ← match ← readChapter name with
        | .ok i => pure i
        | .error e => throwError e
      if info.title.startsWith "Appendix" then continue
      n := n + 1
      items := items.push <|
        s!"<li><span class=\"cg-chapter-num\">{n}.</span><a href=\"{info.file}/\">" ++
        s!"{openerHtml info.title}</a><span class=\"cg-opener\">{openerHtml info.opener}</span></li>"
    -- Every chapter file is either listed or an appendix.
    for entry in ← chapterDir.readDir do
      let some stem := entry.path.fileStem | continue
      unless entry.path.extension == some "lean" && !names.contains stem do continue
      let info ← match ← readChapter stem with
        | .ok i => pure i
        | .error e => throwError e
      unless info.title.startsWith "Appendix" do
        throwError "{entry.path} is a chapter the guide's root does not include"
    let html := "<ol class=\"cg-chapters\">" ++ String.join items.toList ++ "</ol>"
    ``(Verso.Doc.Block.other (CadenceGuide.Block.chapterList $(quote html)) #[])

structure ChapterConfig where
  name : Ident

instance : FromArgs ChapterConfig DocElabM :=
  ⟨ChapterConfig.mk <$> .positional `name .ident⟩

/-- `{chapter Claims}[text]` — `text` linked to the chapter written in
`Chapters/Claims.lean`; with no text, the chapter's title. -/
@[role]
def chapter : RoleExpanderOf ChapterConfig
  | ⟨nameId⟩, inls => do
    let info ← match ← readChapter nameId.getId.toString with
      | .ok i => pure i
      | .error e => throwErrorAt nameId e
    let url := info.file ++ "/"
    if inls.isEmpty then
      ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.text $(quote info.title)] $(quote url))
    else
      let content ← inls.mapM elabInline
      ``(Verso.Doc.Inline.link #[$content,*] $(quote url))

end CadenceGuide
