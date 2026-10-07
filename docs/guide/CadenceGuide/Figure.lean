/-
`{figure "docs/diagrams/x.svg"}` — a diagram, inlined into the page.

One source per diagram, a hand-written SVG under `docs/diagrams`, shown here
and, as a Markdown image, on GitHub. The file is read while the chapter elaborates and its markup placed in
the page, so it takes the page's fonts and scales with the column. A file
that breaks the conventions an inlined SVG depends on fails the build:

* it must exist;
* it must carry a `<title>`, which screen readers and GitHub's image alt read;
* every `class` and every `id` in it must start with `dg-`: an inline SVG's
  `<style>` and ids belong to the whole page, so an unprefixed name could
  restyle the page around it, or collide with another figure's marker;
* every declaration it names must exist. An element that shows a Lean name
  carries it in `data-decl="Composed.liveness"` (a constant, resolved in the
  guide's environment) or `data-decl-veil="Chorus vote"` (an item of a Veil
  model that is not a constant, found in the rendered sources the way
  `{model}` finds one), so a renamed declaration cannot leave a diagram
  stale. A resolved `<text>` or `<tspan>` becomes a link to the declaration
  in the rendered sources.

The file's `@media (prefers-color-scheme: dark)` block, which GitHub's dark
mode needs, is dropped on the way in: the site is light-only, and that block
would turn the figure dark on a light page whenever the reader's system is
dark. If the site gets a dark theme, keep the block instead.
-/
import VersoManual
import CadenceGuide.Audit

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

/-- The index of the first occurrence of `pat` in `s` at or after `start`. -/
def findFrom (s pat : Array Char) (start : Nat) : Option Nat := Id.run do
  let mut i := start
  while i + pat.size ≤ s.size do
    if (List.range pat.size).all (fun k => s[i + k]! == pat[k]!) then return some i
    i := i + 1
  return none

/-- The index of the last occurrence of `pat` in `s` that starts before `stop`. -/
def findBefore (s pat : Array Char) (stop : Nat) : Option Nat := Id.run do
  let mut best := none
  let mut i := 0
  while i < stop do
    match findFrom s pat i with
    | some j => if j < stop then best := some j; i := j + 1 else break
    | none => break
  return best

/-- The index just past the `}` that closes the `{` at `lb`. -/
def closingBrace (s : Array Char) (lb : Nat) : Option Nat := Id.run do
  let mut depth := 0
  for i in [lb:s.size] do
    if s[i]! == '{' then depth := depth + 1
    else if s[i]! == '}' then
      depth := depth - 1
      if depth == 0 then return some (i + 1)
  return none

/-- The SVG without its dark-scheme `@media` blocks. -/
partial def dropDarkScheme (svg : String) : Except String String :=
  let s := svg.toList.toArray
  match findFrom s "prefers-color-scheme".toList.toArray 0 with
  | none => .ok svg
  | some at_ =>
    match findBefore s "@media".toList.toArray at_, findFrom s #['{'] at_ with
    | some start, some brace =>
      match closingBrace s brace with
      | some stop =>
        dropDarkScheme (String.ofList (s.extract 0 start).toList ++ String.ofList (s.extract stop s.size).toList)
      | none => .error "an @media block is not closed"
    | _, _ => .error "`prefers-color-scheme` outside an @media block"

/-- The values of every `attr="…"` in the markup. -/
def attrValues (svg attr : String) : List String :=
  (svg.splitOn s!" {attr}=\"").drop 1 |>.map (·.takeWhile (· != '"') |>.toString)

def escHtml (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

/-- The SVG as it goes into the page, or why it cannot. -/
def figureMarkup (svg : String) : Except String String := do
  unless (svg.splitOn "<title").length > 1 do
    throw "it has no <title>; give it one (and a <desc>), for screen readers and GitHub's alt text"
  let classes := (attrValues svg "class").flatMap (·.splitOn " ") |>.filter (· != "")
  let ids := attrValues svg "id"
  let bad := (classes ++ ids).filter (!·.startsWith "dg-") |>.eraseDups
  unless bad.isEmpty do
    throw s!"its classes and ids must start with `dg-`, so that they cannot reach the page \
      around it; these do not: {bad}"
  -- Everything before the root element: an XML declaration or a comment.
  let body := match svg.splitOn "<svg" with
    | _ :: rest@(_ :: _) => "<svg" ++ "<svg".intercalate rest
    | _ => svg
  dropDarkScheme body

/-- The Veil commands that declare a model item, after the modifiers
`immutable` and `ghost`. -/
def veilKeywords : List String :=
  ["relation", "individual", "function", "action", "procedure", "safety", "invariant",
   "step_property", "type", "instantiate", "assumption", "trusted"]

/-- Does a source line declare `item`? `relation vote_quorum_pos (j : node)`,
`safety [agreement_pos]`. -/
def declaresItem (line item : String) : Bool :=
  let ws := (line.splitOn " ").filter (· != "") |>.dropWhile (fun w => w == "immutable" || w == "ghost")
  match ws with
  | kw :: name :: _ =>
    let bare := ((name.takeWhile (fun c => c != '(' && c != ':')).toString.replace "[" "").replace "]" ""
    veilKeywords.contains kw && bare == item
  | _ => false

/-- Where an item of Veil model `M` (in the module `Cadence.M`) is on its
rendered page, or why it cannot be found. -/
def veilItemUrl (a : Anchors) (model item : String) : DocElabM (Except String String) := do
  let mod := `Cadence ++ model.toName
  let items ← loadItems mod
  let hits := items.filter fun it =>
    (itemHighlighted it).any fun hl =>
      (hl.toString.splitOn "\n").any (declaresItem ·.trimAscii.toString item)
  let #[it] := hits
    | return .error s!"{hits.size} items of {mod} declare `{item}`; expected one"
  let frag := match it.defines.find? a.defs.contains, it.range with
    | some n, _ => some (toString (toString n).sluggify)
    | none, some (st, _) => sectionAt a mod st.line
    | none, none => none
  return .ok (moduleUrl mod ++ (frag.map ("#" ++ ·)).getD "")

/-- Check every `data-decl` and `data-decl-veil` of the SVG, and wrap each
resolved `<text>` or `<tspan>` in a link to it. The errors name the attribute. -/
def resolveDecls (svg : String) : DocElabM (Except (Array String) String) := do
  let env ← getEnv
  let a ← loadAnchors
  let s := svg.toList.toArray
  let mut errors := #[]
  -- (start of element, end of element, url) for each element to wrap.
  let mut wraps : Array (Nat × Nat × String) := #[]
  for attr in ["data-decl", "data-decl-veil"] do
    let pat := s!" {attr}=\"".toList.toArray
    let mut pos := 0
    while true do
      let some at_ := findFrom s pat pos | break
      let vStart := at_ + pat.size
      let some vEnd := findFrom s #['"'] vStart | break
      pos := vEnd
      let value := String.ofList (s.extract vStart vEnd).toList
      let url : Except String String ← if attr == "data-decl" then
          pure <| match declUrl env a value.toName with
            | some u => if env.contains value.toName then .ok u
                        else .error s!"{attr}=\"{value}\" names no declaration"
            | none => .error s!"{attr}=\"{value}\" names no declaration of a compiled module"
        else match value.splitOn " " with
          | [m, item] => do
            match ← veilItemUrl a m item with
            | .ok u => pure (.ok u)
            | .error e => pure (.error s!"{attr}=\"{value}\": {e}")
          | _ => pure (.error s!"{attr}=\"{value}\" is not `<Model> <item>`")
      match url with
      | .error e => errors := errors.push e
      | .ok u =>
        -- The element carrying the attribute, if it is a text run to link.
        let some lt := findBefore s #['<'] at_ | continue
        let tag := String.ofList ((s.extract (lt + 1) at_).toList.takeWhile (· != ' '))
        unless tag == "text" || tag == "tspan" do continue
        let close := s!"</{tag}>".toList.toArray
        let some ce := findFrom s close vEnd | continue
        -- A nested element of the same kind would make the match wrong; leave it unlinked.
        if (findFrom s s!"<{tag}".toList.toArray vEnd).any (· < ce) then continue
        wraps := wraps.push (lt, ce + close.size, u)
  unless errors.isEmpty do return .error errors
  let mut out := ""
  let mut i := 0
  for (st, en, u) in wraps.qsort (·.1 < ·.1) do
    if st < i then continue
    out := out ++ String.ofList (s.extract i st).toList ++ s!"<a href=\"{escHtml u}\">" ++
      String.ofList (s.extract st en).toList ++ "</a>"
    i := en
  return .ok (out ++ String.ofList (s.extract i s.size).toList)

block_extension Block.figure (html : String) where
  data := .str html
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .str h := data | reportError "figure: expected a string" *> pure .empty
      pure (Verso.Output.Html.text false h)
  toTeX := none
  extraCss := [r#"
.cg-figure { margin: 1.2rem 0 1.6rem; }
.cg-figure svg { display: block; max-width: 100%; height: auto; margin: 0 auto; }
.cg-figure figcaption { margin-top: 0.5rem; font-size: 0.92em; color: #57606a; text-align: center; }
"#]

structure FigureConfig where
  file : String
  caption : Option String

instance : FromArgs FigureConfig DocElabM :=
  ⟨FigureConfig.mk <$> .positional `file .string <*> .named `caption .string true⟩

/-- `{figure "docs/diagrams/x.svg" (caption := "…")}` — the SVG file, a path
from the project root, inlined into the page. -/
@[block_command]
def figure : BlockCommandOf FigureConfig
  | ⟨file, caption⟩ => do
    let path : System.FilePath := file
    unless ← path.pathExists do
      throwError "{file} does not exist (the path is relative to the project root)"
    let svg ← match figureMarkup (← IO.FS.readFile path) with
      | .ok s => pure s
      | .error e => throwError "{file}: {e}"
    let svg ← match ← resolveDecls svg with
      | .ok s => pure s
      | .error es => throwError "{file}: a name in the diagram does not resolve:\n{"\n".intercalate es.toList}"
    let cap := match caption with
      | some c => s!"<figcaption>{escHtml c}</figcaption>"
      | none => ""
    let html := s!"<figure class=\"cg-figure\">{svg}{cap}</figure>"
    ``(Verso.Doc.Block.other (CadenceGuide.Block.figure $(quote html)) #[])

end CadenceGuide
