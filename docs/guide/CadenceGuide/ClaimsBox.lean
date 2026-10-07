/-
`:::claims` — a set-off box: the front page's claims box, and the "what you
check" boxes of the chapters on models and contracts.

Presentation only. What it contains is ordinary guide text, so the checks are
those of its contents: a `{decl}` inside it fails the build when the
declaration is renamed, a `{cite}` when the label leaves the label map.

    :::claims (title := "What this project claims")
    …
    :::
-/
import VersoManual

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

block_extension Block.claimsBox (title : Option String) where
  data := toJson title
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ data contents => do
      let title : Option String := (fromJson? data).toOption.join
      let head := match title with
        | some t => {{<div class="cg-claims-title">{{Verso.Output.Html.text true t}}</div>}}
        | none => .empty
      pure {{<aside class="cg-claims">{{head}}{{← contents.mapM goB}}</aside>}}
  toTeX := none
  extraCss := [r#"
.cg-claims { margin: 1.2rem 0 1.8rem; padding: 0.9rem 1.2rem 0.4rem;
  border: 1px solid #d0d7de; border-left: 4px solid #0b57d0; border-radius: 4px;
  background: #f6f8fa; }
.cg-claims-title { font-weight: 700; font-size: 1.05em; margin-bottom: 0.5rem;
  color: var(--verso-structure-color, #10131a); }
.cg-claims > p, .cg-claims > ul, .cg-claims > ol { margin-top: 0.4rem; margin-bottom: 0.7rem; }
"#]

structure ClaimsConfig where
  title : Option String

instance : FromArgs ClaimsConfig DocElabM :=
  ⟨ClaimsConfig.mk <$> .named `title .string true⟩

/-- `:::claims (title := "…")` — its contents in a set-off box. -/
@[directive claims]
def claims : DirectiveExpanderOf ClaimsConfig
  | ⟨title⟩, contents => do
    ``(Verso.Doc.Block.other (CadenceGuide.Block.claimsBox $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

end CadenceGuide
