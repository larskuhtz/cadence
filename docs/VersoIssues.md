# Verso issues this project works around

*What the documentation site ([Documentation.md](./Documentation.md)) has to
compensate for in Verso's literate renderer, why, and what the fix would be.
Kept so the workarounds can be removed when they stop being necessary —
each entry says what to delete.*

Verso is pinned at `v4.32.0`, the tag matching this project's toolchain;
`v4.33`–`v4.35` track later Lean releases and are not available to us. Every
issue below was checked against Verso `main` on 2026-09-23 and is still
present there, so none of them is waiting on an upgrade.

## The one thing to know first

Verso has **two** Markdown converters, and they differ in what they support:

| converter | builds | used by this site? |
|---|---|---|
| `mdBlock` in `VersoLiterate/Exported.lean` | a Verso `Doc` | **no** |
| `md2Html` in `VersoLiterateCode.lean` | HTML directly | **yes** |

Reading the wrong one is the trap. `mdBlock` rejects tables outright with
`"Markdown tables not supported"`, which is easy to mistake for the site's
limit; `md2Html`, the one these pages actually go through, renders tables
fine. Check which converter a symptom belongs to before concluding anything.

Separately: Lean has two docstring *languages*, selected by the built-in
options `doc.verso` / `doc.verso.module`. Unset — the default, and what this
development uses — `/-! … -/` and `/-- … -/` are Markdown. Verso's own
manual is authored in Verso markup instead, which is the better-exercised
path; every issue here is on the Markdown side. Verso's literate test suite
(≈1 350 lines) covers configuration, landing pages and navigation, and none
of the four below.

## 1. Markdown tables are never parsed

**Symptom.** A table in a module header renders as literal `|` rows, with
the `code` spans and links inside its cells correctly formatted — inline
markup is processed, block structure is not.

**Cause.** Not the renderer. `md2Html` handles `.table` and emits a proper
`<thead>`/`<tbody>`. Verso calls `MD4Lean.parse` at its default dialect,
`MD_DIALECT_COMMONMARK`, in which GitHub tables are off, so a table arrives
as one paragraph of text and never reaches the emitter. Verified by parsing
the same input with and without `MD_FLAG_TABLES`: default gives `p[...]`,
the flag gives `TABLE`.

**Fix.** One argument, at the three `MD4Lean.parse` call sites in
`VersoLiterateMain.lean`:

```lean
MD4Lean.parse x MD4Lean.MD_FLAG_TABLES
```

Tried locally: all eleven tables then rendered as real tables, zero leftover
pipe rows. Not adopted, because patching Verso means forking it — and,
having seen the result, because it would not have been the right fix
anyway. Ten of the eleven had cells of 113 to 550 characters, so as tables
they were paragraphs squeezed into columns.

**Our workaround.** Moot, and deliberately so: those eleven were lists of
labelled explanations wearing table syntax, and are now written as lists.
Nothing in the published modules depends on this issue any more. It stays
recorded because a future table would hit it.

## 2. Markdown list items are emitted without `<li>`

**Symptom.** Bulleted and numbered lists in docstrings render as unindented
runs of text with no markers.

**Cause.** `md2Html`'s `.ul`/`.ol` cases put each item's blocks directly
inside `<ul>`/`<ol>`, so every item is a bare `<p>` and there is no list
item for a marker to attach to. Verso's other emitter, `Doc/Html.lean`,
wraps them correctly, so only the Markdown path is affected.

**Fix.** Wrap each item's blocks in `<li>`, as `Doc/Html.lean` does.

**Our workaround.** `display: list-item` on those paragraphs, in
[`site-overrides.css`](./site-overrides.css) §1. Delete that section when
this is fixed. Note the selectors have to out-specify Verso's
`.code-content > .md-text.mod-doc :is(p, ul, ol, …) { display: block }`,
which is (0,3,1).

## 3. Maths is parsed but dropped

**Symptom.** `$a + b$` and `$$…$$` render as literal text.

**Cause.** Two layers. `MD_FLAG_LATEXMATHSPANS` is not passed, as in issue
1, so the parser emits plain text; and even with the flag, `md2Html` renders
both maths inlines as `.empty`, marked `TODO`.

Everything downstream is already in place: KaTeX ships with the site, the
generated pages load a `math.js` that renders `.math.inline` and
`.math.display` on load, and Verso's other converter already produces those
classes. The gap is one emitter.

**Fix.** Pass the flag and fill in the two `TODO` cases in `md2Html`.

**Our workaround.** None, and none wanted: this development currently writes
no maths in its docstrings, and enabling the flag alone would make any that
were written *disappear* rather than show as literal text — silent loss in
place of a visible non-feature.

## 4. A doc comment on an anonymous command keeps its opening `/--`

**Symptom.** A `#guard_msgs` expectation renders with a leading `/--` and no
closing `-/`.

**Cause.** `parseDocComment` in `VersoLiterateMain.lean` strips delimiters
by hand:

```lean
text.dropPrefix "/-- " |>.dropSuffix " -/" |>.dropSuffix "\n-/" |>.dropSuffix "-/"
```

The closing delimiter is matched three ways, the opening one only with a
trailing *space*. Written as `#guard_msgs` itself suggests — `/--` alone on
a line, the message below — the suffix is removed and the prefix is not.
This path handles doc comments on *anonymous* commands, which is why it
shows on `#guard_msgs` and `example` and not on named declarations. 41
occurrences here, all of them axiom or `#veil_status` pins.

**Fix.** Strip `/--` and then any leading whitespace, mirroring the suffix.

**Our workaround.** `fix_docstring_markers` in
[`../scripts/docs.sh`](../scripts/docs.sh) removes the leftover inline from
the JSON. Delete that function when this is fixed.

## 5. The `/--` marker in a code box wraps onto two lines

**Symptom.** The pseudo-element marker before an inlined docstring renders
as `/` on one line and `--` on the next.

**Cause.** `literate.css` sets `width: min-content` on the `::before` and
`::after` markers. A line may break after `/`, so `min-content` resolves to
the width of `--`. Measured in Chrome: 16.86px wide by 32px tall, against
25.30 by 16 when it does not wrap. Verso's other docstring rule, in
`Highlighted.lean`, uses `max-content` and does not have the bug.

**Fix.** `white-space: nowrap`, or `max-content` as elsewhere.

**Our workaround.** Moot — this site drops the markers entirely
([`site-overrides.css`](./site-overrides.css) §3) and marks docstrings by
colour instead. The bug is recorded because anyone keeping the markers will
hit it.

## 6. Markup in plain comments is shown literally

**Symptom.** In a `--` or `/- … -/` comment, `` `code` ``, `*emphasis*`
and `**strong**` appear as typed, backticks and asterisks included, while
the same markup in a doc comment next to it is rendered.

**Cause.** Not a bug but a design line. A doc comment is documentation Lean
attaches to a declaration, and Verso renders it as a Markdown block; a
plain comment is not in Lean's syntax tree at all — SubVerso emits it as a
`lineComment` or `blockComment` token, which the HTML stage prints as one
`<span class="comment">` of text. Nothing is configurable: `literate.toml`
has no option for comments. It matters here more than elsewhere because a
Veil `safety`, `invariant` or `action` cannot take a doc comment (`CLAUDE.md`,
hard rules), so the explanation of every model declaration is a plain
comment.

**Fix.** Upstream, the HTML stage could render a comment token's text as
inline Markdown. Not proposed yet.

**Our workaround.** [`site-comments.js`](./site-comments.js), loaded through
`extra_js`, renders the inline subset in place, with its styles in
[`site-overrides.css`](./site-overrides.css) §5. It is deliberately
conservative — anything it could misread stays as written, and a comment laid
out in columns is left alone, because hiding delimiters would shift its
alignment — and it keeps every delimiter in the DOM, hidden, so the copy
button still copies the source. The rules are in the file's header, and
`node scripts/test-site-comments.js [site/sources]` tests them — given a
rendered site, against every comment on it. Delete the script, its test,
the `extra_js` line and the markup rules of §5 when Verso renders comment
markup itself, or when the comments it serves have become doc comments.
The first rule of §5 — comments a notch smaller, in a quieter blue than the
docstrings, so the code stays in front — is a presentation choice rather
than a workaround, and stays.

## Not bugs, but sharp edges

* **`[modules."X"] title` applies to the whole subtree.** Per-module
  configuration resolves by longest-*prefix* match, and unlike `url` — which
  appends the remaining components — `title` is inherited verbatim. A title
  on the root module retitles every page, and the navigation bar repeats one
  string. Give a title only to a leaf.
* **`extra_css` files are copied in under their own basename.** Naming one
  `literate.css` silently replaces Verso's entire stylesheet. Ours is
  `site-overrides.css` for that reason.
* **`[[targets]] module = "X"` is subtree-inclusive**, and `exclude` matches
  by name prefix — so `"Cadence.Chorus.Proofs"` drops a whole subtree even
  though no module of that name exists.
* **Bare TOML keys must precede every `[section]` header**, or they are
  absorbed into the open table. The symptom is
  `Errors decoding literate.toml: expected array`.
* **The search index is keyed by Lean name, which is global.** Publishing
  two modules that each declare a root-level `main` fails the build with
  `Duplicate document ID`.
