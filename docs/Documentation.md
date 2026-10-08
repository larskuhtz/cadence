# The rendered documentation site

*How the documentation site is built: the guide, the rendered sources and
the trust boundary, and what each is worth as evidence. For what is proven,
read [the guide](https://larskuhtz.github.io/cadence/guide/); this document is about the rendering.*

## Why

Most of this development's explanation lives in the Lean sources — the long
`/-! … -/` headers that state each model's scope, its abstractions and how
each of the paper's properties is covered, and the commentary that sits
between the declarations. In a text editor those headers are Markdown
source, and GitHub does not render them either. The site renders them in
source order, and adds the one thing the sources cannot show in one place:
the boundary between what the kernel checks and what is assumed.

It is documentation, not evidence. Nothing on the site carries weight in any
theorem's trust base — `verify` and `check` remain the gates
([Container.md](Container.md) §4). The single exception is deliberate: the
build fails if any end result's axiom footprint has drifted, so a broken pin
cannot be published quietly.

## What is on it

| Page | Content |
|---|---|
| `index.html` | opens the guide |
| `guide/` | **the guide**, *Cadence Verification*, a Verso document ([guide](guide)), one page per chapter: what is proven, what it rests on, how to read the models and the contracts, and how the proofs are checked — see below |
| `trust-boundary.html` | **generated from the compiled environment**: the axiom footprint of every end result, the axioms this development declares, and which module contracts have no instance |
| `sources/` | every published module rendered in source order — prose, declarations and the code between them — with a name-and-docs search box and a hierarchical navigation bar |

The trust-boundary page is the part worth explaining. It is produced by
[TrustSurface.lean](../scripts/TrustSurface.lean), which walks
the `.olean`s that `lake build` produced and computes, rather than restates:

* **the axiom footprint of each end result**, via the same mechanism as
  `#print axioms` — the expected set is Lean's three standard classical
  axioms, and anything else fails the build;
* **the axioms this development declares** (none), so that no result in the
  first table is satisfied by an assumption introduced here;
* **which contracts have an instance**, in three states that the page is
  careful to distinguish — *proven* outright, *proven relative to* another
  contract that is itself assumed, and *no instance*, which is what
  "unproven" means. The MVBA's, Chorus's and the Conductor's contracts are
  proven in full; the ACS is the one module this development does not
  implement, an assumed module consumed through its contract
  ([CompositionContracts.md](CompositionContracts.md) §5).

Because it is derived, a claim that has drifted from the code cannot survive
a rebuild of the page.

## The guide

The guide, *Cadence Verification*, is the site's entry point and its only
authored part. It is a Verso document under [guide](guide) — a Lean program
that imports the development — written to one rule: it states no fact of its
own. Every statement, status box, checklist and table on it is computed from
the compiled development, or from a checked file, while it builds, so a
change that makes one of them stale fails the build.

### Pages and files

One page per chapter. [CadenceGuide.lean](guide/CadenceGuide.lean) holds the
front page — the claims box, the overview diagram and the chapter list — and
the chapter order (`{include 1 …}`); each chapter is a file of its own under
[Chapters](guide/CadenceGuide/Chapters), so chapters are written
independently. A chapter file says three things about itself, and the front
page's chapter list reads them from it: its title (`#doc (Manual) "…"`), its
address (`%%% file := "…" %%%`, the page `site/guide/<file>/`, so a retitled
chapter keeps its URL), and its opener, the italic paragraph after the
metadata saying what the chapter covers and what it assumes. A file whose
title starts with "Appendix" is an appendix and stays out of the list.

The elements live in [CadenceGuide](guide/CadenceGuide), one module each, and
[Elements.lean](guide/CadenceGuide/Elements.lean) imports them all, with the
development, for the chapters. An element a chapter needs is added as a new
module and imported by that chapter; the existing element modules are
shared, and an edit to one rebuilds every chapter.

### The elements

| Element | Module | Shows | Fails the build when |
|---|---|---|---|
| `{decl}`X`` | [Audit.lean](guide/CadenceGuide/Audit.lean) | a declaration name, linked into the sources where its module has a page (Lean's own declarations, such as `propext`, stay unlinked) | the name does not resolve |
| `{claim X}` | [Audit.lean](guide/CadenceGuide/Audit.lean) | a theorem or instance: its docstring, a status box (the kernel's axioms, the contracts it is conditional on and what discharges them), the signature, collapsed | `X` has no docstring, or uses an axiom beyond Lean's standard three |
| `{model M "safety [x]"}` | [Audit.lean](guide/CadenceGuide/Audit.lean) | a Veil model declaration, quoted from the rendered sources; `(proven := L)` adds `L`'s status box | the text matches no declaration of `M`, or more than one |
| `{contracts}` | [Audit.lean](guide/CadenceGuide/Audit.lean) | every contract class with what provides it | — (derived; an unprovided contract shows as assumed) |
| `{pin "file" "command"}` | [Pin.lean](guide/CadenceGuide/Pin.lean) | a `#guard_msgs` pin quoted as written — the expected output, `#guard_msgs in`, the command — linked to its module's page | the file is not a module of the development, or has no pin of the command, or more than one |
| `{cite}`label`` | [Cite.lean](guide/CadenceGuide/Cite.lean) | a paper citation, "Lemma 9 (`lemma:chorus-agreement`)", rendered from [paper-labels.tsv](paper-labels.tsv) | the label is not in the map |
| `{figure "docs/diagrams/x.svg"}` | [Figure.lean](guide/CadenceGuide/Figure.lean) | an SVG diagram, inlined, without its dark-scheme block; `(caption := "…")` | the file is missing, has no `<title>`, uses a class or id without the `dg-` prefix, or names a declaration that does not resolve (below) |
| `:::claims` | [ClaimsBox.lean](guide/CadenceGuide/ClaimsBox.lean) | a set-off box, `(title := "…")`, for the claims and "what you check" boxes | — (presentation; its contents carry the checks) |
| `:::premises (claims := "A B …")` | [PremiseCover.lean](guide/CadenceGuide/PremiseCover.lean) | a plain-words list of the premises of the named claims, rendered as written | a named premise of one of the claims — the development's constant at the head of an explicit hypothesis, or a parameter whose structure carries conditions — is not mentioned by a `{decl}` inside the block |
| `{chapterList}` | [ChapterList.lean](guide/CadenceGuide/ChapterList.lean) | the front page's chapter list: each chapter the root includes, numbered, its title linked to its page, and its opener; appendices left out | an included chapter is missing or has no title, address or opener; a chapter file is neither included nor an appendix |
| `{chapter Claims}[text]` | [ChapterList.lean](guide/CadenceGuide/ChapterList.lean) | `text` linked to the chapter in `Chapters/Claims.lean`; with no text, the chapter's title | the chapter file does not exist |
| `{contractFields C}` | [ContractFields.lean](guide/CadenceGuide/ContractFields.lean) | a contract's checklist: per field, its docstring's first sentence, its level (safety fragment or temporal) and what proves it (a protocol instance, or *assumed* with the consistency witnesses) | a field has no docstring; a field has no protocol instance and its class is not in `assumedContracts`; a module of `witnessModules` is gone |
| `{auditTable M "file.tsv"}` | [AuditTable.lean](guide/CadenceGuide/AuditTable.lean) | a model's audit table, from its data file (below); `+sample` for a deliberate selection | an action is not a constructor of `M.Label`, has two rows, or (without `+sample`) has none; a relation named in a derived column is not part of `M`; a paper label is not in the map |

In a chapter they read like this — a sketch of the forms that take options:

```
The proposers of a slot are configuration:

{model Cadence.Chorus "immutable relation is_proposer"}

{model Cadence.Chorus "safety [agreement_pos]" (proven := Chorus.reachable_agreement_pos)}

{claim Chorus.termination}

{figure "docs/diagrams/chorus-slot.svg" (caption := "One slot of Chorus.")}

:::claims (title := "What you check, for each action")
1. *Actor.* … {decl}`Chorus.FJustice` … {cite}`lemma:chorus-agreement` …
:::

{chapter ModelIdioms}[Chapter 4] has the table.

{auditTable Chorus "docs/guide/audit/Chorus.tsv"}
```

Paper citations in the guide's prose go through `{cite}`:
[paper-cites.sh](../scripts/paper-cites.sh) reads Lean comments and
Markdown, and a Verso chapter's text is neither.

The two lists the classifications rest on are in
[Audit.lean](guide/CadenceGuide/Audit.lean): `witnessModules`, the modules
whose instances are consistency witnesses rather than implementations (the
ideal ACS and the witness models; [TrustSurface.lean](../scripts/TrustSurface.lean)
keeps the same list), and `assumedContracts`, the contracts this development
takes as assumed modules (the ACS's).

**Names in a diagram.** An SVG element that shows a Lean name carries it in
an attribute, so a renamed declaration fails the build instead of leaving
the diagram stale:

* `data-decl="Composed.liveness"` — a constant, resolved in the guide's
  environment;
* `data-decl-veil="Chorus vote"` — an item of a Veil model that is not a
  constant under that name, found in the model's rendered source (the
  module `Cadence.Chorus`) by the command that declares it: `relation`,
  `ghost relation`, `action`, `safety [x]` and the like;
  `"Chorus Phase.pre_deadline"` is an enum value, which the `enum Phase`
  declaration must list.

A resolved `<text>` or `<tspan>` becomes a link to the declaration in the
rendered sources when its module has a page there; a declaration of Lean's
own, such as `propext`, is checked and left unlinked. The SVG conventions themselves are in
[docs/diagrams](diagrams/README.md).

**One file, two routes.** Each diagram is one hand-written SVG file under
[docs/diagrams](diagrams/README.md). The guide inlines it with `{figure}`;
the README and the pages under docs/ show the same file as a Markdown image,
`![…](diagrams/x.svg)`, which GitHub renders, and the file's own
`prefers-color-scheme` block follows the reader's scheme there. The
rendered sources carry no diagrams.

### The audit table's data file

One file per model, under [audit](guide/audit), tab-separated:

* lines starting with `#` are comments;
* the first other line is the header, naming the columns by key, in any
  order: `action`, `paper`, `actor`, `reads_own`, `reads_net`,
  `reads_net_neg`, `fault`, `writes`, `note` — all of them, and no others;
* a line `group<TAB>title` starts a group of rows under a heading;
* every other line is a row. `action` names one action, or several
  separated by commas for actions that share a row (the Byzantine actions,
  say). `paper` is a comma-separated list of paper labels, or `—`; the
  table renders each label's reference.

Cells are text with `code spans`. In the derived columns — `actor`,
`reads_own`, `reads_net`, `reads_net_neg`, `fault`, `writes` — the first
identifier of every code span, after a leading `¬`, is checked: it must be a
state component of the model, an immutable one, a declaration of the model
(a ghost relation), a field of a class the model instantiates (`is_byz`),
or a parameter of the row's action (`j`). `paper` and `note` are a human's
and are not read for names.

**When a checker supplies the derived columns.** They are the per-action
read/write data a checker can compute from the action bodies. When one does,
it writes the same format with the derived columns only, one row per
action, and the table takes those columns from it and `paper` and `note`
from the hand file, which drops the derived columns; the rendered table
keeps its shape, and every model gets a table at no authoring cost.

### Building it

`scripts/guide.sh` builds the guide and renders it into `site/guide/`,
after one full `scripts/docs.sh` run — the fast loop for editing it. It
re-elaborates the root and every chapter each time, because they read files
lake does not track: the model quotations' JSON, the anchors, the diagrams,
the audit tables.

## Links

A reference to a file is written the way GitHub reads it: a Markdown link
relative to the file it is in — `[Interfaces.lean](Interfaces.lean)` in a
comment in `Cadence/`, `[ChorusDesign.md](../docs/ChorusDesign.md)` from the
same place, `[Architecture.md](../Architecture.md)` from the guide. That is
the only form this repository uses ([CLAUDE.md](../CLAUDE.md), "Documentation
rules"), in doc comments, plain comments, `docs/` and the guide alike, so a
link reads the same in an editor, on GitHub and on the site.

The site cannot follow such a link as written: its pages sit at other paths,
and most targets are not on it. [site-links.sh](../scripts/site-links.sh)
resolves every one — a Lean module the site renders to its page, anything
else to the file on GitHub at the commit being rendered — and stops the
build on a link whose target does not exist, which also makes
`scripts/site-links.sh check` the dead-link check for the whole repository.
The resolved links reach the pages three ways. Links in doc comments and
module headers are rewritten in the renderer's JSON before the HTML stage,
so the pages carry them as plain `href`s. The guide's own links are
rewritten in its pages by `scripts/guide.sh`. Links in plain comments, and in
the quotations and docstrings the guide embeds, are resolved in the browser
from the same table (`site-links.js`), because a plain comment is a single
text token whose text stays exactly as written.

**On the guide.** Every guide page carries a `<base href>` at the guide's
root, so a relative link means the same on every page, whatever its depth.
The one link written in site layout rather than relative to its file is the
trust boundary's, `../trust-boundary.html`, from any guide file. A page does
not record which source file wrote it, so `scripts/guide.sh` rewrites every
page from the link table of all the guide's files together, and stops if
one href goes to two different places from two of them — possible, since
the root and the chapters sit in different directories.

Every link from the guide and from the trust boundary into the sources lands
on the declaration it names, and `scripts/docs.sh` checks each one, on every
guide page, against the rendered pages. The anchors are read back from the
renderer's output — stage 2 indexes them in
`.lake/build/literate/anchors.tsv`. A declaration written in the source, a
Veil `safety`, `invariant` or `action` included, has an anchor of its own. A
declaration a Veil command generates (the `reachable_*` projections,
`invariants_of_reachable`) is not written anywhere, so it links to the
module-doc section of the command that emits it, and is marked as
generated.

The commit comes from the checkout (`origin` and `HEAD`), or from
`SITE_SOURCE_URL` where there is no history — `scripts/container.sh docs`
reads it on the host and passes it in. Nothing in the site depends on where
it is served from: every link between its pages is relative, and every link
out of it is absolute.

Every sources page opens its navigation with links back to the guide and to
the trust boundary, which the renderer's own navigation does not have.

## The renderer, and why this one

The sources are rendered by **Verso's literate renderer**, configured by
[literate.toml](../literate.toml) at the repository root. Verso is
pinned in [lakefile.lean](../lakefile.lean) to the tag matching this project's toolchain and
guarded by `meta if get_config? env = some "dev"`, so a normal `lake build`
neither resolves nor builds it.

The choice is driven by what the models look like. A conventional API
generator such as `doc-gen4` indexes *declarations* and renders their
*docstrings*, and neither half of that fits here:

* Veil's declarations are mostly generated. What a model *is* — its state
  components, actions and properties — is the commands written in the file,
  and a declaration index has no place for a command or for the order the
  commands come in.
* The reasoning is in the module headers, which an index shows once, at the
  top of a module's page, rather than beside the declarations they explain.

A literate renderer shows the file as written, in order: the module headers
render as prose, each doc comment renders in the code with the declaration
it documents — on a Veil command as on any Lean declaration — and the
maintainers' plain comments render with the code they annotate, their inline
markup included, by a small script of this site's
([VersoIssues.md](VersoIssues.md) §6). Nothing in a published module is
invisible.

The site is also far smaller, and all of it is this project. `doc-gen4`
emitted 321 MB here, of which this project's own pages were 6.3 MB; the rest
was Lean core, Batteries and the imported subset of Mathlib, kept so
cross-references resolved. The literate site publishes only this project's
modules: 25 MB, measured 2026-09-29.

### What is published

`literate.toml` selects the library and excludes the three per-action proof
subtrees, the monitor and the tooling; `scripts/docs.sh` prints how many
modules that leaves. The excluded proof files are machine-shaped `#prove_vc` cells whose
content is the VC registry's rather than a reader's; what they establish is
stated by the three `Certify` modules, which are published and which carry the
`#veil_status` pins. `Cadence.Monitor` is excluded because it is not part of
any theorem's trust base ([Monitor.md](Monitor.md)) — and would have to be
anyway, for a reason worth recording: three of its files declare a
root-level `main`, Lean names are global, and the renderer's search index is
keyed by name, so publishing two of them fails the build on the duplicate
document ID. `Cadence.Tooling` is excluded as workflow rather than protocol:
check commands that make the inner loop faster.

Nothing else is. The remaining support modules — the quorum instance, the
ACS median lemma, the counting and pigeonhole arguments, the build-totality
proof — are technical in their *proofs*, but each states a protocol-level
claim in its header, which is what an auditor reads; the proofs themselves
are dealt with below. The same file fixes the reading order and the two page
titles that the module name does not supply.

### The proofs are not published; the statements and the prose are

Verso records the goal at every tactic step and renders each one. For this
development that is both wrong for the reader — the site's own first
paragraph tells them they do not need to read a proof — and ruinous for the
page: a goal over a forty-field state record is enormous, and
`Cadence.Mvba.Compose` came to **47 MB from 360 lines of source**, with
`Cadence.Composition` at 13 MB, two thirds of the whole site between them.

There is no configuration key for it, so `scripts/docs.sh` removes them from
the renderer's own intermediate JSON with one `jq` filter, between Verso's
two stages: a `tactics` node lists its states in `info`, and emptying that
and dropping the `goals` table removes the proof states and nothing else.
Measured on `Mvba.Compose`: **47 MB → 0.32 MB**, with every declaration,
statement, docstring and comment still present — `mvbaSafety`,
`mvba_of_temporal` and all thirteen `theorem`s unchanged, and the only losses
the 1 870 occurrences of `decided` that were inside hypotheses. Whole site, at the
time: **97 MB → 11 MB**.

This is the same intent as excluding the proof families, applied inside a
module: what an auditor reads is the statement and the reasoning around it,
not the tactic state between two `simp` calls.

### What the Markdown path cannot do

Lean has two docstring languages, chosen by `doc.verso`. Unset — the default
and what this development uses — `/-! … -/` and `/-- … -/` are Markdown, and
Verso's Markdown support in the literate genre is thinner than its support
for its own markup. Four gaps show on these pages: tables are never parsed,
list items are emitted without `<li>`, maths is dropped, and a doc comment
on an anonymous command keeps its opening `/--`. Each is small, each is
still present upstream, and three of the four are worked around here.
[VersoIssues.md](VersoIssues.md) is the record: symptom, cause, the fix,
and which workaround to delete when it lands.

Two consequences worth stating here rather than there. **A block of raw HTML
is passed through verbatim**, so an HTML `<table>` at the left margin of a
header reaches the page — the one route to a real table today that needs no
upstream change. And **maths has no rendering path at all**, so formulas
cannot be written in these docstrings yet; mermaid is not supported by Verso
either, while fenced code blocks are.

The headers use lists of labelled explanations — the label, then what it
says — where a table would hold a paragraph per cell. That reads better in
the source as well as on the page, and needs nothing from upstream.


## What it costs

Three costs are specific to this project and worth knowing before changing
anything here.

* **The renderer re-elaborates every module it publishes.** Highlighting
  needs the elaborator's info trees, which an `.olean` does not carry, so
  having built the project is a precondition rather than a substitute. On
  CI's 4-vCPU runner the 67 published modules take 57 minutes one after
  another; `Cadence.Chorus` is 21 of them on its own, `Cadence.Mvba.Compose`
  and `Cadence.Mvba` about four each, and 57 of the 67 are under a minute
  (run 37593789847, 2026-10-07). Locally the three largest renders peak at
  6.4, 2.6 and 2.3 GB (`Chorus`, `Mvba`, `Mvba.Compose`; 408, 85 and 97 s).
  Two things keep this off the critical path:
  * *Renders run `JOBS` at a time*, largest first (default 2; CI uses 2,
    which keeps `Chorus` and its companion inside the 13 GB container with
    room to spare). The `Chorus` render is then the floor.
  * *A rendering is reused while its inputs are unchanged.* Each module's
    JSON carries a key: lake's own input hash for the module (its source,
    the toolchain, every imported `.olean` by content), the source's hash,
    the renderer binary's hash, and the text of the script's filters. Only a
    module whose key changed is rendered again, so a commit that touches no
    Lean source renders nothing, and one that touches a leaf module renders
    that module. CI carries the renderings between runs in an
    `actions/cache` entry; the key, not the entry, decides what is reused.

  Locally (2026-10-07), a full `scripts/docs.sh` with `JOBS=2` and nothing
  to reuse took 12.5 minutes, `Chorus` 7.3 of them; run again, with all 67
  renderings reused, 1.4 minutes, and the same site.
* **The guide computes its status boxes from the environment while it
  builds**, so a per-element cost multiplies by the number of elements. An
  element that walks the environment walks this development's modules only
  (`providersOf` in [Audit.lean](guide/CadenceGuide/Audit.lean) says why);
  the whole guide builds in about 20 s locally.
* **`scripts/docs.sh` refuses to start unless the project is up to date**
  (`lake build --no-build`). That is a hard gate, not a convenience: the
  rendering stage runs with `VEIL_NO_VERIFY=1`, and an out-of-date module
  rebuilt under that variable would put an unverified `.olean` in the build
  tree. Checking first makes that impossible.

## Why the script, and not the one-liner

`lake query :literateHtml` is Verso's documented one-line way to build this
site, and it *does* work on this project — verified, 97 MB of rendered
output. `scripts/docs.sh` drives Verso's three binaries itself for one
reason only: the `jq` passes have to run between the rendering stage and the
HTML stage, and the facet does both in a single job. Everything else is
Verso's — the planner and the HTML renderer are its executables, and
`literate.toml` governs both, so the configuration surface stays the
documented one.

The shape of the stage is determined by two properties of this development.

* **The renderer has no native plugins.** `verso-literate` re-elaborates a
  module in its own process, without the cvc5, lean-smt, lean-auto and Qq
  plugins that lake passes when it builds a module itself, so a module that
  reaches a solver call dies with `Could not find native implementation of
  external declaration 'cvc5.TermManager.new'` — `SIGABRT`, no Lean
  diagnostic. This is the same trap `scripts/scratch.sh` exists to avoid
  ([CLAUDE.md](../CLAUDE.md), Build). `VEIL_NO_VERIFY=1` is the answer, and it is the
  right one independently: a documentation pass should not re-run the
  solver, and verification has already happened — stage 0 insists on it.

* **Veil's VC manager loop does not end by itself.** `#gen_spec` starts it
  and `verso-literate` ends by joining every worker thread, so a renderer
  that ran the loop would wait on it forever (`lean` exits the process
  outright and never notices). The pinned fork does not start the loop under
  `veil.noVerify`, since nothing could ever wake it there
  ([Dependencies.md](Dependencies.md) §6), which is what makes stage 2 a
  plain foreground run.


## Building it

```bash
lake build                                 # or scripts/revalidate.sh
scripts/docs.sh                            # natively; site lands in ./site
RUNTIME=podman scripts/container.sh docs   # in the verified image; also ./site
```

The site's internal links are directory-style, so browse it over a server
rather than from the filesystem:

```bash
python3 -m http.server -d site
```

In CI the `docs` workflow runs it inside the `cadence-verified` image, which
already holds the `.olean`s, and publishes the result to GitHub Pages. It runs
after `publish-images` has published that image for the same commit, not on
the push: the site can only render a commit whose oleans are in the image.

Verso also ships `lake exe verso setup-literate`, which generates a GitHub
Pages workflow of its own. It is not used: it builds the project from source
on a hosted runner, which for this development is the multi-hour `verify`
job rather than a documentation build. The existing `docs` workflow starts
from the published image instead.
