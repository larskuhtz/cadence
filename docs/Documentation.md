# The rendered documentation site

*How the Lean sources are published as a browsable site, what is on it, and
what it is worth as evidence. For what is proven, read
[`../README.md`](../README.md); this document is about the rendering.*

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
([Container.md](./Container.md) §4). The single exception is deliberate: the
build fails if any end result's axiom footprint has drifted, so a broken pin
cannot be published quietly.

## What is on it

| Page | Content |
|---|---|
| `index.html` | the three questions an auditor asks, each linked to where it is answered |
| `trust-boundary.html` | **generated from the compiled environment**: the axiom footprint of every end result, the axioms this development declares, and which module contracts have no instance |
| `sources/` | every published module rendered in source order — prose, declarations and the code between them — with a name-and-docs search box and a hierarchical navigation bar |

The trust-boundary page is the part worth explaining. It is produced by
[`../scripts/TrustSurface.lean`](../scripts/TrustSurface.lean), which walks
the `.olean`s that `lake build` produced and computes, rather than restates:

* **the axiom footprint of each end result**, via the same mechanism as
  `#print axioms` — the expected set is Lean's three standard classical
  axioms, and anything else fails the build;
* **the axioms this development declares** (none), so that no result in the
  first table is satisfied by an assumption introduced here;
* **which contracts have an instance**, in three states that the page is
  careful to distinguish — *proven* outright, *proven relative to* another
  contract that is itself assumed, and *no instance*, which is what
  "unproven" means. The four `…Temporal` classes and `ACSSafety` are in the
  last state, and that is the whole of what this development owes
  ([CompositionContracts.md](./CompositionContracts.md) §5).

Because it is derived, a claim that has drifted from the code cannot survive
a rebuild of the page.

## The renderer, and why this one

The sources are rendered by **Verso's literate renderer**, configured by
[`../literate.toml`](../literate.toml) at the repository root. Verso is
pinned in `lakefile.lean` to the tag matching this project's toolchain and
guarded by `meta if get_config? env = some "dev"`, so a normal `lake build`
neither resolves nor builds it.

The choice is driven by what the models look like. A conventional API
generator — `doc-gen4`, which this site used first — indexes *declarations*
and renders their *docstrings*. Neither half of that fits here:

* Veil's declarations are mostly generated, and Veil generates them without
  source positions, which `doc-gen4` cannot place on a page.
* The prose that matters is not attached to declarations. Roughly a fifth of
  the Lean prose sits in plain `/- … -/` block comments, because the hard
  rule is that a `/-- … -/` docstring before a Veil `safety`/`invariant`/
  `action` breaks the parser (`CLAUDE.md`). A docstring-indexed renderer
  cannot see any of it.

A literate renderer has no such gap: it shows the file as written, in order,
so the module headers render as prose and the commentary between
declarations renders with the code it belongs to. Nothing in a published
module is invisible. Declaration docstrings stay in the code beside what
they document, which is where this development's short field annotations
belong; the prose that carries the reasoning is in the `/-! … -/` module
headers and renders as prose either way.

The site is also far smaller, and all of it is this project. `doc-gen4`
emitted 321 MB here, of which this project's own pages were 6.3 MB; the rest
was Lean core, Batteries and the imported subset of Mathlib, kept so
cross-references resolved. The literate site is **11 MB** and publishes only
this project's modules.

### What is published

`literate.toml` selects the library and excludes the three per-action proof
subtrees, the monitor and the tooling, which leaves 24 of the 106 modules.
The 76 excluded proof files are machine-shaped `#prove_vc` cells whose
content is the VC registry's rather than a reader's; what they establish is
stated by the three `Certify` modules, which are published and which carry the
`#veil_status` pins. `Cadence.Monitor` is excluded because it is not part of
any theorem's trust base ([Monitor.md](./Monitor.md)) — and would have to be
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
the 1 870 occurrences of `decided` that were inside hypotheses. Whole site:
**97 MB → 11 MB**, largest page 0.9 MB.

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
[VersoIssues.md](./VersoIssues.md) is the record: symptom, cause, the fix,
and which workaround to delete when it lands.

Two consequences worth stating here rather than there. **A block of raw HTML
is passed through verbatim**, so an HTML `<table>` at the left margin of a
header reaches the page — the one route to a real table today that needs no
upstream change. And **maths has no rendering path at all**, so formulas
cannot be written in these docstrings yet; mermaid is not supported by Verso
either, while fenced code blocks are.

The tables that used to be in these headers are gone, and not because the
renderer could not draw them. There were eleven; ten had cells of 113 to 550
characters, which is a paragraph in a column, and only one was genuinely
tabular. They were lists of labelled explanations wearing table syntax, so
they are lists now — the label, then what it says — which reads better in
the source as well as on the page, and needs nothing from upstream. The
conversion was mechanical, cell by cell, and checked by comparing the word
counts of every removed row against the bullets that replaced them.


## What it costs

Two costs are specific to this project and worth knowing before changing
anything here.

* **The renderer re-elaborates every module it publishes.** Highlighting
  needs the elaborator's info trees, which an `.olean` does not carry, so
  having built the project is a precondition rather than a substitute. The
  24 published modules take about nine minutes in total, and `Cadence.Chorus`
  is around 200 s of that on its own, at a peak near 10 GB; most of the rest
  are under ten seconds each. Rendering is serial for that reason.
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

That it works at all took a fix in Veil, and the shape of the stage is still
determined by two properties of this development.

* **The renderer has no native plugins.** `verso-literate` re-elaborates a
  module in its own process, without the cvc5, lean-smt, lean-auto and Qq
  plugins that lake passes when it builds a module itself, so a module that
  reaches a solver call dies with `Could not find native implementation of
  external declaration 'cvc5.TermManager.new'` — `SIGABRT`, no Lean
  diagnostic. This is the same trap `scripts/scratch.sh` exists to avoid
  (`CLAUDE.md`, Build). `VEIL_NO_VERIFY=1` is the answer, and it is the
  right one independently: a documentation pass should not re-run the
  solver, and verification has already happened — stage 0 insists on it.

* **Veil's VC manager used to never terminate.** `#gen_spec` started a
  manager loop that is infinite by design, and `verso-literate` ends by
  joining every worker thread, so it hung on every Veil model; `lean` never
  noticed because it exits the process outright. Fixed at source rather than
  worked around: the pinned fork does not start that loop under
  `veil.noVerify`, since nothing could ever wake it there
  ([Dependencies.md](./Dependencies.md) §6). That is what makes stage 2 a
  plain foreground run.


## Building it

```bash
lake build                                 # or scripts/revalidate.sh
scripts/docs.sh                            # natively; site lands in ./site
RUNTIME=podman scripts/container.sh docs   # in the verified image
```

The site's internal links are directory-style, so browse it over a server
rather than from the filesystem:

```bash
python3 -m http.server -d site
```

In CI the `docs` workflow runs it inside the `cadence-verified` image, which
already holds the `.olean`s, and publishes the result to GitHub Pages.

Verso also ships `lake exe verso setup-literate`, which generates a GitHub
Pages workflow of its own. It is not used: it builds the project from source
on a hosted runner, which for this development is the multi-hour `verify`
job rather than a documentation build. The existing `docs` workflow starts
from the published image instead.
