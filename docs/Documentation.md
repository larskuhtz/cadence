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
module is invisible. `docstrings_as_text` is set, so a `/-- … -/` docstring
becomes a paragraph before the declaration rather than a box inside the
listing — which is what makes a model read as the document it is.

The site is also smaller, and all of it is this project. `doc-gen4` emitted
321 MB here, of which this project's own pages were 6.3 MB; the rest was
Lean core, Batteries and the imported subset of Mathlib, kept so
cross-references resolved. The literate site is 97 MB and publishes only
this project's modules.

### What is published

`literate.toml` selects the library and excludes the three per-action proof
subtrees and the monitor, which leaves 25 of the 106 modules. The 76
excluded proof files are machine-shaped `#prove_vc` cells whose content is
the VC registry's rather than a reader's; what they establish is stated by
the three `Certify` modules, which are published and which carry the
`#veil_status` pins. `Cadence.Monitor` is excluded because it is not part of
any theorem's trust base ([Monitor.md](./Monitor.md)) — and would have to be
anyway, for a reason worth recording: three of its files declare a
root-level `main`, Lean names are global, and the renderer's search index is
keyed by name, so publishing two of them fails the build on the duplicate
document ID. The same file fixes the reading order and the two page titles
that the module name does not supply.

### Page sizes

Verso renders the proof state at every tactic step, which for this
development is the one thing that does not scale. The pages an auditor reads
are small — `Chorus` is 0.9 MB, `Interfaces` 0.6 MB, and every other model is
under half a megabyte — but the hand-written proof files are not, because a
goal over a forty-field state record is large and there are hundreds of
them. `Cadence.Mvba.Compose` is 47 MB from 360 lines of source, and
`Cadence.Composition` 13 MB; between them they are two thirds of the site.

There is no configuration key for this, and the tactic states are emitted
unconditionally by Verso's highlighter. It has been measured rather than
guessed: dropping the *hypotheses* from each goal, and keeping the
conclusion, takes `Mvba.Compose` from 47 MB to 10 MB. Doing that would mean
rewriting Verso's intermediate JSON between its own two stages, which is
exactly the kind of bespoke coupling using the documented configuration
avoids — so it is **not** done here, and the right fix is an upstream
option. The heavy pages are the proof files, which this site tells the
reader they do not need to read.

## What it costs

Two costs are specific to this project and worth knowing before changing
anything here.

* **The renderer re-elaborates every module it publishes.** Highlighting
  needs the elaborator's info trees, which an `.olean` does not carry, so
  having built the project is a precondition rather than a substitute. The
  25 published modules take about nine minutes in total, and `Cadence.Chorus`
  is 198 s of that on its own, at a peak around 10 GB; most of the rest are
  under ten seconds each. Rendering is serial for that reason.
* **`scripts/docs.sh` refuses to start unless the project is up to date**
  (`lake build --no-build`). That is a hard gate, not a convenience: the
  rendering stage runs with `VEIL_NO_VERIFY=1`, and an out-of-date module
  rebuilt under that variable would put an unverified `.olean` in the build
  tree. Checking first makes that impossible.

## Two workarounds, and where they belong

`lake query :literateHtml` is Verso's documented one-line way to build this
site, and it is not what `scripts/docs.sh` runs. Two properties of this
development get in the way; both are recorded here because the script's
shape is otherwise inexplicable, and both are fixable upstream rather than
here.

* **No native plugins.** `verso-literate` re-elaborates a module in its own
  process, without the cvc5, lean-smt, lean-auto and Qq plugins that lake
  passes when it builds a module itself. A module that calls the solver
  therefore dies with `Could not find native implementation of external
  declaration 'cvc5.TermManager.new'` — `SIGABRT`, no Lean diagnostic. This
  is the same trap `scripts/scratch.sh` exists to avoid
  (`CLAUDE.md`, Build). `VEIL_NO_VERIFY=1` is the answer here, and it is the
  right one independently: a documentation pass should not re-run the
  solver, and verification has already happened.

* **Veil's VC manager never terminates.** `#gen_spec` starts a manager loop
  that is infinite by design and deliberately not registered as a snapshot
  task — "the manager loop is infinite, so registering it would hang the
  build", in Veil's own `Verifier/Server.lean`. Lean's frontend exits
  without joining it; `verso-literate` ends by joining every worker thread,
  so on any Veil model it waits forever. The JSON is complete before that
  happens — the renderer writes it inside `IO.FS.withFile`, which closes and
  flushes the handle before returning — so `scripts/docs.sh` waits for the
  file to parse and then reaps the process.

  That is why the script drives Verso's three binaries itself: the facet's
  own invocation would hang with no way to intervene. Everything else is
  Verso's — the planner and the HTML renderer are its executables, and
  `literate.toml` governs both, so the configuration surface is the
  documented one.

The proper fix is one of two upstream changes: a Veil manager loop that
terminates, or a `verso-literate` that exits without joining. The first
belongs in the Veil fork ([Dependencies.md](./Dependencies.md) records what
this project needs from it); the second is a plain upstream bug — any Lean
library with a long-running background task deadlocks the renderer the same
way. Until one lands, the wait-and-reap loop is the shape.

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
