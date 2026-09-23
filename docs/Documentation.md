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
stated by
the three `Certify` modules, which are published and which carry the
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

**The Veil-side fix exists and is tested; it is not yet pinned.** Under
`veil.noVerify` the manager loop has nothing to do *and* nothing that could
ever wake it, so `runManager` should not start it — three lines in the
fork's `Verifier/Server.lean`, plus the correction that `vcServerStarted` is
only set when the loop really was started. Verified as a controlled
experiment on a 52-line Veil model, with no part of this project involved:
unpatched, `verso-literate` was still running after 93 s; patched, it exited
of its own accord in 5 s with the same 27-item output.

Landing it means pushing the fork branch and bumping the pin, which
re-verifies the whole development — a dependency bump rather than a
documentation change, so it is deliberately not folded into this one. When it
lands, stage 2 collapses to `lake query :literateHtml` and the wait-and-reap
loop goes; the `jq` filter stays, because it is about what the site should
show rather than about a defect. (`scripts/docs.sh` already tolerates a
renderer that exits on its own — it judges each module by whether the
artefact parses, not by how the poll loop ended.)

The other half could instead be fixed upstream in Verso, by exiting the
process rather than joining the task manager; that would help any Lean
library with a long-running background task, not just Veil.

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
