# The rendered documentation site

*How the Lean sources are published as a browsable site, what is on it, and
what it is worth as evidence. For what is proven, read
[`../README.md`](../README.md); this document is about the rendering.*

## Why

Most of this development's explanation lives in the Lean sources — the long
`/-! … -/` headers that state each model's scope, its abstractions, and how
each of the paper's properties is covered. In a text editor those headers are
Markdown source, and GitHub does not render them either. The site renders
them, links every declaration to its definition, and adds the one thing the
sources cannot show in one place: the boundary between what the kernel checks
and what is assumed.

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
| `Cadence/*.html` | every module's rendered prose, with each declaration linked to its source line on GitHub |
| `Cadence.html` | the audit root — every end result on one page |

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

## Building it

```bash
scripts/docs.sh                      # natively; site lands in ./site
RUNTIME=podman scripts/container.sh docs   # in the verified image
```

The generator is [doc-gen4](https://github.com/leanprover/doc-gen4), pinned
in `lakefile.lean` to the tag matching this project's toolchain and guarded by
`meta if get_config? env = some "dev"`, so a normal `lake build` neither
resolves nor builds it. Its five dependencies are additive — the only one
this tree already has, `Cli`, is pinned at the same revision — so adding it
moved no existing manifest entry and left the Mathlib cache intact.

Two costs are worth knowing before enabling it in CI.

* **The first run analyses the whole import closure**, Mathlib included,
  because doc-gen4 resolves cross-references across everything a module
  imports. Later runs are incremental: only modules whose hash changed are
  re-analysed.
* **The emitted site is around 400 MB**, of which this project's own pages
  are about 6 MB. The rest is Lean core, Batteries and the imported subset of
  Mathlib — kept, rather than pruned, so that a reviewer clicking through to
  a definition in a dependency lands on a real page.

A third cost is cosmetic but worth knowing: doc-gen4 panics, non-fatally and
once per declaration, on anything that carries no source position — which is
most of what Veil generates (state projections, enum instances). About 265
declarations are affected. They are **dropped** from the output rather than
rendered wrongly, and they are Veil internals rather than anything an auditor
reads, so the practical impact is nil; but at roughly 300 backtraces the noise
buries real errors, so `scripts/docs.sh` summarises it and prints the count.
Fixing it properly belongs upstream — a projection of a positionless structure
should be skipped, as declarations without ranges already are.

`scripts/docs.sh` needs the project built, since doc-gen4 reads `.olean`s
rather than re-elaborating sources. In CI the `docs` workflow runs it inside
the `cadence-verified` image, which already holds them, so the job costs
doc-gen4's own build plus one analysis pass — not a re-verification.

## What it does not do

The generator renders **docstrings**: `/-! … -/` module docs and `/-- … -/`
declaration docs. Plain `/- … -/` block comments and `--` line comments are
invisible to it, and this development has about 1 750 lines of those —
roughly a fifth of its Lean prose, concentrated in the per-action and
per-relation commentary of the model files, because a `/-- … -/` docstring
before a Veil `action` breaks the parser (`CLAUDE.md`, hard rules).

That is recoverable and has been checked: a `/-! … -/` *module* docstring is
a standalone command, parses immediately before a Veil declaration, and is
rendered in source order. Converting those comments would lift what the site
shows from roughly four fifths of the prose to nearly all of it. It is
mechanical, file by file, and has not been done.
