import Lake
open Lake DSL

/-! # Cadence — machine-checked verification

Standalone Lean 4 project holding the formal verification of the **Cadence**
BFT consensus protocol: the per-slot consensus **Chorus**, the window-based
orchestrator **Conductor**, the pipelining **Cadence** layer that composes
them, and the fallback receipt/propose layer.

Everything lives in one library, `Cadence`, whose root module
[Cadence.lean](./Cadence.lean) is the audit entry point: it imports every
end result and re-derives each one's axiom footprint as a build-checked pin.
So `lake build` verifies the whole development, and a red build means a
broken claim. Reading order and the trust story: [README.md](./README.md).

## Dependencies

The single direct dependency is a public Veil fork, which pins the rest of
the tree (Loom, lean-smt, Mathlib). What the fork carries beyond upstream
Veil, and why this project needs it, is in
[docs/Dependencies.md](./docs/Dependencies.md). -/

/- No package-level `leanOptions`: every Veil option this project depends on
is set *in the file that needs it*, next to the reasoning for it — proof
reconstruction (`veil.smt.trust false`), the VC registry, the proof cache,
and the two Chorus-only code-generation switches. Solver options are captured
when a module elaborates its specification, so a package-level default would
be a second, invisible place to look. -/
package «cadence»

/- Loom's own lakefile declares case-study libraries that cannot build at its
Veil-support revision, and whose globs overlap the core library — so any
consumer that precompiles modules resolves Loom's modules to that library and
fails on its missing imports. The branch below is a lakefile-only fix; a root
`require` shadows transitive ones, which is why this line comes first.
See [docs/Dependencies.md](./docs/Dependencies.md). -/
require Loom from git "https://github.com/larskuhtz/loom" @ "v4.32.0-for-veil-lakefile-fix"

require veil from git "https://github.com/larskuhtz/veil" @ "port/integration"

/- The documentation generator, behind a config flag so it never enters the
normal build: `lake build` neither resolves nor builds it. Rendering the docs
is `lake -Kenv=dev build Cadence:docs`, which `scripts/docs.sh` wraps.

It is pinned to the tag matching this project's toolchain. Its five
dependencies are additive — the only one this tree already has, `Cli`, is
pinned at the same revision — so adding it changes no existing manifest entry
and leaves the Mathlib cache intact. -/
meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.32.0"

/- The guide (`docs/guide/`, rendered by `scripts/guide.sh`) is a Verso
document: a Lean program, so its code examples elaborate and its references to
this development's declarations are resolved at build time. A renamed
declaration breaks the guide's build rather than rotting a link.

Behind the same `-Kenv=dev` flag as the documentation generator, and pinned to
the tag matching this toolchain. Its four dependencies are additive: `plausible`
and `MD4Lean` are already in this tree at the same revisions. -/
meta if get_config? env = some "dev" then
require verso from git "https://github.com/leanprover/verso" @ "v4.32.0"

/- The guide itself: a Verso document under `docs/guide/`, built by
`scripts/guide.sh`, behind `-Kenv=dev` so a normal `lake build` does not see
it.

Deliberately a library and not a `lean_exe`. The document imports the
development — that is what makes its cross-references checked — so linking it
into an executable would drag the whole closure, Mathlib included, through
native compilation. The renderer is therefore run on the Lean **interpreter**,
exactly as `Cadence/Monitor/` is (`docs/Monitor.md`): no compiled binary, and
no `.c.o.export` objects to build. -/
meta if get_config? env = some "dev" then
lean_lib CadenceGuide where
  srcDir := "docs/guide"
  roots := #[`CadenceGuide]

/-- The whole development: models, per-action proof families, composition
certificates, end theorems, and the model-conformance monitor.

`lake build` schedules the 41 + 10 + 25 per-action proof files in parallel and a
*cold* proof file peaks around 5 GB, so on a machine with less than ~64 GB
build in batches first — [scripts/revalidate.sh](./scripts/revalidate.sh)
does exactly that staging, and the [README](./README.md) spells it out. -/
@[default_target]
lean_lib Cadence where
  globs := #[`Cadence, .submodules `Cadence]
