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

/- The documentation renderer, behind a config flag so it never enters the
normal build: `lake build` neither resolves nor builds it. Rendering the
sources is `scripts/docs.sh`, configured by `literate.toml`.

Verso's *literate* renderer is what this project uses — not its authoring
genres, and not `doc-gen4`. The reason is what the models look like: their
explanation is prose between declarations, much of it in plain `/- … -/`
block comments, because a `/-- … -/` docstring before a Veil `action` breaks
the parser (`CLAUDE.md`, hard rules). A docstring-indexed API renderer shows
none of that; a literate renderer shows the file, in order, as written.
[docs/Documentation.md](./docs/Documentation.md) has the comparison and the
two costs this choice carries.

It is pinned to the tag matching this project's toolchain. Its three new
dependencies are additive, and the two it shares with this tree — `plausible`
and `MD4Lean` — resolve to the revisions already pinned, so adding it moves
no existing entry and leaves the Mathlib cache intact. -/
meta if get_config? env = some "dev" then
require verso from git "https://github.com/leanprover/verso" @ "v4.32.0"

/-- The whole development: models, per-action proof families, composition
certificates, end theorems, and the model-conformance monitor.

`lake build` schedules the 41 + 10 + 25 per-action proof files in parallel and a
*cold* proof file peaks around 5 GB, so on a machine with less than ~64 GB
build in batches first — [scripts/revalidate.sh](./scripts/revalidate.sh)
does exactly that staging, and the [README](./README.md) spells it out. -/
@[default_target]
lean_lib Cadence where
  globs := #[`Cadence, .submodules `Cadence]
