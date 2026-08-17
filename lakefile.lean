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

Both dependencies are pinned to public forks; what each fork carries beyond
its upstream, and why this project needs it, is in
[docs/Dependencies.md](./docs/Dependencies.md). -/

/- No package-level `leanOptions`: every Veil option this project depends on
is set *in the file that needs it*, next to the reasoning for it — proof
reconstruction (`veil.smt.trust false`), the VC registry, the proof cache,
and the two Chorus-only code-generation switches. Solver options are captured
when a module elaborates its specification, so a package-level default would
be a second, invisible place to look. -/
package «cadence»

/- Veil's own transitive Loom pin (`verse-lab/loom @ upgrade-v4.28`) has a
lakefile that cannot be built by a consumer which precompiles modules: it
declares case-study libraries importing a module that branch's core-only
toolchain bump dropped, and their globs overlap the core library. The fork
branch below is a lakefile-only fix. A root `require` shadows transitive
ones, which is why this line comes first. -/
require Loom from git "https://github.com/larskuhtz/loom" @ "upgrade-v4.28-lakefile-fix"

require veil from git "https://github.com/larskuhtz/veil" @ "port/integration"

/-- The whole development: models, per-action proof families, composition
certificates, end theorems, and the model-conformance monitor.

`lake build` schedules the 39 + 10 per-action proof files in parallel and a
*cold* proof file peaks around 5 GB, so on a machine with less than ~64 GB
build in batches first — [scripts/revalidate.sh](./scripts/revalidate.sh)
does exactly that staging, and the [README](./README.md) spells it out. -/
@[default_target]
lean_lib Cadence where
  globs := #[`Cadence, .submodules `Cadence]
