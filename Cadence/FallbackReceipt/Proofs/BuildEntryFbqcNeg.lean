import Cadence.FallbackReceipt

/-! # `FallbackReceipt` proofs — action `build_entry_fbqc_neg`

Scaffolded by `#gen_proof_files FallbackReceipt`; yours to edit. Proves every
registered VC of `build_entry_fbqc_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc FallbackReceipt build_entry_fbqc_neg <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path). -/

open Veil FallbackReceipt

set_option veil.smt.trust false
-- Proof cache: consume entries earlier solves stored (kernel-replayed on
-- hit, `veil.cache.kernelReplay`); store fresh solves for the next rebuild.
set_option veil.cache.proofs true
-- A kernel-replay hit consumes a manual `#prove_vc … by <tac>` cell at the
-- command level and never elaborates the `by` suffix; the unreachable-/
-- unused-tactic linters would flag that (by design here).
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace FallbackReceipt.Proofs

#prove_action FallbackReceipt build_entry_fbqc_neg

end FallbackReceipt.Proofs
