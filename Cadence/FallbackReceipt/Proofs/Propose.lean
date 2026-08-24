import Cadence.FallbackReceipt
import Cadence.ProofPrelude

/-! # `FallbackReceipt` proofs — action `propose`

Scaffolded by `#gen_proof_files FallbackReceipt`; yours to edit. Proves every
registered VC of `propose` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc FallbackReceipt propose <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared block from
`Cadence/ProofPrelude.lean` record what each of the other options is
for. -/

open Veil FallbackReceipt

-- The no-trusted-solver rule (README.md) stays written out per proof file so
-- it remains greppable; the shared block below is defined and documented in
-- `Cadence/ProofPrelude.lean`.
set_option veil.smt.trust false
veil_proof_options

namespace FallbackReceipt.Proofs

#prove_action FallbackReceipt propose

end FallbackReceipt.Proofs
