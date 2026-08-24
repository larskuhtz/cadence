import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `byz_release_msg_decrypt_share`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `byz_release_msg_decrypt_share` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus byz_release_msg_decrypt_share <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared blocks from
`Cadence/ProofPrelude.lean` record what each of the other options is
for. -/

open Veil Chorus

-- The no-trusted-solver rule (README.md) stays written out per proof file so
-- it remains greppable; the shared blocks below are defined and documented
-- in `Cadence/ProofPrelude.lean`.
set_option veil.smt.trust false
veil_proof_options
veil_large_clump_budgets

namespace Chorus.Proofs

#prove_action Chorus byz_release_msg_decrypt_share

end Chorus.Proofs
