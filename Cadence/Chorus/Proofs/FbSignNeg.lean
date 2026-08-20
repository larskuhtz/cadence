import Cadence.Chorus

/-! # `Chorus` proofs — action `fb_sign_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `fb_sign_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus fb_sign_neg <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path). -/

open Veil Chorus

set_option veil.smt.trust false
-- Mirror Chorus.lean's elaboration budgets (the 97-conjunct clump needs them).
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
-- Proof cache: consume entries earlier solves stored (kernel-replayed on
-- hit, `veil.cache.kernelReplay`); store fresh solves for the next rebuild.
set_option veil.cache.proofs true
-- A kernel-replay hit consumes a manual `#prove_vc … by <tac>` cell at the
-- command level and never elaborates the `by` suffix; the unreachable-/
-- unused-tactic linters would flag that (by design here).
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Chorus.Proofs

/- This file carried three preproven manual theorems until 2026-08-19
(`fb_sign_neg` x `inclusion_no_honest_fb_neg` / `fb_neg_qv_no_pos_quorum` /
`fb_neg_no_pos_quorum`): under the pre-`well_encoded` guard their queries
were e-matching-divergent. The `well_encoded` refactor (audit Finding 1)
changed the query shapes and cvc5 now solves all three directly -- the
`no_invalid_encoding` hypothesis supplies the signed-root-is-well-encoded
bridge as an explicit premise, which is exactly the instantiation the old
encoding could not trigger (measured 6.2-17.0 s against the 60 s budget).
If a future statement change re-diverges them, put fresh manual cells on
`#prove_vc Chorus fb_sign_neg <property> by <tac>` lines before the
`#prove_action`, statements regenerated from the failing cells' output. -/

#prove_action Chorus fb_sign_neg

end Chorus.Proofs
