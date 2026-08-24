import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `fb_sign_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `fb_sign_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus fb_sign_neg <property> by <tac>` lines
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
