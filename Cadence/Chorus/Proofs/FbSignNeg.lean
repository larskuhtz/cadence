import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `fb_sign_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `fb_sign_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus fb_sign_neg <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared blocks from
[ProofPrelude.lean](../../ProofPrelude.lean) record what each of the other options is
for. -/

open Veil Chorus

-- The no-trusted-solver rule ([README.md](../../../README.md)) stays written out per proof file so
-- it remains greppable; the shared blocks below are defined and documented
-- in [ProofPrelude.lean](../../ProofPrelude.lean).
set_option veil.smt.trust false
veil_proof_options
veil_large_clump_budgets

namespace Chorus.Proofs

/- The three hardest cells here — `fb_sign_neg` against
`inclusion_no_honest_fb_neg`, `fb_neg_qv_no_pos_quorum` and
`fb_neg_no_pos_quorum` — are solved directly: the `no_invalid_encoding`
invariant supplies the signed-root-is-well-encoded bridge as an explicit
premise, which is the instantiation cvc5 needs. They are the family's slowest
cells on CI's 4-core runner and what sizes its budget
([ProofPrelude.lean](../../ProofPrelude.lean)); they are *completed* solves,
not divergence. If a statement change makes them diverge, put manual cells on
`#prove_vc Chorus fb_sign_neg <property> by <tac>` lines before the
`#prove_action` ([CLAUDE.md](../../../CLAUDE.md), "Manual cells"). -/

#prove_action Chorus fb_sign_neg

end Chorus.Proofs
