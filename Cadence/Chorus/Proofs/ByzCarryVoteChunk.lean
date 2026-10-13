import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `byz_carry_vote_chunk`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `byz_carry_vote_chunk` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus byz_carry_vote_chunk <property> by <tac>` lines
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

/- Written out: the solver took over 15 s on this cell locally, too close to
the budget on CI's runner; a Byzantine write only adds network rows, so the old witness still backs every correct positive fallback entry. -/
#prove_vc Chorus byz_carry_vote_chunk msg_fb_pos_sig_backed by
  unveil_local
  veil_inv_have h_old := msg_fb_pos_sig_backed
  intro _hbyz R J M hR hfb
  obtain ⟨q, hq, hall⟩ := h_old R J M hR hfb
  exact ⟨q, hq, fun r1 hr1 => ⟨(hall r1 hr1).1, fun _ => (hall r1 hr1).2⟩⟩

#prove_action Chorus byz_carry_vote_chunk

end Chorus.Proofs
