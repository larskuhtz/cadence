import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `receive_vote_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `receive_vote_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus receive_vote_pos <property> by <tac>` lines
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
the budget on CI's runner; a negative entry's quorum was received in full, so the new receipt is not in it. -/
#prove_vc Chorus receive_vote_pos fb_neg_qv_no_rcv_quorum by
  unveil_local
  veil_inv_have h_old := fb_neg_qv_no_rcv_quorum
  veil_inv_have h_rcvd := fb_neg_qv_received
  intro _hbyz _hj _hc _hsh _hall _hs _hch _hps hnp hnn R J QV q M hR haux hq hall
  apply h_old R J QV q M hR haux hq
  intro r1 hr1
  obtain ⟨hm, hrc⟩ := hall r1 hr1
  refine ⟨hm, hrc ?_⟩
  rintro rfl rfl rfl _
  rcases h_rcvd _ _ _ hR haux _ hm with ⟨M2, hM2⟩ | hn
  · rw [hnp M2] at hM2; simp at hM2
  · rw [hnn] at hn; simp at hn

/- Written out: the solver took over 15 s on this cell locally, too close to
the budget on CI's runner; the new receipt's guard is its backing. -/
#prove_vc Chorus receive_vote_pos vote_rcv_pos_backed by
  unveil_local
  veil_inv_have h_old := vote_rcv_pos_backed
  intro _hbyz _hj hc hsh hall hs _hch _hps _hnp _hnn I R J M hI hrc
  by_cases hnew : i = I ∧ r = R ∧ j = J ∧ m = M
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hnew
    exact ⟨⟨hc, hsh, hall⟩, hs⟩
  · exact h_old I R J M hI (hrc (fun e1 e2 e3 e4 => hnew ⟨e1, e2, e3, e4⟩))

#prove_action Chorus receive_vote_pos

end Chorus.Proofs
