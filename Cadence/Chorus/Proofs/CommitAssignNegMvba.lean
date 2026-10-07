import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `commit_assign_neg_mvba`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `commit_assign_neg_mvba` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus commit_assign_neg_mvba <property> by <tac>` lines
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

/- The bridge's certificate meets the commit certificate's quorums. The
solver closes this cell only near its budget, so it is written out. -/

#prove_vc Chorus commit_assign_neg_mvba commitqc_pos_mvba_neg_excl by
  unveil_local
  veil_inv_have h_msg_commitqc_pos_votes := msg_commitqc_pos_votes
  veil_inv_have h_vote_unique_pos_neg := vote_unique_pos_neg
  veil_inv_have h_msg_commitqc_pos_backed := msg_commitqc_pos_backed
  veil_inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  veil_inv_have h_commitqc_pos_mvba_neg_excl := commitqc_pos_mvba_neg_excl
  intro _hbyz _hpart _hab _hcom _hprop _hmsg _hcert _hval hev _hfresh _hneg C J M hqc
  refine ⟨?_, h_commitqc_pos_mvba_neg_excl C J M hqc⟩
  rintro rfl
  rcases hev with ⟨Qn, hQn_sup, hQn⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
  · obtain ⟨Qm, hQm_sup, hQm⟩ := h_msg_commitqc_pos_votes C j M hqc
    obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qm Qn hQm_sup hQn_sup
    have hx := h_vote_unique_pos_neg b j M (Bool.eq_false_iff.mpr hb_hon) (hQm b hb1)
    have hy := hQn b hb2
    rw [hx] at hy; simp at hy
  · obtain ⟨Qc, hQc_sup, hQc⟩ := h_msg_commitqc_pos_backed C j M hqc
    obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
    have hcf := h_commit_cast_fallback_sig_excl c (Bool.eq_false_iff.mpr hc_hon) (hQc c hc1).2
    have hy := hqf c hc2
    rw [hcf] at hy; simp at hy

#prove_action Chorus commit_assign_neg_mvba

end Chorus.Proofs
