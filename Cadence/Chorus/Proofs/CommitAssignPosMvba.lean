import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `commit_assign_pos_mvba`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `commit_assign_pos_mvba` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus commit_assign_pos_mvba <property> by <tac>` lines
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

#prove_vc Chorus commit_assign_pos_mvba commitqc_neg_mvba_pos_excl by
  unveil_local
  veil_inv_have h_msg_commitqc_neg_votes := msg_commitqc_neg_votes
  veil_inv_have h_vote_unique_pos_neg := vote_unique_pos_neg
  veil_inv_have h_msg_commitqc_neg_backed := msg_commitqc_neg_backed
  veil_inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  veil_inv_have h_commitqc_neg_mvba_pos_excl := commitqc_neg_mvba_pos_excl
  intro _hbyz _hpart _hab _hcom _hprop _hmsg _hcert _hval hev _hfresh _hneg C J M hqc
  refine ⟨?_, h_commitqc_neg_mvba_pos_excl C J M hqc⟩
  rintro rfl rfl
  rcases hev with ⟨-, ⟨Q2, hQ2_sup, hQ2⟩⟩ | ⟨-, -, ⟨qf, hqf_sup, hqf⟩⟩
  · obtain ⟨Qn, hQn_sup, hQn⟩ := h_msg_commitqc_neg_votes C j hqc
    obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Q2 Qn hQ2_sup hQn_sup
    have hx := h_vote_unique_pos_neg b j m (Bool.eq_false_iff.mpr hb_hon) (hQ2 b hb1)
    have hy := hQn b hb2
    rw [hx] at hy; simp at hy
  · obtain ⟨Qc, hQc_sup, hQc⟩ := h_msg_commitqc_neg_backed C j hqc
    obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
    have hcf := h_commit_cast_fallback_sig_excl c (Bool.eq_false_iff.mpr hc_hon) (hQc c hc1).2
    have hy := hqf c hc2
    rw [hcf] at hy; simp at hy

#prove_vc Chorus commit_assign_pos_mvba mvba_decided_pos_chunks_decodable by
  unveil_local
  veil_inv_have h_old := mvba_decided_pos_chunks_decodable
  veil_inv_have h_dec := vote_pos_quorum_implies_decodable
  veil_inv_have h_fb := msg_fb_pos_sig_backed
  intro _hbyz _hpart _hab _hcom _hprop _hmsg _hcert _hval hev _hfresh _hneg J M hpost
  by_cases hnew : j = J ∧ m = M
  · obtain ⟨rfl, rfl⟩ := hnew
    rcases hev with ⟨-, ⟨q, hq_sup, hq⟩⟩ | ⟨-, ⟨qf, hqf_gtt, hqf⟩, -⟩
    · exact h_dec j m q (nset.supermajority_greater_than_third q hq_sup) hq
    · obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest qf hqf_gtt
      obtain ⟨q, hq_gtt, hq⟩ := h_fb a j m (Bool.eq_false_iff.mpr ha_hon) (hqf a ha_mem)
      exact h_dec j m q hq_gtt hq
  · exact h_old J M (hpost (fun h1 h2 => hnew ⟨h1, h2⟩))

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus commit_assign_pos_mvba commitqc_pos_mvba_consistent by
  unveil_local
  veil_inv_have h_msg_commitqc_pos_votes := msg_commitqc_pos_votes
  veil_inv_have h_vote_unique_pos := vote_unique_pos
  veil_inv_have h_msg_commitqc_pos_backed := msg_commitqc_pos_backed
  veil_inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  veil_inv_have h_old := commitqc_pos_mvba_consistent
  intro _hbyz _hpart _hab _hcom _hprop _hmsg _hcert _hval hev _hfresh _hneg C J M1 M2 hqc hmv
  by_cases hnew : j = J ∧ m = M2
  · obtain ⟨rfl, rfl⟩ := hnew
    rcases hev with ⟨-, ⟨Q2, hQ2_sup, hQ2⟩⟩ | ⟨-, -, ⟨qf, hqf_sup, hqf⟩⟩
    · obtain ⟨Qm, hQm_sup, hQm⟩ := h_msg_commitqc_pos_votes C j M1 hqc
      obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qm Q2 hQm_sup hQ2_sup
      exact h_vote_unique_pos b j M1 m (Bool.eq_false_iff.mpr hb_hon) (hQm b hb1) (hQ2 b hb2)
    · exfalso
      obtain ⟨Qc, hQc_sup, hQc⟩ := h_msg_commitqc_pos_backed C j M1 hqc
      obtain ⟨d, hd1, hd2, hd_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
      have hcf := h_commit_cast_fallback_sig_excl d (Bool.eq_false_iff.mpr hd_hon) (hQc d hd1).2
      have hy := hqf d hd2
      rw [hcf] at hy; simp at hy
  · exact h_old C J M1 M2 hqc (hmv (fun h1 h2 => hnew ⟨h1, h2⟩))

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus commit_assign_pos_mvba speculative_agreement_pos by
  unveil_local
  veil_inv_have h_old := speculative_agreement_pos
  veil_inv_have h_fqb := local_fastqc_pos_backed
  veil_inv_have h_vu := vote_unique_pos
  veil_inv_have h_fb := msg_fb_pos_sig_backed
  intro _hbyz _hpart _hab _hcom _hprop _hmsg _hcert _hval hev _hfresh _hneg hne1 hne2 hne3 hnie
    I1 I2 J M1 M2 h1 h2 hfq hpost
  by_cases hnew : i = I2 ∧ j = J ∧ m = M2
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    obtain ⟨Qf, hQf_sup, hQf⟩ := h_fqb I1 j M1 h1 hfq
    rcases hev with ⟨-, ⟨Q2, hQ2_sup, hQ2⟩⟩ | ⟨-, ⟨qf, hqf_gtt, hqf⟩, -⟩
    · obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qf Q2 hQf_sup hQ2_sup
      exact h_vu b j M1 m (Bool.eq_false_iff.mpr hb_hon) (hQf b hb1) (hQ2 b hb2)
    · -- A correct FallbackQC signer saw `f+1` positive votes for `m`; they
      -- meet the FastQC's supermajority, and nobody equivocates.
      obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest qf hqf_gtt
      obtain ⟨q, hq_gtt, hq⟩ := h_fb a j m (Bool.eq_false_iff.mpr ha_hon) (hqf a ha_mem)
      obtain ⟨d, hd1, hd2⟩ := cnt.supermajority_meets_third Qf q hQf_sup hq_gtt
      exact hne1 d j M1 m (hQf d hd1) (hq d hd2)
  · exact h_old hne1 hne2 hne3 hnie I1 I2 J M1 M2 h1 h2 hfq
      (hpost (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩))

#prove_action Chorus commit_assign_pos_mvba

end Chorus.Proofs
