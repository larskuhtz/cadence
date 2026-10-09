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

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus commit_assign_neg_mvba spec_fastqc_pos_no_mvba_neg by
  unveil_local
  veil_inv_have h_old := spec_fastqc_pos_no_mvba_neg
  veil_inv_have h_fqb := local_fastqc_pos_backed
  veil_inv_have h_vupn := vote_unique_pos_neg
  veil_inv_have h_fbn := fb_neg_no_pos_quorum
  intro _hbyz _hpart _hab _hcom _hprop _hmsg _hcert _hval hev _hfresh _hneg hne1 hne2 hne3 hnie
    I J M hI hfq
  refine ⟨?_, h_old hne1 hne2 hne3 hnie I J M hI hfq⟩
  rintro rfl
  -- The bridge's negative evidence against the FastQC's vote supermajority.
  obtain ⟨Qf, hQf_sup, hQf⟩ := h_fqb I j M hI hfq
  rcases hev with ⟨Qn, hQn_sup, hQn⟩ | ⟨⟨qn, hqn_gtt, hqn⟩ | ⟨m1, m2, hm12, hp1, hp2⟩, -⟩
  · obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qf Qn hQf_sup hQn_sup
    have hx := h_vupn b j M (Bool.eq_false_iff.mpr hb_hon) (hQf b hb1)
    have hy := hQn b hb2
    rw [hx] at hy; simp at hy
  · obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest qn hqn_gtt
    obtain ⟨b, hb, hb_false⟩ :=
      h_fbn hne1 hne2 hne3 hnie a j M (Bool.eq_false_iff.mpr ha_hon) (hqn a ha_mem) Qf hQf_sup
    have hy := hQf b hb
    rw [hb_false] at hy; simp at hy
  · exact hm12 (hne3 j m1 m2 hp1 hp2)

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus commit_assign_neg_mvba speculative_agreement_pos_neg by
  unveil_local
  veil_inv_have h_old := speculative_agreement_pos_neg
  veil_inv_have h_fqb := local_fastqc_pos_backed
  veil_inv_have h_vupn := vote_unique_pos_neg
  veil_inv_have h_fbn := fb_neg_no_pos_quorum
  intro _hbyz _hpart _hab _hcom _hprop _hmsg _hcert _hval hev _hfresh _hneg hne1 hne2 hne3 hnie
    I1 I2 J M h1 h2 hfq
  refine ⟨fun _ hjJ => ?_, h_old hne1 hne2 hne3 hnie I1 I2 J M h1 h2 hfq⟩
  subst hjJ
  obtain ⟨Qf, hQf_sup, hQf⟩ := h_fqb I1 j M h1 hfq
  rcases hev with ⟨Qn, hQn_sup, hQn⟩ | ⟨⟨qn, hqn_gtt, hqn⟩ | ⟨m1, m2, hm12, hp1, hp2⟩, -⟩
  · obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qf Qn hQf_sup hQn_sup
    have hx := h_vupn b j M (Bool.eq_false_iff.mpr hb_hon) (hQf b hb1)
    have hy := hQn b hb2
    rw [hx] at hy; simp at hy
  · obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest qn hqn_gtt
    obtain ⟨b, hb, hb_false⟩ :=
      h_fbn hne1 hne2 hne3 hnie a j M (Bool.eq_false_iff.mpr ha_hon) (hqn a ha_mem) Qf hQf_sup
    have hy := hQf b hb
    rw [hb_false] at hy; simp at hy
  · exact hm12 (hne3 j m1 m2 hp1 hp2)

/- The inclusion premise against the bridge: each of the bridge's three
negative witnesses needs a correct validator's negative vote or entry, or
an equivocating correct proposer, and the premise rules each out. The
solver found this cell close to its budget on CI's runner. -/
#prove_vc Chorus commit_assign_neg_mvba proposal_inclusion_no_neg by
  unveil_local
  veil_inv_have h_inclusion_no_honest_vote_neg := inclusion_no_honest_vote_neg
  veil_inv_have h_inclusion_no_honest_fb_neg := inclusion_no_honest_fb_neg
  veil_inv_have h_proposer_unique_root := proposer_unique_root
  veil_inv_have h_pin := proposal_inclusion_no_neg
  intro _hbyz _hpart _hab _hcom _hprop _hmsg _hcert _hval hev _hcp _hcn J I M hbyzJ hpropJ hall hwe hI
  refine ⟨?_, h_pin J I M hbyzJ hpropJ hall hwe hI⟩
  rintro rfl rfl
  rcases hev with ⟨Qn, hQn_sup, hQn⟩ | ⟨harm, -⟩
  · obtain ⟨a, ha_mem, ha_hon⟩ :=
      nset.greater_than_third_one_honest Qn (nset.supermajority_greater_than_third Qn hQn_sup)
    have hx :=
      h_inclusion_no_honest_vote_neg j a M hbyzJ hpropJ hall hwe (Bool.eq_false_iff.mpr ha_hon)
    have hy := hQn a ha_mem
    rw [hx] at hy; simp at hy
  · rcases harm with ⟨qn, hqn_gtt, hqn⟩ | ⟨m1, m2, hm12, hp1, hp2⟩
    · obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest qn hqn_gtt
      have hx :=
        h_inclusion_no_honest_fb_neg j a M hbyzJ hpropJ hall hwe (Bool.eq_false_iff.mpr ha_hon)
      have hy := hqn a ha_mem
      rw [hx] at hy; simp at hy
    · exact hm12 (h_proposer_unique_root j m1 m2 hbyzJ hp1 hp2)

/- Written out: the solver took over 15 s on this cell locally, too close to
the budget on CI's runner; each negative witness needs a correct validator's negative vote or entry, or an equivocating correct proposer. -/
#prove_vc Chorus commit_assign_neg_mvba inclusion_no_mvba_neg by
  unveil_local
  veil_inv_have h_old := inclusion_no_mvba_neg
  veil_inv_have h_nvn := inclusion_no_honest_vote_neg
  veil_inv_have h_nfn := inclusion_no_honest_fb_neg
  veil_inv_have h_pur := proposer_unique_root
  intro _hbyz _hpart _hab _hcom _hprop _hmsg _hcert _hval hev _hcp _hcn J M hbyzJ hpropJ hall hwe
  refine ⟨?_, h_old J M hbyzJ hpropJ hall hwe⟩
  rintro rfl
  rcases hev with ⟨Qn, hQn_sup, hQn⟩ | ⟨harm, -⟩
  · obtain ⟨a, ha_mem, ha_hon⟩ :=
      nset.greater_than_third_one_honest Qn (nset.supermajority_greater_than_third Qn hQn_sup)
    have hx := h_nvn j a M hbyzJ hpropJ hall hwe (Bool.eq_false_iff.mpr ha_hon)
    have hy := hQn a ha_mem
    rw [hx] at hy; simp at hy
  · rcases harm with ⟨qn, hqn_gtt, hqn⟩ | ⟨m1, m2, hm12, hp1, hp2⟩
    · obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest qn hqn_gtt
      have hx := h_nfn j a M hbyzJ hpropJ hall hwe (Bool.eq_false_iff.mpr ha_hon)
      have hy := hqn a ha_mem
      rw [hx] at hy; simp at hy
    · exact hm12 (h_pur j m1 m2 hbyzJ hp1 hp2)

#prove_action Chorus commit_assign_neg_mvba

end Chorus.Proofs
