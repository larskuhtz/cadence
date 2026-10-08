import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `aggregate_fastqc_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `aggregate_fastqc_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus aggregate_fastqc_pos <property> by <tac>` lines
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

/- Manual discharge of the one VC of this action whose
quorum-intersection chain cvc5's e-matching cannot find automatically:
two applications of the `ByzNodeSet` counting axioms against the
explicitly witnessed quorums, closed by the recorded backing invariants.
The cell restates the canonical VC statement from the registry, so the
`#prove_action` below consumes it as-is after a statement check; the
invariant conjuncts it needs are named, not indexed
(`veil_inv_have`). -/
#prove_vc Chorus aggregate_fastqc_pos spec_fastqc_pos_mvba_pos_unique by
  unveil_local
  veil_inv_have h_mvba_decided_pos_backed := mvba_decided_pos_backed
  veil_inv_have h_msg_fb_pos_sig_backed := msg_fb_pos_sig_backed
  veil_inv_have h_spec_fastqc_pos_mvba_pos_unique := spec_fastqc_pos_mvba_pos_unique
  intro _hbyz_i hsup_q hq_sigs _hfresh hne1 hne2 hne3 hnie I J M M' hbyz_I hfq hmv
  by_cases hnew : i = I ∧ j = J ∧ m = M
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    rcases h_mvba_decided_pos_backed j M' hmv with ⟨Q2, hQ2_sup, hQ2⟩ | ⟨⟨qf, hqf_gtt, hqf⟩, -⟩
    · obtain ⟨a, ha1, ha2, -⟩ := nset.supermajorities_intersect_in_honest q Q2 hsup_q hQ2_sup
      exact hne1 a j m M' (hq_sigs a ha1) (hQ2 a ha2)
    · obtain ⟨rf, hrf_mem, hrf_hon⟩ := nset.greater_than_third_one_honest qf hqf_gtt
      have hrf_hon' : ByzNodeSet.is_byz rf = false := Bool.eq_false_iff.mpr hrf_hon
      obtain ⟨qv2, hqv2_gtt, hqv2⟩ := h_msg_fb_pos_sig_backed rf j M' hrf_hon' (hqf rf hrf_mem)
      obtain ⟨b, hb1, hb2⟩ := cnt.supermajority_meets_third q qv2 hsup_q hqv2_gtt
      exact hne1 b j m M' (hq_sigs b hb1) (hqv2 b hb2)
  · have hold : st.local_fastqc_pos I J M = true := hfq (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩)
    exact h_spec_fastqc_pos_mvba_pos_unique hne1 hne2 hne3 hnie I J M M' hbyz_I hold hmv

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus aggregate_fastqc_pos speculative_agreement_pos_neg by
  unveil_local
  veil_inv_have h_old := speculative_agreement_pos_neg
  veil_inv_have h_cnb := local_committed_neg_backed
  veil_inv_have h_nvotes := msg_commitqc_neg_votes
  veil_inv_have h_mdnb := mvba_decided_neg_backed
  veil_inv_have h_vupn := vote_unique_pos_neg
  veil_inv_have h_fbn := fb_neg_no_pos_quorum
  intro _hbyz hq_sup hq _hfresh hne1 hne2 hne3 hnie I1 I2 J M h1 h2 hpost
  by_cases hnew : i = I1 ∧ j = J ∧ m = M
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    -- The FastQC's vote supermajority `q` against every source of a negative
    -- commit for `j`.
    cases hc : st.local_committed_neg I2 j
    · rfl
    · exfalso
      have neg_quorum : ∀ Qn, nset.supermajority Qn →
          (∀ r, nset.member r Qn = true → st.msg_vote_neg_sig r j = true) → False := by
        intro Qn hQn_sup hQn
        obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest q Qn hq_sup hQn_sup
        have hx := h_vupn b j m (Bool.eq_false_iff.mpr hb_hon) (hq b hb1)
        have hy := hQn b hb2
        rw [hx] at hy; simp at hy
      rcases h_cnb I2 j h2 hc with ⟨C, hC⟩ | haux
      · obtain ⟨Qn, hQn_sup, hQn⟩ := h_nvotes C j hC
        exact neg_quorum Qn hQn_sup hQn
      · rcases h_mdnb j haux with ⟨Qn, hQn_sup, hQn⟩ | ⟨⟨qn, hqn_gtt, hqn⟩ | ⟨m1, m2, hm12, hp1, hp2⟩, -⟩
        · exact neg_quorum Qn hQn_sup hQn
        · obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest qn hqn_gtt
          obtain ⟨b, hb, hb_false⟩ :=
            h_fbn hne1 hne2 hne3 hnie a j m (Bool.eq_false_iff.mpr ha_hon) (hqn a ha_mem) q hq_sup
          have hy := hq b hb
          rw [hb_false] at hy; simp at hy
        · exact hm12 (hne3 j m1 m2 hp1 hp2)
  · exact h_old hne1 hne2 hne3 hnie I1 I2 J M h1 h2 (hpost (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩))

#prove_action Chorus aggregate_fastqc_pos

end Chorus.Proofs
