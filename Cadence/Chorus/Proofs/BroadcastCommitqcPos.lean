import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `broadcast_commitqc_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `broadcast_commitqc_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus broadcast_commitqc_pos <property> by <tac>` lines
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

#prove_vc Chorus broadcast_commitqc_pos commitqc_pos_mvba_consistent by
  unveil_local
  veil_inv_have h_commit_pos_sig_from_local_fastqc := commit_pos_sig_from_local_fastqc
  veil_inv_have h_local_fastqc_pos_backed := local_fastqc_pos_backed
  veil_inv_have h_mvba_decided_pos_backed := mvba_decided_pos_backed
  veil_inv_have h_vote_unique_pos := vote_unique_pos
  veil_inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  veil_inv_have h_commitqc_pos_mvba_consistent := commitqc_pos_mvba_consistent
  intro _hbyz _hpart _hab hsup_q hq _hfresh C J M1 M2 hqc hmv
  by_cases hnew : c = C ∧ j = J ∧ m = M1
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    obtain ⟨a, ha_mem, ha_hon⟩ :=
      nset.greater_than_third_one_honest q (nset.supermajority_greater_than_third q hsup_q)
    have ha_hon' : ByzNodeSet.is_byz a = false := Bool.eq_false_iff.mpr ha_hon
    have ha_fq := h_commit_pos_sig_from_local_fastqc a j m ha_hon' (hq a ha_mem).1
    obtain ⟨Qm, hQm_sup, hQm⟩ := h_local_fastqc_pos_backed a j m ha_hon' ha_fq
    rcases h_mvba_decided_pos_backed j M2 hmv with ⟨Q2, hQ2_sup, hQ2⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
    · obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qm Q2 hQm_sup hQ2_sup
      exact h_vote_unique_pos b j m M2 (Bool.eq_false_iff.mpr hb_hon) (hQm b hb1) (hQ2 b hb2)
    · exfalso
      obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest q qf hsup_q hqf_sup
      have hcf := h_commit_cast_fallback_sig_excl c (Bool.eq_false_iff.mpr hc_hon) (hq c hc1).2
      have hy := hqf c hc2
      rw [hcf] at hy; simp at hy
  · have hold : st.msg_commitqc_pos C J M1 = true := hqc (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩)
    exact h_commitqc_pos_mvba_consistent C J M1 M2 hold hmv


#prove_vc Chorus broadcast_commitqc_pos progress_fallback_signing by
  unveil_local
  veil_inv_have h_progress_fallback_signing := progress_fallback_signing
  intro _hbyz _hpart _hab _hsup_q _hq _hfresh
  exact h_progress_fallback_signing

/- Written out: the solver took over 15 s on this cell locally, too close to
the budget on CI's runner; the new certificate's supermajority meets an old one's in a correct signer, whose commit entry is unique. -/
#prove_vc Chorus broadcast_commitqc_pos commitqc_pos_unique by
  unveil_local
  veil_inv_have h_old := commitqc_pos_unique
  veil_inv_have h_back := msg_commitqc_pos_backed
  veil_inv_have h_cu := commit_pos_sig_unique
  intro _hbyz _hpart _hab hsup hq _hfresh C1 C2 J M1 M2 h1 h2
  have key : ∀ C M2, st.msg_commitqc_pos C j M2 = true → m = M2 := by
    intro C M2 hC
    obtain ⟨Q2, hQ2_sup, hQ2⟩ := h_back C j M2 hC
    obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest q Q2 hsup hQ2_sup
    exact h_cu b j m M2 (Bool.eq_false_iff.mpr hb_hon) (hq b hb1).1 (hQ2 b hb2).1
  by_cases n1 : c = C1 ∧ j = J ∧ m = M1
  · obtain ⟨rfl, rfl, rfl⟩ := n1
    by_cases n2 : c = C2 ∧ m = M2
    · exact n2.2
    · exact key C2 M2 (h2 (fun e1 _ e3 => n2 ⟨e1, e3⟩))
  · by_cases n2 : c = C2 ∧ j = J ∧ m = M2
    · obtain ⟨rfl, rfl, rfl⟩ := n2
      exact (key C1 M1 (h1 (fun e1 e2 e3 => n1 ⟨e1, e2, e3⟩))).symm
    · exact h_old C1 C2 J M1 M2 (h1 (fun e1 e2 e3 => n1 ⟨e1, e2, e3⟩))
        (h2 (fun e1 e2 e3 => n2 ⟨e1, e2, e3⟩))

/- Written out: the solver took over 15 s on this cell locally, too close to
the budget on CI's runner; the new certificate's correct signer holds a FastQC, whose vote supermajority meets a negative MVBA record's evidence in a correct validator. -/
#prove_vc Chorus broadcast_commitqc_pos commitqc_pos_mvba_neg_excl by
  unveil_local
  veil_inv_have h_old := commitqc_pos_mvba_neg_excl
  veil_inv_have h_mdnb := mvba_decided_neg_backed
  veil_inv_have h_cpf := commit_pos_sig_from_local_fastqc
  veil_inv_have h_fqb := local_fastqc_pos_backed
  veil_inv_have h_vupn := vote_unique_pos_neg
  veil_inv_have h_ccf := commit_cast_fallback_sig_excl
  intro _hbyz _hpart _hab hsup hq _hfresh C J M hrow
  by_cases hnew : c = C ∧ j = J ∧ m = M
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    cases hneg : st.aux_mvba_decided_neg j
    · rfl
    · exfalso
      obtain ⟨a, ha_mem, ha_hon⟩ :=
        nset.greater_than_third_one_honest q (nset.supermajority_greater_than_third q hsup)
      have ha' := Bool.eq_false_iff.mpr ha_hon
      obtain ⟨Qm, hQm_sup, hQm⟩ := h_fqb a j m ha' (h_cpf a j m ha' (hq a ha_mem).1)
      rcases h_mdnb j hneg with ⟨Qn, hQn_sup, hQn⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
      · obtain ⟨b, hb1, hb2, hb_hon⟩ :=
          nset.supermajorities_intersect_in_honest Qm Qn hQm_sup hQn_sup
        have hx := h_vupn b j m (Bool.eq_false_iff.mpr hb_hon) (hQm b hb1)
        have hy := hQn b hb2
        rw [hx] at hy; simp at hy
      · obtain ⟨d, hd1, hd2, hd_hon⟩ := nset.supermajorities_intersect_in_honest q qf hsup hqf_sup
        have hcf := h_ccf d (Bool.eq_false_iff.mpr hd_hon) (hq d hd1).2
        have hy := hqf d hd2
        rw [hcf] at hy; simp at hy
  · exact h_old C J M (hrow (fun e1 e2 e3 => hnew ⟨e1, e2, e3⟩))

#prove_action Chorus broadcast_commitqc_pos

end Chorus.Proofs
