import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `mvba_decide_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `mvba_decide_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus mvba_decide_pos <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared blocks from
`Cadence/ProofPrelude.lean` record what each of the other options is
for. -/

open Veil Chorus Veil.InvProjection

-- The no-trusted-solver rule (README.md) stays written out per proof file so
-- it remains greppable; the shared blocks below are defined and documented
-- in `Cadence/ProofPrelude.lean`.
set_option veil.smt.trust false
veil_proof_options
veil_large_clump_budgets

namespace Chorus.Proofs

#prove_vc Chorus mvba_decide_pos commitqc_pos_mvba_consistent by
  unveil_local
  inv_have h_msg_commitqc_pos_votes := msg_commitqc_pos_votes
  inv_have h_vote_unique_pos := vote_unique_pos
  inv_have h_msg_commitqc_pos_backed := msg_commitqc_pos_backed
  inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  inv_have h_commitqc_pos_mvba_consistent := commitqc_pos_mvba_consistent
  intro _hphase _hcompl _hprop _hinvoked hev _hagree _hnneg J M1 M2 hqc hmv
  by_cases hnew : j = J ∧ m = M2
  · obtain ⟨rfl, rfl⟩ := hnew
    rcases hev with ⟨Q2, hQ2_sup, hQ2⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
    · obtain ⟨Qm, hQm_sup, hQm⟩ := h_msg_commitqc_pos_votes j M1 hqc
      obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qm Q2 hQm_sup hQ2_sup
      exact h_vote_unique_pos b j M1 m (Bool.eq_false_iff.mpr hb_hon) (hQm b hb1) (hQ2 b hb2)
    · exfalso
      obtain ⟨Qc, hQc_sup, hQc⟩ := h_msg_commitqc_pos_backed j M1 hqc
      obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
      have hcf := h_commit_cast_fallback_sig_excl c (Bool.eq_false_iff.mpr hc_hon) (hQc c hc1).2
      have hy := hqf c hc2
      rw [hcf] at hy; simp at hy
  · have hmv' : st.mvba_decided_pos J M2 = true := hmv (fun h1 h2 => hnew ⟨h1, h2⟩)
    exact h_commitqc_pos_mvba_consistent J M1 M2 hqc hmv'


#prove_vc Chorus mvba_decide_pos commitqc_neg_mvba_pos_excl by
  unveil_local
  inv_have h_msg_commitqc_neg_votes := msg_commitqc_neg_votes
  inv_have h_vote_unique_pos_neg := vote_unique_pos_neg
  inv_have h_msg_commitqc_neg_backed := msg_commitqc_neg_backed
  inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  inv_have h_commitqc_neg_mvba_pos_excl := commitqc_neg_mvba_pos_excl
  intro _hphase _hcompl _hprop _hinvoked hev _hagree _hnneg J M hqc
  refine ⟨?_, h_commitqc_neg_mvba_pos_excl J M hqc⟩
  rintro rfl rfl
  rcases hev with ⟨Q2, hQ2_sup, hQ2⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
  · obtain ⟨Qn, hQn_sup, hQn⟩ := h_msg_commitqc_neg_votes j hqc
    obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Q2 Qn hQ2_sup hQn_sup
    have hx := h_vote_unique_pos_neg b j m (Bool.eq_false_iff.mpr hb_hon) (hQ2 b hb1)
    have hy := hQn b hb2
    rw [hx] at hy; simp at hy
  · obtain ⟨Qc, hQc_sup, hQc⟩ := h_msg_commitqc_neg_backed j hqc
    obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
    have hcf := h_commit_cast_fallback_sig_excl c (Bool.eq_false_iff.mpr hc_hon) (hQc c hc1).2
    have hy := hqf c hc2
    rw [hcf] at hy; simp at hy

#prove_action Chorus mvba_decide_pos

end Chorus.Proofs
