import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `mvba_decide_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `mvba_decide_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus mvba_decide_neg <property> by <tac>` lines
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

#prove_vc Chorus mvba_decide_neg commitqc_pos_mvba_neg_excl by
  unveil_local
  inv_have h_msg_commitqc_pos_votes := msg_commitqc_pos_votes
  inv_have h_vote_unique_pos_neg := vote_unique_pos_neg
  inv_have h_msg_commitqc_pos_backed := msg_commitqc_pos_backed
  inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  inv_have h_commitqc_pos_mvba_neg_excl := commitqc_pos_mvba_neg_excl
  intro _hphase _hcompl _hprop _hinvoked hev _hnodec J M hqc
  refine ⟨?_, h_commitqc_pos_mvba_neg_excl J M hqc⟩
  rintro rfl
  rcases hev with ⟨Qn, hQn_sup, hQn⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
  · obtain ⟨Qm, hQm_sup, hQm⟩ := h_msg_commitqc_pos_votes j M hqc
    obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qm Qn hQm_sup hQn_sup
    have hx := h_vote_unique_pos_neg b j M (Bool.eq_false_iff.mpr hb_hon) (hQm b hb1)
    have hy := hQn b hb2
    rw [hx] at hy; simp at hy
  · obtain ⟨Qc, hQc_sup, hQc⟩ := h_msg_commitqc_pos_backed j M hqc
    obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
    have hcf := h_commit_cast_fallback_sig_excl c (Bool.eq_false_iff.mpr hc_hon) (hQc c hc1).2
    have hy := hqf c hc2
    rw [hcf] at hy; simp at hy


#prove_vc Chorus mvba_decide_neg inclusion_no_mvba_neg by
  unveil_local
  inv_have h_inclusion_no_honest_vote_neg := inclusion_no_honest_vote_neg
  inv_have h_inclusion_no_honest_fb_neg := inclusion_no_honest_fb_neg
  inv_have h_proposer_unique_root := proposer_unique_root
  inv_have h_inclusion_no_mvba_neg := inclusion_no_mvba_neg
  intro _hphase _hcompl _hprop _hinvoked hev _hnodec J M hbyzJ hpropJ hall hwe
  refine ⟨?_, h_inclusion_no_mvba_neg J M hbyzJ hpropJ hall hwe⟩
  rintro rfl
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

#prove_action Chorus mvba_decide_neg

end Chorus.Proofs
