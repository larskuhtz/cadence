import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `broadcast_commitqc_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `broadcast_commitqc_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus broadcast_commitqc_neg <property> by <tac>` lines
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

#prove_vc Chorus broadcast_commitqc_neg commitqc_neg_mvba_pos_excl by
  unveil_local
  inv_have h_commit_neg_sig_from_local_fastqc := commit_neg_sig_from_local_fastqc
  inv_have h_local_fastqc_neg_backed := local_fastqc_neg_backed
  inv_have h_mvba_decided_pos_backed := mvba_decided_pos_backed
  inv_have h_vote_unique_pos_neg := vote_unique_pos_neg
  inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  inv_have h_commitqc_neg_mvba_pos_excl := commitqc_neg_mvba_pos_excl
  intro hsup_q hq J M hqcneg
  refine Bool.eq_false_iff.mpr fun hb => ?_
  by_cases hnew : j = J
  · subst hnew
    obtain ⟨a, ha_mem, ha_hon⟩ :=
      nset.greater_than_third_one_honest q (nset.supermajority_greater_than_third q hsup_q)
    have ha_hon' : ByzNodeSet.is_byz a = false := Bool.eq_false_iff.mpr ha_hon
    have ha_fqn := h_commit_neg_sig_from_local_fastqc a j ha_hon' (hq a ha_mem).1
    obtain ⟨Qn, hQn_sup, hQn⟩ := h_local_fastqc_neg_backed a j ha_hon' ha_fqn
    rcases h_mvba_decided_pos_backed j M hb with ⟨Q2, hQ2_sup, hQ2⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
    · obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Q2 Qn hQ2_sup hQn_sup
      have hx := h_vote_unique_pos_neg b j M (Bool.eq_false_iff.mpr hb_hon) (hQ2 b hb1)
      have hy := hQn b hb2
      rw [hx] at hy; simp at hy
    · obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest q qf hsup_q hqf_sup
      have hcf := h_commit_cast_fallback_sig_excl c (Bool.eq_false_iff.mpr hc_hon) (hq c hc1).2
      have hy := hqf c hc2
      rw [hcf] at hy; simp at hy
  · have hz := h_commitqc_neg_mvba_pos_excl J M (hqcneg hnew)
    rw [hz] at hb; simp at hb

#prove_action Chorus broadcast_commitqc_neg

end Chorus.Proofs
