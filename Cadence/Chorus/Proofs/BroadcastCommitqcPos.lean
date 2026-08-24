import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `broadcast_commitqc_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `broadcast_commitqc_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus broadcast_commitqc_pos <property> by <tac>` lines
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

#prove_vc Chorus broadcast_commitqc_pos commitqc_pos_mvba_consistent by
  unveil_local
  inv_have h_commit_pos_sig_from_local_fastqc := commit_pos_sig_from_local_fastqc
  inv_have h_local_fastqc_pos_backed := local_fastqc_pos_backed
  inv_have h_mvba_decided_pos_backed := mvba_decided_pos_backed
  inv_have h_vote_unique_pos := vote_unique_pos
  inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  inv_have h_commitqc_pos_mvba_consistent := commitqc_pos_mvba_consistent
  intro hsup_q hq J M1 M2 hqc hmv
  by_cases hnew : j = J ∧ m = M1
  · obtain ⟨rfl, rfl⟩ := hnew
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
  · have hold : st.msg_commitqc_pos J M1 = true := hqc (fun h1 h2 => hnew ⟨h1, h2⟩)
    exact h_commitqc_pos_mvba_consistent J M1 M2 hold hmv


#prove_vc Chorus broadcast_commitqc_pos progress_fallback_signing by
  unveil_local
  inv_have h_progress_fallback_signing := progress_fallback_signing
  intro _hsup_q _hq
  exact h_progress_fallback_signing

#prove_action Chorus broadcast_commitqc_pos

end Chorus.Proofs
