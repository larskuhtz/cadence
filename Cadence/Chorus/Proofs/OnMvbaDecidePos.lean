import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `on_mvba_decide_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `on_mvba_decide_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus on_mvba_decide_pos <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared blocks from
[ProofPrelude.lean](../../ProofPrelude.lean) record what each of the other options is
for.

The two manual cells are the quorum-intersection arguments of the
commitQC-versus-decision family ([MvbaPlan.md](../../../docs/MvbaPlan.md) §6):
the handler's bridge `require` — the decided entry's certificate against the
network — is the evidence hypothesis `hev` the arguments intersect with the
commitQC's quorum. The `intro` pattern follows the handler's guards:
`¬ is_byz i`, `is_proposer j`,
`mvba.decided mvba_st i v`, `mval_pos (mvba.entries v) j m`, and then the
bridge, which names the certificate kind `v` carries for the entry (a
`FastQC`'s vote quorum, or a `FallbackQC` with `FBCert`). -/

open Veil Chorus

-- The no-trusted-solver rule ([README.md](../../../README.md)) stays written out per proof file so
-- it remains greppable; the shared blocks below are defined and documented
-- in [ProofPrelude.lean](../../ProofPrelude.lean).
set_option veil.smt.trust false
veil_proof_options
veil_large_clump_budgets

namespace Chorus.Proofs

#prove_vc Chorus on_mvba_decide_pos commitqc_pos_mvba_consistent by
  unveil_local
  veil_inv_have h_msg_commitqc_pos_votes := msg_commitqc_pos_votes
  veil_inv_have h_vote_unique_pos := vote_unique_pos
  veil_inv_have h_msg_commitqc_pos_backed := msg_commitqc_pos_backed
  veil_inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  veil_inv_have h_commitqc_pos_mvba_consistent := commitqc_pos_mvba_consistent
  intro _hbyz _hprop _hdec _hval hev _hfresh C J M1 M2 hqc hmv
  by_cases hnew : j = J ∧ m = M2
  · obtain ⟨rfl, rfl⟩ := hnew
    rcases hev with ⟨-, ⟨Q2, hQ2_sup, hQ2⟩⟩ | ⟨-, -, ⟨qf, hqf_sup, hqf⟩⟩
    · obtain ⟨Qm, hQm_sup, hQm⟩ := h_msg_commitqc_pos_votes C j M1 hqc
      obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qm Q2 hQm_sup hQ2_sup
      exact h_vote_unique_pos b j M1 m (Bool.eq_false_iff.mpr hb_hon) (hQm b hb1) (hQ2 b hb2)
    · exfalso
      obtain ⟨Qc, hQc_sup, hQc⟩ := h_msg_commitqc_pos_backed C j M1 hqc
      obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
      have hcf := h_commit_cast_fallback_sig_excl c (Bool.eq_false_iff.mpr hc_hon) (hQc c hc1).2
      have hy := hqf c hc2
      rw [hcf] at hy; simp at hy
  · have hmv' : st.aux_mvba_decided_pos J M2 = true := hmv (fun h1 h2 => hnew ⟨h1, h2⟩)
    exact h_commitqc_pos_mvba_consistent C J M1 M2 hqc hmv'

#prove_vc Chorus on_mvba_decide_pos commitqc_neg_mvba_pos_excl by
  unveil_local
  veil_inv_have h_msg_commitqc_neg_votes := msg_commitqc_neg_votes
  veil_inv_have h_vote_unique_pos_neg := vote_unique_pos_neg
  veil_inv_have h_msg_commitqc_neg_backed := msg_commitqc_neg_backed
  veil_inv_have h_commit_cast_fallback_sig_excl := commit_cast_fallback_sig_excl
  veil_inv_have h_commitqc_neg_mvba_pos_excl := commitqc_neg_mvba_pos_excl
  intro _hbyz _hprop _hdec _hval hev _hfresh C J M hqc
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

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus on_mvba_decide_pos mvba_decided_pos_chunks_decodable by
  unveil_local
  veil_inv_have h_old := mvba_decided_pos_chunks_decodable
  veil_inv_have h_dec := vote_pos_quorum_implies_decodable
  veil_inv_have h_fb := msg_fb_pos_sig_backed
  intro _hbyz _hprop _hdec _hval hev _hfresh J M hpost
  by_cases hnew : j = J ∧ m = M
  · obtain ⟨rfl, rfl⟩ := hnew
    rcases hev with ⟨-, ⟨q, hq_sup, hq⟩⟩ | ⟨-, ⟨qf, hqf_gtt, hqf⟩, -⟩
    · exact h_dec j m q hq_sup hq
    · obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest qf hqf_gtt
      obtain ⟨q, hq_gtt, hq⟩ := h_fb a j m (Bool.eq_false_iff.mpr ha_hon) (hqf a ha_mem)
      exact ⟨q, hq_gtt, fun r hr => (hq r hr).2⟩
  · exact h_old J M (hpost (fun h1 h2 => hnew ⟨h1, h2⟩))

#prove_action Chorus on_mvba_decide_pos

end Chorus.Proofs
