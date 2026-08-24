import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `aggregate_fastqc_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `aggregate_fastqc_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus aggregate_fastqc_pos <property> by <tac>` lines
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

/- Manual discharge of the one VC of this action whose
quorum-intersection chain cvc5's e-matching cannot find automatically:
two applications of the `ByzNodeSet` counting axioms against the
explicitly witnessed quorums, closed by the recorded backing invariants.
The cell restates the canonical VC statement from the registry, so the
`#prove_action` below consumes it as-is after a statement check; the
invariant conjuncts it needs are named, not indexed
(`inv_have`, `Cadence/ProofPrelude.lean`). -/
#prove_vc Chorus aggregate_fastqc_pos spec_fastqc_pos_mvba_pos_unique by
  unveil_local
  inv_have h_mvba_decided_pos_backed := mvba_decided_pos_backed
  inv_have h_msg_fb_pos_sig_backed := msg_fb_pos_sig_backed
  inv_have h_spec_fastqc_pos_mvba_pos_unique := spec_fastqc_pos_mvba_pos_unique
  intro _hbyz_i hsup_q hq_sigs hne1 hne2 hne3 hnie I J M M' hbyz_I hfq hmv
  by_cases hnew : i = I ∧ j = J ∧ m = M
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    rcases h_mvba_decided_pos_backed j M' hmv with ⟨Q2, hQ2_sup, hQ2⟩ | ⟨⟨qf, hqf_gtt, hqf⟩, -⟩
    · obtain ⟨a, ha1, ha2, -⟩ := nset.supermajorities_intersect_in_honest q Q2 hsup_q hQ2_sup
      exact hne1 a j m M' (hq_sigs a ha1) (hQ2 a ha2)
    · obtain ⟨rf, hrf_mem, hrf_hon⟩ := nset.greater_than_third_one_honest qf hqf_gtt
      have hrf_hon' : ByzNodeSet.is_byz rf = false := Bool.eq_false_iff.mpr hrf_hon
      obtain ⟨qv2, hqv2_gtt, hqv2⟩ := h_msg_fb_pos_sig_backed rf j M' hrf_hon' (hqf rf hrf_mem)
      obtain ⟨b, hb1, hb2⟩ := nset.supermajority_greater_than_third_intersect q qv2 hsup_q hqv2_gtt
      exact hne1 b j m M' (hq_sigs b hb1) (hqv2 b hb2)
  · have hold : st.local_fastqc_pos I J M = true := hfq (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩)
    exact h_spec_fastqc_pos_mvba_pos_unique hne1 hne2 hne3 hnie I J M M' hbyz_I hold hmv

#prove_action Chorus aggregate_fastqc_pos

end Chorus.Proofs
