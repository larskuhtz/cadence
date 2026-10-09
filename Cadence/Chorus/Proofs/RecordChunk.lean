import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `record_chunk`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `record_chunk` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus record_chunk <property> by <tac>` lines
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

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus record_chunk proposal_inclusion by
  unveil_local
  veil_inv_have h_cb := local_committed_pos_backed
  veil_inv_have h_votes := msg_commitqc_pos_votes
  veil_inv_have h_vsv := vote_sig_pos_implies_voted
  veil_inv_have h_vpd := voted_post_deadline
  veil_inv_have h_mdp := mvba_decided_phase
  intro _hbyz _hprop _x _hchunk _hsig hph _hfresh _hneg J I M M' _hJ _hJp _hall _hwe hI hcom
  -- Nothing is committed before the deadline: a commit's certificate has a
  -- correct voter, who has voted, and an MVBA record postdates the deadline.
  exfalso
  rcases h_cb I J M' hI hcom with ⟨C, hC⟩ | haux
  · obtain ⟨q, hq_sup, hq⟩ := h_votes C J M' hC
    obtain ⟨a, ha_mem, ha_hon⟩ :=
      nset.greater_than_third_one_honest q (nset.supermajority_greater_than_third q hq_sup)
    have hv := h_vsv a J M' (Bool.eq_false_iff.mpr ha_hon) (hq a ha_mem)
    exact h_vpd a (Bool.eq_false_iff.mpr ha_hon) hv hph
  · exact h_mdp J M' (Or.inl haux) hph

/- Written out: the solver took over 15 s on this cell locally, too close to
the budget on CI's runner; before the deadline no correct validator has voted, so no commit certificate exists. -/
#prove_vc Chorus record_chunk inclusion_commitqc_pos_root by
  unveil_local
  veil_inv_have h_votes := msg_commitqc_pos_votes
  veil_inv_have h_sv := vote_sig_pos_implies_voted
  veil_inv_have h_vpd := voted_post_deadline
  intro _hbyz _hj _x _hx _hps hph _hnp _hnn C J M M' _hJ _hJp _hall _hwe hqc
  exfalso
  obtain ⟨q, hq, hallq⟩ := h_votes C J M' hqc
  obtain ⟨b, hb, hbh⟩ :=
    nset.greater_than_third_one_honest q (nset.supermajority_greater_than_third q hq)
  have hb' := Bool.eq_false_iff.mpr hbh
  exact h_vpd b hb' (h_sv b J M' hb' (hallq b hb)) hph

#prove_action Chorus record_chunk

end Chorus.Proofs
