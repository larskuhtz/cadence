import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `commit_assign_pos_fast`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `commit_assign_pos_fast` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus commit_assign_pos_fast <property> by <tac>` lines
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

/- The re-broadcast certificate's chunk backing is the received one's: the
solver crashes (💥) on the sender-index case split, so it is written out. -/

#prove_vc Chorus commit_assign_pos_fast msg_commitqc_pos_chunks_decodable by
  unveil_local
  veil_inv_have h := msg_commitqc_pos_chunks_decodable
  intro _hbyz _hpart _hab _hcom _hprop hqc _hfresh _hneg C J M hpost
  by_cases hnew : i = C ∧ j = J ∧ m = M
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    exact h c j m hqc
  · exact h C J M (hpost (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩))

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus commit_assign_pos_fast speculative_agreement_pos by
  unveil_local
  veil_inv_have h_old := speculative_agreement_pos
  veil_inv_have h_votes := msg_commitqc_pos_votes
  veil_inv_have h_fqb := local_fastqc_pos_backed
  veil_inv_have h_vu := vote_unique_pos
  intro _hbyz _hpart _hab _hcom _hprop hqc _hfresh _hneg hne1 hne2 hne3 hnie
    I1 I2 J M1 M2 h1 h2 hfq hpost
  by_cases hnew : i = I2 ∧ j = J ∧ m = M2
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    -- The certificate's vote supermajority meets the FastQC's in a correct
    -- validator, whose positive entry is unique.
    obtain ⟨Qm, hQm_sup, hQm⟩ := h_votes c j m hqc
    obtain ⟨Qf, hQf_sup, hQf⟩ := h_fqb I1 j M1 h1 hfq
    obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qf Qm hQf_sup hQm_sup
    exact h_vu b j M1 m (Bool.eq_false_iff.mpr hb_hon) (hQf b hb1) (hQm b hb2)
  · exact h_old hne1 hne2 hne3 hnie I1 I2 J M1 M2 h1 h2 hfq
      (hpost (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩))

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus commit_assign_pos_fast msg_commitqc_pos_backed by
  unveil_local
  veil_inv_have h_old := msg_commitqc_pos_backed
  intro _hbyz _hpart _hab _hcom _hprop hqc _hfresh _hneg C J M hpost
  by_cases hnew : i = C ∧ j = J ∧ m = M
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    exact h_old c j m hqc
  · exact h_old C J M (hpost (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩))

#prove_action Chorus commit_assign_pos_fast

end Chorus.Proofs
