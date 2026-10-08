import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `commit_assign_pos_fb`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `commit_assign_pos_fb` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus commit_assign_pos_fb <property> by <tac>` lines
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

#prove_vc Chorus commit_assign_pos_fb proposal_inclusion by
  unveil_local
  veil_inv_have h_old := proposal_inclusion
  veil_inv_have h_qcb := msg_fbcommitqc_backed
  veil_inv_have h_qce := fbcommitqc_entries
  veil_inv_have h_inc := inclusion_mvba_pos_unique
  intro _hbyz _hpart _hab _hcom hprop hmsg hmv _hfresh _hneg J I M M' hJ hJp hall hwe hI hpost
  by_cases hnew : i = I ∧ j = J ∧ m = M'
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    -- The certificate's entry is a certified entry, which inclusion pins.
    obtain ⟨q, hq_sup, hq⟩ := h_qcb c e hmsg
    have haux := (h_qce e j m q hq_sup hq hprop).1 hmv
    exact h_inc j M m hJ hJp hall hwe haux
  · exact h_old J I M M' hJ hJp hall hwe hI (hpost (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩))

#prove_action Chorus commit_assign_pos_fb

end Chorus.Proofs
