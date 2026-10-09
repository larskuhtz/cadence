import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `cast_fast_commit`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `cast_fast_commit` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus cast_fast_commit <property> by <tac>` lines
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

/- Written out: the solver took over 15 s on this cell locally, too close to
the budget on CI's runner; the vote quorums only grow. -/
#prove_vc Chorus cast_fast_commit fast_path_implies_vote_quorums by
  unveil_local
  veil_inv_have h_old := fast_path_implies_vote_quorums
  veil_inv_have h_cpf := commit_pos_sig_from_local_fastqc
  veil_inv_have h_cnf := commit_neg_sig_from_local_fastqc
  veil_inv_have h_fqb := local_fastqc_pos_backed
  veil_inv_have h_fqnb := local_fastqc_neg_backed
  intro hbyz _hpart _hab _hnc _hnp hsigs I0 hI0 hpath J hJ
  by_cases hI : i = I0
  · subst hI
    rcases hsigs J hJ with ⟨M, hM⟩ | hN
    · exact Or.inl ⟨M, h_fqb i J M hbyz (h_cpf i J M hbyz hM)⟩
    · exact Or.inr (h_fqnb i J hbyz (h_cnf i J hbyz hN))
  · exact h_old I0 hI0 (hpath hI) J hJ

#prove_action Chorus cast_fast_commit

end Chorus.Proofs
