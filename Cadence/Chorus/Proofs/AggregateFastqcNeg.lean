import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `aggregate_fastqc_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `aggregate_fastqc_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus aggregate_fastqc_neg <property> by <tac>` lines
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

/- Manual discharge of the one VC of this action that SMT cannot solve at
this clump size: it falls into e-matching divergence, and no budget fixes
it (300 s, 400 s and 900 s all observed to time out). The argument: the
new `local_fastqc_neg i j` entry can complete `i`'s fast meta-block; per
proposer the evidence comes from `local_fastqc_pos_backed` /
`local_fastqc_neg_backed`, and for the new `(i, j)` entry from the
action's own witnessed vote quorum. -/
#prove_vc Chorus aggregate_fastqc_neg fastqc_complete_implies_mvba_evidence by
  unveil_local
  inv_have h_local_fastqc_pos_backed := local_fastqc_pos_backed
  inv_have h_local_fastqc_neg_backed := local_fastqc_neg_backed
  intro _hbyz_i hsup_q hq I hbyz_I hmeta J hprop_J
  rcases hmeta J hprop_J with ⟨M, hpos⟩ | hneg
  · exact Or.inl ⟨M, h_local_fastqc_pos_backed I J M hbyz_I hpos⟩
  · by_cases hnew : i = I ∧ j = J
    · obtain ⟨rfl, rfl⟩ := hnew
      exact Or.inr ⟨q, hsup_q, hq⟩
    · have hpre : st.local_fastqc_neg I J = true := hneg (fun h1 h2 => hnew ⟨h1, h2⟩)
      exact Or.inr (h_local_fastqc_neg_backed I J hbyz_I hpre)

#prove_action Chorus aggregate_fastqc_neg

end Chorus.Proofs
