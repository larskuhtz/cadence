import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `byz_redisseminate_chunk`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `byz_redisseminate_chunk` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus byz_redisseminate_chunk <property> by <tac>` lines
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

#prove_vc Chorus byz_redisseminate_chunk local_fastqc_pos_chunks_decodable by
  unveil_local
  veil_inv_have h_old := local_fastqc_pos_chunks_decodable
  intro _hbyz _hprop _hsig _x _hx _hall I J M hI hfq
  obtain ⟨q, hq, hall⟩ := h_old I J M hI hfq
  refine ⟨q, hq, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hall r hr
  exact ⟨s, fun _ => hs⟩

#prove_action Chorus byz_redisseminate_chunk

end Chorus.Proofs
