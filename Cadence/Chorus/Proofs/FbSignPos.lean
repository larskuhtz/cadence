import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `fb_sign_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `fb_sign_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus fb_sign_pos <property> by <tac>` lines
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
the budget on CI's runner; the new fallback entry only adds to a FallbackQC. -/
#prove_vc Chorus fb_sign_pos mvba_decided_pos_backed by
  unveil_local
  veil_inv_have h_old := mvba_decided_pos_backed
  intro _h1 _h2 _h3 _h4 _h5 _h6 _h7 _h8 _x _hx _hxv _hq _hps _hqs _hwe _hfr J M hJM
  rcases h_old J M hJM with h | ⟨⟨q, hq, hall⟩, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨q, hq, fun r hr _ => hall r hr⟩, hc⟩

#prove_action Chorus fb_sign_pos

end Chorus.Proofs
