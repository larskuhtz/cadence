import Cadence.Mvba
import Cadence.ProofPrelude

/-! # `Mvba` proofs — action `timeout_noqc`

Scaffolded by `#gen_proof_files Mvba`; yours to edit. Proves every
registered VC of `timeout_noqc` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Mvba timeout_noqc <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared block from
[ProofPrelude.lean](../../ProofPrelude.lean) record what each of the other options is
for. -/

open Veil Mvba

-- The no-trusted-solver rule ([README.md](../../../README.md)) stays written out per proof file so
-- it remains greppable; the shared block below is defined and documented in
-- [ProofPrelude.lean](../../ProofPrelude.lean).
set_option veil.smt.trust false
veil_proof_options
-- The clump passed the point where the default elaboration budgets
-- suffice when liveness's invariants and the `entered_needs_certificate`
-- step property went in; the Chorus family has carried this since it was
-- written ([ProofPrelude.lean](../../ProofPrelude.lean)).
veil_large_clump_budgets

namespace Mvba.Proofs

/- **Manual cells — a timeout only adds to what the two invariants read.**
As at `timeout_qc` ([TimeoutQc.lean](TimeoutQc.lean)): the step only adds a
`Timeout` row, which `blocked` and `tc_lock_backed`'s quorum condition read
positively, so each pre-state witness stands. -/
#prove_vc Mvba timeout_noqc prepqc_blocks_lower_commits by
  unveil_local
  veil_inv_have h_blocks := prepqc_blocks_lower_commits
  clear hinv
  intro _ _ _ _ _ _ _ _ _ _ S W V E' E Q hpq hlt hne hsup_Q
  obtain ⟨n, h1, h2, h3⟩ := h_blocks S W V E' E Q hpq hlt hne hsup_Q
  refine ⟨n, h1, h2, ?_⟩
  rcases h3 with ⟨v', hle, hnoqc | hqc⟩ | h
  · exact Or.inl ⟨v', hle, Or.inl (fun _ => hnoqc)⟩
  · exact Or.inl ⟨v', hle, Or.inr hqc⟩
  · exact Or.inr h

#prove_vc Mvba timeout_noqc tc_lock_backed by
  unveil_local
  veil_inv_have h_tc_lock_backed := tc_lock_backed
  clear hinv
  intro _ _ _ _ _ _ _ _ _ _ S V W E hl
  obtain ⟨h1, h2, q, hq, hm⟩ := h_tc_lock_backed S V W E hl
  refine ⟨h1, h2, q, hq, fun r hr => ?_⟩
  rcases hm r hr with h | h
  · exact Or.inl (fun _ => h)
  · exact Or.inr h

#prove_action Mvba timeout_noqc

end Mvba.Proofs
