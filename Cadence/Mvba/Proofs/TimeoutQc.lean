import Cadence.Mvba
import Cadence.ProofPrelude

/-! # `Mvba` proofs — action `timeout_qc`

Scaffolded by `#gen_proof_files Mvba`; yours to edit. Proves every
registered VC of `timeout_qc` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Mvba timeout_qc <property> by <tac>` lines
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
`prepqc_blocks_lower_commits` (through `blocked`) and `tc_lock_backed` (its
quorum condition) read `msg_timeout_*` positively, and this step only adds a
`Timeout` row, so each pre-state witness stands. The solver spends tens of
seconds rediscovering that (CI runs 3–8× slower); the frame is a few
lines. -/
#prove_vc Mvba timeout_qc prepqc_blocks_lower_commits by
  unveil_local
  veil_inv_have h_blocks := prepqc_blocks_lower_commits
  clear hinv
  intro _ _ _ _ _ _ _ _ _ _ _ S W V E' E Q hpq hlt hne hsup_Q
  obtain ⟨n, h1, h2, h3⟩ := h_blocks S W V E' E Q hpq hlt hne hsup_Q
  refine ⟨n, h1, h2, ?_⟩
  rcases h3 with ⟨v', hle, hnoqc | ⟨w', ⟨x, hto⟩, hlt'⟩⟩ | h
  · exact Or.inl ⟨v', hle, Or.inl hnoqc⟩
  · exact Or.inl ⟨v', hle, Or.inr ⟨w', ⟨x, fun _ => hto⟩, hlt'⟩⟩
  · exact Or.inr h

#prove_vc Mvba timeout_qc tc_lock_backed by
  unveil_local
  veil_inv_have h_tc_lock_backed := tc_lock_backed
  clear hinv
  intro _ _ _ _ _ _ _ _ _ _ _ S V W E hl
  obtain ⟨h1, h2, q, hq, hm⟩ := h_tc_lock_backed S V W E hl
  refine ⟨h1, h2, q, hq, fun r hr => ?_⟩
  rcases hm r hr with h | ⟨W', ⟨x, hx⟩, hle⟩
  · exact Or.inl h
  · exact Or.inr ⟨W', ⟨x, fun _ => hx⟩, hle⟩

#prove_action Mvba timeout_qc

end Mvba.Proofs
