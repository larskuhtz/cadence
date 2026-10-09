import Cadence.Mvba
import Cadence.ProofPrelude

/-! # `Mvba` proofs — action `sync_view_adopt`

Scaffolded by `#gen_proof_files Mvba`; yours to edit. Proves every
registered VC of `sync_view_adopt` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Mvba sync_view_adopt <property> by <tac>` lines
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

/- **Manual cells — adoption is a frame step for both invariants, plus one
order chain.** The cold solve put them at 53.6 s and 25.5 s locally, past
the 15 s line for a 4-core CI runner. `local_prepqc_within_entered`: an old
certificate keeps the pre-state's bound, since `entered` only grows; the
adopted one is of view `w ≤ pv` (`tc_lock_backed`), and `pv < v`, the view
the step enters. `prepqc_blocks_lower_commits`: the step adds no prepare
certificate and no `Timeout`, and a new held certificate only adds to
`blocked`, so each pre-state witness stands. -/
#prove_vc Mvba sync_view_adopt local_prepqc_within_entered by
  unveil_local
  veil_inv_have h_within := local_prepqc_within_entered
  veil_inv_have h_tc_lock_backed := tc_lock_backed
  clear hinv
  intro _ _ _ _ _ hnext hlock _ _ R W E U hR hpq hU
  by_cases hnew : i = R ∧ w = W ∧ e = E
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    have hvU : TotalOrderWithMinimum.le v U := hU v (fun h => absurd rfl (h rfl))
    have hwpv := (h_tc_lock_backed s pv w e hlock).2.1
    have hpvv := ((TotalOrderWithMinimum.le_lt pv v).mp
      ((TotalOrderWithMinimum.next_def pv v).mp hnext).1).1
    exact TotalOrderWithMinimum.le_trans w pv U hwpv
      (TotalOrderWithMinimum.le_trans pv v U hpvv hvU)
  · exact h_within R W E U hR (hpq (fun h0 h1 h2 => hnew ⟨h0, h1, h2⟩))
      (fun V hV => hU V (fun _ => hV))

#prove_vc Mvba sync_view_adopt prepqc_blocks_lower_commits by
  unveil_local
  veil_inv_have h_blocks := prepqc_blocks_lower_commits
  clear hinv
  intro _ _ _ _ _ _ _ _ _ S W V E' E Q hpq hlt hne hsup_Q
  obtain ⟨n, h1, h2, h3⟩ := h_blocks S W V E' E Q hpq hlt hne hsup_Q
  exact ⟨n, h1, h2, h3.imp id fun ⟨e', h4, h5⟩ => ⟨e', h4, fun _ => h5⟩⟩

#prove_action Mvba sync_view_adopt

end Mvba.Proofs
