import Cadence.Mvba
import Cadence.ProofPrelude

/-! # `Mvba` proofs — action `adopt_prepqc`

Scaffolded by `#gen_proof_files Mvba`; yours to edit. Proves every
registered VC of `adopt_prepqc` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Mvba adopt_prepqc <property> by <tac>` lines
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

/- **Manual cell — the lock-persistence step, at the validator's own
certificate.** Since R3 `adopt_prepqc` forms the prepare certificate from
the prepares it received (the supplement's `TryFormPrepQC`) and so sets
`msg_prepqc`, which makes it the second action that creates a certificate.
The argument is `form_prepqc`'s manual cell
([FormPrepqc.lean](FormPrepqc.lean), which explains it) verbatim, with the
action's extra guards introduced and unused, and one more step: a
`blocked` witness of the pre-state is one of the post-state, because the
new held certificate only adds to `local_prepqc`. Written out for the same
reason as that cell — its search is a genuine argument, and the solver
found it with too little headroom for a 4-core CI runner. -/
#prove_vc Mvba adopt_prepqc prepqc_blocks_lower_commits by
  unveil_local
  veil_inv_have h_honest_prepare_accepted := honest_prepare_accepted
  veil_inv_have h_accepted_justified := accepted_justified
  veil_inv_have h_tc_nolock_backed := tc_nolock_backed
  veil_inv_have h_tc_lock_backed := tc_lock_backed
  veil_inv_have h_honest_timeout_qc_held := honest_timeout_qc_held
  veil_inv_have h_timeout_qc_backed := timeout_qc_backed
  veil_inv_have h_prepqc_unique := prepqc_unique
  veil_inv_have h_blocks := prepqc_blocks_lower_commits
  clear hinv
  intro _ _ _ _ _ _ _ hsup_q hq _ _ _ W V E' E Q hpq hlt hne hsup_Q
  -- The new certificate is on the accepted representation's entries.
  generalize th.ent x = e at *
  by_cases hnew : v = W ∧ e = E'
  · obtain ⟨rfl, rfl⟩ := hnew
    -- An honest preparer `a` of the new certificate accepted a
    -- representation `X` of `e` in `v`.
    obtain ⟨a, ha_mem, ha_hon⟩ :=
      nset.greater_than_third_one_honest q (nset.supermajority_greater_than_third q hsup_q)
    have ha_hon' : ByzNodeSet.is_byz a = false := Bool.eq_false_iff.mpr ha_hon
    obtain ⟨X, hacc, hXe⟩ := h_honest_prepare_accepted a v e ha_hon' (hq a ha_mem)
    -- `V < v`, so `v` is not the first view and `a`'s acceptance was
    -- justified by a timeout certificate of the previous view `PV ≥ V`.
    have hv0 : ¬ v = TotalOrderWithMinimum.zero := by
      intro h0
      rw [h0] at hlt
      have h := (TotalOrderWithMinimum.le_lt V TotalOrderWithMinimum.zero).mp hlt
      exact h.2 (TotalOrderWithMinimum.le_antisymm _ _ h.1 (TotalOrderWithMinimum.zero_lt V))
    obtain ⟨PV, hnext, hjust⟩ := h_accepted_justified a v X ha_hon' hacc hv0
    rw [hXe] at hjust
    have hVPV : TotalOrderWithMinimum.le V PV := by
      have hn := (TotalOrderWithMinimum.next_def PV v).mp hnext
      rcases TotalOrderWithMinimum.le_total V PV with h | h
      · exact h
      · by_cases hEq : V = PV
        · rw [hEq]; exact TotalOrderWithMinimum.le_refl PV
        · have hltPV : TotalOrderWithMinimum.lt PV V :=
            (TotalOrderWithMinimum.le_lt PV V).mpr ⟨h, fun h' => hEq h'.symm⟩
          have hle := hn.2 V hltPV
          have hlt' := (TotalOrderWithMinimum.le_lt V v).mp hlt
          exact absurd (TotalOrderWithMinimum.le_antisymm _ _ hlt'.1 hle) hlt'.2
    rcases hjust with hnolock | ⟨w, hlock⟩
    · -- The justifying certificate has no lock: its quorum meets `Q` in an
      -- honest `n` that timed out at `PV ≥ V` carrying `⊥`.
      obtain ⟨qt, hqt_sup, hqt⟩ := h_tc_nolock_backed PV hnolock
      obtain ⟨n, hnQ, hnq, hn_hon⟩ :=
        nset.supermajorities_intersect_in_honest Q qt hsup_Q hqt_sup
      exact ⟨n, hnQ, Bool.eq_false_iff.mpr hn_hon, Or.inl ⟨PV, hVPV, Or.inl (hqt n hnq)⟩⟩
    · -- The justifying certificate's lock is `(w, e)`, `w ≤ PV`, and every
      -- member carries `⊥` or a certificate of view `≤ w`.
      obtain ⟨hpq_w, -, qt, hqt_sup, hqt⟩ := h_tc_lock_backed PV w e hlock
      obtain ⟨n, hnQ, hnq, hn_hon⟩ :=
        nset.supermajorities_intersect_in_honest Q qt hsup_Q hqt_sup
      have hn_hon' : ByzNodeSet.is_byz n = false := Bool.eq_false_iff.mpr hn_hon
      rcases hqt n hnq with hnoqc | ⟨w', ⟨x, hto⟩, hw'_le⟩
      · exact ⟨n, hnQ, hn_hon', Or.inl ⟨PV, hVPV, Or.inl hnoqc⟩⟩
      · -- `n` carries a certificate `(w', x)` with `w' ≤ w`: either it is
        -- below `V` (then `n` left `V` without a view-`≥ V` lock), or
        -- `V ≤ w' ≤ w`.
        have hcase : TotalOrderWithMinimum.lt w' V ∨ TotalOrderWithMinimum.le V w' := by
          rcases TotalOrderWithMinimum.le_total V w' with h | h
          · exact Or.inr h
          · by_cases hEq : w' = V
            · exact Or.inr (hEq ▸ TotalOrderWithMinimum.le_refl w')
            · exact Or.inl ((TotalOrderWithMinimum.le_lt w' V).mpr ⟨h, hEq⟩)
        rcases hcase with hlt_w'V | hVw'
        · exact ⟨n, hnQ, hn_hon', Or.inl ⟨PV, hVPV, Or.inr ⟨w', ⟨x, hto⟩, hlt_w'V⟩⟩⟩
        · by_cases hVw : V = w
          · -- The lock is of view `V` itself: `n` holds the view-`V`
            -- certificate, which is on `e ≠ E` by certificate uniqueness.
            have hw'eq : w' = V :=
              TotalOrderWithMinimum.le_antisymm _ _ (hVw ▸ hw'_le) hVw'
            have hheld : st.local_prepqc n V x = true :=
              hw'eq ▸ h_honest_timeout_qc_held n PV w' x hn_hon' hto
            have hpx : st.msg_prepqc V x = true := hw'eq ▸ h_timeout_qc_backed n PV w' x hto
            have hpe : st.msg_prepqc V e = true := hVw ▸ hpq_w
            have hx : x = e := h_prepqc_unique V x e hpx hpe
            exact ⟨n, hnQ, hn_hon', Or.inr ⟨x, fun hxE => hne (hxE ▸ hx), fun _ => hheld⟩⟩
          · -- `V < w`: the invariant at the lock's own certificate `(w, e)`.
            have hVw_lt : TotalOrderWithMinimum.lt V w :=
              (TotalOrderWithMinimum.le_lt V w).mpr
                ⟨TotalOrderWithMinimum.le_trans V w' w hVw' hw'_le, hVw⟩
            obtain ⟨n, h1, h2, h3⟩ := h_blocks w V e E Q hpq_w hVw_lt hne hsup_Q
            exact ⟨n, h1, h2, h3.imp id fun ⟨e', h4, h5⟩ => ⟨e', h4, fun _ => h5⟩⟩
  · -- An old certificate: the invariant in the pre-state.
    have hold : st.msg_prepqc W E' = true := hpq (fun h1 h2 => hnew ⟨h1, h2⟩)
    -- A new held certificate only adds to `blocked`.
    obtain ⟨n, h1, h2, h3⟩ := h_blocks W V E' E Q hold hlt hne hsup_Q
    exact ⟨n, h1, h2, h3.imp id fun ⟨e', h4, h5⟩ => ⟨e', h4, fun _ => h5⟩⟩

#prove_action Mvba adopt_prepqc

end Mvba.Proofs
