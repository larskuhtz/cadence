import Cadence.Mvba
import Cadence.ProofPrelude

/-! # `Mvba` proofs — action `byz_form_prepqc`

Scaffolded by `#gen_proof_files Mvba`; yours to edit. Proves every
registered VC of `byz_form_prepqc` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Mvba byz_form_prepqc <property> by <tac>` lines
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

/- **Manual cell — the lock-persistence step.** The solver can find this
proof, but its search is a genuine argument rather than a lookup, and at
its margin it times out on a 4-core CI runner. Written out, it is Supplement, Lemma 8 (`lem:lock-persistence`) for one view transition: the new
certificate's honest preparer `a` accepted `e` in `v > V` under a timeout
certificate of the previous view `PV ≥ V`; that certificate's `2f+1`
timeout senders meet the given supermajority `Q` in an honest `n`; if the
certificate has no lock, or `n`'s carried certificate is below `V`, `n`
left `V` without a view-`≥ V` lock; if the lock is of view `V` itself,
`n` holds the view-`V` certificate, which is on `e ≠ E` by certificate
uniqueness; otherwise the lock's own certificate is of a view strictly
between `V` and `v`, and the invariant at *that* certificate finishes. The
conjuncts are projected by name (`veil_inv_have`);
the `#prove_action` below consumes the cell after a statement check. -/
#prove_vc Mvba byz_form_prepqc prepqc_blocks_lower_commits by
  unveil_local
  veil_inv_have h_honest_prepare_accepted := honest_prepare_accepted
  veil_inv_have h_accepted_justified := accepted_justified
  veil_inv_have h_tc_nolock_backed := tc_nolock_backed
  veil_inv_have h_tc_lock_backed := tc_lock_backed
  veil_inv_have h_honest_timeout_qc_held := honest_timeout_qc_held
  veil_inv_have h_timeout_qc_backed := timeout_qc_backed
  veil_inv_have h_timeout_qc_view_le := timeout_qc_view_le
  veil_inv_have h_prepqc_unique := prepqc_unique
  veil_inv_have h_blocks := prepqc_blocks_lower_commits
  clear hinv
  intro _ hsup_q hq S W V E' E Q hpq hlt hne hsup_Q
  by_cases hnew : r = S ∧ v = W ∧ e = E'
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
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
    rcases hjust with ⟨s0, hnolock⟩ | ⟨s0, w, hlock⟩
    · -- The justifying certificate has no lock: its quorum meets `Q` in an
      -- honest `n` that timed out at `PV ≥ V` carrying `⊥` (a correct
      -- `Timeout` never carries a certificate above its view, which the
      -- rule would also read as `⊥`).
      obtain ⟨qt, hqt_sup, hqt⟩ := h_tc_nolock_backed s0 PV hnolock
      obtain ⟨n, hnQ, hnq, hn_hon⟩ :=
        nset.supermajorities_intersect_in_honest Q qt hsup_Q hqt_sup
      have hn_hon' : ByzNodeSet.is_byz n = false := Bool.eq_false_iff.mpr hn_hon
      rcases hqt n hnq with hnoqc | ⟨w', ⟨x, hto⟩, hgt⟩
      · exact ⟨n, hnQ, hn_hon', Or.inl ⟨PV, hVPV, Or.inl hnoqc⟩⟩
      · have h := (TotalOrderWithMinimum.le_lt PV w').mp hgt
        exact absurd (TotalOrderWithMinimum.le_antisymm _ _ h.1
          (h_timeout_qc_view_le n PV w' x hn_hon' hto)) h.2
    · -- The justifying certificate's lock is `(w, e)`, `w ≤ PV`, and every
      -- member carries `⊥`, a certificate of view `≤ w`, or one above `PV`,
      -- which a correct member never carries.
      obtain ⟨⟨S1, hpq_w⟩, -, qt, hqt_sup, hqt⟩ := h_tc_lock_backed s0 PV w e hlock
      obtain ⟨n, hnQ, hnq, hn_hon⟩ :=
        nset.supermajorities_intersect_in_honest Q qt hsup_Q hqt_sup
      have hn_hon' : ByzNodeSet.is_byz n = false := Bool.eq_false_iff.mpr hn_hon
      rcases hqt n hnq with hnoqc | ⟨w', ⟨x, hto⟩, hw'_le⟩
      · exact ⟨n, hnQ, hn_hon', Or.inl ⟨PV, hVPV, Or.inl hnoqc⟩⟩
      · rcases hw'_le with hw'_le | hgt
        swap
        · -- A correct `Timeout`'s certificate is never above its view.
          have h := (TotalOrderWithMinimum.le_lt PV w').mp hgt
          exact absurd (TotalOrderWithMinimum.le_antisymm _ _ h.1
            (h_timeout_qc_view_le n PV w' x hn_hon' hto)) h.2
        -- `n` carries a certificate `(w', x)` with `w' ≤ w`: either it is
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
            obtain ⟨S2, hpx⟩ := h_timeout_qc_backed n PV w' x hto
            rw [hw'eq] at hpx
            have hpe : st.msg_prepqc S1 V e = true := hVw ▸ hpq_w
            have hx : x = e := h_prepqc_unique S2 S1 V x e hpx hpe
            exact ⟨n, hnQ, hn_hon', Or.inr ⟨x, fun hxE => hne (hxE ▸ hx), hheld⟩⟩
          · -- `V < w`: the invariant at the lock's own certificate `(w, e)`.
            have hVw_lt : TotalOrderWithMinimum.lt V w :=
              (TotalOrderWithMinimum.le_lt V w).mpr
                ⟨TotalOrderWithMinimum.le_trans V w' w hVw' hw'_le, hVw⟩
            exact h_blocks S1 w V e E Q hpq_w hVw_lt hne hsup_Q
  · -- An old certificate: the invariant in the pre-state.
    have hold : st.msg_prepqc S W E' = true :=
      hpq (fun h0 h1 h2 => hnew ⟨h0, h1, h2⟩)
    exact h_blocks S W V E' E Q hold hlt hne hsup_Q

#prove_action Mvba byz_form_prepqc

end Mvba.Proofs
