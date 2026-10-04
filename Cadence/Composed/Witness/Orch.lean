import Cadence.Composed.Witness.Steps

/-! # Composed.Witness.Orch — the Conductor meets its timing model on the composed witness

[ConductorBounds.md](../../../docs/ConductorBounds.md) §8.2, stage K8.
`OrchAdmissible` ([Composed/Schedule.lean](../Schedule.lean)) on the run of
[Steps.lean](Steps.lean). The orchestrator's state can stutter at every
index (the Conductor's `tick` to the time it already reads), so its part of
the run is stepped at every index and is the composed run read off at the
orchestrator (`partRun_at'_of_all`). Its labelled run is the Conductor's run
of [Steps.lean](Steps.lean) (`crun`), and it meets `Conductor.Sync`:

* **the rows** hold at the end of every plateau, where every correct
  validator is in a window it is not yet ready to leave, and every decided
  window's interval is recorded;
* **(P-open)**: every correct validator opens slot `s` at time `s`;
* **one clock**: the clock is the plateau, and so is `now`;
* **the ACS meets its module**: window `w`'s ideal ACS is stepped at every
  index too, and every correct validator proposes and decides at clock
  `36(w − 1) + 4`, so both of its timing guarantees hold. -/

namespace Composed.Witness

open Cadence Conductor Chorus
open scoped Cadence.Timed

attribute [local instance] Chorus.Witness.nsetC Chorus.Witness.cntC natViewOrder FM AS OSI SCI

/-! ## The Conductor's run -/

/-- **The Conductor's labelled run** under the composed run: its states, its
own labels (a `tick` in place where the composed step is not its), the
plateau clock, GST 0. -/
noncomputable def crun : TConductorRun (fm := FM) (A := AS) thO :=
  plateauRun 56 (by decide) cond clbl cholds cstarts (fun _ _ _ => ostep _)

@[simp] theorem crun_at' (n : ℕ) : crun.at' n = cond n := rfl
@[simp] theorem crun_lbl (n : ℕ) : crun.lbl n = clbl n := rfl
@[simp] theorem crun_clk (n : ℕ) : crun.clk n = n / 56 := rfl

/-! ## One clock, and (P-open) -/

theorem clockAgrees : ClockAgrees (fm := FM) (A := AS) crun := fun _ => rfl

theorem openPunctual : OpenPunctual (fm := FM) (A := AS) crun := by
  intro N i s hi _
  have hi := (correct_iff i).1 hi
  refine ⟨max N (s * 56 + 42 + i.val), le_max_left _ _, ?_, ?_⟩
  · show max N (s * 56 + 42 + i.val) / 56 ≤ max (N / 56) s
    rcases le_total N (s * 56 + 42 + i.val) with h | h
    · rw [max_eq_right h]; have : (s * 56 + 42 + i.val) / 56 = s := by omega
      rw [this]; exact le_max_right _ _
    · rw [max_eq_left h]; exact le_max_left _ _
  · show decide _ = true
    simp only [decide_eq_true_eq]
    omega

/-! ## The rows

At the end of plateau `t`, a correct validator in window `w` has not
completed slot `36w + 3`, the last slot below `w`'s readiness boundary:
otherwise `t ≥ 36w + 4` and it entered `w + 1` at that plateau. -/

/-- Expose a Conductor transition in a hypothesis. -/
local macro "ctr" h:ident : tactic =>
  `(tactic| (simp only [Conductor.relationalTransitionSystem, Conductor.Next, Conductor.NextAct,
      trSimp] at $h:ident))

theorem not_ready (t : ℕ) (i : Fin 4) (hi : i.val < 3) (w : ℕ)
    (hin : InWindow (cond (t * 56 + 55)) i w) : ¬ ReadyNext thO (cond (t * 56 + 55)) i w := by
  intro hrd
  obtain ⟨he, hne⟩ := hin
  have hne := hne (w + 1) rfl
  change decide _ = true at he
  change decide _ = false at hne
  simp only [decide_eq_true_eq, dB] at he
  simp only [decide_eq_false_iff_not, dB] at hne
  have hb := (winBounds_iff (t * 56 + 55) w (w * 36) (w * 36 + 4) (w * 36 + 35)).2
    ⟨rfl, rfl, rfl, by simp only [dB]; omega⟩
  have hc := hrd _ _ _ hb (w * 36 + 3) w (w * 36) (w * 36 + 4) (w * 36 + 35)
    (by show decide _ = true; simp only [decide_eq_true_eq, dB]; omega) hb (by omega) (by omega) (by omega)
  change decide _ = true at hc
  simp only [decide_eq_true_eq] at hc
  omega

theorem not_proposeGate (t : ℕ) (i : Fin 4) (hi : i.val < 3) (w' : ℕ) :
    ¬ Conductor.proposeGate thO i w' (cond (t * 56 + 55)) :=
  fun ⟨w, _, hin, hrd⟩ => not_ready t i hi w hin hrd

/-- A decided window's interval is recorded by the end of the plateau, so
its recording is disabled there. -/
theorem decide_quiet (t w : ℕ) :
    ¬ (decideGate (fm := FM) (A := AS) w (cond (t * 56 + 55)) ∧
      ∃ l, DecideLabel w l ∧ Enabled CRTS thO (cond (t * 56 + 55)) l) := by
  rintro ⟨⟨i, -, hd⟩, l, ⟨w0, first, f0, b0, l0, r1, s1, r2, s2, rfl⟩, s', htr⟩
  change decide _ = true at hd
  simp only [decide_eq_true_eq, dB] at hd
  ctr htr
  obtain ⟨-, hnd, -⟩ := htr
  have := hnd (w * 36) (w * 36 + 4) (w * 36 + 35)
  simp only [Veil.FieldRepresentation.get, instIsSubStateOfRefl.getFrom_id, id, cond,
    decide_eq_true_eq, dB, and_true] at this
  omega

theorem cEnd_ge (N : ℕ) : N ≤ N / 56 * 56 + 55 := by have := idx_eq N; have := pos_lt N; omega

theorem cEnd_clk (N : ℕ) : crun.clk (N / 56 * 56 + 55) = crun.clk N := by
  simp only [crun_clk]; omega

/-- **The Conductor's rows**, at `δ = 0`. -/
theorem timedRows : TimedRows (fm := FM) (A := AS) sch crun where
  propose i w' hi := bufferedFairFamily_of_ends (Nat.zero_le _) fun N =>
    ⟨_, cEnd_ge N, cEnd_clk N, fun ⟨_, hg, _⟩ =>
      not_proposeGate (N / 56) i ((correct_iff i).1 hi) w' hg⟩
  enter i w' hi := bufferedFairFamily_of_ends (Nat.zero_le _) fun N =>
    ⟨_, cEnd_ge N, cEnd_clk N, fun ⟨_, hg, _⟩ =>
      not_proposeGate (N / 56) i ((correct_iff i).1 hi) w' hg.2⟩
  decide w := bufferedFairFamily_of_ends (Nat.zero_le _) fun N =>
    ⟨_, cEnd_ge N, cEnd_clk N, fun ⟨_, hg, hen⟩ => decide_quiet (N / 56) w ⟨hg, hen⟩⟩

/-! ## The ACS meets its module

Window `w`'s ACS is related to itself across every step: by its own
transition where the Conductor moves it, by the ideal ACS's stutter
elsewhere. So its part is the run read off at `acs_state w`. -/

/-- Window `w`'s ACS, as a component of the Conductor. -/
noncomputable abbrev acsC (w : ℕ) := acsComponent (fm := FM) (A := AS) thO w

theorem acs_all (w : ℕ) (n : ℕ) :
    AS.trans ((acsC w).proj (crun.at' n)) ((acsC w).proj (crun.at' (n + 1))) := by
  by_cases h : (acsC w).isSub (crun.lbl n)
  · obtain ⟨_, h'⟩ := (acsC w).step _ _ _ (crun.steps n) h
    exact h'
  · rw [(acsC w).frame _ _ _ (crun.steps n) h]
    exact IdealAcs.trans_refl _

/-- Window `w ≥ 1`'s events: every correct validator has proposed and
decided by the end of plateau `36(w − 1) + 4`. -/
theorem acs_done (w : ℕ) (hw : 1 ≤ w) (j : Fin 4) (hj : j.val < 3) :
    IdealAcs.HasDecided (acsSt w (dB w + 55)) j := by
  simp only [IdealAcs.HasDecided, acsSt, decide_eq_true_eq, dB]; omega

/-- **The ideal ACS's admissibility**, on window `w`'s part, as soon as a
correct validator has proposed there. -/
theorem acsAdmissible : AcsAdmissible (fm := FM) (A := AS) TA crun := by
  intro w ⟨n0, i0, s0, hi0, hp0⟩
  have hw : 1 ≤ w := by
    change (acsSt w n0).prop i0 = some s0 at hp0
    simp only [acsSt] at hp0
    split_ifs at hp0 with h
    · exact h.1
  refine ⟨projOfAll (acs_all w), fun _ _ => ⟨?_, ?_⟩⟩
  · -- ℓ-Termination: everyone has decided by the clock everyone proposed by.
    intro t hall j hj
    obtain ⟨k, hk, s, hs⟩ := hall 0 ((correct_iff 0).2 (by decide))
    rw [partRun_at'_of_all (acs_all w)] at hs
    rw [partRun_clk_of_all (acs_all w)] at hk
    change (acsSt w k).prop 0 = some s at hs
    simp only [acsSt] at hs
    split_ifs at hs with hc
    rw [TimedRun.byGstBound_iff]
    refine ⟨dB w + 55, ?_, ?_⟩
    · rw [partRun_clk_of_all (acs_all w), partRun_gst]
      have hk : k / 56 ≤ t := hk
      show (dB w + 55) / 56 ≤ max t 0 + 2
      simp only [dB] at *
      omega
    · rw [partRun_at'_of_all (acs_all w)]
      exact acs_done w hw j ((correct_iff j).1 hj)
  · -- Δ-Totality: everyone decides at the same clock.
    intro n i hi hd j hj
    rw [partRun_at'_of_all (acs_all w)] at hd
    change decide _ = true at hd
    simp only [decide_eq_true_eq] at hd
    rw [TimedRun.byGstBound_iff]
    refine ⟨dB w + 55, ?_, ?_⟩
    · rw [partRun_clk_of_all (acs_all w), partRun_clk_of_all (acs_all w), partRun_gst]
      show (dB w + 55) / 56 ≤ max (n / 56) 0 + 1
      simp only [dB] at *
      omega
    · rw [partRun_at'_of_all (acs_all w)]
      exact acs_done w hw j ((correct_iff j).1 hj)

/-! ## The orchestrator's part -/

/-- The orchestrator, as a component of the composed system. -/
noncomputable abbrev OC := orchC (A := AS) 4 1 rfl isByz Chorus.Witness.hbyz thO thS thM thG

theorem orch_all (n : ℕ) : OSI.trans (OC.proj (run.at' n)) (OC.proj (run.at' (n + 1))) :=
  ⟨clbl n, ostep n⟩

/-- **The Conductor meets its timing model on the composed witness.** -/
theorem orchAdmissible : OrchAdmissible (A := AS) 4 1 rfl isByz Chorus.Witness.hbyz sch TA run := by
  refine ⟨projOfAll orch_all, crun, ?_, timedRows, openPunctual, clockAgrees, acsAdmissible⟩
  refine timedRun_ext (fun k => ?_) (fun k => ?_) rfl
  · rw [partRun_at'_of_all orch_all]; rfl
  · rw [partRun_clk_of_all orch_all]; rfl

end Composed.Witness

/-! ## The pinned trust base -/

/--
info: 'Composed.Witness.orchAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.orchAdmissible
