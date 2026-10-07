import Cadence.Composed.Witness.Run
import Cadence.Composed.Witness.Actions

/-! # Composed.Witness.Steps — every step of the composed witness is a transition

[ConductorBounds.md](../../../docs/ConductorBounds.md) §8.2, stage K8. The
run of [Run.lean](Run.lean), checked one plateau at a time: every step of
plateau `t` is a transition of the composed system for every `t`
(`gstep`), and so is the Conductor's own step under it (`cstep`). Each is
an action of [Actions.lean](Actions.lean) applied to the closed-form
states: its guards are linear arithmetic over the index, and so is every
field of the post-state. -/

namespace Composed.Witness

open Cadence Conductor Chorus
open scoped Cadence.Timed

attribute [local instance] Chorus.Witness.nsetC Chorus.Witness.cntC natViewOrder FM AS OSI SCI

/-! ## Index arithmetic -/

/-- Position `j` of plateau `t`. -/
theorem idx_eq (n : ℕ) : n = n / 61 * 61 + n % 61 := (Nat.div_add_mod' n 61).symm

theorem pos_lt (n : ℕ) : n % 61 < 61 := Nat.mod_lt n (by decide)

@[simp] theorem nd_val (k : ℕ) : (nd k).val = k % 4 := rfl

/-- Normalise a field equation of the closed-form states to arithmetic. -/
local macro "farith" : tactic =>
  `(tactic| (
    try simp only [cond, acsSt, gs, dB]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff, nd_val]
    omega))

/-! ## The Conductor's fields between two indices -/

theorem cond_now (n : ℕ) (h : n % 61 ≠ 60) : (cond (n + 1)).now = (cond n).now := by
  have := idx_eq n; have := pos_lt n
  show (n + 1) / 61 = n / 61
  omega

theorem acsSt_eq (w n : ℕ)
    (h : w ≠ n / 61 / 36 + 1 ∨ n / 61 % 36 ≠ 4 ∨ n % 61 < 30 ∨ 40 < n % 61 ∨ n % 61 = 37) :
    acsSt w (n + 1) = acsSt w n := by
  have := idx_eq n; have := pos_lt n
  simp only [acsSt, dB, IdealAcs.State.mk.injEq]
  refine ⟨funext fun i => ?_, ?_, funext fun i => ?_, funext fun i => ?_⟩
  · have := i.isLt; split_ifs <;> first | rfl | omega
  · split_ifs <;> first | rfl | omega
  · have := i.isLt; simp only [decide_eq_decide]; omega
  · have := i.isLt; simp only [decide_eq_decide]; omega

theorem cond_acs (n : ℕ) (h : n / 61 % 36 ≠ 4 ∨ n % 61 < 30 ∨ 40 < n % 61 ∨ n % 61 = 37) :
    (cond (n + 1)).acs_state = (cond n).acs_state :=
  funext fun w => acsSt_eq w n (by omega)

theorem cond_decided (n : ℕ) (h : n / 61 % 36 ≠ 4 ∨ n % 61 ≠ 37) :
    (cond (n + 1)).acs_decided = (cond n).acs_decided := by
  have := idx_eq n; have := pos_lt n
  funext w f b l
  simp only [cond, dB, decide_eq_decide]
  omega

theorem cond_entered (n : ℕ) (h : n / 61 % 36 ≠ 4 ∨ n % 61 < 38 ∨ 40 < n % 61) :
    (cond (n + 1)).entered = (cond n).entered := by
  have := idx_eq n; have := pos_lt n
  funext i w
  have := i.isLt
  simp only [cond, dB, decide_eq_decide]
  omega

theorem cond_opened (n : ℕ) (h : n % 61 < 41 ∨ 43 < n % 61) :
    (cond (n + 1)).opened = (cond n).opened := by
  have := idx_eq n; have := pos_lt n
  funext i s
  have := i.isLt
  simp only [cond, decide_eq_decide]
  omega

theorem cond_opened_win (n : ℕ) (h : n % 61 < 41 ∨ 43 < n % 61) :
    (cond (n + 1)).opened_win = (cond n).opened_win := by
  have := idx_eq n; have := pos_lt n
  funext i s w
  have := i.isLt
  simp only [cond, decide_eq_decide]
  omega

theorem cond_completed (n : ℕ) (h : n % 61 < 24 ∨ 26 < n % 61 ∨ n / 61 = 0) :
    (cond (n + 1)).completed = (cond n).completed := by
  have := idx_eq n; have := pos_lt n
  funext i s
  have := i.isLt
  simp only [cond, decide_eq_decide]
  omega

/-! ## The Conductor's steps -/

/-- The Conductor's transition system at the witness's types. -/
noncomputable abbrev CRTS := Conductor.relationalTransitionSystem ℕ ℕ ℕ (Fin 4) ACSt

theorem winBounds_of (n w : ℕ) (h : w = 0 ∨ (1 ≤ w ∧ dB w + 37 < n)) :
    WinBounds (th := thO) (cond n) w (w * 36) (w * 36 + 4) (w * 36 + 35) := by
  rcases h with rfl | h
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · right
    simp only [cond, decide_eq_true_eq, and_true]
    omega

theorem winBounds_iff (n w f b l : ℕ) :
    WinBounds (th := thO) (cond n) w f b l ↔
      (f = w * 36 ∧ b = w * 36 + 4 ∧ l = w * 36 + 35 ∧ (w = 0 ∨ (1 ≤ w ∧ dB w + 37 < n))) := by
  simp only [WinBounds, cond, decide_eq_true_eq, thO]
  show (w = 0 ∧ f = 0 ∧ b = 4 ∧ l = 35 ∨ _) ↔ _
  omega

/-- **A `tick` in place**, at a position with no Conductor event. -/
theorem cstep_stay (n : ℕ) (h55 : n % 61 ≠ 60) (hc : n % 61 < 24 ∨ 26 < n % 61 ∨ n / 61 = 0)
    (hw : n / 61 % 36 ≠ 4 ∨ n % 61 < 30 ∨ 40 < n % 61) (ho : n % 61 < 41 ∨ 43 < n % 61) :
    CRTS.tr thO (cond n) (.tick (n / 61)) (cond (n + 1)) :=
  tr_tick (TotalOrder.le_refl _) (cond_now n h55) (cond_acs n (by omega)) (cond_decided n (by omega))
    (cond_entered n (by omega)) (cond_opened n ho) (cond_opened_win n ho) (cond_completed n hc)

/-- **The clock's `tick`** at the end of a plateau. -/
theorem cstep_tick (n : ℕ) (h55 : n % 61 = 60) :
    CRTS.tr thO (cond n) (.tick (n / 61 + 1)) (cond (n + 1)) := by
  have := idx_eq n
  refine tr_tick (by show n / 61 ≤ n / 61 + 1; omega) ?_ (cond_acs n (by omega)) (cond_decided n (by omega))
    (cond_entered n (by omega)) (cond_opened n (by omega)) (cond_opened_win n (by omega))
    (cond_completed n (by omega))
  show (n + 1) / 61 = n / 61 + 1
  omega

/-- **`complete(t − 1)`** at a finalize handler. -/
theorem cstep_complete (n : ℕ) (h : 24 ≤ n % 61 ∧ n % 61 ≤ 26 ∧ 1 ≤ n / 61) :
    CRTS.tr thO (cond n) (.complete_slot (nd (n % 61 - 24)) (n / 61 - 1)) (cond (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  refine tr_complete_slot ((correct_iff _).2 (by simp; omega)) ?_ ?_ (cond_now n (by omega))
    (cond_acs n (by omega)) (cond_decided n (by omega)) (cond_entered n (by omega))
    (cond_opened n (by omega)) (cond_opened_win n (by omega)) ?_
  · simp only [cond, decide_eq_true_eq, nd_val]; omega
  · simp only [cond, decide_eq_false_iff_not, nd_val]; omega
  · intro i s; have := i.isLt; farith

/-- **`open(t)`** at `i`. -/
theorem cstep_open (n : ℕ) (h : 41 ≤ n % 61 ∧ n % 61 ≤ 43) :
    CRTS.tr thO (cond n) (.open_slot (nd (n % 61 - 41)) (n / 61) (n / 61 / 36) (n / 61 / 36 * 36)
      (n / 61 / 36 * 36 + 4) (n / 61 / 36 * 36 + 35)) (cond (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  refine tr_open_slot ((correct_iff _).2 (by simp; omega)) ?_ (winBounds_of n _ ?_) (by omega) (by omega)
    ?_ ?_ ?_ (cond_now n (by omega)) (cond_acs n (by omega)) (cond_decided n (by omega))
    (cond_entered n (by omega)) ?_ ?_ (cond_completed n (by omega))
  · simp only [cond, decide_eq_true_eq, nd_val, dB]; omega
  · simp only [dB]; omega
  · simp only [cond, decide_eq_false_iff_not, nd_val]; omega
  · show n / 61 ≤ n / 61; exact le_refl _
  · intro s' w0 f0 b0 l0 _ hb _ _ hlt
    simp only [cond, decide_eq_true_eq, nd_val]; omega
  · intro i s; have := i.isLt; farith
  · intro i s w; have := i.isLt; farith

/-! ### Window events

At plateau `t = 36w + 4`, window `w`'s readiness boundary, window `w + 1`'s
events. `dB (w + 1) = 61t`. -/

/-- Compare two ideal-ACS states field by field. -/
local macro "bclose" : tactic =>
  `(tactic| (
    try simp only [decide_eq_true_eq, decide_eq_false_iff_not, decide_eq_decide, Bool.true_eq,
      Bool.false_eq, Bool.not_eq_true, Option.some.injEq] at *
    try simp only [dB] at *
    omega))

/-- Compare two ideal-ACS states field by field. -/
local macro "acs_eq" : tactic =>
  `(tactic| (
    simp only [acsSt, cond, IdealAcs.State.mk.injEq]
    refine ⟨funext fun q => ?_, ?_, funext fun q => ?_, funext fun q => ?_⟩
    all_goals (try have := q.isLt)
    all_goals (try simp only [Function.update_apply, Fin.ext_iff, nd_val])
    all_goals first
      | rfl
      | (split_ifs <;> first
          | rfl
          | bclose
          | (simp only [Option.some.injEq, funext_iff]; intro; split_ifs <;> first | rfl | bclose))
      | bclose))

theorem dB_succ (w : ℕ) : dB (w + 1) = (w * 36 + 4) * 61 := by simp only [dB]; omega

/-- `i` is in window `w` at an index of window `w + 1`'s plateau before it
enters `w + 1`. -/
theorem inWindow_at (n : ℕ) (i : Fin 4) (hi : i.val < 3) (ht : n / 61 % 36 = 4)
    (hj : n % 61 ≤ 38 + i.val) :
    InWindow (cond n) i (n / 61 / 36) := by
  have := idx_eq n; have := pos_lt n
  refine ⟨?_, fun w' hw' => ?_⟩
  · simp only [cond, decide_eq_true_eq, dB]; omega
  · have hw' : n / 61 / 36 + 1 = w' := hw'
    simp only [cond, decide_eq_false_iff_not, dB]; omega

/-- `i` is ready to leave window `w` from its readiness boundary on: every
slot below `36w + 4` completed. -/
theorem readyNext_at (n : ℕ) (i : Fin 4) (hi : i.val < 3) (ht : n / 61 % 36 = 4)
    (hj : 24 + i.val < n % 61) :
    ReadyNext thO (cond n) i (n / 61 / 36) := by
  have := idx_eq n; have := pos_lt n
  intro f b l hb s w0 f0 b0 l0 _ _ _ _ hs
  rw [winBounds_iff] at hb
  simp only [cond, decide_eq_true_eq]
  omega

/-- **`i`'s proposal of `36(w + 1)` to window `w + 1`'s ACS.** -/
theorem cstep_propose (n : ℕ) (h : n / 61 % 36 = 4 ∧ 30 ≤ n % 61 ∧ n % 61 ≤ 32) :
    CRTS.tr thO (cond n) (.acs_propose (nd (n % 61 - 30)) (n / 61 / 36) (n / 61 / 36 + 1)
      ((n / 61 / 36 + 1) * 36) (acsSt (n / 61 / 36 + 1) (n + 1))) (cond (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  have hv := nd_val (n % 61 - 30)
  have hi : (nd (n % 61 - 30)).val < 3 := by omega
  refine tr_acs_propose ((correct_iff _).2 hi) (inWindow_at n _ hi h.1 (by simp; omega)) rfl ?_
    (readyNext_at n _ hi h.1 (by simp; omega)) ?_ ?_ ?_ ?_ (cond_now n (by omega)) ?_
    (cond_decided n (by omega)) (cond_entered n (by omega)) (cond_opened n (by omega))
    (cond_opened_win n (by omega)) (cond_completed n (by omega))
  · intro s' hp
    change (acsSt _ n).prop _ = some s' at hp
    simp only [acsSt, nd_val, dB] at hp
    split_ifs at hp with hc
    omega
  · intro w0 f0 b0 l0 hw0 hb
    have hw0 : w0 + 1 = n / 61 / 36 + 1 := hw0
    rw [winBounds_iff] at hb; omega
  · show n / 61 ≤ (n / 61 / 36 + 1) * 36; omega
  · intro s' w0 f0 b0 l0 hw0 hb h1 h2
    have hw0 : w0 + 1 = n / 61 / 36 + 1 := hw0
    rw [winBounds_iff] at hb; omega
  · refine ⟨?_, ?_⟩
    · show (acsSt _ n).prop _ = none
      simp only [acsSt, nd_val, dB]; split_ifs <;> first | rfl | omega
    · acs_eq
  · intro x
    split_ifs with hx
    · subst hx; rfl
    · exact acsSt_eq x n (Or.inl hx)

/-- **Window `w + 1`'s ACS fixes its decided set**: the three correct
validators' pairs. -/
theorem cstep_core (n : ℕ) (h : n / 61 % 36 = 4 ∧ n % 61 = 33) :
    CRTS.tr thO (cond n) (.acs_step (n / 61 / 36 + 1) (acsSt (n / 61 / 36 + 1) (n + 1))) (cond (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  refine tr_acs_step ?_ (cond_now n (by omega)) ?_ (cond_decided n (by omega)) (cond_entered n (by omega))
    (cond_opened n (by omega)) (cond_opened_win n (by omega)) (cond_completed n (by omega))
  · refine Or.inr (Or.inr (Or.inl ⟨?_, fun q => if q.val < 3 then some ((n / 61 / 36 + 1) * 36) else none,
      ⟨fun p s hp hc => ?_, fun k => ⟨k.val, by omega⟩, fun a b hab => ?_, fun k => ?_⟩, ?_⟩))
    · show (acsSt _ n).core = none
      simp only [acsSt, dB]; split_ifs <;> first | rfl | omega
    · have hp' : p.val < 3 := (correct_iff p).1 hp
      simp only [hp', if_true, Option.some.injEq] at hc
      show (acsSt _ n).prop p = some s
      simp only [acsSt, dB]; split_ifs <;> first | (subst hc; rfl) | omega
    · simp only [Fin.mk.injEq] at hab; exact Fin.ext hab
    · simp only [show k.val < 3 from k.isLt, if_true, Option.isSome_some]
    · acs_eq
  · intro x
    split_ifs with hx
    · subst hx; rfl
    · exact acsSt_eq x n (Or.inl hx)

/-- **`i`'s decision in window `w + 1`'s ACS.** -/
theorem cstep_out (n : ℕ) (h : n / 61 % 36 = 4 ∧ 34 ≤ n % 61 ∧ n % 61 ≤ 36) :
    CRTS.tr thO (cond n) (.acs_step (n / 61 / 36 + 1) (acsSt (n / 61 / 36 + 1) (n + 1))) (cond (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  refine tr_acs_step ?_ (cond_now n (by omega)) ?_ (cond_decided n (by omega)) (cond_entered n (by omega))
    (cond_opened n (by omega)) (cond_opened_win n (by omega)) (cond_completed n (by omega))
  · refine Or.inr (Or.inr (Or.inr ⟨nd (n % 61 - 34), ?_, ?_, ?_⟩))
    · show (acsSt _ n).core.isSome
      simp only [acsSt, dB]; split_ifs <;> first | rfl | omega
    · show ((acsSt _ n).prop _).isSome
      simp only [acsSt, dB, nd_val]; split_ifs <;> first | rfl | omega
    · acs_eq
  · intro x
    split_ifs with hx
    · subst hx; rfl
    · exact acsSt_eq x n (Or.inl hx)

/-- **The recording of window `w + 1`'s interval**, `[36(w + 1), 36(w + 1) + 35]`,
from validator 0's decided pair, at both brackets. -/
theorem cstep_decide (n : ℕ) (h : n / 61 % 36 = 4 ∧ n % 61 = 37) :
    CRTS.tr thO (cond n) (.acs_decide (n / 61 / 36) (n / 61 / 36 + 1) ((n / 61 / 36 + 1) * 36)
      (n / 61 / 36 * 36) (n / 61 / 36 * 36 + 4) (n / 61 / 36 * 36 + 35) 0 ((n / 61 / 36 + 1) * 36) 0
      ((n / 61 / 36 + 1) * 36)) (cond (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  have hdec : ∃ i, ¬ FM.byz i ∧ AS.decided ((cond n).acs_state (n / 61 / 36 + 1)) i 0
      ((n / 61 / 36 + 1) * 36) := by
    refine ⟨0, (correct_iff 0).2 (by decide), ?_,
      fun q => if q.val < 3 then some ((n / 61 / 36 + 1) * 36) else none, ?_, ?_⟩
    · show decide _ = true; simp only [decide_eq_true_eq, dB]; omega
    · show (acsSt _ n).core = _; simp only [acsSt, dB]; rw [if_pos (by omega)]
    · simp
  refine tr_acs_decide (by show n / 61 / 36 + 1 ≠ 0; omega) ?_ ?_ rfl (winBounds_of n _ ?_)
    ((correct_iff 0).2 (by decide)) hdec le_rfl ((correct_iff 0).2 (by decide)) hdec le_rfl
    (cond_now n (by omega)) (cond_acs n (by omega)) ?_ (cond_entered n (by omega))
    (cond_opened n (by omega)) (cond_opened_win n (by omega)) (cond_completed n (by omega))
  · intro f b l; simp only [cond, decide_eq_true_eq, dB]; omega
  · intro i _; have := i.isLt; simp only [cond, decide_eq_true_eq, dB]; omega
  · simp only [dB]; omega
  · intro x f b l
    simp only [cond, thO]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, dB]
    omega

/-- **`i`'s entry into window `w + 1`**, abandoning its ACS. -/
theorem cstep_enter (n : ℕ) (h : n / 61 % 36 = 4 ∧ 38 ≤ n % 61 ∧ n % 61 ≤ 40) :
    CRTS.tr thO (cond n) (.enter_window (nd (n % 61 - 38)) (n / 61 / 36) (n / 61 / 36 + 1)
      ((n / 61 / 36 + 1) * 36) ((n / 61 / 36 + 1) * 36 + 4) ((n / 61 / 36 + 1) * 36 + 35)
      (acsSt (n / 61 / 36 + 1) (n + 1))) (cond (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  have hv := nd_val (n % 61 - 38)
  have hi : (nd (n % 61 - 38)).val < 3 := by omega
  refine tr_enter_window ((correct_iff _).2 hi) (inWindow_at n _ hi h.1 (by simp; omega)) rfl ?_ ?_
    (readyNext_at n _ hi h.1 (by simp; omega)) ?_ (cond_now n (by omega)) ?_ (cond_decided n (by omega))
    ?_ (cond_opened n (by omega)) (cond_opened_win n (by omega)) (cond_completed n (by omega))
  · simp only [cond, decide_eq_true_eq, dB, and_true]; omega
  · show decide _ = true; simp only [decide_eq_true_eq, dB, nd_val]; omega
  · show acsSt _ (n + 1) = _
    acs_eq
  · intro x
    split_ifs with hx
    · subst hx; rfl
    · exact acsSt_eq x n (Or.inl hx)
  · intro i w; have := i.isLt; farith

/-- **Every step of the Conductor's run is a transition.** -/
theorem ostep (n : ℕ) : CRTS.tr thO (cond n) (clbl n) (cond (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  simp only [clbl]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · exact cstep_complete n h1
  · exact cstep_propose n h2
  · by_cases h33 : n % 61 = 33
    · exact cstep_core n ⟨h3.1, h33⟩
    · exact cstep_out n ⟨h3.1, by omega, h3.2.2⟩
  · exact cstep_decide n h4
  · exact cstep_enter n h5
  · exact cstep_open n h6
  · exact cstep_tick n h7
  · exact cstep_stay n h7 (by omega) (by omega) (by omega)

/-! ## The slots' local indices between two indices -/

/-- Index `n` is one of slot `x`'s steps. -/
def SlotStep (x n : ℕ) : Prop :=
  (x * 61 + 44 ≤ n ∧ n < x * 61 + 51) ∨ (x * 61 + 63 ≤ n ∧ n < x * 61 + 88) ∨
    (x * 61 + 112 ≤ n ∧ n < x * 61 + 121) ∨ n = x * 61 + 123 ∨ n = x * 61 + 183

/-- One block of a slot's steps across one index. -/
theorem min_succ (n a c : ℕ) :
    min (n + 1 - a) c = min (n - a) c + if a ≤ n ∧ n < a + c then 1 else 0 := by
  split_ifs <;> omega

theorem loc_succ_of {x n : ℕ} (h : SlotStep x n) : loc x (n + 1) = loc x n + 1 := by
  simp only [loc, min_succ]
  simp only [SlotStep] at h
  split_ifs <;> omega

theorem loc_succ_of_not {x n : ℕ} (h : ¬ SlotStep x n) : loc x (n + 1) = loc x n := by
  simp only [loc, min_succ]
  simp only [SlotStep] at h
  split_ifs <;> omega

/-- At index 0 every slot is at its initial local state. -/
theorem loc_zero (x : ℕ) : loc x 0 = 0 := by simp [loc]

/-! ## The slots' steps, as the contract sees them -/

theorem lab_not_input (m : ℕ) (h1 : 4 ≤ m) (h2 : m < 43) (h3 : m < 29 ∨ 31 < m) :
    ¬ Chorus.Label.isInput (lab m) := by
  interval_cases m <;> first | omega | simp [lab, Chorus.Label.isInput]

/-- An internal step of a slot's instance. -/
theorem sc_step_of (x m : ℕ) (h1 : 4 ≤ m) (h2 : m < 43) (h3 : m < 29 ∨ 31 < m) :
    SCI.step (x, cst m) (x, cst (m + 1)) :=
  ⟨rfl, lab m, lab_not_input m h1 h2 h3, cstep m h2⟩

/-- The Conductor's state does not change at a position without a
Conductor event. -/
theorem cond_eq (n : ℕ) (h55 : n % 61 ≠ 60) (hc : n % 61 < 24 ∨ 26 < n % 61 ∨ n / 61 = 0)
    (hw : n / 61 % 36 ≠ 4 ∨ n % 61 < 30 ∨ 40 < n % 61) (ho : n % 61 < 41 ∨ 43 < n % 61) :
    cond (n + 1) = cond n := by
  have h1 := cond_now n h55
  have h2 := cond_acs n (by omega)
  have h3 := cond_decided n (by omega)
  have h4 := cond_entered n (by omega)
  have h5 := cond_opened n ho
  have h6 := cond_opened_win n ho
  have h7 := cond_completed n hc
  revert h1 h2 h3 h4 h5 h6 h7
  generalize cond (n + 1) = a
  generalize cond n = b
  obtain ⟨_, _, _, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _, _, _⟩ := b
  intro h1 h2 h3 h4 h5 h6 h7
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

/-- The local records of the composed state between two indices: what is
delivered, appended and resolved. -/
theorem gs_delivered (n : ℕ) (h : n % 61 < 24 ∨ 26 < n % 61 ∨ n / 61 = 0) :
    (gs (n + 1)).delivered = (gs n).delivered := by
  have := idx_eq n; have := pos_lt n
  funext i x v; have := i.isLt
  simp only [gs, decide_eq_decide]
  by_cases hv : v = vec x
  · simp only [hv, and_true]; omega
  · simp only [hv, and_false]

theorem gs_appended (n : ℕ) (h : n % 61 < 27 ∨ 29 < n % 61 ∨ n / 61 = 0) :
    (gs (n + 1)).appended = (gs n).appended := by
  have := idx_eq n; have := pos_lt n
  funext i x v; have := i.isLt
  simp only [gs, decide_eq_decide]
  by_cases hv : v = vec x
  · simp only [hv, and_true]; omega
  · simp only [hv, and_false]

theorem gs_resolved (n : ℕ) (h : n % 61 < 27 ∨ 29 < n % 61 ∨ n / 61 = 0) :
    (gs (n + 1)).resolved = (gs n).resolved := by
  have := idx_eq n; have := pos_lt n
  funext i x; have := i.isLt
  simp only [gs, decide_eq_decide]; omega

/-! ## The composed steps -/

/-- **An internal step of slot `x`'s instance** at local index `m`. -/
theorem gstep_sc (n x m : ℕ) (hx : SlotStep x n) (hm : loc x n = m) (h1 : 4 ≤ m) (h2 : m < 43)
    (h3 : m < 29 ∨ 31 < m) (hy : ∀ y, y ≠ x → ¬ SlotStep y n) (hcond : cond (n + 1) = cond n)
    (hd : (gs (n + 1)).delivered = (gs n).delivered) (ha : (gs (n + 1)).appended = (gs n).appended)
    (hr : (gs (n + 1)).resolved = (gs n).resolved) :
    SYS.tr thG (gs n) (.sc_step x (x, cst (m + 1))) (gs (n + 1)) := by
  refine tr_sc_step (orch := OSI) (sc := SCI) ?_ hcond ?_ rfl hr hd ha
  · show SCI.step (x, cst (loc x n)) _
    rw [hm]; exact sc_step_of x m h1 h2 h3
  · intro y
    by_cases hyx : y = x
    · subst hyx; rw [if_pos rfl]
      show (y, cst (loc y (n + 1))) = _
      rw [loc_succ_of hx, hm]
    · rw [if_neg hyx]
      show (y, cst (loc y (n + 1))) = (y, cst (loc y n))
      rw [loc_succ_of_not (hy y hyx)]

/-- Validator `k`'s participation in a slot, its first `k` local steps. -/
theorem sc_participate_of (x k : ℕ) (hk : k < 3) :
    SCI.participate (x, cst k) (nd k) (x, cst (k + 1)) := by
  refine ⟨rfl, ?_⟩
  have := cstep k (by omega)
  interval_cases k <;> exact this

/-- Validator 0's proposal, the slot's local step 3. -/
theorem sc_propose_of (x : ℕ) : SCI.propose (x, cst 3) 0 () (x, cst 4) :=
  ⟨rfl, cstep 3 (by decide)⟩

/-- Validator `k`'s `abandon()`, the slot's local step `29 + k`. -/
theorem sc_abandon_of (x k : ℕ) (hk : k < 3) :
    SCI.abandon (x, cst (29 + k)) (nd k) (x, cst (29 + k + 1)) := by
  refine ⟨rfl, ?_⟩
  have := cstep (29 + k) (by omega)
  interval_cases k <;> exact ⟨_, this⟩

/-- **Validator `k` has finalized** a slot from its local step `27 + k` on,
with the slot's vector: validator 0's root, nothing for the others. -/
theorem sc_finalized_of (x k m : ℕ) (hk : k < 3) (hm : 26 + k < m) :
    SCI.finalized (x, cst m) (nd k) (vec x) := by
  refine ⟨?_, ?_⟩
  · show decide _ = true
    simp only [decide_eq_true_eq, nd_val]; omega
  · show vec x = (x, decisionVector thS (cst m) (nd k))
    simp only [vec, Prod.mk.injEq, true_and]
    funext J
    simp only [decisionVector, thS, Cadence.chorusTheory, decide_eq_true_eq]
    by_cases hJ : J.val = 0
    · have hex : ∃ M, CommittedPos (cst m) (nd k) J M := ⟨(), by
        show decide _ = true; simp only [decide_eq_true_eq, nd_val]; omega⟩
      rw [if_pos hJ, if_pos hJ, dif_pos hex]
    · rw [if_neg hJ, if_neg hJ]

/-- **An orchestrator step** at a position where no slot steps. -/
theorem gstep_orch (n : ℕ) (hs : ∀ y, ¬ SlotStep y n) (hnc : ¬ Conductor.Label.isComplete (clbl n))
    (hd : (gs (n + 1)).delivered = (gs n).delivered) (ha : (gs (n + 1)).appended = (gs n).appended)
    (hr : (gs (n + 1)).resolved = (gs n).resolved) :
    SYS.tr thG (gs n) (.orch_step (cond (n + 1))) (gs (n + 1)) := by
  refine tr_orch_step (orch := OSI) (sc := SCI) ⟨clbl n, hnc, ostep n⟩ rfl ?_ rfl hr hd ha
  funext y
  show (y, cst (loc y (n + 1))) = (y, cst (loc y n))
  rw [loc_succ_of_not (hs y)]

/-- Expose a slot's post-state field. -/
theorem sc_field (n x m : ℕ) (hx : SlotStep x n) (hm : loc x n = m) (hy : ∀ y, y ≠ x → ¬ SlotStep y n)
    (y : ℕ) [Decidable (y = x)] :
    (gs (n + 1)).sc_state y = if y = x then (x, cst (m + 1)) else (gs n).sc_state y := by
  by_cases hyx : y = x
  · subst hyx; rw [if_pos rfl]
    show (y, cst (loc y (n + 1))) = _
    rw [loc_succ_of hx, hm]
  · rw [if_neg hyx]
    show (y, cst (loc y (n + 1))) = (y, cst (loc y n))
    rw [loc_succ_of_not (hy y hyx)]

/-- **Validator `k`'s participation in slot `t`**, at position `44 + k`. -/
theorem gstep_open (n k : ℕ) (hk : k < 3) (hj : n % 61 = 44 + k) :
    SYS.tr thG (gs n) (.on_open (nd k) (n / 61) (n / 61, cst (k + 1))) (gs (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  have hx : SlotStep (n / 61) n := by simp only [SlotStep]; omega
  have hm : loc (n / 61) n = k := by simp only [loc]; omega
  refine tr_on_open (orch := OSI) (sc := SCI) ((correct_iff _).2 (by simp; omega)) ?_ ?_ ?_
    (cond_eq n (by omega) (by omega) (by omega) (by omega))
    (fun y => @sc_field n _ k hx hm (fun y hy => by simp only [SlotStep]; omega) y (Classical.propDecidable _)) rfl
    (gs_resolved n (by omega)) (gs_delivered n (by omega)) (gs_appended n (by omega))
  · show decide _ = true; simp only [decide_eq_true_eq, nd_val]; omega
  · show ¬ (cst (loc _ n)).participating _ = true
    rw [hm]; simp only [cst, decide_eq_true_eq, nd_val]; omega
  · show SCI.participate (n / 61, cst (loc _ n)) _ _
    rw [hm]; exact sc_participate_of _ k hk

/-- **Validator 0's proposal in slot `t`**, at position 47. -/
theorem gstep_propose (n : ℕ) (hj : n % 61 = 47) :
    SYS.tr thG (gs n) (.on_propose 0 (n / 61) () (n / 61, cst 4)) (gs (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  have hx : SlotStep (n / 61) n := by simp only [SlotStep]; omega
  have hm : loc (n / 61) n = 3 := by simp only [loc]; omega
  refine tr_on_propose (orch := OSI) (sc := SCI) ((correct_iff _).2 (by decide)) ?_ ?_ rfl ?_ ?_
    (cond_eq n (by omega) (by omega) (by omega) (by omega))
    (fun y => @sc_field n _ 3 hx hm (fun y hy => by simp only [SlotStep]; omega) y (Classical.propDecidable _)) rfl
    (gs_resolved n (by omega)) (gs_delivered n (by omega)) (gs_appended n (by omega))
  · show decide _ = true; simp only [decide_eq_true_eq]; omega
  · show (cst (loc _ n)).participating _ = true
    rw [hm]; simp only [cst, decide_eq_true_eq]; decide
  · intro q
    show ¬ (cst (loc _ n)).msg_proposer_signed _ _ = true
    rw [hm]; simp only [cst, decide_eq_true_eq]; omega
  · show SCI.propose (n / 61, cst (loc _ n)) _ _ _
    rw [hm]; exact sc_propose_of _

/-- **Validator `k`'s finalize handler for slot `t − 1`**, at position
`24 + k`: `complete(t − 1)` to the Conductor and `abandon()` to the slot. -/
theorem gstep_finalize (n k : ℕ) (hk : k < 3) (hj : n % 61 = 24 + k) (ht : 1 ≤ n / 61) :
    SYS.tr thG (gs n) (.on_finalize (nd k) (n / 61 - 1) (vec (n / 61 - 1)) (cond (n + 1))
      (n / 61 - 1, cst (29 + k + 1))) (gs (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  have hx : SlotStep (n / 61 - 1) n := by simp only [SlotStep]; omega
  have hm : loc (n / 61 - 1) n = 29 + k := by simp only [loc]; omega
  have hc := cstep_complete n (by omega)
  rw [hj, show 24 + k - 24 = k by omega] at hc
  refine tr_on_finalize (orch := OSI) (sc := SCI) ((correct_iff _).2 (by simp; omega)) ?_ ?_ ?_ hc ?_ rfl
    (fun y => @sc_field n _ (29 + k) hx hm (fun y hy => by simp only [SlotStep]; omega) y (Classical.propDecidable _)) rfl
    (gs_resolved n (by omega)) ?_ (gs_appended n (by omega))
  · show decide _ = true; simp only [decide_eq_true_eq, nd_val]; omega
  · show SCI.finalized (_, cst (loc _ n)) _ _
    rw [hm]; exact sc_finalized_of _ k _ hk (by omega)
  · intro v; show decide _ = false
    simp only [decide_eq_false_iff_not, nd_val]; omega
  · show SCI.abandon (_, cst (loc _ n)) _ _
    rw [hm]; exact sc_abandon_of _ k hk
  · intro i y v; have := i.isLt
    simp only [gs]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff, nd_val]
    by_cases hv : v = vec y
    · subst hv
      by_cases hy : y = n / 61 - 1
      · subst hy; simp only [and_true]; omega
      · have : vec y ≠ vec (n / 61 - 1) := fun h => hy (congrArg Prod.fst h)
        simp only [this, and_true, and_false, false_or]
        omega
    · simp only [hv, and_false, false_iff, or_false]
      rintro ⟨_, rfl, h⟩; exact hv h

/-- **Validator `k`'s append of slot `t − 1`'s vector**, at position
`27 + k`. -/
theorem gstep_append (n k : ℕ) (hk : k < 3) (hj : n % 61 = 27 + k) (ht : 1 ≤ n / 61) :
    SYS.tr thG (gs n) (.append (nd k) (n / 61 - 1) (vec (n / 61 - 1))) (gs (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  refine tr_append (orch := OSI) (sc := SCI) ((correct_iff _).2 (by simp; omega)) ?_ ?_ ?_
    (cond_eq n (by omega) (by omega) (by omega) (by omega)) ?_ rfl ?_ (gs_delivered n (by omega)) ?_
  · show decide _ = true; simp only [decide_eq_true_eq, nd_val, and_true]; omega
  · intro v; show decide _ = false; simp only [decide_eq_false_iff_not, nd_val]; omega
  · intro y hy hne
    have hy : y ≤ n / 61 - 1 := hy
    show decide _ = true; simp only [decide_eq_true_eq, nd_val]; omega
  · funext y
    show (y, cst (loc y (n + 1))) = (y, cst (loc y n))
    rw [loc_succ_of_not (by simp only [SlotStep]; omega)]
  · intro i y; have := i.isLt
    simp only [gs]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff, nd_val]
    omega
  · intro i y v; have := i.isLt
    simp only [gs]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff, nd_val]
    by_cases hv : v = vec y
    · subst hv
      by_cases hy : y = n / 61 - 1
      · subst hy; simp only [and_true]; omega
      · have : vec y ≠ vec (n / 61 - 1) := fun h => hy (congrArg Prod.fst h)
        simp only [this, and_true, and_false, false_or]
        omega
    · simp only [hv, and_false, false_iff, or_false]
      rintro ⟨_, rfl, h⟩; exact hv h

/-- The Conductor's label is the `complete` input only at a finalize handler. -/
theorem clbl_not_complete (n : ℕ) (h : ¬ (24 ≤ n % 61 ∧ n % 61 ≤ 26 ∧ 1 ≤ n / 61)) :
    ¬ Conductor.Label.isComplete (clbl n) := by
  simp only [clbl]
  split_ifs <;> first | omega | simp [Conductor.Label.isComplete]

/-- **Every step of the composed run is a transition of the composed
system.** -/
theorem gstep (n : ℕ) : SYS.tr thG (gs n) (glbl n) (gs (n + 1)) := by
  have := idx_eq n; have := pos_lt n
  simp only [glbl]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  · exact gstep_sc n (n / 61 - 3) 42 (by simp only [SlotStep]; omega) (by simp only [loc]; omega)
      (by omega) (by omega) (by omega) (fun y hy => by simp only [SlotStep]; omega)
      (cond_eq n (by omega) (by omega) (by omega) (by omega)) (gs_delivered n (by omega))
      (gs_appended n (by omega)) (gs_resolved n (by omega))
  · exact gstep_sc n (n / 61 - 2) 41 (by simp only [SlotStep]; omega) (by simp only [loc]; omega)
      (by omega) (by omega) (by omega) (fun y hy => by simp only [SlotStep]; omega)
      (cond_eq n (by omega) (by omega) (by omega) (by omega)) (gs_delivered n (by omega))
      (gs_appended n (by omega)) (gs_resolved n (by omega))
  · have := gstep_sc n (n / 61 - 1) (n % 61 + 5) (by simp only [SlotStep]; omega)
      (by simp only [loc]; omega) (by omega) (by omega) (by omega)
      (fun y hy => by simp only [SlotStep]; omega)
      (cond_eq n (by omega) (by omega) (by omega) (by omega)) (gs_delivered n (by omega))
      (gs_appended n (by omega)) (gs_resolved n (by omega))
    rwa [show n % 61 + 5 + 1 = n % 61 + 6 by omega] at this
  · have := gstep_finalize n (n % 61 - 24) (by omega) (by omega) h4.2.2
    rwa [show 29 + (n % 61 - 24) + 1 = n % 61 + 6 by omega] at this
  · exact gstep_append n (n % 61 - 27) (by omega) (by omega) h5.2.2
  · have := gstep_open n (n % 61 - 44) (by omega) (by omega)
    rwa [show n % 61 - 44 + 1 = n % 61 - 43 by omega] at this
  · exact gstep_propose n h7
  · have := gstep_sc n (n / 61) (n % 61 - 44) (by simp only [SlotStep]; omega)
      (by simp only [loc]; omega) (by omega) (by omega) (by omega)
      (fun y hy => by simp only [SlotStep]; omega)
      (cond_eq n (by omega) (by omega) (by omega) (by omega)) (gs_delivered n (by omega))
      (gs_appended n (by omega)) (gs_resolved n (by omega))
    rwa [show n % 61 - 44 + 1 = n % 61 - 43 by omega] at this
  · have := gstep_sc n (n / 61 - 1) (n % 61 - 19) (by simp only [SlotStep]; omega)
      (by simp only [loc]; omega) (by omega) (by omega) (by omega)
      (fun y hy => by simp only [SlotStep]; omega)
      (cond_eq n (by omega) (by omega) (by omega) (by omega)) (gs_delivered n (by omega))
      (gs_appended n (by omega)) (gs_resolved n (by omega))
    rwa [show n % 61 - 19 + 1 = n % 61 - 18 by omega] at this
  · exact gstep_orch n (fun y => by simp only [SlotStep]; omega) (clbl_not_complete n (by omega))
      (gs_delivered n (by omega)) (gs_appended n (by omega)) (gs_resolved n (by omega))

/-! ## The run -/

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation. -/
local macro "fs" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id])

/-- The Conductor's assumptions at `thO`. -/
theorem cholds : CRTS.assumptions thO := by
  simp only [CRTS, Conductor.relationalTransitionSystem, Conductor.Assumptions, Conductor.acs_init,
    Conductor.shift_shape, Conductor.genesis_window, Conductor.start_time_strict]
  fs
  refine ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun s => ⟨?_, ?_⟩, ⟨rfl, rfl, rfl⟩, fun s s' h => ⟨?_, ?_⟩⟩
  · show s ≤ s + 4; omega
  · show s + 4 ≤ s + 35; omega
  · have h : s < s' := h; show s ≤ s'; omega
  · have h : s < s' := h; show ¬ s = s'; omega

/-- The Conductor's initial `entered` record compares windows by a
classical `==`. -/
theorem beq_cl (a b : ℕ) :
    (@BEq.beq ℕ (@instBEqOfDecidableEq ℕ fun x y => Classical.propDecidable (x = y)) a b) =
      decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- The Conductor starts at index 0's state. -/
theorem cstarts : CRTS.init thO (cond 0) := by
  simp only [CRTS, Conductor.relationalTransitionSystem, Conductor.Init, trSimp]
  fs
  simp only [cond, thO, acsSt, acs0, Conductor.State.mk.injEq, funext_iff, IdealAcs.State.mk.injEq]
  and_intros <;> intros <;> first
    | trivial
    | rfl
    | (split_ifs <;> first | rfl | omega)
    | (simp only [eq_comm (a := false), decide_eq_false_iff_not]; omega)
    | (rw [beq_cl, decide_eq_decide]; show _ = (0 : ℕ) ↔ _; omega)
    | (refine ⟨fun q => ?_, ?_, fun q => ?_, fun q => ?_⟩ <;> first
        | (split_ifs <;> first | rfl | omega)
        | (simp only [eq_comm (a := false), decide_eq_false_iff_not]; omega))

/-- The glue's assumptions at `thG`: the Conductor and every slot start
initial, and every slot is tagged with its number. -/
theorem gholds : SYS.assumptions thG := by
  simp only [SYS, sysRTS, Cadence.relationalTransitionSystem, Cadence.Assumptions, Cadence.orch_init,
    Cadence.sc_init, Cadence.sc_tag_init]
  fs
  exact ⟨⟨cholds, cstarts⟩, fun _ => ⟨holds, starts⟩, fun _ => rfl⟩

/-- The composed system starts at index 0's state. -/
theorem gstarts : SYS.init thG (gs 0) := by
  simp only [SYS, sysRTS, Cadence.relationalTransitionSystem, Cadence.Init, trSimp]
  fs
  simp only [gs, thG, loc_zero, Cadence.State.mk.injEq, funext_iff]
  and_intros <;> intros <;> first
    | trivial
    | rfl
    | (simp only [eq_comm (a := false), decide_eq_false_iff_not]; omega)

/-- **The composed witness's run**: plateau `t` is clock `t`, GST is 0. -/
noncomputable def run : TSysRun 4 1 rfl isByz Chorus.Witness.hbyz thO thS thM thG :=
  plateauRun 61 (by decide) gs glbl gholds gstarts (fun _ _ _ => gstep _)

@[simp] theorem run_at' (n : ℕ) : run.at' n = gs n := rfl
@[simp] theorem run_lbl (n : ℕ) : run.lbl n = glbl n := rfl
@[simp] theorem run_clk (n : ℕ) : run.clk n = n / 61 := rfl
@[simp] theorem run_gst : run.gst = 0 := rfl

end Composed.Witness

/-! ## The pinned trust base -/

/--
info: 'Composed.Witness.ostep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.ostep

/--
info: 'Composed.Witness.gstep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.gstep

/--
info: 'Composed.Witness.run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.run
