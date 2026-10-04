import Cadence.Composed.Witness.Steps

/-! # Composed.Witness.Slots — every slot's Chorus meets its timing model

[ConductorBounds.md](../../../docs/ConductorBounds.md) §8.2, stage K8.
`SlotAdmissible` and `SlotInclusive` ([Composed/Schedule.lean](../Schedule.lean))
on the run of [Steps.lean](Steps.lean).

Slot `x` takes its first step at composed index `56x + 44` (validator 0's
`participate`), and from there it is related to itself across every step:
by its own transition at its steps, by a stutter elsewhere ([Slot.lean](Slot.lean),
`stut_tr`). Before, it sits in its initial state, which cannot stutter
(`no_stutter_init`). So its part of the run is the initial state and then
the composed run from `56x + 44` on (`entry_of_from`).

`k` indices after its first step, a slot is at local index `S k`, the same
for every slot. So every slot's Chorus run is **one labelled run** (`srun x`)
whose clock is shifted by the slot's number: the composed witness's
periodicity, one slot at a time. Its premises are the Chorus witness's,
proven the same way: no row is enabled at the end of any clock reading, the
MVBA stays quiet and is abandoned, the markers fire at the landmarks. -/

namespace Composed.Witness

open Cadence Conductor Chorus
open scoped Cadence.Timed

attribute [local instance] Chorus.Witness.nsetC Chorus.Witness.cntC natViewOrder FM AS OSI SCI

/-! ## The local run -/

/-- The local index `k` composed steps after a slot's first. -/
def S (k : ℕ) : ℕ := min k 11 + min (k - 14) 25 + min (k - 69) 1 + min (k - 124) 1

/-- `k` composed steps after its first, the slot takes a step of its own. -/
def Step (k : ℕ) : Prop := k < 11 ∨ (14 ≤ k ∧ k < 39) ∨ k = 69 ∨ k = 124

instance : DecidablePred Step := fun k => by unfold Step; infer_instance

theorem loc_shift (x k : ℕ) : loc x (x * 56 + 44 + k) = S k := by
  simp only [loc, S]; omega

theorem slotStep_shift (x k : ℕ) : SlotStep x (x * 56 + 44 + k) ↔ Step k := by
  simp only [SlotStep, Step]; omega

theorem S_succ_of {k : ℕ} (h : Step k) : S (k + 1) = S k + 1 := by
  simp only [S, Step] at *; omega

theorem S_succ_of_not {k : ℕ} (h : ¬ Step k) : S (k + 1) = S k := by
  simp only [S, Step] at *; omega

/-- A slot's own label `k` steps after its first: its local step, or its
stutter. -/
def ulbl (k : ℕ) : CL := if Step k then lab (S k) else stut (S k)

theorem ustep (k : ℕ) : sys.tr thS (cst (S k)) (ulbl k) (cst (S (k + 1))) := by
  by_cases h : Step k
  · rw [ulbl, if_pos h, S_succ_of h]
    exact cstep _ (by simp only [S, Step] at *; omega)
  · rw [ulbl, if_neg h, S_succ_of_not h]
    exact stut_tr _ (by simp only [S, Step] at *; omega)

/-- **Slot `x`'s Chorus run**: the local states `cst (S k)`, the slot's own
labels, the clock `0` at its initial state and the composed clock after. -/
noncomputable def srun (x : ℕ) : TChorusRun thS thM ℕ where
  at' k := cst (S k)
  lbl := ulbl
  holds := holds
  starts := by simp only [S]; exact starts
  steps := ustep
  clk k := if k = 0 then 0 else x + (44 + k) / 56
  clk_mono k := by
    rcases k with _ | k
    · simp
    · rw [if_neg (Nat.succ_ne_zero k), if_neg (Nat.succ_ne_zero (k + 1))]; omega
  clk_unbounded t := ⟨t * 56 + 1, by rw [if_neg (Nat.succ_ne_zero _)]; omega⟩
  gst := 0

@[simp] theorem srun_at' (x k : ℕ) : (srun x).at' k = cst (S k) := rfl
@[simp] theorem srun_lbl (x k : ℕ) : (srun x).lbl k = ulbl k := rfl
@[simp] theorem srun_clk (x k : ℕ) : (srun x).clk k = if k = 0 then 0 else x + (44 + k) / 56 := rfl
@[simp] theorem srun_gst (x : ℕ) : (srun x).gst = 0 := rfl

/-! ## Quiet ends -/

/-- The local states the clock may move out of. -/
def QS (m : ℕ) : Prop := m = 0 ∨ m = 11 ∨ m = 36 ∨ m = 37 ∨ 38 ≤ m

theorem quietS {m : ℕ} (hm : QS m) {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (cst m) l := by
  rcases hm with rfl | rfl | rfl | rfl | hm
  · exact quiet0 hh ha
  · exact quiet11 hh ha
  · exact quiet36 hh ha
  · exact quiet37 hh ha
  · rw [cst_stable hm]; exact quiet38 hh ha

/-- Every index of the slot's run is followed, on the same clock reading, by
a quiet one. -/
theorem qend (x N : ℕ) : ∃ P, N ≤ P ∧ (srun x).clk P = (srun x).clk N ∧ QS (S P) := by
  by_cases h0 : N = 0
  · subst h0; exact ⟨0, le_rfl, rfl, Or.inl rfl⟩
  · refine ⟨(44 + N) / 56 * 56 + 11, by omega, ?_, ?_⟩
    · rw [srun_clk, srun_clk, if_neg (by omega), if_neg h0]; omega
    · simp only [QS, S]; omega

/-! ## The labels -/

theorem S_lt {k : ℕ} (h : Step k) : S k < 38 := by simp only [S, Step] at *; omega

theorem lab_deadline {m : ℕ} (h : m < 38) (hl : lab m = .advance_to_deadline) : m = 11 := by
  interval_cases m <;> simp_all [lab]

theorem lab_fbArm {m : ℕ} (h : m < 38) (hl : lab m = .advance_to_fb_arm) : m = 36 := by
  interval_cases m <;> simp_all [lab]

theorem lab_mvbaArm {m : ℕ} (h : m < 38) (hl : lab m = .advance_to_mvba_arm) : m = 37 := by
  interval_cases m <;> simp_all [lab]

theorem stut_ne_marker (m : ℕ) (L : Landmark) : stut m ≠ L.marker := by
  unfold stut; split_ifs <;> cases L <;> simp [Landmark.marker]

theorem lab_mvbaStep {m : ℕ} (h : m < 38) (hl : MvbaStepLabel (lab m)) : 33 ≤ m ∧ m ≤ 35 := by
  interval_cases m <;> simp_all [lab, MvbaStepLabel]

theorem stut_mvbaStep {m : ℕ} (hl : MvbaStepLabel (stut m)) : 34 ≤ m := by
  unfold stut at hl; split_ifs at hl with h
  · simp [MvbaStepLabel] at hl
  · omega

/-- The step `k` of slot `x`'s run is a marker only at its landmark. -/
theorem ulbl_marker {k : ℕ} {L : Landmark} (h : ulbl k = L.marker) :
    k = (match L with | .deadline => 14 | .fbArm => 69 | .mvbaArm => 124) := by
  unfold ulbl at h
  split_ifs at h with hs
  · have hlt := S_lt hs
    cases L
    · have := lab_deadline hlt h; simp only [S, Step] at *; omega
    · have := lab_fbArm hlt h; simp only [S, Step] at *; omega
    · have := lab_mvbaArm hlt h; simp only [S, Step] at *; omega
  · exact absurd h (stut_ne_marker _ _)

/-! ## The timing model -/

section Timing

variable (x : ℕ)

/-- Slot `x`'s schedule: deadline `x + 1`. -/
abbrev schX : Chorus.Schedule ℕ ℕ := sch.toFamilySchedule.at x

theorem time_d : Landmark.time (schX x) .deadline = x + 1 := rfl
theorem time_f : Landmark.time (schX x) .fbArm = x + 2 := rfl
theorem time_m : Landmark.time (schX x) .mvbaArm = x + 3 := rfl

/-- **(P-phase)**: each marker fires at its landmark's clock reading
(`x + 1`, `x + 2`, `x + 3`), and the phase reaches the landmark there. -/
theorem phasePunctual : PhasePunctual (schX x) (srun x) := by
  intro L
  refine ⟨fun k hk => ?_, ?_⟩
  · have := ulbl_marker hk
    cases L <;> simp only at this <;> subst this <;> simp [time_d, time_f, time_m, srun_clk]
  · cases L
    · exact ⟨15, by simp [S, cst, Landmark.Reached], by simp [time_d, srun_clk]⟩
    · exact ⟨70, by simp [S, cst, Landmark.Reached], by simp [time_f, srun_clk]⟩
    · exact ⟨125, by simp [S, cst, Landmark.Reached], by simp [time_m, srun_clk]⟩

end Timing

/-! ## The MVBA's projection: quiet, abandoned by the caller -/

/-- The MVBA's label at each step of a slot's run: the three abandonments,
then validator 0's `abandon()` re-issued. -/
def mlbl (k : ℕ) : Mvba.Label (Fin 4) (ByzNSet 4) V E ℕ :=
  if Step k ∧ 33 ≤ S k then .abandon (nd (S k - 33)) else .abandon 0

theorem mlbl_ne_expire (k : ℕ) (i : Fin 4) (v : ℕ) : mlbl k ≠ .expire_timer i v := by
  simp only [mlbl]; split_ifs <;> simp

set_option maxRecDepth 20000 in
theorem mrealizes (k : ℕ) (h : MvbaStepLabel (ulbl k)) :
    (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).tr thM (mst (S k)) (mlbl k)
      (mst (S (k + 1))) := by
  by_cases hs : Step k
  · rw [ulbl, if_pos hs] at h
    have hlt := S_lt hs
    obtain ⟨h1, h2⟩ := lab_mvbaStep (m := S k) hlt h
    rw [mlbl, if_pos ⟨hs, h1⟩, S_succ_of hs]
    have := abandon_tr (nd (S k - 33)) (S k) (by simp; omega) (by simp; omega)
    rwa [show max (S k) (34 + (nd (S k - 33)).val) = S k + 1 by simp; omega] at this
  · rw [ulbl, if_neg hs] at h
    have h34 := stut_mvbaStep (m := S k) h
    rw [mlbl, if_neg (fun h' => hs h'.1), S_succ_of_not hs]
    have := abandon_tr 0 (S k) (by decide) (by simp; omega)
    rwa [show max (S k) (34 + (0 : Fin 4).val) = S k by simp; omega] at this

/-- **The MVBA's projection** of slot `x`'s run. Its steps are the forwarded
abandonments, labelled by the MVBA's own `abandon`, and validator 0's,
re-issued for ever once the slot is done. -/
noncomputable def mproj (x : ℕ) : (mvbaComponent thS thM).Projection (srun x).toLRun where
  lbl := mlbl
  realizes n h := mrealizes n h
  scheduled N := ⟨max N 125, le_max_left _ _, by
    show MvbaStepLabel (ulbl (max N 125))
    have hs : ¬ Step (max N 125) := by simp only [Step]; omega
    rw [ulbl, if_neg hs]
    have : 34 ≤ S (max N 125) := by simp only [S]; omega
    simp only [stut, if_neg (show ¬ S (max N 125) < 34 by omega), MvbaStepLabel]⟩

theorem mproj_at (x k : ℕ) :
    (mproj x).run.at' k = mst (S ((mvbaComponent thS thM).idx (srun x).toLRun k)) := rfl

/-- **The MVBA's own two timed clauses** on the timed projection, with
their antecedents false: no fair MVBA label is enabled at a quiet state, no
timer fires and nobody enters a view. -/
theorem mvbaOwn (x : ℕ) : Mvba.BoundedJustice (schX x).mvba (mproj x).timed ∧
    Mvba.TimerPunctual (schX x).mvba (mproj x).timed := by
  refine ⟨Mvba.boundedJustice_of_quiet fun N D _ => ⟨N, le_rfl,
      le_trans ((mproj x).timed.clk_le_ref N) (Nat.le_add_right _ _),
      fun _ _ hh => by
        show ¬ Enabled _ _ ((mproj x).run.at' N) _
        rw [mproj_at]
        exact Mvba.not_enabled_of_quiet (mquiet _) hh⟩,
    ⟨fun n i v _ hl => absurd hl (mlbl_ne_expire _ i v), fun m i v _ hent => ?_⟩⟩
  change ((mproj x).run.at' m).entered i v = true at hent
  rw [mproj_at] at hent
  simp [mst] at hent

/-! ## The premises of slot `x`'s run -/

section Premises

variable (x : ℕ)

/-- **(Δδ-justice)**: every row and family with its antecedent false at
every clock reading's quiet index. -/
theorem timedJustice : TimedJustice (schX x) (srun x) := by
  refine ⟨fun l h hh hown => ?_, fun i v => ?_, fun i v => ?_, fun i => ?_, fun i v => ?_, fun i v => ?_⟩
  · refine bufferedFair_of_ends (Nat.zero_le _) fun N => ?_
    obtain ⟨P, hP, hc, hq⟩ := qend x N
    exact ⟨P, hP, hc, fun ⟨_, _, hen⟩ => quietS hq hh (fun ⟨_, _, _, h⟩ => hown (h ▸ trivial)) hen⟩
  · refine bufferedFairFamily_of_ends (Nat.zero_le _) fun N => ?_
    obtain ⟨P, hP, hc, hq⟩ := qend x N
    exact ⟨P, hP, hc, fun ⟨_, _, l, ⟨mn, hl⟩, hen⟩ =>
      quietS hq (hd := .net) (by rw [hl]; rfl) (fun ⟨_, _, _, h⟩ => by rw [hl] at h; cases h) hen⟩
  · refine bufferedFairFamily_of_ends (Nat.zero_le _) fun N => ?_
    obtain ⟨P, hP, hc, hq⟩ := qend x N
    exact ⟨P, hP, hc, fun ⟨_, _, l, ⟨mn, hl⟩, hen⟩ =>
      quietS hq (hd := .net) (by rw [hl]; rfl) (fun ⟨_, _, _, h⟩ => by rw [hl] at h; cases h) hen⟩
  · refine bufferedFairFamily_of_ends (Nat.zero_le _) fun N => ?_
    obtain ⟨P, hP, hc, hq⟩ := qend x N
    exact ⟨P, hP, hc, fun ⟨_, _, l, ⟨c, mn, hl⟩, hen⟩ =>
      quietS hq (hd := .net) (by rw [hl]; rfl) (fun ⟨_, _, _, h⟩ => by rw [hl] at h; cases h) hen⟩
  · refine bufferedFairFamily_of_ends (Nat.zero_le _) fun N => ?_
    obtain ⟨P, hP, hc, hq⟩ := qend x N
    exact ⟨P, hP, hc, fun ⟨⟨w, hw⟩, _⟩ => not_accepted _ i w v hw⟩
  · refine bufferedFair_of_ends (Nat.zero_le _) fun N => ?_
    obtain ⟨P, hP, hc, hq⟩ := qend x N
    exact ⟨P, hP, hc, fun ⟨_, ⟨_, hd, _⟩, _⟩ => not_decided _ _ _ hd⟩

/-- **The timing model at the system's MVBA.** -/
theorem syncAtMvba : SyncAtMvba (schX x) (srun x) :=
  ⟨timedJustice x, phasePunctual x, mproj x, mvbaOwn x⟩

/-- No fair label is enabled once the slot is done. -/
theorem justice_tail {k : ℕ} (hk : 125 ≤ k) (l : CL) (hj : JusticeLabel l) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS ((srun x).at' k) l := by
  show ¬ Enabled sys thS (cst (S k)) l
  rw [cst_stable (by simp only [S]; omega)]
  exact justice38 l hj ha

/-- **(F-justice)**, every clause with its antecedent false: from any index
on the slot is done, and nothing fair is enabled. -/
theorem fJustice : FJustice (srun x).toLRun :=
  ⟨fun l hj hfam N hen => absurd (hen (max N 125) (le_max_left _ _)).2
      (justice_tail x (le_max_right _ _) l hj fun ⟨_, _, _, h⟩ => hfam (h ▸ trivial)),
    fun _ _ N hen => by
      obtain ⟨-, l, ⟨_, rfl⟩, hl⟩ := hen (max N 125) (le_max_left _ _)
      exact absurd hl (justice_tail x (le_max_right _ _) _ ⟨fun h => h, fun h => h, fun h => h⟩
        fun ⟨_, _, _, h⟩ => by cases h),
    fun _ N hen => by
      obtain ⟨-, l, ⟨_, _, rfl⟩, hl⟩ := hen (max N 125) (le_max_left _ _)
      exact absurd hl (justice_tail x (le_max_right _ _) _ ⟨fun h => h, fun h => h, fun h => h⟩
        fun ⟨_, _, _, h⟩ => by cases h),
    fun i v N hen => by
      obtain ⟨⟨w, hw⟩, -⟩ := hen N le_rfl
      exact (not_accepted _ i w v hw).elim⟩

/-- **The MVBA's scheduling premise** on the untimed projection: (F-justice)
with its antecedent false, and (A-viewsync) at view 1 vacuously. -/
theorem mvbaAdmissible : MvbaAdmissible (srun x).toLRun := by
  refine ⟨mproj x, fun l hj _ N hen => ?_, ⟨1, 0, 0, rfl, rfl, ?_, fun i V _ _ ⟨n, hn⟩ => ?_,
    fun i n _ hexp => ?_⟩⟩
  · obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp ((Mvba.hop_isSome_iff l).mpr hj)
    have := hen N le_rfl
    rw [mproj_at] at this
    exact absurd this (Mvba.not_enabled_of_quiet (mquiet _) hh)
  · dsimp +instances only [Chorus.Witness.nsetC, byzNodeSetFin]
    decide
  · rw [mproj_at] at hn; simp [mst] at hn
  · rw [mproj_at] at hexp; simp [mst] at hexp

/-- **The bridge**, with `valid := (· = v⋆)`: a certified vector is `v⋆`,
and nobody decides or holds a meta-block in the MVBA. -/
theorem validBridge : ValidBridge (srun x).toLRun :=
  ⟨fun _ v hc => decide_eq_true (certified_eq _ v hc),
    fun _ i v _ hd => absurd hd (not_decided _ i v),
    fun _ i w v _ hacc => absurd hacc (not_accepted _ i w v)⟩

end Premises

/-! ## Every started slot's part is admissible -/

/-- Slot `x`'s instance, as a component of the composed system. -/
noncomputable abbrev SCx (x : ℕ) := slotC (A := AS) 4 1 rfl isByz Chorus.Witness.hbyz thO thS thM thG x

theorem slot_proj (x n : ℕ) : (SCx x).proj (run.at' n) = (x, cst (loc x n)) := rfl

/-- **Slot `x` is stepped exactly from its first step on**: from composed
index `56x + 44` it is related to itself across every step (`ustep`), and
before it sits in its initial state, which cannot stutter. -/
theorem slot_from (x n : ℕ) :
    SCI.trans ((SCx x).proj (run.at' n)) ((SCx x).proj (run.at' (n + 1))) ↔ x * 56 + 44 ≤ n := by
  rw [slot_proj, slot_proj]
  constructor
  · rintro ⟨-, l, htr⟩
    by_contra hlt
    rw [show loc x n = 0 by simp only [loc]; omega, show loc x (n + 1) = 0 by simp only [loc]; omega] at htr
    exact no_stutter_init l htr
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [loc_shift, show x * 56 + 44 + k + 1 = x * 56 + 44 + (k + 1) by omega, loc_shift]
    exact ⟨rfl, ulbl k, ustep k⟩

/-- Slot `x`'s part, at any of its projections, is `srun x`'s states. -/
theorem part_at' (x : ℕ) (p : (stutterComp (SCx x)).Projection (liftRun (SCx x) run).toLRun) (k : ℕ) :
    (partRun p).at' k = (x, cst (S k)) := by
  rw [partRun_at']
  cases k with
  | zero => rw [show p.entry 0 = 0 from rfl, slot_proj, loc_zero, show S 0 = 0 from rfl]
  | succ k =>
    rw [entry_of_from (slot_from x) p k, slot_proj, show x * 56 + 44 + k + 1 = x * 56 + 44 + (k + 1) by omega,
      loc_shift]

/-- Slot `x`'s part, at any of its projections, has `srun x`'s clock. -/
theorem part_clk (x : ℕ) (p : (stutterComp (SCx x)).Projection (liftRun (SCx x) run).toLRun) (k : ℕ) :
    (partRun p).clk k = (srun x).clk k := by
  rw [partRun_clk]
  cases k with
  | zero => rw [show p.entry 0 = 0 from rfl, srun_clk, if_pos rfl]; rfl
  | succ k =>
    rw [entry_of_from (slot_from x) p k, srun_clk, if_neg (Nat.succ_ne_zero k)]
    show (x * 56 + 44 + k + 1) / 56 = _
    omega

/-- **Each started slot's Chorus meets its timing model.** Every slot's,
in fact: at its projection, its part's labelling is `srun x`. -/
theorem slotAdmissible : SlotAdmissible (A := AS) 4 1 rfl isByz Chorus.Witness.hbyz sch run := by
  intro x _
  refine ⟨projOfFrom (slot_from x), srun x, fun k => by rw [part_at']; rfl, fun k => (part_clk x _ k).symm,
    rfl, fJustice x, mvbaAdmissible x, validBridge x, ?_⟩
  rw [part_at']
  exact syncAtMvba x

/-- **(P-incl) on every started slot**: a correct validator holding the
proposer's chunk records it (by the end of the slot's first clock). -/
theorem slotInclusive : SlotInclusive (A := AS) 4 1 rfl isByz Chorus.Witness.hbyz sch run := by
  intro x _ p r' hat _ n i j m hi _ hc _ _
  have hi := (correct_iff i).1 hi
  rw [hat, part_at'] at hc
  change decide _ = true at hc
  simp only [decide_eq_true_eq] at hc
  refine ⟨200, (), ?_⟩
  rw [hat, part_at']
  show decide _ = true
  simp only [S, decide_eq_true_eq]
  omega

end Composed.Witness
