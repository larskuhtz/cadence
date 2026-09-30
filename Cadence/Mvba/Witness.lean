import Cadence.Mvba.Temporal
import Mathlib.Tactic.IntervalCases

/-! # Mvba.Witness — the premises of the MVBA liveness theorems are jointly satisfiable

[Bounds.md](../../docs/Bounds.md) §6.3. A conditional theorem whose premises
can never hold together proves nothing. This file exhibits **one model** —
an instance, a leader schedule, a timing schedule and a labelled timed run —
that satisfies every premise of both MVBA liveness theorems at once:

* `Mvba.timedTermination_premises_satisfiable`: every premise of
  `Mvba.timed_termination`, the contract's bounded Termination
  (`Mvba.mvbaTemporal`);
* `Mvba.termination_premises_satisfiable`: every premise of
  `Mvba.termination`, the untimed claim, on the same run with its clock
  forgotten.

Because the premises are hypotheses, one model suffices. Bounds.md §6.3 is
the auditor's ledger, premise by premise; this header describes the model.

## The instance

* Four validators, `Fin 4`, under the concrete quorum family
  `byzNodeSetFinGen 4 1` ([ByzQuorum.lean](../ByzQuorum.lean)): `f = 1`,
  validator 3 Byzantine, and a quorum is a sorted list of validators with at
  least three members. Validator 3 never acts: the adversary is under no
  obligation.
* Values are `Unit`, and every value is valid. Validator 0 leads every
  view, so both model `assumption`s and `LeaderRotation` with `k = 1` hold.
* Views are `ℕ` (`natViewOrder`, `natViewOrderEnum`); time is `ℕ`; the
  schedule is `Schedule.fixedNat ℕ 1`, the paper's fixed timeout: `Δ = 1`,
  `δ = Δ_sync = 0`, `ρ = 1`, a timeout of 5, and `ℓ = 24`. GST and `t` are 0.

## The run

The three correct validators become available and propose, run the whole
chain of view 0 and decide in it, all at clock 0. At clock 5 their view-0
timers expire, as the timing model requires; a decided validator has halted
(the supplement's `decide(…); abandon()`, [Mvba.lean](../Mvba.lean)), so none
of them times out. Then the run idles on a step that changes nothing, one
clock unit per step. Nobody abandons.

At the idle state no fair label can take a step that changes the state:
the correct validators have halted, the Byzantine one is not honest, and
every certificate an assembly could form already exists. So weak fairness,
which asks only for steps that change the state, asks nothing of the idle
tail, in the untimed claim as in the timed one.

## How the proofs are arranged

Every state is a **closed formula in its index** (`st`): a record is present
at index `n` exactly when the step that sets it comes before `n`, and that
step is `c + i` for a constant `c` per record and validator `i`. So a
transition is linear arithmetic over the index, and `omega` closes it.

The clock advances only out of states at which no fair label is
move-enabled (`quiet`). From every index there is then a later index on the
same clock reading at which a given fair label is not move-enabled, so
bounded weak fairness holds with its antecedent false: the run never leaves
an obligation pending while time passes. The untimed weak fairness holds
for the same reason, at the idle state (`fJustice`). -/

namespace Mvba

open Cadence
open scoped Cadence.Timed

namespace Witness

/-! ## The instance -/

instance : Inhabited (ByzNSet 4) := ⟨⟨[], List.Pairwise.nil⟩⟩

/-- Four validators, one Byzantine (validator 3): the concrete family at
`n = 4`, `f = 1`. -/
@[implicit_reducible]
def nsetW : ByzNodeSet (Fin 4) (ByzNSet 4) :=
  byzNodeSetFinGen 4 1 (by decide) (fun i => i.val = 3) (by decide)

attribute [local instance] nsetW natViewOrder

-- One simp-lemma list serves every step of the run, so a given step leaves
-- some of its entries unused.
set_option linter.unusedSimpArgs false

/-- The correct validators, a supermajority. -/
def Q : ByzNSet 4 := ⟨[0, 1, 2], by decide⟩

/-- `ByzNodeSetHonestQuorum` at this instance: the three correct validators. -/
@[implicit_reducible]
def hqeW : ByzNodeSetHonestQuorum (Fin 4) (ByzNSet 4) nsetW where
  honestQuorum := Q
  honestQuorum_supermajority := by
    dsimp +instances [nsetW, byzNodeSetFinGen, Q]
    decide
  honestQuorum_correct := by
    dsimp +instances [nsetW, byzNodeSetFinGen, Q]
    decide

/-- Every value is valid; validator 0 leads every view. -/
def thW : Theory (Fin 4) (ByzNSet 4) Unit ℕ where
  valid _ := true
  leader _ l := Decidable.decide (l = 0)

abbrev S := Mvba.State (Mvba.FieldAbstractType (Fin 4) (ByzNSet 4) Unit ℕ)
noncomputable abbrev sys := Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) Unit ℕ
abbrev L := Mvba.Label (Fin 4) (ByzNSet 4) Unit ℕ

/-! ## The states

`st n` is the state at index `n`. A record is present iff the step that
sets it is before `n`. With `x` a correct validator (`x < 3`), everything
happens in view 0, and the step that sets each record is:

* `avail_ready x`: `x`, and `input x` with `entered x 0`: `3 + x`;
* the leader's proposal and `Pre-Prepare`: `6`;
* `accepted`/`voted`/`msg_prepare`: `7 + x`; the prepare certificate: `10`,
  by the anonymous assembly; `local_prepqc`: `11 + x`, each validator
  forming its own from the three prepares;
* `commit_sent`/`msg_commit`: `14 + x`; the commit certificate: `17`;
  `decided x`: `18 + x`;
* `timer_expired x 0`: `22 + x`.

Nothing else is ever set: no timeout, no certificate of a later view, no
abandonment, and validator 3 sends nothing. From index 25 on the state no
longer changes. -/

def st (n : Nat) : S where
  msg_preprepare l V _ := Decidable.decide (V = 0 ∧ l.val = 0 ∧ 6 < n)
  msg_prepare r V _ := Decidable.decide (V = 0 ∧ r.val < 3 ∧ 7 + r.val < n)
  msg_commit r V _ := Decidable.decide (V = 0 ∧ r.val < 3 ∧ 14 + r.val < n)
  msg_timeout_qc _ _ _ _ := false
  msg_timeout_noqc _ _ := false
  msg_prepqc V _ := Decidable.decide (V = 0 ∧ 10 < n)
  msg_commitqc V _ := Decidable.decide (V = 0 ∧ 17 < n)
  msg_tc _ := false
  tc_lock _ _ _ := false
  tc_nolock _ := false
  input i _ := Decidable.decide (i.val < 3 ∧ 3 + i.val < n)
  entered i V := Decidable.decide (V = 0 ∧ i.val < 3 ∧ 3 + i.val < n)
  voted i V := Decidable.decide (V = 0 ∧ i.val < 3 ∧ 7 + i.val < n)
  accepted i V _ := Decidable.decide (V = 0 ∧ i.val < 3 ∧ 7 + i.val < n)
  local_prepqc i W _ := Decidable.decide (W = 0 ∧ i.val < 3 ∧ 11 + i.val < n)
  timed_out _ _ := false
  commit_sent i V := Decidable.decide (V = 0 ∧ i.val < 3 ∧ 14 + i.val < n)
  proposed_in l V := Decidable.decide (V = 0 ∧ l.val = 0 ∧ 6 < n)
  decided i _ := Decidable.decide (i.val < 3 ∧ 18 + i.val < n)
  abandoned _ := false
  avail_ready i _ := Decidable.decide (i.val < 3 ∧ i.val < n)
  timer_expired i V := Decidable.decide (V = 0 ∧ i.val < 3 ∧ 22 + i.val < n)

/-! ## The labels

The 25 steps of the active prefix, then the idle tail. Step 21 changes
nothing and is where the clock moves from 0 to 5. -/

/-- The label that changes nothing, used where the clock moves:
availability already marked. -/
def idle : L := .become_avail_ready 0 ()

/-- The label of each step of the active prefix. -/
def prefixLabel : Nat → L
  | 0 => .become_avail_ready 0 ()
  | 1 => .become_avail_ready 1 ()
  | 2 => .become_avail_ready 2 ()
  | 3 => .propose 0 ()
  | 4 => .propose 1 ()
  | 5 => .propose 2 ()
  | 6 => .leader_propose_first 0 ()
  | 7 => .handle_preprepare_first 0 0 ()
  | 8 => .handle_preprepare_first 1 0 ()
  | 9 => .handle_preprepare_first 2 0 ()
  | 10 => .form_prepqc 0 () Q
  | 11 => .adopt_prepqc 0 0 () Q
  | 12 => .adopt_prepqc 1 0 () Q
  | 13 => .adopt_prepqc 2 0 () Q
  | 14 => .send_commit 0 0 ()
  | 15 => .send_commit 1 0 ()
  | 16 => .send_commit 2 0 ()
  | 17 => .form_commitqc 0 () Q
  | 18 => .decide 0 0 ()
  | 19 => .decide 1 0 ()
  | 20 => .decide 2 0 ()
  | 21 => idle
  | 22 => .expire_timer 0 0
  | 23 => .expire_timer 1 0
  | _ => .expire_timer 2 0

/-- The label of the step out of index `n`: the active prefix, then the
idle step for ever. -/
def lbl (n : Nat) : L := if n < 25 then prefixLabel n else idle

/-- The clock: 0 through the decisions, 5 from the view-0 timers on, and one
unit per step once the run is idle. -/
def clk (n : Nat) : ℕ := if n ≤ 21 then 0 else if n ≤ 25 then 5 else n - 20

/-! ## Proof tactics

A transition of `sys` unfolds to its guards and an equation between the
updated state and the post-state. At `st` both sides are structure literals
of `decide`d linear facts, so the equation splits field by field and every
remaining goal is linear arithmetic over the index. -/

/-- The five supermajorities of four validators. -/
theorem supermajority_cases (q : ByzNSet 4) (h : 4 ≤ q.val.length + 1) :
    q.val = [0, 1, 2] ∨ q.val = [0, 1, 3] ∨ q.val = [0, 2, 3] ∨ q.val = [1, 2, 3] ∨
      q.val = [0, 1, 2, 3] := by
  have hall : ∀ q ∈ allByzNSets 4, 4 ≤ q.val.length + 1 →
      (q.val = [0, 1, 2] ∨ q.val = [0, 1, 3] ∨ q.val = [0, 2, 3] ∨ q.val = [1, 2, 3] ∨
        q.val = [0, 1, 2, 3]) := by decide
  exact hall q (allByzNSets_complete q) h

/-- Normalise `decide`d facts over this instance to linear arithmetic. -/
local macro "wnorm" : tactic =>
  `(tactic| (
    try dsimp +instances only [nsetW, byzNodeSetFinGen, natViewOrder]
    try simp only [← Bool.decide_and, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      Bool.not_eq_true, decide_eq_false_iff_not, Fin.ext_iff, List.mem_cons, List.mem_nil_iff,
      List.length_cons, List.length_nil, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.val_zero,
      exists_eq_left, exists_const, and_true, true_and, or_false]))

/-- The same, in a hypothesis. -/
local macro "wnorm_at" h:ident : tactic =>
  `(tactic| (
    try dsimp +instances only [nsetW, byzNodeSetFinGen, natViewOrder] at $h:ident
    try simp only [← Bool.decide_and, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      Bool.not_eq_true, decide_eq_false_iff_not, Fin.ext_iff, List.mem_cons, List.mem_nil_iff,
      List.length_cons, List.length_nil, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.val_zero,
      forall_eq] at $h:ident))

/-- Split a goal into its conjuncts and close each by arithmetic. -/
local macro "wclose" : tactic =>
  `(tactic| (and_intros <;> intros <;> first | trivial | omega))

/-- Expose a transition's guards and update, evaluated at `st`. -/
local macro "wexpose" : tactic =>
  `(tactic| (
    simp only [sys, Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
    try simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id, Mvba.lock_available,
      Veil.FieldRepresentation.get, st, thW, Q, Mvba.State.mk.injEq, funext_iff]))

/-- One step of the run: the guards hold at `st n` and the update is `st m`. -/
local macro "wstep" : tactic => `(tactic| (wexpose <;> wnorm <;> wclose))

/-- The same unfolding as `wexpose`, in a hypothesis. -/
local macro "wunfold" h:ident : tactic =>
  `(tactic| (
    simp only [sys, Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp] at $h:ident
    try simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id, Mvba.lock_available, Mvba.in_view,
      Veil.FieldRepresentation.get, st, thW, Q] at $h:ident
    try wnorm_at $h:ident))

/-- Evaluate `lbl` at a literal index to the label it names. -/
local macro "wlabel" : tactic =>
  `(tactic| simp only [lbl, prefixLabel, idle, Nat.reduceLT, Nat.reduceSub,
    Nat.reduceDiv, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceEqDiff,
    OfNat.ofNat_ne_zero, one_ne_zero, reduceCtorEq])

/-! ## The run is a run of the model

The theory meets the model's two assumptions, index 0 is initial, and every
step is a transition: the 25 steps of the active prefix, then the idle
tail, whose state no longer changes. -/

theorem holds : sys.assumptions thW := by
  simp only [sys, Mvba.relationalTransitionSystem, Mvba.Assumptions, Mvba.leader_functional,
    Mvba.leader_honest_cofinal, thW, instIsSubReaderOfRefl.readFrom_id]
  refine ⟨fun _ L L' h h' => ?_, fun V => ⟨V, 0, TotalOrderWithMinimum.le_refl V, rfl, ?_⟩⟩
  · simp only [decide_eq_true_eq] at h h'
    rw [h, h']
  · dsimp +instances only [nsetW, byzNodeSetFinGen]
    decide

theorem starts : sys.init thW (st 0) := by
  simp only [sys, Mvba.relationalTransitionSystem, Mvba.Init, trSimp]
  simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      Veil.FieldRepresentation.get, st, Mvba.State.mk.injEq, funext_iff]

theorem steps_0 (n : Nat) (h₂ : n < 13) : sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_1 (n : Nat) (h₁ : 13 ≤ n) (h₂ : n < 25) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_prefix (n : Nat) (hn : n < 25) : sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  by_cases h0 : n < 13
  · exact steps_0 n h0
  · exact steps_1 n (by omega) hn

/-- From index 25 on the state no longer changes. -/
theorem st_stable {n : Nat} (h : 25 ≤ n) : st n = st 25 := by
  simp only [st, Mvba.State.mk.injEq, funext_iff]
  wnorm
  wclose

/-- The idle step is a transition from the idle state to itself. -/
theorem tail_step : sys.tr thW (st 25) idle (st 25) := by
  wlabel; wstep

theorem steps (n : Nat) : sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  by_cases h : n < 25
  · exact steps_prefix n h
  · rw [st_stable (by omega), st_stable (n := n + 1) (by omega)]
    have : lbl n = idle := by
      simp only [lbl, if_neg h]
    rw [this]
    exact tail_step

/-! ## No fair label moves at a plateau's end

The clock advances only out of the last index of each clock reading: index
21, every correct validator decided and its timer not yet expired, and the
idle tail. At those states every fair label is either disabled — a correct
validator has decided and halted, the Byzantine one is not honest — or a
step that changes nothing. -/

/-- The indices out of which the clock advances. -/
def PlateauEnd (n : Nat) : Prop := n = 21 ∨ 25 ≤ n

theorem quiet {n : Nat} (hn : PlateauEnd n) {l : L} {hd : Hop} (hh : hop l = some hd) :
    ¬ EnabledMove sys thW (st n) l := by
  rintro ⟨s', htr, hne⟩
  cases l
  all_goals first | (simp [hop] at hh; done) | skip
  all_goals wunfold htr
  case form_tc_nolock v q =>
    obtain ⟨hq, hall, -⟩ := htr
    rcases supermajority_cases q hq with h | h | h | h | h <;> simp [h] at hall <;>
      exact (hall _).1 rfl
  case form_prepqc v e q | form_commitqc v e q =>
    obtain ⟨hq, hall, rfl⟩ := htr
    rcases supermajority_cases q hq with h | h | h | h | h <;>
      simp only [h, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, or_false,
        forall_eq, Fin.isValue] at hall <;>
      wnorm_at hall <;>
      rcases hn with rfl | hn <;>
      first
        | omega
        | (apply hne; simp only [st, Mvba.State.mk.injEq, funext_iff]; wnorm; wclose)
  all_goals (repeat (obtain ⟨_, htr⟩ := htr))
  all_goals (rcases hn with rfl | hn)
  all_goals omega

/-! ## The run and its schedule -/

/-- The paper's fixed timeout at `ℕ`, with a correct leader in every view. -/
def schW : Schedule ℕ ℕ := Schedule.fixedNat ℕ 1

/-- **The labelled timed run.** GST is 0. -/
noncomputable def run : TMvbaRun thW ℕ where
  at' := st
  lbl := lbl
  holds := holds
  starts := starts
  steps := steps
  clk := clk
  clk_mono n := by simp only [clk]; split_ifs <;> omega
  clk_unbounded t := ⟨t + 25, by simp only [clk]; split_ifs <;> omega⟩
  gst := 0

/-- A correct validator is one of the first three. -/
theorem correct_lt {p : Fin 4} (h : ¬ nsetW.is_byz p = true) : p.val < 3 := by
  dsimp +instances only [nsetW, byzNodeSetFinGen] at h
  simp only [decide_eq_true_eq] at h
  omega

/-- Every index is followed, on the same clock reading, by a plateau end. -/
theorem plateau_after (N : Nat) : ∃ P, PlateauEnd P ∧ N ≤ P ∧ clk P = clk N := by
  by_cases h : N ≤ 21
  · refine ⟨21, Or.inl rfl, h, ?_⟩
    simp only [clk]; split_ifs <;> omega
  · refine ⟨max N 25, Or.inr (by omega), by omega, ?_⟩
    simp only [clk]; split_ifs <;> omega

/-- Only the scheduled steps expire a timer: view 0's, for validator `i`, at
index `22 + i`. -/
theorem lbl_expire {n : Nat} {i : Fin 4} {v : ℕ} (h : lbl n = .expire_timer i v) :
    i.val < 3 ∧ v = 0 ∧ n = 22 + i.val := by
  by_cases hn : n < 25
  · revert h
    interval_cases n <;> wlabel <;>
      simp only [Label.expire_timer.injEq, reduceCtorEq, false_implies, and_imp] <;>
      (rintro rfl rfl; decide)
  · simp only [lbl, if_neg hn, idle, reduceCtorEq] at h

/-! ## (a) The timed premises -/

/-- **(Δ-justice)**, every clause with its antecedent false: every window
reaches a plateau end, where no fair label is move-enabled
(`boundedJustice_of_quiet`). -/
theorem boundedJustice : BoundedJustice schW run :=
  boundedJustice_of_quiet fun N D _ =>
    let ⟨P, hP, hNP, hclk⟩ := plateau_after N
    ⟨P, hNP, show clk P ≤ max (clk N) 0 + D by
        rw [hclk]; exact le_trans (le_max_left _ _) (Nat.le_add_right _ _),
      fun _ _ hh => quiet hP hh⟩

/-- **(T-timer)**: view `v`'s timer expires exactly five units after the
validator entered `v`. -/
theorem timerPunctual : TimerPunctual schW run := by
  refine ⟨fun n i v _ hl => ?_, fun m i v _ hent => ?_⟩
  · obtain ⟨hi, rfl, rfl⟩ := lbl_expire hl
    refine ⟨4 + i.val, by omega, ?_, ?_⟩
    · show (st _).entered i 0 = true
      simp [st]
      omega
    · show clk _ + 5 ≤ clk _
      simp only [clk]; split_ifs <;> omega
  · change (st m).entered i v = true at hent
    have he : v = 0 ∧ i.val < 3 ∧ 3 + i.val < m := by simpa [st] using hent
    refine ⟨max m (23 + i.val), le_max_left _ _, ?_, ?_⟩
    · show (st _).timer_expired i v = true
      simp [st]
      omega
    · show clk _ ≤ clk m + 5
      simp only [clk]; split_ifs <;> omega

/-- **(Δ-avail)**: availability is marked before anyone accepts. -/
theorem availWithin : AvailWithin schW run := by
  intro m i v e _ hacc
  change (st m).accepted i v e = true at hacc
  have ha : v = 0 ∧ i.val < 3 ∧ 7 + i.val < m := by simpa [st] using hacc
  refine ⟨m, le_rfl, ?_, ?_⟩
  · show (st m).avail_ready i e = true
    simp [st]
    omega
  · exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)

theorem sync : Sync schW run := ⟨boundedJustice, timerPunctual, availWithin⟩

/-- **(A-leader-rotation-k)** at `k = 1`: validator 0 leads every view. -/
theorem rotation : LeaderRotation natViewOrderEnum schW.k thW := by
  intro v
  refine ⟨0, Nat.one_pos, 0, rfl, ?_⟩
  dsimp +instances only [nsetW, byzNodeSetFinGen]
  decide

/-- The run, as the contract's `TimedRun`. -/
noncomputable def trW : TimedMvbaRun thW ℕ :=
  run.toTimedRun (mvbaSafety thW).init (mvbaSafety thW).trans ⟨holds, starts⟩
    (fun n => ⟨_, run.steps n⟩)

theorem admissible : Admissible schW thW trW :=
  ⟨run, fun _ => rfl, fun _ => rfl, rfl, sync⟩

/-- `ℓ` at this schedule: `(1 + 1) + 2 • 1 + (1 + 1) • 7 + 4 + (1 + 1)`. -/
theorem ell : schW.ℓ natViewOrderEnum = 24 := rfl

/-- Every correct validator has proposed by index 6, at clock 0. -/
theorem proposes_by (p : Fin 4) (hp : ¬ nsetW.is_byz p = true) :
    trW.byTime 0 (fun st => ∃ v, (mvbaSafety thW).proposed st p v) := by
  refine ⟨6, ?_, (), ?_⟩
  · show clk 6 ≤ 0
    decide
  · show (st 6).input p () = true
    have := correct_lt hp
    simp [st]
    omega

/-- Every value is valid. -/
theorem valid_inputs (p : Fin 4) (_ : ¬ nsetW.is_byz p = true) (n : Nat) (v : Unit)
    (_ : (mvbaSafety thW).proposed (trW.at' n) p v) : (mvbaSafety thW).Valid v := rfl

/-- Nobody abandons, so the caller's third condition holds vacuously. -/
theorem abandons_late (p : Fin 4) (_ : ¬ nsetW.is_byz p = true) (n : Nat)
    (hab : (mvbaSafety thW).abandoned (trW.at' n) p) :
    ∃ u, TotalOrder.le 0 u ∧ TotalOrder.le trW.gst u ∧
      (∀ u', TotalOrder.le 0 u' → TotalOrder.le trW.gst u' → TotalOrder.le u u') ∧
      ¬ TotalOrder.le (trW.clk n) (u + schW.ℓ natViewOrderEnum) := by
  change (st n).abandoned p = true at hab
  simp [st] at hab

/-! ## (b) The untimed premises, on the same run -/

/-- **(F-justice)**, with its antecedent false: from any `N` on, the idle
state is reached, and there no fair label can take a step that changes the
state (`quiet`). -/
theorem fJustice : FJustice run.toLRun := by
  intro l hj N hen
  obtain ⟨hd, hh⟩ := Option.isSome_iff_exists.mp ((hop_isSome_iff l).mpr hj)
  exact absurd (hen (max N 25) (le_max_left _ _))
    (quiet (Or.inr (le_max_right _ _)) hh)

/-- **(A-viewsync)** with `W = 1`: the view-0 timers do expire, and no view-1
timer ever does, since nobody enters view 1. -/
theorem aViewSync : AViewSync run.toLRun := by
  refine ⟨1, 0, 0, rfl, rfl, ?_, fun i V hi hV _ => ?_, fun i n hi hexp => ?_⟩
  · dsimp +instances only [nsetW, byzNodeSetFinGen]
    decide
  · have hV0 : V = 0 := by
      have : V < 1 := hV
      omega
    subst hV0
    refine ⟨25, ?_⟩
    show (st 25).timer_expired i 0 = true
    have := correct_lt hi
    simp [st]
    omega
  · change (st n).timer_expired i 1 = true at hexp
    simp [st] at hexp

theorem fAvail : FAvail run.toLRun := by
  intro i n V E _ hacc
  change (st n).accepted i V E = true at hacc
  have ha : V = 0 ∧ i.val < 3 ∧ 7 + i.val < n := by simpa [st] using hacc
  refine ⟨n, ?_⟩
  show (st n).avail_ready i E = true
  simp [st]
  omega

theorem allPropose : AllPropose run.toLRun := by
  intro i hi
  refine ⟨6, (), ?_⟩
  show (st 6).input i () = true
  have := correct_lt hi
  simp [st]
  omega

theorem noEarlyAbandon : NoEarlyAbandon run.toLRun := by
  intro i n _ hab
  change (st n).abandoned i = true at hab
  simp [st] at hab

/-! ## The theorems apply

Both liveness theorems, at this instance and on this run. Not needed for
non-vacuity; they check that the model is an instance of what the theorems
quantify over, with nothing re-bundled. -/

example : Terminates run.toLRun :=
  termination hqeW natViewOrderEnum run.toLRun fJustice aViewSync fAvail allPropose noEarlyAbandon

example (q : Fin 4) (hq : ¬ nsetW.is_byz q = true) :
    trW.byGstBound 0 (schW.ℓ natViewOrderEnum) (fun st => ∃ v, (mvbaSafety thW).decided st q v) :=
  timed_termination hqeW schW natViewOrderEnum rotation trW admissible 0
    proposes_by valid_inputs abandons_late q hq

end Witness

/-! ## The two results -/

open Witness in
/-- **The premises of `Mvba.timed_termination` are jointly satisfiable.**
Some instance, schedule and timed run meet every one of them at once: the
instance hypotheses of `Mvba.mvbaTemporal` (finitely many validators, the
quorum system, a supermajority of correct validators, the view order, a
correct leader in every `k` views, a cancellative Archimedean time), the
schedule's own hypotheses, admissibility (`Sync`, through a labelling), and
the caller's three conditions — everyone proposes by `t`, with a valid
value, and nobody abandons before `max(t, GST) + ℓ`.

It rules out that the bounded Termination claim holds only because no run
can meet its premises: there is an admissible run in which the caller
behaves, so the theorem's conclusion is a real constraint on that run. -/
theorem timedTermination_premises_satisfiable :
    ∃ (node nodeset value view : Type) (_ : Inhabited node) (_ : Inhabited nodeset)
      (_ : Inhabited value) (_ : Inhabited view)
      (nset : ByzNodeSet node nodeset) (vord : TotalOrderWithMinimum view) (_ : Fintype node)
      (time : Type) (_ : LinearOrder time) (_ : AddCommMonoid time)
      (_ : IsOrderedCancelAddMonoid time) (_ : Archimedean time)
      (_ : ByzNodeSetHonestQuorum node nodeset nset)
      (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
      (th : Theory node nodeset value view),
      LeaderRotation vfin sch.k th ∧
      ∃ (tr : TimedMvbaRun th time) (t : time),
        Admissible sch th tr ∧
        (∀ p, ¬ nset.is_byz p = true →
          tr.byTime t (fun st => ∃ v, (mvbaSafety th).proposed st p v)) ∧
        (∀ p, ¬ nset.is_byz p = true → ∀ n v,
          (mvbaSafety th).proposed (tr.at' n) p v → (mvbaSafety th).Valid v) ∧
        (∀ p, ¬ nset.is_byz p = true → ∀ n,
          (mvbaSafety th).abandoned (tr.at' n) p →
            ∃ u, TotalOrder.le t u ∧ TotalOrder.le tr.gst u ∧
              (∀ u', TotalOrder.le t u' → TotalOrder.le tr.gst u' → TotalOrder.le u u') ∧
              ¬ TotalOrder.le (tr.clk n) (u + sch.ℓ vfin)) :=
  ⟨Fin 4, ByzNSet 4, Unit, ℕ, inferInstance, inferInstance, inferInstance, inferInstance,
    nsetW, natViewOrder, inferInstance, ℕ, inferInstance, inferInstance, inferInstance,
    inferInstance, hqeW, schW, natViewOrderEnum, thW, rotation, trW, 0, admissible,
    proposes_by, valid_inputs, abandons_late⟩

open Witness in
/-- **The premises of `Mvba.termination` are jointly satisfiable.** Some
instance and run meet all of them at once: the theorem's hypotheses
(finitely many validators, a supermajority of correct validators, the view
order), the model's `assumption`s, and the claim's five premises —
(F-justice), (A-viewsync), (F-avail), `AllPropose` and `NoEarlyAbandon`.

It rules out that the untimed Termination claim is vacuous, and in
particular that its weak-fairness premise contradicts the rest. Weak
fairness asks only for steps that change the state, so once the run is
idle it asks nothing; nothing in that argument depends on the quorum sort
being finite (Bounds.md §6.2.4). -/
theorem termination_premises_satisfiable :
    ∃ (node nodeset value view : Type) (_ : Inhabited node) (_ : Inhabited nodeset)
      (_ : Inhabited value) (_ : Inhabited view)
      (nset : ByzNodeSet node nodeset) (vord : TotalOrderWithMinimum view) (_ : Fintype node)
      (_ : ByzNodeSetHonestQuorum node nodeset nset) (_ : ViewOrderEnum view vord)
      (th : Theory node nodeset value view),
      (Mvba.relationalTransitionSystem node nodeset value view).assumptions th ∧
      ∃ r : MvbaRun th,
        FJustice r ∧ AViewSync r ∧ FAvail r ∧ AllPropose r ∧ NoEarlyAbandon r :=
  ⟨Fin 4, ByzNSet 4, Unit, ℕ, inferInstance, inferInstance, inferInstance, inferInstance,
    nsetW, natViewOrder, inferInstance, hqeW, natViewOrderEnum, thW, holds, run.toLRun,
    fJustice, aViewSync, fAvail, allPropose, noEarlyAbandon⟩

end Mvba

/-! ## The pinned trust base -/

/--
info: 'Mvba.timedTermination_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.timedTermination_premises_satisfiable

/--
info: 'Mvba.termination_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.termination_premises_satisfiable
