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
  `δ = Δ_sync = 0`, a timeout of 5, and `ℓ = 19`. GST and `t` are 0.

## The run

The three correct validators become available and propose, run the whole
chain of view 0 and decide in it, all at clock 0. In the model a decision
does not stop the view timer (the supplement's does: Bounds.md §6.3.2), so
at clock 5 the view-0 timers expire,
the validators time out, form a timeout certificate, enter view 1 and run
its chain; likewise at clocks 10, 15 and 20 for views 2, 3 and 4. At
clock 25 the view-4 timers expire and the caller abandons each correct
validator — after `ℓ = 19`, as the timed claim requires. Then the run idles:
it cycles through the twenty-two quorum labels still enabled, each a step that
changes nothing, one clock unit per step.

## How the proofs are arranged

Every state is a **closed formula in its index** (`st`): a record is present
at index `n` exactly when the step that sets it comes before `n`, and that
step is `26 · V + c + i` for view `V`, a constant `c` per record and
validator `i`. So a transition is linear arithmetic over the index, and
`omega` closes it.

The clock advances only out of states at which no fair label is
move-enabled (`quiet`). From every index there is then a later index on the
same clock reading at which a given fair label is not move-enabled, so
bounded weak fairness holds with its antecedent false: the run never leaves
an obligation pending while time passes. -/

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
sets it is before `n`. With `x` a correct validator (`x < 3`) and `V ≤ 4` a
view, the step that sets each record is:

* `avail_ready x`: `x`, and `input x`: `3 + x`;
* `entered x V`: `26 V + 3 + x` (by `propose` for view 0, `sync_view`
  otherwise);
* the leader's proposal and `Pre-Prepare` in `V`: `26 V + 6`;
* `accepted`/`voted`/`msg_prepare`: `26 V + 7 + x`; the prepare
  certificate: `26 V + 10`; `local_prepqc`: `26 V + 11 + x`;
* `commit_sent`/`msg_commit`: `26 V + 14 + x`; the commit certificate:
  `26 V + 17`; `decided x`: `18 + x` (view 0 only);
* `timer_expired x V`: `26 V + 22 + x`;
* for `V ≤ 3`, `timed_out`/`msg_timeout_qc` (carrying the view-`V`
  certificate): `26 V + 25 + x`; the timeout certificate with its lock:
  `26 V + 28`;
* `abandoned x`: `129 + x`.

Nothing else is ever set; in particular validator 3 sends nothing. From
index 132 on the state no longer changes. -/

def st (n : Nat) : S where
  msg_preprepare l V _ := Decidable.decide (V ≤ 4 ∧ l.val = 0 ∧ 26 * V + 6 < n)
  msg_prepare r V _ := Decidable.decide (V ≤ 4 ∧ r.val < 3 ∧ 26 * V + 7 + r.val < n)
  msg_commit r V _ := Decidable.decide (V ≤ 4 ∧ r.val < 3 ∧ 26 * V + 14 + r.val < n)
  msg_timeout_qc r V W _ :=
    Decidable.decide (V ≤ 3 ∧ r.val < 3 ∧ W = V ∧ 26 * V + 25 + r.val < n)
  msg_timeout_noqc _ _ := false
  msg_prepqc V _ := Decidable.decide (V ≤ 4 ∧ 26 * V + 10 < n)
  msg_commitqc V _ := Decidable.decide (V ≤ 4 ∧ 26 * V + 17 < n)
  msg_tc V := Decidable.decide (V ≤ 3 ∧ 26 * V + 28 < n)
  tc_lock V W _ := Decidable.decide (V ≤ 3 ∧ W = V ∧ 26 * V + 28 < n)
  tc_nolock _ := false
  input i _ := Decidable.decide (i.val < 3 ∧ 3 + i.val < n)
  entered i V := Decidable.decide (V ≤ 4 ∧ i.val < 3 ∧ 26 * V + 3 + i.val < n)
  voted i V := Decidable.decide (V ≤ 4 ∧ i.val < 3 ∧ 26 * V + 7 + i.val < n)
  accepted i V _ := Decidable.decide (V ≤ 4 ∧ i.val < 3 ∧ 26 * V + 7 + i.val < n)
  local_prepqc i W _ := Decidable.decide (W ≤ 4 ∧ i.val < 3 ∧ 26 * W + 11 + i.val < n)
  timed_out i V := Decidable.decide (V ≤ 3 ∧ i.val < 3 ∧ 26 * V + 25 + i.val < n)
  commit_sent i V := Decidable.decide (V ≤ 4 ∧ i.val < 3 ∧ 26 * V + 14 + i.val < n)
  proposed_in l V := Decidable.decide (V ≤ 4 ∧ l.val = 0 ∧ 26 * V + 6 < n)
  decided i _ := Decidable.decide (i.val < 3 ∧ 18 + i.val < n)
  abandoned i := Decidable.decide (i.val < 3 ∧ 129 + i.val < n)
  avail_ready i _ := Decidable.decide (i.val < 3 ∧ i.val < n)
  timer_expired i V := Decidable.decide (V ≤ 4 ∧ i.val < 3 ∧ 26 * V + 22 + i.val < n)

/-! ## The labels

The first six steps make the correct validators available and have them
propose. Then each view `V ≤ 4` is a block of 26 steps from `26 V + 6`,
by offset `o`:

* `0`: the leader's proposal (fresh in view 0, a re-proposal of the lock
  otherwise); `1`–`3`: each correct validator accepts it; `4`: the prepare
  certificate; `5`–`7`: each adopts it; `8`–`10`: each sends `Commit`;
  `11`: the commit certificate;
* `12`–`14`: each decides (view 0), or a step that changes nothing;
  `15`: a step that changes nothing, across which the clock advances;
* `16`–`18`: each view timer expires;
* `19`–`21`: each times out (views 0–3), or the caller abandons it (view 4);
* `22`: the timeout certificate; `23`–`25`: each enters view `V + 1`.

The last block ends at offset 21, index 132, where the idle tail begins. -/

/-- The label that changes nothing, used for the slots where the clock moves:
availability already marked. -/
def idle : L := .become_avail_ready 0 ()

/-- The label at offset `o` of view `V`'s block. -/
def blockLabel (V o : Nat) : L :=
  match o with
  | 0 => if V = 0 then .leader_propose_first 0 () else .leader_repropose 0 (V - 1) V (V - 1) ()
  | 1 => if V = 0 then .handle_preprepare_first 0 0 () else .handle_preprepare 0 0 (V - 1) V ()
  | 2 => if V = 0 then .handle_preprepare_first 1 0 () else .handle_preprepare 1 0 (V - 1) V ()
  | 3 => if V = 0 then .handle_preprepare_first 2 0 () else .handle_preprepare 2 0 (V - 1) V ()
  | 4 => .form_prepqc V () Q
  | 5 => .adopt_prepqc 0 V ()
  | 6 => .adopt_prepqc 1 V ()
  | 7 => .adopt_prepqc 2 V ()
  | 8 => .send_commit 0 V ()
  | 9 => .send_commit 1 V ()
  | 10 => .send_commit 2 V ()
  | 11 => .form_commitqc V () Q
  | 12 => if V = 0 then .decide 0 0 () else idle
  | 13 => if V = 0 then .decide 1 0 () else idle
  | 14 => if V = 0 then .decide 2 0 () else idle
  | 15 => idle
  | 16 => .expire_timer 0 V
  | 17 => .expire_timer 1 V
  | 18 => .expire_timer 2 V
  | 19 => if V < 4 then .timeout_qc 0 V V () else .abandon 0
  | 20 => if V < 4 then .timeout_qc 1 V V () else .abandon 1
  | 21 => if V < 4 then .timeout_qc 2 V V () else .abandon 2
  | 22 => .form_tc_lock V Q 0 V ()
  | 23 => .sync_view 0 V (V + 1)
  | 24 => .sync_view 1 V (V + 1)
  | _ => .sync_view 2 V (V + 1)

/-- The first six labels: availability, then the three proposals. -/
def prefixLabel : Nat → L
  | 0 => .become_avail_ready 0 ()
  | 1 => .become_avail_ready 1 ()
  | 2 => .become_avail_ready 2 ()
  | 3 => .propose 0 ()
  | 4 => .propose 1 ()
  | _ => .propose 2 ()

/-- **The idle tail**, twenty-two labels in rotation: the prepare and commit
certificates of views 0–4, and the timeout certificates of views 0–3 with
each correct validator's timeout as the carried lock. They are exactly the
fair labels still enabled once the run is idle (`enabled_idle`), and each is
a step that changes nothing. -/
def tailLabel (j : Nat) : L :=
  if j < 5 then .form_prepqc j () Q
  else if j < 10 then .form_commitqc (j - 5) () Q
  else .form_tc_lock ((j - 10) / 3) Q ⟨(j - 10) % 3, by omega⟩ ((j - 10) / 3) ()

/-- The label of the step out of index `n`. -/
def lbl (n : Nat) : L :=
  if n < 6 then prefixLabel n
  else if n < 132 then blockLabel ((n - 6) / 26) ((n - 6) % 26)
  else tailLabel ((n - 132) % 22)

/-- The clock: 0 through view 0, then `5 (V + 1)` from the expiry of view
`V`'s timer, and one unit per step once the run is idle. -/
def clk (n : Nat) : ℕ := if n ≤ 132 then 5 * ((n + 4) / 26) else n - 107

/-! ## Proof tactics

A transition of `sys` unfolds to its guards and an equation between the
updated state and the post-state. At `st` both sides are structure literals
of `decide`d linear facts, so the equation splits field by field and every
remaining goal is linear arithmetic over the index. -/

/-- A bounded quantifier over the five views, expanded, so that `omega` sees
the instances a refutation needs. -/
theorem forall_le_four {P : ℕ → Prop} : (∀ V, V ≤ 4 → P V) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ V hV
    interval_cases V <;> assumption

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

/-- The same, in a hypothesis, with the bounded view quantifiers expanded. -/
local macro "wnorm_at" h:ident : tactic =>
  `(tactic| (
    try dsimp +instances only [nsetW, byzNodeSetFinGen, natViewOrder] at $h:ident
    try simp only [← Bool.decide_and, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      Bool.not_eq_true, decide_eq_false_iff_not, Fin.ext_iff, List.mem_cons, List.mem_nil_iff,
      List.length_cons, List.length_nil, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.val_zero,
      forall_le_four] at $h:ident))

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
  `(tactic| simp only [lbl, blockLabel, prefixLabel, tailLabel, idle, Nat.reduceLT, Nat.reduceSub,
    Nat.reduceDiv, Nat.reduceMod, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceEqDiff,
    OfNat.ofNat_ne_zero, one_ne_zero, reduceCtorEq])

/-! ## The run is a run of the model

The theory meets the model's two assumptions, index 0 is initial, and every
step is a transition: the 132 steps of the active prefix in twelve chunks,
then the idle tail, whose state no longer changes. -/

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

theorem steps_0 (n : Nat) (h₁ : 0 ≤ n) (h₂ : n < 11) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_1 (n : Nat) (h₁ : 11 ≤ n) (h₂ : n < 22) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_2 (n : Nat) (h₁ : 22 ≤ n) (h₂ : n < 33) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_3 (n : Nat) (h₁ : 33 ≤ n) (h₂ : n < 44) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_4 (n : Nat) (h₁ : 44 ≤ n) (h₂ : n < 55) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_5 (n : Nat) (h₁ : 55 ≤ n) (h₂ : n < 66) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_6 (n : Nat) (h₁ : 66 ≤ n) (h₂ : n < 77) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_7 (n : Nat) (h₁ : 77 ≤ n) (h₂ : n < 88) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_8 (n : Nat) (h₁ : 88 ≤ n) (h₂ : n < 99) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_9 (n : Nat) (h₁ : 99 ≤ n) (h₂ : n < 110) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_10 (n : Nat) (h₁ : 110 ≤ n) (h₂ : n < 121) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_11 (n : Nat) (h₁ : 121 ≤ n) (h₂ : n < 132) :
    sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_prefix (n : Nat) (hn : n < 132) : sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  by_cases h0 : n < 11; · exact steps_0 n (by omega) h0
  by_cases h1 : n < 22; · exact steps_1 n (by omega) h1
  by_cases h2 : n < 33; · exact steps_2 n (by omega) h2
  by_cases h3 : n < 44; · exact steps_3 n (by omega) h3
  by_cases h4 : n < 55; · exact steps_4 n (by omega) h4
  by_cases h5 : n < 66; · exact steps_5 n (by omega) h5
  by_cases h6 : n < 77; · exact steps_6 n (by omega) h6
  by_cases h7 : n < 88; · exact steps_7 n (by omega) h7
  by_cases h8 : n < 99; · exact steps_8 n (by omega) h8
  by_cases h9 : n < 110; · exact steps_9 n (by omega) h9
  by_cases h10 : n < 121; · exact steps_10 n (by omega) h10
  exact steps_11 n (by omega) hn

/-- From index 132 on the state no longer changes. -/
theorem st_stable {n : Nat} (h : 132 ≤ n) : st n = st 132 := by
  simp only [st, Mvba.State.mk.injEq, funext_iff]
  wnorm
  wclose

/-- Each idle label is a transition from the idle state to itself. -/
theorem tail_step (j : Nat) (hj : j < 22) : sys.tr thW (st 132) (tailLabel j) (st 132) := by
  interval_cases j <;> wlabel <;> wstep

theorem steps (n : Nat) : sys.tr thW (st n) (lbl n) (st (n + 1)) := by
  by_cases h : n < 132
  · exact steps_prefix n h
  · rw [st_stable (by omega), st_stable (n := n + 1) (by omega)]
    have : lbl n = tailLabel ((n - 132) % 22) := by
      simp only [lbl, if_neg (show ¬ n < 6 by omega), if_neg h]
    rw [this]
    exact tail_step _ (Nat.mod_lt _ (by omega))

/-! ## No fair label moves at a plateau's end

The clock advances only out of the last index of each clock reading: the
end of view `V`'s block (`26 V + 21`, every correct validator settled in
`V`, its timer not yet expired) and the idle tail. At those states every
fair label is either disabled or a step that changes nothing. -/

/-- The indices out of which the clock advances. -/
def PlateauEnd (n : Nat) : Prop := (∃ V, V ≤ 4 ∧ n = 26 * V + 21) ∨ 132 ≤ n

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
      rcases hn with ⟨V, hV, rfl⟩ | hn <;>
      first
        | omega
        | (apply hne; simp only [st, Mvba.State.mk.injEq, funext_iff]; wnorm; wclose)
  all_goals (repeat (obtain ⟨_, htr⟩ := htr))
  all_goals (rcases hn with ⟨V, hV, rfl⟩ | hn)
  all_goals first
    | omega
    | (apply hne; simp only [st, Mvba.State.mk.injEq, funext_iff]; wnorm; wclose)

/-! ## The idle tail is weakly fair

Once idle, the fair labels that are still *enabled* — plain `Enabled`, the
premise of `FJustice` — are exactly the twenty-two of `tailLabel`: every
validator label is disabled (the correct validators are abandoned, the
Byzantine one is not honest), and an assembly is enabled only over the
correct quorum and only for a certificate that already exists. The tail
fires each of them every twenty-two steps. This is where the finite quorum
sort matters (Bounds.md §6.2.4): at `ByzNSet 4` a certificate has one
quorum that can assemble it, so each such label is one label. -/

theorem enabled_idle {l : L} {hd : Hop} (hh : hop l = some hd)
    (hen : Enabled sys thW (st 132) l) : ∃ j, j < 22 ∧ tailLabel j = l := by
  obtain ⟨s', htr⟩ := hen
  cases l
  all_goals first | (simp [hop] at hh; done) | skip
  all_goals wunfold htr
  case form_tc_nolock v q =>
    obtain ⟨hq, hall, -⟩ := htr
    rcases supermajority_cases q hq with h | h | h | h | h <;> simp [h] at hall <;>
      exact ((hall _).1 rfl).elim
  case form_prepqc v e q =>
    obtain ⟨hq, hall, -⟩ := htr
    rcases supermajority_cases q hq with h | h | h | h | h <;>
      simp only [h, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, or_false,
        forall_eq, Fin.isValue] at hall <;>
      wnorm_at hall
    all_goals first
      | omega
      | (refine ⟨v, by omega, ?_⟩
         simp only [tailLabel, if_pos (show v < 5 by omega)]
         congr
         exact Subtype.ext h.symm)
  case form_commitqc v e q =>
    obtain ⟨hq, hall, -⟩ := htr
    rcases supermajority_cases q hq with h | h | h | h | h <;>
      simp only [h, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, or_false,
        forall_eq, Fin.isValue] at hall <;>
      wnorm_at hall
    all_goals first
      | omega
      | (refine ⟨v + 5, by omega, ?_⟩
         simp only [tailLabel, if_neg (show ¬ v + 5 < 5 by omega),
           if_pos (show v + 5 < 10 by omega), Nat.add_sub_cancel]
         congr
         exact Subtype.ext h.symm)
  case form_tc_lock v q r0 w e =>
    obtain ⟨hq, hr0, ht, -, -, hall, -⟩ := htr
    rcases supermajority_cases q hq with h | h | h | h | h <;>
      simp only [h, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, or_false,
        forall_eq, Fin.isValue] at hall <;>
      wnorm_at hall
    all_goals first
      | omega
      | (refine ⟨10 + 3 * v + r0.val, by omega, ?_⟩
         simp only [tailLabel, if_neg (show ¬ 10 + 3 * v + r0.val < 5 by omega),
           if_neg (show ¬ 10 + 3 * v + r0.val < 10 by omega)]
         congr 1 <;> first | omega | (apply Subtype.ext; exact h.symm) | (apply Fin.ext; dsimp only; omega))
  all_goals (repeat (obtain ⟨_, htr⟩ := htr))
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
  clk_unbounded t := ⟨t + 132, by simp only [clk]; split_ifs <;> omega⟩
  gst := 0

/-- A correct validator is one of the first three. -/
theorem correct_lt {p : Fin 4} (h : ¬ nsetW.is_byz p = true) : p.val < 3 := by
  dsimp +instances only [nsetW, byzNodeSetFinGen] at h
  simp only [decide_eq_true_eq] at h
  omega

/-- Every index is followed, on the same clock reading, by a plateau end. -/
theorem plateau_after (N : Nat) : ∃ P, PlateauEnd P ∧ N ≤ P ∧ clk P = clk N := by
  by_cases h : N ≤ 125
  · refine ⟨26 * ((N + 4) / 26) + 21, Or.inl ⟨(N + 4) / 26, by omega, rfl⟩, by omega, ?_⟩
    simp only [clk]; split_ifs <;> omega
  · refine ⟨max N 132, Or.inr (by omega), by omega, ?_⟩
    simp only [clk]; split_ifs <;> omega

/-- Only the scheduled steps expire a timer: view `v`'s, for validator `i`, at
index `26 v + 22 + i`. -/
theorem lbl_expire {n : Nat} {i : Fin 4} {v : ℕ} (h : lbl n = .expire_timer i v) :
    i.val < 3 ∧ v ≤ 4 ∧ n = 26 * v + 22 + i.val := by
  by_cases hn : n < 132
  · revert h
    interval_cases n <;> wlabel <;>
      simp only [Label.expire_timer.injEq, reduceCtorEq, false_implies, and_imp] <;>
      (rintro rfl rfl; decide)
  · simp only [lbl, if_neg (show ¬ n < 6 by omega), if_neg hn, tailLabel] at h
    split_ifs at h

/-! ## (a) The timed premises -/

/-- **(Δ-justice)**, with its antecedent false: every window reaches a plateau
end, where the label is not move-enabled. -/
theorem boundedJustice : BoundedJustice schW run := by
  intro l hd hh N hen
  exfalso
  obtain ⟨P, hP, hNP, hclk⟩ := plateau_after N
  refine quiet hP hh (hen P hNP ?_)
  show clk P ≤ max (clk N) 0 + schW.bound hd
  rw [hclk]
  exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)

/-- **(T-timer)**: view `v`'s timer expires exactly five units after the
validator entered `v`. -/
theorem timerPunctual : TimerPunctual schW run := by
  refine ⟨fun n i v _ hl => ?_, fun m i v _ hent => ?_⟩
  · obtain ⟨hi, hv, rfl⟩ := lbl_expire hl
    refine ⟨26 * v + 4 + i.val, by omega, ?_, ?_⟩
    · show (st _).entered i v = true
      simp only [st, decide_eq_true_eq]
      omega
    · show clk _ + 5 ≤ clk _
      simp only [clk]; split_ifs <;> omega
  · change (st m).entered i v = true at hent
    have he : v ≤ 4 ∧ i.val < 3 ∧ 26 * v + 3 + i.val < m := by simpa [st] using hent
    refine ⟨max m (26 * v + 23 + i.val), le_max_left _ _, ?_, ?_⟩
    · show (st _).timer_expired i v = true
      simp only [st, decide_eq_true_eq]
      omega
    · show clk _ ≤ clk m + 5
      simp only [clk]; split_ifs <;> omega

/-- **(Δ-avail)**: availability is marked before anyone accepts. -/
theorem availWithin : AvailWithin schW run := by
  intro m i v e _ hacc
  change (st m).accepted i v e = true at hacc
  have ha : v ≤ 4 ∧ i.val < 3 ∧ 26 * v + 7 + i.val < m := by simpa [st] using hacc
  refine ⟨m, le_rfl, ?_, ?_⟩
  · show (st m).avail_ready i e = true
    simp only [st, decide_eq_true_eq]
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

/-- `ℓ` at this schedule: `1 + (1 + 1) • 7 + 4 + 0`. -/
theorem ell : schW.ℓ natViewOrderEnum = 19 := rfl

/-- Every correct validator has proposed by index 6, at clock 0. -/
theorem proposes_by (p : Fin 4) (hp : ¬ nsetW.is_byz p = true) :
    trW.byTime 0 (fun st => ∃ v, (mvbaSafety thW).proposed st p v) := by
  refine ⟨6, ?_, (), ?_⟩
  · show clk 6 ≤ 0
    decide
  · show (st 6).input p () = true
    have := correct_lt hp
    simp only [st, decide_eq_true_eq]
    omega

/-- Every value is valid. -/
theorem valid_inputs (p : Fin 4) (_ : ¬ nsetW.is_byz p = true) (n : Nat) (v : Unit)
    (_ : (mvbaSafety thW).proposed (trW.at' n) p v) : (mvbaSafety thW).Valid v := rfl

/-- The caller abandons only at clock 25, after `max(0, 0) + ℓ = 19`. -/
theorem abandons_late (p : Fin 4) (_ : ¬ nsetW.is_byz p = true) (n : Nat)
    (hab : (mvbaSafety thW).abandoned (trW.at' n) p) :
    ∃ u, TotalOrder.le 0 u ∧ TotalOrder.le trW.gst u ∧
      (∀ u', TotalOrder.le 0 u' → TotalOrder.le trW.gst u' → TotalOrder.le u u') ∧
      ¬ TotalOrder.le (trW.clk n) (u + schW.ℓ natViewOrderEnum) := by
  change (st n).abandoned p = true at hab
  have ha : p.val < 3 ∧ 129 + p.val < n := by simpa [st] using hab
  refine ⟨0, TotalOrder.le_refl _, TotalOrder.le_refl _, fun _ h _ => h, ?_⟩
  rw [ell]
  show ¬ clk n ≤ 0 + 19
  simp only [clk]; split_ifs <;> omega

/-! ## (b) The untimed premises, on the same run -/

theorem fJustice : FJustice run.toLRun := by
  intro l hj N hen
  obtain ⟨hd, hh⟩ := Option.isSome_iff_exists.mp ((hop_isSome_iff l).mpr hj)
  have h132 := hen (max N 132) (le_max_left _ _)
  change Enabled sys thW (st (max N 132)) l at h132
  rw [st_stable (le_max_right _ _)] at h132
  obtain ⟨j, hj22, rfl⟩ := enabled_idle hh h132
  refine ⟨132 + 22 * N + j, by omega, ?_⟩
  show lbl _ = _
  simp only [lbl, if_neg (show ¬ 132 + 22 * N + j < 6 by omega),
    if_neg (show ¬ 132 + 22 * N + j < 132 by omega),
    show (132 + 22 * N + j - 132) % 22 = j by omega]

/-- **(A-viewsync)** with `W = 1`: the view-0 timers do expire, and a commit
certificate (of view 0) exists before any view-1 timer does. -/
theorem aViewSync : AViewSync run.toLRun := by
  refine ⟨1, 0, 0, rfl, rfl, ?_, fun i V hi hV _ => ?_, fun i n hi hexp => ?_⟩
  · dsimp +instances only [nsetW, byzNodeSetFinGen]
    decide
  · have hV0 : V = 0 := by
      have : V < 1 := hV
      omega
    subst hV0
    refine ⟨132, ?_⟩
    show (st 132).timer_expired i 0 = true
    have := correct_lt hi
    simp only [st, decide_eq_true_eq]
    omega
  · change (st n).timer_expired i 1 = true at hexp
    have he : i.val < 3 ∧ 48 + i.val < n := by simpa [st] using hexp
    refine ⟨0, (), ?_⟩
    show (st n).msg_commitqc 0 () = true
    simp only [st, decide_eq_true_eq]
    omega

theorem fAvail : FAvail run.toLRun := by
  intro i n V E _ hacc
  change (st n).accepted i V E = true at hacc
  have ha : V ≤ 4 ∧ i.val < 3 ∧ 26 * V + 7 + i.val < n := by simpa [st] using hacc
  refine ⟨n, ?_⟩
  show (st n).avail_ready i E = true
  simp only [st, decide_eq_true_eq]
  omega

theorem allPropose : AllPropose run.toLRun := by
  intro i hi
  refine ⟨6, (), ?_⟩
  show (st 6).input i () = true
  have := correct_lt hi
  simp only [st, decide_eq_true_eq]
  omega

theorem noEarlyAbandon : NoEarlyAbandon run.toLRun := by
  intro i n _ hab
  change (st n).abandoned i = true at hab
  have ha : i.val < 3 ∧ 129 + i.val < n := by simpa [st] using hab
  refine ⟨(), ?_⟩
  show (st n).decided i () = true
  simp only [st, decide_eq_true_eq]
  omega

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
(F-justice) with plain enabledness, (A-viewsync), (F-avail), `AllPropose`
and `NoEarlyAbandon`.

It rules out that the untimed Termination claim is vacuous, and in
particular that its weak-fairness premise contradicts the rest: at the
concrete quorum family the enabled-forever assembly labels are finitely
many, and the run fires each of them forever (Bounds.md §6.2.4). -/
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
