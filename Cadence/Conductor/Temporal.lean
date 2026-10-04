import Cadence.Conductor.Recovery

/-! # Conductor.Temporal — the `OrchestratorTemporal` instance, and the full `Orchestrator`

[ConductorBounds.md](../../docs/ConductorBounds.md) §9, stage K6. The
temporal level of Module 2 (`mod:orchestrator_2`), instantiated over the
fragment the Conductor proves, `orchestratorSafety th`
([Composition.lean](../Composition.lean)), for an arbitrary ACS meeting its
contract, and joined with the fragment into the full contract.
[Chorus/Temporal.lean](../Chorus/Temporal.lean) is the template.

Each class field and what proves it:

* **`Admissible`** is `Conductor.Admissible`: the run is the contract's
  reading (`contractRun`) of a labelled timed run of the Conductor that
  satisfies `Sync`, the claims' run premises by their own names: the rows,
  the punctual openings, one clock, and the ACS meeting its module
  ([Schedule.lean](Schedule.lean)). The labels are the witness of how the
  run was scheduled, which a `TimedRun` does not carry;
* **`admissible_exists`** is the idle run (`Conductor.admissible_exists`):
  the caller completes nothing, so no correct validator becomes ready,
  nobody proposes to an ACS, and the run only moves the clock from one
  starting time to the next and opens window 1's slots at their starting
  times. The ACS premise applies only once a correct validator has
  proposed, so it holds with nothing to say (F24);
* **`clock_agrees`** is `ClockAgrees`, a conjunct of `Sync`;
* **`caller_d_tot`** and **`caller_ℓ`** are Chorus's `d_tot` and
  `ℓ_chorus` (`ConductorSchedule.d_tot`, `ℓchorus`), the constants the
  claims assume (R-tot) and (R-term) at;
* **`totality`** follows from `Conductor.totality` (Lemma 15
  (`lemma:conductor-totality`)): an opening reaches every correct validator
  by `max(t, GST) + d_tot`, so in particular eventually;
* **`bound`** is `2W − p` and **`boundedness`** is `Conductor.boundedness`
  (Lemma 14 (`lem:boundedness`));
* **`recovery_time`** is `2Wτ` and **`recovery`** is `Conductor.recovery`
  (Lemma 16 (`lemma:conductor-recovery`));
* **`OrchestratorWithTotality`**: `d_tot` is Chorus's `d_tot`, the paper's
  `Δ` at `δ = 0` (`conductorWithTotality_d_tot_paper`), and `totality` is
  `Conductor.totality`.

The class carries the paper's values, `2W − p` and `2Wτ`. The sharper
`(W + p − 1)τ` of `Conductor.recovery_sharp` stays a separate theorem, with
P18's slack ([PaperAlignment.md](../../docs/PaperAlignment.md) §6).

`conductorFull` joins the fragment and the temporal level through
[Composition.lean](../Composition.lean)'s `orchestrator_of_temporal`, and
`conductorFull_toSafety` checks by `rfl` that the join hands back exactly
`orchestratorSafety th`.

## What the instance is proven from

Nothing is assumed of the protocol. The hypotheses are the claims'
configuration premises, each by its name in
[Schedule.lean](Schedule.lean), and the time theory:

* **the ACS is an assumed module**: an arbitrary instance `TA` of its
  temporal level over the fragment the Conductor consumes, with the
  system's constants (`TA.Δ = Δ`, `TA.ℓ = ℓ`) and at most its
  `fault_bound` validators Byzantine (P17);
* **the configuration**: τ-spaced starting times (`StartTimes`), windows
  of `W` slots with the readiness boundary at the `(p + 1)`-th
  (`WindowShifts`), starting times that are unbounded (`StartsUnbounded`,
  F28), and a successor for every window (`WindowsUnbounded`, F30);
* finitely many validators, and an ordered time (F27).

The schedule's own fields (the four parameter assumptions, `δ = 0`) are
data of `sch`. Two configuration premises hold outright at the system's
types (`windowsUnbounded_nat` at `window := ℕ`, and
`startsUnbounded_of_startTimes` at an Archimedean time whose slot 1 starts
at or after `0`); `conductorFullNat` is the full contract with both
discharged. -/

namespace Conductor

open Cadence
open scoped Cadence.Timed

attribute [local instance] natSlotOrder

/-! ## The two actions the idle run takes

`tick` and `open_slot`: their guards are their enabledness, and their
effects on the clock and on `opened`. Every other field is framed by the
generated `frame_*` lemmas. -/

section Actions

variable {window node acsstate time : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [Inhabited time] [win_ord : TotalOrderWithMinimum window] [time_ord : TotalOrder time]
  [fm : FaultModel node] [A : ACSSafety node ℕ acsstate fm.byz]
  {th : Conductor.Theory ℕ window time node acsstate}
  {st st' : CState window time node acsstate}

/-- Expose one action's transition body (as in [Schedule.lean](Schedule.lean)). -/
local macro "conductor_tr" h:ident : tactic =>
  `(tactic| (simp only [Conductor.relationalTransitionSystem, Conductor.Next, Conductor.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation. -/
local macro "conductor_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id] at *)

/-- Turn an enabledness goal into the action's guards. -/
local macro "conductor_enabled" : tactic =>
  `(tactic| simp only [Enabled, Conductor.relationalTransitionSystem, Conductor.Next,
      Conductor.NextAct, trSimp])

/-- **The clock can advance to any later time**, or stay where it is. -/
theorem enabled_tick {t : time} (h : TotalOrder.le st.now t) :
    Enabled (Conductor.relationalTransitionSystem ℕ window time node acsstate) th st (.tick t) := by
  conductor_enabled
  exact ⟨_, h, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **What `tick t` does** to the clock: it reads `t`. -/
theorem tick_now {t : time}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st (.tick t) st') :
    st'.now = t := by
  conductor_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  conductor_field_simp

/-- **The opening's guards are its enabledness** (Algorithm 7, lines 27–28
(`line:conductor-wait-for-open`–`line:trigger-open`)). -/
theorem enabled_open_slot {i : node} {s : ℕ} {w : window} {f b l : ℕ}
    (hi : ¬ fm.byz i) (he : st.entered i w = true) (hb : WinBounds (th := th) st w f b l)
    (hfs : f ≤ s) (hsl : s ≤ l) (hno : st.opened i s = false)
    (hnow : TotalOrder.le (th.start_time s) st.now)
    (hbelow : ∀ s' w0 f0 b0 l0, st.entered i w0 = true → WinBounds (th := th) st w0 f0 b0 l0 →
      f0 ≤ s' → s' ≤ l0 → s' < s → st.opened i s' = true) :
    Enabled (Conductor.relationalTransitionSystem ℕ window time node acsstate) th st
      (.open_slot i s w f b l) := by
  conductor_enabled
  exact ⟨_, hi, he, hb, hfs, hsl, fun h => Bool.false_ne_true (hno.symm.trans h), hnow, hbelow, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **What the opening does** to `opened`: it adds the one pair. -/
theorem open_slot_opened {i : node} {s : ℕ} {w : window} {f b l : ℕ}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.open_slot i s w f b l) st') (j : node) (x : ℕ) :
    st'.opened j x = true ↔ (st.opened j x = true ∨ (j = i ∧ x = s)) := by
  conductor_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  conductor_field_simp
  exact ⟨fun h => h.elim (fun h => Or.inr ⟨h.1.symm, h.2.symm⟩) Or.inl,
    fun h => h.elim Or.inr (fun h => Or.inl ⟨h.1.symm, h.2.symm⟩)⟩

end Actions

/-! ## Index arithmetic

The idle run proceeds in blocks of `B = |node| + 1` steps, one block per
slot `k`: a `tick` to `k`'s starting time, then one step per validator,
which opens `k` there if the validator is correct and `k` is in window 1,
and is a `tick` in place otherwise. Its state at index `n` is described by
two numbers: the slot whose starting time the clock reads (`nowSlot`), and
for each validator `j` and slot `s` whether `s`'s opening at `j` lies
before `n` (`s · B + idx j + 2 ≤ n`). -/

section Arith

/-- A position `s · B + a` with `1 ≤ a ≤ B` determines `s` and `a`. -/
theorem blk_unique {B s k a b : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ B) (hb1 : 1 ≤ b) (hb : b ≤ B)
    (h : s * B + a = k * B + b) : s = k ∧ a = b := by
  rcases lt_trichotomy s k with hlt | rfl | hlt
  · have := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega
  · omega
  · have := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega

theorem div_blk {B s a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ B) : (s * B + a + (B - 1)) / B = s + 1 := by
  apply Nat.div_eq_of_lt_le
  · rw [Nat.succ_mul]; omega
  · rw [Nat.succ_mul, Nat.succ_mul]; omega

/-- The slot whose starting time the idle run's clock reads at index `n`:
the current block's slot once its `tick` has been taken, the previous
block's before. -/
def nowSlot (B n : ℕ) : ℕ := (n + (B - 1)) / B - 1

theorem nowSlot_add {B s a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ B) : nowSlot B (s * B + a) = s := by
  simp only [nowSlot, div_blk h1 h2, Nat.add_sub_cancel]

theorem nowSlot_mono (B : ℕ) {m n : ℕ} (h : m ≤ n) : nowSlot B m ≤ nowSlot B n :=
  Nat.sub_le_sub_right (Nat.div_le_div_right (by omega)) 1

/-- After any step, the clock reads the current block's slot. -/
theorem nowSlot_succ {B : ℕ} (hB : 0 < B) (n : ℕ) : nowSlot B (n + 1) = n / B := by
  have hd := Nat.div_add_mod' n B
  have hm := Nat.mod_lt n hB
  conv_lhs => rw [← hd, Nat.add_assoc]
  exact nowSlot_add (by omega) (by omega)

/-- Within a block, after its `tick`, the clock reads the block's slot. -/
theorem nowSlot_of_mod_ne {B n : ℕ} (hB : 0 < B) (hq : n % B ≠ 0) : nowSlot B n = n / B := by
  have hd := Nat.div_add_mod' n B
  have hm := Nat.mod_lt n hB
  conv_lhs => rw [← hd]
  exact nowSlot_add (by omega) (by omega)

/-! ### Positions in a block -/

variable {node : Type} [Fintype node]

/-- The block length, one step per validator and the `tick`. -/
abbrev blk (node : Type) [Fintype node] : ℕ := Fintype.card node + 1

/-- A validator's position within a block. -/
noncomputable def idx (j : node) : ℕ := (Fintype.equivFin node j : ℕ)

theorem idx_lt (j : node) : idx j < Fintype.card node := (Fintype.equivFin node j).isLt

theorem idx_inj {i j : node} (h : idx i = idx j) : i = j :=
  (Fintype.equivFin node).injective (Fin.ext h)

/-- The validator a non-`tick` step of a block acts for. -/
noncomputable def blkNode {q : ℕ} (hq : q % blk node ≠ 0) : node :=
  (Fintype.equivFin node).symm ⟨q % blk node - 1, by
    have h : q % blk node < Fintype.card node + 1 := Nat.mod_lt _ (Nat.succ_pos _)
    omega⟩

theorem idx_blkNode {q : ℕ} (hq : q % blk node ≠ 0) : idx (blkNode hq) = q % blk node - 1 := by
  simp [idx, blkNode]

end Arith

/-! ## The idle run -/

section Idle

open Classical

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time]
  [Fintype node]
  {th : Conductor.Theory ℕ window time node acsstate}

variable (th) in
/-- **The idle run's label at index `n`** (block `k = n / B`, position
`q = n % B`): at `q = 0` a `tick` to slot `k`'s starting time; at `q > 0`,
for the `q`-th validator, the opening of `k` if the validator is correct
and `k` lies in window 1, else a `tick` in place. -/
noncomputable def idleLabel (n : ℕ) : CLabel window time node acsstate :=
  if hq : n % blk node = 0 then .tick (th.start_time (n / blk node))
  else if ¬ fm.byz (blkNode hq) ∧ n / blk node ≤ th.genesis_last then
    .open_slot (blkNode hq) (n / blk node) win_ord.zero 0 th.genesis_boundary th.genesis_last
  else .tick (th.start_time (n / blk node))

variable (th) in
/-- One step of the idle run: the label's transition, if it has one. -/
noncomputable def idleNext (st : CState window time node acsstate) (l : CLabel window time node acsstate) :
    CState window time node acsstate :=
  if h : ∃ st', (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st l st' then
    h.choose else st

variable (th) in
/-- The idle run's states from `st₀`. -/
noncomputable def idleSt (st₀ : CState window time node acsstate) : ℕ → CState window time node acsstate
  | 0 => st₀
  | n + 1 => idleNext th (idleSt st₀ n) (idleLabel th n)

variable (th) in
/-- **What the idle run's state at index `n` is**: every validator in
window 1 and no other, every ACS in its initial state, no interval
recorded, nothing completed, the clock at `nowSlot n`'s starting time, and
`(j, s)` opened exactly when `j` is correct, `s` lies in window 1 and its
opening is before `n`. -/
structure IdleInv (n : ℕ) (st : CState window time node acsstate) : Prop where
  entered : ∀ j x, st.entered j x = true ↔ x = win_ord.zero
  acs : ∀ x, st.acs_state x = th.acs_init_state x
  decided : ∀ x f b l, st.acs_decided x f b l = false
  completed : ∀ j s, st.completed j s = false
  now : st.now = th.start_time (nowSlot (blk node) n)
  opened : ∀ j s, st.opened j s = true ↔
    (¬ fm.byz j ∧ s ≤ th.genesis_last ∧ s * blk node + idx j + 2 ≤ n)

variable (ha : (Conductor.relationalTransitionSystem ℕ window time node acsstate).assumptions th)

include ha in
theorem idleInv_zero {st₀ : CState window time node acsstate}
    (hi : (Conductor.relationalTransitionSystem ℕ window time node acsstate).init th st₀) :
    IdleInv th 0 st₀ where
  entered := init_entered hi
  acs x := by rw [acs_state_init hi]
  decided := init_decided hi
  completed := Conductor.completed.init hi
  now := by
    rw [init_now hi, ha.2.2.1.2.2]
    simp [nowSlot, Nat.div_eq_of_lt (Nat.lt_succ_self (Fintype.card node))]
    rfl
  opened j s := by
    rw [Conductor.opened.init hi j s]
    simp

omit [Inhabited window] [Inhabited node] [Inhabited acsstate] A [LinearOrder time] [Inhabited time] in
/-- In the idle run's states, a window's bounds are window 1's. -/
theorem IdleInv.winBounds {n : ℕ} {st : CState window time node acsstate} (hinv : IdleInv th n st)
    {w : window} {f b l : ℕ} (h : WinBounds (th := th) st w f b l) :
    w = win_ord.zero ∧ f = 0 ∧ b = th.genesis_boundary ∧ l = th.genesis_last := by
  rcases h with h | h
  · exact h
  · rw [hinv.decided] at h; exact absurd h Bool.false_ne_true

omit [Fintype node] in
/-- A label that is enabled is the idle run's step. -/
theorem idleNext_tr {st : CState window time node acsstate} {l : CLabel window time node acsstate}
    (h : Enabled (Conductor.relationalTransitionSystem ℕ window time node acsstate) th st l) :
    (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st l (idleNext th st l) := by
  have h' : ∃ st', (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st l st' := h
  simp only [idleNext, dif_pos h']
  exact h'.choose_spec

/-- **A `tick` to the block's slot that opens nothing**: the description
carries over, provided no opening falls due at this index. -/
theorem idle_tick {n : ℕ} {st st' : CState window time node acsstate} (hinv : IdleInv th n st)
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.tick (th.start_time (n / blk node))) st')
    (hnew : ∀ j s, ¬ fm.byz j → s ≤ th.genesis_last → s * blk node + idx j + 2 ≠ n + 1) :
    IdleInv th (n + 1) st' where
  entered j x := by rw [Conductor.tick.frame_entered htr]; exact hinv.entered j x
  acs x := by rw [Conductor.tick.frame_acs_state htr]; exact hinv.acs x
  decided x f b l := by rw [Conductor.tick.frame_acs_decided htr]; exact hinv.decided x f b l
  completed j s := by rw [Conductor.tick.frame_completed htr]; exact hinv.completed j s
  now := by rw [tick_now htr, nowSlot_succ (Nat.succ_pos _)]
  opened j s := by
    rw [Conductor.tick.frame_opened htr, hinv.opened j s]
    constructor
    · rintro ⟨hj, hs, h⟩; exact ⟨hj, hs, by omega⟩
    · rintro ⟨hj, hs, h⟩; exact ⟨hj, hs, by have := hnew j s hj hs; omega⟩

/-- **The opening of the block's slot at the block's validator**: the
description carries over, with that one pair added. -/
theorem idle_open {n : ℕ} {st st' : CState window time node acsstate} (hinv : IdleInv th n st)
    {i : node} (hi : ¬ fm.byz i) (hk : n / blk node ≤ th.genesis_last) (hq : n % blk node ≠ 0)
    (hidx : idx i = n % blk node - 1)
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.open_slot i (n / blk node) win_ord.zero 0 th.genesis_boundary th.genesis_last) st') :
    IdleInv th (n + 1) st' where
  entered j x := by rw [Conductor.open_slot.frame_entered htr]; exact hinv.entered j x
  acs x := by rw [Conductor.open_slot.frame_acs_state htr]; exact hinv.acs x
  decided x f b l := by rw [Conductor.open_slot.frame_acs_decided htr]; exact hinv.decided x f b l
  completed j s := by rw [Conductor.open_slot.frame_completed htr]; exact hinv.completed j s
  now := by
    rw [Conductor.open_slot.frame_now htr, hinv.now, nowSlot_of_mod_ne (Nat.succ_pos _) hq,
      nowSlot_succ (Nat.succ_pos _)]
  opened j s := by
    have hd := Nat.div_add_mod' n (blk node)
    have hm : n % blk node < Fintype.card node + 1 := Nat.mod_lt _ (Nat.succ_pos _)
    have hj' := idx_lt j
    have hb : blk node = Fintype.card node + 1 := rfl
    rw [open_slot_opened htr j s, hinv.opened j s]
    constructor
    · rintro (⟨hj, hs, h⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hj, hs, by omega⟩
      · exact ⟨hi, hk, by omega⟩
    · rintro ⟨hj, hs, h⟩
      by_cases heq : s * blk node + idx j + 2 = n + 1
      · obtain ⟨h1, h2⟩ := blk_unique (B := blk node) (s := s) (a := idx j + 2) (b := n % blk node + 1)
          (k := n / blk node) (by omega) (by omega) (by omega) (by omega) (by omega)
        exact Or.inr ⟨idx_inj (by omega), h1⟩
      · exact Or.inl ⟨hj, hs, by omega⟩

include ha in
/-- **The idle run steps, and its description carries over.** -/
theorem idle_step {n : ℕ} {st : CState window time node acsstate} (hinv : IdleInv th n st) :
    (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st (idleLabel th n)
        (idleNext th st (idleLabel th n)) ∧
      IdleInv th (n + 1) (idleNext th st (idleLabel th n)) := by
  have hB : 0 < blk node := Nat.succ_pos _
  have hd := Nat.div_add_mod' n (blk node)
  have hm : n % blk node < Fintype.card node + 1 := Nat.mod_lt _ hB
  have hb : blk node = Fintype.card node + 1 := rfl
  by_cases hq : n % blk node = 0
  · -- The block's `tick`.
    have hl : idleLabel th n = .tick (th.start_time (n / blk node)) := by
      simp only [idleLabel, dif_pos hq]
    rw [hl]
    have hle : st.now ≤ th.start_time (n / blk node) := by
      rw [hinv.now, ← nowSlot_succ hB n]
      exact start_time_mono ha (nowSlot_mono _ (Nat.le_succ n))
    have htr := idleNext_tr (enabled_tick (th := th) (st := st) hle)
    refine ⟨htr, idle_tick hinv htr fun j s _ _ heq => ?_⟩
    have := idx_lt j
    have := (blk_unique (B := blk node) (s := s) (a := idx j + 2) (b := 1) (k := n / blk node)
      (by omega) (by omega) le_rfl (by omega) (by omega)).2
    omega
  · have hnow : st.now = th.start_time (n / blk node) := by rw [hinv.now, nowSlot_of_mod_ne hB hq]
    by_cases hc : ¬ fm.byz (blkNode hq) ∧ n / blk node ≤ th.genesis_last
    · -- The opening of the block's slot at the block's validator.
      have hl : idleLabel th n = .open_slot (blkNode hq) (n / blk node) win_ord.zero 0
          th.genesis_boundary th.genesis_last := by
        simp only [idleLabel, dif_neg hq, if_pos hc]
      rw [hl]
      have hidx := idx_blkNode hq
      have htr := idleNext_tr (enabled_open_slot (th := th) (st := st) hc.1
        ((hinv.entered _ _).2 rfl) (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (Nat.zero_le _) hc.2
        (Bool.eq_false_iff.2 fun h => by
          obtain ⟨-, -, h⟩ := (hinv.opened _ _).1 h
          omega)
        (by rw [hnow]; exact le_rfl)
        (fun s' w0 f0 b0 l0 _ hb _ hl hlt => by
          obtain ⟨-, -, -, rfl⟩ := hinv.winBounds hb
          have := Nat.mul_le_mul_right (blk node) (Nat.succ_le_of_lt hlt)
          rw [Nat.succ_mul] at this
          exact (hinv.opened _ _).2 ⟨hc.1, hl, by have := idx_lt (blkNode hq); omega⟩))
      exact ⟨htr, idle_open hinv hc.1 hc.2 hq hidx htr⟩
    · -- A `tick` in place.
      have hl : idleLabel th n = .tick (th.start_time (n / blk node)) := by
        simp only [idleLabel, dif_neg hq, if_neg hc]
      rw [hl]
      have htr := idleNext_tr (enabled_tick (th := th) (st := st) (by rw [hnow]; exact le_rfl))
      refine ⟨htr, idle_tick hinv htr fun j s hj hs heq => hc ?_⟩
      have := idx_lt j
      obtain ⟨h1, h2⟩ := blk_unique (B := blk node) (s := s) (a := idx j + 2) (b := n % blk node + 1)
        (k := n / blk node) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hji : j = blkNode hq := idx_inj (by rw [idx_blkNode hq]; omega)
      subst hji h1
      exact ⟨hj, hs⟩

variable {st₀ : CState window time node acsstate}
  (hi : (Conductor.relationalTransitionSystem ℕ window time node acsstate).init th st₀)

include ha hi in
/-- The idle run's description holds at every index. -/
theorem idleSt_inv (n : ℕ) : IdleInv th n (idleSt th st₀ n) := by
  induction n with
  | zero => exact idleInv_zero ha hi
  | succ n ih => exact (idle_step ha ih).2

/-- **The idle run**, as a labelled timed run of the Conductor: its clock is
the model's `now`, which steps from one starting time to the next, so it is
unbounded exactly because the starting times are (`StartsUnbounded`). -/
noncomputable def idleRun (hunb : StartsUnbounded th) : TConductorRun th where
  at' := idleSt th st₀
  lbl := idleLabel th
  holds := ha
  starts := hi
  steps n := (idle_step ha (idleSt_inv ha hi n)).1
  clk n := (idleSt th st₀ n).now
  clk_mono n := by
    rw [(idleSt_inv ha hi n).now, (idleSt_inv ha hi (n + 1)).now]
    exact start_time_mono ha (nowSlot_mono _ (Nat.le_succ n))
  clk_unbounded t := by
    obtain ⟨s, hs⟩ := hunb t
    refine ⟨s * blk node + 1, ?_⟩
    rw [(idleSt_inv ha hi _).now, nowSlot_add le_rfl (Nat.succ_pos _)]
    exact hs
  gst := st₀.now

end Idle

/-! ## The idle run meets the timing model -/

section IdleTimed

open Classical

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  [Fintype node]
  {th : Conductor.Theory ℕ window time node acsstate}

omit [Inhabited time] in
/-- **A row whose gate never opens is met**: with `δ ≥ 0` the gate would
have to hold where the window opens, at the very index it is measured from. -/
theorem bff_of_never {ρ σ lbl : Type} {sys : Veil.RelationalTransitionSystem ρ σ lbl}
    {th' : ρ} {r : TLRun sys th' time} {D δ : time} (hδ : 0 ≤ δ) {C gate : σ → Prop}
    {S : lbl → Prop} (hg : ∀ n, ¬ gate (r.at' n)) : BufferedFairFamily r D δ C gate S := by
  intro N N' _ _ hgate
  have h1 : r.clk N' ≤ r.ref N' + δ := le_trans (r.clk_le_ref N') (le_add_of_nonneg_right hδ)
  have h2 : r.ref N' + δ ≤ r.bufWindow N N' D δ := le_max_right _ _
  exact (hg N' (hgate N' le_rfl (h1.trans h2))).elim

omit [Inhabited time] in
/-- **The readiness threshold is at least 2**: assumption (4), `d_tot + ℓ ≤
(p − 1)τ`, has a positive left side (`0 ≤ d_tot`, `0 < ℓ`), so `p − 1 ≥ 1`.
It is the reason the idle run stays idle: window 1's first slot lies below
its readiness boundary, and nothing completes it. -/
theorem ConductorSchedule.two_le_p (sch : ConductorSchedule view time vfin) : 2 ≤ sch.p := by
  by_contra h
  have h4 := sch.assm_four_d
  rw [show sch.p - 1 = 0 by omega, zero_nsmul] at h4
  exact absurd h4 (not_le.2 (lt_of_lt_of_le sch.ℓ_pos (le_add_of_nonneg_left sch.d_tot_nonneg)))

variable (sch : ConductorSchedule view time vfin)
  (ha : (Conductor.relationalTransitionSystem ℕ window time node acsstate).assumptions th)
  (hshift : WindowShifts sch th)

omit [Fintype node] in
include ha hshift in
/-- Window 1's readiness boundary is past its first slot. -/
theorem genesis_boundary_pos : 1 ≤ th.genesis_boundary := by
  rw [ha.2.2.1.1, hshift.2]
  have := sch.two_le_p
  show 1 ≤ 0 + sch.p
  omega

include ha hshift in
/-- **No correct validator is ready in the idle run**: window 1's first slot
lies below its readiness boundary and is never completed, so no ACS
proposal is ever due (Algorithm 7, line 23 (`line:ready-check`)). -/
theorem idle_not_proposeGate {n : ℕ} {st : CState window time node acsstate} (hinv : IdleInv th n st)
    (i : node) (w' : window) : ¬ proposeGate th i w' st := by
  rintro ⟨w, -, hin, hrd⟩
  obtain rfl : w = win_ord.zero := (hinv.entered i w).1 hin.1
  have := hrd 0 th.genesis_boundary th.genesis_last (Or.inl ⟨rfl, rfl, rfl, rfl⟩) 0 win_ord.zero 0
    th.genesis_boundary th.genesis_last ((hinv.entered i _).2 rfl) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
    le_rfl (Nat.zero_le _) (genesis_boundary_pos sch ha hshift)
  rw [hinv.completed] at this
  exact Bool.false_ne_true this

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
include ha in
/-- No ACS decides in the idle run: every instance stays initial. -/
theorem idle_not_decideGate {n : ℕ} {st : CState window time node acsstate} (hinv : IdleInv th n st)
    (w : window) : ¬ decideGate w st := by
  rintro ⟨i, -, hd⟩
  rw [hinv.acs] at hd
  exact A.init_has_decided _ i (ha.1 w) hd

variable {st₀ : CState window time node acsstate}
  (hi : (Conductor.relationalTransitionSystem ℕ window time node acsstate).init th st₀)
  (hunb : StartsUnbounded th)

include hshift in
/-- **The idle run meets the timing model**: every row's gate stays shut,
every scheduled slot opens at its starting time, the clock is the model's,
and no correct validator ever proposes to an ACS, so the ACS premise has
nothing to say. -/
theorem idleRun_sync {msg : Type} (TA : ACSTemporal node ℕ acsstate time msg fm.byz) :
    Sync sch TA (idleRun ha hi hunb) := by
  have hδ : 0 ≤ sch.δ := by rw [show sch.δ = 0 from sch.δ_zero]
  refine ⟨⟨fun i w' _ => bff_of_never hδ fun n =>
        idle_not_proposeGate sch ha hshift (idleSt_inv ha hi n) i w',
      fun i w' _ => bff_of_never hδ fun n h =>
        idle_not_proposeGate sch ha hshift (idleSt_inv ha hi n) i w' h.2,
      fun w => bff_of_never hδ fun n => idle_not_decideGate ha (idleSt_inv ha hi n) w⟩,
    ?_, fun _ => rfl, ?_⟩
  · -- (P-open): `(i, s)` opens at index `s · B + idx i + 2`, at `s`'s starting time.
    rintro N i s hcor ⟨w, f, b, l, -, hb, -, hsl⟩
    have hinvN := idleSt_inv ha hi N
    obtain ⟨-, -, -, rfl⟩ := hinvN.winBounds hb
    by_cases hop : (idleSt th st₀ N).opened i s = true
    · exact ⟨N, le_rfl, le_max_left _ _, hop⟩
    · have := idx_lt i
      have hb : blk node = Fintype.card node + 1 := rfl
      refine ⟨s * blk node + (idx i + 2), ?_, ?_, ?_⟩
      · by_contra hlt
        exact hop ((hinvN.opened i s).2 ⟨hcor, hsl, by omega⟩)
      · show (idleSt th st₀ _).now ≤ _
        rw [(idleSt_inv ha hi _).now, nowSlot_add (by omega) (by omega)]
        exact le_max_right _ _
      · exact ((idleSt_inv ha hi _).opened i s).2 ⟨hcor, hsl, by omega⟩
  · -- The ACS premise: nobody proposes, every instance stays initial.
    rintro w ⟨n, i, s, -, hp⟩
    change A.proposed ((idleSt th st₀ n).acs_state w) i s at hp
    rw [(idleSt_inv ha hi n).acs w] at hp
    exact (A.init_proposed _ i s (ha.1 w) hp).elim

end IdleTimed

/-! ## `Admissible`, and admissibility is not vacuous -/

section Fields

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  {msg : Type}

/-- **`OrchestratorTemporal.Admissible`**, as this instance defines it: the
run is the contract's reading (`contractRun`) of a labelled timed run of
the Conductor that satisfies the claims' run premises, `Sync`
([Schedule.lean](Schedule.lean)): the rows, the punctual openings, one
clock, and the ACS meeting its module. Each is a premise by its own name,
restated nowhere. The labels are the witness of how the run was scheduled,
which a `TimedRun` does not carry. -/
def Admissible (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (r : TimedRun (CState window time node acsstate) time (orchestratorSafety th).init
      (orchestratorSafety th).trans) : Prop :=
  ∃ r' : TConductorRun th, contractRun r' = r ∧ Sync sch TA r'

variable [IsOrderedAddMonoid time] [Fintype node]

/-- **`admissible_exists`** — every initial state starts an admissible run:
the idle run (`idleRun`), in which the caller completes nothing. Two
configuration premises make it admissible. The windows' shape
(`WindowShifts`), with assumption (4), puts window 1's first slot below its
readiness boundary, so no correct validator becomes ready and no ACS is
proposed to; and the starting times are unbounded (`StartsUnbounded`), so
the clock, stepping from one starting time to the next, is too. -/
theorem admissible_exists (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) {th : Conductor.Theory ℕ window time node acsstate}
    (hshift : WindowShifts sch th) (hunb : StartsUnbounded th) :
    ∀ st, (orchestratorSafety th).init st →
      ∃ r : TimedRun (CState window time node acsstate) time (orchestratorSafety th).init
        (orchestratorSafety th).trans, Admissible sch TA th r ∧ r.at' 0 = st := by
  rintro st ⟨ha, hi⟩
  exact ⟨contractRun (idleRun ha hi hunb), ⟨_, rfl, idleRun_sync sch ha hshift hi hunb TA⟩, rfl⟩

end Fields

/-! ## `Conductor ⊨ OrchestratorTemporal`, `OrchestratorWithTotality`, and the full `Orchestrator` -/

section Instance

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  [Fintype node] [DecidablePred fm.byz] {msg : Type}

/-- **`Conductor ⊨ OrchestratorTemporal`**, for an arbitrary ACS meeting its
contract (`TA`). Every field is proven, none is weakened:

* `Admissible` is `Conductor.Admissible`, the claims' run premises by name;
* `admissible_exists` from the idle run;
* `clock_agrees` from `ClockAgrees`;
* `caller_d_tot` and `caller_ℓ` are Chorus's `d_tot` and `ℓ_chorus`;
* `totality` from `Conductor.totality` (Lemma 15
  (`lemma:conductor-totality`));
* `bound` is `2W − p` and `boundedness` is `Conductor.boundedness`
  (Lemma 14 (`lem:boundedness`));
* `recovery_time` is `2Wτ` and `recovery` is `Conductor.recovery`
  (Lemma 16 (`lemma:conductor-recovery`)).

Proven from the claims' configuration premises, each by its name: τ-spaced
starting times (`hstart`), the windows' shape (`hshift`), unbounded
starting times (`hunb`, F28), a successor for every window (`hwin`, F30),
the ACS's constants the system's (`hΔ`, `hℓ`) and at most its fault bound
Byzantine (`hfault`). -/
@[implicit_reducible]
noncomputable def conductorTemporal (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) (hunb : StartsUnbounded th)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    OrchestratorTemporal node ℕ (CState window time node acsstate) time fm.byz
      (S := orchestratorSafety th) :=
  OrchestratorTemporal.mk (S := orchestratorSafety th)
    (Admissible := Admissible sch TA th)
    (admissible_exists := admissible_exists sch TA hshift hunb)
    (clock_agrees := fun r hadm n => by
      obtain ⟨r', rfl, -, -, hclock, -⟩ := hadm
      exact hclock n)
    (caller_d_tot := sch.d_tot)
    (caller_ℓ := sch.ℓchorus)
    (totality := fun r hadm hcall i j s hi hj => by
      obtain ⟨r', rfl, hsync⟩ := hadm
      rintro ⟨n, hn⟩
      obtain ⟨-, -, -, -, m, -, hm⟩ :=
        Conductor.totality sch TA th hunb hΔ r' hsync hcall s n i hi hn j hj
      exact ⟨m, hm⟩)
    (bound := sch.bound)
    (boundedness := fun st hr i s hi hop hnc =>
      Conductor.boundedness (A := A) sch th hshift st hr i s hi hop hnc)
    (recovery_time := sch.recoveryTime)
    (recovery := fun r hadm hcall hterm s hs i hi => by
      obtain ⟨r', rfl, hsync⟩ := hadm
      exact Conductor.recovery sch TA th hstart hshift hunb hwin hΔ hℓ hfault r' hsync hcall hterm
        s hs i hi)

/-- **`Conductor ⊨ OrchestratorWithTotality`**: the `d_tot` form of
Totality that Lemma 15 (`lemma:conductor-totality`) proves "more
specifically", over the same `Admissible`. `d_tot` is Chorus's, the
paper's `Δ` at `δ = 0` (`conductorWithTotality_d_tot_paper`), and `totality`
is `Conductor.totality`. -/
@[implicit_reducible]
noncomputable def conductorWithTotality (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) (hunb : StartsUnbounded th)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    OrchestratorWithTotality node ℕ (CState window time node acsstate) time fm.byz
      (S := orchestratorSafety th)
      (T := conductorTemporal sch TA th hstart hshift hunb hwin hΔ hℓ hfault) :=
  OrchestratorWithTotality.mk (S := orchestratorSafety th)
    (T := conductorTemporal sch TA th hstart hshift hunb hwin hΔ hℓ hfault)
    (d_tot := sch.d_tot)
    (totality := fun r hadm hcall s => by
      obtain ⟨r', rfl, hsync⟩ := hadm
      exact Conductor.totality sch TA th hunb hΔ r' hsync hcall s)

/-- **`Conductor ⊨ Orchestrator`**: the full contract, the proven fragment
and the proven temporal level joined by `orchestrator_of_temporal`. -/
@[implicit_reducible]
noncomputable def conductorFull (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) (hunb : StartsUnbounded th)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    Orchestrator node ℕ (CState window time node acsstate) time fm.byz :=
  orchestrator_of_temporal (conductorTemporal sch TA th hstart hshift hunb hwin hΔ hℓ hfault)

/-- The join hands back exactly the proven fragment. -/
theorem conductorFull_toSafety (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) (hunb : StartsUnbounded th)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    (conductorFull sch TA th hstart hshift hunb hwin hΔ hℓ hfault).toOrchestratorSafety =
      orchestratorSafety th := rfl

/-- **`𝓑`, pinned**: the boundedness bound is the paper's `2W − p`
(Theorem 2 (`thm:conductor-correctness`)). -/
theorem conductorTemporal_bound (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) (hunb : StartsUnbounded th)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    (conductorTemporal sch TA th hstart hshift hunb hwin hΔ hℓ hfault).bound = 2 * sch.W - sch.p :=
  rfl

/-- **`𝓡`, pinned**: the recovery time is the paper's `2Wτ` (Theorem 2
(`thm:conductor-correctness`)). -/
theorem conductorTemporal_recovery_time (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) (hunb : StartsUnbounded th)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    (conductorTemporal sch TA th hstart hshift hunb hwin hΔ hℓ hfault).recovery_time =
      (2 * sch.W) • sch.τ :=
  rfl

/-- **The caller's constants, pinned**: (R-tot) and (R-term) are assumed at
Chorus's `d_tot` and `ℓ_chorus`, the constants the Chorus instance proves
(`Φ_oc_eq_chorus`). -/
theorem conductorTemporal_caller (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) (hunb : StartsUnbounded th)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    (conductorTemporal sch TA th hstart hshift hunb hwin hΔ hℓ hfault).caller_d_tot = sch.d_tot ∧
      (conductorTemporal sch TA th hstart hshift hunb hwin hΔ hℓ hfault).caller_ℓ = sch.ℓchorus :=
  ⟨rfl, rfl⟩

/-- **`d_tot`, pinned**: the orchestrator's totality latency is Chorus's
`d_tot`. -/
theorem conductorWithTotality_d_tot (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) (hunb : StartsUnbounded th)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    (conductorWithTotality sch TA th hstart hshift hunb hwin hΔ hℓ hfault).d_tot = sch.d_tot :=
  rfl

/-- At the schedule's `δ = 0`, the paper's instantaneous local computation,
`d_tot` is the paper's `Δ` (Lemma 15 (`lemma:conductor-totality`)). -/
theorem conductorWithTotality_d_tot_paper (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ window time node acsstate)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) (hunb : StartsUnbounded th)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    (conductorWithTotality sch TA th hstart hshift hunb hwin hΔ hℓ hfault).d_tot = sch.Δ := by
  rw [conductorWithTotality_d_tot]
  exact sch.d_tot_paper

end Instance

/-! ## Two configuration premises at the system's types

`WindowsUnbounded` holds at `window := ℕ`, the paper's window numbers.
`StartsUnbounded` holds wherever slot 1 starts at or after `0` and the
time is Archimedean: the τ-spaced starting times then pass every time.
Both stay premises of the generic claims. -/

section Configuration

/-- **Every window has a successor** at the paper's window numbers,
`window := ℕ` (F30). -/
theorem windowsUnbounded_nat : WindowsUnbounded ℕ := fun w => ⟨w + 1, rfl⟩

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}

omit [Inhabited window] [Inhabited node] [Inhabited acsstate] win_ord fm A [Inhabited time] in
/-- **The starting times are unbounded** at τ-spaced starting times
(`StartTimes`) over an Archimedean time, once slot 1 starts at or after `0`
(the paper's slot 1 starts at `0`, Appendix A.1
(`subsection:mcp-preliminaries`)): every time is below some `n • τ`, hence
below slot `n`'s starting time `start₀ + n • τ` (F28). The condition on
`start₀` is needed: with a negative `start₀` in a monoid without negation,
the starting times can stay bounded (F28's example). -/
theorem startsUnbounded_of_startTimes [Archimedean time] {sch : ConductorSchedule view time vfin}
    {th : Conductor.Theory ℕ window time node acsstate} (hstart : StartTimes sch th)
    (h0 : 0 ≤ sch.start₀) : StartsUnbounded th := by
  intro t
  obtain ⟨n, hn⟩ := Archimedean.arch t sch.τ_pos
  refine ⟨n, ?_⟩
  rw [hstart]
  exact le_trans hn (le_add_of_nonneg_left h0)

end Configuration

section Nat

variable {node acsstate : Type} [Inhabited node] [Inhabited acsstate]
  [fm : FaultModel node] [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  [Archimedean time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  [Fintype node] [DecidablePred fm.byz] {msg : Type}

/-- **`Conductor ⊨ Orchestrator` at the paper's window numbers**: the full
contract at `window := ℕ` over an Archimedean time, with `WindowsUnbounded`
and `StartsUnbounded` discharged (`windowsUnbounded_nat`,
`startsUnbounded_of_startTimes`). What stays with the caller: τ-spaced
starting times with slot 1 at or after `0`, the windows' shape, and the
ACS's constants and fault bound. -/
@[implicit_reducible]
noncomputable def conductorFullNat (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (th : Conductor.Theory ℕ ℕ time node acsstate)
    (hstart : StartTimes sch th) (h0 : 0 ≤ sch.start₀) (hshift : WindowShifts sch th)
    (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter fm.byz).card ≤ TA.fault_bound) :
    Orchestrator node ℕ (CState ℕ time node acsstate) time fm.byz :=
  conductorFull sch TA th hstart hshift (startsUnbounded_of_startTimes hstart h0)
    windowsUnbounded_nat hΔ hℓ hfault

end Nat

end Conductor

/-! ## The pinned trust base

The standard Lean trio and nothing else: no `sorryAx`. -/

/--
info: 'Conductor.idleRun_sync' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.idleRun_sync

/--
info: 'Conductor.admissible_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.admissible_exists

/--
info: 'Conductor.conductorTemporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorTemporal

/--
info: 'Conductor.conductorWithTotality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorWithTotality

/--
info: 'Conductor.conductorFull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorFull

/--
info: 'Conductor.conductorFull_toSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorFull_toSafety

/--
info: 'Conductor.conductorTemporal_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorTemporal_bound

/--
info: 'Conductor.conductorTemporal_recovery_time' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorTemporal_recovery_time

/--
info: 'Conductor.conductorTemporal_caller' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorTemporal_caller

/--
info: 'Conductor.conductorWithTotality_d_tot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorWithTotality_d_tot

/--
info: 'Conductor.conductorWithTotality_d_tot_paper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorWithTotality_d_tot_paper

/--
info: 'Conductor.windowsUnbounded_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.windowsUnbounded_nat

/-- info: 'Conductor.startsUnbounded_of_startTimes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Conductor.startsUnbounded_of_startTimes

/--
info: 'Conductor.conductorFullNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.conductorFullNat
