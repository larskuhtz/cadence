import Cadence.Composed.Witness.Slot
import Cadence.Composed.Witness.Periodic
import Cadence.Composed.Censorship
import Cadence.Conductor.IdealAcs

/-! # Composed.Witness.Run — the composed witness's instance, schedule and run

[ConductorBounds.md](../../../docs/ConductorBounds.md) §8.2, stage K8. One
model of the whole composed system: the glue ([Cadence.lean](../../Cadence.lean))
with the Conductor as its orchestrator and Chorus (with the `Mvba` model as
its MVBA) as every slot's consensus, and the ideal ACS
([Conductor/IdealAcs.lean](../../Conductor/IdealAcs.lean)) in every window.

## The instance and the schedule

* `Fin 4`, validator 3 Byzantine and silent, validator 0 the one proposer of
  every slot; Chorus's and the MVBA's configuration are the Chorus
  witness's ([Slot.lean](Slot.lean)).
* `Δ = τ = 1`, `δ = 0`, the MVBA schedule of the Chorus witness (its
  `ℓ_MVBA = 24`), `ℓ_ACS = 2`, `p = 4`, `W = p + Φ_oc + ℓ_ACS = 36` with
  `Φ_oc = 6Δ + ℓ_MVBA = 30` (`sch`). Slot `s` starts at time `s`, its
  deadline is `s + 1`.
* Windows are numbers; window `w` is slots `36w … 36w + 35`, its readiness
  boundary `36w + 4`.

## The run

Time advances by one at the end of every block of `L = 56` steps (a
**plateau**); plateau `t` is clock `t`. Its positions (`glbl`, `clbl`):

* `0` — slot `t − 3`'s MVBA-arm marker; `1` — slot `t − 2`'s fallback-arm
  marker;
* `2–23` — slot `t − 1`'s fast path at its deadline `t`: the deadline
  marker, the three correct validators' votes, FastQCs, commit signatures,
  fast commit votes, commit certificates, committed entries and
  finalizations; `24–26` — each correct validator's finalize handler:
  `complete(t − 1)` to the Conductor and `abandon()` to the slot, in one
  step; `27–29` — its append of slot `t − 1`'s vector;
* `30–40`, at `t = 36k + 4` only (window `k`'s readiness boundary) — each
  correct validator's proposal of slot `36(k + 1)` to window `k + 1`'s ACS,
  the ACS fixing its decided set and each correct validator's decision, the
  recording of the decided interval, and each correct validator's entry
  into window `k + 1`;
* `41–43` — each correct validator's opening of slot `t`; `44–46` — its
  participation in slot `t`; `47` — validator 0's proposal; `48–51` — its
  chunk reaching each of the four validators; `52–54` — each correct
  validator recording it;
* `55` — the clock's `tick` to `t + 1`.

A position whose slot or window does not exist is the Conductor's `tick`
in place, a stutter. Every window repeats the first, shifted by `36` in
time and in slot number; every slot repeats the previous one, shifted by
one. -/

namespace Composed.Witness

open Cadence Conductor Chorus
open scoped Cadence.Timed

attribute [local instance] Chorus.Witness.nsetC Chorus.Witness.cntC natViewOrder

/-! ## The instance -/

/-- The Byzantine validator, the Chorus witness's. -/
abbrev isByz : Fin 4 → Prop := Chorus.Witness.isByz

/-- **The system's fault model**: validator 3 Byzantine. -/
abbrev FM : FaultModel (Fin 4) := fmF 4 1 rfl isByz Chorus.Witness.hbyz

theorem byz_iff (i : Fin 4) : FM.byz i ↔ i.val = 3 := by
  show (byzNodeSetFin 4 1 rfl isByz Chorus.Witness.hbyz).is_byz i = true ↔ _
  dsimp +instances only [byzNodeSetFin]
  simp [isByz, Chorus.Witness.isByz]

theorem correct_iff (i : Fin 4) : ¬ FM.byz i ↔ i.val < 3 := by
  rw [byz_iff]; omega

/-- An ideal ACS instance's state. -/
abbrev ACSt := IdealAcs.State (Fin 4) ℕ

/-- The ideal ACS's initial state. -/
def acs0 : ACSt := ⟨fun _ => none, none, fun _ => false, fun _ => false⟩

instance : Inhabited ACSt := ⟨acs0⟩

/-- **The ideal ACS**, at `f = 1`. -/
@[implicit_reducible]
def AS : ACSSafety (Fin 4) ℕ ACSt FM.byz := IdealAcs.acsSafety FM.byz 1

/-- Its temporal level, at `Δ = 1` and `ℓ = 2`. -/
@[implicit_reducible]
def TA : ACSTemporal (Fin 4) ℕ ACSt ℕ Unit FM.byz (S := AS) :=
  IdealAcs.acsTemporal FM.byz 1 (1 : ℕ) 2 Unit Nat.one_pos

/-- **The Conductor's configuration**: slot `s` starts at `s`, a window's
last slot is its first plus 35, its readiness boundary its first plus 4. -/
def thO : Conductor.Theory ℕ ℕ ℕ (Fin 4) ACSt where
  start_time s := s
  win_last s := s + 35
  win_boundary s := s + 4
  genesis_boundary := 4
  genesis_last := 35
  genesis_time := 0
  acs_init_state _ := acs0

/-! ## The schedule -/

/-- **The schedule**: the Chorus witness's MVBA schedule (`Δ = 1`, `δ = 0`,
`Δ_sync = 1`), slot `s`'s deadline `s + 1`, `W = 36`, `p = 4`, `τ = 1`,
`ℓ_ACS = 2`, slot 1 at time 0. The four parameter assumptions are
arithmetic at `Φ_oc = 30`. -/
def sch : ConductorSchedule ℕ ℕ natViewOrderEnum where
  mvba := Chorus.Witness.schC.mvba
  D s := s + 1
  δ_le_Δ := Nat.zero_le _
  Δ_le_Δsync := le_rfl
  W := 36
  p := 4
  τ := 1
  ℓ := 2
  start₀ := 0
  p_lt_W := by decide
  τ_pos := Nat.one_pos
  D_eq s := by simp; rfl
  assm_one := by decide
  assm_two := by decide
  assm_three := by decide
  assm_four := by decide
  δ_zero := rfl

/-- `ℓ_MVBA` at this schedule. -/
theorem ellM : sch.mvba.ℓ natViewOrderEnum = 24 := by decide

/-- `Φ_oc = 6Δ + ℓ_MVBA = 30`, so `W = p + Φ_oc + ℓ_ACS`. -/
theorem W_eq : sch.W = sch.p + sch.Φ_oc + sch.ℓ := by decide

/-! ## The composed system -/

/-- A slot's proposal vector: validator 0's root, nothing for the others. -/
def vec (x : ℕ) : ℕ × (Fin 4 → Option Unit) := (x, fun j => if j.val = 0 then some () else none)

/-- The slot-consensus fragment at the system's configuration. -/
noncomputable abbrev SCI := SC 4 1 rfl isByz Chorus.Witness.hbyz thS thM

/-- The orchestrator fragment at the system's configuration. -/
noncomputable abbrev OSI := OS (acsstate := ACSt) (A := AS) 4 1 rfl isByz Chorus.Witness.hbyz thO

/-- **The composed system.** -/
noncomputable abbrev SYS := sysRTS (merkle_root := Unit) (view := ℕ) (Phase := Ph) (PathChoice := PC)
  (window := ℕ) (acsstate := ACSt) (A := AS) 4 1 rfl isByz Chorus.Witness.hbyz (time := ℕ) thO thS thM

/-- A Conductor state of the system. -/
abbrev CSt := OrchSt ℕ ℕ ACSt 4
/-- A Conductor label of the system. -/
abbrev CLb := CLabel ℕ ℕ (Fin 4) ACSt
/-- A state of the composed system. -/
abbrev GSt := GState ℕ (Fin 4) (ℕ × (Fin 4 → Option Unit)) Unit CSt (SlotSt Unit ℕ Ph PC 4) ℕ
/-- A label of the composed system. -/
abbrev GLb := GLabel ℕ (Fin 4) (ℕ × (Fin 4 → Option Unit)) Unit CSt (SlotSt Unit ℕ Ph PC 4) ℕ

/-! ## The states

Every record is set at one index, and present at index `n` exactly when
that index is below `n`. -/

/-- The plateau index of window `w ≥ 1`'s events, times `L = 56`: its
predecessor's readiness boundary `36(w − 1) + 4`. -/
def dB (w : ℕ) : ℕ := (w - 1) * 2016 + 224

/-- Window `w`'s ideal ACS at index `n`: the correct validators propose
`36w` at `dB w + 30 + i`, the decided set (their three pairs) is fixed at
`dB w + 33`, each decides at `dB w + 34 + i` and abandons at `dB w + 38 + i`. -/
def acsSt (w n : ℕ) : ACSt where
  prop i := if 1 ≤ w ∧ i.val < 3 ∧ dB w + 30 + i.val < n then some (w * 36) else none
  core := if 1 ≤ w ∧ dB w + 33 < n then some (fun q => if q.val < 3 then some (w * 36) else none) else none
  out i := decide (1 ≤ w ∧ i.val < 3 ∧ dB w + 34 + i.val < n)
  ab i := decide (1 ≤ w ∧ i.val < 3 ∧ dB w + 38 + i.val < n)

/-- **The Conductor's state at index `n`.** The clock reads the plateau;
window `w ≥ 1`'s interval is recorded at `dB w + 37`, entered by `i` at
`dB w + 38 + i`; slot `s` is opened by `i` at `56s + 41 + i` and completed
at `56s + 80 + i` (position 24 + `i` of the next plateau). -/
def cond (n : ℕ) : CSt where
  now := n / 56
  acs_state w := acsSt w n
  acs_decided w f b l := decide (1 ≤ w ∧ dB w + 37 < n ∧ f = w * 36 ∧ b = w * 36 + 4 ∧ l = w * 36 + 35)
  entered i w := decide (w = 0 ∨ (1 ≤ w ∧ i.val < 3 ∧ dB w + 38 + i.val < n))
  opened i s := decide (i.val < 3 ∧ s * 56 + 41 + i.val < n)
  opened_win i s w := decide (i.val < 3 ∧ s * 56 + 41 + i.val < n ∧ w = s / 36)
  completed i s := decide (i.val < 3 ∧ s * 56 + 80 + i.val < n)

/-- **Slot `x`'s local index at composed index `n`**: the number of its
steps before `n`. They are positions 44–54 of plateau `x`, 2–26 of plateau
`x + 1`, 1 of `x + 2` and 0 of `x + 3`. -/
def loc (x n : ℕ) : ℕ :=
  min (n - (x * 56 + 44)) 11 + min (n - (x * 56 + 58)) 25 + min (n - (x * 56 + 113)) 1 +
    min (n - (x * 56 + 168)) 1

/-- **The composed state at index `n`.** Slot `x`'s instance is at its
local index; validator `i`'s finalize handler delivers slot `x`'s vector at
`56x + 80 + i`, its append at `56x + 83 + i`; nothing is ever skipped. -/
def gs (n : ℕ) : GSt where
  os := cond n
  sc_state x := (x, cst (loc x n))
  skipped _ _ := false
  resolved i x := decide (i.val < 3 ∧ x * 56 + 83 + i.val < n)
  delivered i x v := decide (i.val < 3 ∧ x * 56 + 80 + i.val < n ∧ v = vec x)
  appended i x v := decide (i.val < 3 ∧ x * 56 + 83 + i.val < n ∧ v = vec x)

/-- **The configuration of the glue**: validator 0 proposes in every slot;
the orchestrator and every slot start at index 0's states. -/
def thG : GTheory Unit ℕ Ph PC ℕ ℕ ACSt 4 := ⟨fun j _ => decide (j.val = 0), cond 0, fun x => (x, cst 0)⟩

/-! ## The labels -/

/-- The validator a position acts for. -/
def nd (k : ℕ) : Fin 4 := ⟨k % 4, Nat.mod_lt _ (by decide)⟩

/-- **The Conductor's label at index `n`** (plateau `t`, position `j`): the
`complete` input at the finalize handlers, the window events, the openings,
and the end-of-plateau `tick`; a `tick` in place everywhere else. -/
def clbl (n : ℕ) : CLb :=
  let t := n / 56
  let j := n % 56
  let w := t / 36
  if 24 ≤ j ∧ j ≤ 26 ∧ 1 ≤ t then .complete_slot (nd (j - 24)) (t - 1)
  else if t % 36 = 4 ∧ 30 ≤ j ∧ j ≤ 32 then
    .acs_propose (nd (j - 30)) w (w + 1) ((w + 1) * 36) (acsSt (w + 1) (n + 1))
  else if t % 36 = 4 ∧ 33 ≤ j ∧ j ≤ 36 then .acs_step (w + 1) (acsSt (w + 1) (n + 1))
  else if t % 36 = 4 ∧ j = 37 then
    .acs_decide w (w + 1) ((w + 1) * 36) (w * 36) (w * 36 + 4) (w * 36 + 35) 0 ((w + 1) * 36) 0
      ((w + 1) * 36)
  else if t % 36 = 4 ∧ 38 ≤ j ∧ j ≤ 40 then
    .enter_window (nd (j - 38)) w (w + 1) ((w + 1) * 36) ((w + 1) * 36 + 4) ((w + 1) * 36 + 35)
      (acsSt (w + 1) (n + 1))
  else if 41 ≤ j ∧ j ≤ 43 then .open_slot (nd (j - 41)) t w (w * 36) (w * 36 + 4) (w * 36 + 35)
  else if j = 55 then .tick (t + 1)
  else .tick t

/-- **The composed label at index `n`.** -/
def glbl (n : ℕ) : GLb :=
  let t := n / 56
  let j := n % 56
  if j = 0 ∧ 3 ≤ t then .sc_step (t - 3) (t - 3, cst 38)
  else if j = 1 ∧ 2 ≤ t then .sc_step (t - 2) (t - 2, cst 37)
  else if 2 ≤ j ∧ j ≤ 23 ∧ 1 ≤ t then .sc_step (t - 1) (t - 1, cst (j + 10))
  else if 24 ≤ j ∧ j ≤ 26 ∧ 1 ≤ t then
    .on_finalize (nd (j - 24)) (t - 1) (vec (t - 1)) (cond (n + 1)) (t - 1, cst (j + 10))
  else if 27 ≤ j ∧ j ≤ 29 ∧ 1 ≤ t then .append (nd (j - 27)) (t - 1) (vec (t - 1))
  else if 44 ≤ j ∧ j ≤ 46 then .on_open (nd (j - 44)) t (t, cst (j - 43))
  else if j = 47 then .on_propose 0 t () (t, cst 4)
  else if 48 ≤ j ∧ j ≤ 54 then .sc_step t (t, cst (j - 43))
  else .orch_step (cond (n + 1))

end Composed.Witness
