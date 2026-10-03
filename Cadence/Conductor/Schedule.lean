import Cadence.PartProjection
import Cadence.Composition
import Cadence.Chorus.Temporal

/-! # Conductor.Schedule — the timing model, and the three timed claims stated

[ConductorBounds.md](../../docs/ConductorBounds.md) §9, stage K3. This file
states the **timing model** under which the Conductor (Algorithm 7
(`algorithm:conductor`)) is to satisfy the orchestrator contract's timed
fields — every premise a named `Prop` on a labelled timed run of the
Conductor model — and the **three targets** as `Prop`-valued definitions,
apart from any proof: Totality in its `d_tot` form (Lemma 15
(`lemma:conductor-totality`)), `(2W − p)`-Boundedness (Lemma 14
(`lem:boundedness`)) and `(2Wτ)`-Recovery (Lemma 16
(`lemma:conductor-recovery`)). [Chorus/Schedule.lean](../Chorus/Schedule.lean)
is the template, kept for its reason: the premises are fixed, type-checked
and citable on their own, so none can become a hypothesis because a proof
needs it.

`grep -nE '^(def|structure|abbrev|noncomputable def) ' Cadence/Conductor/Schedule.lean`
prints the whole list.

## What is assumed of the instance

* **Slots are numbers** (`natSlotOrder`): `slot := ℕ`, where `s : ℕ` is the
  paper's slot `s + 1`, so the model's least slot is the paper's slot 1.
* **The schedule** (`ConductorSchedule`): Chorus's family schedule (one
  `Δ`, one `δ`, the MVBA's constants, a deadline per slot), extended by the
  window size `W`, the readiness threshold `p`, the slot spacing `τ`, the
  ACS's latency `ℓ`, slot 1's starting time, and as fields the paper's four
  parameter assumptions (Algorithm 7, lines 7–10
  (`line:assumption-one`–`line:assumption-four`)) and `δ = 0` (decided,
  [ConductorBounds.md](../../docs/ConductorBounds.md) §5). `Φ_oc` and
  `d_tot` are not new constants: they are the Chorus instance's own
  `Lchorus …` and `Ltot …` (`Φ_oc_eq_chorus`).
* **The configuration** (`StartTimes`, `WindowShifts`, `StartsUnbounded`):
  the Conductor's theory has the τ-spaced starting times of Appendix A.1
  (`subsection:mcp-preliminaries`), the shift functions of K2 are
  `+ (W − 1)` and `+ p`, and some slot has always not yet started (F28).
* **Time** is linearly ordered with an ordered addition
  (`IsOrderedAddMonoid`, F27), the time theory of
  [ConductorBounds.md](../../docs/ConductorBounds.md) §6.2; the timed claims
  take it as an instance argument.
* **The ACS** is an arbitrary instance of its contract, `ACSSafety` and
  `ACSTemporal` ([Interfaces.lean](../Interfaces.lean)), an **assumed
  module** (P17): the target leaves it unspecified. Its constants are the
  system's (`TA.Δ = Δ`, `TA.ℓ = ℓ`, F23), at most its `fault_bound`
  validators are Byzantine. That it accepts its two inputs is the
  contract's (`ACSTemporal.propose_enabled`, `abandon_enabled`, F26).
  [IdealAcs.lean](IdealAcs.lean) meets all of it.

## What is assumed of a run

* **The rows** (`TimedRows`): the Conductor's three honest handlers fire
  `δ` after their gates open — the ACS proposal (Algorithm 7, line 37
  (`line:ready`)), window entry (Algorithm 7, line 44 (`line:acs-decide`))
  and the recording of the decided interval. All are local: the Conductor's
  only cross-validator channel is the ACS, whose timing enters through its
  own `Admissible`.
* **(P-open)** (`OpenPunctual`): the opening timer is punctual — a slot
  scheduled at clock `c` opens by `max(c, start)`, Algorithm 7, line 27
  (`line:conductor-wait-for-open`).
* **One clock** (`ClockAgrees`): the run's clock is the Conductor's `now`,
  as `OrchestratorTemporal.clock_agrees` asks.
* **The ACS meets its module** (`AcsAdmissible`): once a correct validator
  has proposed to window `w`'s ACS, that ACS's part of the run — the stutter
  lift of [PartProjection.lean](../PartProjection.lean) (F24) — is
  admissible for its contract.

The caller's two conditions, (R-tot) and (R-term), are the contract's own
(`OrchestratorSafety.CallerTotality`, `CallerTermination`), read on the run
through `contractRun`.

## The gate checklist

A row's gate is the local condition its rule waits for, and it opens `δ`
before the rule is due, so a gate that mentioned protocol progress would
let the clause assume it. Every gate mentions only the acting validator's
own local state (its window, the windows' intervals it holds, its
completions) and the output of its own ACS instance that its rule fires
upon (F22). The one exception is the recording of the decided interval,
`acs_decide`, a global step of the model that stands for every validator's
median computation: its gate is that some correct validator's ACS has
output a decision. Everything else a rule's guard needs — the interval
having been recorded, the ACS accepting the input — is protocol state the
proofs establish, or the ACS contract's input-enabledness.

## What this file does not do

Prove anything about the protocol. Its theorems are about its own
definitions: the constants at `δ = 0` are the paper's (`d_tot_paper`,
`Φ_oc_paper`), they are the Chorus instance's (`Φ_oc_eq_chorus`), and the
per-window ACS is a component of the Conductor (`acsComponent`). The proofs
are stages K4 (Totality, and Boundedness in
[Boundedness.lean](Boundedness.lean)) and K5 (Recovery) of
[ConductorBounds.md](../../docs/ConductorBounds.md) §9; the glue's rows,
which time the caller's side, are K7's. -/

namespace Conductor

open Cadence
open scoped Cadence.Timed

/-! ## Slots are numbers -/

/-- **Slots are numbers**, `ℕ` with its order: `s : ℕ` is the paper's slot
`s + 1` (Appendix A.1 (`subsection:mcp-preliminaries`) numbers slots from
1), so the model's least slot is the paper's slot 1 and the shift by `k`
slots is `+ k`. The same order as the view counter's (`natViewOrder`). -/
@[implicit_reducible]
def natSlotOrder : TotalOrderWithMinimum ℕ := natViewOrder

attribute [local instance] natSlotOrder

/-! ## The schedule -/

/-- **The Conductor schedule** — Chorus's family schedule, the window
parameters, and the paper's four parameter assumptions
([Premises.md](../../docs/Premises.md) §9.2).

Chorus's family schedule gives one network bound `Δ`, one local bound `δ`,
the MVBA's constants and each slot's deadline `D`; the Conductor's starting
time of a slot is its deadline minus `Δ` (Algorithm 7, line 27
(`line:conductor-wait-for-open`)), so `D_eq` ties the two. `vfin` is the
view order's enumeration, through which the MVBA's latency `ℓ_MVBA` (hence
`Φ_oc`) is computed, as in `Chorus.chorusWithTotality`. -/
structure ConductorSchedule (view time : Type) [vord : TotalOrderWithMinimum view]
    (vfin : ViewOrderEnum view vord) [LinearOrder time] [AddCommMonoid time]
    extends Chorus.FamilySchedule ℕ view time where
  /-- The window size `W`, a parameter of Algorithm 7
  (`algorithm:conductor`). -/
  W : ℕ
  /-- The readiness threshold `p`, a parameter of Algorithm 7
  (`algorithm:conductor`). -/
  p : ℕ
  /-- The spacing `τ` between consecutive slots' deadlines (Appendix A.1
  (`subsection:mcp-preliminaries`)). -/
  τ : time
  /-- The ACS's termination latency `ℓ`, a parameter of Algorithm 7
  (`algorithm:conductor`). -/
  ℓ : time
  /-- Slot 1's starting time, the paper's time `0` (Appendix A.1
  (`subsection:mcp-preliminaries`): "the starting time of the first slot is
  0"). -/
  start₀ : time
  /-- **The readiness threshold is below the window size**: `p ∈ {0, …, W − 1}`
  (Algorithm 7 (`algorithm:conductor`), its parameters). -/
  p_lt_W : p < W
  /-- **Consecutive deadlines are `τ > 0` apart** (Appendix A.1
  (`subsection:mcp-preliminaries`)). -/
  τ_pos : 0 < τ
  /-- **Chorus's deadline is the Conductor's starting time plus `Δ`**: slot
  `s` starts at `start₀ + s • τ`, and its deadline, the `D` Chorus's
  phases are timed from, is `Δ` later (F23, one `Δ`). -/
  D_eq : ∀ s : ℕ, D s = start₀ + s • τ + mvba.Δ
  /-- **Assumption (1)**, Algorithm 7, line 7 (`line:assumption-one`):
  `(p − 1)τ + Φ_oc + ℓ ≤ Wτ`, with `Φ_oc = ℓ_chorus + d_tot` the Chorus
  instance's (`Φ_oc`). -/
  assm_one : (p - 1) • τ + (Chorus.Lchorus mvba.Δ mvba.δ (mvba.ℓ vfin) +
    Chorus.Ltot mvba.Δ mvba.δ mvba.Δ) + ℓ ≤ W • τ
  /-- **Assumption (2)**, Algorithm 7, line 8 (`line:assumption-two`):
  `(p − 1)τ + Φ_oc ≤ (W − 1)τ`. -/
  assm_two : (p - 1) • τ + (Chorus.Lchorus mvba.Δ mvba.δ (mvba.ℓ vfin) +
    Chorus.Ltot mvba.Δ mvba.δ mvba.Δ) ≤ (W - 1) • τ
  /-- **Assumption (3)**, Algorithm 7, line 9 (`line:assumption-three`):
  `Δ < ℓ`. -/
  assm_three : mvba.Δ < ℓ
  /-- **Assumption (4)**, Algorithm 7, line 10 (`line:assumption-four`):
  `d_tot + ℓ ≤ (p − 1)τ`, with `d_tot` the Chorus instance's (`d_tot`). -/
  assm_four : Chorus.Ltot mvba.Δ mvba.δ mvba.Δ + ℓ ≤ (p - 1) • τ
  /-- **Local steps are instantaneous**, `δ = 0`: the paper's model, in
  which "validators' clocks are synchronized, so they share one global
  timeline" and local computation takes no time (decided,
  [ConductorBounds.md](../../docs/ConductorBounds.md) §5). The Conductor's
  window induction closes only here: at `δ > 0` its tolerance grows by a
  multiple of `δ` per window (F3). Chorus's and the MVBA's own claims stay
  general in `δ`. -/
  δ_zero : mvba.δ = 0

namespace ConductorSchedule

variable {view time : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  [LinearOrder time] [AddCommMonoid time]

/-- The network bound, the MVBA's. -/
abbrev Δ (sch : ConductorSchedule view time vfin) : time := sch.mvba.Δ

/-- The local-step bound, the MVBA's. -/
abbrev δ (sch : ConductorSchedule view time vfin) : time := sch.mvba.δ

/-- Chorus's termination latency `ℓ_chorus`, the Chorus instance's
(`Chorus.chorusWithTotality`'s `ℓ`). -/
def ℓchorus (sch : ConductorSchedule view time vfin) : time :=
  Chorus.Lchorus sch.Δ sch.δ (sch.mvba.ℓ vfin)

/-- Chorus's totality latency `d_tot`, the Chorus instance's
(`Chorus.chorusWithTotality`'s `d_tot`), which is also the Conductor's
(Lemma 15 (`lemma:conductor-totality`)). -/
def d_tot (sch : ConductorSchedule view time vfin) : time :=
  Chorus.Ltot sch.Δ sch.δ sch.Δ

/-- The open-to-complete delay `Φ_oc = ℓ_chorus + d_tot` (a parameter of
Algorithm 7 (`algorithm:conductor`); Proposition 14
(`prop:conductor-open-to-complete`)). -/
def Φ_oc (sch : ConductorSchedule view time vfin) : time :=
  sch.ℓchorus + sch.d_tot

/-- Slot `s`'s starting time, `s.deadline − Δ`: `start₀ + s • τ`. -/
def startTime (sch : ConductorSchedule view time vfin) (s : ℕ) : time :=
  sch.start₀ + s • sch.τ

/-- The recovery time `𝓡 = 2Wτ` (Theorem 2 (`thm:conductor-correctness`)). -/
def recoveryTime (sch : ConductorSchedule view time vfin) : time :=
  (2 * sch.W) • sch.τ

/-- The boundedness bound `𝓑 = 2W − p` (Theorem 2
(`thm:conductor-correctness`)). -/
def bound (sch : ConductorSchedule view time vfin) : ℕ :=
  2 * sch.W - sch.p

/-- Assumption (1), in the paper's letters. -/
theorem assm_one_Φ (sch : ConductorSchedule view time vfin) :
    (sch.p - 1) • sch.τ + sch.Φ_oc + sch.ℓ ≤ sch.W • sch.τ :=
  sch.assm_one

/-- Assumption (2), in the paper's letters. -/
theorem assm_two_Φ (sch : ConductorSchedule view time vfin) :
    (sch.p - 1) • sch.τ + sch.Φ_oc ≤ (sch.W - 1) • sch.τ :=
  sch.assm_two

/-- Assumption (4), in the paper's letters. -/
theorem assm_four_d (sch : ConductorSchedule view time vfin) :
    sch.d_tot + sch.ℓ ≤ (sch.p - 1) • sch.τ :=
  sch.assm_four

/-- At `δ = 0`, `d_tot` is the paper's `Δ` (Proposition 4
(`prop:chorus-totality`)). -/
theorem d_tot_paper (sch : ConductorSchedule view time vfin) : sch.d_tot = sch.Δ := by
  rw [d_tot, show sch.δ = 0 from sch.δ_zero]
  exact Chorus.Ltot_paper _

/-- At `δ = 0`, `ℓ_chorus` is the paper's `5Δ + ℓ_MVBA` (Lemma 11
(`lemma:chorus-termination`)). -/
theorem ℓchorus_paper (sch : ConductorSchedule view time vfin) :
    sch.ℓchorus = 5 • sch.Δ + sch.mvba.ℓ vfin := by
  rw [ℓchorus, show sch.δ = 0 from sch.δ_zero]
  exact Chorus.Lchorus_paper _ _

/-- At `δ = 0`, `Φ_oc = ℓ_chorus + d_tot` is the paper's `6Δ + ℓ_MVBA`. -/
theorem Φ_oc_paper (sch : ConductorSchedule view time vfin) :
    sch.Φ_oc = 6 • sch.Δ + sch.mvba.ℓ vfin := by
  rw [Φ_oc, ℓchorus_paper, d_tot_paper, show (6 : ℕ) = 5 + 1 from rfl, add_nsmul, one_nsmul]
  abel

end ConductorSchedule

/-! ## The configuration -/

section Configuration

variable {view time : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  [LinearOrder time] [AddCommMonoid time]
  {window node acsstate : Type}

/-- **The slots' starting times are τ-spaced from slot 1's**: the Conductor's
`start_time s` is `start₀ + s • τ` (Appendix A.1
(`subsection:mcp-preliminaries`)). With the model's `[genesis_window]` and
`ClockAgrees`, the run starts at slot 1's starting time, the paper's time
`0`. -/
def StartTimes (sch : ConductorSchedule view time vfin)
    (th : Conductor.Theory ℕ window time node acsstate) : Prop :=
  ∀ s, th.start_time s = sch.startTime s

/-- **A window is the `W` slots from its first, with its readiness boundary
at the `(p + 1)`-th**: the model's shift functions are `+ (W − 1)` and `+ p`
(Algorithm 7, line 52 (`line:last-update`); Algorithm 7, line 23
(`line:ready-check`); [ConductorBounds.md](../../docs/ConductorBounds.md)
F21, F25). -/
def WindowShifts (sch : ConductorSchedule view time vfin)
    (th : Conductor.Theory ℕ window time node acsstate) : Prop :=
  (∀ s, th.win_last s = s + (sch.W - 1)) ∧ ∀ s, th.win_boundary s = s + sch.p

/-- **The starting times are unbounded**: whatever the time, some slot has
not started yet. The paper's slots are infinitely many and τ-spaced on the
real line (Appendix A.1 (`subsection:mcp-preliminaries`)), so a validator
that becomes ready can always pick the first slot `s*` of the next window
whose starting time has not passed (Algorithm 7, lines 38–41
(`line:ready-time`–`line:sstar-update`)). Without it the model's
`acs_propose` can stay disabled forever once the clock has passed every
starting time ([ConductorBounds.md](../../docs/ConductorBounds.md) F28).
`StartTimes` alone does not give it: an ordered, cancellative, Archimedean
time can still have `start₀ + s • τ` bounded when `start₀` is negative. -/
def StartsUnbounded (th : Conductor.Theory ℕ window time node acsstate) : Prop :=
  ∀ t, ∃ s, t ≤ th.start_time s

end Configuration

/-! ## Timed runs of the Conductor -/

section Runs

open Classical

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time]

/-- A state of the Conductor with numbered slots. -/
abbrev CState (window time node acsstate : Type) :=
  Conductor.State (Conductor.FieldAbstractType ℕ window time node acsstate)

/-- A label of the Conductor with numbered slots. -/
abbrev CLabel (window time node acsstate : Type) :=
  Conductor.Label ℕ window time node acsstate

/-- A labelled **timed** run of the Conductor with numbered slots: the object
every premise below is about. The clock is the run's ([Timed.lean](../Timed.lean)). -/
abbrev TConductorRun (th : Conductor.Theory ℕ window time node acsstate) :=
  TLRun (Conductor.relationalTransitionSystem ℕ window time node acsstate) th time

variable {th : Conductor.Theory ℕ window time node acsstate}

/-- The run as a run of the orchestrator contract at the Conductor's
fragment (`orchestratorSafety th`, [Composition.lean](../Composition.lean)):
its states and clock, the labels forgotten. The caller's conditions and the
claims' conclusions are read on it in the contract's own vocabulary. -/
noncomputable def contractRun (r : TConductorRun th) :
    TimedRun (CState window time node acsstate) time (orchestratorSafety th).init
      (orchestratorSafety th).trans :=
  r.toTimedRun _ _ ⟨r.holds, r.starts⟩ (fun n => ⟨r.lbl n, r.steps n⟩)

/-! ### A validator's local state, read off the model's state

The model's ghost relations, restated over the state's fields: the bounds of
a window, the window a validator is in, its readiness, and the slots it has
scheduled. Window intervals are global in the model because ACS agreement
makes every correct validator compute the same one; each validator holds
the intervals of the windows it entered. -/

/-- The bounds of window `w` (the model's `win_bounds`): window 1's are the
configuration's, later windows' the recorded ACS decision. -/
def WinBounds (st : CState window time node acsstate) (w : window) (f b l : ℕ) : Prop :=
  (w = win_ord.zero ∧ f = 0 ∧ b = th.genesis_boundary ∧ l = th.genesis_last) ∨
    st.acs_decided w f b l = true

/-- `i` is in window `w` (the model's `in_window`, the paper's
`current_window_i`): it has entered `w` and not `w`'s successor. -/
def InWindow (st : CState window time node acsstate) (i : node) (w : window) : Prop :=
  st.entered i w = true ∧ ∀ w', win_ord.next w w' → st.entered i w' = false

variable (th) in
/-- `i` is ready to leave window `w` (the model's `ready_next`, Algorithm 7,
line 23 (`line:ready-check`)): every slot it has scheduled strictly below
`w`'s readiness boundary is completed. -/
def ReadyNext (st : CState window time node acsstate) (i : node) (w : window) : Prop :=
  ∀ f b l, WinBounds (th := th) st w f b l →
    ∀ s w0 f0 b0 l0, st.entered i w0 = true → WinBounds (th := th) st w0 f0 b0 l0 →
      f0 ≤ s → s ≤ l0 → s < b → st.completed i s = true

variable (th) in
/-- `i` has scheduled slot `s` (the model's `slot_scheduled`, the paper's
eager `opened_i`, Algorithm 7, line 51 (`line:acs-opened-update`)): `s` lies
in the interval of a window `i` has entered. -/
def Scheduled (st : CState window time node acsstate) (i : node) (s : ℕ) : Prop :=
  ∃ w f b l, st.entered i w = true ∧ WinBounds (th := th) st w f b l ∧ f ≤ s ∧ s ≤ l

/-! ### The gates -/

variable (th) in
/-- The ACS proposal's gate (Algorithm 7, line 37 (`line:ready`)): `i` is
in `w'`'s predecessor and ready. -/
def proposeGate (i : node) (w' : window) (st : CState window time node acsstate) : Prop :=
  ∃ w, win_ord.next w w' ∧ InWindow st i w ∧ ReadyNext th st i w

variable (th) in
/-- Window entry's gate (Algorithm 7, line 44 (`line:acs-decide`)): `i`'s
**own** `ACS[w']` has decided (F22), and `i` is in `w'`'s predecessor and
ready. -/
def enterGate (i : node) (w' : window) (st : CState window time node acsstate) : Prop :=
  A.has_decided (st.acs_state w') i ∧ proposeGate th i w' st

/-- The decided interval's gate: some correct validator's `ACS[w]` has
output a decision, which the recording step reads (the model's
`acs_decide`, Algorithm 7, line 48 (`line:median-compute`)). -/
def decideGate (w : window) (st : CState window time node acsstate) : Prop :=
  ∃ i, ¬ fm.byz i ∧ A.has_decided (st.acs_state w) i

/-! ### The rows' label families

Each handler has a parameter that is a result, not a choice (the ACS's
next state, the first slot `s*` its guards determine, the decided interval),
so each row is a family, fair as a whole, as Chorus's proposal is. -/

/-- `i`'s ACS proposal to `ACS[w']`, for any first slot and ACS successor. -/
def ProposeLabel (i : node) (w' : window) : CLabel window time node acsstate → Prop :=
  fun l => ∃ w s a, l = .acs_propose i w w' s a

/-- `i`'s entry into `w'`. -/
def EnterLabel (i : node) (w' : window) : CLabel window time node acsstate → Prop :=
  fun l => ∃ w f b l' a, l = .enter_window i w w' f b l' a

/-- The recording of `w`'s decided interval. -/
def DecideLabel (w : window) : CLabel window time node acsstate → Prop :=
  fun l => ∃ w0 first f0 b0 l0 r1 s1 r2 s2, l = .acs_decide w0 w first f0 b0 l0 r1 s1 r2 s2

/-! ### The premises -/

variable [AddCommMonoid time]

/-- **The rows** — each of the Conductor's honest handlers fires within `δ`
of its gate opening ([Premises.md](../../docs/Premises.md) §9.3).

The timed form of (F-justice) for the Conductor
([Conductor.lean](../Conductor.lean), "Meta-axioms"): Chorus's
`TimedJustice` shape (`BufferedFairFamily`) with every row local, so the
message part is `δ` too and nothing is owed but the gate. The paper's
handlers run instantaneously, and at the schedule's `δ = 0` the clause says
exactly that. -/
structure TimedRows {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
    (sch : ConductorSchedule view time vfin) (r : TConductorRun th) : Prop where
  /-- The ACS proposal (Algorithm 7, lines 37–43
  (`line:ready`–`line:proposed-update`)). -/
  propose : ∀ i w', ¬ fm.byz i →
    BufferedFairFamily r sch.δ sch.δ (fun _ => True) (proposeGate th i w') (ProposeLabel i w')
  /-- Window entry (Algorithm 7, lines 44–52
  (`line:acs-decide`–`line:last-update`)). -/
  enter : ∀ i w', ¬ fm.byz i →
    BufferedFairFamily r sch.δ sch.δ (fun _ => True) (enterGate th i w') (EnterLabel i w')
  /-- The decided interval (Algorithm 7, line 48 (`line:median-compute`)). -/
  decide : ∀ w,
    BufferedFairFamily r sch.δ sch.δ (fun _ => True) (decideGate w) (DecideLabel w)

/-- **(P-open)** — the opening timer is punctual
([Premises.md](../../docs/Premises.md) §9.3).

`schedule_opening(s)` "wait[s] until the first time ≥ max(current local
time, s.deadline − Δ)" and then outputs `open(s)` (Algorithm 7, lines 27–28
(`line:conductor-wait-for-open`–`line:trigger-open`)): a correct validator
that has scheduled `s` at index `N` has opened it by `max(clk N, start s)`.
A local timer on synchronized clocks, so the clause holds before GST too,
as Chorus's (P-phase) does. Its other half, not early, is the model's guard
and needs no premise (`[opened_after_start]`). The model lets an enabled
opening wait ("Timing relaxation" in [Conductor.lean](../Conductor.lean));
this premise is what removes that freedom from the timed claims. -/
def OpenPunctual (r : TConductorRun th) : Prop :=
  ∀ N i s, ¬ fm.byz i → Scheduled th (r.at' N) i s →
    ∃ n, N ≤ n ∧ r.clk n ≤ max (r.clk N) (th.start_time s) ∧ (r.at' n).opened i s = true

/-- **One clock** — the run's clock is the Conductor's `now`
([Premises.md](../../docs/Premises.md) §9.3). `OrchestratorTemporal.clock_agrees`
asks it of every admissible run; time advances exactly at the model's
`tick` steps. -/
def ClockAgrees (r : TConductorRun th) : Prop :=
  ∀ n, r.clk n = (r.at' n).now

end Runs

/-! ## The per-window ACS, as a component of the Conductor -/

section Component

open Classical

variable {window node acsstate time : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [Inhabited time] [win_ord : TotalOrderWithMinimum window] [time_ord : TotalOrder time]
  [fm : FaultModel node] [A : ACSSafety node ℕ acsstate fm.byz]
  {th : Conductor.Theory ℕ window time node acsstate}
  {st st' : Conductor.State (Conductor.FieldAbstractType ℕ window time node acsstate)}

/-- Expose one action's transition body (as in [Composition.lean](../Composition.lean)). -/
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

set_option maxHeartbeats 2000000 in
/-- The oracle step moves window `w`'s ACS by one of its internal steps and
leaves every other window's alone. -/
theorem acs_step_acs {w : window} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st (.acs_step w a) st') :
    A.step (st.acs_state w) a ∧ ∀ x, st'.acs_state x = if x = w then a else st.acs_state x := by
  conductor_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  conductor_field_simp
  exact ⟨‹_›, fun x => by rcases eq_or_ne x w with h | h <;> simp [h, Ne.symm]⟩

set_option maxHeartbeats 2000000 in
/-- The ACS proposal gives `ACS[w']` its `propose` input and leaves every
other window's ACS alone. -/
theorem acs_propose_acs {i : node} {w w' : window} {s : ℕ} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.acs_propose i w w' s a) st') :
    A.propose (st.acs_state w') i s a ∧ ∀ x, st'.acs_state x = if x = w' then a else st.acs_state x := by
  conductor_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  conductor_field_simp
  exact ⟨‹_›, fun x => by rcases eq_or_ne x w' with h | h <;> simp [h, Ne.symm]⟩

set_option maxHeartbeats 2000000 in
/-- Window entry gives `ACS[w']` its `abandon` input and leaves every other
window's ACS alone. -/
theorem enter_window_acs {i : node} {w w' : window} {f b l : ℕ} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.enter_window i w w' f b l a) st') :
    A.abandon (st.acs_state w') i a ∧ ∀ x, st'.acs_state x = if x = w' then a else st.acs_state x := by
  conductor_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  conductor_field_simp
  exact ⟨‹_›, fun x => by rcases eq_or_ne x w' with h | h <;> simp [h, Ne.symm]⟩

set_option maxHeartbeats 2000000 in
/-- The ACS instances start in their configured initial states. -/
theorem acs_state_init
    (hi : (Conductor.relationalTransitionSystem ℕ window time node acsstate).init th st) :
    st.acs_state = th.acs_init_state := by
  simp only [Conductor.relationalTransitionSystem, Conductor.Init, Conductor.initializer.ext.tr] at hi
  subst_vars
  conductor_field_simp

/-- The Conductor's labels that move window `w`'s ACS: its oracle step, and
the two inputs the Conductor gives it. -/
def AcsLabel (w : window) : CLabel window time node acsstate → Prop
  | .acs_step w' _ => w' = w
  | .acs_propose _ _ w' _ _ => w' = w
  | .enter_window _ _ w' _ _ _ _ => w' = w
  | _ => False

/-- **Window `w`'s ACS is a component of the Conductor**: its state is
`acs_state w`; the oracle step and the two inputs at `w` are its
transitions (`ACSSafety.step`, `propose`, `abandon`), and every other step
of the Conductor leaves it alone. The part a per-window premise speaks of,
through the stutter lift ([PartProjection.lean](../PartProjection.lean)). -/
noncomputable def acsComponent (th : Conductor.Theory ℕ window time node acsstate) (w : window) :
    Component (Conductor.relationalTransitionSystem ℕ window time node acsstate) th
      (contractRTS A.toTransitionSystemSafety) () where
  proj st := st.acs_state w
  isSub := AcsLabel w
  init s ha hi := ⟨trivial, by rw [acs_state_init hi]; exact ha.1 w⟩
  frame s l s' htr hl := by
    cases l with
    | tick => exact congrFun (Conductor.tick.frame_acs_state htr) w
    | acs_propose i w0 w' s a =>
      rw [(acs_propose_acs htr).2 w, if_neg (Ne.symm hl)]
    | acs_step w' a =>
      rw [(acs_step_acs htr).2 w, if_neg (Ne.symm hl)]
    | acs_decide => exact congrFun (Conductor.acs_decide.frame_acs_state htr) w
    | enter_window i w0 w' f b l a =>
      rw [(enter_window_acs htr).2 w, if_neg (Ne.symm hl)]
    | open_slot => exact congrFun (Conductor.open_slot.frame_acs_state htr) w
    | complete_slot => exact congrFun (Conductor.complete_slot.frame_acs_state htr) w
  step s l s' htr hl := by
    cases l with
    | acs_propose i w0 w' sl a =>
      cases hl
      obtain ⟨hp, he⟩ := acs_propose_acs htr
      refine ⟨(), ?_⟩
      show A.trans (s.acs_state w) (s'.acs_state w)
      rw [he w, if_pos rfl]
      exact A.propose_trans _ _ _ _ hp
    | acs_step w' a =>
      cases hl
      obtain ⟨hp, he⟩ := acs_step_acs htr
      refine ⟨(), ?_⟩
      show A.trans (s.acs_state w) (s'.acs_state w)
      rw [he w, if_pos rfl]
      exact A.step_trans _ _ hp
    | enter_window i w0 w' f b l a =>
      cases hl
      obtain ⟨hp, he⟩ := enter_window_acs htr
      refine ⟨(), ?_⟩
      show A.trans (s.acs_state w) (s'.acs_state w)
      rw [he w, if_pos rfl]
      exact A.abandon_trans _ _ _ hp
    | _ => exact absurd hl id

end Component

/-! ## The ACS's premise, and the whole timing model -/

section Premise

open Classical

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time]
  {th : Conductor.Theory ℕ window time node acsstate}

/-- **The ACS meets its module** — once a correct validator has proposed to
window `w`'s ACS, that ACS's part of the run is admissible for its contract
([Premises.md](../../docs/Premises.md) §9.3).

The part's run is the stutter lift of [PartProjection.lean](../PartProjection.lean)
(F24): the run's states, clock and GST, with every composed step that is a
transition of the ACS contract — a real step, or a stutter its `trans`
allows — counted as one of the ACS's. Stated with the contract's own field
`TA.Admissible` and restated nowhere, so the ACS's timing model reaches the
Conductor only through `TA`. The guard loses nothing: every use of an ACS
field at `w` has a correct proposal there (Termination's antecedent says
so, and Totality's correct decision implies one by `integrity`); and it is
what lets the Conductor's idle run be admissible without any ACS field
([ConductorBounds.md](../../docs/ConductorBounds.md) F24). -/
def AcsAdmissible {msg : Type} (TA : ACSTemporal node ℕ acsstate time msg fm.byz)
    (r : TConductorRun th) : Prop :=
  ∀ w, (∃ n i s, ¬ fm.byz i ∧ A.proposed ((r.at' n).acs_state w) i s) →
    ∃ p : (stutterComp (acsComponent th w)).Projection (liftRun (acsComponent th w) r).toLRun,
      TA.Admissible (partRun p)

/-- **The whole of what is assumed of a run**: the rows, the punctual
openings, one clock, and the ACS meeting its module. -/
def Sync {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
    {msg : Type} (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (r : TConductorRun th) : Prop :=
  TimedRows sch r ∧ OpenPunctual r ∧ ClockAgrees r ∧ AcsAdmissible TA r

end Premise

/-! ## The targets, stated

Three `Prop`-valued definitions, asserted nowhere. Each conclusion is the
orchestrator contract's field read at the Conductor's fragment
(`orchestratorSafety th`), so the contract instance of K6 consumes them as
they are: Totality is `OrchestratorWithTotality.totality` at `d_tot`,
Boundedness `OrchestratorTemporal.boundedness` at `𝓑 = 2W − p`, Recovery
`OrchestratorTemporal.recovery` at `𝓡 = 2Wτ`. The caller's conditions are
the contract's, at Chorus's latencies: (R-tot) at `d_tot`, (R-term) at
`d_tot` and `ℓ_chorus`. -/

section Claims

open Classical

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  [Fintype node] [DecidablePred fm.byz]

/-- **`d_tot`-Totality, the target** (Lemma 15 (`lemma:conductor-totality`)).
Over an ordered time (F27), under the timing model, with unbounded starting
times (`StartsUnbounded`, F28) and the ACS's `Δ` the system's, and if the
caller's completions are total ((R-tot) at `d_tot`): for every slot, once a
correct validator has opened it at clock `c`, every correct validator opens
it by `max(c, GST) + d_tot`, with `d_tot = Δ` at the schedule's `δ = 0`
(`ConductorSchedule.d_tot_paper`). The proof is the window induction of
Proposition 13 (`prop:window-synchronization`), stage K4. -/
def TotalityClaim [IsOrderedAddMonoid time] {msg : Type} (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz)
    (th : Conductor.Theory ℕ window time node acsstate) : Prop :=
  StartsUnbounded th → TA.Δ = sch.Δ →
  ∀ r : TConductorRun th, Sync sch TA r →
    (orchestratorSafety th).CallerTotality (contractRun r) sch.d_tot →
    ∀ s, (orchestratorSafety th).OpeningsSyncWithin (contractRun r) s sch.d_tot

/-- **`(2W − p)`-Boundedness, the target** (Lemma 14 (`lem:boundedness`)).
With windows of `W` slots and the readiness boundary at the `(p + 1)`-th: at
every reachable state, an opened, uncompleted slot of a correct validator
has fewer than `2W − p` opened slots above it — the contract's form of "if
`p_i` has opened `k` slots, every `s_j` with `j ≤ k − 𝓑` is completed".
A state property: it holds of the Conductor alone, with no run premise and
no caller condition.

This is also the whole of what Lemma 5 (`lemma:cadence-bounded-concurrency`)
needs from the orchestrator (stage K7): a slot instance a correct validator
actively participates in is opened and not completed (the glue's
`[bounded_concurrency_interval]`), so of `𝓑 + 1` such instances the
lowest would have `𝓑` opened slots above it. The proof is Proposition 11
(`prop:open-count-window`) with `[bounded_tail]` and the window widths,
in [Boundedness.lean](Boundedness.lean) (`Conductor.boundedness`). -/
def BoundednessClaim (sch : ConductorSchedule view time vfin)
    (th : Conductor.Theory ℕ window time node acsstate) : Prop :=
  WindowShifts sch th →
  ∀ st, (orchestratorSafety th).reachable st → ∀ i s, ¬ fm.byz i →
    Opened st i s → ¬ Completed st i s →
    ¬ ∃ g : Fin sch.bound → ℕ, Function.Injective g ∧ ∀ k, Opened st i (g k) ∧ s ≤ g k ∧ s ≠ g k

/-- **`(2Wτ)`-Recovery, the target** (Lemma 16 (`lemma:conductor-recovery`)).
Over an ordered time (F27), under the timing model at τ-spaced starting
times and windows of the schedule's shape, with the ACS's `Δ` and `ℓ` the
system's, at most its fault
bound Byzantine, and if the caller's completions are total ((R-tot) at
`d_tot`) and terminate ((R-term) at `d_tot` and
`ℓ_chorus`): every slot whose starting time is at least `GST + 2Wτ` is
opened by every correct validator by its starting time — with Integrity's
timing half, exactly then. The proof is Propositions 14–19, stage K5; the
four parameter assumptions are the schedule's fields. -/
def RecoveryClaim [IsOrderedAddMonoid time] {msg : Type} (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz)
    (th : Conductor.Theory ℕ window time node acsstate) : Prop :=
  StartTimes sch th → WindowShifts sch th →
  TA.Δ = sch.Δ → TA.ℓ = sch.ℓ → (Finset.univ.filter fm.byz).card ≤ TA.fault_bound →
  ∀ r : TConductorRun th, Sync sch TA r →
    (orchestratorSafety th).CallerTotality (contractRun r) sch.d_tot →
    (orchestratorSafety th).CallerTermination (contractRun r) sch.d_tot sch.ℓchorus →
    ∀ s, r.gst + sch.recoveryTime ≤ th.start_time s →
      ∀ i, ¬ fm.byz i → (contractRun r).byTime (th.start_time s) (fun st => Opened st i s)

end Claims

/-! ## The constants are the Chorus instance's

`Φ_oc` and `d_tot` speak about the values the composed theorem will use:
`Chorus.chorusWithTotality`'s `ℓ` and `d_tot` at the schedule's family
schedule, by definition. -/

section AtChorus

open Classical ByzNodeSet

variable {merkle_root view Phase PathChoice : Type}
  [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [vord : TotalOrderWithMinimum view]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
  [node_inhabited : Inhabited (Fin n)]
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time]
  [Archimedean time]
  {is_proposer : Fin n → Bool} {well_encoded : merkle_root → Bool}
  {mvba_init_state : Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)}
  {mvalid : MetaBlock (Fin n) merkle_root → Bool} {mleader : view → Fin n → Bool}

/-- **`Φ_oc` and `d_tot` are the Chorus instance's**: at the system's
configuration, the schedule's `ℓ_chorus` and `d_tot` are
`Chorus.chorusWithTotality`'s `ℓ` and `d_tot` at the schedule's family
schedule, so the four parameter assumptions speak about the constants the
composed theorem uses. By definition. -/
theorem Φ_oc_eq_chorus (vfin : ViewOrderEnum view vord) (sch : ConductorSchedule view time vfin)
    (hprop : ∃ J, is_proposer J = true)
    (hrot : Mvba.LeaderRotation (nset := byzNodeSetFin n f hf is_byz hbyz) vfin sch.mvba.k
      (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader)) :
    (Chorus.chorusWithTotality (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice)
        (is_proposer := is_proposer) (well_encoded := well_encoded)
        (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader)
        n f hf is_byz hbyz sch.toFamilySchedule hprop vfin hrot).ℓ = sch.ℓchorus ∧
    (Chorus.chorusWithTotality (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice)
        (is_proposer := is_proposer) (well_encoded := well_encoded)
        (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader)
        n f hf is_byz hbyz sch.toFamilySchedule hprop vfin hrot).d_tot = sch.d_tot :=
  ⟨rfl, rfl⟩

end AtChorus

end Conductor

/-! ## The pinned trust base

The constants, the component, and the tie to Chorus; the targets are
definitions, so nothing here asserts a bound. -/

/-- info: 'Conductor.ConductorSchedule.d_tot_paper' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Conductor.ConductorSchedule.d_tot_paper

/-- info: 'Conductor.ConductorSchedule.Φ_oc_paper' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Conductor.ConductorSchedule.Φ_oc_paper

/--
info: 'Conductor.acsComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.acsComponent

/--
info: 'Conductor.Φ_oc_eq_chorus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.Φ_oc_eq_chorus
