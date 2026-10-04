import Cadence.System
import Cadence.Conductor.Temporal

/-! # Composed.Schedule — the composed system's timing model, and its timed claims stated

[ConductorBounds.md](../../docs/ConductorBounds.md) §4 and §9, stage K7.
The glue ([Cadence.lean](../Cadence.lean)) at the verified instances — the
Conductor as its orchestrator, Chorus (with the `Mvba` model as its MVBA)
as every slot's consensus — run on one clock, with one time theory and one
`Δ`, at `δ = 0`. This file states the **timing model of a composed run**,
every premise a named `Prop`, and the **four composed claims** as
`Prop`-valued definitions, apart from any proof, as
[Conductor/Schedule.lean](../Conductor/Schedule.lean) does for the
Conductor.

`grep -nE '^(def|structure|abbrev|noncomputable (def|abbrev)) ' Cadence/Composed/Schedule.lean`
prints the whole list.

## The composed system

* **One fault pattern** (`fmF`): Chorus's quorum family's (`n = 3f + 1`,
  at most `f` Byzantine), which the Conductor, the ACS and the glue are
  stated against too, so "correct" is one notion and no transport is needed.
* **The system** (`sysRTS`): the glue's transition system with the
  Conductor's fragment (`orchestratorSafety`) as `orch` and Chorus's
  (`Chorus.scSafety`) as `sc`, slots the numbers `ℕ`.
* **Its parts** (`orchComponent`, `slotComponent`): the orchestrator's state
  `os`, moved by the oracle step and the `complete(s)` input, and slot `x`'s
  instance `sc_state x`, moved by its oracle step and the three inputs. Each
  part's run is the stutter lift of [PartProjection.lean](../PartProjection.lean)
  (F24): a part that stops stepping is read as one whose stutters its own
  contract allows.

## What is assumed of a composed run (`SysSync`)

* **The glue's rows** (`GlueRows`): each of the glue's five handlers fires
  within `δ` of its gate, the timed form of the glue's (F-justice). At the
  schedule's `δ = 0` each handler runs with the event it handles, as the
  paper's do. Every gate reads only the acting validator's own state and
  the outputs it handles.
* **The Conductor meets its timing model** (`OrchAdmissible`): the
  orchestrator's part is admissible for `Conductor.conductorTemporal`.
* **Each started slot's Chorus meets its timing model** (`SlotAdmissible`):
  once a correct validator participates in slot `x`, the slot's part is
  admissible for `Chorus.chorusTemporal`, at the schedule's family schedule.

Censorship resistance takes one premise more, (P-incl) on every started
slot's part (`SlotInclusive`): a chunk delivered by the deadline is
recorded, the paper's "by the deadline" read inclusively (F31, P19).

The caller conditions of either side are **not** premises: Chorus's (C1,
C2, Δ-synchronized participation) and the Conductor's ((R-tot), (R-term))
are discharged in [Corollary4.lean](Corollary4.lean).

## The claims

* `Corollary4Claim` — Corollary 4 (`cor:chorus-correctness-within-cadence`);
* `BoundedConcurrencyClaim` — Lemma 5 (`lemma:cadence-bounded-concurrency`)
  at `𝓑 = 2W − p`;
* `LivenessClaim R` — `𝓡`-Liveness (Definition 2 (`def:liveness`), Lemma 2
  (`lemma:cadence-liveness`)) at recovery time `R`;
* `CensorshipClaim R` — `𝓡`-Censorship resistance (Definition 3
  (`def:censorship-resistance`)) at grace period `R`. -/

namespace Composed

open Cadence Conductor
open scoped Cadence.Timed

attribute [local instance] natSlotOrder


/-! ## The glue's transitions, read on the two sub-protocol states -/

section Glue

open Classical

variable {slot node pvector proposal ostate scstate time : Type}
  [Inhabited slot] [Inhabited node] [Inhabited pvector] [Inhabited proposal] [Inhabited ostate]
  [Inhabited scstate] [Inhabited time] [slot_ord : TotalOrder slot] [time_ord : TotalOrder time]
  [fm : FaultModel node] [orch : OrchestratorSafety node slot ostate time fm.byz]
  [sc : SlotConsensusSafety slot node proposal pvector scstate fm.byz]
  {th : Cadence.Theory slot node pvector proposal ostate scstate time}
  {st st' : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate time)}

/-- Expose one glue action's transition body. -/
local macro "glue_tr" h:ident : tactic =>
  `(tactic| (simp only [Cadence.relationalTransitionSystem, Cadence.Next, Cadence.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation. -/
local macro "glue_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id] at *)

set_option maxHeartbeats 2000000 in
theorem orch_step_os {a : ostate}
    (htr : (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.orch_step a) st') :
    orch.step st.os a ∧ st'.os = a := by
  glue_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  glue_field_simp
  assumption

set_option maxHeartbeats 2000000 in
theorem sc_step_sc {x : slot} {a : scstate}
    (htr : (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.sc_step x a) st') :
    sc.step (st.sc_state x) a ∧ ∀ y, st'.sc_state y = if y = x then a else st.sc_state y := by
  glue_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  glue_field_simp
  exact ⟨‹_›, fun y => by rcases eq_or_ne y x with h | h <;> simp [h, Ne.symm]⟩

set_option maxHeartbeats 2000000 in
theorem on_open_sc {i : node} {x : slot} {a : scstate}
    (htr : (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.on_open i x a) st') :
    sc.participate (st.sc_state x) i a ∧ ∀ y, st'.sc_state y = if y = x then a else st.sc_state y := by
  glue_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  glue_field_simp
  exact ⟨‹_›, fun y => by rcases eq_or_ne y x with h | h <;> simp [h, Ne.symm]⟩

set_option maxHeartbeats 2000000 in
theorem on_propose_sc {i : node} {x : slot} {p : proposal} {a : scstate}
    (htr : (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.on_propose i x p a) st') :
    sc.propose (st.sc_state x) i p a ∧ ∀ y, st'.sc_state y = if y = x then a else st.sc_state y := by
  glue_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  glue_field_simp
  exact ⟨‹_›, fun y => by rcases eq_or_ne y x with h | h <;> simp [h, Ne.symm]⟩

set_option maxHeartbeats 2000000 in
theorem on_finalize_eff {i : node} {x : slot} {v : pvector} {a : ostate} {b : scstate}
    (htr : (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.on_finalize i x v a b) st') :
    orch.complete st.os i x a ∧ sc.abandon (st.sc_state x) i b ∧ st'.os = a ∧
      ∀ y, st'.sc_state y = if y = x then b else st.sc_state y := by
  glue_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  glue_field_simp
  exact ⟨‹_›, ‹_›, fun y => by rcases eq_or_ne y x with h | h <;> simp [h, Ne.symm]⟩

set_option maxHeartbeats 2000000 in
theorem glue_init
    (hi : (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).init th st) :
    st.os = th.orch_init_state ∧ st.sc_state = th.sc_init_state := by
  simp only [Cadence.relationalTransitionSystem, Cadence.Init, Cadence.initializer.ext.tr] at hi
  subst_vars
  glue_field_simp

/-- The glue's labels that move the orchestrator: its oracle step, and the
`complete(s)` input the finalize handler gives it. -/
def OrchLabel : Cadence.Label slot node pvector proposal ostate scstate time → Prop
  | .orch_step _ => True
  | .on_finalize _ _ _ _ _ => True
  | _ => False

/-- **The orchestrator is a component of the glue**: its state is `os`; the
oracle step and the `complete(s)` input are its transitions, and every other
step of the glue leaves it alone. -/
noncomputable def orchComponent (th : Cadence.Theory slot node pvector proposal ostate scstate time) :
    Component (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time) th
      (contractRTS orch.toTransitionSystemSafety) () where
  proj st := st.os
  isSub := OrchLabel
  init s ha hi := ⟨trivial, by rw [(glue_init hi).1]; exact ha.1⟩
  frame s l s' htr hl := by
    cases l with
    | orch_step => exact absurd trivial hl
    | on_finalize => exact absurd trivial hl
    | sc_step => exact Cadence.sc_step.frame_os htr
    | on_open => exact Cadence.on_open.frame_os htr
    | on_propose => exact Cadence.on_propose.frame_os htr
    | record_skip => exact Cadence.record_skip.frame_os htr
    | append => exact Cadence.append.frame_os htr
  step s l s' htr hl := by
    cases l with
    | orch_step a =>
      obtain ⟨h, he⟩ := orch_step_os htr
      exact ⟨(), by show orch.trans s.os s'.os; rw [he]; exact orch.step_trans _ _ h⟩
    | on_finalize i x v a b =>
      obtain ⟨h, -, he, -⟩ := on_finalize_eff htr
      exact ⟨(), by show orch.trans s.os s'.os; rw [he]; exact orch.complete_trans _ _ _ _ h⟩
    | _ => exact absurd hl id

/-- The glue's labels that move slot `x`'s instance: its oracle step, and
the three inputs the handlers give it. -/
def SlotLabel (x : slot) : Cadence.Label slot node pvector proposal ostate scstate time → Prop
  | .sc_step y _ => y = x
  | .on_open _ y _ => y = x
  | .on_propose _ y _ _ => y = x
  | .on_finalize _ y _ _ _ => y = x
  | _ => False

/-- **Slot `x`'s instance is a component of the glue**: its state is
`sc_state x`; the oracle step and the three inputs at `x` are its
transitions (`step`, `participate`, `propose`, `abandon`), and every other
step of the glue leaves it alone. -/
noncomputable def slotComponent (th : Cadence.Theory slot node pvector proposal ostate scstate time)
    (x : slot) :
    Component (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time) th
      (contractRTS sc.toTransitionSystemSafety) () where
  proj st := st.sc_state x
  isSub := SlotLabel x
  init s ha hi := ⟨trivial, by rw [(glue_init hi).2]; exact ha.2.1 x⟩
  frame s l s' htr hl := by
    cases l with
    | orch_step => exact congrFun (Cadence.orch_step.frame_sc_state htr) x
    | record_skip => exact congrFun (Cadence.record_skip.frame_sc_state htr) x
    | append => exact congrFun (Cadence.append.frame_sc_state htr) x
    | sc_step y a => rw [(sc_step_sc htr).2 x, if_neg (Ne.symm hl)]
    | on_open i y a => rw [(on_open_sc htr).2 x, if_neg (Ne.symm hl)]
    | on_propose i y p a => rw [(on_propose_sc htr).2 x, if_neg (Ne.symm hl)]
    | on_finalize i y v a b => rw [(on_finalize_eff htr).2.2.2 x, if_neg (Ne.symm hl)]
  step s l s' htr hl := by
    cases l with
    | sc_step y a =>
      cases hl
      obtain ⟨h, he⟩ := sc_step_sc htr
      exact ⟨(), by show sc.trans _ _; rw [he x, if_pos rfl]; exact sc.step_trans _ _ h⟩
    | on_open i y a =>
      cases hl
      obtain ⟨h, he⟩ := on_open_sc htr
      exact ⟨(), by show sc.trans _ _; rw [he x, if_pos rfl]; exact sc.participate_trans _ _ _ h⟩
    | on_propose i y p a =>
      cases hl
      obtain ⟨h, he⟩ := on_propose_sc htr
      exact ⟨(), by show sc.trans _ _; rw [he x, if_pos rfl]; exact sc.propose_trans _ _ _ _ h⟩
    | on_finalize i y v a b =>
      cases hl
      obtain ⟨-, h, -, he⟩ := on_finalize_eff htr
      exact ⟨(), by show sc.trans _ _; rw [he x, if_pos rfl]; exact sc.abandon_trans _ _ _ h⟩
    | _ => exact absurd hl id

end Glue

/-! ## The glue's rows -/

section Rows

open Classical

variable {slot node pvector proposal ostate scstate time : Type}
  [Inhabited slot] [Inhabited node] [Inhabited pvector] [Inhabited proposal] [Inhabited ostate]
  [Inhabited scstate] [Inhabited time] [slot_ord : TotalOrder slot] [time_ord : TotalOrder time]
  [fm : FaultModel node] [orch : OrchestratorSafety node slot ostate time fm.byz]
  [sc : SlotConsensusSafety slot node proposal pvector scstate fm.byz]

/-- A state of the glue. -/
abbrev GState (slot node pvector proposal ostate scstate time : Type) :=
  Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate time)

/-- A label of the glue. -/
abbrev GLabel (slot node pvector proposal ostate scstate time : Type) :=
  Cadence.Label slot node pvector proposal ostate scstate time

/-- `on_open`'s gate (Algorithm 1, line 17 (`line:participate`)): `i` has
opened `x` and does not yet participate in it. -/
def openGate (i : node) (x : slot) (st : GState slot node pvector proposal ostate scstate time) : Prop :=
  orch.opened st.os i x ∧ ¬ sc.participating (st.sc_state x) i

variable (pvector) in
/-- `on_propose`'s gate (Algorithm 1, lines 18–19
(`line:proposer-check`–`line:propose`)): `i` has opened `x`, participates in
it, is one of its proposers and has not proposed. -/
def proposeGate (th : Cadence.Theory slot node pvector proposal ostate scstate time) (i : node) (x : slot)
    (st : GState slot node pvector proposal ostate scstate time) : Prop :=
  orch.opened st.os i x ∧ sc.participating (st.sc_state x) i ∧ th.is_proposer i x = true ∧
    ¬ ∃ p, sc.proposed (st.sc_state x) i p

/-- `on_finalize`'s gate (Algorithm 1, line 20 (`line:upon-finalize`)): `i`
has opened `x`, its instance has finalized, and the finalization has not
been delivered. -/
def finalizeGate (i : node) (x : slot) (st : GState slot node pvector proposal ostate scstate time) : Prop :=
  orch.opened st.os i x ∧ (∃ v, sc.finalized (st.sc_state x) i v) ∧ ∀ v, st.delivered i x v = false

/-- `record_skip`'s gate (Algorithm 1, line 16 (`line:implicit-skip`)): `i`
has opened a slot above `x`, has not opened `x`, and has not recorded it. -/
def skipGate (i : node) (x : slot) (st : GState slot node pvector proposal ostate scstate time) : Prop :=
  (∃ w, orch.opened st.os i w ∧ slot_ord.le x w ∧ x ≠ w) ∧ ¬ orch.opened st.os i x ∧
    st.skipped i x = false

/-- `append`'s gate (Algorithm 1, line 24 (`line:upon-ready-to-append`)):
`i` holds a pending vector for `x`, has appended none, and every slot below
`x` is resolved. -/
def appendGate (i : node) (x : slot) (st : GState slot node pvector proposal ostate scstate time) : Prop :=
  (∃ v, st.delivered i x v = true) ∧ (∀ v, st.appended i x v = false) ∧
    ∀ y, slot_ord.le y x → y ≠ x → st.resolved i y = true

variable [LinearOrder time] [AddCommMonoid time]

/-- **The glue's rows** — each of the glue's handlers fires within `δ` of
its gate opening ([ConductorBounds.md](../../docs/ConductorBounds.md) §6.4).

The timed form of the glue's (F-justice) ([Cadence.lean](../Cadence.lean),
"Meta-axioms"), in the shape of the Conductor's `TimedRows`: every row is
local, so the message part is `δ` too and nothing is owed but the gate. In
the paper each handler runs atomically with the event it handles, and at
the schedule's `δ = 0` the clause says exactly that. -/
structure GlueRows (th : Cadence.Theory slot node pvector proposal ostate scstate time) (δ : time)
    (r : TLRun (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time) th time) :
    Prop where
  /-- `S[s].participate()` upon `open(s)` (Algorithm 1, line 17 (`line:participate`)). -/
  open_ : ∀ i x, ¬ fm.byz i →
    BufferedFairFamily r δ δ (fun _ => True) (openGate i x) (fun l => ∃ a, l = .on_open i x a)
  /-- `S[s].propose(P)` by a proposer upon `open(s)` (Algorithm 1, line 19
  (`line:propose`)). -/
  propose : ∀ i x, ¬ fm.byz i →
    BufferedFairFamily r δ δ (fun _ => True) (proposeGate pvector th i x)
      (fun l => ∃ p a, l = .on_propose i x p a)
  /-- `complete(s)` and `S[s].abandon()` upon `finalize` (Algorithm 1, lines
  20–23 (`line:upon-finalize`–`line:abandon`)). -/
  finalize : ∀ i x, ¬ fm.byz i →
    BufferedFairFamily r δ δ (fun _ => True) (finalizeGate i x)
      (fun l => ∃ v a b, l = .on_finalize i x v a b)
  /-- The implicit skip (Algorithm 1, line 16 (`line:implicit-skip`)). -/
  skip : ∀ i x, ¬ fm.byz i →
    BufferedFairFamily r δ δ (fun _ => True) (skipGate i x) (fun l => ∃ w, l = .record_skip i x w)
  /-- The append (Algorithm 1, lines 24–26
  (`line:upon-ready-to-append`–`line:pending-remove`)). -/
  append : ∀ i x, ¬ fm.byz i →
    BufferedFairFamily r δ δ (fun _ => True) (appendGate i x) (fun l => ∃ v, l = .append i x v)

end Rows

section Config

open Classical ByzNodeSet

variable {merkle_root view Phase PathChoice window acsstate : Type}
  [Inhabited merkle_root] [Inhabited view] [Inhabited Phase] [Inhabited PathChoice]
  [Inhabited window] [Inhabited acsstate]
  [vord : TotalOrderWithMinimum view] [win_ord : TotalOrderWithMinimum window]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
  [node_inhabited : Inhabited (Fin n)]
  {time : Type} [LinearOrder time] [Inhabited time]

/-- The quorum family. -/
local notation "nsetF" => byzNodeSetFin n f hf is_byz hbyz
/-- Its counting facts. -/
local notation "cntF" => Cadence.byzNodeSetFin_counting n f hf is_byz hbyz

/-- **The system's fault model**: one fault pattern, Chorus's. -/
@[implicit_reducible]
def fmF : FaultModel (Fin n) := ⟨fun i => (nsetF).is_byz i = true⟩

/-- A slot instance's state. -/
abbrev SlotSt (merkle_root view Phase PathChoice : Type) (n : Nat) :=
  Chorus.SlotState ℕ (Fin n) (ByzNSet n) merkle_root view Phase PathChoice

/-- The orchestrator's state. -/
abbrev OrchSt (window time acsstate : Type) (n : Nat) := CState window time (Fin n) acsstate

/-- The Chorus configuration. -/
abbrev ChorusTh (merkle_root view Phase PathChoice : Type) (n : Nat) :=
  Chorus.Theory ℕ (Fin n) (ByzNSet n) merkle_root
    (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view))
    (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)
    (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)) Phase PathChoice

/-- The MVBA configuration. -/
abbrev MvbaTh (merkle_root view : Type) (n : Nat) :=
  Mvba.Theory (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view

variable [A : ACSSafety (Fin n) ℕ acsstate (fmF n f hf is_byz hbyz).byz]

/-- The slot-consensus fragment at the system's configuration. -/
noncomputable abbrev SC (thS : ChorusTh merkle_root view Phase PathChoice n) (thM : MvbaTh merkle_root view n) :=
  Chorus.scSafety (slot := ℕ) (nset := nsetF) (cnt := cntF) thS thM

/-- The orchestrator fragment at the system's configuration. -/
noncomputable abbrev OS (thO : Conductor.Theory ℕ window time (Fin n) acsstate) :=
  orchestratorSafety (fm := fmF n f hf is_byz hbyz) (acs := A) thO

/-- **The composed system**: the glue at the Conductor and Chorus. -/
noncomputable abbrev sysRTS (thO : Conductor.Theory ℕ window time (Fin n) acsstate)
    (thS : ChorusTh merkle_root view Phase PathChoice n) (thM : MvbaTh merkle_root view n) :=
  @Cadence.relationalTransitionSystem ℕ (Fin n) (ℕ × (Fin n → Option merkle_root)) merkle_root
    (OrchSt window time acsstate n) (SlotSt merkle_root view Phase PathChoice n) time
    _ _ _ _ _ _ _ TotalOrderWithMinimum.toTotalOrder _ (fmF n f hf is_byz hbyz)
    (OS n f hf is_byz hbyz thO) (SC n f hf is_byz hbyz thS thM)


/-- The glue's configuration at the system's instances. -/
abbrev GTheory (merkle_root view Phase PathChoice window time acsstate : Type) (n : Nat) :=
  Cadence.Theory ℕ (Fin n) (ℕ × (Fin n → Option merkle_root)) merkle_root
    (OrchSt window time acsstate n) (SlotSt merkle_root view Phase PathChoice n) time

/-- A labelled timed run of the composed system: the object every premise
below is about. The clock is the run's. -/
abbrev TSysRun (thO : Conductor.Theory ℕ window time (Fin n) acsstate)
    (thS : ChorusTh merkle_root view Phase PathChoice n) (thM : MvbaTh merkle_root view n)
    (thG : GTheory merkle_root view Phase PathChoice window time acsstate n) :=
  TLRun (sysRTS n f hf is_byz hbyz thO thS thM) thG time

/-- The orchestrator, as a component of the composed system. -/
noncomputable abbrev orchC (thO : Conductor.Theory ℕ window time (Fin n) acsstate)
    (thS : ChorusTh merkle_root view Phase PathChoice n) (thM : MvbaTh merkle_root view n)
    (thG : GTheory merkle_root view Phase PathChoice window time acsstate n) :=
  orchComponent (slot_ord := TotalOrderWithMinimum.toTotalOrder) (fm := fmF n f hf is_byz hbyz)
    (orch := OS n f hf is_byz hbyz thO) (sc := SC n f hf is_byz hbyz thS thM) thG

/-- Slot `x`'s instance, as a component of the composed system. -/
noncomputable abbrev slotC (thO : Conductor.Theory ℕ window time (Fin n) acsstate)
    (thS : ChorusTh merkle_root view Phase PathChoice n) (thM : MvbaTh merkle_root view n)
    (thG : GTheory merkle_root view Phase PathChoice window time acsstate n) (x : ℕ) :=
  slotComponent (slot_ord := TotalOrderWithMinimum.toTotalOrder) (fm := fmF n f hf is_byz hbyz)
    (orch := OS n f hf is_byz hbyz thO) (sc := SC n f hf is_byz hbyz thS thM) thG x

variable [AddCommMonoid time] {vfin : ViewOrderEnum view vord} {msg : Type}

/-- **The Conductor meets its timing model** — the orchestrator's part of
the run is admissible for the Conductor's temporal instance.

The part's run is the stutter lift of [PartProjection.lean](../PartProjection.lean)
(F24): the run's states, clock and GST, every composed step that is a
transition of the orchestrator contract counted as one of the
orchestrator's. `Conductor.Admissible` is `Conductor.conductorTemporal`'s
`Admissible` field by definition (`orchAdmissible_field`), so this is the
contract's premise, restated nowhere: the Conductor's rows, its punctual
openings, its clock the run's, and the ACS meeting its module
([Premises.md](../../docs/Premises.md) §9.3). -/
def OrchAdmissible (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal (Fin n) ℕ acsstate time msg (fmF n f hf is_byz hbyz).byz)
    {thO : Conductor.Theory ℕ window time (Fin n) acsstate}
    {thS : ChorusTh merkle_root view Phase PathChoice n} {thM : MvbaTh merkle_root view n}
    {thG : GTheory merkle_root view Phase PathChoice window time acsstate n}
    (r : TSysRun n f hf is_byz hbyz thO thS thM thG) : Prop :=
  ∃ p : (stutterComp (orchC n f hf is_byz hbyz thO thS thM thG)).Projection
      (liftRun (orchC n f hf is_byz hbyz thO thS thM thG) r).toLRun,
    Conductor.Admissible (fm := fmF n f hf is_byz hbyz) sch TA thO (partRun p)

/-- **Each started slot's Chorus meets its timing model** — once a correct
validator participates in slot `x`, that slot's part of the run is
admissible for Chorus's temporal instance.

The part's run is the stutter lift (F24), as for the orchestrator.
`Chorus.Admissible` is `Chorus.chorusTemporal`'s `Admissible` field by
definition, at the schedule's family schedule: (F-justice) on Chorus's
honest actions, the MVBA meeting its module, the certificate bridge and
the timed rows ([Premises.md](../../docs/Premises.md) §3–§5). The guard
loses nothing: every caller condition Chorus's claims take is about a slot
a correct validator participates in. -/
def SlotAdmissible (sch : ConductorSchedule view time vfin)
    {thO : Conductor.Theory ℕ window time (Fin n) acsstate}
    {thS : ChorusTh merkle_root view Phase PathChoice n} {thM : MvbaTh merkle_root view n}
    {thG : GTheory merkle_root view Phase PathChoice window time acsstate n}
    (r : TSysRun n f hf is_byz hbyz thO thS thM thG) : Prop :=
  ∀ x, (∃ k i, ¬ (fmF n f hf is_byz hbyz).byz i ∧
      (SC n f hf is_byz hbyz thS thM).participating ((r.at' k).sc_state x) i) →
    ∃ p : (stutterComp (slotC n f hf is_byz hbyz thO thS thM thG x)).Projection
        (liftRun (slotC n f hf is_byz hbyz thO thS thM thG x) r).toLRun,
      Chorus.Admissible (nset := nsetF) (cnt := cntF) sch.toFamilySchedule (partRun p)

/-- **The whole of what is assumed of a composed run**: the glue's rows,
the Conductor's timing model on its part, and Chorus's on every started
slot's part. -/
def SysSync (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal (Fin n) ℕ acsstate time msg (fmF n f hf is_byz hbyz).byz)
    {thO : Conductor.Theory ℕ window time (Fin n) acsstate}
    {thS : ChorusTh merkle_root view Phase PathChoice n} {thM : MvbaTh merkle_root view n}
    {thG : GTheory merkle_root view Phase PathChoice window time acsstate n}
    (r : TSysRun n f hf is_byz hbyz thO thS thM thG) : Prop :=
  GlueRows (slot_ord := TotalOrderWithMinimum.toTotalOrder) (fm := fmF n f hf is_byz hbyz)
      (orch := OS n f hf is_byz hbyz thO) (sc := SC n f hf is_byz hbyz thS thM) thG sch.δ r ∧
    OrchAdmissible n f hf is_byz hbyz sch TA r ∧ SlotAdmissible n f hf is_byz hbyz sch r

/-- **Each started slot's chunks are on time by the deadline** — (P-incl),
Chorus's `DeadlineInclusive`, on every started slot's part of the run
([Premises.md](../../docs/Premises.md) §4.8).

Read through every labelling of the part: `DeadlineInclusive` speaks only
of a run's states and clocks, so this is that premise about the part's own
states and clocks, restated nowhere. Used only by censorship resistance:
it is the paper's "by the deadline" read inclusively (P19). -/
def SlotInclusive (sch : ConductorSchedule view time vfin)
    {thO : Conductor.Theory ℕ window time (Fin n) acsstate}
    {thS : ChorusTh merkle_root view Phase PathChoice n} {thM : MvbaTh merkle_root view n}
    {thG : GTheory merkle_root view Phase PathChoice window time acsstate n}
    (r : TSysRun n f hf is_byz hbyz thO thS thM thG) : Prop :=
  ∀ x, (∃ k i, ¬ (fmF n f hf is_byz hbyz).byz i ∧
      (SC n f hf is_byz hbyz thS thM).participating ((r.at' k).sc_state x) i) →
    ∀ (p : (stutterComp (slotC n f hf is_byz hbyz thO thS thM thG x)).Projection
        (liftRun (slotC n f hf is_byz hbyz thO thS thM thG x) r).toLRun)
      (r' : Chorus.TChorusRun (nset := nsetF) thS thM time),
      (∀ k, r'.at' k = ((partRun p).at' k).2) → (∀ k, r'.clk k = (partRun p).clk k) →
      Chorus.DeadlineInclusive (nset := nsetF) (sch.toFamilySchedule.at x) r'

/-! ## The composed claims, stated

Four `Prop`-valued definitions, asserted nowhere; the proofs are in
[Corollary4.lean](Corollary4.lean), [Concurrency.lean](Concurrency.lean),
[Liveness.lean](Liveness.lean) and [Censorship.lean](Censorship.lean). Chorus enters at the system's
configuration (`Cadence.chorusTheory`, `Cadence.mvbaTheory`), as its
contract instance `Chorus.chorusWithTotality` is stated there. -/

section Claims

variable [IsOrderedCancelAddMonoid time] [Archimedean time]
  {is_proposer : Fin n → Bool} {well_encoded : merkle_root → Bool}
  {mvba_init_state : Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)}
  {mvalid : MetaBlock (Fin n) merkle_root → Bool} {mleader : view → Fin n → Bool}

/-- **Corollary 4 (`cor:chorus-correctness-within-cadence`), the claim**:
"When run within Cadence, Chorus is a correct implementation of the slot
consensus primitive." Over τ-spaced, unbounded starting times and the
ACS's `Δ` the system's: in every composed run that meets the timing model
(`SysSync`), every slot's Chorus part meets every condition Chorus's
contract instance (`Chorus.chorusWithTotality`) takes from its caller —
Δ-synchronized participation (Definition 5
(`def:delta-synchronized-participation`)), no abandonment before
finalizing (C1), no start before `D − Δ` (C2). So Chorus's timed claims
hold of every slot with no caller premise left
(`corollary4_bounded_termination`, `corollary4_totality`,
`corollary4_termination`). -/
def Corollary4Claim (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal (Fin n) ℕ acsstate time msg (fmF n f hf is_byz hbyz).byz)
    (thO : Conductor.Theory ℕ window time (Fin n) acsstate)
    (hprop : ∃ J, is_proposer J = true)
    (hrot : Mvba.LeaderRotation (nset := nsetF) vfin sch.mvba.k
      (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader)) : Prop :=
  StartTimes sch thO → StartsUnbounded thO → TA.Δ = sch.Δ →
  ∀ (thG : GTheory merkle_root view Phase PathChoice window time acsstate n)
    (r : TSysRun n f hf is_byz hbyz thO
      (Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer
        well_encoded mvba_init_state)
      (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader) thG),
    SysSync n f hf is_byz hbyz sch TA r →
    ∀ x (ps : (stutterComp (slotC n f hf is_byz hbyz thO _ _ thG x)).Projection
        (liftRun (slotC n f hf is_byz hbyz thO _ _ thG x) r).toLRun),
      let CWT := Chorus.chorusWithTotality (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice)
        (is_proposer := is_proposer) (well_encoded := well_encoded) (mvba_init_state := mvba_init_state)
        (mvalid := mvalid) (mleader := mleader) n f hf is_byz hbyz sch.toFamilySchedule hprop vfin hrot
      let SCI := SC n f hf is_byz hbyz
        (Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer
          well_encoded mvba_init_state)
        (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader)
      CWT.SyncParticipation (partRun ps) ∧
      (∀ i, ¬ (nsetF).is_byz i = true → ∀ k,
        SCI.abandoned ((partRun ps).at' k) i → ∃ V, SCI.finalized ((partRun ps).at' k) i V) ∧
      (∀ k i, ¬ (nsetF).is_byz i = true → SCI.participating ((partRun ps).at' k) i →
        CWT.deadline (SCI.tag ((partRun ps).at' k)) ≤ (partRun ps).clk k + CWT.Δ)

/-- **`𝓡`-Liveness of the composed system, the claim** (Definition 2
(`def:liveness`), Lemma 2 (`lemma:cadence-liveness`)), at recovery time
`R`. Under the Conductor's configuration premises and the ACS's constants
and fault bound, in every composed run that meets the timing model, for
every slot `s` with `s.deadline − Δ ≥ GST + R`, every correct validator
appends a proposal vector `V` with `V.slot = s` to its local log. Proven at
the paper's `𝓡 = 2Wτ` (`liveness`) and at `(W + p − 1)τ` (`liveness_sharp`,
P18). -/
def LivenessClaim (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal (Fin n) ℕ acsstate time msg (fmF n f hf is_byz hbyz).byz)
    (thO : Conductor.Theory ℕ window time (Fin n) acsstate) (R : time) : Prop :=
  StartTimes sch thO → WindowShifts sch thO → StartsUnbounded thO → WindowsUnbounded window →
  TA.Δ = sch.Δ → TA.ℓ = sch.ℓ →
  (Finset.univ.filter (fmF n f hf is_byz hbyz).byz).card ≤ TA.fault_bound →
  ∀ (thG : GTheory merkle_root view Phase PathChoice window time acsstate n)
    (r : TSysRun n f hf is_byz hbyz thO
      (Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer
        well_encoded mvba_init_state)
      (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader) thG),
    SysSync n f hf is_byz hbyz sch TA r →
    ∀ s, r.gst + R ≤ thO.start_time s →
      ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
        ∃ m v, (r.at' m).appended i s v = true ∧
          (SC n f hf is_byz hbyz
            (Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer
              well_encoded mvba_init_state)
            (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader)).slot_of v = s

/-- **`c`-Censorship resistance of the composed system, the claim**
(Definition 3 (`def:censorship-resistance`)), at grace period `R`. Over the
same premises as `LivenessClaim`, with (P-incl) on every started slot
(`SlotInclusive`) and a well-encoded root available to a correct proposer:
for every slot `s` with `s.deadline − Δ ≥ GST + R` and every correct
proposer `j` of `s`, `j` proposes some `P`, and every correct validator
appends a vector `V` with `V.slot = s` and `V[j] = P`. The glue's proposer
assignment is Chorus's by construction (`is_proposer j` for every slot),
so no tie between the two is assumed. -/
def CensorshipClaim (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal (Fin n) ℕ acsstate time msg (fmF n f hf is_byz hbyz).byz)
    (thO : Conductor.Theory ℕ window time (Fin n) acsstate) (R : time) : Prop :=
  StartTimes sch thO → WindowShifts sch thO → StartsUnbounded thO → WindowsUnbounded window →
  TA.Δ = sch.Δ → TA.ℓ = sch.ℓ →
  (Finset.univ.filter (fmF n f hf is_byz hbyz).byz).card ≤ TA.fault_bound →
  (∃ m, well_encoded m = true) →
  ∀ (o : OrchSt window time acsstate n) (sci : ℕ → SlotSt merkle_root view Phase PathChoice n)
    (r : TSysRun n f hf is_byz hbyz thO
      (Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer
        well_encoded mvba_init_state)
      (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader) ⟨fun j _ => is_proposer j, o, sci⟩),
    SysSync n f hf is_byz hbyz sch TA r → SlotInclusive n f hf is_byz hbyz sch r →
    ∀ s, r.gst + R ≤ thO.start_time s →
      ∀ j, ¬ (fmF n f hf is_byz hbyz).byz j → is_proposer j = true →
        ∃ P, (∃ k, (SC n f hf is_byz hbyz
            (Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer
              well_encoded mvba_init_state)
            (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader)).proposed ((r.at' k).sc_state s) j P) ∧
          ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
            ∃ m v, (r.at' m).appended i s v = true ∧
              (SC n f hf is_byz hbyz
                (Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer
                  well_encoded mvba_init_state)
                (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader)).slot_of v = s ∧
              (SC n f hf is_byz hbyz
                (Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer
                  well_encoded mvba_init_state)
                (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader)).includes v j P

end Claims

/-- **Lemma 5 (`lemma:cadence-bounded-concurrency`), the claim, at
`𝓑 = 2W − p`**: with windows of the schedule's shape, at every reachable
state of the composed system, no correct validator actively participates in
`𝓑 + 1` distinct slot-consensus instances. A state property: no run
premise and no caller condition. -/
def BoundedConcurrencyClaim (sch : ConductorSchedule view time vfin)
    (thO : Conductor.Theory ℕ window time (Fin n) acsstate) : Prop :=
  WindowShifts sch thO →
  ∀ (thS : ChorusTh merkle_root view Phase PathChoice n) (thM : MvbaTh merkle_root view n)
    (thG : GTheory merkle_root view Phase PathChoice window time acsstate n)
    (st : GState ℕ (Fin n) (ℕ × (Fin n → Option merkle_root)) merkle_root
      (OrchSt window time acsstate n) (SlotSt merkle_root view Phase PathChoice n) time),
    (sysRTS n f hf is_byz hbyz thO thS thM).reachable thG st →
    ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
      ¬ ∃ g : Fin (sch.bound + 1) → ℕ, Function.Injective g ∧
        ∀ k, (SC n f hf is_byz hbyz thS thM).participating (st.sc_state (g k)) i ∧
          ¬ (SC n f hf is_byz hbyz thS thM).abandoned (st.sc_state (g k)) i

end Config

end Composed

/-! ## The pinned trust base

The standard Lean trio and nothing else: no `sorryAx`. -/

/--
info: 'Composed.orchComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.orchComponent

/--
info: 'Composed.slotComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.slotComponent
