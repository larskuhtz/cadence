import Cadence.Chorus.Termination
import Cadence.Mvba.Temporal

/-! # Chorus.Schedule — the timing model, and the two timed claims stated

[Bounds.md](../../docs/Bounds.md) §6.4, stage S2. This file states the
**timing model** under which Chorus is to satisfy the contract's two timed
fields, `SlotConsensusWithTotality.bounded_termination` and `totality` —
every premise a named `Prop` on a labelled timed run — and the **two
targets** as `Prop`-valued definitions, apart from any proof. That is
[Mvba/Schedule.lean](../Mvba/Schedule.lean)'s discipline, kept for its
reason: the premises are fixed, type-checked and citable on their own, so
none can become a hypothesis because a proof needs it.

`grep -nE '^(def|structure|inductive|abbrev) ' Cadence/Chorus/Schedule.lean`
prints the whole list.

## What is assumed of a run

Four named premises, all relating an *environment* event — a label firing, a
clock reading — to a guard, a local record or the network's own facts.

* **(Δδ-justice)** — `TimedJustice`: every fair action of the hop table
  fires within its bound. A step that consumes another party's message is a
  `Δ`-row, a local step a `δ`-row, and the bound is split (Timed.lean's
  `BufferedFair`): the message part is due `Δ` after it was sent, the rule
  fires `δ` after its local gate opened. The paper's buffering sentence,
  Appendix C.3 (`subsection:chorus-protocol-overview`). A row is owed only for messages
  from **correct** senders (`Owed`), as the paper's network promises
  delivery only "between correct validators"
  (Proposition 5 (`prop:chorus-finalization-time`)'s proof).
* **(P-phase)** — `PhasePunctual`: the three phase markers fire at the
  slot's landmarks `D`, `D + Δ`, `D + 2Δ`, not earlier and not later.
* **The MVBA's timing** — `TimedMvbaAdmissible`: the MVBA's steps inside the
  run, with the clock carried along, satisfy the MVBA contract's own
  `Admissible`. Stated with the contract's field, restated nowhere. At the
  system's MVBA its one clause on the caller, the handoff of decided
  certificates, is derived from (Δδ-justice)'s handoff row
  (`relayed_of_timedJustice`), so only the MVBA's own scheduling is assumed.
* **The bridge** — `ValidBridge` ([Liveness.lean](Liveness.lean)), unchanged:
  it is not timing.

And the caller's four, the contract's antecedents: everyone participates
by `t` (`AllParticipateBy`), participation is synchronized within a
tolerance (`SyncParticipationWithin`), nobody abandons before finalizing
(`NoAbandonBeforeFinalizing`, C1), and nobody starts before `D − Δ`
(`NoEarlyStart`, C2).

## The gate checklist

A row's **gate** is the local condition its rule waits for, and it opens `δ`
before the rule is due. So a gate that mentioned protocol progress would let
the clause absorb it: "the rule fires `δ` after its gate opened" would then
say that progress happens. Every gate therefore mentions **only**

* the acting validator's own local state — its participation, `Active`; and
* the phase — the landmark its rule waits for.

`gate` below has one line per row, and each is checked against this list by
reading it. Everything else a rule's guard needs is either its network part
(owed `Δ` after it was sent) or protocol state that the proof has to
establish.

## What is assumed of the instance

The MVBA's timing premise is the MVBA contract's `Admissible` at an instance
`T : MVBATemporal … (S := mvbaSafety thM)`, and the claim consumes `T.ℓ`
only. At the system's MVBA, `T := Mvba.mvbaTemporal thM hqe sch.mvba vfin
hrot`, `T.ℓ` is `Mvba.Schedule.ℓ` by `rfl` (`mvbaTemporal_ℓ`) and
`T.Admissible` is `Mvba.Admissible`, the labelled form of `Mvba.Sync`
(`timedMvbaAdmissible_atMvba_iff`, `timedMvbaAdmissible_of_sync`). The
quorum family and `ViewOrderEnum` are hypotheses of the theorems to come,
as for the untimed claim.

## What this file does not do

Prove anything about the protocol. Its theorems are about its own
definitions: the hop table covers exactly the fair labels that are not
phase markers (`hop_isSome_iff`), the markers are exactly the three
landmarks' (`markerLabel_iff`), the two constants are the paper's at `δ = 0`
(`Lchorus_paper`, `Ltot_paper`), and the MVBA premise unfolds at the
system's instance. The proofs are stages S3 and S4 of
[Bounds.md](../../docs/Bounds.md) §6.4.6: `TotalityClaim` is `Chorus.totality`
([Totality.lean](Totality.lean)), `TimedTerminationClaim` is
`Chorus.timed_termination` ([TimedTermination.lean](TimedTermination.lean)). -/

namespace Chorus

open Cadence
-- Veil's `TotalOrder` on the clock is the scoped bridge from its linear
-- order ([Timed.lean](../Timed.lean)), as in [Mvba/Schedule.lean](../Mvba/Schedule.lean).
open scoped Cadence.Timed

/-! ## The phase markers, and the hop table -/

section Labels

variable {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}

/-- **The three phase markers.** They leave the hop table, as the MVBA's
`expire_timer` left its own: their timing is (P-phase), a punctual timer at
each landmark, and not a hop bound. -/
def MarkerLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice → Prop
  | .advance_to_deadline => True
  | .advance_to_fb_arm => True
  | .advance_to_mvba_arm => True
  | _ => False

/-- **The hop table.** `some .net` for a step whose guard consumes another
party's message or a certificate assembled from others' signatures (a
`Δ`-row), `some .loc` for a local step (a `δ`-row), `none` for a label under
no bound — the adversary's, the oracle step, the caller's three inputs, and
the three phase markers ((P-phase) times them).

* `Δ`: the proposer's chunk (`deliver_chunk_assigned`), others' votes
  (`aggregate_fastqc_*`, `fb_sign_*`), others' commit votes
  (`broadcast_commitqc_*`), others' fallback votes (the `mvba_propose`
  family on its `FBCert` trigger, Algorithm 5, line 36 (`line:fb-mvba-propose`)), the caster's chunk (`redisseminate_chunk`), a
  certificate someone else sent (`commit_assign_*`), a decided MVBA
  certificate (the handoff `accept_mvba_commitqc`, and the `CommitQC`
  route's handlers `on_mvba_commitqc_*`);
* `δ`: `record_chunk`, `vote`, `commit_sign_*`, `cast_fast_commit`,
  `cast_fallback_vote`, the `mvba_propose` family on its case-(a) trigger
  (Algorithm 5, line 23 (`line:fb-mvba-propose-fast`): the proposer's own complete fast meta-block,
  local state), the decision handlers `on_mvba_decide_*` and
  `mvba_terminate`, `cast_fb_commit`, `finalize_commit`, and the
  availability report `mvba_avail_ready` (a family, `avail`: it reads the
  validator's own chunk receipts).

**The proposal is two families, the paper's two rules** (F9). `mvba_propose`
is one label with both triggers, so `hop` gives it its `Δ` row and
`TimedJustice` adds the case-(a) rule as a `δ`-family (`proposeFast`). As one
`Δ`-row the case-(a) proposal would cost a second `Δ`: its trigger exists
only once the FastQCs have *arrived* (the `aggregate_fastqc_*` hop), so its
window cannot open before then.

**The decision handlers stay `δ`-rows.** Each fires on the acting validator's
*own* MVBA decision, a local output, and the certificates its bridge check
reads travel inside the decided value (the check holds at the decision by
`ValidBridge`'s completeness). The transfer of a decision to a validator
that did not decide first is the handoff row: a correct decision's
certificate reaches the MVBA of every correct validator within `Δ`, which is
the MVBA's own handoff premise (`Mvba.Relayed`, `Δ + ρ`) derived
(`relayed_of_timedJustice`). Its cost is the last term of `ℓ_MVBA` and is
not charged again here.

Written with a wildcard, so that an action added to the model lands on
`none`, which *weakens* the premise set rather than strengthening it;
`hop_isSome_iff` pins the coverage. -/
def hop : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice →
    Option Mvba.Hop
  | .deliver_chunk_assigned .. => some .net
  | .aggregate_fastqc_pos .. => some .net
  | .aggregate_fastqc_neg .. => some .net
  | .fb_sign_pos .. => some .net
  | .fb_sign_neg .. => some .net
  | .broadcast_commitqc_pos .. => some .net
  | .broadcast_commitqc_neg .. => some .net
  | .mvba_propose .. => some .net
  | .accept_mvba_commitqc .. => some .net
  | .on_mvba_commitqc_pos .. => some .net
  | .on_mvba_commitqc_neg .. => some .net
  | .redisseminate_chunk .. => some .net
  | .commit_assign_pos .. => some .net
  | .commit_assign_neg .. => some .net
  | .record_chunk .. => some .loc
  | .vote .. => some .loc
  | .commit_sign_pos .. => some .loc
  | .commit_sign_neg .. => some .loc
  | .cast_fast_commit .. => some .loc
  | .cast_fallback_vote .. => some .loc
  | .on_mvba_decide_pos .. => some .loc
  | .on_mvba_decide_neg .. => some .loc
  | .mvba_terminate .. => some .loc
  | .cast_fb_commit .. => some .loc
  | .finalize_commit .. => some .loc
  | .mvba_avail_ready .. => some .loc
  | _ => none

/-- **The table covers exactly the fair labels that are not phase markers.**
A label has a hop bound iff it is a `JusticeLabel` of
[Liveness.lean](Liveness.lean) and not one of the three markers; the case
split is over the model's own label type, so an action added to the model and
forgotten here is an error, not a silent omission. -/
theorem hop_isSome_iff
    (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) :
    (hop l).isSome ↔ JusticeLabel l ∧ ¬ MarkerLabel l := by
  cases l <;> simp [hop, JusticeLabel, ByzLabel, OracleLabel, InputLabel, MarkerLabel]

end Labels

/-! ## The schedule and the two constants -/

/-- **The Chorus schedule**: the MVBA's schedule — one `Δ` and one `δ` for the
whole run — plus the slot's deadline `D` (`s.deadline`). The deadline is any
value; its relation to the participation times is the caller's C2
(`NoEarlyStart`). -/
structure Schedule (view time : Type) [vord : TotalOrderWithMinimum view]
    [LinearOrder time] [AddCommMonoid time] where
  /-- The MVBA's schedule, whose `Δ` and `δ` Chorus shares. -/
  mvba : Mvba.Schedule view time
  /-- The slot's deadline. -/
  D : time
  /-- **A local step is no slower than a network hop**: `δ ≤ Δ`, true at the
  paper's `δ = 0`. A property of the timing model, like `0 < Δ`. It is what
  makes a `Δ`-row cost `Δ`: with its gate already open, a row's window is
  `ref N + max(Δ, δ)` (`BufferedFair` at `N = N'`), so without it every
  network hop whose gate opened first would cost `δ` (F10,
  [Bounds.md](../../docs/Bounds.md) §6.4.2). It implies the `δ ≤ Δ + ρ` that
  `relayed_of_timedJustice` takes. -/
  δ_le_Δ : mvba.δ ≤ mvba.Δ

section Constants

variable {time : Type} [LinearOrder time] [AddCommMonoid time]

/-- **The termination latency** `ℓ`, over the network bound `Δ`, the local
bound `δ` and the MVBA's `ℓ_MVBA`: the paper's `5Δ + ℓ_MVBA`
(Lemma 11 (`lemma:chorus-termination`)) plus the local steps the timeline counts.

The `δ`-count is `9`, along [Bounds.md](../../docs/Bounds.md) §6.4.3's
timeline from `M := max(t, GST)`, with the paper's outer case split at
`T₀`. Every `Δ`-row costs `Δ` because `δ ≤ Δ` (`Schedule.δ_le_Δ`).

* **to the MVBA proposals, `3δ`** (proven, [Timeline.lean](Timeline.lean)):
  the first-round vote (`δ`) by `M + Δ + δ`; the second-round vote, fast or
  fallback (`δ`), by `M + 2Δ + 2δ` — the fallback entry before it is a
  `Δ`-row whose message part is the votes, so it adds no `δ` of its own;
  then the proposal on a correct `FBCert`, a `Δ`-row, by `M + 3Δ + 2δ`, or,
  in case (a), a correct fast voter's FastQCs, a `Δ`-row, by `M + 3Δ + 2δ`
  and the proposal on them, a `δ`-row (F9): `t_M = M + 3Δ + 3δ`;
* **the decision** by `t_M + ℓ_MVBA` (`T.termination`);
* **to the fallback commit vote, `3δ`**: the decision handlers, the
  termination record, the vote;
* **to finalization, `δ`**: the commitment is a `Δ`-row on the commit votes,
  and the finalization one `δ`, so `T₀ = M + 4Δ + ℓ_MVBA + 7δ`;
* **the outer split, `2δ`**: if a correct validator finalizes by `T₀`,
  totality (`Ltot` at `d = Δ`: `Δ + 2δ`, proven as `totality`) finalizes
  everyone by `M + 5Δ + ℓ_MVBA + 9δ`; otherwise nobody has abandoned by `T₀` (C1) and
  the chain above finalizes everyone by `T₀`.

R7 fixed the count at `8` before any proof; S3's milestones put the case-(a)
proposals one `δ` later (F9), so it is `9`. S4 confirmed the rest: the
milestones as proven reach `T₀` with `7δ`, and the outer split adds `2δ`
(`Chorus.timed_termination`). F4 (the bound is loose by one `Δ`) is
confirmed and does not change this statement: `Chorus.timed_termination_tight`
proves `4Δ + ℓ_MVBA + 8δ` from the same premises, and implies it. -/
def Lchorus (Δ δ ℓM : time) : time :=
  5 • Δ + ℓM + 9 • δ

omit [LinearOrder time] in
/-- At `δ = 0`, the paper's instantaneous local computation, the latency is
the paper's `5Δ + ℓ_MVBA`. -/
theorem Lchorus_paper (Δ ℓM : time) : Lchorus Δ 0 ℓM = 5 • Δ + ℓM := by
  simp [Lchorus]

/-- **The totality latency** for participation synchronized within `d`: the
certificate's `Δ` or the late validator's start, whichever is later, then
the commitment and the finalization (`δ` each). [Bounds.md](../../docs/Bounds.md)
§6.4.4. The tolerance `d` is a parameter (F3): the Conductor leg decides
at which tolerance to consume it. -/
def Ltot (Δ δ d : time) : time :=
  max Δ d + 2 • δ

/-- At `δ = 0` and the paper's tolerance `d = Δ`, the latency is the paper's
`d_tot = Δ` (Proposition 4 (`prop:chorus-totality`)). -/
theorem Ltot_paper (Δ : time) : Ltot Δ 0 Δ = Δ := by
  simp [Ltot]

end Constants

namespace Schedule

variable {view time : Type} [vord : TotalOrderWithMinimum view]
  [LinearOrder time] [AddCommMonoid time]

/-- The network bound, the MVBA's. -/
abbrev Δ (sch : Schedule view time) : time := sch.mvba.Δ

/-- The local-step bound, the MVBA's. -/
abbrev δ (sch : Schedule view time) : time := sch.mvba.δ

/-- A row's bound: `Δ` for a network step, `δ` for a local one. -/
def bound (sch : Schedule view time) : Mvba.Hop → time
  | .net => sch.Δ
  | .loc => sch.δ

/-- `ℓ` at this schedule, over the MVBA's latency `ℓM` — which the claim
takes from the MVBA contract, `T.ℓ`, never from the MVBA's constants. -/
def ℓ (sch : Schedule view time) (ℓM : time) : time :=
  Lchorus sch.Δ sch.δ ℓM

/-- `d_tot` at this schedule, for a participation tolerance `d`. -/
def dtot (sch : Schedule view time) (d : time) : time :=
  Ltot sch.Δ sch.δ d

end Schedule

/-- **The slot's three landmarks.** The deadline `D`, the fallback arm
`D + Δ`, the MVBA arm `D + 2Δ` (the paper's arm times, stated in the network
bound; Algorithm 5 (`alg:fallback`)). -/
inductive Landmark where
  | deadline
  | fbArm
  | mvbaArm
  deriving DecidableEq

namespace Landmark

/-- The clock reading of each landmark. -/
def time {view time : Type} [vord : TotalOrderWithMinimum view] [LinearOrder time]
    [AddCommMonoid time] (sch : Schedule view time) : Landmark → time
  | .deadline => sch.D
  | .fbArm => sch.D + sch.Δ
  | .mvbaArm => sch.D + 2 • sch.Δ

/-- Each landmark's marker. -/
def marker {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type} :
    Landmark → Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice
  | .deadline => .advance_to_deadline
  | .fbArm => .advance_to_fb_arm
  | .mvbaArm => .advance_to_mvba_arm

/-- The phase is at or past the landmark: once there, it stays (the phase
only moves forward). -/
def Reached {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}
    [Chorus.Phase_EnumClass Phase]
    (s : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg
      Phase PathChoice)) : Landmark → Prop
  | .deadline => s.phase ≠ Phase_EnumClass.pre_deadline
  | .fbArm => s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm
  | .mvbaArm => s.phase = Phase_EnumClass.post_mvba_arm

end Landmark

/-- The markers are exactly the three landmarks'. -/
theorem markerLabel_iff {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}
    (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) :
    MarkerLabel l ↔ ∃ L : Landmark, l = L.marker := by
  constructor
  · intro h
    cases l <;> simp [MarkerLabel] at h
    · exact ⟨.deadline, rfl⟩
    · exact ⟨.fbArm, rfl⟩
    · exact ⟨.mvbaArm, rfl⟩
  · rintro ⟨L, rfl⟩
    cases L <;> trivial

/-! ## The premises, one named `Prop` each -/

section Runs

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
  {time : Type} [LinearOrder time] [AddCommMonoid time]

/-- A state of Chorus at the `Mvba` instance. -/
abbrev StateAtMvba (slot node nodeset merkle_root view Phase PathChoice : Type) :=
  Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
    (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
    (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)

/-- A label of Chorus at the `Mvba` instance. -/
abbrev LabelAtMvba (slot node nodeset merkle_root view Phase PathChoice : Type) :=
  Chorus.Label slot node nodeset merkle_root
    (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
    (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice

/-- A labelled **timed** run of Chorus at the `Mvba` instance: the object every
premise below is about. Its `toLRun` is [Liveness.lean](Liveness.lean)'s
`ChorusRun`. -/
abbrev TChorusRun
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)
    (time : Type) [LinearOrder time] :=
  TLRun (atMvba (slot := slot) (Phase := Phase) (PathChoice := PathChoice) thM) thS time

/-! ### The gates

One line per row, each only the acting validator's `Active` (its
participation) and the phase: the header's checklist. -/

/-- The MVBA proposal's gate: the proposer actively participates, and the MVBA
arm `D + 2Δ` has opened. The paper's fallback trigger may fire from the
fallback arm on; the gate is the later arm because the case-(a) trigger
(Algorithm 5, line 23 (`line:fb-mvba-propose-fast`)) waits for it, and [Bounds.md](../../docs/Bounds.md)
§6.4.3's timeline reaches the proposals only after it. -/
def proposeGate (i : node) (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) :
    Prop :=
  Active s i ∧ s.phase = Phase_EnumClass.post_mvba_arm

/-- **The gates.** A sending rule is gated on its sender's active participation
(Appendix C.3 (`subsection:chorus-protocol-overview`)), and a rule that waits for a landmark
on the landmark's phase. The processing rules (`record_chunk`,
`aggregate_fastqc_*`, the decision and certificate handlers, and the
availability report) have no participation gate, as in the model, and no
phase gate: the paper's decision handler is "upon `MVBA[s].decide(B′)`"
(Algorithm 5, line 37 (`line:fb-mvba-decide`)). -/
def gate : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice →
    StateAtMvba slot node nodeset merkle_root view Phase PathChoice → Prop
  | .deliver_chunk_assigned _ j _ => fun s => Active s j
  | .vote i => fun s => Active s i ∧ s.phase ≠ Phase_EnumClass.pre_deadline
  | .commit_sign_pos i .. => fun s => Active s i
  | .commit_sign_neg i .. => fun s => Active s i
  | .cast_fast_commit i => fun s => Active s i
  | .broadcast_commitqc_pos c .. => fun s => Active s c
  | .broadcast_commitqc_neg c .. => fun s => Active s c
  | .fb_sign_pos i .. => fun s => Active s i ∧
      (s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
  | .fb_sign_neg i .. => fun s => Active s i ∧
      (s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
  | .cast_fallback_vote i => fun s => Active s i ∧
      (s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
  | .mvba_propose i .. => proposeGate i
  | .redisseminate_chunk k .. => fun s => Active s k
  | .cast_fb_commit i _ => fun s => Active s i
  | .commit_assign_pos i .. => fun s => Active s i
  | .commit_assign_neg i .. => fun s => Active s i
  | .finalize_commit i => fun s => Active s i
  | _ => fun _ => True

/-! ### What a row is owed for: correct senders

The owed-conditions are [Liveness.lean](Liveness.lean)'s `Owed`,
`proposeOwed` and `relayOwed`, shared with the untimed `FJustice` so that
the two premises read alike: a row is owed only for messages from correct
senders, because the paper's network delivers "every message between
correct validators" within `Δ` after GST, and a Byzantine sender may send to
some validators only. -/

/-! ### (Δδ-justice), (P-phase), the MVBA's timing -/

/-- **(Δδ-justice)** — the timed form of `FJustice`, with the hop split. Every
row of the hop table other than the two families is `BufferedFair` at its
bound, gate and `Owed`; the proposal is one family per validator and value,
as in `FJustice`: if `i` can propose `v` throughout the window, with its
trigger owed and its gate open, `i` proposes `v` (for some MVBA successor
state) within it. The paper has two proposal rules, and so does the premise
(F9): on the fallback votes of a correct supermajority
(Algorithm 5, line 36 (`line:fb-mvba-propose`), a `Δ`-family, `propose`), and on the proposer's own
complete fast meta-block (Algorithm 5, line 23 (`line:fb-mvba-propose-fast`), a `δ`-family,
`proposeFast`: the FastQCs it reads are local once adopted). The handoff is one family per receiver, a `Δ`-row with no
gate (it processes a message): once a correct validator has decided, whose
decision output is the certificate's broadcast, `i` takes a transferred
certificate within `Δ` if it can throughout the window. This row is what
the MVBA's handoff premise is derived from (`relayed_of_timedJustice`). The
availability report is one family per validator and value, a `δ`-row with
no gate: once `i` holds `v`, it reports `AvailReady_i(v)` within `δ` of
its chunk wait being met. With the re-dissemination rows it is what the
MVBA's (Δ-avail) is to be derived from. It cannot be yet: the model's
re-dissemination is gated on its sender's participation at delivery, where
the paper sends inside the fallback-entry rule (F15,
[Bounds.md](../../docs/Bounds.md) §6.4.2), so (Δ-avail) stays assumed
inside `TimedMvbaAdmissible` until the model fix (R19,
[TODO.md](../../docs/TODO.md) § Liveness).

Each window is measured from `max(clk N, gst)` (`TLRun.ref`), so an
obligation pending at GST is due `Δ` (or `δ`) after it. Stated over plain
enabledness, as since R6: every fair action of the model fires once
(`justice_enabledMove`). -/
structure TimedJustice (sch : Schedule view time)
    (r : TChorusRun thS thM time) : Prop where
  rows : ∀ (l : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice) (h : Mvba.Hop),
    hop l = some h → ¬ FamilyLabel l →
      BufferedFair r (sch.bound h) sch.δ (Owed (nset := nset) (mvba := Mvba.mvbaSafety thM) thS l)
        (gate l) l
  propose : ∀ (i : node) (v : MetaBlock node merkle_root),
    BufferedFairFamily r sch.Δ sch.δ (CorrectFBCert (nset := nset))
      (proposeGate i) (fun l => ∃ mvba_next, l = .mvba_propose i v mvba_next)
  proposeFast : ∀ (i : node) (v : MetaBlock node merkle_root),
    BufferedFairFamily r sch.δ sch.δ
      (fun s => Chorus.complete_fast_metablock (nset := nset) (mvba := Mvba.mvbaSafety thM) i thS s)
      (proposeGate i) (fun l => ∃ mvba_next, l = .mvba_propose i v mvba_next)
  relay : ∀ i : node,
    BufferedFairFamily r sch.Δ sch.δ (relayOwed (nset := nset) (mvba := Mvba.mvbaSafety thM))
      (fun _ => True) (fun l => ∃ c mvba_next, l = .accept_mvba_commitqc i c mvba_next)
  avail : ∀ (i : node) (v : MetaBlock node merkle_root),
    BufferedFairFamily r sch.δ sch.δ (availOwed i v)
      (fun _ => True) (fun l => ∃ mvba_next, l = .mvba_avail_ready i v mvba_next)

/-- **(P-phase)** — the phase markers are punctual timers. For each landmark
`L`:

* **(P1) not early** — its marker fires only at a clock at or after `L`;
* **(P2) not late** — the phase has reached `L` at some index whose clock is
  at most `L`.

The clocks are synchronized throughout, so the clause holds before GST too,
as the MVBA's (T-timer) does. Termination uses only (P2). (P1) is part of
the timing model and is what a timed proposal-inclusion corollary would need
(the phase is `pre_deadline` until `D`). The untimed claim keeps the markers
weakly fair; the two classifications are separate. -/
def PhasePunctual (sch : Schedule view time) (r : TChorusRun thS thM time) : Prop :=
  ∀ L : Landmark,
    (∀ n, r.lbl n = L.marker → L.time sch ≤ r.clk n) ∧
    (∃ n, L.Reached (r.at' n) ∧ r.clk n ≤ L.time sch)

/-- The MVBA's projected timed run, as a run of the MVBA contract (`TimedRun`
at `mvbaSafety thM`): the timed projection with its labels forgotten. -/
noncomputable def mvbaTimedRun {r : TChorusRun thS thM time}
    (p : (mvbaComponent thS thM).Projection r.toLRun) :
    TimedRun (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      time (Mvba.mvbaSafety thM).init (Mvba.mvbaSafety thM).trans :=
  p.timed.toTimedRun (Mvba.mvbaSafety thM).init (Mvba.mvbaSafety thM).trans
    ⟨p.timed.holds, p.timed.starts⟩ (fun n => ⟨_, p.timed.steps n⟩)

/-- **The MVBA's timing premise**, the timed `MvbaAdmissible`: the run has a
projection onto the MVBA whose timed run — the MVBA's states at its steps,
each with the clock of the composed index at which the MVBA entered it, and
the composed run's GST — is admissible for the MVBA contract `T`. Stated
with the contract's own field `T.Admissible` and restated nowhere, so a
refinement of the MVBA's timing model reaches this leg only through `T`.

The projection is data, as in the untimed `MvbaAdmissible`: the composed run
records only the MVBA's post-states, so a premise about how its labels were
scheduled has to supply them; `Projection.ofScheduled` says one always exists
when the MVBA is stepped infinitely often.

**The handoff is derived (C15, R8).** At the system's MVBA, `T.Admissible`
includes `Mvba.Relayed`: the MVBA's caller hands a decided commit
certificate to every undecided correct validator within `Δ + ρ`, which the
supplement asks of the *composing* layer (Supplement, Lemma 13 (`lem:decision-propagation`)). In
the composed system that caller is Chorus, whose handoff row (`TimedJustice`'s
`relay`) delivers it: `relayed_of_timedJustice` derives the clause for every
projection, at every schedule with `δ ≤ Δ + ρ`, and
`timedMvbaAdmissible_of_rows` is this premise with the clause supplied. So
what a witness has to show of the MVBA is only its own three clauses. -/
def TimedMvbaAdmissible
    (T : MVBATemporal node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset time nset (fun i => nset.is_byz i = true) (S := Mvba.mvbaSafety thM))
    (r : TChorusRun thS thM time) : Prop :=
  ∃ p : (mvbaComponent thS thM).Projection r.toLRun, T.Admissible (mvbaTimedRun p)

/-- **The whole of what is assumed of a run's timing**: the three clauses.
The bridge `ValidBridge` is not timing and is a separate premise. -/
def Sync (sch : Schedule view time)
    (T : MVBATemporal node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset time nset (fun i => nset.is_byz i = true) (S := Mvba.mvbaSafety thM))
    (r : TChorusRun thS thM time) : Prop :=
  TimedJustice sch r ∧ PhasePunctual sch r ∧ TimedMvbaAdmissible T r

/-! ### The caller's conditions

The antecedents of `SlotConsensusWithTotality.bounded_termination` and
`totality`, over the model's own observables. Within Cadence the
composition discharges each: the glue participates at `open`
(Algorithm 1, line 17 (`line:participate`)), the Conductor's opening totality synchronizes the
starts (Lemma 15 (`lemma:conductor-totality`)), its integrity keeps them after `D − Δ`
(Lemma 12 (`lemma:conductor-integrity`)), and the glue abandons only after finalizing
(Algorithm 1, line 23 (`line:abandon`)). C1 is [Liveness.lean](Liveness.lean)'s
`NoAbandonBeforeFinalizing`, used as it is. -/

/-- **Every correct validator participates by `t`.** -/
def AllParticipateBy (t : time) (r : TChorusRun thS thM time) : Prop :=
  ∀ i, ¬ nset.is_byz i = true → ∃ n, r.clk n ≤ t ∧ (r.at' n).participating i = true

/-- **Participation synchronized within `d`** (Definition 5 (`def:delta-synchronized-participation`)
at tolerance `d`): once a correct validator participates at clock `c`, every
correct validator participates by `max(c, GST) + d`. The contract's
`SyncParticipation` is the case `d = Δ` (`syncParticipation_def`, with
`byGstBound` read as `max`). -/
def SyncParticipationWithin (d : time) (r : TChorusRun thS thM time) : Prop :=
  ∀ n i, ¬ nset.is_byz i = true → (r.at' n).participating i = true →
    ∀ j, ¬ nset.is_byz j = true →
      ∃ m, r.clk m ≤ max (r.clk n) r.gst + d ∧ (r.at' m).participating j = true

/-- **C2: nobody starts before `D − Δ`.** Whenever a correct validator
participates, the clock has reached `D − Δ`: `D ≤ clk + Δ`, the contract's
form, which needs no subtraction. The Conductor's integrity. -/
def NoEarlyStart (sch : Schedule view time) (r : TChorusRun thS thM time) : Prop :=
  ∀ n i, ¬ nset.is_byz i = true → (r.at' n).participating i = true → sch.D ≤ r.clk n + sch.Δ

/-! ## The targets, stated

Two `Prop`-valued definitions, asserted nowhere. Each is the contract field's
statement in the model's vocabulary: `finalized` is `local_committed`,
`participating` and `abandoned` the model's own relations, `byGstBound`'s
least upper bound written as `max`. -/

/-- **ℓ-termination, the target** (Lemma 11 (`lemma:chorus-termination`)). Under the
timing model at a schedule `sch` and an MVBA contract `T`, the bridge, and
the caller's conditions — participation synchronized within `Δ`, no
abandonment before finalizing (C1), no start before `D − Δ` (C2) — if every
correct validator participates by `t`, every correct validator finalizes at
some index whose clock is at most `max(t, GST) + ℓ`, with
`ℓ = 5Δ + T.ℓ + 9δ` (`Lchorus`).

The MVBA enters only through `T`: its `Admissible` and its `ℓ`. At the
system's MVBA, `T := Mvba.mvbaTemporal thM hqe sch.mvba vfin hrot`. -/
def TimedTerminationClaim (sch : Schedule view time)
    (T : MVBATemporal node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset time nset (fun i => nset.is_byz i = true) (S := Mvba.mvbaSafety thM))
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice) :
    Prop :=
  ∀ r : TChorusRun thS thM time, Sync sch T r → ValidBridge r.toLRun →
    SyncParticipationWithin sch.Δ r → NoAbandonBeforeFinalizing r.toLRun → NoEarlyStart sch r →
    ∀ t : time, AllParticipateBy t r →
      ∀ j, ¬ nset.is_byz j = true →
        ∃ n, r.clk n ≤ max t r.gst + sch.ℓ T.ℓ ∧ (r.at' n).local_committed j = true

/-- **d_tot-totality, the target** (Proposition 4 (`prop:chorus-totality`)), at a
participation tolerance `d` (F3). Under (Δδ-justice), participation
synchronized within `d` and no abandonment before finalizing (C1), if a
correct validator finalizes at an index with clock `c`, every correct
validator finalizes by `max(c, GST) + max(Δ, d) + 2δ` (`Ltot`). The
contract's `totality` is the case `d = Δ`, whose latency is `Δ + 2δ`, the
paper's `d_tot = Δ` at `δ = 0` (`Ltot_paper`).

It takes fewer premises than the contract's field allows: the proof needs
only the commitment and finalization rows, so neither the phase timers, nor
the MVBA, nor the bridge is a premise. -/
def TotalityClaim (sch : Schedule view time) (d : time)
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view) : Prop :=
  ∀ r : TChorusRun thS thM time, TimedJustice sch r →
    SyncParticipationWithin d r → NoAbandonBeforeFinalizing r.toLRun →
    ∀ n i, ¬ nset.is_byz i = true → (r.at' n).local_committed i = true →
      ∀ j, ¬ nset.is_byz j = true →
        ∃ m, r.clk m ≤ max (r.clk n) r.gst + sch.dtot d ∧ (r.at' m).local_committed j = true

end Runs

/-! ## At the system's MVBA

`T := Mvba.mvbaTemporal`, the instance [System.lean](../System.lean)'s MVBA
carries. Its `ℓ` is the MVBA schedule's, and its `Admissible` is the
labelled form of `Mvba.Sync`; both by definition. -/

section AtMvba

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time]
  [Archimedean time] [Fintype node]

omit [Inhabited merkle_root] cnt in
/-- The MVBA's `ℓ` at the system's instance is `Mvba.Schedule.ℓ`, by `rfl`. -/
theorem mvbaTemporal_ℓ (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : Mvba.LeaderRotation vfin sch.mvba.k thM) :
    (Mvba.mvbaTemporal thM hqe sch.mvba vfin hrot).ℓ = sch.mvba.ℓ vfin :=
  rfl

/-- At the system's instance the MVBA premise is `Mvba.Admissible` of the
projected timed run: the run has a projection with a labelling of the MVBA's
states and clocks that satisfies `Mvba.Sync`. By definition. -/
theorem timedMvbaAdmissible_atMvba_iff (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : Mvba.LeaderRotation vfin sch.mvba.k thM) (r : TChorusRun thS thM time) :
    TimedMvbaAdmissible (Mvba.mvbaTemporal thM hqe sch.mvba vfin hrot) r ↔
      ∃ p : (mvbaComponent thS thM).Projection r.toLRun,
        Mvba.Admissible sch.mvba thM (mvbaTimedRun p) :=
  Iff.rfl

/-- **The form a witness supplies.** A projection whose timed run satisfies
`Mvba.Sync` — the timed projection labelled by itself — makes the MVBA
premise hold at the system's instance. -/
theorem timedMvbaAdmissible_of_sync (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : Mvba.LeaderRotation vfin sch.mvba.k thM) {r : TChorusRun thS thM time}
    (p : (mvbaComponent thS thM).Projection r.toLRun) (h : Mvba.Sync sch.mvba p.timed) :
    TimedMvbaAdmissible (Mvba.mvbaTemporal thM hqe sch.mvba vfin hrot) r :=
  ⟨p, p.timed, fun _ => rfl, fun _ => rfl, rfl, h⟩

omit [Archimedean time] [Fintype node] in
/-- **C15: the MVBA's handoff premise is derived, not assumed.** In every run
satisfying (Δδ-justice), at every schedule whose local bound is at most a
retransmitted hop (`δ ≤ Δ + ρ`, the paper's `δ = 0` included), every
projection's timed run satisfies `Mvba.Relayed`: once a correct validator
`j` has decided `e`, any correct validator that can take a transferred
certificate on `e` does so within `Δ + ρ`.

The argument: if `decide i v e` stayed enabled for `Δ + ρ` after `j`
decided, then from the composed index at which that window opens, the
handoff row for `i` is owed (a correct validator has decided, and its
decision output is the broadcast) and enabled (with the certificate on
`(v, e)`), so it fires within `max(Δ, δ) ≤ Δ + ρ`, `i` decides, and `decide
i v e` is disabled inside the window after all. So the clause holds with its
antecedent false. -/
theorem relayed_of_timedJustice (sch : Schedule view time) (hδ : sch.δ ≤ sch.Δ + sch.mvba.ρ)
    {r : TChorusRun thS thM time} (hTJ : TimedJustice sch r)
    (p : (mvbaComponent thS thM).Projection r.toLRun) : Mvba.Relayed sch.mvba p.timed := by
  letI : MVBASafety node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset nset (fun i => nset.is_byz i = true) := Mvba.mvbaSafety thM
  intro i j v e hj K hen
  exfalso
  have hΔρ : sch.Δ ≤ sch.Δ + sch.mvba.ρ := le_add_of_nonneg_right sch.mvba.ρ_nonneg
  have hK0 : p.timed.clk K ≤ p.timed.ref K + (sch.Δ + sch.mvba.ρ) :=
    le_trans (p.timed.clk_le_ref K) (le_add_of_nonneg_right (le_trans sch.mvba.Δ_pos.le hΔρ))
  have hi := (decide_enabled_guards (hen K le_rfl hK0).1).1
  -- The window opens at the composed index `N₀` at which the MVBA entered `K`.
  set N₀ := p.entry K
  have href : p.timed.ref K = r.ref N₀ := rfl
  -- The antecedent, read at the composed indices of the window.
  have hcomp : ∀ n, N₀ ≤ n → r.clk n ≤ r.ref N₀ + (sch.Δ + sch.mvba.ρ) →
      Enabled (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)) thM
        (r.at' n).mvba_st (.decide i v e) ∧ (r.at' n).mvba_st.decided j e = true := fun n hn hc => by
    have hk := hen ((mvbaComponent thS thM).cover r.toLRun n) (p.le_cover_of_entry_le hn)
      (by rw [href]; exact le_trans (r.clk_le_of_le (p.entry_cover_le n)) hc)
    have hst : p.timed.at' ((mvbaComponent thS thM).cover r.toLRun n) = (r.at' n).mvba_st :=
      (p.proj_eq_run_cover n).symm
    rw [hst] at hk
    exact hk
  have hW : r.bufWindow N₀ N₀ sch.Δ sch.δ ≤ r.ref N₀ + (sch.Δ + sch.mvba.ρ) :=
    max_le (add_le_add le_rfl hΔρ) (add_le_add le_rfl hδ)
  -- The handoff row fires inside the window.
  obtain ⟨m, hm, ⟨c, mn, hl⟩, hcm⟩ := hTJ.relay i N₀ N₀ le_rfl
    (fun n hn hc => by
      obtain ⟨hen', hd⟩ := hcomp n hn (le_trans hc hW)
      have hg := decide_enabled_guards hen'
      refine ⟨⟨j, e, hj, hd⟩, fun _ => ?_⟩
      obtain ⟨st', htr'⟩ := hen'
      -- The certificate is on `e`'s entries; the MVBA takes it with `e` itself.
      have hacc : Mvba.Accept thM (r.at' n).mvba_st i (.commitqc v (thM.ent e)) st' :=
        ⟨e, rfl, htr'⟩
      refine ⟨_, ⟨.commitqc v (thM.ent e), st', rfl⟩,
        enabled_accept_mvba_commitqc hi (fun hf => ?_) hacc⟩
      obtain ⟨w, hw⟩ := qc_accepted_decided r.toLRun n hf
      exact hg.2 w hw)
    (fun _ _ _ => trivial)
  -- So `i` has decided inside the window, where `decide i v e` is still enabled.
  obtain ⟨w, e', x, -, -, htr⟩ := accept_mvba_commitqc_tr (hl ▸ r.steps m)
  exact (decide_enabled_guards (hcomp (m + 1) (by omega) (le_trans hcm hW)).1).2 x
    (Mvba.decide_effect htr)

/-- **The form a witness supplies, with the handoff derived.** A projection
whose timed run satisfies the MVBA's own three clauses — (Δ-justice),
(T-timer), (Δ-avail) — together with (Δδ-justice) of the composed run gives
the MVBA premise at the system's instance: its fourth clause, the caller's
handoff, is `relayed_of_timedJustice`. -/
theorem timedMvbaAdmissible_of_rows (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : Mvba.LeaderRotation vfin sch.mvba.k thM) (hδ : sch.δ ≤ sch.Δ + sch.mvba.ρ)
    {r : TChorusRun thS thM time} (hTJ : TimedJustice sch r)
    (p : (mvbaComponent thS thM).Projection r.toLRun)
    (hown : Mvba.BoundedJustice sch.mvba p.timed ∧ Mvba.TimerPunctual sch.mvba p.timed ∧
      Mvba.AvailWithin sch.mvba p.timed) :
    TimedMvbaAdmissible (Mvba.mvbaTemporal thM hqe sch.mvba vfin hrot) r :=
  timedMvbaAdmissible_of_sync hqe sch vfin hrot p
    ⟨hown.1, hown.2.1, hown.2.2, relayed_of_timedJustice sch hδ hTJ p⟩

end AtMvba

end Chorus

/-! ## The pinned trust base

The hop table's coverage, the markers, the two constants at `δ = 0`, and the
MVBA premise at the system's instance; the targets are definitions, so
nothing here asserts a bound. -/

/-- info: 'Chorus.hop_isSome_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Chorus.hop_isSome_iff

/-- info: 'Chorus.markerLabel_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Chorus.markerLabel_iff

/-- info: 'Chorus.Lchorus_paper' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Chorus.Lchorus_paper

/-- info: 'Chorus.Ltot_paper' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Chorus.Ltot_paper

/--
info: 'Chorus.mvbaTemporal_ℓ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.mvbaTemporal_ℓ

/--
info: 'Chorus.timedMvbaAdmissible_atMvba_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.timedMvbaAdmissible_atMvba_iff

/--
info: 'Chorus.timedMvbaAdmissible_of_sync' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.timedMvbaAdmissible_of_sync

/--
info: 'Chorus.relayed_of_timedJustice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.relayed_of_timedJustice

/--
info: 'Chorus.timedMvbaAdmissible_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.timedMvbaAdmissible_of_rows
