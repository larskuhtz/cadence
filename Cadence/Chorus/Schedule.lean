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
  system's MVBA its two clauses on the caller are derived from (Δδ-justice):
  the handoff of decided certificates from the decider's broadcast and the
  handoff row (`relayedWhileActive_of_timedJustice`, in
  [TimedTermination.lean](TimedTermination.lean)), and the availability shares
  (Δ-avail) from the availability row and the schedule's `Δ ≤ Δ_sync`
  (`availWithin_of_timedJustice`, in [TimedTermination.lean](TimedTermination.lean)).
  So the claim at the system's MVBA assumes of the MVBA only its own
  scheduling (`SyncAtMvba`).
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

* the acting validator's own local state — its participation, `Active`, the
  output of its own MVBA instance that its rule fires upon (the decision
  `cast_fb_commit` handles; F15, [Bounds.md](../../docs/Bounds.md) §6.4.2),
  and its own record `local_mvba_complete` that stands for that decided
  vector having arrived; and
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

open Classical in
/-- **The hop of a step that reads a message from sender `s`, taken by
`i`.** A message a validator sent itself is local to it: reading it costs a
local step, `.loc`, as much as any internal step. A message from anyone else
is a network hop, `.net`. The paper's own structure: a collector forms the
fallback commit certificate and broadcasts it
(Algorithm 5, lines 42–44 (`line:fb-collect-commit`–`line:fb-commit-broadcast`)), and
finalizes through Algorithm 5, line 45 (`line:fb-recv-commit`) on its own
broadcast. -/
noncomputable def rcvHop {node : Type} (i s : node) : Mvba.Hop :=
  if s = i then .loc else .net

/-- A validator's own message is a local read. -/
theorem rcvHop_self {node : Type} (i : node) : rcvHop i i = .loc := by
  simp [rcvHop]

/-- **The hop table.** `some .net` for a step that consumes a message another
party sent, or a certificate formed from others' signatures (a `Δ`-row),
`some .loc` for a local step (a `δ`-row), `none` for a label under no bound —
the adversary's, the oracle step, the caller's three inputs, and the three
phase markers ((P-phase) times them).

* `Δ`: the receivers' steps — a chunk (`record_chunk`), a vote
  (`receive_vote_*`), others' votes (`aggregate_fastqc_*`, `fb_sign_pos`),
  others' commit votes (`broadcast_commitqc_*`), others' fallback commit
  votes (`broadcast_fbcommitqc`), others' fallback votes (the `mvba_propose`
  family on its `FBCert` trigger, Algorithm 5, line 36 (`line:fb-mvba-propose`)),
  an MVBA commit certificate someone sent (the handoff
  `accept_mvba_commitqc`), and a chunk a fallback signer re-disseminated (the
  DA wait `cast_fb_commit` and the availability report `mvba_avail_ready`);
* `rcvHop`, by sender: a commitment proof (`commit_assign_*`) is a `Δ`-row
  when another validator sent it and a `δ`-row when the actor sent it
  itself, its own certificate being local state;
* `δ`: `vote`, `fb_sign_neg` (on the votes the validator has received,
  its own receipts), `commit_sign_*`, `cast_fast_commit`,
  `cast_fallback_vote`, the `mvba_propose` family on its case-(a) trigger
  (Algorithm 5, line 23 (`line:fb-mvba-propose-fast`): the proposer's own complete fast meta-block,
  local state), the decision handlers `on_mvba_decide_*`, `mvba_terminate`,
  the certificate's broadcast `send_mvba_cert` on the validator's own
  decision, and `finalize_commit`.

**A step that consumes a message is timed at its receiver.** A message is
on the network from its send on, and the step that acts on it is a
`Δ`-row whose owed-condition is that its sender is correct (`Owed`): it is
due `Δ` after the send, after GST. So a re-disseminated chunk is timed at
the two rules that read it (F15): the availability report
`mvba_avail_ready` (the family `avail`) and the fallback commit vote
`cast_fb_commit` (`fbCommit`, split at its trigger: the chunks are due `Δ`
after they were sent, the vote `δ` after the validator's own decision).

**The proposal is two families, the paper's two rules** (F9). `mvba_propose`
is one label with both triggers, so `hop` gives it its `Δ` row and
`TimedJustice` adds the case-(a) rule as a `δ`-family (`proposeFast`). As one
`Δ`-row the case-(a) proposal would cost a second `Δ`: its trigger exists
only once the FastQCs have *arrived* (the `aggregate_fastqc_*` hop), so its
window cannot open before then.

**The decision handlers stay `δ`-rows.** Each fires on the acting validator's
*own* MVBA decision, a local output, and the certificates its bridge check
reads travel inside the decided value (the check holds at the decision by
`ValidBridge`'s completeness). So does the broadcast of the decision's
commit certificate (`send_mvba_cert`); its receipt is the handoff row.

Written with a wildcard, so that an action added to the model lands on
`none`, which *weakens* the premise set rather than strengthening it;
`hop_isSome_iff` pins the coverage. -/
noncomputable def hop : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice →
    Option Mvba.Hop
  | .record_chunk .. => some .net
  | .receive_vote_pos .. => some .net
  | .receive_vote_neg .. => some .net
  | .aggregate_fastqc_pos .. => some .net
  | .aggregate_fastqc_neg .. => some .net
  | .fb_sign_pos .. => some .net
  | .broadcast_commitqc_pos .. => some .net
  | .broadcast_commitqc_neg .. => some .net
  | .broadcast_fbcommitqc .. => some .net
  | .mvba_propose .. => some .net
  | .accept_mvba_commitqc .. => some .net
  | .commit_assign_pos_fast i _ _ c => some (rcvHop i c)
  | .commit_assign_pos_fb i _ _ c _ => some (rcvHop i c)
  | .commit_assign_pos_mvba i _ _ s _ _ => some (rcvHop i s)
  | .commit_assign_neg_fast i _ c => some (rcvHop i c)
  | .commit_assign_neg_fb i _ c _ => some (rcvHop i c)
  | .commit_assign_neg_mvba i _ s _ _ => some (rcvHop i s)
  | .cast_fb_commit .. => some .net
  | .mvba_avail_ready .. => some .net
  | .vote .. => some .loc
  | .fb_sign_neg .. => some .loc
  | .commit_sign_pos .. => some .loc
  | .commit_sign_neg .. => some .loc
  | .cast_fast_commit .. => some .loc
  | .cast_fallback_vote .. => some .loc
  | .on_mvba_decide_pos .. => some .loc
  | .on_mvba_decide_neg .. => some .loc
  | .mvba_terminate .. => some .loc
  | .send_mvba_cert .. => some .loc
  | .finalize_commit .. => some .loc
  | _ => none

/-- **The labels with a clause of their own in `TimedJustice`**: the three
families of `FamilyLabel` (the proposal, the handoff, the availability
report) and the fallback commit vote, whose row is split at its trigger
(`fbCommit`). Every other row of the table is `TimedJustice.rows`. -/
def OwnClauseLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice → Prop
  | .mvba_propose .. => True
  | .accept_mvba_commitqc .. => True
  | .mvba_avail_ready .. => True
  | .cast_fb_commit .. => True
  | _ => False

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

/-- **The Chorus schedule** — the MVBA's schedule, the slot's deadline, and
two inequalities ([Premises.md](../../docs/Premises.md) §2.8).

The MVBA's schedule gives one `Δ` and one `δ` for the whole run; `D` is the
slot's deadline (`s.deadline`). The deadline is any value; its relation to
the participation times is the caller's C2 (`NoEarlyStart`). -/
structure Schedule (view time : Type) [vord : TotalOrderWithMinimum view]
    [LinearOrder time] [AddCommMonoid time] where
  /-- The MVBA's schedule, whose `Δ` and `δ` Chorus shares. -/
  mvba : Mvba.Schedule view time
  /-- The slot's deadline. -/
  D : time
  /-- **A local step is no slower than a network hop**
  ([Premises.md](../../docs/Premises.md) §2.8).

  `δ ≤ Δ`, true at the paper's `δ = 0`. A property of the timing model,
  like `0 < Δ`. It is what
  makes a `Δ`-row cost `Δ`: with its gate already open, a row's window is
  `ref N + max(Δ, δ)` (`BufferedFair` at `N = N'`), so without it every
  network hop whose gate opened first would cost `δ` (F10,
  [Bounds.md](../../docs/Bounds.md) §6.4.2). -/
  δ_le_Δ : mvba.δ ≤ mvba.Δ
  /-- **A local step is no slower than the MVBA's retransmission period**
  ([Premises.md](../../docs/Premises.md) §2.8).

  `δ ≤ ρ`, true at the paper's `δ = 0`. A correct decider broadcasts its
  commit certificate in a local step after its decision (`send_mvba_cert`),
  and the receiver's handoff is a `Δ`-row on it: `δ + Δ` after the
  decision. The MVBA's handoff premise allows `Δ + ρ`
  (`Mvba.Relayed`, Supplement, Lemma 13 (`lem:decision-propagation`)), so
  this is what lets `relayedWhileActive_of_timedJustice` derive it. -/
  δ_le_ρ : mvba.δ ≤ mvba.ρ
  /-- **The MVBA's availability window covers one Chorus network hop**
  ([Premises.md](../../docs/Premises.md) §2.8).

  `Δ ≤ Δ_sync`, a property of the composed timing model. The MVBA assumes
  that a correct validator holding a meta-block has, within `Δ_sync`, the
  availability shares its `Commit` waits for (Supplement, Section 1.2
  (`subsec:mvba-protocol`), "Availability-synchronization assumption").
  Chorus provides them in one network hop: each FallbackQC entry has a
  correct signer, which sent every validator its chunk when it signed
  (Algorithm 5, line 12 (`line:fb-redisseminate`)), before any validator
  could hold the meta-block, and the availability report is a `Δ`-row.
  With it, (Δ-avail) is derived, not assumed
  (`availWithin_of_timedJustice`); the `Δ_sync` the MVBA's latency charges
  is then at least the hop Chorus needs. True when the two layers share
  `Δ`, `Δ_sync = Δ`. -/
  Δ_le_Δsync : mvba.Δ ≤ mvba.Δsync

section Constants

variable {time : Type} [LinearOrder time] [AddCommMonoid time]

/-- **The termination latency** `ℓ`, over the network bound `Δ`, the local
bound `δ` and the MVBA's `ℓ_MVBA`: the paper's `5Δ + ℓ_MVBA`
(Lemma 11 (`lemma:chorus-termination`)) plus the local steps the timeline counts.

The `δ`-count is `9`, along [Bounds.md](../../docs/Bounds.md) §6.4.3's
timeline from `M := max(t, GST)`, with one case split at the fallback
commit votes' deadline `X_v`. Every `Δ`-row costs `Δ` because `δ ≤ Δ`
(`Schedule.δ_le_Δ`).

* **to the MVBA proposals, `4δ`** (proven, [Timeline.lean](Timeline.lean)):
  the first-round vote (`δ`) by `M + Δ + δ`; the votes received (a `Δ`-row
  each) by `M + 2Δ + δ`; the fallback entry, on the received votes (`δ`),
  by `M + 2Δ + 2δ`; the second-round vote, fast or fallback (`δ`), by
  `M + 2Δ + 3δ`; then the proposal on a correct `FBCert`, a `Δ`-row, by
  `M + 3Δ + 3δ`, or, in case (a), a correct fast voter's FastQCs, a
  `Δ`-row, by `M + 3Δ + 3δ` and the proposal on them, a `δ`-row (F9):
  `t_M = M + 3Δ + 4δ`;
* **the decision** by `t_M + ℓ_MVBA` (`T.termination`);
* **to the fallback commit vote, `3δ`**: the decision handlers, the
  termination record, the vote, by `X_v = M + 3Δ + ℓ_MVBA + 7δ`;
* **to finalization, `Δ + 2δ`**: the finalizer forms its own fallback commit
  certificate from the votes (a `Δ`-row), assigns its entries on it (its
  own send, a local read, `δ`), and finalizes (`δ`), so
  `T₀ = M + 4Δ + ℓ_MVBA + 9δ`;
* **the split, at `X_v`**: if a correct validator finalizes by `X_v`,
  totality (`Ltot` at `d = Δ`: `Δ + 2δ`, proven as `totality`) finalizes
  everyone by `M + 4Δ + ℓ_MVBA + 9δ`; otherwise nobody has abandoned by
  `X_v` (C1) and the chain above finalizes everyone by `T₀`. Both are
  within `M + 4Δ + ℓ_MVBA + 9δ` (`Chorus.timed_termination_tight`), so
  within `M + 5Δ + ℓ_MVBA + 9δ` (`Chorus.timed_termination`). -/
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

/-- Every row's bound is at most `Δ`. -/
theorem bound_le_Δ (sch : Schedule view time) (h : Mvba.Hop) : sch.bound h ≤ sch.Δ := by
  cases h
  · exact le_rfl
  · exact sch.δ_le_Δ

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

/-- The fallback commit vote's gate: its trigger, "upon `MVBA[s].decide(B′)`"
(Algorithm 5, line 37 (`line:fb-mvba-decide`)). The voter actively
participates, its own MVBA has decided `v` and nothing else (P11), and the
voter's own record `local_mvba_complete` holds, the model's shadow of the
decided vector having arrived. -/
def fbCommitGate (i : node) (v : MetaBlock node merkle_root)
    (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) : Prop :=
  Active s i ∧ Mvba.Decided s.mvba_st i v ∧
    (∀ v', Mvba.Decided s.mvba_st i v' → v' = v) ∧ s.local_mvba_complete i = true

/-- **The gates.** A sending rule is gated on its sender's active participation
(Appendix C.3 (`subsection:chorus-protocol-overview`)), and a rule that waits for a landmark
on the landmark's phase. The processing rules (`record_chunk`, the vote
receipts `receive_vote_*`, `aggregate_fastqc_*`, the decision handlers, the
certificate handoff, and the availability report) have no participation
gate, as in the model, and no phase gate: the paper's decision handler is
"upon `MVBA[s].decide(B′)`" (Algorithm 5, line 37 (`line:fb-mvba-decide`)). A
chunk is due at its recipient `Δ` after its correct sender sent it, whatever
the sender does next (F15, the proposer's half). The fallback commit vote
is gated on its trigger (`fbCommitGate`). -/
def gate : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice →
    StateAtMvba slot node nodeset merkle_root view Phase PathChoice → Prop
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
  | .send_mvba_cert i .. => fun s => Active s i
  | .cast_fb_commit i v => fbCommitGate i v
  | .broadcast_fbcommitqc c .. => fun s => Active s c
  | .commit_assign_pos_fast i .. => fun s => Active s i
  | .commit_assign_pos_fb i .. => fun s => Active s i
  | .commit_assign_pos_mvba i .. => fun s => Active s i
  | .commit_assign_neg_fast i .. => fun s => Active s i
  | .commit_assign_neg_fb i .. => fun s => Active s i
  | .commit_assign_neg_mvba i .. => fun s => Active s i
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

/-- **(Δδ-justice)** — each owed Chorus step happens within its hop's bound
([Premises.md](../../docs/Premises.md) §4.1).

The timed form of `FJustice`, with the hop split. Every row of the hop
table other than those with a clause of their own
(`OwnClauseLabel`) is `BufferedFair` at its bound, gate and `Owed`; the proposal is one family per validator and value,
as in `FJustice`: if `i` can propose `v` throughout the window, with its
trigger owed and its gate open, `i` proposes `v` (for some MVBA successor
state) within it. The paper has two proposal rules, and so does the premise
(F9): on the fallback votes of a correct supermajority
(Algorithm 5, line 36 (`line:fb-mvba-propose`), a `Δ`-family, `propose`), and on the proposer's own
complete fast meta-block (Algorithm 5, line 23 (`line:fb-mvba-propose-fast`), a `δ`-family,
`proposeFast`: the FastQCs it reads are local once adopted). The handoff is one family per receiver, a `Δ`-row with no
gate (it processes a message): once a correct validator has sent an MVBA
commit certificate (`send_mvba_cert`, or the re-broadcast of a finalization
on one), `i` takes a received certificate within `Δ` if it can throughout
the window. The
availability report is one family per validator and value, a `Δ`-row with
no gate: once `i` holds `v`, it reports `AvailReady_i(v)` within `Δ`, the
hop of the chunks its wait reads (F15). With the schedule's `Δ ≤ Δ_sync`
it is what the MVBA's (Δ-avail) is derived from
(`availWithin_of_timedJustice`). The fallback commit vote is a `Δ`-row split
at its trigger (`fbCommit`): its message part, the re-disseminated chunks of
its DA wait, is due `Δ` after they were sent, and the vote `δ` after its
gate, the validator's own decision (`fbCommitGate`), opened. Its untimed
owed-condition, the decision, is that gate.

Each window is measured from `max(clk N, gst)` (`TLRun.ref`), so an
obligation pending at GST is due `Δ` (or `δ`) after it. Stated over plain
enabledness, as since R6: every fair action of the model fires once
(`justice_enabledMove`). -/
structure TimedJustice (sch : Schedule view time)
    (r : TChorusRun thS thM time) : Prop where
  rows : ∀ (l : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice) (h : Mvba.Hop),
    hop l = some h → ¬ OwnClauseLabel l →
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
    BufferedFairFamily r sch.Δ sch.δ (relayOwed (nset := nset))
      (fun _ => True) (fun l => ∃ s c mvba_next, l = .accept_mvba_commitqc i s c mvba_next)
  avail : ∀ (i : node) (v : MetaBlock node merkle_root),
    BufferedFairFamily r sch.Δ sch.δ (availOwed i v)
      (fun _ => True) (fun l => ∃ mvba_next, l = .mvba_avail_ready i v mvba_next)
  fbCommit : ∀ (i : node) (v : MetaBlock node merkle_root),
    BufferedFair r sch.Δ sch.δ (fun _ => True) (fbCommitGate i v) (.cast_fb_commit i v)

/-- **(P-phase)** — the slot's phase timers fire on time
([Premises.md](../../docs/Premises.md) §4.2).

The phase markers are punctual timers. For each landmark `L`:

* **(P1) not early** — its marker fires only at a clock at or after `L`;
* **(P2) not late** — the phase has reached `L` at some index whose clock is
  at most `L`.

The clocks are synchronized throughout, so the clause holds before GST too,
as the MVBA's (T-timer) does. Termination uses only (P2). Censorship
resistance uses (P1): the phase is `pre_deadline` until `D`
(`Chorus.phase_pre_of_lt`, in `Composed.censorship`). The untimed claim keeps the markers
weakly fair; the two classifications are separate. -/
def PhasePunctual (sch : Schedule view time) (r : TChorusRun thS thM time) : Prop :=
  ∀ L : Landmark,
    (∀ n, r.lbl n = L.marker → L.time sch ≤ r.clk n) ∧
    (∃ n, L.Reached (r.at' n) ∧ r.clk n ≤ L.time sch)

/-- **(P-incl) A chunk due by the deadline is recorded** —
the paper's "by the deadline" read inclusively
([Premises.md](../../docs/Premises.md) §4.8).

Proposition 3 (`prop:honest-positive-entry`) has every correct
validator receive a correct proposer's chunk "by the deadline" and
set its positive entry before voting. A chunk sent at `D − Δ` may
arrive exactly at `D`, where the deadline marker may also fire;
the paper counts the chunk as on time without saying so (P19).
This premise states that reading: a chunk a correct proposer has
sent a correct validator at an index whose reference time
`max(clk, GST)` is at most `D − Δ`, so that it is due at its recipient by
`D`, is recorded (`record_chunk`). In an actual run: messages delivered
by the deadline are processed before the deadline handler. -/
def DeadlineInclusive (sch : Schedule view time)
    (r : TChorusRun thS thM time) : Prop :=
  ∀ n (i j : node) (m : merkle_root), ¬ nset.is_byz i = true → ¬ nset.is_byz j = true →
    thS.is_proposer j = true →
    (r.at' n).msg_chunk j i j m = true →
    r.ref n + sch.Δ ≤ sch.D →
    ∃ k m', (r.at' k).local_entry_pos i j m' = true

/-- The MVBA's projected timed run, as a run of the MVBA contract (`TimedRun`
at `mvbaSafety thM`): the timed projection with its labels forgotten. -/
noncomputable def mvbaTimedRun {r : TChorusRun thS thM time}
    (p : (mvbaComponent thS thM).Projection r.toLRun) :
    TimedRun (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      time (Mvba.mvbaSafety thM).init (Mvba.mvbaSafety thM).trans :=
  p.timed.toTimedRun (Mvba.mvbaSafety thM).init (Mvba.mvbaSafety thM).trans
    ⟨p.timed.holds, p.timed.starts⟩ (fun n => ⟨_, p.timed.steps n⟩)

/-- **The MVBA's timing premise** — the MVBA's steps inside the run meet the
MVBA contract's timing model ([Premises.md](../../docs/Premises.md) §4.3).

The timed `MvbaAdmissible`: the run has a projection onto the MVBA whose
timed run — the MVBA's states at its steps,
each with the clock of the composed index at which the MVBA entered it, and
the composed run's GST — is admissible for the MVBA contract `T`. Stated
with the contract's own field `T.Admissible` and restated nowhere, so a
refinement of the MVBA's timing model reaches this leg only through `T`.

The projection is data, as in the untimed `MvbaAdmissible`: the composed run
records only the MVBA's post-states, so a premise about how its labels were
scheduled has to supply them; `Projection.ofScheduled` says one always exists
when the MVBA is stepped infinitely often.

**The caller's two clauses are derived.** At the system's MVBA,
`T.Admissible` includes two clauses that the supplement asks of the
*composing* layer, Chorus:

* `Mvba.Relayed` (C15, R8): while a correct decider takes part (it has
  proposed and not abandoned), its decided commit certificate reaches every
  undecided correct validator within `Δ + ρ` (Supplement, Lemma 13
  (`lem:decision-propagation`)). The decider's `send_mvba_cert` row, gated
  on its own participation, broadcasts it within `δ`, and Chorus's handoff
  row (`TimedJustice`'s `relay`) delivers it `Δ` later; with the schedule's
  `δ ≤ ρ`: `relayedWhileActive_of_timedJustice`.
* `Mvba.AvailWithin`, (Δ-avail) (F15, R19): a correct validator holding a
  meta-block is `AvailReady` for it within `Δ_sync`. Each FallbackQC entry's
  correct signer sent the chunks when it signed, and the availability row
  reports within `Δ ≤ Δ_sync`: `availWithin_of_timedJustice`.

`timedMvbaAdmissible_of_rows` is this premise with both supplied, and
`SyncAtMvba` the timing model at the system's MVBA with only the MVBA's own
two clauses, (Δ-justice) and (T-timer), assumed of the MVBA
(`MvbaOwnTiming`). -/
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

/-- **Every correct validator participates by `t`**
([Premises.md](../../docs/Premises.md) §6.1). -/
def AllParticipateBy (t : time) (r : TChorusRun thS thM time) : Prop :=
  ∀ i, ¬ nset.is_byz i = true → ∃ n, r.clk n ≤ t ∧ (r.at' n).participating i = true

/-- **Participation synchronized within `d`** — once one correct validator
participates at `c`, all do by `max(c, GST) + d`
([Premises.md](../../docs/Premises.md) §6.4).

Definition 5 (`def:delta-synchronized-participation`) at tolerance `d`.
The contract's `SyncParticipation` is the case `d = Δ`
(`syncParticipation_def`, with `byGstBound` read as `max`). -/
def SyncParticipationWithin (d : time) (r : TChorusRun thS thM time) : Prop :=
  ∀ n i, ¬ nset.is_byz i = true → (r.at' n).participating i = true →
    ∀ j, ¬ nset.is_byz j = true →
      ∃ m, r.clk m ≤ max (r.clk n) r.gst + d ∧ (r.at' m).participating j = true

/-- **C2** — no correct validator participates before `D − Δ`
([Premises.md](../../docs/Premises.md) §6.3).

Whenever a correct validator participates, the clock has reached `D − Δ`:
`D ≤ clk + Δ`, the contract's form, which needs no subtraction. The
Conductor's integrity. -/
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

/-- **The MVBA's own scheduling** — the MVBA's steps inside the run meet the
MVBA's own two timing clauses ([Premises.md](../../docs/Premises.md) §4.3).

The run has a projection onto the MVBA whose timed run satisfies the two clauses the MVBA's timing model assumes of
its own steps, (Δ-justice) (`Mvba.BoundedJustice`) and (T-timer)
(`Mvba.TimerPunctual`). The MVBA's two clauses on its caller, the handoff
and (Δ-avail), are not here: Chorus is the caller, and its rows provide
them (`timedMvbaAdmissible_of_rows`). -/
def MvbaOwnTiming (sch : Schedule view time) (r : TChorusRun thS thM time) : Prop :=
  ∃ p : (mvbaComponent thS thM).Projection r.toLRun,
    Mvba.BoundedJustice sch.mvba p.timed ∧ Mvba.TimerPunctual sch.mvba p.timed

/-- **The timing model at the system's MVBA**: (Δδ-justice), (P-phase), and
the MVBA's own scheduling. The MVBA's two clauses on its caller are not
assumed: `sync_of_syncAtMvba` derives `Sync` at `T := Mvba.mvbaTemporal`
from it and the bridge. -/
def SyncAtMvba (sch : Schedule view time) (r : TChorusRun thS thM time) : Prop :=
  TimedJustice sch r ∧ PhasePunctual sch r ∧ MvbaOwnTiming sch r

/-- **ℓ-termination at the system's MVBA, the target**: `TimedTerminationClaim`
at `T := Mvba.mvbaTemporal`, whose `ℓ` is the MVBA schedule's
(`mvbaTemporal_ℓ`), with `Sync` read as `SyncAtMvba`: the MVBA's timing
premise is its own two clauses only. -/
def TimedTerminationClaimAtMvba (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view) :
    Prop :=
  ∀ r : TChorusRun thS thM time, SyncAtMvba sch r → ValidBridge r.toLRun →
    SyncParticipationWithin sch.Δ r → NoAbandonBeforeFinalizing r.toLRun → NoEarlyStart sch r →
    ∀ t : time, AllParticipateBy t r →
      ∀ j, ¬ nset.is_byz j = true →
        ∃ n, r.clk n ≤ max t r.gst + sch.ℓ (sch.mvba.ℓ vfin) ∧ (r.at' n).local_committed j = true

end AtMvba

end Chorus

/-! ## The pinned trust base

The hop table's coverage, the markers, the two constants at `δ = 0`, and the
MVBA premise at the system's instance; the targets are definitions, so
nothing here asserts a bound. -/

/--
info: 'Chorus.hop_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
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


