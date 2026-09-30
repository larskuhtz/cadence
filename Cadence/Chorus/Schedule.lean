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
  `subsection:chorus-protocol-overview`. A row is owed only for messages
  from **correct** senders (`Owed`), as the paper's network promises
  delivery only "between correct validators"
  (`prop:chorus-finalization-time`'s proof).
* **(P-phase)** — `PhasePunctual`: the three phase markers fire at the
  slot's landmarks `D`, `D + Δ`, `D + 2Δ`, not earlier and not later.
* **The MVBA's timing** — `TimedMvbaAdmissible`: the MVBA's steps inside the
  run, with the clock carried along, satisfy the MVBA contract's own
  `Admissible`. Stated with the contract's field, restated nowhere.
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
[Bounds.md](../../docs/Bounds.md) §6.4.6. -/

namespace Chorus

open Cadence
-- Veil's `TotalOrder` on the clock is the scoped bridge from its linear
-- order ([Timed.lean](../Timed.lean)), as in [Mvba/Schedule.lean](../Mvba/Schedule.lean).
open scoped Cadence.Timed

/-! ## The phase markers, and the hop table -/

section Labels

variable {slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice : Type}

/-- **The three phase markers.** They leave the hop table, as the MVBA's
`expire_timer` left its own: their timing is (P-phase), a punctual timer at
each landmark, and not a hop bound. -/
def MarkerLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice → Prop
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
  family, through `FBCert`), the caster's chunk (`redisseminate_chunk`), a
  certificate someone else sent (`commit_assign_*`);
* `δ`: `record_chunk`, `vote`, `commit_sign_*`, `cast_fast_commit`,
  `cast_fallback_vote`, the decision handlers `on_mvba_decide_*` and
  `mvba_terminate`, `cast_fb_commit`, `finalize_commit`.

**The decision handlers stay `δ`-rows.** Each fires on the acting validator's
*own* MVBA decision, a local output, and the certificates its bridge check
reads travel inside the decided value (the check holds at the decision by
`ValidBridge`'s completeness). The transfer of a decision to a validator
that did not decide first is the MVBA's own `decide` step, a network hop
inside the MVBA since step 5b ((N3); `Mvba.BoundedJustice.decisions`), so its
cost is inside `ℓ_MVBA` and not charged again here.

Written with a wildcard, so that an action added to the model lands on
`none`, which *weakens* the premise set rather than strengthening it;
`hop_isSome_iff` pins the coverage. -/
def hop : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice →
    Option Mvba.Hop
  | .deliver_chunk_assigned .. => some .net
  | .aggregate_fastqc_pos .. => some .net
  | .aggregate_fastqc_neg .. => some .net
  | .fb_sign_pos .. => some .net
  | .fb_sign_neg .. => some .net
  | .broadcast_commitqc_pos .. => some .net
  | .broadcast_commitqc_neg .. => some .net
  | .mvba_propose .. => some .net
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
  | _ => none

/-- **The table covers exactly the fair labels that are not phase markers.**
A label has a hop bound iff it is a `JusticeLabel` of
[Liveness.lean](Liveness.lean) and not one of the three markers; the case
split is over the model's own label type, so an action added to the model and
forgotten here is an error, not a silent omission. -/
theorem hop_isSome_iff
    (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) :
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

section Constants

variable {time : Type} [LinearOrder time] [AddCommMonoid time]

/-- **The termination latency** `ℓ`, over the network bound `Δ`, the local
bound `δ` and the MVBA's `ℓ_MVBA`: the paper's `5Δ + ℓ_MVBA`
(`lemma:chorus-termination`) plus the local steps the timeline counts.

The `δ`-count is `8`, along [Bounds.md](../../docs/Bounds.md) §6.4.3's
timeline from `M := max(t, GST)`, with the paper's outer case split at
`T₀`:

* **to the MVBA proposals, `2δ`**: the first-round vote (`δ`) by `M + Δ + δ`,
  the fallback vote (`δ`) by `M + 2Δ + 2δ` — the fallback entry before it
  is a `Δ`-row whose message part is the votes, so it adds no `δ` of its
  own — and the proposal, a `Δ`-row on the fallback votes, by
  `t_M = M + 3Δ + 2δ`;
* **the decision** by `t_M + ℓ_MVBA` (`T.termination`);
* **to the fallback commit vote, `3δ`**: the decision handlers, the
  termination record, the vote;
* **to finalization, `δ`**: the commitment is a `Δ`-row on the commit votes,
  and the finalization one `δ`, so `T₀ = M + 4Δ + ℓ_MVBA + 6δ`;
* **the outer split, `2δ`**: if a correct validator finalizes by `T₀`,
  totality (`Ltot` at `d = Δ`: `Δ + 2δ`) finalizes everyone by
  `M + 5Δ + ℓ_MVBA + 8δ`; otherwise nobody has abandoned by `T₀` (C1) and
  the chain above finalizes everyone by `T₀`.

A bound fixed here before the proof; S3–S4 confirm it or restate it before
the instance, as `Mvba.Lcert` was. F4 (the bound looks loose by one `Δ`) is
open and does not change this statement: a sharper lemma would imply it. -/
def Lchorus (Δ δ ℓM : time) : time :=
  5 • Δ + ℓM + 8 • δ

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
`d_tot = Δ` (`prop:chorus-totality`). -/
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
bound; `alg:fallback`). -/
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
def marker {slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice : Type} :
    Landmark → Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice
  | .deadline => .advance_to_deadline
  | .fbArm => .advance_to_fb_arm
  | .mvbaArm => .advance_to_mvba_arm

/-- The phase is at or past the landmark: once there, it stays (the phase
only moves forward). -/
def Reached {slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice : Type}
    [Chorus.Phase_EnumClass Phase]
    (s : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg
      Phase PathChoice)) : Landmark → Prop
  | .deadline => s.phase ≠ Phase_EnumClass.pre_deadline
  | .fbArm => s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm
  | .mvbaArm => s.phase = Phase_EnumClass.post_mvba_arm

end Landmark

/-- The markers are exactly the three landmarks'. -/
theorem markerLabel_iff {slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice : Type}
    (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) :
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
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (node → Option merkle_root) view}
  {time : Type} [LinearOrder time] [AddCommMonoid time]

/-- A state of Chorus at the `Mvba` instance. -/
abbrev StateAtMvba (slot node nodeset merkle_root view Phase PathChoice : Type) :=
  Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
    (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
    (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)

/-- A label of Chorus at the `Mvba` instance. -/
abbrev LabelAtMvba (slot node nodeset merkle_root view Phase PathChoice : Type) :=
  Chorus.Label slot node nodeset merkle_root
    (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
    (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice

/-- A labelled **timed** run of Chorus at the `Mvba` instance: the object every
premise below is about. Its `toLRun` is [Liveness.lean](Liveness.lean)'s
`ChorusRun`. -/
abbrev TChorusRun
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view)
    (time : Type) [LinearOrder time] :=
  TLRun (atMvba (slot := slot) (Phase := Phase) (PathChoice := PathChoice) thM) thS time

/-! ### The gates

One line per row, each only the acting validator's `Active` (its
participation) and the phase: the header's checklist. -/

/-- The MVBA proposal's gate: the proposer actively participates, and the MVBA
arm `D + 2Δ` has opened. The paper's fallback trigger may fire from the
fallback arm on; the gate is the later arm because the case-(a) trigger
(`line:fb-mvba-propose-fast`) waits for it, and [Bounds.md](../../docs/Bounds.md)
§6.4.3's timeline reaches the proposals only after it. -/
def proposeGate (i : node) (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) :
    Prop :=
  Active s i ∧ s.phase = Phase_EnumClass.post_mvba_arm

/-- **The gates.** A sending rule is gated on its sender's active participation
(`subsection:chorus-protocol-overview`), and a rule that waits for a landmark
on the landmark's phase. The processing rules (`record_chunk`,
`aggregate_fastqc_*`, and the decision handlers apart from their phase) have
no participation gate, as in the model. -/
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
  | .on_mvba_decide_pos .. => fun s => s.phase = Phase_EnumClass.post_mvba_arm
  | .on_mvba_decide_neg .. => fun s => s.phase = Phase_EnumClass.post_mvba_arm
  | .mvba_terminate .. => fun s => s.phase = Phase_EnumClass.post_mvba_arm
  | .redisseminate_chunk k .. => fun s => Active s k
  | .cast_fb_commit i => fun s => Active s i ∧ s.phase = Phase_EnumClass.post_mvba_arm
  | .commit_assign_pos i .. => fun s => Active s i
  | .commit_assign_neg i .. => fun s => Active s i
  | .finalize_commit i => fun s => Active s i
  | _ => fun _ => True

/-! ### What a row is owed for: correct senders

The paper's network delivers "every message between correct validators"
within `Δ` after GST. The model's network relations hold from a message's
first delivery to anyone, a Byzantine sender's included, so a `Δ`-row that
consumes a Byzantine validator's message would demand a delivery the paper
does not promise: a Byzantine voter may send its vote to some validators
only. `Owed` is the condition under which the paper's network owes the
row's delivery, per label: the messages it consumes came from correct
validators. Each is a fact about who sent a message, never a protocol
conclusion. -/

/-- A correct supermajority has broadcast its first-round votes. -/
def CorrectVotesCast (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) : Prop :=
  ∃ q, nset.supermajority q ∧ Mvba.CorrectQuorum (node := node) q ∧
    ∀ r, nset.member r q = true → s.msg_vote_cast r = true

/-- A correct supermajority has broadcast its fallback votes: `FBCert` from
correct senders. -/
def CorrectFBCert (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) : Prop :=
  ∃ q, nset.supermajority q ∧ Mvba.CorrectQuorum (node := node) q ∧
    ∀ r, nset.member r q = true → s.msg_fallback_sig r = true

/-- A correct supermajority has broadcast its fallback commit votes:
`fbCommitQC` from correct senders. -/
def CorrectFbCommitQC (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) :
    Prop :=
  ∃ q, nset.supermajority q ∧ Mvba.CorrectQuorum (node := node) q ∧
    ∀ r, nset.member r q = true → s.msg_fbcommit_sig r = true

/-- `f+1` correct validators hold their chunk under `(j, m)`: the data is
decodable from correct holders. -/
def CorrectChunkQuorum (j : node) (m : merkle_root)
    (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) : Prop :=
  ∃ q, nset.greater_than_third q ∧ Mvba.CorrectQuorum (node := node) q ∧
    ∀ r, nset.member r q = true → s.msg_chunk_received r j m = true

/-- The MVBA proposal is owed when its trigger came from correct senders:
`FBCert` from a correct supermajority, or the proposer's own complete fast
meta-block, which is local. The certificates of a particular value need no
condition: if `i` proposes any value, every member of the family is disabled
for `i`. -/
def proposeOwed (i : node) (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) :
    Prop :=
  CorrectFBCert s ∨
    Chorus.complete_fast_metablock (nset := nset) (mvba := Mvba.mvbaSafety thM) i thS s

/-- **What a row is owed for.** Per label, the condition under which the
environment owes the step at all.

* `Δ`-rows over a quorum parameter: the quorum is correct;
* `fb_sign_pos`: also the `2f+1` votes its guard counts, from correct voters;
* the proposal: its trigger from correct senders (`proposeOwed`);
* `redisseminate_chunk`: the data decodable from correct holders;
* `commit_assign_*`: a commitment proof a correct validator sent — a correct
  validator's finalization re-broadcasts its proof
  (`line:fast-rebroadcast-commitqc`, `line:fb-commit-rebroadcast`), and the
  fallback commit certificate from correct commit voters, over the decided
  entry;
* `cast_fb_commit`: the voter has itself decided. The model's guard reads
  the shared `mvba_complete`, which the first validator to decide sets; the
  paper's rule fires on the voter's own decision (`line:fb-commitvote`).
  Without this line the row would owe a vote from a validator whose MVBA has
  not decided yet;
* everything else: nothing (`True`). The chunk's delivery has a correct
  proposer by its guard, and the decision handlers and `mvba_terminate` fire
  on the validator's own decision by theirs. -/
def Owed : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice →
    StateAtMvba slot node nodeset merkle_root view Phase PathChoice → Prop
  | .aggregate_fastqc_pos _ _ _ q => fun _ => Mvba.CorrectQuorum (node := node) q
  | .aggregate_fastqc_neg _ _ q => fun _ => Mvba.CorrectQuorum (node := node) q
  | .broadcast_commitqc_pos _ _ _ q => fun _ => Mvba.CorrectQuorum (node := node) q
  | .broadcast_commitqc_neg _ _ q => fun _ => Mvba.CorrectQuorum (node := node) q
  | .fb_sign_pos _ _ _ q qc => fun s => Mvba.CorrectQuorum (node := node) q ∧
      Mvba.CorrectQuorum (node := node) qc ∧ CorrectVotesCast s
  | .fb_sign_neg _ _ qv => fun _ => Mvba.CorrectQuorum (node := node) qv
  | .mvba_propose i .. => proposeOwed (thS := thS) (thM := thM) i
  | .redisseminate_chunk _ _ j m => CorrectChunkQuorum j m
  | .commit_assign_pos _ j m => fun s =>
      (∃ k, ¬ nset.is_byz k = true ∧ s.local_committed k = true ∧
        s.local_committed_pos k j m = true) ∨
      (CorrectFbCommitQC s ∧ s.mvba_decided_pos j m = true)
  | .commit_assign_neg _ j => fun s =>
      (∃ k, ¬ nset.is_byz k = true ∧ s.local_committed k = true ∧
        s.local_committed_neg k j = true) ∨
      (CorrectFbCommitQC s ∧ s.mvba_decided_neg j = true)
  | .cast_fb_commit i => fun s => ∃ v, (Mvba.mvbaSafety thM).decided s.mvba_st i v
  | _ => fun _ => True

/-! ### (Δδ-justice), (P-phase), the MVBA's timing -/

/-- **(Δδ-justice)** — the timed form of `FJustice`, with the hop split. Every
row of the hop table other than the proposal is `BufferedFair` at its bound,
gate and `Owed`; the proposal is one family per validator and value, as in
`FJustice`: if `i` can propose `v` throughout the window, with its trigger
owed and its gate open, `i` proposes `v` (for some MVBA successor state)
within it.

Each window is measured from `max(clk N, gst)` (`TLRun.ref`), so an
obligation pending at GST is due `Δ` (or `δ`) after it. Stated over plain
enabledness, as since R6: every fair action of the model fires once
(`justice_enabledMove`). -/
structure TimedJustice (sch : Schedule view time)
    (r : TChorusRun thS thM time) : Prop where
  rows : ∀ (l : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice) (h : Mvba.Hop),
    hop l = some h → ¬ ProposeLabel l →
      BufferedFair r (sch.bound h) sch.δ (Owed (thS := thS) (thM := thM) l) (gate l) l
  propose : ∀ (i : node) (v : node → Option merkle_root),
    BufferedFairFamily r sch.Δ sch.δ (proposeOwed (thS := thS) (thM := thM) i) (proposeGate i)
      (fun l => ∃ mvba_next, l = .mvba_propose i v mvba_next)

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
    TimedRun (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
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

**What stays assumed here, and why (C15).** At the system's MVBA,
`T.Admissible` includes `Mvba.BoundedJustice.decisions`: a decided commit
certificate reaches every undecided correct validator within `Δ + ρ`, which
the supplement asks of the *composing* layer (`lem:decision-propagation`).
In the composed system that delivery is Chorus's. It is assumed here, not
derived from Chorus's steps, because the Chorus model has no step that
carries it: the MVBA's messages are inside its abstract state, and the
MVBA's `decide` is taken by the oracle step `mvba_step`, whose scheduling is
exactly what this premise states. Its cost `Δ + ρ` is inside `T.ℓ`. -/
def TimedMvbaAdmissible
    (T : MVBATemporal node (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view)) time
      (fun i => nset.is_byz i = true) (S := Mvba.mvbaSafety thM))
    (r : TChorusRun thS thM time) : Prop :=
  ∃ p : (mvbaComponent thS thM).Projection r.toLRun, T.Admissible (mvbaTimedRun p)

/-- **The whole of what is assumed of a run's timing**: the three clauses.
The bridge `ValidBridge` is not timing and is a separate premise. -/
def Sync (sch : Schedule view time)
    (T : MVBATemporal node (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view)) time
      (fun i => nset.is_byz i = true) (S := Mvba.mvbaSafety thM))
    (r : TChorusRun thS thM time) : Prop :=
  TimedJustice sch r ∧ PhasePunctual sch r ∧ TimedMvbaAdmissible T r

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
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (node → Option merkle_root) view}
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
