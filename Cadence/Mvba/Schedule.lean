import Cadence.Timed
import Cadence.Mvba.Liveness
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Defs

/-! # Mvba.Schedule — the timing model, and the bounded claim stated

[Bounds.md](../../docs/Bounds.md) §6.2, step 1. This file states the
**timing model** under which the leader-based MVBA satisfies
`MVBATemporal.termination` — every premise a named `Prop` on a labelled
timed run — and the **target** as a `Prop`-valued definition, apart from
its proof. That separation is [Mvba/Liveness.lean](Liveness.lean)'s
discipline and it is kept for the same reason: the premises are fixed,
type-checked and citable on their own, so none can become a hypothesis
because a proof needs it.

`grep -nE '^(def|structure) [A-Z]' Cadence/Mvba/Schedule.lean` prints the
whole list — the latency constant, the schedule, (Δ-justice)'s vocabulary
and the structure of its six clauses, the other two clauses and their
conjunction, (A-leader-rotation-k), `Admissible`, the two claims — and
nothing else; the hop table `hop` and `Schedule.ℓ` are the two lower-case
definitions.

## What is assumed of a run, and of nothing else

An admissible run satisfies exactly five clauses, all relating an
*environment* event — a label firing, a clock reading — to a guard or a
local record. None mentions a commit certificate, a good view, a leader or
GST as a model event; the caller's handoff names a correct validator's
decision, as the supplement's termination setting does; [Bounds.md](../../docs/Bounds.md) §6.2.4
has the table.

Each entry is the clause, what this file calls it, and the sentence of the
supplement it is the formal shape of.

* **(F-byz)** — nothing of `ByzLabel`; no counterpart, the adversary is
  under no obligation
* **(Δ-justice)** — `BoundedJustice`: a local step fires within `δ`, and a
  network step within `Δ` when its messages were sent at or after GST by
  correct validators and retained, or within `Δ + ρ` when they are
  retransmitted; the supplement's termination setting (messages sent at or
  after GST delivered within `Δ`; timeouts, `ViewTC_i` and a decided
  `CommitQC` re-sent every `ρ`) and `sec:reliable-delivery` (one-view
  retention), local steps instantaneous (`δ = 0`)
* **(T-timer)** — `TimerPunctual`: `expire_timer i v` fires no earlier than
  `τ v` after `i` entered `v`, and `timer_expired i v` holds no later; the
  view timer, restarted on entry
* **(Δ-avail)** — `AvailWithin`: `avail_ready` within `Δ_sync` of accepting;
  `lem:avail-progress`
* **(Δ-relay)** — `Relayed`, the caller's: once a correct validator has
  decided, a correct validator takes the transferred certificate within
  `Δ + ρ` (the input `decide`); the composing layer's delivery of a decided
  `CommitQC`, `lem:decision-propagation`

(A-viewsync), the strongest premise of `Mvba.termination`, is **not
assumed**. Both of its clauses are a corollary: `AViewSyncClaim` below is
that statement, and `Mvba.aViewSync_of_sync` proves it.

## What is assumed of the instance

Two things a run predicate cannot say: the leader schedule has a correct
leader in every `k` consecutive views (`LeaderRotation`, the supplement's
"every `f+1` consecutive views" with `k = f+1`; the model's own
`leader_honest_cofinal` is its `k`-free shadow), and the schedule's three
hypotheses (`Schedule`): the timeout is bounded, eventually exceeds the
chain's latency, and the constants are non-negative (`ρ` among them). Why the timeout *must*
be bounded for a fixed `ℓ` to exist — the backoff remark of the supplement at
`026dc8b` was incompatible with its `O(fΔ)` theorem, and `eb1bb51` replaced
it by the fixed `T := Δ_R + 4Δ + max{Δ, Δ_sync}` — is
[Bounds.md](../../docs/Bounds.md) §6.2.3. The paper's fixed `T` is the
special case `vL = vord.zero`, `τ` constant.

## The two constants

`Lcert Δ δ Δsync` is the chain's latency in a correct-led view whose budget
is not exhausted, from the first correct entry to the commit certificate;
at `δ = 0` it is the supplement's `3Δ + max{Δ, Δ_sync}` (`Lcert_paper`),
with `Δ_R = 0` because `Recover` is the identity in this model.
`Schedule.ℓ` is the contract's `ℓ_MVBA`: a retransmitted hop to
synchronise, the first burnt view's two retransmissions, at most
`|below v_L| + k` burnt views, the good view's chain, and the decision's
transfer. Their derivation is [Bounds.md](../../docs/Bounds.md) §6.2.6; the
proof that `ℓ` bounds termination is `Mvba.bounded_termination`
([Mvba/BoundedTermination.lean](BoundedTermination.lean)).
[Mvba/Temporal.lean](Temporal.lean) turns it into the contract's
`MVBATemporal` instance, with `Admissible` below as the run model.

## What this file does not do

Prove anything about the protocol. Its theorems are about its own
definitions: the hop table is defined on exactly the `JusticeLabel`s
(`hop_isSome_iff`), and the latency constant is the paper's at `δ = 0`. It
builds on the model and on [Mvba/Liveness.lean](Liveness.lean), and neither
depends on it. -/

namespace Mvba

open Cadence
-- Veil's `TotalOrder` on the clock is the scoped bridge from its linear
-- order ([Timed.lean](../Timed.lean)); every `TimedRun` projection below
-- needs it.
open scoped Cadence.Timed

/-! ## The hop table

Which kind of step each honest action is. A **network hop** is a step whose
guard consumes another party's message or a certificate assembled from
others' signatures — the model puts the delivery delay on the observation,
since a sent message is visible at once. A **local step** (`δ`) reads the
validator's own state and certificates it already counted. A network hop's
bound depends on the message's history, `Δ` or `Δ + ρ` (`BoundedJustice`
below). The classification is checked against the paper by its
consequence: at `δ = 0` the good view's latency is the paper's constant.

`decide` is not in the table. It takes a commit certificate that a
validator did not form itself, which reaches it only by transfer
(`lem:decision-propagation`): the supplement's `CommitQC` travels by
Chorus's broadcast. Since R8 taking it is the contract's input `accept`
([Compose.lean](Compose.lean)), and its timing is the caller's, `Relayed`.
At the pin `026dc8b` the table classed it as local, which the good view
could not catch, since there every correct validator forms the certificate
itself ([MvbaPlan.md](../../docs/MvbaPlan.md) §11.3, C16 (N3)); from step 5b
to R8 it was a network hop, whose delivery clause stood in for the
composing layer.

`adopt_prepqc` is a network hop too: a validator forms its prepare
certificate from the `Prepare`s it received itself, since prepare
certificates do not travel (the supplement's `TryFormPrepQC`; the model's
guard reads the prepares since R3, [Bounds.md](../../docs/Bounds.md)
§6.2.4, (N4)). Until then it was a local step that consumed a certificate
formed anywhere.

The commit and timeout certificates are network hops at the validator
that forms them, `form_own_commitqc` and `form_own_tc_*` (the supplement's
`TryFormCommitQC` and `HandleTimeout`), since R4. Before, the table timed
the anonymous assemblies, which are the adversary's and carry no bound
([Bounds.md](../../docs/Bounds.md) §6.4.7). -/

section Hops

variable {node nodeset value view : Type}

/-- The two kinds of honest step. -/
inductive Hop where
  | net
  | loc
  deriving DecidableEq

/-- **The hop table.** `some .net` for a step that consumes another party's
message, `some .loc` for a local step, `none` for a label under no bound —
the adversary's, the anonymous assemblies (the adversary's capability too,
`AssemblyLabel`), the timer's, the availability layer's and the caller's.

Written with a wildcard so that an action added to the model lands on
`none`: under no bound, hence *weakening* the premise set rather than
silently strengthening it. `hop_isSome_iff` pins that the table covers
exactly `JusticeLabel`, so an omission is caught there. -/
def hop : Mvba.Label node nodeset value view → Option Hop
  | .handle_preprepare_first .. => some .net
  | .handle_preprepare .. => some .net
  | .adopt_prepqc .. => some .net
  | .form_own_commitqc .. => some .net
  | .form_own_tc_lock .. => some .net
  | .form_own_tc_nolock .. => some .net
  | .sync_view .. => some .net
  | .sync_view_adopt .. => some .net
  | .leader_propose_first .. => some .loc
  | .leader_repropose .. => some .loc
  | .leader_propose_fresh .. => some .loc
  | .send_commit .. => some .loc
  | .timeout_qc .. => some .loc
  | .timeout_noqc .. => some .loc
  | _ => none

/-- **The table covers exactly the fair labels.** A label has a hop bound
iff it is a `JusticeLabel`; the case split is over the model's own label
type, so adding an action and forgetting it here is an error, not a silent
omission. -/
theorem hop_isSome_iff (l : Mvba.Label node nodeset value view) :
    (hop l).isSome ↔ JusticeLabel l := by
  cases l <;> first
    | exact ⟨fun _ => ⟨fun h => h, fun h => h, fun h => h, fun h => h, fun h => h⟩, fun _ => rfl⟩
    | exact ⟨fun h => absurd h Bool.false_ne_true, fun hj => (hj.1 trivial).elim⟩
    | exact ⟨fun h => absurd h Bool.false_ne_true, fun hj => (hj.2.1 trivial).elim⟩
    | exact ⟨fun h => absurd h Bool.false_ne_true, fun hj => (hj.2.2.1 trivial).elim⟩
    | exact ⟨fun h => absurd h Bool.false_ne_true, fun hj => (hj.2.2.2.1 trivial).elim⟩
    | exact ⟨fun h => absurd h Bool.false_ne_true, fun hj => (hj.2.2.2.2 trivial).elim⟩

end Hops

/-! ## The schedule -/

section Constants

variable {time : Type} [LinearOrder time] [AddCommMonoid time]

/-- **The chain's latency**, from the first correct entry into a correct-led
view to its commit certificate, when no correct validator times out: one
network hop to synchronise the entries, a local step for the leader's
`Pre-Prepare`, a hop to accept it, a hop to each validator's own prepare
certificate — in parallel with availability — a local step to send
`Commit`, and a hop to the commit certificate. [Bounds.md](../../docs/Bounds.md) §6.2.6
is the table. -/
def Lcert (Δ δ Δsync : time) : time :=
  3 • Δ + max Δ Δsync + 2 • δ

/-- At `δ = 0` — the supplement's instantaneous local computation — the
latency is the supplement's `Δ_R + 3Δ + max{Δ, Δ_sync}` with `Δ_R = 0`
(`Recover` is the identity here). The check that the hop table is the
paper's. -/
theorem Lcert_paper (Δ Δsync : time) : Lcert Δ 0 Δsync = 3 • Δ + max Δ Δsync := by
  simp [Lcert]

end Constants

/-- **The timing model's data and its three hypotheses.** The hop bounds,
the retransmission interval, the availability bound, the view timeout as a
function of the view, and
what is assumed of them: non-negativity, the cap (S-cap), and the ramp
(S-ramp) — from `vL` on, every view's budget exceeds the chain's latency.
`k` is the leader-rotation window (`LeaderRotation`). -/
structure Schedule (view time : Type) [vord : TotalOrderWithMinimum view]
    [LinearOrder time] [AddCommMonoid time] where
  /-- The network hop bound after GST. -/
  Δ : time
  /-- The local-step bound; the paper's is `0`. -/
  δ : time
  /-- The retransmission interval of `sec:reliable-delivery`, which the
  supplement names `ρ_mvba` (`subsec:mvba-protocol`), to keep it apart from
  its Merkle-root symbol `ρ`, and assumes `O(Δ)`: timeouts, `ViewTC_i` and a
  decided `CommitQC` are re-sent every `ρ_mvba`. The field keeps the
  name `ρ`. -/
  ρ : time
  /-- The availability layer's bound (`Δ_sync`). -/
  Δsync : time
  /-- The view timeout: view `v`'s timer expires `τ v` after entry. -/
  τ : view → time
  /-- **(S-cap)** — the cap on the schedule. -/
  τmax : time
  /-- **(S-ramp)** — the first view from which the budget clears the
  latency. `vord.zero` for a fixed known timeout. -/
  vL : view
  /-- The leader-rotation window: some `k` consecutive views contain a
  correct leader. -/
  k : Nat
  Δ_pos : 0 < Δ
  δ_nonneg : 0 ≤ δ
  ρ_nonneg : 0 ≤ ρ
  Δsync_nonneg : 0 ≤ Δsync
  τ_nonneg : ∀ v, 0 ≤ τ v
  τ_le_max : ∀ v, τ v ≤ τmax
  τ_ramp : ∀ v, vord.le vL v → Lcert Δ δ Δsync < τ v

namespace Schedule

variable {view time : Type} [vord : TotalOrderWithMinimum view]
  [LinearOrder time] [AddCommMonoid time]

/-- **What one view costs at most** when it does not decide: its budget,
at most one adoption and the timeout (two local steps), the certificate
(one hop), the advance (one hop). [Bounds.md](../../docs/Bounds.md) §6.2.6. -/
def burn (sch : Schedule view time) : time :=
  sch.τmax + 2 • sch.δ + 2 • sch.Δ

/-- **`ℓ_MVBA`**, milestone by milestone from `u := max(t, gst)`:

* `Δ + ρ` — everyone reaches `M`, the highest view a correct validator is
  in at `u`, on the certificate below it, which may predate GST and so
  arrives by retransmission;
* `2 • ρ` — view `M`'s timeouts and its certificate may predate GST too,
  so the first burnt view pays a retransmission on each of its two network
  hops;
* `(|below vL| + k) • burn` — the burnt views `M, …, W − 1`: at most
  `|below vL|` successors of `M` clear the ramp, one more puts the good
  view's predecessor past it (the one-view retention needs `W − 1` fresh
  and above `Δ` — the supplement's charge of views `V` and `V + 1`), and
  fewer than `k` more reach a correct leader;
* `Lcert` — the good view's chain, to its commit certificate;
* `Δ + ρ` — the decision, which reaches a validator that did not form the
  certificate by transfer (`lem:decision-propagation`).

`O(kΔ)` when every constant is `O(Δ)` and the ramp is empty — the
supplement's `O(fΔ)` at `k = f + 1`. -/
def ℓ (sch : Schedule view time) (vfin : ViewOrderEnum view vord) : time :=
  (sch.Δ + sch.ρ) + 2 • sch.ρ + ((vfin.below sch.vL).length + sch.k) • sch.burn
    + Lcert sch.Δ sch.δ sch.Δsync + (sch.Δ + sch.ρ)

end Schedule

/-! ## The premises, one named `Prop` each -/

section Runs

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]

/-- A labelled timed run of the MVBA: the object every premise below is
about. Its `toLRun` is [Mvba/Liveness.lean](Liveness.lean)'s `MvbaRun`. -/
abbrev TMvbaRun (th : Theory node nodeset value view) (time : Type) [LinearOrder time] :=
  TLRun (Mvba.relationalTransitionSystem node nodeset value view) th time

/-! ### (Δ-justice): the supplement's network, clause by clause

The termination setting of `eb1bb51` (`subsec:mvba-correctness`, before
`lem:decision-propagation`) and `sec:reliable-delivery` say what the network
guarantees. Messages between correct validators **sent at or after GST**
are delivered within `Δ`. **Timeouts, `ViewTC_i` and a decided `CommitQC`
are retransmitted** every `ρ`. A validator **retains** view-scoped
messages for the next view and **discards** those of lower views; it may
discard farther ones. (Δ-justice) is those rules, one clause each, over
the model's labels. The model's network relations hold from a message's
first delivery to a correct validator — a sent message is visible at
once — so "the message" of a label is the relation its guard reads, and
"when it was sent" is the first index at which that relation holds.

The words the clauses use, each a predicate on the run or a state. -/

/-- **Bounded weak fairness while `C` holds**: `BoundedFair` with the window
antecedent also asking `C` at every index inside it. The form every
network clause takes: `C` is what the supplement needs to hold while the
delivery is pending — the receiver still takes part, and has not moved on
from the message's view. -/
def BoundedFairWhile (r : TMvbaRun th time) (D : time) (l : Mvba.Label node nodeset value view)
    (C : Mvba.State (Mvba.FieldAbstractType node nodeset value view) → Prop) : Prop :=
  ∀ N, (∀ n, N ≤ n → r.clk n ≤ r.ref N + D →
      Enabled (Mvba.relationalTransitionSystem node nodeset value view) th (r.at' n) l ∧
        C (r.at' n)) →
    r.FiresWithin N D l

/-- `BoundedFairWhile` over state-changing steps: only the right-hand side
of `Mvba.boundedFairWhile_iff_move`; no premise is stated with it. -/
def BoundedFairWhileMove (r : TMvbaRun th time) (D : time) (l : Mvba.Label node nodeset value view)
    (C : Mvba.State (Mvba.FieldAbstractType node nodeset value view) → Prop) : Prop :=
  ∀ N, (∀ n, N ≤ n → r.clk n ≤ r.ref N + D →
      EnabledMove (Mvba.relationalTransitionSystem node nodeset value view) th (r.at' n) l ∧
        C (r.at' n)) →
    r.FiresWithin N D l

/-- **(N1) Sent at or after GST**: wherever `P` holds, the clock has
reached GST — so `P` first held at or after it. -/
def SinceGst (r : TMvbaRun th time)
    (P : Mvba.State (Mvba.FieldAbstractType node nodeset value view) → Prop) : Prop :=
  ∀ n, P (r.at' n) → r.gst ≤ r.clk n

/-- `i` has entered view `w` or the one before it, or a higher one. -/
def ReachedPrev (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view))
    (i : node) (w : view) : Prop :=
  ∃ V, s.entered i V = true ∧ (vord.le w V ∨ vord.next V w)

/-- **(N2) One-view retention**: wherever `P` holds, `i` has reached
`w − 1`. A view-`w` message sent then reaches `i` in view `w − 1` or
later, so `i` retains it (`sec:reliable-delivery`, "Future-view message
retention"). -/
def RetainedBy (r : TMvbaRun th time) (i : node) (w : view)
    (P : Mvba.State (Mvba.FieldAbstractType node nodeset value view) → Prop) : Prop :=
  ∀ n, P (r.at' n) → ReachedPrev (r.at' n) i w

/-- Every correct validator takes part: none is abandoned or has halted
after deciding. The supplement's scope for its synchronisation lemmas,
"no correct validator has decided or abandoned, so all participate". -/
def AllActive (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) : Prop :=
  ∀ j, ¬ nset.is_byz j = true → Active s j

/-- **(N2) Lower views are discarded**: `i` has not moved past `v`, so it
still processes view-`v` messages. -/
def NotPast (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view))
    (i : node) (v : view) : Prop :=
  ∀ V, s.entered i V = true → vord.le V v

/-- Some member of `q` has sent a `Timeout` for `v`. -/
def AnyTimeout (q : nodeset) (v : view)
    (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) : Prop :=
  ∃ p, nset.member p q = true ∧
    (s.msg_timeout_noqc p v = true ∨ ∃ w e, s.msg_timeout_qc p v w e = true)

/-- **What a first delivery needs**, per network label: the conditions
under which the supplement's network delivers the label's messages to the
label's own validator within `Δ`.

* a `Pre-Prepare` — from a correct leader, sent at or after GST, and
  retained by its receiver;
* the `Prepare`s a validator forms its own certificate from — from a
  correct quorum, the first of them sent at or after GST, and retained by
  that validator;
* the `Commit`s and timeouts a validator forms a certificate from — from
  a correct quorum, the first of them sent at or after GST, and retained
  by that validator;
* a timeout certificate — first obtained at or after GST. Its first
  correct holder processes it on arrival and forwards it
  (`line:mvba:sv-forward`).

A commit certificate's transfer is not here: taking it is the input
`decide`, the caller's, and its timing is `Relayed`.

A label the table classes local, or no label at all, has no first
delivery (`False`). -/
def Delivers (r : TMvbaRun th time) : Mvba.Label node nodeset value view → Prop
  | .handle_preprepare_first j l e =>
    ¬ nset.is_byz l = true ∧ SinceGst r (fun s => s.msg_preprepare l vord.zero e = true) ∧
      RetainedBy r j vord.zero (fun s => s.msg_preprepare l vord.zero e = true)
  | .handle_preprepare j l _ v e =>
    ¬ nset.is_byz l = true ∧ SinceGst r (fun s => s.msg_preprepare l v e = true) ∧
      RetainedBy r j v (fun s => s.msg_preprepare l v e = true)
  | .adopt_prepqc j v e q =>
    CorrectQuorum (node := node) q ∧
      SinceGst r (fun s => ∃ p, nset.member p q = true ∧ s.msg_prepare p v e = true) ∧
      RetainedBy r j v (fun s => ∃ p, nset.member p q = true ∧ s.msg_prepare p v e = true)
  | .form_own_commitqc j v e q =>
    CorrectQuorum (node := node) q ∧
      SinceGst r (fun s => ∃ p, nset.member p q = true ∧ s.msg_commit p v e = true) ∧
      RetainedBy r j v (fun s => ∃ p, nset.member p q = true ∧ s.msg_commit p v e = true)
  | .form_own_tc_lock j v q _ _ _ =>
    CorrectQuorum (node := node) q ∧ SinceGst r (AnyTimeout q v) ∧ RetainedBy r j v (AnyTimeout q v)
  | .form_own_tc_nolock j v q =>
    CorrectQuorum (node := node) q ∧ SinceGst r (AnyTimeout q v) ∧ RetainedBy r j v (AnyTimeout q v)
  | .sync_view _ pv _ => SinceGst r (fun s => s.msg_tc pv = true)
  | .sync_view_adopt _ pv _ w e => SinceGst r (fun s => s.tc_lock pv w e = true)
  | _ => False

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **The untimed premise asks the same of the senders.** A label whose
first delivery the timed premise owes has the correct senders the untimed
(F-justice) asks for: `Owed` is `Delivers`' sender part. -/
theorem owed_of_delivers {r : TMvbaRun th time} {l : Mvba.Label node nodeset value view}
    (h : Delivers r l) : Owed l := by
  cases l <;> first | exact h.elim | exact h.1 | trivial

/-- **While a first delivery is pending**: every correct validator takes
part. That the receiver has not moved past the message's view — it
discards lower views' messages — is in the guard of every per-validator
step that reads view-scoped messages (`in_view`). -/
def Receiving : Mvba.Label node nodeset value view →
    Mvba.State (Mvba.FieldAbstractType node nodeset value view) → Prop
  | _ => AllActive

/-- Some correct validator has entered `v`. -/
def SomeEntered (v : view) (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) :
    Prop :=
  ∃ j, ¬ nset.is_byz j = true ∧ s.entered j v = true

/-- **(Δ-justice)** — the supplement's network, as five clauses. The timed
form of `FJustice`: a fair label that is enabled throughout its window
fires within it — the same plain enabledness, with a deadline in place of
"eventually". Every clause is a `BoundedFair` or `BoundedFairWhile` of a
fair label, and for a fair label either one over plain enabledness is the
same premise as over state-changing steps (`boundedFair_iff_move`,
`boundedFairWhile_iff_move`, from `enabledMove_of_enabled`).

* `local_` — a local step fires within `δ`, as before;
* `first` — a network step whose messages were sent at or after GST by
  correct validators, and retained, fires within `Δ` (N1, N2);
* `forwarded` — a timeout certificate forwarded at or after GST, by the
  first correct validator to enter the view it justifies
  (`line:mvba:sv-forward`), is processed within `Δ`;
* `timeouts` — a correct quorum's timeouts are re-sent every `ρ` by
  validators still in the view, so a correct validator in the view forms
  the certificate within `Δ + ρ` whenever they were first sent (N1);
* `certificates` — every active validator re-sends `ViewTC_i` every `ρ`
  (`line:mvba:viewtc-retx`), so a timeout certificate is processed within
  `Δ + ρ` whenever it was formed (N1).

A decided certificate's transfer is the caller's, and is `Relayed`.

Each window is measured from `max(clk N, gst)` (`BoundedFair`). -/
structure BoundedJustice (sch : Schedule view time) (r : TMvbaRun th time) : Prop where
  local_ : ∀ l : Mvba.Label node nodeset value view, hop l = some .loc →
    BoundedFair r sch.δ l
  first : ∀ (l : Mvba.Label node nodeset value view), hop l = some .net →
    Delivers r l → BoundedFairWhile r sch.Δ l (Receiving l)
  forwarded : ∀ (i : node) (pv v : view), SinceGst r (SomeEntered v) →
    BoundedFairWhile r sch.Δ (.sync_view i pv v) (fun s => AllActive s ∧ SomeEntered v s) ∧
    ∀ w e, BoundedFairWhile r sch.Δ (.sync_view_adopt i pv v w e)
      (fun s => AllActive s ∧ SomeEntered v s)
  timeouts : ∀ (i : node) (v : view) (q : nodeset), ¬ nset.is_byz i = true →
    CorrectQuorum (node := node) q →
    (∀ r₀ w e, BoundedFairWhile r (sch.Δ + sch.ρ) (.form_own_tc_lock i v q r₀ w e)
      (fun s => AllActive s ∧ ∀ p, nset.member p q = true → NotPast s p v)) ∧
    BoundedFairWhile r (sch.Δ + sch.ρ) (.form_own_tc_nolock i v q)
      (fun s => AllActive s ∧ ∀ p, nset.member p q = true → NotPast s p v)
  certificates : ∀ (i : node) (pv v : view),
    BoundedFairWhile r (sch.Δ + sch.ρ) (.sync_view i pv v) AllActive ∧
    ∀ w e, BoundedFairWhile r (sch.Δ + sch.ρ) (.sync_view_adopt i pv v w e) AllActive

/-- **(Δ-relay)** — the caller hands decided certificates on: once a correct
validator `j` has decided `e`, a correct validator that can take a
transferred certificate on `e` does so within `Δ + ρ`, measured from
`max(clk N, gst)`. The supplement's termination setting asks this of the
composing layer (`lem:decision-propagation`: Chorus broadcasts the
`CommitQC` a decision outputs, and serves it again every `ρ` to whoever is
undecided) (N3). Taking a certificate is the input `decide`, so this is a
premise on the caller, not on the MVBA's scheduling. It is owed only for a
correct validator's decision. The timed form of (F-relay); within Cadence
it is derived from Chorus's rows (`Chorus.relayed_of_timedJustice`). -/
def Relayed (sch : Schedule view time) (r : TMvbaRun th time) : Prop :=
  ∀ (i j : node) (v : view) (e : value), ¬ nset.is_byz j = true →
    BoundedFairWhile r (sch.Δ + sch.ρ) (.decide i v e) (fun s => s.decided j e = true)

omit [IsOrderedAddMonoid time] in
/-- **The bridge, for (Δ-justice)'s local clauses.** For a fair label of this
model, bounded fairness over plain enabledness and over state-changing steps
are the same premise: every fair label is move-enabled wherever it is
enabled (`enabledMove_of_enabled`, at every state). -/
theorem boundedFair_iff_move {r : TMvbaRun th time} {D : time}
    {l : Mvba.Label node nodeset value view} (hj : JusticeLabel l) :
    BoundedFair r D l ↔ BoundedFairMove r D l :=
  Cadence.boundedFair_iff_move fun _ => enabledMove_of_enabled l hj

omit [IsOrderedAddMonoid time] in
/-- **The bridge, for (Δ-justice)'s network clauses**: the same, with the
clause's window condition `C` alongside. -/
theorem boundedFairWhile_iff_move {r : TMvbaRun th time} {D : time}
    {l : Mvba.Label node nodeset value view}
    {C : Mvba.State (Mvba.FieldAbstractType node nodeset value view) → Prop}
    (hj : JusticeLabel l) :
    BoundedFairWhile r D l C ↔ BoundedFairWhileMove r D l C :=
  ⟨fun h N hen => h N fun n hn hc => ⟨Enabled.of_move (hen n hn hc).1, (hen n hn hc).2⟩,
   fun h N hen => h N fun n hn hc =>
     ⟨enabledMove_of_enabled l hj (hen n hn hc).1, (hen n hn hc).2⟩⟩

/-- **(T-timer)** — the view timer is punctual. For a correct validator `i`
and a view `v`:

* **(T1) not early** — `expire_timer i v` fires at `n` only if `i` entered
  `v` at some `m ≤ n` with `clk m + τ v ≤ clk n`;
* **(T2) not late** — if `i` entered `v` at `m`, then `timer_expired i v`
  holds at some `n ≥ m` with `clk n ≤ clk m + τ v`.

Both are about the environment's marker, neither about the protocol's
state beyond `entered`. Together they say the marker fires when the clock
reaches entry plus budget, which also forbids the clock from jumping over
that value while the timer is pending. -/
def TimerPunctual (sch : Schedule view time) (r : TMvbaRun th time) : Prop :=
  (∀ (n : Nat) (i : node) (v : view), ¬ nset.is_byz i = true →
    r.lbl n = .expire_timer i v →
      ∃ m, m ≤ n ∧ (r.at' m).entered i v = true ∧ r.clk m + sch.τ v ≤ r.clk n) ∧
  (∀ (m : Nat) (i : node) (v : view), ¬ nset.is_byz i = true →
    (r.at' m).entered i v = true →
      ∃ n, m ≤ n ∧ (r.at' n).timer_expired i v = true ∧ r.clk n ≤ r.clk m + sch.τ v)

/-- **(Δ-avail)** — the availability shares arrive within `Δsync` of
accepting a vector, after GST. The timed form of `FAvail`. -/
def AvailWithin (sch : Schedule view time) (r : TMvbaRun th time) : Prop :=
  ∀ (m : Nat) (i : node) (v : view) (e : value), ¬ nset.is_byz i = true →
    (r.at' m).accepted i v e = true →
      ∃ n, m ≤ n ∧ (r.at' n).avail_ready i e = true ∧ r.clk n ≤ r.ref m + sch.Δsync

/-- **The whole of what is assumed of a run**: the three clauses of the
MVBA's own scheduling and the caller's handoff. (F-byz) is the absence of a
fifth. -/
def Sync (sch : Schedule view time) (r : TMvbaRun th time) : Prop :=
  BoundedJustice sch r ∧ TimerPunctual sch r ∧ AvailWithin sch r ∧ Relayed sch r

/-- **(A-leader-rotation-k)** — among any `k` consecutive views there is
one with a correct leader. The supplement's "every `f+1` consecutive views
contain a correct leader" (`subsec:mvba-protocol`), with `k = f+1`. The
model's assumption `leader_honest_cofinal` is the `k`-free consequence. A
hypothesis of the *instance*, since it constrains the theory, not the
run. -/
def LeaderRotation (vfin : ViewOrderEnum view vord) (k : Nat)
    (th : Theory node nodeset value view) : Prop :=
  ∀ v : view, ∃ j, j < k ∧
    ∃ L : node, th.leader (vfin.succ^[j] v) L = true ∧ ¬ nset.is_byz L = true

/-! ## The contract's runs, and admissibility -/

/-- A `TimedRun` of the MVBA — the object `MVBATemporal`'s fields quantify
over, at `Mvba.mvbaSafety th`: the model's states with a clock reading at
every index. The `TotalOrder` on `time` is [Timed.lean](../Timed.lean)'s scoped
bridge from the linear order. -/
abbrev TimedMvbaRun (th : Theory node nodeset value view) (time : Type) [LinearOrder time] :=
  TimedRun (Mvba.State (Mvba.FieldAbstractType node nodeset value view)) time
    (mvbaSafety th).init (mvbaSafety th).trans

/-- **`MVBATemporal.Admissible`**, as this instance defines it: the run has a
labelling — a `TMvbaRun` with its states and clocks — that satisfies
`Sync sch`. The labels are the witness of how the run was scheduled, which
a `TimedRun` does not carry. -/
def Admissible (sch : Schedule view time) (th : Theory node nodeset value view)
    (tr : TimedMvbaRun th time) : Prop :=
  ∃ r : TMvbaRun th time,
    (∀ n, tr.at' n = r.at' n) ∧ (∀ n, tr.clk n = r.clk n) ∧ tr.gst = r.gst ∧ Sync sch r

/-! ## The targets, stated

Two `Prop`-valued definitions, asserted nowhere. The first is
`MVBATemporal.termination` in the model's own vocabulary; the second is the
statement that (A-viewsync) is a consequence rather than a premise. -/

/-- **Bounded termination, the target.** Under (A-leader-rotation-k) and
the three clauses, if every correct validator has proposed by `t` and none
is abandoned at a clock at or before `max(t, gst) + ℓ`, then every correct
validator has decided at some index whose clock is at most
`max(t, gst) + ℓ`. This is `MVBATemporal.termination`'s statement at
`Mvba.mvbaSafety th`, with `byGstBound`'s least upper bound written as `max` and
the observables read off the model's state. -/
def BoundedTerminationClaim (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (th : Theory node nodeset value view) : Prop :=
  LeaderRotation vfin sch.k th →
  ∀ r : TMvbaRun th time, Sync sch r →
    ∀ t : time,
      (∀ p, ¬ nset.is_byz p = true →
        ∃ (n : Nat) (E : value), r.clk n ≤ t ∧ (r.at' n).input p E = true) →
      (∀ p, ¬ nset.is_byz p = true → ∀ n, (r.at' n).abandoned p = true →
        ¬ r.clk n ≤ max t r.gst + sch.ℓ vfin) →
      ∀ q, ¬ nset.is_byz q = true →
        ∃ (n : Nat) (E : value), r.clk n ≤ max t r.gst + sch.ℓ vfin ∧
          (r.at' n).decided q E = true

/-- **(A-viewsync) is a consequence.** For finitely many validators, under
(A-leader-rotation-k) and the three clauses, a run in which every correct
validator proposes and none is abandoned before deciding satisfies
[Mvba/Liveness.lean](Liveness.lean)'s `AViewSync`: both clauses, and the existence of the
good view. The premises besides the timing model are `Mvba.termination`'s
own, `AllPropose` and `NoEarlyAbandon`, so this is the formal version of the
trust-base move that [Liveness.md](../../docs/Liveness.md) §2.1 describes.

The finite validator set is load-bearing. It turns "every correct validator
proposes at some index" into a common deadline, and without one nothing
stops every correct-led view from being burnt before its leader has
proposed. [Bounds.md](../../docs/Bounds.md) §6.2.8 has the argument. -/
def AViewSyncClaim [Fintype node] (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (th : Theory node nodeset value view) : Prop :=
  LeaderRotation vfin sch.k th →
  ∀ r : TMvbaRun th time, Sync sch r →
    AllPropose r.toLRun → NoEarlyAbandon r.toLRun → AViewSync r.toLRun

end Runs

end Mvba

/-! ## The pinned trust base

Definitions, the hop table's coverage and the constant check; the targets
are definitions, so nothing here asserts a bound. -/

/--
info: 'Mvba.boundedFair_iff_move' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.boundedFair_iff_move

/--
info: 'Mvba.boundedFairWhile_iff_move' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.boundedFairWhile_iff_move

/-- info: 'Mvba.hop_isSome_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Mvba.hop_isSome_iff

/-- info: 'Mvba.Lcert_paper' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Mvba.Lcert_paper
