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

`grep -n '^def [A-Z]' Cadence/Mvba/Schedule.lean` prints the whole list —
the hop table, the schedule, the four clauses and their conjunction,
(A-leader-rotation-k), `Admissible`, the two constants, the two claims —
and nothing else.

## What is assumed of a run, and of nothing else

An admissible run satisfies exactly four clauses, all relating an
*environment* event — a label firing, a clock reading — to a guard or a
local record. None mentions `decided`, a commit certificate, a good view, a
leader or GST as a model event; [Bounds.md](../../docs/Bounds.md) §6.2.4
has the table.

Each entry is the clause, what this file calls it, and the sentence of the
supplement it is the formal shape of.

* **(F-byz)** — nothing of `ByzLabel`; no counterpart, the adversary is
  under no obligation
* **(Δ-justice)** — `BoundedJustice`: every `JusticeLabel` fires within its
  hop bound of becoming move-enabled, after GST; delivery within `Δ` after
  GST, local steps instantaneous (`δ = 0`)
* **(T-timer)** — `TimerPunctual`: `expire_timer i v` fires no earlier than
  `τ v` after `i` entered `v`, and `timer_expired i v` holds no later; the
  view timer, restarted on entry
* **(Δ-avail)** — `AvailWithin`: `avail_ready` within `Δ_sync` of accepting;
  `lem:avail-progress`

(A-viewsync), the strongest premise of `Mvba.termination`, is **not
assumed**. Both of its clauses are a corollary: `AViewSyncClaim` below is
that statement, and `Mvba.aViewSync_of_sync` proves it.

## What is assumed of the instance

Two things a run predicate cannot say: the leader schedule has a correct
leader in every `k` consecutive views (`LeaderRotation`, the supplement's
"every `f+1` consecutive views" with `k = f+1`; the model's own
`leader_honest_cofinal` is its `k`-free shadow), and the schedule's three
hypotheses (`Schedule`): the timeout is bounded, eventually exceeds the
chain's latency, and the constants are non-negative. Why the timeout *must*
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
`Schedule.ℓ` is the contract's `ℓ_MVBA`: one hop to synchronise, at most
`|below v_L| + k` burnt views, the good view's chain, one local step to
decide. Their derivation is [Bounds.md](../../docs/Bounds.md) §6.2.6; the
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

Which of the two bounds each honest action is held to. A **network hop**
(`Δ`) is a step whose guard consumes another party's message or a
certificate assembled from others' signatures — the model puts the delivery
delay on the observation, since a sent message is visible at once. A
**local step** (`δ`) reads the validator's own state and certificates it
already counted. The classification is checked against the paper by its
consequence: at `δ = 0` the latency is the paper's constant. -/

section Hops

variable {node nodeset value view : Type}

/-- The two kinds of honest step. -/
inductive Hop where
  | net
  | loc
  deriving DecidableEq

/-- **The hop table.** `some .net` for a step that consumes another party's
message, `some .loc` for a local step, `none` for a label under no bound —
the adversary's, the timer's, the availability layer's and the caller's.

Written with a wildcard so that an action added to the model lands on
`none`: under no bound, hence *weakening* the premise set rather than
silently strengthening it. `hop_isSome_iff` pins that the table covers
exactly `JusticeLabel`, so an omission is caught there. -/
def hop : Mvba.Label node nodeset value view → Option Hop
  | .handle_preprepare_first .. => some .net
  | .handle_preprepare .. => some .net
  | .form_prepqc .. => some .net
  | .form_commitqc .. => some .net
  | .form_tc_lock .. => some .net
  | .form_tc_nolock .. => some .net
  | .sync_view .. => some .net
  | .sync_view_adopt .. => some .net
  | .leader_propose_first .. => some .loc
  | .leader_repropose .. => some .loc
  | .leader_propose_fresh .. => some .loc
  | .adopt_prepqc .. => some .loc
  | .send_commit .. => some .loc
  | .decide .. => some .loc
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
    | exact ⟨fun _ => ⟨fun h => h, fun h => h, fun h => h, fun h => h⟩, fun _ => rfl⟩
    | exact ⟨fun h => absurd h Bool.false_ne_true, fun hj => (hj.1 trivial).elim⟩
    | exact ⟨fun h => absurd h Bool.false_ne_true, fun hj => (hj.2.1 trivial).elim⟩
    | exact ⟨fun h => absurd h Bool.false_ne_true, fun hj => (hj.2.2.1 trivial).elim⟩
    | exact ⟨fun h => absurd h Bool.false_ne_true, fun hj => (hj.2.2.2 trivial).elim⟩

end Hops

/-! ## The schedule -/

section Constants

variable {time : Type} [LinearOrder time] [AddCommMonoid time]

/-- **The chain's latency**, from the first correct entry into a correct-led
view to its commit certificate, when no correct validator times out: one
network hop to synchronise the entries, a local step for the leader's
`Pre-Prepare`, a hop to accept it, a hop to the prepare certificate and a
local step to adopt it — in parallel with availability — a local step to
send `Commit`, and a hop to the commit certificate. [Bounds.md](../../docs/Bounds.md) §6.2.6
is the table. -/
def Lcert (Δ δ Δsync : time) : time :=
  3 • Δ + max (Δ + δ) Δsync + 2 • δ

/-- At `δ = 0` — the supplement's instantaneous local computation — the
latency is the supplement's `Δ_R + 3Δ + max{Δ, Δ_sync}` with `Δ_R = 0`
(`Recover` is the identity here). The check that the hop table is the
paper's. -/
theorem Lcert_paper (Δ Δsync : time) : Lcert Δ 0 Δsync = 3 • Δ + max Δ Δsync := by
  simp [Lcert]

end Constants

/-- **The timing model's data and its three hypotheses.** The hop bounds,
the availability bound, the view timeout as a function of the view, and
what is assumed of them: non-negativity, the cap (S-cap), and the ramp
(S-ramp) — from `vL` on, every view's budget exceeds the chain's latency.
`k` is the leader-rotation window (`LeaderRotation`). -/
structure Schedule (view time : Type) [vord : TotalOrderWithMinimum view]
    [LinearOrder time] [AddCommMonoid time] where
  /-- The network hop bound after GST. -/
  Δ : time
  /-- The local-step bound; the paper's is `0`. -/
  δ : time
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
  Δsync_nonneg : 0 ≤ Δsync
  τ_nonneg : ∀ v, 0 ≤ τ v
  τ_le_max : ∀ v, τ v ≤ τmax
  τ_ramp : ∀ v, vord.le vL v → Lcert Δ δ Δsync < τ v

namespace Schedule

variable {view time : Type} [vord : TotalOrderWithMinimum view]
  [LinearOrder time] [AddCommMonoid time]

/-- The bound a hop kind is held to. -/
def bound (sch : Schedule view time) : Hop → time
  | .net => sch.Δ
  | .loc => sch.δ

/-- **What one view costs at most** when it does not decide: its budget,
at most one adoption and the timeout (two local steps), the certificate
(one hop), the advance (one hop). [Bounds.md](../../docs/Bounds.md) §6.2.6. -/
def burn (sch : Schedule view time) : time :=
  sch.τmax + 2 • sch.δ + 2 • sch.Δ

/-- **`ℓ_MVBA`.** One hop to synchronise everyone to the highest view
entered at `max(t, gst)`, at most `|below vL| + k` burnt views to reach a
correct-led view past the ramp — at most `|below vL|` successors clear the
ramp, and fewer than `k` more reach a correct leader — that view's chain,
and one local step to decide on the certificate. `O(kΔ)` when every
constant is `O(Δ)` and the ramp is empty — the supplement's `O(fΔ)` at
`k = f + 1`. -/
def ℓ (sch : Schedule view time) (vfin : ViewOrderEnum view vord) : time :=
  sch.Δ + ((vfin.below sch.vL).length + sch.k) • sch.burn
    + Lcert sch.Δ sch.δ sch.Δsync + sch.δ

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

/-- **(Δ-justice)** — bounded weak fairness after GST of every label the hop
table covers, at its hop bound. The timed form of `FJustice`, with
`EnabledMove` for `Enabled` ([Timed.lean](../Timed.lean), the header). -/
def BoundedJustice (sch : Schedule view time) (r : TMvbaRun th time) : Prop :=
  ∀ (l : Mvba.Label node nodeset value view) (h : Hop), hop l = some h →
    BoundedFair r (sch.bound h) l

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

/-- **The whole of what is assumed of a run**: the three clauses. (F-byz)
is the absence of a fourth. -/
def Sync (sch : Schedule view time) (r : TMvbaRun th time) : Prop :=
  BoundedJustice sch r ∧ TimerPunctual sch r ∧ AvailWithin sch r

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

/-- info: 'Mvba.hop_isSome_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Mvba.hop_isSome_iff

/-- info: 'Mvba.Lcert_paper' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Mvba.Lcert_paper
