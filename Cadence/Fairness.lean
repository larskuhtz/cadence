import Veil
import Cadence.Interfaces

/-! # Fairness over a Veil transition system

The vocabulary a run-level liveness statement needs, and nothing else: a run
that records **which action fired**, what it means for an action to be
enabled, and weak and strong fairness of one action label.

## Why it lives here, and what it is meant to become

Veil has no surface syntax for fairness. The fork's design proposal
(`docs/Liveness.md` on its `lars/liveness` branch — a document, not an
implementation) plans per-action annotations

```
fairness justice    send_vote
fairness compassion deliver
response [name]     p ↝ q
```

discharged by a liveness-to-safety reduction. This file is deliberately the
same shape, one level down: fairness is a predicate on a **label**, not on a
syntactic action or a state, so `fairness justice a` becomes
`WeaklyFair r .a` and `response [n] p ↝ q` becomes `LeadsTo r p q` with no
re-encoding. When the tool grows the syntax, this file is what it replaces,
and the consuming statements keep their shape.

Nothing here is Cadence-specific and nothing here is assumed: these are
definitions. A liveness theorem takes the fairness it needs as an explicit
hypothesis built from them, so the scheduling assumptions of a claim are a
list of named `Prop`s at the front of its statement rather than conditions
buried in a proof.

## The one modelling choice

A `Veil.RelationalTransitionSystem`'s `next` hides the label
(`next th s s' := ∃ l, tr th s l s'`), and [`Interfaces.lean`](./Interfaces.lean)'s
`Run` is built over such an unlabelled relation, because that is all the
*contracts* need. Fairness cannot be stated that way — "this action fires"
is a statement about the label — so `LRun` below carries the label sequence
and `LRun.toRun` forgets it, which is the bridge to the contract vocabulary
(`Run`, `TimedRun`, `MVBATemporal.termination`). -/

namespace Cadence

open Veil

section

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}

/-- A **labelled run**: an infinite sequence of states with the label of each
step, starting from an initial state of a theory the system admits.

The `assumptions` field is what makes every state of a run reachable
(`LRun.reachable`), so the module's invariants are available throughout. -/
structure LRun (sys : RelationalTransitionSystem ρ σ lbl) (th : ρ) where
  /-- The state at each index. -/
  at' : Nat → σ
  /-- The label of the step out of each index. -/
  lbl : Nat → lbl
  /-- The theory is one the system admits. -/
  holds : sys.assumptions th
  /-- The run starts in an initial state. -/
  starts : sys.init th (at' 0)
  /-- Consecutive states are related by the labelled transition relation. -/
  steps : ∀ n, sys.tr th (at' n) (lbl n) (at' (n + 1))

namespace LRun

/-- Every state of a labelled run is reachable, so every invariant of the
module holds at it. -/
theorem reachable (r : LRun sys th) : ∀ n, sys.reachable th (r.at' n)
  | 0 => RelationalTransitionSystem.reachable.init _ r.holds r.starts
  | n + 1 =>
    RelationalTransitionSystem.reachable.step _ _ (reachable r n) ⟨r.lbl n, r.steps n⟩

/-- Forgetting the labels gives a `Run` in the sense of
[`Interfaces.lean`](./Interfaces.lean), which is what the module contracts'
temporal fields quantify over. -/
def toRun (r : LRun sys th) : Run σ (sys.init th) (sys.next th) where
  at' := r.at'
  starts := r.starts
  steps n := ⟨r.lbl n, r.steps n⟩

/-- **A predicate preserved by every step holds ever after.** The bridge
from a per-transition monotonicity lemma — which is what Veil's `#gen_spec`
emits — to a statement about the rest of the run. Every argument over a run
needs it and none should re-derive it. -/
theorem mono (r : LRun sys th) {P : σ → Prop}
    (hstep : ∀ n, P (r.at' n) → P (r.at' (n + 1)))
    {N : Nat} (hP : P (r.at' N)) : ∀ n, N ≤ n → P (r.at' n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hP
  | succ n _ ih => exact hstep n ih

/-- **A finite family of eventualities is one eventuality.** If each entry
of a *finite list* eventually satisfies a monotone predicate, then at some
single index they all do.

This is the formal content of "liveness must assemble a quorum": weak
fairness delivers each member's message eventually, and a quorum guard needs
them all *at the same state*. Monotonicity makes the conjunction stable and
finiteness makes it collapse — with an infinite index list only finitely
many have arrived at any finite point, and the guard never fires. It is why
liveness needs `ByzNodeSetEnum` and safety does not
([`ByzQuorum.lean`](./ByzQuorum.lean)). -/
theorem eventually_forall (r : LRun sys th) {α : Type v} (P : α → σ → Prop)
    (hmono : ∀ a n, P a (r.at' n) → P a (r.at' (n + 1))) (N : Nat) :
    ∀ (xs : List α), (∀ a ∈ xs, ∃ n, N ≤ n ∧ P a (r.at' n)) →
      ∃ n, N ≤ n ∧ ∀ a ∈ xs, P a (r.at' n)
  | [], _ => ⟨N, Nat.le_refl N, by simp⟩
  | a :: xs, h => by
    obtain ⟨na, hna, hPa⟩ := h a (by simp)
    obtain ⟨nx, hnx, hPx⟩ :=
      eventually_forall r P hmono N xs (fun b hb => h b (by simp [hb]))
    refine ⟨max na nx, Nat.le_trans hna (Nat.le_max_left _ _), fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact r.mono (P := P b) (fun m hm => hmono b m hm) hPa _ (Nat.le_max_left _ _)
    · exact r.mono (P := fun s => P b s)
        (fun m hm => hmono b m hm) (hPx b hb') _ (Nat.le_max_right _ _)

/-! ### Temporal vocabulary

Only the three shapes the fork's proposal keeps: eventually, always, and
leads-to. No LTL parser, and deliberately no nesting beyond what a
`response` obligation needs. -/

/-- `P` holds at some point of the run. -/
def Eventually (r : LRun sys th) (P : σ → Prop) : Prop :=
  ∃ n, P (r.at' n)

/-- `P` holds at every point of the run. -/
def Always (r : LRun sys th) (P : σ → Prop) : Prop :=
  ∀ n, P (r.at' n)

/-- `P ↝ Q`: from every point at which `P` holds, `Q` holds at that point or
later. This is the `response` shape of the fork's proposal, and
`Eventually` is the case `P ≡ True`. -/
def LeadsTo (r : LRun sys th) (P Q : σ → Prop) : Prop :=
  ∀ n, P (r.at' n) → ∃ m, n ≤ m ∧ Q (r.at' m)

theorem eventually_of_leadsTo {r : LRun sys th} {P Q : σ → Prop}
    (h : r.LeadsTo P Q) {n : Nat} (hP : P (r.at' n)) : r.Eventually Q :=
  let ⟨m, _, hQ⟩ := h n hP
  ⟨m, hQ⟩

end LRun

/-! ## Enabledness and the two fairness classes -/

/-- A label is **enabled** at a state when the system has a transition out of
that state under it. For a Veil action this is exactly its `require`
clauses being satisfiable by some update, which is why no separate notion of
"guard" is needed here. -/
def Enabled (sys : RelationalTransitionSystem ρ σ lbl) (th : ρ) (st : σ) (l : lbl) : Prop :=
  ∃ st', sys.tr th st l st'

/-- **Weak fairness** (the proposal's `fairness justice`): a label that is
enabled at every point from `N` on fires at some point from `N` on.

Stated as an implication per starting index rather than with nested temporal
operators, which is the form a proof actually uses and which needs no
`◇□` machinery. -/
def WeaklyFair (r : LRun sys th) (l : lbl) : Prop :=
  ∀ N, (∀ n, N ≤ n → Enabled sys th (r.at' n) l) → ∃ n, N ≤ n ∧ r.lbl n = l

/-- **Strong fairness** (the proposal's `fairness compassion`): a label
enabled at infinitely many points fires at some point from `N` on. Defined
for completeness and for the network-delivery case the proposal mentions;
the Cadence models assume only weak fairness, and `docs/MvbaPlan.md` §3.2
records why strengthening would buy nothing there. -/
def StronglyFair (r : LRun sys th) (l : lbl) : Prop :=
  ∀ N, (∀ n, ∃ m, n ≤ m ∧ Enabled sys th (r.at' m) l) → ∃ n, N ≤ n ∧ r.lbl n = l

theorem WeaklyFair.of_stronglyFair {r : LRun sys th} {l : lbl}
    (h : StronglyFair r l) : WeaklyFair r l :=
  fun N hen => h N (fun n => ⟨max N n, Nat.le_max_right _ _, hen _ (Nat.le_max_left _ _)⟩)

/-- **The form a proof uses.** If a weakly-fair label never fires from `N`
on, it must be disabled somewhere from `N` on — so a proof that the label
*stays* enabled has produced a contradiction, and a proof that it can only
be disabled by progress has produced progress. This is the contrapositive of
`WeaklyFair` and the only way this file's fairness is consumed. -/
theorem exists_disabled_of_never_fires {r : LRun sys th} {l : lbl}
    (hwf : WeaklyFair r l) {N : Nat} (hnever : ∀ n, N ≤ n → r.lbl n ≠ l) :
    ∃ n, N ≤ n ∧ ¬ Enabled sys th (r.at' n) l := by
  by_contra hc
  obtain ⟨n, hn, hfire⟩ := hwf N (fun n hn => by
    by_contra hen
    exact hc ⟨n, hn, hen⟩)
  exact hnever n hn hfire

/-- If a label fires at `n`, it was enabled at `n`. -/
theorem enabled_of_fires (r : LRun sys th) (n : Nat) :
    Enabled sys th (r.at' n) (r.lbl n) :=
  ⟨r.at' (n + 1), r.steps n⟩

end

end Cadence

/-! ## The pinned trust base

Definitions and four small lemmas about them; no axiom beyond the standard
trio, and nothing about any particular protocol. -/

/--
info: 'Cadence.exists_disabled_of_never_fires' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.exists_disabled_of_never_fires

/-- info: 'Cadence.LRun.reachable' does not depend on any axioms -/
#guard_msgs in
#print axioms Cadence.LRun.reachable
