import Veil
import Mathlib.Data.Nat.Nth
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

## Two modelling choices

**Runs carry labels.** A `Veil.RelationalTransitionSystem`'s `next` hides the label
(`next th s s' := ∃ l, tr th s l s'`), and [`Interfaces.lean`](./Interfaces.lean)'s
`Run` is built over such an unlabelled relation, because that is all the
*contracts* need. Fairness cannot be stated that way — "this action fires"
is a statement about the label — so `LRun` below carries the label sequence
and `LRun.toRun` forgets it, which is the bridge to the contract vocabulary
(`Run`, `TimedRun`, `MVBATemporal.termination`).

**A run of the whole can be read as a run of a part.** Chorus holds the MVBA
as an abstract state that only two of its actions advance, and the MVBA's
liveness theorem (`Mvba.termination`) is stated over runs of the MVBA's
*own* transition system. Consuming it inside a run of Chorus needs the
composed run *projected* onto the MVBA's steps, with a proof that fairness
means the same thing on both sides of the projection. That is the second
half of this file, `Component`, and it is as generic as the first: nothing
in it names a protocol. -/

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

/-! ## Components: a run of the whole, read as a run of a part

A **component** is one Veil module held inside another: the outer module's
state contains a state of the inner one, a few of the outer module's actions
advance it — by transitions the inner module itself allows — and every other
action leaves it alone. Chorus and the MVBA are the instance this exists for
(`Chorus.lean`, "The MVBA instance": the abstract state `mvba_st`, advanced
only by `mvba_step` and `mvba_propose`, whose guards are the contract's
`step` and `propose`; `docs/Liveness.md` §4), but nothing below is about
them.

The point of the definition is to consume a liveness theorem proven about
the inner module — over runs of *its* transition system, with fairness
hypotheses about *its* labels — inside a run of the outer one. That takes a
projection from an `LRun` of the whole to an `LRun` of the part, keeping
exactly the steps at which the part moved, and a proof that weak fairness
survives the re-indexing. Both are here, and the fairness transfer is an
equivalence (`Component.Projection.weaklyFair_iff`), so a fairness premise
can be *read* at either level and the projection smuggles nothing in.

**Two things the composed run does not carry**, and how the definitions
account for them:

* *The part's label.* The outer module records only the part's post-state
  (Chorus's `mvba_step` takes the next MVBA state as its one parameter), and
  two labels of the part may explain the same step. A fairness statement
  about the part's labels therefore needs a **labelling** of the part's
  steps, supplied as data (`Component.Projection.lbl`, constrained by
  `realizes`). A liveness premise stated through the projection quantifies
  over that labelling — "the part's steps in this run *can be labelled* so
  that its scheduler was fair" — which is the honest form: the composed
  model erased the labels, so an assumption about how the part was
  scheduled has to put them back. `Projection.ofScheduled` shows a
  labelling always exists; what is assumed is never that, only its
  fairness.
* *Infinitely many steps.* `LRun` is an infinite sequence, so a part that
  is stepped only finitely often has no run in its own vocabulary.
  `Component.Scheduled` says the part is stepped infinitely often. It is a
  premise about the composed run's scheduler, weaker than weak fairness of
  the part's oracle step (it says nothing about *which* step is taken), and
  it is part of a `Projection` because the projection cannot be built
  without it. -/

section Component

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {ρ' σ' lbl' : Type} {sub : RelationalTransitionSystem ρ' σ' lbl'} {th' : ρ'}

/-- **A component**: the inner system `sub` (at theory `th'`) held inside the
outer system `sys` (at theory `th`). Five facts, each a first-order statement
about the two models that an instance proves from the outer module's action
bodies — for Chorus, from the generated per-action frame lemmas of `mvba_st`
and the two oracle actions' guards. -/
structure Component (sys : RelationalTransitionSystem ρ σ lbl) (th : ρ)
    (sub : RelationalTransitionSystem ρ' σ' lbl') (th' : ρ') where
  /-- The part's state, read off the whole's. -/
  proj : σ → σ'
  /-- The outer labels that are the part's own steps. -/
  isSub : lbl → Prop
  /-- An admissible initial configuration of the whole is one of the part:
  the part's theory is admissible and its state starts initial. -/
  init : ∀ s, sys.assumptions th → sys.init th s → sub.assumptions th' ∧ sub.init th' (proj s)
  /-- Every other step of the whole leaves the part's state alone. -/
  frame : ∀ s l s', sys.tr th s l s' → ¬ isSub l → proj s' = proj s
  /-- A step of the part, taken by the whole, is a transition of the part
  under some label of its own. -/
  step : ∀ s l s', sys.tr th s l s' → isSub l → ∃ l', sub.tr th' (proj s) l' (proj s')

namespace Component

variable (C : Component sys th sub th') (r : LRun sys th)

/-- **The part is stepped infinitely often** in the run `r`. Needed because a
run is infinite; see the section header for why it is a premise and how weak
a one. -/
def Scheduled : Prop := ∀ N, ∃ n, N ≤ n ∧ C.isSub (r.lbl n)

/-- The index in `r` of the part's `k`-th step (Mathlib's `Nat.nth`; total,
and meaningful under `Scheduled`). -/
noncomputable def idx (k : Nat) : Nat := Nat.nth (fun n => C.isSub (r.lbl n)) k

open Classical in
/-- The number of the part's steps strictly before index `n` of `r`
(Mathlib's `Nat.count`): the projected index that *covers* `n`, since between
the part's steps its state is constant. -/
noncomputable def cover (n : Nat) : Nat := Nat.count (fun m => C.isSub (r.lbl m)) n

/-- Across a stretch of `r` containing no step of the part, the part's state
is constant: `frame`, iterated. -/
theorem proj_eq_of_no_sub {m n : Nat} (hmn : m ≤ n)
    (h : ∀ i, m ≤ i → i < n → ¬ C.isSub (r.lbl i)) :
    C.proj (r.at' n) = C.proj (r.at' m) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [C.frame _ _ _ (r.steps n) (h n hmn (Nat.lt_succ_self n))]
    exact ih fun i hi hin => h i hi (Nat.lt_succ_of_lt hin)

theorem not_isSub_of_between {k n : Nat} (h₁ : C.idx r k < n) (h₂ : n < C.idx r (k + 1)) :
    ¬ C.isSub (r.lbl n) := fun hn =>
  absurd (Nat.le_nth_of_lt_nth_succ h₂ hn) (Nat.not_le.mpr h₁)

theorem not_isSub_of_lt_idx_zero {n : Nat} (h : n < C.idx r 0) : ¬ C.isSub (r.lbl n) := by
  intro hn
  have h0 : C.idx r 0 = sInf (setOf fun n => C.isSub (r.lbl n)) := Nat.nth_zero
  have := Nat.sInf_le (show n ∈ setOf fun n => C.isSub (r.lbl n) from hn)
  omega

theorem proj_idx_zero : C.proj (r.at' (C.idx r 0)) = C.proj (r.at' 0) :=
  C.proj_eq_of_no_sub r (Nat.zero_le _) fun _ _ hi => C.not_isSub_of_lt_idx_zero r hi

/-- **The part's state is always reachable in the part's own system**, at
every index of the composed run — so every invariant the inner module proves
holds of the state the outer module holds. Needs no scheduling hypothesis:
it is `init`, `step` and `frame` by induction along `r`. -/
theorem reachable_proj : ∀ n, sub.reachable th' (C.proj (r.at' n))
  | 0 =>
    let ⟨ha, hi⟩ := C.init _ r.holds r.starts
    RelationalTransitionSystem.reachable.init _ ha hi
  | n + 1 => by
    by_cases hs : C.isSub (r.lbl n)
    · obtain ⟨l', hl'⟩ := C.step _ _ _ (r.steps n) hs
      exact RelationalTransitionSystem.reachable.step _ _ (reachable_proj n) ⟨l', hl'⟩
    · rw [C.frame _ _ _ (r.steps n) hs]
      exact reachable_proj n

/-! ### What `Scheduled` buys: the index arithmetic

All of it is Mathlib's `Nat.nth`/`Nat.count` theory specialised to "the
`k`-th step of the part". Nothing here mentions a labelling. -/

namespace Scheduled

variable {C r}

theorem infinite (h : C.Scheduled r) : (setOf fun n => C.isSub (r.lbl n)).Infinite :=
  Set.infinite_of_not_bddAbove <| not_bddAbove_iff.mpr fun N =>
    let ⟨n, hn, hs⟩ := h (N + 1)
    ⟨n, hs, by omega⟩

theorem isSub_idx (h : C.Scheduled r) (k : Nat) : C.isSub (r.lbl (C.idx r k)) :=
  Nat.nth_mem_of_infinite h.infinite k

theorem idx_strictMono (h : C.Scheduled r) : StrictMono (C.idx r) :=
  Nat.nth_strictMono h.infinite

theorem idx_lt_idx_succ (h : C.Scheduled r) (k : Nat) : C.idx r k < C.idx r (k + 1) :=
  h.idx_strictMono (Nat.lt_succ_self k)

theorem le_idx (h : C.Scheduled r) (k : Nat) : k ≤ C.idx r k :=
  Nat.le_nth fun hf => absurd hf h.infinite

/-- The part's state after its `k`-th step is its state at its `(k+1)`-th:
nothing of the part happens in between. -/
theorem proj_idx_succ (h : C.Scheduled r) (k : Nat) :
    C.proj (r.at' (C.idx r (k + 1))) = C.proj (r.at' (C.idx r k + 1)) :=
  C.proj_eq_of_no_sub r (h.idx_lt_idx_succ k) fun _ hi hik =>
    C.not_isSub_of_between r (Nat.lt_of_succ_le hi) hik

open Classical in
theorem cover_idx (h : C.Scheduled r) (k : Nat) : C.cover r (C.idx r k) = k :=
  Nat.count_nth_of_infinite h.infinite k

open Classical in
theorem idx_cover_of_isSub {n : Nat} (hn : C.isSub (r.lbl n)) : C.idx r (C.cover r n) = n :=
  Nat.nth_count hn

open Classical in
/-- `C.idx r (C.cover r n)` is the part's first step at or after `n`. -/
theorem le_idx_cover (h : C.Scheduled r) (n : Nat) : n ≤ C.idx r (C.cover r n) :=
  Nat.le_nth_count h.infinite n

open Classical in
theorem cover_mono : Monotone (C.cover r) := Nat.count_monotone _

theorem le_cover_of_idx_le (h : C.Scheduled r) {k n : Nat} (hkn : C.idx r k ≤ n) :
    k ≤ C.cover r n := by
  have := cover_mono (C := C) (r := r) hkn
  rwa [h.cover_idx] at this

open Classical in
/-- **The state correspondence.** The part's state at any index `n` of the
composed run is its state at the projected index covering `n`. Every
transfer of a state fact between the two runs is this lemma. -/
theorem proj_eq_proj_idx_cover (h : C.Scheduled r) (n : Nat) :
    C.proj (r.at' n) = C.proj (r.at' (C.idx r (C.cover r n))) := by
  induction n with
  | zero =>
    show C.proj (r.at' 0) = C.proj (r.at' (C.idx r (Nat.count _ 0)))
    rw [Nat.count_zero, C.proj_idx_zero]
  | succ n ih =>
    show C.proj (r.at' (n + 1)) = C.proj (r.at' (C.idx r (Nat.count _ (n + 1))))
    rw [Nat.count_succ]
    by_cases hn : C.isSub (r.lbl n)
    · rw [if_pos hn]
      change _ = C.proj (r.at' (C.idx r (C.cover r n + 1)))
      rw [h.proj_idx_succ, idx_cover_of_isSub hn]
    · rw [if_neg hn, C.frame _ _ _ (r.steps n) hn]
      exact ih

end Scheduled

/-! ### The projection -/

/-- **A projection of `r` onto the part**: a labelling of the part's steps by
labels of the part that explain them, together with the part being stepped
infinitely often. From it, `Projection.run` is a run of the part's own
transition system.

This is the object a liveness premise about the part is stated over when the
part is consumed inside a composed run: "there is a `p : C.Projection r`
whose `p.run` satisfies the part's premises". The section header says why the
labelling is data and why infinitude is a field. -/
structure Projection (C : Component sys th sub th') (r : LRun sys th) where
  /-- The part's label at each index of `r` (meaningful at the part's
  steps; arbitrary elsewhere). -/
  lbl : Nat → lbl'
  /-- At each of the part's steps, the label explains the step. -/
  realizes : ∀ n, C.isSub (r.lbl n) →
    sub.tr th' (C.proj (r.at' n)) (lbl n) (C.proj (r.at' (n + 1)))
  /-- The part is stepped infinitely often. -/
  scheduled : C.Scheduled r

open Classical in
/-- **A labelling always exists**: `Component.step` provides a label for every
step of the part, so the only content of "there is a projection satisfying
…" is what is asked of it, never its existence. -/
noncomputable def Projection.ofScheduled (h : C.Scheduled r) : C.Projection r :=
  have : Nonempty lbl' :=
    let ⟨n, _, hn⟩ := h 0
    ⟨(C.step _ _ _ (r.steps n) hn).choose⟩
  { lbl := fun n =>
      if hn : C.isSub (r.lbl n) then (C.step _ _ _ (r.steps n) hn).choose else Classical.choice this
    realizes := fun n hn => by
      simp only [dif_pos hn]
      exact (C.step _ _ _ (r.steps n) hn).choose_spec
    scheduled := h }

namespace Projection

variable {C r} (p : C.Projection r)

/-- **The projected run**: the part's state at each of its steps in `r`, with
the projection's label there. Its `k`-th state is the part's state at the
part's `k`-th step, its `k`-th step that step's label; the first state is
initial because the part is constant before its first step, and consecutive
states are related because it is constant between steps. -/
noncomputable def run : LRun sub th' where
  at' k := C.proj (r.at' (C.idx r k))
  lbl k := p.lbl (C.idx r k)
  holds := (C.init _ r.holds r.starts).1
  starts := by
    show sub.init th' (C.proj (r.at' (C.idx r 0)))
    rw [C.proj_idx_zero]
    exact (C.init _ r.holds r.starts).2
  steps k := by
    show sub.tr th' (C.proj (r.at' (C.idx r k))) (p.lbl (C.idx r k)) (C.proj (r.at' (C.idx r (k + 1))))
    rw [p.scheduled.proj_idx_succ]
    exact p.realizes _ (p.scheduled.isSub_idx k)

@[simp] theorem run_at' (k : Nat) : p.run.at' k = C.proj (r.at' (C.idx r k)) := rfl
@[simp] theorem run_lbl (k : Nat) : p.run.lbl k = p.lbl (C.idx r k) := rfl

/-- Every state of the composed run, seen by the part, is a state of the
projected run — at the index covering it. With `run_at'` (every projected
state is the part of a composed state) this is the whole correspondence. -/
theorem proj_eq_run_cover (n : Nat) : C.proj (r.at' n) = p.run.at' (C.cover r n) :=
  p.scheduled.proj_eq_proj_idx_cover n

theorem exists_run_eq (n : Nat) : ∃ k, p.run.at' k = C.proj (r.at' n) :=
  ⟨C.cover r n, (p.proj_eq_run_cover n).symm⟩

/-! #### The temporal shapes transfer, both ways

For each of the three shapes of the run vocabulary, holding of the projected
run is equivalent to holding of the composed run with the part's state read
off each composed state. These are what carry a premise stated on the
composed run (a caller's input having been given, say) to the part's run,
and the part's conclusion (every correct party decided) back. -/

theorem eventually_iff (P : σ' → Prop) :
    p.run.Eventually P ↔ r.Eventually (fun s => P (C.proj s)) :=
  ⟨fun ⟨k, hk⟩ => ⟨C.idx r k, hk⟩,
   fun ⟨n, hn⟩ => ⟨C.cover r n, by rw [← p.proj_eq_run_cover]; exact hn⟩⟩

theorem always_iff (P : σ' → Prop) :
    p.run.Always P ↔ r.Always (fun s => P (C.proj s)) :=
  ⟨fun h n => by
    show P (C.proj (r.at' n))
    rw [p.proj_eq_run_cover]
    exact h _,
   fun h k => h (C.idx r k)⟩

theorem leadsTo_iff (P Q : σ' → Prop) :
    p.run.LeadsTo P Q ↔ r.LeadsTo (fun s => P (C.proj s)) (fun s => Q (C.proj s)) := by
  constructor
  · intro h n hP
    obtain ⟨k, hk, hQ⟩ := h (C.cover r n) (p.proj_eq_run_cover n ▸ hP)
    exact ⟨C.idx r k,
      Nat.le_trans (p.scheduled.le_idx_cover n) (p.scheduled.idx_strictMono.monotone hk), hQ⟩
  · intro h k hP
    obtain ⟨m, hm, hQ⟩ := h (C.idx r k) hP
    exact ⟨C.cover r m, p.scheduled.le_cover_of_idx_le hm, p.proj_eq_run_cover m ▸ hQ⟩

/-! #### The fairness transfer -/

/-- **Weak fairness of a label of the part, read in the composed run**: if
the label is enabled — at the part's state — at every index of `r` from `N`
on, then at some index from `N` on the whole takes a step of the part that
the projection labels with it. The composed-run form of `WeaklyFair p.run l'`;
`weaklyFair_iff` says the two are the same. -/
def WeaklyFairIn (l' : lbl') : Prop :=
  ∀ N, (∀ n, N ≤ n → Enabled sub th' (C.proj (r.at' n)) l') →
    ∃ n, N ≤ n ∧ C.isSub (r.lbl n) ∧ p.lbl n = l'

/-- **Weak fairness survives the projection, in both directions.** The
direction a consumer needs is right-to-left: a fairness premise about the
part, stated over the composed run, gives `WeaklyFair` on the projected run,
which is what the part's liveness theorem consumes. Its content is exactly
`docs/Liveness.md` §4's "a label continuously enabled in the projection was
continuously enabled in the composed run": between the part's steps its state
does not change (`proj_eq_run_cover`), so enabledness from projected index
`K` on is enabledness from composed index `C.idx r K` on. The other direction
needs only that the part's `k`-th step comes no earlier than index `k`. -/
theorem weaklyFair_iff (l' : lbl') : WeaklyFair p.run l' ↔ p.WeaklyFairIn l' := by
  constructor
  · intro h N hen
    obtain ⟨k, hk, hl⟩ := h N fun k hk =>
      hen (C.idx r k) (Nat.le_trans hk (p.scheduled.le_idx k))
    exact ⟨C.idx r k, Nat.le_trans hk (p.scheduled.le_idx k), p.scheduled.isSub_idx k, hl⟩
  · intro h K hen
    obtain ⟨n, hn, hsub, hl⟩ := h (C.idx r K) fun n hn => by
      rw [p.proj_eq_run_cover n]
      exact hen (C.cover r n) (p.scheduled.le_cover_of_idx_le hn)
    refine ⟨C.cover r n, p.scheduled.le_cover_of_idx_le hn, ?_⟩
    show p.lbl (C.idx r (C.cover r n)) = l'
    rw [Scheduled.idx_cover_of_isSub hsub, hl]

end Projection
end Component

end Component

end Cadence

/-! ## The pinned trust base

Definitions and small lemmas about them; no axiom beyond the standard trio,
and nothing about any particular protocol. The component half rests on
Mathlib's `Nat.nth` and `Nat.count`, which is where the classical choice
comes from. -/

/--
info: 'Cadence.exists_disabled_of_never_fires' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.exists_disabled_of_never_fires

/-- info: 'Cadence.LRun.reachable' does not depend on any axioms -/
#guard_msgs in
#print axioms Cadence.LRun.reachable

/--
info: 'Cadence.Component.Projection.weaklyFair_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.Component.Projection.weaklyFair_iff

/--
info: 'Cadence.Component.Projection.leadsTo_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.Component.Projection.leadsTo_iff

/--
info: 'Cadence.Component.reachable_proj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.Component.reachable_proj
