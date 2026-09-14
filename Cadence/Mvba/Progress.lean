import Cadence.Mvba

/-! # Mvba.Progress — disabling implies progress

The formal content of [`docs/MvbaPlan.md`](../../docs/MvbaPlan.md) §3.1(a).

Chorus's liveness argument rests on a prose fact recorded in
[`docs/Liveness.md`](../../docs/Liveness.md): its enabledness is monotone,
so an action once enabled stays enabled and weak fairness needs no further
justification. **That fact is false for `Mvba`**, whose honest actions are
guarded by the current view and by the timeout and vote flags: eleven of
the nineteen carry a guard that can go from true to false.

This file proves the weaker fact that replaces it, and it is a *theorem*,
not an assumption: whenever one of those guards is falsified, a monotone
relation has grown at a view that is not below the guard's view — the
validator entered a higher view, timed out, voted, or adopted a lock. That
is the "rank strictly increased" side condition the well-founded ranking of
`MvbaPlan.md` §3.3 will consume, and **no scheduling assumption enters
here**.

Two things are worth noting about how little the arguments need.

* **No `step_property`, so no verification conditions.** Every `Mvba` state
  relation is assigned only `true` in every action body, so Veil's
  generated whole-system monotonicity lemmas (`<relation>.mono`, emitted at
  `#gen_spec`) already cover the growth. `#veil_status Mvba` is unchanged by
  this file.
* **Only the current-view guard needs the transition at all.** The five
  flag and vote guards are facts about *any* pair of states, proven in the
  first section below: if the guard held of the first state and fails of
  the second, the witness that breaks it cannot have been present in the
  first, since the first satisfied the guard. Monotonicity is needed only
  for `in_view`, whose ghost reads `entered` both positively and
  negatively, so the positive conjunct has to be carried across the step.
-/

namespace Mvba

/-! ## The shape of the argument, once

A guard `∀ a, P a → Q a` that holds of one state and fails of another
yields a witness that is new *and* violates `Q` — new because the first
state satisfied the guard. Pure logic, stated once so the guards below are
each one line. -/

theorem exists_new_witness {α : Sort u} {P P' Q : α → Prop}
    (h : ∀ a, P a → Q a) (h' : ¬ ∀ a, P' a → Q a) :
    ∃ a, P' a ∧ ¬ P a ∧ ¬ Q a := by
  by_contra hc
  apply h'
  intro a ha
  by_contra hq
  exact hc ⟨a, ha, fun hp => hq (h a hp), hq⟩

section Order

variable {view : Type} [vord : TotalOrderWithMinimum view]

/-- In a total order, failing `le W v` is `lt v W`. -/
theorem lt_of_not_le {v W : view} (h : ¬ vord.le W v) : vord.lt v W := by
  rcases vord.le_total v W with hvw | hwv
  · refine (vord.le_lt v W).mpr ⟨hvw, ?_⟩
    rintro rfl
    exact h (vord.le_refl v)
  · exact absurd hwv h

end Order

/-! ## The flag and vote guards

Five of the six guards read a monotone relation negatively and are
falsified exactly by that relation acquiring a witness the guard excludes.
None of them needs the transition, so they are stated over an arbitrary
pair of states. -/

section StatePair

variable {node nodeset value view : Type}
  [vord : TotalOrderWithMinimum view]
  {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}

/-- The model's `in_view` ghost over the state accessors: `v` is `i`'s
maximum entered view. Used by the step lemma below. -/
def InView (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view))
    (i : node) (v : view) : Prop :=
  s.entered i v = true ∧ ∀ V, s.entered i V = true → vord.le V v

omit vord in
/-- `¬ timed_out i v`, the guard of `adopt_prepqc` and `send_commit`, is
falsified only by `i` having timed out in `v` — the growth itself. -/
theorem timed_out_of_guard_disabled
    (i : node) (v : view) (h' : ¬ st'.timed_out i v = false) :
    st'.timed_out i v = true := by
  cases hb : st'.timed_out i v with
  | false => exact absurd hb h'
  | true => rfl

/-- `∀ W, voted i W → W < v`, the guard of both Pre-Prepare handlers, is
falsified only by a new vote at a view not below `v`. -/
theorem voted_not_below_of_guard_disabled
    (i : node) (v : view)
    (h : ∀ W, st.voted i W = true → vord.lt W v)
    (h' : ¬ ∀ W, st'.voted i W = true → vord.lt W v) :
    ∃ W, st'.voted i W = true ∧ st.voted i W = false ∧ ¬ vord.lt W v := by
  obtain ⟨W, hW, hold, hlt⟩ := exists_new_witness h h'
  refine ⟨W, hW, ?_, hlt⟩
  cases hb : st.voted i W with
  | false => rfl
  | true => exact absurd hb hold

/-- `∀ W E, local_prepqc i W E → W < v`, the guard of `adopt_prepqc`, is
falsified only by a new lock at a view not below `v`. -/
theorem prepqc_not_below_of_guard_disabled
    (i : node) (v : view)
    (h : ∀ W E, st.local_prepqc i W E = true → vord.lt W v)
    (h' : ¬ ∀ W E, st'.local_prepqc i W E = true → vord.lt W v) :
    ∃ W E, st'.local_prepqc i W E = true ∧ st.local_prepqc i W E = false ∧
      ¬ vord.lt W v := by
  have h2 : ∀ p : view × value, st.local_prepqc i p.1 p.2 = true → vord.lt p.1 v :=
    fun p hp => h p.1 p.2 hp
  have h2' : ¬ ∀ p : view × value, st'.local_prepqc i p.1 p.2 = true → vord.lt p.1 v :=
    fun hm => h' fun W E hWE => hm (W, E) hWE
  obtain ⟨⟨W, E⟩, hW, hold, hlt⟩ := exists_new_witness h2 h2'
  refine ⟨W, E, hW, ?_, hlt⟩
  cases hb : st.local_prepqc i W E with
  | false => rfl
  | true => exact absurd hb hold

/-- `∀ V, entered i V → V ≤ pv`, the guard of `sync_view` and
`sync_view_adopt`, is falsified only by entering a view above `pv`. -/
theorem entered_above_of_guard_disabled
    (i : node) (pv : view)
    (h : ∀ V, st.entered i V = true → vord.le V pv)
    (h' : ¬ ∀ V, st'.entered i V = true → vord.le V pv) :
    ∃ V, st'.entered i V = true ∧ st.entered i V = false ∧ vord.lt pv V := by
  obtain ⟨V, hV, hold, hle⟩ := exists_new_witness h h'
  refine ⟨V, hV, ?_, lt_of_not_le hle⟩
  cases hb : st.entered i V with
  | false => rfl
  | true => exact absurd hb hold

omit vord in
/-- `∀ W E, ¬ local_prepqc i W E`, the guard of `timeout_noqc`, is falsified
only by `i` adopting some lock. -/
theorem prepqc_of_no_lock_guard_disabled
    (i : node)
    (h : ∀ W E, st.local_prepqc i W E = false)
    (h' : ¬ ∀ W E, st'.local_prepqc i W E = false) :
    ∃ W E, st'.local_prepqc i W E = true ∧ st.local_prepqc i W E = false := by
  by_contra hc
  apply h'
  intro W E
  cases hb : st'.local_prepqc i W E with
  | false => rfl
  | true => exact absurd ⟨W, E, hb, h W E⟩ hc

/-- `∀ W E, local_prepqc i W E → W ≤ w`, the guard of `timeout_qc`, is
falsified only by a new lock above `w`. -/
theorem prepqc_above_of_guard_disabled
    (i : node) (w : view)
    (h : ∀ W E, st.local_prepqc i W E = true → vord.le W w)
    (h' : ¬ ∀ W E, st'.local_prepqc i W E = true → vord.le W w) :
    ∃ W E, st'.local_prepqc i W E = true ∧ st.local_prepqc i W E = false ∧
      vord.lt w W := by
  have h2 : ∀ p : view × value, st.local_prepqc i p.1 p.2 = true → vord.le p.1 w :=
    fun p hp => h p.1 p.2 hp
  have h2' : ¬ ∀ p : view × value, st'.local_prepqc i p.1 p.2 = true → vord.le p.1 w :=
    fun hm => h' fun W E hWE => hm (W, E) hWE
  obtain ⟨⟨W, E⟩, hW, hold, hle⟩ := exists_new_witness h2 h2'
  refine ⟨W, E, hW, ?_, lt_of_not_le hle⟩
  cases hb : st.local_prepqc i W E with
  | false => rfl
  | true => exact absurd hb hold

end StatePair

/-! ## The current view

`in_view i v` guards nine honest actions and is the one guard whose
falsification needs the step, because its ghost reads `entered` both
positively and negatively: the positive conjunct has to be carried forward
by `entered.mono` before the maximality conjunct can be blamed. -/

section Step

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}
  {l : Label node nodeset value view}

/-- **Leaving a view is entering a higher one.** If `i` was in view `v`
before the step and is not after it, `i` has entered some strictly higher
view. -/
theorem entered_higher_of_in_view_disabled
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (i : node) (v : view) (h : InView st i v) (h' : ¬ InView st' i v) :
    ∃ W, st'.entered i W = true ∧ vord.lt v W := by
  have hv : st'.entered i v = true := Mvba.entered.mono htr i v h.1
  have hmax : ¬ ∀ V, st'.entered i V = true → vord.le V v := fun hm => h' ⟨hv, hm⟩
  obtain ⟨W, hW, -, hnle⟩ := exists_new_witness h.2 hmax
  exact ⟨W, hW, lt_of_not_le hnle⟩

end Step

end Mvba

/-! ## The pinned trust base

Plain Lean over the model's generated monotonicity lemmas: the standard
trio and nothing else — no `sorryAx`, no solver, no assumption of the
model beyond what `Cadence.Mvba` already carries. -/

/--
info: 'Mvba.entered_higher_of_in_view_disabled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.entered_higher_of_in_view_disabled

/--
info: 'Mvba.voted_not_below_of_guard_disabled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.voted_not_below_of_guard_disabled

/--
info: 'Mvba.prepqc_above_of_guard_disabled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.prepqc_above_of_guard_disabled
