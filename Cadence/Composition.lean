import Cadence.Cadence
import Cadence.Conductor

/-! # Composition layer

Plain-Lean theorems connecting the verified Veil modules to the module
contracts of [`Interfaces.lean`](./Interfaces.lean), per
`docs/ConductorDesign.md` §5.2 and `docs/CompositionContracts.md`.
Everything here rests on the per-VC theorems persisted by the `#gen_theorems`
commands in the module files (named `<Module>.<action>_<property>` /
`<Module>.initializer_<property>`), composed by ordinary induction over the
generated `RelationalTransitionSystem.reachable` relation into

> **`<Module>.invariants_of_reachable`** — every reachable state of the
> module satisfies its assembled `Invariants` conjunction —

and one named **`<Module>.reachable_<property>`** projection per conjunct.
Both are *emitted* here by `#gen_composition <Module>`, from the per-action
preservation lemmas the same `#gen_theorems` commands emit: the induction is
no longer written out in this file, and no consumer indexes the `Invariants`
conjunction positionally — a property that has been renamed or reordered
fails loudly by name. The contract instances and corollaries below are
projected from those. The trust
base is exactly that of the `#check_invariants` sweeps — and since both
modules run with proof reconstruction, that base is the standard
`propext`/`Classical.choice`/`Quot.sound` trio alone: the persisted VC
theorems are kernel-checked proofs with **no `sorryAx`**, pinned by the
`#guard_msgs` axiom checks at the end of this file. No *new* axioms or trust
is introduced here.

## What is (and is not) established

* **`Conductor.orchestratorSafety`** — `Conductor ⊨ OrchestratorSafety`: for
  every Conductor theory, the Conductor's own transition system (its `init`,
  its `next`, its `reachable`, the `complete_slot` action as the
  `complete(s)` input) is an instance of the state-level orchestrator
  contract, with *every* field proven: the closure axioms are the
  reachability constructors; the observables' monotonicity, the frame of
  `completed` under internal steps and the effect of `complete` are proven
  action by action from Veil's pre-computed transition bodies
  (`<action>.ext.tr`); the paper's Monotonicity from `[open_local_order]`
  and the `open_slot` guard; open-prefix agreement from
  `safety [open_prefix_agreement]`. This is the object the `Cadence` glue
  module consumes as its `orch` constraint — nothing is restated between
  the two.
* **`Conductor.OrchestratorResidual`** and **`orchestrator_of_residual`** —
  the remaining obligations of the full `Orchestrator` contract, stated over
  the Conductor's transition system as the fields of a Lean structure, and
  the proof that they are *all* that is missing: given a residual, the
  Conductor is a full `Orchestrator`. Integrity's timing half is proven
  inside (`safety [opened_after_start]`); Totality, `B`-Boundedness and
  `R`-Recovery, and the admissible-run model they are stated over, are the
  residual. Type-checking `orchestrator_of_residual` is what guarantees the
  residual's fields say exactly what the class says.
* **`Cadence.positional_log_safety`** — the paper's MCP Safety over
  positional logs, for the glue at *any* instances of the two contracts;
  [`System.lean`](./System.lean) instantiates it at the Conductor and Chorus
  instances.
* The `Chorus ⊨ SlotConsensusSafety` instance lives in
  [`Chorus/Compose.lean`](./Chorus/Compose.lean), so that this file does not
  depend on the Chorus build.
* **Not** established (out of scope, `docs/ChorusDesign.md` §10.1): that the
  glue's *records* of the inputs it does not drive into the contracts
  (`sc_abandoned`, `proposed`) coincide with the instances' inputs — a
  trace-level refinement seam, named in `Cadence.lean`'s header.

## Verification-engineering note (important for future edits)

The generated VC theorems and the generated `relationalTransitionSystem`
are heavily type-class-parameterised (`DecidableEq` per sort, per-field
`FieldRepresentation` instances, per-action `Decidable` instances). The
RTS definition is elaborated by Veil under `open Classical in` **without**
`DecidableEq` binders, so every decidability instance baked into it is
literally `fun a b => Classical.propDecidable (a = b)`. Two consequences,
both discovered the hard way:

1. This file must work in the same instance regime — sections bind only
   `Inhabited`/order/contract instances (no `DecidableEq`), with `open
   Classical` providing the fallback — otherwise every unification compares
   terms built from *different* `Decidable` instances and dies in deep
   structural `whnf`.
2. Applying a VC theorem *by hand* in that regime does not work: instance
   synthesis for the `χ_rep : (f : Label) → FieldRepresentation …` arguments
   diverges (the search reduces `toDomain`/`IteratedProd` per candidate), so
   every shared instance argument has to be spelled out to mirror the RTS's
   own instantiation term-for-term. This file used to carry two macros doing
   exactly that. It does not any more: `#gen_composition` *extracts* the
   canonical instantiation from the module's own `relationalTransitionSystem`
   elaboration instead of reconstructing it, which is why the two inductions
   are now one command each.
3. The step-level contract fields are still hand-written, because they relate
   *two* states and no cell states them. They are proven by unfolding an
   action's pre-computed transition body — Veil's `trSimp` simp set is
   exactly the `derived_eq` theorems and the `tr` definitions, so one
   `simp only [trSimp]` covers every action — destructuring its guards,
   substituting the post-state and simplifying the field-representation
   `get`/`set` pair at the canonical (functional) representation. The
   `conductor_tr` and `conductor_field_simp` macros package the two halves,
   and neither has to be extended when an action is added. -/

open Veil

/-- Bridge from a persisted Veil VC theorem (a
`meetsSpecificationIfSuccessfulAssuming` statement about an action) to a
Hoare triple on the action's derived transition — the form consumed by the
`reachable` induction. Composes Veil's `toTransitionDerived_sound` with
`Transition.meetsSpecificationIfSuccessful_eq`. -/
theorem triple_of_meets {ρ σ α : Type} [Inhabited α] {m : Veil.Mode}
    {act : Veil.VeilM m ρ σ α} {assu : ρ → Prop} {pre post : Veil.SProp ρ σ}
    (h : act.meetsSpecificationIfSuccessfulAssuming assu pre post) :
    ∀ r s s', assu r → pre r s → act.toTransitionDerived r s s' → post r s' := by
  intro r s s' hassu hpre htr
  rw [← Veil.VeilM.toTransitionDerived_sound] at htr
  exact ((Veil.Transition.meetsSpecificationIfSuccessful_eq act _ _).mpr h) r s s' ⟨hassu, hpre⟩ htr

/-! ## The positional-log lemma (generic half)

The paper's MCP Safety (`def:safety`) speaks about *positions* of ordered
logs; the glue module proves the slot-indexed residues. The bridge is a
protocol-independent fact about sorted association lists: if two strictly
sorted lists agree on shared keys and are mutually downward-closed (a key
of one that lies strictly below some key of the other also occurs in the
other), then they agree *positionally* on their common prefix. This is
the list-level content of `lemma:cadence-safety`'s case analysis. -/

/-- Generic positional prefix agreement for sorted association lists. -/
theorem sorted_prefix_agreement {α β : Type} {r : α → α → Prop}
    (hirr : ∀ a, ¬ r a a) (hasym : ∀ a b, r a b → r b a → False)
    (rtotal : ∀ a b, r a b ∨ a = b ∨ r b a)
    {L₁ L₂ : List (α × β)}
    (hs₁ : L₁.Pairwise (fun a b => r a.1 b.1)) (hs₂ : L₂.Pairwise (fun a b => r a.1 b.1))
    (agree : ∀ s v v', (s, v) ∈ L₁ → (s, v') ∈ L₂ → v = v')
    (down₁₂ : ∀ s v s' v', (s, v) ∈ L₁ → (s', v') ∈ L₂ → r s s' → ∃ u, (s, u) ∈ L₂)
    (down₂₁ : ∀ s v s' v', (s, v) ∈ L₂ → (s', v') ∈ L₁ → r s s' → ∃ u, (s, u) ∈ L₁) :
    ∀ k (h₁ : k < L₁.length) (h₂ : k < L₂.length), L₁[k]'h₁ = L₂[k]'h₂ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro h₁ h₂
    have mono₁ := List.pairwise_iff_getElem.mp hs₁
    have mono₂ := List.pairwise_iff_getElem.mp hs₂
    -- The two entries at position k.
    have hm₁ : L₁[k]'h₁ ∈ L₁ := List.getElem_mem h₁
    have hm₂ : L₂[k]'h₂ ∈ L₂ := List.getElem_mem h₂
    -- Key sub-argument, used symmetrically: the slot at position k of one
    -- log cannot be strictly below the slot at position k of the other.
    -- (Otherwise it occurs in the other log by downward closure, at an
    -- index < k, where the IH pins it back into the first log — clashing
    -- with strict sortedness at position k.)
    have not_lt₁₂ : ¬ r (L₁[k]'h₁).1 (L₂[k]'h₂).1 := by
      intro hr
      obtain ⟨u, hu⟩ := down₁₂ (L₁[k]'h₁).1 (L₁[k]'h₁).2 (L₂[k]'h₂).1 (L₂[k]'h₂).2
        hm₁ hm₂ hr
      obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hu
      -- j < k in L₂, since its slot is strictly below L₂[k]'s slot.
      have hjk : j < k := by
        rcases Nat.lt_trichotomy j k with h | h | h
        · exact h
        · exfalso; subst h; rw [hje] at hr; exact hirr _ hr
        · exfalso
          have := mono₂ k j h₂ hj h
          rw [hje] at this
          exact hasym _ _ hr this
      -- By IH, position j agrees, so L₁[j] carries the same slot as L₁[k].
      have hIH := IH j hjk (by omega) (by omega)
      have : (L₁[j]'(by omega)).1 = (L₁[k]'h₁).1 := by
        rw [hIH, hje]
      have hmono := mono₁ j k (by omega) h₁ hjk
      rw [this] at hmono
      exact hirr _ hmono
    have not_lt₂₁ : ¬ r (L₂[k]'h₂).1 (L₁[k]'h₁).1 := by
      intro hr
      obtain ⟨u, hu⟩ := down₂₁ (L₂[k]'h₂).1 (L₂[k]'h₂).2 (L₁[k]'h₁).1 (L₁[k]'h₁).2
        hm₂ hm₁ hr
      obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hu
      have hjk : j < k := by
        rcases Nat.lt_trichotomy j k with h | h | h
        · exact h
        · exfalso; subst h; rw [hje] at hr; exact hirr _ hr
        · exfalso
          have := mono₁ k j h₁ hj h
          rw [hje] at this
          exact hasym _ _ hr this
      have hIH := IH j hjk (by omega) (by omega)
      have : (L₂[j]'(by omega)).1 = (L₂[k]'h₂).1 := by
        rw [← hIH, hje]
      have hmono := mono₂ j k (by omega) h₂ hjk
      rw [this] at hmono
      exact hirr _ hmono
    -- Hence the slots agree, and same-slot agreement pins the vectors.
    have hslots : (L₁[k]'h₁).1 = (L₂[k]'h₂).1 := by
      rcases rtotal (L₁[k]'h₁).1 (L₂[k]'h₂).1 with h | h | h
      · exact absurd h not_lt₁₂
      · exact h
      · exact absurd h not_lt₂₁
    have hvecs : (L₁[k]'h₁).2 = (L₂[k]'h₂).2 := by
      apply agree (L₁[k]'h₁).1
      · simpa using hm₁
      · rw [hslots]; simpa using hm₂
    exact Prod.ext hslots hvecs

/-! ## Cadence glue module: `Invariants` hold in every reachable state -/

namespace Cadence
open Classical

variable {slot node pvector proposal ostate scstate : Type}
  [Inhabited slot] [Inhabited node] [Inhabited pvector] [Inhabited proposal]
  [Inhabited ostate] [Inhabited scstate]
  [TotalOrder slot] [fm : FaultModel node]
  [orch : OrchestratorSafety node slot ostate fm.byz]
  [sc : SlotConsensusSafety slot node proposal pvector scstate fm.byz]

/- Every reachable state of the Cadence glue satisfies the assembled
invariant clump — the induction over `reachable`, one case per action, each
discharged by the per-action preservation lemma `#gen_theorems` emitted in
[`Cadence.lean`](./Cadence.lean) — together with one named
`reachable_<property>` projection per conjunct, in declaration order.
Emitted by Veil from the module's own `relationalTransitionSystem`, so the
composition regime (the canonical instantiation of every VC theorem) is
extracted rather than restated here; everything goes through `addDecl` and
is kernel-checked. Stated for arbitrary instances of the two contracts:
this is the glue's claim *as a function of its assumptions*. -/
#gen_composition Cadence

/-! ### MCP Safety in positional form (`def:safety`, `lemma:cadence-safety`)

The paper's top-level safety property over ordered local logs, derived
from the SMT-checked slot-indexed residues: `log_agreement` gives
same-slot agreement, and `skip_agreement` + `appended_prefix_resolved` +
`resolved_backed` (+ the `appended → delivered → opened` chain) give
mutual downward closure; `sorted_prefix_agreement` lifts the two to
positional prefix consistency. A validator's *local log* is any list
enumerating its `appended` relation in strictly increasing slot order
(`IsLog`) — existence of such a list for a reachable state is a
finiteness fact (each action appends at most one entry) deliberately not
formalised; the theorem quantifies over any such enumeration, exactly
matching the paper's `local_log(p, t)`. -/

/-- `v` is appended for slot `s` in `i`'s local log, in state `st`. -/
def AppendedIn
    (st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate))
    (i : node) (s : slot) (v : pvector) : Prop :=
  @Veil.FieldRepresentation.get _ _ _
    (@Cadence.instAbstractFieldRepresentation slot node pvector proposal ostate scstate
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      Cadence.State.Label.appended)
    st.appended i s v = true

/-- `L` is `i`'s local log in state `st`: the (slot, vector) pairs of
`appended`, listed in strictly increasing slot order. -/
def IsLog
    (st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate))
    (i : node) (L : List (slot × pvector)) : Prop :=
  L.Pairwise (fun a b => TotalOrder.le a.1 b.1 ∧ a.1 ≠ b.1) ∧
  ∀ s v, ((s, v) ∈ L ↔ AppendedIn st i s v)

set_option maxHeartbeats 1000000 in
/-- **MCP Safety, positional form**: two correct validators never disagree on
the log entry at a given position — for the glue over *any* orchestrator
and slot consensus satisfying the contracts. -/
theorem positional_log_safety
    {th : Cadence.Theory slot node pvector proposal ostate scstate}
    {st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate)}
    (hreach : (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate).reachable th st)
    {i j : node} (hi : ¬ fm.byz i) (hj : ¬ fm.byz j)
    {Li Lj : List (slot × pvector)} (hLi : IsLog st i Li) (hLj : IsLog st j Lj) :
    ∀ k (h₁ : k < Li.length) (h₂ : k < Lj.length), Li[k]'h₁ = Lj[k]'h₂ := by
  have hla := reachable_log_agreement hreach
  have hsa := reachable_skip_agreement hreach
  have hrb := reachable_resolved_backed hreach
  have hapr := reachable_appended_prefix_resolved hreach
  have had := reachable_appended_delivered hreach
  have hdo := reachable_delivered_opened hreach
  apply sorted_prefix_agreement (r := fun a b : slot => TotalOrder.le a b ∧ a ≠ b)
  · intro a ⟨_, hne⟩; exact hne rfl
  · intro a b ⟨hab, hne⟩ ⟨hba, _⟩; exact hne (TotalOrder.le_antisymm _ _ hab hba)
  · intro a b
    by_cases he : a = b
    · exact Or.inr (Or.inl he)
    · rcases TotalOrder.le_total a b with h | h
      · exact Or.inl ⟨h, he⟩
      · exact Or.inr (Or.inr ⟨h, fun hba => he hba.symm⟩)
  · exact hLi.1
  · exact hLj.1
  · -- same-slot agreement
    intro s v v' hv hv'
    have hai := (hLi.2 s v).mp hv
    have haj := (hLj.2 s v').mp hv'
    exact hla i j s v v' ⟨hi, hj, hai, haj⟩
  · -- downward closure Li → Lj
    intro s v s' v' hv hv' hr
    have hai := (hLi.2 s v).mp hv
    have haj := (hLj.2 s' v').mp hv'
    -- below an appended slot, everything is resolved at j
    have hres := hapr j s' s v' ⟨hj, haj, hr⟩
    rcases hrb j s ⟨hj, hres⟩ with hskip | ⟨u, hu⟩
    · -- skipped at j contradicts i having opened s
      exfalso
      have hdel := had i s v ⟨hi, hai⟩
      have hop := hdo i s v ⟨hi, hdel⟩
      exact hsa i j s ⟨hi, hj, hop⟩ hskip
    · exact ⟨u, (hLj.2 s u).mpr hu⟩
  · -- downward closure Lj → Li
    intro s v s' v' hv hv' hr
    have hai := (hLj.2 s v).mp hv
    have haj := (hLi.2 s' v').mp hv'
    have hres := hapr i s' s v' ⟨hi, haj, hr⟩
    rcases hrb i s ⟨hi, hres⟩ with hskip | ⟨u, hu⟩
    · exfalso
      have hdel := had j s v ⟨hj, hai⟩
      have hop := hdo j s v ⟨hj, hdel⟩
      exact hsa j i s ⟨hj, hi, hop⟩ hskip
    · exact ⟨u, (hLi.2 s u).mpr hu⟩

end Cadence

/-! ## Conductor: `Invariants` hold in every reachable state -/

namespace Conductor
open Classical

variable {slot window time node acsstate : Type}
  [Inhabited slot] [Inhabited window] [Inhabited time] [Inhabited node] [Inhabited acsstate]
  [TotalOrderWithMinimum slot] [TotalOrderWithMinimum window] [TotalOrder time]
  [fm : FaultModel node] [acs : ACSSafety node slot acsstate fm.byz]

/- Every reachable state of the Conductor satisfies the assembled invariant
clump — for every fault model and every ACS instance satisfying the
contract's state-level fragment — plus one named `reachable_<property>`
projection per conjunct. Emitted by Veil from the per-action preservation
lemmas `#gen_theorems` persisted in [`Conductor.lean`](./Conductor.lean),
as in the `Cadence` namespace above. -/
#gen_composition Conductor


/-! ### Conductor ⊨ OrchestratorSafety

The instance theorem of `docs/CompositionContracts.md`: the Conductor's own
transition system, packaged as the state-level orchestrator contract that
the `Cadence` glue module consumes. Every field is proven; the temporal
fields of the full `Orchestrator` are the residual structure that follows. -/

/-- The `TotalOrder` a `TotalOrderWithMinimum` carries: the contract classes
are stated over Veil's plain `TotalOrder`, the Conductor over the richer
class. Scoped, so the glue-side `slot_ord` and this bridge are the same
instance wherever the Conductor's instance is used. -/
@[implicit_reducible]
scoped instance _root_.TotalOrderWithMinimum.toTotalOrder {t : Type} [ord : TotalOrderWithMinimum t] :
    TotalOrder t where
  le := ord.le
  le_refl := ord.le_refl
  le_trans := ord.le_trans
  le_antisymm := ord.le_antisymm
  le_total := ord.le_total

/- The abstract field representation of the Conductor state, at the
canonical `Classical` instances (cf. the `ovc%` macro). -/
local macro "afr%" f:ident : term =>
  `(@Conductor.instAbstractFieldRepresentation slot window time node acsstate
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b))
    $f)

/-- The Conductor's `opened` relation, read at the canonical representation:
the contract's `open(s)` observable. -/
noncomputable abbrev Opened (st : Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
    (i : node) (s : slot) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Conductor.State.Label.opened) st.opened i s = true

/-- The Conductor's `completed` relation: the contract's record of the
`complete(s)` input. -/
noncomputable abbrev Completed (st : Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
    (i : node) (s : slot) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Conductor.State.Label.completed) st.completed i s = true

/-- The Conductor's clock `now`: the contract's `clock`. -/
noncomputable abbrev Clock (st : Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) : time :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Conductor.State.Label.now) st.now

/-- The labels of the `complete(s)` input; every other label is an internal
step of the orchestrator. -/
def Label.isComplete : Conductor.Label slot window time node acsstate → Prop
  | .complete_slot _ _ => True
  | _ => False

/-- Expose one action's pre-computed transition body: dispatch the label,
then rewrite the derived transition to `<action>.ext.tr` and unfold it with
Veil's `trSimp` set (exactly the `derived_eq` theorems and the `tr`
definitions, for every action of every module in scope). -/
local macro "conductor_tr" h:ident : tactic =>
  `(tactic| (simp only [Conductor.relationalTransitionSystem, Conductor.Next, Conductor.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
(functional) representation, in every hypothesis and the goal. -/
local macro "conductor_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [Opened, Completed, Clock,
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id] at *)

section StepFacts
variable {th : Conductor.Theory slot window time node acsstate}
  {st st' : Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)}

set_option maxHeartbeats 2000000 in
/-- An `open(s)` output stands across every action. -/
theorem opened_mono_tr {l : Conductor.Label slot window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st l st')
    (j : node) (s0 : slot) (h : Opened st j s0) : Opened st' j s0 := by
  cases l <;> conductor_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    conductor_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 2000000 in
/-- A `complete(s)` record stands across every action. -/
theorem completed_mono_tr {l : Conductor.Label slot window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st l st')
    (j : node) (s0 : slot) (h : Completed st j s0) : Completed st' j s0 := by
  cases l <;> conductor_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    conductor_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 2000000 in
/-- Internal steps leave `completed` untouched. -/
theorem completed_frame_internal {l : Conductor.Label slot window time node acsstate}
    (hl : ¬ Label.isComplete l)
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st l st')
    (j : node) (s0 : slot) : Completed st' j s0 ↔ Completed st j s0 := by
  cases l <;> simp [Label.isComplete] at hl <;> conductor_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    conductor_field_simp

set_option maxHeartbeats 2000000 in
/-- `complete(s)` at `i` records exactly `(i, s)`. -/
theorem complete_frame_other {i : node} {s : slot}
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st (.complete_slot i s) st')
    (j : node) (s0 : slot) (hne : j ≠ i ∨ s0 ≠ s) : Completed st' j s0 ↔ Completed st j s0 := by
  conductor_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); conductor_field_simp
  intro hij hs
  subst hij; subst hs
  rcases hne with h | h <;> exact absurd rfl h

theorem complete_effect_tr {i : node} {s : slot}
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st (.complete_slot i s) st') :
    Completed st' i s := by
  conductor_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); conductor_field_simp

/-- Initially nothing is opened. -/
theorem init_not_opened
    (hinit : (Conductor.relationalTransitionSystem slot window time node acsstate).init th st)
    (i : node) (s : slot) : ¬ Opened st i s := by
  simp only [Conductor.relationalTransitionSystem, Conductor.Init] at hinit
  simp only [Conductor.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); conductor_field_simp

/-- Initially nothing is completed. -/
theorem init_not_completed
    (hinit : (Conductor.relationalTransitionSystem slot window time node acsstate).init th st)
    (i : node) (s : slot) : ¬ Completed st i s := by
  simp only [Conductor.relationalTransitionSystem, Conductor.Init] at hinit
  simp only [Conductor.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); conductor_field_simp

set_option maxHeartbeats 2000000 in
/-- The paper's Monotonicity, in the contract's step form: no action opens a
slot below a slot the same correct validator has already opened without it.
Only `open_slot` opens anything, and its guard together with
`[open_local_order]` at the pre-state — the hypothesis, projected out of
reachability by `reachable_open_local_order` — rules that case out. -/
theorem monotonicity_tr {l : Conductor.Label slot window time node acsstate}
    (horder : Conductor.open_local_order
      (ρ := Conductor.Theory slot window time node acsstate)
      (σ := Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) th st)
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st l st')
    (i : node) (s s' : slot) (hi : ¬ fm.byz i)
    (hs' : Opened st i s') (hle : TotalOrderWithMinimum.le s s') (hne : s ≠ s')
    (hns : ¬ Opened st i s) : ¬ Opened st' i s := by
  have hlt : TotalOrderWithMinimum.lt s s' := (TotalOrderWithMinimum.le_lt s s').mpr ⟨hle, hne⟩
  cases l with
  | open_slot i0 s0 w f b l =>
    conductor_tr htr
    obtain ⟨_, hent, hwb, hf, hl, _, _, _, heq⟩ := htr
    subst heq
    intro hop
    simp +unfoldPartialApp [Opened, Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id] at hop
    rcases hop with ⟨rfl, rfl⟩ | hop
    · exact hns (horder _ s' _ w f b l ⟨hi, hs', hent, hwb, hf, hl, hlt⟩)
    · exact hns hop
  | _ =>
    conductor_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); conductor_field_simp; exact hns

end StepFacts

set_option maxHeartbeats 1000000 in
/-- **`Conductor ⊨ OrchestratorSafety`.** For every Conductor theory `th`
(its immutable configuration: the slots' starting times, window 1, the ACS
instances' initial states) and fault model `fm`, the Conductor's transition system is an instance of the
state-level orchestrator contract. `init` is the Conductor's initial-state
relation together with its theory assumptions, `step` its transitions other
than `complete_slot`, `complete` the `complete_slot` action, `trans` any
transition, `reachable` its reachable set; `opened` and `completed` are the
relations of those names. Every property field is proven — the closure
fields by the reachability constructors, the step fields by
`opened_mono_tr` and its siblings, Monotonicity by `monotonicity_tr`, and
open-prefix agreement by projecting `safety [open_prefix_agreement]` out of
`invariants_of_reachable`. -/
@[implicit_reducible]
noncomputable def orchestratorSafety (th : Conductor.Theory slot window time node acsstate) :
    OrchestratorSafety node slot (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
      fm.byz where
  init st := (Conductor.relationalTransitionSystem slot window time node acsstate).assumptions th ∧
    (Conductor.relationalTransitionSystem slot window time node acsstate).init th st
  step st st' := ∃ l, ¬ Label.isComplete l ∧
    (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st l st'
  complete st i s st' :=
    (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st (.complete_slot i s) st'
  trans st st' := (Conductor.relationalTransitionSystem slot window time node acsstate).next th st st'
  reachable st := (Conductor.relationalTransitionSystem slot window time node acsstate).reachable th st
  step_trans _ _ h := ⟨h.choose, h.choose_spec.2⟩
  complete_trans _ _ _ _ h := ⟨_, h⟩
  reachable_init st h := Veil.RelationalTransitionSystem.reachable.init st h.1 h.2
  reachable_trans st st' hr hn := Veil.RelationalTransitionSystem.reachable.step st st' hr hn
  opened := Opened
  completed := Completed
  opened_mono _ _ i s hn h := opened_mono_tr hn.choose_spec i s h
  completed_mono _ _ i s hn h := completed_mono_tr hn.choose_spec i s h
  complete_effect _ _ _ _ h := complete_effect_tr h
  complete_frame _ _ _ _ j s' h _ hne := complete_frame_other h j s' hne
  completed_step_frame _ _ i s h _ := completed_frame_internal h.choose_spec.1 h.choose_spec.2 i s
  init_opened _ i s h := init_not_opened h.2 i s
  init_completed _ i s h := init_not_completed h.2 i s
  monotonicity _ _ i s s' hr hn hi hs' hle hne hns :=
    monotonicity_tr (reachable_open_local_order hr) hn.choose_spec i s s' hi hs' hle hne hns
  open_prefix_agreement _ hr i j s s' hi hj his hjs hle hne :=
    reachable_open_prefix_agreement hr i j s s'
      ⟨hi, hj, his, hjs, (TotalOrderWithMinimum.le_lt s' s).mpr ⟨hle, hne⟩⟩

/-! ### The residual: what the full `Orchestrator` still owes

The fields below are the obligations of `Orchestrator` (the paper's
`mod:orchestrator_2` in full, [`Interfaces.lean`](./Interfaces.lean)) that
this development does not prove for the Conductor, restated over the
Conductor's own transition system. They are the formal counterparts of the
paper's Totality (`lemma:conductor-totality`), `B`-Boundedness
(`lem:boundedness`, `B = 2W − p`) and `R`-Recovery (`prop:smooth-windows`,
`prop:first-post-gst-window-time`, `R = 2Wτ`), together with the admissible
execution model they are stated for. `orchestrator_of_residual` proves that
they are *all* that is missing: Integrity's timing half is discharged by
`safety [opened_after_start]` on the way. Type-checking that definition is
what guarantees these restatements match the class field for field.

Why they are residual: the untimed model does not carry the per-window
induction the paper's proofs run (`Conductor.lean`, "Liveness"), and the
count `2W − p` needs window widths that the interval encoding keeps meta.
`docs/Architecture.md` §4 item 4 lists them by their meta-axiom names;
this structure is the same list as a type. -/
structure OrchestratorResidual [Add time] (th : Conductor.Theory slot window time node acsstate) where
  /-- The admissible executions — the Conductor's fairness and network
      assumptions ((F-justice), (A-acs-termination), (A-acs-totality),
      (A-sc-termination) in `Conductor.lean`'s liveness section), as a
      predicate on timed runs of the Conductor. -/
  Admissible : TimedRun (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) time
    (orchestratorSafety th).init (orchestratorSafety th).trans Clock → Prop
  admissible_exists : ∀ st, (orchestratorSafety th).init st →
    ∃ r : TimedRun (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) time
      (orchestratorSafety th).init (orchestratorSafety th).trans Clock, Admissible r ∧ r.at' 0 = st
  /-- **(A-orch-totality)** — `lemma:conductor-totality`. -/
  totality : ∀ r : TimedRun (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) time
      (orchestratorSafety th).init (orchestratorSafety th).trans Clock, Admissible r →
    ∀ i j s, ¬ fm.byz i → ¬ fm.byz j →
      r.eventually (fun st => Opened st i s) → r.eventually (fun st => Opened st j s)
  /-- `B = 2W − p`. -/
  bound : Nat
  /-- **(A-orch-boundedness)** — `lem:boundedness`; the interval form is
      `safety [bounded_tail]`, the count is this. -/
  boundedness : ∀ st, (orchestratorSafety th).reachable st → ∀ i s,
    ¬ fm.byz i → Opened st i s → ¬ Completed st i s →
    ¬ ∃ f : Fin bound → slot, Function.Injective f ∧
      ∀ k, Opened st i (f k) ∧ TotalOrderWithMinimum.le s (f k) ∧ s ≠ f k
  /-- `R = 2Wτ`. -/
  recovery_time : time
  /-- **(A-orch-recovery)** — `prop:smooth-windows`,
      `prop:first-post-gst-window-time`, under the four parameter assumptions
      `line:assumption-one..four`. -/
  recovery : ∀ r : TimedRun (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) time
      (orchestratorSafety th).init (orchestratorSafety th).trans Clock, Admissible r →
    ∀ s, TotalOrder.le (r.gst + recovery_time) (th.start_time s) →
    ∀ i, ¬ fm.byz i → r.byTime (th.start_time s) (fun st => Opened st i s)

/-- Given the residual, the Conductor is a full `Orchestrator`. The one
upper-level field this development *does* prove — Integrity's timing half,
"no slot is opened before its starting time" — is discharged here from
`safety [opened_after_start]`; everything else is the residual, field for
field. -/
@[implicit_reducible]
noncomputable def orchestrator_of_residual [Add time] {th : Conductor.Theory slot window time node acsstate}
    (h : OrchestratorResidual th) :
    Orchestrator node slot (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) time
      fm.byz where
  toOrchestratorSafety := orchestratorSafety th
  clock := Clock
  start_time := th.start_time
  Admissible := h.Admissible
  admissible_exists := h.admissible_exists
  integrity_timing _ hr i s hi hop := reachable_opened_after_start hr i s ⟨hi, hop⟩
  totality := h.totality
  bound := h.bound
  boundedness := h.boundedness
  recovery_time := h.recovery_time
  recovery := h.recovery

end Conductor

/-! ## The pinned trust base

The composition artefacts rest on the standard Lean trio alone: the
persisted VC theorems this file composes are kernel-checked reconstructed
proofs, with **no `sorryAx`**, and the step-level contract fields are proven
by unfolding Veil's own transition definitions. A regression that
reintroduces trusted SMT anywhere below these theorems (e.g. a module sweep
silently falling back to `veil.smt.trust true`) fails these guards. The
residual-conditioned full instance is pinned too: its extra assumptions
enter as a *hypothesis*, never as an axiom. -/

/--
info: 'Cadence.positional_log_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.positional_log_safety

/--
info: 'Conductor.orchestratorSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.orchestratorSafety

/--
info: 'Conductor.orchestrator_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.orchestrator_of_residual
