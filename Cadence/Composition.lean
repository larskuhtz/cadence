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
  `safety [open_prefix_agreement]`; and Integrity's timing half, which is
  first-order, from `safety [opened_after_start]`. This is the object the `Cadence` glue
  module consumes as its `orch` constraint — nothing is restated between
  the two.
* **`Conductor.orchestrator_of_temporal`** — that the *only* thing between
  the proven fragment and the full `Orchestrator` contract is an instance of
  `OrchestratorTemporal` at that fragment, of which this development has
  none. Totality, `B`-Boundedness, `R`-Recovery and the admissible-run model
  are that class's fields, already stated over `(orchestratorSafety th)`'s
  own relations, so nothing is restated anywhere to say what is missing.
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
3. The step-level contract fields relate *two* states, which no invariant
   cell states — but since 2026-09-10 almost none of them is hand-written
   either. Whatever the update records determine comes from Veil's
   generated step lemmas (`<relation>.mono`, `<action>.frame_<f>`,
   `<f>.init`), and what needs the invariants at the pre-state — the paper's
   Monotonicity — is a `step_property` in `Conductor.lean`, checked per
   action and applied here as `Conductor.monotonicity_step`. Exactly two
   facts remain hand-written, both about a *single* action rather than all
   of them: `complete_effect_tr` and `complete_frame_other`. They unfold
   that action's pre-computed transition body — Veil's `trSimp` simp set is
   exactly the `derived_eq` theorems and the `tr` definitions — and simplify
   the field-representation `get`/`set` pair at the canonical (functional)
   representation; the `conductor_tr` and `conductor_field_simp` macros
   package the two halves, and neither names an action, so neither has to be
   extended when one is added. `docs/CompositionContracts.md` §4 has the
   three sources and when each applies. -/

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

variable {slot node pvector proposal ostate scstate time : Type}
  [Inhabited slot] [Inhabited node] [Inhabited pvector] [Inhabited proposal]
  [Inhabited ostate] [Inhabited scstate] [Inhabited time]
  [TotalOrder slot] [TotalOrder time] [fm : FaultModel node]
  [orch : OrchestratorSafety node slot ostate time fm.byz]
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
    (st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate time))
    (i : node) (s : slot) (v : pvector) : Prop :=
  @Veil.FieldRepresentation.get _ _ _
    (@Cadence.instAbstractFieldRepresentation slot node pvector proposal ostate scstate time
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b))
      Cadence.State.Label.appended)
    st.appended i s v = true

/-- `L` is `i`'s local log in state `st`: the (slot, vector) pairs of
`appended`, listed in strictly increasing slot order. -/
def IsLog
    (st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate time))
    (i : node) (L : List (slot × pvector)) : Prop :=
  L.Pairwise (fun a b => TotalOrder.le a.1 b.1 ∧ a.1 ≠ b.1) ∧
  ∀ s v, ((s, v) ∈ L ↔ AppendedIn st i s v)

set_option maxHeartbeats 1000000 in
/-- **MCP Safety, positional form**: two correct validators never disagree on
the log entry at a given position — for the glue over *any* orchestrator
and slot consensus satisfying the contracts. -/
theorem positional_log_safety
    {th : Cadence.Theory slot node pvector proposal ostate scstate time}
    {st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate time)}
    (hreach : (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).reachable th st)
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
fields of the full `Orchestrator` are the `OrchestratorTemporal` class that
follows, of which this development has no instance. -/

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

/-- An `open(s)` output stands across every action: the generated
whole-system monotonicity lemma of `opened`. -/
theorem opened_mono_tr {l : Conductor.Label slot window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st l st')
    (j : node) (s0 : slot) (h : Opened st j s0) : Opened st' j s0 :=
  Conductor.opened.mono htr j s0 h

/-- A `complete(s)` record stands across every action: the generated
whole-system monotonicity lemma of `completed`. -/
theorem completed_mono_tr {l : Conductor.Label slot window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st l st')
    (j : node) (s0 : slot) (h : Completed st j s0) : Completed st' j s0 :=
  Conductor.completed.mono htr j s0 h

/-- Internal steps leave `completed` untouched: the generated per-action
frame lemma of each internal action. -/
theorem completed_frame_internal {l : Conductor.Label slot window time node acsstate}
    (hl : ¬ Label.isComplete l)
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st l st')
    (j : node) (s0 : slot) : Completed st' j s0 ↔ Completed st j s0 := by
  cases l with
  | complete_slot => exact (hl trivial).elim
  | tick => simp only [Completed, Conductor.tick.frame_completed htr]
  | acs_propose => simp only [Completed, Conductor.acs_propose.frame_completed htr]
  | acs_step => simp only [Completed, Conductor.acs_step.frame_completed htr]
  | acs_decide => simp only [Completed, Conductor.acs_decide.frame_completed htr]
  | enter_window => simp only [Completed, Conductor.enter_window.frame_completed htr]
  | open_slot => simp only [Completed, Conductor.open_slot.frame_completed htr]

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

/-- Initially nothing is opened: the generated initial-value lemma. -/
theorem init_not_opened
    (hinit : (Conductor.relationalTransitionSystem slot window time node acsstate).init th st)
    (i : node) (s : slot) : ¬ Opened st i s :=
  fun h => Bool.false_ne_true ((Conductor.opened.init hinit i s).symm.trans h)

/-- Initially nothing is completed: the generated initial-value lemma. -/
theorem init_not_completed
    (hinit : (Conductor.relationalTransitionSystem slot window time node acsstate).init th st)
    (i : node) (s : slot) : ¬ Completed st i s :=
  fun h => Bool.false_ne_true ((Conductor.completed.init hinit i s).symm.trans h)

/-- The paper's Monotonicity, in the contract's step form, from the checked
`step_property [monotonicity]` cells: `Conductor.monotonicity_step` is the
property over every label, from the assumptions and the invariants at the
pre-state. -/
theorem monotonicity_tr {l : Conductor.Label slot window time node acsstate}
    (hassu : (Conductor.relationalTransitionSystem slot window time node acsstate).assumptions th)
    (hinv : Conductor.Invariants (Conductor.Theory slot window time node acsstate)
      (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
      slot window time node acsstate (Conductor.FieldAbstractType slot window time node acsstate) th st)
    (htr : (Conductor.relationalTransitionSystem slot window time node acsstate).tr th st l st')
    (i : node) (s s' : slot) (hi : ¬ fm.byz i)
    (hs' : Opened st i s') (hle : TotalOrderWithMinimum.le s s') (hne : s ≠ s')
    (hns : ¬ Opened st i s) : ¬ Opened st' i s :=
  Conductor.monotonicity_step hassu hinv htr i s s' ⟨hi, hs', hle, hne, hns⟩

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
      time fm.byz where
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
  clock := Clock
  start_time := th.start_time
  opened_mono _ _ i s _ hn h := opened_mono_tr hn.choose_spec i s h
  completed_mono _ _ i s _ hn h := completed_mono_tr hn.choose_spec i s h
  complete_effect _ _ _ _ h := complete_effect_tr h
  complete_frame _ _ _ _ j s' h _ hne := complete_frame_other h j s' hne
  completed_step_frame _ _ i s h _ := completed_frame_internal h.choose_spec.1 h.choose_spec.2 i s
  init_opened _ i s h := init_not_opened h.2 i s
  init_completed _ i s h := init_not_completed h.2 i s
  integrity_timing _ hr i s hi hop := reachable_opened_after_start hr i s ⟨hi, hop⟩
  monotonicity _ _ i s s' hr hn hi hs' hle hne hns :=
    monotonicity_tr (Veil.RelationalTransitionSystem.reachable_assumptions _ th _ hr)
      (invariants_of_reachable hr) hn.choose_spec i s s' hi hs' hle hne hns
  open_prefix_agreement _ hr i j s s' hi hj his hjs hle hne :=
    reachable_open_prefix_agreement hr i j s s'
      ⟨hi, hj, his, hjs, (TotalOrderWithMinimum.le_lt s' s).mpr ⟨hle, hne⟩⟩

/-! ### What the full `Orchestrator` still owes

`OrchestratorSafety` above is proven. What remains between it and the full
`Orchestrator` (the paper's `mod:orchestrator_2`,
[`Interfaces.lean`](./Interfaces.lean)) is an instance of
**`OrchestratorTemporal … (S := orchestratorSafety th)`** — and there is
none. That is the whole statement of the gap: not a structure restating the
missing obligations at the Conductor's types, but the absence of an instance
of a class whose every field is already stated over `(orchestratorSafety
th).init`, `.trans`, `.reachable` and `.opened`.

Its fields are the formal counterparts of the paper's Totality
(`lemma:conductor-totality`), `B`-Boundedness (`lem:boundedness`,
`B = 2W − p`) and `R`-Recovery (`prop:smooth-windows`,
`prop:first-post-gst-window-time`, `R = 2Wτ`), together with the admissible
execution model they are stated for — (A-orch-totality),
(A-orch-boundedness) and (A-orch-recovery) of
[`docs/Architecture.md`](../docs/Architecture.md) §4 item 4, whose
`Admissible` is the Conductor's fairness and network assumptions
((F-justice), (A-acs-termination), (A-acs-totality), (A-sc-termination) in
`Conductor.lean`'s liveness section).

Why they are not proven: the untimed model does not carry the per-window
induction the paper's proofs run (`Conductor.lean`, "Liveness"), and the
count `2W − p` needs window widths that the interval encoding keeps meta.

Integrity's timing half, which *is* proven, is no longer discharged on the
way here: it is a first-order fact about a reachable state, so it sits in
the fragment above (`integrity_timing`, from `safety [opened_after_start]`)
and the glue may use it. -/

/-- Given a temporal level **at this fragment**, the Conductor is a full
`Orchestrator`. Nothing is restated to join them: the safety fields come
from `orchestratorSafety th`, the rest from `h`, and
`(orchestrator_of_temporal h).toOrchestratorSafety` is `orchestratorSafety
th` by `rfl` — so the composition consumes exactly what was proven. -/
@[implicit_reducible]
noncomputable def orchestrator_of_temporal [Add time]
    {th : Conductor.Theory slot window time node acsstate}
    (h : OrchestratorTemporal node slot
      (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) time
      fm.byz (S := orchestratorSafety th)) :
    Orchestrator node slot
      (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) time
      fm.byz :=
  { orchestratorSafety th, h with }

/-- The fragment the composition consumes is exactly the one that was
proven — the join drops nothing. -/
theorem orchestrator_of_temporal_toSafety [Add time]
    {th : Conductor.Theory slot window time node acsstate}
    (h : OrchestratorTemporal node slot
      (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate)) time
      fm.byz (S := orchestratorSafety th)) :
    (orchestrator_of_temporal h).toOrchestratorSafety = orchestratorSafety th := rfl

end Conductor

/-! ## The pinned trust base

The composition artefacts rest on the standard Lean trio alone: the
persisted VC theorems this file composes are kernel-checked reconstructed
proofs, with **no `sorryAx`**, and the step-level contract fields are proven
by unfolding Veil's own transition definitions. A regression that
reintroduces trusted SMT anywhere below these theorems (e.g. a module sweep
silently falling back to `veil.smt.trust true`) fails these guards. The
temporal-conditioned full instance is pinned too: its extra assumptions
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
info: 'Conductor.orchestrator_of_temporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.orchestrator_of_temporal
