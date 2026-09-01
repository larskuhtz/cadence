import Cadence.Cadence
import Cadence.Conductor

/-! # Composition layer

Plain-Lean theorems connecting the verified Veil modules to the module
contracts of [`Interfaces.lean`](./Interfaces.lean), per
`docs/ConductorDesign.md` §5.2. Everything here consumes the
per-VC theorems persisted by the `#gen_theorems` commands in the module
files (named `<Module>.<action>_<property>` / `<Module>.initializer_<property>`)
and composes them, by ordinary induction over the generated
`RelationalTransitionSystem.reachable` relation, into

> **`<Module>.invariants_of_reachable`** — every reachable state of the
> module satisfies its assembled `Invariants` conjunction —

from which the contract instances and corollaries are projected. The trust
base is exactly that of the `#check_invariants` sweeps — and since both
modules run with proof reconstruction (`Cadence.lean` since 2026-07-07,
`Conductor.lean` since 2026-07-10), that base is
the standard `propext`/`Classical.choice`/`Quot.sound` trio alone: the
persisted VC theorems are kernel-checked proofs with **no `sorryAx`**,
pinned by the `#guard_msgs` axiom checks at the end of this file. No *new*
axioms or trust is introduced here.

## What is (and is not) established

* `Conductor.orchestrator_instance` — a `Orchestrator` structure (the
  contract consumed by the Cadence glue's `orch_open` oracle) built from
  any reachable Conductor state, its `open_prefix_agreement` field proven
  from the module's invariants. This machine-checks the obligation-table
  row "open_prefix_agreement ↦ Conductor `safety [open_prefix_agreement]`".
* The corresponding `Chorus ⊨ SlotConsensus` instance lives in a separate
  file (so that this file does not depend on the expensive `Chorus`
  build).
* **Not** established (out of scope, `docs/ChorusDesign.md` §10.1): trace-level
  refinement — that running the implementing module *implements* the
  consuming module's oracle transitions. The composition claim remains:
  the oracle contracts are true of the implementations' reachable states
  (checked here), and the glue is verified against those contracts.

## Verification-engineering note (important for future edits)

The generated VC theorems and the generated `relationalTransitionSystem`
are heavily type-class-parameterised (`DecidableEq` per sort, per-field
`FieldRepresentation` instances, per-action `Decidable` instances). The
RTS definition is elaborated by Veil under `open Classical in` **without**
`DecidableEq` binders, so every decidability instance baked into it is
literally `fun a b => Classical.propDecidable (a = b)`. Two consequences,
both discovered the hard way:

1. This file must work in the same instance regime — sections bind only
   `Inhabited`/order instances (no `DecidableEq`), with `open Classical`
   providing the fallback — otherwise every unification compares terms
   built from *different* `Decidable` instances and dies in deep
   structural `whnf`.
2. Instance *synthesis* for the `χ_rep : (f : Label) → FieldRepresentation …`
   arguments diverges (the search reduces `toDomain`/`IteratedProd`
   per candidate). The `cvc%`/`ovc%` macros below therefore apply the VC
   theorems with **all** shared instance arguments explicit, mirroring
   the RTS's own instantiation term-for-term; only the small per-action
   `Decidable` side conditions are left to synthesis.
3. Those side conditions are passed positionally as `_`, so each call site
   states how many the theorem has. Veil canonicalises an action's extra
   parameters, and two side conditions that are literally the same collapse
   into one — so the count is a property of the *generated* theorem, not of
   the action's own guards. `#check @<Module>.<action>_<property>` shows the
   telescope; a wrong count is an "application type mismatch" naming the
   first argument that landed in the wrong slot. -/

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

/- Apply a persisted `Cadence` VC theorem at the canonical instantiation of
`Cadence.relationalTransitionSystem` (see the header note): all shared
instance arguments explicit, matching the RTS's `Classical` elaboration
term-for-term. Action arguments are passed named (e.g. `(i := i)`), leaving
the per-action `Decidable` side-condition instances to synthesis. -/
local macro "cvc%" t:ident s:term:max n:term:max p:term:max q:term:max args:term:max* : term =>
  `(@$t
    (Cadence.Theory $s $n $p $q)
    (Cadence.State (Cadence.FieldAbstractType $s $n $p $q))
    $s (fun a b => Classical.propDecidable (a = b)) inferInstance
    $n (fun a b => Classical.propDecidable (a = b)) inferInstance
    $p (fun a b => Classical.propDecidable (a = b)) inferInstance
    $q (fun a b => Classical.propDecidable (a = b)) inferInstance
    inferInstance
    (Cadence.FieldAbstractType $s $n $p $q)
    (fun f => @Cadence.instAbstractFieldRepresentation $s $n $p $q
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) f)
    (fun f => @Cadence.instLawfulAbstractFieldRepresentation $s $n $p $q
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) f)
    instIsSubStateOfRefl instIsSubReaderOfRefl
    $args*)

variable {slot node pvector proposal : Type}
  [Inhabited slot] [Inhabited node] [Inhabited pvector] [Inhabited proposal]
  [TotalOrder slot]

set_option maxHeartbeats 2000000 in
/-- Every reachable state of the Cadence glue satisfies the assembled
invariant clump — the induction over `reachable`, with the base and step
obligations discharged by the persisted `#check_invariants` VC theorems. -/
theorem invariants_of_reachable
    {th : Cadence.Theory slot node pvector proposal}
    {st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal)}
    (h : (Cadence.relationalTransitionSystem slot node pvector proposal).reachable th st) :
    Cadence.Invariants (Cadence.Theory slot node pvector proposal)
      (Cadence.State (Cadence.FieldAbstractType slot node pvector proposal))
      slot node pvector proposal
      (Cadence.FieldAbstractType slot node pvector proposal) th st := by
  induction h with
  | init s hassu hinit =>
    have htr : Cadence.initializer.ext.toTransitionDerived th default s := by
      rw [Cadence.initializer.ext.derived_eq]; exact hinit
    exact ⟨triple_of_meets (cvc% Cadence.initializer_log_agreement slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_skip_agreement slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_inclusion_lift slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_bounded_concurrency_interval slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_finalized_agreement slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_finalized_inclusion slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_opened_prefix_agreement slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_skipped_witness slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_opened_skipped_excl slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_skipped_resolved slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_appended_resolved slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_resolved_backed slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_appended_prefix_resolved slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_appended_finalized slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_finalized_opened slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_finalized_completed slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_completed_finalized slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_sc_started_iff_opened slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_sc_abandoned_iff_completed slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_abandoned_after_finalize slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_proposed_proposer_opened slot node pvector proposal) th default s hassu trivial htr,
      triple_of_meets (cvc% Cadence.initializer_pending_append_enabled slot node pvector proposal) th default s hassu trivial htr⟩
  | step s1 s2 hr hnext ih =>
    have hassu := Veil.RelationalTransitionSystem.reachable_assumptions _ th s1 hr
    obtain ⟨l, htr⟩ := hnext
    cases l with
    | orch_open i s0 =>
      exact ⟨triple_of_meets (cvc% Cadence.orch_open_log_agreement slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_skip_agreement slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_inclusion_lift slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_bounded_concurrency_interval slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_finalized_agreement slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_finalized_inclusion slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_opened_prefix_agreement slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_skipped_witness slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_opened_skipped_excl slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_skipped_resolved slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_appended_resolved slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_resolved_backed slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_appended_prefix_resolved slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_appended_finalized slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_finalized_opened slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_finalized_completed slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_completed_finalized slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_sc_started_iff_opened slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_sc_abandoned_iff_completed slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_abandoned_after_finalize slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_proposed_proposer_opened slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.orch_open_pending_append_enabled slot node pvector proposal _ _ _ i s0) th s1 s2 hassu ih htr⟩
    | record_skip i s0 s_wit =>
      exact ⟨triple_of_meets (cvc% Cadence.record_skip_log_agreement slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_skip_agreement slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_inclusion_lift slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_bounded_concurrency_interval slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_finalized_agreement slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_finalized_inclusion slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_opened_prefix_agreement slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_skipped_witness slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_opened_skipped_excl slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_skipped_resolved slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_appended_resolved slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_resolved_backed slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_appended_prefix_resolved slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_appended_finalized slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_finalized_opened slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_finalized_completed slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_completed_finalized slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_sc_started_iff_opened slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_sc_abandoned_iff_completed slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_abandoned_after_finalize slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_proposed_proposer_opened slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.record_skip_pending_append_enabled slot node pvector proposal _ i s0 s_wit) th s1 s2 hassu ih htr⟩
    | sc_finalize i s0 v =>
      exact ⟨triple_of_meets (cvc% Cadence.sc_finalize_log_agreement slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_skip_agreement slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_inclusion_lift slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_bounded_concurrency_interval slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_finalized_agreement slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_finalized_inclusion slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_opened_prefix_agreement slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_skipped_witness slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_opened_skipped_excl slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_skipped_resolved slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_appended_resolved slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_resolved_backed slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_appended_prefix_resolved slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_appended_finalized slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_finalized_opened slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_finalized_completed slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_completed_finalized slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_sc_started_iff_opened slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_sc_abandoned_iff_completed slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_abandoned_after_finalize slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_proposed_proposer_opened slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.sc_finalize_pending_append_enabled slot node pvector proposal _ _ _ i s0 v) th s1 s2 hassu ih htr⟩
    | append i s0 v =>
      exact ⟨triple_of_meets (cvc% Cadence.append_log_agreement slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_skip_agreement slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_inclusion_lift slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_bounded_concurrency_interval slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_finalized_agreement slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_finalized_inclusion slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_opened_prefix_agreement slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_skipped_witness slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_opened_skipped_excl slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_skipped_resolved slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_appended_resolved slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_resolved_backed slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_appended_prefix_resolved slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_appended_finalized slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_finalized_opened slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_finalized_completed slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_completed_finalized slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_sc_started_iff_opened slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_sc_abandoned_iff_completed slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_abandoned_after_finalize slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_proposed_proposer_opened slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr,
        triple_of_meets (cvc% Cadence.append_pending_append_enabled slot node pvector proposal _ _ i s0 v) th s1 s2 hassu ih htr⟩

/-! ### Named projections — the slot-indexed MCP safety properties

Declaration-order projections out of `Invariants` (see `Cadence.lean`),
exposed under their property names for the positional-log corollary and
external consumers. -/

section Projections
variable {th : Cadence.Theory slot node pvector proposal}
  {st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal)}

theorem reachable_log_agreement
    (h : (Cadence.relationalTransitionSystem slot node pvector proposal).reachable th st) : Cadence.log_agreement
    (ρ := Cadence.Theory slot node pvector proposal)
    (σ := Cadence.State (Cadence.FieldAbstractType slot node pvector proposal)) th st :=
  (invariants_of_reachable h).1

theorem reachable_skip_agreement
    (h : (Cadence.relationalTransitionSystem slot node pvector proposal).reachable th st) : Cadence.skip_agreement
    (ρ := Cadence.Theory slot node pvector proposal)
    (σ := Cadence.State (Cadence.FieldAbstractType slot node pvector proposal)) th st :=
  (invariants_of_reachable h).2.1

theorem reachable_inclusion_lift
    (h : (Cadence.relationalTransitionSystem slot node pvector proposal).reachable th st) : Cadence.inclusion_lift
    (ρ := Cadence.Theory slot node pvector proposal)
    (σ := Cadence.State (Cadence.FieldAbstractType slot node pvector proposal)) th st :=
  (invariants_of_reachable h).2.2.1

theorem reachable_bounded_concurrency_interval
    (h : (Cadence.relationalTransitionSystem slot node pvector proposal).reachable th st) : Cadence.bounded_concurrency_interval
    (ρ := Cadence.Theory slot node pvector proposal)
    (σ := Cadence.State (Cadence.FieldAbstractType slot node pvector proposal)) th st :=
  (invariants_of_reachable h).2.2.2.1

end Projections

/-! ### MCP Safety in positional form (`def:safety`, `lemma:cadence-safety`)

The paper's top-level safety property over ordered local logs, derived
from the SMT-checked slot-indexed residues: `log_agreement` gives
same-slot agreement, and `skip_agreement` + `appended_prefix_resolved` +
`resolved_backed` (+ the `appended → finalized → opened` chain) give
mutual downward closure; `sorted_prefix_agreement` lifts the two to
positional prefix consistency. A validator's *local log* is any list
enumerating its `appended` relation in strictly increasing slot order
(`IsLog`) — existence of such a list for a reachable state is a
finiteness fact (each action appends at most one entry) deliberately not
formalised; the theorem quantifies over any such enumeration, exactly
matching the paper's `local_log(p, t)`. -/

/-- `v` is appended for slot `s` in `i`'s local log, in state `st`. -/
def AppendedIn
    (st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal))
    (i : node) (s : slot) (v : pvector) : Prop :=
  @Veil.FieldRepresentation.get _ _ _
    (@Cadence.instAbstractFieldRepresentation slot node pvector proposal
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      Cadence.State.Label.appended)
    st.appended i s v = true

/-- `L` is `i`'s local log in state `st`: the (slot, vector) pairs of
`appended`, listed in strictly increasing slot order. -/
def IsLog
    (st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal))
    (i : node) (L : List (slot × pvector)) : Prop :=
  L.Pairwise (fun a b => TotalOrder.le a.1 b.1 ∧ a.1 ≠ b.1) ∧
  ∀ s v, ((s, v) ∈ L ↔ AppendedIn st i s v)

set_option maxHeartbeats 1000000 in
theorem positional_log_safety
    {th : Cadence.Theory slot node pvector proposal}
    {st : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal)}
    (hreach : (Cadence.relationalTransitionSystem slot node pvector proposal).reachable th st)
    {i j : node} (hi : th.is_byz i = false) (hj : th.is_byz j = false)
    {Li Lj : List (slot × pvector)} (hLi : IsLog st i Li) (hLj : IsLog st j Lj) :
    ∀ k (h₁ : k < Li.length) (h₂ : k < Lj.length), Li[k]'h₁ = Lj[k]'h₂ := by
  have hinv := invariants_of_reachable hreach
  have hla := hinv.1              -- log_agreement
  have hsa := hinv.2.1            -- skip_agreement
  have hrb := hinv.2.2.2.2.2.2.2.2.2.2.2.1        -- resolved_backed (#12)
  have hapr := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1     -- appended_prefix_resolved (#13)
  have haf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1    -- appended_finalized (#14)
  have hfo := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1  -- finalized_opened (#15)
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
    exact hla i j s v v' ⟨by simp [hi], by simp [hj], hai, haj⟩
  · -- downward closure Li → Lj
    intro s v s' v' hv hv' hr
    have hai := (hLi.2 s v).mp hv
    have haj := (hLj.2 s' v').mp hv'
    -- below an appended slot, everything is resolved at j
    have hres := hapr j s' s v' ⟨by simp [hj], haj, hr⟩
    rcases hrb j s ⟨by simp [hj], hres⟩ with hskip | ⟨u, hu⟩
    · -- skipped at j contradicts i having opened s
      exfalso
      have hfin := haf i s v ⟨by simp [hi], hai⟩
      have hop := hfo i s v ⟨by simp [hi], hfin⟩
      exact hsa i j s ⟨by simp [hi], by simp [hj], hop⟩ hskip
    · exact ⟨u, (hLj.2 s u).mpr hu⟩
  · -- downward closure Lj → Li
    intro s v s' v' hv hv' hr
    have hai := (hLj.2 s v).mp hv
    have haj := (hLi.2 s' v').mp hv'
    have hres := hapr i s' s v' ⟨by simp [hi], haj, hr⟩
    rcases hrb i s ⟨by simp [hi], hres⟩ with hskip | ⟨u, hu⟩
    · exfalso
      have hfin := haf j s v ⟨by simp [hj], hai⟩
      have hop := hfo j s v ⟨by simp [hj], hfin⟩
      exact hsa j i s ⟨by simp [hj], by simp [hi], hop⟩ hskip
    · exact ⟨u, (hLi.2 s u).mpr hu⟩

end Cadence

/-! ## Conductor: `Invariants` hold in every reachable state -/

namespace Conductor
open Classical

local macro "ovc%" t:ident s:term:max w:term:max ti:term:max n:term:max args:term:max* : term =>
  `(@$t
    (Conductor.Theory $s $w $ti $n)
    (Conductor.State (Conductor.FieldAbstractType $s $w $ti $n))
    $s (fun a b => Classical.propDecidable (a = b)) inferInstance
    $w (fun a b => Classical.propDecidable (a = b)) inferInstance
    $ti (fun a b => Classical.propDecidable (a = b)) inferInstance
    $n (fun a b => Classical.propDecidable (a = b)) inferInstance
    inferInstance inferInstance inferInstance
    (Conductor.FieldAbstractType $s $w $ti $n)
    (fun f => @Conductor.instAbstractFieldRepresentation $s $w $ti $n
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) f)
    (fun f => @Conductor.instLawfulAbstractFieldRepresentation $s $w $ti $n
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) f)
    instIsSubStateOfRefl instIsSubReaderOfRefl
    $args*)

variable {slot window time node : Type}
  [Inhabited slot] [Inhabited window] [Inhabited time] [Inhabited node]
  [TotalOrderWithMinimum slot] [TotalOrderWithMinimum window] [TotalOrder time]

set_option maxHeartbeats 4000000 in
/-- Every reachable state of the Conductor satisfies the assembled
invariant clump. -/
theorem invariants_of_reachable
    {th : Conductor.Theory slot window time node}
    {st : Conductor.State (Conductor.FieldAbstractType slot window time node)}
    (h : (Conductor.relationalTransitionSystem slot window time node).reachable th st) :
    Conductor.Invariants (Conductor.Theory slot window time node)
      (Conductor.State (Conductor.FieldAbstractType slot window time node))
      slot window time node
      (Conductor.FieldAbstractType slot window time node) th st := by
  induction h with
  | init s hassu hinit =>
    have htr : Conductor.initializer.ext.toTransitionDerived th default s := by
      rw [Conductor.initializer.ext.derived_eq]; exact hinit
    exact ⟨triple_of_meets (ovc% Conductor.initializer_window_assignment_agreement slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_win_separation slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_open_prefix_agreement slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_opened_after_start slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_bounded_tail slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_entered_prefix slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_entered_zero slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_decided_nonzero slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_bounds_shape slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_decided_downward_closed slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_win_bounds_ordered slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_acs_proposal_above_prev slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_proposal_prev_entered slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_entered_has_bounds slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_opened_backed slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_opened_win_entered slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_opened_win_contained slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_open_local_order slot window time node) th default s hassu trivial htr,
      triple_of_meets (ovc% Conductor.initializer_completed_opened slot window time node) th default s hassu trivial htr⟩
  | step s1 s2 hr hnext ih =>
    have hassu := Veil.RelationalTransitionSystem.reachable_assumptions _ th s1 hr
    obtain ⟨l, htr⟩ := hnext
    cases l with
    | tick t =>
      exact ⟨triple_of_meets (ovc% Conductor.tick_window_assignment_agreement slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_win_separation slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_open_prefix_agreement slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_opened_after_start slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_bounded_tail slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_entered_prefix slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_entered_zero slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_decided_nonzero slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_bounds_shape slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_decided_downward_closed slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_win_bounds_ordered slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_acs_proposal_above_prev slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_proposal_prev_entered slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_entered_has_bounds slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_opened_backed slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_opened_win_entered slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_opened_win_contained slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_open_local_order slot window time node _ t) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.tick_completed_opened slot window time node _ t) th s1 s2 hassu ih htr⟩
    | acs_propose i w w' s_star =>
      exact ⟨triple_of_meets (ovc% Conductor.acs_propose_window_assignment_agreement slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_win_separation slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_open_prefix_agreement slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_opened_after_start slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_bounded_tail slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_entered_prefix slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_entered_zero slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_decided_nonzero slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_bounds_shape slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_decided_downward_closed slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_win_bounds_ordered slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_acs_proposal_above_prev slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_proposal_prev_entered slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_entered_has_bounds slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_opened_backed slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_opened_win_entered slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_opened_win_contained slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_open_local_order slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_propose_completed_opened slot window time node _ _ _ _ i w w' s_star) th s1 s2 hassu ih htr⟩
    | byz_acs_propose r w s0 =>
      exact ⟨triple_of_meets (ovc% Conductor.byz_acs_propose_window_assignment_agreement slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_win_separation slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_open_prefix_agreement slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_opened_after_start slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_bounded_tail slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_entered_prefix slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_entered_zero slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_decided_nonzero slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_bounds_shape slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_decided_downward_closed slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_win_bounds_ordered slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_acs_proposal_above_prev slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_proposal_prev_entered slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_entered_has_bounds slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_opened_backed slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_opened_win_entered slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_opened_win_contained slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_open_local_order slot window time node r w s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.byz_acs_propose_completed_opened slot window time node r w s0) th s1 s2 hassu ih htr⟩
    | acs_decide w0 w first boundary last f0 b0 l0 r1 sp1 =>
      exact ⟨triple_of_meets (ovc% Conductor.acs_decide_window_assignment_agreement slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_win_separation slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_open_prefix_agreement slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_opened_after_start slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_bounded_tail slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_entered_prefix slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_entered_zero slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_decided_nonzero slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_bounds_shape slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_decided_downward_closed slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_win_bounds_ordered slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_acs_proposal_above_prev slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_proposal_prev_entered slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_entered_has_bounds slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_opened_backed slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_opened_win_entered slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_opened_win_contained slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_open_local_order slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.acs_decide_completed_opened slot window time node _ _ _ _ _ w0 w first boundary last f0 b0 l0 r1 sp1) th s1 s2 hassu ih htr⟩
    | enter_window i w w' f b l =>
      exact ⟨triple_of_meets (ovc% Conductor.enter_window_window_assignment_agreement slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_win_separation slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_open_prefix_agreement slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_opened_after_start slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_bounded_tail slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_entered_prefix slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_entered_zero slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_decided_nonzero slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_bounds_shape slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_decided_downward_closed slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_win_bounds_ordered slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_acs_proposal_above_prev slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_proposal_prev_entered slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_entered_has_bounds slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_opened_backed slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_opened_win_entered slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_opened_win_contained slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_open_local_order slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.enter_window_completed_opened slot window time node _ _ _ i w w' f b l) th s1 s2 hassu ih htr⟩
    | open_slot i s0 w f b l =>
      exact ⟨triple_of_meets (ovc% Conductor.open_slot_window_assignment_agreement slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_win_separation slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_open_prefix_agreement slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_opened_after_start slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_bounded_tail slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_entered_prefix slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_entered_zero slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_decided_nonzero slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_bounds_shape slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_decided_downward_closed slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_win_bounds_ordered slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_acs_proposal_above_prev slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_proposal_prev_entered slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_entered_has_bounds slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_opened_backed slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_opened_win_entered slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_opened_win_contained slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_open_local_order slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.open_slot_completed_opened slot window time node _ _ _ _ i s0 w f b l) th s1 s2 hassu ih htr⟩
    | complete_slot i s0 =>
      exact ⟨triple_of_meets (ovc% Conductor.complete_slot_window_assignment_agreement slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_win_separation slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_open_prefix_agreement slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_opened_after_start slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_bounded_tail slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_entered_prefix slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_entered_zero slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_decided_nonzero slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_bounds_shape slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_decided_downward_closed slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_win_bounds_ordered slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_acs_proposal_above_prev slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_proposal_prev_entered slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_entered_has_bounds slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_opened_backed slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_opened_win_entered slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_opened_win_contained slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_open_local_order slot window time node i s0) th s1 s2 hassu ih htr,
        triple_of_meets (ovc% Conductor.complete_slot_completed_opened slot window time node i s0) th s1 s2 hassu ih htr⟩

/-! ### Conductor ⊨ Orchestrator

The instance theorem of `docs/ConductorDesign.md` §5.2: from any reachable
Conductor state, the data the Cadence glue consumes — who is correct,
which slots each validator has opened/completed — forms an `Orchestrator`
structure (`Interfaces.lean`), with the one formal contract field,
`open_prefix_agreement`, discharged by the module's proven safety
property of the same name. This machine-checks the obligation-table row;
the temporal rows (totality, recovery, boundedness) remain the documented
meta-axioms. -/

/-- The `TotalOrder` a `TotalOrderWithMinimum` carries (the `Orchestrator`
class of `Interfaces.lean` is stated over plain `TotalOrder`). Registered as
a local instance so the `Orchestrator` structure below elaborates at it. -/
@[implicit_reducible]
def _root_.TotalOrderWithMinimum.toTotalOrder {t : Type} [ord : TotalOrderWithMinimum t] :
    TotalOrder t where
  le := ord.le
  le_refl := ord.le_refl
  le_trans := ord.le_trans
  le_antisymm := ord.le_antisymm
  le_total := ord.le_total

attribute [local instance] TotalOrderWithMinimum.toTotalOrder

/- The abstract field representation of the Conductor state, at the
canonical `Classical` instances (cf. the `ovc%` macro). -/
local macro "afr%" f:ident : term =>
  `(@Conductor.instAbstractFieldRepresentation slot window time node
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    $f)

set_option maxHeartbeats 1000000 in
/-- Any reachable Conductor state induces an `Orchestrator` contract
instance: `correct`/`opened`/`completed` are read off the state, and the
contract's one formal safety field is the module's proven
`safety [open_prefix_agreement]`, projected out of
`invariants_of_reachable`. -/
@[implicit_reducible]
noncomputable def orchestrator_instance
    {th : Conductor.Theory slot window time node}
    {st : Conductor.State (Conductor.FieldAbstractType slot window time node)}
    (h : (Conductor.relationalTransitionSystem slot window time node).reachable th st) :
    Orchestrator node slot where
  correct i := ¬ th.is_byz i = true
  opened i s :=
    @Veil.FieldRepresentation.get _ _ _ (afr% Conductor.State.Label.opened) st.opened i s = true
  completed i s :=
    @Veil.FieldRepresentation.get _ _ _ (afr% Conductor.State.Label.completed) st.completed i s = true
  open_prefix_agreement := by
    have hp : Conductor.open_prefix_agreement
        (ρ := Conductor.Theory slot window time node)
        (σ := Conductor.State (Conductor.FieldAbstractType slot window time node)) th st :=
      (invariants_of_reachable h).2.2.1
    intro i j s s' hci hcj hi hj hle hne
    exact hp i j s s' ⟨hci, hcj, hi, hj, (TotalOrderWithMinimum.le_lt s' s).mpr ⟨hle, hne⟩⟩

end Conductor

/-! ## The pinned trust base

Both composition artefacts rest on the standard Lean trio alone: the
persisted VC theorems this file composes are kernel-checked reconstructed
proofs, with **no `sorryAx`**. A regression
that reintroduces trusted SMT anywhere below these theorems (e.g. a module
sweep silently falling back to `veil.smt.trust true`) fails these guards. -/

/--
info: 'Cadence.positional_log_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.positional_log_safety

/--
info: 'Conductor.orchestrator_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.orchestrator_instance
