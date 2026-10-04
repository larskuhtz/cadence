import Cadence.Composed.Schedule

/-! # Composed.Glue — the glue's run facts, for any orchestrator and slot consensus

[ConductorBounds.md](../../docs/ConductorBounds.md) §9, stage K7. Plain
Lean about the glue ([Cadence.lean](../Cadence.lean)) over arbitrary
instances of the two contracts, used by the composed claims:

* **enabledness and effects** of the handlers, from the transition bodies;
* **the glue's invariants at a reachable state**, each a projection of
  `Cadence.reachable_<invariant>` ([Composition.lean](../Composition.lean))
  in the contracts' vocabulary;
* **monotonicity along a run** of every record the claims chain;
* **what each row delivers** (`within_participating`, `within_delivered`,
  `within_skipped`, `within_appended`): from an index where its gate's
  monotone part holds, its effect holds by `ref N + δ`. A handler that gives
  an input is enabled only where the instance accepts it, so these lemmas
  take the acceptance of `participate()`, `complete(s)` and `abandon()` as
  hypotheses; [Corollary4.lean](Corollary4.lean) proves them of Chorus and
  the Conductor. -/

namespace Composed

open Cadence
open scoped Cadence.Timed

section Glue

open Classical

variable {slot node pvector proposal ostate scstate time : Type}
  [Inhabited slot] [Inhabited node] [Inhabited pvector] [Inhabited proposal] [Inhabited ostate]
  [Inhabited scstate] [Inhabited time] [slot_ord : TotalOrder slot] [time_ord : TotalOrder time]
  [fm : FaultModel node] [orch : OrchestratorSafety node slot ostate time fm.byz]
  [sc : SlotConsensusSafety slot node proposal pvector scstate fm.byz]
  {th : Cadence.Theory slot node pvector proposal ostate scstate time}
  {st st' : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate time)}

/-- Expose one glue action's transition body. -/
local macro "glue_tr" h:ident : tactic =>
  `(tactic| (simp only [Cadence.relationalTransitionSystem, Cadence.Next, Cadence.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation. -/
local macro "glue_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id] at *)

/-- Turn an enabledness goal into the action's guards. -/
local macro "glue_enabled" : tactic =>
  `(tactic| simp only [Enabled, Cadence.relationalTransitionSystem, Cadence.Next,
      Cadence.NextAct, trSimp])

local notation "GRTS" => Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time

theorem enabled_on_open {i : node} {x : slot} {a : scstate} (hi : ¬ fm.byz i)
    (ho : orch.opened st.os i x) (hn : ¬ sc.participating (st.sc_state x) i)
    (hp : sc.participate (st.sc_state x) i a) :
    Enabled GRTS th st (.on_open i x a) := by
  glue_enabled
  exact ⟨_, hi, ho, hn, hp, rfl⟩

theorem enabled_on_finalize {i : node} {x : slot} {v : pvector} {a : ostate} {b : scstate}
    (hi : ¬ fm.byz i) (ho : orch.opened st.os i x) (hf : sc.finalized (st.sc_state x) i v)
    (hd : ∀ v', st.delivered i x v' = false) (hc : orch.complete st.os i x a)
    (hab : sc.abandon (st.sc_state x) i b) :
    Enabled GRTS th st (.on_finalize i x v a b) := by
  glue_enabled
  exact ⟨_, hi, ho, hf, fun v' h => Bool.false_ne_true ((hd v').symm.trans h), hc, hab, rfl⟩

theorem enabled_record_skip {i : node} {x w : slot} (hi : ¬ fm.byz i)
    (hw : orch.opened st.os i w) (hle : slot_ord.le x w) (hne : x ≠ w) (hn : ¬ orch.opened st.os i x) :
    Enabled GRTS th st (.record_skip i x w) := by
  glue_enabled
  exact ⟨_, hi, hw, hle, hne, hn, rfl⟩

theorem enabled_on_propose {i : node} {x : slot} {p : proposal} {a : scstate} (hi : ¬ fm.byz i)
    (ho : orch.opened st.os i x) (hp : sc.participating (st.sc_state x) i)
    (hJ : th.is_proposer i x = true) (hn : ¬ ∃ p', sc.proposed (st.sc_state x) i p')
    (hpr : sc.propose (st.sc_state x) i p a) :
    Enabled GRTS th st (.on_propose i x p a) := by
  glue_enabled
  exact ⟨_, hi, ho, hp, hJ, fun p' h => hn ⟨p', h⟩, hpr, rfl⟩

theorem enabled_append {i : node} {x : slot} {v : pvector} (hi : ¬ fm.byz i)
    (hd : st.delivered i x v = true) (ha : ∀ v', st.appended i x v' = false)
    (hr : ∀ y, slot_ord.le y x → y ≠ x → st.resolved i y = true) :
    Enabled GRTS th st (.append i x v) := by
  glue_enabled
  exact ⟨_, hi, hd, fun v' h => Bool.false_ne_true ((ha v').symm.trans h),
    fun y ⟨h1, h2⟩ => hr y h1 h2, rfl⟩

set_option maxHeartbeats 2000000 in
theorem on_finalize_delivered {i : node} {x : slot} {v : pvector} {a : ostate} {b : scstate}
    (htr : (GRTS).tr th st (.on_finalize i x v a b) st') : st'.delivered i x v = true := by
  glue_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  glue_field_simp

set_option maxHeartbeats 2000000 in
theorem record_skip_resolved {i : node} {x w : slot}
    (htr : (GRTS).tr th st (.record_skip i x w) st') : st'.resolved i x = true ∧ st'.skipped i x = true := by
  glue_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  glue_field_simp

set_option maxHeartbeats 2000000 in
theorem append_appended {i : node} {x : slot} {v : pvector}
    (htr : (GRTS).tr th st (.append i x v) st') : st'.resolved i x = true ∧ st'.appended i x v = true := by
  glue_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  glue_field_simp

/-- A glue step moves the orchestrator by one of its transitions, or not at
all. -/
theorem os_trans_or_eq {l} (htr : (GRTS).tr th st l st') :
    st'.os = st.os ∨ orch.trans st.os st'.os := by
  by_cases h : OrchLabel l
  · obtain ⟨_, h'⟩ := (orchComponent th).step st l st' htr h
    exact Or.inr h'
  · exact Or.inl ((orchComponent th).frame st l st' htr h)

/-- A glue step moves slot `x`'s instance by one of its transitions, or not
at all. -/
theorem sc_trans_or_eq {l} (x : slot) (htr : (GRTS).tr th st l st') :
    st'.sc_state x = st.sc_state x ∨ sc.trans (st.sc_state x) (st'.sc_state x) := by
  by_cases h : SlotLabel x l
  · obtain ⟨_, h'⟩ := (slotComponent th x).step st l st' htr h
    exact Or.inr h'
  · exact Or.inl ((slotComponent th x).frame st l st' htr h)

/-! ### The glue's invariants, at a reachable state -/

variable (hr : (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).reachable th st)
include hr

theorem inv_orch_reachable : orch.reachable st.os := Cadence.reachable_orch_reachable hr

theorem inv_sc_reachable (x : slot) : sc.reachable (st.sc_state x) := Cadence.reachable_sc_reachable hr x

theorem inv_sc_tagged (x : slot) : sc.tag (st.sc_state x) = x := Cadence.reachable_sc_tagged hr x

theorem inv_participating_opened {i : node} {x : slot} (hi : ¬ fm.byz i)
    (h : sc.participating (st.sc_state x) i) : orch.opened st.os i x :=
  Cadence.reachable_participating_opened hr i x ⟨hi, h⟩

theorem inv_abandoned_finalized {i : node} {x : slot} (hi : ¬ fm.byz i)
    (h : sc.abandoned (st.sc_state x) i) : ∃ v, sc.finalized (st.sc_state x) i v :=
  Cadence.reachable_abandoned_after_finalize hr i x ⟨hi, h⟩

theorem inv_completed_delivered {i : node} {x : slot} (hi : ¬ fm.byz i)
    (h : orch.completed st.os i x) : ∃ v, st.delivered i x v = true :=
  Cadence.reachable_completed_delivered hr i x ⟨hi, h⟩

theorem inv_delivered_completed {i : node} {x : slot} {v : pvector} (hi : ¬ fm.byz i)
    (h : st.delivered i x v = true) : orch.completed st.os i x :=
  Cadence.reachable_delivered_completed hr i x v ⟨hi, h⟩

theorem inv_delivered_finalized {i : node} {x : slot} {v : pvector} (hi : ¬ fm.byz i)
    (h : st.delivered i x v = true) : sc.finalized (st.sc_state x) i v :=
  Cadence.reachable_delivered_finalized hr i x v ⟨hi, h⟩

theorem inv_delivered_opened {i : node} {x : slot} {v : pvector} (hi : ¬ fm.byz i)
    (h : st.delivered i x v = true) : orch.opened st.os i x :=
  Cadence.reachable_delivered_opened hr i x v ⟨hi, h⟩

theorem inv_skipped_resolved {i : node} {x : slot} (hi : ¬ fm.byz i)
    (h : st.skipped i x = true) : st.resolved i x = true :=
  Cadence.reachable_skipped_resolved hr i x ⟨hi, h⟩

theorem inv_appended_resolved {i : node} {x : slot} {v : pvector} (hi : ¬ fm.byz i)
    (h : st.appended i x v = true) : st.resolved i x = true :=
  Cadence.reachable_appended_resolved hr i x v ⟨hi, h⟩

theorem inv_bounded_concurrency {i : node} {x : slot} (hi : ¬ fm.byz i)
    (hp : sc.participating (st.sc_state x) i) (hn : ¬ sc.abandoned (st.sc_state x) i) :
    orch.opened st.os i x ∧ ¬ orch.completed st.os i x :=
  Cadence.reachable_bounded_concurrency_interval hr i x ⟨hi, hp, hn⟩

/-- An appended vector carries its slot: it was delivered, so finalized by
the slot's instance (`slot_safety`), whose tag is the slot. -/
theorem inv_appended_slot {i : node} {x : slot} {v : pvector} (hi : ¬ fm.byz i)
    (h : st.appended i x v = true) : sc.slot_of v = x := by
  have hd : st.delivered i x v = true := Cadence.reachable_appended_delivered hr i x v ⟨hi, h⟩
  have hf := inv_delivered_finalized hr hi hd
  rw [← inv_sc_tagged hr x]
  exact sc.slot_safety _ (inv_sc_reachable hr x) i v hi hf

omit hr

end Glue

/-! ## Along a run -/

section Run

open Classical

variable {slot node pvector proposal ostate scstate time : Type}
  [Inhabited slot] [Inhabited node] [Inhabited pvector] [Inhabited proposal] [Inhabited ostate]
  [Inhabited scstate] [Inhabited time] [slot_ord : TotalOrder slot] [time_ord : TotalOrder time]
  [fm : FaultModel node] [orch : OrchestratorSafety node slot ostate time fm.byz]
  [sc : SlotConsensusSafety slot node proposal pvector scstate fm.byz]
  {th : Cadence.Theory slot node pvector proposal ostate scstate time}
  [LinearOrder time]

local notation "GRTS" => Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time

variable {r : TLRun (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time) th time}

/-! ### What stays true -/

theorem run_opened_mono {N : Nat} {i : node} {x : slot} (h : orch.opened (r.at' N).os i x) :
    ∀ m, N ≤ m → orch.opened (r.at' m).os i x :=
  r.mono (P := fun st => orch.opened st.os i x) (fun n hn => by
    rcases os_trans_or_eq (r.steps n) with he | ht
    · rw [he]; exact hn
    · exact orch.opened_mono _ _ i x (inv_orch_reachable (r.reachable n)) ht hn) h

theorem run_completed_mono {N : Nat} {i : node} {x : slot} (h : orch.completed (r.at' N).os i x) :
    ∀ m, N ≤ m → orch.completed (r.at' m).os i x :=
  r.mono (P := fun st => orch.completed st.os i x) (fun n hn => by
    rcases os_trans_or_eq (r.steps n) with he | ht
    · rw [he]; exact hn
    · exact orch.completed_mono _ _ i x (inv_orch_reachable (r.reachable n)) ht hn) h

theorem run_participating_mono {N : Nat} {i : node} {x : slot}
    (h : sc.participating ((r.at' N).sc_state x) i) :
    ∀ m, N ≤ m → sc.participating ((r.at' m).sc_state x) i :=
  r.mono (P := fun st => sc.participating (st.sc_state x) i) (fun n hn => by
    rcases sc_trans_or_eq x (r.steps n) with he | ht
    · rw [he]; exact hn
    · exact sc.participating_mono _ _ i ht hn) h

theorem run_finalized_mono {N : Nat} {i : node} {x : slot} {v : pvector}
    (h : sc.finalized ((r.at' N).sc_state x) i v) :
    ∀ m, N ≤ m → sc.finalized ((r.at' m).sc_state x) i v :=
  r.mono (P := fun st => sc.finalized (st.sc_state x) i v) (fun n hn => by
    rcases sc_trans_or_eq x (r.steps n) with he | ht
    · rw [he]; exact hn
    · exact sc.finalized_mono _ _ i v (inv_sc_reachable (r.reachable n) x) ht hn) h

theorem run_delivered_mono {N : Nat} {i : node} {x : slot} {v : pvector}
    (h : (r.at' N).delivered i x v = true) : ∀ m, N ≤ m → (r.at' m).delivered i x v = true :=
  r.mono (P := fun st => st.delivered i x v = true)
    (fun n hn => Cadence.delivered.mono (r.steps n) i x v hn) h

theorem run_appended_mono {N : Nat} {i : node} {x : slot} {v : pvector}
    (h : (r.at' N).appended i x v = true) : ∀ m, N ≤ m → (r.at' m).appended i x v = true :=
  r.mono (P := fun st => st.appended i x v = true)
    (fun n hn => Cadence.appended.mono (r.steps n) i x v hn) h

theorem run_resolved_mono {N : Nat} {i : node} {x : slot}
    (h : (r.at' N).resolved i x = true) : ∀ m, N ≤ m → (r.at' m).resolved i x = true :=
  r.mono (P := fun st => st.resolved i x = true)
    (fun n hn => Cadence.resolved.mono (r.steps n) i x hn) h

theorem run_on_time_mono {N : Nat} {j : node} {x : slot} {P : proposal}
    (h : sc.on_time ((r.at' N).sc_state x) j P) :
    ∀ m, N ≤ m → sc.on_time ((r.at' m).sc_state x) j P :=
  r.mono (P := fun st => sc.on_time (st.sc_state x) j P) (fun n hn => by
    rcases sc_trans_or_eq x (r.steps n) with he | ht
    · rw [he]; exact hn
    · exact sc.on_time_mono _ _ j P (inv_sc_reachable (r.reachable n) x) ht hn) h

set_option maxHeartbeats 2000000 in
/-- **A correct proposer's proposals are its own inputs**: whatever every
`propose` input guarantees of its proposal holds of every proposal a
correct validator has made. The contract's frames keep every other step
and input from recording a correct validator's proposal. -/
theorem run_proposed_of {W : proposal → Prop}
    (hW : ∀ s i p s', sc.propose s i p s' → W p) {j : node} (hj : ¬ fm.byz j) (x : slot) :
    ∀ n p, sc.proposed ((r.at' n).sc_state x) j p → W p := by
  intro n
  induction n with
  | zero =>
    intro p h
    have hi := r.starts
    rw [(glue_init hi).2] at h
    exact absurd h (sc.init_proposed _ j p (r.holds.2.1 x))
  | succ n ih =>
    intro p h
    by_cases hold : sc.proposed ((r.at' n).sc_state x) j p
    · exact ih p hold
    · have htr := r.steps n
      cases hl : r.lbl n with
      | orch_step a =>
        rw [hl] at htr
        rw [congrFun (Cadence.orch_step.frame_sc_state htr) x] at h; exact absurd h hold
      | record_skip i y w =>
        rw [hl] at htr
        rw [congrFun (Cadence.record_skip.frame_sc_state htr) x] at h; exact absurd h hold
      | append i y v =>
        rw [hl] at htr
        rw [congrFun (Cadence.append.frame_sc_state htr) x] at h; exact absurd h hold
      | sc_step y a =>
        rw [hl] at htr
        obtain ⟨hs, he⟩ := sc_step_sc htr
        rw [he x] at h
        by_cases hy : x = y
        · subst hy; rw [if_pos rfl] at h
          exact absurd ((sc.proposed_step_frame _ _ j p hs hj).1 h) hold
        · rw [if_neg hy] at h; exact absurd h hold
      | on_open i y a =>
        rw [hl] at htr
        obtain ⟨hs, he⟩ := on_open_sc htr
        rw [he x] at h
        by_cases hy : x = y
        · subst hy; rw [if_pos rfl] at h
          exact absurd ((sc.participate_proposed_frame _ _ _ j p hs hj).1 h) hold
        · rw [if_neg hy] at h; exact absurd h hold
      | on_finalize i y v a b =>
        rw [hl] at htr
        obtain ⟨-, hs, -, he⟩ := on_finalize_eff htr
        rw [he x] at h
        by_cases hy : x = y
        · subst hy; rw [if_pos rfl] at h
          exact absurd ((sc.abandon_proposed_frame _ _ _ j p hs hj).1 h) hold
        · rw [if_neg hy] at h; exact absurd h hold
      | on_propose i y p' a =>
        rw [hl] at htr
        obtain ⟨hs, he⟩ := on_propose_sc htr
        rw [he x] at h
        by_cases hy : x = y
        · subst hy; rw [if_pos rfl] at h
          by_cases hq : j = i ∧ p = p'
          · obtain ⟨rfl, rfl⟩ := hq
            exact hW _ _ _ _ hs
          · have hne : j ≠ i ∨ p ≠ p' := by
              by_cases hji : j = i
              · exact Or.inr (fun hp => hq ⟨hji, hp⟩)
              · exact Or.inl hji
            exact absurd ((sc.propose_frame _ _ _ _ j p hs hj hne).1 h) hold
        · rw [if_neg hy] at h; exact absurd h hold

theorem run_skipped_mono {N : Nat} {i : node} {x : slot}
    (h : (r.at' N).skipped i x = true) : ∀ m, N ≤ m → (r.at' m).skipped i x = true :=
  r.mono (P := fun st => st.skipped i x = true)
    (fun n hn => Cadence.skipped.mono (r.steps n) i x hn) h

/-! ### What the rows deliver

Each row, read from an index `N` at which its gate's monotone part holds:
its effect holds by `ref N + δ`. -/

variable [AddCommMonoid time] {δ : time}

theorem bufWindow_self (N : Nat) : r.bufWindow N N δ δ ≤ r.ref N + δ := le_of_eq (max_self _)

/-- **`on_open`'s row**: an opening is followed by participation within `δ`,
when the instance accepts `participate()` everywhere. -/
theorem within_participating (rows : GlueRows th δ r)
    (hpart : ∀ s i, ∃ s', sc.participate s i s') {i : node} (hi : ¬ fm.byz i) {x : slot} {N : Nat}
    (ho : orch.opened (r.at' N).os i x) :
    r.WithinFrom N (r.ref N + δ) (fun st => sc.participating (st.sc_state x) i) :=
  r.withinFrom_of_bufferedFairFamily (rows.open_ i x hi) le_rfl (bufWindow_self N)
    (fun l ⟨a, hl⟩ st st' htr => by
      subst hl
      obtain ⟨hp, he⟩ := on_open_sc htr
      rw [he x, if_pos rfl]
      exact sc.participate_effect _ _ _ hp)
    (fun n hn _ hnot => ⟨trivial, fun hg => by
      obtain ⟨a, ha⟩ := hpart ((r.at' n).sc_state x) i
      exact ⟨_, ⟨a, rfl⟩, enabled_on_open hi hg.1 hg.2 ha⟩⟩)
    (fun n hn _ hnot => ⟨run_opened_mono ho n hn, hnot⟩)

/-- **`on_finalize`'s row**: a finalization of an opened slot is delivered
within `δ`, when the orchestrator accepts `complete(s)` for an opened,
uncompleted slot and the instance accepts `abandon()` everywhere. -/
theorem within_delivered (rows : GlueRows th δ r)
    (hcomp : ∀ o i x, orch.reachable o → ¬ fm.byz i → orch.opened o i x → ¬ orch.completed o i x →
      ∃ o', orch.complete o i x o')
    (hab : ∀ s i, ∃ s', sc.abandon s i s') {i : node} (hi : ¬ fm.byz i) {x : slot} {N : Nat}
    (ho : orch.opened (r.at' N).os i x) {v : pvector} (hf : sc.finalized ((r.at' N).sc_state x) i v) :
    r.WithinFrom N (r.ref N + δ) (fun st => ∃ v, st.delivered i x v = true) :=
  r.withinFrom_of_bufferedFairFamily (rows.finalize i x hi) le_rfl (bufWindow_self N)
    (fun l ⟨v', a, b, hl⟩ st st' htr => by
      subst hl
      exact ⟨v', on_finalize_delivered htr⟩)
    (fun n hn _ hnot => ⟨trivial, fun hg => by
      obtain ⟨-, ⟨v', hv'⟩, hd⟩ := hg
      have hnc : ¬ orch.completed (r.at' n).os i x := fun hc =>
        hnot (inv_completed_delivered (r.reachable n) hi hc)
      obtain ⟨a, ha⟩ := hcomp _ i x (inv_orch_reachable (r.reachable n)) hi (run_opened_mono ho n hn) hnc
      obtain ⟨b, hb⟩ := hab ((r.at' n).sc_state x) i
      exact ⟨_, ⟨v', a, b, rfl⟩, enabled_on_finalize hi (run_opened_mono ho n hn) hv' hd ha hb⟩⟩)
    (fun n hn _ hnot => ⟨run_opened_mono ho n hn, ⟨v, run_finalized_mono hf n hn⟩,
      fun v' => Bool.eq_false_iff.2 fun h => hnot ⟨v', h⟩⟩)

/-- **`record_skip`'s row**: a slot below an opened one that stays unopened
is recorded as skipped within `δ`. -/
theorem within_skipped (rows : GlueRows th δ r) {i : node} (hi : ¬ fm.byz i) {x w : slot} {N : Nat}
    (hw : orch.opened (r.at' N).os i w) (hle : slot_ord.le x w) (hne : x ≠ w)
    (hno : ∀ m, N ≤ m → ¬ orch.opened (r.at' m).os i x) :
    r.WithinFrom N (r.ref N + δ) (fun st => st.skipped i x = true) :=
  r.withinFrom_of_bufferedFairFamily (rows.skip i x hi) le_rfl (bufWindow_self N)
    (fun l ⟨w', hl⟩ st st' htr => by
      subst hl
      exact (record_skip_resolved htr).2)
    (fun n hn _ hnot => ⟨trivial, fun hg => by
      obtain ⟨⟨w', hw', hle', hne'⟩, hn', -⟩ := hg
      exact ⟨_, ⟨w', rfl⟩, enabled_record_skip hi hw' hle' hne' hn'⟩⟩)
    (fun n hn _ hnot => ⟨⟨w, run_opened_mono hw n hn, hle, hne⟩, hno n hn,
      Bool.eq_false_iff.2 hnot⟩)

/-- **`append`'s row**: a delivered finalization whose lower slots are all
resolved is appended within `δ`. -/
theorem within_appended (rows : GlueRows th δ r) {i : node} (hi : ¬ fm.byz i) {x : slot} {N : Nat}
    {v : pvector} (hd : (r.at' N).delivered i x v = true)
    (hres : ∀ y, slot_ord.le y x → y ≠ x → (r.at' N).resolved i y = true) :
    r.WithinFrom N (r.ref N + δ) (fun st => ∃ v, st.appended i x v = true) :=
  r.withinFrom_of_bufferedFairFamily (rows.append i x hi) le_rfl (bufWindow_self N)
    (fun l ⟨v', hl⟩ st st' htr => by
      subst hl
      exact ⟨v', (append_appended htr).2⟩)
    (fun n hn _ hnot => ⟨trivial, fun hg => by
      obtain ⟨⟨v', hv'⟩, ha, hr⟩ := hg
      exact ⟨_, ⟨v', rfl⟩, enabled_append hi hv' ha hr⟩⟩)
    (fun n hn _ hnot => ⟨⟨v, run_delivered_mono hd n hn⟩,
      fun v' => Bool.eq_false_iff.2 fun h => hnot ⟨v', h⟩,
      fun y h1 h2 => run_resolved_mono (hres y h1 h2) n hn⟩)

end Run

end Composed

/-! ## The pinned trust base

The standard Lean trio and nothing else: no `sorryAx`. -/

/--
info: 'Composed.within_participating' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.within_participating

/--
info: 'Composed.within_delivered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.within_delivered

/--
info: 'Composed.within_skipped' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.within_skipped

/--
info: 'Composed.within_appended' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.within_appended

/--
info: 'Composed.inv_appended_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.inv_appended_slot
