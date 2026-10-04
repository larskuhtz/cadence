import Cadence.Composed.Censorship

/-! # Composed.Witness.Actions — the glue's and the Conductor's actions, by their effects

[ConductorBounds.md](../../../docs/ConductorBounds.md) §8.2, stage K8. A
run is built one transition at a time, and a transition of a Veil model is
its action's guards together with the post-state its update computes. This
file states that, once per action of the glue
([Cadence.lean](../../Cadence.lean)) and of the Conductor
([Conductor.lean](../../Conductor.lean)): if the guards hold and every field
of a candidate post-state is what the update makes of it, the candidate is
the transition's post-state (`tr_<action>`). Each is proven by unfolding
the action's generated transition, so nothing here is assumed. The
composed witness ([Steps.lean](Steps.lean)) applies them with its
closed-form states.

They are the converse of the effect lemmas the claims' proofs use
([Composed/Schedule.lean](../Schedule.lean), [Conductor/Schedule.lean](../../Conductor/Schedule.lean)):
those read a transition's effect, these build one. -/

namespace Composed.Witness

open Cadence Conductor

/-! ## The glue -/

section Glue

open Classical

variable {slot node pvector proposal ostate scstate time : Type}
  [Inhabited slot] [Inhabited node] [Inhabited pvector] [Inhabited proposal] [Inhabited ostate]
  [Inhabited scstate] [Inhabited time] [slot_ord : TotalOrder slot] [time_ord : TotalOrder time]
  [fm : FaultModel node] [orch : OrchestratorSafety node slot ostate time fm.byz]
  [sc : SlotConsensusSafety slot node proposal pvector scstate fm.byz]
  {th : Cadence.Theory slot node pvector proposal ostate scstate time}
  {st st' : Cadence.State (Cadence.FieldAbstractType slot node pvector proposal ostate scstate time)}

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation. -/
local macro "glue_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id])

/-- Unfold a glue action's transition to its guards and update. -/
local macro "glue_mk" : tactic =>
  `(tactic| (simp only [Cadence.relationalTransitionSystem, Cadence.Next, Cadence.NextAct, trSimp]; glue_field_simp))

theorem tr_orch_step {a : ostate} (h : orch.step st.os a) (hos : st'.os = a)
    (hsc : st'.sc_state = st.sc_state) (hsk : st'.skipped = st.skipped) (hr : st'.resolved = st.resolved)
    (hd : st'.delivered = st.delivered) (hap : st'.appended = st.appended) :
    (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.orch_step a) st' := by
  obtain ⟨_, _, _, _, _, _⟩ := st'
  simp only at hos hsc hsk hr hd hap
  subst hos hsc hsk hr hd hap
  glue_mk
  exact h

theorem tr_sc_step {x : slot} {a : scstate} (h : sc.step (st.sc_state x) a) (hos : st'.os = st.os)
    (hsc : ∀ y, st'.sc_state y = if y = x then a else st.sc_state y) (hsk : st'.skipped = st.skipped)
    (hr : st'.resolved = st.resolved)
    (hd : st'.delivered = st.delivered) (hap : st'.appended = st.appended) :
    (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.sc_step x a) st' := by
  obtain ⟨_, _, _, _, _, _⟩ := st'
  simp only at hos hsc hsk hr hd hap
  subst hos hsk hr hd hap
  glue_mk
  refine ⟨h, ?_⟩
  intro y; rw [hsc y]; by_cases hy : y = x <;> simp [hy, Ne.symm]

theorem tr_on_open {i : node} {x : slot} {a : scstate} (hi : ¬ fm.byz i) (ho : orch.opened st.os i x)
    (hp : ¬ sc.participating (st.sc_state x) i)
    (h : sc.participate (st.sc_state x) i a) (hos : st'.os = st.os)
    (hsc : ∀ y, st'.sc_state y = if y = x then a else st.sc_state y) (hsk : st'.skipped = st.skipped)
    (hr : st'.resolved = st.resolved)
    (hd : st'.delivered = st.delivered) (hap : st'.appended = st.appended) :
    (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.on_open i x a) st' := by
  obtain ⟨_, _, _, _, _, _⟩ := st'
  simp only at hos hsc hsk hr hd hap
  subst hos hsk hr hd hap
  glue_mk
  refine ⟨hi, ho, hp, h, ?_⟩
  intro y; rw [hsc y]; by_cases hy : y = x <;> simp [hy, Ne.symm]

theorem tr_on_propose {i : node} {x : slot} {p : proposal} {a : scstate} (hi : ¬ fm.byz i)
    (ho : orch.opened st.os i x) (hp : sc.participating (st.sc_state x) i)
    (hprop : th.is_proposer i x = true) (hnp : ∀ q, ¬ sc.proposed (st.sc_state x) i q)
    (h : sc.propose (st.sc_state x) i p a) (hos : st'.os = st.os)
    (hsc : ∀ y, st'.sc_state y = if y = x then a else st.sc_state y) (hsk : st'.skipped = st.skipped)
    (hr : st'.resolved = st.resolved)
    (hd : st'.delivered = st.delivered) (hap : st'.appended = st.appended) :
    (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.on_propose i x p a) st' := by
  obtain ⟨_, _, _, _, _, _⟩ := st'
  simp only at hos hsc hsk hr hd hap
  subst hos hsk hr hd hap
  glue_mk
  refine ⟨hi, ho, hp, hprop, hnp, h, ?_⟩
  intro y; rw [hsc y]; by_cases hy : y = x <;> simp [hy, Ne.symm]

theorem tr_on_finalize {i : node} {x : slot} {v : pvector} {a : ostate} {b : scstate} (hi : ¬ fm.byz i)
    (ho : orch.opened st.os i x) (hf : sc.finalized (st.sc_state x) i v)
    (hnd : ∀ v', st.delivered i x v' = false)
    (hc : orch.complete st.os i x a) (hab : sc.abandon (st.sc_state x) i b) (hos : st'.os = a)
    (hsc : ∀ y, st'.sc_state y = if y = x then b else st.sc_state y) (hsk : st'.skipped = st.skipped)
    (hr : st'.resolved = st.resolved)
    (hd : ∀ j y w, st'.delivered j y w = (decide (j = i ∧ y = x ∧ w = v) || st.delivered j y w))
    (hap : st'.appended = st.appended) :
    (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.on_finalize i x v a b) st' := by
  obtain ⟨_, _, _, _, _, _⟩ := st'
  simp only at hos hsc hsk hr hd hap
  subst hos hsk hr hap
  glue_mk
  refine ⟨hi, ho, hf, hnd, hc, hab, ?_, ?_⟩
  · intro y; rw [hsc y]; by_cases hy : y = x <;> simp [hy, Ne.symm]
  · intro j y w; rw [hd j y w]
    by_cases h1 : j = i <;> by_cases h2 : y = x <;> by_cases h3 : w = v <;> simp [h1, h2, h3, Ne.symm]

theorem tr_append {i : node} {x : slot} {v : pvector} (hi : ¬ fm.byz i)
    (hdl : st.delivered i x v = true) (hna : ∀ v', st.appended i x v' = false)
    (hready : ∀ y, slot_ord.le y x → y ≠ x → st.resolved i y = true)
    (hos : st'.os = st.os) (hsc : st'.sc_state = st.sc_state) (hsk : st'.skipped = st.skipped)
    (hr : ∀ j y, st'.resolved j y = (decide (j = i ∧ y = x) || st.resolved j y))
    (hd : st'.delivered = st.delivered)
    (hap : ∀ j y w, st'.appended j y w = (decide (j = i ∧ y = x ∧ w = v) || st.appended j y w)) :
    (Cadence.relationalTransitionSystem slot node pvector proposal ostate scstate time).tr th st
      (.append i x v) st' := by
  obtain ⟨_, _, _, _, _, _⟩ := st'
  simp only at hos hsc hsk hr hd hap
  subst hos hsc hsk hd
  glue_mk
  refine ⟨hi, hdl, hna, fun y hy => hready y hy.1 hy.2, ?_, ?_⟩
  · intro j y; rw [hr j y]
    by_cases h1 : j = i <;> by_cases h2 : y = x <;> simp [h1, h2, Ne.symm]
  · intro j y w; rw [hap j y w]
    by_cases h1 : j = i <;> by_cases h2 : y = x <;> by_cases h3 : w = v <;> simp [h1, h2, h3, Ne.symm]

end Glue

/-! ## The Conductor -/

section Conductor

open Classical

attribute [local instance] natSlotOrder

variable {window node acsstate time : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [Inhabited time] [win_ord : TotalOrderWithMinimum window] [time_ord : TotalOrder time]
  [fm : FaultModel node] [A : ACSSafety node ℕ acsstate fm.byz]
  {th : Conductor.Theory ℕ window time node acsstate}
  {st st' : CState window time node acsstate}

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation. -/
local macro "cfs" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id])

/-- Unfold a Conductor action's transition to its guards and update. -/
local macro "cmk" : tactic =>
  `(tactic| (simp only [Conductor.relationalTransitionSystem, Conductor.Next, Conductor.NextAct, trSimp]; cfs))

/-- Split the candidate post-state into its fields, substitute the
unchanged ones, and unfold the transition. -/
local macro "cstruct" : tactic =>
  `(tactic| (obtain ⟨_, _, _, _, _, _, _⟩ := st'
             simp only at *
             subst_vars
             cmk))

theorem tr_tick {t : time} (h : TotalOrder.le st.now t) (hnow : st'.now = t)
    (has : st'.acs_state = st.acs_state) (hd : st'.acs_decided = st.acs_decided)
    (he : st'.entered = st.entered) (ho : st'.opened = st.opened) (how : st'.opened_win = st.opened_win)
    (hc : st'.completed = st.completed) :
    (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st (.tick t) st' := by
  cstruct
  exact h

theorem tr_complete_slot {i : node} {s : ℕ} (hi : ¬ fm.byz i) (ho : st.opened i s = true)
    (hnc : st.completed i s = false) (hnow : st'.now = st.now)
    (has : st'.acs_state = st.acs_state) (hd : st'.acs_decided = st.acs_decided)
    (he : st'.entered = st.entered) (hop : st'.opened = st.opened) (how : st'.opened_win = st.opened_win)
    (hc : ∀ j x, st'.completed j x = (decide (j = i ∧ x = s) || st.completed j x)) :
    (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st (.complete_slot i s) st' := by
  cstruct
  refine ⟨hi, ho, hnc, ?_⟩
  intro j x; rw [hc j x]
  by_cases h1 : j = i <;> by_cases h2 : x = s <;> simp [h1, h2, Ne.symm]

theorem tr_open_slot {i : node} {s : ℕ} {w : window} {f b l : ℕ}
    (hi : ¬ fm.byz i) (he : st.entered i w = true) (hb : WinBounds (th := th) st w f b l)
    (hfs : f ≤ s) (hsl : s ≤ l) (hno : st.opened i s = false)
    (hnow : TotalOrder.le (th.start_time s) st.now)
    (hbelow : ∀ s' w0 f0 b0 l0, st.entered i w0 = true → WinBounds (th := th) st w0 f0 b0 l0 →
      f0 ≤ s' → s' ≤ l0 → s' < s → st.opened i s' = true)
    (hnow' : st'.now = st.now)
    (has : st'.acs_state = st.acs_state) (hd : st'.acs_decided = st.acs_decided)
    (hen : st'.entered = st.entered)
    (hop : ∀ j x, st'.opened j x = (decide (j = i ∧ x = s) || st.opened j x))
    (how : ∀ j x y, st'.opened_win j x y = (decide (j = i ∧ x = s ∧ y = w) || st.opened_win j x y))
    (hc : st'.completed = st.completed) :
    (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.open_slot i s w f b l) st' := by
  cstruct
  refine ⟨hi, he, hb, hfs, hsl, hno, hnow, hbelow, ?_, ?_⟩
  · intro j x; rw [hop j x]
    by_cases h1 : j = i <;> by_cases h2 : x = s <;> simp [h1, h2, Ne.symm]
  · intro j x y; rw [how j x y]
    by_cases h1 : j = i <;> by_cases h2 : x = s <;> by_cases h3 : y = w <;> simp [h1, h2, h3, Ne.symm]

theorem tr_acs_step {w : window} {a : acsstate} (h : A.step (st.acs_state w) a) (hnow : st'.now = st.now)
    (has : ∀ x, st'.acs_state x = if x = w then a else st.acs_state x) (hd : st'.acs_decided = st.acs_decided)
    (he : st'.entered = st.entered) (hop : st'.opened = st.opened) (how : st'.opened_win = st.opened_win)
    (hc : st'.completed = st.completed) :
    (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st (.acs_step w a) st' := by
  cstruct
  refine ⟨h, ?_⟩
  intro x; rw [has x]; by_cases h1 : x = w <;> simp [h1, Ne.symm]

theorem tr_acs_propose {i : node} {w w' : window} {s : ℕ} {a : acsstate}
    (hi : ¬ fm.byz i) (hin : InWindow st i w) (hn : win_ord.next w w')
    (hnp : ∀ s', ¬ A.proposed (st.acs_state w') i s') (hrd : ReadyNext th st i w)
    (hbeyond : ∀ w0 f0 b0 l0, win_ord.next w0 w' → WinBounds (th := th) st w0 f0 b0 l0 → l0 < s)
    (hnow : TotalOrder.le st.now (th.start_time s))
    (hfirst : ∀ s' w0 f0 b0 l0, win_ord.next w0 w' → WinBounds (th := th) st w0 f0 b0 l0 →
      l0 < s' → s' < s → ¬ TotalOrder.le st.now (th.start_time s'))
    (hp : A.propose (st.acs_state w') i s a) (hnow' : st'.now = st.now)
    (has : ∀ x, st'.acs_state x = if x = w' then a else st.acs_state x) (hd : st'.acs_decided = st.acs_decided)
    (he : st'.entered = st.entered) (hop : st'.opened = st.opened) (how : st'.opened_win = st.opened_win)
    (hc : st'.completed = st.completed) :
    (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.acs_propose i w w' s a) st' := by
  cstruct
  refine ⟨hi, hin.1, hin.2, hn, hnp, hrd, hbeyond, hnow,
    hfirst, hp, ?_⟩
  intro x; rw [has x]; by_cases h1 : x = w' <;> simp [h1, Ne.symm]

theorem tr_acs_decide {w0 w : window} {first f0 b0 l0 : ℕ} {r1 r2 : node} {s1 s2 : ℕ}
    (hw : w ≠ win_ord.zero) (hnd : ∀ f b l, ¬ st.acs_decided w f b l = true)
    (hne : ∀ i, ¬ fm.byz i → ¬ st.entered i w = true) (hn : win_ord.next w0 w)
    (hb : WinBounds (th := th) st w0 f0 b0 l0)
    (hr1 : ¬ fm.byz r1) (hd1 : ∃ i, ¬ fm.byz i ∧ A.decided (st.acs_state w) i r1 s1) (hs1 : s1 ≤ first)
    (hr2 : ¬ fm.byz r2) (hd2 : ∃ i, ¬ fm.byz i ∧ A.decided (st.acs_state w) i r2 s2) (hs2 : first ≤ s2)
    (hnow : st'.now = st.now)
    (has : st'.acs_state = st.acs_state)
    (hd : ∀ x f b l, st'.acs_decided x f b l =
      (decide (x = w ∧ f = first ∧ b = th.win_boundary first ∧ l = th.win_last first) || st.acs_decided x f b l))
    (he : st'.entered = st.entered) (hop : st'.opened = st.opened) (how : st'.opened_win = st.opened_win)
    (hc : st'.completed = st.completed) :
    (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.acs_decide w0 w first f0 b0 l0 r1 s1 r2 s2) st' := by
  cstruct
  refine ⟨hw, fun f b l => by simpa using hnd f b l, fun i hi => by simpa using hne i hi, hn, hb, hr1, hd1,
    hs1, hr2, hd2, hs2, ?_⟩
  intro x f b l; rw [hd x f b l]
  by_cases h1 : x = w <;> by_cases h2 : f = first <;> by_cases h3 : b = th.win_boundary first <;>
    by_cases h4 : l = th.win_last first <;> simp [h1, h2, h3, h4, Ne.symm]

theorem tr_enter_window {i : node} {w w' : window} {f b l : ℕ} {a : acsstate}
    (hi : ¬ fm.byz i) (hin : InWindow st i w) (hn : win_ord.next w w')
    (hd : st.acs_decided w' f b l = true) (hdec : A.has_decided (st.acs_state w') i)
    (hrd : ReadyNext th st i w) (hab : A.abandon (st.acs_state w') i a) (hnow : st'.now = st.now)
    (has : ∀ x, st'.acs_state x = if x = w' then a else st.acs_state x) (hdd : st'.acs_decided = st.acs_decided)
    (he : ∀ j x, st'.entered j x = (decide (j = i ∧ x = w') || st.entered j x))
    (hop : st'.opened = st.opened) (how : st'.opened_win = st.opened_win)
    (hc : st'.completed = st.completed) :
    (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.enter_window i w w' f b l a) st' := by
  cstruct
  refine ⟨hi, hin.1, hin.2, hn, hd, hdec, hrd, hab, ?_, ?_⟩
  · intro x; rw [has x]; by_cases h1 : x = w' <;> simp [h1, Ne.symm]
  · intro j x; rw [he j x]
    by_cases h1 : j = i <;> by_cases h2 : x = w' <;> simp [h1, h2, Ne.symm]

end Conductor

end Composed.Witness
