import Cadence.Conductor.Schedule

/-! # Conductor.Boundedness — the count `2W − p`, and the model facts the window lemmas share

[ConductorBounds.md](../../docs/ConductorBounds.md) §9, stage K4. This file
proves **`(2W − p)`-Boundedness** (Lemma 14 (`lem:boundedness`)), the
target `BoundednessClaim` of [Schedule.lean](Schedule.lean), and collects
the plain-Lean facts about the Conductor model that it and the window
induction (stage K4's next file) both read.

## The count

Proposition 11 (`prop:open-count-window`) and Lemma 14 count the opened
slots of a correct validator `p_i` in window `ω`: readiness for `ω` asked
every slot below the previous window's readiness boundary to be complete,
so an opened, uncompleted slot `s` lies at or above it. The model states
that as an interval fact, `safety [bounded_tail]`; the widths are
`[win_bounds_shift]`'s, with the shifts `+ (W − 1)` and `+ p` of the
schedule (`WindowShifts`). What is left is counting. If `s` lies in window
`ω₀` with first slot `f`, every opened slot above `s` lies either in `ω₀`,
at most `f + W − 1`, or in `ω₀`'s successor, `W` slots; and if `p_i` has
entered that successor, `[bounded_tail]` puts `s` at or above `f + p`. So
at most `(W − 1 − p) + W` opened slots lie above `s`: with `s` itself, the
paper's `2W − p`, exactly (`boundedness`). No slack.

The proof never needs a window's successor to exist in the abstract window
order: the one window above `ω₀` that can hold an opened slot is found
from an opened slot's own window, through its entered predecessor
(`entered_pred`).

## The model facts

Read off a reachable state or a single transition, each in plain Lean:

* the window order: successors and predecessors are unique, and a window
  above `w` is at or above `w`'s successor (from `TotalOrderWithMinimum`'s
  `next_def`);
* what `enter_window` and `acs_propose` require and do
  (`enter_window_guards`, `enter_window_entered`, `acs_propose_guards`),
  and that no other step enters a window (`entered_step`) or records a
  correct validator's proposal (`proposed_step`);
* **an entered window other than window 1 has an entered predecessor**
  (`entered_pred`): an induction over reachability, since the model records
  the predecessor only in `enter_window`'s guard;
* a window has one set of bounds (`winBounds_unique`), and they persist
  (`winBounds_mono`). -/

namespace Conductor

open Cadence
open Classical

attribute [local instance] natSlotOrder

/-! ## The window order -/

section WindowOrder

variable {window : Type} [win_ord : TotalOrderWithMinimum window]

theorem win_le_of_lt {a b : window} (h : win_ord.lt a b) : win_ord.le a b :=
  ((win_ord.le_lt a b).1 h).1

theorem win_ne_of_lt {a b : window} (h : win_ord.lt a b) : a ≠ b :=
  ((win_ord.le_lt a b).1 h).2

/-- A window strictly below another is not at or above it. -/
theorem win_not_le_of_lt {a b : window} (h : win_ord.lt a b) (h' : win_ord.le b a) : False :=
  win_ne_of_lt h (win_ord.le_antisymm _ _ (win_le_of_lt h) h')

theorem win_lt_of_next {a b : window} (h : win_ord.next a b) : win_ord.lt a b :=
  ((win_ord.next_def a b).1 h).1

/-- A window above `w` is at or above `w`'s successor. -/
theorem win_next_le_of_lt {w w' x : window} (hn : win_ord.next w w') (h : win_ord.lt w x) :
    win_ord.le w' x :=
  ((win_ord.next_def w w').1 hn).2 x h

theorem win_trichotomy (a b : window) : win_ord.lt a b ∨ a = b ∨ win_ord.lt b a := by
  rcases win_ord.le_total a b with h | h
  · by_cases he : a = b
    · exact Or.inr (Or.inl he)
    · exact Or.inl ((win_ord.le_lt a b).2 ⟨h, he⟩)
  · by_cases he : b = a
    · exact Or.inr (Or.inl he.symm)
    · exact Or.inr (Or.inr ((win_ord.le_lt b a).2 ⟨h, he⟩))

/-- Successors are unique. -/
theorem win_next_unique {w a b : window} (ha : win_ord.next w a) (hb : win_ord.next w b) : a = b :=
  win_ord.le_antisymm _ _ (win_next_le_of_lt ha (win_lt_of_next hb))
    (win_next_le_of_lt hb (win_lt_of_next ha))

/-- Predecessors are unique. -/
theorem win_pred_unique {a b w : window} (ha : win_ord.next a w) (hb : win_ord.next b w) : a = b := by
  rcases win_trichotomy a b with h | h | h
  · exact (win_not_le_of_lt (win_lt_of_next hb) (win_next_le_of_lt ha h)).elim
  · exact h
  · exact (win_not_le_of_lt (win_lt_of_next ha) (win_next_le_of_lt hb h)).elim

/-- Window 1 is no window's successor. -/
theorem win_next_ne_zero {w w' : window} (h : win_ord.next w w') : w' ≠ win_ord.zero := by
  rintro rfl
  exact win_not_le_of_lt (win_lt_of_next h) (win_ord.zero_lt w)

end WindowOrder

/-! ## Single steps -/

section Steps

variable {window node acsstate time : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [Inhabited time] [win_ord : TotalOrderWithMinimum window] [time_ord : TotalOrder time]
  [fm : FaultModel node] [A : ACSSafety node ℕ acsstate fm.byz]
  {th : Conductor.Theory ℕ window time node acsstate}
  {st st' : CState window time node acsstate}

/-- Expose one action's transition body (as in [Schedule.lean](Schedule.lean)). -/
local macro "conductor_tr" h:ident : tactic =>
  `(tactic| (simp only [Conductor.relationalTransitionSystem, Conductor.Next, Conductor.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation. -/
local macro "conductor_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id] at *)

set_option maxHeartbeats 2000000 in
/-- **What window entry requires** (Algorithm 7, line 44
(`line:acs-decide`)): the validator is correct, in the predecessor window
and ready, the window's interval is recorded, and its own ACS instance has
decided. -/
theorem enter_window_guards {i : node} {w w' : window} {f b l : ℕ} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.enter_window i w w' f b l a) st') :
    ¬ fm.byz i ∧ InWindow st i w ∧ win_ord.next w w' ∧ st.acs_decided w' f b l = true ∧
      A.has_decided (st.acs_state w') i ∧ ReadyNext th st i w := by
  conductor_tr htr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ := htr
  exact ⟨h1, ⟨h2, fun x hx => Bool.eq_false_iff.mpr (h3 x hx)⟩, h4, h5, h6, h7⟩

set_option maxHeartbeats 2000000 in
/-- **What window entry does** to `entered`: it adds the one pair. -/
theorem enter_window_entered {i : node} {w w' : window} {f b l : ℕ} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.enter_window i w w' f b l a) st') (j : node) (x : window) :
    st'.entered j x = true ↔ (st.entered j x = true ∨ (j = i ∧ x = w')) := by
  conductor_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  conductor_field_simp
  constructor
  · rintro (⟨rfl, rfl⟩ | h)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl h
  · rintro (h | ⟨rfl, rfl⟩)
    · exact Or.inr h
    · exact Or.inl ⟨rfl, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **What the ACS proposal requires** (Algorithm 7, line 37
(`line:ready`)): the validator is correct, in the predecessor window, and
ready. -/
theorem acs_propose_guards {i : node} {w w' : window} {s : ℕ} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.acs_propose i w w' s a) st') :
    ¬ fm.byz i ∧ InWindow st i w ∧ win_ord.next w w' ∧ ReadyNext th st i w := by
  conductor_tr htr
  obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := htr
  exact ⟨h1, ⟨h2, fun x hx => Bool.eq_false_iff.mpr (h3 x hx)⟩, h4, h6⟩

/-- Initially every validator is in window 1 and no other. -/
theorem init_entered
    (hi : (Conductor.relationalTransitionSystem ℕ window time node acsstate).init th st)
    (j : node) (x : window) :
    st.entered j x = true ↔ x = win_ord.zero := by
  simp only [Conductor.relationalTransitionSystem, Conductor.Init, Conductor.initializer.ext.tr] at hi
  subst_vars
  conductor_field_simp

/-- **Only window entry enters a window**: a pair `entered` after a step was
entered before it, or the step is that validator's entry into that window. -/
theorem entered_step {l : CLabel window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st l st')
    (j : node) (x : window) (h : st'.entered j x = true) :
    st.entered j x = true ∨ ∃ w f b l' a, l = .enter_window j w x f b l' a := by
  cases l with
  | tick => rw [Conductor.tick.frame_entered htr] at h; exact Or.inl h
  | acs_propose => rw [Conductor.acs_propose.frame_entered htr] at h; exact Or.inl h
  | acs_step => rw [Conductor.acs_step.frame_entered htr] at h; exact Or.inl h
  | acs_decide => rw [Conductor.acs_decide.frame_entered htr] at h; exact Or.inl h
  | open_slot => rw [Conductor.open_slot.frame_entered htr] at h; exact Or.inl h
  | complete_slot => rw [Conductor.complete_slot.frame_entered htr] at h; exact Or.inl h
  | enter_window i w w' f b l' a =>
    rcases (enter_window_entered htr j x).1 h with h | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, f, b, l', a, rfl⟩

/-- **Only the validator's own ACS proposal records it**: a correct
validator's proposal to `ACS[x]` present after a step was present before it,
or the step is that validator's `acs_propose` to `ACS[x]`. The ACS's
internal steps and the other inputs leave a correct validator's proposals
alone (the contract's `proposed_step_frame`, `propose_frame`,
`abandon_proposed_frame`). -/
theorem proposed_step {l : CLabel window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st l st')
    {p : node} (hp : ¬ fm.byz p) (x : window) {s : ℕ}
    (h : A.proposed (st'.acs_state x) p s) :
    A.proposed (st.acs_state x) p s ∨ ∃ w s' a, l = .acs_propose p w x s' a := by
  cases l with
  | tick => rw [Conductor.tick.frame_acs_state htr] at h; exact Or.inl h
  | acs_decide => rw [Conductor.acs_decide.frame_acs_state htr] at h; exact Or.inl h
  | open_slot => rw [Conductor.open_slot.frame_acs_state htr] at h; exact Or.inl h
  | complete_slot => rw [Conductor.complete_slot.frame_acs_state htr] at h; exact Or.inl h
  | acs_step w a =>
    obtain ⟨hs, he⟩ := acs_step_acs htr
    rw [he x] at h
    by_cases hx : x = w
    · subst hx
      rw [if_pos rfl] at h
      exact Or.inl ((A.proposed_step_frame _ _ p s hs hp).1 h)
    · rw [if_neg hx] at h; exact Or.inl h
  | acs_propose i w w' s' a =>
    obtain ⟨hs, he⟩ := acs_propose_acs htr
    rw [he x] at h
    by_cases hx : x = w'
    · subst hx
      rw [if_pos rfl] at h
      by_cases hpi : p = i
      · subst hpi; exact Or.inr ⟨w, s', a, rfl⟩
      · exact Or.inl ((A.propose_frame _ i s' a p s hs hp (Or.inl hpi)).1 h)
    · rw [if_neg hx] at h; exact Or.inl h
  | enter_window i w w' f b l' a =>
    obtain ⟨hs, he⟩ := enter_window_acs htr
    rw [he x] at h
    by_cases hx : x = w'
    · subst hx
      rw [if_pos rfl] at h
      exact Or.inl ((A.abandon_proposed_frame _ i a p s hs hp).1 h)
    · rw [if_neg hx] at h; exact Or.inl h

/-- **Every step moves an ACS instance along its contract, or leaves it
alone** (`acsComponent`'s frame and step). -/
theorem acs_state_step {l : CLabel window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st l st')
    (x : window) :
    st'.acs_state x = st.acs_state x ∨ A.trans (st.acs_state x) (st'.acs_state x) := by
  by_cases hl : AcsLabel x l
  · obtain ⟨_, h⟩ := (acsComponent th x).step st l st' htr hl
    exact Or.inr h
  · exact Or.inl ((acsComponent th x).frame st l st' htr hl)

/-- The bounds of a window persist. -/
theorem winBounds_mono {l : CLabel window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st l st')
    {w : window} {f b l' : ℕ} (h : WinBounds (th := th) st w f b l') :
    WinBounds (th := th) st' w f b l' :=
  h.imp_right (Conductor.acs_decided.mono htr w f b l')

end Steps

/-! ## Reachable states -/

section Reachable

variable {window node acsstate time : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [Inhabited time] [win_ord : TotalOrderWithMinimum window] [time_ord : TotalOrder time]
  [fm : FaultModel node] [A : ACSSafety node ℕ acsstate fm.byz]
  {th : Conductor.Theory ℕ window time node acsstate}
  {st : CState window time node acsstate}

/-- **An entered window other than window 1 has an entered predecessor.**
Window entry requires the validator to be in the predecessor
(Algorithm 7, line 44 (`line:acs-decide`)), and entry is never undone. An
induction over reachability: the model's invariants record the predecessor
of a decided window only in `acs_decide`'s guard. -/
theorem entered_pred
    (hr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).reachable th st) :
    ∀ j x, st.entered j x = true → x = win_ord.zero ∨ ∃ w, win_ord.next w x ∧ st.entered j w = true := by
  induction hr with
  | init s _ hi => intro j x h; exact Or.inl ((init_entered hi j x).1 h)
  | step s s' _ hn ih =>
    intro j x h
    obtain ⟨l, htr⟩ := hn
    rcases entered_step htr j x h with h0 | ⟨w, f, b, l', a, rfl⟩
    · rcases ih j x h0 with h1 | ⟨w, hw, hwe⟩
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, Conductor.entered.mono htr j w hwe⟩
    · obtain ⟨-, hin, hnx, -⟩ := enter_window_guards htr
      exact Or.inr ⟨w, hnx, Conductor.entered.mono htr j w hin.1⟩

/-- **A window has one set of bounds**: window 1's are the configuration's
and it is never ACS-decided (`[decided_nonzero]`); a later window's
decision is unique (`[window_assignment_agreement]`). -/
theorem winBounds_unique
    (hr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).reachable th st)
    {w : window} {f b l f' b' l' : ℕ}
    (h₁ : WinBounds (th := th) st w f b l) (h₂ : WinBounds (th := th) st w f' b' l') :
    f = f' ∧ b = b' ∧ l = l' := by
  rcases h₁ with ⟨hw, rfl, rfl, rfl⟩ | h₁ <;> rcases h₂ with ⟨hw', rfl, rfl, rfl⟩ | h₂
  · exact ⟨rfl, rfl, rfl⟩
  · exact absurd hw (Conductor.reachable_decided_nonzero hr w f' b' l' h₂)
  · exact absurd hw' (Conductor.reachable_decided_nonzero hr w f b l h₁)
  · exact Conductor.reachable_window_assignment_agreement hr w f b l f' b' l' ⟨h₁, h₂⟩

end Reachable

/-! ## `(2W − p)`-Boundedness -/

section Count

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}

open scoped Cadence.Timed

omit [AddCommMonoid time] in
/-- **Where the opened slots above an uncompleted one lie** (Proposition 11
(`prop:open-count-window`), interval form). Let `s` be an opened,
uncompleted slot of correct `i`, in window `ws` with bounds `[fs, ls]`.
An opened slot `t > s` lies in `ws`, at most `ls`, or in an entered
successor of `ws`; and `s` is at or above `ws`'s readiness boundary as soon
as `i` has entered a successor (`[bounded_tail]`). -/
theorem opened_above
    {th : Conductor.Theory ℕ window time node acsstate} {st : CState window time node acsstate}
    (hr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).reachable th st)
    {i : node} (hi : ¬ fm.byz i) {s : ℕ} (hnc : ¬ st.completed i s = true)
    {ws : window} {fs bs ls : ℕ} (hent : st.entered i ws = true)
    (hbs : WinBounds (th := th) st ws fs bs ls) (hfs : fs ≤ s) (hsl : s ≤ ls)
    {t : ℕ} (ht : st.opened i t = true) (hst : s < t) :
    t ≤ ls ∨ ∃ wn fn bn ln, win_ord.next ws wn ∧ st.entered i wn = true ∧
      WinBounds (th := th) st wn fn bn ln ∧ fn ≤ t ∧ t ≤ ln := by
  obtain ⟨wt, hwt⟩ := Conductor.reachable_opened_backed hr i t ⟨hi, ht⟩
  have hentt := Conductor.reachable_opened_win_entered hr i t wt ⟨hi, hwt⟩
  obtain ⟨ft, bt, lt', hbt⟩ := Conductor.reachable_entered_has_bounds hr i wt ⟨hi, hentt⟩
  have hct := Conductor.reachable_opened_win_contained hr i t wt ft bt lt' ⟨hi, hwt, hbt⟩
  rcases win_trichotomy ws wt with hlt | rfl | hlt
  · -- `wt` above `ws`: it is `ws`'s successor, or `s` would be complete.
    rcases entered_pred hr i wt hentt with h0 | ⟨w0, hn0, he0⟩
    · subst h0
      exact (win_not_le_of_lt hlt (win_ord.zero_lt ws)).elim
    rcases win_trichotomy ws w0 with hlt0 | rfl | hlt0
    · obtain ⟨f0, b0, l0, hb0⟩ := Conductor.reachable_entered_has_bounds hr i w0 ⟨hi, he0⟩
      have hsep : ls < f0 :=
        Conductor.reachable_win_bounds_ordered hr ws w0 fs bs ls f0 b0 l0 ⟨hlt0, hbs, hb0⟩
      have hfb : f0 ≤ b0 := (Conductor.reachable_bounds_shape hr w0 f0 b0 l0 hb0).1
      exact (hnc (Conductor.reachable_bounded_tail hr i s wt w0 ws f0 b0 l0 fs bs ls
        ⟨hi, hentt, hn0, hb0, hent, hbs, hfs, hsl, show s < b0 by omega⟩)).elim
    · exact Or.inr ⟨wt, ft, bt, lt', hn0, hentt, hbt, hct⟩
    · exact (win_not_le_of_lt hlt (win_next_le_of_lt hn0 hlt0)).elim
  · exact Or.inl (Conductor.reachable_opened_win_contained hr i t ws fs bs ls ⟨hi, hwt, hbs⟩).2
  · have hsep : lt' < fs :=
      Conductor.reachable_win_bounds_ordered hr wt ws ft bt lt' fs bs ls ⟨hlt, hbt, hbs⟩
    have h1 : t ≤ lt' := hct.2
    have h2 : fs ≤ s := hfs
    have h3 : lt' < fs := hsep
    omega

/-- **`(2W − p)`-Boundedness** (Lemma 14 (`lem:boundedness`)), the target
`BoundednessClaim`: at every reachable state, an opened, uncompleted slot
of a correct validator has fewer than `2W − p` opened slots above it.
With windows of `W` slots and the readiness boundary at the `(p + 1)`-th
(`WindowShifts`): the opened slots above `s` lie in `s`'s window, at most
`W − 1 − p` of them once `i` has entered the next window, and in that next
window, at most `W` (`opened_above`). With `s` itself that is the paper's
`2W − p`; the contract's form counts the slots above `s`, so the bound is
met with nothing to spare. -/
theorem boundedness (sch : ConductorSchedule view time vfin)
    (th : Conductor.Theory ℕ window time node acsstate) :
    BoundednessClaim (A := A) sch th := by
  intro hshift st hr i s hi hop hnc ⟨g, hg, hgk⟩
  have hr' : (Conductor.relationalTransitionSystem ℕ window time node acsstate).reachable th st := hr
  have hnc' : ¬ st.completed i s = true := hnc
  obtain ⟨ws, hws⟩ := Conductor.reachable_opened_backed hr' i s ⟨hi, hop⟩
  have hent := Conductor.reachable_opened_win_entered hr' i s ws ⟨hi, hws⟩
  obtain ⟨fs, bs, ls, hbs⟩ := Conductor.reachable_entered_has_bounds hr' i ws ⟨hi, hent⟩
  obtain ⟨hfs, hsl⟩ := Conductor.reachable_opened_win_contained hr' i s ws fs bs ls ⟨hi, hws, hbs⟩
  obtain ⟨hb, hl⟩ := Conductor.reachable_win_bounds_shift hr' ws fs bs ls hbs
  have hbs' : bs = fs + sch.p := hb.trans (hshift.2 fs)
  have hls' : ls = fs + (sch.W - 1) := hl.trans (hshift.1 fs)
  have hpW := sch.p_lt_W
  have hgt : ∀ k, s < g k := fun k => lt_of_le_of_ne (hgk k).2.1 (hgk k).2.2
  have hcard : (Finset.univ.image g).card = sch.bound := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hfs' : fs ≤ s := hfs
  have hsl' : s ≤ ls := hsl
  by_cases hex : ∃ wn, win_ord.next ws wn ∧ st.entered i wn = true
  · obtain ⟨wn, hn, hen⟩ := hex
    obtain ⟨fn, bn, ln, hbn⟩ := Conductor.reachable_entered_has_bounds hr' i wn ⟨hi, hen⟩
    have hln : ln = fn + (sch.W - 1) :=
      (Conductor.reachable_win_bounds_shift hr' wn fn bn ln hbn).2.trans (hshift.1 fn)
    have hbsle : bs ≤ s := by
      by_contra hlt
      exact hnc' (Conductor.reachable_bounded_tail hr' i s wn ws ws fs bs ls fs bs ls
        ⟨hi, hen, hn, hbs, hent, hbs, hfs, hsl, show s < bs by omega⟩)
    have hsub : Finset.univ.image g ⊆ Finset.Ioc s ls ∪ Finset.Icc fn ln := by
      intro t ht
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ht
      rcases opened_above hr' hi hnc' hent hbs hfs hsl (hgk k).1 (hgt k) with h | ⟨wn', fn', bn', ln', hn', -, hb', h1, h2⟩
      · exact Finset.mem_union_left _ (Finset.mem_Ioc.2 ⟨hgt k, h⟩)
      · obtain rfl := win_next_unique hn hn'
        obtain ⟨rfl, -, rfl⟩ := winBounds_unique hr' hb' hbn
        exact Finset.mem_union_right _ (Finset.mem_Icc.2 ⟨h1, h2⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [hcard, Nat.card_Ioc, Nat.card_Icc] at this
    simp only [ConductorSchedule.bound] at this
    omega
  · have hsub : Finset.univ.image g ⊆ Finset.Ioc s ls := by
      intro t ht
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ht
      rcases opened_above hr' hi hnc' hent hbs hfs hsl (hgk k).1 (hgt k) with h | ⟨wn', -, -, -, hn', hen', -⟩
      · exact Finset.mem_Ioc.2 ⟨hgt k, h⟩
      · exact (hex ⟨wn', hn', hen'⟩).elim
    have := Finset.card_le_card hsub
    rw [hcard, Nat.card_Ioc] at this
    simp only [ConductorSchedule.bound] at this
    omega

end Count

end Conductor

/-! ## The pinned trust base -/

/--
info: 'Conductor.entered_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.entered_pred

/--
info: 'Conductor.boundedness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.boundedness
