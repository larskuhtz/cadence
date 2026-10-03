import Cadence.Conductor.Boundedness

/-! # Conductor.Induction — the window induction, and `d_tot`-Totality

[ConductorBounds.md](../../docs/ConductorBounds.md) §9, stage K4. This file
proves the Conductor's **window synchronization**, Proposition 13
(`prop:window-synchronization`), its three corollaries, and from it
**`d_tot`-Totality**, Lemma 15 (`lemma:conductor-totality`): the target
`TotalityClaim` of [Schedule.lean](Schedule.lean).

## What is proven, with its deadline

Definition 6 (`def:window-synchronized`) calls a window synchronized when
four kinds of event are each "if one correct validator does it at `t`,
every correct validator does it by `max(t, GST) + d_tot`". Each is a named
`Prop` here, at a tolerance `d`, read on a timed run of the Conductor:

| the paper | here | event |
|---|---|---|
| Def. 6 (1); Corollary 1 (`cor:entry-synchronization`) | `EntrySync`, `entry_sync` | entering window `ω` |
| Def. 6 (2); Lemma 15 (`lemma:conductor-totality`) | `OpenSync`, `open_sync` | opening slot `s` |
| Def. 6 (3); Corollary 3 (`cor:completion-totality`) | `CompSync`, `comp_sync` | completing slot `s` |
| Def. 6 (4); Corollary 2 (`cor:proposal-synchronization`) | `PropSync`, `prop_sync` | proposing to `ACS[ω]` |

all at `d = Δ`, which is `d_tot` at the schedule's `δ = 0`
(`ConductorSchedule.d_tot_paper`). Proposition 13 is `window_synchronized`:
every window is synchronized. `totality` is `TotalityClaim`.

## How the induction runs

The paper inducts over windows. Here the induction is over **slot
numbers** (`window_induction`), which orders the same dependencies without
asking the abstract window order to be well-founded: a window is named by
its first slot, and everything the entry into a window with first slot `k`
depends on concerns smaller slots.

* **Entry** (`entry_step`). A correct `p_i` enters `ω` at `t` only once its
  own `ACS[ω]` has decided and it is ready in the predecessor `ω₀`
  (Algorithm 7, line 44 (`line:acs-decide`)). Every correct `p_j` then has
  its own decision by `max(t, GST) + Δ` (the ACS's Δ-Totality, read on the
  window's part of the run), has entered `ω₀` by then (entry into `ω₀`),
  and has completed every slot `p_i` needed for readiness (completions of
  smaller slots). So `p_j`'s entry is due, and the entry row fires it, at
  `δ = 0` with no delay.
* **Proposals** (`prop_step`). The same argument for the ACS proposal of
  Algorithm 7, line 37 (`line:ready`), with the proposal row in place of
  the entry row. It is the ACS's first assumption, which its Δ-Totality
  above consumes; the second, no premature abandonment, is the model's
  invariant `[acs_abandoned_decided]` (Proposition 12
  (`prop:acs-no-premature-abandonment`)).
* **Openings** (`open_step`). A slot `s` opened by `p_i` at `t` lies in a
  window `p_i` entered by `t`; `p_j` enters it by `max(t, GST) + Δ` and,
  its timer being punctual, opens `s` by the later of that and `s`'s
  starting time, which is at most `t`.
* **Completions** are the caller's (R-tot): openings synchronized within
  `d_tot` give completions synchronized within `d_tot`.

Window 1 is entered by everyone at the start (`entry_zero`).

## What the proof consumes

The ACS only through its contract: `T_acs.Admissible` of the window's part
of the run (the premise `AcsAdmissible`), the Δ-Totality field read there
(`Cadence.acs_totality_in`), `integrity`, and the input-enabledness fields
`propose_enabled` and `abandon_enabled`. Chorus only through (R-tot), as
stated. The model through its invariants and the plain-Lean facts of
[Boundedness.lean](Boundedness.lean). The ACS's fault bound, its
termination and its median bracket are not used: entry reads a window's
interval only after a correct validator has entered it, by which time it
is recorded. -/

namespace Conductor

open Cadence
open Classical
open scoped Cadence.Timed

attribute [local instance] natSlotOrder

/-! ## Enabledness and effects of the two rows' actions -/

section Actions

variable {window node acsstate time : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [Inhabited time] [win_ord : TotalOrderWithMinimum window] [time_ord : TotalOrder time]
  [fm : FaultModel node] [A : ACSSafety node ℕ acsstate fm.byz]
  {th : Conductor.Theory ℕ window time node acsstate}
  {st st' : CState window time node acsstate}

/-- Turn an enabledness goal into the action's guards (as `mvba_enabled`
in [Mvba/Liveness.lean](../Mvba/Liveness.lean)). -/
local macro "conductor_enabled" : tactic =>
  `(tactic| simp only [Enabled, Conductor.relationalTransitionSystem, Conductor.Next,
      Conductor.NextAct, trSimp])

/-- **Window entry's guards are its enabledness.** -/
theorem enabled_enter_window {i : node} {w w' : window} {f b l : ℕ} {a : acsstate}
    (hi : ¬ fm.byz i) (hin : InWindow st i w) (hn : win_ord.next w w')
    (hd : st.acs_decided w' f b l = true) (hdec : A.has_decided (st.acs_state w') i)
    (hrd : ReadyNext th st i w) (hab : A.abandon (st.acs_state w') i a) :
    Enabled (Conductor.relationalTransitionSystem ℕ window time node acsstate) th st
      (.enter_window i w w' f b l a) := by
  conductor_enabled
  exact ⟨_, hi, hin.1, fun x hx h => Bool.false_ne_true ((hin.2 x hx).symm.trans h), hn, hd, hdec, hrd, hab, rfl⟩

/-- **The ACS proposal's guards are its enabledness**, with the `s*` rule of
Algorithm 7, lines 38–41 (`line:ready-time`–`line:sstar-update`) as three
hypotheses over the predecessor's last slot. -/
theorem enabled_acs_propose {i : node} {w w' : window} {s : ℕ} {a : acsstate}
    (hi : ¬ fm.byz i) (hin : InWindow st i w) (hn : win_ord.next w w')
    (hnp : ∀ s', ¬ A.proposed (st.acs_state w') i s') (hrd : ReadyNext th st i w)
    (hbeyond : ∀ w0 f0 b0 l0, win_ord.next w0 w' → WinBounds (th := th) st w0 f0 b0 l0 → l0 < s)
    (hnow : TotalOrder.le st.now (th.start_time s))
    (hfirst : ∀ s' w0 f0 b0 l0, win_ord.next w0 w' → WinBounds (th := th) st w0 f0 b0 l0 →
      l0 < s' → s' < s → ¬ TotalOrder.le st.now (th.start_time s'))
    (hp : A.propose (st.acs_state w') i s a) :
    Enabled (Conductor.relationalTransitionSystem ℕ window time node acsstate) th st
      (.acs_propose i w w' s a) := by
  conductor_enabled
  exact ⟨_, hi, hin.1, fun x hx h => Bool.false_ne_true ((hin.2 x hx).symm.trans h), hn, hnp, hrd, hbeyond, hnow,
    hfirst, hp, rfl⟩

/-- **The ACS proposal's effect**: the validator has proposed to `ACS[w']`. -/
theorem acs_propose_proposed {i : node} {w w' : window} {s : ℕ} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.acs_propose i w w' s a) st') :
    A.proposed (st'.acs_state w') i s := by
  obtain ⟨hp, he⟩ := acs_propose_acs htr
  rw [he w', if_pos rfl]
  exact A.propose_effect _ _ _ _ hp

/-- A correct validator's ACS records persist across a step: its proposals
and its decision (the contract's `*_mono` fields, along `acs_state_step`). -/
theorem proposed_persists {l : CLabel window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st l st')
    (x : window) {p : node} {s : ℕ} (h : A.proposed (st.acs_state x) p s) :
    A.proposed (st'.acs_state x) p s := by
  rcases acs_state_step htr x with he | he
  · rw [he]; exact h
  · exact A.proposed_mono _ _ p s he h

theorem has_decided_persists {l : CLabel window time node acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st l st')
    (x : window) {i : node} (h : A.has_decided (st.acs_state x) i) :
    A.has_decided (st'.acs_state x) i := by
  rcases acs_state_step htr x with he | he
  · rw [he]; exact h
  · exact A.has_decided_mono _ _ i he h

end Actions

/-! ## The four conditions of Definition 6 (`def:window-synchronized`) -/

section Conditions

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time]
  {th : Conductor.Theory ℕ window time node acsstate}

/-- `P` holds by `max(clk n, GST) + d`, the paper's deadline from index `n`. -/
def ByGst (r : TConductorRun th) (n : ℕ) (d : time) (P : CState window time node acsstate → Prop) :
    Prop :=
  ∃ m, r.clk m ≤ r.ref n + d ∧ P (r.at' m)

/-- **Entry into `ω` is synchronized within `d`** (Definition 6
(`def:window-synchronized`), the first condition): once a correct validator
has entered `ω`, every correct validator enters it by `max(t, GST) + d`. -/
def EntrySync (r : TConductorRun th) (d : time) (ω : window) : Prop :=
  ∀ n i, ¬ fm.byz i → (r.at' n).entered i ω = true →
    ∀ j, ¬ fm.byz j → ByGst r n d (fun st => st.entered j ω = true)

/-- **The openings of `s` are synchronized within `d`** (Definition 6, the
second condition). -/
def OpenSync (r : TConductorRun th) (d : time) (s : ℕ) : Prop :=
  ∀ n i, ¬ fm.byz i → (r.at' n).opened i s = true →
    ∀ j, ¬ fm.byz j → ByGst r n d (fun st => st.opened j s = true)

/-- **The completions of `s` are synchronized within `d`** (Definition 6,
the third condition). -/
def CompSync (r : TConductorRun th) (d : time) (s : ℕ) : Prop :=
  ∀ n i, ¬ fm.byz i → (r.at' n).completed i s = true →
    ∀ j, ¬ fm.byz j → ByGst r n d (fun st => st.completed j s = true)

/-- **The proposals to `ACS[ω]` are synchronized within `d`** (Definition 6,
the fourth condition; the ACS's first assumption, "Δ-synchronized
proposals", at `d = Δ`). -/
def PropSync (r : TConductorRun th) (d : time) (ω : window) : Prop :=
  ∀ n p s, ¬ fm.byz p → A.proposed ((r.at' n).acs_state ω) p s →
    ∀ q, ¬ fm.byz q → ByGst r n d (fun st => ∃ s', A.proposed (st.acs_state ω) q s')

/-- **Window `ω` is synchronized** (Definition 6 (`def:window-synchronized`)):
its entry, the openings and completions of its slots, and the proposals to
the next window's ACS. -/
def WindowSynchronized (r : TConductorRun th) (d : time) (ω : window) : Prop :=
  EntrySync r d ω ∧
    (∀ n f b l, WinBounds (th := th) (r.at' n) ω f b l → ∀ s, f ≤ s → s ≤ l →
      OpenSync r d s ∧ CompSync r d s) ∧
    ∀ ω', win_ord.next ω ω' → PropSync r d ω'

end Conditions

/-! ## Moving along the run -/

section Run

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time]
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th}

/-- The first step at which a property of the index becomes true. -/
theorem exists_first_step {P : ℕ → Prop} (h0 : ¬ P 0) {n : ℕ} (hn : P n) :
    ∃ e, e < n ∧ ¬ P e ∧ P (e + 1) := by
  obtain ⟨k, hk, hmin⟩ : ∃ k, P k ∧ ∀ j < k, ¬ P j :=
    ⟨Nat.find ⟨n, hn⟩, Nat.find_spec ⟨n, hn⟩, fun j hj => Nat.find_min ⟨n, hn⟩ hj⟩
  have hkn : k ≤ n := by
    by_contra h
    exact hmin n (by omega) hn
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h0 hk
  refine ⟨k - 1, by omega, hmin _ (by omega), ?_⟩
  rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]

/-- A monotone fact holding at an index with clock at most `X` holds at an
index past `N` with clock at most `X`, if `N`'s clock is at most `X`. -/
theorem within_from {P : CState window time node acsstate → Prop}
    (hmono : ∀ n, P (r.at' n) → P (r.at' (n + 1))) {X : time} {m N : ℕ}
    (hm : r.clk m ≤ X) (hP : P (r.at' m)) (hN : r.clk N ≤ X) :
    ∃ m', N ≤ m' ∧ r.clk m' ≤ X ∧ P (r.at' m') := by
  refine ⟨max m N, le_max_right _ _, ?_, r.toLRun.mono hmono hP _ (le_max_left _ _)⟩
  rcases le_total m N with h | h
  · rw [max_eq_right h]; exact hN
  · rw [max_eq_left h]; exact hm

theorem ref_mono {m n : ℕ} (h : m ≤ n) : r.ref m ≤ r.ref n :=
  max_le_max (r.clk_le_of_le h) le_rfl

theorem clk_le_ref_add [AddCommMonoid time] [IsOrderedAddMonoid time] {d : time} (hd : 0 ≤ d) (n : ℕ) : r.clk n ≤ r.ref n + d :=
  le_trans (r.clk_le_ref n) (le_add_of_nonneg_right hd)

theorem gst_le_ref_add [AddCommMonoid time] [IsOrderedAddMonoid time] {d : time} (hd : 0 ≤ d) (n : ℕ) : r.gst ≤ r.ref n + d :=
  le_trans (r.gst_le_ref n) (le_add_of_nonneg_right hd)

/-- A deadline from an earlier index is a deadline from a later one. -/
theorem ByGst.mono_idx [AddCommMonoid time] [IsOrderedAddMonoid time] {d : time} {P : CState window time node acsstate → Prop} {m n : ℕ}
    (h : ByGst r m d P) (hmn : m ≤ n) : ByGst r n d P := by
  obtain ⟨k, hk, hP⟩ := h
  exact ⟨k, le_trans hk (by gcongr; exact ref_mono hmn), hP⟩

theorem entered_persists (x : window) (j : node) :
    ∀ n, (r.at' n).entered j x = true → (r.at' (n + 1)).entered j x = true :=
  fun n => Conductor.entered.mono (r.steps n) j x

theorem completed_persists (j : node) (s : ℕ) :
    ∀ n, (r.at' n).completed j s = true → (r.at' (n + 1)).completed j s = true :=
  fun n => Conductor.completed.mono (r.steps n) j s

theorem opened_persists (j : node) (s : ℕ) :
    ∀ n, (r.at' n).opened j s = true → (r.at' (n + 1)).opened j s = true :=
  fun n => Conductor.opened.mono (r.steps n) j s

/-- Bounds known at one index are the bounds at every later index. -/
theorem winBounds_later {w : window} {f b l : ℕ} {m n : ℕ}
    (h : WinBounds (th := th) (r.at' m) w f b l) (hmn : m ≤ n) :
    WinBounds (th := th) (r.at' n) w f b l :=
  r.toLRun.mono (P := fun st => WinBounds (th := th) st w f b l)
    (fun k hk => winBounds_mono (r.steps k) hk) h n hmn

/-- Bounds known at two indices are the same bounds. -/
theorem winBounds_eq {w : window} {f b l f' b' l' : ℕ} {m m' : ℕ}
    (h : WinBounds (th := th) (r.at' m) w f b l) (h' : WinBounds (th := th) (r.at' m') w f' b' l') :
    f = f' ∧ b = b' ∧ l = l' :=
  winBounds_unique (r.reachable (max m m')) (winBounds_later h (le_max_left _ _))
    (winBounds_later h' (le_max_right _ _))

/-- **The step at which a correct validator entered a window other than
window 1** is its `enter_window` into it. -/
theorem first_entry {i : node} {ω : window} (hω : ω ≠ win_ord.zero) {n : ℕ}
    (hn : (r.at' n).entered i ω = true) :
    ∃ e, e < n ∧ ∃ w f b l a, r.lbl e = .enter_window i w ω f b l a := by
  have h0 : ¬ (r.at' 0).entered i ω = true := fun h => hω ((init_entered r.starts i ω).1 h)
  obtain ⟨e, hen, hne, he1⟩ := exists_first_step (P := fun k => (r.at' k).entered i ω = true) h0 hn
  refine ⟨e, hen, ?_⟩
  rcases entered_step (r.steps e) i ω he1 with h | h
  · exact (hne h).elim
  · exact h

/-- **The step at which a correct validator first proposed to `ACS[ω]`** is
its `acs_propose` to it. -/
theorem first_proposal {p : node} (hp : ¬ fm.byz p) {ω : window} {n : ℕ} {s : ℕ}
    (hn : A.proposed ((r.at' n).acs_state ω) p s) :
    ∃ e, e < n ∧ ∃ w s' a, r.lbl e = .acs_propose p w ω s' a := by
  have h0 : ¬ A.proposed ((r.at' 0).acs_state ω) p s := by
    rw [acs_state_init r.starts]
    exact A.init_proposed _ p s (r.holds.1 ω)
  obtain ⟨e, hen, hne, he1⟩ :=
    exists_first_step (P := fun k => A.proposed ((r.at' k).acs_state ω) p s) h0 hn
  refine ⟨e, hen, ?_⟩
  rcases proposed_step (r.steps e) hp ω he1 with h | h
  · exact (hne h).elim
  · exact h

/-- **A correct validator that has decided in `ACS[ω]` has proposed to it**
(the contract's `integrity`, at the instance's reachable state). -/
theorem proposed_of_has_decided {n : ℕ} {ω : window} {i : node} (hi : ¬ fm.byz i)
    (h : A.has_decided ((r.at' n).acs_state ω) i) :
    ∃ s, A.proposed ((r.at' n).acs_state ω) i s :=
  A.integrity _ (Conductor.reachable_acs_reachable (r.reachable n) ω) i hi h

/-- **A correct validator that has entered a window other than window 1 has
proposed to its ACS**: it entered on its own decision there. -/
theorem proposed_of_entered {n : ℕ} {ω : window} (hω : ω ≠ win_ord.zero) {j : node}
    (hj : ¬ fm.byz j) (h : (r.at' n).entered j ω = true) :
    ∃ s, A.proposed ((r.at' n).acs_state ω) j s := by
  obtain ⟨e, hen, w, f, b, l, a, hl⟩ := first_entry hω h
  have htr := r.steps e
  rw [hl] at htr
  obtain ⟨-, -, -, -, hdec, -⟩ := enter_window_guards htr
  obtain ⟨s, hs⟩ := proposed_of_has_decided hj hdec
  exact ⟨s, r.toLRun.mono (P := fun st => A.proposed (st.acs_state ω) j s)
    (fun k hk => proposed_persists (r.steps k) ω hk) hs n (by omega)⟩

end Run

/-! ## Readiness is transferred within `d`

The step both rows share: once a correct `p_i` is ready to leave `w`, every
correct `p_j` is in `w` and ready by `max(t, GST) + d` — or has left `w`
already. -/

section Readiness

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th} {d : time}

/-- **Ready by the deadline, as facts at one index.** If correct `p_i` is
in `w` and ready at `e`, entry into `w` is synchronized, and the completions
of every slot below `w`'s readiness boundary are, then every correct `p_j`
has, at one index past `e` with clock at most `max(clk e, GST) + d`, entered
`w` and completed every slot `p_i` had to complete. -/
theorem ready_by {e : ℕ} {i : node} (hi : ¬ fm.byz i) {w : window} {fw bw lw : ℕ}
    (hd : 0 ≤ d) (hin : InWindow (r.at' e) i w) (hrd : ReadyNext th (r.at' e) i w)
    (hbw : WinBounds (th := th) (r.at' e) w fw bw lw)
    (hent : EntrySync r d w) (hcomp : ∀ s, s < bw → CompSync r d s)
    {j : node} (hj : ¬ fm.byz j) :
    ∃ N, e ≤ N ∧ r.clk N ≤ r.ref e + d ∧ (r.at' N).entered j w = true ∧
      ∀ s, s < bw → Scheduled th (r.at' e) i s → (r.at' N).completed j s = true := by
  have hclk := clk_le_ref_add (r := r) hd e
  obtain ⟨m1, hm1, he1⟩ := hent e i hi hin.1 j hj
  -- Every slot `p_i` had to complete, `p_j` completes by the deadline.
  have hall : ∀ s ∈ List.range bw, ∃ m, e ≤ m ∧ r.clk m ≤ r.ref e + d ∧
      (Scheduled th (r.at' e) i s → (r.at' m).completed j s = true) := by
    intro s hs
    have hsb : s < bw := List.mem_range.1 hs
    by_cases hsc : Scheduled th (r.at' e) i s
    · obtain ⟨w0, f0, b0, l0, he0, hb0, hf0, hl0⟩ := hsc
      have hci : (r.at' e).completed i s = true :=
        hrd fw bw lw hbw s w0 f0 b0 l0 he0 hb0 hf0 hl0 hsb
      obtain ⟨m, hm, hc⟩ := hcomp s hsb e i hi hci j hj
      obtain ⟨m', hm', hc', hP⟩ :=
        within_from (P := fun st => st.completed j s = true) (completed_persists j s) hm hc hclk
      exact ⟨m', hm', hc', fun _ => hP⟩
    · exact ⟨e, le_rfl, hclk, fun h => (hsc h).elim⟩
  obtain ⟨N0, hN0, hcN0, hN0all⟩ :=
    r.withinFrom_forall (fun s st => Scheduled th (r.at' e) i s → st.completed j s = true)
      (fun s n h hs => completed_persists j s n (h hs)) e _ hclk (List.range bw) hall
  obtain ⟨N, hN, hcN, heN⟩ :=
    within_from (P := fun st => st.entered j w = true) (entered_persists w j) hm1 he1 hcN0
  refine ⟨N, le_trans hN0 hN, hcN, heN, fun s hs hsc => ?_⟩
  exact r.toLRun.mono (P := fun st => st.completed j s = true) (completed_persists j s)
    (hN0all s (List.mem_range.2 hs) hsc) N hN

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **The gate stays open while `p_j` has not moved on.** After the index of
`ready_by`, at every index at which `p_j` has not entered `w`'s successor
`ω`, `p_j` is in `w` and ready: the windows it has entered are at most `w`,
`p_i` had entered them all, and `p_j` completed every slot of theirs below
`w`'s boundary. -/
theorem gate_of_ready {e : ℕ} {i : node} (hi : ¬ fm.byz i) {w ω : window} {fw bw lw : ℕ}
    (hin : InWindow (r.at' e) i w) (hn : win_ord.next w ω)
    (hbw : WinBounds (th := th) (r.at' e) w fw bw lw)
    {j : node} (hj : ¬ fm.byz j) {N : ℕ} (hentN : (r.at' N).entered j w = true)
    (hcompN : ∀ s, s < bw → Scheduled th (r.at' e) i s → (r.at' N).completed j s = true)
    {n : ℕ} (hNn : N ≤ n) (hno : ¬ (r.at' n).entered j ω = true) :
    InWindow (r.at' n) j w ∧ ReadyNext th (r.at' n) j w := by
  have hentn : (r.at' n).entered j w = true :=
    r.toLRun.mono (P := fun st => st.entered j w = true) (entered_persists w j) hentN n hNn
  refine ⟨⟨hentn, fun w' hw' => ?_⟩, ?_⟩
  · rw [win_next_unique hw' hn]
    exact Bool.eq_false_iff.mpr hno
  · intro f b l hb s w0 f0 b0 l0 he0 hb0 hf0 hl0 hlt
    -- `w`'s boundary is the one known at `e`.
    obtain ⟨-, rfl, -⟩ := winBounds_eq hb hbw
    -- `p_i` had entered `w0` at `e`: `w0` is at most `w`.
    have hei : (r.at' e).entered i w0 = true := by
      rcases win_trichotomy w0 w with hlt0 | rfl | hlt0
      · exact Conductor.reachable_entered_prefix (r.reachable e) i w0 w ⟨hi, hin.1, hlt0⟩
      · exact hin.1
      · rcases win_trichotomy ω w0 with hlt1 | rfl | hlt1
        · exact (hno (Conductor.reachable_entered_prefix (r.reachable n) j ω w0
            ⟨hj, he0, hlt1⟩)).elim
        · exact (hno he0).elim
        · exact (win_not_le_of_lt hlt1 (win_next_le_of_lt hn hlt0)).elim
    obtain ⟨f0', b0', l0', hb0'⟩ := Conductor.reachable_entered_has_bounds (r.reachable e) i w0 ⟨hi, hei⟩
    obtain ⟨rfl, -, rfl⟩ := winBounds_eq hb0' hb0
    exact r.toLRun.mono (P := fun st => st.completed j s = true) (completed_persists j s)
      (hcompN s hlt ⟨w0, f0', b0', l0', hei, hb0', hf0, hl0⟩) n hNn

end Readiness

/-! ## The four steps -/

section Steps

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  {msg : Type} {sch : ConductorSchedule view time vfin}
  {TA : ACSTemporal node ℕ acsstate time msg fm.byz}
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th}

/-- What window `ω`'s predecessor contributes to the entry into `ω` and to
the proposals to `ACS[ω]`: its own entry, and the completions of the slots
below its readiness boundary, are synchronized. -/
def PredSync (r : TConductorRun th) (d : time) (ω : window) : Prop :=
  ∀ w, win_ord.next w ω → EntrySync r d w ∧
    ∀ k f b l, WinBounds (th := th) (r.at' k) w f b l → ∀ s, s < b → CompSync r d s

/-- **Window 1 is entered by everyone at the start** (Algorithm 7, line 30
(`line:enter_window_1`)), so its entry is synchronized at any tolerance. -/
theorem entry_zero {d : time} (hd : 0 ≤ d) :
    EntrySync r d win_ord.zero := by
  intro n i _ _ j _
  exact ⟨0, le_trans (r.clk_le_of_le (Nat.zero_le n)) (clk_le_ref_add hd n),
    Conductor.reachable_entered_zero (r.reachable 0) j⟩

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- Starting times are monotone in the slot number (`[start_time_strict]`). -/
theorem start_time_mono
    (hth : (Conductor.relationalTransitionSystem ℕ window time node acsstate).assumptions th)
    {s s' : ℕ} (h : s ≤ s') : th.start_time s ≤ th.start_time s' := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · exact (hth.2.2.2 s s' hlt).1

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **The first slot `s*` exists** (Algorithm 7, lines 38–41
(`line:ready-time`–`line:sstar-update`)): with unbounded starting times,
past any slot `l0` there is a least slot whose starting time has not
passed. -/
theorem sstar_exists
    (hth : (Conductor.relationalTransitionSystem ℕ window time node acsstate).assumptions th)
    (hunb : StartsUnbounded th) (now : time) (l0 : ℕ) :
    ∃ s, l0 < s ∧ now ≤ th.start_time s ∧ ∀ s', l0 < s' → s' < s → ¬ now ≤ th.start_time s' := by
  obtain ⟨s0, hs0⟩ := hunb now
  have hex : ∃ s, l0 < s ∧ now ≤ th.start_time s :=
    ⟨max s0 (l0 + 1), by omega, le_trans hs0 (start_time_mono hth (le_max_left _ _))⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun s' hl hs h => ?_⟩
  exact Nat.find_min hex hs ⟨hl, h⟩

/-- **The proposals to `ACS[ω]` are synchronized** (the step behind
Corollary 2 (`cor:proposal-synchronization`)). A correct `p_i` proposes at
`t` only when ready in `ω`'s predecessor `w` (Algorithm 7, line 37
(`line:ready`)); every correct `p_j` is then in `w` and ready by
`max(t, GST) + Δ` (`ready_by`), and its proposal row fires — `s*` exists by
`StartsUnbounded`, the ACS accepts the input (`propose_enabled`) — unless it
has proposed already. -/
theorem prop_step (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (hrows : TimedRows sch r) (hunb : StartsUnbounded th) {ω : window}
    (hpred : PredSync r sch.Δ ω) : PropSync r sch.Δ ω := by
  have hd : (0 : time) ≤ sch.Δ := le_of_lt sch.mvba.Δ_pos
  intro n p s hp hprop q hq
  obtain ⟨e, hen, w, s', a, hl⟩ := first_proposal hp hprop
  have htr := r.steps e
  rw [hl] at htr
  obtain ⟨-, hin, hnw, hrd⟩ := acs_propose_guards htr
  obtain ⟨hentw, hcompw⟩ := hpred w hnw
  obtain ⟨fw, bw, lw, hbw⟩ := Conductor.reachable_entered_has_bounds (r.reachable e) p w ⟨hp, hin.1⟩
  obtain ⟨N, heN, hcN, hentN, hcompN⟩ := ready_by hp hd hin hrd hbw hentw (hcompw e fw bw lw hbw) hq
  refine ByGst.mono_idx ?_ hen.le
  by_contra hno
  have hwin : ∀ k, r.clk k ≤ r.ref N + sch.δ → r.clk k ≤ r.ref e + sch.Δ := by
    intro k hk
    rw [show sch.δ = 0 from sch.δ_zero, add_zero] at hk
    exact le_trans hk (r.ref_le hcN (gst_le_ref_add hd e))
  obtain ⟨x, -, hlx, hcx⟩ := (hrows.propose q ω hq).diag le_rfl N (fun k hk hck => by
    have hck' := hwin k hck
    have hnp : ∀ s', ¬ A.proposed ((r.at' k).acs_state ω) q s' :=
      fun s' h => hno ⟨k, hck', s', h⟩
    have hne : ¬ (r.at' k).entered q ω = true := fun h => by
      obtain ⟨s', hs'⟩ := proposed_of_entered (win_next_ne_zero hnw) hq h
      exact hnp s' hs'
    obtain ⟨hin', hrd'⟩ := gate_of_ready hp hin hnw hbw hq hentN hcompN hk hne
    refine ⟨trivial, ⟨w, hnw, hin', hrd'⟩, ?_⟩
    have hbwk := winBounds_later hbw (le_trans heN hk)
    have hreach := Conductor.reachable_acs_reachable (r.reachable k) ω
    have hnab : ¬ A.abandoned ((r.at' k).acs_state ω) q := fun h => by
      obtain ⟨s', hs'⟩ := proposed_of_has_decided hq
        (Conductor.reachable_acs_abandoned_decided (r.reachable k) q ω ⟨hq, h⟩)
      exact hnp s' hs'
    obtain ⟨ss, hlss, hnow, hfirst⟩ := sstar_exists r.holds hunb (r.at' k).now lw
    obtain ⟨a', ha'⟩ := TA.propose_enabled _ q ss hreach hq hnab hnp
    refine ⟨.acs_propose q w ω ss a', ⟨w, ss, a', rfl⟩,
      enabled_acs_propose hq hin' hnw hnp hrd' ?_ hnow ?_ ha'⟩
    · intro w0 f0 b0 l0 hn0 hb0
      obtain rfl := win_pred_unique hn0 hnw
      obtain ⟨-, -, rfl⟩ := winBounds_unique (r.reachable k) hb0 hbwk
      exact hlss
    · intro s0 w0 f0 b0 l0 hn0 hb0 hl0 hs0
      obtain rfl := win_pred_unique hn0 hnw
      obtain ⟨-, -, rfl⟩ := winBounds_unique (r.reachable k) hb0 hbwk
      exact hfirst s0 hl0 hs0)
  obtain ⟨w0, s0, a0, hl0⟩ := hlx
  have htr0 := r.steps x
  rw [hl0] at htr0
  exact hno ⟨x + 1, hwin _ hcx, s0, acs_propose_proposed htr0⟩

/-- **Entry into `ω` is synchronized** (the step behind Corollary 1
(`cor:entry-synchronization`)). A correct `p_i` enters `ω` at `t` on its own
decision in `ACS[ω]`, ready in the predecessor `w` (Algorithm 7, line 44
(`line:acs-decide`)). Every correct `p_j` decides in `ACS[ω]` by
`max(t, GST) + Δ` — the ACS's Δ-Totality on the window's part of the run,
under synchronized proposals (`PropSync`) and no premature abandonment
(`[acs_abandoned_decided]`) — and is in `w` and ready by then
(`ready_by`); its entry row fires, the ACS accepting the `abandon` input
(`abandon_enabled`). -/
theorem entry_step (hsync : Sync sch TA r) (hΔ : TA.Δ = sch.Δ) {ω : window}
    (hω : ω ≠ win_ord.zero) (hpred : PredSync r sch.Δ ω) (hprop : PropSync r sch.Δ ω) :
    EntrySync r sch.Δ ω := by
  obtain ⟨hrows, -, -, hadm⟩ := hsync
  have hd : (0 : time) ≤ sch.Δ := le_of_lt sch.mvba.Δ_pos
  intro n i hi hent j hj
  obtain ⟨e, hen, w, f, b, l, a, hl⟩ := first_entry hω hent
  have htr := r.steps e
  rw [hl] at htr
  obtain ⟨-, hin, hnw, hdrec, hdec, hrd⟩ := enter_window_guards htr
  obtain ⟨hentw, hcompw⟩ := hpred w hnw
  obtain ⟨fw, bw, lw, hbw⟩ := Conductor.reachable_entered_has_bounds (r.reachable e) i w ⟨hi, hin.1⟩
  obtain ⟨N, heN, hcN, hentN, hcompN⟩ := ready_by hi hd hin hrd hbw hentw (hcompw e fw bw lw hbw) hj
  -- `p_j`'s own decision in `ACS[ω]`, by the ACS's Δ-Totality.
  obtain ⟨s0, hs0⟩ := proposed_of_has_decided hi hdec
  obtain ⟨pp, hpp⟩ := hadm ω ⟨e, i, s0, hi, hs0⟩
  have hsp : TA.SyncProposals (partRun pp) := by
    rw [TA.syncProposals_def]
    intro k q s hq hk q' hq'
    rw [partRun_at'] at hk
    refine partRun_byGst_at pp k _ _ ?_
    obtain ⟨m, hm, hP⟩ := hprop _ q s hq hk q' hq'
    exact ⟨m, by rw [hΔ]; exact hm, hP⟩
  have hnpa : TA.NoPrematureAbandon (partRun pp) := by
    rw [TA.noPrematureAbandon_def]
    intro k i' hi' hk
    rw [partRun_at'] at hk ⊢
    exact Conductor.reachable_acs_abandoned_decided (r.reachable _) i' ω ⟨hi', hk⟩
  obtain ⟨m2, hm2, hdj⟩ := acs_totality_in (TA := TA) pp hpp hsp hnpa e i hi hdec j hj
  rw [hΔ] at hm2
  obtain ⟨N', hNN', hcN', hdjN'⟩ :=
    within_from (P := fun st => A.has_decided (st.acs_state ω) j)
      (fun k hk => has_decided_persists (r.steps k) ω hk) hm2 hdj hcN
  -- `p_j`'s entry row.
  refine ByGst.mono_idx ?_ hen.le
  by_contra hno
  have hwin : ∀ k, r.clk k ≤ r.ref N' + sch.δ → r.clk k ≤ r.ref e + sch.Δ := by
    intro k hk
    rw [show sch.δ = 0 from sch.δ_zero, add_zero] at hk
    exact le_trans hk (r.ref_le hcN' (gst_le_ref_add hd e))
  obtain ⟨x, -, hlx, hcx⟩ := (hrows.enter j ω hj).diag le_rfl N' (fun k hk hck => by
    have hck' := hwin k hck
    have hne : ¬ (r.at' k).entered j ω = true := fun h => hno ⟨k, hck', h⟩
    obtain ⟨hin', hrd'⟩ := gate_of_ready hi hin hnw hbw hj hentN hcompN (le_trans hNN' hk) hne
    have hdjk : A.has_decided ((r.at' k).acs_state ω) j :=
      r.toLRun.mono (P := fun st => A.has_decided (st.acs_state ω) j)
        (fun m hm => has_decided_persists (r.steps m) ω hm) hdjN' k hk
    refine ⟨trivial, ⟨hdjk, w, hnw, hin', hrd'⟩, ?_⟩
    have hdreck : (r.at' k).acs_decided ω f b l = true :=
      r.toLRun.mono (P := fun st => st.acs_decided ω f b l = true)
        (fun m hm => Conductor.acs_decided.mono (r.steps m) ω f b l hm) hdrec k
        (le_trans heN (le_trans hNN' hk))
    obtain ⟨a', ha'⟩ :=
      TA.abandon_enabled _ j (Conductor.reachable_acs_reachable (r.reachable k) ω) hj
    exact ⟨.enter_window j w ω f b l a', ⟨w, f, b, l, a', rfl⟩,
      enabled_enter_window hj hin' hnw hdreck hdjk hrd' ha'⟩)
  obtain ⟨w0, f0, b0, l0, a0, hl0⟩ := hlx
  have htr0 := r.steps x
  rw [hl0] at htr0
  exact hno ⟨x + 1, hwin _ hcx, (enter_window_entered htr0 j ω).2 (Or.inr ⟨rfl, rfl⟩)⟩

/-- **The openings of `s` are synchronized** (the step behind Lemma 15
(`lemma:conductor-totality`)). A correct `p_i` opens `s` at `t` in a window
it has entered; every correct `p_j` enters that window by
`max(t, GST) + Δ`, and its punctual timer (`OpenPunctual`) opens `s` by the
later of that and `s`'s starting time, which is at most `t`
(`[opened_after_start]`, one clock). -/
theorem open_step (hsync : Sync sch TA r) {s : ℕ}
    (hentry : ∀ ω, (∃ n f b l, WinBounds (th := th) (r.at' n) ω f b l ∧ f ≤ s) →
      EntrySync r sch.Δ ω) :
    OpenSync r sch.Δ s := by
  obtain ⟨-, hpunct, hclock, -⟩ := hsync
  have hd : (0 : time) ≤ sch.Δ := le_of_lt sch.mvba.Δ_pos
  intro n i hi hop j hj
  obtain ⟨ω, hw⟩ := Conductor.reachable_opened_backed (r.reachable n) i s ⟨hi, hop⟩
  have hent := Conductor.reachable_opened_win_entered (r.reachable n) i s ω ⟨hi, hw⟩
  obtain ⟨f, b, l, hb⟩ := Conductor.reachable_entered_has_bounds (r.reachable n) i ω ⟨hi, hent⟩
  obtain ⟨hfs, hsl⟩ :=
    Conductor.reachable_opened_win_contained (r.reachable n) i s ω f b l ⟨hi, hw, hb⟩
  obtain ⟨m, hm, hej⟩ := hentry ω ⟨n, f, b, l, hb, hfs⟩ n i hi hent j hj
  obtain ⟨N, hN, hcN, hejN⟩ :=
    within_from (P := fun st => st.entered j ω = true) (entered_persists ω j) hm hej
      (clk_le_ref_add hd n)
  obtain ⟨m', -, hcm', hop'⟩ :=
    hpunct N j s hj ⟨ω, f, b, l, hejN, winBounds_later hb hN, hfs, hsl⟩
  have hstart : th.start_time s ≤ r.clk n := by
    rw [hclock n]
    exact Conductor.reachable_opened_after_start (r.reachable n) i s ⟨hi, hop⟩
  exact ⟨m', le_trans hcm' (max_le hcN (le_trans hstart (clk_le_ref_add hd n))), hop'⟩

end Steps

/-! ## The induction, and what it gives -/

section Induction

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  {msg : Type} {sch : ConductorSchedule view time vfin}
  {TA : ACSTemporal node ℕ acsstate time msg fm.byz}
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th}

omit [IsOrderedAddMonoid time] in
/-- The orchestrator contract's reading of synchronized openings, on
`contractRun`, is `OpenSync`. -/
theorem openSync_iff {d : time} {s : ℕ} :
    (orchestratorSafety th).OpeningsSyncWithin (contractRun r) s d ↔ OpenSync r d s := by
  simp only [OrchestratorSafety.OpeningsSyncWithin, TimedRun.byGstBound_iff]
  rfl

omit [IsOrderedAddMonoid time] in
/-- The contract's reading of synchronized completions is `CompSync`. -/
theorem compSync_iff {d : time} {s : ℕ} :
    (orchestratorSafety th).CompletionsSyncWithin (contractRun r) s d ↔ CompSync r d s := by
  simp only [OrchestratorSafety.CompletionsSyncWithin, TimedRun.byGstBound_iff]
  rfl

omit [IsOrderedAddMonoid time] in
/-- **(R-tot), read on the run**: synchronized openings of `s` give
synchronized completions. -/
theorem comp_of_open {d : time}
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) d) {s : ℕ}
    (h : OpenSync r d s) : CompSync r d s :=
  compSync_iff.1 (hcall s (openSync_iff.2 h))

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- A window's predecessor ends strictly before the window's first slot
(`[win_bounds_ordered]`, at an index where both are known). -/
theorem pred_last_lt {w ω : window} (hn : win_ord.next w ω) {n n0 : ℕ} {fw bw lw k b0 l0 : ℕ}
    (hbw : WinBounds (th := th) (r.at' n) w fw bw lw)
    (hb0 : WinBounds (th := th) (r.at' n0) ω k b0 l0) : fw ≤ bw ∧ bw ≤ lw ∧ lw < k := by
  have hbw' := winBounds_later hbw (le_max_left n n0)
  have hb0' := winBounds_later hb0 (le_max_right n n0)
  obtain ⟨h1, h2⟩ := Conductor.reachable_bounds_shape (r.reachable (max n n0)) w fw bw lw hbw'
  exact ⟨h1, h2, Conductor.reachable_win_bounds_ordered (r.reachable (max n n0)) w ω fw bw lw k b0 l0
    ⟨win_lt_of_next hn, hbw', hb0'⟩⟩

/-- **The window induction** (Proposition 13 (`prop:window-synchronization`)),
over first slots: for every `k`, entry into the window whose first slot is
`k` is synchronized, and so are the openings of slot `k`, within `Δ`.
Everything the entry into a window depends on — its predecessor's entry,
the completions below the predecessor's readiness boundary, the proposals to
its ACS — concerns smaller slots. -/
theorem window_induction (hsync : Sync sch TA r) (hunb : StartsUnbounded th)
    (hΔ : TA.Δ = sch.Δ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ) :
    ∀ k, (∀ ω, (∃ n b l, WinBounds (th := th) (r.at' n) ω k b l) → EntrySync r sch.Δ ω) ∧
      OpenSync r sch.Δ k := by
  have hd : (0 : time) ≤ sch.Δ := le_of_lt sch.mvba.Δ_pos
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  have hcomp_lt : ∀ s, s < k → CompSync r sch.Δ s := fun s hs => comp_of_open hcall (ih s hs).2
  have hent : ∀ ω, (∃ n b l, WinBounds (th := th) (r.at' n) ω k b l) → EntrySync r sch.Δ ω := by
    rintro ω ⟨n0, b0, l0, hb0⟩
    by_cases hz : ω = win_ord.zero
    · subst hz
      exact entry_zero hd
    · have hpred : PredSync r sch.Δ ω := by
        intro w hnw
        refine ⟨fun n i hi he j hj => ?_, fun n f b l hb s hs => ?_⟩
        · obtain ⟨fw, bw, lw, hbw⟩ :=
            Conductor.reachable_entered_has_bounds (r.reachable n) i w ⟨hi, he⟩
          obtain ⟨h1, h2, h3⟩ := pred_last_lt hnw hbw hb0
          exact (ih fw (by omega)).1 w ⟨n, bw, lw, hbw⟩ n i hi he j hj
        · obtain ⟨-, h2, h3⟩ := pred_last_lt hnw hb hb0
          exact hcomp_lt s (by omega)
      exact entry_step hsync hΔ hz hpred (prop_step TA hsync.1 hunb hpred)
  refine ⟨hent, open_step hsync fun ω ⟨n, f, b, l, hb, hf⟩ => ?_⟩
  rcases Nat.lt_or_eq_of_le hf with hlt | rfl
  · exact (ih f hlt).1 ω ⟨n, b, l, hb⟩
  · exact hent ω ⟨n, b, l, hb⟩

/-! ### The paper's items, each with its deadline `max(t, GST) + Δ`

All under the same premises: the timing model (`Sync`), unbounded starting
times, the ACS's `Δ` the system's, and (R-tot) at `Δ`, which is `d_tot` at
`δ = 0` (`ConductorSchedule.d_tot_paper`). -/

/-- **Lemma 15 (`lemma:conductor-totality`), openings**: if a correct
validator opens slot `s` at `t`, every correct validator opens `s` by
`max(t, GST) + Δ`. -/
theorem open_sync (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ) (s : ℕ) :
    OpenSync r sch.Δ s :=
  (window_induction hsync hunb hΔ hcall s).2

/-- **Corollary 3 (`cor:completion-totality`)**: if a correct validator
completes slot `s` at `t`, every correct validator completes `s` by
`max(t, GST) + Δ`. -/
theorem comp_sync (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ) (s : ℕ) :
    CompSync r sch.Δ s :=
  comp_of_open hcall (open_sync hsync hunb hΔ hcall s)

/-- **Corollary 1 (`cor:entry-synchronization`)**: if a correct validator
enters window `ω` at `t`, every correct validator enters `ω` by
`max(t, GST) + Δ`. -/
theorem entry_sync (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ) (ω : window) :
    EntrySync r sch.Δ ω := by
  intro n i hi he j hj
  obtain ⟨f, b, l, hb⟩ := Conductor.reachable_entered_has_bounds (r.reachable n) i ω ⟨hi, he⟩
  exact (window_induction hsync hunb hΔ hcall f).1 ω ⟨n, b, l, hb⟩ n i hi he j hj

/-- **Corollary 2 (`cor:proposal-synchronization`)**: if a correct validator
proposes to `ACS[ω]` at `t`, every correct validator proposes to it by
`max(t, GST) + Δ` — the ACS's first assumption, Δ-synchronized proposals. -/
theorem prop_sync (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ) (ω : window) :
    PropSync r sch.Δ ω :=
  prop_step TA hsync.1 hunb fun w _ =>
    ⟨entry_sync hsync hunb hΔ hcall w, fun _ _ _ _ _ s _ => comp_sync hsync hunb hΔ hcall s⟩

/-- **Proposition 13 (`prop:window-synchronization`)**: every window is
synchronized within `Δ` — its entry, the openings and completions of its
slots, and the proposals to the next window's ACS (Definition 6
(`def:window-synchronized`)). -/
theorem window_synchronized (hsync : Sync sch TA r) (hunb : StartsUnbounded th)
    (hΔ : TA.Δ = sch.Δ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ) (ω : window) :
    WindowSynchronized r sch.Δ ω :=
  ⟨entry_sync hsync hunb hΔ hcall ω,
    fun _ _ _ _ _ s _ _ => ⟨open_sync hsync hunb hΔ hcall s, comp_sync hsync hunb hΔ hcall s⟩,
    fun ω' _ => prop_sync hsync hunb hΔ hcall ω'⟩

/-- **`d_tot`-Totality** (Lemma 15 (`lemma:conductor-totality`)), the target
`TotalityClaim` of [Schedule.lean](Schedule.lean): over an ordered time,
under the timing model, with unbounded starting times and the ACS's `Δ` the
system's, if the caller's completions are total ((R-tot) at `d_tot`), then
for every slot, once a correct validator has opened it at clock `c`, every
correct validator opens it by `max(c, GST) + d_tot`. At `δ = 0`,
`d_tot = Δ` (`ConductorSchedule.d_tot_paper`), and this is `open_sync`. -/
theorem totality (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz)
    (th : Conductor.Theory ℕ window time node acsstate) :
    TotalityClaim sch TA th := by
  intro hunb hΔ r hsync hcall s
  rw [sch.d_tot_paper] at hcall ⊢
  exact openSync_iff.2 (open_sync hsync hunb hΔ hcall s)

end Induction

end Conductor

/-! ## The pinned trust base -/

/--
info: 'Conductor.window_synchronized' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.window_synchronized

/--
info: 'Conductor.entry_sync' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.entry_sync

/--
info: 'Conductor.prop_sync' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.prop_sync

/--
info: 'Conductor.comp_sync' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.comp_sync

/--
info: 'Conductor.open_sync' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.open_sync

/--
info: 'Conductor.totality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.totality
