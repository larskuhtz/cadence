import Cadence.Conductor.Induction

/-! # Conductor.Recovery — `(2Wτ)`-Recovery

[ConductorBounds.md](../../docs/ConductorBounds.md) §9, stage K5. This file
proves the Conductor's **recovery**, Lemma 16 (`lemma:conductor-recovery`):
the target `RecoveryClaim` of [Schedule.lean](Schedule.lean), at the
paper's `𝓡 = 2Wτ`, through the paper's chain, Propositions 14–19.

## What is proven, with its deadline

`T₁(ω)` is the starting time of window `ω`'s first slot and `T_p(ω)` that of
its `p`-th; `d_tot = Δ` at the schedule's `δ = 0`
(`ConductorSchedule.d_tot_paper`).

| the paper | here | deadline |
|---|---|---|
| Proposition 14 (`prop:conductor-open-to-complete`) | `open_to_complete` | `max(t, GST) + d_tot + ℓ_chorus` |
| Proposition 15 (`prop:enters-every-window`) | `enters_every_window` | eventually (`window_entered_by`: by some time) |
| Proposition 16 (`prop:window-open-time`) | `window_open_time` | `max(T₁(ω), GST) + d_tot + ℓ` |
| Proposition 17 (`prop:window-progression`) | `window_progression` | (1) the next window starts after `ω`'s last slot; (2) entered by `T₁(ω + 1)` |
| Proposition 18 (`prop:smooth-windows`) | `smooth_windows` | each slot opened by its starting time |
| Proposition 19 (`prop:first-post-gst-window-time`) | `first_post_gst_window_time` | `T₁(ω) ≤ GST + Wτ` |
| Lemma 16 (`lemma:conductor-recovery`) | `recovery` (`RecoveryClaim`) | `𝓡 = 2Wτ` |

`recovery_sharp` proves the same at `𝓡 = (W + p − 1)τ ≤ 2Wτ`, slack the
proof shows ([ConductorBounds.md](../../docs/ConductorBounds.md) §9, K5).

## How the chain runs

The engine is `succ_window`: once every correct validator has entered a
window `ω` by `X`, and the slots below `ω`'s readiness boundary start by
`T`, every correct validator has opened those slots by `max(X, T)`
(`OpenPunctual`), so the caller's termination (R-term) completes them
`ℓ_chorus` after `max(X, T, GST)`; every correct validator is then ready and
proposes to the next ACS (the proposal row, `δ = 0`); the ACS decides `ℓ`
later (its termination, under its two assumptions: Corollary 2
(`cor:proposal-synchronization`) and Proposition 12
(`prop:acs-no-premature-abandonment`)); every correct validator then enters
the next window, computing its interval from its own decision (the entry
row). The paper's propositions instantiate it:

* **Proposition 15**: from window 1, with no deadline to keep.
* **Proposition 16**: a correct proposal at or below `ω`'s first slot (the
  median's lower bracket) was made by `T₁(ω)` (the `s*` rule), so every
  correct validator is ready in the predecessor and has proposed by
  `max(T₁(ω), GST) + Δ` (Corollaries 1–3); the ACS decides `ℓ` later.
* **Proposition 17**: from `T_p(ω)`, everyone has proposed by
  `T_p(ω) + ℓ_chorus`, before `T₁(ω + 1)`, so every correct proposal is
  `ω`'s last slot plus one (the `s*` rule), and so is the median; entry
  follows `ℓ` later, by `T₁(ω + 1)` (assumption (1)).
* **Proposition 18**: Proposition 16 and assumption (4) put the entry into
  the smallest post-GST window by its `T_p`; Proposition 17, iterated
  (`progression_chain`), does the rest.
* **Proposition 19**: the median's upper bracket is a correct proposal made
  by `GST + (p − 1)τ + ℓ_chorus` (assumption (4), then `succ_window`), so
  its slot starts by `GST + Wτ` (assumption (2)).

## What the proof consumes

The timing model (`Sync`): both rows, the punctual openings, one clock, and
the ACS's admissibility once a correct validator has proposed. The ACS only
through its contract: ℓ-Termination (`Cadence.acs_termination_in`),
Validity (`validity_genuine`, for the median's brackets), and its
input-enabledness; Δ-Totality through Lemma 15 and its corollaries. The
median's brackets are the model's assumption `[acs_first_bracket]` on the
first slot each validator computes; the lower median meets it under the
fault bound (`Cadence.lowerMedian_first_assumptions`), which is where the
fault bound enters. The caller through (R-tot) and (R-term). The
configuration: τ-spaced and unbounded starting times, the window shifts, and
a successor for every window (F30). The parameter assumptions: (1) in
Proposition 17, (2) in Proposition 19, (4) in Propositions 18 and 19, and
(3) only for `0 < ℓ` — slack recorded in
[ConductorBounds.md](../../docs/ConductorBounds.md) §9, K5.

## Where the run may start after GST

The paper's time starts at `0 = T₁(1)` with `GST ≥ 0`. A run here starts at
slot 1's starting time and GST is arbitrary, so window 1 may be post-GST
with `T₁(1) > GST + Wτ`, where Proposition 19's `ω = 1` case does not
apply; `recovery` handles window 1 apart: it is entered at its starting
time, so all of its slots are opened by theirs. -/

namespace Conductor

open Cadence
open Classical
open scoped Cadence.Timed

attribute [local instance] natSlotOrder

/-! ## The recording of an interval, and the proposal's `s*` rule -/

section Actions

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

/-- Turn an enabledness goal into the action's guards. -/
local macro "conductor_enabled" : tactic =>
  `(tactic| simp only [Enabled, Conductor.relationalTransitionSystem, Conductor.Next,
      Conductor.NextAct, trSimp])

set_option maxHeartbeats 2000000 in
/-- **The `s*` rule at the ACS proposal** (Algorithm 7, lines 38–41
(`line:ready-time`–`line:sstar-update`)): the proposer had proposed nothing
to `ACS[w']`, the proposed slot is beyond its own interval of the current
window, its starting time has not passed, and every slot between them
has. -/
theorem acs_propose_sstar {i : node} {w w' : window} {s : ℕ} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.acs_propose i w w' s a) st') :
    win_ord.next w w' ∧ (∀ s', ¬ A.proposed (st.acs_state w') i s') ∧
      (∀ f0 b0 l0, Bounds st i w f0 b0 l0 → l0 < s) ∧
      TotalOrder.le st.now (th.start_time s) ∧
      (∀ s' f0 b0 l0, Bounds st i w f0 b0 l0 →
        l0 < s' → s' < s → ¬ TotalOrder.le st.now (th.start_time s')) := by
  conductor_tr htr
  obtain ⟨-, -, -, h4, h5, -, h7, h8, h9, -⟩ := htr
  exact ⟨h4, h5, h7, h8, h9⟩

set_option maxHeartbeats 2000000 in
/-- The ACS proposal leaves the clock alone. -/
theorem acs_propose_now {i : node} {w w' : window} {s : ℕ} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.acs_propose i w w' s a) st') :
    st'.now = st.now := by
  conductor_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  conductor_field_simp

/-- **The ACS proposal records exactly its own input**: a correct
validator's proposal present after the step was present before it, or it
is this one (the contract's `propose_frame`). -/
theorem acs_propose_new {i : node} {w w' : window} {s : ℕ} {a : acsstate}
    (htr : (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th st
      (.acs_propose i w w' s a) st') {q : node} (hq : ¬ fm.byz q) (x : window) {s' : ℕ}
    (h : A.proposed (st'.acs_state x) q s') :
    A.proposed (st.acs_state x) q s' ∨ (q = i ∧ x = w' ∧ s' = s) := by
  obtain ⟨hp, he⟩ := acs_propose_acs htr
  rw [he x] at h
  by_cases hx : x = w'
  · subst hx
    rw [if_pos rfl] at h
    by_cases hqs : q = i ∧ s' = s
    · exact Or.inr ⟨hqs.1, rfl, hqs.2⟩
    · refine Or.inl ((A.propose_frame _ i s a q s' hp hq ?_).1 h)
      by_cases hqi : q = i
      · exact Or.inr fun hs => hqs ⟨hqi, hs⟩
      · exact Or.inl hqi
  · rw [if_neg hx] at h
    exact Or.inl h

/-- Initially every validator holds window 1's interval and no other
(Algorithm 7, lines 31–34 (`line:startup-foreach`–`line:startup-last`)). -/
theorem init_bounds
    (hi : (Conductor.relationalTransitionSystem ℕ window time node acsstate).init th st)
    (j : node) (x : window) (f b l : ℕ) :
    Bounds st j x f b l ↔
      (x = win_ord.zero ∧ f = 0 ∧ b = th.genesis_boundary ∧ l = th.genesis_last) := by
  unfold Bounds
  simp only [Conductor.relationalTransitionSystem, Conductor.Init, Conductor.initializer.ext.tr] at hi
  subst_vars
  conductor_field_simp
  rw [and_assoc, and_assoc]; rfl

/-- Initially the clock reads the configured genesis time. -/
theorem init_now
    (hi : (Conductor.relationalTransitionSystem ℕ window time node acsstate).init th st) :
    st.now = th.genesis_time := by
  simp only [Conductor.relationalTransitionSystem, Conductor.Init, Conductor.initializer.ext.tr] at hi
  subst_vars
  conductor_field_simp

end Actions

/-! ## Moving along the run -/

section Run

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time]
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th}

/-- **A correct validator's proposal of `s` to `ACS[ω]` was made by its
own `acs_propose` of exactly `s`**, at a step before which it had proposed
nothing to `ACS[ω]`. -/
theorem proposal_step_exact {p : node} (hp : ¬ fm.byz p) {ω : window} {n s : ℕ}
    (hn : A.proposed ((r.at' n).acs_state ω) p s) :
    ∃ e, e < n ∧ (∃ w a, r.lbl e = .acs_propose p w ω s a) ∧
      ∀ s', ¬ A.proposed ((r.at' e).acs_state ω) p s' := by
  have h0 : ¬ A.proposed ((r.at' 0).acs_state ω) p s := by
    rw [acs_state_init r.starts]
    exact A.init_proposed _ p s (r.holds.1 ω)
  obtain ⟨e, hen, hne, he1⟩ :=
    exists_first_step (P := fun k => A.proposed ((r.at' k).acs_state ω) p s) h0 hn
  have htr := r.steps e
  rcases proposed_step htr hp ω he1 with h | ⟨w, s', a, hl⟩
  · exact (hne h).elim
  · rw [hl] at htr
    rcases acs_propose_new htr hp ω he1 with h | ⟨-, -, rfl⟩
    · exact (hne h).elim
    · exact ⟨e, hen, ⟨w, a, hl⟩, (acs_propose_sstar htr).2.1⟩

/-- **A correct validator proposes to `ACS[ω]` once**: if it has proposed
`s` at all and has proposed something by index `m`, its proposal of `s`
was the step of an index before `m`. -/
theorem proposal_before {p : node} (hp : ¬ fm.byz p) {ω : window} {n s : ℕ}
    (hn : A.proposed ((r.at' n).acs_state ω) p s) {m : ℕ}
    (hm : ∃ s', A.proposed ((r.at' m).acs_state ω) p s') :
    ∃ e, e < m ∧ ∃ w a, r.lbl e = .acs_propose p w ω s a := by
  obtain ⟨e, -, hl, hnone⟩ := proposal_step_exact hp hn
  refine ⟨e, ?_, hl⟩
  by_contra hme
  obtain ⟨s', hs'⟩ := hm
  exact hnone s' (r.toLRun.mono (P := fun st => A.proposed (st.acs_state ω) p s')
    (fun k hk => proposed_persists (r.steps k) ω hk) hs' e (by omega))

/-- **The run starts at slot 1's starting time**, the paper's time `0`
(`[genesis_window]`, one clock). -/
theorem clk_zero {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
    [AddCommMonoid time] {sch : ConductorSchedule view time vfin}
    (hstart : StartTimes sch th) (hclock : ClockAgrees r) : r.clk 0 = sch.start₀ := by
  rw [hclock 0, init_now r.starts, r.holds.2.2.1.2.2, hstart,
    show (TotalOrderWithMinimum.zero : ℕ) = 0 from rfl]
  simp [ConductorSchedule.startTime]

/-- A window's interval known at one index is the interval a correct
validator holds wherever it has entered the window. -/
theorem bounds_at_entry {ω : window} {j : node} (hj : ¬ fm.byz j) {N n0 : ℕ}
    (he : (r.at' N).entered j ω = true) {f b l : ℕ}
    (hb : WinBounds (r.at' n0) ω f b l) : Bounds (r.at' N) j ω f b l := by
  obtain ⟨f', b', l', hb'⟩ := Conductor.reachable_entered_has_bounds (r.reachable N) j ω ⟨hj, he⟩
  obtain ⟨rfl, rfl, rfl⟩ := winBounds_eq ⟨j, hj, hb'⟩ hb
  exact hb'

/-- A window's interval known at one index is its interval where a correct
validator has entered it. -/
theorem winBounds_at_entry {ω : window} {j : node} (hj : ¬ fm.byz j) {N n0 : ℕ}
    (he : (r.at' N).entered j ω = true) {f b l : ℕ}
    (hb : WinBounds (r.at' n0) ω f b l) : WinBounds (r.at' N) ω f b l :=
  ⟨j, hj, bounds_at_entry hj he hb⟩

/-- **A slot of an entered window is opened by the later of the entry and
its starting time** (`OpenPunctual`, Algorithm 7, line 27
(`line:conductor-wait-for-open`)). -/
theorem open_by (hpunct : OpenPunctual r) {ω : window} {j : node} (hj : ¬ fm.byz j) {N n0 : ℕ}
    (he : (r.at' N).entered j ω = true) {f b l : ℕ}
    (hb : WinBounds (r.at' n0) ω f b l) {s : ℕ} (hfs : f ≤ s) (hsl : s ≤ l) :
    ∃ n, N ≤ n ∧ r.clk n ≤ max (r.clk N) (th.start_time s) ∧ (r.at' n).opened j s = true :=
  hpunct N j s hj ⟨ω, f, b, l, he, bounds_at_entry hj he hb, hfs, hsl⟩

/-- The contract's "by time `t`", on `contractRun`, is the run's. -/
theorem contract_byTime_iff {t : time} {P : CState window time node acsstate → Prop} :
    (contractRun r).byTime t P ↔ ∃ n, r.clk n ≤ t ∧ P (r.at' n) :=
  Iff.rfl

end Run

/-! ## Completions below a window's readiness boundary

What every correct validator needs before it can leave window `ω`: the
slots of `ω` and of the windows below it that lie below `ω`'s readiness
boundary, completed. Once every correct validator has entered `ω`, every
correct validator has opened each such slot by the later of that time and
the slot's starting time, so the caller's termination (R-term) completes it
`ℓ_chorus` later. -/

section Completions

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  {msg : Type} {sch : ConductorSchedule view time vfin}
  {TA : ACSTemporal node ℕ acsstate time msg fm.byz}
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th}

variable (r) in
/-- Slot `s` lies in window `ω` or in a window below it. -/
def Lower (ω : window) (s : ℕ) : Prop :=
  ∃ w0 n0 f0 b0 l0, (w0 = ω ∨ win_ord.lt w0 ω) ∧ WinBounds (r.at' n0) w0 f0 b0 l0 ∧
    f0 ≤ s ∧ s ≤ l0

/-- **(R-term), read on the run**: if every correct validator opens `s` by
`t`, every correct validator completes it by `max(t, GST) + ℓ_chorus`. Its
condition, synchronized openings, is Lemma 15 (`lemma:conductor-totality`). -/
theorem complete_by (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    {s : ℕ} {t : time} (hopen : ∀ i, ¬ fm.byz i → ∃ n, r.clk n ≤ t ∧ (r.at' n).opened i s = true)
    {j : node} (hj : ¬ fm.byz j) :
    ∃ m, r.clk m ≤ max t r.gst + sch.ℓchorus ∧ (r.at' m).completed j s = true := by
  have h := hterm s (openSync_iff.2 (open_sync hsync hunb hΔ hcall s)) t
    (fun i hi => contract_byTime_iff.2 (hopen i hi)) j hj
  rw [TimedRun.byGstBound_iff] at h
  exact contract_byTime_iff.1 h

/-- **The completions below `ω`'s readiness boundary.** If every correct
validator has entered `ω` by `X`, and every slot below the boundary `b`
starts by `T`, then every correct `p_j` has, at one index with clock at most
`max(X, T, GST) + ℓ_chorus`, entered `ω` and completed every slot below `b`
of `ω` and the windows below it. -/
theorem completions_by (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    (hℓc : 0 ≤ sch.ℓchorus) {ω : window} {b : ℕ} {X T : time}
    (hT : ∀ s, s < b → th.start_time s ≤ T)
    (hall : ∀ j, ¬ fm.byz j → ∃ m, r.clk m ≤ X ∧ (r.at' m).entered j ω = true)
    {j : node} (hj : ¬ fm.byz j) :
    ∃ N, r.clk N ≤ max (max X T) r.gst + sch.ℓchorus ∧ (r.at' N).entered j ω = true ∧
      ∀ s, s < b → Lower r ω s → (r.at' N).completed j s = true := by
  obtain ⟨m0, hm0, he0⟩ := hall j hj
  have hY : max (max X T) r.gst ≤ max (max X T) r.gst + sch.ℓchorus := le_add_of_nonneg_right hℓc
  have hclk0 : r.clk m0 ≤ max (max X T) r.gst + sch.ℓchorus :=
    le_trans hm0 (le_trans (le_trans (le_max_left X T) (le_max_left _ _)) hY)
  have hall' : ∀ s ∈ List.range b, ∃ m, m0 ≤ m ∧ r.clk m ≤ max (max X T) r.gst + sch.ℓchorus ∧
      (Lower r ω s → (r.at' m).completed j s = true) := by
    intro s hs
    have hsb : s < b := List.mem_range.1 hs
    by_cases hL : Lower r ω s
    · obtain ⟨w0, n0, f0, b0, l0, hle, hb0, hf, hl⟩ := hL
      have hopen : ∀ i, ¬ fm.byz i → ∃ n, r.clk n ≤ max X T ∧ (r.at' n).opened i s = true := by
        intro i hi
        obtain ⟨mi, hmi, hei⟩ := hall i hi
        have hei0 : (r.at' mi).entered i w0 = true := by
          rcases hle with rfl | hlt
          · exact hei
          · exact Conductor.reachable_entered_prefix (r.reachable mi) i w0 ω ⟨hi, hei, hlt⟩
        obtain ⟨n, -, hn, ho⟩ := open_by hsync.2.1 hi hei0 hb0 hf hl
        exact ⟨n, le_trans hn (max_le_max hmi (hT s hsb)), ho⟩
      obtain ⟨m, hm, hc⟩ := complete_by hsync hunb hΔ hcall hterm hopen hj
      obtain ⟨m', hm', hc', hP⟩ :=
        within_from (P := fun st => st.completed j s = true) (completed_persists j s) hm hc hclk0
      exact ⟨m', hm', hc', fun _ => hP⟩
    · exact ⟨m0, le_rfl, hclk0, fun h => (hL h).elim⟩
  obtain ⟨N, hN, hcN, hNall⟩ :=
    r.withinFrom_forall (fun s st => Lower r ω s → st.completed j s = true)
      (fun s n h hs => completed_persists j s n (h hs)) m0 _ hclk0 (List.range b) hall'
  exact ⟨N, hcN, r.toLRun.mono (P := fun st => st.entered j ω = true) (entered_persists ω j) he0 N hN,
    fun s hs hL => hNall s (List.mem_range.2 hs) hL⟩

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **The gate stays open while `p_j` has not moved on.** Once `p_j` has
entered `ω` and completed every slot below `ω`'s boundary of `ω` and the
windows below it, it is in `ω` and ready at every later index at which it
has not entered `ω`'s successor. -/
theorem gate_of_completed {ω ω' : window} (hn : win_ord.next ω ω') {f b l n0 : ℕ}
    (hb : WinBounds (r.at' n0) ω f b l) {j : node} (hj : ¬ fm.byz j) {N : ℕ}
    (hentN : (r.at' N).entered j ω = true)
    (hcompN : ∀ s, s < b → Lower r ω s → (r.at' N).completed j s = true)
    {k : ℕ} (hNk : N ≤ k) (hno : ¬ (r.at' k).entered j ω' = true) :
    InWindow (r.at' k) j ω ∧ ReadyNext (r.at' k) j ω := by
  have hentk : (r.at' k).entered j ω = true :=
    r.toLRun.mono (P := fun st => st.entered j ω = true) (entered_persists ω j) hentN k hNk
  refine ⟨⟨hentk, fun w' hw' => ?_⟩, ?_⟩
  · rw [win_next_unique hw' hn]
    exact Bool.eq_false_iff.mpr hno
  · intro f' b' l' hb' s w0 f0 b0 l0 he0 hb0 hf0 hl0 hlt
    obtain ⟨-, rfl, -⟩ := winBounds_eq ⟨j, hj, hb'⟩ hb
    have hL : Lower r ω s := by
      refine ⟨w0, k, f0, b0, l0, ?_, ⟨j, hj, hb0⟩, hf0, hl0⟩
      rcases win_trichotomy w0 ω with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · exfalso
        rcases win_trichotomy ω' w0 with h1 | rfl | h1
        · exact hno (Conductor.reachable_entered_prefix (r.reachable k) j ω' w0 ⟨hj, he0, h1⟩)
        · exact hno he0
        · exact win_not_le_of_lt h1 (win_next_le_of_lt hn h)
    exact r.toLRun.mono (P := fun st => st.completed j s = true) (completed_persists j s)
      (hcompN s hlt hL) k hNk

end Completions

/-! ## The two rows, and the ACS's termination, by a deadline

Each of the Conductor's handlers fires as soon as its gate is open (`δ = 0`),
so a gate open from an index whose clock and GST are at most `Y` has fired
its row by `Y`. -/

section Rows

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  {msg : Type} {sch : ConductorSchedule view time vfin}
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th}

omit [IsOrderedAddMonoid time] in
/-- At `δ = 0`, the window of a row from index `N` ends at `max(clk N, GST)`. -/
theorem row_window {N : ℕ} {Y : time} (hcN : r.clk N ≤ Y) (hgY : r.gst ≤ Y) :
    ∀ k, r.clk k ≤ r.ref N + sch.δ → r.clk k ≤ Y := by
  intro k hk
  rw [show sch.δ = 0 from sch.δ_zero, add_zero] at hk
  exact le_trans hk (r.ref_le hcN hgY)

/-- **The proposal row, by a deadline** (Algorithm 7, line 37
(`line:ready`)): if from index `N` on `p_j` is in `ω` and ready whenever it
has not entered `ω`'s successor `ω'`, it proposes to `ACS[ω']` by
`max(clk N, GST)`. -/
theorem propose_by (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (hrows : TimedRows sch r)
    (hunb : StartsUnbounded th) {ω ω' : window} (hn : win_ord.next ω ω') {j : node}
    (hj : ¬ fm.byz j) {N : ℕ} {f b l : ℕ} (hb : WinBounds (r.at' N) ω f b l)
    {Y : time} (hcN : r.clk N ≤ Y) (hgY : r.gst ≤ Y)
    (hgate : ∀ k, N ≤ k → ¬ (r.at' k).entered j ω' = true →
      InWindow (r.at' k) j ω ∧ ReadyNext (r.at' k) j ω) :
    ∃ m, r.clk m ≤ Y ∧ ∃ s, A.proposed ((r.at' m).acs_state ω') j s := by
  by_contra hno
  have hwin := row_window (sch := sch) hcN hgY
  obtain ⟨x, -, hlx, hcx⟩ := (hrows.propose j ω' hj).diag le_rfl N (fun k hk hck => by
    have hck' := hwin k hck
    have hnp : ∀ s', ¬ A.proposed ((r.at' k).acs_state ω') j s' :=
      fun s' h => hno ⟨k, hck', s', h⟩
    have hne : ¬ (r.at' k).entered j ω' = true := fun h => by
      obtain ⟨s', hs'⟩ := proposed_of_entered (win_next_ne_zero hn) hj h
      exact hnp s' hs'
    obtain ⟨hin', hrd'⟩ := hgate k hk hne
    refine ⟨trivial, ⟨ω, hn, hin', hrd'⟩, ?_⟩
    have hbk := winBounds_later hb hk
    have hreach := Conductor.reachable_acs_reachable (r.reachable k) ω'
    have hnab : ¬ A.abandoned ((r.at' k).acs_state ω') j := fun h => by
      obtain ⟨s', hs'⟩ := proposed_of_has_decided hj
        (Conductor.reachable_acs_abandoned_decided (r.reachable k) j ω' ⟨hj, h⟩)
      exact hnp s' hs'
    obtain ⟨ss, hlss, hnow, hfirst⟩ := sstar_exists r.holds hunb (r.at' k).now l
    obtain ⟨a', ha'⟩ := TA.propose_enabled _ j ss hreach hj hnab hnp
    refine ⟨.acs_propose j ω ω' ss a', ⟨ω, ss, a', rfl⟩,
      enabled_acs_propose hj hin' hn hnp hrd' ?_ hnow ?_ ha'⟩
    · intro f0 b0 l0 hb0
      obtain ⟨-, -, rfl⟩ := winBounds_unique (r.reachable k) ⟨j, hj, hb0⟩ hbk
      exact hlss
    · intro s0 f0 b0 l0 hb0 hl0 hs0
      obtain ⟨-, -, rfl⟩ := winBounds_unique (r.reachable k) ⟨j, hj, hb0⟩ hbk
      exact hfirst s0 hl0 hs0)
  obtain ⟨w0, s0, a0, hl0⟩ := hlx
  have htr0 := r.steps x
  rw [hl0] at htr0
  exact hno ⟨x + 1, hwin _ hcx, s0, acs_propose_proposed htr0⟩

/-- **ACS ℓ-Termination, by a deadline** (Module 4 (`mod:acs`)): if every
correct validator has proposed to `ACS[ω']` by `Y ≥ GST`, every correct
validator decides in it by `Y + ℓ`. Its two assumptions are Corollary 2
(`cor:proposal-synchronization`) and Proposition 12
(`prop:acs-no-premature-abandonment`). -/
theorem decide_by {TA : ACSTemporal node ℕ acsstate time msg fm.byz} (hsync : Sync sch TA r)
    (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    {ω' : window} {Y : time} (hgY : r.gst ≤ Y)
    (hprop : ∀ j, ¬ fm.byz j → ∃ m, r.clk m ≤ Y ∧ ∃ s, A.proposed ((r.at' m).acs_state ω') j s)
    {j : node} (hj : ¬ fm.byz j) :
    ∃ m, r.clk m ≤ Y + sch.ℓ ∧ A.has_decided ((r.at' m).acs_state ω') j := by
  obtain ⟨m, -, s, hs⟩ := hprop j hj
  obtain ⟨pp, hpp⟩ := hsync.2.2.2 ω' ⟨m, j, s, hj, hs⟩
  have hps := prop_sync hsync hunb hΔ hcall ω'
  have h := acs_termination_in (TA := TA) (C := acsComponent th ω') pp hpp
    (fun n q s hq hk q' hq' => by
      obtain ⟨m, hm, hP⟩ := hps n q s hq hk q' hq'
      exact ⟨m, by rw [hΔ]; exact hm, hP⟩)
    (fun n i hi hk => Conductor.reachable_acs_abandoned_decided (r.reachable n) i ω' ⟨hi, hk⟩)
    Y hprop j hj
  rw [max_eq_left hgY, hℓ] at h
  exact h

/-- **The entry row, by a deadline** (Algorithm 7, line 44
(`line:acs-decide`)): if at index `N` `p_j` has decided in `ACS[ω']`, and
from `N` on `p_j` is in `ω` and ready whenever it has not entered `ω'`, it
enters `ω'`, computing the window's interval from its own decision, by
`max(clk N, GST)`. -/
theorem enter_by (TA : ACSTemporal node ℕ acsstate time msg fm.byz) (hrows : TimedRows sch r)
    {ω ω' : window} (hn : win_ord.next ω ω') {j : node} (hj : ¬ fm.byz j) {N : ℕ}
    {Z : time} (hcN : r.clk N ≤ Z) (hgZ : r.gst ≤ Z)
    (hdec : A.has_decided ((r.at' N).acs_state ω') j)
    (hgate : ∀ k, N ≤ k → ¬ (r.at' k).entered j ω' = true →
      InWindow (r.at' k) j ω ∧ ReadyNext (r.at' k) j ω) :
    ∃ m, r.clk m ≤ Z ∧ (r.at' m).entered j ω' = true := by
  by_contra hno
  have hwin := row_window (sch := sch) hcN hgZ
  obtain ⟨x, -, hlx, hcx⟩ := (hrows.enter j ω' hj).diag le_rfl N (fun k hk hck => by
    have hck' := hwin k hck
    have hne : ¬ (r.at' k).entered j ω' = true := fun h => hno ⟨k, hck', h⟩
    obtain ⟨hin', hrd'⟩ := hgate k hk hne
    have hdjk : A.has_decided ((r.at' k).acs_state ω') j :=
      r.toLRun.mono (P := fun st => A.has_decided (st.acs_state ω') j)
        (fun m hm => has_decided_persists (r.steps m) ω' hm) hdec k hk
    refine ⟨trivial, ⟨hdjk, ω, hn, hin', hrd'⟩, ?_⟩
    obtain ⟨a', ha'⟩ :=
      TA.abandon_enabled _ j (Conductor.reachable_acs_reachable (r.reachable k) ω') hj
    exact ⟨.enter_window j ω ω' _ a', ⟨ω, _, a', rfl⟩,
      enabled_enter_window hj hin' hn hdjk hrd' rfl
        (fun _ _ _ hb => entry_beyond (r.reachable k) hj hn hdjk hb) ha'⟩)
  obtain ⟨w0, f0, a0, hl0⟩ := hlx
  have htr0 := r.steps x
  rw [hl0] at htr0
  exact hno ⟨x + 1, hwin _ hcx, (enter_window_entered htr0 j ω').2 (Or.inr ⟨rfl, rfl⟩)⟩

end Rows

/-! ## The schedule's arithmetic -/

namespace ConductorSchedule

variable {view time : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]

/-- `ℓ_MVBA` is a sum of nonnegative delays. -/
theorem ℓmvba_nonneg (sch : ConductorSchedule view time vfin) : 0 ≤ sch.mvba.ℓ vfin := by
  have hΔ := sch.mvba.Δ_pos.le
  have hρ := sch.mvba.ρ_nonneg
  have hδ := sch.mvba.δ_nonneg
  have hs := sch.mvba.Δsync_nonneg
  have hτ : 0 ≤ sch.mvba.τmax := le_trans (sch.mvba.τ_nonneg vord.zero) (sch.mvba.τ_le_max _)
  simp only [Mvba.Schedule.ℓ, Mvba.Schedule.burn, Mvba.Lcert]
  repeat first
    | apply add_nonneg
    | apply nsmul_nonneg
    | exact le_trans hΔ (le_max_left _ _)
    | assumption

/-- `ℓ_chorus` is nonnegative. -/
theorem ℓchorus_nonneg (sch : ConductorSchedule view time vfin) : 0 ≤ sch.ℓchorus := by
  rw [sch.ℓchorus_paper]
  exact add_nonneg (nsmul_nonneg sch.mvba.Δ_pos.le _) sch.ℓmvba_nonneg

omit [IsOrderedAddMonoid time] in
/-- `d_tot` is nonnegative. -/
theorem d_tot_nonneg (sch : ConductorSchedule view time vfin) : 0 ≤ sch.d_tot := by
  rw [sch.d_tot_paper]
  exact sch.mvba.Δ_pos.le

omit [IsOrderedAddMonoid time] in
/-- The ACS's latency is positive: `Δ < ℓ` (assumption (3)) and `0 < Δ`. -/
theorem ℓ_pos (sch : ConductorSchedule view time vfin) : 0 < sch.ℓ :=
  lt_trans sch.mvba.Δ_pos sch.assm_three

omit [IsOrderedAddMonoid time] in
/-- A window has at least one slot: `p < W`. -/
theorem one_le_W (sch : ConductorSchedule view time vfin) : 1 ≤ sch.W := by
  have := sch.p_lt_W
  omega

end ConductorSchedule

/-! ## Starting times and window bounds at the schedule -/

section Arith

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  {sch : ConductorSchedule view time vfin}
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th}

omit [Inhabited window] [Inhabited node] [Inhabited acsstate] win_ord fm A [Inhabited time]
  [IsOrderedAddMonoid time] in
/-- `k` slots later is `k • τ` later. -/
theorem start_add (hstart : StartTimes sch th) (s k : ℕ) :
    th.start_time (s + k) = th.start_time s + k • sch.τ := by
  rw [hstart, hstart, ConductorSchedule.startTime, ConductorSchedule.startTime, add_nsmul, add_assoc]

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- Later slots start strictly later (`[start_time_strict]`). -/
theorem start_time_lt
    (hth : (Conductor.relationalTransitionSystem ℕ window time node acsstate).assumptions th)
    {s s' : ℕ} (h : s < s') : th.start_time s < th.start_time s' :=
  lt_of_le_of_ne (hth.2.2.2.1 s s' h).1 (hth.2.2.2.1 s s' h).2

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- Starting times order slots. -/
theorem le_of_start_le
    (hth : (Conductor.relationalTransitionSystem ℕ window time node acsstate).assumptions th)
    {s s' : ℕ} (h : th.start_time s ≤ th.start_time s') : s ≤ s' := by
  by_contra h'
  exact absurd h (not_le.2 (start_time_lt hth (by omega)))

omit [IsOrderedAddMonoid time] in
/-- **A window's bounds are its first slot's shifts**: the readiness
boundary is `f + p` and the last slot `f + (W − 1)` (`[win_bounds_shift]`). -/
theorem bounds_shift (hshift : WindowShifts sch th) {ω : window} {n f b l : ℕ}
    (hb : WinBounds (r.at' n) ω f b l) : b = f + sch.p ∧ l = f + (sch.W - 1) := by
  obtain ⟨hb', hl'⟩ := winBounds_shift (r.reachable n) hb
  exact ⟨hb'.trans (hshift.2 f), hl'.trans (hshift.1 f)⟩

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- Window 1 starts at slot 1 (`[bounds_genesis]`). -/
theorem zero_first {n f b l : ℕ} (hb : WinBounds (r.at' n) win_ord.zero f b l) : f = 0 := by
  obtain ⟨i, -, h⟩ := hb
  exact (Conductor.reachable_bounds_genesis (r.reachable n) i f b l h).1

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- Every correct validator holds window 1's interval from the start. -/
theorem genesis_winBounds {i : node} (hi : ¬ fm.byz i) :
    WinBounds (r.at' 0) win_ord.zero 0 th.genesis_boundary th.genesis_last := by
  obtain ⟨f, b, l, h⟩ := Conductor.reachable_entered_has_bounds (r.reachable 0) i win_ord.zero
    ⟨hi, Conductor.reachable_entered_zero (r.reachable 0) i⟩
  obtain ⟨rfl, rfl, rfl⟩ := Conductor.reachable_bounds_genesis (r.reachable 0) i f b l h
  exact ⟨i, hi, h⟩

end Arith

/-! ## The chain of windows -/

section Chain

variable {window : Type} [win_ord : TotalOrderWithMinimum window]

/-- `ω'` is the `k`-th successor of `ω` in the window order: the paper's
window `ω + k`. Window `ω ∈ ℕ≥1` of the paper is the `(ω − 1)`-th
successor of window 1. -/
inductive WinSucc (ω : window) : ℕ → window → Prop
  | refl : WinSucc ω 0 ω
  | next {k : ℕ} {ω₁ ω₂ : window} : WinSucc ω k ω₁ → win_ord.next ω₁ ω₂ → WinSucc ω (k + 1) ω₂

/-- With every window having a successor, every window has a `k`-th one. -/
theorem WinSucc.exists (hwin : WindowsUnbounded window) (ω : window) :
    ∀ k, ∃ ω', WinSucc ω k ω'
  | 0 => ⟨ω, .refl⟩
  | k + 1 => by
    obtain ⟨ω₁, h₁⟩ := WinSucc.exists hwin ω k
    obtain ⟨ω₂, h₂⟩ := hwin ω₁
    exact ⟨ω₂, .next h₁ h₂⟩

end Chain

/-! ## The successor window, timed

The engine of Propositions 15–19: once every correct validator has entered
`ω`, the slots below `ω`'s readiness boundary complete `ℓ_chorus` after
they are all open (R-term), every correct validator proposes to the next
ACS as soon as it is ready, the ACS decides `ℓ` later (its termination),
and every correct validator enters `ω`'s
successor at once (`δ = 0`). -/

section Engine

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  {msg : Type} {sch : ConductorSchedule view time vfin}
  {TA : ACSTemporal node ℕ acsstate time msg fm.byz}
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th}

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
theorem clk_max_le {a b : ℕ} {t : time} (ha : r.clk a ≤ t) (hb : r.clk b ≤ t) :
    r.clk (max a b) ≤ t := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **A window's interval is bracketed by two correct proposals** (the
median's range, Algorithm 7, line 48 (`line:median-compute`)): a window
other than window 1 has a correct validator's proposal at or below its first
slot and one at or above it. A correct validator holding the interval
computed it from its own decision (`[bounds_decided]`), and the first slot
it computes is bracketed by two correct pairs of its decided set
(`[acs_first_bracket]`), which are genuine proposals (`validity_genuine`). -/
theorem recorded_bracket {ω : window} (hω : ω ≠ win_ord.zero) {n f b l : ℕ}
    (hb : WinBounds (r.at' n) ω f b l) :
    ∃ r1 s1 r2 s2, ¬ fm.byz r1 ∧ ¬ fm.byz r2 ∧ s1 ≤ f ∧ f ≤ s2 ∧
      (∃ m, A.proposed ((r.at' m).acs_state ω) r1 s1) ∧
      (∃ m, A.proposed ((r.at' m).acs_state ω) r2 s2) := by
  obtain ⟨i, hi, hbi⟩ := hb
  obtain ⟨hdec, hf⟩ := Conductor.reachable_bounds_decided (r.reachable n) i ω f b l ⟨hi, hbi, hω⟩
  have hreach := Conductor.reachable_acs_reachable (r.reachable n) ω
  obtain ⟨⟨r1, s1, hr1, hd1, hs1⟩, ⟨r2, s2, hr2, hd2, hs2⟩⟩ :=
    r.holds.2.2.2.2.2 _ i ⟨hreach, hi, hdec⟩
  subst hf
  exact ⟨r1, s1, r2, s2, hr1, hr2, hs1, hs2,
    ⟨n, A.validity_genuine _ hreach i r1 s1 hi hr1 hd1⟩,
    ⟨n, A.validity_genuine _ hreach i r2 s2 hi hr2 hd2⟩⟩

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **The `s*` rule, read on the run**: a correct proposal to `ω'` from
`ω`, whose last slot is `l`, made at step `e` is of a slot beyond `l`
whose starting time has not passed at `e`, and every slot strictly between
them had started before `e` (Algorithm 7, lines 38–41
(`line:ready-time`–`line:sstar-update`)). -/
theorem sstar_slot (hclock : ClockAgrees r) {ω ω' : window} (hn : win_ord.next ω ω')
    {n0 f b l : ℕ} (hb : WinBounds (r.at' n0) ω f b l) {e : ℕ} {q : node} {w : window}
    {s : ℕ} {a : acsstate} (hl : r.lbl e = .acs_propose q w ω' s a) :
    l < s ∧ r.clk e ≤ th.start_time s ∧ ∀ s', l < s' → s' < s → th.start_time s' < r.clk e := by
  have htr := r.steps e
  rw [hl] at htr
  obtain ⟨hq, hin, hnw, -⟩ := acs_propose_guards htr
  obtain ⟨-, -, hbeyond, hnow, hfirst⟩ := acs_propose_sstar htr
  obtain rfl := win_pred_unique hnw hn
  have hbe := bounds_at_entry hq hin.1 hb
  refine ⟨hbeyond f b l hbe, by rw [hclock e]; exact hnow, fun s' hl' hs' => ?_⟩
  rw [hclock e]
  exact not_le.mp (hfirst s' f b l hbe hl' hs')

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- Every correct proposal to `ACS[ω']` is made at a step no later than the
deadline by which every correct validator has proposed to it: a correct
validator proposes once. -/
theorem proposal_step_by {ω' : window} {Y : time}
    (hprop : ∀ j, ¬ fm.byz j → ∃ m, r.clk m ≤ Y ∧ ∃ s, A.proposed ((r.at' m).acs_state ω') j s)
    {q : node} (hq : ¬ fm.byz q) {n s : ℕ} (hn : A.proposed ((r.at' n).acs_state ω') q s) :
    ∃ e, r.clk e ≤ Y ∧ ∃ w a, r.lbl e = .acs_propose q w ω' s a := by
  obtain ⟨m, hm, hm'⟩ := hprop q hq
  obtain ⟨e, hem, hl⟩ := proposal_before hq hn hm'
  exact ⟨e, le_trans (r.clk_le_of_le hem.le) hm, hl⟩


/-- **The successor window, timed.** If every correct validator has entered
`ω` by `X` and every slot below `ω`'s readiness boundary `b` starts by `T`,
then with `Y ≥ max(X, T, GST) + ℓ_chorus` every correct validator proposes
to `ACS[ω']` by `Y` and enters `ω`'s successor `ω'` by `Y + ℓ`. -/
theorem succ_window (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    {ω ω' : window} (hn : win_ord.next ω ω') {n0 f b l : ℕ}
    (hb : WinBounds (r.at' n0) ω f b l) {X T Y : time}
    (hT : ∀ s, s < b → th.start_time s ≤ T) (hY : max (max X T) r.gst + sch.ℓchorus ≤ Y)
    (hall : ∀ j, ¬ fm.byz j → ∃ m, r.clk m ≤ X ∧ (r.at' m).entered j ω = true) :
    (∀ j, ¬ fm.byz j → ∃ m, r.clk m ≤ Y ∧ ∃ s, A.proposed ((r.at' m).acs_state ω') j s) ∧
      ∀ j, ¬ fm.byz j → ∃ m, r.clk m ≤ Y + sch.ℓ ∧ (r.at' m).entered j ω' = true := by
  have hℓc := sch.ℓchorus_nonneg
  have hgY : r.gst ≤ Y := le_trans (le_trans (le_max_right _ _) (le_add_of_nonneg_right hℓc)) hY
  have hYℓ : Y ≤ Y + sch.ℓ := le_add_of_nonneg_right sch.ℓ_pos.le
  have hcomp : ∀ j, ¬ fm.byz j → ∃ N, r.clk N ≤ max (max X T) r.gst + sch.ℓchorus ∧
      (r.at' N).entered j ω = true ∧ ∀ s, s < b → Lower r ω s → (r.at' N).completed j s = true :=
    fun j hj => completions_by hsync hunb hΔ hcall hterm hℓc hT hall hj
  have hprop : ∀ j, ¬ fm.byz j → ∃ m, r.clk m ≤ Y ∧ ∃ s, A.proposed ((r.at' m).acs_state ω') j s := by
    intro j hj
    obtain ⟨N, hcN, he, hc⟩ := hcomp j hj
    exact propose_by TA hsync.1 hunb hn hj (winBounds_at_entry hj he hb) (le_trans hcN hY) hgY
      (fun k hk hno => gate_of_completed hn hb hj he hc hk hno)
  refine ⟨hprop, fun j hj => ?_⟩
  obtain ⟨N, hcN, he, hc⟩ := hcomp j hj
  obtain ⟨md, hmd, hdec⟩ := decide_by hsync hunb hΔ hℓ hcall hgY hprop hj
  have hc2 : r.clk (max N md) ≤ Y + sch.ℓ := clk_max_le (le_trans (le_trans hcN hY) hYℓ) hmd
  have hdec2 : A.has_decided ((r.at' (max N md)).acs_state ω') j :=
    r.toLRun.mono (P := fun st => A.has_decided (st.acs_state ω') j)
      (fun m hm => has_decided_persists (r.steps m) ω' hm) hdec _ (le_max_right _ _)
  exact enter_by TA hsync.1 hn hj hc2 (le_trans hgY hYℓ) hdec2
    (fun k hk hno => gate_of_completed hn hb hj he hc (le_trans (le_max_left N md) hk) hno)

end Engine

/-! ## The paper's items -/

section Items

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}
  {msg : Type} {sch : ConductorSchedule view time vfin}
  {TA : ACSTemporal node ℕ acsstate time msg fm.byz}
  {th : Conductor.Theory ℕ window time node acsstate} {r : TConductorRun th}

/-- **Proposition 14 (`prop:conductor-open-to-complete`)**: if a correct
validator opens slot `s` at `t`, every correct validator completes `s` by
`max(t, GST) + d_tot + ℓ_chorus` (`d_tot = Δ` at `δ = 0`). The openings are
synchronized within `Δ` (Lemma 15 (`lemma:conductor-totality`)), and the
caller's termination completes the slot `ℓ_chorus` after the last of them. -/
theorem open_to_complete (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    {n : ℕ} {i : node} (hi : ¬ fm.byz i) {s : ℕ} (hop : (r.at' n).opened i s = true)
    {j : node} (hj : ¬ fm.byz j) :
    ∃ m, r.clk m ≤ max (r.clk n) r.gst + sch.Δ + sch.ℓchorus ∧ (r.at' m).completed j s = true := by
  have hd : (0 : time) ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hos := open_sync hsync hunb hΔ hcall s
  obtain ⟨m, hm, hc⟩ := complete_by hsync hunb hΔ hcall hterm (t := r.ref n + sch.Δ)
    (fun i' hi' => hos n i hi hop i' hi') hj
  rw [max_eq_left (gst_le_ref_add hd n)] at hm
  exact ⟨m, hm, hc⟩


/-- **Every window of the chain is entered by some time** (Proposition 15
(`prop:enters-every-window`), with its deadline): window 1 at the start, and
each successor by `succ_window`. -/
theorem window_entered_by (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    {k : ℕ} {ω : window} (h : WinSucc win_ord.zero k ω) :
    ∃ X, ∀ j, ¬ fm.byz j → ∃ m, r.clk m ≤ X ∧ (r.at' m).entered j ω = true := by
  induction h with
  | refl => exact ⟨r.clk 0, fun j _ => ⟨0, le_rfl, Conductor.reachable_entered_zero (r.reachable 0) j⟩⟩
  | next _ hn ih =>
    obtain ⟨X, hX⟩ := ih
    by_cases hex : ∃ i, ¬ fm.byz i
    · obtain ⟨i, hi⟩ := hex
      obtain ⟨m, -, he⟩ := hX i hi
      obtain ⟨f, b, l, hb⟩ := Conductor.reachable_entered_has_bounds (r.reachable m) i _ ⟨hi, he⟩
      exact ⟨_, (succ_window hsync hunb hΔ hℓ hcall hterm hn ⟨i, hi, hb⟩ (T := th.start_time b)
        (fun s hs => start_time_mono r.holds hs.le) le_rfl hX).2⟩
    · exact ⟨r.clk 0, fun j hj => (hex ⟨j, hj⟩).elim⟩

/-- **Proposition 15 (`prop:enters-every-window`)**: every correct validator
eventually enters every window — window 1 and each of its successors. -/
theorem enters_every_window (hsync : Sync sch TA r) (hunb : StartsUnbounded th)
    (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    {k : ℕ} {ω : window} (h : WinSucc win_ord.zero k ω) {j : node} (hj : ¬ fm.byz j) :
    ∃ m, (r.at' m).entered j ω = true := by
  obtain ⟨X, hX⟩ := window_entered_by hsync hunb hΔ hℓ hcall hterm h
  obtain ⟨m, -, he⟩ := hX j hj
  exact ⟨m, he⟩

/-- The `k`-th window's interval is held by a correct validator, and starts at slot `k + 1` or
later (`[win_bounds_ordered]`). -/
theorem chain_bounds (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    {i₀ : node} (hi₀ : ¬ fm.byz i₀) {k : ℕ} {ω : window} (h : WinSucc win_ord.zero k ω) :
    ∃ n f b l, WinBounds (r.at' n) ω f b l ∧ k ≤ f := by
  induction h with
  | refl => exact ⟨0, 0, th.genesis_boundary, th.genesis_last, genesis_winBounds hi₀, le_rfl⟩
  | @next k ω₁ ω₂ h₁ hn ih =>
    obtain ⟨n₁, f₁, b₁, l₁, hb₁, hk⟩ := ih
    obtain ⟨m, he⟩ := enters_every_window hsync hunb hΔ hℓ hcall hterm (.next h₁ hn) hi₀
    obtain ⟨f₂, b₂, l₂, hb₂⟩ := Conductor.reachable_entered_has_bounds (r.reachable m) i₀ ω₂ ⟨hi₀, he⟩
    obtain ⟨h1, h2, h3⟩ := pred_last_lt hn hb₁ ⟨i₀, hi₀, hb₂⟩
    exact ⟨m, f₂, b₂, l₂, ⟨i₀, hi₀, hb₂⟩, by omega⟩

/-- **The smallest post-GST window exists**: some window of the chain
starts at or after GST, and the least one is window 1 or follows a window
that starts before GST. -/
theorem exists_post_gst (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    (hwin : WindowsUnbounded window) {i₀ : node} (hi₀ : ¬ fm.byz i₀) :
    ∃ k ω n f b l, WinSucc win_ord.zero k ω ∧ WinBounds (r.at' n) ω f b l ∧
      r.gst ≤ th.start_time f ∧
      (k = 0 ∨ ∃ ω₁ n₁ f₁ b₁ l₁, win_ord.next ω₁ ω ∧
        WinBounds (r.at' n₁) ω₁ f₁ b₁ l₁ ∧ th.start_time f₁ < r.gst) := by
  have hex : ∃ k, ∃ ω n f b l, WinSucc win_ord.zero k ω ∧ WinBounds (r.at' n) ω f b l ∧
      r.gst ≤ th.start_time f := by
    obtain ⟨s0, hs0⟩ := hunb r.gst
    obtain ⟨ω, hω⟩ := WinSucc.exists hwin win_ord.zero s0
    obtain ⟨n, f, b, l, hb, hk⟩ := chain_bounds hsync hunb hΔ hℓ hcall hterm hi₀ hω
    exact ⟨s0, ω, n, f, b, l, hω, hb, le_trans hs0 (start_time_mono r.holds hk)⟩
  obtain ⟨ω, n, f, b, l, hω, hb, hg⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, ω, n, f, b, l, hω, hb, hg, ?_⟩
  generalize hk : Nat.find hex = k at hω
  cases hω with
  | refl => exact Or.inl rfl
  | @next k' ω₁ _ h₁ hn =>
    refine Or.inr ?_
    obtain ⟨n₁, f₁, b₁, l₁, hb₁, -⟩ := chain_bounds hsync hunb hΔ hℓ hcall hterm hi₀ h₁
    refine ⟨ω₁, n₁, f₁, b₁, l₁, hn, hb₁, not_le.mp fun h => ?_⟩
    exact Nat.find_min hex (show k' < Nat.find hex by omega) ⟨ω₁, n₁, f₁, b₁, l₁, h₁, hb₁, h⟩

/-- **Proposition 16 (`prop:window-open-time`)**: every correct validator
enters window `ω` by `max(T₁(ω), GST) + d_tot + ℓ`, where `T₁(ω)` is the
starting time of `ω`'s first slot (`d_tot = Δ` at `δ = 0`). A correct
validator's proposal at or below the first slot (the median's lower
bracket) was made by `T₁(ω)`, from the predecessor, ready; every correct
validator is then ready and has proposed by `max(T₁(ω), GST) + Δ`
(Corollaries 1–3), decides `ℓ` later (the ACS's termination), and enters. -/
theorem window_open_time (hsync : Sync sch TA r) (hunb : StartsUnbounded th) (hΔ : TA.Δ = sch.Δ)
    (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hstart : StartTimes sch th) {ω : window} {n0 f b l : ℕ}
    (hb : WinBounds (r.at' n0) ω f b l) {j : node} (hj : ¬ fm.byz j) :
    ∃ m, r.clk m ≤ max (th.start_time f) r.gst + sch.Δ + sch.ℓ ∧ (r.at' m).entered j ω = true := by
  have hd : (0 : time) ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hℓ0 : (0 : time) ≤ sch.ℓ := sch.ℓ_pos.le
  by_cases hz : ω = win_ord.zero
  · subst hz
    obtain rfl := zero_first hb
    refine ⟨0, ?_, Conductor.reachable_entered_zero (r.reachable 0) j⟩
    have h0 : r.clk 0 = th.start_time 0 := by
      rw [clk_zero hstart hsync.2.2.1, hstart]
      simp [ConductorSchedule.startTime]
    rw [h0, add_assoc]
    exact le_trans (le_max_left _ _) (le_add_of_nonneg_right (add_nonneg hd hℓ0))
  -- The median's lower bracket: a correct proposal at or below the first slot.
  obtain ⟨r1, s1, -, -, hr1, -, hs1, -, ⟨m1, hm1⟩, -⟩ := recorded_bracket hz hb
  obtain ⟨e, -, ⟨w, a, hl⟩, -⟩ := proposal_step_exact hr1 hm1
  have htr := r.steps e
  rw [hl] at htr
  obtain ⟨-, hin, hnw, hrd⟩ := acs_propose_guards htr
  obtain ⟨-, -, -, hnow, -⟩ := acs_propose_sstar htr
  have hclk : r.clk e ≤ th.start_time f := by
    rw [hsync.2.2.1 e]
    exact le_trans hnow (start_time_mono r.holds hs1)
  have hclk1 : r.clk (e + 1) ≤ th.start_time f := by
    rw [hsync.2.2.1 (e + 1), acs_propose_now htr, ← hsync.2.2.1 e]
    exact hclk
  -- Every correct validator proposes by `max(T₁, GST) + Δ` (Corollary 2).
  have hgY : r.gst ≤ max (th.start_time f) r.gst + sch.Δ :=
    le_trans (le_max_right _ _) (le_add_of_nonneg_right hd)
  have hps := prop_sync hsync hunb hΔ hcall ω
  have hprop : ∀ q, ¬ fm.byz q → ∃ m, r.clk m ≤ max (th.start_time f) r.gst + sch.Δ ∧
      ∃ s, A.proposed ((r.at' m).acs_state ω) q s := fun q hq => by
    obtain ⟨m, hm, hP⟩ := hps (e + 1) r1 s1 hr1 (acs_propose_proposed htr) q hq
    exact ⟨m, le_trans hm (add_le_add_left (max_le_max hclk1 le_rfl) _), hP⟩
  -- ... decides `ℓ` later (the ACS's termination) ...
  obtain ⟨md, hmd, hdec⟩ := decide_by hsync hunb hΔ hℓ hcall hgY hprop hj
  -- ... is ready in the predecessor by `max(T₁, GST) + Δ` (Corollaries 1 and 3) ...
  obtain ⟨fw, bw, lw, hbw⟩ := Conductor.reachable_entered_has_bounds (r.reachable e) r1 w ⟨hr1, hin.1⟩
  obtain ⟨N, heN, hcN, hentN, hcompN⟩ := ready_by hr1 hd hin hrd hbw
    (entry_sync hsync hunb hΔ hcall w) (fun s _ => comp_sync hsync hunb hΔ hcall s) hj
  have hYℓ : max (th.start_time f) r.gst + sch.Δ ≤ max (th.start_time f) r.gst + sch.Δ + sch.ℓ :=
    le_add_of_nonneg_right hℓ0
  have hcN' : r.clk N ≤ max (th.start_time f) r.gst + sch.Δ :=
    le_trans hcN (add_le_add_left (max_le_max hclk le_rfl) _)
  have hc2 : r.clk (max N md) ≤ max (th.start_time f) r.gst + sch.Δ + sch.ℓ :=
    clk_max_le (le_trans hcN' hYℓ) hmd
  have hdec2 : A.has_decided ((r.at' (max N md)).acs_state ω) j :=
    r.toLRun.mono (P := fun st => A.has_decided (st.acs_state ω) j)
      (fun m hm => has_decided_persists (r.steps m) ω hm) hdec _ (le_max_right _ _)
  -- ... and it enters, computing the interval from its own decision.
  exact enter_by TA hsync.1 hnw hj hc2 (le_trans hgY hYℓ) hdec2
    (fun k hk hno => gate_of_ready hr1 hin hnw hbw hj hentN hcompN (le_trans (le_max_left N md) hk) hno)

/-- **Proposition 17 (`prop:window-progression`)**: if every correct
validator enters a post-GST window `ω` by `T_p(ω)`, the starting time of
its `p`-th slot, then (1) the next window's interval starts right after
`ω`'s last slot, and (2) every correct validator enters it by its starting
time `T₁(ω + 1)`. Every correct validator completes the slots below `ω`'s
boundary by `T_p(ω) + ℓ_chorus` and proposes then, before the next window's
first slot starts (assumption (1)), so every correct proposal is that slot
(the `s*` rule); the ACS decides `ℓ` later, still by `T₁(ω + 1)`
(assumption (1)). -/
theorem window_progression (hsync : Sync sch TA r) (hunb : StartsUnbounded th)
    (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th)
    {ω ω' : window} (hn : win_ord.next ω ω') {n0 f b l : ℕ}
    (hb : WinBounds (r.at' n0) ω f b l) (hpost : r.gst ≤ th.start_time f)
    (hall : ∀ j, ¬ fm.byz j →
      ∃ m, r.clk m ≤ th.start_time (f + (sch.p - 1)) ∧ (r.at' m).entered j ω = true) :
    (∀ n f' b' l', WinBounds (r.at' n) ω' f' b' l' → f' = l + 1) ∧
      ∀ j, ¬ fm.byz j → ∃ m, r.clk m ≤ th.start_time (l + 1) ∧ (r.at' m).entered j ω' = true := by
  obtain ⟨rfl, rfl⟩ := bounds_shift hshift hb
  have hW := sch.one_le_W
  have hT : ∀ s, s < f + sch.p → th.start_time s ≤ th.start_time (f + (sch.p - 1)) :=
    fun s hs => start_time_mono r.holds (by omega)
  have hgT : r.gst ≤ th.start_time (f + (sch.p - 1)) := le_trans hpost (start_time_mono r.holds (by omega))
  have hY : max (max (th.start_time (f + (sch.p - 1))) (th.start_time (f + (sch.p - 1)))) r.gst +
      sch.ℓchorus ≤ th.start_time (f + (sch.p - 1)) + sch.ℓchorus := by
    rw [max_self, max_eq_left hgT]
  obtain ⟨hprop, hent⟩ := succ_window hsync hunb hΔ hℓ hcall hterm hn hb hT hY hall
  -- `T_p(ω) + ℓ_chorus + ℓ ≤ T₁(ω + 1)`: assumption (1), with `ℓ_chorus ≤ Φ_oc`.
  have harith : th.start_time (f + (sch.p - 1)) + sch.ℓchorus + sch.ℓ ≤
      th.start_time (f + (sch.W - 1) + 1) := by
    rw [show f + (sch.W - 1) + 1 = f + sch.W by omega, start_add hstart, start_add hstart]
    have h2 : (sch.p - 1) • sch.τ + sch.ℓchorus + sch.ℓ ≤ (sch.p - 1) • sch.τ + sch.Φ_oc + sch.ℓ :=
      add_le_add_left (add_le_add_right (le_add_of_nonneg_right sch.d_tot_nonneg) _) _
    calc th.start_time f + (sch.p - 1) • sch.τ + sch.ℓchorus + sch.ℓ
        = th.start_time f + ((sch.p - 1) • sch.τ + sch.ℓchorus + sch.ℓ) := by abel
      _ ≤ th.start_time f + sch.W • sch.τ := add_le_add_right (h2.trans sch.assm_one_Φ) _
  refine ⟨fun n f' b' l' hb' => ?_, fun j hj => ?_⟩
  · -- Point 1: every correct proposal to the next ACS is the slot after `ω`'s last.
    obtain ⟨r1, s1, r2, s2, hr1, hr2, hs1, hs2, ⟨m1, hm1⟩, ⟨m2, hm2⟩⟩ :=
      recorded_bracket (win_next_ne_zero hn) hb'
    have hslot : ∀ q s m, ¬ fm.byz q → A.proposed ((r.at' m).acs_state ω') q s →
        s = f + (sch.W - 1) + 1 := by
      intro q s m hq hm
      obtain ⟨e, hce, w, a, hl⟩ := proposal_step_by hprop hq hm
      obtain ⟨hlt, -, hfirst⟩ := sstar_slot hsync.2.2.1 hn hb hl
      by_contra hne
      have hbefore := hfirst (f + (sch.W - 1) + 1) (by omega) (by omega)
      have hafter : r.clk e ≤ th.start_time (f + (sch.W - 1) + 1) :=
        le_trans hce (le_trans (le_add_of_nonneg_right sch.ℓ_pos.le) harith)
      exact absurd hbefore (not_lt.2 hafter)
    have h1 := hslot r1 s1 m1 hr1 hm1
    have h2 := hslot r2 s2 m2 hr2 hm2
    omega
  · -- Point 2: every correct validator enters the next window by its starting time.
    obtain ⟨m, hm, he⟩ := hent j hj
    exact ⟨m, le_trans hm harith, he⟩

/-- The progression from a post-GST window entered by `T_p` on time: the
`k`-th window after it starts `kW` slots later, and is entered by every
correct validator by its `T_p`, and from the first successor on by its
`T₁`. -/
theorem progression_chain (hsync : Sync sch TA r) (hunb : StartsUnbounded th)
    (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) {i₀ : node} (hi₀ : ¬ fm.byz i₀)
    {ωs : window} {n0 fs bs ls : ℕ} (hb : WinBounds (r.at' n0) ωs fs bs ls)
    (hpost : r.gst ≤ th.start_time fs)
    (hall : ∀ j, ¬ fm.byz j →
      ∃ m, r.clk m ≤ th.start_time (fs + (sch.p - 1)) ∧ (r.at' m).entered j ωs = true)
    {k : ℕ} {ω : window} (h : WinSucc ωs k ω) :
    (∃ n b l, WinBounds (r.at' n) ω (fs + k * sch.W) b l) ∧
      (∀ j, ¬ fm.byz j →
        ∃ m, r.clk m ≤ th.start_time (fs + k * sch.W + (sch.p - 1)) ∧ (r.at' m).entered j ω = true) ∧
      (0 < k → ∀ j, ¬ fm.byz j →
        ∃ m, r.clk m ≤ th.start_time (fs + k * sch.W) ∧ (r.at' m).entered j ω = true) := by
  induction h with
  | refl =>
    refine ⟨⟨n0, bs, ls, by simpa using hb⟩, by simpa using hall, fun h => absurd h (lt_irrefl 0)⟩
  | @next k ω₁ ω₂ _ hn ih =>
    obtain ⟨⟨n₁, b₁, l₁, hb₁⟩, hall₁, -⟩ := ih
    have hpost₁ : r.gst ≤ th.start_time (fs + k * sch.W) :=
      le_trans hpost (start_time_mono r.holds (by omega))
    obtain ⟨hpt1, hpt2⟩ :=
      window_progression hsync hunb hΔ hℓ hcall hterm hstart hshift hn hb₁ hpost₁ hall₁
    obtain ⟨-, rfl⟩ := bounds_shift hshift hb₁
    have hW := sch.one_le_W
    have hnext : fs + k * sch.W + (sch.W - 1) + 1 = fs + (k + 1) * sch.W := by
      rw [Nat.succ_mul]; omega
    rw [hnext] at hpt2
    obtain ⟨m, -, he⟩ := hpt2 i₀ hi₀
    obtain ⟨f₂, b₂, l₂, hb₂⟩ := Conductor.reachable_entered_has_bounds (r.reachable m) i₀ ω₂ ⟨hi₀, he⟩
    have hf₂ := hpt1 m f₂ b₂ l₂ ⟨i₀, hi₀, hb₂⟩
    rw [hnext] at hf₂
    subst hf₂
    refine ⟨⟨m, b₂, l₂, ⟨i₀, hi₀, hb₂⟩⟩, fun j hj => ?_, fun _ => hpt2⟩
    obtain ⟨m', hm', he'⟩ := hpt2 j hj
    exact ⟨m', le_trans hm' (start_time_mono r.holds (by omega)), he'⟩

/-- **Proposition 18 (`prop:smooth-windows`)**: from the window after a
post-GST window `ω*` on — in particular after the smallest one — the
windows follow each other without gaps (the `(k + 1)`-th window after `ω*`
starts `(k + 1)W` slots after it, so its first slot follows its
predecessor's last), and every correct validator opens each of their slots
by its starting time. `ω*` itself is entered by `T_p(ω*)`: Proposition 16
and assumption (4). -/
theorem smooth_windows (hsync : Sync sch TA r) (hunb : StartsUnbounded th)
    (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th) {i₀ : node} (hi₀ : ¬ fm.byz i₀)
    {ωs : window} {n0 fs bs ls : ℕ} (hb : WinBounds (r.at' n0) ωs fs bs ls)
    (hpost : r.gst ≤ th.start_time fs) {k : ℕ} {ω : window} (h : WinSucc ωs (k + 1) ω) :
    (∃ n b l, WinBounds (r.at' n) ω (fs + (k + 1) * sch.W) b l) ∧
      ∀ s, fs + (k + 1) * sch.W ≤ s → s < fs + (k + 2) * sch.W → ∀ j, ¬ fm.byz j →
        ∃ m, r.clk m ≤ th.start_time s ∧ (r.at' m).opened j s = true := by
  have hall : ∀ j, ¬ fm.byz j →
      ∃ m, r.clk m ≤ th.start_time (fs + (sch.p - 1)) ∧ (r.at' m).entered j ωs = true := by
    intro j hj
    obtain ⟨m, hm, he⟩ := window_open_time hsync hunb hΔ hℓ hcall hstart hb hj
    refine ⟨m, le_trans hm ?_, he⟩
    rw [max_eq_left hpost, start_add hstart, add_assoc]
    have h4 := sch.assm_four_d
    rw [sch.d_tot_paper] at h4
    exact add_le_add_right h4 _
  obtain ⟨⟨n, b, l, hbω⟩, -, hT₁⟩ :=
    progression_chain hsync hunb hΔ hℓ hcall hterm hstart hshift hi₀ hb hpost hall h
  refine ⟨⟨n, b, l, hbω⟩, fun s hs1 hs2 j hj => ?_⟩
  obtain ⟨-, rfl⟩ := bounds_shift hshift hbω
  obtain ⟨m, hm, he⟩ := hT₁ (Nat.succ_pos k) j hj
  have hsl : s ≤ fs + (k + 1) * sch.W + (sch.W - 1) := by
    have : (k + 2) * sch.W = (k + 1) * sch.W + sch.W := Nat.succ_mul _ _
    omega
  obtain ⟨m', -, hm', ho⟩ := open_by hsync.2.1 hj he hbω hs1 hsl
  exact ⟨m', le_trans hm' (max_le (le_trans hm (start_time_mono r.holds hs1)) le_rfl), ho⟩

/-- **Proposition 19 (`prop:first-post-gst-window-time`)**: the smallest
post-GST window, when it is not window 1, starts by `GST + Wτ`. Its
predecessor `ω₁` starts before GST and is entered by
`GST + d_tot + ℓ ≤ GST + (p − 1)τ` (Proposition 16, assumption (4)); every
correct validator then completes the slots below `ω₁`'s boundary by
`GST + (p − 1)τ + ℓ_chorus` and proposes; a correct proposal at or above the
next window's first slot (the median's upper bracket) is either the slot
after `ω₁`'s last, which starts before `GST + Wτ`, or the first slot not yet
started when it was made, which starts within `τ` of that time, by
`GST + Wτ` (assumption (2)). -/
theorem first_post_gst_window_time (hsync : Sync sch TA r) (hunb : StartsUnbounded th)
    (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hcall : (orchestratorSafety th).CallerTotality (contractRun r) sch.Δ)
    (hterm : (orchestratorSafety th).CallerTermination (contractRun r) sch.Δ sch.ℓchorus)
    (hstart : StartTimes sch th) (hshift : WindowShifts sch th)
    {ω₁ ω : window} (hn : win_ord.next ω₁ ω) {n₁ f₁ b₁ l₁ : ℕ}
    (hb₁ : WinBounds (r.at' n₁) ω₁ f₁ b₁ l₁) (hpre : th.start_time f₁ < r.gst)
    {n f b l : ℕ} (hb : WinBounds (r.at' n) ω f b l) :
    th.start_time f ≤ r.gst + sch.W • sch.τ := by
  obtain ⟨rfl, rfl⟩ := bounds_shift hshift hb₁
  have hW := sch.one_le_W
  have hτ : (0 : time) ≤ sch.τ := sch.τ_pos.le
  -- Every correct validator enters `ω₁` by `GST + (p − 1)τ`.
  have hX : r.gst + sch.Δ + sch.ℓ ≤ r.gst + (sch.p - 1) • sch.τ := by
    have h4 := sch.assm_four_d
    rw [sch.d_tot_paper] at h4
    rw [add_assoc]
    exact add_le_add_right h4 _
  have hall : ∀ j, ¬ fm.byz j →
      ∃ m, r.clk m ≤ r.gst + (sch.p - 1) • sch.τ ∧ (r.at' m).entered j ω₁ = true := by
    intro j hj
    obtain ⟨m, hm, he⟩ := window_open_time hsync hunb hΔ hℓ hcall hstart hb₁ hj
    rw [max_eq_right hpre.le] at hm
    exact ⟨m, le_trans hm hX, he⟩
  have hT : ∀ s, s < f₁ + sch.p → th.start_time s ≤ r.gst + (sch.p - 1) • sch.τ := by
    intro s hs
    refine le_trans (start_time_mono r.holds (show s ≤ f₁ + (sch.p - 1) by omega)) ?_
    rw [start_add hstart]
    exact add_le_add_left hpre.le _
  have hgX : r.gst ≤ r.gst + (sch.p - 1) • sch.τ := le_add_of_nonneg_right (nsmul_nonneg hτ _)
  have hY : max (max (r.gst + (sch.p - 1) • sch.τ) (r.gst + (sch.p - 1) • sch.τ)) r.gst +
      sch.ℓchorus ≤ r.gst + (sch.p - 1) • sch.τ + sch.ℓchorus := by
    rw [max_self, max_eq_left hgX]
  obtain ⟨hprop, -⟩ := succ_window hsync hunb hΔ hℓ hcall hterm hn hb₁ hT hY hall
  -- The median's upper bracket: a correct proposal at or above the first slot.
  obtain ⟨-, -, r2, s2, -, hr2, -, hs2, -, ⟨m2, hm2⟩⟩ := recorded_bracket (win_next_ne_zero hn) hb
  obtain ⟨e, hce, w, a, hl⟩ := proposal_step_by hprop hr2 hm2
  obtain ⟨hlt, -, hfirst⟩ := sstar_slot hsync.2.2.1 hn hb₁ hl
  have hWτ : sch.W • sch.τ = (sch.W - 1) • sch.τ + sch.τ := by
    rw [← succ_nsmul, Nat.sub_add_cancel hW]
  have hs2le : th.start_time s2 ≤ r.gst + sch.W • sch.τ := by
    rcases Nat.lt_or_ge (f₁ + (sch.W - 1) + 1) s2 with hgt | hle
    · -- The first slot not yet started: within `τ` of the proposal.
      have h1 := hfirst (s2 - 1) (by omega) (by omega)
      have h2 : (sch.p - 1) • sch.τ + sch.ℓchorus ≤ (sch.W - 1) • sch.τ :=
        le_trans (add_le_add_right (le_add_of_nonneg_right sch.d_tot_nonneg) _) sch.assm_two_Φ
      rw [show s2 = s2 - 1 + 1 by omega, start_add hstart, one_nsmul, hWτ]
      calc th.start_time (s2 - 1) + sch.τ
          ≤ r.gst + (sch.p - 1) • sch.τ + sch.ℓchorus + sch.τ := add_le_add_left (le_trans h1.le hce) _
        _ = r.gst + ((sch.p - 1) • sch.τ + sch.ℓchorus) + sch.τ := by abel
        _ ≤ r.gst + (sch.W - 1) • sch.τ + sch.τ := add_le_add_left (add_le_add_right h2 _) _
        _ = r.gst + ((sch.W - 1) • sch.τ + sch.τ) := by abel
    · -- The slot after `ω₁`'s last.
      rw [show s2 = f₁ + sch.W by omega, start_add hstart]
      exact add_le_add_left hpre.le _
  exact le_trans (start_time_mono r.holds hs2) hs2le

end Items

/-! ## Lemma 16: `(2Wτ)`-Recovery -/

section Recovery

variable {window node acsstate : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [win_ord : TotalOrderWithMinimum window] [fm : FaultModel node]
  [A : ACSSafety node ℕ acsstate fm.byz]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {view : Type} [vord : TotalOrderWithMinimum view] {vfin : ViewOrderEnum view vord}

/-- **`(2Wτ)`-Recovery** (Lemma 16 (`lemma:conductor-recovery`)), the target
`RecoveryClaim` of [Schedule.lean](Schedule.lean): every slot whose starting
time is at least `GST + 2Wτ` is opened by every correct validator by its
starting time. The smallest post-GST window `ω*` starts by `GST + Wτ`
(Proposition 19) — or is window 1, entered at its starting time — so such a
slot lies in a window from `ω*`'s successor on, all of whose slots are
opened by their starting times (Proposition 18). -/
theorem recovery {msg : Type} (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz)
    (th : Conductor.Theory ℕ window time node acsstate) :
    RecoveryClaim sch TA th := by
  intro hstart hshift hunb hwin hΔ hℓ r hsync hcall hterm s hs i hi
  rw [sch.d_tot_paper] at hcall hterm
  rw [contract_byTime_iff]
  obtain ⟨k, ω, n, f, b, l, hk, hb, hpost, hcase⟩ :=
    exists_post_gst hsync hunb hΔ hℓ hcall hterm hwin hi
  have hW := sch.one_le_W
  by_cases hsW : f + sch.W ≤ s
  · -- `s` lies in the `j`-th window after `ω*`, `j ≥ 1`.
    obtain ⟨q, hq⟩ : ∃ q, q = (s - f) / sch.W := ⟨_, rfl⟩
    have hdm := Nat.div_add_mod (s - f) sch.W
    have hmod := Nat.mod_lt (s - f) (show 0 < sch.W by omega)
    rw [← hq] at hdm
    have hq1 : 1 ≤ q := by
      rw [hq]
      exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
    obtain ⟨ω', hω'⟩ := WinSucc.exists hwin ω (j + 1)
    obtain ⟨-, hopen⟩ :=
      smooth_windows hsync hunb hΔ hℓ hcall hterm hstart hshift hi hb hpost hω'
    have e1 : (j + 1) * sch.W = sch.W * (j + 1) := Nat.mul_comm _ _
    have e2 : (j + 2) * sch.W = sch.W * (j + 1) + sch.W := by
      rw [show j + 2 = (j + 1) + 1 from rfl, Nat.succ_mul, Nat.mul_comm]
    exact hopen s (by omega) (by omega) i hi
  · rcases hcase with rfl | ⟨ω₁, n₁, f₁, b₁, l₁, hn, hb₁, hpre⟩
    · -- `ω*` is window 1, entered at its starting time: `s` lies in it.
      cases hk
      obtain rfl := zero_first hb
      obtain ⟨-, rfl⟩ := bounds_shift hshift hb
      have h0 : r.clk 0 = th.start_time 0 := by
        rw [clk_zero hstart hsync.2.2.1, hstart]
        simp [ConductorSchedule.startTime]
      obtain ⟨m, -, hm, ho⟩ := open_by hsync.2.1 hi (Conductor.reachable_entered_zero (r.reachable 0) i)
        hb (Nat.zero_le s) (by omega)
      exact ⟨m, le_trans hm (max_le (h0 ▸ start_time_mono r.holds (Nat.zero_le s)) le_rfl), ho⟩
    · -- Otherwise `ω*` starts by `GST + Wτ` (Proposition 19), so `s` is beyond it.
      exfalso
      apply hsW
      have h19 :=
        first_post_gst_window_time hsync hunb hΔ hℓ hcall hterm hstart hshift hn hb₁ hpre hb
      refine le_of_start_le r.holds ?_
      rw [start_add hstart]
      refine le_trans ?_ hs
      rw [ConductorSchedule.recoveryTime, two_mul, add_nsmul, ← add_assoc]
      exact add_le_add_left h19 _

/-- **Recovery holds at `(W + p − 1)τ`**, which is at most the paper's
`2Wτ` (`p < W`): slack in `𝓡`, recorded for the authors
([ConductorBounds.md](../../docs/ConductorBounds.md) §9, K5). The smallest
post-GST window `ω*` is itself entered by `T_p(ω*)` (Proposition 16 and
assumption (4)), so its slots from the `p`-th on are opened by their
starting times as well, and these start by `GST + (W + p − 1)τ`. Same
premises as `RecoveryClaim`. -/
theorem recovery_sharp {msg : Type} (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal node ℕ acsstate time msg fm.byz)
    (th : Conductor.Theory ℕ window time node acsstate) :
    StartTimes sch th → WindowShifts sch th → StartsUnbounded th → WindowsUnbounded window →
    TA.Δ = sch.Δ → TA.ℓ = sch.ℓ →
    ∀ r : TConductorRun th, Sync sch TA r →
      (orchestratorSafety th).CallerTotality (contractRun r) sch.d_tot →
      (orchestratorSafety th).CallerTermination (contractRun r) sch.d_tot sch.ℓchorus →
      ∀ s, r.gst + (sch.W + (sch.p - 1)) • sch.τ ≤ th.start_time s →
        ∀ i, ¬ fm.byz i → (contractRun r).byTime (th.start_time s) (fun st => Opened st i s) := by
  intro hstart hshift hunb hwin hΔ hℓ r hsync hcall hterm s hs i hi
  rw [sch.d_tot_paper] at hcall hterm
  rw [contract_byTime_iff]
  obtain ⟨k, ω, n, f, b, l, hk, hb, hpost, hcase⟩ :=
    exists_post_gst hsync hunb hΔ hℓ hcall hterm hwin hi
  have hW := sch.one_le_W
  by_cases hsW : f + sch.W ≤ s
  · obtain ⟨q, hq⟩ : ∃ q, q = (s - f) / sch.W := ⟨_, rfl⟩
    have hdm := Nat.div_add_mod (s - f) sch.W
    have hmod := Nat.mod_lt (s - f) (show 0 < sch.W by omega)
    rw [← hq] at hdm
    have hq1 : 1 ≤ q := by
      rw [hq]
      exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
    obtain ⟨ω', hω'⟩ := WinSucc.exists hwin ω (j + 1)
    obtain ⟨-, hopen⟩ :=
      smooth_windows hsync hunb hΔ hℓ hcall hterm hstart hshift hi hb hpost hω'
    have e1 : (j + 1) * sch.W = sch.W * (j + 1) := Nat.mul_comm _ _
    have e2 : (j + 2) * sch.W = sch.W * (j + 1) + sch.W := by
      rw [show j + 2 = (j + 1) + 1 from rfl, Nat.succ_mul, Nat.mul_comm]
    exact hopen s (by omega) (by omega) i hi
  · obtain ⟨-, rfl⟩ := bounds_shift hshift hb
    rcases hcase with rfl | ⟨ω₁, n₁, f₁, b₁, l₁, hn, hb₁, hpre⟩
    · cases hk
      obtain rfl := zero_first hb
      have h0 : r.clk 0 = th.start_time 0 := by
        rw [clk_zero hstart hsync.2.2.1, hstart]
        simp [ConductorSchedule.startTime]
      obtain ⟨m, -, hm, ho⟩ := open_by hsync.2.1 hi (Conductor.reachable_entered_zero (r.reachable 0) i)
        hb (Nat.zero_le s) (by omega)
      exact ⟨m, le_trans hm (max_le (h0 ▸ start_time_mono r.holds (Nat.zero_le s)) le_rfl), ho⟩
    · -- `s` lies in `ω*`, at or after its `p`-th slot, which `ω*`'s entry precedes.
      have h19 :=
        first_post_gst_window_time hsync hunb hΔ hℓ hcall hterm hstart hshift hn hb₁ hpre hb
      have hsp : f + (sch.p - 1) ≤ s := by
        refine le_of_start_le r.holds ?_
        rw [start_add hstart]
        refine le_trans ?_ hs
        rw [add_nsmul, ← add_assoc]
        exact add_le_add_left h19 _
      obtain ⟨m, hm, he⟩ := window_open_time hsync hunb hΔ hℓ hcall hstart hb hi
      have hent : r.clk m ≤ th.start_time s := by
        refine le_trans hm (le_trans ?_ (start_time_mono r.holds hsp))
        rw [max_eq_left hpost, start_add hstart, add_assoc]
        have h4 := sch.assm_four_d
        rw [sch.d_tot_paper] at h4
        exact add_le_add_right h4 _
      obtain ⟨m', -, hm', ho⟩ := open_by hsync.2.1 hi he hb (show f ≤ s by omega) (by omega)
      exact ⟨m', le_trans hm' (max_le hent le_rfl), ho⟩

end Recovery

end Conductor

/-! ## The pinned trust base -/

/--
info: 'Conductor.open_to_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.open_to_complete

/--
info: 'Conductor.enters_every_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.enters_every_window

/--
info: 'Conductor.window_open_time' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.window_open_time

/--
info: 'Conductor.window_progression' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.window_progression

/--
info: 'Conductor.smooth_windows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.smooth_windows

/--
info: 'Conductor.first_post_gst_window_time' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.first_post_gst_window_time

/--
info: 'Conductor.recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.recovery

/--
info: 'Conductor.recovery_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.recovery_sharp
