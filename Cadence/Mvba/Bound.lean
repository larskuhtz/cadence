import Cadence.Mvba.Schedule
import Mathlib.Tactic.Abel

/-! # Mvba.Bound — the good-view lemma

[`docs/Bounds.md`](../../docs/Bounds.md) §6.2, step 2. The second of the two
lemmas §6.2.6 derives, proven: **a correct-led view whose budget clears the
chain's latency decides within that latency.** From the first index at which
a correct validator has entered such a view `W`, at a clock `E₀` at or after
GST, with every correct validator having proposed and none abandoned inside
the window, a commit certificate of `W` exists by `E₀ + Lcert` and every
correct validator has decided by `E₀ + Lcert + δ` (`good_view_decides`).

The premises are `Mvba/Schedule.lean`'s three clauses and nothing else: no
fairness of the untimed kind, no (A-viewsync), no statement about the timer
beyond (T1). The two instance hypotheses are the quorum classes the untimed
chain already takes.

## How it is built

The untimed chain of `Mvba/Liveness.lean` is re-run with "within `D`" in
place of "eventually". Each of its links was `enabled_<action>` (guards ⇒
enabledness) + one weak-fairness step + `<action>_effect`; each link here
keeps the first and the third and replaces the second by one application of
`BoundedFair` through `TLRun.withinFrom_of_boundedFair` below. That lemma
also pays the one side condition move-enabledness costs: a label whose effect
sets a flag the goal is about is *move*-enabled wherever it is enabled and the
goal does not yet hold, because its post-state has the flag and the
pre-state does not (`EnabledMove.of_enabled_of_effect`).

The anti-monotone guards are handled exactly as the untimed links handle
them — a lapse of `¬ proposed_in`, `∀ W, voted i W → W < v`, the lock-view
bound, `¬ commit_sent` or `∀ E, ¬ decided` *is* the goal, by the same
invariants — except `in_view`, `¬ timed_out` and `¬ abandoned`, which the
untimed chain assumed (`SettledIn`) and which here hold on a **prefix** of
the run rather than for ever:

* `¬ timed_out i W` below the clock `E₀ + τ W`: (T1) says the timer fires
  no earlier than `τ W` after an entry, every correct entry is at or after
  `E₀`, and a validator that has timed out had its timer fire first
  (`not_timed_out_before_budget`);
* `in_view i W` on the same prefix: `entered_le_of_no_timeout_before`, the
  prefix form of `Mvba.entered_le_of_no_timeout` — no correct validator is
  above `W` while none has timed out in it;
* `¬ abandoned` inside the window: the caller's premise, as in the claim.

`τ W > Lcert` makes the chain's window lie inside that prefix, which is the
whole role of (S-ramp) here.

## One requirement on the time theory

The lemma takes `[IsOrderedCancelAddMonoid time]`, where `Schedule.lean`
takes `IsOrderedAddMonoid`. The step that needs it is "`Lcert < τ W`, hence
`E₀ + Lcert < E₀ + τ W`": without cancellation it fails — in `ℕ∞` a clock
reading `⊤` makes both sides `⊤`, a correct `W`-timer may fire inside the
window, and a validator that times out in `W` stops the chain. `ℕ`, `ℚ≥0`
and `ℝ≥0` are cancellative; `docs/Bounds.md` §6.2.8 records the finding.

## What is local, and why

Three facts `Mvba/Liveness.lean` does not export are proven here from the
generated lemmas and the `reachable_*` projections, since that file is
read-only for this leg (`docs/Liveness.md` §4.1): the `timer_expired` flag is
set only by `expire_timer` (`timer_set_label`, from M13's per-action frame
lemmas), the prefix form of `entered_le_of_no_timeout`, and the timeout
certificate below a view present *at* the first entry into it rather than at
some index (`msg_tc_below_of_entered`). -/

/-! ## Two generic facts about bounded fairness -/

namespace Cadence

open Veil

section

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {time : Type} [LinearOrder time]

/-- **The side condition, paid once.** If every step under `l` from `st`
lands in a state satisfying `P`, and `st` does not satisfy `P`, then an
enabled `l` is move-enabled: the post-state differs from `st` because one
satisfies `P` and the other does not. -/
theorem EnabledMove.of_enabled_of_effect {st : σ} {l : lbl} {P : σ → Prop}
    (hen : Enabled sys th st l) (heff : ∀ st', sys.tr th st l st' → P st')
    (hnot : ¬ P st) : EnabledMove sys th st l := by
  obtain ⟨st', htr⟩ := hen
  exact ⟨st', htr, fun h => hnot (h ▸ heff st' htr)⟩

namespace TLRun

variable {r : TLRun sys th time}

/-- A later deadline is a weaker one. -/
theorem WithinFrom.mono_time {N : Nat} {t t' : time} {P : σ → Prop}
    (h : r.WithinFrom N t P) (ht : t ≤ t') : r.WithinFrom N t' P :=
  let ⟨n, hn, hclk, hP⟩ := h
  ⟨n, hn, le_trans hclk ht, hP⟩

/-- **One timed link.** The shape every link of the good-view chain has:
if every firing of `l` establishes `P`, and wherever `P` does not yet hold
inside the window `l` is enabled, then `P` holds within the window — by one
application of bounded fairness, whose move-enabledness side condition is
discharged by `EnabledMove.of_enabled_of_effect`.

The window is the fairness window `ref N + D` widened to any `B` above it,
so that a caller states its stable facts once, up to its own deadline. -/
theorem withinFrom_of_boundedFair [Add time] {D : time} {l : lbl}
    (hbf : BoundedFair r D l) {N : Nat} {B : time} (hB : r.ref N + D ≤ B)
    {P : σ → Prop}
    (heff : ∀ st st', sys.tr th st l st' → P st')
    (hen : ∀ n, N ≤ n → r.clk n ≤ B → ¬ P (r.at' n) → Enabled sys th (r.at' n) l) :
    r.WithinFrom N B P := by
  by_cases hf : r.FiresWithin N D l
  · obtain ⟨n, hn, hl, hclk⟩ := hf
    exact ⟨n + 1, Nat.le_succ_of_le hn, le_trans hclk hB, heff _ _ (hl ▸ r.steps n)⟩
  · obtain ⟨n, hn, hclk, hne⟩ := exists_not_moveEnabled_of_not_firesWithin hbf hf
    by_cases hP : P (r.at' n)
    · exact ⟨n, hn, le_trans hclk hB, hP⟩
    · exact absurd (EnabledMove.of_enabled_of_effect
        (hen n hn (le_trans hclk hB) hP) (heff _) hP) hne

/-- The clock at the later of two indices is the clock at one of them. -/
theorem clk_max_le {m n : Nat} {t : time} (hm : r.clk m ≤ t) (hn : r.clk n ≤ t) :
    r.clk (max m n) ≤ t := by
  rcases le_total m n with h | h
  · rw [max_eq_right h]; exact hn
  · rw [max_eq_left h]; exact hm

end TLRun

end

end Cadence

namespace Mvba

open Cadence
open scoped Cadence.Timed

/-- Expose an action's transition body in `h` — `Mvba/Liveness.lean`'s
local tactic of the same name, repeated because it is local there. -/
local macro "mvba_tr" h:ident : tactic =>
  `(tactic| (simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `set`/`get` pair in a hypothesis. -/
local macro "mvba_effect_at" h:ident : tactic =>
  `(tactic| simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id] at $h:ident)

/-! ## Three state facts `Mvba/Liveness.lean` does not export -/

section Local

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}

/-- `expire_timer i' v'` sets the marker of `(i', v')` and no other. -/
theorem expire_timer_sets {i i' : node} {v v' : view}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.expire_timer i' v') st')
    (h0 : ¬ st.timer_expired i v = true) (h1 : st'.timer_expired i v = true) :
    i' = i ∧ v' = v := by
  mvba_tr htr
  obtain ⟨-, rfl⟩ := htr
  mvba_effect_at h1
  exact h1.resolve_right h0

/-- **Only the timer sets the timer.** A step that turns `timer_expired i v`
on is `expire_timer i v`. Every other action leaves the relation untouched,
which is M13's generated frame lemma for that action; the case split is over
the model's own label type, so an added action is a missing case, not a
silent gap. -/
theorem timer_set_label {l : Mvba.Label node nodeset value view} {i : node} {v : view}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (h0 : ¬ st.timer_expired i v = true) (h1 : st'.timer_expired i v = true) :
    l = .expire_timer i v := by
  cases l
  case expire_timer i' v' =>
    obtain ⟨rfl, rfl⟩ := expire_timer_sets htr h0 h1
    rfl
  case propose => rw [Mvba.propose.frame_timer_expired htr] at h1; exact absurd h1 h0
  case abandon => rw [Mvba.abandon.frame_timer_expired htr] at h1; exact absurd h1 h0
  case leader_propose_first =>
    rw [Mvba.leader_propose_first.frame_timer_expired htr] at h1; exact absurd h1 h0
  case leader_repropose =>
    rw [Mvba.leader_repropose.frame_timer_expired htr] at h1; exact absurd h1 h0
  case leader_propose_fresh =>
    rw [Mvba.leader_propose_fresh.frame_timer_expired htr] at h1; exact absurd h1 h0
  case handle_preprepare_first =>
    rw [Mvba.handle_preprepare_first.frame_timer_expired htr] at h1; exact absurd h1 h0
  case handle_preprepare =>
    rw [Mvba.handle_preprepare.frame_timer_expired htr] at h1; exact absurd h1 h0
  case form_prepqc => rw [Mvba.form_prepqc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case adopt_prepqc => rw [Mvba.adopt_prepqc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case become_avail_ready =>
    rw [Mvba.become_avail_ready.frame_timer_expired htr] at h1; exact absurd h1 h0
  case send_commit => rw [Mvba.send_commit.frame_timer_expired htr] at h1; exact absurd h1 h0
  case form_commitqc =>
    rw [Mvba.form_commitqc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case decide => rw [Mvba.decide.frame_timer_expired htr] at h1; exact absurd h1 h0
  case timeout_qc => rw [Mvba.timeout_qc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case timeout_noqc => rw [Mvba.timeout_noqc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case form_tc_lock => rw [Mvba.form_tc_lock.frame_timer_expired htr] at h1; exact absurd h1 h0
  case form_tc_nolock =>
    rw [Mvba.form_tc_nolock.frame_timer_expired htr] at h1; exact absurd h1 h0
  case sync_view => rw [Mvba.sync_view.frame_timer_expired htr] at h1; exact absurd h1 h0
  case sync_view_adopt =>
    rw [Mvba.sync_view_adopt.frame_timer_expired htr] at h1; exact absurd h1 h0
  case byz_preprepare =>
    rw [Mvba.byz_preprepare.frame_timer_expired htr] at h1; exact absurd h1 h0
  case byz_prepare => rw [Mvba.byz_prepare.frame_timer_expired htr] at h1; exact absurd h1 h0
  case byz_commit => rw [Mvba.byz_commit.frame_timer_expired htr] at h1; exact absurd h1 h0
  case byz_timeout_qc =>
    rw [Mvba.byz_timeout_qc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case byz_timeout_noqc =>
    rw [Mvba.byz_timeout_noqc.frame_timer_expired htr] at h1; exact absurd h1 h0

/-- **A marker that is on was switched on by an `expire_timer` step before.**
`timer_expired` is empty initially (M13's `init` lemma), so a least index
where it holds exists, and the step into it is the timer's. -/
theorem exists_expire_timer_before (r : MvbaRun th) {i : node} {v : view} {n : Nat}
    (h : (r.at' n).timer_expired i v = true) :
    ∃ m, m < n ∧ r.lbl m = .expire_timer i v := by
  classical
  have hex : ∃ k, (r.at' k).timer_expired i v = true := ⟨n, h⟩
  have hk := Nat.find_spec hex
  have hle : Nat.find hex ≤ n := Nat.find_min' hex h
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0] at hk
    simp [Mvba.timer_expired.init r.starts i v] at hk
  · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin : ¬ (r.at' m).timer_expired i v = true := Nat.find_min hex (by omega)
    exact ⟨m, by omega, timer_set_label (r.steps m) hmin (by rw [← hm]; exact hk)⟩

/-- **The prefix form of `entered_le_of_no_timeout`.** If no correct
validator has timed out in `W` at any index before `K`, then up to `K` no
correct validator is in a view above `W`. The untimed lemma's induction,
stopped at `K`: the step into index `n + 1` consults a timeout at index `n`,
so the hypothesis is needed strictly below the bound. -/
theorem entered_le_of_no_timeout_before (r : MvbaRun th) {W : view} {K : Nat}
    (hvs : ∀ (i : node) (n : Nat), n < K → ¬ nset.is_byz i = true →
      ¬ (r.at' n).timed_out i W = true) :
    ∀ n, n ≤ K → ∀ (j : node) (V : view), ¬ nset.is_byz j = true →
      (r.at' n).entered j V = true → vord.le V W := by
  intro n
  induction n with
  | zero => exact fun _ j V _ hV => absurd hV (init_not_entered r.starts j V)
  | succ n ih =>
    intro hK j V hj hV
    have hn : n ≤ K := Nat.le_of_succ_le hK
    by_cases hprev : (r.at' n).entered j V = true
    · exact ih hn j V hj hprev
    rcases Mvba.reachable_entered_needs_certificate_step (r.reachable n) (r.steps n)
      j V ⟨hj, hprev, hV⟩ with rfl | ⟨PV, hnext, hcert⟩
    · exact vord.zero_lt W
    have hto : ∃ R, ¬ nset.is_byz R = true ∧ (r.at' n).timed_out R PV = true := by
      rcases hcert with htc | ⟨Wc, Ec, hlock⟩
      · exact exists_honest_timed_out_of_tc (r.reachable n) htc
      · exact exists_honest_timed_out_of_tc_lock (r.reachable n) hlock
    obtain ⟨R, hR, hRto⟩ := hto
    have hPV : vord.le PV W :=
      ih hn R PV hR (Mvba.reachable_timed_out_entered (r.reachable n) R PV hR hRto)
    have hPVne : ¬ PV = W := by
      rintro rfl
      exact hvs R n hK hR hRto
    exact ((vord.next_def PV V).mp hnext).2 W ((vord.le_lt PV W).mpr ⟨hPV, hPVne⟩)

/-- **The certificate below a view is there at any index where the view has
been entered** — `exists_tc_below_of_entered` with the index kept: the first
entry is before `N`, and the certificate it read persists. -/
theorem msg_tc_below_of_entered (r : MvbaRun th) {i : node} (hi : ¬ nset.is_byz i = true)
    {pv W : view} (hnext : vord.next pv W) {N : Nat}
    (hent : (r.at' N).entered i W = true) : (r.at' N).msg_tc pv = true := by
  obtain ⟨m, hfalse, htrue⟩ := exists_first_entry r hent
  have hfalse' : ¬ (r.at' m).entered i W = true := by simp [hfalse]
  have hmN : m < N := by
    by_contra h
    exact hfalse' (r.mono (P := fun s => s.entered i W = true)
      (fun k hk => Mvba.entered.mono (r.steps k) i W hk) hent m (Nat.le_of_not_lt h))
  have htc : (r.at' m).msg_tc pv = true := by
    rcases Mvba.reachable_entered_needs_certificate_step (r.reachable m) (r.steps m)
      i W ⟨hi, hfalse', htrue⟩ with rfl | ⟨PV, hPV, hcert⟩
    · exact absurd hnext not_next_zero
    · have hPVpv : PV = pv := next_unique hPV hnext
      subst hPVpv
      rcases hcert with h | ⟨w, e, h⟩
      · exact h
      · exact Mvba.reachable_tc_lock_implies_tc (r.reachable m) PV w e h
  exact r.mono (P := fun s => s.msg_tc pv = true)
    (fun k hk => Mvba.msg_tc.mono (r.steps k) pv hk) htc N (Nat.le_of_lt hmN)

end Local

/-! ## The prefix on which the good view is safe from its timer -/

section Prefix

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]

/-- **No correct validator times out in `W` before its budget runs out**,
counted from the first correct entry into `W`. A validator that has timed
out had its marker on (`timed_out_implies_timer`), the marker was switched
on by an `expire_timer` step, and (T1) puts that step at least `τ W` after
an entry of the same validator — which is not before `N₀`. -/
theorem not_timed_out_before_budget {sch : Schedule view time} {r : TMvbaRun th time}
    (htp : TimerPunctual sch r) {W : view} {N₀ : Nat}
    (hfirst : ∀ (n : Nat) (j : node), ¬ nset.is_byz j = true →
      (r.at' n).entered j W = true → N₀ ≤ n)
    {i : node} (hi : ¬ nset.is_byz i = true) {n : Nat}
    (hn : r.clk n < r.clk N₀ + sch.τ W) : ¬ (r.at' n).timed_out i W = true := by
  intro hto
  have htimer := Mvba.reachable_timed_out_implies_timer (r.reachable n) i W hi hto
  obtain ⟨m, hmn, hl⟩ := exists_expire_timer_before r.toLRun htimer
  obtain ⟨m', -, hent, hclk⟩ := htp.1 m i W hi hl
  have h1 : r.clk N₀ ≤ r.clk m' := r.clk_le_of_le (hfirst m' i hi hent)
  have h2 : r.clk N₀ + sch.τ W ≤ r.clk n :=
    le_trans (add_le_add h1 le_rfl) (le_trans hclk (r.clk_le_of_le (Nat.le_of_lt hmn)))
  exact absurd hn (not_lt.mpr h2)

/-- **… hence nobody is above `W` on that prefix either**: the prefix form
of `entered_le_of_no_timeout`, read at a clock. -/
theorem entered_le_before_budget {sch : Schedule view time} {r : TMvbaRun th time}
    (htp : TimerPunctual sch r) {W : view} {N₀ : Nat}
    (hfirst : ∀ (n : Nat) (j : node), ¬ nset.is_byz j = true →
      (r.at' n).entered j W = true → N₀ ≤ n)
    {n : Nat} (hn : r.clk n < r.clk N₀ + sch.τ W) :
    ∀ (j : node) (V : view), ¬ nset.is_byz j = true →
      (r.at' n).entered j V = true → vord.le V W :=
  entered_le_of_no_timeout_before r.toLRun (K := n)
    (fun _ _ hm hi => not_timed_out_before_budget htp hfirst hi
      (lt_of_le_of_lt (r.clk_le_of_le (Nat.le_of_lt hm)) hn)) n le_rfl

end Prefix

/-! ## The eight timed links

Each is its untimed twin in `Mvba/Liveness.lean` with the weak-fairness step
replaced by `withinFrom_of_boundedFair`: the monotone guards are given at the
starting index `N` and carried by the generated `<relation>.mono` lemmas, the
anti-monotone guards the untimed link assumed (`SettledIn`) are given on the
window `clk n ≤ B`, and the anti-monotone guard whose lapse is the goal is
discharged by the same invariant the untimed link uses. `hgst` puts the
window's reference time at `clk N`, which is where every link of the good
view starts. -/

section Links

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {time : Type} [LinearOrder time] [AddCommMonoid time]
  {sch : Schedule view time} {r : TMvbaRun th time}

/-- The fairness window of a link starting at or after GST is `clk N + D`. -/
theorem ref_add_le {N : Nat} (hgst : r.gst ≤ r.clk N) {D B : time}
    (hB : r.clk N + D ≤ B) : r.ref N + D ≤ B := by
  rw [r.ref_eq_of_gst_le hgst]; exact hB

/-- **Link 1, `sync_view` (a `Δ` hop): a correct validator enters `W`.** Its
view guard `∀ V, entered i V → V ≤ PV` lapses only by entering a view above
`PV`, which on the prefix bounded by `W` is `W` itself. -/
theorem within_entered_of_tc (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {PV W : view} (hnext : vord.next PV W)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.Δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (htc : (r.at' N).msg_tc PV = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → ¬ (r.at' n).abandoned i = true ∧
      ∀ V, (r.at' n).entered i V = true → vord.le V W) :
    r.WithinFrom N B (fun s => s.entered i W = true) := by
  refine r.withinFrom_of_boundedFair (hbj (.sync_view i PV W) .net rfl) (ref_add_le hgst hB)
    (fun _ _ h => sync_view_effect h) ?_
  intro n hn hclk hnot
  obtain ⟨hab, hle⟩ := hwin n hn hclk
  refine enabled_sync_view hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ hab hnext
    (r.mono (P := fun s => s.msg_tc PV = true)
      (fun m hm => Mvba.msg_tc.mono (r.steps m) PV hm) htc n hn) ?_
  intro V hV
  by_contra hnle
  have hWV : vord.le W V := ((vord.next_def PV W).mp hnext).2 V (lt_of_not_le hnle)
  have hVW : V = W := vord.le_antisymm V W (hle V hV) hWV
  subst hVW
  exact hnot hV

/-- **Link 2, `leader_repropose` / `leader_propose_fresh` (a `δ` step): the
correct leader proposes.** Which of the two labels applies is fixed by the
certificate below `W`, as in the untimed leader link; `¬ proposed_in` lapses
only by the proposal (`proposed_in_backed`). -/
theorem within_preprepare_of_leader (hbj : BoundedJustice sch r)
    {L : node} (hL : ¬ nset.is_byz L = true) {PV W : view} (hnext : vord.next PV W)
    (hlead : th.leader W L = true)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input L E₀ = true)
    (hjust : (∃ w e, (r.at' N).tc_lock PV w e = true) ∨ (r.at' N).tc_nolock PV = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B →
      ¬ (r.at' n).abandoned L = true ∧ InView (r.at' n) L W) :
    r.WithinFrom N B (fun s => ∃ E, s.msg_preprepare L W E = true) := by
  have hin' : ∀ n, N ≤ n → (r.at' n).input L E₀ = true :=
    r.mono (P := fun s => s.input L E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) L E₀ hm) hin
  have hnp : ∀ n, ¬ (∃ E, (r.at' n).msg_preprepare L W E = true) →
      ¬ (r.at' n).proposed_in L W = true := fun n hnot hp =>
    hnot (Mvba.reachable_proposed_in_backed (r.reachable n) L W hL hp)
  rcases hjust with ⟨w, e, hw⟩ | hnl
  · refine r.withinFrom_of_boundedFair (hbj (.leader_repropose L PV W w e) .loc rfl)
      (ref_add_le hgst hB) (fun _ _ h => ⟨e, leader_repropose_effect h⟩) ?_
    intro n hn hclk hnot
    obtain ⟨hab, hview⟩ := hwin n hn hclk
    exact enabled_leader_repropose hL ⟨E₀, hin' n hn⟩ hab hnext hlead hview
      (r.mono (P := fun s => s.tc_lock PV w e = true)
        (fun m hm => Mvba.tc_lock.mono (r.steps m) PV w e hm) hw n hn) (hnp n hnot)
  · refine r.withinFrom_of_boundedFair (hbj (.leader_propose_fresh L PV W E₀) .loc rfl)
      (ref_add_le hgst hB) (fun _ _ h => ⟨E₀, leader_propose_fresh_effect h⟩) ?_
    intro n hn hclk hnot
    obtain ⟨hab, hview⟩ := hwin n hn hclk
    exact enabled_leader_propose_fresh hL hab hnext hlead hview
      (r.mono (P := fun s => s.tc_nolock PV = true)
        (fun m hm => Mvba.tc_nolock.mono (r.steps m) PV hm) hnl n hn) (hin' n hn) (hnp n hnot)

/-- **Link 3, `handle_preprepare` (a `Δ` hop): a correct validator accepts
the correct leader's proposal.** The vote guard lapses only by the
acceptance itself (`accepted_of_vote_guard_lapsed`, which needs the
validator in `W` and not timed out there — the prefix facts). -/
theorem within_accepted (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {L : node} (hL : ¬ nset.is_byz L = true)
    {PV W : view} (hnext : vord.next PV W) (hlead : th.leader W L = true)
    {e : value} (hvalid : th.valid e = true)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.Δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hpp : (r.at' N).msg_preprepare L W e = true)
    (hjust : (∃ w, (r.at' N).tc_lock PV w e = true) ∨ (r.at' N).tc_nolock PV = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → ¬ (r.at' n).abandoned i = true ∧
      InView (r.at' n) i W ∧ ¬ (r.at' n).timed_out i W = true) :
    r.WithinFrom N B (fun s => s.accepted i W e = true) := by
  refine r.withinFrom_of_boundedFair (hbj (.handle_preprepare i L PV W e) .net rfl)
    (ref_add_le hgst hB) (fun _ _ h => (handle_preprepare_effect h).1) ?_
  intro n hn hclk hnot
  obtain ⟨hab, hview, hnto⟩ := hwin n hn hclk
  have hpp' := r.mono (P := fun s => s.msg_preprepare L W e = true)
    (fun m hm => Mvba.msg_preprepare.mono (r.steps m) L W e hm) hpp n hn
  refine enabled_handle_preprepare hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩
    hab hview hnext hlead hpp' hvalid ?_ ?_
  · rcases hjust with ⟨w, hw⟩ | hnl
    · exact Or.inl ⟨w, r.mono (P := fun s => s.tc_lock PV w e = true)
        (fun m hm => Mvba.tc_lock.mono (r.steps m) PV w e hm) hw n hn⟩
    · exact Or.inr (r.mono (P := fun s => s.tc_nolock PV = true)
        (fun m hm => Mvba.tc_nolock.mono (r.steps m) PV hm) hnl n hn)
  · by_contra hlapse
    exact hnot (accepted_of_vote_guard_lapsed (r.reachable n) hi hview hnto hlead hL hpp'
      hlapse)

/-- **Link 4, `form_prepqc` (a `Δ` hop): the prepare certificate forms.**
Both guards monotone; the untimed twin is `eventually_prepqc_of_prepare_quorum`. -/
theorem within_prepqc (hbj : BoundedJustice sch r)
    {W : view} {e : value} {q : nodeset} (hsm : nset.supermajority q)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.Δ ≤ B)
    (hall : ∀ p, nset.member p q = true → (r.at' N).msg_prepare p W e = true) :
    r.WithinFrom N B (fun s => s.msg_prepqc W e = true) := by
  refine r.withinFrom_of_boundedFair (hbj (.form_prepqc W e q) .net rfl)
    (ref_add_le hgst hB) (fun _ _ h => form_prepqc_effect h) ?_
  intro n hn _ _
  exact enabled_form_prepqc hsm (fun p hp => r.mono (P := fun s => s.msg_prepare p W e = true)
    (fun m hm => Mvba.msg_prepare.mono (r.steps m) p W e hm) (hall p hp) n hn)

/-- **Link 5, `adopt_prepqc` (a `δ` step): a correct validator holds the
certificate.** The lock-view guard lapses only by the adoption
(`local_prepqc_of_guard_lapsed`). -/
theorem within_local_prepqc (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {W : view} {e : value}
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hqc : (r.at' N).msg_prepqc W e = true) (hacc : (r.at' N).accepted i W e = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → ¬ (r.at' n).abandoned i = true ∧
      InView (r.at' n) i W ∧ ¬ (r.at' n).timed_out i W = true) :
    r.WithinFrom N B (fun s => s.local_prepqc i W e = true) := by
  refine r.withinFrom_of_boundedFair (hbj (.adopt_prepqc i W e) .loc rfl)
    (ref_add_le hgst hB) (fun _ _ h => adopt_prepqc_effect h) ?_
  intro n hn hclk hnot
  obtain ⟨hab, hview, hnto⟩ := hwin n hn hclk
  have hqc' := r.mono (P := fun s => s.msg_prepqc W e = true)
    (fun m hm => Mvba.msg_prepqc.mono (r.steps m) W e hm) hqc n hn
  refine enabled_adopt_prepqc hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ hab hview hqc'
    (r.mono (P := fun s => s.accepted i W e = true)
      (fun m hm => Mvba.accepted.mono (r.steps m) i W e hm) hacc n hn) ?_ hnto
  by_contra hlapse
  exact hnot (local_prepqc_of_guard_lapsed (r.reachable n) hi hview hqc' hlapse)

/-- **Link 6, `send_commit` (a `δ` step): a correct validator sends its
`Commit`.** `¬ commit_sent` lapses only by the `Commit` being on the network
(`commit_sent_backed`). -/
theorem within_msg_commit (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {W : view} {e : value}
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hacc : (r.at' N).accepted i W e = true) (hloc : (r.at' N).local_prepqc i W e = true)
    (hav : (r.at' N).avail_ready i e = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → ¬ (r.at' n).abandoned i = true ∧
      InView (r.at' n) i W ∧ ¬ (r.at' n).timed_out i W = true) :
    r.WithinFrom N B (fun s => s.msg_commit i W e = true) := by
  refine r.withinFrom_of_boundedFair (hbj (.send_commit i W e) .loc rfl)
    (ref_add_le hgst hB) (fun _ _ h => (send_commit_effect h).2) ?_
  intro n hn hclk hnot
  obtain ⟨hab, hview, hnto⟩ := hwin n hn hclk
  have hacc' := r.mono (P := fun s => s.accepted i W e = true)
    (fun m hm => Mvba.accepted.mono (r.steps m) i W e hm) hacc n hn
  exact enabled_send_commit hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ hab hview hacc'
    (r.mono (P := fun s => s.local_prepqc i W e = true)
      (fun m hm => Mvba.local_prepqc.mono (r.steps m) i W e hm) hloc n hn) hnto
    (fun hcs => hnot (Mvba.reachable_commit_sent_backed (r.reachable n) i W e hi hcs hacc'))
    (r.mono (P := fun s => s.avail_ready i e = true)
      (fun m hm => Mvba.avail_ready.mono (r.steps m) i e hm) hav n hn)

/-- **Link 7, `form_commitqc` (a `Δ` hop): the commit certificate forms.** -/
theorem within_commitqc (hbj : BoundedJustice sch r)
    {W : view} {e : value} {q : nodeset} (hsm : nset.supermajority q)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.Δ ≤ B)
    (hall : ∀ p, nset.member p q = true → (r.at' N).msg_commit p W e = true) :
    r.WithinFrom N B (fun s => s.msg_commitqc W e = true) := by
  refine r.withinFrom_of_boundedFair (hbj (.form_commitqc W e q) .net rfl)
    (ref_add_le hgst hB) (fun _ _ h => form_commitqc_effect h) ?_
  intro n hn _ _
  exact enabled_form_commitqc hsm (fun p hp => r.mono (P := fun s => s.msg_commit p W e = true)
    (fun m hm => Mvba.msg_commit.mono (r.steps m) p W e hm) (hall p hp) n hn)

/-- **Link 8, `decide` (a `δ` step): a correct validator decides.** Needs no
view guard, so no prefix fact: only `¬ abandoned` on the window, and
`∀ E, ¬ decided` lapses only by the decision. -/
theorem within_decided (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {W : view} {e : value}
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hqc : (r.at' N).msg_commitqc W e = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → ¬ (r.at' n).abandoned i = true) :
    r.WithinFrom N B (fun s => ∃ E, s.decided i E = true) := by
  refine r.withinFrom_of_boundedFair (hbj (.decide i W e) .loc rfl)
    (ref_add_le hgst hB) (fun _ _ h => ⟨e, decide_effect h⟩) ?_
  intro n hn hclk hnot
  exact enabled_decide hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ (hwin n hn hclk)
    (r.mono (P := fun s => s.msg_commitqc W e = true)
      (fun m hm => Mvba.msg_commitqc.mono (r.steps m) W e hm) hqc n hn)
    (fun E hE => hnot ⟨E, hE⟩)

end Links

/-! ## The good view decides within `Lcert + δ` -/

section GoodView

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time]

/-- **The good-view lemma** (`docs/Bounds.md` §6.2.6, the second table).
Let `W` be a view above the first with a correct leader `L` and a budget
`τ W` above the chain's latency, and `N₀` the first index at which a correct
validator has entered `W`, its clock `E₀ := clk N₀` at or after GST. If every
correct validator has proposed by `N₀` and none is abandoned at a clock at
or before `E₀ + Lcert + δ`, then under the three clauses a commit certificate
of `W` exists by `E₀ + Lcert` and every correct validator has decided by
`E₀ + Lcert + δ`.

The milestones, each one timed link (the `≤` are clock bounds, `t₃` the
acceptance deadline):

* every correct validator is in `W` — `E₀ + Δ`, `sync_view`, since the
  certificate below `W` is there at `N₀` and nobody is above `W`;
* the leader's `Pre-Prepare` — `+ δ`;
* the honest quorum has accepted and prepared — `+ Δ` (`t₃`);
* the prepare certificate — `+ Δ`;
* each member holds it — `+ δ`, and has its shares by `t₃ + Δsync`
  ((Δ-avail)); both by `t₃ + max (Δ + δ) Δsync`;
* each member's `Commit` — `+ δ`;
* the commit certificate — `+ Δ`, which is `E₀ + Lcert`;
* every correct validator decided — `+ δ`.

The quorum steps collapse a family of per-member deadlines into one index by
`TLRun.withinFrom_forall` over the honest quorum's member list. -/
theorem good_view_decides
    (enum : ByzNodeSetEnum node nodeset nset)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    {sch : Schedule view time} {r : TMvbaRun th time} (hsync : Sync sch r)
    {PV W : view} {L : node} (hnext : vord.next PV W)
    (hlead : th.leader W L = true) (hL : ¬ nset.is_byz L = true)
    (hramp : Lcert sch.Δ sch.δ sch.Δsync < sch.τ W)
    {N₀ : Nat} {i₀ : node} (hi₀ : ¬ nset.is_byz i₀ = true)
    (hent₀ : (r.at' N₀).entered i₀ W = true)
    (hfirst : ∀ (n : Nat) (j : node), ¬ nset.is_byz j = true →
      (r.at' n).entered j W = true → N₀ ≤ n)
    (hgst : r.gst ≤ r.clk N₀)
    (hin : ∀ p, ¬ nset.is_byz p = true → ∃ E, (r.at' N₀).input p E = true)
    (hnab : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true →
      r.clk n ≤ r.clk N₀ + Lcert sch.Δ sch.δ sch.Δsync + sch.δ →
        ¬ (r.at' n).abandoned p = true) :
    ∃ e : value,
      r.WithinFrom N₀ (r.clk N₀ + Lcert sch.Δ sch.δ sch.Δsync)
        (fun s => s.msg_commitqc W e = true) ∧
      ∀ q, ¬ nset.is_byz q = true →
        r.WithinFrom N₀ (r.clk N₀ + Lcert sch.Δ sch.δ sch.Δsync + sch.δ)
          (fun s => ∃ E, s.decided q E = true) := by
  obtain ⟨hbj, htp, hav⟩ := hsync
  have hQc := hqe.honestQuorum_correct
  have hQs := hqe.honestQuorum_supermajority
  have hmemQ : ∀ p, p ∈ enum.members hqe.honestQuorum → nset.member p hqe.honestQuorum = true :=
    fun p hp => (enum.mem_members p _).mpr hp
  /- The deadlines, named. -/
  have hΔ : (0 : time) ≤ sch.Δ := le_of_lt sch.Δ_pos
  have hδ : (0 : time) ≤ sch.δ := sch.δ_nonneg
  obtain ⟨t₁, ht₁⟩ : ∃ t, t = r.clk N₀ + sch.Δ := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t, t = t₁ + sch.δ := ⟨_, rfl⟩
  obtain ⟨t₃, ht₃⟩ : ∃ t, t = t₂ + sch.Δ := ⟨_, rfl⟩
  obtain ⟨t₄, ht₄⟩ : ∃ t, t = t₃ + sch.Δ := ⟨_, rfl⟩
  obtain ⟨t₅, ht₅⟩ : ∃ t, t = t₃ + max (sch.Δ + sch.δ) sch.Δsync := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆⟩ : ∃ t, t = t₅ + sch.δ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ t, t = t₆ + sch.Δ := ⟨_, rfl⟩
  /- `T` is `E₀ + Lcert`: the milestone table sums to the constant. -/
  have hTL : r.clk N₀ + Lcert sch.Δ sch.δ sch.Δsync = T := by
    subst hT ht₆ ht₅ ht₃ ht₂ ht₁
    simp only [Lcert]
    abel
  have h₁₂ : t₁ ≤ t₂ := ht₂ ▸ le_add_of_nonneg_right hδ
  have h₂₃ : t₂ ≤ t₃ := ht₃ ▸ le_add_of_nonneg_right hΔ
  have h₄₅ : t₄ + sch.δ ≤ t₅ := by
    rw [ht₄, ht₅, add_assoc]; exact add_le_add le_rfl (le_max_left _ _)
  have h₃₅' : t₃ + sch.Δsync ≤ t₅ := by
    rw [ht₅]; exact add_le_add le_rfl (le_max_right _ _)
  have h₄₅' : t₄ ≤ t₅ := le_trans (le_add_of_nonneg_right hδ) h₄₅
  have h₃₄ : t₃ ≤ t₄ := ht₄ ▸ le_add_of_nonneg_right hΔ
  have h₅₆ : t₅ ≤ t₆ := ht₆ ▸ le_add_of_nonneg_right hδ
  have h₆T : t₆ ≤ T := hT ▸ le_add_of_nonneg_right hΔ
  have h₅T : t₅ ≤ T := le_trans h₅₆ h₆T
  have h₃T : t₃ ≤ T := le_trans (le_trans h₃₄ h₄₅') h₅T
  have h₂T : t₂ ≤ T := le_trans h₂₃ h₃T
  have h₁T : t₁ ≤ T := le_trans h₁₂ h₂T
  have hE₁ : r.clk N₀ ≤ t₁ := ht₁ ▸ le_add_of_nonneg_right hΔ
  /- The prefix: before `E₀ + τ W`, and `T` is before it. -/
  have hTτ : T < r.clk N₀ + sch.τ W := hTL ▸ add_lt_add_of_le_of_lt le_rfl hramp
  have hnto : ∀ (i : node) (n : Nat), ¬ nset.is_byz i = true → r.clk n ≤ T →
      ¬ (r.at' n).timed_out i W = true := fun i n hi h =>
    not_timed_out_before_budget htp hfirst hi (lt_of_le_of_lt h hTτ)
  have hbound : ∀ (n : Nat), r.clk n ≤ T → ∀ (j : node) (V : view),
      ¬ nset.is_byz j = true → (r.at' n).entered j V = true → vord.le V W :=
    fun n h => entered_le_before_budget htp hfirst (lt_of_le_of_lt h hTτ)
  have hnab' : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true → r.clk n ≤ T →
      ¬ (r.at' n).abandoned p = true := fun p n hp h =>
    hnab p n hp (hTL ▸ le_trans h (le_add_of_nonneg_right hδ))
  /- Settled in `W` on the prefix, once entered. -/
  have hset : ∀ (p : node), ¬ nset.is_byz p = true → ∀ N, (r.at' N).entered p W = true →
      ∀ n, N ≤ n → r.clk n ≤ T → ¬ (r.at' n).abandoned p = true ∧
        InView (r.at' n) p W ∧ ¬ (r.at' n).timed_out p W = true :=
    fun p hp N hN n hn h =>
      ⟨hnab' p n hp h,
       ⟨r.mono (P := fun s => s.entered p W = true)
          (fun m hm => Mvba.entered.mono (r.steps m) p W hm) hN n hn,
        fun V hV => hbound n h p V hp hV⟩,
       hnto p n hp h⟩
  have hgstN : ∀ n, N₀ ≤ n → r.gst ≤ r.clk n := fun n hn =>
    le_trans hgst (r.clk_le_of_le hn)
  have hinN : ∀ p, ¬ nset.is_byz p = true → ∀ n, N₀ ≤ n → ∃ E, (r.at' n).input p E = true :=
    fun p hp n hn =>
      let ⟨E, hE⟩ := hin p hp
      ⟨E, r.mono (P := fun s => s.input p E = true)
        (fun m hm => Mvba.input.mono (r.steps m) p E hm) hE n hn⟩
  have htc : (r.at' N₀).msg_tc PV = true := msg_tc_below_of_entered r.toLRun hi₀ hnext hent₀
  /- (1) The leader and the honest quorum are in `W` by `t₁`. -/
  obtain ⟨N₁, hN₁, hc₁, hall₁⟩ :=
    r.withinFrom_forall (fun p s => s.entered p W = true)
      (fun p m hm => Mvba.entered.mono (r.steps m) p W hm) N₀ t₁ hE₁
      (L :: enum.members hqe.honestQuorum) (fun p hp => by
        have hpc : ¬ nset.is_byz p = true := by
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact hL
          · exact hQc p (hmemQ p hp')
        obtain ⟨E, hE⟩ := hin p hpc
        exact within_entered_of_tc hbj hpc hnext hgst (le_of_eq ht₁.symm) hE htc
          (fun n _ h => ⟨hnab' p n hpc (le_trans h h₁T),
            fun V hV => hbound n (le_trans h h₁T) p V hpc hV⟩))
  have hLent : (r.at' N₁).entered L W = true := hall₁ L (by simp)
  have hQent : ∀ p, nset.member p hqe.honestQuorum = true → (r.at' N₁).entered p W = true :=
    fun p hp => hall₁ p (List.mem_cons_of_mem _ ((enum.mem_members p _).mp hp))
  /- (2) The leader's `Pre-Prepare` by `t₂`. -/
  have hjust₁ : (∃ w e, (r.at' N₁).tc_lock PV w e = true) ∨ (r.at' N₁).tc_nolock PV = true := by
    rcases Mvba.reachable_msg_tc_backed (r.reachable N₀) PV htc with hnl | ⟨w, e, hw⟩
    · exact Or.inr (r.mono (P := fun s => s.tc_nolock PV = true)
        (fun m hm => Mvba.tc_nolock.mono (r.steps m) PV hm) hnl N₁ hN₁)
    · exact Or.inl ⟨w, e, r.mono (P := fun s => s.tc_lock PV w e = true)
        (fun m hm => Mvba.tc_lock.mono (r.steps m) PV w e hm) hw N₁ hN₁⟩
  obtain ⟨EL, hEL⟩ := hinN L hL N₁ hN₁
  obtain ⟨n₂, hn₂, hc₂, e, hpp⟩ :=
    within_preprepare_of_leader hbj hL hnext hlead (hgstN N₁ hN₁)
      (ht₂ ▸ add_le_add hc₁ le_rfl) hEL hjust₁
      (fun n hn h =>
        let hs := hset L hL N₁ hLent n hn (le_trans h h₂T)
        ⟨hs.1, hs.2.1⟩)
  have hN₂ : N₀ ≤ n₂ := Nat.le_trans hN₁ hn₂
  have hvalid : th.valid e = true :=
    Mvba.reachable_honest_preprepare_valid (r.reachable n₂) L W e hL hpp
  have hjust₂ := Mvba.reachable_honest_preprepare_justified (r.reachable n₂) L W e PV hL hpp hnext
  /- (3) The honest quorum has accepted by `t₃`. -/
  obtain ⟨N₃, hN₃, hc₃, hall₃⟩ :=
    r.withinFrom_forall (fun p s => s.accepted p W e = true)
      (fun p m hm => Mvba.accepted.mono (r.steps m) p W e hm) n₂ t₃ (le_trans hc₂ h₂₃)
      (enum.members hqe.honestQuorum) (fun p hp => by
        have hpq := hmemQ p hp
        obtain ⟨E, hE⟩ := hinN p (hQc p hpq) n₂ hN₂
        exact within_accepted hbj (hQc p hpq) hL hnext hlead hvalid (hgstN n₂ hN₂)
          (ht₃ ▸ add_le_add hc₂ le_rfl) hE hpp hjust₂
          (fun n hn h => hset p (hQc p hpq) N₁ (hQent p hpq) n (Nat.le_trans hn₂ hn)
            (le_trans h h₃T)))
  have hN₃' : N₀ ≤ N₃ := Nat.le_trans hN₂ hN₃
  have hacc₃ : ∀ p, nset.member p hqe.honestQuorum = true → (r.at' N₃).accepted p W e = true :=
    fun p hp => hall₃ p ((enum.mem_members p _).mp hp)
  /- (4) The prepare certificate by `t₄`. -/
  obtain ⟨n₄, hn₄, hc₄, hqc⟩ :=
    within_prepqc hbj hQs (hgstN N₃ hN₃') (ht₄ ▸ add_le_add hc₃ le_rfl)
      (fun p hp => Mvba.reachable_accepted_implies_prepare (r.reachable N₃) p W e (hQc p hp)
        (hacc₃ p hp))
  have hN₄ : N₀ ≤ n₄ := Nat.le_trans hN₃' hn₄
  /- (5)–(6) Each member adopts, has its shares, and commits by `t₆`. -/
  obtain ⟨N₆, hN₆, hc₆, hall₆⟩ :=
    r.withinFrom_forall (fun p s => s.msg_commit p W e = true)
      (fun p m hm => Mvba.msg_commit.mono (r.steps m) p W e hm) n₄ t₆
      (le_trans hc₄ (le_trans h₄₅' h₅₆))
      (enum.members hqe.honestQuorum) (fun p hp => by
        have hpq := hmemQ p hp
        have hpc := hQc p hpq
        have hwin : ∀ n, N₃ ≤ n → r.clk n ≤ T → ¬ (r.at' n).abandoned p = true ∧
            InView (r.at' n) p W ∧ ¬ (r.at' n).timed_out p W = true :=
          fun n hn h => hset p hpc N₁ (hQent p hpq) n (Nat.le_trans (Nat.le_trans hn₂ hN₃) hn) h
        obtain ⟨E, hE⟩ := hinN p hpc n₄ hN₄
        -- Adoption, from the certificate.
        obtain ⟨a, ha, hca, hloc⟩ :=
          within_local_prepqc hbj hpc (hgstN n₄ hN₄) (le_trans (add_le_add hc₄ le_rfl) h₄₅)
            hE hqc
            (r.mono (P := fun s => s.accepted p W e = true)
              (fun m hm => Mvba.accepted.mono (r.steps m) p W e hm) (hacc₃ p hpq) n₄ hn₄)
            (fun n hn h => hwin n (Nat.le_trans hn₄ hn) (le_trans h h₅T))
        -- The shares, from the acceptance.
        obtain ⟨b, hb, hsh, hcb⟩ := hav N₃ p W e hpc (hacc₃ p hpq)
        have hcb' : r.clk b ≤ t₅ := by
          rw [r.ref_eq_of_gst_le (hgstN N₃ hN₃')] at hcb
          exact le_trans hcb (le_trans (add_le_add hc₃ le_rfl) h₃₅')
        -- Both, at the later of the two.
        have hc : r.clk (max a b) ≤ t₅ := r.clk_max_le hca hcb'
        have hNc : n₄ ≤ max a b := Nat.le_trans ha (Nat.le_max_left _ _)
        obtain ⟨c, hc', hcc, hcm⟩ :=
          within_msg_commit hbj hpc (hgstN _ (Nat.le_trans hN₄ hNc))
            (ht₆ ▸ add_le_add hc le_rfl)
            (r.mono (P := fun s => s.input p E = true)
              (fun m hm => Mvba.input.mono (r.steps m) p E hm) hE _ hNc)
            (r.mono (P := fun s => s.accepted p W e = true)
              (fun m hm => Mvba.accepted.mono (r.steps m) p W e hm) (hacc₃ p hpq) _
              (Nat.le_trans hn₄ hNc))
            (r.mono (P := fun s => s.local_prepqc p W e = true)
              (fun m hm => Mvba.local_prepqc.mono (r.steps m) p W e hm) hloc _
              (Nat.le_max_left _ _))
            (r.mono (P := fun s => s.avail_ready p e = true)
              (fun m hm => Mvba.avail_ready.mono (r.steps m) p e hm) hsh _
              (Nat.le_max_right _ _))
            (fun n hn h => hwin n (Nat.le_trans (Nat.le_trans hn₄ hNc) hn) (le_trans h h₆T))
        exact ⟨c, Nat.le_trans hNc hc', hcc, hcm⟩)
  have hN₆' : N₀ ≤ N₆ := Nat.le_trans hN₄ hN₆
  /- (7) The commit certificate by `T = E₀ + Lcert`. -/
  obtain ⟨n₇, hn₇, hc₇, hcqc⟩ :=
    within_commitqc hbj hQs (hgstN N₆ hN₆') (hT ▸ add_le_add hc₆ le_rfl)
      (fun p hp => hall₆ p ((enum.mem_members p _).mp hp))
  have hN₇ : N₀ ≤ n₇ := Nat.le_trans hN₆' hn₇
  refine ⟨e, ⟨n₇, hN₇, hTL ▸ hc₇, hcqc⟩, fun q hq => ?_⟩
  /- (8) Every correct validator decides by `T + δ`. -/
  obtain ⟨E, hE⟩ := hinN q hq n₇ hN₇
  obtain ⟨n₈, hn₈, hc₈, hdec⟩ :=
    within_decided hbj hq (hgstN n₇ hN₇) (add_le_add hc₇ le_rfl) hE hcqc
      (fun n _ h => hnab q n hq (hTL ▸ h))
  exact ⟨n₈, Nat.le_trans hN₇ hn₈, hTL ▸ hc₈, hdec⟩

end GoodView

end Mvba

/-! ## The pinned trust base

The good-view lemma and the facts it rests on; the standard trio. -/

/--
info: 'Mvba.good_view_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.good_view_decides

/--
info: 'Mvba.timer_set_label' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.timer_set_label

/--
info: 'Mvba.entered_le_of_no_timeout_before' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.entered_le_of_no_timeout_before

/--
info: 'Mvba.not_timed_out_before_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.not_timed_out_before_budget
