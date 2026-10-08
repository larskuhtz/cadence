import Cadence.Mvba.Schedule
import Mathlib.Tactic.Abel

/-! # Mvba.Bound — the good-view lemma

[Bounds.md](../../docs/Bounds.md) §6.2. The second of the two lemmas §6.2.6
derives, proven: **a correct-led view whose budget clears the
chain's latency decides within that latency.** From the first index at which
a correct validator has entered such a view `W`, at a clock `E₀` at or after
GST, with every correct validator having proposed and none abandoned inside
the window, a commit certificate of `W` exists by `E₀ + Lcert` and every
correct validator has decided by `E₀ + Lcert + Δ` (`good_view_decides`):
the decision is a network hop, since a validator that did not form the
certificate obtains it by transfer. The lemma also takes the one-view
retention at `E₀`: every correct validator had reached `W − 1` there.
Every message the chain waits for is sent from inside `W`, so after `E₀`,
and each network clause's conditions — sent at or after GST by correct
validators, retained — follow from that and from the provenance facts
below.

The premises are the three clauses of [Schedule.lean](Schedule.lean) and
nothing else: no
fairness of the untimed kind, no (A-viewsync), no statement about the timer
beyond (T1). The two instance hypotheses are the quorum classes the untimed
chain already takes.

## How it is built

The untimed chain of [Liveness.lean](Liveness.lean) is re-run with "within
`D`" in place of "eventually". Each of its links was `enabled_<action>` (guards ⇒
enabledness) + one weak-fairness step + `<action>_effect`; each link here
keeps the first and the third and replaces the second by one application of
`BoundedFair` through `TLRun.withinFrom_of_boundedFair` below.

The anti-monotone guards are handled exactly as the untimed links handle
them — a lapse of `¬ proposed_in`, `∀ W, voted i W → W < v`, the lock-view
bound, `¬ commit_sent` or `∀ E, ¬ decided` *is* the goal, by the same
invariants — except `in_view`, `¬ timed_out` and being active (`Active`:
neither abandoned nor halted after deciding), which the untimed chain
assumed (`SettledIn`) and which here hold on a **prefix** of the run rather
than for ever:

* `¬ timed_out i W` below the clock `E₀ + τ W`: (T1) says the timer fires
  no earlier than `τ W` after an entry, every correct entry is at or after
  `E₀`, and a validator that has timed out had its timer fire first
  (`not_timed_out_before_budget`);
* `in_view i W` on the same prefix: `entered_le_of_no_timeout_before`, the
  prefix form of `Mvba.entered_le_of_no_timeout` — no correct validator is
  above `W` while none has timed out in it;
* `¬ abandoned` inside the window: the caller's premise, as in the claim;
  and "not yet decided" up to the certificate: a hypothesis of
  `good_view_decides`, which `bounded_termination` supplies in the branch
  where no correct validator has decided early (in the other branch a
  certificate already exists, and the decide link finishes alone).

`τ W > Lcert` makes the chain's window lie inside that prefix, which is the
whole role of (S-ramp) here.

## One requirement on the time theory

The lemma takes `[IsOrderedCancelAddMonoid time]`, where
[Schedule.lean](Schedule.lean) takes `IsOrderedAddMonoid`. The step that needs it is "`Lcert < τ W`, hence
`E₀ + Lcert < E₀ + τ W`": without cancellation it fails — in `ℕ∞` a clock
reading `⊤` makes both sides `⊤`, a correct `W`-timer may fire inside the
window, and a validator that times out in `W` stops the chain. `ℕ`, `ℚ≥0`
and `ℝ≥0` are cancellative; [Bounds.md](../../docs/Bounds.md) §6.2.8 has
the counterexample.

## The state facts proven here

Five facts [Liveness.lean](Liveness.lean) does not provide are proven here
from Veil's generated lemmas and the `reachable_*` projections: the
`timer_expired` flag is set only by `expire_timer` (`timer_set_label`, from
the per-action frame lemmas), the prefix form of `entered_le_of_no_timeout`,
the timeout certificate below a view present *at* the first entry into
it rather than at some index (`msg_tc_below_of_entered`), and two
provenance facts the network clauses need: a correct leader's `Pre-Prepare`
of `V` is sent from inside `V` (`honest_preprepare_entered`), and a correct
validator that voted in `W` has reached `W` (`entered_ge_of_voted`). -/

/-! ## Two generic facts about bounded fairness -/

namespace Cadence

open Veil

section

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {time : Type} [LinearOrder time]

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
application of bounded fairness.

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
  · obtain ⟨n, hn, hclk, hne⟩ := exists_not_enabled_of_not_firesWithin hbf hf
    by_cases hP : P (r.at' n)
    · exact ⟨n, hn, le_trans hclk hB, hP⟩
    · exact absurd (hen n hn (le_trans hclk hB) hP) hne

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

/-- Expose an action's transition body in `h` — the local tactic of the
same name in [Liveness.lean](Liveness.lean), repeated because it is local
there. -/
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

/-! ## State facts [Liveness.lean](Liveness.lean) does not provide -/

section Local

variable {node nodeset value evec view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited evec] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value evec view}
  {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)}

/-- `expire_timer i' v'` sets the marker of `(i', v')` and no other. -/
theorem expire_timer_sets {i i' : node} {v v' : view}
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st
      (.expire_timer i' v') st')
    (h0 : ¬ st.timer_expired i v = true) (h1 : st'.timer_expired i v = true) :
    i' = i ∧ v' = v := by
  mvba_tr htr
  obtain ⟨-, -, rfl⟩ := htr
  mvba_effect_at h1
  exact h1.resolve_right h0

/-- **Only the timer sets the timer.** A step that turns `timer_expired i v`
on is `expire_timer i v`. Every other action leaves the relation untouched,
which is Veil's generated frame lemma for that action; the case split is over
the model's own label type, so an added action is a missing case, not a
silent gap. -/
theorem timer_set_label {l : Mvba.Label node nodeset value evec view} {i : node} {v : view}
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
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
  case byz_form_prepqc => rw [Mvba.byz_form_prepqc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case adopt_prepqc => rw [Mvba.adopt_prepqc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case become_avail_ready =>
    rw [Mvba.become_avail_ready.frame_timer_expired htr] at h1; exact absurd h1 h0
  case send_commit => rw [Mvba.send_commit.frame_timer_expired htr] at h1; exact absurd h1 h0
  case byz_form_commitqc =>
    rw [Mvba.byz_form_commitqc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case decide => rw [Mvba.decide.frame_timer_expired htr] at h1; exact absurd h1 h0
  case timeout_qc => rw [Mvba.timeout_qc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case timeout_noqc => rw [Mvba.timeout_noqc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case byz_form_tc_lock => rw [Mvba.byz_form_tc_lock.frame_timer_expired htr] at h1; exact absurd h1 h0
  case byz_form_tc_nolock =>
    rw [Mvba.byz_form_tc_nolock.frame_timer_expired htr] at h1; exact absurd h1 h0
  case form_own_commitqc =>
    rw [Mvba.form_own_commitqc.frame_timer_expired htr] at h1; exact absurd h1 h0
  case form_own_tc_lock =>
    rw [Mvba.form_own_tc_lock.frame_timer_expired htr] at h1; exact absurd h1 h0
  case form_own_tc_nolock =>
    rw [Mvba.form_own_tc_nolock.frame_timer_expired htr] at h1; exact absurd h1 h0
  case sync_view_nolock => rw [Mvba.sync_view_nolock.frame_timer_expired htr] at h1; exact absurd h1 h0
  case sync_view_lock => rw [Mvba.sync_view_lock.frame_timer_expired htr] at h1; exact absurd h1 h0
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
`timer_expired` is empty initially (Veil's generated `init` lemma), so a least index
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
      j V ⟨hj, hprev, hV⟩ with rfl | ⟨PV, S, hnext, hcert⟩
    · exact vord.zero_lt W
    have hto : ∃ R, ¬ nset.is_byz R = true ∧ (r.at' n).timed_out R PV = true := by
      rcases hcert with hnl | ⟨Wc, Ec, hlock⟩
      · exact exists_honest_timed_out_of_tc_nolock (r.reachable n) hnl
      · exact exists_honest_timed_out_of_tc_lock (r.reachable n) hlock
    obtain ⟨R, hR, hRto⟩ := hto
    have hPV : vord.le PV W :=
      ih hn R PV hR (Mvba.reachable_timed_out_entered (r.reachable n) R PV hR hRto)
    have hPVne : ¬ PV = W := by
      rintro rfl
      exact hvs R n hK hR hRto
    exact ((vord.next_def PV V).mp hnext).2 W ((vord.le_lt PV W).mpr ⟨hPV, hPVne⟩)

/-- **The certificate below a view is there at any index where a correct
validator has entered the view**, sent by that validator: it forwarded the
certificate it advanced on (`exists_tc_below_of_entered`). -/
theorem msg_tc_below_of_entered (r : MvbaRun th) {i : node} (hi : ¬ nset.is_byz i = true)
    {pv W : view} (hnext : vord.next pv W) {N : Nat}
    (hent : (r.at' N).entered i W = true) : (r.at' N).msg_tc i pv = true :=
  exists_tc_below_of_entered r hi hnext hent

/-- **An honest `Pre-Prepare` is sent from inside its view**, one step: a
step that turns `msg_preprepare L V e` on for a correct `L` is one of the
three leader actions, each guarded on `in_view L V`. Every other action
leaves the relation untouched (Veil's generated frame lemmas), and
`byz_preprepare` requires a Byzantine sender. -/
theorem preprepare_set_entered {l : Mvba.Label node nodeset value evec view} {L : node} {V : view}
    {e : value} (hL : ¬ nset.is_byz L = true)
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (h0 : ¬ st.msg_preprepare L V e = true) (h1 : st'.msg_preprepare L V e = true) :
    st.entered L V = true := by
  cases l
  case leader_propose_first l' e' =>
    mvba_tr htr
    obtain ⟨-, -, -, -, hent, -, -, -, rfl⟩ := htr
    mvba_effect_at h1
    rcases h1 with ⟨rfl, rfl, rfl⟩ | h1
    · exact hent
    · exact absurd h1 h0
  case leader_repropose l' pv' v' w' e' =>
    mvba_tr htr
    obtain ⟨-, -, -, -, -, -, hent, -, -, -, -, rfl⟩ := htr
    mvba_effect_at h1
    rcases h1 with ⟨rfl, rfl, rfl⟩ | h1
    · exact hent
    · exact absurd h1 h0
  case leader_propose_fresh l' pv' v' e' =>
    mvba_tr htr
    obtain ⟨-, -, -, -, -, hent, -, -, -, -, rfl⟩ := htr
    mvba_effect_at h1
    rcases h1 with ⟨rfl, rfl, rfl⟩ | h1
    · exact hent
    · exact absurd h1 h0
  case byz_preprepare l' v' e' =>
    mvba_tr htr
    obtain ⟨hbyz, rfl⟩ := htr
    mvba_effect_at h1
    rcases h1 with ⟨rfl, rfl, rfl⟩ | h1
    · exact absurd hbyz hL
    · exact absurd h1 h0
  case propose =>
    rw [Mvba.propose.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case abandon =>
    rw [Mvba.abandon.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case handle_preprepare_first =>
    rw [Mvba.handle_preprepare_first.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case handle_preprepare =>
    rw [Mvba.handle_preprepare.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case byz_form_prepqc =>
    rw [Mvba.byz_form_prepqc.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case adopt_prepqc =>
    rw [Mvba.adopt_prepqc.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case expire_timer =>
    rw [Mvba.expire_timer.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case become_avail_ready =>
    rw [Mvba.become_avail_ready.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case send_commit =>
    rw [Mvba.send_commit.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case byz_form_commitqc =>
    rw [Mvba.byz_form_commitqc.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case decide =>
    rw [Mvba.decide.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case timeout_qc =>
    rw [Mvba.timeout_qc.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case timeout_noqc =>
    rw [Mvba.timeout_noqc.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case byz_form_tc_lock =>
    rw [Mvba.byz_form_tc_lock.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case byz_form_tc_nolock =>
    rw [Mvba.byz_form_tc_nolock.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case form_own_commitqc =>
    rw [Mvba.form_own_commitqc.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case form_own_tc_lock =>
    rw [Mvba.form_own_tc_lock.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case form_own_tc_nolock =>
    rw [Mvba.form_own_tc_nolock.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case sync_view_nolock =>
    rw [Mvba.sync_view_nolock.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case sync_view_lock =>
    rw [Mvba.sync_view_lock.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case sync_view_adopt =>
    rw [Mvba.sync_view_adopt.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case byz_prepare =>
    rw [Mvba.byz_prepare.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case byz_commit =>
    rw [Mvba.byz_commit.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case byz_timeout_qc =>
    rw [Mvba.byz_timeout_qc.frame_msg_preprepare htr] at h1; exact absurd h1 h0
  case byz_timeout_noqc =>
    rw [Mvba.byz_timeout_noqc.frame_msg_preprepare htr] at h1; exact absurd h1 h0

/-- **… so a correct leader has entered the view of every `Pre-Prepare` it
has sent**, at every index. The relation is empty initially (Veil's
generated `init` lemma), and the step that sets it is a leader action. -/
theorem honest_preprepare_entered (r : MvbaRun th) {L : node} (hL : ¬ nset.is_byz L = true)
    {V : view} {e : value} :
    ∀ n, (r.at' n).msg_preprepare L V e = true → (r.at' n).entered L V = true := by
  intro n
  induction n with
  | zero => intro h; simp [Mvba.msg_preprepare.init r.starts L V e] at h
  | succ n ih =>
    intro h
    by_cases h0 : (r.at' n).msg_preprepare L V e = true
    · exact Mvba.entered.mono (r.steps n) L V (ih h0)
    · exact Mvba.entered.mono (r.steps n) L V (preprepare_set_entered hL (r.steps n) h0 h)

/-- **A correct validator that voted in a view above the first has reached
it.** `voted_within_entered` bounds a vote by every bound on the entries, so
if every view `i` has entered were below `W`, the view before `W` would
bound them and the vote. -/
theorem entered_ge_of_voted (r : MvbaRun th) {i : node} (hi : ¬ nset.is_byz i = true)
    {PV W : view} (hnext : vord.next PV W) {n : Nat} (hv : (r.at' n).voted i W = true) :
    ∃ V, vord.le W V ∧ (r.at' n).entered i V = true := by
  by_contra hno
  push Not at hno
  have hbound : ∀ V, (r.at' n).entered i V = true → vord.le V PV := by
    intro V hV
    rcases vord.le_total V PV with h | h
    · exact h
    · by_cases hVeq : V = PV
      · exact hVeq ▸ vord.le_refl _
      · exact absurd (((vord.next_def PV W).mp hnext).2 V ((vord.le_lt PV V).mpr ⟨h, fun h' => hVeq h'.symm⟩)) (hno V · hV)
  have hWPV := Mvba.reachable_voted_within_entered (r.reachable n) i W PV hi hv hbound
  exact ((vord.le_lt PV W).mp ((vord.next_def PV W).mp hnext).1).2
    (vord.le_antisymm _ _ ((vord.le_lt PV W).mp ((vord.next_def PV W).mp hnext).1).1 hWPV)

end Local

/-! ## The prefix on which the good view is safe from its timer -/

section Prefix

variable {node nodeset value evec view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited evec] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value evec view}
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

Each is its untimed twin in [Liveness.lean](Liveness.lean) with the weak-fairness step
replaced by one (Δ-justice) clause, through `withinFrom_of_boundedFair` (a
local step) or `withinFrom_of_boundedFairWhile` (a network step): the
monotone guards are given at the starting index `N` and carried by the
generated `<relation>.mono` lemmas, the anti-monotone guards the untimed
link assumed (`SettledIn`) are given on the window `clk n ≤ B`, and the
anti-monotone guard whose lapse is the goal is discharged by the same
invariant the untimed link uses. A network link also takes the conditions
of its clause: that its messages were sent at or after GST and retained,
and that every correct validator takes part on the window. `hgst` puts the
window's reference time at `clk N`, which is where every link of the good
view starts. -/

section Links

variable {node nodeset value evec view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited evec] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value evec view}
  {time : Type} [LinearOrder time] [AddCommMonoid time]
  {sch : Schedule view time} {r : TMvbaRun th time}

/-- **One timed link, for a network clause.** `withinFrom_of_boundedFair`
for `BoundedFairWhile`: the clause's window condition `C` is owed wherever
the goal does not yet hold. -/
theorem withinFrom_of_boundedFairWhile {D : time} {l : Mvba.Label node nodeset value evec view}
    {C : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view) → Prop}
    (hbf : BoundedFairWhile r D l C) {N : Nat} {B : time} (hB : r.ref N + D ≤ B)
    {P : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view) → Prop}
    (heff : ∀ st st', (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st' →
      P st')
    (hen : ∀ n, N ≤ n → r.clk n ≤ B → ¬ P (r.at' n) →
      Enabled (Mvba.relationalTransitionSystem node nodeset value evec view) th (r.at' n) l ∧
        C (r.at' n)) :
    r.WithinFrom N B P := by
  by_cases hf : r.FiresWithin N D l
  · obtain ⟨n, hn, hl, hclk⟩ := hf
    exact ⟨n + 1, Nat.le_succ_of_le hn, le_trans hclk hB, heff _ _ (hl ▸ r.steps n)⟩
  · have hex : ∃ n, N ≤ n ∧ r.clk n ≤ r.ref N + D ∧
        ¬ (Enabled (Mvba.relationalTransitionSystem node nodeset value evec view) th
          (r.at' n) l ∧ C (r.at' n)) := by
      by_contra hc
      push Not at hc
      exact hf (hbf N (fun n hn hclk => hc n hn hclk))
    obtain ⟨n, hn, hclk, hne⟩ := hex
    by_cases hP : P (r.at' n)
    · exact ⟨n, hn, le_trans hclk hB, hP⟩
    · obtain ⟨hen', hC⟩ := hen n hn (le_trans hclk hB) hP
      exact absurd ⟨hen', hC⟩ hne

/-- The fairness window of a link starting at or after GST is `clk N + D`. -/
theorem ref_add_le {N : Nat} (hgst : r.gst ≤ r.clk N) {D B : time}
    (hB : r.clk N + D ≤ B) : r.ref N + D ≤ B := by
  rw [r.ref_eq_of_gst_le hgst]; exact hB

/-- **Link 1, `sync_view_*` (a forwarded certificate, `Δ`): a correct
validator enters `W`.** A correct validator `s` in `W` forwarded the
certificate below it when it entered (Supplement, Algorithm 1, line 98 (`line:mvba:sv-forward`)), after GST. Its view guard
`∀ V, entered i V → V ≤ PV` lapses only by entering a view above `PV`,
which on the prefix bounded by `W` is `W` itself. -/
theorem within_entered_of_tc (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {PV W : view} (hnext : vord.next PV W)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.Δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    {s : node} (hs : ¬ nset.is_byz s = true)
    (htc : (r.at' N).msg_tc s PV = true)
    (hfwd : SinceGst r (fun t => t.entered s W = true)) (hsW : (r.at' N).entered s W = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n) ∧
      ∀ V, (r.at' n).entered i V = true → vord.le V W) :
    r.WithinFrom N B (fun t => t.entered i W = true) := by
  have hin' : ∀ n, N ≤ n → ∃ E, (r.at' n).input i E = true := fun n hn =>
    ⟨E₀, r.mono (P := fun t => t.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩
  have hsW' : ∀ n, N ≤ n → (r.at' n).entered s W = true :=
    r.mono (P := fun t => t.entered s W = true)
      (fun m hm => Mvba.entered.mono (r.steps m) s W hm) hsW
  have hbelow : ∀ n, N ≤ n → r.clk n ≤ B → ¬ (r.at' n).entered i W = true →
      ∀ V, (r.at' n).entered i V = true → vord.le V PV := by
    intro n hn hclk hnot V hV
    by_contra hnle
    have hWV : vord.le W V := ((vord.next_def PV W).mp hnext).2 V (lt_of_not_le hnle)
    have hVW : V = W := vord.le_antisymm V W ((hwin n hn hclk).2 V hV) hWV
    subst hVW
    exact hnot hV
  rcases Mvba.reachable_msg_tc_backed (r.reachable N) s PV htc with hnl | ⟨w, e, hlk⟩
  · refine withinFrom_of_boundedFairWhile ((hbj.forwarded i s PV W hs hfwd).1)
      (ref_add_le hgst hB) (fun _ _ h => sync_view_nolock_effect h) ?_
    intro n hn hclk hnot
    exact ⟨enabled_sync_view_nolock hi (hin' n hn) ((hwin n hn hclk).1 i hi) hnext
      (r.mono (P := fun t => t.msg_tc_nolock s PV = true)
        (fun m hm => Mvba.msg_tc_nolock.mono (r.steps m) s PV hm) hnl n hn)
      (hbelow n hn hclk hnot), (hwin n hn hclk).1, hsW' n hn⟩
  · refine withinFrom_of_boundedFairWhile ((hbj.forwarded i s PV W hs hfwd).2.1 w e)
      (ref_add_le hgst hB) (fun _ _ h => sync_view_lock_effect h) ?_
    intro n hn hclk hnot
    exact ⟨enabled_sync_view_lock hi (hin' n hn) ((hwin n hn hclk).1 i hi) hnext
      (r.mono (P := fun t => t.msg_tc_lock s PV w e = true)
        (fun m hm => Mvba.msg_tc_lock.mono (r.steps m) s PV w e hm) hlk n hn)
      (hbelow n hn hclk hnot), (hwin n hn hclk).1, hsW' n hn⟩

/-- **Link 2, `leader_repropose` / `leader_propose_fresh` (a `δ` step): the
correct leader proposes.** Which of the two labels applies is fixed by the
certificate below `W` the leader entered on (`ViewTC_L`), as in the untimed
leader link; `¬ proposed_in` lapses only by the proposal
(`proposed_in_backed`). -/
theorem within_preprepare_of_leader (hbj : BoundedJustice sch r)
    {L : node} (hL : ¬ nset.is_byz L = true) {PV W : view} (hnext : vord.next PV W)
    (hlead : th.leader W L = true)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input L E₀ = true)
    (hjust : (∃ w e, (r.at' N).msg_tc_lock L PV w e = true) ∨ (r.at' N).msg_tc_nolock L PV = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B →
      Active (r.at' n) L ∧ InView (r.at' n) L W) :
    r.WithinFrom N B (fun s => ∃ E, s.msg_preprepare L W E = true) := by
  have hin' : ∀ n, N ≤ n → (r.at' n).input L E₀ = true :=
    r.mono (P := fun s => s.input L E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) L E₀ hm) hin
  have hnp : ∀ n, ¬ (∃ E, (r.at' n).msg_preprepare L W E = true) →
      ¬ (r.at' n).proposed_in L W = true := fun n hnot hp =>
    hnot (Mvba.reachable_proposed_in_backed (r.reachable n) L W hL hp)
  rcases hjust with ⟨w, e, hw⟩ | hnl
  · -- `Recover(lock(J))`: a valid representation of the lock's entries.
    obtain ⟨S', hpq⟩ := (Mvba.reachable_tc_lock_backed (r.reachable N) L PV w e hw).1
    obtain ⟨x, hxv, hxe⟩ := Mvba.reachable_prepqc_valid (r.reachable N) S' w e hpq
    refine r.withinFrom_of_boundedFair (hbj.local_ (.leader_repropose L PV W w x) rfl)
      (ref_add_le hgst hB) (fun _ _ h => ⟨x, leader_repropose_effect h⟩) ?_
    intro n hn hclk hnot
    obtain ⟨hab, hview⟩ := hwin n hn hclk
    exact enabled_leader_repropose hL ⟨E₀, hin' n hn⟩ hab hnext hlead hview
      (hxe ▸ r.mono (P := fun s => s.msg_tc_lock L PV w e = true)
        (fun m hm => Mvba.msg_tc_lock.mono (r.steps m) L PV w e hm) hw n hn) hxv (hnp n hnot)
  · refine r.withinFrom_of_boundedFair (hbj.local_ (.leader_propose_fresh L PV W E₀) rfl)
      (ref_add_le hgst hB) (fun _ _ h => ⟨E₀, leader_propose_fresh_effect h⟩) ?_
    intro n hn hclk hnot
    obtain ⟨hab, hview⟩ := hwin n hn hclk
    exact enabled_leader_propose_fresh hL hab hnext hlead hview
      (r.mono (P := fun s => s.msg_tc_nolock L PV = true)
        (fun m hm => Mvba.msg_tc_nolock.mono (r.steps m) L PV hm) hnl n hn) (hin' n hn) (hnp n hnot)

/-- **Link 3, `handle_preprepare` (a first delivery, `Δ`): a correct
validator accepts the correct leader's proposal**, sent at or after GST and
retained by the receiver. The vote guard lapses only by the acceptance
itself (`accepted_of_vote_guard_lapsed`, which needs the validator in `W`
and not timed out there — the prefix facts). -/
theorem within_accepted (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {L : node} (hL : ¬ nset.is_byz L = true)
    {PV W : view} (hnext : vord.next PV W) (hlead : th.leader W L = true)
    {e : value} (hvalid : th.valid e = true)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.Δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hpp : (r.at' N).msg_preprepare L W e = true)
    (hjust : (∃ s w, (r.at' N).msg_tc_lock s PV w (th.ent e) = true) ∨
      ∃ s, (r.at' N).msg_tc_nolock s PV = true)
    (hsince : SinceGst r (fun s => s.msg_preprepare L W e = true))
    (hret : RetainedBy r i W (fun s => s.msg_preprepare L W e = true))
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n) ∧
      InView (r.at' n) i W ∧ ¬ (r.at' n).timed_out i W = true) :
    r.WithinFrom N B (fun s => s.accepted i W e = true) := by
  refine withinFrom_of_boundedFairWhile
    (hbj.first (.handle_preprepare i L PV W e) rfl ⟨hL, hsince, hret⟩)
    (ref_add_le hgst hB) (fun _ _ h => (handle_preprepare_effect h).1) ?_
  intro n hn hclk hnot
  obtain ⟨hall, hview, hnto⟩ := hwin n hn hclk
  have hpp' := r.mono (P := fun s => s.msg_preprepare L W e = true)
    (fun m hm => Mvba.msg_preprepare.mono (r.steps m) L W e hm) hpp n hn
  refine ⟨enabled_handle_preprepare hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩
    (hall i hi) hview hnext hlead hpp' hvalid ?_ ?_, hall⟩
  · rcases hjust with ⟨s, w, hw⟩ | ⟨s, hnl⟩
    · exact Or.inl ⟨s, w, r.mono (P := fun t => t.msg_tc_lock s PV w (th.ent e) = true)
        (fun m hm => Mvba.msg_tc_lock.mono (r.steps m) s PV w (th.ent e) hm) hw n hn⟩
    · exact Or.inr ⟨s, r.mono (P := fun t => t.msg_tc_nolock s PV = true)
        (fun m hm => Mvba.msg_tc_nolock.mono (r.steps m) s PV hm) hnl n hn⟩
  · by_contra hlapse
    exact hnot (accepted_of_vote_guard_lapsed (r.reachable n) hi hview hnto hlead hL hpp'
      hlapse)

/-- **Link 4, `adopt_prepqc` (a first delivery, `Δ`): a correct validator
forms and holds the prepare certificate**, from a correct quorum's
`Prepare`s sent at or after GST that it retained, while it is in the view.
Prepare certificates do not travel, so this is a network hop at every
validator, not an assembly somewhere followed by a local step. The
lock-view guard lapses only by the adoption (`local_prepqc_of_guard_lapsed`);
the untimed twin is `eventually_local_prepqc_of_settled`. -/
theorem within_local_prepqc (hbj : BoundedJustice sch r)
    {W : view} {e : value} {q : nodeset} (hsm : nset.supermajority q)
    (hQ : CorrectQuorum (node := node) q)
    {i : node} (hi : ¬ nset.is_byz i = true)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.Δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hall : ∀ p, nset.member p q = true → (r.at' N).msg_prepare p W (th.ent e) = true)
    (hacc : (r.at' N).accepted i W e = true)
    (hsince : SinceGst r (fun s => ∃ p, nset.member p q = true ∧ s.msg_prepare p W (th.ent e) = true))
    (hret : RetainedBy r i W (fun s => ∃ p, nset.member p q = true ∧ s.msg_prepare p W (th.ent e) = true))
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n) ∧ Active (r.at' n) i ∧
      InView (r.at' n) i W ∧ ¬ (r.at' n).timed_out i W = true) :
    r.WithinFrom N B (fun s => s.local_prepqc i W (th.ent e) = true) := by
  refine withinFrom_of_boundedFairWhile
    (hbj.first (.adopt_prepqc i W e q) rfl ⟨hQ, hsince, hret⟩)
    (ref_add_le hgst hB) (fun _ _ h => adopt_prepqc_effect h) ?_
  intro n hn hclk hnot
  obtain ⟨hallA, hab, hview, hnto⟩ := hwin n hn hclk
  have hall' : ∀ p, nset.member p q = true → (r.at' n).msg_prepare p W (th.ent e) = true :=
    fun p hp => r.mono (P := fun s => s.msg_prepare p W (th.ent e) = true)
      (fun m hm => Mvba.msg_prepare.mono (r.steps m) p W (th.ent e) hm) (hall p hp) n hn
  refine ⟨enabled_adopt_prepqc hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ hab hview hsm hall'
    (r.mono (P := fun s => s.accepted i W e = true)
      (fun m hm => Mvba.accepted.mono (r.steps m) i W e hm) hacc n hn) ?_ hnto, hallA⟩
  by_contra hlapse
  exact hnot (local_prepqc_of_guard_lapsed (r.reachable n) hi hview hsm hall' hlapse)

/-- **Link 5, `send_commit` (a `δ` step): a correct validator sends its
`Commit`.** `¬ commit_sent` lapses only by the `Commit` being on the network
(`commit_sent_backed`). -/
theorem within_msg_commit (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {W : view} {e : value}
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hacc : (r.at' N).accepted i W e = true) (hloc : (r.at' N).local_prepqc i W (th.ent e) = true)
    (hav : (r.at' N).avail_ready i e = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → Active (r.at' n) i ∧
      InView (r.at' n) i W ∧ ¬ (r.at' n).timed_out i W = true) :
    r.WithinFrom N B (fun s => s.msg_commit i W (th.ent e) = true) := by
  refine r.withinFrom_of_boundedFair (hbj.local_ (.send_commit i W e) rfl)
    (ref_add_le hgst hB) (fun _ _ h => (send_commit_effect h).2) ?_
  intro n hn hclk hnot
  obtain ⟨hab, hview, hnto⟩ := hwin n hn hclk
  have hacc' := r.mono (P := fun s => s.accepted i W e = true)
    (fun m hm => Mvba.accepted.mono (r.steps m) i W e hm) hacc n hn
  exact enabled_send_commit hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ hab hview hacc'
    (r.mono (P := fun s => s.local_prepqc i W (th.ent e) = true)
      (fun m hm => Mvba.local_prepqc.mono (r.steps m) i W (th.ent e) hm) hloc n hn) hnto
    (fun hcs => hnot (Mvba.reachable_commit_sent_backed (r.reachable n) i W e hi hcs hacc'))
    (r.mono (P := fun s => s.avail_ready i e = true)
      (fun m hm => Mvba.avail_ready.mono (r.steps m) i e hm) hav n hn)

/-- **Link 7, `form_own_commitqc` (a first delivery, `Δ`): a correct
validator forms the commit certificate and decides**, from a correct
quorum's `Commit`s sent at or after GST that it retained, while it is in
the view (the supplement's `TryFormCommitQC` and `Decide`). Its guard
`DecidedQC_i = ⊥` is the window's `AllActive`. -/
theorem within_commitqc (hbj : BoundedJustice sch r)
    {W : view} {e : value} (hval : th.valid e = true) {q : nodeset} (hsm : nset.supermajority q)
    (hQ : CorrectQuorum (node := node) q) {i : node} (hi : ¬ nset.is_byz i = true)
    {N : Nat} (hgst : r.gst ≤ r.clk N) {B : time} (hB : r.clk N + sch.Δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hall : ∀ p, nset.member p q = true → (r.at' N).msg_commit p W (th.ent e) = true)
    (hsince : SinceGst r (fun s => ∃ p, nset.member p q = true ∧ s.msg_commit p W (th.ent e) = true))
    (hret : RetainedBy r i W (fun s => ∃ p, nset.member p q = true ∧ s.msg_commit p W (th.ent e) = true))
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n) ∧ InView (r.at' n) i W) :
    r.WithinFrom N B (fun s => s.decided i e = true ∧ s.msg_commitqc i W (th.ent e) = true) := by
  refine withinFrom_of_boundedFairWhile
    (hbj.first (.form_own_commitqc i W e q) rfl ⟨hQ, hsince, hret⟩)
    (ref_add_le hgst hB)
    (fun _ _ h => ⟨(form_own_commitqc_effect h).2, (form_own_commitqc_effect h).1⟩) ?_
  intro n hn hclk _
  obtain ⟨hallA, hview⟩ := hwin n hn hclk
  exact ⟨enabled_form_own_commitqc hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ (hallA i hi) hview hsm
    (fun p hp => r.mono (P := fun s => s.msg_commit p W (th.ent e) = true)
      (fun m hm => Mvba.msg_commit.mono (r.steps m) p W (th.ent e) hm) (hall p hp) n hn) hval, hallA⟩

/-- **Link 8 by transfer, `decide` (`Δ + ρ`, the caller's): a correct
validator decides** within `Δ + ρ` of the reference time `ref N`, once some
correct validator `j` has decided on the certificate's vector and still
takes part — it has proposed, and has not abandoned on the window — the
composing layer hands `j`'s decided `CommitQC` on (`Relayed`,
Supplement, Lemma 13 (`lem:decision-propagation`)). From any index, before GST included. Needs no
view guard, so no prefix fact: only `¬ abandoned` on the window, and
`∀ E, ¬ decided` lapses only by the decision. -/
theorem within_decided_ref (hrel : Relayed sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {W : view} {e : value}
    {j : node} (hj : ¬ nset.is_byz j = true)
    {N : Nat} {B : time} (hB : r.ref N + (sch.Δ + sch.ρ) ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hqc : (r.at' N).msg_commitqc j W (th.ent e) = true) (hdec : (r.at' N).decided j e = true)
    {E₁ : value} (hjin : (r.at' N).input j E₁ = true)
    (hwin : ∀ n, N ≤ n → r.clk n ≤ B → ¬ (r.at' n).abandoned i = true)
    (hjwin : ∀ n, N ≤ n → r.clk n ≤ B → ¬ (r.at' n).abandoned j = true) :
    r.WithinFrom N B (fun s => ∃ E, s.decided i E = true) := by
  have hval := Mvba.reachable_external_validity (r.reachable N) j e hj hdec
  refine withinFrom_of_boundedFairWhile (hrel i j W e hj)
    hB (fun _ _ h => ⟨e, decide_effect h⟩) ?_
  intro n hn hclk hnot
  exact ⟨enabled_decide hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ (hwin n hn hclk)
    (r.mono (P := fun s => s.msg_commitqc j W (th.ent e) = true)
      (fun m hm => Mvba.msg_commitqc.mono (r.steps m) j W (th.ent e) hm) hqc n hn) hval
    (fun E hE => hnot ⟨E, hE⟩),
    r.mono (P := fun s => s.decided j e = true)
      (fun m hm => Mvba.decided.mono (r.steps m) j e hm) hdec n hn,
    ⟨E₁, r.mono (P := fun s => s.input j E₁ = true)
      (fun m hm => Mvba.input.mono (r.steps m) j E₁ hm) hjin n hn⟩, hjwin n hn hclk⟩

end Links

/-! ## The good view decides within `Lcert` -/

section GoodView

variable {node nodeset value evec view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited evec] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value evec view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time]

/-- **The good-view lemma** ([Bounds.md](../../docs/Bounds.md) §6.2.6, the
second table).
Let `W` be a view above the first with a correct leader `L` and a budget
`τ W` above the chain's latency, and `N₀` the first index at which a correct
validator has entered a view at or above `W` — at which every correct
validator had reached `W − 1` (the one-view retention) — its clock
`E₀ := clk N₀` at or after GST. If every
correct validator has proposed by `N₀` and none is abandoned at a clock at
or before `E₀ + Lcert`, then under the three clauses **some correct
validator has decided by `E₀ + Lcert`**. Either one already has — a decided
validator halts, so the chain below may use only validators that have
not — or none has, and the chain runs to its last link, where a correct
validator in `W` forms the commit certificate and decides in the same
step (`TryFormCommitQC` and `Decide`). Everyone else learns the decision by
transfer, which `bounded_termination` adds.

The milestones, each one timed link (the `≤` are clock bounds, `t₃` the
acceptance deadline):

* every correct validator is in `W` — `E₀ + Δ`, `sync_view_*`, since the
  first correct validator in `W` forwarded the certificate below it at `N₀`,
  after GST, and nobody is above `W`;
* the leader's `Pre-Prepare`, on the certificate it entered on — `+ δ`;
* the honest quorum has accepted and prepared — `+ Δ` (`t₃`);
* each member holds its own prepare certificate, formed from the quorum's
  `Prepare`s — `+ Δ`, and has its shares by `t₃ + Δsync` ((Δ-avail)); both
  by `t₃ + max Δ Δsync`;
* each member's `Commit` — `+ δ`;
* the commit certificate, formed by `i₀` from the quorum's `Commit`s, and
  `i₀`'s decision — `+ Δ`, which is `E₀ + Lcert`.

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
    (hfirstAbove : ∀ (n : Nat) (j : node) (V : view), ¬ nset.is_byz j = true →
      vord.le W V → (r.at' n).entered j V = true → N₀ ≤ n)
    (hret : ∀ p, ¬ nset.is_byz p = true → ReachedPrev (r.at' N₀) p W)
    (hgst : r.gst ≤ r.clk N₀)
    (hin : ∀ p, ¬ nset.is_byz p = true → ∃ E, (r.at' N₀).input p E = true)
    (hnab : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true →
      r.clk n ≤ r.clk N₀ + Lcert sch.Δ sch.δ sch.Δsync →
        ¬ (r.at' n).abandoned p = true) :
    ∃ j : node, ¬ nset.is_byz j = true ∧
      r.WithinFrom N₀ (r.clk N₀ + Lcert sch.Δ sch.δ sch.Δsync)
        (fun s => ∃ E, s.decided j E = true) := by
  by_cases hdec : ∃ j : node, ¬ nset.is_byz j = true ∧
      r.WithinFrom N₀ (r.clk N₀ + Lcert sch.Δ sch.δ sch.Δsync)
        (fun s => ∃ E, s.decided j E = true)
  · exact hdec
  /- Nobody correct has decided by `E₀ + Lcert` — before `N₀` either, since a
  decision stands. So every correct validator takes part in the chain. -/
  have hL0 : (0 : time) ≤ Lcert sch.Δ sch.δ sch.Δsync :=
    add_nonneg (add_nonneg (nsmul_nonneg (le_of_lt sch.Δ_pos) 3)
      (le_trans sch.Δsync_nonneg (le_max_right _ _))) (nsmul_nonneg sch.δ_nonneg 2)
  have hnodec : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true →
      r.clk n ≤ r.clk N₀ + Lcert sch.Δ sch.δ sch.Δsync → ∀ E,
        ¬ (r.at' n).decided p E = true := by
    intro p n hp hc E hE
    apply hdec
    rcases Nat.le_total N₀ n with h | h
    · exact ⟨p, hp, n, h, hc, E, hE⟩
    · exact ⟨p, hp, N₀, le_rfl, le_add_of_nonneg_right hL0, E,
        r.mono (P := fun s => s.decided p E = true)
          (fun m hm => Mvba.decided.mono (r.steps m) p E hm) hE N₀ h⟩
  obtain ⟨hbj, htp, hav, -⟩ := hsync
  have hfirst : ∀ (n : Nat) (j : node), ¬ nset.is_byz j = true →
      (r.at' n).entered j W = true → N₀ ≤ n := fun n j hj h =>
    hfirstAbove n j W hj (vord.le_refl W) h
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
  obtain ⟨t₅, ht₅⟩ : ∃ t, t = t₃ + max sch.Δ sch.Δsync := ⟨_, rfl⟩
  obtain ⟨t₆, ht₆⟩ : ∃ t, t = t₅ + sch.δ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ t, t = t₆ + sch.Δ := ⟨_, rfl⟩
  /- `T` is `E₀ + Lcert`: the milestone table sums to the constant. -/
  have hTL : r.clk N₀ + Lcert sch.Δ sch.δ sch.Δsync = T := by
    subst hT ht₆ ht₅ ht₃ ht₂ ht₁
    simp only [Lcert]
    abel
  have h₁₂ : t₁ ≤ t₂ := ht₂ ▸ le_add_of_nonneg_right hδ
  have h₂₃ : t₂ ≤ t₃ := ht₃ ▸ le_add_of_nonneg_right hΔ
  have h₄₅' : t₄ ≤ t₅ := by
    rw [ht₄, ht₅]; exact add_le_add le_rfl (le_max_left _ _)
  have h₃₅' : t₃ + sch.Δsync ≤ t₅ := by
    rw [ht₅]; exact add_le_add le_rfl (le_max_right _ _)
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
      Active (r.at' n) p := fun p n hp h =>
    ⟨hnab p n hp (hTL ▸ h), hnodec p n hp (hTL ▸ h)⟩
  have hall' : ∀ n, r.clk n ≤ T → AllActive (r.at' n) := fun n h p hp => hnab' p n hp h
  /- The network clauses' conditions. Every message the chain waits for was
  sent from inside `W`, so after `N₀`: at or after GST, and when every
  correct validator had reached `W − 1` (`hret`). -/
  have hsinceP : ∀ P : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view) → Prop,
      (∀ n, P (r.at' n) → N₀ ≤ n) → SinceGst r P := fun P hP n hn =>
    le_trans hgst (r.clk_le_of_le (hP n hn))
  have hretP : ∀ P : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view) → Prop,
      (∀ n, P (r.at' n) → N₀ ≤ n) → ∀ p, ¬ nset.is_byz p = true → RetainedBy r p W P :=
    fun P hP p hp n hn => by
      obtain ⟨V, hV, hVW⟩ := hret p hp
      exact ⟨V, r.mono (P := fun s => s.entered p V = true)
        (fun m hm => Mvba.entered.mono (r.steps m) p V hm) hV n (hP n hn), hVW⟩
  have hvoted : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true →
      (r.at' n).voted p W = true → N₀ ≤ n := fun p n hp hv =>
    let ⟨V, hWV, hV⟩ := entered_ge_of_voted r.toLRun hp hnext hv
    hfirstAbove n p V hp hWV hV
  have hprepN : ∀ (e : evec) n, (∃ p, nset.member p hqe.honestQuorum = true ∧
      (r.at' n).msg_prepare p W e = true) → N₀ ≤ n := fun e n ⟨p, hp, hpr⟩ =>
    let ⟨X, hX, _⟩ := Mvba.reachable_honest_prepare_accepted (r.reachable n) p W e (hQc p hp) hpr
    hvoted p n (hQc p hp) (Mvba.reachable_accepted_implies_voted (r.reachable n) p W X (hQc p hp) hX)
  have hcommitN : ∀ (p : node) (e : evec) n, ¬ nset.is_byz p = true →
      (r.at' n).msg_commit p W e = true → N₀ ≤ n := fun p e n hp hc =>
    let ⟨X, _, hX, _⟩ := (Mvba.reachable_honest_commit_accepted (r.reachable n) p W e hp hc).2
    hvoted p n hp (Mvba.reachable_accepted_implies_voted (r.reachable n) p W X hp hX)
  /- Settled in `W` on the prefix, once entered. -/
  have hset : ∀ (p : node), ¬ nset.is_byz p = true → ∀ N, (r.at' N).entered p W = true →
      ∀ n, N ≤ n → r.clk n ≤ T → Active (r.at' n) p ∧
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
  have htc : (r.at' N₀).msg_tc i₀ PV = true := msg_tc_below_of_entered r.toLRun hi₀ hnext hent₀
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
        exact within_entered_of_tc hbj hpc hnext hgst (le_of_eq ht₁.symm) hE hi₀ htc
          (hsinceP _ (fun n hjW => hfirst n i₀ hi₀ hjW)) hent₀
          (fun n _ h => ⟨hall' n (le_trans h h₁T),
            fun V hV => hbound n (le_trans h h₁T) p V hpc hV⟩))
  have hLent : (r.at' N₁).entered L W = true := hall₁ L (by simp)
  have hQent : ∀ p, nset.member p hqe.honestQuorum = true → (r.at' N₁).entered p W = true :=
    fun p hp => hall₁ p (List.mem_cons_of_mem _ ((enum.mem_members p _).mp hp))
  /- (2) The leader's `Pre-Prepare` by `t₂`, on the certificate it entered
  on and forwarded (`ViewTC_L`). -/
  have hjust₁ := exists_justification_below_of_entered r.toLRun hL hnext hLent
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
        have hppN : ∀ n, (r.at' n).msg_preprepare L W e = true → N₀ ≤ n := fun n h =>
          hfirst n L hL (honest_preprepare_entered r.toLRun hL n h)
        exact within_accepted hbj (hQc p hpq) hL hnext hlead hvalid (hgstN n₂ hN₂)
          (ht₃ ▸ add_le_add hc₂ le_rfl) hE hpp hjust₂ (hsinceP _ hppN)
          (hretP _ hppN p (hQc p hpq))
          (fun n hn h =>
            let hs := hset p (hQc p hpq) N₁ (hQent p hpq) n (Nat.le_trans hn₂ hn)
              (le_trans h h₃T)
            ⟨hall' n (le_trans h h₃T), hs.2.1, hs.2.2⟩))
  have hN₃' : N₀ ≤ N₃ := Nat.le_trans hN₂ hN₃
  have hacc₃ : ∀ p, nset.member p hqe.honestQuorum = true → (r.at' N₃).accepted p W e = true :=
    fun p hp => hall₃ p ((enum.mem_members p _).mp hp)
  /- (4)–(6) Each member forms its own prepare certificate from the honest
  quorum's `Prepare`s by `t₄`, has its shares, and commits by `t₆`. -/
  obtain ⟨N₆, hN₆, hc₆, hall₆⟩ :=
    r.withinFrom_forall (fun p s => s.msg_commit p W (th.ent e) = true)
      (fun p m hm => Mvba.msg_commit.mono (r.steps m) p W (th.ent e) hm) N₃ t₆
      (le_trans hc₃ (le_trans h₃₄ (le_trans h₄₅' h₅₆)))
      (enum.members hqe.honestQuorum) (fun p hp => by
        have hpq := hmemQ p hp
        have hpc := hQc p hpq
        have hwin : ∀ n, N₃ ≤ n → r.clk n ≤ T → Active (r.at' n) p ∧
            InView (r.at' n) p W ∧ ¬ (r.at' n).timed_out p W = true :=
          fun n hn h => hset p hpc N₁ (hQent p hpq) n (Nat.le_trans (Nat.le_trans hn₂ hN₃) hn) h
        obtain ⟨E, hE⟩ := hinN p hpc N₃ hN₃'
        -- Its own certificate, from the quorum's prepares.
        obtain ⟨a, ha, hca, hloc⟩ :=
          within_local_prepqc hbj hQs hQc hpc (hgstN N₃ hN₃') (ht₄ ▸ add_le_add hc₃ le_rfl)
            hE
            (fun p' hp' => Mvba.reachable_accepted_implies_prepare (r.reachable N₃) p' W e
              (hQc p' hp') (hacc₃ p' hp'))
            (hacc₃ p hpq) (hsinceP _ (hprepN (th.ent e))) (hretP _ (hprepN (th.ent e)) p hpc)
            (fun n hn h => ⟨hall' n (le_trans h (le_trans h₄₅' h₅T)),
              hwin n hn (le_trans h (le_trans h₄₅' h₅T))⟩)
        have hca' : r.clk a ≤ t₅ := le_trans hca h₄₅'
        -- The shares, from the acceptance.
        obtain ⟨b, hb, hsh, hcb⟩ := hav N₃ p W e hpc (hacc₃ p hpq)
        have hcb' : r.clk b ≤ t₅ := by
          rw [r.ref_eq_of_gst_le (hgstN N₃ hN₃')] at hcb
          exact le_trans hcb (le_trans (add_le_add hc₃ le_rfl) h₃₅')
        -- Both, at the later of the two.
        have hc : r.clk (max a b) ≤ t₅ := r.clk_max_le hca' hcb'
        have hNc : N₃ ≤ max a b := Nat.le_trans ha (Nat.le_max_left _ _)
        obtain ⟨c, hc', hcc, hcm⟩ :=
          within_msg_commit hbj hpc (hgstN _ (Nat.le_trans hN₃' hNc))
            (ht₆ ▸ add_le_add hc le_rfl)
            (r.mono (P := fun s => s.input p E = true)
              (fun m hm => Mvba.input.mono (r.steps m) p E hm) hE _ hNc)
            (r.mono (P := fun s => s.accepted p W e = true)
              (fun m hm => Mvba.accepted.mono (r.steps m) p W e hm) (hacc₃ p hpq) _ hNc)
            (r.mono (P := fun s => s.local_prepqc p W (th.ent e) = true)
              (fun m hm => Mvba.local_prepqc.mono (r.steps m) p W (th.ent e) hm) hloc _
              (Nat.le_max_left _ _))
            (r.mono (P := fun s => s.avail_ready p e = true)
              (fun m hm => Mvba.avail_ready.mono (r.steps m) p e hm) hsh _
              (Nat.le_max_right _ _))
            (fun n hn h => hwin n (Nat.le_trans hNc hn) (le_trans h h₆T))
        exact ⟨c, Nat.le_trans hNc hc', hcc, hcm⟩)
  have hN₆' : N₀ ≤ N₆ := Nat.le_trans hN₃' hN₆
  /- (7) `i₀`, in `W` since `N₀`, forms the commit certificate from the
  honest quorum's `Commit`s and decides, by `T = E₀ + Lcert`. -/
  obtain ⟨E₆, hE₆⟩ := hinN i₀ hi₀ N₆ hN₆'
  obtain ⟨n₇, hn₇, hc₇, hdec₇, -⟩ :=
    within_commitqc hbj hvalid hQs hQc hi₀ (hgstN N₆ hN₆') (hT ▸ add_le_add hc₆ le_rfl) hE₆
      (fun p hp => hall₆ p ((enum.mem_members p _).mp hp))
      (hsinceP _ (fun n ⟨p, hp, hc⟩ => hcommitN p (th.ent e) n (hQc p hp) hc))
      (hretP _ (fun n ⟨p, hp, hc⟩ => hcommitN p (th.ent e) n (hQc p hp) hc) i₀ hi₀)
      (fun n hn h => ⟨hall' n h, (hset i₀ hi₀ N₀ hent₀ n (Nat.le_trans hN₆' hn) h).2.1⟩)
  exact ⟨i₀, hi₀, n₇, Nat.le_trans hN₆' hn₇, hTL ▸ hc₇, e, hdec₇⟩

end GoodView

end Mvba

/-! ## The pinned trust base

The good-view lemma, the facts it rests on, and the network link; the standard trio. -/

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

/--
info: 'Mvba.preprepare_set_entered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.preprepare_set_entered

/--
info: 'Mvba.honest_preprepare_entered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.honest_preprepare_entered

/--
info: 'Mvba.entered_ge_of_voted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.entered_ge_of_voted

/--
info: 'Mvba.withinFrom_of_boundedFairWhile' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.withinFrom_of_boundedFairWhile
