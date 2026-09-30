import Cadence.Mvba.Bound

/-! # Mvba.BoundedTermination — the burn lemma, and the bound

[Bounds.md](../../docs/Bounds.md) §6.2. The target `BoundedTerminationClaim`
of [Schedule.lean](Schedule.lean), proven (`bounded_termination`): under the
three clauses of `Sync`, (A-leader-rotation-k) and the two quorum classes,
if every correct validator has proposed by `t` and none is abandoned by
`max(t, gst) + ℓ`, every correct validator has decided by `max(t, gst) + ℓ`.
`ℓ` is `Schedule.ℓ`, a closed term in the schedule's constants.

The proof is §6.2.6's, in its order:

* **The burn lemma** (`synced_succ`). Write `Synced v X` for "every correct
  validator has entered some view at or above `v` by time `X`". From
  `Synced v X` with `X` at or after GST, `Synced (succ v) (X + burn)`,
  whatever the leader or the outcome of `v`. The four rows of §6.2.6's first
  table are four steps: (T2) expires the timers, `within_timed_out` turns an
  expired timer into a timeout within `2δ`, `within_tc` assembles the
  certificate, and `within_entered_above_of_tc` moves everyone past it.
* **The finite starting point.** `N₀` is the last index whose clock is at
  or before `u := max(t, gst)`, and `M` the highest view a correct validator
  has entered there. That maximum exists because the views entered at any
  index lie in a finite list (`entered_covered`): each step enters at most
  one view (`entered_set_view`). Neither the node sort nor the views need
  be finite for this. `Synced M (u + Δ)` is one `sync_view` hop through the
  certificate below `M`.
* **The successor count.** At most `|below vL|` successors of `M` clear the
  ramp (`exists_iterate_succ_ge`, a pigeonhole over `below vL`), and fewer
  than `k` more reach a correct-led view `W` (`LeaderRotation`). So
  `Synced W (u + Δ + n • burn)` with `n ≤ |below vL| + k` (`synced_iterate`).
* **The assembly.** `W`'s first correct entry `N_W` (by `Nat.find`) is after
  `N₀`, so its clock is after `u`, hence after GST. At that index everyone
  has proposed, and the first correct validator at or above `W` is *in* `W`
  (`entered_eq_of_first_above`). `Mvba.good_view_decides` then decides
  everyone by `clk N_W + Lcert + δ ≤ u + ℓ`. The first half, up to the good
  view, is its own lemma, `exists_good_view`, which returns the view with
  every premise of `good_view_decides` in a `GoodView` structure.
* **(A-viewsync), derived.** `aViewSync_of_sync` proves `AViewSyncClaim`
  for finitely many validators, and its core, for any node sort and a
  proposal deadline, is `aViewSync_of_proposedBy`. Any correct-led view above
  every view entered when a correct validator has first decided is a good
  view in `AViewSync`'s sense (`aViewSync_of_decision`, from the two timer
  clauses alone). A correct decision exists by `bounded_termination`, or
  because an abandoned correct validator has already decided.

## The `2δ` of the timeout row

`timeout_qc i v w e` names the validator's highest held certificate, so an
adoption between the timer's expiry and the timeout moves the label. At
most one adoption can intervene (§6.2.6), which is
`local_prepqc_new_in_view`: a certificate a validator acquires while it
stays in `v` is a certificate *of* `v`. `adopt_prepqc` requires `in_view`,
and `sync_view_adopt` leaves the view; `local_prepqc_set` is the case split
over the model's labels, from Veil's generated frame lemmas. Once a certificate of `v`
is held, it is the highest one for as long as the validator stays in `v`
(`local_prepqc_within_entered`), so the label no longer moves. The first
window has at most one adoption and the second none. That is the whole
content of `within_timed_out`, and it needs no new invariant.

Everything else is a link of the shape [Bound.lean](Bound.lean) uses, one
`withinFrom_of_boundedFair` each.

## The time theory

The burn lemma and its iteration are stated over the time theory of
[Schedule.lean](Schedule.lean) (`IsOrderedAddMonoid`). The assembly takes `[IsOrderedCancelAddMonoid time]`
as a hypothesis of the theorem. It needs it for the good-view lemma (§6.2.8's
`ℕ∞` counterexample) and, in one other place, for `u < u + Δ`, which is how
`N₀` is found. The claim itself stays at the weaker theory, so the claim
states the supplement's premises and the extra class appears only where a
proof uses it. -/

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

/-- The same, on the goal. -/
local macro "mvba_effect" : tactic =>
  `(tactic| simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id])

/-! ## Which certificates a step adopts -/

section Local

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}

/-- **A certificate is adopted in the view it is of, or on leaving a view.**
The two actions that grow `local_prepqc` are `adopt_prepqc`, guarded on
`in_view i W` for the certificate's own view `W`, and `sync_view_adopt`,
which enters the view after one bounding all of `i`'s entries. Every other
action leaves the relation untouched (Veil's generated frame lemmas); the case split is
over the model's own label type. -/
theorem local_prepqc_set {l : Mvba.Label node nodeset value view} {i : node} {W : view}
    {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (h0 : ¬ st.local_prepqc i W e = true) (h1 : st'.local_prepqc i W e = true) :
    InView st i W ∨ ∃ pv v, vord.next pv v ∧ (∀ V, st.entered i V = true → vord.le V pv) ∧
      st'.entered i v = true := by
  cases l
  case adopt_prepqc i' v' e' q' =>
    mvba_tr htr
    obtain ⟨-, -, -, -, hent, hle, -, -, -, -, -, rfl⟩ := htr
    mvba_effect_at h1
    rcases h1 with ⟨rfl, rfl, rfl⟩ | h1
    · exact Or.inl ⟨hent, hle⟩
    · exact absurd h1 h0
  case sync_view_adopt i' pv v' w' e' =>
    mvba_tr htr
    obtain ⟨-, -, -, -, hnext, -, hbelow, -, rfl⟩ := htr
    mvba_effect_at h1
    rcases h1 with ⟨rfl, rfl, rfl⟩ | h1
    · exact Or.inr ⟨pv, v', hnext, hbelow, by mvba_effect⟩
    · exact absurd h1 h0
  case propose =>
    rw [Mvba.propose.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case abandon =>
    rw [Mvba.abandon.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case leader_propose_first =>
    rw [Mvba.leader_propose_first.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case leader_repropose =>
    rw [Mvba.leader_repropose.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case leader_propose_fresh =>
    rw [Mvba.leader_propose_fresh.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case handle_preprepare_first =>
    rw [Mvba.handle_preprepare_first.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case handle_preprepare =>
    rw [Mvba.handle_preprepare.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case form_prepqc =>
    rw [Mvba.form_prepqc.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case expire_timer =>
    rw [Mvba.expire_timer.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case become_avail_ready =>
    rw [Mvba.become_avail_ready.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case send_commit =>
    rw [Mvba.send_commit.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case form_commitqc =>
    rw [Mvba.form_commitqc.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case decide =>
    rw [Mvba.decide.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case timeout_qc =>
    rw [Mvba.timeout_qc.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case timeout_noqc =>
    rw [Mvba.timeout_noqc.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case form_tc_lock =>
    rw [Mvba.form_tc_lock.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case form_tc_nolock =>
    rw [Mvba.form_tc_nolock.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case form_own_commitqc =>
    rw [Mvba.form_own_commitqc.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case form_own_tc_lock =>
    rw [Mvba.form_own_tc_lock.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case form_own_tc_nolock =>
    rw [Mvba.form_own_tc_nolock.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case sync_view =>
    rw [Mvba.sync_view.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case byz_preprepare =>
    rw [Mvba.byz_preprepare.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case byz_prepare =>
    rw [Mvba.byz_prepare.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case byz_commit =>
    rw [Mvba.byz_commit.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case byz_timeout_qc =>
    rw [Mvba.byz_timeout_qc.frame_local_prepqc htr] at h1; exact absurd h1 h0
  case byz_timeout_noqc =>
    rw [Mvba.byz_timeout_noqc.frame_local_prepqc htr] at h1; exact absurd h1 h0

/-- **A certificate acquired while staying in `v` is of `v`.** If `i` is in
`v` from `N` on, up to an index at which it is in no higher view, then any
certificate it holds there and did not hold at `N` is a certificate of
`v`. By `local_prepqc_set`: an adoption was in its own view, which is `v`;
an adopting `sync_view` would have taken `i` above `v`. -/
theorem local_prepqc_new_in_view (r : MvbaRun th) {i : node} {v W : view} {e : value}
    {N : Nat} (hent : (r.at' N).entered i v = true)
    (hN : ¬ (r.at' N).local_prepqc i W e = true) :
    ∀ n, N ≤ n → (∀ V, (r.at' n).entered i V = true → vord.le V v) →
      (r.at' n).local_prepqc i W e = true → W = v := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact fun _ h => absurd h hN
  | succ n hn ih =>
    intro hbelow h1
    have hbelow' : ∀ V, (r.at' n).entered i V = true → vord.le V v := fun V hV =>
      hbelow V (Mvba.entered.mono (r.steps n) i V hV)
    by_cases h0 : (r.at' n).local_prepqc i W e = true
    · exact ih hbelow' h0
    have hentn : (r.at' n).entered i v = true :=
      r.mono (P := fun s => s.entered i v = true)
        (fun m hm => Mvba.entered.mono (r.steps m) i v hm) hent n hn
    rcases local_prepqc_set (r.steps n) h0 h1 with hview | ⟨pv, v', hnext, hle, hv'⟩
    · exact vord.le_antisymm W v (hbelow' W hview.1) (hview.2 v hentn)
    · exfalso
      have hvpv : vord.le v pv := hle v hentn
      have hv'v : vord.le v' v := hbelow v' hv'
      have hlt := (vord.le_lt pv v').mp ((vord.next_def pv v').mp hnext).1
      exact hlt.2 (vord.le_antisymm pv v' hlt.1 (vord.le_trans v' v pv hv'v hvpv))

end Local


/-! ## Which view a step enters, and why the entered views are finitely many -/

section Entry

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}

/-- The one view a label can enter: `propose` enters the first view, the two
`sync_view` variants the view they name, every other action none. -/
def enteredView : Mvba.Label node nodeset value view → Option view
  | .propose .. => some vord.zero
  | .sync_view _ _ v => some v
  | .sync_view_adopt _ _ v _ _ => some v
  | _ => none

/-- **Each step enters at most one view**: a view newly entered by any
validator is the label's `enteredView`. One case per action, the non-entering
ones from Veil's generated frame lemmas. -/
theorem entered_set_view {l : Mvba.Label node nodeset value view} {j : node} {V : view}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (h0 : ¬ st.entered j V = true) (h1 : st'.entered j V = true) :
    enteredView l = some V := by
  cases l
  case propose i' e' =>
    mvba_tr htr
    obtain ⟨-, -, -, rfl⟩ := htr
    mvba_effect_at h1
    rcases h1 with ⟨-, h⟩ | h
    · subst h; rfl
    · exact absurd h h0
  case sync_view i' pv v' =>
    mvba_tr htr
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := htr
    mvba_effect_at h1
    rcases h1 with ⟨-, h⟩ | h
    · subst h; rfl
    · exact absurd h h0
  case sync_view_adopt i' pv v' w' e' =>
    mvba_tr htr
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
    mvba_effect_at h1
    rcases h1 with ⟨-, h⟩ | h
    · subst h; rfl
    · exact absurd h h0
  case abandon => rw [Mvba.abandon.frame_entered htr] at h1; exact absurd h1 h0
  case leader_propose_first =>
    rw [Mvba.leader_propose_first.frame_entered htr] at h1; exact absurd h1 h0
  case leader_repropose =>
    rw [Mvba.leader_repropose.frame_entered htr] at h1; exact absurd h1 h0
  case leader_propose_fresh =>
    rw [Mvba.leader_propose_fresh.frame_entered htr] at h1; exact absurd h1 h0
  case handle_preprepare_first =>
    rw [Mvba.handle_preprepare_first.frame_entered htr] at h1; exact absurd h1 h0
  case handle_preprepare =>
    rw [Mvba.handle_preprepare.frame_entered htr] at h1; exact absurd h1 h0
  case form_prepqc => rw [Mvba.form_prepqc.frame_entered htr] at h1; exact absurd h1 h0
  case adopt_prepqc => rw [Mvba.adopt_prepqc.frame_entered htr] at h1; exact absurd h1 h0
  case expire_timer => rw [Mvba.expire_timer.frame_entered htr] at h1; exact absurd h1 h0
  case become_avail_ready =>
    rw [Mvba.become_avail_ready.frame_entered htr] at h1; exact absurd h1 h0
  case send_commit => rw [Mvba.send_commit.frame_entered htr] at h1; exact absurd h1 h0
  case form_commitqc => rw [Mvba.form_commitqc.frame_entered htr] at h1; exact absurd h1 h0
  case decide => rw [Mvba.decide.frame_entered htr] at h1; exact absurd h1 h0
  case timeout_qc => rw [Mvba.timeout_qc.frame_entered htr] at h1; exact absurd h1 h0
  case timeout_noqc => rw [Mvba.timeout_noqc.frame_entered htr] at h1; exact absurd h1 h0
  case form_tc_lock => rw [Mvba.form_tc_lock.frame_entered htr] at h1; exact absurd h1 h0
  case form_tc_nolock => rw [Mvba.form_tc_nolock.frame_entered htr] at h1; exact absurd h1 h0
  case form_own_commitqc => rw [Mvba.form_own_commitqc.frame_entered htr] at h1; exact absurd h1 h0
  case form_own_tc_lock => rw [Mvba.form_own_tc_lock.frame_entered htr] at h1; exact absurd h1 h0
  case form_own_tc_nolock => rw [Mvba.form_own_tc_nolock.frame_entered htr] at h1; exact absurd h1 h0
  case byz_preprepare => rw [Mvba.byz_preprepare.frame_entered htr] at h1; exact absurd h1 h0
  case byz_prepare => rw [Mvba.byz_prepare.frame_entered htr] at h1; exact absurd h1 h0
  case byz_commit => rw [Mvba.byz_commit.frame_entered htr] at h1; exact absurd h1 h0
  case byz_timeout_qc => rw [Mvba.byz_timeout_qc.frame_entered htr] at h1; exact absurd h1 h0
  case byz_timeout_noqc =>
    rw [Mvba.byz_timeout_noqc.frame_entered htr] at h1; exact absurd h1 h0

/-- **At every index, the entered views lie in a finite list** — of any
validator, correct or not, with no finiteness of the node sort: the list
grows by at most the one view each step enters (`entered_set_view`). -/
theorem entered_covered (r : MvbaRun th) :
    ∀ n, ∃ Vs : List view, ∀ (j : node) (V : view), (r.at' n).entered j V = true → V ∈ Vs
  | 0 => ⟨[], fun j V h => absurd h (init_not_entered r.starts j V)⟩
  | n + 1 => by
    obtain ⟨Vs, hVs⟩ := entered_covered r n
    refine ⟨(enteredView (r.lbl n)).toList ++ Vs, fun j V h => ?_⟩
    by_cases h0 : (r.at' n).entered j V = true
    · exact List.mem_append_right _ (hVs j V h0)
    · rw [entered_set_view (r.steps n) h0 h]
      exact List.mem_append_left _ (by simp)

/-- **Entering a view above the first means the certificate below it is
there**, with the predecessor produced rather than given
(`msg_tc_below_of_entered` takes it as an argument). -/
theorem exists_tc_pred_of_entered (r : MvbaRun th) {j : node} (hj : ¬ nset.is_byz j = true)
    {V : view} {N : Nat} (hent : (r.at' N).entered j V = true) (hV : V ≠ vord.zero) :
    ∃ PV, vord.next PV V ∧ (r.at' N).msg_tc PV = true := by
  obtain ⟨m, hfalse, htrue⟩ := exists_first_entry r hent
  have hfalse' : ¬ (r.at' m).entered j V = true := by simp [hfalse]
  rcases Mvba.reachable_entered_needs_certificate_step (r.reachable m) (r.steps m)
    j V ⟨hj, hfalse', htrue⟩ with h0 | ⟨PV, hPV, _⟩
  · exact absurd h0 hV
  · exact ⟨PV, hPV, msg_tc_below_of_entered r hj hPV hent⟩

/-- **The first index at which a correct validator is at or above `W` has
one *in* `W`.** A step that enters a view above `W` reads a certificate for
the view below it, which is at or above `W`, and a certificate needs a
correct validator to have timed out — hence to have entered — that view
already. -/
theorem entered_eq_of_first_above (r : MvbaRun th) {W : view} {n : Nat}
    (hnone : ∀ (j : node) (V : view), ¬ nset.is_byz j = true → vord.le W V →
      ¬ (r.at' n).entered j V = true)
    {j : node} (hj : ¬ nset.is_byz j = true) {V : view} (hWV : vord.le W V)
    (hV : (r.at' (n + 1)).entered j V = true) : V = W := by
  rcases Mvba.reachable_entered_needs_certificate_step (r.reachable n) (r.steps n)
    j V ⟨hj, hnone j V hj hWV, hV⟩ with h0 | ⟨PV, hPV, hcert⟩
  · subst h0; exact vord.le_antisymm _ _ (vord.zero_lt W) hWV
  · by_contra hne
    have hWlt : vord.lt W V := (vord.le_lt W V).mpr ⟨hWV, fun h => hne h.symm⟩
    have hWPV : vord.le W PV := by
      by_contra hle
      exact not_le_of_lt hWlt (((vord.next_def PV V).mp hPV).2 W (lt_of_not_le hle))
    have hto : ∃ R, ¬ nset.is_byz R = true ∧ (r.at' n).timed_out R PV = true := by
      rcases hcert with htc | ⟨Wc, Ec, hlock⟩
      · exact exists_honest_timed_out_of_tc (r.reachable n) htc
      · exact exists_honest_timed_out_of_tc_lock (r.reachable n) hlock
    obtain ⟨R, hR, hRto⟩ := hto
    exact hnone R PV hR hWPV (Mvba.reachable_timed_out_entered (r.reachable n) R PV hR hRto)

end Entry

/-! ## Counting successors

What `ViewOrderEnum` is for here: `succ` names the next view, and the finite
list `below vL` bounds how many successors of any view can stay below the
ramp. The bound is by pigeonhole, and the rest of this section is the
view-order facts it needs. -/

section Succ

variable {view : Type} [vord : TotalOrderWithMinimum view]

theorem vlt_of_lt_of_le {a b c : view} (h₁ : vord.lt a b) (h₂ : vord.le b c) : vord.lt a c := by
  have h₁' := (vord.le_lt a b).mp h₁
  refine (vord.le_lt a c).mpr ⟨vord.le_trans a b c h₁'.1 h₂, fun hac => ?_⟩
  subst hac
  exact h₁'.2 (vord.le_antisymm _ _ h₁'.1 h₂)

theorem vlt_of_le_of_lt {a b c : view} (h₁ : vord.le a b) (h₂ : vord.lt b c) : vord.lt a c := by
  have h₂' := (vord.le_lt b c).mp h₂
  refine (vord.le_lt a c).mpr ⟨vord.le_trans a b c h₁ h₂'.1, fun hac => ?_⟩
  subst hac
  exact h₂'.2 (vord.le_antisymm _ _ h₂'.1 h₁)

variable (vfin : ViewOrderEnum view vord)

/-- The successor is strictly above. -/
theorem lt_succ (v : view) : vord.lt v (vfin.succ v) :=
  ((vord.next_def v (vfin.succ v)).mp (vfin.next_succ v)).1

/-- Iterated successors climb weakly. -/
theorem le_iterate_succ (v : view) : ∀ j, vord.le v (vfin.succ^[j] v)
  | 0 => vord.le_refl v
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    exact vord.le_trans _ _ _ (le_iterate_succ v j) ((vord.le_lt _ _).mp (lt_succ vfin _)).1

/-- Iterated successors climb strictly at a positive count. -/
theorem lt_iterate_succ (v : view) {j : Nat} (hj : 1 ≤ j) : vord.lt v (vfin.succ^[j] v) := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  exact vlt_of_le_of_lt (le_iterate_succ vfin v j) (lt_succ vfin _)

theorem iterate_succ_strictMono (v : view) {a b : Nat} (hab : a < b) :
    vord.lt (vfin.succ^[a] v) (vfin.succ^[b] v) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = (d + 1) + a := ⟨b - a - 1, by omega⟩
  rw [Function.iterate_add_apply]
  exact lt_iterate_succ vfin _ (by omega)

/-- **The ramp is reached within `|below vL|` successors**, and at least one
is taken: from any `M`, some `succ^[a] M` with `1 ≤ a ≤ |below vL|` is at or
above `vL`. Otherwise `vL` and the `|below vL|` successors below it would be
that many plus one distinct views in the list `below vL`. -/
theorem exists_iterate_succ_ge (M vL : view) :
    ∃ a, 1 ≤ a ∧ a ≤ (vfin.below vL).length ∧ vord.le vL (vfin.succ^[a] M) := by
  classical
  by_contra hcon
  push Not at hcon
  set len := (vfin.below vL).length
  have hlt : ∀ i, i < len → vord.lt (vfin.succ^[i + 1] M) vL := fun i hi =>
    lt_of_not_le (hcon (i + 1) (by omega) (by omega))
  let L : List view := vL :: (List.range len).map (fun i => vfin.succ^[i + 1] M)
  have hnd : L.Nodup := by
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, ?_⟩
    · obtain ⟨i, hi, hiv⟩ := List.mem_map.mp hmem
      have := ((vord.le_lt _ _).mp (hlt i (List.mem_range.mp hi))).2
      exact this hiv
    · refine List.Nodup.map_on (fun a _ b _ hab => ?_) List.nodup_range
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact ((vord.le_lt _ _).mp (iterate_succ_strictMono vfin M (Nat.succ_lt_succ h))).2 hab
      · exact ((vord.le_lt _ _).mp
          (iterate_succ_strictMono vfin M (Nat.succ_lt_succ h))).2 hab.symm
  have hsub : L ⊆ vfin.below vL := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact vfin.mem_below x x (vord.le_refl x)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact vfin.mem_below vL _ ((vord.le_lt _ _).mp (hlt i (List.mem_range.mp hi))).1
  have := (List.subperm_of_subset hnd hsub).length_le
  simp [L, len] at this

end Succ

/-! ## An expired timer, and the timeout within `2δ` -/

section Timeout

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {sch : Schedule view time} {r : TMvbaRun th time}

/-- The goal of the timeout row for `i` in `v`: it has timed out there, or
it is in a higher view already. Monotone, and the second half is what a
validator that has left `v` satisfies without doing anything. -/
def TimedOutOrAbove (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view))
    (i : node) (v : view) : Prop :=
  s.timed_out i v = true ∨ ∃ V, vord.lt v V ∧ s.entered i V = true

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
theorem TimedOutOrAbove.mono {i : node} {v : view} (n : Nat)
    (h : TimedOutOrAbove (r.at' n) i v) : TimedOutOrAbove (r.at' (n + 1)) i v := by
  rcases h with h | ⟨V, hV, hent⟩
  · exact Or.inl (Mvba.timed_out.mono (r.steps n) i v h)
  · exact Or.inr ⟨V, hV, Mvba.entered.mono (r.steps n) i V hent⟩

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- A validator in `v` that has not reached the goal is still in `v`. -/
theorem inView_of_not_above {i : node} {v : view} {N n : Nat} (hn : N ≤ n)
    (hent : (r.at' N).entered i v = true) (hg : ¬ TimedOutOrAbove (r.at' n) i v) :
    InView (r.at' n) i v :=
  ⟨r.mono (P := fun s => s.entered i v = true)
      (fun m hm => Mvba.entered.mono (r.steps m) i v hm) hent n hn,
   fun V hV => by
     by_contra hle
     exact hg (Or.inr ⟨V, lt_of_not_le hle, hV⟩)⟩

omit [IsOrderedAddMonoid time] in
/-- **Holding a certificate of `v` itself, the label is fixed** and one `δ`
step suffices: `timeout_qc i v v e` stays enabled until the goal holds,
since no held certificate is of a view above `v` while `i` is in it. -/
theorem within_timed_out_of_top (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {v : view} {e : value}
    {N : Nat} {B : time} (hB : r.ref N + sch.δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hent : (r.at' N).entered i v = true)
    (htimer : (r.at' N).timer_expired i v = true)
    (htop : (r.at' N).local_prepqc i v e = true)
    (hnab : ∀ n, N ≤ n → r.clk n ≤ B → Active (r.at' n) i) :
    r.WithinFrom N B (fun s => TimedOutOrAbove s i v) := by
  refine r.withinFrom_of_boundedFair (hbj.local_ (.timeout_qc i v v e) rfl) hB
    (fun _ _ h => Or.inl (timeout_qc_effect h)) ?_
  intro n hn hclk hnot
  have hview := inView_of_not_above hn hent hnot
  exact enabled_timeout_qc hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩
    (hnab n hn hclk) hview
    (r.mono (P := fun s => s.timer_expired i v = true)
      (fun m hm => Mvba.timer_expired.mono (r.steps m) i v hm) htimer n hn)
    (fun h => hnot (Or.inl h))
    (r.mono (P := fun s => s.local_prepqc i v e = true)
      (fun m hm => Mvba.local_prepqc.mono (r.steps m) i v e hm) htop n hn)
    (fun W E hW => Mvba.reachable_local_prepqc_within_entered (r.reachable n) i W E v hi hW
      hview.2)

/-- **An expired timer produces a `Timeout` within `2δ`** — or the
validator has left `v`. The timed twin of `eventually_timed_out_of_timer`,
and §6.2.6's second row. The cases:

* the goal already holds at `N`: nothing to do;
* a certificate of `v` is held at some index inside the first `δ` window:
  from there `within_timed_out_of_top`, one more `δ`;
* otherwise no certificate is acquired inside the first window
  (`local_prepqc_new_in_view`), so the label chosen at `N` — `timeout_qc`
  on the highest certificate then held, found over `below v`, or
  `timeout_noqc` if none — stays enabled for the whole window, and fires. -/
theorem within_timed_out (vfin : ViewOrderEnum view vord) (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {v : view}
    {N : Nat} {B : time} (hB : r.ref N + 2 • sch.δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hent : (r.at' N).entered i v = true)
    (htimer : (r.at' N).timer_expired i v = true)
    (hnab : ∀ n, N ≤ n → r.clk n ≤ B → Active (r.at' n) i) :
    r.WithinFrom N B (fun s => TimedOutOrAbove s i v) := by
  classical
  have hδ : (0 : time) ≤ sch.δ := sch.δ_nonneg
  have hB₁ : r.ref N + sch.δ ≤ B :=
    le_trans (add_le_add le_rfl (by rw [two_nsmul]; exact le_add_of_nonneg_left hδ)) hB
  -- Already done at `N`.
  by_cases hg : TimedOutOrAbove (r.at' N) i v
  · exact ⟨N, le_rfl, le_trans (r.clk_le_ref N) (le_trans (le_add_of_nonneg_right hδ) hB₁), hg⟩
  have hview := inView_of_not_above le_rfl hent hg
  -- A certificate of `v` itself, now or inside the first window: one step.
  by_cases hlate : ∃ n', N ≤ n' ∧ r.clk n' ≤ r.ref N + sch.δ ∧
      ∃ e', (r.at' n').local_prepqc i v e' = true
  · obtain ⟨n', hn', hc', e', he'⟩ := hlate
    have href : r.ref n' + sch.δ ≤ B := by
      refine le_trans (add_le_add (r.ref_le hc' (le_trans (r.gst_le_ref N)
        (le_add_of_nonneg_right hδ))) le_rfl) ?_
      rw [add_assoc, ← two_nsmul]; exact hB
    obtain ⟨n, hn, hc, hP⟩ := within_timed_out_of_top hbj hi href
      (r.mono (P := fun s => s.input i E₀ = true)
        (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n' hn')
      (r.mono (P := fun s => s.entered i v = true)
        (fun m hm => Mvba.entered.mono (r.steps m) i v hm) hent n' hn')
      (r.mono (P := fun s => s.timer_expired i v = true)
        (fun m hm => Mvba.timer_expired.mono (r.steps m) i v hm) htimer n' hn')
      he' (fun n hn h => hnab n (Nat.le_trans hn' hn) h)
    exact ⟨n, Nat.le_trans hn' hn, hc, hP⟩
  push Not at hlate
  -- Otherwise every certificate acquired in the first window is one already held.
  have hold : ∀ n, N ≤ n → r.clk n ≤ r.ref N + sch.δ → ¬ TimedOutOrAbove (r.at' n) i v →
      ∀ W E, (r.at' n).local_prepqc i W E = true → (r.at' N).local_prepqc i W E = true := by
    intro n hn hc hnot W E hW
    by_contra hnew
    have hWv := local_prepqc_new_in_view r.toLRun hent hnew n hn
      (inView_of_not_above hn hent hnot).2 hW
    subst hWv
    exact hlate n hn hc E hW
  have hstable : ∀ n, N ≤ n → ¬ TimedOutOrAbove (r.at' n) i v →
      (∃ E, (r.at' n).input i E = true) ∧ InView (r.at' n) i v ∧
        (r.at' n).timer_expired i v = true ∧ ¬ (r.at' n).timed_out i v = true :=
    fun n hn hnot =>
      ⟨⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
          (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩,
       inView_of_not_above hn hent hnot,
       r.mono (P := fun s => s.timer_expired i v = true)
          (fun m hm => Mvba.timer_expired.mono (r.steps m) i v hm) htimer n hn,
       fun h => hnot (Or.inl h)⟩
  refine TLRun.WithinFrom.mono_time ?_ hB₁
  by_cases hany : ∃ W E, (r.at' N).local_prepqc i W E = true
  · obtain ⟨W₀, E₀', hW₀⟩ := hany
    have hheld : ∀ W E, (r.at' N).local_prepqc i W E = true → W ∈ vfin.below v :=
      fun W E hW => vfin.mem_below v W
        (Mvba.reachable_local_prepqc_within_entered (r.reachable N) i W E v hi hW hview.2)
    obtain ⟨w, -, ⟨e, he⟩, hmax⟩ :=
      exists_greatest vord.le vord.le_total (fun a b c => vord.le_trans a b c)
        (fun W => ∃ E, (r.at' N).local_prepqc i W E = true) (vfin.below v) W₀
        (hheld W₀ E₀' hW₀) ⟨E₀', hW₀⟩
    refine r.withinFrom_of_boundedFair (hbj.local_ (.timeout_qc i v w e) rfl) le_rfl
      (fun _ _ h => Or.inl (timeout_qc_effect h)) ?_
    intro n hn hclk hnot
    obtain ⟨hin', hview', htimer', hnto⟩ := hstable n hn hnot
    exact enabled_timeout_qc hi hin' (hnab n hn (le_trans hclk hB₁)) hview' htimer' hnto
      (r.mono (P := fun s => s.local_prepqc i w e = true)
        (fun m hm => Mvba.local_prepqc.mono (r.steps m) i w e hm) he n hn)
      (fun W E hW => by
        have h := hold n hn hclk hnot W E hW
        exact hmax W (hheld W E h) ⟨E, h⟩)
  · push Not at hany
    refine r.withinFrom_of_boundedFair (hbj.local_ (.timeout_noqc i v) rfl) le_rfl
      (fun _ _ h => Or.inl (timeout_noqc_effect h)) ?_
    intro n hn hclk hnot
    obtain ⟨hin', hview', htimer', hnto⟩ := hstable n hn hnot
    exact enabled_timeout_noqc hi hin' (hnab n hn (le_trans hclk hB₁)) hview' htimer' hnto
      (fun W E hW => hany W E (hold n hn hclk hnot W E hW))

end Timeout


/-! ## The timed links the good view did not need

The eight links of [Bound.lean](Bound.lean) are the good view's; the burn
lemma needs the view change as well. Each is the untimed link's
(`eventually_entered_above_of_tc`, `eventually_tc_of_timed_out_quorum`) with
one (Δ-justice) clause in place of the weak-fairness step, and each comes
twice: as a first delivery (`Δ`, for a fresh view, whose messages were all
sent after GST) and as a retransmission (`Δ + ρ`, whatever the history —
the first view burnt after `max(t, gst)`). The timeouts of the previous
section are `δ` steps. -/

section Links

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {time : Type} [LinearOrder time] [AddCommMonoid time]
  {sch : Schedule view time} {r : TMvbaRun th time}

omit [AddCommMonoid time] in
/-- **Nobody correct is past `v` while no certificate at or above `v`
exists**: entering a view above `v` reads the certificate of the view
below it, which is at or above `v`. -/
theorem notPast_of_no_tc {n : Nat} {p : node} (hp : ¬ nset.is_byz p = true) {v : view}
    (hno : ¬ ∃ pv, vord.le v pv ∧ (r.at' n).msg_tc pv = true) : NotPast (r.at' n) p v := by
  intro V hV
  by_contra hle
  have hvV : vord.lt v V := lt_of_not_le hle
  have hV0 : V ≠ vord.zero := fun h => not_le_of_lt hvV (h ▸ vord.zero_lt v)
  obtain ⟨PV, hPV, htc⟩ := exists_tc_pred_of_entered r.toLRun hp hV hV0
  refine hno ⟨PV, ?_, htc⟩
  by_contra hle'
  exact not_le_of_lt hvV (((vord.next_def PV V).mp hPV).2 v (lt_of_not_le hle'))

/-- **`sync_view`, retransmitted (`Δ + ρ`): given a certificate for `pv`, a
correct validator is above `pv` within `Δ + ρ`**, whenever the certificate
was formed: an active holder re-sends its `ViewTC_i`. The timed twin of
`eventually_entered_above_of_tc`: the view guard's lapse *is* the goal. -/
theorem within_entered_above_of_tc (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {pv v : view} (hnext : vord.next pv v)
    {N : Nat} {B : time} (hB : r.ref N + (sch.Δ + sch.ρ) ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (htc : (r.at' N).msg_tc pv = true)
    (hact : ∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n)) :
    r.WithinFrom N B (fun s => ∃ V, vord.lt pv V ∧ s.entered i V = true) := by
  refine withinFrom_of_boundedFairWhile (hbj.certificates i pv v).1 hB
    (fun _ _ h => ⟨v, ((vord.next_def pv v).mp hnext).1, sync_view_effect h⟩) ?_
  intro n hn hclk hnot
  exact ⟨enabled_sync_view hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ (hact n hn hclk i hi) hnext
    (r.mono (P := fun s => s.msg_tc pv = true)
      (fun m hm => Mvba.msg_tc.mono (r.steps m) pv hm) htc n hn)
    (fun V hV => by
      by_contra hle
      exact hnot ⟨V, lt_of_not_le hle, hV⟩), hact n hn hclk⟩

/-- **`sync_view`, first delivery (`Δ`)**: the same, for a certificate first
obtained at or after GST, which its first correct holder processes and
forwards on arrival. -/
theorem within_entered_above_of_fresh_tc (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {pv v : view} (hnext : vord.next pv v)
    {N : Nat} {B : time} (hB : r.ref N + sch.Δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (htc : (r.at' N).msg_tc pv = true)
    (hsince : SinceGst r (fun s => s.msg_tc pv = true))
    (hact : ∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n)) :
    r.WithinFrom N B (fun s => ∃ V, vord.lt pv V ∧ s.entered i V = true) := by
  refine withinFrom_of_boundedFairWhile (hbj.first (.sync_view i pv v) rfl hsince) hB
    (fun _ _ h => ⟨v, ((vord.next_def pv v).mp hnext).1, sync_view_effect h⟩) ?_
  intro n hn hclk hnot
  exact ⟨enabled_sync_view hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ (hact n hn hclk i hi) hnext
    (r.mono (P := fun s => s.msg_tc pv = true)
      (fun m hm => Mvba.msg_tc.mono (r.steps m) pv hm) htc n hn)
    (fun V hV => by
      by_contra hle
      exact hnot ⟨V, lt_of_not_le hle, hV⟩), hact n hn hclk⟩

/-- **`sync_view`, forwarded (`Δ`)**: the same, for the certificate below a
view `v` into which a correct validator entered at or after GST
(`line:mvba:sv-forward`). -/
theorem within_entered_above_of_forwarded (hbj : BoundedJustice sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {pv v : view} (hnext : vord.next pv v)
    {N : Nat} {B : time} (hB : r.ref N + sch.Δ ≤ B)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (htc : (r.at' N).msg_tc pv = true)
    (hfwd : SinceGst r (SomeEntered v)) (hsome : SomeEntered v (r.at' N))
    (hact : ∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n)) :
    r.WithinFrom N B (fun s => ∃ V, vord.lt pv V ∧ s.entered i V = true) := by
  refine withinFrom_of_boundedFairWhile (hbj.forwarded i pv v hfwd).1 hB
    (fun _ _ h => ⟨v, ((vord.next_def pv v).mp hnext).1, sync_view_effect h⟩) ?_
  intro n hn hclk hnot
  obtain ⟨j, hj, hjv⟩ := hsome
  exact ⟨enabled_sync_view hi
    ⟨E₀, r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin n hn⟩ (hact n hn hclk i hi) hnext
    (r.mono (P := fun s => s.msg_tc pv = true)
      (fun m hm => Mvba.msg_tc.mono (r.steps m) pv hm) htc n hn)
    (fun V hV => by
      by_contra hle
      exact hnot ⟨V, lt_of_not_le hle, hV⟩),
    hact n hn hclk, j, hj, r.mono (P := fun s => s.entered j v = true)
      (fun m hm => Mvba.entered.mono (r.steps m) j v hm) hjv n hn⟩

omit [AddCommMonoid time] in
/-- **A correct validator that has entered `v` can form `v`'s timeout
certificate at every index where no certificate at or above `v` exists yet**,
given a quorum of timeouts: it is in `v` (`notPast_of_no_tc`), its "not
already formed" record is unset (`tc_formed_backed`), and one of its two
rules applies, fixed by `exists_dominating_timeout`. Both links below read
it. -/
theorem form_own_tc_enabled (enum : ByzNodeSetEnum node nodeset nset)
    {q : nodeset} (hsm : nset.supermajority q) {v : view} {i : node}
    (hi : ¬ nset.is_byz i = true) {N : Nat}
    (hto : ∀ p, nset.member p q = true → SentTimeout (r.at' N) p v)
    (hent : (r.at' N).entered i v = true) :
    (∀ n, N ≤ n → Active (r.at' n) i → ¬ (∃ pv, vord.le v pv ∧ (r.at' n).msg_tc pv = true) →
      Enabled (Mvba.relationalTransitionSystem node nodeset value view) th (r.at' n)
        (.form_own_tc_nolock i v q)) ∨
    ∃ r₀ w e, ∀ n, N ≤ n → Active (r.at' n) i →
      ¬ (∃ pv, vord.le v pv ∧ (r.at' n).msg_tc pv = true) →
      Enabled (Mvba.relationalTransitionSystem node nodeset value view) th (r.at' n)
        (.form_own_tc_lock i v q r₀ w e) := by
  have hin : ∀ n, N ≤ n → ∃ E, (r.at' n).input i E = true := fun n hn =>
    let ⟨E, hE⟩ := Mvba.reachable_entered_implies_input (r.reachable N) i v hi hent
    ⟨E, r.mono (P := fun s => s.input i E = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E hm) hE n hn⟩
  have hview : ∀ n, N ≤ n → ¬ (∃ pv, vord.le v pv ∧ (r.at' n).msg_tc pv = true) →
      InView (r.at' n) i v := fun n hn hnot =>
    ⟨r.mono (P := fun s => s.entered i v = true)
      (fun m hm => Mvba.entered.mono (r.steps m) i v hm) hent n hn, notPast_of_no_tc hi hnot⟩
  have hnf : ∀ n, ¬ (∃ pv, vord.le v pv ∧ (r.at' n).msg_tc pv = true) →
      ¬ (r.at' n).tc_formed i v = true := fun n hnot h =>
    hnot ⟨v, vord.le_refl v, Mvba.reachable_tc_formed_backed (r.reachable n) i v h⟩
  rcases exists_dominating_timeout (enum.members q)
      (fun p hp => hto p ((enum.mem_members p q).mpr hp)) with hall | ⟨r₀, w, e, hr₀, hq₀, hdom⟩
  · refine Or.inl fun n hn hact hnot => ?_
    exact enabled_form_own_tc_nolock hi (hin n hn) hact (hview n hn hnot) (hnf n hnot) hsm
      (fun p hp => r.mono (P := fun s => s.msg_timeout_noqc p v = true)
        (fun m hm => Mvba.msg_timeout_noqc.mono (r.steps m) p v hm)
        (hall p ((enum.mem_members p q).mp hp)) n hn)
  · refine Or.inr ⟨r₀, w, e, fun n hn hact hnot => ?_⟩
    exact enabled_form_own_tc_lock hi (hin n hn) hact (hview n hn hnot) (hnf n hnot) hsm
      ((enum.mem_members r₀ q).mpr hr₀)
      (r.mono (P := fun s => s.msg_timeout_qc r₀ v w e = true)
        (fun m hm => Mvba.msg_timeout_qc.mono (r.steps m) r₀ v w e hm) hq₀ n hn)
      (r.mono (P := fun s => s.msg_prepqc w e = true)
        (fun m hm => Mvba.msg_prepqc.mono (r.steps m) w e hm)
        (Mvba.reachable_timeout_qc_backed (r.reachable N) r₀ v w e hq₀) n hn)
      (Mvba.reachable_timeout_qc_view_le (r.reachable N) r₀ v w e hq₀)
      (fun p hp => by
        rcases hdom p ((enum.mem_members p q).mp hp) with hnq | ⟨W, E, hW, hWle⟩
        · exact Or.inl (r.mono (P := fun s => s.msg_timeout_noqc p v = true)
            (fun m hm => Mvba.msg_timeout_noqc.mono (r.steps m) p v hm) hnq n hn)
        · exact Or.inr ⟨W, E, r.mono (P := fun s => s.msg_timeout_qc p v W E = true)
            (fun m hm => Mvba.msg_timeout_qc.mono (r.steps m) p v W E hm) hW n hn, hWle⟩)

/-- **`form_own_tc_*`, retransmitted (`Δ + ρ`): a correct quorum all of whose
members have sent a `Timeout` for `v` closes it — or some certificate at or
above `v` appears — within `Δ + ρ`**, whenever the timeouts were sent:
members still in `v` re-send them, and a correct member of the quorum,
which entered `v` to time out there, forms the certificate. Which of its
rules fires is fixed at `N` (`form_own_tc_enabled`), and a member leaving
`v` is itself the second outcome (`notPast_of_no_tc`). -/
theorem within_tc (enum : ByzNodeSetEnum node nodeset nset) (hbj : BoundedJustice sch r)
    {q : nodeset} (hsm : nset.supermajority q) (hQ : CorrectQuorum (node := node) q) {v : view}
    {N : Nat} {B : time} (hB : r.ref N + (sch.Δ + sch.ρ) ≤ B)
    (hto : ∀ p, nset.member p q = true → SentTimeout (r.at' N) p v)
    (hact : ∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n)) :
    r.WithinFrom N B (fun s => ∃ pv, vord.le v pv ∧ s.msg_tc pv = true) := by
  /- The forming validator: a member of the quorum, which is correct and
  timed out in `v`, so entered it. -/
  obtain ⟨i, hiq, -⟩ := nset.greater_than_third_one_honest q
    (nset.supermajority_greater_than_third _ hsm)
  have hi := hQ i hiq
  have hent : (r.at' N).entered i v = true := by
    refine Mvba.reachable_timed_out_entered (r.reachable N) i v hi ?_
    rcases hto i hiq with h | ⟨w, e, h⟩
    · exact Mvba.reachable_honest_timeout_noqc_timed_out (r.reachable N) i v hi h
    · exact Mvba.reachable_honest_timeout_qc_timed_out (r.reachable N) i v w e hi h
  rcases form_own_tc_enabled enum hsm hi hto hent with hnl | ⟨r₀, w, e, hl⟩
  · refine withinFrom_of_boundedFairWhile (hbj.timeouts i v q hi hQ).2 hB
      (fun _ _ h => ⟨v, vord.le_refl v, form_own_tc_nolock_effect h⟩) ?_
    intro n hn hclk hnot
    exact ⟨hnl n hn (hact n hn hclk i hi) hnot, hact n hn hclk,
      fun p hp => notPast_of_no_tc (hQ p hp) hnot⟩
  · refine withinFrom_of_boundedFairWhile ((hbj.timeouts i v q hi hQ).1 r₀ w e) hB
      (fun _ _ h => ⟨v, vord.le_refl v, form_own_tc_lock_effect h⟩) ?_
    intro n hn hclk hnot
    exact ⟨hl n hn (hact n hn hclk i hi) hnot, hact n hn hclk,
      fun p hp => notPast_of_no_tc (hQ p hp) hnot⟩

/-- **`form_own_tc_*`, first delivery (`Δ`)**: the same, for timeouts first
sent at or after GST and retained by a correct validator `i` in `v` that
forms the certificate. -/
theorem within_tc_fresh (enum : ByzNodeSetEnum node nodeset nset) (hbj : BoundedJustice sch r)
    {q : nodeset} (hsm : nset.supermajority q) (hQ : CorrectQuorum (node := node) q) {v : view}
    {i : node} (hi : ¬ nset.is_byz i = true)
    {N : Nat} {B : time} (hB : r.ref N + sch.Δ ≤ B)
    (hto : ∀ p, nset.member p q = true → SentTimeout (r.at' N) p v)
    (hent : (r.at' N).entered i v = true)
    (hsince : SinceGst r (AnyTimeout q v)) (hret : RetainedBy r i v (AnyTimeout q v))
    (hact : ∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n)) :
    r.WithinFrom N B (fun s => ∃ pv, vord.le v pv ∧ s.msg_tc pv = true) := by
  rcases form_own_tc_enabled enum hsm hi hto hent with hnl | ⟨r₀, w, e, hl⟩
  · refine withinFrom_of_boundedFairWhile
      (hbj.first (.form_own_tc_nolock i v q) rfl ⟨hQ, hsince, hret⟩) hB
      (fun _ _ h => ⟨v, vord.le_refl v, form_own_tc_nolock_effect h⟩) ?_
    intro n hn hclk hnot
    exact ⟨hnl n hn (hact n hn hclk i hi) hnot, hact n hn hclk⟩
  · refine withinFrom_of_boundedFairWhile
      (hbj.first (.form_own_tc_lock i v q r₀ w e) rfl ⟨hQ, hsince, hret⟩) hB
      (fun _ _ h => ⟨v, vord.le_refl v, form_own_tc_lock_effect h⟩) ?_
    intro n hn hclk hnot
    exact ⟨hl n hn (hact n hn hclk i hi) hnot, hact n hn hclk⟩

end Links

/-! ## The burn lemma -/

section Burn

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **`Synced r v X`** — every correct validator has entered some view at or
above `v` by time `X`. The burn lemma's hypothesis and conclusion. -/
def Synced (r : TMvbaRun th time) (v : view) (X : time) : Prop :=
  ∀ i, ¬ nset.is_byz i = true →
    ∃ n, r.clk n ≤ X ∧ ∃ V, vord.le v V ∧ (r.at' n).entered i V = true

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **`v` is fresh** — no correct validator reached a view at or above `v`
before GST: the supplement's fresh view (`τ_v ≥ t₀`, "Termination
setting"), with GST for `t₀`. Every message a correct validator sends from
such a view is sent after GST. -/
def FreshFrom (r : TMvbaRun th time) (v : view) : Prop :=
  ∀ (n : Nat) (j : node) (V : view), ¬ nset.is_byz j = true → vord.le v V →
    (r.at' n).entered j V = true → r.gst ≤ r.clk n

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
theorem FreshFrom.mono {r : TMvbaRun th time} {v v' : view} (h : FreshFrom r v)
    (hle : vord.le v v') : FreshFrom r v' :=
  fun n j V hj hV hent => h n j V hj (vord.le_trans _ _ _ hle hV) hent

omit [Inhabited view] in
/-- What a burnt view costs is non-negative. -/
theorem Schedule.burn_nonneg (sch : Schedule view time) : 0 ≤ sch.burn :=
  add_nonneg (add_nonneg (le_trans (sch.τ_nonneg vord.zero) (sch.τ_le_max vord.zero))
    (nsmul_nonneg sch.δ_nonneg 2)) (nsmul_nonneg (le_of_lt sch.Δ_pos) 2)

/-- **The burn lemma's core** ([Bounds.md](../../docs/Bounds.md) §6.2.6, the
first table), for any two hop bounds: `D₁` for the timeout certificate and
`D₂` for the advance past it, each given as the link that achieves it. From
`Synced v X` with `X` at or after GST, `Synced (succ v)` by
`X + τmax + 2δ + D₁ + D₂` — whatever the leader or the outcome of `v`,
provided every correct validator is active (neither abandoned nor halted
after deciding) until then. The four rows:

* every correct validator still in `v` has its timer expired by
  `X + τ v ≤ X + τmax` — (T2) from its entry, which is by `X`;
* … and has timed out or left `v` by `+ 2δ` — `within_timed_out`, the one
  adoption that can move `timeout_qc`'s label being the second `δ`;
* a timeout certificate for some view `pv ≥ v` exists by `+ D₁` — either a
  member of the honest quorum is above `v`, and the certificate that let it
  climb is there already, or the whole quorum has timed out in `v` and
  `form_tc_*` fires (`htc`);
* every correct validator is above `pv` by `+ D₂` — `sync_view` (`hsy`); a
  validator already above `pv` has no work.

A validator already above `v` at the start needs nothing in the first two
rows: the goal of each row is a disjunction whose second half ("above `v`") it
satisfies at its own witness index. -/
theorem synced_succ_of_hops (enum : ByzNodeSetEnum node nodeset nset)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset) (vfin : ViewOrderEnum view vord)
    {sch : Schedule view time} {r : TMvbaRun th time} (hsync : Sync sch r)
    {v : view} {X : time} (hX : r.gst ≤ X) (hs : Synced r v X)
    {D₁ D₂ : time} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hnab : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true →
      r.clk n ≤ X + (sch.τmax + 2 • sch.δ + D₁ + D₂) → Active (r.at' n) p)
    (htc : ∀ (N : Nat) (B : time), r.ref N + D₁ ≤ B →
      (∀ p, nset.member p hqe.honestQuorum = true → SentTimeout (r.at' N) p v) →
      (∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n)) →
      r.WithinFrom N B (fun s => ∃ pv, vord.le v pv ∧ s.msg_tc pv = true))
    (hsy : ∀ (i : node) (pv : view) (N : Nat) (B : time) (E₀ : value),
      ¬ nset.is_byz i = true → vord.le v pv → r.ref N + D₂ ≤ B →
      (r.at' N).input i E₀ = true → (r.at' N).msg_tc pv = true →
      (∀ n, N ≤ n → r.clk n ≤ B → AllActive (r.at' n)) →
      r.WithinFrom N B (fun s => ∃ V, vord.lt pv V ∧ s.entered i V = true)) :
    Synced r (vfin.succ v) (X + (sch.τmax + 2 • sch.δ + D₁ + D₂)) := by
  obtain ⟨hbj, htp, -⟩ := hsync
  have hQc := hqe.honestQuorum_correct
  have hQs := hqe.honestQuorum_supermajority
  have hmemQ : ∀ p, p ∈ enum.members hqe.honestQuorum → nset.member p hqe.honestQuorum = true :=
    fun p hp => (enum.mem_members p _).mpr hp
  have hδ : (0 : time) ≤ sch.δ := sch.δ_nonneg
  have hτ : (0 : time) ≤ sch.τmax := le_trans (sch.τ_nonneg vord.zero) (sch.τ_le_max vord.zero)
  /- The deadlines, named. -/
  obtain ⟨t₁, ht₁⟩ : ∃ t, t = X + sch.τmax := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t, t = t₁ + 2 • sch.δ := ⟨_, rfl⟩
  obtain ⟨t₃, ht₃⟩ : ∃ t, t = t₂ + D₁ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ t, t = t₃ + D₂ := ⟨_, rfl⟩
  have hTb : X + (sch.τmax + 2 • sch.δ + D₁ + D₂) = T := by
    subst hT ht₃ ht₂ ht₁
    abel
  have hX₁ : X ≤ t₁ := ht₁ ▸ le_add_of_nonneg_right hτ
  have h₁₂ : t₁ ≤ t₂ := ht₂ ▸ le_add_of_nonneg_right (nsmul_nonneg hδ 2)
  have h₂₃ : t₂ ≤ t₃ := ht₃ ▸ le_add_of_nonneg_right hD₁
  have h₃T : t₃ ≤ T := hT ▸ le_add_of_nonneg_right hD₂
  have hX₂ : X ≤ t₂ := le_trans hX₁ h₁₂
  have hX₃ : X ≤ t₃ := le_trans hX₂ h₂₃
  have h₂T : t₂ ≤ T := le_trans h₂₃ h₃T
  have hnab' : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true → r.clk n ≤ T →
      Active (r.at' n) p := fun p n hp h => hnab p n hp (hTb ▸ h)
  have hall' : ∀ n, r.clk n ≤ T → AllActive (r.at' n) := fun n h p hp => hnab' p n hp h
  have hinp : ∀ p, ¬ nset.is_byz p = true → ∀ {m V}, (r.at' m).entered p V = true →
      ∀ n, m ≤ n → ∃ E, (r.at' n).input p E = true := fun p hp m V hent n hn =>
    let ⟨E, hE⟩ := Mvba.reachable_entered_implies_input (r.reachable m) p V hp hent
    ⟨E, r.mono (P := fun s => s.input p E = true)
      (fun k hk => Mvba.input.mono (r.steps k) p E hk) hE n hn⟩
  obtain ⟨R₀, hR₀⟩ :=
    nset.greater_than_third_one_honest hqe.honestQuorum
      (nset.supermajority_greater_than_third _ hQs)
  have hclk0 : r.clk 0 ≤ X := by
    obtain ⟨m, hm, -⟩ := hs R₀ hR₀.2
    exact le_trans (r.clk_le_of_le (Nat.zero_le m)) hm
  /- (1)–(2) The honest quorum has timed out in `v`, or is above it, by `t₂`. -/
  obtain ⟨N₁, -, hc₁, hall₁⟩ :=
    r.withinFrom_forall (fun p s => TimedOutOrAbove s p v)
      (fun p m hm => TimedOutOrAbove.mono m hm) 0 t₂ (le_trans hclk0 hX₂)
      (enum.members hqe.honestQuorum) (fun p hp => by
        have hpc := hQc p (hmemQ p hp)
        obtain ⟨m, hcm, V, hvV, hent⟩ := hs p hpc
        by_cases hVv : V = v
        · subst hVv
          obtain ⟨n, hmn, htimer, hcn⟩ := htp.2 m p V hpc hent
          have hcn' : r.clk n ≤ t₁ :=
            le_trans hcn (ht₁ ▸ add_le_add hcm (sch.τ_le_max V))
          obtain ⟨E, hE⟩ := hinp p hpc hent n hmn
          obtain ⟨k, hk, hck, hP⟩ :=
            within_timed_out vfin hbj hpc (N := n) (B := t₂)
              (ht₂ ▸ add_le_add (r.ref_le hcn' (le_trans hX hX₁)) le_rfl) hE
              (r.mono (P := fun s => s.entered p V = true)
                (fun j hj => Mvba.entered.mono (r.steps j) p V hj) hent n hmn) htimer
              (fun n _ h => hnab' p n hpc (le_trans h h₂T))
          exact ⟨k, Nat.zero_le k, hck, hP⟩
        · exact ⟨m, Nat.zero_le m, le_trans hcm hX₂,
            Or.inr ⟨V, (vord.le_lt v V).mpr ⟨hvV, fun h => hVv h.symm⟩, hent⟩⟩)
  /- (3) A timeout certificate for some view at or above `v`, by `t₃`. -/
  obtain ⟨pv, hvpv, n₂, hc₂, htc'⟩ : ∃ pv, vord.le v pv ∧ ∃ n, r.clk n ≤ t₃ ∧
      (r.at' n).msg_tc pv = true := by
    by_cases habove : ∃ p, p ∈ enum.members hqe.honestQuorum ∧
        ∃ V, vord.lt v V ∧ (r.at' N₁).entered p V = true
    · obtain ⟨p, hp, V, hvV, hent⟩ := habove
      have hV0 : V ≠ vord.zero := fun h => not_le_of_lt hvV (h ▸ vord.zero_lt v)
      obtain ⟨PV, hPV, htc⟩ := exists_tc_pred_of_entered r.toLRun (hQc p (hmemQ p hp)) hent hV0
      refine ⟨PV, ?_, N₁, le_trans hc₁ h₂₃, htc⟩
      by_contra hle
      exact not_le_of_lt hvV (((vord.next_def PV V).mp hPV).2 v (lt_of_not_le hle))
    · push Not at habove
      obtain ⟨n, -, hc, pv, hvpv, htc⟩ :=
        htc N₁ t₃ (ht₃ ▸ add_le_add (r.ref_le hc₁ (le_trans hX hX₂)) le_rfl) (fun p hp => by
            have hpm := (enum.mem_members p _).mp hp
            rcases hall₁ p hpm with hto | ⟨V, hvV, hent⟩
            · exact Mvba.reachable_timed_out_implies_message (r.reachable N₁) p v (hQc p hp) hto
            · exact absurd hent (habove p hpm V hvV))
          (fun n _ h => hall' n (le_trans h h₃T))
      exact ⟨pv, hvpv, n, hc, htc⟩
  /- (4) Every correct validator is above `pv` by `T`. -/
  intro i hi
  obtain ⟨m, hcm, V, -, hent⟩ := hs i hi
  obtain ⟨E, hE⟩ := hinp i hi hent (max n₂ m) (Nat.le_max_right _ _)
  obtain ⟨n, -, hc, V', hlt, hent'⟩ :=
    hsy i pv (max n₂ m) T E hi hvpv
      (hT ▸ add_le_add (r.ref_le (r.clk_max_le hc₂ (le_trans hcm hX₃)) (le_trans hX hX₃)) le_rfl)
      hE
      (r.mono (P := fun s => s.msg_tc pv = true)
        (fun j hj => Mvba.msg_tc.mono (r.steps j) pv hj) htc' _ (Nat.le_max_left _ _))
      (fun n _ h => hall' n h)
  exact ⟨n, hTb ▸ hc, V', ((vord.next_def v (vfin.succ v)).mp (vfin.next_succ v)).2 V'
    (vlt_of_le_of_lt hvpv hlt), hent'⟩

/-- **The burn lemma, for a fresh view**: `Synced (succ v) (X + burn)`, the
paper's `τ_{w+1} ≤ τ_w + 2Δ + T` (`lem:convergence`). Every timeout and
certificate of a view at or above `v` is sent after GST, so both network
hops are first deliveries, at `Δ`. The timeouts are retained by the first
member of the honest quorum to send one, which was in `v` when it did. -/
theorem synced_succ (enum : ByzNodeSetEnum node nodeset nset)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset) (vfin : ViewOrderEnum view vord)
    {sch : Schedule view time} {r : TMvbaRun th time} (hsync : Sync sch r)
    {v : view} {X : time} (hX : r.gst ≤ X) (hs : Synced r v X) (hfresh : FreshFrom r v)
    (hnab : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true → r.clk n ≤ X + sch.burn →
      Active (r.at' n) p) :
    Synced r (vfin.succ v) (X + sch.burn) := by
  classical
  have hΔ : (0 : time) ≤ sch.Δ := le_of_lt sch.Δ_pos
  have hb : sch.τmax + 2 • sch.δ + sch.Δ + sch.Δ = sch.burn := by
    simp only [Schedule.burn, two_nsmul]; abel
  have hQc := hqe.honestQuorum_correct
  rw [← hb] at hnab ⊢
  refine synced_succ_of_hops enum hqe vfin hsync hX hs hΔ hΔ hnab ?_ ?_
  · intro N B hB hto hact
    /- The timeouts of the honest quorum were sent from `v`, after GST. -/
    have hent_of : ∀ n, AnyTimeout hqe.honestQuorum v (r.at' n) →
        ∃ p, ¬ nset.is_byz p = true ∧ (r.at' n).entered p v = true := by
      rintro n ⟨p, hp, hsent⟩
      refine ⟨p, hQc p hp, Mvba.reachable_timed_out_entered (r.reachable n) p v (hQc p hp) ?_⟩
      rcases hsent with h | ⟨w, e, h⟩
      · exact Mvba.reachable_honest_timeout_noqc_timed_out (r.reachable n) p v (hQc p hp) h
      · exact Mvba.reachable_honest_timeout_qc_timed_out (r.reachable n) p v w e (hQc p hp) h
    have hsince : SinceGst r (AnyTimeout hqe.honestQuorum v) := fun n hn =>
      let ⟨p, hp, hent⟩ := hent_of n hn
      hfresh n p v hp (vord.le_refl v) hent
    /- The first of them, and its sender. -/
    obtain ⟨R₀, hR₀q, hR₀⟩ :=
      nset.greater_than_third_one_honest hqe.honestQuorum
        (nset.supermajority_greater_than_third _ hqe.honestQuorum_supermajority)
    have hex : ∃ n, AnyTimeout hqe.honestQuorum v (r.at' n) := ⟨N, R₀, hR₀q, hto R₀ hR₀q⟩
    obtain ⟨p₀, hp₀, hent₀⟩ := hent_of _ (Nat.find_spec hex)
    have hret : RetainedBy r p₀ v (AnyTimeout hqe.honestQuorum v) := fun n hn =>
      ⟨v, r.mono (P := fun s => s.entered p₀ v = true)
        (fun m hm => Mvba.entered.mono (r.steps m) p₀ v hm) hent₀ n (Nat.find_min' hex hn),
       Or.inl (vord.le_refl v)⟩
    have hent₀N : (r.at' N).entered p₀ v = true :=
      r.mono (P := fun s => s.entered p₀ v = true)
        (fun m hm => Mvba.entered.mono (r.steps m) p₀ v hm) hent₀ N
        (Nat.find_min' hex ⟨R₀, hR₀q, hto R₀ hR₀q⟩)
    exact within_tc_fresh enum hsync.1 hqe.honestQuorum_supermajority hQc hp₀ hB hto hent₀N
      hsince hret hact
  · intro i pv N B E₀ hi hvpv hB hin htc hact
    refine within_entered_above_of_fresh_tc hsync.1 hi (vfin.next_succ pv) hB hin htc ?_ hact
    intro n hn
    obtain ⟨R, hR, hRto⟩ := exists_honest_timed_out_of_tc (r.reachable n) hn
    exact hfresh n R pv hR hvpv (Mvba.reachable_timed_out_entered (r.reachable n) R pv hR hRto)

/-- **The burn lemma, for any view**: `Synced (succ v) (X + (burn + 2 • ρ))`.
The timeouts and the certificate may predate GST, so both network hops are
retransmissions, at `Δ + ρ` each — the first view burnt after
`max(t, gst)`, as the supplement's first view `V` is
(`lem:convergence`, "Reaching `V`"). -/
theorem synced_succ_first (enum : ByzNodeSetEnum node nodeset nset)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset) (vfin : ViewOrderEnum view vord)
    {sch : Schedule view time} {r : TMvbaRun th time} (hsync : Sync sch r)
    {v : view} {X : time} (hX : r.gst ≤ X) (hs : Synced r v X)
    (hnab : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true →
      r.clk n ≤ X + (sch.burn + 2 • sch.ρ) → Active (r.at' n) p) :
    Synced r (vfin.succ v) (X + (sch.burn + 2 • sch.ρ)) := by
  have hΔρ : (0 : time) ≤ sch.Δ + sch.ρ := add_nonneg (le_of_lt sch.Δ_pos) sch.ρ_nonneg
  have hb : sch.τmax + 2 • sch.δ + (sch.Δ + sch.ρ) + (sch.Δ + sch.ρ) =
      sch.burn + 2 • sch.ρ := by
    simp only [Schedule.burn, two_nsmul]; abel
  rw [← hb] at hnab ⊢
  refine synced_succ_of_hops enum hqe vfin hsync hX hs hΔρ hΔρ hnab ?_ ?_
  · intro N B hB hto hact
    exact within_tc enum hsync.1 hqe.honestQuorum_supermajority hqe.honestQuorum_correct hB hto
      hact
  · intro i pv N B E₀ hi _ hB hin htc hact
    exact within_entered_above_of_tc hsync.1 hi (vfin.next_succ pv) hB hin htc hact

/-- **`n` burnt fresh views cost `n • burn`.** The burn lemma iterated from a
fresh view, with the abandonment premise stated once up to a deadline `D`
past all of them. -/
theorem synced_iterate (enum : ByzNodeSetEnum node nodeset nset)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset) (vfin : ViewOrderEnum view vord)
    {sch : Schedule view time} {r : TMvbaRun th time} (hsync : Sync sch r)
    {v : view} {X D : time} (hX : r.gst ≤ X) (hs : Synced r v X) (hfresh : FreshFrom r v)
    (hnab : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true → r.clk n ≤ D →
      Active (r.at' n) p) :
    ∀ k : Nat, X + k • sch.burn ≤ D → Synced r (vfin.succ^[k] v) (X + k • sch.burn)
  | 0, _ => by simpa using hs
  | k + 1, hD => by
    have hb := sch.burn_nonneg
    have hk : X + k • sch.burn + sch.burn = X + (k + 1) • sch.burn := by
      rw [succ_nsmul, add_assoc]
    have hkD : X + k • sch.burn ≤ D :=
      le_trans (le_trans (le_add_of_nonneg_right hb) (le_of_eq hk)) hD
    rw [Function.iterate_succ_apply', ← hk]
    exact synced_succ enum hqe vfin hsync
      (le_trans hX (le_add_of_nonneg_right (nsmul_nonneg hb k)))
      (synced_iterate enum hqe vfin hsync hX hs hfresh hnab k hkD)
      (hfresh.mono (le_iterate_succ vfin v k))
      (fun p n hp h => hnab p n hp (le_trans h (hk ▸ hD)))

end Burn

/-! ## The assembly

§6.2.6's last paragraph, step by step. The milestones are named in the proof:
`N₀` and `M`; `Synced M (u + Δ + ρ)`; the first burn; `W`, its predecessor
`PV` and the count `j + a + 1`; `Synced W T`; `N_W` and the entry into `W`
itself; the retention at `N_W`; the good-view lemma. -/

section Assembly

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time]

/-- **The good view the assembly reaches**, measured from `u`: a view `W`
above the first (its predecessor `PV`), with a correct leader `L` and a
budget past the ramp, and the first index `N` at which a correct validator
has entered a view at or above it — `i₀`, which is *in* `W` there —
together with every other premise of `good_view_decides` at `N`: at `N`
every correct validator had reached `PV` (the one-view retention), and the
clock bounds `u < clk N ≤ u + (Δ + ρ) + 2 • ρ + burns • burn` with
`burns ≤ |below vL| + k`.

A structure rather than an existential, so that its fields have names: this
is what `exists_good_view` returns, and `bounded_termination` consumes it
by passing the fields to `good_view_decides` one by one. -/
structure GoodView (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (r : TMvbaRun th time) (u : time) where
  /-- The view below `W`. -/
  PV : view
  /-- The good view. -/
  W : view
  /-- Its correct leader. -/
  L : node
  /-- The first index at which a correct validator has entered `W` or above. -/
  N : Nat
  /-- A correct validator in `W` at `N`. -/
  i₀ : node
  next : vord.next PV W
  leads : th.leader W L = true
  leader_correct : ¬ nset.is_byz L = true
  ramp : Lcert sch.Δ sch.δ sch.Δsync < sch.τ W
  i₀_correct : ¬ nset.is_byz i₀ = true
  entered : (r.at' N).entered i₀ W = true
  first : ∀ (n : Nat) (j : node) (V : view), ¬ nset.is_byz j = true → vord.le W V →
    (r.at' n).entered j V = true → N ≤ n
  /-- The one-view retention: at `N` every correct validator has reached `PV`. -/
  retained : ∀ p, ¬ nset.is_byz p = true → ReachedPrev (r.at' N) p W
  gst_le : r.gst ≤ r.clk N
  input : ∀ p, ¬ nset.is_byz p = true → ∃ E, (r.at' N).input p E = true
  after : u < r.clk N
  /-- How many views were burnt on the way to `W`. -/
  burns : Nat
  burns_le : burns ≤ (vfin.below sch.vL).length + sch.k
  within : r.clk N ≤ u + (sch.Δ + sch.ρ) + 2 • sch.ρ + burns • sch.burn

/-- **The one-view retention** (the model's `lem:convergence`, "Retention"):
let `PV` be fresh and past the ramp, `N_P` the first index at which a
correct validator is at or above it, and `N_W` an index at which a correct
validator is above it. Then every correct validator reached `PV` before
`N_W`. The first correct validator in `PV` forwarded the certificate below
it after GST, so everyone reaches `PV` within `Δ` of `N_P`; and nobody is
above `PV` before `clk N_P + τ PV`, which is later, since the budget of a
view past the ramp exceeds `Lcert`, hence `Δ`. -/
theorem retained_before
    {sch : Schedule view time} {r : TMvbaRun th time} (hsync : Sync sch r)
    {PPV PV : view} (hPPV : vord.next PPV PV) (hramp : Lcert sch.Δ sch.δ sch.Δsync < sch.τ PV)
    (hfresh : FreshFrom r PV) {N_P : Nat}
    (hfirstP : ∀ (n : Nat) (j : node) (V : view), ¬ nset.is_byz j = true → vord.le PV V →
      (r.at' n).entered j V = true → N_P ≤ n)
    {iP : node} (hiP : ¬ nset.is_byz iP = true) (hentP : (r.at' N_P).entered iP PV = true)
    {N_W : Nat} {jW : node} (hjW : ¬ nset.is_byz jW = true) {VW : view}
    (hVW : vord.lt PV VW) (hentW : (r.at' N_W).entered jW VW = true)
    (hin : ∀ p, ¬ nset.is_byz p = true → ∃ E, (r.at' N_P).input p E = true)
    (hact : ∀ n, r.clk n ≤ r.clk N_W → AllActive (r.at' n)) :
    ∀ p, ¬ nset.is_byz p = true →
      ∃ V, vord.le PV V ∧ ∃ n, n < N_W ∧ (r.at' n).entered p V = true := by
  obtain ⟨hbj, htp, -⟩ := hsync
  have hΔ : (0 : time) ≤ sch.Δ := le_of_lt sch.Δ_pos
  have hgstP : r.gst ≤ r.clk N_P := hfresh N_P iP PV hiP (vord.le_refl PV) hentP
  /- `Δ < τ PV`: the budget clears `Lcert`, and `Lcert ≥ Δ`. -/
  have hΔL : sch.Δ ≤ Lcert sch.Δ sch.δ sch.Δsync := by
    simp only [Lcert]
    exact le_trans (le_max_left _ _)
      (le_trans (le_add_of_nonneg_left (nsmul_nonneg hΔ 3))
        (le_add_of_nonneg_right (nsmul_nonneg sch.δ_nonneg 2)))
  have hΔτ : sch.Δ < sch.τ PV := lt_of_le_of_lt hΔL hramp
  /- Nobody correct is above `PV` before `clk N_P + τ PV`, so `N_W` is later. -/
  have hfirst : ∀ (n : Nat) (j : node), ¬ nset.is_byz j = true →
      (r.at' n).entered j PV = true → N_P ≤ n := fun n j hj h =>
    hfirstP n j PV hj (vord.le_refl PV) h
  have hlate : r.clk N_P + sch.τ PV ≤ r.clk N_W := by
    by_contra h
    exact not_le_of_lt hVW
      (entered_le_before_budget htp hfirst (not_le.mp h) jW VW hjW hentW)
  have hwin : r.clk N_P + sch.Δ < r.clk N_W :=
    lt_of_lt_of_le ((add_lt_add_iff_left _).mpr hΔτ) hlate
  /- The certificate below `PV`, forwarded at `N_P`, after GST. -/
  have htc : (r.at' N_P).msg_tc PPV = true := msg_tc_below_of_entered r.toLRun hiP hPPV hentP
  have hfwd : SinceGst r (SomeEntered PV) := fun n ⟨j, hj, h⟩ =>
    hfresh n j PV hj (vord.le_refl PV) h
  intro p hp
  obtain ⟨E, hE⟩ := hin p hp
  obtain ⟨n, -, hc, V, hlt, hent⟩ :=
    within_entered_above_of_forwarded hbj hp hPPV (N := N_P) (B := r.clk N_P + sch.Δ)
      (by rw [r.ref_eq_of_gst_le hgstP]) hE htc hfwd ⟨iP, hiP, hentP⟩
      (fun n _ h => hact n (le_trans h (le_of_lt hwin)))
  exact ⟨V, ((vord.next_def PPV PV).mp hPPV).2 V hlt, n,
    r.lt_of_clk_le_of_lt hc hwin, hent⟩

/-- **The assembly's first half** ([Bounds.md](../../docs/Bounds.md)
§6.2.6, "The assembly", up to the good-view lemma): if every correct validator has
proposed by `t` and every correct validator is active (not abandoned, not
yet decided) until the last burn, a good view is reached from
`u := max(t, gst)`. `bounded_termination` is this plus
`good_view_decides`.

The route: everyone reaches `M`, the highest view a correct validator is in
at `u`, within `Δ + ρ` (retransmission: its certificate may predate GST);
view `M` is burnt at retransmission cost; the views after it are fresh and
burnt at `burn` each; and the good view `W` is chosen with its predecessor
`PV` past the ramp and above `M`, so that `PV` is fresh and the one-view
retention holds at `W`'s first entry — the supplement's charge of views
`V` and `V + 1` (`lem:good-view` takes `w ≥ V + 2`). -/
theorem exists_good_view (enum : ByzNodeSetEnum node nodeset nset)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : LeaderRotation vfin sch.k th)
    {r : TMvbaRun th time} (hsync : Sync sch r) {t : time}
    (hprop : ∀ p, ¬ nset.is_byz p = true →
      ∃ (n : Nat) (E : value), r.clk n ≤ t ∧ (r.at' n).input p E = true)
    (hnab' : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true →
      r.clk n ≤ max t r.gst + ((sch.Δ + sch.ρ) + 2 • sch.ρ
        + ((vfin.below sch.vL).length + sch.k) • sch.burn) →
        Active (r.at' n) p) :
    Nonempty (GoodView sch vfin r (max t r.gst)) := by
  classical
  have hQs := hqe.honestQuorum_supermajority
  have hΔ : (0 : time) ≤ sch.Δ := le_of_lt sch.Δ_pos
  have hρ : (0 : time) ≤ sch.ρ := sch.ρ_nonneg
  have hΔρ : (0 : time) ≤ sch.Δ + sch.ρ := add_nonneg hΔ hρ
  have hb : (0 : time) ≤ sch.burn := sch.burn_nonneg
  obtain ⟨u, hu⟩ : ∃ u, u = max t r.gst := ⟨_, rfl⟩
  rw [← hu] at hnab' ⊢
  set K := (vfin.below sch.vL).length + sch.k with hK
  obtain ⟨Bs, hBs⟩ : ∃ B, B = u + ((sch.Δ + sch.ρ) + 2 • sch.ρ + K • sch.burn) := ⟨_, rfl⟩
  rw [← hBs] at hnab'
  have hact : ∀ n, r.clk n ≤ Bs → AllActive (r.at' n) := fun n h p hp => hnab' p n hp h
  have htu : t ≤ u := hu ▸ le_max_left _ _
  have hgu : r.gst ≤ u := hu ▸ le_max_right _ _
  obtain ⟨R₀, hR₀⟩ :=
    nset.greater_than_third_one_honest hqe.honestQuorum
      (nset.supermajority_greater_than_third _ hQs)
  /- `N₀`, the last index at or before `u`. -/
  have hex : ∃ n, u < r.clk n := by
    obtain ⟨n, hn⟩ := r.clk_unbounded (u + sch.Δ)
    exact ⟨n, lt_of_lt_of_le (lt_add_of_pos_right u sch.Δ_pos) hn⟩
  have hclk0 : r.clk 0 ≤ u := by
    obtain ⟨m, E, hm, -⟩ := hprop R₀ hR₀.2
    exact le_trans (r.clk_le_of_le (Nat.zero_le m)) (le_trans hm htu)
  have hpos : 0 < Nat.find hex := by
    by_contra h
    have h0 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [h0] at this
    exact absurd hclk0 (not_le.mpr this)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, Nat.find hex = N₀ + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hcN₀ : r.clk N₀ ≤ u := not_lt.mp (Nat.find_min hex (by omega))
  have hafter : ∀ n, N₀ < n → u < r.clk n := fun n hn =>
    lt_of_lt_of_le (Nat.find_spec hex) (r.clk_le_of_le (by omega))
  have hbefore : ∀ n, r.clk n ≤ u → n ≤ N₀ := fun n hn => by
    by_contra h
    exact absurd hn (not_le.mpr (hafter n (by omega)))
  /- Every correct validator has proposed, hence entered the first view, by `N₀`. -/
  have hin₀ : ∀ p, ¬ nset.is_byz p = true → ∃ E, (r.at' N₀).input p E = true := by
    intro p hp
    obtain ⟨m, E, hm, hE⟩ := hprop p hp
    exact ⟨E, r.mono (P := fun s => s.input p E = true)
      (fun k hk => Mvba.input.mono (r.steps k) p E hk) hE N₀ (hbefore m (le_trans hm htu))⟩
  have hinN : ∀ p, ¬ nset.is_byz p = true → ∀ n, N₀ ≤ n → ∃ E, (r.at' n).input p E = true :=
    fun p hp n hn =>
      let ⟨E, hE⟩ := hin₀ p hp
      ⟨E, r.mono (P := fun s => s.input p E = true)
        (fun k hk => Mvba.input.mono (r.steps k) p E hk) hE n hn⟩
  have hz₀ : ∀ p, ¬ nset.is_byz p = true → (r.at' N₀).entered p vord.zero = true := by
    intro p hp
    obtain ⟨E, hE⟩ := hin₀ p hp
    exact Mvba.reachable_input_implies_entered (r.reachable N₀) p E hp hE
  /- `M`, the highest view a correct validator has entered at `N₀`. -/
  obtain ⟨Vs, hVs⟩ := entered_covered r.toLRun N₀
  obtain ⟨M, -, ⟨jM, hjM, hjMent⟩, hMmax⟩ :=
    exists_greatest vord.le vord.le_total (fun a b c => vord.le_trans a b c)
      (fun V => ∃ j, ¬ nset.is_byz j = true ∧ (r.at' N₀).entered j V = true) Vs vord.zero
      (hVs R₀ _ (hz₀ R₀ hR₀.2)) ⟨R₀, hR₀.2, hz₀ R₀ hR₀.2⟩
  have hMmax' : ∀ (j : node) (V : view), ¬ nset.is_byz j = true →
      (r.at' N₀).entered j V = true → vord.le V M := fun j V hj h =>
    hMmax V (hVs j V h) ⟨j, hj, h⟩
  /- Every view above `M` is fresh: a correct entry into it is after `N₀`. -/
  have hlateAbove : ∀ v, vord.lt M v → ∀ (n : Nat) (j : node) (V : view),
      ¬ nset.is_byz j = true → vord.le v V → (r.at' n).entered j V = true → N₀ < n := by
    intro v hMv n j V hj hvV hent
    by_contra hle
    have hent₀ := r.mono (P := fun s => s.entered j V = true)
      (fun k hk => Mvba.entered.mono (r.steps k) j V hk) hent N₀ (by omega)
    exact not_le_of_lt (vlt_of_lt_of_le hMv hvV) (hMmax' j V hj hent₀)
  have hfreshAbove : ∀ v, vord.lt M v → FreshFrom r v := fun v hMv n j V hj hvV hent =>
    le_trans hgu (le_of_lt (hafter n (hlateAbove v hMv n j V hj hvV hent)))
  /- The deadlines. -/
  obtain ⟨X₀, hX₀⟩ : ∃ X, X = u + (sch.Δ + sch.ρ) := ⟨_, rfl⟩
  obtain ⟨X₁, hX₁⟩ : ∃ X, X = X₀ + (sch.burn + 2 • sch.ρ) := ⟨_, rfl⟩
  have hgX₀ : r.gst ≤ X₀ := hX₀ ▸ le_trans hgu (le_add_of_nonneg_right hΔρ)
  have hgX₁ : r.gst ≤ X₁ :=
    hX₁ ▸ le_trans hgX₀ (le_add_of_nonneg_right (add_nonneg hb (nsmul_nonneg hρ 2)))
  have hdeadline : ∀ c : Nat, c + 1 ≤ K → X₁ + c • sch.burn ≤ Bs := by
    intro c hc
    have h := nsmul_le_nsmul_left hb hc
    rw [hBs, hX₁, hX₀]
    calc u + (sch.Δ + sch.ρ) + (sch.burn + 2 • sch.ρ) + c • sch.burn
        = u + ((sch.Δ + sch.ρ) + 2 • sch.ρ + (c + 1) • sch.burn) := by
          rw [succ_nsmul sch.burn c]; abel
      _ ≤ u + ((sch.Δ + sch.ρ) + 2 • sch.ρ + K • sch.burn) := by gcongr
  have hK1 : 1 ≤ K := by
    obtain ⟨a, ha1, haL, -⟩ := exists_iterate_succ_ge vfin M sch.vL
    omega
  have hX₁B : X₁ ≤ Bs := by simpa using hdeadline 0 hK1
  have hX₀B : X₀ ≤ Bs :=
    le_trans (hX₁ ▸ le_add_of_nonneg_right (add_nonneg hb (nsmul_nonneg hρ 2))) hX₁B
  /- `Synced M (u + (Δ + ρ))`: a retransmitted hop through the certificate
  below `M`, which may predate GST. -/
  have hsM : Synced r M X₀ := by
    intro i hi
    by_cases hM0 : M = vord.zero
    · exact ⟨N₀, hX₀ ▸ le_trans hcN₀ (le_add_of_nonneg_right hΔρ), vord.zero,
        hM0 ▸ vord.le_refl _, hz₀ i hi⟩
    · obtain ⟨PV, hPV, htc⟩ := exists_tc_pred_of_entered r.toLRun hjM hjMent hM0
      obtain ⟨E, hE⟩ := hin₀ i hi
      obtain ⟨n, -, hc, V, hlt, hent⟩ :=
        within_entered_above_of_tc hsync.1 hi hPV (N := N₀) (B := X₀)
          (hX₀ ▸ add_le_add (r.ref_le hcN₀ hgu) le_rfl) hE htc
          (fun n _ h => hact n (le_trans h hX₀B))
      exact ⟨n, hc, V, ((vord.next_def PV M).mp hPV).2 V hlt, hent⟩
  /- The first burn, at retransmission cost. -/
  have hs₁ : Synced r (vfin.succ M) X₁ :=
    hX₁ ▸ synced_succ_first enum hqe vfin hsync hgX₀ hsM
      (fun p n hp h => hnab' p n hp (le_trans h (hX₁ ▸ hX₁B)))
  /- `W`: its predecessor past the ramp, then a correct leader within `k` views. -/
  obtain ⟨a, ha1, haL, hvL⟩ := exists_iterate_succ_ge vfin M sch.vL
  obtain ⟨j, hjk, L, hlead, hL⟩ := hrot (vfin.succ^[a + 1] M)
  obtain ⟨PV, hPV⟩ : ∃ PV, PV = vfin.succ^[j + a] M := ⟨_, rfl⟩
  have hWeq : vfin.succ^[j] (vfin.succ^[a + 1] M) = vfin.succ PV := by
    rw [hPV, ← Function.iterate_add_apply, show j + (a + 1) = (j + a) + 1 by omega,
      Function.iterate_succ_apply']
  have hWeq' : vfin.succ^[j + a] (vfin.succ M) = vfin.succ PV := by
    rw [hPV, ← Function.iterate_succ_apply, Function.iterate_succ_apply']
  rw [hWeq] at hlead
  have hMPV : vord.lt M PV := hPV ▸ lt_iterate_succ vfin M (by omega)
  have hvLPV : vord.le sch.vL PV := by
    refine vord.le_trans _ _ _ hvL ?_
    rw [hPV, Function.iterate_add_apply]
    exact le_iterate_succ vfin (vfin.succ^[a] M) j
  have hPVW : vord.lt PV (vfin.succ PV) := lt_succ vfin PV
  have hMW : vord.lt M (vfin.succ PV) :=
    vlt_of_lt_of_le hMPV ((vord.le_lt _ _).mp hPVW).1
  /- `Synced W T` after `j + a` more burns, each of a fresh view. -/
  have hja : j + a + 1 ≤ K := by omega
  obtain ⟨T, hT⟩ : ∃ T, T = X₁ + (j + a) • sch.burn := ⟨_, rfl⟩
  have hTB : T ≤ Bs := hT ▸ hdeadline (j + a) hja
  have hsW : Synced r (vfin.succ PV) T := by
    rw [hT, ← hWeq']
    exact synced_iterate enum hqe vfin hsync hgX₁ hs₁ (hfreshAbove _ (lt_succ vfin M)) hnab'
      (j + a) (hT ▸ hTB)
  /- `N_W`, the first index at which a correct validator is at or above `W`. -/
  have hexW : ∃ n, ∃ i, ¬ nset.is_byz i = true ∧ ∃ V, vord.le (vfin.succ PV) V ∧
      (r.at' n).entered i V = true := by
    obtain ⟨n, -, V, hWV, hent⟩ := hsW R₀ hR₀.2
    exact ⟨n, R₀, hR₀.2, V, hWV, hent⟩
  have hcNW : r.clk (Nat.find hexW) ≤ T := by
    obtain ⟨n, hc, V, hWV, hent⟩ := hsW R₀ hR₀.2
    exact le_trans (r.clk_le_of_le (Nat.find_min' hexW ⟨R₀, hR₀.2, V, hWV, hent⟩)) hc
  have hNW : N₀ < Nat.find hexW := by
    obtain ⟨i, hi, V, hWV, hent⟩ := Nat.find_spec hexW
    exact hlateAbove _ hMW _ i V hi hWV hent
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hexW = m + 1 := ⟨Nat.find hexW - 1, by omega⟩
  have hnone : ∀ (i : node) (V : view), ¬ nset.is_byz i = true → vord.le (vfin.succ PV) V →
      ¬ (r.at' m).entered i V = true := fun i V hi hWV hent =>
    Nat.find_min hexW (m := m) (by omega) ⟨i, hi, V, hWV, hent⟩
  obtain ⟨i₀, hi₀, V₀, hWV₀, hent₀⟩ := Nat.find_spec hexW
  rw [hm] at hent₀
  have hV₀ : V₀ = vfin.succ PV := entered_eq_of_first_above r.toLRun hnone hi₀ hWV₀ hent₀
  subst hV₀
  rw [← hm] at hent₀
  have hfirst : ∀ (n : Nat) (i : node) (V : view), ¬ nset.is_byz i = true →
      vord.le (vfin.succ PV) V → (r.at' n).entered i V = true → Nat.find hexW ≤ n :=
    fun n i V hi hWV h => Nat.find_min' hexW ⟨i, hi, V, hWV, h⟩
  have hgstW : r.gst ≤ r.clk (Nat.find hexW) := le_trans hgu (le_of_lt (hafter _ hNW))
  /- `N_P`, the first index at which a correct validator is at or above `PV`,
  and the one-view retention at `N_W`. -/
  have hexP : ∃ n, ∃ i, ¬ nset.is_byz i = true ∧ ∃ V, vord.le PV V ∧
      (r.at' n).entered i V = true :=
    ⟨Nat.find hexW, i₀, hi₀, vfin.succ PV, ((vord.le_lt _ _).mp hPVW).1, hent₀⟩
  have hNP : N₀ < Nat.find hexP := by
    obtain ⟨i, hi, V, hPVV, hent⟩ := Nat.find_spec hexP
    exact hlateAbove PV hMPV _ i V hi hPVV hent
  obtain ⟨mP, hmP⟩ : ∃ m, Nat.find hexP = m + 1 := ⟨Nat.find hexP - 1, by omega⟩
  have hnoneP : ∀ (i : node) (V : view), ¬ nset.is_byz i = true → vord.le PV V →
      ¬ (r.at' mP).entered i V = true := fun i V hi hPVV hent =>
    Nat.find_min hexP (m := mP) (by omega) ⟨i, hi, V, hPVV, hent⟩
  obtain ⟨iP, hiP, VP, hPVP, hentP⟩ := Nat.find_spec hexP
  rw [hmP] at hentP
  have hVP : VP = PV := entered_eq_of_first_above r.toLRun hnoneP hiP hPVP hentP
  subst hVP
  rw [← hmP] at hentP
  have hPV0 : VP ≠ vord.zero := fun h => not_le_of_lt hMPV (h ▸ vord.zero_lt M)
  obtain ⟨PPV, hPPV, -⟩ := exists_tc_pred_of_entered r.toLRun hiP hentP hPV0
  have hret := retained_before hsync hPPV (sch.τ_ramp VP hvLPV) (hfreshAbove VP hMPV)
    (fun n i V hi hPVV h => Nat.find_min' hexP ⟨i, hi, V, hPVV, h⟩) hiP hentP
    (N_W := Nat.find hexW) hi₀ hPVW hent₀
    (fun p hp => hinN p hp _ (Nat.le_of_lt hNP))
    (fun n h => hact n (le_trans h (le_trans hcNW hTB)))
  have hretW : ∀ p, ¬ nset.is_byz p = true →
      ReachedPrev (r.at' (Nat.find hexW)) p (vfin.succ VP) := by
    intro p hp
    obtain ⟨V, hPVV, n, hn, hent⟩ := hret p hp
    refine ⟨V, r.mono (P := fun s => s.entered p V = true)
      (fun k hk => Mvba.entered.mono (r.steps k) p V hk) hent _ (Nat.le_of_lt hn), ?_⟩
    by_cases hVeq : V = VP
    · exact Or.inr (hVeq ▸ vfin.next_succ VP)
    · exact Or.inl (((vord.next_def VP (vfin.succ VP)).mp (vfin.next_succ VP)).2 V
        ((vord.le_lt VP V).mpr ⟨hPVV, fun h => hVeq h.symm⟩))
  have hvLW : vord.le sch.vL (vfin.succ VP) :=
    vord.le_trans _ _ _ hvLPV ((vord.le_lt _ _).mp hPVW).1
  exact ⟨{
    PV := VP, W := vfin.succ VP, L, N := Nat.find hexW, i₀
    next := vfin.next_succ VP
    leads := hlead
    leader_correct := hL
    ramp := sch.τ_ramp _ hvLW
    i₀_correct := hi₀
    entered := hent₀
    first := hfirst
    retained := hretW
    gst_le := hgstW
    input := fun p hp => hinN p hp _ (Nat.le_of_lt hNW)
    after := hafter _ hNW
    burns := j + a + 1
    burns_le := hja
    within := by
      refine le_trans hcNW (le_of_eq ?_)
      rw [hT, hX₁, hX₀, succ_nsmul sch.burn (j + a)]
      abel }⟩

/-- **Bounded termination** ([Bounds.md](../../docs/Bounds.md) §6.2.6, "The
assembly").
`BoundedTerminationClaim`, proven, under the two quorum classes and a
cancellative time theory (§6.2.8 says why cancellation is needed). Two
cases, split at the certificate deadline `C = ℓ − (Δ + ρ)` past
`max(t, gst)`:

* a correct validator has decided by then. A decision is certificate-backed
  (`decided_backed`), and the composing layer serves a decided certificate
  to every correct validator within `Δ + ρ` of it (`within_decided_ref`,
  `lem:decision-propagation`);
* none has. Then every correct validator is active up to the deadline, and
  in the good view `exists_good_view` reaches a correct validator forms the
  commit certificate and decides inside the deadline (`good_view_decides`) —
  so this case does not occur.

The split is what the halt after deciding costs: a decided validator sends
nothing more, so the chain may use only validators that have not decided,
and a decision before the chain completes is its own route to the bound. -/
theorem bounded_termination (enum : ByzNodeSetEnum node nodeset nset)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord) :
    BoundedTerminationClaim sch vfin th := by
  intro hrot r hsync t hprop hnab q hq
  have hnab' : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true →
      r.clk n ≤ max t r.gst + sch.ℓ vfin → ¬ (r.at' n).abandoned p = true :=
    fun p n hp h hab => hnab p hp n hab h
  have hb : (0 : time) ≤ sch.burn := sch.burn_nonneg
  have hδ : (0 : time) ≤ sch.δ := sch.δ_nonneg
  have hρ : (0 : time) ≤ sch.ρ := sch.ρ_nonneg
  have hΔρ : (0 : time) ≤ sch.Δ + sch.ρ := add_nonneg (le_of_lt sch.Δ_pos) hρ
  have hL0 : (0 : time) ≤ Lcert sch.Δ sch.δ sch.Δsync :=
    add_nonneg (add_nonneg (nsmul_nonneg (le_of_lt sch.Δ_pos) 3)
      (le_trans sch.Δsync_nonneg (le_max_right _ _))) (nsmul_nonneg hδ 2)
  /- `A`, the good view's deadline, and `C`, the certificate deadline: `ℓ`
  without the final decision's transfer. -/
  obtain ⟨A, hA⟩ : ∃ A, A = (sch.Δ + sch.ρ) + 2 • sch.ρ
      + ((vfin.below sch.vL).length + sch.k) • sch.burn := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = A + Lcert sch.Δ sch.δ sch.Δsync := ⟨_, rfl⟩
  have hA0 : (0 : time) ≤ A := hA ▸ add_nonneg (add_nonneg hΔρ (nsmul_nonneg hρ 2))
    (nsmul_nonneg hb _)
  have hC0 : (0 : time) ≤ C := hC ▸ add_nonneg hA0 hL0
  have hℓ : sch.ℓ vfin = C + (sch.Δ + sch.ρ) := by simp only [Schedule.ℓ, hC, hA]
  have hgu : r.gst ≤ max t r.gst := le_max_right _ _
  have hCℓ : max t r.gst + C ≤ max t r.gst + sch.ℓ vfin := by
    rw [hℓ, ← add_assoc]; exact le_add_of_nonneg_right hΔρ
  by_cases hdec : ∃ (j : node) (n : Nat) (E : value), ¬ nset.is_byz j = true ∧
      r.clk n ≤ max t r.gst + C ∧ (r.at' n).decided j E = true
  /- A correct validator decided by the certificate deadline. A decision is
  certificate-backed, and the decided certificate reaches every correct
  validator within `Δ + ρ` of it. -/
  · obtain ⟨j, n, E, hj, hcn, hjE⟩ := hdec
    obtain ⟨V, hV⟩ := Mvba.reachable_decided_backed (r.reachable n) j E hj hjE
    obtain ⟨m, E₀, hm, hin⟩ := hprop q hq
    have hcm : r.clk m ≤ max t r.gst + C :=
      le_trans hm (le_trans (le_max_left _ _) (le_add_of_nonneg_right hC0))
    have href : r.ref (max n m) ≤ max t r.gst + C := by
      refine r.ref_le ?_ (le_trans hgu (le_add_of_nonneg_right hC0))
      rcases Nat.le_total n m with h | h
      · rw [Nat.max_eq_right h]; exact hcm
      · rw [Nat.max_eq_left h]; exact hcn
    obtain ⟨k, -, hk, E', hE'⟩ :=
      within_decided_ref hsync.2.2.2 hq hj (B := max t r.gst + sch.ℓ vfin)
        (le_trans (add_le_add href le_rfl) (le_of_eq (by rw [hℓ, add_assoc])))
        (r.mono (P := fun s => s.input q E₀ = true)
          (fun a ha => Mvba.input.mono (r.steps a) q E₀ ha) hin _ (Nat.le_max_right _ _))
        (r.mono (P := fun s => s.msg_commitqc V E = true)
          (fun a ha => Mvba.msg_commitqc.mono (r.steps a) V E ha) hV _ (Nat.le_max_left _ _))
        (r.mono (P := fun s => s.decided j E = true)
          (fun a ha => Mvba.decided.mono (r.steps a) j E ha) hjE _ (Nat.le_max_left _ _))
        (fun k _ h => hnab' q k hq h)
    exact ⟨k, E', hk, hE'⟩
  /- Nobody correct decided by the certificate deadline, so every correct
  validator is active up to it, and the good view decides. -/
  · push Not at hdec
    have hAC : max t r.gst + A ≤ max t r.gst + C :=
      add_le_add le_rfl (hC ▸ le_add_of_nonneg_right hL0)
    have hact : ∀ (p : node) (n : Nat), ¬ nset.is_byz p = true →
        r.clk n ≤ max t r.gst + ((sch.Δ + sch.ρ) + 2 • sch.ρ
          + ((vfin.below sch.vL).length + sch.k) • sch.burn) →
          Active (r.at' n) p := fun p n hp h =>
      ⟨hnab' p n hp (le_trans h (le_trans (hA ▸ hAC) hCℓ)),
        fun E hE => hdec p n E hp (le_trans h (hA ▸ hAC)) hE⟩
    obtain ⟨g⟩ := exists_good_view enum hqe sch vfin hrot hsync hprop hact
    /- The good view's certificate is inside the deadline `max(t, gst) + C`. -/
    have hEC : r.clk g.N + Lcert sch.Δ sch.δ sch.Δsync ≤ max t r.gst + C := by
      have h := nsmul_le_nsmul_left hb g.burns_le
      calc r.clk g.N + Lcert sch.Δ sch.δ sch.Δsync
          ≤ max t r.gst + (sch.Δ + sch.ρ) + 2 • sch.ρ
              + ((vfin.below sch.vL).length + sch.k) • sch.burn
              + Lcert sch.Δ sch.δ sch.Δsync := by
            gcongr
            exact le_trans g.within (add_le_add le_rfl h)
        _ = max t r.gst + C := by rw [hC, hA]; abel
    /- So some correct validator in `W` forms the commit certificate and
    decides by then — which this case says no correct validator did. -/
    obtain ⟨j, hj, n, -, hc, E, hE'⟩ :=
      good_view_decides enum hqe hsync g.next g.leads g.leader_correct g.ramp g.i₀_correct
        g.entered g.first g.retained g.gst_le g.input
        (fun p n hp h => hnab' p n hp (le_trans h (le_trans hEC hCℓ)))
    exact absurd hE' (hdec j n E hj (le_trans hc hEC))

end Assembly

/-! ## (A-viewsync), derived

`AViewSyncClaim`, proven. The second clause of (A-viewsync) only asks that a
`W`-timer does not expire before *some* correct validator has decided, so
any correct-led view above every view entered at a correct decision is a
good view: its timers are started after the decision by (T1). What is left
is to show that a correct validator decides. If a correct validator is ever
abandoned, it has decided by then (`NoEarlyAbandon`). Otherwise
`bounded_termination` applies with its abandonment premise vacuous. [Bounds.md](../../docs/Bounds.md) §6.2.8 says what this means for
(A-viewsync) as a premise. -/

section ViewSync

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {time : Type} [LinearOrder time]

/-- **A correct decision makes a good view.** If a correct validator has
decided at index `a`, then under (A-leader-rotation-k) and (T-timer) the run
satisfies `AViewSync`. The good view is the first correct-led view above
every view entered at `a`, and no timing enters the argument:

* its first clause is (T2), for every view;
* its second holds because a correct validator's `W`-timer expires only
  after it entered `W` (T1), which is after `a`, when the decision already
  stands. -/
theorem aViewSync_of_decision [AddCommMonoid time] (vfin : ViewOrderEnum view vord) {sch : Schedule view time}
    (hrot : LeaderRotation vfin sch.k th) {r : TMvbaRun th time}
    (htp : TimerPunctual sch r) {a : Nat} {p : node} {E₁ : value} (hp : ¬ nset.is_byz p = true)
    (hdec : (r.at' a).decided p E₁ = true) : AViewSync r.toLRun := by
  /- `M`, above every view entered at `a`. -/
  obtain ⟨Vs, hVs⟩ := entered_covered r.toLRun a
  obtain ⟨M, -, -, hM⟩ :=
    exists_greatest vord.le vord.le_total (fun a b c => vord.le_trans a b c) (fun _ => True)
      (vord.zero :: Vs) vord.zero (by simp) trivial
  /- `W`, the first correct-led view above `M`. -/
  obtain ⟨j, -, L, hlead, hL⟩ := hrot (vfin.succ M)
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'] at hlead
  have hMW : vord.lt M (vfin.succ (vfin.succ^[j] M)) :=
    vlt_of_le_of_lt (le_iterate_succ vfin M j) (lt_succ vfin _)
  refine ⟨vfin.succ (vfin.succ^[j] M), vfin.succ^[j] M, L, vfin.next_succ _, hlead, hL,
    fun i V hi _ ⟨n, hn⟩ => ?_, fun i n hi hte => ?_⟩
  · obtain ⟨m, -, hm, -⟩ := htp.2 n i V hi hn
    exact ⟨m, hm⟩
  · obtain ⟨n', hn'n, hlbl⟩ := exists_expire_timer_before r.toLRun hte
    obtain ⟨m, hmn', hent, -⟩ := htp.1 n' i _ hi hlbl
    have ham : a < m := by
      by_contra hle
      have hent' := r.mono (P := fun s => s.entered i (vfin.succ (vfin.succ^[j] M)) = true)
        (fun k hk => Mvba.entered.mono (r.steps k) i _ hk) hent a (Nat.le_of_not_lt hle)
      exact not_le_of_lt hMW (hM _ (List.mem_cons_of_mem _ (hVs i _ hent')) trivial)
    exact ⟨p, E₁, hp, r.mono (P := fun s => s.decided p E₁ = true)
      (fun k hk => Mvba.decided.mono (r.steps k) p E₁ hk) hdec n (by omega)⟩

/-- **(A-viewsync) from a proposal deadline.** The core of the claim, for
any node sort: if every correct validator has proposed by some time `t` and
none is abandoned before deciding, the run satisfies `AViewSync`. -/
theorem aViewSync_of_proposedBy [AddCommMonoid time] [IsOrderedCancelAddMonoid time]
    (enum : ByzNodeSetEnum node nodeset nset) (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : LeaderRotation vfin sch.k th) {r : TMvbaRun th time} (hsync : Sync sch r)
    {t : time} (hprop : ∀ p, ¬ nset.is_byz p = true →
      ∃ (n : Nat) (E : value), r.clk n ≤ t ∧ (r.at' n).input p E = true)
    (hnea : NoEarlyAbandon r.toLRun) : AViewSync r.toLRun := by
  classical
  obtain ⟨a, p, E₁, hp, hdec⟩ :
      ∃ a p E, ¬ nset.is_byz p = true ∧ (r.at' a).decided p E = true := by
    by_cases hab : ∃ p n, ¬ nset.is_byz p = true ∧ (r.at' n).abandoned p = true
    · obtain ⟨p, n, hp, h⟩ := hab
      obtain ⟨E, hE⟩ := hnea p n hp h
      exact ⟨n, p, E, hp, hE⟩
    · push Not at hab
      obtain ⟨R₀, hR₀⟩ :=
        nset.greater_than_third_one_honest hqe.honestQuorum
          (nset.supermajority_greater_than_third _ hqe.honestQuorum_supermajority)
      obtain ⟨n, E, -, hE⟩ := bounded_termination enum hqe sch vfin hrot r hsync t hprop
        (fun p hp n h => absurd h (hab p n hp)) R₀ hR₀.2
      exact ⟨n, R₀, E, hR₀.2, hE⟩
  exact aViewSync_of_decision vfin hrot hsync.2.1 hp hdec

/-- `AllPropose` over a list of validators gives one index at which all of
them have proposed: the latest of their proposals. -/
theorem exists_index_all_input {r : TMvbaRun th time} (hall : AllPropose r.toLRun) :
    ∀ xs : List node, ∃ N, ∀ p ∈ xs, ¬ nset.is_byz p = true →
      ∃ E, (r.at' N).input p E = true
  | [] => ⟨0, by simp⟩
  | p :: xs => by
    classical
    obtain ⟨N, hN⟩ := exists_index_all_input hall xs
    have hmono : ∀ {q E m m'}, m ≤ m' → (r.at' m).input q E = true →
        (r.at' m').input q E = true := fun hm h =>
      r.mono (P := fun s => s.input _ _ = true)
        (fun k hk => Mvba.input.mono (r.steps k) _ _ hk) h _ hm
    by_cases hp : nset.is_byz p = true
    · refine ⟨N, fun q hq hqc => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd hp hqc
      · exact hN q hq hqc
    · obtain ⟨n, E, hE⟩ := hall p hp
      refine ⟨max N n, fun q hq hqc => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨E, hmono (Nat.le_max_right _ _) hE⟩
      · obtain ⟨E', hE'⟩ := hN q hq hqc
        exact ⟨E', hmono (Nat.le_max_left _ _) hE'⟩

/-- **(A-viewsync) is a consequence** of the timing model: `AViewSyncClaim`,
proven for finitely many validators, under the honest-quorum class and a
cancellative time theory. The finite validator set turns `AllPropose` into a
deadline (the clock at the index `exists_index_all_input` finds) and supplies
the quorum enumeration (`ByzNodeSetEnum.ofFintype`). -/
theorem aViewSync_of_sync [AddCommMonoid time] [IsOrderedCancelAddMonoid time] [Fintype node]
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord) :
    AViewSyncClaim sch vfin th := by
  intro hrot r hsync hall hnea
  obtain ⟨N, hN⟩ := exists_index_all_input hall (Finset.univ : Finset node).toList
  exact aViewSync_of_proposedBy (ByzNodeSetEnum.ofFintype node nodeset nset) hqe sch vfin hrot
    hsync (t := r.clk N)
    (fun p hp => let ⟨E, hE⟩ := hN p (Finset.mem_toList.mpr (Finset.mem_univ p)) hp
      ⟨N, E, le_rfl, hE⟩) hnea

end ViewSync

end Mvba

/-! ## The pinned trust base

The bound, the burn lemma, and the state facts they add; the standard trio. -/

/--
info: 'Mvba.bounded_termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.bounded_termination

/--
info: 'Mvba.synced_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.synced_succ

/--
info: 'Mvba.synced_iterate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.synced_iterate

/--
info: 'Mvba.within_timed_out' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.within_timed_out

/--
info: 'Mvba.within_tc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.within_tc

/--
info: 'Mvba.within_entered_above_of_tc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.within_entered_above_of_tc

/--
info: 'Mvba.local_prepqc_set' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.local_prepqc_set

/--
info: 'Mvba.local_prepqc_new_in_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.local_prepqc_new_in_view

/--
info: 'Mvba.entered_set_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.entered_set_view

/--
info: 'Mvba.entered_covered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.entered_covered

/--
info: 'Mvba.entered_eq_of_first_above' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.entered_eq_of_first_above

/--
info: 'Mvba.exists_iterate_succ_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.exists_iterate_succ_ge

/--
info: 'Mvba.exists_good_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.exists_good_view

/--
info: 'Mvba.aViewSync_of_decision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.aViewSync_of_decision

/--
info: 'Mvba.aViewSync_of_sync' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.aViewSync_of_sync

/--
info: 'Mvba.aViewSync_of_proposedBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.aViewSync_of_proposedBy

/--
info: 'Mvba.notPast_of_no_tc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.notPast_of_no_tc

/--
info: 'Mvba.within_entered_above_of_fresh_tc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.within_entered_above_of_fresh_tc

/--
info: 'Mvba.within_entered_above_of_forwarded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.within_entered_above_of_forwarded

/--
info: 'Mvba.within_tc_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.within_tc_fresh

/--
info: 'Mvba.synced_succ_of_hops' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.synced_succ_of_hops

/--
info: 'Mvba.synced_succ_first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.synced_succ_first

/--
info: 'Mvba.retained_before' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.retained_before
