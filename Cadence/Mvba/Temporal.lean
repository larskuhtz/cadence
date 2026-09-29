import Cadence.Mvba.BoundedTermination
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Mvba.Temporal — the timed `MVBATemporal` instance, and the full `MVBA`

[`docs/Bounds.md`](../../docs/Bounds.md) §6.2, step 4. The contract's
temporal level, instantiated at the **lifted fragment**
`(mvbaSafety th).timed time`, which is the model's state paired with a clock
(`docs/Bounds.md` §6.2.1). Its four fields:

* **`clock`** is the second component, `Prod.snd`;
* **`Admissible`** is `Schedule.Admissible sch th`: the run has a labelling
  satisfying the three clauses of `Sync`;
* **`ℓ`** is `Schedule.ℓ sch vfin`, a closed term in the schedule's constants;
* **`termination`** is `bounded_termination`, read through `Admissible`'s
  labelling (`timed_termination`);
* **`admissible_exists`** is the run in which nobody proposes and the
  environment only marks availability (`admissible_exists`).

`mvbaTimed` joins it with the fragment into the full `MVBA` class, the way
`Mvba/Compose.lean`'s `mvba_of_temporal` does, and `mvbaTimed_toSafety`
checks that the join hands back the lifted fragment by `rfl`.

## What the instance is proven from

Nothing is assumed of the protocol. The instance takes as hypotheses what
§6.2.5 says an instance must, since no run predicate can say it:

* **finitely many validators**, `[Fintype node]`: every concrete instance
  has them, and it supplies the quorum enumeration `Mvba.termination` takes
  as the class `ByzNodeSetEnum` (`ByzNodeSetEnum.ofFintype`);
* `ByzNodeSetHonestQuorum`, a supermajority of correct validators, and
  `ViewOrderEnum`, as for `Mvba.termination`;
* (A-leader-rotation-k), `LeaderRotation vfin sch.k th`;
* the time theory: a linearly ordered, **cancellative** additive monoid
  (§6.2.8's `ℕ∞` finding), and **Archimedean**, which only
  `admissible_exists` uses (§6.2.2).

The schedule `sch` carries its own hypotheses (S-cap), (S-ramp) and
`0 < Δ` as fields.

## The seam

This instance is at the lifted fragment, and Chorus consumes
`mvbaSafety th` at `Mvba.State`, so `System.lean` does not inherit it.
`docs/Bounds.md` §6.2.1 states the seam and the proposal to the Chorus leg
for closing it. -/

namespace Mvba

open Cadence
open scoped Cadence.Timed

section Witness

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}

/-- Expose an action's transition body in `h`, as in `Mvba/Compose.lean`. -/
local macro "mvba_tr" h:ident : tactic =>
  `(tactic| (simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-! ## The witness run's states

Every state of the run is **quiet**: no input, no entry, no acceptance, and
none of the four message rows the assemblies count. Quiet holds initially
(M13's `init` lemmas), and `become_avail_ready` preserves it (M13's frame
lemmas). At a quiet state no label under the hop table is move-enabled,
because each one's guards read one of those records. -/

/-- The records whose absence disables every fair label. -/
def Quiet (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) : Prop :=
  (∀ i E, s.input i E = false) ∧
  (∀ i v, s.entered i v = false) ∧
  (∀ i v e, s.accepted i v e = false) ∧
  (∀ i v e, s.msg_prepare i v e = false) ∧
  (∀ i v e, s.msg_commit i v e = false) ∧
  (∀ i v w e, s.msg_timeout_qc i v w e = false) ∧
  (∀ i v, s.msg_timeout_noqc i v = false)

theorem quiet_init {s : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}
    (h : (Mvba.relationalTransitionSystem node nodeset value view).init th s) : Quiet s :=
  ⟨Mvba.input.init h, Mvba.entered.init h, Mvba.accepted.init h, Mvba.msg_prepare.init h,
    Mvba.msg_commit.init h, Mvba.msg_timeout_qc.init h, Mvba.msg_timeout_noqc.init h⟩

theorem quiet_avail {s s' : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}
    {i : node} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th s
      (.become_avail_ready i e) s') (h : Quiet s) : Quiet s' := by
  simp only [Quiet, Mvba.become_avail_ready.frame_input htr,
    Mvba.become_avail_ready.frame_entered htr, Mvba.become_avail_ready.frame_accepted htr,
    Mvba.become_avail_ready.frame_msg_prepare htr, Mvba.become_avail_ready.frame_msg_commit htr,
    Mvba.become_avail_ready.frame_msg_timeout_qc htr,
    Mvba.become_avail_ready.frame_msg_timeout_noqc htr]
  exact h

/-- **No fair label moves at a quiet state.** One guard per label: twelve
read an input, and the four assemblies read a message row of some member
of their quorum, which exists (`greater_than_third_one_honest`). -/
theorem not_moveEnabled_of_quiet {s : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}
    (hq : Quiet s) {l : Mvba.Label node nodeset value view} {h : Hop} (hh : hop l = some h) :
    ¬ EnabledMove (Mvba.relationalTransitionSystem node nodeset value view) th s l := by
  obtain ⟨hin, -, -, hpr, hcm, htq, htn⟩ := hq
  have member : ∀ q : nodeset, nset.supermajority q → ∃ a, nset.member a q = true := fun q hs =>
    let ⟨a, ha, _⟩ := nset.greater_than_third_one_honest q (nset.supermajority_greater_than_third q hs)
    ⟨a, ha⟩
  rintro ⟨s', htr, -⟩
  cases l
  all_goals first
    | (simp [hop] at hh; done)
    | skip
  /- The sixteen fair labels: expose the guards and read them at the quiet
  state. Twelve fail on the input and `form_tc_lock` on its named member's
  timeout message. Where `simp` does not already close an assembly over a
  quorum, it is left with a supermajority that has no member. -/
  all_goals mvba_tr htr
  all_goals simp +unfoldPartialApp [Veil.FieldRepresentation.get, instIsSubStateOfRefl.getFrom_id,
    hin, hpr, hcm, htq, htn] at htr
  all_goals obtain ⟨a, ha⟩ := member _ htr.1; simp [htr.2.1 a] at ha

/-- `become_avail_ready` is unguarded, so it has a successor at every
state. -/
theorem avail_enabled (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view))
    (i : node) (e : value) :
    ∃ s', (Mvba.relationalTransitionSystem node nodeset value view).tr th s
      (.become_avail_ready i e) s' := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
  exact ⟨_, rfl⟩

/-- The witness run's step: the environment marks `default`'s shares for
`default` as available. -/
noncomputable def availStep (th : Theory node nodeset value view)
    (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) :
    Mvba.State (Mvba.FieldAbstractType node nodeset value view) :=
  Classical.choose (avail_enabled (th := th) s default default)

theorem availStep_tr (s : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) :
    (Mvba.relationalTransitionSystem node nodeset value view).tr th s
      (.become_avail_ready default default) (availStep th s) :=
  Classical.choose_spec (avail_enabled (th := th) s default default)

theorem quiet_iterate {s : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}
    (h : Quiet s) : ∀ n, Quiet ((availStep th)^[n] s)
  | 0 => h
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact quiet_avail (availStep_tr _) (quiet_iterate h n)

end Witness

/-! ## The witness run's clock

`c`, then `max c ((n + 1) • Δ)`. The `max` is there because `c + n • Δ`,
§6.2.7's first plan, need not be unbounded: in an Archimedean monoid with
negative elements, `c + n • Δ` can stay below `0` for every `n`
(`docs/Bounds.md` §6.2.8, the step-4 reassessment, has the example). The
Archimedean axiom bounds `n • Δ` from below, and that is all this clock
needs. -/

section Clock

variable {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]

/-- The witness run's clock. -/
def witnessClock (c Δ : time) : Nat → time
  | 0 => c
  | n + 1 => max c ((n + 1) • Δ)

theorem witnessClock_mono {Δ : time} (hΔ : 0 ≤ Δ) (c : time) :
    ∀ n, witnessClock c Δ n ≤ witnessClock c Δ (n + 1)
  | 0 => le_max_left _ _
  | _ + 1 => max_le_max le_rfl (nsmul_le_nsmul_left hΔ (Nat.le_succ _))

theorem witnessClock_unbounded [Archimedean time] {Δ : time} (hΔ : 0 < Δ) (c t : time) :
    ∃ n, t ≤ witnessClock c Δ n := by
  obtain ⟨m, hm⟩ := Archimedean.arch t hΔ
  exact ⟨m + 1, le_trans hm
    (le_trans (nsmul_le_nsmul_left hΔ.le (Nat.le_succ m)) (le_max_right _ _))⟩

end Clock

/-! ## The instance -/

section Instance

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {time : Type} [LinearOrder time]

/-! ### The observables are the model's fields

The lifted fragment's observables are `mvbaSafety th`'s on the first
component, and those are the model's relations. All three facts hold by
definition, and nothing is translated. -/

theorem timed_decided_iff (th : Theory node nodeset value view)
    (st : TimedState node nodeset value view time) (q : node) (v : value) :
    ((mvbaSafety th).timed time).decided st q v ↔ st.1.decided q v = true := Iff.rfl

theorem timed_proposed_iff (th : Theory node nodeset value view)
    (st : TimedState node nodeset value view time) (q : node) (v : value) :
    ((mvbaSafety th).timed time).proposed st q v ↔ st.1.input q v = true := Iff.rfl

theorem timed_abandoned_iff (th : Theory node nodeset value view)
    (st : TimedState node nodeset value view time) (q : node) :
    ((mvbaSafety th).timed time).abandoned st q ↔ st.1.abandoned q = true := Iff.rfl

variable [AddCommMonoid time]

/-- The witness run from an initial state `st` and clock `c`: nobody
proposes, the environment only marks availability, and the clock is
`witnessClock c Δ`. -/
noncomputable def witnessRun [IsOrderedAddMonoid time] [Archimedean time] (th : Theory node nodeset value view)
    (hth : (Mvba.relationalTransitionSystem node nodeset value view).assumptions th)
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view))
    (hst : (Mvba.relationalTransitionSystem node nodeset value view).init th st)
    (c Δ : time) (hΔ : 0 < Δ) : TMvbaRun th time where
  at' n := (availStep th)^[n] st
  lbl _ := .become_avail_ready default default
  holds := hth
  starts := hst
  steps n := by
    show (Mvba.relationalTransitionSystem node nodeset value view).tr th _ _
      ((availStep th)^[n + 1] st)
    rw [Function.iterate_succ_apply']
    exact availStep_tr _
  clk := witnessClock c Δ
  clk_mono := witnessClock_mono hΔ.le c
  clk_unbounded := witnessClock_unbounded hΔ c
  gst := c

/-- **The witness run is admissible.** (Δ-justice) is vacuous because no
fair label is ever move-enabled (`not_moveEnabled_of_quiet`), at index `N`
itself, which is inside every window. (T1) is vacuous because the timer never
fires, (T2) because nobody enters a view, and (Δ-avail) because nobody
accepts. This covers the three labels no proof uses (the two view-zero
labels and `sync_view_adopt`, §6.2.8's step-3 reassessment): they are fair
labels like the rest, and vacuously so. -/
theorem witnessRun_sync [IsOrderedAddMonoid time] [Archimedean time] (sch : Schedule view time)
    {th : Theory node nodeset value view}
    (hth : (Mvba.relationalTransitionSystem node nodeset value view).assumptions th)
    {st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}
    (hst : (Mvba.relationalTransitionSystem node nodeset value view).init th st) (c : time) :
    Sync sch (witnessRun th hth st hst c sch.Δ sch.Δ_pos) := by
  have hq := quiet_iterate (th := th) (quiet_init hst)
  refine ⟨fun l h hh N hen => ?_, ⟨fun n i v _ hl => ?_, fun m i v _ hent => ?_⟩,
    fun m i v e _ hacc => ?_⟩
  · have hD : (0 : time) ≤ sch.bound h := by
      cases h
      · exact sch.Δ_pos.le
      · exact sch.δ_nonneg
    exact absurd (hen N le_rfl (le_trans (TLRun.clk_le_ref _ N) (le_add_of_nonneg_right hD)))
      (not_moveEnabled_of_quiet (hq N) hh)
  · cases hl
  · exact absurd hent (by simp [witnessRun, (hq m).2.1 i v])
  · exact absurd hacc (by simp [witnessRun, (hq m).2.2.1 i v e])

/-- **`admissible_exists`** — every initial lifted state starts an
admissible run: the witness run, labelled by itself. -/
theorem admissible_exists [IsOrderedAddMonoid time] [Archimedean time] (sch : Schedule view time)
    {th : Theory node nodeset value view} (st : TimedState node nodeset value view time)
    (h : ((mvbaSafety th).timed time).init st) :
    ∃ tr : TimedMvbaRun th time, Admissible sch th tr ∧ tr.at' 0 = st := by
  obtain ⟨s, c⟩ := st
  obtain ⟨hth, hst⟩ : (Mvba.relationalTransitionSystem node nodeset value view).assumptions th ∧
      (Mvba.relationalTransitionSystem node nodeset value view).init th s := h
  let r := witnessRun th hth s hst c sch.Δ sch.Δ_pos
  exact ⟨r.toTimedRun (mvbaSafety th) ⟨hth, hst⟩ (fun n => ⟨_, r.steps n⟩),
    ⟨r, fun _ => rfl, rfl, witnessRun_sync sch hth hst c⟩, rfl⟩

/-- **`termination` at the lifted fragment** — `MVBATemporal.termination`'s
statement, instantiated. It is `bounded_termination` read through the
labelling `Admissible` provides, with `byGstBound`'s least upper bound and
the abandonment premise's written as `max t gst` (`gstLub_iff`). -/
theorem timed_termination [IsOrderedCancelAddMonoid time] [Fintype node]
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    {th : Theory node nodeset value view} (hrot : LeaderRotation vfin sch.k th) :
    ∀ tr : TimedMvbaRun th time, Admissible sch th tr →
      ∀ t : time,
        (∀ p, ¬ nset.is_byz p = true →
          tr.byTime t (fun st => ∃ v, ((mvbaSafety th).timed time).proposed st p v)) →
        (∀ p, ¬ nset.is_byz p = true → ∀ n,
          ((mvbaSafety th).timed time).abandoned (tr.at' n) p →
            ∃ u, TotalOrder.le t u ∧ TotalOrder.le tr.gst u ∧
              (∀ u', TotalOrder.le t u' → TotalOrder.le tr.gst u' → TotalOrder.le u u') ∧
              ¬ TotalOrder.le (tr.at' n).2 (u + sch.ℓ vfin)) →
        ∀ q, ¬ nset.is_byz q = true →
          tr.byGstBound t (sch.ℓ vfin)
            (fun st => ∃ v, ((mvbaSafety th).timed time).decided st q v) := by
  rintro tr ⟨r, hat, hgst, hsync⟩ t hprop hnab q hq
  rw [TimedRun.byGstBound_iff, hgst]
  obtain ⟨n, E, hc, hd⟩ :=
    bounded_termination (ByzNodeSetEnum.ofFintype node nodeset nset) hqe sch vfin hrot r hsync t
    (fun p hp => by
      obtain ⟨n, hle, v, hv⟩ := hprop p hp
      rw [hat n] at hle hv
      exact ⟨n, v, hle, (timed_proposed_iff th _ p v).mp hv⟩)
    (fun p hp n hab hle => by
      obtain ⟨u, h₁, h₂, h₃, hnot⟩ :=
        hnab p hp n (by rw [hat n]; exact (timed_abandoned_iff th _ p).mpr hab)
      rw [gstLub_iff.mp ⟨h₁, h₂, h₃⟩, hat n, hgst] at hnot
      exact hnot hle)
    q hq
  unfold TimedRun.byTime
  exact ⟨n, by rw [hat n]; exact hc, E, by rw [hat n]; exact (timed_decided_iff th _ q E).mpr hd⟩

/-- **`Mvba ⊨ MVBATemporal`, at the lifted fragment.** The temporal level of
`mod:mvba` for the clock-carrying lift of `mvbaSafety th`, proven from the
instance hypotheses of §6.2.5: finitely many validators,
`ByzNodeSetHonestQuorum`, `ViewOrderEnum`, (A-leader-rotation-k), and a
cancellative, Archimedean time theory. No field
of `MVBATemporal` is weakened. `Admissible` is this development's run
model (`Schedule.Admissible`), and the class leaves that choice to the
instance. -/
@[implicit_reducible]
noncomputable def mvbaTemporal [IsOrderedCancelAddMonoid time] [Archimedean time] [Fintype node]
    (th : Theory node nodeset value view)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : LeaderRotation vfin sch.k th) :
    MVBATemporal node value (Msg view value) (TimedState node nodeset value view time) time
      (fun i => nset.is_byz i = true) (S := (mvbaSafety th).timed time) :=
  -- The constructor with `S` named: a `where` instance would synthesise the
  -- class's `[S : MVBASafety …]` argument by search, which finds none.
  MVBATemporal.mk (S := (mvbaSafety th).timed time)
    (clock := Prod.snd)
    (Admissible := Admissible sch th)
    (admissible_exists := admissible_exists sch)
    (ℓ := sch.ℓ vfin)
    (termination := timed_termination hqe sch vfin hrot)

/-- **`Mvba ⊨ MVBA`, at the lifted fragment**: the fragment and the
temporal level joined, as `mvba_of_temporal` joins them. Nothing is
restated. -/
@[implicit_reducible]
noncomputable def mvbaTimed [IsOrderedCancelAddMonoid time] [Archimedean time] [Fintype node]
    (th : Theory node nodeset value view)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : LeaderRotation vfin sch.k th) :
    MVBA node value (Msg view value) (TimedState node nodeset value view time) time
      (fun i => nset.is_byz i = true) :=
  { (mvbaSafety th).timed time, mvbaTemporal th hqe sch vfin hrot with }

/-- The join hands back exactly the lifted fragment. -/
theorem mvbaTimed_toSafety [IsOrderedCancelAddMonoid time] [Archimedean time] [Fintype node]
    (th : Theory node nodeset value view)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : LeaderRotation vfin sch.k th) :
    (mvbaTimed th hqe sch vfin hrot).toMVBASafety = (mvbaSafety th).timed time := rfl

end Instance

/-! ## The schedule hypotheses are satisfiable

The paper's fixed known timeout at `time := ℕ`, the obvious model of the
clock: `Δ = 1`, instantaneous local steps and availability, and a timeout
of `5 > Lcert 1 0 0 = 4` in every view, so the ramp is empty. `ℕ` is a
cancellative, Archimedean linearly ordered monoid, so `mvbaTemporal`'s
time theory is met too. -/

/-- A fixed-timeout schedule over `ℕ`, for any leader-rotation window `k`. -/
def Schedule.fixedNat (view : Type) [vord : TotalOrderWithMinimum view] (k : Nat) :
    Schedule view ℕ where
  Δ := 1
  δ := 0
  Δsync := 0
  τ _ := 5
  τmax := 5
  vL := vord.zero
  k := k
  Δ_pos := Nat.one_pos
  δ_nonneg := le_rfl
  Δsync_nonneg := le_rfl
  τ_nonneg _ := Nat.zero_le _
  τ_le_max _ := le_rfl
  τ_ramp _ _ := by simp [Lcert]

/-- The instance at that schedule, for every theory with a correct leader in
every `k` consecutive views. The class's `TotalOrder ℕ` here is the one
instance search finds, Veil's own, and it agrees with the bridge the
instance was built with. -/
noncomputable example {node nodeset value view : Type} [Fintype node]
    [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
    [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
    (th : Theory node nodeset value view)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (vfin : ViewOrderEnum view vord) (k : Nat) (hrot : LeaderRotation vfin k th) :
    MVBATemporal node value (Msg view value) (TimedState node nodeset value view ℕ) ℕ
      (fun i => nset.is_byz i = true) (S := (mvbaSafety th).timed ℕ) :=
  mvbaTemporal th hqe (Schedule.fixedNat view k) vfin hrot

end Mvba

/-! ## The pinned trust base

The instance, its two proven fields and the join; the standard trio. -/

/--
info: 'Mvba.admissible_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.admissible_exists

/--
info: 'Mvba.timed_termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.timed_termination

/--
info: 'Mvba.mvbaTemporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaTemporal

/--
info: 'Mvba.mvbaTimed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaTimed

/--
info: 'Mvba.mvbaTimed_toSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaTimed_toSafety
