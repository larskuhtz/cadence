import Cadence.Mvba.BoundedTermination
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Mvba.Temporal — the timed `MVBATemporal` instance, and the full `MVBA`

[Bounds.md](../../docs/Bounds.md) §6.2, step 4. The contract's
temporal level, instantiated at `mvbaSafety th`, the fragment Chorus
consumes. Its fields:

* **`Admissible`** is `Schedule.Admissible sch th`: the run has a labelling
  satisfying the clauses of `Sync`;
* **`ℓ`** is `Schedule.ℓ sch vfin`, a closed term in the schedule's constants;
* **`termination`** is `bounded_termination`, read through `Admissible`'s
  labelling (`timed_termination`);
* **`admissible_exists`** is the run in which nobody proposes and the
  environment only marks availability (`admissible_exists`).

`mvbaFull` joins it with the fragment into the full `MVBA` class, through
[Mvba/Compose.lean](Compose.lean)'s `mvba_of_temporal`, and `mvbaFull_toSafety` checks
that the join hands back `mvbaSafety th` by `rfl`. The run carries the clock
(`TimedRun.clk`), so neither the model nor the fragment has one.

## What the instance is proven from

Nothing is assumed of the protocol. The instance takes as hypotheses what
§6.2.5 says an instance must, since no run predicate can say it:

* **finitely many validators**, `[Fintype node]`: every concrete instance
  has them, and they supply the quorum enumeration the proofs use
  (`ByzNodeSetEnum.ofFintype`);
* `ByzNodeSetHonestQuorum`, a supermajority of correct validators, and
  `ViewOrderEnum`;
  these three are `Mvba.termination`'s hypotheses too;
* (A-leader-rotation-k), `LeaderRotation vfin sch.k th`;
* the time theory: a linearly ordered, **cancellative** additive monoid
  (§6.2.8's `ℕ∞` finding), and **Archimedean**, which only
  `admissible_exists` uses (§6.2.2).

The schedule `sch` carries its own hypotheses (S-cap), (S-ramp) and
`0 < Δ` as fields. -/

namespace Mvba

open Cadence
open scoped Cadence.Timed

section Witness

variable {node nodeset value evec view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited evec] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value evec view}

/-- Expose an action's transition body in `h`, as in
[Mvba/Compose.lean](Compose.lean). -/
local macro "mvba_tr" h:ident : tactic =>
  `(tactic| (simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-! ## The witness run's states

Every state of the run is **quiet**: no input, no entry, no acceptance, and
none of the four message rows the assemblies count. Quiet holds initially
(Veil's generated `<relation>.init` lemmas), and `become_avail_ready`
preserves it (the generated `<action>.frame_<relation>` lemmas). At a quiet state no label under the hop table is enabled,
because each one's guards read one of those records. -/

/-- The records whose absence disables every fair label. -/
def Quiet (s : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) : Prop :=
  (∀ i E, s.input i E = false) ∧
  (∀ i v, s.entered i v = false) ∧
  (∀ i v e, s.accepted i v e = false) ∧
  (∀ i v e, s.msg_prepare i v e = false) ∧
  (∀ i v e, s.msg_commit i v e = false) ∧
  (∀ i v w e, s.msg_timeout_qc i v w e = false) ∧
  (∀ i v, s.msg_timeout_noqc i v = false)

theorem quiet_init {s : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)}
    (h : (Mvba.relationalTransitionSystem node nodeset value evec view).init th s) : Quiet s :=
  ⟨Mvba.input.init h, Mvba.entered.init h, Mvba.accepted.init h, Mvba.msg_prepare.init h,
    Mvba.msg_commit.init h, Mvba.msg_timeout_qc.init h, Mvba.msg_timeout_noqc.init h⟩

theorem quiet_avail {s s' : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)}
    {i : node} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th s
      (.become_avail_ready i e) s') (h : Quiet s) : Quiet s' := by
  simp only [Quiet, Mvba.become_avail_ready.frame_input htr,
    Mvba.become_avail_ready.frame_entered htr, Mvba.become_avail_ready.frame_accepted htr,
    Mvba.become_avail_ready.frame_msg_prepare htr, Mvba.become_avail_ready.frame_msg_commit htr,
    Mvba.become_avail_ready.frame_msg_timeout_qc htr,
    Mvba.become_avail_ready.frame_msg_timeout_noqc htr]
  exact h

/-- **No fair label is enabled at a quiet state.** Every fair label is a
correct validator's step, and each one's guard reads that validator's
input. -/
theorem not_enabled_of_quiet {s : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)}
    (hq : Quiet s) {l : Mvba.Label node nodeset value evec view} {h : Hop} (hh : hop l = some h) :
    ¬ Enabled (Mvba.relationalTransitionSystem node nodeset value evec view) th s l := by
  obtain ⟨hin, -, -, -, -, -, -⟩ := hq
  rintro ⟨s', htr⟩
  cases l
  all_goals first
    | (simp [hop] at hh; done)
    | skip
  /- The fourteen fair labels: expose the guards and read them at the quiet
  state. Each fails on the input. -/
  all_goals mvba_tr htr
  all_goals simp +unfoldPartialApp [Veil.FieldRepresentation.get, instIsSubStateOfRefl.getFrom_id,
    hin] at htr

/-- Nor can anybody take a transferred certificate: `decide` needs the input
too. -/
theorem not_enabled_decide_of_quiet {s : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)}
    (hq : Quiet s) {i : node} {v : view} {e : value} :
    ¬ Enabled (Mvba.relationalTransitionSystem node nodeset value evec view) th s (.decide i v e) := by
  obtain ⟨hin, -, -, -, -, -, -⟩ := hq
  rintro ⟨s', htr⟩
  mvba_tr htr
  simp +unfoldPartialApp [Veil.FieldRepresentation.get, instIsSubStateOfRefl.getFrom_id,
    hin] at htr

/-- `become_avail_ready` is unguarded, so it has a successor at every
state. -/
theorem avail_enabled (s : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view))
    (i : node) (e : value) :
    ∃ s', (Mvba.relationalTransitionSystem node nodeset value evec view).tr th s
      (.become_avail_ready i e) s' := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
  exact ⟨_, rfl⟩

/-- The witness run's step: the environment marks `default`'s shares for
`default` as available. -/
noncomputable def availStep (th : Theory node nodeset value evec view)
    (s : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) :
    Mvba.State (Mvba.FieldAbstractType node nodeset value evec view) :=
  Classical.choose (avail_enabled (th := th) s default default)

theorem availStep_tr (s : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) :
    (Mvba.relationalTransitionSystem node nodeset value evec view).tr th s
      (.become_avail_ready default default) (availStep th s) :=
  Classical.choose_spec (avail_enabled (th := th) s default default)

theorem quiet_iterate {s : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)}
    (h : Quiet s) : ∀ n, Quiet ((availStep th)^[n] s)
  | 0 => h
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact quiet_avail (availStep_tr _) (quiet_iterate h n)

end Witness

/-! ## The instance -/

section Instance

variable {node nodeset value evec view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited evec] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {time : Type} [LinearOrder time] [AddCommMonoid time]

/-- The witness run from an initial state `st`: nobody proposes, the
environment only marks availability, and the clock reads `n • Δ` at index
`n`. The Archimedean axiom makes that clock unbounded. -/
noncomputable def witnessRun [IsOrderedAddMonoid time] [Archimedean time]
    (th : Theory node nodeset value evec view)
    (hth : (Mvba.relationalTransitionSystem node nodeset value evec view).assumptions th)
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view))
    (hst : (Mvba.relationalTransitionSystem node nodeset value evec view).init th st)
    (Δ : time) (hΔ : 0 < Δ) : TMvbaRun th time where
  at' n := (availStep th)^[n] st
  lbl _ := .become_avail_ready default default
  holds := hth
  starts := hst
  steps n := by
    show (Mvba.relationalTransitionSystem node nodeset value evec view).tr th _ _
      ((availStep th)^[n + 1] st)
    rw [Function.iterate_succ_apply']
    exact availStep_tr _
  clk n := n • Δ
  clk_mono n := nsmul_le_nsmul_left hΔ.le (Nat.le_succ n)
  clk_unbounded t := Archimedean.arch t hΔ
  gst := 0

/-- **(Δ-justice) holds vacuously on a run that keeps reaching a quiet
index.** If every window from every index contains an index at which no
label the hop table covers is enabled, then every clause of
`BoundedJustice` holds with its window antecedent false: each clause asks
its label to be enabled throughout its window. The window lengths are
the schedule's three, `δ`, `Δ` and `Δ + ρ`, all non-negative. -/
theorem boundedJustice_of_quiet [IsOrderedAddMonoid time] {sch : Schedule view time}
    {th : Theory node nodeset value evec view} {r : TMvbaRun th time}
    (hq : ∀ (N : Nat) (D : time), 0 ≤ D → ∃ n, N ≤ n ∧ r.clk n ≤ r.ref N + D ∧
      ∀ (l : Mvba.Label node nodeset value evec view) (h : Hop), hop l = some h →
        ¬ Enabled (Mvba.relationalTransitionSystem node nodeset value evec view) th (r.at' n) l) :
    BoundedJustice sch r := by
  have hΔ : (0 : time) ≤ sch.Δ := sch.Δ_pos.le
  have hΔρ : (0 : time) ≤ sch.Δ + sch.ρ := add_nonneg hΔ sch.ρ_nonneg
  /- One window antecedent, refuted at the quiet index inside it. -/
  have hwhile : ∀ (D : time), 0 ≤ D → ∀ (l : Mvba.Label node nodeset value evec view) (h : Hop),
      hop l = some h → ∀ C, BoundedFairWhile r D l C := fun D hD l h hh C N hen => by
    obtain ⟨n, hn, hc, hnm⟩ := hq N D hD
    exact absurd (hen n hn hc).1 (hnm l h hh)
  refine ⟨fun l hh N hen => ?_, fun l hh _ => hwhile _ hΔ l _ hh _,
    fun i pv v _ => ⟨hwhile _ hΔ _ _ rfl _, fun w e => hwhile _ hΔ _ _ rfl _⟩,
    fun i v q _ _ => ⟨fun r₀ w e => hwhile _ hΔρ _ _ rfl _, hwhile _ hΔρ _ _ rfl _⟩,
    fun i pv v => ⟨hwhile _ hΔρ _ _ rfl _, fun w e => hwhile _ hΔρ _ _ rfl _⟩⟩
  obtain ⟨n, hn, hc, hnm⟩ := hq N sch.δ sch.δ_nonneg
  exact absurd (hen n hn hc) (hnm l _ hh)

/-- **The witness run is admissible.** (Δ-justice) is vacuous because no
fair label is ever enabled (`not_enabled_of_quiet`), at index `N`
itself, which is inside every window. (T1) is vacuous because the timer never
fires, (T2) because nobody enters a view, and (Δ-avail) because nobody
accepts. This covers the three labels no proof uses (the two view-zero
labels and `sync_view_adopt`, §6.2.8's step-3 reassessment): they are fair
labels like the rest, and vacuously so. -/
theorem witnessRun_sync [IsOrderedAddMonoid time] [Archimedean time] (sch : Schedule view time)
    {th : Theory node nodeset value evec view}
    (hth : (Mvba.relationalTransitionSystem node nodeset value evec view).assumptions th)
    {st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)}
    (hst : (Mvba.relationalTransitionSystem node nodeset value evec view).init th st) :
    Sync sch (witnessRun th hth st hst sch.Δ sch.Δ_pos) := by
  have hq := quiet_iterate (th := th) (quiet_init hst)
  refine ⟨boundedJustice_of_quiet fun N D hD => ⟨N, le_rfl,
      le_trans (TLRun.clk_le_ref _ N) (le_add_of_nonneg_right hD),
      fun _ _ hh => not_enabled_of_quiet (hq N) hh⟩,
    ⟨fun n i v _ hl => ?_, fun m i v _ hent => ?_⟩, fun m i v e _ hacc => ?_,
    fun i j v e _ N hen => absurd (hen N le_rfl (TLRun.clk_le_ref _ N |>.trans
      (le_add_of_nonneg_right (add_nonneg sch.Δ_pos.le sch.ρ_nonneg)))).1
      (not_enabled_decide_of_quiet (hq N))⟩
  · cases hl
  · exact absurd hent (by simp [witnessRun, (hq m).2.1 i v])
  · exact absurd hacc (by simp [witnessRun, (hq m).2.2.1 i v e])

/-- **`admissible_exists`** — every initial state starts an admissible run:
the witness run, labelled by itself. -/
theorem admissible_exists [IsOrderedAddMonoid time] [Archimedean time] (sch : Schedule view time)
    {th : Theory node nodeset value evec view}
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view))
    (h : (mvbaSafety th).init st) :
    ∃ tr : TimedMvbaRun th time, Admissible sch th tr ∧ tr.at' 0 = st := by
  obtain ⟨hth, hst⟩ : (Mvba.relationalTransitionSystem node nodeset value evec view).assumptions th ∧
      (Mvba.relationalTransitionSystem node nodeset value evec view).init th st := h
  let r := witnessRun th hth st hst sch.Δ sch.Δ_pos
  exact ⟨r.toTimedRun (mvbaSafety th).init (mvbaSafety th).trans ⟨hth, hst⟩
      (fun n => ⟨_, r.steps n⟩),
    ⟨r, fun _ => rfl, fun _ => rfl, rfl, witnessRun_sync sch hth hst⟩, rfl⟩

/-- **`termination`** — `MVBATemporal.termination`'s statement, instantiated.
It is `bounded_termination` read through the labelling `Admissible`
provides, with `byGstBound`'s least upper bound and the abandonment
premise's written as `max t gst` (`gstLub_iff`). The caller's validity
antecedent is not used: `Mvba.propose` checks validity itself. The
observables are the model's fields by definition, so no translation is
needed. -/
theorem timed_termination [IsOrderedCancelAddMonoid time] [Fintype node]
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    {th : Theory node nodeset value evec view} (hrot : LeaderRotation vfin sch.k th) :
    ∀ tr : TimedMvbaRun th time, Admissible sch th tr →
      ∀ t : time,
        (∀ p, ¬ nset.is_byz p = true →
          tr.byTime t (fun st => ∃ v, (mvbaSafety th).proposed st p v)) →
        (∀ p, ¬ nset.is_byz p = true → ∀ n v,
          (mvbaSafety th).proposed (tr.at' n) p v → (mvbaSafety th).Valid v) →
        (∀ p, ¬ nset.is_byz p = true → ∀ n,
          (mvbaSafety th).abandoned (tr.at' n) p →
            ∃ u, TotalOrder.le t u ∧ TotalOrder.le tr.gst u ∧
              (∀ u', TotalOrder.le t u' → TotalOrder.le tr.gst u' → TotalOrder.le u u') ∧
              ¬ TotalOrder.le (tr.clk n) (u + sch.ℓ vfin)) →
        ∀ q, ¬ nset.is_byz q = true →
          tr.byGstBound t (sch.ℓ vfin)
            (fun st => ∃ v, (mvbaSafety th).decided st q v) := by
  rintro tr ⟨r, hat, hclk, hgst, hsync⟩ t hprop - hnab q hq
  rw [TimedRun.byGstBound_iff, hgst]
  obtain ⟨n, E, hc, hd⟩ :=
    bounded_termination (ByzNodeSetEnum.ofFintype node nodeset nset) hqe sch vfin hrot r hsync t
      (fun p hp => by
        obtain ⟨n, hle, v, hv⟩ := hprop p hp
        rw [hat n] at hv
        rw [hclk n] at hle
        exact ⟨n, v, hle, hv⟩)
      (fun p hp n hab hle => by
        obtain ⟨u, h₁, h₂, h₃, hnot⟩ := hnab p hp n (by rw [hat n]; exact hab)
        rw [gstLub_iff.mp ⟨h₁, h₂, h₃⟩, hclk n, hgst] at hnot
        exact hnot hle)
      q hq
  unfold TimedRun.byTime
  exact ⟨n, by rw [hclk n]; exact hc, E, by rw [hat n]; exact hd⟩

/-- **`Mvba ⊨ MVBATemporal`.** The temporal level of Module 3 (`mod:mvba`) at the
fragment Chorus consumes, `mvbaSafety th`, proven from the instance
hypotheses of §6.2.5: finitely many validators, `ByzNodeSetHonestQuorum`,
`ViewOrderEnum`, (A-leader-rotation-k), and a cancellative, Archimedean
time theory. No field of `MVBATemporal` is weakened. `Admissible` is this
development's run model (`Schedule.Admissible`), and the class leaves that
choice to the instance. -/
@[implicit_reducible]
noncomputable def mvbaTemporal [IsOrderedCancelAddMonoid time] [Archimedean time] [Fintype node]
    (th : Theory node nodeset value evec view)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : LeaderRotation vfin sch.k th) :
    MVBATemporal node value evec (Msg view value evec)
      (Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) nodeset time
      nset (fun i => nset.is_byz i = true) (S := mvbaSafety th) :=
  -- The constructor with `S` named: a `where` instance would synthesise the
  -- class's `[S : MVBASafety …]` argument by search, which finds none.
  MVBATemporal.mk (S := mvbaSafety th)
    (Admissible := Admissible sch th)
    (admissible_exists := admissible_exists sch)
    (ℓ := sch.ℓ vfin)
    (termination := timed_termination hqe sch vfin hrot)

/-- **`Mvba ⊨ MVBA`**: the full contract, the fragment and the temporal level
joined by `mvba_of_temporal`. Its safety fragment is `mvbaSafety th`, the
instance [System.lean](../System.lean) plugs into Chorus, so the MVBA the composed
system runs is this one. -/
@[implicit_reducible]
noncomputable def mvbaFull [IsOrderedCancelAddMonoid time] [Archimedean time] [Fintype node]
    (th : Theory node nodeset value evec view)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : LeaderRotation vfin sch.k th) :
    MVBA node value evec (Msg view value evec)
      (Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) nodeset time
      nset (fun i => nset.is_byz i = true) :=
  mvba_of_temporal th (mvbaTemporal th hqe sch vfin hrot)

/-- The join hands back exactly the fragment Chorus consumes. -/
theorem mvbaFull_toSafety [IsOrderedCancelAddMonoid time] [Archimedean time] [Fintype node]
    (th : Theory node nodeset value evec view)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : LeaderRotation vfin sch.k th) :
    (mvbaFull th hqe sch vfin hrot).toMVBASafety = mvbaSafety th := rfl

end Instance

/-! ## The schedule hypotheses are satisfiable

The paper's fixed known timeout at `time := ℕ`, the obvious model of the
clock: `Δ = 1`, instantaneous local steps and availability, a
retransmission interval `ρ = 1` (the supplement's `ρ_mvba = O(Δ)`), and a
timeout of `5 > Lcert 1 0 0 = 4` in every view, so the ramp is empty. The
timeout is the supplement's `T := Δ_R + 4Δ + max{Δ, Δ_sync}` at `Δ_R = 0`. `ℕ` is a
cancellative, Archimedean linearly ordered monoid, so `mvbaTemporal`'s
time theory is met too. -/

/-- A fixed-timeout schedule over `ℕ`, for any leader-rotation window `k`. -/
def Schedule.fixedNat (view : Type) [vord : TotalOrderWithMinimum view] (k : Nat) :
    Schedule view ℕ where
  Δ := 1
  δ := 0
  ρ := 1
  Δsync := 0
  τ _ := 5
  τmax := 5
  vL := vord.zero
  k := k
  Δ_pos := Nat.one_pos
  δ_nonneg := le_rfl
  ρ_nonneg := Nat.zero_le _
  Δsync_nonneg := le_rfl
  τ_nonneg _ := Nat.zero_le _
  τ_le_max _ := le_rfl
  τ_ramp _ _ := by simp [Lcert]

/-- The instance at that schedule, for every theory with a correct leader in
every `k` consecutive views. The class's `TotalOrder ℕ` here is the one
instance search finds, Veil's own, and it agrees with the bridge the
instance was built with. -/
noncomputable example {node nodeset value evec view : Type} [Fintype node]
    [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited evec] [Inhabited view]
    [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
    (th : Theory node nodeset value evec view)
    (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (vfin : ViewOrderEnum view vord) (k : Nat) (hrot : LeaderRotation vfin k th) :
    MVBATemporal node value evec (Msg view value evec)
      (Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) nodeset ℕ
      nset (fun i => nset.is_byz i = true) (S := mvbaSafety th) :=
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
info: 'Mvba.mvbaFull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaFull

/--
info: 'Mvba.mvbaFull_toSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaFull_toSafety

/--
info: 'Mvba.boundedJustice_of_quiet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.boundedJustice_of_quiet
