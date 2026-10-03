import Cadence.Timed

/-! # PartProjection — a part that stops stepping, read as a run of its contract

[ConductorBounds.md](../docs/ConductorBounds.md) F24 and §9 K0. A module
contract's `TimedRun` takes a `trans` step at every index, forever. Inside a
composed system a part is moved only by a few of the consumer's actions — a
window's ACS by `acs_step`, `acs_propose` and `enter_window` in the
Conductor, a slot's consensus by the glue's oracle step and inputs — and once
every correct validator has abandoned it, nothing has to move it again. So
[Fairness.lean](Fairness.lean)'s `Component.Projection`, which needs the part
stepped infinitely often, has nothing to project. This file is the library
form of the answer the K0 spike settled
([spikes/14_part_projection.lean](../spikes/14_part_projection.lean)): a
stutter lift at the projection, with no change to any class.

* **A contract as a transition system** (`contractRTS`): one label, whose
  transition is the contract's `trans`, so that `Component` and the timed
  projection of [Timed.lean](Timed.lean) apply to a part held abstractly.
* **The stutter lift** (`stutterSys`, `stutterComp`, `liftRun`): the
  composed run relabelled so that every composed step that is a transition
  of the part's own contract — a real step, or a stutter its `trans` allows
  — counts as a step of the part. Same states, same clock, same `gst`. A
  part stepped only finitely often is then scheduled exactly when its final
  state can stutter (`lift_scheduled_of_finite`), and a part already
  scheduled stays scheduled (`lift_scheduled_of_scheduled`). The stutter is
  read off `trans`, so it is legal only where the implementation makes it
  so.
* **The part's run** (`partRun`), a `TimedRun` of exactly the contract's
  `init` and `trans`, and **meaning is kept**: every shape a contract field
  uses — "at every index", "eventually", "by time `t`", "by
  `max(t, GST) + d`" — reads the same on the part's run and on the composed
  run, with the part's state read off each composed state
  (`partRun_forall_iff`, `partRun_eventually_iff`, `partRun_byTime_iff`,
  `partRun_byGstBound_iff`, `partRun_byGst_at`, `composed_byGst_of_cover`).
* **Two contracts' fields, read in the composed run**: the ACS's
  ℓ-Termination and Δ-Totality (`acs_termination_in`, `acs_totality_in`)
  and slot-consensus Termination (`sc_termination_in`), each stated wholly
  in the composed run's vocabulary and proven from the contract field.

Nothing here is assumed: these are definitions and lemmas about them. The
premise that uses them — a started part's run is admissible for its
contract — is stated by each consumer: the Conductor's is `AcsAdmissible` in
[Conductor/Schedule.lean](Conductor/Schedule.lean). -/

namespace Cadence

open Veil
open scoped Cadence.Timed

/-! ## 1. A contract as a one-label transition system -/

/-- The contract's transitions as a Veil relational transition system with a
single label. A `Component` into it is a part held abstractly by a consumer. -/
def contractRTS {σ : Type} (T : TransitionSystemSafety σ) : RelationalTransitionSystem Unit σ Unit where
  assumptions _ := True
  init _ := T.init
  tr _ s _ s' := T.trans s s'

/-! ## 2. The stutter lift -/

section Lift

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {σ' : Type} {T : TransitionSystemSafety σ'}
variable {time : Type} [LinearOrder time]

/-- The composed system with every label in two copies: `.inl l` is `l` taken
while the part stays put and is not stepped, `.inr l` is `l` taken while the
part makes one transition of its contract — a real step, or a stutter its
`trans` allows. -/
def stutterSys (C : Component sys th (contractRTS T) ()) :
    RelationalTransitionSystem ρ σ (lbl ⊕ lbl) where
  assumptions := sys.assumptions
  init := sys.init
  tr th' s l s' := match l with
    | .inl l => sys.tr th' s l s' ∧ ¬ C.isSub l
    | .inr l => sys.tr th' s l s' ∧ T.trans (C.proj s) (C.proj s')

/-- The part, as a component of the relabelled system: its steps are the
`.inr` copies. -/
def stutterComp (C : Component sys th (contractRTS T) ()) :
    Component (stutterSys C) th (contractRTS T) () where
  proj := C.proj
  isSub l := match l with
    | .inl _ => False
    | .inr _ => True
  init s ha hi := C.init s ha hi
  frame s l s' h hl := by
    cases l with
    | inl l => exact C.frame s l s' h.1 h.2
    | inr l => exact absurd trivial hl
  step s l s' h hl := by
    cases l with
    | inl l => exact absurd hl id
    | inr l => exact ⟨(), h.2⟩

open Classical in
/-- **The lifted run**: the composed run's states, clock and `gst`, with each
step labelled `.inr` exactly when it is a transition of the part's contract.
A real step of the part always is (`Component.step`), so `.inl` steps leave
the part alone. -/
noncomputable def liftRun (C : Component sys th (contractRTS T) ()) (r : TLRun sys th time) :
    TLRun (stutterSys C) th time where
  at' := r.at'
  lbl n := if T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1))) then .inr (r.lbl n) else .inl (r.lbl n)
  holds := r.holds
  starts := r.starts
  steps n := by
    by_cases h : T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1)))
    · simp only [if_pos h]
      exact ⟨r.steps n, h⟩
    · simp only [if_neg h]
      refine ⟨r.steps n, fun hs => h ?_⟩
      obtain ⟨_, h'⟩ := C.step _ _ _ (r.steps n) hs
      exact h'
  clk := r.clk
  clk_mono := r.clk_mono
  clk_unbounded := r.clk_unbounded
  gst := r.gst

theorem lift_isSub_iff (C : Component sys th (contractRTS T) ()) (r : TLRun sys th time) (n : Nat) :
    (stutterComp C).isSub ((liftRun C r).lbl n) ↔ T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1))) := by
  classical
  show (stutterComp C).isSub (if _ then _ else _) ↔ _
  split <;> simp_all [stutterComp]

/-- A part that the composed run already steps infinitely often is scheduled
in the lift: nothing is lost. -/
theorem lift_scheduled_of_scheduled (C : Component sys th (contractRTS T) ()) (r : TLRun sys th time)
    (h : C.Scheduled r.toLRun) : (stutterComp C).Scheduled (liftRun C r).toLRun := by
  intro N
  obtain ⟨n, hn, hs⟩ := h N
  obtain ⟨_, h'⟩ := C.step _ _ _ (r.steps n) hs
  exact ⟨n, hn, (lift_isSub_iff C r n).2 h'⟩

/-- **A part that stops is scheduled in the lift exactly when its final state
can stutter.** If the composed run steps the part for the last time before
`N`, the part's state is constant from `N` on, and every later composed step
is a transition of the part iff `trans` relates that state to itself. -/
theorem lift_scheduled_of_finite (C : Component sys th (contractRTS T) ()) (r : TLRun sys th time)
    (N : Nat) (hN : ∀ n, N ≤ n → ¬ C.isSub (r.lbl n))
    (hst : T.trans (C.proj (r.at' N)) (C.proj (r.at' N))) :
    (stutterComp C).Scheduled (liftRun C r).toLRun := by
  intro M
  have hc : ∀ n, N ≤ n → C.proj (r.at' n) = C.proj (r.at' N) := fun n hn =>
    C.proj_eq_of_no_sub r.toLRun hn fun i hi _ => hN i hi
  refine ⟨max M N, le_max_left _ _, (lift_isSub_iff C r _).2 ?_⟩
  rw [hc _ (le_max_right _ _), hc _ (Nat.le_succ_of_le (le_max_right _ _))]
  exact hst

end Lift

/-! ## 3. The part's run, and the transfer of every shape a field uses -/

section Transfer

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {σ' : Type} {T : TransitionSystemSafety σ'}
variable {time : Type} [LinearOrder time]
variable {C : Component sys th (contractRTS T) ()} {r : TLRun sys th time}

/-- **The part's run**, as the contract's `TimedRun`: the timed projection of
the lifted run onto the lifted part. Its states are the part's states at the
composed indices where it entered them, its clock those indices' clock, its
`gst` the composed run's. -/
noncomputable def partRun (p : (stutterComp C).Projection (liftRun C r).toLRun) :
    TimedRun σ' time T.init T.trans :=
  p.timed.toTimedRun T.init T.trans p.timed.starts (fun n => p.timed.steps n)

variable (p : (stutterComp C).Projection (liftRun C r).toLRun)

theorem partRun_at' (k : Nat) : (partRun p).at' k = C.proj (r.at' (p.entry k)) :=
  p.run_at'_entry k

theorem partRun_clk (k : Nat) : (partRun p).clk k = r.clk (p.entry k) := rfl

theorem partRun_gst : (partRun p).gst = r.gst := rfl

/-- "By time `t`" means the same on the part's run and on the composed run. -/
theorem partRun_byTime_iff (t : time) (P : σ' → Prop) :
    (partRun p).byTime t P ↔ ∃ n, r.clk n ≤ t ∧ P (C.proj (r.at' n)) := by
  constructor
  · rintro ⟨k, hk, hP⟩
    exact p.timed_back hk hP
  · rintro ⟨n, hn, hP⟩
    exact p.timed_forward (r := liftRun C r) hn hP

/-- "By `max(t, GST) + d`" means the same on both runs: one `gst`. -/
theorem partRun_byGstBound_iff [Add time] (t d : time) (P : σ' → Prop) :
    (partRun p).byGstBound t d P ↔ ∃ n, r.clk n ≤ max t r.gst + d ∧ P (C.proj (r.at' n)) := by
  rw [TimedRun.byGstBound_iff, partRun_byTime_iff]
  rfl

/-- "At every index" means the same on both runs. -/
theorem partRun_forall_iff (P : σ' → Prop) :
    (∀ k, P ((partRun p).at' k)) ↔ ∀ n, P (C.proj (r.at' n)) :=
  p.always_iff P

/-- "Eventually" means the same on both runs. -/
theorem partRun_eventually_iff (P : σ' → Prop) :
    (partRun p).eventually P ↔ ∃ n, P (C.proj (r.at' n)) :=
  p.eventually_iff P

/-- The composed reading of a "from index `k`, by `max(clk k, GST) + d`"
premise gives the part's reading at `k`. -/
theorem partRun_byGst_at [Add time] (k : Nat) (d : time) (Q : σ' → Prop)
    (h : ∃ m, r.clk m ≤ max (r.clk (p.entry k)) r.gst + d ∧ Q (C.proj (r.at' m))) :
    (partRun p).byGstBound ((partRun p).clk k) d Q :=
  (partRun_byGstBound_iff p _ d Q).2 h

/-- The part's reading at the projected index covering composed index `n`
gives the composed reading from `n`: the covering state was entered no
later. -/
theorem composed_byGst_of_cover [AddCommMonoid time] [IsOrderedAddMonoid time] (n : Nat)
    (d : time) (Q : σ' → Prop)
    (h : (partRun p).byGstBound ((partRun p).clk ((stutterComp C).cover (liftRun C r).toLRun n)) d Q) :
    ∃ m, r.clk m ≤ max (r.clk n) r.gst + d ∧ Q (C.proj (r.at' m)) := by
  obtain ⟨m, hm, hQ⟩ := (partRun_byGstBound_iff p _ d Q).1 h
  refine ⟨m, le_trans hm ?_, hQ⟩
  have := (liftRun C r).clk_le_of_le (p.entry_cover_le n)
  gcongr
  exact this

/-- The part's state at the projected index covering `n` is its state at `n`. -/
theorem partRun_at'_cover (n : Nat) :
    (partRun p).at' ((stutterComp C).cover (liftRun C r).toLRun n) = C.proj (r.at' n) :=
  (p.proj_eq_run_cover n).symm

end Transfer

/-! ## 4. The contract fields, read in the composed run

Each theorem takes the part's admissibility on `partRun p` and states
everything else — the field's antecedents and its conclusion — at the
composed run. Its proof is the contract's field plus section 3. -/

section Fields

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]
variable {r : TLRun sys th time}

section ACS

variable {V Sl σ' msg : Type} {byz : V → Prop}
variable [A : ACSSafety V Sl σ' byz] [TA : ACSTemporal V Sl σ' time msg byz]
variable {C : Component sys th (contractRTS A.toTransitionSystemSafety) ()}

omit [IsOrderedAddMonoid time] in
/-- **ACS ℓ-Termination, in the composed run.** -/
theorem acs_termination_in (p : (stutterComp C).Projection (liftRun C r).toLRun)
    (hadm : TA.Admissible (partRun p))
    (hsync : ∀ n q s, ¬ byz q → A.proposed (C.proj (r.at' n)) q s →
      ∀ q', ¬ byz q' → ∃ m, r.clk m ≤ max (r.clk n) r.gst + TA.Δ ∧
        ∃ s', A.proposed (C.proj (r.at' m)) q' s')
    (hnpa : ∀ n i, ¬ byz i → A.abandoned (C.proj (r.at' n)) i → A.has_decided (C.proj (r.at' n)) i)
    (t : time) (hprop : ∀ i, ¬ byz i → ∃ n, r.clk n ≤ t ∧ ∃ s, A.proposed (C.proj (r.at' n)) i s) :
    ∀ j, ¬ byz j → ∃ n, r.clk n ≤ max t r.gst + TA.ℓ ∧ A.has_decided (C.proj (r.at' n)) j := by
  have hsync' : TA.SyncProposals (partRun p) := by
    rw [TA.syncProposals_def]
    intro k q s hq hk q' hq'
    rw [partRun_at'] at hk
    exact partRun_byGst_at p k _ _ (hsync _ q s hq hk q' hq')
  have hnpa' : TA.NoPrematureAbandon (partRun p) := by
    rw [TA.noPrematureAbandon_def]
    intro k i hi hk
    rw [partRun_at'] at hk ⊢
    exact hnpa _ i hi hk
  intro j hj
  exact (partRun_byGstBound_iff p t TA.ℓ _).1
    (TA.termination (partRun p) hadm hsync' hnpa' t
      (fun i hi => (partRun_byTime_iff p t _).2 (hprop i hi)) j hj)

/-- **ACS Δ-Totality, in the composed run** — the direction that brings a
part's conclusion "from the index where it happened" back. -/
theorem acs_totality_in (p : (stutterComp C).Projection (liftRun C r).toLRun)
    (hadm : TA.Admissible (partRun p)) (hsync : TA.SyncProposals (partRun p))
    (hnpa : TA.NoPrematureAbandon (partRun p))
    (n : Nat) (i : V) (hi : ¬ byz i) (hd : A.has_decided (C.proj (r.at' n)) i) :
    ∀ j, ¬ byz j → ∃ m, r.clk m ≤ max (r.clk n) r.gst + TA.Δ ∧ A.has_decided (C.proj (r.at' m)) j := by
  intro j hj
  have hd' : A.has_decided ((partRun p).at' ((stutterComp C).cover (liftRun C r).toLRun n)) i := by
    rw [partRun_at'_cover]; exact hd
  exact composed_byGst_of_cover p n _ _ (TA.totality (partRun p) hadm hsync hnpa _ i hi hd' j hj)

end ACS

section SC

variable {Sl V P PV σ' msg : Type} {byz : V → Prop}
variable [SS : SlotConsensusSafety Sl V P PV σ' byz] [ST : SlotConsensusTemporal Sl V P PV σ' time msg byz]
variable {C : Component sys th (contractRTS SS.toTransitionSystemSafety) ()}

omit [IsOrderedAddMonoid time] in
/-- **Slot-consensus Termination, in the composed run.** -/
theorem sc_termination_in (p : (stutterComp C).Projection (liftRun C r).toLRun)
    (hadm : ST.Admissible (partRun p))
    (hpart : ∀ i, ¬ byz i → ∃ n, SS.participating (C.proj (r.at' n)) i)
    (hab : ∀ i, ¬ byz i → ∀ n, SS.abandoned (C.proj (r.at' n)) i →
      ∃ V, SS.finalized (C.proj (r.at' n)) i V) :
    ∀ j, ¬ byz j → ∃ n, ∃ V, SS.finalized (C.proj (r.at' n)) j V := by
  intro j hj
  refine (partRun_eventually_iff p _).1
    (ST.termination (partRun p) hadm (fun i hi => (partRun_eventually_iff p _).2 (hpart i hi)) ?_ j hj)
  intro i hi
  exact (partRun_forall_iff p (fun st => SS.abandoned st i → ∃ V, SS.finalized st i V)).2 (hab i hi)

end SC

end Fields

end Cadence

/-! ## The pinned trust base

Nothing assumed beyond the standard trio. -/

/--
info: 'Cadence.liftRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.liftRun

/--
info: 'Cadence.lift_isSub_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.lift_isSub_iff

/--
info: 'Cadence.lift_scheduled_of_scheduled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.lift_scheduled_of_scheduled

/--
info: 'Cadence.lift_scheduled_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.lift_scheduled_of_finite

/--
info: 'Cadence.partRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun

/--
info: 'Cadence.partRun_at'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun_at'

/--
info: 'Cadence.partRun_clk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun_clk

/--
info: 'Cadence.partRun_gst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun_gst

/--
info: 'Cadence.partRun_byTime_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun_byTime_iff

/--
info: 'Cadence.partRun_byGstBound_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun_byGstBound_iff

/--
info: 'Cadence.partRun_forall_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun_forall_iff

/--
info: 'Cadence.partRun_eventually_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun_eventually_iff

/--
info: 'Cadence.partRun_byGst_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun_byGst_at

/--
info: 'Cadence.composed_byGst_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.composed_byGst_of_cover

/--
info: 'Cadence.partRun_at'_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.partRun_at'_cover

/--
info: 'Cadence.acs_termination_in' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.acs_termination_in

/--
info: 'Cadence.acs_totality_in' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.acs_totality_in

/--
info: 'Cadence.sc_termination_in' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.sc_termination_in
