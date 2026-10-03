import Cadence.Timed

/-! Spike 14 (2026-10-03, R24, [ConductorBounds.md](../docs/ConductorBounds.md)
F24 / K0): how a part that stops stepping is projected into the `TimedRun`
its contract's `Admissible` speaks about — before any Conductor scaffolding.

**The problem.** A contract's `TimedRun` takes a `trans` step at every index,
forever. Inside the Conductor, a window's ACS is moved only by `acs_step`
and `acs_propose`, and inside the glue a slot's consensus only by `sc_step`
(and, after K1, its inputs). Once every correct validator has abandoned the
instance, nothing has to move it again, so
[Fairness.lean](../Cadence/Fairness.lean)'s `Component.Projection`, which
needs the part stepped infinitely often (`scheduled`), has nothing to project.

**What this file establishes.** Each numbered item is a section below, and
everything is plain Lean over the contracts as they are in
[Interfaces.lean](../Cadence/Interfaces.lean); no class is edited.

1. *A contract as a transition system* (`contractRTS`): one label, `tr` the
   contract's `trans`, so that `Component` and the timed projection of
   [Timed.lean](../Cadence/Timed.lean) apply to an abstract part unchanged.
2. *The stutter lift* (`stutterSys`, `stutterComp`, `liftRun`): the
   composed run relabelled so that every composed step that is also a
   transition of the part's own contract (a real step, or a stutter its
   `trans` allows) counts as a step of the part. Same states, same clock,
   same `gst`. A part stepped only finitely often is then scheduled exactly
   when its final state can stutter (`lift_scheduled_of_finite`), and a part
   already scheduled stays scheduled (`lift_scheduled_of_scheduled`). The
   stutter is added at the projection, and it is legal only where the
   implementation's `trans` makes it so: for Chorus and the MVBA, `abandon`
   re-issued to an abandoned validator changes nothing (both actions only
   set `abandoned i`).
3. *Meaning is kept* (`partRun`, `partRun_byTime_iff`,
   `partRun_byGstBound_iff`, `partRun_forall_iff`, `partRun_eventually_iff`):
   every shape a contract field uses reads the same on the part's run and on
   the composed run, with the part's state read off each composed state.
4. *It type-checks against both classes*: `acs_termination_in` and
   `acs_totality_in` (`ACSTemporal`), `sc_termination_in`
   (`SlotConsensusTemporal`), each stated entirely in the composed run's
   vocabulary and proven from the contract field.
5. *The ACS's idle admissibility* (`Toy`, `ToyAdmissible`,
   `toy_admissible_exists`): a consumer whose admissibility asks for a
   window's ACS projection only once a correct validator has proposed to
   that window has an admissible run from every initial state, built from
   the fragment's `init_proposed` alone, with no `ACSTemporal` field and no
   use of `admissible_exists`. `toy_acs_termination` shows the premise is
   still what the consumer's proofs consume.

Expected: `exit 0`, no errors, no `sorry`. -/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Spike14

open Cadence Veil
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

/-- **ACS ℓ-Termination, in the composed run.** -/
theorem acs_termination_in (p : (stutterComp C).Projection (liftRun C r).toLRun)
    (hadm : TA.Admissible (partRun p))
    (hsync : ∀ n q s, ¬ byz q → A.proposed (C.proj (r.at' n)) q s →
      ∀ q', ¬ byz q' → ∃ m, r.clk m ≤ max (r.clk n) r.gst + TA.Δ ∧
        ∃ s', A.proposed (C.proj (r.at' m)) q' s')
    (hnpa : ∀ n i, ¬ byz i → TA.abandoned (C.proj (r.at' n)) i → A.has_decided (C.proj (r.at' n)) i)
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

/-- **Slot-consensus Termination, in the composed run.** -/
theorem sc_termination_in (p : (stutterComp C).Projection (liftRun C r).toLRun)
    (hadm : ST.Admissible (partRun p))
    (hpart : ∀ i, ¬ byz i → ∃ n, ST.participating (C.proj (r.at' n)) i)
    (hab : ∀ i, ¬ byz i → ∀ n, ST.abandoned (C.proj (r.at' n)) i →
      ∃ V, SS.finalized (C.proj (r.at' n)) i V) :
    ∀ j, ¬ byz j → ∃ n, ∃ V, SS.finalized (C.proj (r.at' n)) j V := by
  intro j hj
  refine (partRun_eventually_iff p _).1
    (ST.termination (partRun p) hadm (fun i hi => (partRun_eventually_iff p _).2 (hpart i hi)) ?_ j hj)
  intro i hi
  exact (partRun_forall_iff p (fun st => ST.abandoned st i → ∃ V, SS.finalized st i V)).2 (hab i hi)

end SC

end Fields

/-! ## 5. The ACS's idle admissibility, on a toy consumer

The Conductor's shape, cut down to what F24 is about: one abstract ACS state
per window, moved by the oracle step and by the `propose` input, and a clock
moved by `tick`. Readiness, entry and the rows are left out; K6 shows that
the Conductor's rows are disabled in its idle run, as `Chorus.not_enabled_of_idle`
does for Chorus. -/

section Toy

variable {V W Sl σ time msg : Type} [DecidableEq W] {byz : V → Prop}
variable [LinearOrder time]
variable [A : ACSSafety V Sl σ byz]

/-- The toy consumer's state: one ACS state per window, and a clock. -/
structure ToyState (W σ time : Type) where
  acs : W → σ
  now : time

/-- The toy consumer's labels. -/
inductive ToyLabel (V W Sl σ time : Type) where
  | acsStep (w : W) (a : σ)
  | acsPropose (i : V) (w : W) (s : Sl) (a : σ)
  | tick (t : time)

variable (V Sl byz) in
/-- The toy consumer, as a relational transition system. -/
def Toy : RelationalTransitionSystem Unit (ToyState W σ time) (ToyLabel V W Sl σ time) where
  assumptions _ := True
  init _ s := ∀ w, A.init (s.acs w)
  tr _ s l s' := match l with
    | .acsStep w a => A.step (s.acs w) a ∧ s' = ⟨Function.update s.acs w a, s.now⟩
    | .acsPropose i w sl a => A.propose (s.acs w) i sl a ∧ s' = ⟨Function.update s.acs w a, s.now⟩
    | .tick t => s.now ≤ t ∧ s' = ⟨s.acs, t⟩

/-- Window `w`'s ACS, as a component of the toy consumer. -/
def acsComp (w : W) : Component (Toy V Sl byz (W := W) (σ := σ) (time := time)) ()
    (contractRTS A.toTransitionSystemSafety) () where
  proj s := s.acs w
  isSub l := match l with
    | .acsStep w' _ => w' = w
    | .acsPropose _ w' _ _ => w' = w
    | .tick _ => False
  init s _ hi := ⟨trivial, hi w⟩
  frame s l s' h hl := by
    cases l with
    | acsStep w' a =>
      obtain ⟨-, rfl⟩ := h
      exact Function.update_of_ne (Ne.symm hl) _ _
    | acsPropose i w' sl a =>
      obtain ⟨-, rfl⟩ := h
      exact Function.update_of_ne (Ne.symm hl) _ _
    | tick t =>
      obtain ⟨-, rfl⟩ := h
      rfl
  step s l s' h hl := by
    cases l with
    | acsStep w' a =>
      obtain ⟨hs, rfl⟩ := h
      cases hl
      refine ⟨(), ?_⟩
      show A.trans (s.acs w) (Function.update s.acs w a w)
      rw [Function.update_self]
      exact A.step_trans _ _ hs
    | acsPropose i w' sl a =>
      obtain ⟨hs, rfl⟩ := h
      cases hl
      refine ⟨(), ?_⟩
      show A.trans (s.acs w) (Function.update s.acs w a w)
      rw [Function.update_self]
      exact A.propose_trans _ _ _ _ hs
    | tick t => exact absurd hl id

variable [AddCommMonoid time] [IsOrderedAddMonoid time]
variable [TA : ACSTemporal V Sl σ time msg byz]

/-- **The toy consumer's admissibility**: the run's clock is the consumer's,
and **once a correct validator has proposed to window `w`'s ACS**, that ACS's
part run — the lifted projection, stutters included where the ACS's `trans`
allows them — exists and is admissible. -/
def ToyAdmissible (r : TLRun (Toy V Sl byz (W := W) (σ := σ) (time := time)) () time) : Prop :=
  (∀ n, r.clk n = (r.at' n).now) ∧
  ∀ w, (∃ n i s, ¬ byz i ∧ A.proposed ((r.at' n).acs w) i s) →
    ∃ p : (stutterComp (acsComp (byz := byz) (V := V) (Sl := Sl) w)).Projection
        (liftRun (acsComp w) r).toLRun,
      TA.Admissible (partRun p)

/-- **The idle run is admissible, from every initial state, for every ACS.**
Only the clock moves; no window's ACS is touched, so no correct validator
ever proposes (`init_proposed`), and the conditional premise holds
vacuously. No `ACSTemporal` field is used, `admissible_exists` included. The
clock sequence is a parameter, as `Chorus.idleClk` is for Chorus. -/
theorem toy_admissible_exists (c : Nat → time) (hc : Monotone c) (hu : ∀ t, ∃ n, t ≤ c n)
    (s₀ : ToyState W σ time) (hi : (Toy V Sl byz).init () s₀) (h₀ : s₀.now = c 0) :
    ∃ r : TLRun (Toy V Sl byz (W := W) (σ := σ) (time := time)) () time,
      ToyAdmissible (TA := TA) r ∧ r.at' 0 = s₀ := by
  let r : TLRun (Toy V Sl byz (W := W) (σ := σ) (time := time)) () time :=
    { at' := fun n => ⟨s₀.acs, c n⟩
      lbl := fun n => .tick (c (n + 1))
      holds := trivial
      starts := hi
      steps := fun n => ⟨hc (Nat.le_succ n), rfl⟩
      clk := c
      clk_mono := fun n => hc (Nat.le_succ n)
      clk_unbounded := hu
      gst := c 0 }
  refine ⟨r, ⟨fun n => rfl, fun w ⟨n, i, s, hci, hp⟩ => ?_⟩, ?_⟩
  · exact absurd hp (A.init_proposed _ i s (hi w))
  · cases s₀
    simp only [r, ToyState.mk.injEq, true_and]
    exact h₀.symm

/-- **The premise is what the consumer's proofs consume**: in an admissible
run, once a correct validator has proposed to window `w`, ACS Termination
holds for `w` in the consumer's own vocabulary. -/
theorem toy_acs_termination {r : TLRun (Toy V Sl byz (W := W) (σ := σ) (time := time)) () time}
    (hadm : ToyAdmissible (TA := TA) r) (w : W)
    (hstart : ∃ n i s, ¬ byz i ∧ A.proposed ((r.at' n).acs w) i s)
    (hsync : ∀ n q s, ¬ byz q → A.proposed ((r.at' n).acs w) q s →
      ∀ q', ¬ byz q' → ∃ m, r.clk m ≤ max (r.clk n) r.gst + TA.Δ ∧
        ∃ s', A.proposed ((r.at' m).acs w) q' s')
    (hnpa : ∀ n i, ¬ byz i → TA.abandoned ((r.at' n).acs w) i → A.has_decided ((r.at' n).acs w) i)
    (t : time) (hprop : ∀ i, ¬ byz i → ∃ n, r.clk n ≤ t ∧ ∃ s, A.proposed ((r.at' n).acs w) i s) :
    ∀ j, ¬ byz j → ∃ n, r.clk n ≤ max t r.gst + TA.ℓ ∧ A.has_decided ((r.at' n).acs w) j := by
  obtain ⟨p, hp⟩ := hadm.2 w hstart
  exact acs_termination_in p hp hsync hnpa t hprop

end Toy

end Spike14

/-! ## The trust base

Nothing assumed beyond the standard trio. -/

/--
info: 'Spike14.acs_termination_in' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike14.acs_termination_in

/--
info: 'Spike14.sc_termination_in' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike14.sc_termination_in

/--
info: 'Spike14.toy_admissible_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike14.toy_admissible_exists

/--
info: 'Spike14.lift_scheduled_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike14.lift_scheduled_of_finite
