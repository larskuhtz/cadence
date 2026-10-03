import Cadence.Conductor.Schedule

/-! # IdealAcs — the ACS contract's model, the consistency witness

[ConductorBounds.md](../../docs/ConductorBounds.md) §3.3, option (c1),
decided 2026-10-03. The Conductor's timed claims are stated for an
arbitrary ACS meeting its contract, `ACSSafety` and `ACSTemporal`
([Interfaces.lean](../Interfaces.lean)): the target leaves the ACS
unspecified (P17, [PaperAlignment.md](../../docs/PaperAlignment.md) §6), so
the ACS is an **assumed module**, named in the trust statement. An assumption
of that kind is only worth making if it can be met. This file meets it: a
plain-Lean instance of both levels of the contract, with every field proven.

**It is the class's model, not a protocol, and not the paper's ACS.** It
sends no messages, and it keeps one global decided set per instance:

* a validator's `propose(s)` records `s`, once; a Byzantine validator's
  proposal is an internal step;
* an internal step fixes the decided set, once: any set of pairs, one per
  validator, at least `2f + 1` validators, whose correct validators' pairs
  are their proposals;
* once the set is fixed, an internal step lets any validator that has
  proposed output `decide`;
* `abandon()` records itself, and an internal step may leave the state as it
  is.

Its admissible runs are, by definition, those in which the module's two
timing guarantees hold whenever its two assumptions do (`Admissible`): an
ideal functionality's timing is what it promises. So the timed fields are
immediate, and what the instance shows is that the contract's fields —
agreement, validity in both halves, integrity, one slot per validator, the
frames, the timing, and admissible runs from every initial state — hold
together. It also meets the two conditions the Conductor's claims add
(`inputsEnabled`, and `trans_refl`: a finished instance can stutter, F24).

What it is used for: the consistency of the premises of the Conductor's
timed claims, in the composed witness of K8
([ConductorBounds.md](../../docs/ConductorBounds.md) §8.2). Once a paper
revision specifies an ACS, option (a) replaces the assumption with a proof
and this file stays a witness. -/

namespace Cadence.IdealAcs

open Classical
open scoped Cadence.Timed

variable {V Sl : Type}

/-- The state of one ideal ACS instance. -/
structure State (V Sl : Type) where
  /-- Each validator's proposal, once made. -/
  prop : V → Option Sl
  /-- The decided set, once fixed: at most one slot per validator. -/
  core : Option (V → Option Sl)
  /-- The validator has output `decide`. -/
  out : V → Bool
  /-- The validator has abandoned. -/
  ab : V → Bool

section Transitions

variable (byz : V → Prop) (f : Nat)

/-- `p` proposed `s`. -/
def Proposed (st : State V Sl) (p : V) (s : Sl) : Prop := st.prop p = some s

/-- `i` has decided, with `(p, s)` in the decided set. -/
def Decided (st : State V Sl) (i p : V) (s : Sl) : Prop :=
  st.out i = true ∧ ∃ c, st.core = some c ∧ c p = some s

/-- `i` has decided. -/
def HasDecided (st : State V Sl) (i : V) : Prop := st.out i = true

/-- `i` has abandoned. -/
def Abandoned (st : State V Sl) (i : V) : Prop := st.ab i = true

/-- A decided set the instance may fix at `st`: the pairs of correct
validators are their proposals, and at least `2f + 1` distinct validators
have a pair. -/
def ValidCore (st : State V Sl) (c : V → Option Sl) : Prop :=
  (∀ p s, ¬ byz p → c p = some s → st.prop p = some s) ∧
  ∃ g : Fin (2 * f + 1) → V, Function.Injective g ∧ ∀ k, (c (g k)).isSome

/-- The initial state: nothing proposed, decided or abandoned. -/
def Init (st : State V Sl) : Prop :=
  st.prop = (fun _ => none) ∧ st.core = none ∧ st.out = (fun _ => false) ∧ st.ab = (fun _ => false)

/-- The internal steps: a stutter, a Byzantine validator's proposal, fixing
the decided set, and a validator's `decide` output. -/
def Step (st st' : State V Sl) : Prop :=
  st' = st ∨
  (∃ p s, byz p ∧ st.prop p = none ∧ st' = { st with prop := Function.update st.prop p (some s) }) ∨
  (st.core = none ∧ ∃ c, ValidCore byz f st c ∧ st' = { st with core := some c }) ∨
  (∃ i, st.core.isSome ∧ (st.prop i).isSome ∧ st' = { st with out := Function.update st.out i true })

/-- The input `propose(s)` at `p`: once. -/
def Propose (st : State V Sl) (p : V) (s : Sl) (st' : State V Sl) : Prop :=
  st.prop p = none ∧ st' = { st with prop := Function.update st.prop p (some s) }

/-- The input `abandon()` at `i`. -/
def Abandon (st : State V Sl) (i : V) (st' : State V Sl) : Prop :=
  st' = { st with ab := Function.update st.ab i true }

/-- Any transition. -/
def Trans (st st' : State V Sl) : Prop :=
  Step byz f st st' ∨ (∃ p s, Propose st p s st') ∨ ∃ i, Abandon st i st'

/-- The reachable states, over-approximated by the instance's invariant: an
output follows a fixed set and the validator's own proposal, and a fixed
set is valid. -/
def Inv (st : State V Sl) : Prop :=
  (∀ i, st.out i = true → st.core.isSome ∧ (st.prop i).isSome) ∧
  ∀ c, st.core = some c → ValidCore byz f st c

end Transitions

section Lemmas

variable {byz : V → Prop} {f : Nat}

theorem prop_mono {st st' : State V Sl} (h : Trans byz f st st') {p : V} {s : Sl}
    (hp : st.prop p = some s) : st'.prop p = some s := by
  rcases h with (rfl | ⟨q, s', -, hq, rfl⟩ | ⟨-, c, -, rfl⟩ | ⟨i, -, -, rfl⟩) | ⟨q, s', hq, rfl⟩ | ⟨i, rfl⟩
  · exact hp
  · have : p ≠ q := by rintro rfl; simp_all
    simpa [Function.update_of_ne this] using hp
  · exact hp
  · exact hp
  · have : p ≠ q := by rintro rfl; simp_all
    simpa [Function.update_of_ne this] using hp
  · exact hp

theorem core_mono {st st' : State V Sl} (h : Trans byz f st st') {c : V → Option Sl}
    (hc : st.core = some c) : st'.core = some c := by
  rcases h with (rfl | ⟨q, s', -, -, rfl⟩ | ⟨h0, -, -, rfl⟩ | ⟨i, -, -, rfl⟩) | ⟨q, s', -, rfl⟩ | ⟨i, rfl⟩
  all_goals first | exact hc | simp_all

theorem out_mono {st st' : State V Sl} (h : Trans byz f st st') {i : V}
    (ho : st.out i = true) : st'.out i = true := by
  rcases h with (rfl | ⟨q, s', -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨j, -, -, rfl⟩) | ⟨q, s', -, rfl⟩ | ⟨j, rfl⟩
  all_goals first | exact ho | (by_cases hij : i = j <;> simp_all)

theorem ab_mono {st st' : State V Sl} (h : Trans byz f st st') {i : V}
    (ha : st.ab i = true) : st'.ab i = true := by
  rcases h with (rfl | ⟨q, s', -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨j, -, -, rfl⟩) | ⟨q, s', -, rfl⟩ | ⟨j, rfl⟩
  all_goals first | exact ha | (by_cases hij : i = j <;> simp_all)

theorem validCore_mono {st st' : State V Sl} (h : Trans byz f st st') {c : V → Option Sl}
    (hv : ValidCore byz f st c) : ValidCore byz f st' c :=
  ⟨fun p s hp hc => prop_mono h (hv.1 p s hp hc), hv.2⟩

theorem inv_init {st : State V Sl} (h : Init st) : Inv byz f st := by
  obtain ⟨-, hc, ho, -⟩ := h
  refine ⟨fun i hi => ?_, fun c h' => ?_⟩
  · simp [ho] at hi
  · simp [hc] at h'

theorem inv_trans {st st' : State V Sl} (hi : Inv byz f st) (h : Trans byz f st st') :
    Inv byz f st' := by
  obtain ⟨hout, hcore⟩ := hi
  refine ⟨fun i ho => ?_, fun c hc => ?_⟩
  · rcases h with (rfl | ⟨q, s', -, hq, rfl⟩ | ⟨h0, c, -, rfl⟩ | ⟨j, hj1, hj2, rfl⟩) | ⟨q, s', hq, rfl⟩ | ⟨j, rfl⟩
    · exact hout i ho
    · obtain ⟨h1, h2⟩ := hout i ho
      refine ⟨h1, ?_⟩
      by_cases hiq : i = q
      · subst hiq; simp
      · simpa [Function.update_of_ne hiq] using h2
    · exact ⟨by simp, (hout i ho).2⟩
    · by_cases hij : i = j
      · subst hij; exact ⟨hj1, hj2⟩
      · exact hout i (by simpa [Function.update_of_ne hij] using ho)
    · obtain ⟨h1, h2⟩ := hout i ho
      refine ⟨h1, ?_⟩
      by_cases hiq : i = q
      · subst hiq; simp
      · simpa [Function.update_of_ne hiq] using h2
    · exact hout i ho
  · rcases h with (rfl | ⟨q, s', hb, hq, rfl⟩ | ⟨h0, c', hv, rfl⟩ | ⟨j, -, -, rfl⟩) | ⟨q, s', hq, rfl⟩ | ⟨j, rfl⟩
    · exact hcore c hc
    · exact validCore_mono (Or.inl (Or.inr (Or.inl ⟨q, s', hb, hq, rfl⟩))) (hcore c hc)
    · simp only [Option.some.injEq] at hc
      subst hc
      exact validCore_mono (st := st) (Or.inl (Or.inr (Or.inr (Or.inl ⟨h0, c', hv, rfl⟩)))) hv
    · exact hcore c hc
    · exact validCore_mono (Or.inr (Or.inl ⟨q, s', hq, rfl⟩)) (hcore c hc)
    · exact hcore c hc

/-- **A finished instance can stutter**: every state is related to itself,
so an instance nothing moves any more is scheduled in the stutter lift
(`lift_scheduled_of_finite`, [PartProjection.lean](../PartProjection.lean)). -/
theorem trans_refl (st : State V Sl) : Trans byz f st st :=
  Or.inl (Or.inl rfl)

end Lemmas

/-! ## The contract's fragment -/

/-- **The ideal ACS ⊨ `ACSSafety`**, for every fault pattern `byz` and
resilience `f`. -/
@[implicit_reducible]
def acsSafety (byz : V → Prop) (f : Nat) : ACSSafety V Sl (State V Sl) byz where
  init := Init
  step := Step byz f
  trans := Trans byz f
  reachable := Inv byz f
  step_trans _ _ h := Or.inl h
  reachable_init _ h := inv_init h
  reachable_trans _ _ hr h := inv_trans hr h
  propose := Propose
  abandon := Abandon
  propose_trans st p s st' h := Or.inr (Or.inl ⟨p, s, h⟩)
  abandon_trans st i st' h := Or.inr (Or.inr ⟨i, h⟩)
  proposed := Proposed
  decided := Decided
  has_decided := HasDecided
  abandoned := Abandoned
  proposed_mono _ _ _ _ h hp := prop_mono h hp
  decided_mono _ _ _ _ _ h hd := ⟨out_mono h hd.1, hd.2.choose, core_mono h hd.2.choose_spec.1,
    hd.2.choose_spec.2⟩
  has_decided_mono _ _ _ h hd := out_mono h hd
  abandoned_mono _ _ _ h ha := ab_mono h ha
  propose_effect _ _ _ _ h := by
    obtain ⟨-, rfl⟩ := h
    simp [Proposed]
  abandon_effect _ _ _ h := by
    subst h
    simp [Abandoned]
  propose_frame st p s st' q s' h _ hne := by
    obtain ⟨hp, rfl⟩ := h
    by_cases hqp : q = p
    · subst hqp
      have hs : s' ≠ s := hne.resolve_left (· rfl)
      simp [Proposed, hp, hs.symm]
    · simp [Proposed, Function.update_of_ne hqp]
  abandon_frame st i st' j h _ hne := by
    subst h
    simp [Abandoned, Function.update_of_ne hne]
  propose_abandoned_frame st p s st' j h _ := by
    obtain ⟨-, rfl⟩ := h
    rfl
  abandon_proposed_frame st i st' q s h _ := by
    subst h
    rfl
  proposed_step_frame st st' p s h hp := by
    rcases h with rfl | ⟨q, s', hq, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · rfl
    · have : p ≠ q := by rintro rfl; exact hp hq
      simp [Proposed, Function.update_of_ne this]
    · rfl
    · rfl
  abandoned_step_frame st st' i h _ := by
    rcases h with rfl | ⟨q, s', -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rfl
  init_proposed st p s h := by
    simp [Proposed, h.1]
  init_has_decided st i h := by
    simp [HasDecided, h.2.2.1]
  init_abandoned st i h := by
    simp [Abandoned, h.2.2.2]
  decided_has_decided _ _ _ _ _ _ hd := hd.1
  agreement st _ i j p s _ _ hd hj := ⟨hj, hd.2⟩
  validity_genuine st hr i p s _ hp hd := by
    obtain ⟨-, c, hc, hcp⟩ := hd
    exact (hr.2 c hc).1 p s hp hcp
  integrity st hr i _ hd := by
    obtain ⟨-, h⟩ := hr.1 i hd
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
    exact ⟨s, hs⟩
  decided_unique st _ i p s s' _ hd hd' := by
    obtain ⟨-, c, hc, hcp⟩ := hd
    obtain ⟨-, c', hc', hcp'⟩ := hd'
    rw [hc] at hc'
    cases hc'
    rw [hcp] at hcp'
    exact Option.some.inj hcp'

/-! ## The contract's temporal level -/

section Temporal

variable (byz : V → Prop) (f : Nat) {time : Type} [LinearOrder time] [AddCommMonoid time]
  (Δ ℓ : time)

/-- The module's first assumption, Δ-synchronized proposals, over this
instance's runs. -/
def SyncProposals (r : TimedRun (State V Sl) time Init (Trans byz f)) : Prop :=
  ∀ n p s, ¬ byz p → Proposed (r.at' n) p s →
    ∀ q, ¬ byz q → r.byGstBound (r.clk n) Δ (fun st => ∃ s', Proposed st q s')

/-- The module's second assumption, no premature abandonment. -/
def NoPrematureAbandon (r : TimedRun (State V Sl) time Init (Trans byz f)) : Prop :=
  ∀ n i, ¬ byz i → Abandoned (r.at' n) i → HasDecided (r.at' n) i

/-- ℓ-Termination's conclusion, over a run. -/
def Terminates (r : TimedRun (State V Sl) time Init (Trans byz f)) : Prop :=
  ∀ t, (∀ i, ¬ byz i → r.byTime t (fun st => ∃ s, Proposed st i s)) →
    ∀ j, ¬ byz j → r.byGstBound t ℓ (fun st => HasDecided st j)

/-- Δ-Totality's conclusion, over a run. -/
def DecidesTogether (r : TimedRun (State V Sl) time Init (Trans byz f)) : Prop :=
  ∀ n i, ¬ byz i → HasDecided (r.at' n) i →
    ∀ j, ¬ byz j → r.byGstBound (r.clk n) Δ (fun st => HasDecided st j)

/-- **The ideal instance's admissible runs**: whenever the module's two
assumptions hold, so do its two timing guarantees. The ideal
functionality's timing is, by definition, what it promises. -/
def Admissible (r : TimedRun (State V Sl) time Init (Trans byz f)) : Prop :=
  SyncProposals byz f Δ r → NoPrematureAbandon byz f r →
    Terminates byz f ℓ r ∧ DecidesTogether byz f Δ r

variable [IsOrderedAddMonoid time] [Archimedean time]

/-- **The ideal ACS ⊨ `ACSTemporal`**, at network bound `Δ > 0` and latency
`ℓ`, for any message type (it sends none). Admissible runs exist from every
initial state: the idle run, which stutters while the clock advances in
steps of `Δ`; nobody proposes or decides in it, so both guarantees hold. -/
@[implicit_reducible]
def acsTemporal (msg : Type) (hΔ : 0 < Δ) :
    @ACSTemporal V Sl (State V Sl) time msg _ _ byz (acsSafety byz f) :=
  letI : ACSSafety V Sl (State V Sl) byz := acsSafety byz f
  { sent _ _ _ := False,
    sent_mono _ _ _ _ _ h := h,
    Admissible := Admissible byz f Δ ℓ,
    admissible_exists st hi :=
      ⟨{ at' := fun _ => st
         starts := hi
         steps := fun _ => trans_refl st
         clk := fun n => n • Δ
         clock_mono := fun n => nsmul_le_nsmul_left hΔ.le (Nat.le_succ n)
         clock_unbounded := fun t => Archimedean.arch t hΔ
         gst := 0 },
        fun _ _ => ⟨fun t hall j hj => by
            obtain ⟨n, -, s, hs⟩ := hall j hj
            exact absurd hs (by simp [Proposed, hi.1]),
          fun n i _ hd => absurd hd (by simp [HasDecided, hi.2.2.1])⟩,
        rfl⟩,
    fault_bound := f,
    validity_quantitative st hr i _ hd := by
      obtain ⟨hc, -⟩ := hr.1 i hd
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
      obtain ⟨-, g, hg, hgk⟩ := hr.2 c hc
      refine ⟨g, hg, fun k => ?_⟩
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hgk k)
      exact ⟨s, hd, c, hc, hs⟩,
    Δ := Δ,
    ℓ := ℓ,
    SyncProposals := SyncProposals byz f Δ,
    syncProposals_def _ := Iff.rfl,
    NoPrematureAbandon := NoPrematureAbandon byz f,
    noPrematureAbandon_def _ := Iff.rfl,
    termination r hadm hs hn := (hadm hs hn).1,
    totality r hadm hs hn := (hadm hs hn).2,
    quiescence _ _ _ _ _ _ _ h _ := h.elim }

end Temporal

/-- **The ideal ACS accepts its inputs**: a correct validator that has not
proposed can propose any slot, and any validator can abandon. The premise
`AcsInputsEnabled` of the Conductor's timed claims
([Schedule.lean](Schedule.lean)) holds of it. -/
theorem inputsEnabled (byz : V → Prop) (f : Nat) :
    Conductor.AcsInputsEnabled (acsSafety (Sl := Sl) byz f) := by
  intro st _ i _
  refine ⟨fun s hnp => ⟨_, ?_, rfl⟩, ⟨_, rfl⟩⟩
  cases h : st.prop i with
  | none => rfl
  | some s' => exact absurd h (hnp s')

end Cadence.IdealAcs

/-! ## The pinned trust base -/

/--
info: 'Cadence.IdealAcs.acsSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.IdealAcs.acsSafety

/--
info: 'Cadence.IdealAcs.acsTemporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.IdealAcs.acsTemporal

/--
info: 'Cadence.IdealAcs.inputsEnabled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.IdealAcs.inputsEnabled

/--
info: 'Cadence.IdealAcs.trans_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.IdealAcs.trans_refl
