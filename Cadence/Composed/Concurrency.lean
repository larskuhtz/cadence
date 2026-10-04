import Cadence.Composed.Glue

/-! # Composed.Concurrency — Lemma 5, bounded concurrency at `𝓑 = 2W − p`

[ConductorBounds.md](../../docs/ConductorBounds.md) §9, stage K7. Lemma 5
(`lemma:cadence-bounded-concurrency`): a correct validator actively
participates in at most `𝓑` slot-consensus instances at any time. The
paper's proof reduces it to the orchestrator's `𝓑`-Boundedness through one
fact about the glue; here that fact is the glue's invariant
`[bounded_concurrency_interval]` (an active instance is opened and not
completed), and the bound is the Conductor's `2W − p` (Lemma 14
(`lem:boundedness`), `Conductor.boundedness`). Of `𝓑 + 1` active slots the
least is opened and uncompleted with `𝓑` opened slots above it, which
Boundedness excludes. A state property of the composed system: it holds at
every reachable state, so at every index of every run, with the windows'
shape as its only premise. -/

namespace Composed

open Cadence Conductor
open scoped Cadence.Timed

attribute [local instance] natSlotOrder

section Concurrency

open Classical ByzNodeSet

variable {merkle_root view Phase PathChoice window acsstate : Type}
  [Inhabited merkle_root] [Inhabited view] [Inhabited Phase] [Inhabited PathChoice]
  [Inhabited window] [Inhabited acsstate]
  [vord : TotalOrderWithMinimum view] [win_ord : TotalOrderWithMinimum window]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
  [node_inhabited : Inhabited (Fin n)]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time]
  [A : ACSSafety (Fin n) ℕ acsstate (fmF n f hf is_byz hbyz).byz]
  {vfin : ViewOrderEnum view vord}
  {thO : Conductor.Theory ℕ window time (Fin n) acsstate}
  {thS : ChorusTh merkle_root view Phase PathChoice n} {thM : MvbaTh merkle_root view n}
  {thG : GTheory merkle_root view Phase PathChoice window time acsstate n}

/-- **Lemma 5 (`lemma:cadence-bounded-concurrency`), `𝓑 = 2W − p`** — at
every reachable state of the composed system, a correct validator actively
participates in at most `𝓑 = 2W − p` slot-consensus instances: no `𝓑 + 1`
distinct slots have it participating and not yet abandoned.

The paper's proof: an instance is active exactly while its slot is opened
and not completed, and the orchestrator's `𝓑`-Boundedness bounds those. Here
the direction the bound needs is the glue's `[bounded_concurrency_interval]`,
and the bound is the Conductor's `2W − p`-Boundedness (Lemma 14
(`lem:boundedness`), `Conductor.boundedness`): of `𝓑 + 1` active slots, the
least is opened and not completed, with the other `𝓑` opened above it. Its
one premise is the windows' shape (`WindowShifts`); no run premise, no
caller condition, and nothing of Chorus. -/
theorem bounded_concurrency (sch : ConductorSchedule view time vfin) (hshift : WindowShifts sch thO)
    {st : GState ℕ (Fin n) (ℕ × (Fin n → Option merkle_root)) merkle_root
      (OrchSt window time acsstate n) (SlotSt merkle_root view Phase PathChoice n) time}
    (hr : (sysRTS n f hf is_byz hbyz (A := A) thO thS thM).reachable thG st)
    (i : Fin n) (hi : ¬ (fmF n f hf is_byz hbyz).byz i) :
    ¬ ∃ g : Fin (sch.bound + 1) → ℕ, Function.Injective g ∧
      ∀ k, (SC n f hf is_byz hbyz thS thM).participating (st.sc_state (g k)) i ∧
        ¬ (SC n f hf is_byz hbyz thS thM).abandoned (st.sc_state (g k)) i := by
  rintro ⟨g, hg, hact⟩
  have hoc := fun k => inv_bounded_concurrency (slot_ord := TotalOrderWithMinimum.toTotalOrder)
    (fm := fmF n f hf is_byz hbyz) (orch := OS n f hf is_byz hbyz (A := A) thO)
    (sc := SC n f hf is_byz hbyz thS thM) hr hi (hact k).1 (hact k).2
  obtain ⟨k0, -, hmin⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  refine Conductor.boundedness (fm := fmF n f hf is_byz hbyz) (A := A) sch thO hshift st.os
    (inv_orch_reachable (slot_ord := TotalOrderWithMinimum.toTotalOrder)
      (fm := fmF n f hf is_byz hbyz) (orch := OS n f hf is_byz hbyz (A := A) thO)
      (sc := SC n f hf is_byz hbyz thS thM) hr)
    i (g k0) hi (hoc k0).1 (hoc k0).2 ⟨g ∘ k0.succAbove, hg.comp (Fin.succAbove_right_injective),
      fun k => ⟨(hoc _).1, hmin _ (Finset.mem_univ _), fun h => Fin.succAbove_ne k0 k (hg h).symm⟩⟩

/-- **Lemma 5 (`lemma:cadence-bounded-concurrency`) at `𝓑 = 2W − p`**, as
its claim (`BoundedConcurrencyClaim`). -/
theorem boundedConcurrency (sch : ConductorSchedule view time vfin) :
    BoundedConcurrencyClaim n f hf is_byz hbyz (A := A) (Phase := Phase) (PathChoice := PathChoice)
      (merkle_root := merkle_root) sch thO :=
  fun hshift _ _ _ _ hr i hi => bounded_concurrency n f hf is_byz hbyz sch hshift hr i hi

end Concurrency

end Composed

/-! ## The pinned trust base

The standard Lean trio and nothing else: no `sorryAx`. -/

/--
info: 'Composed.bounded_concurrency' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.bounded_concurrency

/--
info: 'Composed.boundedConcurrency' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.boundedConcurrency
