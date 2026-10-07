import Cadence.Composed.Witness.Glue
import Cadence.Composed.Witness.Orch
import Cadence.Composed.Witness.Slots
import Cadence.Composed.Concurrency

/-! # Composed.Witness — the composed claims' premises are jointly satisfiable

[ConductorBounds.md](../../docs/ConductorBounds.md) §8.2, stage K8. A
conditional theorem whose premises can never hold together proves nothing,
and the per-module witnesses do not certify the composition
([CompositionContracts.md](../../docs/CompositionContracts.md) §7,
"Vacuity does not compose"). This file exhibits **one model of the whole
composed system** — an instance, a schedule, the assumed ACS and a run —
that satisfies every premise of the four composed claims at once
([Premises.md](../../docs/Premises.md) §0):

* `corollary4_premises_satisfiable` — Corollary 4
  (`cor:chorus-correctness-within-cadence`);
* `boundedConcurrency_premises_satisfiable` — Lemma 5
  (`lemma:cadence-bounded-concurrency`);
* `liveness_premises_satisfiable` — `𝓡`-Liveness (Definition 2
  (`def:liveness`)), at both of its recovery times;
* `censorship_premises_satisfiable` — `𝓡`-Censorship resistance
  (Definition 3 (`def:censorship-resistance`)), at both of its grace periods.

Each proves the premises only, never a conclusion; the sharp forms
(`liveness_sharp`, `censorship_sharp`) take the same premises as the
paper's. The examples at the end apply each proven claim to the model, at
the claim's own instance regime: the check that the premise set shown here
is the one the claims take.

## The model

Built in [Witness/](Witness/): [Run.lean](Witness/Run.lean) (instance,
schedule, closed-form states and labels), [Steps.lean](Witness/Steps.lean)
(every step a transition), [Glue.lean](Witness/Glue.lean),
[Orch.lean](Witness/Orch.lean) and [Slots.lean](Witness/Slots.lean) (the
three parts of `SysSync`, and (P-incl)), over the generic lemmas of
[Periodic.lean](Witness/Periodic.lean) and [Actions.lean](Witness/Actions.lean)
and one slot's trajectory, [Slot.lean](Witness/Slot.lean).

* **Instance.** Four validators, validator 3 Byzantine and silent; validator
  0 proposes in every slot and leads every MVBA view; roots are `Unit`,
  every root well-encoded; slots, views, windows and time are `ℕ`.
* **Schedule.** `Δ = τ = 1`, `δ = 0`, the Chorus witness's MVBA schedule
  (`ℓ_MVBA = 24`), `ℓ_ACS = 2`, `p = 4`, `W = p + Φ_oc + ℓ_ACS = 36`; slot
  `s` starts at time `s`, its deadline `s + 1`.
* **The assumed ACS** is the ideal one ([Conductor/IdealAcs.lean](../Conductor/IdealAcs.lean)).
* **The run.** Every clock `t` is a block of 61 steps. Each correct validator
  opens slot `t`, participates in it, and validator 0 proposes, sending
  everyone its chunk; the correct validators record it. At `t + 1`, the
  slot's deadline, it goes through the fast path, each correct validator
  finalizes it, completes it at the Conductor, abandons it, appends its
  vector, and receives the correct validators' votes; at `t + 2` and `t + 3`
  its arm markers fire on a quiet instance.
  At each window's readiness boundary `36k + 4`, every correct validator
  proposes slot `36(k + 1)` to the next window's ACS, which decides at once,
  the interval `[36(k + 1), 36(k + 1) + 35]` is recorded, and everyone enters
  it. GST is 0. Every handler fires in the clock its gate opens in, so every
  row holds with nothing pending when the clock moves. -/

namespace Composed.Witness

open Cadence Conductor Chorus
open scoped Cadence.Timed
open Classical

attribute [local instance] Chorus.Witness.nsetC Chorus.Witness.cntC natViewOrder FM AS OSI SCI

/-! ## The configuration premises, at the model -/

theorem startTimes : StartTimes sch thO := fun s => by
  show s = 0 + s • 1
  simp

theorem windowShifts : WindowShifts sch thO := ⟨fun _ => rfl, fun _ => rfl⟩

theorem startsUnbounded : StartsUnbounded thO := fun t => ⟨t, le_rfl⟩

theorem hΔ : TA.Δ = sch.Δ := rfl

theorem hℓ : TA.ℓ = sch.ℓ := rfl

theorem hfault : (Finset.univ.filter (fmF 4 1 rfl isByz Chorus.Witness.hbyz).byz).card ≤ TA.fault_bound := by
  have : Finset.univ.filter (fmF 4 1 rfl isByz Chorus.Witness.hbyz).byz = {3} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [byz_iff, Fin.ext_iff]
    rfl
  rw [this]
  decide

theorem hprop : ∃ J, (fun j : Fin 4 => decide (j.val = 0)) J = true := ⟨0, rfl⟩

/-- (A-leader-rotation-k) at `k = 1`: validator 0 leads every view. -/
theorem hrot : Mvba.LeaderRotation (nset := byzNodeSetFin 4 1 rfl isByz Chorus.Witness.hbyz)
    natViewOrderEnum sch.mvba.k
    (Cadence.mvbaTheory (nodeset := ByzNSet 4) (fun v => decide (v = Chorus.Witness.vstar))
      (fun _ l => decide (l = 0))) :=
  Chorus.Witness.rotation

/-- **The timing model of the composed run**: the glue's rows, the
Conductor's on its part, Chorus's on every started slot's part. -/
theorem sysSync : SysSync (A := AS) 4 1 rfl isByz Chorus.Witness.hbyz sch TA run :=
  ⟨glueRows, orchAdmissible, slotAdmissible⟩

/-! ## The four results -/

/-- **The premises of Corollary 4 (`cor:chorus-correctness-within-cadence`)
are jointly satisfiable** (`Corollary4Claim`, proven as `Composed.corollary4`).
Some configuration — Chorus's and the MVBA's at the system's types, a slot
proposer (`hprop`), (A-leader-rotation-k) (`hrot`), a Conductor schedule
with its four parameter assumptions and `δ = 0`, an ideal ACS — and some
composed run meet all of them at once: τ-spaced, unbounded starting times,
the ACS's `Δ` the system's, and the whole timing model `SysSync` — the
glue's rows, the Conductor's `Sync` on its part (its rows, (P-open), one
clock, every window's ACS meeting its module), and Chorus's `Admissible` on
every started slot's part. -/
theorem corollary4_premises_satisfiable :
    ∃ (sch : ConductorSchedule ℕ ℕ natViewOrderEnum)
      (TA : ACSTemporal (Fin 4) ℕ ACSt ℕ Unit (fmF 4 1 rfl isByz Chorus.Witness.hbyz).byz)
      (thO : Conductor.Theory ℕ ℕ ℕ (Fin 4) ACSt)
      (is_proposer : Fin 4 → Bool) (well_encoded : Unit → Bool) (mvba_init_state : MS)
      (mvalid : V → Bool) (mleader : ℕ → Fin 4 → Bool)
      (_ : ∃ J, is_proposer J = true)
      (_ : Mvba.LeaderRotation (nset := byzNodeSetFin 4 1 rfl isByz Chorus.Witness.hbyz)
        natViewOrderEnum sch.mvba.k (Cadence.mvbaTheory (nodeset := ByzNSet 4) mvalid mleader))
      (thG : GTheory Unit ℕ Ph PC ℕ ℕ ACSt 4)
      (r : TSysRun 4 1 rfl isByz Chorus.Witness.hbyz thO
        (Cadence.chorusTheory (slot := ℕ) (Phase := Ph) (PathChoice := PC) is_proposer well_encoded
          mvba_init_state)
        (Cadence.mvbaTheory (nodeset := ByzNSet 4) mvalid mleader) thG),
      StartTimes sch thO ∧ StartsUnbounded thO ∧ TA.Δ = sch.Δ ∧
        SysSync 4 1 rfl isByz Chorus.Witness.hbyz sch TA r :=
  ⟨sch, TA, thO, _, _, mst 0, _, _, hprop, hrot, thG, run, startTimes, startsUnbounded, hΔ, sysSync⟩

/-- **The premise of Lemma 5 (`lemma:cadence-bounded-concurrency`) is
satisfiable** (`BoundedConcurrencyClaim`, proven as
`Composed.boundedConcurrency`), together with the states the claim speaks
of: windows of the schedule's shape (`WindowShifts`), and reachable states
of the composed system — every state of the run, in which every correct
validator actively participates in up to four slots at once. -/
theorem boundedConcurrency_premises_satisfiable :
    ∃ (sch : ConductorSchedule ℕ ℕ natViewOrderEnum) (thO : Conductor.Theory ℕ ℕ ℕ (Fin 4) ACSt)
      (thS : ChorusTh Unit ℕ Ph PC 4) (thM : MvbaTh Unit ℕ 4) (thG : GTheory Unit ℕ Ph PC ℕ ℕ ACSt 4)
      (r : TSysRun 4 1 rfl isByz Chorus.Witness.hbyz thO thS thM thG),
      WindowShifts sch thO ∧
        ∀ n, (sysRTS (A := AS) 4 1 rfl isByz Chorus.Witness.hbyz thO thS thM).reachable thG (r.at' n) :=
  ⟨sch, thO, thS, thM, thG, run, windowShifts, run.reachable⟩

/-- **The premises of `𝓡`-Liveness (Definition 2 (`def:liveness`)) are
jointly satisfiable** (`LivenessClaim`, proven as `Composed.liveness` at
`𝓡 = 2Wτ` and `Composed.liveness_sharp` at `(W + p − 1)τ`, on the same
premises): Corollary 4's, and the windows' shape, a successor for every
window, the ACS's latency the system's, and at most its fault bound
Byzantine. -/
theorem liveness_premises_satisfiable :
    ∃ (sch : ConductorSchedule ℕ ℕ natViewOrderEnum)
      (TA : ACSTemporal (Fin 4) ℕ ACSt ℕ Unit (fmF 4 1 rfl isByz Chorus.Witness.hbyz).byz)
      (thO : Conductor.Theory ℕ ℕ ℕ (Fin 4) ACSt)
      (is_proposer : Fin 4 → Bool) (well_encoded : Unit → Bool) (mvba_init_state : MS)
      (mvalid : V → Bool) (mleader : ℕ → Fin 4 → Bool)
      (_ : ∃ J, is_proposer J = true)
      (_ : Mvba.LeaderRotation (nset := byzNodeSetFin 4 1 rfl isByz Chorus.Witness.hbyz)
        natViewOrderEnum sch.mvba.k (Cadence.mvbaTheory (nodeset := ByzNSet 4) mvalid mleader))
      (thG : GTheory Unit ℕ Ph PC ℕ ℕ ACSt 4)
      (r : TSysRun 4 1 rfl isByz Chorus.Witness.hbyz thO
        (Cadence.chorusTheory (slot := ℕ) (Phase := Ph) (PathChoice := PC) is_proposer well_encoded
          mvba_init_state)
        (Cadence.mvbaTheory (nodeset := ByzNSet 4) mvalid mleader) thG),
      StartTimes sch thO ∧ WindowShifts sch thO ∧ StartsUnbounded thO ∧ WindowsUnbounded ℕ ∧
        TA.Δ = sch.Δ ∧ TA.ℓ = sch.ℓ ∧
        (Finset.univ.filter (fmF 4 1 rfl isByz Chorus.Witness.hbyz).byz).card ≤ TA.fault_bound ∧
        SysSync 4 1 rfl isByz Chorus.Witness.hbyz sch TA r :=
  ⟨sch, TA, thO, _, _, mst 0, _, _, hprop, hrot, thG, run, startTimes, windowShifts, startsUnbounded,
    windowsUnbounded_nat, hΔ, hℓ, hfault, sysSync⟩

/-- **The premises of `𝓡`-Censorship resistance (Definition 3
(`def:censorship-resistance`)) are jointly satisfiable** (`CensorshipClaim`,
proven as `Composed.censorship` at `2Wτ` and `Composed.censorship_sharp` at
`(W + p − 1)τ`, on the same premises): Liveness's, a well-encoded root for a
correct proposer to propose, (P-incl) on every started slot's part, and the
glue's proposer assignment Chorus's. -/
theorem censorship_premises_satisfiable :
    ∃ (sch : ConductorSchedule ℕ ℕ natViewOrderEnum)
      (TA : ACSTemporal (Fin 4) ℕ ACSt ℕ Unit (fmF 4 1 rfl isByz Chorus.Witness.hbyz).byz)
      (thO : Conductor.Theory ℕ ℕ ℕ (Fin 4) ACSt)
      (is_proposer : Fin 4 → Bool) (well_encoded : Unit → Bool) (mvba_init_state : MS)
      (mvalid : V → Bool) (mleader : ℕ → Fin 4 → Bool)
      (_ : ∃ J, is_proposer J = true)
      (_ : Mvba.LeaderRotation (nset := byzNodeSetFin 4 1 rfl isByz Chorus.Witness.hbyz)
        natViewOrderEnum sch.mvba.k (Cadence.mvbaTheory (nodeset := ByzNSet 4) mvalid mleader))
      (o : OrchSt ℕ ℕ ACSt 4) (sci : ℕ → SlotSt Unit ℕ Ph PC 4)
      (r : TSysRun 4 1 rfl isByz Chorus.Witness.hbyz thO
        (Cadence.chorusTheory (slot := ℕ) (Phase := Ph) (PathChoice := PC) is_proposer well_encoded
          mvba_init_state)
        (Cadence.mvbaTheory (nodeset := ByzNSet 4) mvalid mleader) ⟨fun j _ => is_proposer j, o, sci⟩),
      StartTimes sch thO ∧ WindowShifts sch thO ∧ StartsUnbounded thO ∧ WindowsUnbounded ℕ ∧
        TA.Δ = sch.Δ ∧ TA.ℓ = sch.ℓ ∧
        (Finset.univ.filter (fmF 4 1 rfl isByz Chorus.Witness.hbyz).byz).card ≤ TA.fault_bound ∧
        (∃ m, well_encoded m = true) ∧
        SysSync 4 1 rfl isByz Chorus.Witness.hbyz sch TA r ∧
        SlotInclusive 4 1 rfl isByz Chorus.Witness.hbyz sch r :=
  ⟨sch, TA, thO, _, _, mst 0, _, _, hprop, hrot, cond 0, fun x => (x, cst 0), run, startTimes, windowShifts,
    startsUnbounded, windowsUnbounded_nat, hΔ, hℓ, hfault, ⟨(), rfl⟩, sysSync, slotInclusive⟩

/-- **The premises of the Conductor's three timed claims are jointly
satisfiable** (`Conductor.TotalityClaim`, `Conductor.BoundednessClaim`,
`Conductor.RecoveryClaim`; [Premises.md](../../docs/Premises.md) §9), on
the orchestrator's part of the same run: the configuration premises, the
ACS's constants and fault bound, the Conductor's timing model `Sync`, and
the caller's (R-tot) and (R-term), which within the composed run are
theorems (`Composed.caller_totality`, `Composed.caller_termination`). -/
theorem conductor_premises_satisfiable :
    ∃ (sch : ConductorSchedule ℕ ℕ natViewOrderEnum)
      (TA : ACSTemporal (Fin 4) ℕ ACSt ℕ Unit (fmF 4 1 rfl isByz Chorus.Witness.hbyz).byz)
      (thO : Conductor.Theory ℕ ℕ ℕ (Fin 4) ACSt)
      (r : TConductorRun (fm := fmF 4 1 rfl isByz Chorus.Witness.hbyz) (A := AS) thO),
      StartTimes sch thO ∧ WindowShifts sch thO ∧ StartsUnbounded thO ∧ WindowsUnbounded ℕ ∧
        TA.Δ = sch.Δ ∧ TA.ℓ = sch.ℓ ∧
        (Finset.univ.filter (fmF 4 1 rfl isByz Chorus.Witness.hbyz).byz).card ≤ TA.fault_bound ∧
        Conductor.Sync sch TA r ∧
        (orchestratorSafety (fm := fmF 4 1 rfl isByz Chorus.Witness.hbyz) (acs := AS) thO).CallerTotality
          (contractRun r) sch.d_tot ∧
        (orchestratorSafety (fm := fmF 4 1 rfl isByz Chorus.Witness.hbyz) (acs := AS) thO).CallerTermination
          (contractRun r) sch.d_tot sch.ℓchorus := by
  refine ⟨sch, TA, thO, crun, startTimes, windowShifts, startsUnbounded, windowsUnbounded_nat, hΔ, hℓ, hfault,
    csync, ?_, ?_⟩
  · rw [crun_contract]
    exact caller_totality 4 1 rfl isByz Chorus.Witness.hbyz (A := AS) sch hprop hrot glueRows slotAdmissible _
  · rw [crun_contract]
    exact caller_termination 4 1 rfl isByz Chorus.Witness.hbyz (A := AS) sch TA hprop hrot glueRows
      slotAdmissible _ (crun_contract ▸ ⟨crun, rfl, csync⟩) startTimes

/-! ## The proven claims apply

Not needed for non-vacuity: these check that the model is an instance of
what each claim quantifies over, at its own instance regime, with nothing
re-bundled. -/

example := corollary4 4 1 rfl isByz Chorus.Witness.hbyz (A := AS) sch TA hprop hrot
  startTimes startsUnbounded hΔ thG run sysSync

example := boundedConcurrency 4 1 rfl isByz Chorus.Witness.hbyz (A := AS) (thO := thO) sch windowShifts
  thS thM thG

example := liveness 4 1 rfl isByz Chorus.Witness.hbyz (A := AS) sch TA hprop hrot startTimes windowShifts
  startsUnbounded windowsUnbounded_nat hΔ hℓ hfault thG run sysSync

example := liveness_sharp 4 1 rfl isByz Chorus.Witness.hbyz (A := AS) sch TA hprop hrot startTimes
  windowShifts startsUnbounded windowsUnbounded_nat hΔ hℓ hfault thG run sysSync

example := censorship 4 1 rfl isByz Chorus.Witness.hbyz (A := AS) sch TA hprop hrot startTimes windowShifts
  startsUnbounded windowsUnbounded_nat hΔ hℓ hfault ⟨(), rfl⟩ (cond 0) (fun x => (x, cst 0)) run sysSync
  slotInclusive

example := Conductor.totality sch TA thO startsUnbounded hΔ crun csync

example := Conductor.boundedness sch thO windowShifts

example := Conductor.recovery sch TA thO startTimes windowShifts startsUnbounded windowsUnbounded_nat hΔ hℓ hfault
  crun csync

example := censorship_sharp 4 1 rfl isByz Chorus.Witness.hbyz (A := AS) sch TA hprop hrot startTimes
  windowShifts startsUnbounded windowsUnbounded_nat hΔ hℓ hfault ⟨(), rfl⟩ (cond 0) (fun x => (x, cst 0))
  run sysSync slotInclusive

end Composed.Witness

/-! ## The pinned trust base -/

/--
info: 'Composed.Witness.corollary4_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.corollary4_premises_satisfiable

/--
info: 'Composed.Witness.boundedConcurrency_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.boundedConcurrency_premises_satisfiable

/--
info: 'Composed.Witness.liveness_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.liveness_premises_satisfiable

/--
info: 'Composed.Witness.conductor_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.conductor_premises_satisfiable

/--
info: 'Composed.Witness.censorship_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.censorship_premises_satisfiable
