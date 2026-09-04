import Cadence.Composition
import Cadence.Chorus.Compose

/-! # The composed system — the glue's theorems at the verified instances

[`Cadence.lean`](./Cadence.lean) is verified against the two module
contracts as *class constraints*: its theorems hold for every orchestrator
satisfying `OrchestratorSafety` and every slot consensus satisfying
`SlotConsensusSafety`. [`Composition.lean`](./Composition.lean) proves that
the Conductor is such an orchestrator (`Conductor.orchestratorSafety`) and
[`Chorus/Compose.lean`](./Chorus/Compose.lean) that Chorus is such a slot
consensus (`Chorus.slotConsensusSafety`). This file does the last step: it
**instantiates** the glue's end theorem at those two instances, so that the
resulting statement carries no contract hypothesis at all — it speaks about
the glue running the Conductor's and Chorus's own transition systems.

What remains as a hypothesis is exactly what genuinely is one:

* the two modules' immutable configurations (`thC`, `thS` — who is
  Byzantine, the slots' starting times, the proposers, the well-encoded
  roots), and
* that they agree on **who is Byzantine** (`hbyz`): the system's fault
  model `fm` — the one the Conductor and the glue are stated against — and
  Chorus's `ByzNodeSet.is_byz` are one fault pattern. The contracts are
  stated against one `byz`, so Chorus's instance has to be brought to it;
  this hypothesis is that transport, and it is the only place where the two
  models' notions of "correct" meet.

Nothing about the temporal obligations enters here — MCP Safety is a safety
property, and its proof needs only the two `…Safety` fragments, which are
fully proven. The residuals (`Conductor.OrchestratorResidual`,
`Chorus.SlotConsensusResidual`) are consumed by nothing in this file.

The one composition claim this file does *not* make is the one declared out
of scope throughout (`docs/ChorusDesign.md` §10.1): that running the
Conductor and Chorus *implements* the glue's oracle steps — trace-level
refinement. Here the glue's `orch_step`/`sc_step` are the modules' own
transitions, which is as close as a state-based composition comes; the
remaining seam is named in `Cadence.lean`'s header. -/

namespace Cadence
open Classical Conductor

section System

variable {slot window time node acsstate nodeset merkle_root Phase PathChoice : Type}
  [Inhabited slot] [Inhabited window] [Inhabited time] [Inhabited node] [Inhabited acsstate]
  [Inhabited nodeset] [Inhabited merkle_root] [Inhabited Phase] [Inhabited PathChoice]
  [TotalOrderWithMinimum slot] [TotalOrderWithMinimum window] [TotalOrder time]
  [fm : FaultModel node] [acs : ACSSafety node slot acsstate fm.byz]
  [nset : ByzNodeSet node nodeset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase]
  [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

/-- A contract instance stated against one fault pattern is an instance
against any propositionally equal one. Used to bring Chorus's instance
(stated against `ByzNodeSet.is_byz`) to the system's fault model. -/
@[implicit_reducible]
def SlotConsensusSafety.castByz {slot validator proposal pvector state : Type}
    {byz byz' : validator → Prop} (h : byz = byz')
    (S : SlotConsensusSafety slot validator proposal pvector state byz) :
    SlotConsensusSafety slot validator proposal pvector state byz' :=
  h ▸ S

/-- Chorus's instance, brought to the system's fault model. -/
@[implicit_reducible]
noncomputable def chorusInstance
    (thS : Chorus.Theory slot node nodeset merkle_root Phase PathChoice)
    (hbyz : ∀ i, (nset.is_byz i = true) ↔ fm.byz i) :
    SlotConsensusSafety slot node merkle_root (slot × (node → Option merkle_root))
      (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
      fm.byz :=
  SlotConsensusSafety.castByz (funext fun i => propext (hbyz i))
    (Chorus.slotConsensusSafety thS)

/-- The glue's transition system at the verified instances: slots ordered
by the Conductor's slot order, the fault model the system's `fm`, the
orchestrator state the Conductor's state, each slot's consensus state a
Chorus state, proposal vectors the tagged Chorus decision vectors. -/
noncomputable abbrev systemRTS (thC : Conductor.Theory slot window time node acsstate)
    (thS : Chorus.Theory slot node nodeset merkle_root Phase PathChoice)
    (hbyz : ∀ i, (nset.is_byz i = true) ↔ fm.byz i) :=
  @Cadence.relationalTransitionSystem slot node (slot × (node → Option merkle_root)) merkle_root
    (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
    (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    _ _ _ _ _ _ TotalOrderWithMinimum.toTotalOrder fm
    (Conductor.orchestratorSafety thC) (chorusInstance thS hbyz)

/-- **MCP Safety, positional form, for the composed system** (`def:safety`,
`lemma:cadence-safety`): in every reachable state of the glue running the
Conductor and Chorus, two correct validators never disagree on the log entry
at a given position. No contract hypothesis remains — only the two modules'
configurations and their agreement on the fault pattern. -/
theorem system_positional_log_safety
    (thC : Conductor.Theory slot window time node acsstate)
    (thS : Chorus.Theory slot node nodeset merkle_root Phase PathChoice)
    (hbyz : ∀ i, (nset.is_byz i = true) ↔ fm.byz i)
    {th : Cadence.Theory slot node (slot × (node → Option merkle_root)) merkle_root
      (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
      (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))}
    {st : Cadence.State (Cadence.FieldAbstractType slot node (slot × (node → Option merkle_root)) merkle_root
      (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
      (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)))}
    (hreach : (systemRTS thC thS hbyz).reachable th st)
    {i j : node} (hi : ¬ fm.byz i) (hj : ¬ fm.byz j)
    {Li Lj : List (slot × (slot × (node → Option merkle_root)))}
    (hLi : Cadence.IsLog st i Li) (hLj : Cadence.IsLog st j Lj) :
    ∀ k (h₁ : k < Li.length) (h₂ : k < Lj.length), Li[k]'h₁ = Lj[k]'h₂ :=
  @Cadence.positional_log_safety slot node (slot × (node → Option merkle_root)) merkle_root
    (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
    (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    _ _ _ _ _ _ TotalOrderWithMinimum.toTotalOrder fm
    (Conductor.orchestratorSafety thC) (chorusInstance thS hbyz)
    th st hreach i j hi hj Li Lj hLi hLj

end System
end Cadence

/-! ## The pinned trust base

The composed theorem rests on the standard Lean trio alone: it is the glue's
theorem applied to two kernel-checked instances, and the transport of
Chorus's instance to the system's fault model is a rewrite along a
propositional equality of predicates. -/

/--
info: 'Cadence.system_positional_log_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.system_positional_log_safety
