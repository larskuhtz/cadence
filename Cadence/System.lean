import Cadence.Composition
import Cadence.Chorus.Compose
import Cadence.Mvba.Compose

/-! # The composed system — the glue's theorems at the verified instances

[`Cadence.lean`](./Cadence.lean) is verified against the two module
contracts as *class constraints*: its theorems hold for every orchestrator
satisfying `OrchestratorSafety` and every slot consensus satisfying
`SlotConsensusSafety`. [`Composition.lean`](./Composition.lean) proves that
the Conductor is such an orchestrator (`Conductor.orchestratorSafety`) and
[`Chorus/Compose.lean`](./Chorus/Compose.lean) that Chorus is such a slot
consensus (`Chorus.slotConsensusSafety`) — Chorus itself being verified
against the MVBA contract `MVBASafety` as a class constraint, which
[`Mvba/Compose.lean`](./Mvba/Compose.lean) instantiates from the
leader-based MVBA model (`Mvba.mvbaSafety`). This file does the last step: it
**instantiates** the glue's end theorem at those instances, with Chorus's
MVBA constraint filled by `Mvba.mvbaSafety`, so that the resulting statement
carries no contract hypothesis at all — it speaks about the glue running
the Conductor's and Chorus's own transition systems, Chorus running the
`Mvba` model's.

What remains as a hypothesis is exactly what genuinely is one:

* the three modules' immutable configurations (`thC`, `thS`, `thM` — who is
  Byzantine, the slots' starting times, the proposers, the well-encoded
  roots, the MVBA's leader schedule and validity predicate, and the
  abstract MVBA state Chorus starts from), and
* that the Conductor and Chorus agree on **who is Byzantine** (`hbyz`): the
  system's fault model `fm` — the one the Conductor and the glue are stated
  against — and Chorus's `ByzNodeSet.is_byz` are one fault pattern. The
  contracts are stated against one `byz`, so Chorus's instance has to be
  brought to it; this hypothesis is that transport, and it is the only
  place where two models' notions of "correct" meet. **No such transport
  is needed between Chorus and the MVBA**: both are stated against the
  same `nset.is_byz`, so `Mvba.mvbaSafety` is *exactly* the instance
  Chorus's constraint asks for.

**Chorus's three assumptions at this instantiation.** Chorus states three
`assumption`s about its immutable configuration (`Chorus.lean`,
"Assumptions"): the MVBA starts in an initial state (`[mvba_init]`), and
the two facts about the entry-vector projections `mval_pos` / `mval_neg`
that its agreement argument uses (`[mval_pos_functional]`,
`[mval_pos_neg_excl]`). They enter the composed statement as the
`assumptions` conjunct of the slot-consensus instance's `init` — a
hypothesis on the *initial* states, as the glue's own `[sc_init]` is. At the
intended configuration — `mval_pos v j m := v j = some m`, `mval_neg v j :=
v j = none` (`chorusTheory` below) — the two projection assumptions are
theorems, so the one genuine hypothesis among the three is that the abstract
MVBA state Chorus starts from is an initial state of `Mvba`
(`chorusTheory_assumptions`).

Nothing about the temporal obligations enters here — MCP Safety is a safety
property, and its proof needs only the proven `…Safety` fragments. The
temporal levels (`OrchestratorTemporal`, `SlotConsensusTemporal`,
`MVBATemporal`), of which this development has no instance, are consumed by
nothing in this file.

The one composition claim this file does *not* make is the one declared out
of scope throughout (`docs/ChorusDesign.md` §10.1): that running the
Conductor and Chorus *implements* the glue's oracle steps — trace-level
refinement. Here the glue's `orch_step`/`sc_step` are the modules' own
transitions, and Chorus's `mvba_step` is the `Mvba` model's own internal
transition, which is as close as a state-based composition comes; the
remaining seam is named in `Cadence.lean`'s header. -/

namespace Cadence
open Classical Conductor

section System

variable {slot window time node acsstate nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited window] [Inhabited time] [Inhabited node] [Inhabited acsstate]
  [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view] [Inhabited Phase] [Inhabited PathChoice]
  [TotalOrderWithMinimum slot] [TotalOrderWithMinimum window] [TotalOrder time]
  -- The MVBA's views are ordered as the Conductor's slots and windows are.
  [TotalOrderWithMinimum view]
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

/-! ### Chorus at the `Mvba` instance

The three abstract sorts Chorus's MVBA constraint is stated over are
instantiated at the `Mvba` model's own types: the value is the entry vector
`node → Option merkle_root` (`docs/MvbaPlan.md` §1.2), the state is the
model's abstract state, the message type the model's `Msg`. -/

/-- Chorus's slot-consensus instance with its MVBA constraint filled by
`Mvba.mvbaSafety thM`, brought to the system's fault model. -/
@[implicit_reducible]
noncomputable def chorusInstance
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view)
    (hbyz : ∀ i, (nset.is_byz i = true) ↔ fm.byz i) :
    SlotConsensusSafety slot node merkle_root (slot × (node → Option merkle_root))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
        (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
        (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice))
      fm.byz :=
  SlotConsensusSafety.castByz (funext fun i => propext (hbyz i))
    (Chorus.slotConsensusSafety (mvba := Mvba.mvbaSafety thM) thS)

/-- The glue's transition system at the verified instances: slots ordered
by the Conductor's slot order, the fault model the system's `fm`, the
orchestrator state the Conductor's state, each slot's consensus state a
Chorus state (whose MVBA is the `Mvba` model), proposal vectors the tagged
Chorus decision vectors. -/
noncomputable abbrev systemRTS (thC : Conductor.Theory slot window time node acsstate)
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view)
    (hbyz : ∀ i, (nset.is_byz i = true) ↔ fm.byz i) :=
  @Cadence.relationalTransitionSystem slot node (slot × (node → Option merkle_root)) merkle_root
    (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
    (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)) time
    _ _ _ _ _ _ _ TotalOrderWithMinimum.toTotalOrder _ fm
    (Conductor.orchestratorSafety thC) (chorusInstance thS thM hbyz)

/-- **MCP Safety, positional form, for the composed system** (`def:safety`,
`lemma:cadence-safety`): in every reachable state of the glue running the
Conductor and Chorus — Chorus running the `Mvba` model as its MVBA — two
correct validators never disagree on the log entry at a given position. No
contract hypothesis remains — only the three modules' configurations and
the Conductor's and Chorus's agreement on the fault pattern. -/
theorem system_positional_log_safety
    (thC : Conductor.Theory slot window time node acsstate)
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view)
    (hbyz : ∀ i, (nset.is_byz i = true) ↔ fm.byz i)
    {th : Cadence.Theory slot node (slot × (node → Option merkle_root)) merkle_root
      (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
        (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
        (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)) time}
    {st : Cadence.State (Cadence.FieldAbstractType slot node (slot × (node → Option merkle_root)) merkle_root
      (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
        (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
        (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)) time)}
    (hreach : (systemRTS thC thS thM hbyz).reachable th st)
    {i j : node} (hi : ¬ fm.byz i) (hj : ¬ fm.byz j)
    {Li Lj : List (slot × (slot × (node → Option merkle_root)))}
    (hLi : Cadence.IsLog st i Li) (hLj : Cadence.IsLog st j Lj) :
    ∀ k (h₁ : k < Li.length) (h₂ : k < Lj.length), Li[k]'h₁ = Lj[k]'h₂ :=
  @Cadence.positional_log_safety slot node (slot × (node → Option merkle_root)) merkle_root
    (Conductor.State (Conductor.FieldAbstractType slot window time node acsstate))
    (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)) time
    _ _ _ _ _ _ _ TotalOrderWithMinimum.toTotalOrder _ fm
    (Conductor.orchestratorSafety thC) (chorusInstance thS thM hbyz)
    th st hreach i j hi hj Li Lj hLi hLj

/-! ### Chorus's assumptions, discharged at the entry vector

`chorusTheory` is the Chorus configuration with the entry-vector projections
fixed the way the value type dictates; `chorusTheory_assumptions` shows that
of Chorus's three `assumption`s only `[mvba_init]` survives as a hypothesis
at it. -/

/-- The Chorus configuration at the system's instantiation: the proposers,
the well-encoded roots, and the abstract MVBA state Chorus starts from, with
`mval_pos v j m := v j = some m` and `mval_neg v j := v j = none`. -/
@[implicit_reducible]
noncomputable def chorusTheory (is_proposer : node → Bool) (well_encoded : merkle_root → Bool)
    (mvba_init_state : Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view)) :
    Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice :=
  ⟨is_proposer, well_encoded,
    fun v j m => decide (v j = some m), fun v j => decide (v j = none), mvba_init_state⟩

omit [TotalOrderWithMinimum slot] fm in
/-- At `chorusTheory`, Chorus's three assumptions reduce to the one that is a
genuine hypothesis: the abstract MVBA state Chorus starts from is an initial
state of the `Mvba` model (the two projection assumptions hold by
computation). -/
theorem chorusTheory_assumptions
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view)
    (is_proposer : node → Bool) (well_encoded : merkle_root → Bool)
    (mvba_init_state : Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view)) :
    (Chorus.relationalTransitionSystem slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice
      (mvba := Mvba.mvbaSafety thM)).assumptions
        (chorusTheory is_proposer well_encoded mvba_init_state)
    ↔ (Mvba.mvbaSafety thM).init mvba_init_state := by
  constructor
  · rintro ⟨h, -, -⟩
    exact h
  · intro h
    refine ⟨h, ?_, ?_⟩
    · intro v j m1 m2 h1 h2
      simp only [decide_eq_true_eq] at h1 h2
      rw [h1] at h2
      exact Option.some.inj h2
    · rintro v j m ⟨h1, h2⟩
      simp only [decide_eq_true_eq] at h1 h2
      rw [h1] at h2
      exact Option.some_ne_none _ h2

end System
end Cadence

/-! ## The pinned trust base

The composed theorem rests on the standard Lean trio alone: it is the glue's
theorem applied to three kernel-checked instances (the Conductor's, Chorus's
— with the `Mvba` model's plugged into it — and the transport of Chorus's
instance to the system's fault model, a rewrite along a propositional
equality of predicates). -/

/--
info: 'Cadence.system_positional_log_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.system_positional_log_safety
