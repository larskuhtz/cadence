import Veil

/-! # Module contracts for the Cadence composition

This file states the **interfaces between the protocol's modules** as Lean
type classes, lifted from the paper's module specifications (Appendix B
(`section:framework`), Appendix D (`section:conductor-formal`)). Citations
name the target revision's rendered references
([PaperAlignment.md](../docs/PaperAlignment.md) §0).

Each entry is the paper's module, the class that states it here, and what
implements it in this development.

* Module 1 (`mod:slotconsensus`), per-slot consensus — `SlotConsensus`; Chorus ([Chorus.lean](Chorus.lean))
* Module 2 (`mod:orchestrator_2`), slot scheduling — `Orchestrator`; Conductor ([Conductor.lean](Conductor.lean))
* Module 4 (`mod:acs`), agreement on a core set — `ACS`; out of scope (a standard
  primitive)
* Module 3 (`mod:mvba`), multi-valued Byzantine agreement — `MVBA`; Mvba ([Mvba.lean](Mvba.lean) — the
  leader-based protocol of the paper repository's internal supplement;
  consumed by Chorus as its `mvba` constraint, instantiated in [System.lean](System.lean))

Every class states the **whole** of the paper's module: its interface (inputs
and outputs), and every one of its properties — safety, liveness, and the
quantitative bounds — as a field. A property is a field whether or not this
development can prove it, and whether or not anything consumes it: the
interface is part of the *specification*, so an obligation belongs here even
when it is only ever discharged by hand. What differs between the properties
is *where* they are discharged, and the two-level shape below makes that
difference visible in the types rather than in prose.

## The shape: one skeleton, two levels

Each module `X` is two classes over a shared skeleton.

* **`TransitionSystemSafety`** — what every contract has because it *is* a
  transition system: `init`, the internal `step`, their union `trans`, an
  over-approximated `reachable`, and the three closure facts. Stated once and
  extended by all four fragments, so "the module's transition system" means
  the same seven things everywhere and a reader who has understood one
  contract has understood that much of the others.
* **`XSafety extends TransitionSystemSafety`** — the *state-level* fragment. It fixes an abstract state type
  and the module's transitions over it (`init`, the internal `step`, the input
  transitions the paper's safety properties refer to, and their union
  `trans`), the observables a consumer reads off that state, and every
  property that is a predicate on reachable states or a relation between
  consecutive states: the paper's safety properties, the monotonicity of the
  observables, and the frame conditions that say internal steps do not
  fabricate inputs. Every field is first-order — no quantification over
  functions or runs — because this is the fragment a **Veil module
  `instantiate`s as a class constraint**, and Veil hands every axiom of an
  instantiated class to the SMT solver verbatim. That is what lets the
  consumer *use* the contract instead of restating it, and it is also why a
  non-first-order field here is fatal: the check commands reject one by class
  and field name before any solver starts
  (`attribute [veil_smt_ignore] C.field` is the escape hatch, used here only
  for the MVBA's decision-handoff and certificate-level facts, which no
  consumer's safety cell reads;
  [CLAUDE.md](../CLAUDE.md) and `spikes/03_*.lean` have the detail).
* **`XTemporal … [S : XSafety …]`** — everything else the paper promises,
  stated **over the safety instance**: every field mentions `S.init`,
  `S.trans`, `S.reachable` or one of `S`'s observables, so a temporal
  obligation is an obligation about *exactly* the transition system the
  fragment fixes and cannot drift from it. Temporal properties are stated
  over explicit runs (`Run`, `TimedRun` below); bounds are carried as data;
  the inputs that only the temporal properties refer to enter here with
  their observables. This level is consumed at the Lean level only, so it may
  quantify freely.
* **`X extends XSafety, XTemporal`** — the paper's module in one name. The
  second parent's instance argument is the first parent, so `X` is exactly
  "a safety fragment together with a temporal level *about it*"; nothing is
  restated to join them.

## Conventions shared by every class

* **Correctness is one object.** Every class takes the fault pattern
  `byz : validator → Prop` as an explicit *parameter* rather than a field, so
  that the several contracts a consumer instantiates are all stated against
  the same notion of "correct" (`FaultModel` packages it for a Veil module,
  whose `instantiate` needs a term). The paper states every property for
  correct validators only; Byzantine validators' inputs and outputs are
  unconstrained.
* **Inputs are transitions, outputs are observables.** A paper input such as
  `complete(s)` is a relation `complete : state → validator → slot → state →
  Prop` — the consumer *drives* it by picking a post-state; a paper output
  such as `open(s)` is an observable `opened : state → validator → slot →
  Prop` the consumer *reads*. Every observable is **monotone** along
  transitions (an event, once it has happened, has happened), and internal
  steps leave a correct validator's inputs unchanged (**frame** axioms) — an
  input can only be given by the consumer.
* **Reachability is abstract and over-approximating.** `reachable` is a field
  closed under `init` and `trans`; an implementation supplies its true
  reachable set, a consumer only needs the closure. Properties are stated at
  `reachable st` — **including the step-level ones**: the monotonicity fields
  (`opened_mono`, `completed_mono`, `finalized_mono`, `on_time_mono`) take the
  pre-state's reachability before `trans`, as `monotonicity` does. The reason is on the provider side: an implementation discharges these
  from checked two-state cells (Veil's `step_property`), whose hypotheses are
  the module's assumptions and invariants at the pre-state, so an all-states
  field could not consume them. It costs a consumer nothing: the glue and
  the Conductor carry `orch_reachable` / `sc_reachable` / `acs_*` as
  invariants.
* **Runs.** `Run state init trans` is an infinite sequence of states along
  `trans`; `TimedRun` adds a clock reading at every index (monotone,
  non-Zeno) and the run's global stabilisation time `gst`. The clock is the
  run's, not the state's: a module whose state has a clock (the
  Conductor's `now`) ties the two in its own contract
  (`OrchestratorTemporal.clock_agrees`). The paper's execution model —
  fair scheduling of the module's own transitions plus partial synchrony —
  is not expressible against an abstract state, so each upper class carries
  an **`Admissible : TimedRun → Prop`** field that the implementation
  *defines*, and states every temporal property for admissible runs only.
  `admissible_exists` forbids the vacuous definition. Its intended content
  is the named fairness and network assumptions of
  [Architecture.md](../docs/Architecture.md) §4 items 2 and 4; the one
  implementation that defines it is the MVBA's (`Mvba.Admissible`,
  [Mvba/Schedule.lean](Mvba/Schedule.lean)).
* **Time.** Timed properties take a `time` type with Veil's `TotalOrder` and
  an `Add`. The paper's `max(t, GST) + d` is written as `TimedRun.byGstBound`
  — "by `u + d` for the least `u` above both `t` and `gst`" — so no
  decidability of the order is needed. -/

/- Why the contracts live in this file and not in
[Primitives.lean](Primitives.lean): [Chorus.lean](Chorus.lean) imports
Primitives.lean, so a contract kept there would invalidate Chorus's compiled
artefact on every contract edit. Chorus does import this file, since it
consumes `MVBASafety` as a class constraint, so an edit here rebuilds the
Chorus family too — a warm replay from the proof cache when no VC statement
changes, a cold re-solve otherwise. If the contracts start changing often,
the MVBA classes can move to a file of their own that Chorus.lean imports
alone; they do not go back into Primitives.lean. -/

/-! ## Shared vocabulary -/

/-- The fault pattern of an execution: `byz i` says validator `i` is
Byzantine. A Veil module instantiates this once and passes `fm.byz` to every
module contract it consumes, so all of them speak about the same set of
correct validators. -/
class FaultModel (validator : Type) where
  byz : validator → Prop

/-- **The transition-system skeleton shared by all four module contracts.**

Every `…Safety` fragment extends this, so `init` / `step` / `trans` /
`reachable` mean the same thing in each of them and the closure facts are
stated once. `step` is the module's *internal* (module-driven) transitions;
`trans` is any transition, internal steps and the consumer's inputs alike,
and is what runs are sequences of. `reachable` is an over-approximation: an
implementation supplies its true reachable set, a consumer needs only that
it is closed under `init` and `trans`.

A Veil module `instantiate`s a fragment, not this class; the fragment's
parent arrives as a projection field and is destructured into the solver's
hypotheses like any other, which the fork's `VeilTest/DestructParentClass.lean`
pins and [spikes/07_sc_state_tag_ok.lean](../spikes/07_sc_state_tag_ok.lean) exercises here. -/
class TransitionSystemSafety (state : Type) where
  init : state → Prop
  /-- Internal (module-driven) transitions. -/
  step : state → state → Prop
  /-- Any transition — internal steps and the consumer's inputs. -/
  trans : state → state → Prop
  /-- The over-approximated reachable states. -/
  reachable : state → Prop
  step_trans : ∀ st st', step st st' → trans st st'
  reachable_init : ∀ st, init st → reachable st
  reachable_trans : ∀ st st', reachable st → trans st st' → reachable st'

/-- A run of a module: an infinite sequence of states, starting in an initial
state, each consecutive pair a transition. The temporal obligations of the
module contracts quantify over these. -/
structure Run (state : Type) (init : state → Prop) (trans : state → state → Prop) where
  at' : Nat → state
  starts : init (at' 0)
  steps : ∀ n, trans (at' n) (at' (n + 1))

namespace Run
variable {state : Type} {init : state → Prop} {trans : state → state → Prop}

/-- `P` holds at some point of the run. -/
def eventually (r : Run state init trans) (P : state → Prop) : Prop := ∃ n, P (r.at' n)

end Run

/-- A timed run: a run with a clock reading `clk n` at every index (the
paper's synchronized clocks), monotone and unbounded (no Zeno runs), and the
run's global stabilisation time `gst`. The clock belongs to the run, so a
module whose state has no clock is timed without adding one to its state. -/
structure TimedRun (state time : Type) [TotalOrder time]
    (init : state → Prop) (trans : state → state → Prop)
    extends Run state init trans where
  /-- The clock reading at each index. -/
  clk : Nat → time
  clock_mono : ∀ n, TotalOrder.le (clk n) (clk (n + 1))
  clock_unbounded : ∀ t, ∃ n, TotalOrder.le t (clk n)
  gst : time

namespace TimedRun
variable {state time : Type} [TotalOrder time]
  {init : state → Prop} {trans : state → state → Prop}

/-- `P` holds at some point of the run whose clock reads at most `t`
("by time `t`"). -/
def byTime (r : TimedRun state time init trans) (t : time) (P : state → Prop) : Prop :=
  ∃ n, TotalOrder.le (r.clk n) t ∧ P (r.at' n)

/-- The paper's "by time `max(t, GST) + d`", without `max`: `P` holds by
`u + d` where `u` is the least time above both `t` and the run's `gst`. -/
def byGstBound [Add time] (r : TimedRun state time init trans) (t d : time)
    (P : state → Prop) : Prop :=
  ∃ u, TotalOrder.le t u ∧ TotalOrder.le r.gst u ∧
    (∀ u', TotalOrder.le t u' → TotalOrder.le r.gst u' → TotalOrder.le u u') ∧
    r.byTime (u + d) P

end TimedRun

/-! ## Slot Consensus, Module 1 (`mod:slotconsensus`)

The paper's module is *parameterised by a slot* `s`, one instance per slot,
and the glue holds one abstract state per slot
(`function sc_state (s : slot) : scstate` in [Cadence.lean](Cadence.lean)).
The class carries that parameter **in the state** rather than as an index on
every field: a state knows which instance it belongs to, through the
observable `tag : state → slot`, and `tag_frame` says transitions stay inside
their instance. The indexed form's `init s st` is `init st ∧ tag st = s`, and a consumer
pins the correspondence once, for its *initial* states, from which
`tag (sc_state s) = s` follows as an ordinary inductive invariant.

The reason is uniformity: this is the only family-indexed contract, and
indexing the shared skeleton to accommodate it would make the other three
read as degenerate families (`init () st`) for the sake of this one.
[spikes/07_sc_state_tag_ok.lean](../spikes/07_sc_state_tag_ok.lean)
establishes that the encoding costs a consumer exactly one assumption and
still yields everything the indexed form gave;
[spikes/08_sc_tag_frame_removed.lean](../spikes/08_sc_tag_frame_removed.lean)
is its negative control.

The implementation instance (`Chorus.slotConsensusSafety`,
[Chorus/Compose.lean](Chorus/Compose.lean)) runs one independent copy of
the single-slot Chorus model per slot: its state is a `slot × Chorus.State`
pair whose first component is the tag, and each finalized vector carries the
same slot.

Interface (Module 1 (`mod:slotconsensus`)): inputs `participate()`, `abandon()`,
`propose(P)`; output `finalize(V)`.

**The three inputs are in the fragment.** The paper's module lists them as
its interface ("a validator starts participating", "a validator stops
participating", "a proposer submits its proposal"), and its prose calls the
participation signals and the proposals "a validator's *inputs* to the
instance". The glue gives all three (Algorithm 1, line 17
(`line:participate`); Algorithm 1, line 19 (`line:propose`); Algorithm 1,
line 23 (`line:abandon`)), so they are transitions of the fragment the glue
instantiates, each recorded by an observable (`participating`, `abandoned`,
`proposed`), with the same first-order facts every other contract states of
its inputs: the record is monotone, the input sets it, internal steps leave
a correct validator's records alone, nothing is recorded initially, and an
input records itself and nothing else (`complete_frame`'s pattern: the
other validators' records of the same input, and every validator's records
of the other two inputs, are unchanged). The last is what lets a consumer
derive a state-level fact about one input from its own calls: without it, a
`participate` could set `abandoned`, and "the glue abandons only after
finalizing" would not give Module 1's assumed behaviour at the contract
level.

### Obligations

Each entry is the class field, the paper's name for it, the level it sits at,
and where it is discharged.

* **`agreement`** — Agreement (incl. per-validator integrity: take `i = j`);
  *safety*. Chorus `safety [agreement_pos]`, `[agreement_pos_neg]`, `invariant
  [local_committed_complete]` — `Chorus.slotConsensusSafety`
* **`slot_safety`** — Slot safety; *safety*. By construction of the tagged
  state (`slot_of V = tag st`)
* **`proposal_inclusion`** — Proposal inclusion (conditional on synchrony);
  *safety*. Chorus `safety [proposal_inclusion]`,
  `[proposal_inclusion_no_neg]`; the synchrony premise's state-level form is
  `on_time` = Chorus's `all_honest_recorded`
* **`termination`** — Termination; *temporal*. `Chorus.chorusTemporal`
  ([Chorus/Temporal.lean](Chorus/Temporal.lean)), from `Chorus.termination`
  ([Chorus/Termination.lean](Chorus/Termination.lean)). Its run premises
  are named in [Chorus/Liveness.lean](Chorus/Liveness.lean) and make up the
  instance's `Admissible`: (F-justice) on Chorus's own honest actions
  (`FJustice`), the MVBA's scheduling on the run's MVBA projection
  (`MvbaAdmissible`) and the certificate bridge (`ValidBridge`); the
  field's two antecedents are the caller's (`AllParticipate`,
  `NoAbandonBeforeFinalizing`)
* **`hiding_residue`** — Hiding (Definition 4 (`def:hiding`), specialised to the instance's
  slot); *safety*. First-order and proven by Chorus (`safety
  [hiding_until_deadline]`), so it sits in the fragment — see the field's
  docstring for what it does and does not say
* **`participate`, `abandon`, `propose`** and their observables, effects,
  frames and initial conditions — the interface's three inputs; *safety
  (first-order)*. Chorus, from its `participate`, `abandon` and `propose`
  actions' bodies and Veil's generated frame lemmas —
  `Chorus.slotConsensusSafety`
* **`quiescence`** — Quiescence (Lemma 6 (`lemma:chorus-quiescence`));
  *safety (one-step form, from a reachable state)*. `Chorus.chorusTemporal`,
  in the lemma's two parts: Chorus's own sending rules require
  `participating i ∧ ¬ abandoned i` (`Chorus.own_sent_new`,
  [Chorus/Compose.lean](Chorus/Compose.lean)), and the MVBA's sends are
  confined by the MVBA's own `quiescence` to the window between a gated
  `mvba_propose` and a forwarded `abandon` (`Chorus.mvba_sent_new`)

`d_tot`-totality and `ℓ`-termination are *not* properties of Module 1 (`mod:slotconsensus`)
— they are Chorus-specific strengthenings the Conductor's proofs consume —
and live in `SlotConsensusWithTotality` below. -/

/-- The state-level fragment of Module 1 (`mod:slotconsensus`). This is what the
`Cadence` glue module instantiates. Unindexed: the instance's slot is the
state observable `tag` (see the section docstring). -/
class SlotConsensusSafety (slot validator proposal pvector state : Type)
    (byz : validator → Prop) extends TransitionSystemSafety state where

  /-- The slot whose instance this state belongs to — the module's parameter,
      carried by the state instead of indexing every field. -/
  tag : state → slot
  /-- Transitions stay inside their instance: a state never becomes another
      slot's. With a consumer's initial-state assumption this makes "slot
      `s`'s state is tagged `s`" an inductive invariant. -/
  tag_frame : ∀ st st', trans st st' → tag st' = tag st

  /-- Output `finalize(V)`: `finalized st i V` says validator `i` has
      finalized proposal vector `V`, in state `st` of this instance. -/
  finalized : state → validator → pvector → Prop
  /-- The slot identifier a proposal vector carries (`V.slot`). -/
  slot_of : pvector → slot
  /-- `includes V j P`: `V` maps proposer `j` to proposal `P` (`V[j] = P`).
      Pure data of the vector. -/
  includes : pvector → validator → proposal → Prop
  /-- The state-level form of proposal inclusion's synchrony premise — "`j` is
      a correct proposer of the slot, `s.deadline − Δ ≥ GST`, and `j` proposed
      `P` at `s.deadline − Δ`". The premise is about the timed execution; its
      consequence inside an untimed implementation is a *state* fact
      (for Chorus: every honest validator has recorded `j`'s entry `P`,
      `all_honest_recorded`), which is what `on_time st j P` names. It is
      monotone: once established it stays established. -/
  on_time : state → validator → proposal → Prop

  /-- A finalization, once output, stands. -/
  finalized_mono : ∀ st st' i V, reachable st → trans st st' → finalized st i V → finalized st' i V
  on_time_mono : ∀ st st' j P, reachable st → trans st st' → on_time st j P → on_time st' j P
  /-- Nothing is finalized before the instance runs. -/
  init_finalized : ∀ st i V, init st → ¬ finalized st i V

  /-- **Agreement** — correct validators never finalize conflicting proposal
      vectors; with `i = j` this is per-validator integrity ("no correct
      validator finalizes two different proposal vectors, even on separate
      occasions"). -/
  agreement : ∀ st, reachable st → ∀ i j V V',
    ¬ byz i → ¬ byz j → finalized st i V → finalized st j V' → V = V'
  /-- **Slot safety** — a finalized proposal vector carries the slot of the
      instance that finalized it. -/
  slot_safety : ∀ st, reachable st → ∀ i V,
    ¬ byz i → finalized st i V → slot_of V = tag st
  /-- **Proposal inclusion** — under the synchrony premise, the finalized
      vector contains the correct proposer's on-time proposal. -/
  proposal_inclusion : ∀ st, reachable st → ∀ i j V P,
    ¬ byz i → finalized st i V → on_time st j P → includes V j P

  /-- The slot's deadline has passed in state `st` (for Chorus: the phase is
      no longer `pre_deadline`). -/
  deadline_passed : state → Prop
  /-- The instance's proposal payloads have become recoverable — the
      decryption threshold has been reached (for Chorus: the slot key is
      released, `slot_key_released`). -/
  payload_recoverable : state → Prop
  /-- **Hiding** (Definition 4 (`def:hiding`), specialised to this instance's slot) — its
      *protocol-level residue*: payloads become recoverable only after the
      deadline. The paper's definition is simulation-based (an ideal
      functionality and a simulator) and is not expressible in this language;
      what it reduces to is this residue together with the cryptographic
      hiding of the threshold encryption (`ThresholdIBE.decrypt_secret`,
      [Primitives.lean](Primitives.lean)) and the paper's simulation
      argument (Appendix C.2 (`appendix:encryption`)). Those two steps stay meta-theoretic
      ([Architecture.md](../docs/Architecture.md) §4 item 3).

      First-order, and proven by Chorus, so it sits in the fragment. -/
  hiding_residue : ∀ st, reachable st → payload_recoverable st → deadline_passed st

  /-- Input `participate()` at validator `i`: "a validator starts
      participating" (Module 1 (`mod:slotconsensus`), Interface). -/
  participate : state → validator → state → Prop
  /-- Input `abandon()` at validator `i`: "a validator stops participating". -/
  abandon : state → validator → state → Prop
  /-- Input `propose(P)` by (proposer) `i`: "a proposer submits its proposal
      `P`". -/
  propose : state → validator → proposal → state → Prop
  participate_trans : ∀ st i st', participate st i st' → trans st st'
  abandon_trans : ∀ st i st', abandon st i st' → trans st st'
  propose_trans : ∀ st i P st', propose st i P st' → trans st st'

  /-- Input record: `i` has started participating. -/
  participating : state → validator → Prop
  /-- Input record: `i` has stopped participating. -/
  abandoned : state → validator → Prop
  /-- Input record: `i` has proposed `P`. -/
  proposed : state → validator → proposal → Prop

  participating_mono : ∀ st st' i, trans st st' → participating st i → participating st' i
  abandoned_mono : ∀ st st' i, trans st st' → abandoned st i → abandoned st' i
  proposed_mono : ∀ st st' i P, trans st st' → proposed st i P → proposed st' i P
  participate_effect : ∀ st i st', participate st i st' → participating st' i
  abandon_effect : ∀ st i st', abandon st i st' → abandoned st' i
  propose_effect : ∀ st i P st', propose st i P st' → proposed st' i P
  /-- Internal steps do not fabricate a correct validator's inputs. -/
  participating_step_frame : ∀ st st' i, step st st' → ¬ byz i →
    (participating st' i ↔ participating st i)
  abandoned_step_frame : ∀ st st' i, step st st' → ¬ byz i →
    (abandoned st' i ↔ abandoned st i)
  proposed_step_frame : ∀ st st' i P, step st st' → ¬ byz i →
    (proposed st' i P ↔ proposed st i P)
  /-- An input records itself and nothing else: `participate()` at `i`
      leaves every other correct validator's participation unchanged… -/
  participate_frame : ∀ st i st' j, participate st i st' → ¬ byz j → j ≠ i →
    (participating st' j ↔ participating st j)
  /-- …`abandon()` at `i` every other correct validator's abandonment… -/
  abandon_frame : ∀ st i st' j, abandon st i st' → ¬ byz j → j ≠ i →
    (abandoned st' j ↔ abandoned st j)
  /-- …and `propose(P)` by `i` every other correct proposal. -/
  propose_frame : ∀ st i P st' j P', propose st i P st' → ¬ byz j →
    (j ≠ i ∨ P' ≠ P) → (proposed st' j P' ↔ proposed st j P')
  /-- No input records another: `participate()` leaves every correct
      validator's abandonment and proposals unchanged, `abandon()` its
      participation and proposals, `propose(P)` its participation and
      abandonment. -/
  participate_abandoned_frame : ∀ st i st' j, participate st i st' → ¬ byz j →
    (abandoned st' j ↔ abandoned st j)
  participate_proposed_frame : ∀ st i st' j P, participate st i st' → ¬ byz j →
    (proposed st' j P ↔ proposed st j P)
  abandon_participating_frame : ∀ st i st' j, abandon st i st' → ¬ byz j →
    (participating st' j ↔ participating st j)
  abandon_proposed_frame : ∀ st i st' j P, abandon st i st' → ¬ byz j →
    (proposed st' j P ↔ proposed st j P)
  propose_participating_frame : ∀ st i P st' j, propose st i P st' → ¬ byz j →
    (participating st' j ↔ participating st j)
  propose_abandoned_frame : ∀ st i P st' j, propose st i P st' → ¬ byz j →
    (abandoned st' j ↔ abandoned st j)
  init_participating : ∀ st i, init st → ¬ participating st i
  init_abandoned : ∀ st i, init st → ¬ abandoned st i
  init_proposed : ∀ st i P, init st → ¬ proposed st i P

/-- The temporal level of Module 1 (`mod:slotconsensus`), over a safety instance `S`:
every property the fragment cannot state. `message` is the module's own
protocol-message type (used by Quiescence). -/
class SlotConsensusTemporal (slot validator proposal pvector state time message : Type)
    [TotalOrder time] [Add time] (byz : validator → Prop)
    [S : SlotConsensusSafety slot validator proposal pvector state byz] where
  /-- `i` has sent protocol message `m` of this instance. -/
  sent : state → validator → message → Prop
  sent_mono : ∀ st st' i m, S.trans st st' → sent st i m → sent st' i m

  /-- The executions under which the temporal guarantees hold: the
      implementation's fair-scheduling and network assumptions, *defined by
      the implementation*. The properties below are stated for admissible
      runs only. -/
  Admissible : TimedRun state time S.init S.trans → Prop
  /-- Admissibility is not vacuous: every initial state starts some
      admissible run. -/
  admissible_exists : ∀ st, S.init st →
    ∃ r : TimedRun state time S.init S.trans, Admissible r ∧ r.at' 0 = st

  /-- **Termination** — if every correct validator starts participating (and
      none abandons before finalizing — the paper's assumed behaviour of
      correct validators), then every correct validator eventually finalizes. -/
  termination : ∀ (r : TimedRun state time S.init S.trans), Admissible r →
    (∀ i, ¬ byz i → r.eventually (fun st => S.participating st i)) →
    (∀ i, ¬ byz i → ∀ n, S.abandoned (r.at' n) i → ∃ V, S.finalized (r.at' n) i V) →
    ∀ j, ¬ byz j → r.eventually (fun st => ∃ V, S.finalized st j V)

  /-- **Quiescence** — a correct validator sends no protocol message before it
      starts participating or after it stops. Stated in one-step form, over a
      transition rather than over a run, as it is in the other three
      contracts: a send that appears across a transition out of a reachable
      state finds the sender participating and not yet abandoned. The paper's
      property is about executions, so the transition starts from a
      reachable state. -/
  quiescence : ∀ st st' i m, S.reachable st → S.trans st st' → ¬ byz i →
    sent st' i m → ¬ sent st i m → S.participating st' i ∧ ¬ S.abandoned st i

/-- Module 1 (`mod:slotconsensus`) in full: the fragment together with a temporal level
about it. -/
class SlotConsensus (slot validator proposal pvector state time message : Type)
    [TotalOrder time] [Add time] (byz : validator → Prop) extends
    SlotConsensusSafety slot validator proposal pvector state byz,
    SlotConsensusTemporal slot validator proposal pvector state time message byz

/-! ### Slot consensus with the Chorus timing strengthenings

`d_tot`-**totality** (Proposition 4 (`prop:chorus-totality`); `d_tot = Δ`) and `ℓ`-**termination** (Lemma 11 (`lemma:chorus-termination`),
`ℓ = 5Δ + ℓ_MVBA`) are not part of Module 1 (`mod:slotconsensus`): they are properties of
Chorus that the Conductor's totality and recovery proofs consume
(Lemma 15 (`lemma:conductor-totality`), through `Φ_oc = ℓ_chorus + d_tot`). Both are
conditioned on *Δ-synchronized participation*
(Definition 5 (`def:delta-synchronized-participation`)), which is stated here as a predicate
on the run. An orchestrator built on a slot consensus without these does not
achieve the paper's bounds. Both are proven for Chorus at the system's
configuration (`Chorus.chorusWithTotality`,
[Chorus/Temporal.lean](Chorus/Temporal.lean)), over timed runs that carry
their own clock ([Bounds.md](../docs/Bounds.md) §6.4).

Like `SlotConsensusTemporal`, this is a class **over** the safety instance:
one more level of what the implementation still owes, kept separate because
Module 1 (`mod:slotconsensus`) does not promise it — only Chorus does. -/
class SlotConsensusWithTotality (slot validator proposal pvector state time message : Type)
    [TotalOrder time] [Add time] (byz : validator → Prop)
    [S : SlotConsensusSafety slot validator proposal pvector state byz]
    [T : SlotConsensusTemporal slot validator proposal pvector state time message byz] where
  /-- The network delay bound after `gst`. -/
  Δ : time
  /-- Chorus's termination latency. -/
  ℓ : time
  /-- Chorus's totality latency (`d_tot = Δ` in the paper). -/
  d_tot : time
  /-- The slot's deadline `D` (`s.deadline`). Within Cadence it is
      `start_time s + Δ` (`OrchestratorSafety.start_time`). -/
  deadline : slot → time
  /-- **Δ-synchronized participation**: if a correct validator starts
      participating at time `t`, every correct validator does so by
      `max(t, GST) + Δ`. -/
  SyncParticipation : TimedRun state time S.init S.trans → Prop
  syncParticipation_def : ∀ r : TimedRun state time S.init S.trans,
    SyncParticipation r ↔
      ∀ n i, ¬ byz i → S.participating (r.at' n) i →
        ∀ j, ¬ byz j → r.byGstBound (r.clk n) Δ (fun st => S.participating st j)
  /-- **ℓ-Termination** — under Δ-synchronized participation, if all correct
      validators participate by `t`, every correct validator finalizes by
      `max(t, GST) + ℓ`.

      Two further antecedents are the caller's side of the contract, the
      conditions the paper's proof uses "when run within Cadence". Neither
      is a condition on the scheduler, so neither is part of `Admissible`.
      *No abandonment before finalizing* (Algorithm 1, line 23 (`line:abandon`)) is the same
      antecedent `SlotConsensusTemporal.termination` has; without it, a
      validator that abandons at once never finalizes. *No start before
      `D − Δ`* is the Conductor's integrity (Lemma 12 (`lemma:conductor-integrity`)),
      stated over the observable `participating`. It holds at the start
      index exactly when the paper's form does, and it follows at every
      later one. Without it, a slot whose deadline lies far after `t`
      cannot finalize by `max(t, GST) + ℓ`. -/
  bounded_termination : ∀ r : TimedRun state time S.init S.trans,
    T.Admissible r → SyncParticipation r →
    (∀ i, ¬ byz i → ∀ n, S.abandoned (r.at' n) i → ∃ V, S.finalized (r.at' n) i V) →
    (∀ n i, ¬ byz i → S.participating (r.at' n) i →
      TotalOrder.le (deadline (S.tag (r.at' n))) (r.clk n + Δ)) →
    ∀ t, (∀ i, ¬ byz i → r.byTime t (fun st => S.participating st i)) →
    ∀ j, ¬ byz j → r.byGstBound t ℓ (fun st => ∃ V, S.finalized st j V)
  /-- **d_tot-Totality** — under Δ-synchronized participation, if a correct
      validator finalizes at time `t`, every correct validator finalizes by
      `max(t, GST) + d_tot`. The one caller antecedent is *no abandonment
      before finalizing*, as in `bounded_termination`: a correct validator
      that had abandoned before finalizing would never finalize. -/
  totality : ∀ r : TimedRun state time S.init S.trans,
    T.Admissible r → SyncParticipation r →
    (∀ i, ¬ byz i → ∀ n, S.abandoned (r.at' n) i → ∃ V, S.finalized (r.at' n) i V) →
    ∀ n i V, ¬ byz i → S.finalized (r.at' n) i V →
    ∀ j, ¬ byz j → r.byGstBound (r.clk n) d_tot (fun st => ∃ V', S.finalized st j V')

/-! ## Orchestrator, Module 2 (`mod:orchestrator_2`)

The persistent slot-scheduling primitive. Interface: input `complete(s)`,
output `open(s)`; a slot never opened is *skipped*.

### Obligations

Each entry is the class field, the paper's name for it, the level it sits at,
and where it is discharged.

* **`totality`** — Totality; *temporal*, in rely form (see "Within
  Cadence" below). **not proven**: Lemma 15 (`lemma:conductor-totality`),
  a per-window induction over timed runs
* **`opened_mono`** — Integrity, "at most once"; *safety*. The `opened`
  observable is monotone, so an open event (`¬ opened st ∧ opened st'`)
  happens at most once per `(i, s)` — `Conductor.orchestratorSafety`
* **`integrity_timing`** — Integrity, "not before `s.deadline − Δ`"; *safety*.
  First-order and proven by the Conductor (`safety [opened_after_start]`), so
  it sits in the fragment — which is why the fragment carries `time` —
  `Conductor.orchestratorSafety`
* **`monotonicity`** — Monotonicity; *safety*. Conductor `invariant
  [open_local_order]` + the `open_slot` guard — `Conductor.orchestratorSafety`
* **`open_prefix_agreement`** — Totality + Integrity + Monotonicity, safety
  residue; *safety*. Conductor `safety [open_prefix_agreement]` —
  `Conductor.orchestratorSafety`
* **`boundedness`, `bound`** — `B`-Boundedness; *temporal (quantifies over
  `Fin bound → slot`)*. **not proven**: the interval form is Conductor `safety
  [bounded_tail]`; the count `B = 2W − p` adds the window widths, which the
  model states (`[win_bounds_shift]`) and the instance at `slot := ℕ` fixes
* **`recovery`, `recovery_time`** — `R`-Recovery; *temporal*, in rely form.
  **not proven**: Lemma 16 (`lemma:conductor-recovery`), through
  Proposition 18 (`prop:smooth-windows`) and Proposition 19
  (`prop:first-post-gst-window-time`), under the four parameter assumptions
* **`OrchestratorWithTotality`** — the `d_tot` form of Totality that
  Lemma 15 (`lemma:conductor-totality`) proves "more specifically"; a
  Conductor-level strengthening, not part of Module 2. **not proven**

### Within Cadence: the caller's two conditions

Totality and Recovery do not hold of the Conductor alone: a caller that
never completes a slot leaves every correct validator in window 1. The paper
proves both only "when run within Cadence" (Appendix D.2
(`subsection:conductor-proof`)), and its proofs use exactly two facts about
the caller's completions, each conditional on the openings (P15,
[PaperAlignment.md](../docs/PaperAlignment.md) §6):

* **(R-tot)** `CallerTotality` — for every slot whose openings are
  synchronized within `d`, the completions are synchronized within `d`
  too (Chorus's totality, Proposition 4 (`prop:chorus-totality`), read
  through the glue: opening is starting to participate, finalizing is
  completing);
* **(R-term)** `CallerTermination` — for every slot whose openings are
  synchronized within `d`, if every correct validator opens it by `t`, every
  correct validator completes it by `max(t, GST) + ℓ` (Chorus's
  termination, Lemma 11 (`lemma:chorus-termination`)).

They are the antecedents of `totality` and `recovery`, stated over the
fragment's own observables, as `SlotConsensusWithTotality`'s caller
conditions are. `Admissible` stays the implementation's scheduler, network
and timers, and says nothing about the caller. One tolerance serves both
sides of (R-tot) because the paper's induction closes on it: Chorus's
totality latency equals the tolerance its condition grants ("both equal
`Δ = d_tot`", before Definition 6 (`def:window-synchronized`)). An
unconditional open-to-complete bound, Module 2's commented-out assumed
behaviour, would assume part of the conclusion (Proposition 14
(`prop:conductor-open-to-complete`) derives it from Totality).

### `open_prefix_agreement` — the safety residue of Totality + Monotonicity

The paper's prose after Module 2 (`mod:orchestrator_2`) derives from the three baseline
properties that *whenever a correct validator opens a slot `s`, every correct
validator opens exactly the same set of slots with number at most
`s.number`*. Totality is temporal, but the derived statement has a
state-level residue that is inductive and is the fact Lemma 1 (`lemma:cadence-safety`)
case 1 actually uses: if correct `j` has opened `s` and correct `i` has
opened `s' < s`, then `j` has (already) opened `s'`. The glue's proof of
skip agreement combines it with `monotonicity`: once `j` opens past `s'`
without opening it, `s'` is never opened by `j`, hence — by this field — by
no correct validator. -/

/-- The state-level fragment of Module 2 (`mod:orchestrator_2`). This is what the
`Cadence` glue module instantiates.

It carries `time`, `clock` and `start_time` — not because the glue reasons
about time (it does not) but because Integrity's second half is a
first-order fact about a reachable state that the Conductor *proves*, and
the placement rule puts such a property in the fragment. The glue therefore
declares a phantom `time` sort with its order and never mentions it again;
the paper's orchestrator interface does speak of starting times, so the sort
is honest rather than an artefact. -/
class OrchestratorSafety (validator slot state time : Type) [ord : TotalOrder slot]
    [tord : TotalOrder time] (byz : validator → Prop)
    extends TransitionSystemSafety state where
  /-- Input `complete(s)` at validator `i`. -/
  complete : state → validator → slot → state → Prop
  complete_trans : ∀ st i s st', complete st i s st' → trans st st'

  /-- Output `open(s)`: the orchestrator has output `open(s)` at validator `i`. -/
  opened : state → validator → slot → Prop
  /-- Input record: validator `i` has input `complete(s)`. -/
  completed : state → validator → slot → Prop
  /-- The module's clock, read off its state (Conductor's `now`). -/
  clock : state → time
  /-- The slot's starting time `s.deadline − Δ`. -/
  start_time : slot → time

  /-- **Integrity, first half.** An `open(s)` output stands; hence the event
      happens at most once per `(i, s)`. -/
  opened_mono : ∀ st st' i s, reachable st → trans st st' → opened st i s → opened st' i s
  completed_mono : ∀ st st' i s, reachable st → trans st st' → completed st i s → completed st' i s
  complete_effect : ∀ st i s st', complete st i s st' → completed st' i s
  /-- An input records itself and nothing else: `complete(s)` at `i` leaves
      every other correct validator's `completed` record unchanged. -/
  complete_frame : ∀ st i s st' j s', complete st i s st' → ¬ byz j →
    (j ≠ i ∨ s' ≠ s) → (completed st' j s' ↔ completed st j s')
  /-- Internal steps do not fabricate a correct validator's `complete` inputs. -/
  completed_step_frame : ∀ st st' i s, step st st' → ¬ byz i →
    (completed st' i s ↔ completed st i s)
  init_opened : ∀ st i s, init st → ¬ opened st i s
  init_completed : ∀ st i s, init st → ¬ completed st i s

  /-- **Integrity, second half** — no slot is opened before its starting
      time. -/
  integrity_timing : ∀ st, reachable st → ∀ i s,
    ¬ byz i → opened st i s → TotalOrder.le (start_time s) (clock st)
  /-- **Monotonicity** — a correct validator opens slots in increasing order;
      state-level form: a slot below an opened slot that is not opened is
      never opened. -/
  monotonicity : ∀ st st' i s s', reachable st → trans st st' → ¬ byz i →
    opened st i s' → ord.le s s' → s ≠ s' → ¬ opened st i s → ¬ opened st' i s
  /-- **Open-prefix agreement** — the safety residue of Totality +
      Monotonicity (see the section docstring). -/
  open_prefix_agreement : ∀ st, reachable st → ∀ i j s s',
    ¬ byz i → ¬ byz j → opened st i s' → opened st j s → ord.le s' s → s' ≠ s →
    opened st j s'

namespace OrchestratorSafety

variable {validator slot state time : Type} {ord : TotalOrder slot} [tord : TotalOrder time]
  [Add time] {byz : validator → Prop}

/-- **Openings of `s` synchronized within `d`**: once a correct validator
has opened `s`, at index `n`, every correct validator opens `s` by
`max(clk n, GST) + d`. The form of Definition 6
(`def:window-synchronized`)'s second condition, for one slot. -/
def OpeningsSyncWithin (S : @OrchestratorSafety validator slot state time ord tord byz)
    (r : TimedRun state time S.init S.trans) (s : slot) (d : time) : Prop :=
  ∀ n i, ¬ byz i → S.opened (r.at' n) i s →
    ∀ j, ¬ byz j → r.byGstBound (r.clk n) d (fun st => S.opened st j s)

/-- **Completions of `s` synchronized within `d`**: once a correct
validator has completed `s`, at index `n`, every correct validator completes
`s` by `max(clk n, GST) + d`. Definition 6 (`def:window-synchronized`)'s
third condition, for one slot. -/
def CompletionsSyncWithin (S : @OrchestratorSafety validator slot state time ord tord byz)
    (r : TimedRun state time S.init S.trans) (s : slot) (d : time) : Prop :=
  ∀ n i, ¬ byz i → S.completed (r.at' n) i s →
    ∀ j, ¬ byz j → r.byGstBound (r.clk n) d (fun st => S.completed st j s)

/-- **(R-tot), the caller's totality at tolerance `d`**: for every slot
whose openings are synchronized within `d`, the completions are
synchronized within `d` too. Within Cadence it is Chorus's `d_tot`-totality
(Proposition 4 (`prop:chorus-totality`)) read through the glue, at
`d = d_tot = Δ`. -/
def CallerTotality (S : @OrchestratorSafety validator slot state time ord tord byz)
    (r : TimedRun state time S.init S.trans) (d : time) : Prop :=
  ∀ s, S.OpeningsSyncWithin r s d → S.CompletionsSyncWithin r s d

/-- **(R-term), the caller's termination at tolerance `d` and latency `ℓ`**:
for every slot whose openings are synchronized within `d`, if every correct
validator opens it by `t`, every correct validator completes it by
`max(t, GST) + ℓ`. Within Cadence it is Chorus's `ℓ`-termination (Lemma 11
(`lemma:chorus-termination`)) read through the glue. -/
def CallerTermination (S : @OrchestratorSafety validator slot state time ord tord byz)
    (r : TimedRun state time S.init S.trans) (d ℓ : time) : Prop :=
  ∀ s, S.OpeningsSyncWithin r s d →
    ∀ t, (∀ i, ¬ byz i → r.byTime t (fun st => S.opened st i s)) →
      ∀ j, ¬ byz j → r.byGstBound t ℓ (fun st => S.completed st j s)

end OrchestratorSafety

/-- The temporal level of Module 2 (`mod:orchestrator_2`), over a safety instance `S`. -/
class OrchestratorTemporal (validator slot state time : Type) [ord : TotalOrder slot]
    [TotalOrder time] [Add time] (byz : validator → Prop)
    [S : OrchestratorSafety validator slot state time byz] where
  /-- The executions under which the temporal guarantees hold, defined by the
      implementation (see the file header). -/
  Admissible : TimedRun state time S.init S.trans → Prop
  admissible_exists : ∀ st, S.init st →
    ∃ r : TimedRun state time S.init S.trans, Admissible r ∧ r.at' 0 = st
  /-- In an admissible run the run's clock is the module's own (`S.clock`,
      Conductor's `now`), so the timed properties below and the fragment's
      `integrity_timing` speak about one clock. -/
  clock_agrees : ∀ (r : TimedRun state time S.init S.trans), Admissible r →
    ∀ n, r.clk n = S.clock (r.at' n)

  /-- The caller's totality latency, which is also the tolerance its
      condition grants: (R-tot) is assumed at it. Within Cadence, Chorus's
      `d_tot = Δ` (Proposition 4 (`prop:chorus-totality`)). -/
  caller_d_tot : time
  /-- The caller's termination latency: (R-term) is assumed at it. Within
      Cadence, Chorus's `ℓ_chorus` (Lemma 11 (`lemma:chorus-termination`)). -/
  caller_ℓ : time

  /-- **Totality**, in rely form — if the caller's completions are total
      ((R-tot), `CallerTotality`) and some correct validator opens `s`,
      every correct validator eventually opens `s`. Module 2's Totality,
      with the condition under which the paper proves it ("when run within
      Cadence", Lemma 15 (`lemma:conductor-totality`)) as its antecedent. -/
  totality : ∀ (r : TimedRun state time S.init S.trans), Admissible r →
    S.CallerTotality r caller_d_tot →
    ∀ i j s, ¬ byz i → ¬ byz j →
      r.eventually (fun st => S.opened st i s) → r.eventually (fun st => S.opened st j s)
  /-- The bound `B` (`2W − p` for Conductor). -/
  bound : Nat
  /-- **`B`-Boundedness** — an opened-but-uncompleted slot of a correct
      validator has fewer than `B` opened slots above it; equivalently (the
      paper's form) if `p_i` has opened `k` slots `s_1 < … < s_k`, every `s_j`
      with `j ≤ k − B` is completed. -/
  boundedness : ∀ st, S.reachable st → ∀ i s, ¬ byz i → S.opened st i s →
    ¬ S.completed st i s →
    ¬ ∃ f : Fin bound → slot, Function.Injective f ∧
      ∀ k, S.opened st i (f k) ∧ ord.le s (f k) ∧ s ≠ f k
  /-- The recovery time `R` (`2Wτ` for Conductor). -/
  recovery_time : time
  /-- **`R`-Recovery**, in rely form — if the caller's completions are total
      ((R-tot)) and terminate ((R-term)), every slot whose starting time is
      at least `R` after `gst` is opened by every correct validator, and no
      later than its starting time (with `integrity_timing`: exactly then).
      Lemma 16 (`lemma:conductor-recovery`) proves it "when run within
      Cadence". -/
  recovery : ∀ (r : TimedRun state time S.init S.trans), Admissible r →
    S.CallerTotality r caller_d_tot → S.CallerTermination r caller_d_tot caller_ℓ →
    ∀ s, TotalOrder.le (r.gst + recovery_time) (S.start_time s) →
    ∀ i, ¬ byz i → r.byTime (S.start_time s) (fun st => S.opened st i s)

/-- Module 2 (`mod:orchestrator_2`) in full. -/
class Orchestrator (validator slot state time : Type) [ord : TotalOrder slot]
    [TotalOrder time] [Add time] (byz : validator → Prop) extends
    OrchestratorSafety validator slot state time byz,
    OrchestratorTemporal validator slot state time byz

/-! ### The orchestrator with `d_tot`-totality

Module 2's Totality is eventual. Lemma 15 (`lemma:conductor-totality`)
proves "more specifically" that an opening at `t` reaches every correct
validator by `max(t, GST) + d_tot`, and Corollary 4
(`cor:chorus-correctness-within-cadence`) consumes exactly that bound: it is
Chorus's Δ-synchronized participation. So the bound is a property of the
Conductor, not of Module 2, as `d_tot`-totality is of Chorus and not of
Module 1 (`SlotConsensusWithTotality`), and it sits one level up, over the
temporal instance, in the same rely form (P15,
[PaperAlignment.md](../docs/PaperAlignment.md) §6). -/

/-- The `d_tot` strengthening of the orchestrator's Totality, over a safety
instance `S` and a temporal instance `T`. -/
class OrchestratorWithTotality (validator slot state time : Type) [ord : TotalOrder slot]
    [TotalOrder time] [Add time] (byz : validator → Prop)
    [S : OrchestratorSafety validator slot state time byz]
    [T : OrchestratorTemporal validator slot state time byz] where
  /-- The orchestrator's totality latency (`d_tot = Δ` for the Conductor
      within Cadence). -/
  d_tot : time
  /-- **`d_tot`-Totality**, in rely form — if the caller's completions are
      total ((R-tot)), then for every slot, an opening by a correct validator
      at `t` is followed by every correct validator's by `max(t, GST) +
      d_tot`. -/
  totality : ∀ (r : TimedRun state time S.init S.trans), T.Admissible r →
    S.CallerTotality r T.caller_d_tot →
    ∀ s, S.OpeningsSyncWithin r s d_tot

/-! ## Agreement on a Core Set, Module 4 (`mod:acs`)

Each validator proposes a slot; ACS outputs one agreed set of at least
`2f + 1` validator–slot pairs. The Conductor consumes one instance per
window. Interface: inputs `propose(s)` (which doubles as starting to
participate), `abandon()`; output `decide(set)`, exposed relationally as
`decided st i p s` ("`i` has decided, with `(p, s)` in its set") plus the
event marker `has_decided st i`.

No implementation is in scope — the target leaves the ACS unspecified
([ConductorBounds.md](../docs/ConductorBounds.md) §3) — so no instance
exists here: every field is an assumption of the composition
([Architecture.md](../docs/Architecture.md) §4 item 3). What is
machine-checked is that the Conductor consumes exactly this class
([Conductor.lean](Conductor.lean) `instantiate acs`), with one documented
bridge: the median-range guard of its `acs_decide` action. Cardinality is
outside the first-order fragment, so the bridge is a stated `require`; that
the median of a decided set meets it is a theorem from this class
(`Cadence.acs_median_bracket`, [AcsMedian.lean](AcsMedian.lean)), through
`decided_unique`, `validity_quantitative` and the system's fault bound.

**Both inputs are in the fragment.** The module's interface is `propose(s)`
("a validator proposes slot `s`, thereby starting to participate") and
`abandon()` ("a validator stops participating"), and the Conductor gives both
(Algorithm 7, line 42 (`line:acs-propose`); Algorithm 7, line 45
(`line:acs-abandon`)). With `abandon` in the fragment, and the two cross-frames
saying that neither input records the other, the module's second assumption
(no premature abandonment) is a state invariant of the Conductor rather
than a reading of the paper (Proposition 12
(`prop:acs-no-premature-abandonment`)).

**One slot per validator.** Module 4 (`mod:acs`)'s Validity bounds the size
of a decided set (`|set| ≥ 2f + 1`) but not the number of pairs one
validator contributes. The median argument behind Proposition 7
(`prop:acs-nonoverlap`) ("since at most `f` of the `2f + 1` decided values
are faulty") needs the latter: with Validity as stated, `2f + 1` pairs of a
single Byzantine validator are a valid decision, and the median is the
adversary's choice. `decided_unique` states the missing bound, and
`validity_quantitative` counts distinct validators. Every ACS that collects
one signed proposal per validator meets both, and the paper's own reading
of a decided set as "the decided estimates" of the validators presumes
them. Flagged to the authors as P16
([PaperAlignment.md](../docs/PaperAlignment.md) §6).

### Obligations

Each entry is the class field, the paper's name for it, and the level it sits
at.

* **`agreement`** — Agreement; *safety*
* **`validity_genuine`** — Validity, qualitative half (correct pairs genuine);
  *safety*
* **`validity_quantitative`, `fault_bound`** — Validity, quantitative half
  (`|set| ≥ 2f + 1`, counted in distinct validators); *upper, state-shaped
  (cardinality)*
* **`decided_unique`** — one slot per validator in a decided set (P16); *safety*
* **`abandon`, `abandoned`** and their frames — the interface's second
  input; *safety (first-order)*
* **`integrity`** — Integrity; *safety*
* **`termination`, `ℓ`** — `ℓ`-Termination; *temporal (under the module's two
  assumptions)*
* **`totality`, `Δ`** — `Δ`-Totality; *temporal (under the module's two
  assumptions)*
* **`quiescence`** — Quiescence; *temporal* -/

/-- The state-level fragment of Module 4 (`mod:acs`). This is what the `Conductor`
module instantiates. -/
class ACSSafety (validator slot state : Type) (byz : validator → Prop)
    extends TransitionSystemSafety state where
  /-- Input `propose(s)` by validator `p`: "a validator proposes slot `s`,
      thereby starting to participate" (Module 4 (`mod:acs`), Interface). -/
  propose : state → validator → slot → state → Prop
  /-- Input `abandon()` at validator `i`: "a validator stops
      participating". -/
  abandon : state → validator → state → Prop
  propose_trans : ∀ st p s st', propose st p s st' → trans st st'
  abandon_trans : ∀ st i st', abandon st i st' → trans st st'

  /-- `p` has proposed slot `s`. -/
  proposed : state → validator → slot → Prop
  /-- `i` has decided, with `(p, s)` in its decided set. -/
  decided : state → validator → validator → slot → Prop
  /-- `i` has decided (some set). -/
  has_decided : state → validator → Prop
  /-- Input record: `i` has abandoned. -/
  abandoned : state → validator → Prop

  proposed_mono : ∀ st st' p s, trans st st' → proposed st p s → proposed st' p s
  decided_mono : ∀ st st' i p s, trans st st' → decided st i p s → decided st' i p s
  has_decided_mono : ∀ st st' i, trans st st' → has_decided st i → has_decided st' i
  abandoned_mono : ∀ st st' i, trans st st' → abandoned st i → abandoned st' i
  propose_effect : ∀ st p s st', propose st p s st' → proposed st' p s
  abandon_effect : ∀ st i st', abandon st i st' → abandoned st' i
  /-- An input records itself and nothing else: `propose(s)` by `p` leaves
      every other correct validator's proposals unchanged… -/
  propose_frame : ∀ st p s st' q s', propose st p s st' → ¬ byz q →
    (q ≠ p ∨ s' ≠ s) → (proposed st' q s' ↔ proposed st q s')
  /-- …`abandon()` at `i` every other correct validator's abandonment… -/
  abandon_frame : ∀ st i st' j, abandon st i st' → ¬ byz j → j ≠ i →
    (abandoned st' j ↔ abandoned st j)
  /-- …and neither input records the other. -/
  propose_abandoned_frame : ∀ st p s st' j, propose st p s st' → ¬ byz j →
    (abandoned st' j ↔ abandoned st j)
  abandon_proposed_frame : ∀ st i st' q s, abandon st i st' → ¬ byz q →
    (proposed st' q s ↔ proposed st q s)
  /-- Internal steps do not fabricate a correct validator's inputs
      (Byzantine proposals are unconstrained and may appear at any step). -/
  proposed_step_frame : ∀ st st' p s, step st st' → ¬ byz p →
    (proposed st' p s ↔ proposed st p s)
  abandoned_step_frame : ∀ st st' i, step st st' → ¬ byz i →
    (abandoned st' i ↔ abandoned st i)
  init_proposed : ∀ st p s, init st → ¬ proposed st p s
  init_has_decided : ∀ st i, init st → ¬ has_decided st i
  init_abandoned : ∀ st i, init st → ¬ abandoned st i

  decided_has_decided : ∀ st, reachable st → ∀ i p s,
    ¬ byz i → decided st i p s → has_decided st i
  /-- **Agreement** — no two correct validators decide different sets: a pair
      in one correct decider's set is in every correct decider's set. -/
  agreement : ∀ st, reachable st → ∀ i j p s,
    ¬ byz i → ¬ byz j → decided st i p s → has_decided st j → decided st j p s
  /-- **Validity, qualitative half** — a decided pair attributed to a correct
      validator is genuine: that validator proposed that slot. -/
  validity_genuine : ∀ st, reachable st → ∀ i p s,
    ¬ byz i → ¬ byz p → decided st i p s → proposed st p s
  /-- **Integrity** — a correct validator decides only after having proposed. -/
  integrity : ∀ st, reachable st → ∀ i,
    ¬ byz i → has_decided st i → ∃ s, proposed st i s
  /-- **One slot per validator** — a correct validator's decided set holds at
      most one pair of each validator. Not in Module 4 (`mod:acs`)'s Validity,
      and needed by the median argument (P16, the section docstring). -/
  decided_unique : ∀ st, reachable st → ∀ i p s s',
    ¬ byz i → decided st i p s → decided st i p s' → s = s'

/-- The temporal level of Module 4 (`mod:acs`), over a safety instance `S`. -/
class ACSTemporal (validator slot state time message : Type)
    [TotalOrder time] [Add time] (byz : validator → Prop)
    [S : ACSSafety validator slot state byz] where
  /-- `i` has sent protocol message `m` of this instance. -/
  sent : state → validator → message → Prop
  sent_mono : ∀ st st' i m, S.trans st st' → sent st i m → sent st' i m

  Admissible : TimedRun state time S.init S.trans → Prop
  admissible_exists : ∀ st, S.init st →
    ∃ r : TimedRun state time S.init S.trans, Admissible r ∧ r.at' 0 = st

  /-- The resilience parameter `f` (at most `f` Byzantine validators). -/
  fault_bound : Nat
  /-- **Validity, quantitative half** — a correct validator's decided set has
      pairs of at least `2f + 1` distinct validators. With `decided_unique`
      that is `|set| ≥ 2f + 1`, Module 4 (`mod:acs`)'s count, with each
      validator counted once. -/
  validity_quantitative : ∀ st, S.reachable st → ∀ i, ¬ byz i → S.has_decided st i →
    ∃ g : Fin (2 * fault_bound + 1) → validator,
      Function.Injective g ∧ ∀ k, ∃ s, S.decided st i (g k) s

  Δ : time
  ℓ : time
  /-- The module's first assumption, **Δ-synchronized proposals**: if a correct
      validator proposes at `t`, every correct validator proposes by
      `max(t, GST) + Δ`. -/
  SyncProposals : TimedRun state time S.init S.trans → Prop
  syncProposals_def : ∀ r : TimedRun state time S.init S.trans, SyncProposals r ↔
    ∀ n p s, ¬ byz p → S.proposed (r.at' n) p s →
      ∀ q, ¬ byz q → r.byGstBound (r.clk n) Δ (fun st => ∃ s', S.proposed st q s')
  /-- The module's second assumption, **no premature abandonment**: a correct
      validator that has proposed does not abandon before deciding. -/
  NoPrematureAbandon : TimedRun state time S.init S.trans → Prop
  noPrematureAbandon_def : ∀ r : TimedRun state time S.init S.trans,
    NoPrematureAbandon r ↔
      ∀ n i, ¬ byz i → S.abandoned (r.at' n) i → S.has_decided (r.at' n) i
  /-- **ℓ-Termination** — under the two assumptions: if all correct validators
      propose by `t`, every correct validator decides by `max(t, GST) + ℓ`. -/
  termination : ∀ r : TimedRun state time S.init S.trans,
    Admissible r → SyncProposals r → NoPrematureAbandon r →
    ∀ t, (∀ i, ¬ byz i → r.byTime t (fun st => ∃ s, S.proposed st i s)) →
    ∀ j, ¬ byz j → r.byGstBound t ℓ (fun st => S.has_decided st j)
  /-- **Δ-Totality** — under the two assumptions: if a correct validator
      decides at `t`, all correct validators decide by `max(t, GST) + Δ`. -/
  totality : ∀ r : TimedRun state time S.init S.trans,
    Admissible r → SyncProposals r → NoPrematureAbandon r →
    ∀ n i, ¬ byz i → S.has_decided (r.at' n) i →
    ∀ j, ¬ byz j → r.byGstBound (r.clk n) Δ (fun st => S.has_decided st j)
  /-- **Quiescence** — no protocol message before proposing or after
      abandoning. Stated in one-step form, over a transition out of a
      reachable state, as in `SlotConsensusTemporal`: the paper's property is
      about executions. -/
  quiescence : ∀ st st' i m, S.reachable st → S.trans st st' → ¬ byz i →
    sent st' i m → ¬ sent st i m →
      (∃ s, S.proposed st' i s) ∧ ¬ S.abandoned st i

/-- Module 4 (`mod:acs`) in full. -/
class ACS (validator slot state time message : Type) [TotalOrder time] [Add time]
    (byz : validator → Prop) extends
    ACSSafety validator slot state byz,
    ACSTemporal validator slot state time message byz

/-! ## Multi-Value Byzantine Agreement, Module 3 (`mod:mvba`)

Invoked by Chorus's fallback path, one instance per slot. Interface: inputs
`propose(B)` (a valid meta-block; doubles as starting to participate),
`abandon()`; output `decide(B)`. `Valid` is the publicly verifiable external
validity predicate the instance is parameterised by.

**The value is a meta-block representation; agreement is over its
entries.** A meta-block carries, for each proposer, an entry and the
certificate that makes it valid, and the MVBA "votes and decides over
`entries(B)`" (Supplement, Section 1.1 (`subsec:mvba-datatypes`)). Two
valid meta-blocks may carry different certificates for the same entries,
so correct validators may decide different representations. The class's
`value` is the representation, `entries` projects it to its entry vector,
and Agreement and Integrity are stated over `entries`, in the forms of
Supplement, Section 1.2 (`subsec:mvba-protocol`), "Agreement and Integrity
over entries". The system instantiates `value` at `MetaBlock` below.

The implementation is `Mvba` ([Mvba.lean](Mvba.lean)) — the leader-based
protocol of the paper repository's internal supplement, at the paper
target ([PaperAlignment.md](../docs/PaperAlignment.md) §0); [MvbaPlan.md](../docs/MvbaPlan.md) §0 says
what that referent is and is not — with `Valid` the model's immutable
`valid` and `entries` its immutable `ent`. The instance is `Mvba.mvbaSafety`
([Mvba/Compose.lean](Mvba/Compose.lean)), every field of the fragment
proven — the inputs, their observables, the frames, one-step Quiescence and
the certificate-level facts included, which is why they sit in the
fragment. The temporal level — the admissible-run model, `ℓ` and
Termination — is `Mvba.mvbaTemporal` ([Mvba/Temporal.lean](Mvba/Temporal.lean)),
proven from the instance hypotheses its docstring lists, and `Mvba.mvbaFull`
joins the two into the full class.

**Chorus consumes this class as a constraint**
([CompositionContracts.md](../docs/CompositionContracts.md) §3): `instantiate mvba : MVBASafety node
mvalue mentries mmsg mstate nodeset nset (fun i => nset.is_byz i = true)`
over an abstract state `mvba_st`, advanced by the oracle step `mvba_step`,
the driven input `mvba_propose` and the handoff `accept_mvba_commitqc`, with
two per-entry decision handlers and the fallback commit vote reading
`mvba.decided` off the state ([Chorus.lean](Chorus.lean), "The MVBA
instance"). Chorus reads a decided representation through `mvba.entries`
and two immutable projections of the entry vector, `mval_pos`/`mval_neg`,
and reads a positive entry's certificate kind through `mval_fb`;
[System.lean](System.lean) instantiates all of it at `Mvba.mvbaSafety`.
One thing is deliberately *not* a field of this class: the paper's `Valid
B` is a function of the meta-block, which *carries* its certificates, while
Chorus checks a decided entry's certificate against its own network
relations (the certificate the representation names: a vote quorum for a
`FastQC`, `fb_quorum_pos j m ∧ fbcert` for a `FallbackQC`) — a predicate on
Chorus's *state*, which a class parameter declared before the module's
state exists cannot mention. That check is the handlers' one stated bridge,
the MVBA counterpart of the Conductor's ACS median bridge
([CompositionContracts.md](../docs/CompositionContracts.md) §7).

### Obligations

Each entry is the class field, the paper's name for it, the level it sits at,
and where it is discharged.

* **`agreement`** — Agreement, over entries; *safety*. Mvba `safety
  [agreement]` — `Mvba.mvbaSafety`
* **`integrity`** — Integrity, over entries; *safety*. Mvba `safety
  [integrity]`, the stronger "decides at most once" — `Mvba.mvbaSafety`
* **`external_validity`** — External validity; *safety*. Mvba `safety
  [external_validity]` — `Mvba.mvbaSafety`
* **`termination`, `ℓ`** — `ℓ_MVBA`-Termination; *temporal*. The
  supplement's Supplement, Theorem 2 (`thm:termination`), `O(fΔ)` — `Mvba.mvbaTemporal`
  ([Mvba/Temporal.lean](Mvba/Temporal.lean)), under the timing model of [Mvba/Schedule.lean](Mvba/Schedule.lean)
* **`quiescence`** — Quiescence; *safety (one-step form)*. Mvba, from the
  transition bodies (`sent_new_tr`: every honest send requires the input and
  `¬ abandoned`) — `Mvba.mvbaSafety`
* **`certifies`, `decided_certified`, `accept`, `accept_trans`,
  `accept_effect`, `accept_enabled`** — the decision handoff of the
  supplement's strengthened interface (`decide(x, CommitQC)`, "Decision
  output and handoff", Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)); *safety (first-order, rely
  form)*. Mvba: a certificate is an existing commit certificate, a decision
  has one (`decided_backed`), and the handoff is `decide` — `Mvba.mvbaSafety`.
  Chorus drives `accept` (`accept_mvba_commitqc`)
* **`availReady`, `markAvail` and its fields** — `AvailReady_p(v)` and the
  input by which the composing dissemination layer reports it
  (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Commit availability
  condition", "Availability-synchronization assumption"); *safety
  (first-order, rely form)*. Mvba: `become_avail_ready` is that input, and
  nothing else writes `avail_ready` — `Mvba.mvbaSafety`. Chorus drives it
  (`mvba_avail_ready`), with its chunk wait as the guard
* **`certified_mono`, `certified_unique`, `certified_decided`,
  `certified_valid`, `certified_available`** — what a commit certificate
  guarantees on its own: it stays valid, it certifies one entry vector, the
  one every correct validator decides, with a valid representation and with
  the availability its correct signers established (Supplement, Section 1.2
  (`subsec:mvba-protocol`), "Commit availability condition"); *safety
  (first-order)*. Mvba: the monotonicity of `msg_commitqc`,
  `commitqc_agree`, `decided_backed`, `commitqc_valid` and
  `honest_commit_accepted` with `commitqc_backed` — `Mvba.mvbaSafety` -/

/-- The certificate that holds a positive entry of a meta-block: a `FastQC`
(`2f+1` fast votes) or a `FallbackQC` (`f+1` fallback entries)
(Supplement, Section 1.1 (`subsec:mvba-datatypes`)). -/
inductive CertKind where
  | fastQC
  | fallbackQC
  deriving DecidableEq, Inhabited

/-- **A meta-block representation**, the value the system instantiates the
MVBA at: for each proposer, its entry — a root (positive) or `none`
(negative) — and, for a positive entry, the kind of certificate that holds
it. The representation leaves out the certificate kinds of negative entries
and the `FBCert`: no rule of either document reads them, and whether they
verify is part of `Valid` ([PaperAlignment.md](../docs/PaperAlignment.md)
§8.1 (a)). -/
abbrev MetaBlock (node merkle_root : Type) := node → Option (merkle_root × CertKind)

/-- `entries(B)`: the meta-block's entry vector, its certificates dropped. -/
def MetaBlock.entries {node merkle_root : Type} (b : MetaBlock node merkle_root) :
    node → Option merkle_root :=
  fun j => (b j).map Prod.fst

/-- The state-level fragment of Module 3 (`mod:mvba`).

**Why the class takes a quorum family.** A certified meta-block's entries
are available: a supermajority signed its commit certificate, and each
correct member of that supermajority held its share before signing
(`certified_available`). Saying "a supermajority" needs the system's quorum
family, so the class takes it as the parameter `B`; it is used for nothing
else, and `byz` stays the class's notion of a correct party. -/
class MVBASafety (party value entryvec message state pset : Type)
    (B : ByzNodeSet party pset) (byz : party → Prop)
    extends TransitionSystemSafety state where
  /-- The publicly verifiable validity predicate. -/
  Valid : value → Prop
  /-- `entries(B)`: the entry vector of a representation. -/
  entries : value → entryvec

  /-- Input `propose(v)` by party `p`. That `v` is `Valid` is the caller's
      obligation; it is an antecedent of `MVBATemporal.termination`, the rely
      side of the contract, and not a field here. -/
  propose : state → party → value → state → Prop
  /-- Input `abandon()` at party `p`. -/
  abandon : state → party → state → Prop
  propose_trans : ∀ st p v st', propose st p v st' → trans st st'
  abandon_trans : ∀ st p st', abandon st p st' → trans st st'

  /-- Output `decide(v)`: `p` has decided the representation `v`. -/
  decided : state → party → value → Prop
  proposed : state → party → value → Prop
  abandoned : state → party → Prop
  /-- `p` has sent protocol message `m`. -/
  sent : state → party → message → Prop

  decided_mono : ∀ st st' p v, trans st st' → decided st p v → decided st' p v
  proposed_mono : ∀ st st' p v, trans st st' → proposed st p v → proposed st' p v
  abandoned_mono : ∀ st st' p, trans st st' → abandoned st p → abandoned st' p
  sent_mono : ∀ st st' p m, trans st st' → sent st p m → sent st' p m
  propose_effect : ∀ st p v st', propose st p v st' → proposed st' p v
  abandon_effect : ∀ st p st', abandon st p st' → abandoned st' p
  proposed_step_frame : ∀ st st' p v, step st st' → ¬ byz p →
    (proposed st' p v ↔ proposed st p v)
  abandoned_step_frame : ∀ st st' p, step st st' → ¬ byz p →
    (abandoned st' p ↔ abandoned st p)
  init_decided : ∀ st p v, init st → ¬ decided st p v
  init_proposed : ∀ st p v, init st → ¬ proposed st p v
  init_abandoned : ∀ st p, init st → ¬ abandoned st p

  /-- **Quiescence** — no protocol message before proposing or after
      abandoning. First-order in one-step form, and proven by `Mvba`
      (`sent_new_tr`), so it sits in the fragment. -/
  quiescence : ∀ st st' p m, trans st st' → ¬ byz p →
    sent st' p m → ¬ sent st p m →
      (∃ v, proposed st' p v) ∧ ¬ abandoned st p

  /-- **Agreement** — "if correct validators decide `x` and `x′`, then
      `entries(x) = entries(x′)`" (Module 3 (`mod:mvba`); Supplement,
      Section 1.2 (`subsec:mvba-protocol`), "Agreement and Integrity over
      entries"). -/
  agreement : ∀ st, reachable st → ∀ p q v v',
    ¬ byz p → ¬ byz q → decided st p v → decided st q v' → entries v = entries v'
  /-- **Integrity** — "all decision outputs of a correct validator carry the
      same entry vector" (Supplement, Section 1.2 (`subsec:mvba-protocol`),
      "Agreement and Integrity over entries"). Redelivery with that entry
      vector is permitted, so this is not "at most one representation"
      ([PaperAlignment.md](../docs/PaperAlignment.md) §5.4, P1). -/
  integrity : ∀ st, reachable st → ∀ p v v',
    ¬ byz p → decided st p v → decided st p v' → entries v = entries v'
  /-- **External validity** — a decided value is valid. -/
  external_validity : ∀ st, reachable st → ∀ p v,
    ¬ byz p → decided st p v → Valid v

  /-- `AvailReady_p(v)`: `p` holds its assigned availability share under
      every positive `FallbackQC` entry of `v` (Supplement, Section 1.2
      (`subsec:mvba-protocol`), "Commit availability condition"). -/
  availReady : state → party → value → Prop
  /-- Input: the composing dissemination layer reports `AvailReady_p(v)`.
      "The MVBA treats availability synchronization as a service of the
      composing dissemination and ChunkSync layer" (Supplement, Section 1.2
      (`subsec:mvba-protocol`), "Availability-synchronization assumption"),
      so the caller decides when `p` holds its shares, and this input is how
      it says so. -/
  markAvail : state → party → value → state → Prop
  markAvail_trans : ∀ st p v st', markAvail st p v st' → trans st st'
  markAvail_effect : ∀ st p v st', markAvail st p v st' → availReady st' p v
  /-- The report is about `p` and `v` only. -/
  availReady_markAvail_frame : ∀ st p v st' q w, markAvail st p v st' →
    availReady st' q w → availReady st q w ∨ (q = p ∧ w = v)
  init_availReady : ∀ st p v, init st → ¬ availReady st p v
  /-- `availReady` changes only by its input: every internal step and every
      other input leaves it as it is. -/
  availReady_step_frame : ∀ st st' p v, step st st' →
    (availReady st' p v ↔ availReady st p v)
  availReady_propose_frame : ∀ st q w st' p v, propose st q w st' →
    (availReady st' p v ↔ availReady st p v)
  availReady_abandon_frame : ∀ st q st' p v, abandon st q st' →
    (availReady st' p v ↔ availReady st p v)

  /- The decision handoff: the supplement's strengthened interface
  (`decide(x, CommitQC)`, "Decision output and handoff"). A decision comes
  with a transferable certificate over its entries, and a transferred valid
  certificate is accepted. -/

  /-- `c` is a valid commitment proof for the entry vector `e` at `st`: the
      certificate a decision outputs, "an aggregate of `2f+1` Commit
      signatures over `entries(x)`", which any party can check. -/
  certifies : state → message → entryvec → Prop
  /-- **Decide exposes its certificate** — a correct party's decision has a
      valid certificate that commits its entries. -/
  decided_certified : ∀ st, reachable st → ∀ p v, ¬ byz p → decided st p v →
    ∃ c, certifies st c (entries v)
  /-- Input: the caller hands party `p` a transferred certificate `c`. -/
  accept : state → party → message → state → Prop
  accept_trans : ∀ st p c st', accept st p c st' → trans st st'
  availReady_accept_frame : ∀ st q c st' p v, accept st q c st' →
    (availReady st' p v ↔ availReady st p v)
  /-- Accepting a valid certificate for `e` decides a representation of `e`
      (`Recover(e)`). -/
  accept_effect : ∀ st p c st' e, accept st p c st' → certifies st c e →
    ∃ v, entries v = e ∧ decided st' p v
  /-- **A transferred valid certificate is accepted** — in the rely form: if
      the caller hands a valid certificate to a correct party that has
      proposed, is not abandoned and has not decided, the party can take
      it. -/
  accept_enabled : ∀ st p c e, reachable st → ¬ byz p → certifies st c e →
    (∃ v', proposed st p v') → ¬ abandoned st p → (∀ v', ¬ decided st p v') →
    ∃ st', accept st p c st'

  /- What a certificate guarantees on its own. A certificate can exist before
  any correct party decides — the adversary can aggregate the signatures —
  so these are not consequences of the decision-level fields. -/

  /-- **A valid certificate stays valid** — what makes it a transferable
      commitment proof. -/
  certified_mono : ∀ st st' c e, trans st st' → certifies st c e → certifies st' c e

  /-- **One certified entry vector** — two valid certificates certify the
      same entries. -/
  certified_unique : ∀ st, reachable st → ∀ c c' e e',
    certifies st c e → certifies st c' e' → e = e'
  /-- **A certified entry vector is the decided one** — every correct
      party's decision has the certified entries. -/
  certified_decided : ∀ st, reachable st → ∀ c e p v,
    certifies st c e → ¬ byz p → decided st p v → entries v = e
  /-- **A certified entry vector has a valid representation.** -/
  certified_valid : ∀ st, reachable st → ∀ c e,
    certifies st c e → ∃ v, entries v = e ∧ Valid v
  /-- **A certified entry vector is available** — the certificate's signers
      include a supermajority each of whose correct members was
      `AvailReady` for a valid representation of the certified entries
      before signing. -/
  certified_available : ∀ st, reachable st → ∀ c e, certifies st c e →
    ∃ q, B.supermajority q ∧ ∀ p, B.member p q = true → ¬ byz p →
      ∃ v, entries v = e ∧ Valid v ∧ availReady st p v

/- The handoff and certificate facts no consumer's safety cell reads are
withheld from the solver. Every field of an instantiated class is otherwise
a hypothesis of every cell, and each of these has an `∃` in its conclusion.
Chorus's cells read the inputs, `certified_unique`, `certified_decided`,
`certified_mono` and the `availReady` frames, all universal. The withheld
fields stay declared axioms of the class, proven by `Mvba.mvbaSafety`. -/
attribute [veil_smt_ignore] MVBASafety.decided_certified MVBASafety.accept_effect
  MVBASafety.accept_enabled MVBASafety.certified_valid MVBASafety.certified_available

/-- The temporal level of Module 3 (`mod:mvba`), over a safety instance `S`.
With the inputs, their observables, the frames and Quiescence all in the
fragment — `Mvba` proves every one of them — this level is exactly the
admissible-run model, `ℓ` and Termination. -/
class MVBATemporal (party value entryvec message state pset time : Type)
    [TotalOrder time] [Add time] (B : ByzNodeSet party pset) (byz : party → Prop)
    [S : MVBASafety party value entryvec message state pset B byz] where
  Admissible : TimedRun state time S.init S.trans → Prop
  admissible_exists : ∀ st, S.init st →
    ∃ r : TimedRun state time S.init S.trans, Admissible r ∧ r.at' 0 = st

  ℓ : time
  /-- **ℓ_MVBA-Termination** — if all correct parties propose valid values
      by `t` and no correct party abandons before `max(t, GST) + ℓ`, every
      correct party decides by `max(t, GST) + ℓ`. The three antecedents are
      the caller's side of the contract: when to propose, what (`Valid`
      inputs, Supplement, Section 1.2 (`subsec:mvba-protocol`)'s precondition), and not to abandon. -/
  termination : ∀ r : TimedRun state time S.init S.trans, Admissible r →
    ∀ t, (∀ p, ¬ byz p → r.byTime t (fun st => ∃ v, S.proposed st p v)) →
    (∀ p, ¬ byz p → ∀ n v, S.proposed (r.at' n) p v → S.Valid v) →
    (∀ p, ¬ byz p → ∀ n, S.abandoned (r.at' n) p →
      ∃ u, TotalOrder.le t u ∧ TotalOrder.le r.gst u ∧
        (∀ u', TotalOrder.le t u' → TotalOrder.le r.gst u' → TotalOrder.le u u') ∧
        ¬ TotalOrder.le (r.clk n) (u + ℓ)) →
    ∀ q, ¬ byz q → r.byGstBound t ℓ (fun st => ∃ v, S.decided st q v)

/-- Module 3 (`mod:mvba`) in full. -/
class MVBA (party value entryvec message state pset time : Type) [TotalOrder time] [Add time]
    (B : ByzNodeSet party pset) (byz : party → Prop) extends
    MVBASafety party value entryvec message state pset B byz,
    MVBATemporal party value entryvec message state pset time B byz
