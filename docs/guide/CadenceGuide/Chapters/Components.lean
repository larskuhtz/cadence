/-
Chapter 6 of the guide: The components.
-/
import CadenceGuide.Elements
import CadenceGuide.ChapterList

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "The components" =>
%%%
file := "components"
%%%

_One section per model: what it covers, what it abstracts, its results, and where its details are._

The development follows the paper's decomposition: five models, one per
algorithm of the paper it verifies, and a composition layer that joins them
into the system the composed claims are about. This chapter is the
reference for each part. A section says what the paper specifies, what the
model covers and what it leaves out, the end results as the development
states them, and where to read further. {chapter Approach}[Chapter 1]
shows how the parts fit together.

:::table +header
*
  * Component
  * Paper
  * Model
  * Meets
  * Consumes
*
  * Chorus
  * {cite}`section:slot_agreement`
  * [Chorus.lean](../../../../Cadence/Chorus.lean)
  * {cite}`mod:slotconsensus`
  * the MVBA's contract
*
  * The MVBA
  * {cite}`sec:mvba-instantiation`
  * [Mvba.lean](../../../../Cadence/Mvba.lean)
  * {cite}`mod:mvba`
  * —
*
  * The Conductor
  * {cite}`algorithm:conductor`
  * [Conductor.lean](../../../../Cadence/Conductor.lean)
  * {cite}`mod:orchestrator_2`
  * the ACS's contract, {cite}`mod:acs`
*
  * The glue
  * {cite}`algorithm:cadence`
  * [Cadence.lean](../../../../Cadence/Cadence.lean)
  * MCP Safety, {cite}`def:safety`
  * the orchestrator's and the slot consensus's contracts
*
  * The receipt layer
  * {cite}`alg:fallback`
  * [FallbackReceipt.lean](../../../../Cadence/FallbackReceipt.lean)
  * a valid fallback meta-block, by construction
  * —
*
  * The composition
  * {cite}`subsection:correctness_cadence`
  * [System.lean](../../../../Cadence/System.lean), [Composed](../../../../Cadence/Composed/Schedule.lean)
  * the composed claims
  * the instances above
:::

Each model is a file of its own, and its header, the prose at the top of the
rendered source, is the long form of its section here: the modelling
choices, the paper lines each part follows, and what each abstraction costs.

# Chorus

*The paper.* Chorus is the per-slot consensus, {cite}`section:slot_agreement`:
for one slot, `n = 3f + 1` validators agree on a vector holding one entry per
proposer. A slot finishes on the fast path, two rounds of voting, or on the
fallback path, one more round, an MVBA instance and a final round of commit
votes. {cite}`mod:slotconsensus` is its specification.

*The model.* One slot instance, with the paper's participation interface
(`participate`, `propose`, `abandon`), honest actions for the rules of
{cite}`alg:proposer-dissemination` to {cite}`alg:da`, and one adversary action
per capability of a Byzantine validator. It abstracts:

* the MVBA, which enters as its contract, a class over an abstract state; the
  composed system fills it with the MVBA model below;
* the slot's timers, as one shared `phase` that the environment advances in
  order;
* erasure coding: roots are opaque, and the re-encode check is modelled by
  its verdict, `well_encoded`;
* other slots: the model is one slot, and the slots' independence is argued
  rather than modelled.

[ChorusDesign.md](../../../ChorusDesign.md) §3.4 and §8 list each abstraction
with its argument.

{chapter ReadingModel}[Chapter 3] reads the model in detail, and
{chapter ModelIdioms}[chapter 4] audits it action by action.

*The end result.* Chorus meets the whole of {cite}`mod:slotconsensus` at the
configuration the composed system runs:

{claim Chorus.slotConsensusFull}

The safety fragment it carries is {decl}`Chorus.slotConsensusSafety`, proven
from the model's invariants; termination is {decl}`Chorus.termination`, and
the timed bounds are {decl}`Chorus.timed_termination` and
{decl}`Chorus.totality`.

*Further detail:* [ChorusDesign.md](../../../ChorusDesign.md) (the modelling
choices and the network abstraction), [Liveness.md](../../../Liveness.md) §4
(the termination proof), [Bounds.md](../../../Bounds.md) §6.4 (the timed
bounds).

# The MVBA

*The paper.* {cite}`mod:mvba` specifies an MVBA by its interface and five
properties, with no algorithm. The algorithm is the leader-based protocol of
the paper repository's internal supplement, {cite}`sec:mvba-instantiation`:
views with rotating leaders, a lock, and timeout certificates that close a
view that does not decide. The supplement is part of the paper target.

*The model.* The supplement's {cite}`alg:mvba`, one handler per action, with
views, timeouts, timeout certificates and the lock. The value agreed on is a
meta-block, and agreement is over its entry vector. It abstracts:

* time: the model has no clock, and the view timer is a marker the
  environment sets; the timing model lives in the timed claim, over runs;
* `Recover`, as a choice among the valid meta-blocks with the given entries,
  which contains the supplement's choice;
* persistence and crash recovery, which the supplement handles separately;
* availability, which is the caller's input: Chorus drives it.

The model's header lists the rest, with each departure's argument.

*The end results.* The three safety properties of {cite}`mod:mvba`, proven
for every reachable state. Agreement, as the model states it:

{model Cadence.Mvba "safety [agreement]" (proven := Mvba.reachable_agreement)}

The whole contract, with termination within an explicit `ℓ_MVBA` of order
`fΔ`, is the MVBA the composed system runs:

{claim Mvba.mvbaFull}

The supplement's proof of agreement inducts over views. The model's
invariants replace that induction with one first-order statement, and
the mutation test of {chapter Checking}[chapter 7] shows that the lock
check they rest on is needed.

*Further detail:* the [model's header](../../../../Cadence/Mvba.lean),
[MvbaPlan.md](../../../MvbaPlan.md) (the decision record, and the map from
the supplement's lemmas to the invariants), [Bounds.md](../../../Bounds.md)
§6.2 (the bound on termination).

# The Conductor

*The paper.* The Conductor is the orchestrator, {cite}`algorithm:conductor`,
in the ACS-based formal version of {cite}`section:conductor-formal`, which is
the one the paper proves. Slots are scheduled in windows of `W` slots; a
validator that has completed the earlier slots proposes a first slot for the
next window to that window's ACS instance, and the median of the decided
proposals becomes the window's first slot. {cite}`mod:orchestrator_2` is its
specification.

*The model.* Windows, the readiness check, the ACS proposals and the median
rule, with the slot openings at their starting times. It abstracts:

* the ACS, which enters as its contract, one abstract instance per window;
  the ACS is an assumed module ({chapter Contracts}[chapter 5]);
* time, as an abstract clock that only makes "not before the starting time"
  expressible; the timing lives in the timed claims, over runs;
* punctual opening: the model lets an enabled opening wait, which only adds
  behaviours, and requires openings in slot order where the paper's argument
  uses punctuality;
* counting, replaced by intervals of slots.

The Conductor has no Byzantine message surface of its own: Byzantine
validators act through their ACS proposals.

*The end result.* The Conductor meets the whole of
{cite}`mod:orchestrator_2`, for every ACS that meets its contract:

{claim Conductor.conductorFull}

The fragment is {decl}`Conductor.orchestratorSafety`; the timed fields are
{decl}`Conductor.totality` ({cite}`lemma:conductor-totality`),
{decl}`Conductor.boundedness` ({cite}`lem:boundedness`) and
{decl}`Conductor.recovery` ({cite}`lemma:conductor-recovery`).

*Further detail:* [ConductorDesign.md](../../../ConductorDesign.md) (the
module decomposition and the modelling choices),
[ConductorBounds.md](../../../ConductorBounds.md) (the timed claims and their
proofs).

# The glue

*The paper.* {cite}`algorithm:cadence` wires one orchestrator and one slot
consensus instance per slot into the full protocol; {cite}`subsection:correctness_cadence`
proves the system's properties from the two modules' specifications.

*The model.* The algorithm's handlers, verified against the two contracts
alone: the orchestrator and every slot's consensus are abstract states the
glue holds and reads only through the contracts' observables. It abstracts:

* the sub-protocols, as steps that advance their abstract state by anything
  the contract allows;
* the paper's atomic handlers, as separate actions that may run late, which
  admits more behaviours, so every safety property holds of the atomic
  algorithm too.

The glue has no network and no Byzantine actions: validators interact only
inside the two sub-protocols.

*The end result.* MCP Safety, {cite}`def:safety`, for any orchestrator and
slot consensus that meet the two contracts:

{claim Cadence.positional_log_safety}

It rests on two slot-indexed properties of the model, `log_agreement` and
`skip_agreement`, which are {cite}`lemma:cadence-safety`'s two cases.

*Further detail:* the [model's header](../../../../Cadence/Cadence.lean),
[CompositionContracts.md](../../../CompositionContracts.md) (how a model
consumes a contract).

# The receipt layer

*The paper.* The fallback path's receipt rules, {cite}`alg:fallback`: a
validator accepts a fallback vote only if every entry in it is a valid FastQC
or the sender's own signed entry ({cite}`line:fb-accept`), and builds one
entry per proposer from what it accepted ({cite}`line:fb-build-entry`).

*The model.* One correct receiving validator: its accepted votes, the
FastQCs it harvests, its build and its MVBA proposal. It refines a step that
the Chorus model takes as one action, at the grain of one validator, and
meets no contract. All its state is the validator's own, so it reads its own
records negatively, as the paper's `if / else if` precedence does.

*The end results.* Whenever the validator proposes, every proposer's entry
is backed by a certificate:

{model Cadence.FallbackReceipt "safety [certified_propose]" (proven := FallbackReceipt.reachable_certified_propose)}

And once it has accepted `2f + 1` votes, one of the three build cases
applies to every proposer, for every `n = 3f + 1`:

{claim FallbackReceipt.build_totality_of_reachable}

The layer has the shape of the Chorus proof family at a fraction of the
size, so it is also the place where a change to the verification pipeline
is tried first.

*Further detail:* [ChorusDesign.md](../../../ChorusDesign.md) §7.2 (the
receipt rules), [Architecture.md](../../../Architecture.md) §5 (why the layer
has its own model).

# The composition

*The paper.* Cadence's properties follow from the modules'
specifications: MCP Safety by {cite}`lemma:cadence-safety`, and the timed
claims through {cite}`cor:chorus-correctness-within-cadence`, which says that
within Cadence every slot's Chorus instance gets what it needs from its
caller.

*The model.* Two files join the parts. [System.lean](../../../../Cadence/System.lean)
instantiates the glue's theorem at the Conductor's and Chorus's own transition
systems, with the MVBA model inside Chorus. The files under
[Composed](../../../../Cadence/Composed/Schedule.lean) run the glue, the
Conductor and Chorus on one clock and prove every condition each module
takes from its caller as a theorem about the composed run. The ACS stays an
assumed module throughout.

*The end results* are the composed claims, which
{chapter Claims}[chapter 2] shows in full, each with its premises:

* MCP Safety for the composed system, with no timing premise,
  {decl}`Cadence.system_positional_log_safety`;
* Corollary 4, {decl}`Composed.corollary4`, from which the timed claims
  follow;
* bounded concurrency, {decl}`Composed.boundedConcurrency`
  ({cite}`lemma:cadence-bounded-concurrency`);
* liveness and censorship resistance, {decl}`Composed.liveness`
  ({cite}`lemma:cadence-liveness`) and {decl}`Composed.censorship`
  ({cite}`def:censorship-resistance`), each also at the sharper recovery
  time ({decl}`Composed.liveness_sharp`, {decl}`Composed.censorship_sharp`).

The witness model, {decl}`Composed.Witness.liveness_premises_satisfiable`
and its siblings, meets all the premises at once.

*Further detail:* [Premises.md](../../../Premises.md) §0 (the premises of
the composed claims), [CompositionContracts.md](../../../CompositionContracts.md)
§6–§7 (the composed system, and the seams that remain),
[ConductorBounds.md](../../../ConductorBounds.md) §4 and §6 (the composition
of the timed claims, and the timing model). [Cadence.lean](../../../../Cadence.lean) lists every end result of
the development with its axiom pin.
