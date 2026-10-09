/-
Chapter 5 of the guide: Reviewing the contracts.
-/
import CadenceGuide.Elements
import CadenceGuide.ChapterList

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "Reviewing the contracts" =>
%%%
file := "contracts"
%%%

_How to check that each module contract asks only for what a real protocol delivers, field by field; assumes chapters 1 and 3._

The modules of Cadence meet through contracts. Chorus sees the MVBA inside
it only through the MVBA's contract, and the glue sees Chorus and the
Conductor only through theirs. That is what lets each proof stay the size of one
module, and it moves part of the audit to the contracts themselves: a
contract that promises too much makes every proof above it too easy. This
chapter shows how to read a contract, what can go wrong with one, and gives
the checklist for each.

# What a contract is

A contract is a Lean class: a list of fields, stated over an abstract state
type that the class leaves open. Each of the paper's modules is one contract
in [Interfaces.lean](../../../../Cadence/Interfaces.lean), and the class
states the whole module, its interface and every property, whether this
development proves it or not.

* *Inputs are transitions.* A paper input such as `complete(s)` is a relation
  between a state and the next; the caller gives it by moving to a state
  that satisfies it.
* *Outputs are observables.* A paper output such as `open(s)` is a predicate
  on the state that the caller reads. Every observable only ever becomes
  true, and a module's internal steps never fabricate a correct validator's
  input.
* *Properties are fields too.* Agreement, termination and the bounds are
  fields whose type is a statement about the transitions and observables.

Each module is two classes over the same transition system. The *safety
fragment* ({decl}`SlotConsensusSafety`, {decl}`OrchestratorSafety`,
{decl}`MVBASafety`, {decl}`ACSSafety`) holds what can be said about a
reachable state or a single step. It must be first-order, because a Veil
model that consumes the contract hands every field of it to the SMT solver.
The *temporal level* ({decl}`SlotConsensusTemporal` and its siblings) holds
everything stated over runs: termination, the timing bounds, and the
execution model under which they hold. The full class, {decl}`SlotConsensus`
for {cite}`mod:slotconsensus`, is the two together.

A contract has a guarantee side and a rely side. The guarantee side is the
fields. The rely side is explicit at the temporal level, in two places: what
the caller must do appears as antecedents of a field, and what the
environment must do is the field `Admissible`, the runs under which the
timed fields hold, which each implementation defines. The safety fields have
no rely side: they hold whatever the caller does.

*Proven* means that a declaration of the development builds a value of the
class from a model, every field proven. The table below is computed from the
compiled development: for each contract, what provides it.

{contracts}

Three of the four modules have a protocol model behind them: Chorus meets
Module 1 ({decl}`Chorus.slotConsensusFull`), the Conductor meets Module 2
({decl}`Conductor.conductorFull`), and the supplement's MVBA meets Module 3
({decl}`Mvba.mvbaFull`). The ACS has only an ideal model, and is an assumed
module; a section below says what that means.

# The escape-hatch question

A proof that consumes a contract takes every field as given. So a field that
promises more than a distributed protocol could deliver is an escape hatch:
a proof above it can discharge a hard step through the field instead of
through the protocol, and the proof is still correct.

An illustration, constructed for this guide. Chorus finalizes a slot on a
fast path, or on a fallback path that ends in the MVBA. Suppose the
fast path had a bug that stalls it, and the MVBA contract promised that every
correct validator decides within `ℓ`, with no condition on its caller and no
condition on the network. Chorus's termination proof would then go through:
every stalled slot falls back, and the contract field supplies the decision.
The theorem would be true, and it would say nothing about Chorus's main
route, and the fallback it rests on would be one that no message-passing
MVBA implements. Nothing in the proof would look wrong; the hole is in what
the contract asks.

Strength of this kind hides in three places.

* *A property stronger than the paper's.* The contract's field drops a
  condition the paper's module has, or adds a conclusion it lacks. Compare
  each field with the module it states.
* *The execution model.* `Admissible` is data the implementation supplies,
  and a timed field holds only in admissible runs. Defined as "the timed
  fields hold", it makes every timed field true by definition. The contract
  forbids only the empty definition, through `admissible_exists`, so the
  definition is one line to read in every instance. For a protocol it must
  name scheduling, network and timer conditions only.
* *Observables the instance defines.* A property conditional on an
  observable is as strong as the observable's definition. Proposal
  inclusion in Module 1 holds for an on-time proposal, and "on time" is an
  observable each implementation defines; defined as never true, the
  property says nothing.

:::claims (title := "What you check, per field")
1. Does the field say what the paper's module says, no more? The *Says*
   column gives the field's own description; the paper's module is cited at
   the class.
2. Is its rely side explicit: the caller's duties as antecedents, the
   environment as `Admissible`?
3. Could a message-passing protocol meet it, run by validators that know
   only their own state and the messages they received, against Byzantine
   validators?
4. What proves it? A protocol model, whose own audit is
   {chapter ModelIdioms}[chapter 4]'s; an ideal
   model, which shows only that the field can be met; or nothing, which makes
   the field an assumption of every claim above it.
:::

# The checklists

One table per contract, read from the compiled class. *Says* is the first
sentence of the field's description. *Level* is the safety fragment or the
temporal level. *Proven by* is the declaration that provides the field: a
protocol model, or, for the ACS, _assumed_, with the ideal model that shows
the field can be met. A field without a description, or one that no protocol
model provides in a contract that is not assumed, fails the guide's build,
so these tables cannot fall behind the classes.

The fields fall into two kinds. Most are *mechanical*: an input is a
transition, a record only ever becomes true, an input records itself and
nothing else, nothing is recorded initially. They make the interface exact
and are quick to check. The rest are the paper's properties and the
execution model, and they carry the weight of the review.

## Slot consensus: Chorus

{cite}`mod:slotconsensus`, one instance per slot. The temporal
level's termination takes two caller conditions as antecedents, every
correct validator participating and none abandoning before it finalizes:
Chorus's termination needs both and the module does not state them (finding
P13, {chapter Claims}[chapter 2]).

{contractFields SlotConsensus}

The timing strengthenings Chorus proves beyond Module 1, termination within
`ℓ` and totality within `d_tot`, which the Conductor's proofs consume, are a
level of their own:

{contractFields SlotConsensusWithTotality}

## Slot scheduling: the Conductor

{cite}`mod:orchestrator_2`. Totality and recovery hold only
"when run within Cadence": a caller that never completes a slot keeps every
validator in the first window. The contract states the two conditions the
paper's proofs take from the caller as antecedents (finding P15).

{contractFields Orchestrator}

{contractFields OrchestratorWithTotality}

## The MVBA

{cite}`mod:mvba`, as the supplement's leader-based protocol
meets it. Agreement is over a meta-block's entries, and the fragment includes
the decision handoff, a decision's certificate that another validator can
accept, and the availability the MVBA waits for, which its caller reports as
an input (finding P12).

{contractFields MVBA}

# The ACS, an assumed module

The paper specifies the ACS as {cite}`mod:acs` and leaves its
protocol open (finding P17). The Conductor and the composed claims are
therefore proven for every ACS that meets the contract, and every field of
it is an assumption of those claims:

{contractFields ACS}

Two fields go beyond Module 4. A correct validator's decided set holds at
most one pair of each validator, and the validity count is of distinct
validators. The Conductor's median argument needs both, Module 4 does not
state them (finding P16), and every ACS that collects one signed proposal per
validator meets them.

*The ideal model.* An assumption is only worth making if it can be met.
[IdealAcs.lean](../../../../Cadence/Conductor/IdealAcs.lean) meets both levels
of the contract, every field proven ({decl}`Cadence.IdealAcs.acsSafety`,
{decl}`Cadence.IdealAcs.acsTemporal`), and the composed witness of
{chapter Claims}[chapter 2] runs it in every window. It is the contract's
model, not a protocol, and it shows exactly the strength the escape-hatch
question looks for:

* *a global state*: one decided set per instance, fixed by a single internal
  step that every validator then reads;
* *knowledge of the fault pattern*: the step that fixes the set checks the
  correct validators' pairs against their proposals, which needs to know who
  is correct;
* *timing by definition*: its admissible runs are those in which its two
  timing guarantees hold whenever its two assumptions do;
* *no adversary*: it sends no messages, and a Byzantine validator's proposal
  is just another internal step.

So it shows that the contract is consistent: all of its fields hold together.
Whether a message-passing protocol meets them is the open part, and the
reason the front page names the ACS as an assumed module.

# The bridges and the fault pattern

Three places in the composition are written down rather than derived, and an
auditor reads each.

* *The MVBA certificate bridge.* The paper's validity check on a meta-block
  verifies the certificates the meta-block carries. Chorus checks a decided
  entry's certificate against its own network relations instead, because
  the MVBA's validity predicate is fixed before Chorus's state exists and
  cannot mention it. The check is stated at Chorus's decision handlers, and
  its liveness direction is the premise {decl}`Chorus.ValidBridge`
  ({chapter ReadingModel}[chapter 3] reads the handler).
* *The ACS median bridge.* Each validator computes a new window's first
  slot from its own decided set, and the Conductor model assumes two things
  of that computation: it depends on the decided set alone, and two correct
  validators' pairs of the set bracket it, one at or below it and one at or
  above. The bracket stands in for the median the paper takes as the first
  slot: that the lower median meets both, for every ACS meeting the
  contract and at most `f` Byzantine validators, is a theorem,
  {decl}`Cadence.lowerMedian_first_assumptions`.
* *The fault pattern.* MCP Safety takes the hypothesis that the Conductor
  and Chorus agree on who is Byzantine. The timed claims state every module
  at one fault pattern and need none.

[CompositionContracts.md](../../../CompositionContracts.md#7-the-remaining-seams-named)
§7 names every seam of the composition, these three included.

# What a machine check would need

The Lean classes accept any instance: a value with every field proven is an
instance, whether it comes from a protocol model or from an ideal
functionality with global knowledge. The ideal ACS is the proof. So the
question this chapter asks, whether a contract's fields could be met by a
distributed protocol, is the auditor's for every contract.

For the three contracts with a protocol model, the answer reduces to the
model: the field is proven of a Veil model, and
{chapter ModelIdioms}[chapter 4]'s audit, which
checks that every action reads only what its validator could know, is what
makes that model distributed. The ACS has only its ideal model. A tool
that checks the locality of a model's actions, and a reference ACS built
from the MVBA, are further work ({chapter OpenIssues}[chapter 8]).

# Further detail

* [CompositionContracts.md](../../../CompositionContracts.md) — how the
  contracts are designed (§2), what each implementation proves of its own
  (§5), and the seams (§7).
* [Interfaces.lean](../../../../Cadence/Interfaces.lean) — the contracts, each
  class with the paper's module and where every field is discharged.
* [Architecture.md](../../../Architecture.md#4-the-meta-assumption-inventory)
  §4 — everything the development assumes rather than proves, the ACS among
  it.
