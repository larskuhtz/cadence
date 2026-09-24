/-
The guide to auditing the Cadence formalization.

A Verso document, and so a Lean program. It carries no facts of its own:

* every statement is the real declaration, embedded from the compiled
  development (`{claim}`), and every Veil model declaration is quoted from the
  rendered sources (`{model}`) — so a renamed or removed declaration fails
  this build rather than leaving a stale quotation;
* every status box is computed when the guide is built
  (`docs/guide/CadenceGuide/Audit.lean`): the kernel's axiom footprint, the
  module contracts a result is conditional on, and which declarations
  discharge them.

The one kind of hand-written code is an *outline*, marked as such and always
followed by the real declaration.
-/
import VersoManual
import CadenceGuide.Audit

-- The guide resolves its references in this module's environment, so it
-- imports what it talks about.
import Cadence

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "Auditing the Cadence formalization" =>

%%%
shortTitle := "Auditing Cadence"
%%%

This guide walks an auditor through one complete result of the Cadence
verification: what it states, what it is proven from, and which parts a human
has to check. It assumes you know BFT consensus, and nothing about Lean or
about Veil, the language the protocol models are written in. The design
documents in the repository's `docs/` folder go deeper; the
[rendered sources](../sources/Cadence/) show every module as written.

A theorem in Lean holds once the kernel accepts it, relative to the axioms it
uses. So an audit reads three things, and none of them is a proof:

1. *The model* — the protocol as a state machine. Is it the protocol of the
   paper?
2. *The statements* — the theorems, and the module contracts they are stated
   against. Do they say what the paper claims?
3. *The meta-theory* — the arguments that sit above the models and connect
   them: why a property of the model is a property of the protocol. Most of
   it is mechanised; what is not is a short named list.

Everything else is mechanically checked, and this guide shows where the
checking is rather than asking you to take it on trust. The
[trust boundary](../trust-boundary.html) is the same information for every
end result of the development at once.

*How to read the boxes.* Under each statement is a box computed when this
guide is built, from the same compiled development the statement comes from.
It records the axioms the kernel found in the proof, and every module contract
the statement is _conditional on_, with the declarations that discharge it. A
green edge means no contract is assumed; an amber edge means the result holds
for any implementation of the listed contracts. The build fails if any proof
uses an axiom beyond Lean's standard three.

# The claim

The whole system exists for one property: two correct validators never hold
different entries at the same position of their logs. In outline:

```
theorem system_positional_log_safety :
    reachable st →                  -- any state the composed system can reach
    ¬ byz i → ¬ byz j →              -- two correct validators
    IsLog st i Li → IsLog st j Lj →  -- their logs
    Li[k] = Lj[k]                    -- agree at every common position
```

The real statement also names the three modules' configurations and one
genuine hypothesis, that Conductor and Chorus agree on who is faulty:

{claim Cadence.system_positional_log_safety}

The box lists one contract the result is still conditional on:
{decl}`ACSSafety`, the agreement-on-a-common-subset primitive that the
Conductor runs once per window. That is by design — the ACS is a standard
primitive whose implementation is out of scope — but it means the headline
theorem holds for every ACS meeting that contract, and an auditor should
read the contract's fields as an assumption. Every other module contract is
discharged inside this development. The rest of this guide takes the result
apart, into the pieces an auditor reads and the pieces the machine has
checked.

# How the claim is assembled

Cadence is built from modules, as in the paper: an orchestrator (the
Conductor) that decides which slots are open, a per-slot consensus (Chorus)
that decides each slot, and a thin layer — the _glue_, `Cadence/Cadence.lean`
— that runs one consensus instance per slot and assembles their outputs into
a log. The claim is proven in three steps, and the boxes show how the steps
plug together.

## Step 1 — the glue, against contracts

The glue does not contain an orchestrator or a slot consensus. It is written
and verified against their _contracts_ — the module specifications of the
paper, stated as Lean type classes — and its properties are proven by
induction over its actions: every action preserves a collection of
invariants, each preservation is a verification condition discharged by an
SMT solver, and every discharge is reconstructed as a proof term that the
kernel re-checks. Two properties carry the claim. Here they are as the model
states them, quoted from the source:

{model Cadence.Cadence "safety [log_agreement]" (proven := Cadence.reachable_log_agreement)}

{model Cadence.Cadence "safety [skip_agreement]" (proven := Cadence.reachable_skip_agreement)}

Both boxes are amber: the glue's properties hold for _any_ orchestrator and
slot consensus meeting the contracts, and the boxes name the declarations
that will later supply them.

## Step 2 — from slots to logs

The two properties are about slots. The claim is about positions in a list.
The step between them is plain Lean — a lemma about sorted lists, outside the
solver — and it keeps the contract hypotheses:

{claim Cadence.positional_log_safety}

## Step 3 — plugging in the implementations

Each contract is discharged by proving that an implementation meets it. The
Conductor meets the orchestrator contract outright:

{claim Conductor.orchestratorSafety}

Chorus meets the slot-consensus contract given an MVBA, the agreement
sub-protocol it runs internally; the `Mvba` model supplies that, and the
composed instance fills the constraint:

{claim Cadence.chorusInstance}

Instantiating Step 2 at these instances is the claim of the first section,
and that is why its box lists only the contract the Conductor itself
consumes. Every link in this chain is a
kernel-checked Lean term; what it rests on beyond that is the subject of the
last section.

# The model: what to check against the paper

A Veil model is a state machine. Three kinds of declaration make it up:

* `relation` and `individual` declare the _state_ — the facts the protocol
  tracks.
* `action` declares a _step_, with guards written `require` and updates
  written `:=`. An action may fire whenever its guards hold; nothing forces
  it to.
* `safety` declares something the protocol promises; `invariant` declares a
  helper needed to make the promises provable by induction.

The glue's final step, appending a decided slot to the log:

{model Cadence.Cadence "action append"}

Everything else in a model file is one of those kinds, or a comment
explaining a modelling decision. The questions for an auditor are whether the
guards and updates are the paper's `algorithm:cadence`, and whether the
modelling decisions the file documents are sound. The glue's header records
three, each argued in prose rather than checked:

* *How the sub-protocols appear.* The paper runs each handler atomically upon
  an event; the model separates the two, which admits strictly more
  behaviours, so every safety property holds of the atomic algorithm a
  fortiori.
* *State locality.* Every state item is either one validator's own record or
  sub-protocol state read through a contract.
* *Threat model.* Byzantine validators take no glue actions; they act only
  inside the sub-protocols, whose contracts constrain correct validators only.

Read them in the [header of the glue](../sources/Cadence/Cadence/).

The sub-protocols enter the glue as class constraints, written `instantiate`:

{model Cadence.Cadence "instantiate orch"}

{model Cadence.Cadence "instantiate sc"}

Every property of a contract is then available to the solver as an axiom of
the model, and the glue reaches the sub-protocol only through the operations
the contract declares — so it cannot depend on how either one works inside,
and no glue guard or invariant restates a contract property.

# The contracts: what is proven, what is assumed

The contracts are in `Cadence/Interfaces.lean`, which states every property
of every paper module, proven or not. Each paper module is split in two. A
first-order fragment — {decl}`OrchestratorSafety`, {decl}`SlotConsensusSafety`,
… — is what the models consume and the implementations prove. A temporal
level carries the timing and liveness obligations. This table is computed
from the development: a contract with no providing declaration is an
obligation it leaves open.

{contracts}

The rows marked _assumed_ are the whole of what this development owes: each
temporal class is stated over its fragment's own relations, so there is no
second place where these obligations are written down.

# What no machine checks

Three kinds of argument sit above the kernel and are believed rather than
derived. They are the meta-theory an audit has to read.

* *The modelling arguments* recorded in each model's header — for the glue,
  the three listed above; for Chorus, also the monotone-network contract
  (`docs/ChorusDesign.md` §3.1.1), which Veil does not enforce.
* *The assumed contracts* in the table above, read as assumptions: for the
  headline claim, {decl}`ACSSafety`.
* *The interpretation of each contract's vocabulary* in its consumer, where a
  class parameter has to be read in the consumer's own terms. The glue has
  none; two exist elsewhere, and `docs/CompositionContracts.md` §7 lists them.
* *The tooling* — Lean's kernel, and Veil's generation of the verification
  conditions from a model.

`docs/Architecture.md` §4 is the complete list, and the auditor's checklist.
