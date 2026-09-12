/-
The guide to reading the Cadence formalization.

A Verso document, and so a Lean program: every `{InlineLean.name …}` is
resolved against the compiled development and every `{docstring …}` is the
real docstring from the source, so a renamed declaration breaks this build
rather than rotting a link.

The guide carries no facts of its own — no counts, no measurements, no status
claims. Those live in `docs/` and in the generated trust boundary. Simplified
code blocks are illustrations, and the real declaration always follows.
-/
import VersoManual

-- The guide resolves its references in this module's environment, so it
-- imports what it talks about.
import Cadence.Composition
import Cadence.System

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Reading the Cadence formalization" =>

%%%
shortTitle := "Reading Cadence"
%%%

This guide introduces the Lean sources of the Cadence verification: the
vocabulary they are written in, how the pieces fit together, and which places
matter. Comprehensive and more technical documentation is in the `docs/`
folder.

It assumes you know BFT consensus, and nothing about Lean or about Veil, the
language the protocol models are written in.

You can skip the proofs. A theorem in Lean holds once the kernel accepts it,
relative to the axioms it uses, so what an auditor reads is the _statements_,
the _model_ they are about, and the _axioms_ they rest on.

# The smallest model

Start with `Cadence/Cadence.lean`, the pipelining glue. It is the paper's
`algorithm:cadence`: the layer that runs one slot-consensus instance per slot
under an orchestrator and assembles their outputs into a log. It has six
actions, no cryptography, no quorums and no clock arithmetic — and it proves
the property the whole system exists for.

That property is log agreement: two correct validators never hold different
entries at the same position. In outline:

```
theorem positional_log_safety :
    reachable st →
    ¬ byz i → ¬ byz j →
    entryAt i p = some v →
    entryAt j p = some w →
    v = w
```

The real statement adds what the outline leaves out: the module's type
parameters, the fault model, and the two interfaces the glue is verified
against.

{docstring Cadence.positional_log_safety}

Read that as a theorem about a _family_ of systems: it holds for any
orchestrator and any slot consensus meeting their interfaces, rather than for
the Conductor and Chorus specifically. Plugging in the real implementations,
so that no interface assumption remains, happens in `Cadence/System.lean`:

{docstring Cadence.system_positional_log_safety}

# How a model is written

A Veil model is a state machine, and three kinds of declaration make it up.

* `relation` and `individual` declare the _state_ — the facts the protocol
  tracks.
* `action` declares a _step_, with guards written `require` and updates
  written `:=`. An action may fire whenever its guards hold; nothing forces
  it to.
* `safety` declares something the protocol promises. `invariant` declares a
  helper needed to make the promises provable by induction.

Simplified to the shape, the glue's append step and its agreement property
look like this:

```
relation appended (i : node) (s : slot) (v : pvector)

action append (i : node) (s : slot) (v : pvector) = {
  require finalized i s v        -- the slot consensus decided v for s
  require ready_to_append i s    -- every earlier slot is resolved
  appended i s v := true
}

safety [log_agreement]
  ∀ i j s v w, ¬ byz i → ¬ byz j →
    appended i s v → appended j s w → v = w
```

The real `append` carries more bookkeeping and `ready_to_append` is spelled
out over the glue's own relations, but the shape is this: a guarded update,
and a property quantified over correct validators.

Everything else in a model file is one of those three kinds, or a comment
explaining a modelling decision.

Veil elaborates each declaration into Lean definitions — transition
relations, frame conditions, label constructors — chosen by the translation
rather than written by hand. The kernel checks those; people should read the
model sources. One generated artefact is worth knowing by name, because it is
the model's alphabet: {InlineLean.name Cadence.Label}`Cadence.Label` has one
constructor per action.

# Contracts, and what is assumed

The glue contains neither a slot consensus nor an orchestrator. It consumes
them through the interfaces the paper specifies, written in the source as
`instantiate`:

```
instantiate orch : OrchestratorSafety node slot ostate time fm.byz
instantiate sc   : SlotConsensusSafety slot node proposal pvector scstate fm.byz
```

Two things follow. Every property of the interface becomes available to the
prover, so the glue's proofs use them directly instead of restating them. And
the glue reaches the sub-protocol only through the operations the interface
declares, so it cannot depend on how either one works inside.

The interfaces are Lean type classes in `Cadence/Interfaces.lean`, the
natural next file to read: it states every property of every module of the
protocol, whether or not this development proves it.

Each paper module is split in two. A state-level fragment —
{InlineLean.name OrchestratorSafety}`OrchestratorSafety`,
{InlineLean.name SlotConsensusSafety}`SlotConsensusSafety` — is what the
models consume and the implementations prove. A temporal level carries the
timing and liveness obligations. For the temporal level, including
{InlineLean.name SlotConsensusTemporal}`SlotConsensusTemporal`, this
development supplies no instance, and that absence is the full statement of
what it leaves unproven.

The generated trust boundary derives which contracts have an instance, so
that claim can be checked rather than taken.

# Where to go next

* `Cadence/Interfaces.lean` — the module contracts, and the vocabulary the
  rest of the development is stated in.
* `Cadence/Conductor.lean` — the next model up in size, and the one that
  provides the glue's orchestrator instance.
* `Cadence/Chorus.lean` — per-slot consensus, where the cryptography and the
  quorum reasoning live.
* `docs/Architecture.md` §4 — everything the machine does not establish, in
  one list. This is the auditor's checklist.
