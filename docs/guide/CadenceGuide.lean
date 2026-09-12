/-
The guide to reading the Cadence formalization.

This is a Verso document, which means it is a Lean program: every
`{name …}` below is resolved against the compiled development, so a renamed
declaration breaks this build rather than rotting a link, and every
`{docstring …}` is the real docstring from the source rather than a
paraphrase of it.

The guide deliberately states **no facts of its own** — no counts, no
measurements, no status claims. Those live in `docs/` and in the generated
trust boundary, and the guide points at them. Its job is to make the sources
readable, not to be a second source of truth.
-/
import VersoManual

-- Imported for the sake of the references below: `{name …}` resolves in this
-- module's environment, so the guide sees what the development compiled.
import Cadence.Composition
import Cadence.System

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Reading the Cadence formalization" =>

%%%
shortTitle := "Reading Cadence"
%%%

This guide is for a reviewer who wants to read the Lean sources of the Cadence
verification and understand what they say. It is not the documentation of
record: the design documents under `docs/` are comprehensive, and the sources
themselves are the source of truth. This guide is the thing that makes them
approachable — it introduces the vocabulary, shows how the pieces fit, and
points at the places that matter.

It assumes you know BFT consensus. It assumes nothing about Lean, and nothing
about Veil, the domain-specific language the protocol models are written in.

You do not need to read any proof. A theorem in Lean holds when the kernel
accepts it, relative to the axioms it uses, so what an auditor has to read is
the _statements_, the _model_ they are about, and the _axioms_ they rest on.
Everything below is aimed at those three.

# Start with the smallest model

The development has five protocol models. Four of them are large. The fifth —
the pipelining glue — is small, has no cryptography, no quorums and no clock
arithmetic, and yet it proves the property the whole system exists for. It is
the right place to learn to read the others.

The glue is the paper's `algorithm:cadence`: the layer that runs one slot
consensus instance per slot under an orchestrator, and assembles their outputs
into a log. Its source is `Cadence/Cadence.lean`.

## What it proves

The top-level correctness property of a multiple-concurrent-proposer protocol
is that correct validators never disagree about the log. In the formalization
that is:

{docstring Cadence.positional_log_safety}

Two things in that statement are worth dwelling on, because they are the shape
of every result in this development.

First, it is stated *for any* orchestrator and slot consensus that satisfy
their contracts — not for the Conductor and Chorus specifically. The glue is
verified against interfaces, so its theorem is about a family of systems.

Second, that generality is discharged elsewhere. The composed statement, with
the real implementations plugged in and no interface assumption left, is:

{docstring Cadence.system_positional_log_safety}

# How a model is written

A Veil model is a state machine. Three kinds of declaration make it up, and
recognising them is most of what it takes to read one.

* *State* — `relation` and `individual` declarations. These are the mutable
  facts the protocol tracks. In the glue they are things like which slots a
  validator has opened and what it has appended to its log.
* *Actions* — `action` declarations. These are the protocol's steps. Each
  has guards, written `require`, and updates. An action may fire whenever its
  guards hold; nothing forces it to.
* *Properties* — `safety` and `invariant` declarations. A `safety` is
  something the protocol promises; an `invariant` is a helper, needed to make
  the promises provable by induction but not itself interesting.

The glue has six actions. Their names are collected, by the tool, into a type
of labels — {InlineLean.name Cadence.Label}`Cadence.Label`, one constructor per
action, which you can read as the model's alphabet. It carries no
documentation of its own, because it is generated rather than written: that is
the first sign of the boundary described next.

Everything else in the file is one of the three kinds above, or a comment
explaining a modelling decision. That is the whole surface.

## Why the elaborated form looks different

Reading the _generated_ Lean rather than the source is not recommended, and it
is worth knowing why. Veil is a surface language: a declaration such as
`action append` elaborates mechanically into a family of Lean definitions —
transition relations, frame conditions, label constructors — with names and
shapes chosen by the translation rather than by a human. Those definitions are
what the kernel checks, and they are correct, but they are not written to be
read.

So: read the model sources, and use the generated artefacts only when you want
to confirm that something exists. This guide links to the sources.

# Contracts, and what the glue assumes

The glue does not contain a slot consensus or an orchestrator. It _consumes_
them, through the two interfaces the paper specifies. In the source this is an
`instantiate` line, and the effect is that every property of the interface is
available to the prover as an axiom, while the glue's own code can only reach
the sub-protocol through the operations the interface declares.

The two interfaces it consumes are {InlineLean.name OrchestratorSafety}`OrchestratorSafety`
and {InlineLean.name SlotConsensusSafety}`SlotConsensusSafety`. Both are Lean type classes,
declared in `Cadence/Interfaces.lean`, which is worth reading next: it states
every property of every module of the protocol, whether or not this development
proves it.

That last point is the heart of the audit surface, and it is deliberate. Each
paper module is split into two classes: a state-level fragment that the models
consume and the implementations prove, and a temporal level carrying the timing
and liveness obligations. The implementations provide instances of the first.
For the second — {InlineLean.name SlotConsensusTemporal}`SlotConsensusTemporal` and its
siblings — this development provides *no instance at all*, and that absence
is the complete statement of what it does not prove.

Nothing has to be believed about that; it is derivable, and the generated trust
boundary derives it.

# Where to go from here

* `Cadence/Interfaces.lean` — the module contracts, and so the vocabulary the
  rest of the development is stated in.
* `Cadence/Conductor.lean` — the next model up in size, and the one the glue's
  orchestrator interface is instantiated by.
* `Cadence/Chorus.lean` — the large one: per-slot consensus, where the
  cryptography and the quorum reasoning live.
* `docs/Architecture.md` §4 — the inventory of everything the machine does not
  establish. Short, and the checklist an auditor works through.
