/-
The guide to the Cadence verification: the front page, and the chapters in
reading order.

A Verso document, and so a Lean program. It carries no facts of its own:

* every statement is the real declaration, embedded from the compiled
  development (`{claim}`), and every Veil model declaration is quoted from the
  rendered sources (`{model}`) — so a renamed or removed declaration fails
  this build rather than leaving a stale quotation;
* every status box, checklist and table is computed when the guide is built
  ([Elements.lean](CadenceGuide/Elements.lean) lists the elements): the
  kernel's axiom footprint, the module contracts a result is conditional on,
  and which declarations discharge them.

The one kind of hand-written code is an *outline*, marked as such and always
followed by the real declaration.

Each chapter is a file of its own under [Chapters](CadenceGuide/Chapters) and
a page of its own on the site, so the chapters can be written independently.
This file holds the front page and the order of the chapters; the front
page's chapter list ([ChapterList.lean](CadenceGuide/ChapterList.lean)) reads
that order, and each chapter's title and opener, from the files.
-/
import CadenceGuide.Elements
import CadenceGuide.ChapterList
import CadenceGuide.Chapters.Approach
import CadenceGuide.Chapters.Claims
import CadenceGuide.Chapters.ReadingModel
import CadenceGuide.Chapters.ModelIdioms
import CadenceGuide.Chapters.Contracts
import CadenceGuide.Chapters.Components
import CadenceGuide.Chapters.Checking
import CadenceGuide.Chapters.OpenIssues
import CadenceGuide.Chapters.EarlierWalkthrough
import CadenceGuide.Chapters.Specimen

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "Cadence Verification" =>

%%%
shortTitle := "Cadence Verification"
%%%

_What is proven about the Cadence protocol, and what it rests on._

:::claims (title := "What this project claims")

*The paper.* The development corresponds to revision `48cac9a` of the
Cadence paper repository: the main body of _Cadence: Extreme Pipelining
with Multiple Concurrent Proposers_ ([arXiv:2607.02275](https://arxiv.org/abs/2607.02275)),
together with its internal supplement, which specifies the MVBA.

*The composed system.* Cadence runs one Chorus instance per slot,
scheduled by the Conductor, with the supplement's MVBA inside each Chorus
instance. For `n = 3f + 1` validators, at most `f` of them Byzantine, the
composed system satisfies:

* *MCP Safety*, {cite}`def:safety`: two correct validators
  never hold different entries at the same position of their logs. It
  holds in every reachable state, with no timing premise.
  {decl}`Cadence.system_positional_log_safety`
* *{cite}`cor:chorus-correctness-within-cadence`*: within
  Cadence, every slot's Chorus instance gets everything it needs from its
  caller. So every slot is finalized by every correct validator within
  `5Δ + ℓ_MVBA` after all correct validators have joined it, counted from
  GST at the earliest, and within `Δ` of the first correct validator to
  finalize it. {decl}`Composed.corollary4`
* *Bounded concurrency*, {cite}`lemma:cadence-bounded-concurrency`:
  no correct validator takes part in more than `2W − p` slot instances at
  once, where `W` and `p` are the Conductor's window parameters.
  {decl}`Composed.boundedConcurrency`
* *𝓡-Liveness*, {cite}`lemma:cadence-liveness` for
  {cite}`def:liveness`: every slot that starts at least `𝓡 = 2Wτ` after GST
  is in the log of every correct validator, where `τ` is the time between
  consecutive slot starts. The same holds at the smaller
  `𝓡 = (W + p − 1)τ`. {decl}`Composed.liveness`, {decl}`Composed.liveness_sharp`
* *𝓡-Censorship resistance*, {cite}`def:censorship-resistance`:
  for every such slot, each correct proposer's proposal is in that slot's
  entry of every correct validator's log. {decl}`Composed.censorship`,
  {decl}`Composed.censorship_sharp`

*The modules.* Each module meets the paper's specification of it, every
property proven:

* *Chorus* meets {cite}`mod:slotconsensus`: agreement, proposal
  inclusion, hiding (its protocol half), quiescence, termination within
  `5Δ + ℓ_MVBA` ({cite}`lemma:chorus-termination`) and totality within
  `Δ` ({cite}`prop:chorus-totality`). {decl}`Chorus.slotConsensusFull`,
  {decl}`Chorus.chorusWithTotality`
* *The Conductor*, {cite}`algorithm:conductor`, meets
  {cite}`mod:orchestrator_2` for every ACS that meets {cite}`mod:acs`:
  agreement on the open slots, integrity, totality within `Δ`
  ({cite}`lemma:conductor-totality`), `(2W − p)`-boundedness
  ({cite}`lem:boundedness`) and `(2Wτ)`-recovery
  ({cite}`lemma:conductor-recovery`). {decl}`Conductor.conductorFull`,
  {decl}`Conductor.conductorWithTotality`
* *The MVBA*, the supplement's leader-based protocol, meets
  {cite}`mod:mvba`: agreement, integrity, external validity, quiescence, and
  termination within an explicit `ℓ_MVBA` of order `fΔ`. {decl}`Mvba.mvbaFull`

*What the claims rest on.*

* *The ACS is an assumed module.* The paper leaves the ACS protocol
  open (finding P17), so the Conductor and the composed system are proven
  for every ACS that meets {cite}`mod:acs`. An idealized ACS, with
  global knowledge and no adversary, shows that Module 4 can be met; a
  message-passing protocol that meets it is outside this development.
* *Environment premises*, for every claim except MCP Safety: partial
  synchrony, in which every step a correct validator owes after GST
  happens within `Δ`; timers that fire on time; and the configuration's
  constraints on the window parameters. The composed claims and the
  Conductor's bounds also take local steps to need no time (`δ = 0`), as
  the paper does; Chorus's bounds are proven with an explicit `δ` term
  and are quoted above at `δ = 0`, and the MVBA's bound holds for any `δ`.
  Censorship resistance also reads "by the deadline" as inclusive
  (finding P19). The full list is one page, [Premises.md](../Premises.md) §0,
  and one model of the composed system meets all of it at once.
* *Cryptography*, stated as assumptions: each signed message is
  attributed to its signer, so signatures cannot be forged; threshold
  encryption keeps a proposal hidden until the decryption shares are
  released.
* *Modelling idioms*, which {chapter ModelIdioms}[chapter 4] explains: the network keeps every
  message once sent, and protocol steps react only to the presence of
  messages; the state of all validators is one global state, in which each
  step reads its own validator's records and the network; Chorus's timers
  are one shared phase that the environment advances and every
  validator's guards read, a global read standing for each validator's
  own clock; Byzantine
  validators act through explicit adversary actions; Chorus is modelled
  for one slot, with erasure coding abstracted.
* *Trusted tools*: Lean's kernel, and Veil's translation of each model
  into the conditions proven about it. SMT solver results are rebuilt as
  Lean proofs and checked by the kernel.

Every theorem is checked by Lean's kernel from Lean's three standard
axioms, and [Cadence.lean](../../Cadence.lean) pins the axioms of each.
:::

Cadence is a Byzantine fault-tolerant consensus protocol in which several
proposers contribute to every slot and consecutive slots run in an
overlapping pipeline. This project verifies it with machine-checked proofs.
The protocol is written as models in Veil, a language for describing
distributed protocols as state machines, embedded in the Lean proof
assistant. The models follow the paper's own decomposition: Chorus, the
consensus of one slot; the MVBA that Chorus runs when its fast path fails;
the Conductor, which schedules the slots; and the glue that runs one Chorus
instance per slot and assembles the log. Each is proven against the paper's
specification of the module it implements, and the claims above follow from
those proofs. The pages of this guide show the compiled declarations
themselves, and every status box on them is computed from the proofs while
the guide builds.

{figure "docs/diagrams/modules-contracts.svg" (caption := "The modules, the contracts between them, and the composed claims.")}

The guide is one story, read front to back. Each chapter opens with a line
saying what it covers and what it assumes, so you can stop where your
question is answered or skip to the part you want to check.

{chapterList}

{include 1 CadenceGuide.Chapters.Approach}

{include 1 CadenceGuide.Chapters.Claims}

{include 1 CadenceGuide.Chapters.ReadingModel}

{include 1 CadenceGuide.Chapters.ModelIdioms}

{include 1 CadenceGuide.Chapters.Contracts}

{include 1 CadenceGuide.Chapters.Components}

{include 1 CadenceGuide.Chapters.Checking}

{include 1 CadenceGuide.Chapters.OpenIssues}

{include 1 CadenceGuide.Chapters.EarlierWalkthrough}

{include 1 CadenceGuide.Chapters.Specimen}
