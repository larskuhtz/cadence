/-
Chapter 2 of the guide: Claims, premises, witnesses.
-/
import CadenceGuide.Elements
import CadenceGuide.PremiseCover
import CadenceGuide.ChapterList

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "Claims, premises, witnesses" =>
%%%
file := "claims"
%%%

_Each end claim with its premises in plain words, the model that meets them all, and what the review found in the paper; no Lean needed._

The front page states each claim in a sentence. This chapter gives each one
as the kernel checked it, and then asks the three questions an auditor asks
of a conditional theorem: what does it assume, can the assumptions hold at
all, and are they the right ones? The first two have machine-checked
answers. The third is the auditor's, and the chapter ends with what the
review of the paper found that bears on it.

# The composed claims

These theorems speak about the composed system: the per-slot consensus
Chorus, scheduled by the Conductor, with the supplement's MVBA inside each
Chorus instance, for `n = 3f + 1` validators of which at most `f` are
Byzantine. Each is shown below as it is stated in the development: its
description, a box computed when this guide is built, and the formal
statement, collapsed.

The box records two things. *Axioms* are the axioms the kernel found in the
proof; the build fails on anything beyond Lean's standard three. *Conditional
on* lists every module contract the theorem takes as a hypothesis, with what
discharges it. A contract with no protocol instance is an assumption of the
claim, and for every claim here that contract is the ACS's: the paper leaves
the ACS protocol open, so the claims hold for every ACS that meets Module 4
({cite}`mod:acs`). Chapter 5 reviews that contract field by field.

## MCP Safety

Two correct validators never hold different entries at the same position of
their logs ({cite}`def:safety`). It holds in every reachable state, with no
timing premise:

{claim Cadence.system_positional_log_safety}

Besides the ACS contract, the statement takes the three modules'
configurations and one hypothesis, `hbyz`: the Conductor and Chorus agree on
which validators are Byzantine. The front page omits it as a configuration
fact. The four timed claims below need no such hypothesis, because they state
every module at one fault pattern, {decl}`Composed.fmF`.

## Corollary 4

Within Cadence, every slot's Chorus instance gets everything it needs from
its caller ({cite}`cor:chorus-correctness-within-cadence`). Literally, the
theorem says that in every run meeting the premises below, each slot's part
of the run meets the three conditions Chorus's timed contract takes from its
caller: participation synchronized within `Δ`, no abandoning before
finalizing, and no start before the slot's starting time.

{claim Composed.corollary4}

The consequences are what a reader cares about, and each is a theorem of its
own: every slot is finalized by every correct validator within `5Δ + ℓ_MVBA`
after all correct validators have joined it, counted from GST at the earliest
({decl}`Composed.corollary4_bounded_termination`), and within `Δ` of the first
correct validator to finalize it ({decl}`Composed.corollary4_totality`).

## Bounded concurrency

No correct validator takes part in more than `2W − p` slot instances at once
({cite}`lemma:cadence-bounded-concurrency`), where `W` and `p` are the
Conductor's window parameters. Like MCP Safety, it is a property of every
reachable state:

{claim Composed.boundedConcurrency}

## Liveness

Every slot that starts at least `𝓡 = 2Wτ` after GST is in the log of every
correct validator ({cite}`def:liveness`, {cite}`lemma:cadence-liveness`),
where `τ` is the time between consecutive slot starts:

{claim Composed.liveness}

The same holds at the smaller `𝓡 = (W + p − 1)τ`, on the same premises
({decl}`Composed.liveness_sharp`); the paper's bound is not tight (finding
P18, below).

## Censorship resistance

For every such slot, each correct proposer's proposal is in that slot's entry
of every correct validator's log ({cite}`def:censorship-resistance`):

{claim Composed.censorship}

Again at `(W + p − 1)τ` as well ({decl}`Composed.censorship_sharp`).
Censorship resistance takes two premises more than liveness, both listed
below.

# Claim, premise, witness

A conditional theorem is only as good as its premises, so the premises play
the role of the claim's axioms. Four properties of a premise set matter, and
the development settles three of them by machine:

* *Completeness.* The claim is proven from exactly the premises it states,
  and the kernel checks the proof with no further axiom. Nothing is assumed
  that the statement does not show.
* *Consistency.* All premises of a claim hold together in one model, a
  *witness*. A claim whose premises could never hold together would be true
  and say nothing.
* *Each premise is used.* Every premise is consumed by some step of the
  proof, so none can be dropped without a replacement.
* *Plausibility* is the auditor's judgement: whether the premises describe
  the runs a real network and a real implementation produce. No tool checks
  it, and the premise ledger gives each premise a line on why it is
  plausible and which sentence of the paper it formalises.

The figure shows the four for the liveness claim.

{figure "docs/diagrams/claim-premise-witness.svg" (caption := "One claim, its premises, the proof step that uses each, and the one model that meets them all. Plausibility is the part no tool checks.")}

# The premises in plain words

What the composed claims assume, simplified. A line marked _paper_ states
something the paper states or works under; a line marked _not stated in the
paper_ is a reading or a modelling choice the development adds, and each of
those is either a finding for the paper's authors or argued in the ledger.
Every condition one module needs from another is proven inside the
composition, so what remains is the environment and the configuration. The
full list, with each premise's use and witness, is
[Premises.md](../../../Premises.md#0-the-composed-system-the-premises-of-the-end-claims) §0.

:::premises (claims := "Composed.corollary4 Composed.boundedConcurrency Composed.liveness Composed.liveness_sharp Composed.censorship Composed.censorship_sharp")
* *Validators, faults and time.* `n = 3f + 1` validators, at most `f`
  Byzantine, one notion of "correct" for every module; clock readings can
  be added, compared and cancelled, and no time lies beyond every multiple
  of a delay. _Paper._
  ([§0.2](../../../Premises.md#02-the-instance-and-the-configuration), [§2.1](../../../Premises.md#21-validators-and-faults), [§2.6](../../../Premises.md#26-time))

* *Partial synchrony.* After GST, every step a correct validator owes
  happens within its bound: `Δ` for a message from a correct validator,
  `δ` for a local step. Nothing is owed on a Byzantine validator's message.
  _Paper._ The Conductor's and every slot's timing models,
  {decl}`Composed.OrchAdmissible` and {decl}`Composed.SlotAdmissible`, carry
  it. ([§4.1](../../../Premises.md#41-timedjustice-δδ-justice), [§4.4](../../../Premises.md#44-boundedjustice-δ-justice))

* *Handlers run with their events.* Each handler of the glue and of the
  Conductor fires when its event occurs, and local steps take no time
  (`δ = 0`), as throughout the paper. _Paper._ {decl}`Composed.GlueRows`;
  together with the two timing models above, this is the whole run premise,
  {decl}`Composed.SysSync`. ([§0.3](../../../Premises.md#03-the-run-composedsyssync), [§9.3](../../../Premises.md#93-the-run-conductorsync))

* *Timers fire on time.* Chorus's deadline timers, the MVBA's view timer and
  the Conductor's slot openings fire at their landmarks on synchronized
  clocks. _Paper._ ([§4.2](../../../Premises.md#42-phasepunctual-p-phase), [§4.5](../../../Premises.md#45-timerpunctual-t-timer), [§9.3](../../../Premises.md#93-the-run-conductorsync))

* *Fair scheduling.* An enabled step of a correct validator eventually
  happens. Nothing is asked of a Byzantine validator's steps, so no progress
  relies on the adversary's help. _Not stated in the paper:_ weak fairness is
  the untimed form of the paper's network, a modelling choice.
  ([§3.1](../../../Premises.md#31-fjustice-f-justice-for-chorus), [§3.3](../../../Premises.md#33-mvbafjustice-f-justice-for-the-mvba))

* *The assumed ACS.* Every window's ACS meets Module 4 in the run, with the
  system's `Δ`, a latency `ℓ` and the system's fault bound. _Paper:_ Module 4
  is the paper's; the paper leaves its protocol open (P17).
  {decl}`ACSTemporal` ([§0.2](../../../Premises.md#02-the-instance-and-the-configuration), [§9.2](../../../Premises.md#92-the-instance-the-schedule-and-the-assumed-acs))

* *The configuration.* The window parameters `W`, `p`, `τ` meet the paper's
  four parameter assumptions; slots start `τ` apart, without end; a window
  is `W` consecutive slots with its readiness boundary at `p`, and every
  window has a successor; a slot's deadline is its starting time plus `Δ`.
  _Paper._ {decl}`Conductor.ConductorSchedule`, {decl}`Conductor.StartTimes`,
  {decl}`Conductor.StartsUnbounded`, {decl}`Conductor.WindowShifts`,
  {decl}`Conductor.WindowsUnbounded` ([§0.2](../../../Premises.md#02-the-instance-and-the-configuration), [§9.2](../../../Premises.md#92-the-instance-the-schedule-and-the-assumed-acs))

* *Correct MVBA leaders.* Among every `k` consecutive views of the MVBA, one
  has a correct leader. _Paper._ {decl}`Mvba.LeaderRotation`
  ([§2.5](../../../Premises.md#25-a-correct-leader-in-every-k-views-leaderrotation-a-leader-rotation-k))

* *A proposer per slot.* Chorus's contract instance is formed for a slot
  with at least one proposer; the proposers may all stay silent. _Not stated
  in the paper,_ which allows an empty proposer set (P14). No step of the
  composed proofs uses it. ([§2.10](../../../Premises.md#210-the-slot-has-a-proposer-the-contract-instance-only))

* *The certificate bridge.* The MVBA's validity check on a meta-block is
  Chorus's check of the certificates its entries name. _Not stated in the
  paper:_ the paper reads validity as certificate verification, and the
  composition makes that reading a premise. {decl}`Chorus.ValidBridge`
  ([§5.1](../../../Premises.md#51-validbridge))

* *Censorship resistance only:* a proposal chunk that arrives exactly at the
  deadline counts as on time, _not stated in the paper_ (P19),
  {decl}`Composed.SlotInclusive`; and a correct proposer has a well-encoded
  proposal to submit, _paper._ ([§4.8](../../../Premises.md#48-deadlineinclusive-p-incl), [§0.2](../../../Premises.md#02-the-instance-and-the-configuration))
:::

The safety claims, MCP Safety and bounded concurrency, take none of the run
premises: they hold in every reachable state.

# What non-vacuous means here

A premise set is non-vacuous when it can hold, and here that is a theorem.
One model of the whole composed system meets every premise of the four timed
claims at once: four validators, one of them Byzantine and silent, the ideal
ACS of chapter 5, and a run in which every slot is opened, proposed in,
finalized and appended, and every window decided and entered. One theorem
per claim proves that its premises hold there, and only the premises, never
a conclusion:

{claim Composed.Witness.liveness_premises_satisfiable}

The others are {decl}`Composed.Witness.corollary4_premises_satisfiable`,
{decl}`Composed.Witness.boundedConcurrency_premises_satisfiable` and
{decl}`Composed.Witness.censorship_premises_satisfiable`. As a check that the
premise set shown is the one the claims take, each proven claim is also
applied to the model.

The witness is a model of the _composed_ system, not one per module. A
module's own witness can rest on inputs its caller never supplies, so
non-vacuity does not compose the way safety does
([CompositionContracts.md](../../../CompositionContracts.md#vacuity-does-not-compose) §7, "Vacuity
does not compose").

The second half is that each premise is used. A transitive analysis of the
proof terms found every premise of every claim consumed by some step, with
one exception kept by decision: the timed MVBA claim does not use its
antecedent that every proposal is valid, because the model's `propose`
checks validity itself; the antecedent stays, as the paper's caller
condition of Module 3 ({cite}`mod:mvba`)
([Premises.md](../../../Premises.md#7-independence-every-premise-is-used) §7).

That is the formal bar: one model, and every premise used. Above it, the
auditor judges whether each premise is one the real system meets; the
plain-words list and the ledger are written for that judgement.

# The paper target and the findings

## The target

The development corresponds to one revision of the paper repository,
`48cac9a`: the main body of _Cadence: Extreme Pipelining with Multiple
Concurrent Proposers_ (arXiv:2607.02275), together with its internal
supplement, which specifies the MVBA. Claims are about that revision, and a
protocol bug found here is a bug in it. The guide cites the paper as its
rendered PDF shows it, with the source label in parentheses: Lemma 11
({cite}`lemma:chorus-termination`), or for the supplement,
{cite}`lem:decision-propagation`. The target, and how a later paper commit
becomes one, is [PaperAlignment.md](../../../PaperAlignment.md#0-the-target) §0.

## What to accept against the paper

Every rule of the target is modelled, and where a model differs from the
paper the difference is one of a few kinds an auditor accepts or rejects as a
whole. The main ones:

* *One model per slot, no wire format.* Chorus models one slot's instance.
  Signature domain tags, slot checks, the threshold-encryption operations and
  individual decryption shares are not modelled: each message type is its
  own relation, and hiding is a property of the cryptography, stated as an
  assumption.
* *No crashes, no persistence.* With state persisted before each send, a
  crash and restart looks to every other validator like a pause, and the
  models' runs pause. Termination under crashes is not claimed.
* *Over-approximations.* Where a rule would need to read the absence of a
  message, the model allows more runs instead: the MVBA enters the first
  view on `propose`, not the view of the highest retained timeout
  certificate. The glue's handlers are separate, later steps rather than
  atomic with their events, and the Conductor's openings may fire late.
  Every safety claim covers the paper's runs because they are among the
  model's; the timed claims close the extra freedom with their premises.
* *Uninterpreted arithmetic.* The Conductor's window widths and slot
  spacing are functions constrained by order facts; the timed claims fix
  the paper's arithmetic at their instance.
* *A chosen reading where the paper is silent.* An `upon` handler runs once,
  and a redelivered MVBA decision casts its vote once; both are findings
  below.

The full table, each row with its argument, is
[PaperAlignment.md](../../../PaperAlignment.md#510-what-remains-different-and-why) §5.10.

## The findings for the paper's authors

The review against the target produced findings about the paper's
statements, proofs, module interfaces and conventions, written up to be sent
to the authors. None of them is a flaw in the protocol: the properties are
proven of the modelled protocol, and where the paper uses a condition it does
not state, they are proven under that condition. The findings fall into
three groups.

*They affect the paper's correctness argument:* a proof step rests on
something the cited statement or module does not provide, although the claim
itself holds.

* *P1.* Module 3's Integrity was not revised with its Agreement, which is
  stated over a meta-block's entries; the model states both over entries.
* *P2.* Two proofs argue from one decided meta-block, where the MVBA's
  Agreement gives only equal entries, and from two commitment proofs, where
  the supplement adds a third; the model proves the claims without either.
* *P12.* The MVBA's availability couples it to the dissemination layer
  through state Module 3 does not expose; the model states the dependency.
* *P13.* Module 1 states Termination without the conditions Chorus needs
  from its caller; the model's contract carries them as antecedents.
* *P15.* Module 2's Totality and Recovery rest on conditions about the
  caller the module does not state; the model's contract states them.
* *P16.* Module 4's Validity lacks the one-pair-per-validator bound the
  median argument needs; the model's contract carries it.
* *P19.* A chunk that arrives exactly at the deadline is counted as on time
  without a stated rule; the model states the inclusive reading as a premise.

*They are open questions for the authors:* the paper leaves a rule, a
convention or a choice unstated, and the model takes one reading.

*They are presentation, source hygiene or slack:* the claims and their
proofs stand as written, and in two places the proof gives more than the
statement says, which the model confirms by proof.

Each finding, with the paper's text, why it matters and its status, is
[PaperAlignment.md](../../../PaperAlignment.md#6-findings-for-the-papers-authors) §6, the page for the authors.

# Further detail

* [Premises.md](../../../Premises.md) — every premise of every claim, the
  modules' own claims included, with role, plausibility, witness and use.
* [CompositionContracts.md](../../../CompositionContracts.md#6-the-composed-system) §6 — how the
  composed claims are put together from the modules' contracts.
* [PaperAlignment.md](../../../PaperAlignment.md) — the target, the review
  against it, and the findings.
* {chapter Contracts}[Chapter 5] — the ACS contract and the other module
  contracts, field by field.
