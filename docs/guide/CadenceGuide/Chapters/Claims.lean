/-
Chapter 2 of the guide: Claims, premises, witnesses.
-/
import CadenceGuide.Elements
import CadenceGuide.PremiseCover
import CadenceGuide.Findings
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

# The claims at a glance

Each row is one result as the kernel checked it: the paper's statement it
proves, the theorem, what the theorem concludes, its bound where it has
one, and the premises it takes. A bound is quoted at the paper's `δ = 0`
where the theorem fixes it, and a tighter bound is named where one is
proven. The premises are named as in the list further down, which gives
each one in plain words.

:::table +header
*
  * Paper result
  * Theorem
  * What it concludes
  * Bound
  * Premises
*
  * MCP Safety: {cite}`def:safety`, {cite}`lemma:cadence-safety`
  * {decl}`Cadence.system_positional_log_safety`
  * Two correct validators never hold different entries at one position of their logs, in every reachable state.
  * —
  * No run premise. The ACS contract, the modules' configurations, and `hbyz` (below).
*
  * {cite}`cor:chorus-correctness-within-cadence`
  * {decl}`Composed.corollary4`
  * In every run meeting the premises, every started slot's Chorus part meets Chorus's three caller conditions: correct validators join within `Δ` of each other, none leaves before finalizing, none joins before the slot starts.
  * —
  * The run premises, with the configuration's starting times and the ACS's `Δ`.
*
  * Corollary 4 with {cite}`lemma:chorus-termination`
  * {decl}`Composed.corollary4_bounded_termination`
  * Once every correct validator participates in a slot by `t`, every correct validator finalizes it by `max(t, GST) + ℓ`.
  * `ℓ = 5Δ + ℓ_MVBA`. Chorus alone is also proven at `4Δ + ℓ_MVBA + 9δ` ({decl}`Chorus.timed_termination_tight_atMvba`, finding P5).
  * As Corollary 4.
*
  * Corollary 4 with {cite}`prop:chorus-totality`
  * {decl}`Composed.corollary4_totality`
  * Once one correct validator finalizes a slot at `c`, every correct validator finalizes it by `max(c, GST) + Δ`.
  * `Δ`
  * As Corollary 4.
*
  * {cite}`lemma:cadence-bounded-concurrency`
  * {decl}`Composed.boundedConcurrency`
  * No correct validator takes part in more than `2W − p` slot instances at once, in every reachable state.
  * `2W − p`
  * No run premise: the window shape, {decl}`Conductor.WindowShifts`.
*
  * 𝓡-Liveness: {cite}`def:liveness`, {cite}`lemma:cadence-liveness`
  * {decl}`Composed.liveness`, {decl}`Composed.liveness_sharp`
  * Every slot that starts at least `𝓡` after GST is in the log of every correct validator.
  * `𝓡 = 2Wτ`, and `(W + p − 1)τ` (finding P18).
  * The run premises and the whole configuration.
*
  * 𝓡-Censorship resistance: {cite}`def:censorship-resistance`
  * {decl}`Composed.censorship`, {decl}`Composed.censorship_sharp`
  * For every such slot, each correct proposer's proposal is in that slot's entry of every correct validator's log.
  * As liveness.
  * As liveness, with (P-incl) and a proposal to make.
*
  * {cite}`thm:chorus-correctness`: Chorus meets {cite}`mod:slotconsensus`
  * {decl}`Chorus.slotConsensusFull`, {decl}`Chorus.chorusWithTotality`
  * Every field of the module, and termination and totality within the bounds.
  * Termination `5Δ + ℓ_MVBA + 9δ`, tight `4Δ + ℓ_MVBA + 9δ`; totality `Δ + 2δ`.
  * [Premises.md](../../../Premises.md#1-the-claims-and-their-premises) §1, the Chorus rows.
*
  * {cite}`thm:conductor-correctness`: the Conductor meets {cite}`mod:orchestrator_2`
  * {decl}`Conductor.conductorFull`, {decl}`Conductor.conductorWithTotality`
  * Every field of the module, for every ACS that meets {cite}`mod:acs`.
  * Totality `Δ`; boundedness `2W − p`; recovery `2Wτ`, and `(W + p − 1)τ` ({decl}`Conductor.recovery_sharp`).
  * [Premises.md](../../../Premises.md#9-the-conductors-timed-claims) §9; `δ = 0`.
*
  * The MVBA meets {cite}`mod:mvba` ({cite}`thm:agreement`, {cite}`thm:termination`)
  * {decl}`Mvba.mvbaFull`
  * Every field of the module.
  * Termination within `ℓ_MVBA`, of order `fΔ`, for any `δ`.
  * [Premises.md](../../../Premises.md#1-the-claims-and-their-premises) §1, the Mvba rows.
:::

The safety claims, MCP Safety and bounded concurrency, hold in every
reachable state and take no premise about runs. The others hold in every
run that meets their premises.

# The composed claims, as stated

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
the ACS protocol open, so the claims hold for every ACS that meets
{cite}`mod:acs`. {chapter Contracts}[Chapter 5] reviews that contract field by field.

## MCP Safety

{claim Cadence.system_positional_log_safety}

Besides the ACS contract, the statement takes the three modules'
configurations and one hypothesis, `hbyz`: the Conductor and Chorus agree on
which validators are Byzantine. It is a configuration fact, so the front
page leaves it out. The claims below need no such hypothesis, because they
state every module at one fault pattern, {decl}`Composed.fmF`.

## Corollary 4

{claim Composed.corollary4}

The theorem concludes the three caller conditions. What a reader cares
about follows from them, and each consequence is a theorem of its own, on
the same premises: every slot is finalized by every correct validator within
`5Δ + ℓ_MVBA` after all correct validators have joined it, counted from GST
at the earliest ({decl}`Composed.corollary4_bounded_termination`), and
within `Δ` of the first correct validator to finalize it
({decl}`Composed.corollary4_totality`). The bound is the paper's: its
{cite}`lemma:chorus-termination` states `5Δ + ℓ_MVBA`, and its proof gives
`4Δ + ℓ_MVBA` (finding P5), which is proven for Chorus on its own,
{decl}`Chorus.timed_termination_tight_atMvba`.

## Bounded concurrency

{claim Composed.boundedConcurrency}

## Liveness

{claim Composed.liveness}

The same holds at the smaller `𝓡 = (W + p − 1)τ`, on the same premises
({decl}`Composed.liveness_sharp`); the paper's bound is not tight (finding
P18).

## Censorship resistance

{claim Composed.censorship}

It holds at `(W + p − 1)τ` as well ({decl}`Composed.censorship_sharp`).

# Reading a statement

A statement above shows few hypotheses: Corollary 4's takes a schedule
`sch`, the ACS `TA`, `hprop` and `hrot`. The premises are inside the
conclusion, because each claim is stated as a definition, a `…Claim`, which
the theorem proves. Corollary 4's has this shape, written here as an
outline:

```
-- outline, not the declaration
Corollary4Claim sch TA thO hprop hrot :=
  StartTimes sch thO → StartsUnbounded thO → TA.Δ = sch.Δ →   -- the configuration
  ∀ run r, SysSync sch TA r →                                  -- the run premises
  ∀ slot x, x's part of r meets Chorus's three caller conditions
```

The real definitions are {decl}`Composed.Corollary4Claim`,
{decl}`Composed.LivenessClaim`, {decl}`Composed.CensorshipClaim` and
{decl}`Composed.BoundedConcurrencyClaim`. Every run premise is one
definition, {decl}`Composed.SysSync`:

{model Cadence.Composed.Schedule "def SysSync"}

It has three parts. {decl}`Composed.GlueRows` says each handler of the glue
runs with its event. {decl}`Composed.OrchAdmissible` says the Conductor's
part of the run meets the Conductor's own timing model, and
{decl}`Composed.SlotAdmissible` says every started slot's part meets
Chorus's. Each module's timing model is the one its contract instance
names, `Conductor.Admissible` and `Chorus.Admissible`, so the premise list
below says which named premise lives in which part.

Lean's printer leaves out the proof arguments of a term and writes `⋯` in
their place. In the witness theorem further down,
`Composed.SysSync 4 1 ⋯ Composed.Witness.isByz ⋯` is the run premise at four
validators and one fault: the first `⋯` is the proof that `4 = 3 · 1 + 1`,
the second the proof that at most one validator is Byzantine.

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
  it, and [the premise ledger](../../../Premises.md) gives each premise a line on why it is
  plausible and which sentence of the paper it formalises.

The figure shows the four for the liveness claim.

{figure "docs/diagrams/claim-premise-witness.svg" (caption := "One claim, its premises, the proof step that uses each, and the one model that meets them all. Plausibility is the part no tool checks.")}

# The premises in plain words

What the composed claims assume, simplified. Each premise has one name,
used on the front page, here and in the premise ledger, followed by its tag
where it has one ({chapter Glossary}[the key to the tags]), and by the Lean definitions that state it ("in the
statement"). A line marked _paper_ states something the paper states or
works under; a line marked _not stated in the paper_ is a reading or a
modelling choice the development adds, and each of those is either a
finding for the paper's authors or argued in the ledger. Every condition
one module needs from another is proven inside the composition, so what
remains is the environment and the configuration. The full list, with each
premise's use and witness, is
[Premises.md](../../../Premises.md#0-the-composed-system-the-premises-of-the-end-claims) §0.

:::premises (claims := "Composed.corollary4 Composed.boundedConcurrency Composed.liveness Composed.liveness_sharp Composed.censorship Composed.censorship_sharp")
* *Validators and faults.* `n = 3f + 1` validators, at most `f`
  Byzantine, one notion of "correct" for every module; clock readings can
  be added, compared and cancelled, and no time lies beyond every multiple
  of a delay. _Paper._ In the statement: the parameters `n`, `f` and the
  fault pattern, {decl}`Composed.fmF`.
  ([§0.2](../../../Premises.md#02-the-instance-and-the-configuration), [§2.1](../../../Premises.md#21-validators-and-faults), [§2.6](../../../Premises.md#26-time))

* *Partial synchrony*, (Δδ-justice) and (Δ-justice). After GST, a correct
  validator acts on a correct validator's message within `Δ` of its sending,
  and takes each local step within `δ`. Nothing is owed on a Byzantine
  validator's message. _Paper._ In the statement: inside
  {decl}`Composed.SlotAdmissible` (Chorus's rows, the MVBA's) and
  {decl}`Composed.OrchAdmissible` (the Conductor's rows, the ACS's).
  ([§4.1](../../../Premises.md#41-timedjustice-δδ-justice), [§4.4](../../../Premises.md#44-boundedjustice-δ-justice))

* *Local steps take no time* (`δ = 0`). Each handler of the glue and of the
  Conductor runs with its event, as throughout the paper. _Paper._ In the
  statement: the schedule's `δ_zero`, and {decl}`Composed.GlueRows`;
  together with the two timing models above, this is the whole run
  premise, {decl}`Composed.SysSync`.
  ([§0.3](../../../Premises.md#03-the-run-composedsyssync), [§9.3](../../../Premises.md#93-the-run-conductorsync))

* *Synchronized clocks*, (P-phase), (T-timer) and (P-open). Every validator
  reads one clock, and every timer fires exactly at its landmark: Chorus's
  deadline timers, the MVBA's view timer and the Conductor's slot openings.
  _Paper._ In the statement: inside {decl}`Composed.SlotAdmissible` and
  {decl}`Composed.OrchAdmissible`.
  ([§4.2](../../../Premises.md#42-phasepunctual-p-phase), [§4.5](../../../Premises.md#45-timerpunctual-t-timer), [§9.3](../../../Premises.md#93-the-run-conductorsync))

* *Fair scheduling*, (F-justice). An enabled step of a correct validator
  eventually happens. Nothing is asked of a Byzantine validator's steps, so
  no progress relies on the adversary's help. _Not stated in the paper:_
  weak fairness is the untimed form of the paper's network, a modelling
  choice. In the statement: inside {decl}`Composed.SlotAdmissible`.
  ([§3.1](../../../Premises.md#31-fjustice-f-justice-for-chorus), [§3.3](../../../Premises.md#33-mvbafjustice-f-justice-for-the-mvba))

* *The assumed ACS.* Every window's ACS meets Module 4 in the run, with the
  system's `Δ` and a latency `ℓ`. _Paper:_ Module 4 is the paper's; the
  paper leaves its protocol open (P17). In the statement: `TA`, an
  {decl}`ACSTemporal`, with `TA.Δ = sch.Δ` and `TA.ℓ = sch.ℓ`, and inside
  {decl}`Composed.OrchAdmissible`.
  ([§0.2](../../../Premises.md#02-the-instance-and-the-configuration), [§9.2](../../../Premises.md#92-the-instance-the-schedule-and-the-assumed-acs))

* *The configuration.* The window parameters `W`, `p`, `τ` meet the paper's
  four parameter assumptions; slots start `τ` apart, without end; a window
  is `W` consecutive slots with its readiness boundary at `p`, and every
  window has a successor; a slot's deadline is its starting time plus `Δ`.
  _Paper._ In the statement: {decl}`Conductor.ConductorSchedule`,
  {decl}`Conductor.StartTimes`, {decl}`Conductor.StartsUnbounded`,
  {decl}`Conductor.WindowShifts`, {decl}`Conductor.WindowsUnbounded`.
  ([§0.2](../../../Premises.md#02-the-instance-and-the-configuration), [§9.2](../../../Premises.md#92-the-instance-the-schedule-and-the-assumed-acs))

* *Correct MVBA leaders*, (A-leader-rotation-k). Among every `k`
  consecutive views of the MVBA, one has a correct leader. _Paper._ In the
  statement: `hrot`, a {decl}`Mvba.LeaderRotation`.
  ([§2.5](../../../Premises.md#25-a-correct-leader-in-every-k-views-leaderrotation-a-leader-rotation-k))

* *A proposer per slot.* Chorus's contract instance is formed for a slot
  with at least one proposer; the proposers may all stay silent. _Not
  stated in the paper,_ which allows an empty proposer set (P14). In the
  statement: `hprop`. The instance uses it to show that its runs exist; no
  step of the composed proofs uses it.
  ([§2.10](../../../Premises.md#210-the-slot-has-a-proposer-the-contract-instance-only))

* *The certificate bridge*, (ValidBridge). The MVBA's validity check on a
  meta-block is Chorus's check of the certificates its entries name. _Not
  stated in the paper:_ the paper reads validity as certificate
  verification, and the composition makes that reading a premise. In the
  statement: inside {decl}`Composed.SlotAdmissible`, as
  {decl}`Chorus.ValidBridge`.
  ([§5.1](../../../Premises.md#51-validbridge))

* *On time at the deadline*, (P-incl), censorship resistance only. A
  proposal chunk that arrives exactly at the deadline counts as on time.
  _Not stated in the paper:_ its proof of {cite}`prop:honest-positive-entry`
  relies on this reading and states no rule for the tie (P19). In the
  statement: {decl}`Composed.SlotInclusive`.
  ([§4.8](../../../Premises.md#48-deadlineinclusive-p-incl))

* *A proposal to make*, censorship resistance only. A correct proposer has
  a well-encoded proposal to submit. _Paper._ In the statement:
  `∃ m, well_encoded m`.
  ([§0.2](../../../Premises.md#02-the-instance-and-the-configuration))
:::

The safety claims, MCP Safety and bounded concurrency, take none of the run
premises: they hold in every reachable state.

# How these premises differ from textbook partial synchrony

Textbook partial synchrony bounds message delay after GST and says little
else. The composed claims assume a little more, as the paper does. Each
difference, with why it is plausible:

* *Synchronized clocks and exact timers*, (P-phase), (T-timer), (P-open).
  The run has one clock that every validator reads, and a timer fires
  exactly when the clock reaches its landmark; in Chorus the timers are one
  shared `phase` ({chapter ModelIdioms}[chapter 4]). There is no clock skew
  and no timer drift. _Plausible_ as the paper's own setting: it assumes
  synchronized clocks and one global timeline
  ({cite}`subsection:mcp-overview`). A deployment with skewed clocks meets
  it only up to the skew, which the development does not model.
* *Local steps take no time* (`δ = 0`). The composed claims and the
  Conductor's bounds assume it, through the schedule's `δ_zero`. Chorus's
  own bounds carry an explicit `δ` term, and the MVBA's hold for any `δ`.
  _Plausible_ where computation is fast against the network, and it is the
  paper's model throughout.
* *The inclusive deadline*, (P-incl). Censorship resistance counts a chunk
  that arrives exactly at the deadline as on time; no other claim takes it.
  _Plausible:_ an implementation processes its inbox before the timer that
  closes it at the same instant. The paper's proof relies on this reading
  without stating it (P19).
* *The assumed ACS.* The ACS is a module the paper specifies and does not
  implement (P17), and the claims hold for every ACS that meets its
  contract. _Plausible_ as a standard primitive; that a message-passing
  protocol meets the contract, with the one-pair-per-validator bound of
  P16, is the open part ({chapter Contracts}[chapter 5]).
* *The certificate bridge*, (ValidBridge). The MVBA's validity check is
  Chorus's certificate check. _Plausible:_ certificates are publicly
  verifiable, so a value is valid exactly when the certificates it carries
  verify.

# What non-vacuous means here

A premise set is non-vacuous when it can hold, and here that is a theorem.
One model of the whole composed system meets every premise of Corollary 4,
bounded concurrency, liveness and censorship resistance at once. It has four
validators, one of them Byzantine and silent, the ideal ACS of
{chapter Contracts}[chapter 5], and a run in which every slot is opened, proposed in,
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
two kinds of exception
([Premises.md](../../../Premises.md#7-independence-every-premise-is-used) §7).
The timed MVBA claim does not use its antecedent that every proposal is
valid, because the model's `propose` checks validity itself; the antecedent
stays, as the paper's caller condition of {cite}`mod:mvba`. And a slot's
non-empty proposer set is used only by Chorus's contract instance, to show
that its runs exist; the composed claims take it because their statements
name that instance.

That is the formal bar: one model, and every premise used. Above it, the
auditor judges whether each premise is one the real system meets; the
plain-words list and the ledger are written for that judgement.

# The paper target and the findings

## The target

Every claim is about one revision of the paper, `48cac9a`, its main body
together with the internal supplement; {chapter Approach}[chapter 1] says
what that means and how the guide cites it.

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
not state, they are proven under that condition. They fall into three
groups:

* *correctness argument*: a proof step rests on something the cited
  statement or module does not provide, although the claim itself holds;
* *open question*: the paper leaves a rule, a convention or a choice
  unstated, and the model takes one reading;
* *presentation*, *hygiene* or *slack*: the claims and their proofs stand
  as written, and where the proof gives more than the statement says, the
  model confirms it by proof.

The table is read from the findings' home when this guide is built.

{findings}

The findings that quote the supplement need it to be checked. Auditors can
obtain the paper sources at the target revision, the supplement included,
and all of it is to be made public
([PaperAlignment.md](../../../PaperAlignment.md#9-scope-and-access) §9).
Each finding, with the paper's text, why it matters and a suggested
correction, is
[PaperAlignment.md](../../../PaperAlignment.md#6-findings-for-the-papers-authors) §6,
the page for the authors.

# Further detail

* [Premises.md](../../../Premises.md) — every premise of every claim, the
  modules' own claims included, with role, plausibility, witness and use.
* [CompositionContracts.md](../../../CompositionContracts.md#6-the-composed-system) §6 — how the
  composed claims are put together from the modules' contracts.
* [PaperAlignment.md](../../../PaperAlignment.md) — the target, the review
  against it, and the findings.
* {chapter Contracts}[Chapter 5] — the ACS contract and the other module
  contracts, field by field.
