/-
Chapter 1 of the guide: How the verification is built.
-/
import CadenceGuide.Elements
import CadenceGuide.ChapterList

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "How the verification is built" =>
%%%
file := "approach"
%%%

_The modules, the contracts between them, and how the proofs compose; no Lean needed._

# The approach

The paper describes Cadence as a set of modules, gives each module a
specification, and proves the protocol's properties from those
specifications. The verification follows the same plan. Each protocol
module is a _model_ in Veil: a state machine whose state is a collection of
facts (who has voted, which messages exist, what a validator has decided)
and whose steps are _actions_, each with guards that say when it may fire
and updates that say what it changes. A model's safety properties are
proven by induction: they hold in the initial states, and every action
preserves them, so they hold in every reachable state. Each module's
specification is a _contract_: a Lean class listing the properties the
paper states for the module. A model that uses a module sees only its
contract, so its proofs hold for any implementation of it; a model that
implements a module proves its contract. Plain Lean then joins the pieces
into statements about the whole system, the timed ones included, which are
proven over runs of the composed system.

# Modules and contracts

The paper names four modules, and the development has one model for each
module it implements, plus the glue that composes them. The diagram on the
front page shows how they fit:

{figure "docs/diagrams/modules-contracts.svg" (caption := "The modules, the contracts between them, and the composed claims.")}

Read it from the bottom up. Each model meets the contract written beside
it, and each arrow labelled _fills_ is a Lean instance: the proof that one
model meets a contract, plugged into the model above that consumes it. The
glue consumes two contracts, the orchestrator's and the slot consensus's,
and the composed claims at the top are proven about the glue running the
Conductor and Chorus. The ACS, drawn dashed, is the one module the
development assumes.

:::table +header
*
  * Paper module
  * Contract
  * Model
  * Instance
*
  * {cite}`mod:slotconsensus`, the per-slot consensus
  * {decl}`SlotConsensusSafety`, {decl}`SlotConsensus`
  * Chorus, [Chorus.lean](../../../../Cadence/Chorus.lean)
  * {decl}`Chorus.slotConsensusSafety`, {decl}`Chorus.slotConsensusFull`
*
  * {cite}`mod:orchestrator_2`, slot scheduling
  * {decl}`OrchestratorSafety`, {decl}`Orchestrator`
  * the Conductor, {cite}`algorithm:conductor`, [Conductor.lean](../../../../Cadence/Conductor.lean)
  * {decl}`Conductor.orchestratorSafety`, {decl}`Conductor.conductorFull`
*
  * {cite}`mod:mvba`, multi-valued Byzantine agreement
  * {decl}`MVBASafety`, {decl}`MVBA`
  * the supplement's leader-based MVBA, [Mvba.lean](../../../../Cadence/Mvba.lean)
  * {decl}`Mvba.mvbaSafety`, {decl}`Mvba.mvbaFull`
*
  * {cite}`mod:acs`, agreement on a core set
  * {decl}`ACSSafety`, {decl}`ACS`
  * none: an assumed module
  * consistency witness only: {decl}`Cadence.IdealAcs.acsSafety`, {decl}`Cadence.IdealAcs.acsTemporal`
:::

Two models implement no contract. The _glue_,
[Cadence.lean](../../../../Cadence/Cadence.lean), is {cite}`algorithm:cadence`:
it runs one slot consensus per slot under the orchestrator and assembles
the log, and the composed claims are proven about it. The _receipt layer_,
[FallbackReceipt.lean](../../../../Cadence/FallbackReceipt.lean), refines
one step of Chorus's fallback path, {cite}`alg:fallback`: how a validator
turns the receipts it has received into a valid proposal. It is verified on
its own terms, at a finer grain than the Chorus model.

The ACS's instance is an idealized one: a model with global knowledge and
no adversary. It shows that {cite}`mod:acs` can be met, so the claims that
assume it are not vacuous; it is not a protocol a validator could run.
{chapter Contracts}[Chapter 5] reviews every contract field by field, and
says what checking that a real protocol meets them involves.

# The composition

*A model consumes a contract* by declaring it in an `instantiate` line. The
glue's line for the slot consensus, quoted from the model:

{model Cadence.Cadence "instantiate sc"}

It reads: the glue holds a state for each slot's consensus instance, of an
abstract type, and assumes only that this state behaves as
{decl}`SlotConsensusSafety` says. Every property of the contract becomes a
hypothesis of every proof about the glue, and the glue changes that state
only through the operations the contract declares: its inputs (participate,
propose, abandon) and an internal step. So the glue cannot depend on how
Chorus works inside, and no guard or invariant of the glue restates a
property of the contract. Chorus consumes the MVBA's contract in the same
way, and the Conductor the ACS's.

*Each contract has two levels.* The models' proofs are discharged by an SMT
solver, which works with first-order facts: properties of one state, or of
one step. So each contract is split. The _safety fragment_
({decl}`SlotConsensusSafety`, {decl}`OrchestratorSafety`, {decl}`MVBASafety`,
{decl}`ACSSafety`) holds the first-order properties, and is what the models
consume. The _temporal level_ ({decl}`SlotConsensusTemporal`,
{decl}`OrchestratorTemporal`, {decl}`MVBATemporal`, {decl}`ACSTemporal`)
holds the properties over runs, termination and the timing bounds, stated
over the fragment's own states and steps. The full contract, such as
{decl}`SlotConsensus`, is the two joined.

*An instance fills a contract.* Each implementing model proves its safety
fragment from its own transition system ({decl}`Chorus.slotConsensusSafety`
for Chorus) and its temporal level from named premises about its runs
({decl}`Chorus.chorusTemporal`), and the two are joined into the full
contract ({decl}`Chorus.slotConsensusFull`). The composed system is the
glue with its two contracts filled by the Conductor's and Chorus's
instances, and Chorus's own MVBA contract filled by {decl}`Mvba.mvbaSafety`.

*The composed claims* are proven about that system. MCP Safety is the
glue's safety theorem with the instances plugged in:
{decl}`Cadence.system_positional_log_safety` holds for every ACS meeting
its contract. The timed claims run the glue, the Conductor and Chorus on
one clock, and each condition a module's guarantees take from its caller is
a theorem about the composed run rather than a premise: Chorus's conditions
are discharged from the glue and the Conductor ({decl}`Composed.corollary4`),
and the Conductor's from Chorus ({decl}`Composed.caller_totality`,
{decl}`Composed.caller_termination`).

Where a consumer has to interpret a contract in its own vocabulary, the
development states the interpretation as a _bridge_ and justifies it
separately; Chorus's check of a decided MVBA value's certificates against
its own network is one. {chapter Contracts}[Chapter 5] names each of them.

# Where the paper fits

The development targets one revision of the paper repository, `48cac9a`:
the main body, the paper whose arXiv versions are 2607.02275 v1 and v2,
together with the internal supplement, which specifies the MVBA. Claims
are stated about that revision, and a protocol bug found here is a bug in
that revision. A later paper commit becomes the target only after its
differences have been checked and modelled;
[PaperAlignment.md](../../../PaperAlignment.md) §0 is the record.

Citations name a result as the rendered PDF numbers it, with its LaTeX
label in parentheses: {cite}`lemma:chorus-agreement`, or
{cite}`lem:decision-propagation` for the supplement. The guide reads every
reference from the label map of the target revision,
[paper-labels.tsv](../../../paper-labels.tsv), so a label the target does
not have fails the guide's build.

What the review of the paper found, for its authors, is summarised in
{chapter Claims}[chapter 2].

# Four kinds of evidence

Every result rests on one or more of four kinds of machine-checked
evidence. In each, the final check is Lean's kernel.

:::table +header
*
  * Kind
  * What it establishes, and where it is used
*
  * Inductive invariants
  * A property holds in every reachable state of a model. Veil generates one
    condition per action and property; the SMT solver cvc5 discharges each,
    and its proof is rebuilt as a Lean proof the kernel checks. Used for the
    safety properties of every model, such as Chorus's agreement,
    {decl}`Chorus.reachable_agreement_pos`.
*
  * Composition
  * Plain Lean over the proven conditions: the induction to every reachable
    state, the contract instances, and the composed system. Used for
    {decl}`Chorus.slotConsensusSafety` and
    {decl}`Cadence.system_positional_log_safety`, among others.
*
  * Timed runs
  * Plain Lean over the runs of a model, with a clock: liveness and the
    timing bounds. Each premise is a named hypothesis, and one model and run
    meeting all of a claim's premises at once shows they are consistent.
    Used for {decl}`Chorus.termination` and {decl}`Composed.liveness`, with
    the witness {decl}`Composed.Witness.liveness_premises_satisfiable`.
*
  * The model checker
  * Exhaustive search of a small instance, used where a found
    counterexample is complete evidence. In the mutation test,
    [NoLock.lean](../../../../Cadence/Mvba/NoLock.lean), the MVBA with its
    lock check removed lets two correct validators decide differently, so
    the proven invariants are needed.
:::

None of these says that a statement is the right one, or that a premise is
plausible. That is what a reader checks, and the next chapters show how:
{chapter Claims}[chapter 2] lists each claim's premises in plain words,
{chapter ReadingModel}[chapter 3] and {chapter ModelIdioms}[chapter 4]
teach how to read a model and what it asks you to accept, and
{chapter Contracts}[chapter 5] reviews the contracts.
{chapter Checking}[Chapter 7] explains how the machine part is checked.

*Further detail.*

* [Architecture.md](../../../Architecture.md) §2, the methods with the
  per-model counts;
* [CompositionContracts.md](../../../CompositionContracts.md) §2–§4, the
  contract design, its consumers and its instances;
* [Cadence.lean](../../../../Cadence.lean), every end result with its
  axiom pin.
