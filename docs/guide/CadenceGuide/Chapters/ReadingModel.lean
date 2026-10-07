/-
Chapter 3 of the guide: Reading a model: Chorus.

Teaches the reading of a Veil model on the declarations of Chorus that
[GuidePlan.md](../../../GuidePlan.md) §4.1 selects: every quotation is
embedded from the rendered sources (`{model}`) or the compiled development
(`{claim}`), so a changed declaration changes the page and a vanished one
fails the build.
-/
import CadenceGuide.Elements

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "Reading a model: Chorus" =>
%%%
file := "reading-a-model"
tag := "reading-a-model"
%%%

_How a Veil model states a protocol, taught on selected parts of Chorus; assumes chapter 1, no prior Lean._

Chorus is the consensus that decides one slot of Cadence. Its model is the
largest in the development, and it uses every kind of declaration a Veil
model has. This chapter reads a dozen of them closely: enough to read the
rest of the file, and the other models, on your own. Every quotation below
is the model's source as built, so what you read here is what was proven.

# What a Veil model is

A Veil model is a state machine, written as a list of declarations of four
kinds.

* *State.* A `relation` is a set of tuples: a fact that holds or not for
  each combination of its arguments, such as "validator `i` recorded root
  `m` for proposer `j`". An `individual` is a single value. `immutable`
  marks configuration, fixed for the whole run. A `ghost relation` is a
  named formula over the state: a definition, not stored.
* *Actions.* An `action` is a step. Its guards are written `require`, its
  updates `:=`. An action may fire whenever its guards hold, and nothing
  forces it to. Its parameters make it a family: `vote i` is one step for
  each validator `i`. A capital letter in an update, as in
  `local_entry_neg i J`, updates every `J` at once.
* *Properties.* A `safety` declaration is something the protocol promises;
  an `invariant` is a helper that makes the promises provable. Both are
  formulas over one state.
* *The initial state*, `after_init`, which sets every component.

A run starts in the initial state and takes one action at a time, any
action whose guards hold. A property is *proven* when it holds in every
state a run can reach. The proof is an induction over the actions: the
property holds initially, and every action preserves it. Veil turns each
pair of an action and an invariant into one verification condition, which
an SMT solver discharges and Lean's kernel then checks; chapter 7, *How
the proofs are checked*, follows that pipeline.

# One slot

{figure "docs/diagrams/chorus-slot.svg" (caption := "One slot of Chorus on its phase axis, with the actions this chapter quotes.")}

A slot has three landmarks: the deadline, the fallback arm one `Δ` later,
and the MVBA arm one `Δ` after that. Before the deadline, each proposer
signs one root and its chunks reach the validators, who record them. At
the deadline every validator votes. Where FastQCs form for every proposer,
the *fast path* finalizes: commit votes, then a commit certificate. Otherwise the *fallback path* runs: fallback entries and
votes, an MVBA instance that agrees on the entries, and a final commit
round. Byzantine validators act throughout.
{cite}`section:slot_agreement` is the paper's account, with the pseudocode
in {cite}`alg:proposer-dissemination` to {cite}`alg:da`.

# The state

Every state component of Chorus falls into one of four categories, and its
name says which:

:::table +header
*
  * Category
  * Named
  * Stands for
*
  * network
  * `msg_*`
  * a signed message exists, and every validator can see it
*
  * derived certificate
  * `ghost relation`
  * a fact about the network, such as "a supermajority signed this"
*
  * local
  * `local_*`
  * one validator's own record, read and written by its own actions only
*
  * abstract
  * a bare name
  * a landmark or an oracle that is not any one validator's: the phase, the MVBA's state
:::

Configuration sits beside them, as `immutable` relations. Here is one
declaration of each kind.

## Configuration

{model Cadence.Chorus "immutable relation is_proposer"}

The proposers of the slot. An immutable relation never changes during a
run, and every theorem holds for every choice of it: the proofs assume
nothing about who proposes.

## A network relation

{model Cadence.Chorus "relation msg_vote_pos_sig"}

A tuple `(r, j, m)` is validator `r`'s signature on the positive vote entry
for proposer `j` and root `m`. The first argument is the signer. Actions
only ever add tuples, so a message, once sent, stays visible to every
validator: the network is *monotone*. A correct validator's row is written
only by its own honest actions; a Byzantine validator's row only by the
adversary's. Chapter 4 explains why this reading of the network is sound
for safety, and what it asks of every action.

## Local state

{model Cadence.Chorus "relation local_entry_pos"}

Validator `i`'s per-proposer entry. A local relation is indexed by the
validator that owns it, its first argument, and only that validator's
actions write its row.

## A derived certificate

{model Cadence.Chorus "ghost relation vote_quorum_pos"}

A FastQC: a supermajority `q` of validators all of whom signed the same
positive entry. It is not stored. A certificate exists exactly when its
signatures do, as in the protocol, where anyone holding the signatures can
assemble it and any receiver can verify it. So it has no owner, and no
validator index.

## The phase

{model Cadence.Chorus "enum Phase"}

{model Cadence.Chorus "individual phase"}

The slot's landmarks, as one value. Three environment actions,
`advance_to_deadline`, `advance_to_fb_arm` and `advance_to_mvba_arm`, move
it forward, one step each and never back. A validator's timer firing is a
guard reading the phase: "the deadline has passed" is
`phase ≠ pre_deadline`. The phase is one value for all validators, and
chapter 4 says what that asks you to accept.

# Four honest actions

## A proposer proposes

{model Cadence.Chorus "action propose"}

Read the guards in order. `¬ is_byz j` makes this an honest action: it
belongs to a correct validator, the proposer `j`. Every action of a
correct validator starts this way, and Byzantine validators have actions of their own. The
next two guards are the participation gate: `j` has joined the slot and has
not left it, which every action that sends a message requires. Then `j` is
a proposer, its root is validly encoded, and the deadline has not passed.
The last guard says `j` has not signed a different root; it reads `j`'s own
row of a network relation, one of the two kinds of negative network read
chapter 4 admits. The single update is the signature.

Delivering the chunks is a separate action, `deliver_chunk_assigned`,
because when a chunk *arrives* decides what the receiver records.

## A validator records a chunk

{model Cadence.Chorus "action record_chunk"}

The receiving side. The guards read the network positively (its chunk has
arrived, and the proposer signed the root) and the validator's own rows
negatively (it has no entry for `j` yet). The deadline is a read of the
phase. There is no participation gate, because recording sends nothing.

## A validator votes

{model Cadence.Chorus "action vote"}

{cite}`alg:voting` loops over the proposers; the model takes the whole
loop as one atomic step. The capitals `J` and `M` range over every proposer
and every root, so the first update signs a positive entry for each
proposer the validator recorded, and the next two sign a negative entry for
each proposer it did not. Each update has the form `x := x || …`, so it
only ever adds tuples. The step also broadcasts the vote, `msg_vote_cast`,
and releases the validator's decryption share.

## A validator finalizes

{model Cadence.Chorus "action finalize_commit"}

The protocol's output, written to the validator's own row. It requires a
committed entry for every proposer, and each of those comes from
`commit_assign_pos` or `commit_assign_neg`, which commit only on a
commitment proof: a fast commit certificate, a fallback commit certificate,
or the MVBA's own commit certificate.

# The adversary

{model Cadence.Chorus "action byz_sign_vote_pos"}

A Byzantine validator `r` signs a positive vote entry for any proposer and
any root, as often as it likes. The one guard it meets is the check an
honest receiver makes: a positive vote entry carries the signer's chunk,
and a vote without one is discarded on receipt, so it could never influence
a correct validator.

The adversary is a family of such actions, `byz_*`, one per capability:
each kind of signature, delivering a chunk, re-disseminating one, and
assembling a commit certificate. Each writes only Byzantine
signers' rows, so signatures cannot be forged. Chapter 4 explains why the
adversary has to be at least this strong.

# The MVBA as a consumed contract

{model Cadence.Chorus "instantiate mvba"}

The fallback path runs an MVBA, and Chorus does not contain one. It holds
an abstract state, `mvba_st`, and the class `MVBASafety` over it: the
paper's MVBA module, {cite}`mod:mvba`, stated as a Lean class. Every field of the
class (agreement, integrity, external validity, that decisions are never
undone) is a hypothesis of every verification condition of Chorus, and no
guard or invariant restates one. Chorus reaches the MVBA only through the
class's operations: `mvba.step`, `mvba.propose`, `mvba.decided` and the
others. The instance that fills the class in the composed system is the
MVBA model's own, {decl}`Mvba.mvbaSafety`. Chapter 5, *Reviewing the
contracts*, is about checking such a class.

{model Cadence.Chorus "action on_mvba_decide_pos"}

The decision handler. It reads validator `i`'s own decision through the
class (`mvba.decided mvba_st i v`), and records entry `j` in Chorus's own
record, which the commit actions read. Before it does, it checks the
certificate `v` names for that entry against Chorus's network. That guard
is the *bridge*: the class's validity predicate is fixed before Chorus's
network exists, so it cannot speak about Chorus's signatures, and the guard
says what a valid certificate means there. For safety it can only remove
behaviours, and only if the MVBA were wrong. Liveness needs the other
direction, and that is a named premise, below.

# A safety property and its proof

{model Cadence.Chorus "safety [agreement_pos]" (proven := Chorus.reachable_agreement_pos)}

Two correct validators that finalized the slot committed the same root for
every proposer. The formula speaks about one state; "proven as" names the
theorem that it holds in *every reachable* state. The box under it lists
what the proof rests on: the kernel's axioms, and the contracts the result
is conditional on, with what discharges them.

The argument is the paper's own, {cite}`lemma:chorus-agreement` through
{cite}`prop:agreement-entries`, and it consults no clock: two commit
certificates agree because two supermajorities share a correct member, two
MVBA decisions agree by the class's agreement, and a commit certificate
excludes a fallback decision because a correct validator never votes on
both paths. Each step is an invariant of the model, and the induction
checks them all together.

# A liveness claim and its premises

{claim Chorus.termination}

Termination is about runs, not states: it says that something eventually
happens. Every correct validator finalizes the slot, in every run that
satisfies five premises. Each premise is a named definition and an explicit
hypothesis of the theorem; none is an axiom.

:::table +header
*
  * Premise
  * In plain words
*
  * {decl}`Chorus.FJustice`
  * A correct validator's step that stays possible eventually happens, for messages from correct senders: weak fairness, (F-justice). Byzantine steps get no fairness.
*
  * {decl}`Chorus.MvbaAdmissible`
  * The MVBA's steps inside the run are scheduled as the MVBA's own termination theorem asks.
*
  * {decl}`Chorus.ValidBridge`
  * The MVBA's validity check and Chorus's certificate check agree, in both directions.
*
  * {decl}`Chorus.AllParticipate`
  * Every correct validator joins the slot.
*
  * {decl}`Chorus.NoAbandonBeforeFinalizing`
  * No correct validator leaves the slot before it has finalized.
:::

The first three describe the environment and the seam to the MVBA. The last
two are conditions on the caller, and within Cadence the glue meets them.
The MVBA's termination is not a premise: the proof applies the MVBA model's
theorem. [Premises.md](../../../Premises.md) §3, §5 and §6 give each
premise's role, why it is plausible, and the step that uses it. The timed
form, with its bound of `5Δ + ℓ_MVBA`, is {decl}`Chorus.timed_termination`.

# Where the rest is

* *The whole model*: [Chorus.lean](../../../../Cadence/Chorus.lean), with
  every action, property and invariant in order, each with its
  explanation.
* *The modelling choices*: [ChorusDesign.md](../../../ChorusDesign.md),
  for the network abstraction (§3), the cryptographic primitives and the
  MVBA class (§4), the adversary (§5), the invariants (§6), liveness (§7)
  and the abstractions worth a reviewer's attention (§8).
* *The liveness proof*: [Liveness.md](../../../Liveness.md) §4 walks
  through {decl}`Chorus.termination`; [Bounds.md](../../../Bounds.md) §6.4
  derives the timed bound.

The next chapter turns from reading a model to judging one: the idioms
every declaration above relies on, and how to check that an action keeps
them.
