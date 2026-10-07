/-
Chapter 4 of the guide: What a model asks you to accept.

The modelling idioms of Chorus, and the audit table that checks every
action against them. The table is the data file
[Chorus.tsv](../../audit/Chorus.tsv), filled by hand from the action
bodies and checked against the model's actions when the guide builds.
-/
import CadenceGuide.Elements

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "What a model asks you to accept" =>
%%%
file := "modelling-idioms"
tag := "modelling-idioms"
%%%

_The modelling idioms a theorem relies on, how a model can break them, and the per-action table that checks Chorus; assumes chapter 3._

A theorem about a model is a theorem about the protocol when the model
allows every behaviour the protocol has. Veil checks that each property
holds in every state the model can reach. Whether the model can reach
enough states is a question about how it is written, and it is the
reader's to check: a guard stronger than anything a validator can observe,
or an adversary weaker than a real one, removes behaviours, and a theorem
can then hold because the bad behaviour was never in the model.

Chorus is written in a few idioms that keep its behaviours a superset of
the protocol's. This chapter states them, shows how a departure would
mislead, and ends with the table that checks every action of Chorus
against them.

# One flat state space

A Veil model has one state: every validator, the network and the
environment at once. The language has no notion of a validator's own
memory, and a guard could read any component. Distribution is a reading of
that state, carried by the names of its components
({ref "reading-a-model"}[chapter 3] has the table):

* *Local rows.* A `local_*` relation is indexed by the validator that owns
  it, its first argument: `local_entry_pos i j m` is validator `i`'s record.
* *The network.* A `msg_*` relation is indexed by the signer, and a tuple
  is a message that exists and is visible to everyone. Chunks are the one
  exception: `msg_chunk_received i j m` is indexed by its receiver `i`,
  because a proposer sends each validator its own chunk.
* *Derived certificates.* A `ghost relation` over the network, owned by
  nobody.
* *Abstract state.* The phase, the MVBA's state, and Chorus's records of
  the MVBA's decision: shared, and changed only by the environment or
  through the MVBA class.

The reading becomes a rule for actions, which
[ChorusDesign.md](../../../ChorusDesign.md) §3.5.3 states:

> Honest actions write only `local_*` rows of the acting validator, `msg_*`
> entries the acting validator is entitled to sign, or a single abstract
> landmark. They read any `msg_*` and any `local_*` row they own; reading
> another validator's `local_*` is a contract violation.

# The shared phase

`phase` is one value, and every timer guard reads it: `propose` and
`record_chunk` before the deadline, `vote` after it, the fallback entries
and the fallback vote from the fallback arm on, and the MVBA proposal's
fast trigger at the MVBA arm. In the protocol each validator has its own
clock and its own timers. The paper assumes the clocks are synchronized, so
that validators share one timeline ({cite}`subsection:mcp-overview`); a
slot's deadline is then one instant for every validator, and `phase` makes
that instant a component of the state. The environment advances it, forward
only, and a validator's timer firing is the guard "the phase has passed".

So the model has no state in which one validator is before the deadline
and another after it, and the paper's synchronized clocks are what make
that faithful. This is the reading to accept. No claim depends on *when*
the environment advances the phase: the safety claims hold for every order
of the phase steps among the others. One property speaks about the phase
itself, `hiding_until_deadline`: the slot key cannot be reconstructed
before the shared deadline. The timed claims add that the markers fire on
time, (P-phase) in [Premises.md](../../../Premises.md) §4.2.

# The monotone network

Two properties make the network *monotone*
([ChorusDesign.md](../../../ChorusDesign.md) §3.1):

* *(M-update)*: an action only adds tuples to a network relation, never
  removes one;
* *(M-frame)*: a guard reads a network relation only in positive position:
  it can require that a message exists, never that one does not.

Together they make every asynchronous run a run of the model. Take a real
run, in which each validator has received some of the messages sent so
far. In the model the network holds every message sent, and each validator
acts on the ones it has received. A positive guard satisfied by fewer
messages is satisfied by more, so every step a real validator takes is a
step of the model. A negative guard would break this: "nobody signed a
conflicting vote" can be true of what a validator received and false of
the network. The model also has runs the protocol lacks, such as a
validator acting on a message it has not yet received; extra behaviour can
only make safety harder to prove. So safety in the model is safety under
asynchrony ([ChorusDesign.md](../../../ChorusDesign.md) §3.2).

(M-update) holds by the form of every update: Veil's generated
monotonicity lemmas cover the updates that write `true`, and the three
bulk updates of `vote` are proven monotone by hand. (M-frame) is checked by
no tool. It is checked by reading each guard, which the audit table below
records ([Architecture.md](../../../Architecture.md) §4, item 1).

Two kinds of negative network read are documented exceptions, each sound
for its own reason ([ChorusDesign.md](../../../ChorusDesign.md) §3.1.1):

* *Self-row reads.* A guard reads negatively a row indexed by the acting
  validator and written only by its own actions: "I have not signed a
  different root" in `propose`, "I have not yet cast my commit vote"
  (`¬ msg_commit_cast i`) in the signing steps of both paths. For a correct
  validator that row is its own history, and no other participant's message
  can disable the guard. [ChorusDesign.md](../../../ChorusDesign.md) §3.1
  lists every one.
* *The witnessed quorum of `fb_sign_neg`.* The paper's validator signs a
  negative fallback entry when, among the votes it received, no root has
  enough positive votes. The model has no "received" set, so the action
  takes one as a parameter, `qv`, a supermajority of broadcast votes, and
  its negation ranges over the votes in `qv` only:

{model Cadence.Chorus "action fb_sign_neg"}

A validator can observe that a quorum is absent from the votes it holds,
so this guard is one a real validator checks. The behaviours asynchrony
makes real stay in: a validator may sign negative although a positive
quorum exists outside `qv`.

Local rows need no exception: a validator observes its own state,
including what it has not yet done. The guards that keep a step from
firing twice read such records, `local_commit_entry i j` and its siblings.

# The adversary as explicit actions

Chorus's safety holds against the adversary the model contains, the
`byz_*` actions, and a capability left out is an attack never checked. So
the adversary must be at least as strong as a real Byzantine validator: it
may do anything that some correct validator could observe. In Chorus it
can

* sign any message in its own name, of every kind, as often as it likes;
* equivocate: sign two roots as a proposer, and deliver different chunks
  to different validators;
* assemble a commit certificate from signatures that exist, and
  re-disseminate a chunk once enough are on the network;
* act at any time, with no fairness, so no liveness argument relies on its
  help ((F-byz), [Premises.md](../../../Premises.md) §3.1).

Its guards are the checks an honest receiver makes: a positive vote entry
carries the signer's chunk, a vote has an entry for every proposer, a
positive fallback entry carries the proposer's signature. A message failing
them is discarded on receipt, so these guards remove only messages that
could never influence a correct validator. What the adversary cannot do is
write a correct validator's row, which is how the model states that
signatures cannot be forged. Inside the MVBA it can do whatever the class
`MVBASafety` leaves unconstrained ([ChorusDesign.md](../../../ChorusDesign.md) §5).

# When a model departs from an idiom

Each idiom keeps the model's runs a superset of the protocol's. Here are
three edits that would break that, one of each kind. They are outlines,
written for this page; none is in the model.

*A guard reading another validator's row.* Suppose `commit_assign_pos i j m`
also required that no validator had committed the negative entry for `j`:

```
require ∀ i', ¬ local_committed_neg i' j     -- outline: not in the model
```

`agreement_pos_neg` would then hold by this guard: a validator commits only
when it sees no conflicting commit. No real validator can see another's
commits, so the theorem would say nothing about the protocol, whose
agreement rests on quorum intersection.

*A guard consulting the fault pattern.* Suppose `record_chunk i j m` also
required `¬ is_byz j`, so that correct validators record only correct
proposers' chunks:

```
require ¬ is_byz j                           -- outline: not in the model
```

A Byzantine proposer's equivocation, different chunks to different
validators, would never reach a correct validator's entries, and every
property that has to survive it would hold because an oracle filtered the
attack out. In a correct validator's action, `is_byz` names its actor and
nobody else.

*Acting on knowledge no node could have.* Suppose the negation in
`fb_sign_neg` ranged over every vote on the network instead of the votes in
`qv`:

```
require ∀ M q, ¬ (nset.greater_than_third q ∧   -- outline: not in the model
  (∀ r, nset.member r q → msg_vote_pos_sig r j M) ∧ …)
```

A real validator knows only the votes it received. This guard would remove
the runs in which a validator signs negative while a positive quorum exists
elsewhere: the runs with late messages, which asynchrony makes real, and
which the speculative-safety argument has to survive.

Nothing in the build flags any of these edits. The proofs still go through,
and may get easier. That is why the idioms are checked by reading the
actions, and what the rest of this chapter is for.

# What an auditor checks

:::claims (title := "What you check, for each action")
1. *Actor.* A correct validator's action requires `¬ is_byz` of its actor
   and of nobody else; an adversary action requires `is_byz` of its own;
   an environment action (the clock, the network's delivery, the MVBA's
   step) belongs to nobody.
2. *Reads.* The actor's own local rows, in either polarity; network
   relations and certificates, in positive position; a negative network
   read only as a self-row read or the witnessed quorum of `fb_sign_neg`.
3. *Writes.* The actor's own local rows; network rows the actor signs; a
   certificate whose guard is its validity check; the shared state through
   its own rules.
4. *The adversary.* Every message a Byzantine validator could send that an
   honest receiver would accept is the update of some `byz_*` action.
5. *The paper.* The guards and updates are the rule the Paper column
   cites.
:::

Today these checks are made by hand, and the table below records them.
The V line is building a checker that computes the actor, read and write
columns from the action bodies. When it lands, the table takes those
columns from it and keeps the Paper and Note columns from this file, and
the other models get tables of their own.

# The Chorus audit table

One row per action, grouped as the model groups them; actions of one shape
share a row. *Reads, own* is the actor's own rows (negative reads marked
`¬`); *Reads, network* is everything else the guards read, in positive
position: network relations, certificates, and the shared state (the phase,
the MVBA class's operations, Chorus's records of the MVBA's decision).
Configuration, such as `is_proposer`, is fixed data every validator knows
and is left out. A note marked ⚠ is a departure beyond the documented
exceptions, under review.

The guide's build checks that every action of the model has a row and that
every relation the derived columns name is part of the model, so the table
cannot silently fall behind the model. Whether each cell is right is the
hand check.

{auditTable Chorus "docs/guide/audit/Chorus.tsv"}

*Further detail:* the network abstraction and its contract,
[ChorusDesign.md](../../../ChorusDesign.md) §3 (the state categories in
§3.5); the adversary, §5; the abstractions worth a reviewer's attention,
§8; and the full list of what has to be believed,
[Architecture.md](../../../Architecture.md) §4.
