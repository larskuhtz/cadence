/-
Chapter 4 of the guide: What a model asks you to accept.

The modelling idioms of Chorus, and the audit table that checks every
action against them. The table is the data file
[Chorus.tsv](../../audit/Chorus.tsv), filled by hand from the action
bodies and checked against the model's actions when the guide builds.
-/
import CadenceGuide.Elements
import CadenceGuide.ChapterList

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "What a model asks you to accept" =>
%%%
file := "modelling-idioms"
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
({chapter ReadingModel}[chapter 3] has the table):

* *Local rows.* A `local_*` relation is indexed by the validator that owns
  it, its first argument: `local_entry_pos i j m` is validator `i`'s record.
* *Messages.* A `msg_*` relation is indexed by its sender, first. A tuple is
  a message that has been sent and stays visible. Chunks are the one
  point-to-point message: `msg_chunk s i j m` names its recipient `i`
  second, because a proposer sends each validator its own chunk.
* *Derived certificates.* A `ghost relation` over the messages, owned by
  nobody: a validator that has received the signatures can check it.
* *Auxiliary records.* An `aux_*` relation records history for the proofs.
  Actions write it and none reads it, so it changes no run.
* *Global time and the MVBA.* The phase, which the environment moves, and
  the MVBA's state, used only through the MVBA class at the acting
  validator's index.

# The rules

The reading becomes rules for actions. They are stated once, for every
model, in [Locality.md](../../../Locality.md), in a form a checker can apply
by matching names, index positions and the sign of a read. A correct
validator `x` reads

* *R1* its own local rows, in either polarity;
* *R2* messages in positive position, and a point-to-point message, a
  chunk, only as its recipient;
* *R3* its own sends, in either polarity: "I have signed no other root",
  "I have not cast my commit vote";
* *R4* global time;
* *R5* configuration, and the fault predicate only at `x`;
* *R6* the MVBA class's operations at index `x`;

and writes

* *W1* its own local rows;
* *W2* messages under its own name, only by adding them;
* *W3* the MVBA's state, only through an input at index `x`.

The environment reads and writes only global time. A Byzantine validator
may read anything, since a coalition of them is subsumed by one
unconstrained adversary, and it writes messages only under its own name.
A read or a write that fits no rule is a gap in the model, to be replaced
by one that fits.

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

The messages form a *monotone* network: an action only adds messages, and
a correct validator reads another's message only in positive position — it
can require that a message exists, never that one does not
([Locality.md](../../../Locality.md) §1). That is how the model captures a
network that delays or drops messages at will: a message, once sent, may
be acted on at any later step, or never.

This makes every asynchronous run a run of the model. Take a real run, in
which each validator has received some of the messages sent so far. In the
model the network holds every message sent, and each validator acts on the
ones it has received. A positive guard satisfied by fewer messages is
satisfied by more, so every step a real validator takes is a step of the
model. A negative guard over other validators' messages would break this:
"nobody signed a conflicting vote" can be true of what a validator received
and false of the network. The model also has runs the protocol lacks, such
as a validator acting on a message the real network would deliver later;
extra behaviour can only make safety harder to prove. So safety in the model
is safety under asynchrony ([ChorusDesign.md](../../../ChorusDesign.md) §3.2).

Where the paper's rule does depend on what a validator has *not* received,
the model gives the validator that state. The fallback entry is negative
when, among the votes the validator received, no root has enough positive
votes. So the validator keeps a receipt of each vote it receives,
`receive_vote_pos` and `receive_vote_neg`, and `fb_sign_neg` reads its own
receipts:

{model Cadence.Chorus "action fb_sign_neg"}

Monotone updates hold by the form of every update: Veil's generated
monotonicity lemmas cover the updates that write `true`, and the three bulk
updates of `vote` are proven monotone by hand. The rules on reads are
checked by reading each action, and the audit table below records that
check ([Architecture.md](../../../Architecture.md) §4,
item 1).

# The adversary as explicit actions

Chorus's safety holds against the adversary the model contains, the
`byz_*` actions, and a capability left out is an attack never checked. So
the adversary must be at least as strong as a real Byzantine validator: it
may do anything that some correct validator could observe. In Chorus it
can

* sign any message in its own name, of every kind, as often as it likes;
* equivocate: sign two roots as a proposer, send different chunks to
  different validators, and send different votes to different validators;
* form a certificate from signatures that exist and send it, and
  re-disseminate a chunk once enough are on the network;
* act at any time, with no fairness, so no liveness argument relies on its
  help ((F-byz), [Premises.md](../../../Premises.md) §3.1).

Its guards are the checks an honest receiver makes: a positive vote entry
carries the signer's chunk, a vote has an entry for every proposer, a
positive fallback entry carries the proposer's signature, a certificate
has its signatures. A message failing them is discarded on receipt, so
these guards remove only messages that could never influence a correct
validator. What the adversary cannot do is send under a correct
validator's name or write its rows, which is how the model states that
signatures cannot be forged. Inside the MVBA it can do whatever the class
`MVBASafety` leaves unconstrained ([ChorusDesign.md](../../../ChorusDesign.md) §5).

# When a model departs from an idiom

Each rule keeps the model's runs a superset of the protocol's. Here are
three edits that would break one, each a different rule. They are
outlines, written for this page; none is in the model.

*A guard reading another validator's row.* Suppose
`commit_assign_pos_fast i j m c` also required that no validator had
committed the negative entry for `j`:

```
require ∀ i', ¬ local_committed_neg i' j     -- outline: not in the model
```

`agreement_pos_neg` would then hold by this guard: a validator commits only
when it sees no conflicting commit. No real validator can see another's
commits, so the theorem would say nothing about the protocol, whose
agreement rests on quorum intersection. The rule broken: *R1*, a validator
reads only its own local rows.

*A guard consulting the fault pattern.* Suppose `record_chunk i j m` also
required `¬ is_byz j`, so that correct validators record only correct
proposers' chunks:

```
require ¬ is_byz j                           -- outline: not in the model
```

A Byzantine proposer's equivocation, different chunks to different
validators, would never reach a correct validator's entries, and every
property that has to survive it would hold because an oracle filtered the
attack out. The rule broken: *R5*, a correct validator's action reads the
fault predicate only at its actor.

*Acting on knowledge no node could have.* Suppose `fb_sign_neg` read the
votes on the network instead of its own receipts, negatively:

```
require ∀ M q, ¬ (nset.greater_than_third q ∧   -- outline: not in the model
  (∀ r, nset.member r q → msg_vote_pos_sig r j M) ∧ …)
```

A real validator knows only the votes it received. This guard would remove
the runs in which a validator signs negative while a positive quorum exists
elsewhere — the runs with late messages, which asynchrony makes real, and
which the speculative-safety argument has to survive — and a Byzantine
validator signing a late positive entry could block a correct validator's
step. The rule broken: *R2*, messages are read only in positive position.

Nothing in the build flags any of these edits. The proofs still go through,
and may get easier. That is why the rules are checked by reading the
actions, and what the rest of this chapter is for.

# What an auditor checks

:::claims (title := "What you check, for each action")
1. *Actor.* A correct validator's action requires `¬ is_byz` of its actor
   and of nobody else; an adversary action requires `is_byz` of its own;
   an environment action (the phase markers) reads and writes only the
   phase; the MVBA's step belongs to the MVBA.
2. *Reads.* The actor's own local rows, in either polarity; its own sends,
   in either polarity; other messages and the certificates over them, in
   positive position, and a chunk only as its recipient; the phase,
   configuration, and the MVBA class at the actor's index, or its check of
   a certificate the actor received.
3. *Writes.* The actor's own local rows; messages under its own name; the
   MVBA's state through an input at its index; auxiliary records, which no
   action reads.
4. *The adversary.* Every message a Byzantine validator could send that an
   honest receiver would accept is the update of some `byz_*` action.
5. *The paper.* The guards and updates are the rule the Paper column
   cites.
:::

Today these checks are made by hand, and the table below records them.
The V line is building a checker that computes the actor, read and write
columns from the action bodies, by the rules of
[Locality.md](../../../Locality.md). When it lands, the table takes those
columns from it and keeps the Paper and Note columns from this file, and
the other models get tables of their own.

# The Chorus audit table

One row per action, grouped as the model groups them; actions of one shape
share a row. *Reads, own* is the actor's own rows (negative reads marked
`¬`); *Reads, network* is everything else the guards read, all in positive
position: messages and certificates, the phase, and the MVBA class's
operations. *Negative network reads* are only ever the actor's own sends.
Configuration, such as `is_proposer`, is fixed data every validator knows
and is left out. The note names the rules of
[Locality.md](../../../Locality.md) each row follows.

The guide's build checks that every action of the model has a row and that
every relation the derived columns name is part of the model, so the table
cannot silently fall behind the model. Whether each cell is right is the
hand check.

{auditTable Chorus "docs/guide/audit/Chorus.tsv"}

*Further detail:* the rules, [Locality.md](../../../Locality.md); how Chorus
instantiates them, [ChorusDesign.md](../../../ChorusDesign.md) §3 (the state
by kind in §3.5); the adversary, §5; the abstractions worth a reviewer's
attention, §8; and the full list of what has to be believed,
[Architecture.md](../../../Architecture.md) §4.
