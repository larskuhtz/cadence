# Locality — what an action may read and write

*The locality rules for the actions of every model. [The guide's chapter
4](https://larskuhtz.github.io/cadence/guide/modelling-idioms/) teaches them
on Chorus: why each matters, how a departure makes a theorem hold for the
wrong reason, and the table that checks every Chorus action. This page is
the authority for the rules, and the specification of a locality checker.*

The models describe a distributed protocol only if every correct
validator's step depends on what that validator can know, and changes only
what it owns. This page states that requirement once, for every model, as
rules that each action can be checked against by pattern matching over
names, index positions and the polarity of a read. A read or a write that
fits no rule is a gap in the model, to be replaced by one that fits; no
action has an exception argued for it alone.

The last column of each table says whether a rule is **syntactic** —
decidable from the action's text and the declarations — or needs a
**semantic step**, and which one.

## 1. Why the network is monotone

A validator talks to the rest of the system — other validators, and the
environment — only through the network. The network is the set of
`msg_*` relations, and they are **global** and **monotone**: a message,
once sent, stays observable, and no node is ever forced to act on it.

That one idealisation captures a Byzantine network up to synchrony. A
message may be delayed arbitrarily: its receiver acts on it whenever it
chooses, or never. Before GST this is the asynchronous network, under which
safety must hold; after GST it still encodes every delay up to the bound.
So a model that is safe under the monotone network is safe under any
scheduling of the real one ([ChorusDesign.md](ChorusDesign.md) §3.2 is the
simulation).

Liveness overlays the fewest assumptions that make progress possible: when
the environment moves global time on (Chorus's phase, the Conductor's
clock), that a correct validator's enabled step eventually fires, that its
local timeouts expire, and that after GST a message is acted on within `Δ`.
They are stated over runs, outside the models, and listed in
[Premises.md](Premises.md). The premises follow the paper's partial
synchrony: no message is lost, and one sent before GST arrives by GST + `Δ`
([Bounds.md](Bounds.md) §2).

Monotonicity is required of the network, and of global time, which only
moves forward. Local state carries no such requirement: a validator
observes its own state exactly, so it may read it in either polarity and
overwrite it.

## 2. The kinds of state

Every mutable component is of exactly one kind, recognisable from its
declaration.

| Kind | What it is | How a checker recognises it |
|---|---|---|
| **Local** | one validator's state | an owner index in a fixed position: `local_*` with the owner first, and each model's named list (§7) |
| **Network** | a message on the network | `msg_*`, with the **sender** at a fixed index position and, for a point-to-point message, the **recipient** at another |
| **Environment** | global time | the declared time components: Chorus `phase`, Conductor `now` |
| **Sub-protocol** | the state of a consumed contract | the abstract state of an `instantiate`d contract class, read and changed only through the contract's operations |
| **Auxiliary** | a history record for the proofs, not protocol state | the `aux_` prefix |

Immutable configuration, the action's parameters, and ghost relations (each
of the kind it unfolds to) complete the vocabulary. **No other mutable
protocol state exists**: in particular no protocol record that several
validators write, and no network relation without a sender. (Auxiliary
records, below, are not protocol state.)

**Auxiliary relations** record what happened so that invariants can refer to
it afterwards — which certified entries the MVBA produced, which vote quorum
a validator signed a negative entry against. Any action may write one; **no
action reads one**, in a guard or in an update's right-hand side, so they
cannot change which runs exist: deleting every auxiliary relation from a
model leaves its transitions on the other state unchanged. Invariants and
proofs read them freely. *Check*: syntactic — no action body mentions an
`aux_` relation except as the target of an assignment.

## 3. The actors

Every action has exactly one actor.

| Actor | Which actions | Check |
|---|---|---|
| **Correct validator `x`** | guarded `require ¬ is_byz x` (`¬ fm.byz x` in the Conductor) on a node parameter `x`; and the inputs a caller invokes at `x` | syntactic; inputs once labelled |
| **Byzantine validator `x`** | `byz_*`, guarded `require is_byz x` | syntactic |
| **Environment** | the actions that move global time | syntactic once labelled |
| **Sub-protocol** | a consumed contract's own step (`mvba_step`) | syntactic: the only write is the sub-protocol state, through `<c>.step` |

## 4. The rules

The rules read differently for the two kinds of validator, because
constraining each one moves the claims in opposite directions. A theorem
about the models holds for every run they allow. Restricting a correct
validator to what it can know and own makes those runs *more* like the real
protocol's, and the claims stronger; restricting a Byzantine validator
removes attacks, and makes the claims weaker. So a correct validator's rules
are **permissions** (§4.1): it may do only what they allow. A Byzantine
validator's rules are **prohibitions** (§4.2): it may do anything they do not
forbid, and each prohibition is either cryptography or a gap that is listed.

### 4.1 Correct validators: what a step may do

**A correct validator `x`** reads only:

| Rule | Read | Check |
|---|---|---|
| **R1** | its own local rows, in either polarity | syntactic |
| **R2** | network rows in positive position; a point-to-point row only at recipient `x` | syntactic (polarity of the occurrence, ghosts unfolded) |
| **R3** | network rows at sender `x`, in either polarity: what it has sent is its own state | syntactic |
| **R4** | environment state (global time) | syntactic |
| **R5** | configuration and its parameters; the fault predicate only at `x` (the actor guard `¬ is_byz x`) | syntactic |
| **R6** | the sub-protocol's operations at index `x` (`mvba.decided mvba_st x v`) | syntactic |

and writes only:

| Rule | Write | Check |
|---|---|---|
| **W1** | its own local rows | syntactic |
| **W2** | network rows at sender `x`, only by `:= true` (or a disjunction with the old value) | syntactic |
| **W3** | the sub-protocol state, only as `st := next` after `require <c>.<input> st x … next` | syntactic; *semantic step*: that an input changes no other validator's part, which is the contract's frame fields |

The rules bound what a correct step can *know*; they do not say what it
*must* do. That is the paper's algorithm, which each action follows, and
a correct step that waits for less than the paper's handler does, or more,
is a faithfulness matter, checked against the paper
([PaperAlignment.md](PaperAlignment.md)), not a locality one.

The actor guard reads the fault predicate at the actor's own index. It marks
the step as a correct validator's, which is how §3 recognises the actor, and
reads nothing about any other validator: no correct step reads the fault
status of another validator, in a guard or in an update.

### 4.2 Byzantine validators: what a step must not do

**A Byzantine validator `x`** may do anything the following rules do not
forbid.

| Rule | Prohibition | Check |
|---|---|---|
| **B1** | it writes no correct validator's local state and no environment state; it writes network rows only at sender `x`, and only by `:= true` | syntactic |
| **B2** | it forges no signature: a row carrying a correct validator's signature is sent only by that validator, a certificate is formed only from signatures on the network, and a proposer-signed root only exists if its proposer signed it (`msg_proposer_signed`) | syntactic: the guard reads the signature's network row positively |
| **B3** | it changes the sub-protocol state only through the contract, whose own Byzantine behaviour is the implementing model's | syntactic |
| **B4** | it sends no message that every correct receiver would reject: the check a correct receiver applies is stated as a guard on the Byzantine sender | syntactic; listed below, each one a gap |

**Nothing limits what a Byzantine step reads.** A coalition of Byzantine
validators is subsumed by one unconstrained adversary, and the models let it
read even a correct validator's local state, which the paper's adversary,
seeing only the messages sent to it, cannot. That makes the adversary
stronger than the paper's, and every claim holds against it; no proof relies
on what a Byzantine validator does not know.

**B2 models signatures by their absence.** Every message on the network
carries valid signatures; one with an invalid signature is modelled as never
sent, which is the same as a correct receiver discarding it. So B2 is the
cryptographic assumption, part of the locality rules in the inventory of
what has to be believed ([Architecture.md](Architecture.md) §4, item 1),
not a restriction of the adversary's choices. A certificate's content is
what its signatures determine: a timeout certificate's `highPrepQC` is the
highest certificate its members carry whose view is at most the view of
the timeout carrying it (Supplement, Algorithm 1, line 4
(`line:mvba:derived`)), which is why `byz_form_tc_lock` and
`byz_form_tc_nolock` read their members' views, as the correct
`form_own_tc_*` do.

**B4 is a gap in the model, to be closed.** A guard that stands for a
receiver's check is equivalent to the check only while every correct
receiver applies it, and it hides the check from the correct side, where
the paper has it. None remain: every receiver check is a guard of the
correct receiver, and only B1–B3 constrain the adversary. The table lists
the B4 guards a model carries, and is empty:

| Model | Action | Guard | The receiver's check (paper) |
|---|---|---|---|

### 4.3 The environment and the sub-protocol

**The environment** reads and writes only environment state. It never
reads or writes a validator's state or the network. *Check*: syntactic.

**A sub-protocol's step** writes only the sub-protocol state. Its own
locality is the implementing model's, checked there by these same rules
(`Mvba` for the MVBA); the contract abstracts it.

## 5. Composition

A model consumes a sub-protocol through its contract class
([CompositionContracts.md](CompositionContracts.md)), and the contract's
operations are the interface between a node and its part of the
sub-protocol. The rule is the same as for state: **an operation a node
invokes carries only information available to that node, and what it
returns carries only information local to that node.** Concretely, every
operation an action uses is one of:

| Operation | Example | Rule |
|---|---|---|
| an **input** at the actor's index | `mvba.propose st x v next`, `acs.abandon st x next` | W3 |
| an **output or record** at the actor's index | `mvba.decided st x v`, `acs.has_decided st x` | R6 |
| a **pure function** of data the node holds | `mvba.entries v`; the Conductor's `acs_first (acs_state w) x`, the first slot `x` computes from its own decided set | R5; for `acs_first`, a *semantic step*: the model's assumption `[acs_first_local]` that it reads only the decided set at its index |
| a **check** of a message the node holds | `mvba.certifies st c e`, for a certificate `c` the node has received | R2: the check holds iff the signatures it verifies are on the sub-protocol's network, which a contract field keeps monotone (`certified_mono`) |

The sub-protocol's own step (`mvba.step`) is not invoked by a node: it is the
sub-protocol's actors, whose locality the implementing model checks.

The split is between **computational content and properties**. The
operations above are what actions compute with, and they obey these rules.
The contract's *fields* — agreement, frames, monotonicity, the temporal
obligations — are properties: they relate the state at several validators,
or several states, and are used only in invariants and proofs, which are
not bound by locality. A field never appears in a guard; that would be
restating a contract property in a consumer, which the composition already
forbids. *Check*: syntactic — a guard's contract terms are the operations
above, at the actor's index where they take one.

## 6. Certificates

A certificate is formed in local state and travels as a message. A
validator **forms** it in a step that reads the signatures it aggregates
positively (R2) and records it in its own local row (W1), or **receives** it
as a message from a sender (R2) and records it. To send it on, it writes a
network row at its own sender index (W2), guarded by its own local record.
Where the signatures are broadcast to everyone, a step may read the
aggregate as a ghost over the signatures and act on it at once; what it
decides is then recorded in its own local state, never left to be derived
again from the network by a later step.

## 7. The models against the rules

The auxiliary relations of every model:

| Model | Auxiliary relations |
|---|---|
| Chorus | `aux_mvba_decided_pos`, `aux_mvba_decided_neg` (the certified entries), `aux_fb_neg_qv` (the vote quorum behind a negative fallback entry) |
| Conductor | `aux_opened_win` (the window a slot was opened in) |
| Cadence (glue), FallbackReceipt, Mvba | none |

| Model | Local rows (§2) | Status |
|---|---|---|
| Cadence (glue) | `skipped`, `resolved`, `delivered`, `appended` | conforms |
| FallbackReceipt | every relation (one validator) | conforms |
| Chorus | `local_*`, `participating`, `abandoned` | conforms, checked action by action in the guide's audit table ([guide/audit/Chorus.tsv](guide/audit/Chorus.tsv)); `send_mvba_cert` sends the certificate its own decision output (`mvba.decidedCert`, an output at the actor's index, R6); no B4 guard: a Byzantine vote may be incomplete or carry any chunk, and the vote receipts and the fallback entry count only votes that pass the paper's vote handler (`vote_valid`, [ChorusDesign.md](ChorusDesign.md) §3.5.3) |
| Mvba | every relation except `msg_*` | conforms: the view timer is the validator's own step, every certificate is sent by its former or forwarder under its own name, a decision records its certificate (`decided_qc`), and the adversary aggregates only under its own name (`byz_form_*`); no B4 guard: a Byzantine timeout may carry a certificate of any view, and the timeout-certificate rules read one above the timeout's view as `⊥`, as the supplement's receiver does; [MvbaPlan.md](MvbaPlan.md) §11 has the design |
| Conductor | `entered`, `local_bounds`, `opened`, `completed` | conforms: each validator computes its window's interval from its own ACS decision in its entry step (`acs_first`, Algorithm 7, line 48 (`line:median-compute`)) and keeps it in its own row, so agreement on the intervals is a property (`[window_assignment_agreement]`), not a shared write; [ConductorBounds.md](ConductorBounds.md) §10 has the design |
