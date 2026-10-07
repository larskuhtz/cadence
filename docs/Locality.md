# Locality — what an action may read and write

The models describe a distributed protocol only if every correct
validator's step depends on what that validator can know, and changes only
what it owns. This page states that requirement once, for every model, as
rules that each action can be checked against by pattern matching over
names, index positions and the polarity of a read. A read or a write that
fits no rule is a gap in the model, to be replaced by one that fits; no
action carries an argument of its own.

The rules are also the specification of a locality checker. The last column
of each table says whether a rule is **syntactic** — decidable from the
action's text and the declarations — or needs a **semantic step**, and
which one.

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
global state exists**: in particular no record that several validators
write, and no network relation without a sender.

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

**A correct validator `x`** reads only:

| Rule | Read | Check |
|---|---|---|
| **R1** | its own local rows, in either polarity | syntactic |
| **R2** | network rows in positive position; a point-to-point row only at recipient `x` | syntactic (polarity of the occurrence, ghosts unfolded) |
| **R3** | network rows at sender `x`, in either polarity: what it has sent is its own state | syntactic |
| **R4** | environment state (global time) | syntactic |
| **R5** | configuration and its parameters; the fault predicate only at `x` | syntactic |
| **R6** | the sub-protocol's operations at index `x` (`mvba.decided mvba_st x v`) | syntactic |

and writes only:

| Rule | Write | Check |
|---|---|---|
| **W1** | its own local rows | syntactic |
| **W2** | network rows at sender `x`, only by `:= true` (or a disjunction with the old value) | syntactic |
| **W3** | the sub-protocol state, only as `st := next` after `require <c>.<input> st x … next` | syntactic; *semantic step*: that an input changes no other validator's part, which is the contract's frame fields |

**A Byzantine validator `x`** may read anything: a coalition of Byzantine
validators is subsumed by an unconstrained one, and so is ignoring a message
it has read. It writes only network rows at sender `x` (unforgeability),
monotonically (W2), and the sub-protocol state only through the contract,
whose Byzantine behaviour is the contract's. It never writes a correct
validator's local state or the environment's. *Check*: syntactic. That a
Byzantine message passes the checks a correct receiver applies is a
faithfulness matter, stated per action, not a locality one.

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
| a **pure function** of data the node holds | `mvba.entries v` | R5 |
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
| Conductor | `opened_win` (the window a slot was opened in; to be renamed `aux_opened_win`) |
| Cadence (glue), FallbackReceipt, Mvba | none |

| Model | Local rows (§2) | Status |
|---|---|---|
| Cadence (glue) | `skipped`, `resolved`, `delivered`, `appended` | conforms |
| FallbackReceipt | every relation (one validator) | conforms |
| Chorus | `local_*`, `participating`, `abandoned` | conforms; checked action by action in the guide's audit table ([guide/audit/Chorus.tsv](guide/audit/Chorus.tsv)) |
| Mvba | every relation except `msg_*`, `tc_lock`, `tc_nolock` | open: environment-written timers, sender-less certificates |
| Conductor | `entered`, `opened`, `opened_win`, `completed` | open: the global `acs_decided` |
