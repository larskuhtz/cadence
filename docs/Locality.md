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
| **Local** | one validator's state | an owner index in a fixed position: `local_*` with the owner first, and each model's named list (§6) |
| **Network** | a message on the network | `msg_*`, with the **sender** at a fixed index position and, for a point-to-point message, the **recipient** at another |
| **Environment** | global time | the declared time components: Chorus `phase`, Conductor `now` |
| **Sub-protocol** | the state of a consumed contract | the abstract state of an `instantiate`d contract class, read and changed only through the contract's operations |

Immutable configuration, the action's parameters, and ghost relations (each
of the kind it unfolds to) complete the vocabulary. **No other mutable
global state exists**: in particular no record that several validators
write, and no network relation without a sender.

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

## 5. Certificates

A certificate is formed in local state and travels as a message. A
validator **forms** it in a step that reads the signatures it aggregates
positively (R2) and records it in its own local row (W1), or **receives** it
as a message from a sender (R2) and records it. To send it on, it writes a
network row at its own sender index (W2), guarded by its own local record.
Where the signatures are broadcast to everyone, a step may read the
aggregate as a ghost over the signatures and act on it at once; what it
decides is then recorded in its own local state, never left to be derived
again from the network by a later step.

## 6. The models against the rules

| Model | Local rows (§2) | Status |
|---|---|---|
| Cadence (glue) | `skipped`, `resolved`, `delivered`, `appended` | conforms |
| FallbackReceipt | every relation (one validator) | conforms |
| Chorus | `local_*`, `participating`, `abandoned` | in progress: shared MVBA records, the witnessed quorum, chunk delivery by the environment |
| Mvba | every relation except `msg_*`, `tc_lock`, `tc_nolock` | open: environment-written timers, sender-less certificates |
| Conductor | `entered`, `opened`, `opened_win`, `completed` | open: the global `acs_decided` |
