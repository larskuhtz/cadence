# Locality — what an action may read and write

The models describe a distributed protocol only if every correct
validator's step depends on what that validator can know. This page states
that requirement once, as one idiom for every model: a short list of rules
that each action can be checked against at a glance. No action needs an
argument of its own to pass: a read or a write that fits no rule is a gap in
the model, to be replaced by one that fits.

The rules are also the specification of a locality checker. For each rule
the last column says whether it is **syntactic** — decidable from the
action's text and the declarations' names and index positions — or needs a
**semantic step**, and which one. The semantic steps are the checker's hard
cases.

Why the idiom is sound for safety — every run of the asynchronous protocol
is a run of the model — is [ChorusDesign.md](ChorusDesign.md) §3.2. The
models' own state inventories (what each relation stands for) are in their
design notes: [ChorusDesign.md](ChorusDesign.md) §3.5 for Chorus, the model
headers for the others.

## 1. Declarations the rules use

| Kind | What it is | How a checker finds it |
|---|---|---|
| **Local row** | State owned by one validator, its owner at a fixed index position | `local_*` with the owner first, plus each model's named list (Chorus: `participating`, `abandoned`; Mvba: every mutable relation except the network and certificate relations; Conductor: `entered`, `opened`, `opened_win`, `completed`; the glue: `skipped`, `resolved`, `delivered`, `appended`) |
| **Message** | A signed message on the network, its signer at a fixed index position | `msg_*` with a signer index |
| **Certificate** | A transferable aggregate of messages, with no signer | `msg_*` without a signer index, and the ghost relations defined over messages |
| **Delivery** | A point-to-point message, indexed by its recipient | Chorus's `msg_chunk_received` only |
| **Configuration** | Fixed for the run | `immutable`, the quorum and order theories, the fault predicate |
| **Global time** | One synchronized clock or phase; GST | Chorus `phase`, Conductor `now`; GST appears only in the timed runs |
| **Sub-protocol** | A contract consumed as a class constraint over an abstract state | `instantiate <c> : <Class> …` and the state it is read through (`mvba_st`, `acs_state w`, `os`, `sc_state s`) |

## 2. The actor

Every action has exactly one label.

| Label | Which actions | Rule | Check |
|---|---|---|---|
| **Correct validator `x`** | an action guarded `require ¬ is_byz x` (`¬ fm.byz x` in the Conductor) on a node parameter `x` | `x` is the actor; the rules of §3 and §4 apply | syntactic |
| **Byzantine validator `x`** | `byz_*`, guarded `require is_byz x` | unrestricted reads; writes only what `x` may sign (W2) | syntactic |
| **Input at `x`** | an input the caller invokes (Chorus `participate`, `abandon`; Mvba `propose`, `abandon`) | as a correct validator `x` | syntactic once labelled |
| **Environment** | the clock, message delivery, a sub-protocol's internal step, certificate assembly | may read anything; writes only environment-owned state (E1) | syntactic once labelled |

Today the labels other than the first two are declared by the label classes
of the liveness files ([Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean),
[Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean),
[Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean)), which
classify every action label for the fairness premises. A checker reads them
there, or from an annotation on the action.

## 3. Reads of a correct validator

A correct validator `x`'s guards and update right-hand sides read only:

| Rule | Read | Polarity | Check |
|---|---|---|---|
| **R1 Own state** | a local row at owner `x`; a message row at signer `x` — what `x` has sent | any | syntactic |
| **R2 Network** | a message, certificate or delivery row | positive only | syntactic (polarity of the occurrence, ghosts unfolded) |
| **R3 Configuration** | immutable state; the fault predicate at `x` only | any | syntactic |
| **R4 Sub-protocol at `x`** | a contract observable or input applied to the sub-protocol state and `x` (`mvba.decided mvba_st x v`, `acs.has_decided (acs_state w) x`) | any for `x`'s own inputs, positive for outputs | syntactic |
| **R5 Parameters** | the action's own parameters | any | syntactic |
| **R6 Global time** | the global phase or clock, GST | any | syntactic |

**R1 includes what `x` has sent.** `¬ msg_commit_cast i` in Chorus's
commit and fallback rules, and `∀ m2, msg_proposer_signed j m2 → m2 = m` in
`propose j`, read the actor's own rows: "I have not cast", "I have signed no
other root". A message row at signer `x` is written only by `x`'s correct
actions or, if `x` is Byzantine, by `x`'s Byzantine ones, which a correct
`x` never is.

**R2 is positive.** A message, once produced, stays observable, and a
validator that has not received it yet is free not to act; so a positive
read never requires knowledge a validator lacks. A negative read would: no
validator can observe that a message does not exist. A validator observes
the absence of something only in its own state, which is R1 — so a rule of
the protocol of the form "no `X` among the messages I received" is modelled
by receipt rows: an action of `x` that records a received message in a
local row of `x`, read positively from the network, and the rule reading
those rows negatively.

**R4 covers a sub-protocol's transferable certificates.** A contract
observable without a validator index, read positively, is a certificate the
sub-protocol produces and any holder can forward (Chorus reads
`mvba.certifies mvba_st c e`). It is R2 for the sub-protocol's network.
*Semantic step*: the observable must be monotone, which is a contract field
(`certified_mono`); a checker takes the list of such observables from the
contract.

## 4. Writes of a correct validator

| Rule | Write | Check |
|---|---|---|
| **W1 Own state** | a local row at owner `x` | syntactic |
| **W2 Own messages** | a message row at signer `x` | syntactic |
| **W3 Certificates** | a certificate relation, by an action whose guard is the certificate's validity check over messages (R2) | *semantic step*: the guard must imply the validity predicate; syntactic when the guard names it |
| **W4 Deliveries** | a delivery row, by a send of `x` whose guard shows `x` holds the content | *semantic step*: what "holds the content" means is the message type's |
| **W5 Sub-protocol inputs** | the sub-protocol state, only as `st := next` after `require <input> st x … next` at the actor's index | syntactic; *semantic step* for the frame — that the input changes no other correct validator's inputs — which is a contract field |

## 5. Environment and Byzantine actions

**E1 The environment** may read any state: it is the scheduler and the
network. It writes only state that no correct validator's action writes —
global time, deliveries, a sub-protocol's internal state, assembled
certificates, and a validator's input rows that the environment owns (Mvba's
`timer_expired i v`, `avail_ready i x`). An environment action never writes
a row a validator's own rule writes, so it never stands in for a
validator's decision. *Check*: syntactic, given the writer sets of every
relation.

**B1 Byzantine validators** collude arbitrarily, so their reads are
unrestricted: a fully unconstrained adversary subsumes any collusion. What
binds them is unforgeability: a Byzantine `x` writes message rows only at
signer `x` (W2), and certificates and deliveries only under the same
validity checks a receiver performs (W3, W4), since a message failing them
is discarded on receipt. *Check*: syntactic for W2.

## 6. What the rules leave to the reader

Two things stay outside any rule and are checked once, per model, by the
model's design note: what each relation stands for in the paper (the state
inventories), and the soundness of the monotone network itself
([ChorusDesign.md](ChorusDesign.md) §3.2). The audit table of Chorus
([guide/audit/Chorus.tsv](guide/audit/Chorus.tsv)) applies the rules action
by action.
