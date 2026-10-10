# Chorus — Veil model design notes

*The design rationale of the Chorus model. [The guide's chapters
3](https://larskuhtz.github.io/cadence/guide/reading-a-model/) and [4](https://larskuhtz.github.io/cadence/guide/modelling-idioms/) teach how to read the
model and what it asks an auditor to accept; this page is the authority for
how Chorus instantiates the locality rules of [Locality.md](Locality.md)
(§3) and for the Chorus modelling choices.*

The top-level architecture document, with the methods, the trust bases and
the meta-assumption inventory, is [Architecture.md](Architecture.md).

This document explains the modelling choices in
[Cadence/Chorus.lean](../Cadence/Chorus.lean) and [Cadence/Primitives.lean](../Cadence/Primitives.lean):
what is in scope, what is abstracted, and what limitations the chosen
abstractions impose on the kind of properties that can be proven.

## 1. Scope

Chorus is the inner *per-slot one-shot* BFT consensus layer of Cadence.
Paper target: [PaperAlignment.md](PaperAlignment.md) §0. Citations name what the
target's rendered PDF shows, with the label in parentheses; the root
[README.md](../README.md) says how to resolve them. The Chorus
chapter is Appendix C (`section:slot_agreement`), with pseudocode in Algorithm 2
(`alg:proposer-dissemination`) to Algorithm 6 (`alg:da`), and the MVBA
module specification is Module 3 (`mod:mvba`).

For each slot `s` Chorus runs an independent agreement instance among a
set `Π` of `n = 3f + 1` validators with `k` concurrent *proposers*
`Ps ⊆ Π`. The protocol has three time landmarks per slot:

* **`Ds`** (deadline) — proposers stop disseminating; validators broadcast
  their proposal votes (one signed entry per proposer, plus chunks and
  the decryption share).
* **`Ds + Δ`** (fallback arm) — validators that have received ≥ 2f+1
  votes and have not cast a fast commit vote enter the fallback path.
* **`Ds + 2Δ`** (MVBA arm) — the MVBA may be invoked (also by validators
  holding a complete fast meta-block — the paper's case-(a) trigger).

Finalization occurs via one of two *commitment proofs*
(Lemma 9 (`lemma:chorus-agreement`)):

* **Fast path** (Algorithm 4 (`alg:fast-path-certification`)): two voting rounds
  produce a `commitQC` (2f+1 matching broadcast fast commit votes).
  A validator that holds FastQCs for every proposer may additionally
  commit *speculatively* before the commitQC forms; speculation is not
  finalization and is revertible under equivocation (see §8).
* **Fallback path** (Algorithm 5 (`alg:fallback`)): a third round of fallback votes
  enables the slot's MVBA instance, whose decided certificate finalizes
  the slot.

The model is **single-slot**: state and messages are not
slot-parameterised, since per-slot instances are independent. The `slot` type
is retained as a placeholder for a possible multi-slot extension.

## 2. Type-level structure

```
slot          -- opaque slot identifier (placeholder, see §1)
node          -- validator identity
nodeset       -- a set of nodes; carries the supermajority / >1/3 quorum
              -- predicates and Byzantine intersection axioms via the
              -- ByzNodeSet class (Veil/Frontend/Std.lean).
merkle_root   -- opaque commitment to an erasure-coded encrypted proposal.
```

Modelling Merkle roots as an opaque token (rather than as a hash of the
underlying chunks) is sufficient because the binding property we use is
already captured at the signature level: a positive vote/commit entry
for `(s, j, m)` is *only* produced by an honest validator that recorded
*some* chunk under root `m`, and the proposer signature ties `m` to a
unique payload via injectivity of the hash (cf.
[Cadence/Primitives.lean](../Cadence/Primitives.lean) `HashFunction` and `MerkleTree`).

## 3. Network model

We follow the standard Veil idealisation of asynchronous BFT:

> Each signed message is a *monotone* relation. Once produced, it
> remains observable forever.

The rules every action follows — what a correct validator may read and
write, what the environment and the adversary may do — are stated once, for
every model, in [Locality.md](Locality.md). This section says how Chorus
instantiates them: which relations are messages, which are local, and the
few places where a reader might expect something else.

The **messages** are the `msg_*` relations, each with its sender at the
first index: `msg_proposer_signed`, `msg_chunk` (the one point-to-point
message, recipient second), `msg_vote_pos_sig`, `msg_vote_neg_sig`,
`msg_vote_cast`, `msg_decrypt_share`, `msg_fb_pos_sig`, `msg_fb_neg_sig`,
`msg_fallback_sig`, `msg_commit_pos_sig`, `msg_commit_neg_sig`,
`msg_commit_cast`, `msg_commitqc_pos/neg`, `msg_fbcommit_sig`,
`msg_fbcommitqc` and `msg_mvba_cert`. The **local state** is the `local_*`
relations, owner first, with `participating` and `abandoned`. The
**auxiliary records**, written by actions and read by none, are
`aux_mvba_decided_pos/neg` and `aux_fb_neg_qv`. Global time is `phase`, and
the consumed MVBA's state is `mvba_st`. Transferable certificates
(FastQC, FallbackQC, EquivCert, FBCert, commitQC, fbCommitQC,
decodability, the reconstructed slot key) are also **derived predicates**
(`ghost relation`s) over the signatures — see §3.5.

### 3.1 What "monotone" means here

The single word "monotone" hides two distinct properties:

* **(M-update)** *Monotone update* — tuples can only be added to the
  relation, never removed.
* **(M-frame)** *Positive-only use* — the relation appears in a correct
  validator's guards and updates only in positive position, except where
  the validator reads what it has itself sent.

The network relations have both, and the soundness argument of §3.2 uses
both. Local state needs neither: a validator observes its own state
exactly, so it may read it in either polarity and overwrite it
(`local_path` is a function that changes value). Global time only moves
forward.

(M-update) is syntactic for every network relation: each write is the
literal `true`, except `vote`'s bulk updates of `msg_vote_pos_sig` and
`msg_vote_neg_sig` (and of the voter's own `local_entry_neg`), which are disjunctions with the
relation's old value (`msg_vote_pos_sig i J M := msg_vote_pos_sig i J M ||
(…)`). Veil's generated `<f>.mono` lemmas cover the literal-`true` writes
only, so those three are proven by hand, with the same statement, in
[Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)
(`Chorus.msg_vote_pos_sig_mono` and its two siblings).

(M-frame) is the rule R2 of [Locality.md](Locality.md), with R3 for the
validator's own sends. The reads of Chorus that are negative and touch a
message are all R3 — a read of a row whose sender is the acting validator:

* `propose j` requires `∀ m2, msg_proposer_signed j m2 → m2 = m` — "I have
  signed no other root";
* `commit_sign_pos`, `commit_sign_neg`, `cast_fast_commit`, `fb_sign_pos`,
  `fb_sign_neg` and `cast_fallback_vote` require `¬ msg_commit_cast i` —
  "I have not cast my fast commit vote".

Every other negative read is of the validator's own local rows (R1): the
fired-once records, `local_path`, the receipts.

**One relation per message type.** Each signed object is its own relation
in the inventory above, and every guard reads the relation of the type it
needs, so a signature of one type can never stand for another in the
model. The implementation's side of this choice is the supplement's rule
that all signatures are domain-separated: "the bytes signed for each
message type begin with a tag unique to that type", which "rules out
type-confusion attacks" (Supplement, Section 10.5 (`sec:domain-separation`)). At the target the main
body tags every signature as well (`⟨Prop, s, j, H(payload)⟩` and
`⟨Root, s, j, ρ⟩` for the proposer, `vote`, `fb`, `fallback`, … for the
votes; [PaperAlignment.md](PaperAlignment.md) §5.1). The models rest on
non-confusability; the tags are how a deployment obtains it.

`phase` is a 4-valued enum (`pre_deadline → post_deadline →
post_fb_arm → post_mvba_arm`); it advances only through the environment's
`advance_to_*` actions, whose preconditions force the forward direction.

**A rule that reads the absence of something reads its own receipts.** The
paper's validator signs a *negative* fallback entry for `j` exactly when,
among the ≥ 2f+1 votes it received, no root has an f+1 positive sub-quorum
with decodable data (Algorithm 5, line 8 (`line:fb-cast-entry`),
else-branch). "Among the votes it received" is a statement about the
validator's own state, so the model gives it that state: the receive steps
`receive_vote_pos` / `receive_vote_neg` record, in the validator's own
rows, the entry of each sender's vote it receives — one per sender and
proposer, the first, as a vote is one message per sender
(Algorithm 3, line 14 (`line:vote-broadcast`)). `fb_sign_neg i j qv`
requires `i` to hold the entry for `j` of every vote in the supermajority
`qv`, and reads those receipts negatively. Decodability adds no condition:
`f+1` received positive votes carry `f+1` chunks. The positive rule
`fb_sign_pos`, and the FastQC aggregation, read the vote signatures on the
network directly, positively, rather than through receipts: a signature
there may be one a Byzantine signer never cast in a vote, which only adds
behaviours, and every receipt is backed by a cast vote's signature
(`vote_rcv_pos_backed`), so whenever the negative rule is disabled the
positive one is enabled.

**The fallback commit vote reads only the validator's own decision.**
`cast_fb_commit i v` requires `mvba.decided mvba_st i v` (the contract's
output at `i`), its own transport record `local_mvba_complete i`, and waits
under exactly the FallbackQC entries of `v`: `∀ J M, mval_pos
(mvba.entries v) J M → mval_fb v J → chunk_received i J M`, the chunks
addressed to `i` (Algorithm 5, lines 37–39
(`line:fb-mvba-decide`–`line:fb-commit-wait`), and Algorithm 5, line 41
(`line:fb-commitvote`), which signs `entries(B′)` of the validator's own
`B′`; [PaperAlignment.md](PaperAlignment.md) §8.1 (d)).

**A certificate carries its entries.** A validator finalizes on a
certificate it received, and the certificate says what is committed: a
fast commit certificate names its entry, a fallback commit certificate
`fbCommitQC = ⟨FallbackCommit, s, E, Σ⟩` carries the vector `E`
(Algorithm 5, line 45 (`line:fb-recv-commit`)), and the MVBA's commit
certificate is checked against a representation of the entries it
certifies. So the three finalization routes (`commit_assign_*_fast`,
`_fb`, `_mvba`) read only the received message, and each re-broadcasts it
under the finalizer's own name (Algorithm 4, line 35
(`line:fast-rebroadcast-commitqc`), Algorithm 5, line 46
(`line:fb-commit-rebroadcast`)).

Crucially, **nothing forces a validator to act on a message**: a message
on the network is one the validator *may* have received, and every rule
that reads one is a step the validator *may* take. The model does not
track delivery; when a message is acted on is the receiver's step, and the
liveness premises say when that step is owed (§7).

### 3.1.1 What the tool does not check

The positive-use property of the network relations is an **assumption of
the soundness argument**, not a property Veil enforces. If an edit
observes a message negatively (via `¬R`, `∀ R, R(…) → …`, an
`if-then-else` whose `else` branch fires on `¬R`, or an update sensitive to
`¬R`) at a row that is not the actor's own send, the SMT proofs may still
go through but the claim that "safety in this model implies safety in an
asynchronous network" silently no longer holds. Every action is therefore
checked by hand against [Locality.md](Locality.md), and the result is the
audit table of the guide ([guide/audit/Chorus.tsv](guide/audit/Chorus.tsv)),
one row per action with the rule each read and write follows. The rules
are written so that a checker can apply them by pattern matching; that
checker is planned ([TODO.md](TODO.md), "Soundness instruments").
### 3.2 Why this is sound for safety

The monotone model is a **conservative over-approximation** of
asynchronous behaviour with per-recipient delivery state `R_i ⊆ Σ`.
For any async execution `E_async` we can simulate it in the monotone
model by letting the global set be `⋃ᵢ R_i` and having validator `i`'s
actions consult only the signatures that lay in its `R_i` at the
corresponding step: the monotone model never *forces* anyone to consult
anything, every read of another's message is positive, and where the
paper's rule reads what `i` has *not* received, `i`'s own receipt steps
fire at its deliveries, so its receipt rows are exactly what it received
(`fb_sign_neg`'s `qv` is then its actual received-vote set). So

> `{ reachable states in async with per-recipient delivery }` ⊆
> `{ reachable states in monotone }`.

If safety holds in the monotone model, it holds in async. The reverse
is not true — the monotone model admits states no async run can reach —
but the extra states only enable *more* protocol activity, never less,
so they cannot mask a safety violation.

Selective-revelation attacks (a Byzantine proposer sending chunks for
`m₁` to half the validators and `m₂` to the other half) are still
modelled correctly because **chunks are point-to-point**:
`msg_chunk j i j m₁` and `msg_chunk j i' j m₂` are separate messages to
`i` and `i'`. The proposer's two signed headers are globally
visible (so `equiv_evidence j` can be witnessed), but who recorded
which chunk locally is per-validator — exactly the protocol-relevant
granularity.

### 3.3 Why GST is not needed here

This is the standard DLS-style decomposition for partially-synchronous
BFT consensus:

* **Safety** holds in pure asynchrony. It needs only (a) signature
  unforgeability, (b) quorum intersection (`2/3 + 2/3 > 1`), (c)
  per-validator local consistency (no self-equivocation). All three
  are captured in the Veil model: (a) by the honest/Byzantine action
  split, (b) by `ByzNodeSet`, (c) by the `local_entry_*`,
  `vote_unique_*`, and `local_committed_pos_*` invariants.
* **Liveness** is what requires partial synchrony / GST. Without it,
  FLP rules out deterministic asynchronous termination, so the
  protocol falls back to randomisation (the MVBA in the fallback
  path) or to eventual synchrony bounding message delay.

Chorus follows this pattern, and the paper's own agreement proof
(Proposition 1 (`prop:agreement-entries`)) is asynchronous: two commitQCs agree by
quorum intersection on commit votes; two MVBA decisions agree by the
MVBA's agreement property; and a commitQC excludes any fallback-shaped
MVBA decision because the `FBCert` every fallback meta-block carries
is a second supermajority whose honest common member with the commitQC
would have had to cast both a fast commit vote and a fallback vote —
excluded by `pathVote`. None of these arguments consults a clock, and
all are discharged in this model from the `ByzNodeSet` intersection
axioms (see §6). GST is the assumption needed for *liveness*, not
safety — see §7.

Two conditional properties take a premise that synchrony would
establish, and prove the protocol consequence asynchronously:

* **Proposal inclusion** — the paper's premise "a correct proposer
  disseminates at `s.deadline − Δ ≥ GST`" implies (in the real
  protocol) that every honest validator records the positive entry
  before the deadline. The model takes that consequence
  (`all_honest_recorded j m`) as the hypothesis and proves that no
  conflicting entry can ever be certified or committed.
* **Speculative safety** — the paper's claim "a speculative commit is
  reverted only if the proposer is the culprit" is stated relative to
  the `no_equivocation` and `no_invalid_encoding` state predicates —
  the culprit set of the paper's proof sketch
  (Section 4.5 (`subsection:chorus-proof`), closing parenthetical): equivocation, or
  committing to an invalidly encoded root.

### 3.4 What is omitted

* **Message delivery order** — any signature, once produced, is visible
  to any action that wishes to consume it. This subsumes the worst
  case of an adversarial scheduler.
* **Timeouts as such** — timing is only the four-valued `Phase` enum,
  advancing non-deterministically in order. This is enough to express
  preconditions like "fallback entries are signed at or after the
  fallback arm" without committing to a clock model.
* **The Conductor layer** — Chorus is one slot. Pipelining via the
  Conductor is out of scope *of this module*. The `participate()` /
  `abandon()` interface through which Cadence drives a slot instance is
  modelled here as two input actions, with the participation gate on every
  sending rule (the model's "Participation inputs" section); *who* invokes
  them, and when, is the glue's business. The Conductor and the glue are
  modelled separately in [Cadence/Conductor.lean](../Cadence/Conductor.lean) and
  [Cadence/Cadence.lean](../Cadence/Cadence.lean) against the module contracts of
  [Cadence/Interfaces.lean](../Cadence/Interfaces.lean) (see
  [ConductorDesign.md](ConductorDesign.md) and those files' headers).
* **`FastBlock` dissemination/adoption** (Algorithm 4 (`alg:fast-path-certification`),
  FastBlock handler) — the paper broadcasts a formed fast meta-block so
  peers can adopt `Ev(pid) ← B(pid)` without re-aggregating. In the
  monotone model a certificate exists iff its backing signatures do, so
  adoption and re-aggregation coincide: `aggregate_fastqc_*` covers
  both.
* **DA re-encode consistency check** (Algorithm 6, line 24 (`line:da-reencode`)) —
  modelled **abstractly**, by its verdict rather than its arithmetic.
  The paper decodes `f+1` chunks, re-encodes, and compares the root;
  with `merkle_root` opaque the model cannot compute this, so the
  check's verdict is the immutable predicate `well_encoded m` — sound
  because encoding validity is a property of the whole committed set
  the root binds, identical at every validator
  (Proposition 2 (`prop:recovery-consistency`)). Honest `propose` requires it (recovery
  guarantee (ii): a correct proposer encodes validly), `fb_sign_pos`
  requires it (the paper's fallback-yes caster reconstructs and
  re-encode-checks), and `fb_sign_neg`'s guard admits the
  re-encode-failure fallback-no — the culprit case of the paper's proof
  sketch (Section 4.5 (`subsection:chorus-proof`), closing parenthetical) that
  involves no equivocation, only an invalidly encoded root. The
  erasure arithmetic itself stays unmodelled: "`f+1` chunks for root
  `m`" is still taken as decodable (`chunk_quorum` reads `isDecoded` at
  the chunk-count threshold), and a Byzantine proposer can still
  deliver `f+1` mutually-inconsistent chunks — but the fallback layer
  sees the verdict the real DA would reach on them. Agreement and proposal
  inclusion do not depend on the check: agreement rests on quorum
  intersection over root-opaque certificates, and an on-time honest
  proposer's root passes the check by the encoding half of the
  `all_honest_recorded` premise.

  Modelling the verdict is load-bearing for the **speculative-finality**
  properties. If invalid encodings cannot exist in the model, those
  properties are provable under `no_equivocation` alone — a stronger claim
  than the paper makes, since the paper names an invalidly encoded root as a
  second culprit case. With `well_encoded` present they take the paper's full
  culprit set, `no_equivocation` + `no_invalid_encoding`.

## 3.5 The state, by kind

Every state item in [Cadence/Chorus.lean](../Cadence/Chorus.lean) is of one
of the kinds of [Locality.md](Locality.md) §2. The kind determines what it
**stands for** in the real protocol and which rules govern its use.

### Messages — `msg_*`, sender first

Signed messages on the network. Under the monotone idealisation of §3.1
they stay observable once sent; a validator reads them positively, and its
own sends in either polarity.

| Relation | Paper analogue |
|---|---|
| `msg_proposer_signed j m` | outer chunk-header signature `σ` on `⟨s, j, mroot⟩` (Algorithm 2 (`alg:proposer-dissemination`)). |
| `msg_chunk s i j m` | sender `s` has sent validator `i` its assigned chunk under `j`'s root `m`: the proposer's send (Algorithm 2 (`alg:proposer-dissemination`)) or a fallback signer's re-dissemination (Algorithm 5, line 12 (`line:fb-redisseminate`)). The only point-to-point message — see §3.5.1. |
| `msg_vote_pos_sig r j m`, `msg_vote_neg_sig r j` | per-proposer signed entries of the `Vote` broadcast (Algorithm 3 (`alg:voting`)). |
| `msg_vote_cast r` | `r` has broadcast its `Vote` (Algorithm 3, line 14 (`line:vote-broadcast`)). Whether a receiver accepts it is the receiver's check, `vote_valid` (§3.5.3). |
| `msg_vote_chunk r j m` | the chunk with index `r` under `j`'s root `m` that `r`'s `Vote` carries for its positive entry (Algorithm 3, line 14 (`line:vote-broadcast`)); broadcast with the vote (§3.5.3). |
| `msg_fb_pos_sig r j m`, `msg_fb_neg_sig r j` | per-proposer signed fallback entries in the `FallbackVote` broadcast (Algorithm 5 (`alg:fallback`)). |
| `msg_fallback_sig r` | the `σ_r` on `⟨fallback, s⟩` in the `FallbackVote` broadcast. |
| `msg_commit_pos_sig r j m`, `msg_commit_neg_sig r j` | per-proposer signature inside the `CommitVote` (Algorithm 4 (`alg:fast-path-certification`)). |
| `msg_commit_cast r` | `r` has broadcast its `CommitVote` (Algorithm 4, line 24 (`line:fast-commitvote`)). Only broadcast commit signatures count toward a commitQC. |
| `msg_commitqc_pos c j m`, `msg_commitqc_neg c j` | `c` has broadcast a fast commit certificate for the entry (Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)), formed from the votes it received or re-broadcast on finalizing (Algorithm 4, line 35 (`line:fast-rebroadcast-commitqc`)). |
| `msg_decrypt_share r` | the extraction share released with `r`'s `Vote`. |
| `msg_fbcommit_sig r e` | `r`'s `FallbackCommitVote` over the entry vector `e` (Algorithm 5, line 41 (`line:fb-commitvote`)). A correct voter signs its own decision's entries. |
| `msg_fbcommitqc c e` | `c` has broadcast `fbCommitQC = ⟨FallbackCommit, s, e, Σ⟩` (Algorithm 5, line 44 (`line:fb-commit-broadcast`)), formed from the votes it received or re-broadcast on finalizing (Algorithm 5, line 46 (`line:fb-commit-rebroadcast`)). |
| `msg_mvba_cert i c` | `i` has broadcast the MVBA's commit certificate `c`: the one its decision outputs, or one it finalized on (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"). |

**Positional chunks.** A chunk is identified by `(assignee, proposer,
root)`: `msg_chunk s i j m` carries the fragment at validator `i`'s own
position under `j`'s root `m`, and the decode threshold `chunk_quorum`
counts distinct assignees. That is the target's positional reading:
Algorithm 6 (`alg:da`) stores validated fragments as pairs `(r, d_r)`, checks each leaf at
its index, and decodes from `f+1` distinct indices, and the re-encode check
(Algorithm 6, line 24 (`line:da-reencode`)) compares positional leaf hashes.
`Primitives.ErasureCoding` states the codec at the same reading
([PaperAlignment.md](PaperAlignment.md) §5.2).

### Derived certificates — ghost relations

Transferable certificates are definitional predicates over the messages:
`vote_quorum_pos/neg` (FastQC certificates), `fb_quorum_pos/neg`
(FallbackQCs), `equiv_evidence` (EquivCert — the proposer's signatures
on two distinct roots), `fbcert` (FBCert), `commitqc_pos/neg`
(commitQC validity), `fbcommitqc e` (fbCommitQC validity — `2f+1` fallback
commit votes over `e`, Algorithm 5, line 43 (`line:fb-formcommitqc`)),
`chunk_received i j m` (a chunk addressed to `i` from any sender),
`chunk_quorum` (`isDecoded`: `f+1` validators hold their chunk),
`slot_key_released` (f+1 extraction shares),
`complete_fast_metablock` / `mvba_invoked` (MVBA proposal triggers;
`mvba_invoked`, which ranges over every correct validator, is read by no
action), `mvba_complete` (some validator has transported its decision; read
by no action), plus the hypothesis predicates `no_equivocation`,
`no_invalid_encoding` and `all_honest_recorded`. A ghost is of the kind it
unfolds to: a guard that reads one is a positive read of the messages it
aggregates — a validator that has received the signatures can check the
certificate — or of the validator's own rows (`complete_fast_metablock i`).

The certificates a validator *sends* are messages of their own, formed in
the sending step from the signatures the sender received:
`broadcast_commitqc_*` (`msg_commitqc_*`), `broadcast_fbcommitqc`
(`msg_fbcommitqc`), and `send_mvba_cert` (`msg_mvba_cert`). A receiver
finalizes on the certificate it received, which carries its entries (§3.1).
Verification-wise the materialisation matters too: it keeps the deep quorum
reasoning at the forming action (where the quorum is an explicit witness)
instead of every commit-side VC re-deriving it from an `∃`-quorum ghost.

### Local state — `local_*`, owner first

Each row belongs to one validator; only that validator's actions read or
write it.

| Relation | Paper analogue |
|---|---|
| `local_entry_pos i j m`, `local_entry_neg i j` | validator `i`'s per-proposer `Entry(pid)` (Algorithm 3 (`alg:voting`)). |
| `local_voted i` | `i` has executed the deadline vote handler. |
| `local_path i : PathChoice` | `i`'s `pathVote ∈ {none, fast, fallback}`. |
| `local_fastqc_pos i j m`, `local_fastqc_neg i j` | `i` has aggregated `Ev(j)` as a FastQC (Algorithm 4, line 18 (`line:fast-formqc`)). Kept per-validator because an honest commit signature is justified by *the signer's own* FastQC observation. |
| `local_vote_rcv_pos i r j m`, `local_vote_rcv_neg i r j` | `i` has received `r`'s vote, whose entry for `j` is positive on `m`, resp. negative: the received votes the fallback rule ranges over (Algorithm 5, line 8 (`line:fb-cast-entry`)). One entry per sender and proposer, the first received. |
| `local_committed i`, `local_committed_pos i j m`, `local_committed_neg i j` | `i`'s finalization decision. |
| `participating i`, `abandoned i` | `i` has invoked the slot-consensus inputs `participate()` / `abandon()` (Module 1 (`mod:slotconsensus`)); written only by the input actions of the same name. Named as the contract's observables rather than `local_*`. Every sending rule reads them at its own sender (the participation gate). |
| `local_commit_entry i j`, `local_fb_entry i j` | `i` has signed its commit-vote entry, resp. its fallback entry, for proposer `j` (the per-proposer steps of Algorithm 4, line 24 (`line:fast-commitvote`) and Algorithm 5, line 8 (`line:fb-cast-entry`)). |
| `local_commitqc_sent c j`, `local_fbcommitqc_sent c` | collector `c` has broadcast its commit certificate's entry for `j` (Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)), resp. its fallback commit certificate (Algorithm 5, line 44 (`line:fb-commit-broadcast`)). |
| `local_mvba_recorded i j` | `i` has handled entry `j` of its MVBA decision (Algorithm 5, line 37 (`line:fb-mvba-decide`)). |
| `local_mvba_cert_sent i` | `i` has broadcast the commit certificate its MVBA decision output. |
| `local_mvba_qc_accepted i` | `i` has handed a received MVBA commit certificate to its MVBA (`accept_mvba_commitqc`). |
| `local_avail_marked i v` | `i` has reported `AvailReady_i(v)` to its MVBA (`mvba_avail_ready`). |
| `local_mvba_complete i` | `i` has handled every proposer's entry of its decision (`mvba_terminate`, the shadow of Algorithm 5, line 37 (`line:fb-mvba-decide`) delivering `B′` at once). Its fallback commit vote waits for it. |
| `local_fbcommit_voted i` | `i` has cast its fallback commit vote (Algorithm 5, line 41 (`line:fb-commitvote`)). |

Cross-validator agreement that a "global QC" idiom would give
definitionally is a **theorem** here — e.g.
`local_fastqc_pos_cross_unique`, discharged from
`local_fastqc_pos_backed` and quorum intersection.

### Auxiliary records — `aux_*`

History for the proofs: written by actions, read by none, so they change
no run ([Locality.md](Locality.md) §2).

| Relation | What it records |
|---|---|
| `aux_mvba_decided_pos j m`, `aux_mvba_decided_neg j` | the entries the MVBA certified: written by a correct validator's decision handlers `on_mvba_decide_*` and by finalization on an MVBA commit certificate (`commit_assign_*_mvba`). The invariants state agreement between the commit routes over them; their uniqueness is *proven* from the contract's agreement and certificate fields (§6.4). |
| `aux_fb_neg_qv i j qv` | the received-vote quorum against which `i` cast its negative fallback entry for `j`; it lets the speculative-safety invariants refer to the quorum after the fact without a quantifier alternation that breaks the SMT matcher. |

### Global time and the MVBA

| State | Paper analogue |
|---|---|
| `phase : Phase` | the slot's notional time landmark, moved by the environment (`advance_to_*`). One global value: per-validator clock skew is absorbed into the gap between `advance_*` actions. |
| `mvba_st : mstate` | the abstract state of the slot's MVBA instance (Module 3 (`mod:mvba`)), held as the glue holds `sc_state s`: an opaque sort, used only through the contract `mvba : MVBASafety …` (§4) — its operations at the acting validator's index, or a check of a certificate it holds ([Locality.md](Locality.md) §5) — advanced by the oracle step `mvba_step` and the driven inputs `mvba_propose`, `accept_mvba_commitqc`, `mvba_avail_ready` and `abandon`. |

### 3.5.1 Why chunks are the only point-to-point message

In the paper, every other network message is broadcast on the gossip
overlay. Once they exist, every validator eventually sees them, and the
monotone-network idealisation collapses "exists somewhere" with
"globally visible". Chunks are different: the proposer sends *one chunk
per validator*, point-to-point, and the per-validator distinction
directly affects the protocol — `local_entry_pos i j m` is producible
only when `i` received its assigned chunk before the deadline. So
`msg_chunk` names its recipient, and a correct validator reads only the
chunks addressed to itself ([Locality.md](Locality.md) R2).

### 3.5.2 Chunk dissemination and data availability

**Who sends a chunk, and when.** The paper sends chunks in two rules, and
in both the send is part of the rule's own step:

| paper | model |
|---|---|
| the proposer: upon `propose`, … for each validator `p_r`: send `p_r` its chunk (Algorithm 2 (`alg:proposer-dissemination`)) | `propose j m` writes `msg_chunk j I j m` for every validator `I`, beside its signature `msg_proposer_signed j m` (gated on participation). |
| the positive fallback signer: re-encode the proposal; send each validator its assigned chunk for `ρ` (Algorithm 5, line 12 (`line:fb-redisseminate`)) | `fb_sign_pos i j m q` writes `msg_chunk i I j m` for every `I`, in the gated signing step. |

When a chunk reaches its recipient is the recipient's step: `record_chunk`
before the deadline, and the waits of `cast_fb_commit` and
`mvba_avail_ready` after it. The timing premise owes each of them within
`Δ` of a correct sender's send after GST (§7). A Byzantine proposer sends
any chunk to anyone (`byz_send_chunk`, unconstrained recipient and root),
and any Byzantine validator sends any chunk of any root under its own name
at any time (`byz_redisseminate_chunk`, guarded by its actor marker only;
the receiver checks the proposer's signature); both unfair.

The decoding threshold (`isDecoded`) is the ghost `chunk_quorum j m`:
`f+1` validators broadcast their chunk under `m` with their votes
(`msg_vote_chunk`), so every validator that receives those votes holds
`f+1` distinct chunks. A valid positive vote entry carries the signer's
chunk, and a receiver counts only valid votes (§3.5.3), so a validator
that holds `f+1` valid positive votes holds `f+1` chunks: the fallback
rules' "decodable data" condition is met by the votes they count, and a
correct positive fallback entry is backed by `f+1` chunk-carrying votes
(`msg_fb_pos_sig_backed`). A FastQC's `2f+1` signers include `f+1`
correct ones, each carrying its chunk (`vote_pos_sig_chunk`), so its root
is decodable too (`vote_pos_quorum_implies_decodable`) — the paper's own
argument (Proposition 4 (`prop:chorus-totality`), the proof's FastQC case).

The model-level DA safety theorem is
`local_committed_pos_implies_decodable`: every honest positive commit
has `f+1` validators that broadcast their chunk for the committed root —
the counterpart of "`recoverProposals` does not block" (Algorithm 6,
line 12 (`line:da-wait`)).

### 3.5.3 Vote validity at the receivers

**The paper's receiver.** Algorithm 4 (`alg:fast-path-certification`), the
vote handler, upon receiving `⟨Vote, s, SignedEntries, Chunks,
DecryptShare⟩` from `p_r`:

> for each proposer `p_j ∈ s.proposers`: if `SignedEntries` has no entry
> for `p_j`, or its signature fails verification under `p_r`: return.
> Let `⟨⟨s, j, ρ⟩, σ⟩` be the signed entry for `p_j`. If `ρ ≠ ⊥`, and
> either no `m ∈ Chunks` has (chunk index `r` and matching `ρ`), or
> `tryIngestChunk(m) = false`: return.
> If `tryIngestShare(r, DecryptShare) = false`: return.
> For each signed entry `pv = ⟨E, σ⟩ ∈ SignedEntries` with
> `E = ⟨s, j, ρ⟩`: `Votes(j, ρ) ← Votes(j, ρ) ∪ {pv}`.

`tryIngestChunk` (Algorithm 6 (`alg:da`)) rejects a chunk unless `j` is a
proposer of the slot, the proposer's signature on `⟨Root, s, j, ρ⟩`
verifies, and the Merkle proof verifies index `r` against `ρ`;
`tryIngestShare` verifies the decryption share. The handler is atomic: a
vote counts only if it is complete, every positive entry carries a valid
chunk with the sender's index, and the share verifies. A correct vote
carries exactly that (Algorithm 3, line 14 (`line:vote-broadcast`)).

**In the model** the check is a ghost over the sender's broadcast rows,
which a correct receiver reads positively ([Locality.md](Locality.md) R2):

```
ghost relation vote_entry_valid (r j : node) :=
  (∃ m, msg_vote_pos_sig r j m ∧ msg_vote_chunk r j m ∧ msg_proposer_signed j m)
  ∨ msg_vote_neg_sig r j
ghost relation vote_valid (r : node) :=
  msg_vote_cast r ∧ msg_decrypt_share r ∧ ∀ j, is_proposer j → vote_entry_valid r j
```

The model keeps a vote's entries as per-entry rows, so an equivocating
sender's rows may support several valid votes; a receiver that takes `r`'s
entry for `j` from one and its entry for `j′` from another holds entries
that form one valid vote, because each entry is checked on its own. The
correct steps that count *votes* read it:

| Action | Guard | The paper's rule |
|---|---|---|
| `receive_vote_pos i r j m` | `vote_valid r`, `msg_vote_pos_sig r j m`, `msg_vote_chunk r j m`, `msg_proposer_signed j m` | the vote handler: the whole vote is checked, then its entry for `j` counts |
| `receive_vote_neg i r j` | `vote_valid r`, `msg_vote_neg_sig r j` | the same |
| `fb_sign_pos i j m q` | `2f+1` senders with `vote_valid`; `f+1` senders with `msg_vote_pos_sig r j m ∧ msg_vote_chunk r j m ∧ vote_valid r`; `msg_proposer_signed j m` | "at least `2f+1` valid Vote messages have been received" (Algorithm 5, line 7 (`line:fb-pathvote-guard`)); "collected `f+1` valid positive votes for `(p_j, ρ)`" (Algorithm 5, line 8 (`line:fb-cast-entry`)) |
| `fb_sign_neg i j qv` | `i`'s own receipts, which come only from valid votes | "among the votes received" |

The Byzantine sends carry no receiver check: `byz_cast_vote` casts any
vote, complete or not, `byz_sign_vote_pos` signs any positive entry, and
`byz_carry_vote_chunk` attaches any chunk. Completeness is a receiver-side
fact (`vote_rcv_pos_backed`, `vote_rcv_neg_backed`: a correct receipt
comes from a valid vote) and, for correct senders, a sender-side one
(`vote_cast_valid`: a correct cast vote is valid), which is what the
liveness proofs use.

**A FastQC is checked by its signatures.** The paper's FastQC is a
transferable certificate, "an aggregate of `2f+1` matching signed entries"
(Algorithm 4, line 18 (`line:fast-formqc`)), and a correct validator also
*adopts* one: from any valid fast meta-block (Algorithm 4
(`alg:fast-path-certification`), the `FastBlock` handler) and from a
fallback vote (Algorithm 5, line 20 (`line:fb-harvest`)). A FastQC carries
no chunks and no votes, so its only check is its signatures, and the
adversary, which reads every signed entry on the network, can assemble
one from any `2f+1` and send it in a `FastBlock`. `aggregate_fastqc_*`
models formation and adoption together, so its guard is the adoption
check, `2f+1` signatures; reading `vote_valid` there would remove runs the
paper allows a correct validator. The decodability of a FastQC's root does
not depend on it (§3.5.2).

**Why the carried chunk is its own relation.** `msg_chunk s i j m` is the
point-to-point message carrying *`i`'s* chunk, sent to `i`. A vote's chunk
has the *sender's* index `r` and is broadcast with the vote, so
`msg_chunk r I j m` would carry the wrong index, and `msg_chunk r r j m`
("`r` holds its chunk") is a point-to-point row at recipient `r`, which a
correct receiver `i ≠ r` may not read (R2). `msg_vote_chunk r j m` is a
broadcast row at sender `r`: every correct receiver reads it positively
(R2), and a Byzantine sender writes it only under its own name (B1).
`byz_carry_vote_chunk` needs no guard: the model does not track chunk
contents, and a chunk passes the Merkle check iff it is the real chunk of
`ρ` at its index, which its holder can show. Nothing limits what the
adversary reads ([Locality.md](Locality.md) §4.2), so it holds every chunk
any validator was sent, and for its own proposers' roots every chunk it
chose to make — the reading `byz_redisseminate_chunk` has too. The part of
`tryIngestChunk` the model can state, the proposer's signature on the
root, is the receiver's check (`msg_proposer_signed j m` in
`vote_entry_valid`).

## 4. Cryptographic primitives

[Cadence/Primitives.lean](../Cadence/Primitives.lean) declares type classes that state
the *signatures and properties* of each cryptographic primitive Chorus
depends on (hash, signature, threshold IBE, erasure coding, Merkle
tree, MVBA). The Veil module does **not** instantiate them directly;
instead it models their *observable effects* via the first-order
relations described above. The classes serve as documentation and as
the proof obligation a concrete implementation must discharge.

### Why this split?

Veil's verification works at first-order logic with quorums. Several
primitives (hash injectivity, Merkle binding, EUF-CMA unforgeability)
are conveniently expressed as Lean axioms but live *outside* the Veil
specification's vocabulary. Keeping the Veil module purely relational:

1. lets the concrete crypto vary without changing the safety proofs;
2. cleanly separates computational from symbolic guarantees (hashes
   are computationally collision-resistant; the Veil layer assumes
   exact injectivity, sound under a bounded adversary);
3. confines quantifier alternation — the Veil layer stays as close to
   EPR as practical, with the existential-quorum invariants the
   protocol forces (see §6).

**Hiding** is split the same way. The cryptographic layer — TIBE
unpredictability and the random-oracle simulation argument
(Appendix C.2 (`appendix:encryption`)) — is axiomatised as
`ThresholdIBE.decrypt_secret`: decryption succeeds only with a
threshold of correct shares. The protocol layer is proven in the model:
`safety [hiding_until_deadline]` shows the share threshold cannot be
reached while the slot is `pre_deadline`, because at most `f` shares
are Byzantine and honest validators release shares only with their
deadline vote.

### The MVBA as a class constraint

Chorus consumes the MVBA (Module 3 (`mod:mvba`)) exactly as the glue
consumes the slot consensus and the Conductor the ACS
([CompositionContracts.md](CompositionContracts.md) §3): the
state-level contract `MVBASafety` of
[Cadence/Interfaces.lean](../Cadence/Interfaces.lean) is a **class
constraint** — `instantiate mvba : MVBASafety node mvalue mmsg mstate (fun
i => nset.is_byz i = true)` — over an abstract state `mvba_st : mstate` the
module holds, and Veil hands every axiom of the class to the solver, so
agreement, integrity, external validity, the monotonicity of `decided` and
the frames are *used* in the verification conditions and restated nowhere.
The instance is the verified leader-based model
[Cadence/Mvba.lean](../Cadence/Mvba.lean) through `Mvba.mvbaSafety`
([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)), plugged in
by [Cadence/System.lean](../Cadence/System.lean); both are stated against
the same `nset.is_byz`, so no fault-model transport is needed between them.

**The value is the meta-block representation.** Module 3 (`mod:mvba`) decides a
meta-block, and agreement is over its entries, so two correct validators
may decide representations whose certificates differ. The class is
instantiated at `value := MetaBlock node merkle_root` (entries plus each
positive entry's certificate kind) and `entryvec := node → Option
merkle_root` ([PaperAlignment.md](PaperAlignment.md) §8.1). A Veil module needs first-order
sorts, so `mvalue` and `mentries` are opaque, joined by the contract's
`mvba.entries`; an entry vector is read through two immutable projections
`mval_pos e j m` / `mval_neg e j` and a positive entry's kind through
`mval_fb v j`, with two `assumption`s — functional in the root, and
exclusive — that [System.lean](../Cadence/System.lean) discharges at `e j = some m` /
`e j = none ∧ is_proposer j` (the one genuine hypothesis among Chorus's assumptions is then
`[mvba_init]`, that the abstract state Chorus starts from is an initial
state of the instance; [System.lean](../Cadence/System.lean), `chorusTheory_assumptions`).

**The actions.** `mvba_step` is the oracle step — any internal transition
`MVBASafety.step` allows, including the ones that output `decide(B)` at
correct validators. `mvba_propose` drives the contract's `propose` input,
the paper's `MVBA[s].propose(B_i)`, under the proposer's own trigger (the
two triggers below) and with the caller's `Valid B_i` obligation as
guards (every entry a proposer's and certificate-backed, every proposer
covered); safety needs nothing from it, liveness needs it for
Termination's "all correct validators propose" premise (§7). `abandon`
is forwarded by Chorus's own `abandon` input. `mvba_avail_ready i v`
drives the contract's availability input `markAvail`: Chorus reports
`AvailReady_i(v)` once `i` has received its assigned chunk under every
positive `FallbackQC` entry of `v`, the supplement's definition
(Supplement, Section 1.2 (`subsec:mvba-protocol`), "Commit availability
condition"), and `avail_ready_chunks` proves that meaning. The
**decision handlers** `on_mvba_decide_pos i j m v` / `on_mvba_decide_neg
i j v` handle a correct validator's decision (`mvba.decided mvba_st i v`)
entry by entry, each marking its own row `local_mvba_recorded i j` and
recording the entry in the auxiliary `aux_mvba_decided_*` — per entry
rather than in one step, so every update stays a `:= true` and the
downstream invariants keep their form. `mvba_terminate i v` records that
`i` has handled every proposer's entry of its own decision
(`local_mvba_complete i`), reading only its own rows: the model shadow of
Algorithm 5, line 37 (`line:fb-mvba-decide`) delivering `B'` at once, and the
gate of `i`'s fallback commit vote. None of them has a phase gate, and none requires
that the MVBA was invoked: the paper's handler runs "upon
`MVBA[s].decide(B′)`", with no further condition, and a
decision can come before the MVBA arm (the case-2 proposal needs only the
fallback votes).

**The `CommitQC` route** (Supplement, Section 1.2 (`subsec:mvba-protocol`),
"Decision output and handoff"): "A correct validator that receives a
valid such certificate re-broadcasts it and finalizes the certified
outcome, recovering a matching meta-block or the underlying proposals as
required by the ordinary commitment-proof recovery path." The certificate
travels as a message: a correct validator sends the certificate its own
decision outputs (`send_mvba_cert i c`, guarded by the contract's output
`mvba.decidedCert` at `i`; `msg_mvba_cert i c`). A receiver hands
it to its own MVBA (`accept_mvba_commitqc`), and finalizes on it
(`commit_assign_pos_mvba i j m s c v` / `commit_assign_neg_mvba`): the
received certificate `c`, checked with the contract's `mvba.certifies`
against a representation `v` of its entries (the recovered meta-block),
the certificates `v` names checked against the network (the bridge
below), and the certificate re-broadcast under the finalizer's own name.
The route's agreement with the fast path is `commitqc_pos_mvba_consistent`
and its two exclusion siblings, by the main body's fast-path argument over
the bridge evidence. Its agreement with the `fbCommitQC` route and with
itself is the contract's `certified_unique` and `certified_decided`,
through the ties.

**The one stated bridge.** Before acting on an entry, each handler
verifies the entry's certificate against the network: `vote_quorum_pos j
m ∨ (fb_quorum_pos j m ∧ fbcert)` for a positive entry, `vote_quorum_neg
j ∨ ((fb_quorum_neg j ∨ equiv_evidence j) ∧ fbcert)` for a negative one —
a FastQC-shaped entry needs a `2f+1` vote quorum; a fallback-shaped entry
(FallbackQC or EquivCert) additionally `FBCert`, because only fallback
meta-blocks may carry such entries and every valid fallback meta-block
includes `FBCert` (Appendix C.3 (`subsection:fallback_path`)). This is the interpretation
of the class's `Valid` in Chorus's vocabulary, and it is a **bridge, not a
restatement** ([MvbaPlan.md](MvbaPlan.md) §1.1): `Valid` is a class parameter fixed
before the module's state exists, so it cannot mention Chorus's network
relations, while the paper's `Valid B` checks the certificates the
meta-block *carries* — publicly verifiable objects every receiver can
re-check. It is sound in both directions that matter: it
removes no real behaviour (a correct MVBA's decision passes the check,
by `external_validity` and public verifiability), and if the MVBA were
wrong the handler would simply not fire — safety-conservative.
`mvba_decided_pos_backed` / `mvba_decided_neg_backed` persist the
evidence a record carried. The evidence conditions are deliberately
certificate-checkable network predicates, *not* conditions on honest
validators' internal state: the MVBA can only verify what a proposal
carries, so a gate referring to honest validators' aggregated FastQCs would
not be implementable. None is needed — with commitQC-based finalization the
paper's own asynchronous agreement argument goes through (§6). The bridge is
stated in five places and nowhere else: the two decision handlers and the
two finalization rules on an MVBA certificate (`commit_assign_*_mvba`) in
[Cadence/Chorus.lean](../Cadence/Chorus.lean), and — as the same
disjunction — the validity guards of `mvba_propose`, where it is the
caller's obligation rather than the receiver's check. At the route the
checked representation is the recovered one, and the same soundness
argument applies: `Recover(e)` returns a valid representation
(`certified_valid`), and a valid one passes the check.

**What the class buys.** Agreement of the auxiliary records —
`mvba_decided_pos_unique`, `mvba_decided_pos_neg_excl` — is *proven* from the
class's `agreement` at the reachable abstract state (`mvba_reachable`),
through two **tie invariants** (`mvba_decided_pos_tied`,
`mvba_decided_neg_tied`: every record is the projection of some correct
validator's decision or of a valid certificate) and the two `mval_*`
assumptions, with `certified_decided` and `certified_unique` for the
certificate-sourced records and `certified_mono` keeping the ties
inductive. This is how
`Mvba.mvbaSafety` enters Chorus's trust base: the decision handlers assert no
agreement property of their own. [spikes/09_mvba_consumer_ok.lean](../spikes/09_mvba_consumer_ok.lean) and
[10_mvba_consumer_no_tie.lean](../spikes/10_mvba_consumer_no_tie.lean) are the shape experiment and its negative
control; without the ties, uniqueness fails at exactly the handlers.

**Two invocation triggers.** The paper invokes MVBA under two triggers
(Algorithm 5 (`alg:fallback`)): the fallback trigger — `|M_i| ≥ 2f+1` fallback votes,
whose monotone-network shadow is `fbcert` — and the case-(a) trigger — a
complete fast meta-block held at the MVBA arm. Both are modelled:
`mvba_propose` requires the proposer's own trigger (`fbcert` from the
fallback arm on, or its own `complete_fast_metablock` at the MVBA arm),
and the decision handlers and `mvba_terminate` fire on the acting
validator's decision alone. The paper's `mvbaInvoked` is the proposer's own
flag, guarding its proposal and the forwarding of `abandon()` (Algorithm 5,
line 48 (`line:fb-abandon`)); the decision handler does not read it, and
the contract (Module 3 (`mod:mvba`)) does not order a decision after a
proposal. The derived `mvba_invoked = fbcert ∨ (∃ honest I,
complete_fast_metablock I)` is the run-level statement that one of the
triggers holds, used by the progress dichotomy and read by no action. The
case-(a) trigger is load-bearing for liveness in the *mixed* regime where
between 1 and 2f honest validators took the fast path — there neither a
commitQC nor an FBCert is guaranteed, and termination flows through MVBA
proposals of fast meta-blocks (see §7).

## 5. Byzantine adversary

### Threat model

The adversary controls `B ⊆ Π` with `|B| ≤ f` (captured by
`ByzNodeSet.is_byz` and the quorum axioms). Within that bound it is
fully Byzantine: it may sign any *network-valid* message attributed to
a Byzantine signer, equivocate (produce two distinct signed chunk
headers for the same proposer), send chunks of distinct roots to disjoint
subsets of validators (`byz_send_chunk`), and cast inconsistent votes /
fallback signatures / commit votes, sending different votes to different
validators. Cryptographic unforgeability prevents it from signing as a
correct validator: a Byzantine action writes messages only under its own
name. A correct validator's local state and the phase are updated only by
their own actions ([Locality.md](Locality.md) §4).

**Receivers check what they accept.** A correct receiver counts a vote
only if it passes the paper's vote handler (`vote_valid`, §3.5.3), so a
Byzantine vote may be incomplete, carry no chunk, or carry any chunk
(`byz_cast_vote`, `byz_sign_vote_pos`, `byz_carry_vote_chunk`, each guarded
by its actor marker only). The one Byzantine guard that reads a message is
unforgeability ([Locality.md](Locality.md) §4.2, B2): `byz_sign_fb_pos`
requires `msg_proposer_signed j m`, because a positive fallback entry
carries the proposer signature `σ_p`.

**The adversary's share of the anonymous capabilities.** Assembling a
commit certificate from `2f+1` broadcast commit votes, and re-disseminating a
chunk once `f+1` chunks are on the network, are capabilities any holder of
the data has. For a correct sender the first is the rule
`broadcast_commitqc_*`, gated on participation and fired once; the second
is part of the fallback-entry rule `fb_sign_pos` (Algorithm 5, line 12
(`line:fb-redisseminate`)). In Byzantine hands they are
`byz_broadcast_commitqc_*`, with the certificate's signatures as its only
check ([Locality.md](Locality.md) §4.2, B2), and `byz_redisseminate_chunk`,
with none: no gate, no record, and no fairness ((F-byz)). Keeping them out
of the correct validators' actions keeps every fair action fired-once
([Bounds.md](Bounds.md) §6.4.7) without constraining the adversary.

### Per-relation actions, not a monolithic transition

The adversary is a family of per-relation actions — one per
adversarial capability — rather than a single `transition byz_step`
with a per-relation "pin honest"/"monotone Byzantine" body. That is not
a stylistic choice: at ~30 relations the monolithic form's elaboration
exceeds Lean's heartbeat budget. Each action requires `is_byz` and
assigns one tuple; Veil's frame condition covers the rest. The two
forms are semantically equivalent (any combined change decomposes into
a sequence), except that Byzantine validators' own local state only
grows monotonically — unobservable by honest invariants.

### Quorum axioms

Veil's `ByzNodeSet` class provides the first two facts below; the other
three are Cadence's own class `Cadence.ByzNodeSetCounting`
([Cadence/QuorumCounting.lean](../Cadence/QuorumCounting.lean)), which
Chorus consumes with `instantiate cnt`, so its fields are solver
hypotheses exactly like `ByzNodeSet`'s. Both are proven for the concrete
`byzNodeSetFin` (`n = 3f+1`) and `byzNodeSetFinGen` (`n ≥ 3f+1`) families,
the counting class in [Cadence/ByzQuorum.lean](../Cadence/ByzQuorum.lean):

* `supermajorities_intersect_in_honest` — two supermajorities share an
  honest member (`2(2f+1) − (3f+1) = f+1 > f`).
* `greater_than_third_one_honest` — an `f+1`-set contains an honest
  member.
* `honest_third_in_supermajority` — a supermajority
  contains an *all-honest `f+1`-subset* (`2f+1 − f = f+1`). Used where
  an honest sub-quorum is needed (e.g. pinning fallback entries under
  the proposal-inclusion premise).
* `supermajority_meets_third` — a supermajority and an
  `f+1`-set share a (possibly Byzantine) member
  (`(2f+1) + (f+1) − (3f+1) = 1`). Used by the speculative-safety
  argument, whose per-member consistency comes from `no_equivocation`
  rather than honesty.
* `supermajorities_share_third` — two
  supermajorities share an `f+1`-subset. Used to intersect a
  fallback signer's witnessed vote quorum with a FastQC's backing.

Note the *honest* variant of `supermajority_meets_third` — "a supermajority and an
`f+1`-set share an honest member" — is false in general (the single
guaranteed intersection element can be Byzantine); the speculative
invariants work around it via `no_equivocation`.

## 6. Invariants

Grouped by purpose. See [Cadence/Chorus.lean](../Cadence/Chorus.lean) for the statements; this is a map.

### 6.1 Safety properties

| Property | Paper analogue |
|---|---|
| `agreement_pos`, `agreement_pos_neg` | Agreement (Lemma 9 (`lemma:chorus-agreement`)), at the granularity of per-proposer committed entries. |
| `integrity_pos`, `integrity_pos_neg` | per-validator commit integrity. |
| `hiding_until_deadline` | Hiding (Lemma 7 (`lemma:chorus-hiding`)), protocol layer: the slot key is not reconstructible pre-deadline. |
| `proposal_inclusion`, `proposal_inclusion_no_neg` | Proposal inclusion (Lemma 10 (`lemma:chorus-proposal-inclusion`)), relative to the premise `all_honest_recorded`. |
| `speculative_agreement_pos`, `speculative_agreement_pos_neg` | the speculative-finality claim (Section 4.2 (`subsection:fast-path-overview`)), relative to `no_equivocation` + `no_invalid_encoding` — the paper's full "proposer is the culprit" set (Section 4.5 (`subsection:chorus-proof`)). |

Slot safety (Lemma 8 (`lemma:chorus-slot-safety`)) is trivial in the single-slot
model; termination is §7.

**Verification note.** Most obligations discharge automatically; a few
VCs — those needing one or two explicit `ByzNodeSet` counting-axiom
instantiations against witnessed quorums, at actions with bulk or
quorum-completing updates — are discharged by manual `#prove_vc … by
<tactic>` cells in their actions' proof files
(`Cadence/Chorus/Proofs/<Action>.lean`), consumed by `#prove_action` after
a statement check against the model's VC registry.

**How agreement is proven (the paper's Proposition 1 (`prop:agreement-entries`)).**
`local_committed_pos_backed` reduces every honest commit to a broadcast
commitQC or a certified entry in `aux_mvba_decided_pos` — a commit on an
`fbCommitQC` included, whose entries are certified (`fbcommitqc_entries`).
Case commitQC–commitQC: `supermajorities_intersect_in_honest` +
`commit_pos_sig_unique`. Case MVBA–MVBA: `mvba_decided_pos_unique`, itself
proven from the MVBA
contract's `agreement` at the reachable abstract state (§6.4). Case commitQC–MVBA
(`commitqc_pos_mvba_consistent` and the two exclusion variants): by
`mvba_decided_pos_backed`, the decision carried either a vote
supermajority — which intersects the commitQC's honest member's own
FastQC backing in an honest double-voter (`vote_unique_pos`) — or a
fallback certificate together with `fbcert` — which intersects the
commitQC in an honest validator with both `msg_commit_cast` and
`msg_fallback_sig`, contradicting the `pathVote` exclusion
(`commit_cast_fallback_sig_excl`). Pure quorum reasoning, valid under
full asynchrony.

*Correspondence with the paper's argument.* The paper's
Proposition 1 (`prop:agreement-entries`) argues the fallback cases through the *commit
round*: two `fbCommitQC`s intersect in an honest commit-voter, who
commit-votes once, for the entries of its single MVBA decision (MVBA
Integrity); an `fbCommitQC` and a `commitQC` intersect as in case 3
above. The model reaches the same conclusion one layer lower: an
`fbCommitQC` over `e` has a correct voter, who voted for the entries of its
own decision (`fbcommit_sig_entries`), so every entry of `e` is a certified
entry (`fbcommitqc_entries`), and decision agreement comes from the MVBA
contract — so the model's proof does not need the fbCommitQC–fbCommitQC
intersection at all. The commit round's own certificate discipline is
nonetheless modelled and checked (`fbcommit_sig_backed`,
`fbcommitqc_implies_mvba_complete`, §6.7): an `fbCommitQC` cannot exist
before the decision vector it certifies.

### 6.2 Local sanity

`proposer_unique_root`, `local_entry_pos_signed`, `local_entry_unique`,
`local_entry_pos_neg_excl`, `local_entry_pos_chunk`, the
signed-implies-voted family (`vote_sig_pos_implies_voted`,
`vote_sig_neg_implies_voted`, `local_entry_neg_implies_voted`,
`vote_cast_implies_voted`, `voted_implies_cast`, `share_implies_voted`),
`vote_pos_from_local`, `vote_neg_from_local`, `vote_unique_pos`,
`vote_unique_pos_neg`, `voted_entry_pos_signed`, `vote_cast_valid`,
`vote_pos_sig_chunk`.

Phase timestamps: `voted_post_deadline`, `fastqc_post_deadline`,
`fb_sig_phase`, `mvba_decided_phase` — every protocol artefact postdates
the landmark that produces it (a record, the deadline: its certificate's
correct signers signed after it); used by `hiding_until_deadline` and by the
premise-stability arguments of the conditional properties.

### 6.3 Certificate backing and intersection consequences

`local_fastqc_pos_backed`, `local_fastqc_neg_backed`,
`local_fastqc_pos_self_unique`, `local_fastqc_pos_cross_unique`,
`local_fastqc_pos_neg_excl`, `msg_fb_pos_sig_backed`,
`commit_pos_sig_from_local_fastqc`, `commit_neg_sig_from_local_fastqc`,
`commit_pos_sig_unique`, `commit_pos_sig_neg_excl`; the path exclusion
family (`commit_cast_path_fast`, `fallback_sig_path_fallback`,
`commit_cast_fallback_sig_excl`); the commitQC-level family over the
broadcast certificates (`msg_commitqc_pos/neg_backed`,
`msg_commitqc_pos/neg_votes`, `commitqc_pos_unique`,
`commitqc_pos_neg_excl`, `commitqc_pos_mvba_consistent`,
`commitqc_pos_mvba_neg_excl`, `commitqc_neg_mvba_pos_excl`).

### 6.4 MVBA correctness, from the class

`mvba_reachable` (the abstract state is reachable — `[mvba_init]` and the
contract's closure axioms along `mvba_step`/`mvba_propose`),
`mvba_decided_pos_tied`, `mvba_decided_neg_tied` (every auxiliary record
is the projection, through `mval_pos`/`mval_neg`, of some correct
validator's decision on the abstract state or of a valid commit
certificate — inductive under the oracle step because the contract's
`decided_mono` and `certified_mono` keep both), and from these,
through `mvba.agreement` at the reachable state plus the two `mval_*`
assumptions, `mvba_decided_pos_unique` and `mvba_decided_pos_neg_excl` —
the contract's agreement *used*, not restated, and kept as invariants
because the downstream cells e-match on them. Then
`mvba_decided_pos_backed`, `mvba_decided_neg_backed`,
`mvba_decided_is_proposer`, `mvba_decided_phase`,
`mvba_complete_per_proposer`, `mvba_decided_pos_proposer_signed`. The
`*_backed` invariants persist the bridge evidence a record carried; they
are what keeps the commitQC-consistency family inductive when commit
votes are cast *after* a decision. `mvba_decided_pos_proposer_signed`
materialises one consequence (a decided-positive root is proposer-signed)
so the commit-round VCs need not re-derive it. A validator's own rows
link its decision to the records: `local_mvba_recorded_backed`,
`mvba_recorded_entries` (an entry it handled is recorded, for every
representation it decided) and `mvba_complete_recorded`.

### 6.5 Commit backing and data availability

`local_committed_pos_backed`, `local_committed_neg_backed`,
`local_committed_pos_unique`, `local_committed_pos_neg_excl`;
`vote_pos_quorum_implies_decodable`,
`local_fastqc_pos_chunks_decodable`,
`mvba_decided_pos_chunks_decodable`, `msg_commitqc_pos_chunks_decodable`;
from these and `local_committed_pos_backed`, the theorem
`Chorus.local_committed_pos_implies_decodable` (§3.5.2), proven once at every
reachable state in [Cadence/Chorus/Compose.lean](../Cadence/Chorus/Compose.lean).

### 6.6 Conditional-property support

Proposal inclusion (all relative to `all_honest_recorded`):
`inclusion_no_honest_vote_neg`, `inclusion_vote_pos_unique`,
`inclusion_no_honest_fb_neg`, `inclusion_fb_pos_unique`,
`inclusion_no_fastqc_neg`, `inclusion_fastqc_pos_unique`,
`inclusion_no_mvba_neg`, `inclusion_mvba_pos_unique`.

Speculative safety: `vote_rcv_pos_backed`, `vote_rcv_neg_backed` (a
receipt holds what the sender signed), `fb_neg_sig_has_witness`,
`fb_neg_qv_is_proposer`, `fb_neg_qv_backed`, `fb_neg_qv_received`,
`fb_neg_qv_no_rcv_quorum` — together the persistent residue of
`fb_sign_neg`'s guard over the validator's receipts, anchored on the
`aux_fb_neg_qv` record — and, relative to `no_equivocation` +
`no_invalid_encoding`, `fb_neg_qv_no_pos_quorum`: without equivocation the
entry a validator received from a sender is the sender's only entry, so no
positive quorum within `qv` exists at all. Then `fb_neg_no_pos_quorum`,
`spec_fastqc_pos_no_mvba_neg`, `spec_fastqc_pos_mvba_pos_unique` (same
two hypotheses).

### 6.7 Fallback commit round

`fbcommit_sig_backed` (an honest commit vote postdates the decision
vector it signs — Algorithm 5, line 37 (`line:fb-mvba-decide`) precedes Algorithm 5, line 41 (`line:fb-commitvote`)),
`fbcommitqc_implies_mvba_complete` (an `fbCommitQC`
certifies the decision vector: its `2f+1` votes contain an honest one),
and `mvba_decided_pos_proposer_signed` (filed under §6.4). Together
with `mvba_decided_pos_chunks_decodable` and `mvba_decided_is_proposer`
these are the backing and fair-progress content of the commit round —
see the "Commit-round epilogue" in §7 and the invariant block's header
comment in [Cadence/Chorus.lean](../Cadence/Chorus.lean).

## 7. Liveness

> **(Liveness)** Under (F-justice), (F-byz), the MVBA's scheduling and the
> validity bridge below, every honest validator eventually commits every
> slot.

This is a theorem: `Chorus.termination`
([Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)), for the single slot the
model holds, at every `n = 3f+1` and at the configuration the composed
system runs, with the premises stated as named `Prop`s in
[Cadence/Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean). What follows is the argument its proof
carries out; [Liveness.md](Liveness.md) §2 is the premise list in short.

The argument follows the classical verification-diagram method for
deductive liveness (cf. McMillan, *"Toward Liveness Proofs at Scale"*,
CAV 2024): every state-level step is a kernel-checked theorem, and the
premises contribute only *temporal* content — finitely many instances of
the single rule "*a continuously enabled fair action eventually fires*",
plus the MVBA's own termination theorem. The model-side encoding is the
"Liveness" section of [Cadence/Chorus.lean](../Cadence/Chorus.lean); the state-level theorems live in
[Cadence/Chorus/Progress.lean](../Cadence/Chorus/Progress.lean),
[Cadence/Chorus/Counting.lean](../Cadence/Chorus/Counting.lean) and
[Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean), and the temporal steps are
carried out over runs in [Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean).

**The chain** — how theorems and temporal steps alternate:

1. *(temporal — (F-justice).)* Every honest validator reaches
   **saturation**: it casts its path vote, fast or fallback, carrying
   the per-proposer entries that cast requires. On the way it receives
   every correct validator's vote (`receive_vote_*`, owed for a correct
   voter), and its negative fallback entry reads those receipts, "among
   the votes it received". Each constituent action
   is continuously enabled once its case applies (`progress_voting` /
   `progress_fallback_signing` state the per-proposer case analyses)
   until the step the link waits for has happened: its network guards
   never revert, and its fired-once guard fails only once it has fired,
   whose effect is that step (`Chorus.fb_entry_sigs` and its siblings in
   [Termination.lean](../Cadence/Chorus/Termination.lean)). So weak fairness
   fires it.
2. *(theorem.)* `Chorus.progress_dichotomy_of_saturation`: in any
   reachable saturated state, either a commitQC exists for **every**
   proposer from honest votes alone, or `mvba_invoked` holds together
   with per-proposer evidence stated verbatim as the decision handlers'
   bridge `require` and `mvba_propose`'s validity guards. Its proof is
   the case split below.
3. *(temporal, commit route — (F-justice).)* Certificates become
   broadcast certificates and commits: a correct collector's
   `broadcast_commitqc_*` guard is the commitQC itself (the collector is
   the validator itself, which is actively participating on this
   branch), `commit_assign_*_fast`'s the certificate a correct collector
   sent (the route names its sender, and is owed when the sender is
   correct), `finalize_commit`'s the per-proposer completeness
   (`local_committed_complete`). A finalizer re-broadcasts its
   certificates under its own name, so it is a correct sender in turn.
4. *(temporal, MVBA route — (F-justice) on `mvba_propose`, then the
   MVBA's own termination theorem, then (F-justice) on the handlers.)* Every correct validator
   proposes: the dichotomy's evidence is `mvba_propose`'s guard, and the
   proposal is state-level buildable — a fallback meta-block entry from
   **any** supermajority of accepted receipts, Byzantine members
   included (`Chorus.build_totality_of_reachable`), and a fast
   meta-block by aggregation, whose guard witness is *definitionally*
   the dichotomy's vote-quorum evidence (`vote_quorum_pos`'s definition
   and `aggregate_fastqc_pos`'s requires are the same two lines). The
   instance then decides at every correct validator (`Mvba.termination`,
   applied to the run's MVBA steps under `MvbaAdmissible`;
   [docs/Liveness.md](Liveness.md) §4.6),
   and each correct validator's handlers and `mvba_terminate` record its
   decision (`local_mvba_complete`). A decided certificate reaches an
   undecided correct validator through Chorus: the decider broadcasts the
   certificate its decision outputs (`send_mvba_cert`), and the receiver
   hands it to its MVBA (`accept_mvba_commitqc`). The handlers' one enabledness leg the class does
   not give is the bridge's completeness direction — a decided entry's
   certificate is on the network, which is what "publicly verifiable"
   means; the theorem names it as `ValidBridge` ([MvbaPlan.md](MvbaPlan.md) §3).
5. *(theorem + temporal.)* The fallback commit round
   (Algorithm 5, lines 37–47 (`line:fb-mvba-decide`–`line:fb-finalize`)) carries decisions to
   finalization: once `local_mvba_complete i` holds, a decided-positive root is
   held by a FastQC, which needs no wait, or by a FallbackQC, whose
   correct signer sent every validator its assigned chunk when it signed
   (`fb_sign_pos`, Algorithm 5, line 12 (`line:fb-redisseminate`);
   `Chorus.fb_pos_sig_chunks`); `cast_fb_commit` is then enabled
   (it has no phase gate); the `2f+1` honest
   commit votes are a certificate outright
   (`Chorus.fbcommitqc_of_honest_commit_votes` — the honest population
   is itself the quorum), a correct collector forms and broadcasts it
   (`broadcast_fbcommitqc`, Algorithm 5, lines 42–44
   (`line:fb-collect-commit`–`line:fb-commit-broadcast`)), and the
   receivers' route `commit_assign_*_fb` commits on it (Algorithm 5,
   line 45 (`line:fb-recv-commit`)); `fbcommitqc_implies_mvba_complete` +
   `mvba_complete_per_proposer` hand over its preconditions as on the
   commit route.

**The assumptions:**

* **(F-justice)** — phase advancement, aggregation, and per-validator
  honest actions are weakly fair; a step that consumes a message is owed
  only for a correct sender's message. Weak fairness suffices *because* the
  model is monotone: enabledness itself is monotone, so the
  enable/disable flicker that strong fairness exists for cannot occur.
  ((F-compassion) — strong fairness — is reserved vocabulary for the
  non-monotone implementation and is never invoked.)
* **(F-byz)** — Byzantine actions are unfair: no progress obligation is
  satisfied by adversarial help, which makes the discharged content
  strictly stronger than deadlock freedom.
* **The MVBA's scheduling** (`MvbaAdmissible`) — the run's MVBA steps,
  read as a run of the MVBA model, satisfy that model's own scheduling
  premises, so `Mvba.termination` applies to them. Its caller premises
  are derived, not assumed: (i) *all correct validators propose* is chain
  step 4 (the per-validator implementation refinement of the build step is
  the receipt layer — §7.2, [Architecture.md](Architecture.md) §5); (ii)
  *no correct validator abandons before deciding* holds on the branch of
  the proof that needs the MVBA, where no correct validator ever finalizes:
  by the caller premise `NoAbandonBeforeFinalizing` none abandons Chorus,
  and the MVBA's `abandon()` is invoked only by Chorus's `abandon`
  (Algorithm 5, line 48 (`line:fb-abandon`)). Within Cadence the glue abandons only after
  finalizing (Algorithm 1, line 23 (`line:abandon`)); (iii) *decided
  certificates are handed on* (F-relay) holds on the same branch, where
  every correct decider is active and sends its certificate
  (`Chorus.fRelay_of_fJustice`); (iv) *availability* (F-avail) follows
  from the availability report's fairness (`Chorus.fAvail_of_fJustice`).
* **The validity bridge** (`ValidBridge`) — the MVBA's `Valid` agrees with
  Chorus's certificate check, in both directions: a certified meta-block is
  `Valid`, and a decided one is certified. This is the cryptographic seam
  of §4, not a fairness assumption.
* **(A-mvba), retired.** The MVBA's termination used to be assumed here.
  The two premises above replace it
  ([Architecture.md](Architecture.md) §4 item 2). The randomised
  primitive's probability-1 termination stays a paper-level argument
  ([Liveness.md](Liveness.md) §2); the instance this development runs is
  the supplement's leader-based protocol, whose termination is proven.

**The ranking is structural.** Per-slot state is finite and all
relations are monotone, so the residual count of unset tuples strictly
decreases with every helpful firing — a fair run cannot stall before
any chain step. The (D) obligation of the verification diagram is
discharged by the monotonicity audit (§3.1), not by SMT; stating it as
invariants yields only tautologies of the form `… ∧ ¬X → ¬X`, so do
not add them.

**The case split** (the dichotomy's proof, on the number `x` of honest
validators that cast a fast commit vote):

* `x ≥ 2f+1`: honest commit votes agree per proposer (FastQC
  cross-uniqueness), so any `2f+1` of them are a commitQC
  (`Chorus.commitqc_of_honest_fast_dominant`) — no MVBA involved.
* `1 ≤ x ≤ 2f` (mixed): neither commitQC nor FBCert is guaranteed
  (Byzantine help is unfair; only `2f+1 − x` honest validators can
  still fallback-vote). The paper's case-(a) MVBA trigger closes the
  regime: any fast-path validator's FastQCs are backed by
  network-visible vote supermajorities
  (`fast_path_implies_vote_quorums`), which are at once the invocation
  trigger (a complete fast meta-block) and the per-proposer evidence.
* `x = 0`: every honest validator casts fallback votes (per-proposer
  signing is enabled one way or the other —
  `progress_fallback_signing`), so `FBCert` exists outright
  (`Chorus.fbcert_of_honest_fallback_votes` — the honest population is
  itself the quorum), and the per-proposer evidence is the **evidence
  pigeonhole** (`Chorus.evidence_pigeonhole_of_reachable`): `2f+1`
  honest per-proposer fallback entries split, by two-class counting,
  into an `f+1` negative sub-quorum (a negative FallbackQC), an `f+1`
  positive sub-quorum on one root (a positive FallbackQC), or positive
  entries on two roots — both proposer-signed, i.e. `equiv_evidence`.

The counting in these theorems partitions quorums by the value their
members signed — set comprehension, outside the abstract `ByzNodeSet`
language — which is why they are plain Lean over the concrete instance
family `byzNodeSetFin n f`, for every `n = 3f+1` and any Byzantine set
of size `≤ f`, rather than SMT-discharged invariants.

### 7.1 What stays outside Lean, and outside the models

Outside Lean: only the premises. Quantification over infinite fair
executions and the rule "continuously enabled ⇒ eventually fires" are
Lean: [Cadence/Fairness.lean](../Cadence/Fairness.lean)'s run vocabulary, used by
`Chorus.termination`. Phase markers never *must* advance; the network has
no GST marker; the MVBA instance's internal steps (`mvba_step`) are
scheduled by its own premises (`MvbaAdmissible`), not by (F-justice).
Everything state-level — enabledness, counting, certificate formation,
the case analysis — is theorems, and so is the temporal chain, so the
premises are consumed at exactly the seams the chain names and nowhere
else. They hold together: one model and run meets all of them at once
(`Chorus.termination_premises_satisfiable`,
[Cadence/Chorus/Witness.lean](../Cadence/Chorus/Witness.lean);
[Premises.md](Premises.md)).

Outside the models: the temporal layer is proven over runs of the
generated transition system in plain Lean, not by Veil's pipeline.
Internalising it is the liveness-to-safety extension designed in the Veil
fork ([Liveness.md](Liveness.md) §3 points to it).
Safety properties are unaffected by all of this: they hold in every
reachable state regardless of scheduling.

### 7.2 The fallback receipt rules, and why they are shaped this way

The fallback receipt/propose layer (Algorithm 5 (`alg:fallback`)) is the bridge
between two premises of different shape. The model's MVBA handoff needs
*global* evidence existence: `equiv_evidence j` holds the moment the
proposer has signed two roots, the MVBA's decisions are read off the
abstract instance and checked against network-global certificates (the
bridge, §4). The real MVBA needs *per-validator* evidence: every correct
validator must assemble certified evidence it holds locally into a valid
fallback meta-block (Appendix C.3 (`subsection:fallback_path`)) and
propose it, once (the paper's flag `mvbaInvoked`). The receipt rules are what carry the
first to the second, and two rules do it.

* *Receipt restriction* (Algorithm 5, line 18 (`line:fb-accept`)): a fallback vote is accepted
  only if every carried entry is a valid FastQC or the **sender's own**
  valid fallback signed entry, one vote counted per sender. The receipt
  rule harvests FastQCs only (Algorithm 5, line 20 (`line:fb-harvest`)), and the `Ev` chain is
  `⊥ →` own signed entry `→ FastQC` (Algorithm 4 (`alg:fast-path-certification`)).
* *Atomic build at propose time*
  (Algorithm 5, lines 26–30 (`line:fb-build-entry`–`line:fb-formqc`)): there are no standing
  FallbackQC/EquivCert formation rules; when `|M_i| ≥ 2f+1` fires, the
  meta-block is assembled per proposer directly from `M_i` — FastQC if
  harvested, else EquivCert from two conflicting positive entries, else
  a FallbackQC from `f+1` matching entries. The counting argument (if
  neither of the first two cases applies, the `2f+1` bare entries span
  at most two values — one root and `⊥` — so one value has `f+1`
  matching copies) is inline in the paper (Appendix C.3 (`subsection:fallback_path`),
  meta-block paragraph) and spelled out in the `M+3Δ` step of
  Proposition 5 (`prop:chorus-finalization-time`).

**Why the counting has to cover Byzantine votes.** The evidence
pigeonhole of §7 splits the `2f+1` *honest* fallback entries globally,
but a validator's `M_i` guarantees only `f+1` honest votes. Closing the
argument per validator therefore counts the Byzantine votes' entries
too, and the receipt restriction is what makes every accepted entry
countable: an entry is a FastQC or a signed entry of its sender, so each
of the `2f+1` accepted votes feeds one of the three build cases.

**Which half is load-bearing.** The receipt restriction. The atomic
build alone is not enough: a validator that still *accepted* carried
EquivCerts without counting them would leave a vote in `M_i` that feeds
no build case, and could then propose an entry that is a bare signed
entry rather than valid evidence — with the paper's `mvbaInvoked` set once, never
to re-propose. The atomic build removes the remaining race: with no
standing upgrade rules there is nothing for the propose to overtake.
The paper's v1 had exactly that gap — a liveness bug, reported by a
parallel verification effort, reproduced here, and fixed in v2; the
model checker's counterexample to the v1 rules is preserved at the tag
`v1-receipt-refutation`.

**Mechanised:** [Cadence/FallbackReceipt.lean](../Cadence/FallbackReceipt.lean)
verifies these rules — "`B` is valid by construction" by SMT for all `n`,
and the per-validator counting argument for every `n = 3f+1` in
[Cadence/FallbackReceipt/Totality.lean](../Cadence/FallbackReceipt/Totality.lean).

Around the receipt layer the paper also fixes the MVBA module interface
(Module 3 (`mod:mvba`)), the fallback commit round (§6.7), and an explicit
participation convention. The model tracks all three, and none of them
contradicts a proven safety invariant. One guard is worth naming because
the model depends on it: a correct receiver accepts a positive vote only
if it carries its *sender's assigned* chunk (`vote_valid`, §3.5.3), which
is what makes the fallback rules' reading of `isDecoded` honest — `f+1`
accepted positive votes pin `f+1` *distinct* chunks.

## 8. Abstractions worth flagging for review

* **Single Merkle root per chunk.** We collapse "encrypt → erasure-code
  → Merkle-commit" into a single opaque root and do not track chunk
  indices; quantitative erasure-code reasoning and the DA re-encode
  check are out of scope (§3.4).

* **Per-proposer signing decomposed.** The paper's `for pj ∈ Ps` loops
  are decomposed into per-proposer signing actions followed by a cast
  action whose precondition enforces loop completion (`vote` is fully
  atomic; `commit_sign_* / cast_fast_commit` and `fb_sign_* /
  cast_fallback_vote` are decomposed). Because only *broadcast* votes
  are network-relevant, the certificates over commit signatures
  (`commitqc_*`) require `msg_commit_cast` of every contributor —
  signatures produced but never cast never reach the network in the
  paper and never enter a certificate here.

* **Finalization is commitQC- or MVBA-backed — speculative commit is
  not finalization.** `commit_assign_*` requires a `commitqc_*`
  certificate or an MVBA decision, exactly the paper's commitment
  proofs. A complete set of own FastQCs — the paper's speculative
  commit — deliberately does not finalize; its safety is captured
  separately by the `speculative_agreement_*` properties, conditional
  on `no_equivocation` + `no_invalid_encoding`, matching the paper's
  revertibility claim at its proof sketch's full culprit set.

* **TIBE / encrypted payload.** Payload bytes are not modelled.
  `msg_decrypt_share` and the `slot_key_released` ghost capture the
  share-release discipline; `hiding_until_deadline` is the protocol
  half of hiding, `ThresholdIBE` in
  [Cadence/Primitives.lean](../Cadence/Primitives.lean) the cryptographic half.

* **EquivCert is the pair of proposer signatures.** `equiv_evidence j`
  holds iff the proposer signed two distinct roots — the content of
  the certificate `⟨equiv, s, j, ρ₁, σ_{p,1}, ρ₂, σ_{p,2}⟩`. The
  fallback votes through which an implementation *observes* the two
  signed roots are visibility plumbing the monotone network abstracts
  away. A failure of that observation step — a validator receiving
  evidence and not counting it — is something this model cannot express,
  which is why the receipt rules are verified in their own per-validator
  model (§7.2). Under those rules the abstraction is *aligned* rather than
  merely benign: fallback votes carry only FastQCs or the sender's own
  signed entry — exactly this model's `msg_fb_pos_sig`/`msg_fb_neg_sig`
  vocabulary — and EquivCerts / FallbackQCs exist only as objects
  assembled at propose time from the signed entries in `M_i`, i.e. the
  paper itself treats these certificates as derived from network-visible
  signatures, which is precisely the ghost-relation view here.

* **Byzantine chunks.** `byz_send_chunk` lets a Byzantine proposer send
  any chunk under its own name to any recipient, capturing chunk
  equivocation (§5).

* **One entry per received vote.** A receiver keeps the first entry it
  receives from each sender for each proposer (`receive_vote_*`); a vote is
  one message per sender, so a Byzantine sender that signs conflicting
  entries reaches different receivers with different votes, and each
  receiver keeps one (§3.1).

## 9. What is left for the next iteration

These are places the Chorus model could go further; none is a gap in what
the development *claims*. This section is the home of the Chorus-specific
items. The cross-cutting ones, the locality checker among them, are in
[TODO.md](TODO.md), and the bigger lifts in §§10.1–10.3 below.

1. **A model instance of `ThresholdIBE`.** It is the one primitive class of
   [Cadence/Primitives.lean](../Cadence/Primitives.lean) with no instance,
   and an instance would show its axioms are satisfiable rather than
   contradictory. The quorum classes have theirs, and the `MVBA` contract,
   which lives in [Cadence/Interfaces.lean](../Cadence/Interfaces.lean), has
   `Mvba.mvbaSafety` / `Mvba.mvba_of_temporal`
   ([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)), consumed by
   Chorus (§4).

2. **Epochs and proposer rotation.** Derive `is_proposer` from a
   VRF-output relation instead of fixed configuration, once a `VRF`
   primitive class exists in
   [Cadence/Primitives.lean](../Cadence/Primitives.lean). Epochs and
   proposer rotation are outside the papers' consensus-layer treatment.

3. **Multi-slot Chorus.** The model fixes one slot, and cross-slot
   independence is argued rather than modelled (§3.4).

4. **An in-build `sat trace` for Chorus.** Chorus cannot carry one today:
   the trace pipeline needs the label enumeration that
   [Chorus.lean](../Cadence/Chorus.lean) disables for size, and every
   finalizing run passes through `vote`, whose bulk update uses a `decide`
   the trace pipeline cannot translate. Either fix is a model refactor.
   Finalization is shown reachable in the build by the run of
   [Chorus/Witness.lean](../Cadence/Chorus/Witness.lean), and again in CI
   by the monitor's fast-path fixture ([Monitor.md](Monitor.md)).

## 10. Bigger lifts — what would need new machinery

### 10.1 Making the network assumption explicit and proven

The async-soundness argument in §3.2–§3.3 is a **meta-level claim**: it
depends on the locality rules of [Locality.md](Locality.md) (§3.1.1), which Veil does not
enforce. Making the simulation a theorem in the system would remove the
largest item of [Architecture.md](Architecture.md) §4. Two routes:

**(a) Model the network explicitly.** Introduce a per-recipient
delivery relation `delivered_to i σ` and precondition every consuming
action on it, with an adversarial delivery action. Textbook-correct,
but it roughly doubles the state space and pushes more invariants
outside EPR. Probably necessary for liveness or message-level
adversaries anyway.

**(b) Keep the lightweight monotone abstraction, but prove the
simulation.** Define an explicit-network `AsyncChorus` alongside
`Chorus`, a forward-simulation relation, and prove every `AsyncChorus`
transition is matched under it. Safety in `Chorus` then transfers as a
discharged theorem. A cheaper variant: a checkable per-action
"monotonicity frame condition" (adding network tuples preserves
enablement and updates), which would catch contract violations
mechanically without the full simulation.

### 10.2 Lifting to message-level adversaries

The current adversary is signature-level. Reordering and duplication
are absorbed by the monotone abstraction; selective *delay* is the part
the (M-frame) contract covers implicitly and an explicit network model
would make formal.

### 10.3 Liveness

See §7.1: the one thing not encoded is the temporal rule itself. The
designed extension — ω-acceptance annotations on actions, discharged
via a liveness-to-safety (L2S) reduction reusing the existing
safety-VC machinery — is Veil work and lives in the fork
([Liveness.md](Liveness.md) §3 points to it). Bounded delivery after
GST is not part of that extension: the timed claims are proven over timed
runs of the generated transition system, in plain Lean
([Bounds.md](Bounds.md)). Out of scope either way: probabilistic
termination, whose treatment would be to axiomatise the randomised
primitive and discharge the probability argument on paper.
