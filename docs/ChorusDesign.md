# Chorus — Veil model design notes

*(The per-model design rationale. The top-level architecture document — with
the methods, the trust bases and the meta-assumption inventory — is
[Architecture.md](Architecture.md); the entry point for the repository is
[README.md](../README.md).)*

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

Concretely there are twelve signed-message / network relations
(`msg_proposer_signed`, `msg_chunk_received`, `msg_vote_pos_sig`,
`msg_vote_neg_sig`, `msg_vote_cast`, `msg_fb_pos_sig`, `msg_fb_neg_sig`,
`msg_fallback_sig`, `msg_commit_pos_sig`, `msg_commit_neg_sig`,
`msg_commit_cast`, `msg_decrypt_share`), one family of per-validator
certificate observations (`local_fastqc_pos/neg` — the FastQC a
validator's own commit signature is justified by), the per-validator
protocol state (`local_entry_*`, `local_voted`, `local_path`,
`local_committed*`), and the abstract/oracle state (`mvba_st`, `mvba_decided_*`,
`mvba_complete`, `phase`). All *transferable* certificates (FallbackQC,
EquivCert, FBCert, commitQC, chunk-decodability, the reconstructed slot
key) are **derived predicates** (`ghost relation`s) over the signature
relations — see §3.5.

### 3.1 What "monotone" actually means here

The single word "monotone" hides two distinct properties:

* **(M-update)** *Monotone update* — tuples can only be added to the
  relation, never removed.
* **(M-frame)** *Positive-only use* — the relation appears in action
  preconditions only in positive position (no `¬R(…)`, no
  `∀M, ¬R(…, M)` over the relation).

(M-update) and (M-frame) are independent. The standard
"monotone-abstraction" idiom for asynchronous networks relies on
**both**, and the soundness argument in §3.2 below uses both for the
network relations. Auditing Chorus, the property split is:

| Relation | M-update | M-frame |
|---|:-:|:-:|
| `msg_chunk_received` | ✓ | ✓ |
| `msg_proposer_signed` | ✓ | ✗ — one self-row read: `propose j` guards on its **own** row (see "Self-row negative reads" below) |
| `msg_vote_*_sig`, `msg_vote_cast`, `msg_fb_*_sig`, `msg_fallback_sig`, `msg_commit_*_sig`, `msg_decrypt_share`, `msg_fbcommit_sig` | ✓ | ✓ (but see the note on `fb_sign_neg` below) |
| `msg_commit_cast` | ✓ | ✗ — six self-row reads: `¬ msg_commit_cast i` for the acting validator `i` (see "Self-row negative reads" below) |
| `local_fastqc_*` | ✓ | ✗ (negative observations of own state) |
| `mvba_st : mstate` | (the contract's `decided_mono`: decisions only accrue along `mvba.step`/`mvba.propose`) | ✓ — consulted only through `mvba.decided`, in positive position, by the decision handlers, `mvba_terminate` and `cast_fb_commit` |
| `mvba_decided_*`, `mvba_complete` | ✓ | ✓ — read positively only. The records are written by the decision handlers, which never read them |
| `phase : Phase` enum | (forward-only, see below) | ✓ |
| `local_entry_pos/neg`, `local_voted`, `local_path`, `local_committed*` | ✓ | ✗ |
| `participating`, `abandoned` | ✓ (written only by the inputs `participate i` / `abandon i`) | ✗ — the participation gate `participating i ∧ ¬ abandoned i` of every sending rule, read at the acting validator (for `broadcast_commitqc_*` and `redisseminate_chunk`, the sender parameter) |
| `local_chunk_sent`, `local_commit_entry`, `local_fb_entry`, `local_commitqc_sent`, `local_mvba_recorded`, `local_fbcommit_voted` (the fired-once records, S1b) | ✓ (each written only by the action it guards) | ✗ — each action's "not already" guard, read at the acting validator only |

(M-update) is syntactic for every relation in the table: each write is the
literal `true`, except `vote`'s bulk updates of `msg_vote_pos_sig`,
`msg_vote_neg_sig` and `local_entry_neg`, which are disjunctions with the
relation's old value (`msg_vote_pos_sig i J M := msg_vote_pos_sig i J M ||
(…)`). Veil's generated `<f>.mono` lemmas cover the literal-`true` writes
only, so those three are proven by hand, with the same statement, in
[Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)
(`Chorus.msg_vote_pos_sig_mono` and its two siblings).

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
post_fb_arm → post_mvba_arm`); it advances only through explicit
`advance_to_*` actions whose preconditions force the forward direction.

**The `fb_sign_neg` guard.** One action deliberately deviates from pure
(M-frame): the paper's validator signs a *negative* fallback entry for
`j` exactly when, among the ≥ 2f+1 votes it received, no root has an
f+1 positive sub-quorum with decodable data (Algorithm 5, line 8 (`line:fb-cast-entry`), else-branch). A per-validator "received" set does
not exist in the monotone model, so the guard is stated relative to a
*witnessed* supermajority `qv` of broadcast votes (the action's
parameter): `∀ M q, ¬(q ⊆ qv ∧ q positive-signs M ∧ …)`. The negation
ranges over the witnessed subset only, so a validator may still
negative-sign although a positive quorum exists outside `qv` — the
behaviours asynchrony makes real are retained (the abstraction stays
conservative). A guard negating over the *global* signature state would not
be conservative: it would exclude real behaviours.

**The fallback commit wait reads only the validator's own decision.**
`cast_fb_commit i v` requires `mvba.decided mvba_st i v` (the oracle state,
in positive position) and waits under exactly the FallbackQC entries of
`v`: `∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J →
msg_chunk_received i J M`. The antecedents are immutable projections and
the chunk receipt is read positively, so the action consults no network
relation negatively and none of the shared decision records (Algorithm 5,
lines 37–39 (`line:fb-mvba-decide`–`line:fb-commit-wait`);
[PaperAlignment.md](PaperAlignment.md) §8.1 (d)).

**Self-row negative reads (`msg_proposer_signed`, `msg_commit_cast`).**
Seven guards read a network relation negatively where the row consulted
is indexed by the **acting validator itself** and written by no one
else:

* `propose j` requires `∀ m2, msg_proposer_signed j m2 → m2 = m` — "I
  have not already signed a different root". For honest `j` the row
  `msg_proposer_signed j` is written only by `propose j` itself: the
  only other writer, `byz_sign_proposer j`, requires `is_byz j`, and
  `is_byz` is immutable configuration.
* `commit_sign_pos`, `commit_sign_neg`, `cast_fast_commit`,
  `fb_sign_pos`, `fb_sign_neg`, and `cast_fallback_vote` require
  `¬ msg_commit_cast i` — "I have not already cast my fast commit
  vote". For honest `i` the row `msg_commit_cast i` is written only by
  `cast_fast_commit i` (the only other writer, `byz_cast_commit i`,
  requires `is_byz i`).

These reads are **sound**, for a reason distinct from the two
exceptions above: under the §3.2 simulation the global monotone value
of a self-row coincides with the acting validator's local knowledge in
the asynchronous run — the row records the validator's own *production*
history, not delivery, so no adversarial scheduling can make the
monotone read differ from what the real validator observes about
itself. Semantically these are the local checks "I have not already
proposed / already cast" that any real validator performs on its own
state. Network tuples produced by *other* participants can never
disable these guards.

The network relations satisfy **both** properties elsewhere. The
per-validator local state relations satisfy only (M-update): they appear
in negative position in some preconditions — e.g., `commit_assign_neg`
requires `∀ m, ¬ local_committed_pos i j m`. This is sound because a
validator can correctly observe its own non-decisions; what would *not*
be sound is asking "no validator has signed this" or "no FastQC exists".

Crucially, **there is no `received i σ` predicate**: nothing in the
model *forces* validator `i` to act on a globally-visible signature.
An honest validator may fire an action whose precondition references
that signature; it equally may not. The model therefore does **not**
claim "every message is received eventually" — it does not track
delivery at all.

### 3.1.1 Load-bearing contract for future edits

The positive-use property of the network relations is an **assumption
of the soundness argument**, not a property the Veil tool enforces.
If a future edit observes a network relation negatively (via `¬R`,
`∀ R, R(…) → …`, an `if-then-else` whose `else` branch fires on
`¬R`, or any update expression sensitive to `¬R`), the SMT proofs may
still go through but the claim that "safety in this model implies
safety in an asynchronous network" will silently no longer hold.

Therefore the following is a **contract**, not a documentation aid:

> Actions in [Cadence/Chorus.lean](../Cadence/Chorus.lean) must consult the **network relations**
> listed in §3.1 only in positive position, both in preconditions and
> in update right-hand sides — with two documented exception
> categories: (i) `fb_sign_neg`'s witnessed-quorum guard, whose
> negation is scoped to the action's own `qv` parameter (it observes
> the *absence of a quorum within a set the validator has received*,
> which a real validator can observe); and (ii) the seven **self-row
> reads** enumerated in §3.1 — a negative read of a relation row that
> is indexed by the acting validator and written only by that
> validator's own actions. Any new self-row read must satisfy the same
> writer condition (audit every writer of the row, honest and
> Byzantine) and be added to the §3.1 enumeration. The
> **per-validator local relations** are exempt — negative observations
> of one's own local state are sound.


The robust semantic formulation is *action monotonicity w.r.t. network
tuples produced by other participants*: adding such tuples to the
pre-state should never disable an action nor change its update
behaviour. The self-row reads satisfy this through the writer
condition — only the acting validator's own firing adds the tuple the
guard consults — and `fb_sign_neg` deviates knowingly: a larger
pre-state can disable the action for a given `qv` exactly as more
received votes can in the real protocol. When adding or modifying an
action, audit it against this contract. A future improvement (tracked
in [TODO.md](TODO.md) § Soundness and as §9 item 3 below) is an
automated syntactic check — one that *classifies* every occurrence
(positive / self-row / documented exception) rather than merely
rejects, so that reads like the seven above are reported and
acknowledged explicitly instead of slipping past a reject-only lint.

### 3.2 Why this is sound for safety

The monotone model is a **conservative over-approximation** of
asynchronous behaviour with per-recipient delivery state `R_i ⊆ Σ`.
For any async execution `E_async` we can simulate it in the monotone
model by letting the global set be `⋃ᵢ R_i` and having validator `i`'s
actions consult only the signatures that lay in its `R_i` at the
corresponding step (the monotone model never *forces* anyone to
consult anything; `fb_sign_neg`'s `qv` is instantiated with the
validator's actual received-vote set, and the paper's guard implies
the model's `qv`-relative guard). So

> `{ reachable states in async with per-recipient delivery }` ⊆
> `{ reachable states in monotone }`.

If safety holds in the monotone model, it holds in async. The reverse
is not true — the monotone model admits states no async run can reach —
but the extra states only enable *more* protocol activity, never less,
so they cannot mask a safety violation.

Selective-revelation attacks (a Byzantine proposer sending chunks for
`m₁` to half the validators and `m₂` to the other half) are still
modelled correctly because **chunks are per-recipient**:
`msg_chunk_received i j m₁` vs `msg_chunk_received i j m₂` is a
function of `i`. The proposer's two signed headers are globally
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

## 3.5 State locality contract

Every state item in [Cadence/Chorus.lean](../Cadence/Chorus.lean) falls into one of
four categories. The category determines what it **stands for** in the
real protocol and what part of the soundness argument lifts it back to
the asynchronous-network world.

### (N) Network state — broadcast, globally visible

Signed messages observed on the gossip overlay. Under the monotone
idealisation of §3.1 they become globally visible the moment they
exist. Naming convention: `msg_*`.

| Relation | Paper analogue |
|---|---|
| `msg_proposer_signed j m` | outer chunk-header signature `σ` on `⟨s, j, mroot⟩` (Algorithm 2 (`alg:proposer-dissemination`)). |
| `msg_chunk_received i j m` | the chunk **assigned to validator `i`** has reached `i` (proposer unicast, vote-carried, fallback re-dissemination Algorithm 5, line 12 (`line:fb-redisseminate`), or commit-round broadcast Algorithm 5, line 39 (`line:fb-commit-wait`); the receive-time rebroadcast `line:da-rebroadcast`, a v1 rule, was removed in v2 — chunk redistribution is now vote-carried, matching this model's `vote_pos_sig_chunk` chain). The **only** per-recipient network relation — see §3.5.1. |
| `msg_vote_pos_sig r j m`, `msg_vote_neg_sig r j` | per-proposer signed entries of the `Vote` broadcast (Algorithm 3 (`alg:voting`)). |
| `msg_vote_cast r` | `r` has broadcast its `Vote` (Algorithm 3, line 14 (`line:vote-broadcast`)). Receivers discard votes without an entry per proposer, so a cast vote implies per-proposer signatures (`vote_cast_entries`). |
| `msg_fb_pos_sig r j m`, `msg_fb_neg_sig r j` | per-proposer signed fallback entries in the `FallbackVote` broadcast (Algorithm 5 (`alg:fallback`)). |
| `msg_fallback_sig r` | the `σ_r` on `⟨fallback, s⟩` in the `FallbackVote` broadcast. |
| `msg_commit_pos_sig r j m`, `msg_commit_neg_sig r j` | per-proposer signature inside the `CommitVote` (Algorithm 4 (`alg:fast-path-certification`)). |
| `msg_commit_cast r` | `r` has broadcast its `CommitVote` (Algorithm 4, line 24 (`line:fast-commitvote`)). Only broadcast commit signatures count toward a commitQC. |
| `msg_decrypt_share r` | the extraction share released with `r`'s `Vote`. |
| `msg_fbcommit_sig r` | `r`'s `FallbackCommitVote` broadcast (Algorithm 5, line 41 (`line:fb-commitvote`)). The entry vector it signs is implicit — an honest vote is over the MVBA-decided entries, unique by the MVBA contract's agreement (§6.4); see the relation's comment in [Cadence/Chorus.lean](../Cadence/Chorus.lean) for why this over-approximates only the adversary. |

**Positional chunks.** A chunk is identified by `(assignee, proposer,
root)`: `msg_chunk_received i j m` is the fragment at validator `i`'s own
position under `j`'s root `m`, and the decode threshold `chunk_quorum`
counts distinct assignees. That is the target's positional reading:
Algorithm 6 (`alg:da`) stores validated fragments as pairs `(r, d_r)`, checks each leaf at
its index, and decodes from `f+1` distinct indices, and the re-encode check
(Algorithm 6, line 24 (`line:da-reencode`)) compares positional leaf hashes. The model never had
an unindexed fragment to confuse, so nothing changes in it.
`Primitives.ErasureCoding` states the codec at the same reading
([PaperAlignment.md](PaperAlignment.md) §5.2).

The contract from §3.1.1 applies to all of these.

### (D) Derived certificates — ghost relations

Transferable certificates are definitional predicates over (N):
`vote_quorum_pos/neg` (FastQC certificates), `fb_quorum_pos/neg`
(FallbackQCs), `equiv_evidence` (EquivCert — the proposer's signatures
on two distinct roots), `fbcert` (FBCert), `commitqc_pos/neg`
(commitQC validity), `fbcommitqc` (fbCommitQC — `2f+1` fallback commit
votes, Algorithm 5, line 43 (`line:fb-formcommitqc`)), `chunk_quorum` (`isDecoded`),
`slot_key_released` (f+1 extraction shares),
`complete_fast_metablock` / `mvba_invoked` (MVBA proposal triggers),
plus the hypothesis predicates `no_equivocation`,
`no_invalid_encoding` and `all_honest_recorded`. A certificate "exists"
iff its aggregated signatures are observable — which matches the
protocol, where any holder of the signatures (honest or Byzantine)
can assemble the certificate and any receiver can verify it. Nothing
needs to *own* a transferable certificate, so they carry no validator
index.

One certificate additionally has an *assembled-and-broadcast* network
form: `msg_commitqc_pos/neg` (category (N)), set by the
`broadcast_commitqc_*` actions whose precondition is exactly the
certificate's validity check (Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)). Finalization (`commit_assign_*`)
consumes the broadcast form. Verification-wise this materialisation
matters: it keeps the deep quorum reasoning at the single assembly
action (where the quorum is an explicit witness) instead of forcing
every commit-side VC to re-derive it from an `∃`-quorum ghost, which
is what sent the SMT matcher into timeouts.

### (L) Local state — per-validator, only `i` observes its own

Naming convention: `local_*`. Honest actions read and write only the
row indexed by the acting validator.

| Relation | Paper analogue |
|---|---|
| `local_entry_pos i j m`, `local_entry_neg i j` | validator `i`'s per-proposer `Entry(pid)` (Algorithm 3 (`alg:voting`)). |
| `local_voted i` | `i` has executed the deadline vote handler. |
| `local_path i : PathChoice` | `i`'s `pathVote ∈ {none, fast, fallback}`. |
| `local_fastqc_pos i j m`, `local_fastqc_neg i j` | `i` has aggregated `Ev(j)` as a FastQC (Algorithm 4, line 18 (`line:fast-formqc`)). Kept per-validator (unlike the transferable certificates) because an honest commit signature is justified by *the signer's own* FastQC observation. |
| `local_committed i`, `local_committed_pos i j m`, `local_committed_neg i j` | `i`'s finalization decision. |
| `participating i`, `abandoned i` | `i` has invoked the slot-consensus inputs `participate()` / `abandon()` (Module 1 (`mod:slotconsensus`)); written only by the input actions of the same name. Named as the contract's observables rather than `local_*`. Every sending rule reads them at its own sender (the participation gate), which is a local read. |
| `local_chunk_sent k i j m` | sender `k` has sent `i` its assigned chunk under `(j, m)`: the proposer's `deliver_chunk_assigned` (`k = j`) or a correct `redisseminate_chunk` (Algorithm 5, line 12 (`line:fb-redisseminate`)). |
| `local_commit_entry i j`, `local_fb_entry i j` | `i` has signed its commit-vote entry, resp. its fallback entry, for proposer `j` (the per-proposer steps of Algorithm 4, line 24 (`line:fast-commitvote`) and Algorithm 5, line 8 (`line:fb-cast-entry`)). |
| `local_commitqc_sent c j` | collector `c` has broadcast its commit certificate's entry for `j` (Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)). |
| `local_mvba_recorded i j` | `i` has recorded entry `j` of its MVBA decision (Algorithm 5, line 37 (`line:fb-mvba-decide`)). |
| `local_fbcommit_voted i` | `i` has cast its fallback commit vote (Algorithm 5, line 41 (`line:fb-commitvote`)). |
| `local_fb_neg_qv i j qv` | *auxiliary (proof-only) history variable*: the witnessed vote quorum against which `i` cast its negative fallback entry (the `qv` parameter of `fb_sign_neg` at firing time). Written by `fb_sign_neg`, read by no action; it lets the speculative-safety invariants refer to the quorum after the fact without a quantifier alternation that breaks the SMT matcher. |

Cross-validator agreement that a "global QC" idiom would give
definitionally is a **theorem** here — e.g.
`local_fastqc_pos_cross_unique`, discharged from
`local_fastqc_pos_backed` and quorum intersection.

### (A) Abstract / oracle state — black-box semantics

Naming convention: bare identifier.

| State | Paper analogue |
|---|---|
| `phase : Phase` | the slot's notional time landmark. One global value: per-validator clock skew is absorbed into the gap between `advance_*` actions. |
| `mvba_st : mstate` | the abstract state of the slot's MVBA instance (Module 3 (`mod:mvba`)), held as the glue holds `sc_state s`: an opaque sort, read only through the contract `mvba : MVBASafety …` (§4), advanced by the oracle step `mvba_step` and the driven inputs `mvba_propose`, `accept_mvba_commitqc`, `mvba_avail_ready` and `abandon`. |
| `mvba_decided_pos j m`, `mvba_decided_neg j` | Chorus's per-proposer records of the certified entries, written by the decision handlers `on_mvba_decide_*` from a correct validator's decision `mvba.decided mvba_st i v`, and by the `CommitQC` route's handlers `on_mvba_commitqc_*` from a valid certificate `mvba.certifies mvba_st c (mvba.entries v)`, through the entry-vector projections `mval_pos`/`mval_neg`. The contract's agreement and its certificate fields make a single global view sound: `mvba_decided_pos_unique` is *proven* from them (§6.4). |
| `mvba_complete : Bool` | a correct validator's full decision vector has been recorded (`mvba_terminate`). |

### 3.5.1 Why `msg_chunk_received` is the only per-recipient network relation

In the paper, every other network message is broadcast on the gossip
overlay. Once they exist, every validator eventually sees them, and the
monotone-network idealisation collapses "exists somewhere" with
"globally visible". Chunks are different: the proposer sends *one chunk
per validator*, point-to-point, and the per-validator distinction
directly affects the protocol — `local_entry_pos i j m` is producible
only when `i` received its assigned chunk before the deadline.

### 3.5.2 Chunk delivery and data availability

Chunk delivery is *not* part of `propose`: `propose` records the
proposer's atomic root commitment (`msg_proposer_signed`), and
`deliver_chunk_assigned` (honest proposers) / `byz_deliver_chunk`
(Byzantine proposers, unconstrained recipient/root) deliver chunks
per-recipient and asynchronously.

The decoding threshold (`isDecoded`) is the ghost `chunk_quorum j m`
(`f+1` delivered chunks). Two facts govern it:

* A *valid* positive vote entry carries the signer's chunk — receivers
  discard unbacked positive entries (Algorithm 4 (`alg:fast-path-certification`),
  receive handler). The model enforces this for Byzantine signers as a
  validity precondition on `byz_sign_vote_pos` and derives it for
  honest signers, yielding the invariant `vote_pos_sig_chunk`: *every*
  positive vote signature is chunk-backed. Consequently an f+1
  positive-vote quorum is itself a chunk quorum
  (`vote_pos_quorum_implies_decodable`) — the erasure-decode threshold
  (c) follows from the vote threshold (b) at the network level.
* `fb_sign_pos` nevertheless keeps (c) as an explicit precondition,
  because `isDecoded` is a check the real protocol performs.

The model-level DA safety theorem is
`local_committed_pos_implies_decodable`: every honest positive commit
has `f+1` chunks delivered for the committed root — the counterpart of
"`recoverProposals` does not block" (Algorithm 6, line 12 (`line:da-wait`)).

### 3.5.3 The faithfulness contract — summary

> Every state item is one of: a network message (`msg_*`, monotone,
> globally visible), a derived certificate (ghost relation over
> `msg_*`), a per-validator local state (`local_*`), or an
> abstract/oracle quantity (bare name).
>
> Honest actions write only `local_*` rows of the acting validator,
> `msg_*` entries the acting validator is entitled to sign, or a
> single abstract landmark. They read any `msg_*` and any `local_*`
> row they own; reading another validator's `local_*` is a contract
> violation.

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
i j v` transport a correct validator's decision (`mvba.decided mvba_st i
v`) entry by entry into the records `mvba_decided_pos j m` /
`mvba_decided_neg j` — per entry rather than as a bulk transport, so every
update stays a monotone `:= true` and the downstream invariants keep their
form. `mvba_terminate i v` records that every proposer's entry of a
correct validator's decision has been recorded (`mvba_complete`), the
model shadow of Algorithm 5, line 37 (`line:fb-mvba-decide`) delivering `B'` at once, and gates
the fallback commit round. None of them has a phase gate: the paper's
handler runs "upon `MVBA[s].decide(B′)`", with no time condition, and a
decision can come before the MVBA arm (the case-2 proposal needs only the
fallback votes).

**The `CommitQC` route** (Supplement, Section 1.2 (`subsec:mvba-protocol`),
"Decision output and handoff"): "A correct validator that receives a
valid such certificate re-broadcasts it and finalizes the certified
outcome, recovering a matching meta-block or the underlying proposals as
required by the ordinary commitment-proof recovery path." The handlers
`on_mvba_commitqc_pos i j m c v` / `on_mvba_commitqc_neg i j c v` take a
valid certificate `c` and a representation `v` of its entries (the
recovered meta-block), check the certificates `v` names against the
network, the bridge below, and record the entries in the same shared
records. Finalization is then the ordinary `commit_assign_*` /
`finalize_commit`, whose certificate disjunct reads `fbcommitqc ∨
mvba_commitqc` (the ghost "a valid MVBA certificate exists"). The
re-broadcast needs no step, since a valid certificate stays valid
(`certified_mono`). The records are fired once per entry from either
source (`local_mvba_recorded`). The route's agreement with the fast path
is `commitqc_pos_mvba_consistent` and its two exclusion siblings at the
new handlers, by the main body's fast-path argument over the bridge
evidence. Its agreement with the `fbCommitQC` route and with itself is
the contract's `certified_unique` and `certified_decided`, through the
restated ties.

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
re-check. The guard has exactly the shape of the Conductor's ACS median
bridge (`acs_decide`), and it is sound in both directions that matter: it
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
two `CommitQC` route handlers in [Cadence/Chorus.lean](../Cadence/Chorus.lean), and — as the
same disjunction — the validity guards of `mvba_propose`, where it is the
caller's obligation rather than the receiver's check. At the route the
checked representation is the recovered one, and the same soundness
argument applies: `Recover(e)` returns a valid representation
(`certified_valid`), and a valid one passes the check.

**What the class buys.** Agreement of the records —
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
and the decision handlers and `mvba_terminate` require the derived
`mvba_invoked = fbcert ∨ (∃ honest I, complete_fast_metablock I)` — a
Chorus-side listening condition on which no safety invariant relies. The
`CommitQC` route does not: a validator on the fast path that receives a
certificate finalizes on it. The
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
headers for the same proposer), selectively deliver chunks of distinct
roots to disjoint subsets of validators (`byz_deliver_chunk`), and cast
inconsistent votes / fallback signatures / commit votes. Cryptographic
unforgeability prevents it from signing as an honest node; honest local
state, MVBA decisions and the phase are updated only by their own
actions.

**Network validity is part of the threat model.** Honest receivers
verify messages before consuming them, so a malformed message never
enters a quorum any honest validator or the MVBA observes. The
Byzantine actions mirror the receivers' checks:

* `byz_sign_vote_pos` requires the signer's chunk
  (`msg_chunk_received r j m`) — positive vote entries without a valid
  chunk are discarded (Algorithm 4 (`alg:fast-path-certification`), receive handler);
* `byz_cast_vote` requires a signed entry per proposer — incomplete
  votes are discarded;
* `byz_sign_fb_pos` requires `msg_proposer_signed j m` — the positive
  fallback entry carries the proposer signature `σ_p`, which receivers
  verify.

These preconditions do not weaken the adversary: they exclude only
messages that could never influence an honest participant.

**The adversary's share of the anonymous capabilities.** Assembling a
commit certificate from `2f+1` broadcast commit votes, and re-disseminating a
chunk once `f+1` chunks are on the network, are capabilities any holder of
the data has. For a correct sender they are the honest rules
`broadcast_commitqc_*` and `redisseminate_chunk`, gated on participation and
fired once. In Byzantine hands they are `byz_broadcast_commitqc_*` and
`byz_redisseminate_chunk`: the same validity checks, no gate, no record, and
no fairness ((F-byz)). Until S1b both were branches of the honest actions;
splitting them keeps every fair action fired-once
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
`local_committed_pos_backed` reduces every honest commit to a
`commitqc_pos` or an `mvba_decided_pos`. Case commitQC–commitQC:
`supermajorities_intersect_in_honest` + `commit_pos_sig_unique`. Case
MVBA–MVBA: `mvba_decided_pos_unique`, itself proven from the MVBA
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
above. The model reaches the same conclusion one layer lower: its
fallback finalization route (`fbcommitqc ∧ mvba_decided_*`,
`commit_assign_*`) consumes the *decision* directly, and decision
agreement comes from the MVBA contract — so the model's proof does not need
the fbCommitQC–fbCommitQC intersection at all. The commit round's own
certificate discipline is nonetheless modelled and checked
(`fbcommit_sig_backed`, `fbcommitqc_implies_mvba_complete`, §6.7): an
`fbCommitQC` cannot exist before the decision vector it certifies.

### 6.2 Local sanity

`proposer_unique_root`, `local_entry_pos_signed`, `local_entry_unique`,
`local_entry_pos_neg_excl`, `local_entry_pos_chunk`, the
signed-implies-voted family (`vote_sig_pos_implies_voted`,
`vote_sig_neg_implies_voted`, `local_entry_neg_implies_voted`,
`vote_cast_implies_voted`, `voted_implies_cast`, `share_implies_voted`),
`vote_pos_from_local`, `vote_neg_from_local`, `vote_unique_pos`,
`vote_unique_pos_neg`, `voted_entry_pos_signed`, `vote_cast_entries`,
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
`mvba_decided_pos_tied`, `mvba_decided_neg_tied` (every record is the
projection, through `mval_pos`/`mval_neg`, of some correct validator's
decision on the abstract state — inductive under the oracle step because
the contract's `decided_mono` keeps decisions decided), and from these,
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
so the commit-round VCs need not re-derive it.

### 6.5 Commit backing and data availability

`local_committed_pos_backed`, `local_committed_neg_backed`,
`local_committed_pos_unique`, `local_committed_pos_neg_excl`;
`vote_pos_quorum_implies_decodable`,
`local_fastqc_pos_chunks_decodable`,
`mvba_decided_pos_chunks_decodable`,
`local_committed_pos_implies_decodable` (§3.5.2).

### 6.6 Conditional-property support

Proposal inclusion (all relative to `all_honest_recorded`):
`inclusion_no_honest_vote_neg`, `inclusion_vote_pos_unique`,
`inclusion_no_honest_fb_neg`, `inclusion_fb_pos_unique`,
`inclusion_no_fastqc_neg`, `inclusion_fastqc_pos_unique`,
`inclusion_no_mvba_neg`, `inclusion_mvba_pos_unique`.

Speculative safety: `fb_neg_sig_has_witness`, `fb_neg_qv_is_proposer`,
`fb_neg_qv_backed`, and (relative to `no_equivocation` +
`no_invalid_encoding`) `fb_neg_qv_no_pos_quorum` — together the
persistent residue of `fb_sign_neg`'s witnessed-quorum guard, anchored
on the `local_fb_neg_qv` history variable — plus `fb_neg_no_pos_quorum`,
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
"Liveness" section of [Cadence/Chorus.lean](../Cadence/Chorus.lean) (whose prose
still names (A-mvba)); the state-level theorems live in
[Cadence/Chorus/Progress.lean](../Cadence/Chorus/Progress.lean),
[Cadence/Chorus/Counting.lean](../Cadence/Chorus/Counting.lean) and
[Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean), and the temporal steps are
carried out over runs in [Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean).

**The chain** — how theorems and temporal steps alternate:

1. *(temporal — (F-justice).)* Every honest validator reaches
   **saturation**: it casts its path vote, fast or fallback, carrying
   the per-proposer entries that cast requires. Each constituent action
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
   branch), `commit_assign_*`'s the broadcast
   certificate, `finalize_commit`'s the per-proposer completeness
   (`local_committed_complete`).
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
   and the handlers and `mvba_terminate` record the decision
   (`mvba_complete`). The handlers' one enabledness leg the class does
   not give is the bridge's completeness direction — a decided entry's
   certificate is on the network, which is what "publicly verifiable"
   means; the theorem names it as `ValidBridge` ([MvbaPlan.md](MvbaPlan.md) §3).
5. *(theorem + temporal.)* The fallback commit round
   (Algorithm 5, lines 37–47 (`line:fb-mvba-decide`–`line:fb-finalize`)) carries decisions to
   finalization: once `mvba_complete` holds, a decided-positive root is
   held by a FastQC, which needs no wait, or by a FallbackQC, whose
   correct signer's `redisseminate_chunk` is enabled
   (`mvba_decided_is_proposer` + `mvba_decided_pos_chunks_decodable` +
   `mvba_decided_pos_proposer_signed`) and owed, so (F-justice) delivers
   each honest validator's assigned chunk; `cast_fb_commit` is then enabled
   (it has no phase gate); the `2f+1` honest
   commit votes are a certificate outright
   (`Chorus.fbcommitqc_of_honest_commit_votes` — the honest population
   is itself the quorum), and `fbcommitqc_implies_mvba_complete` +
   `mvba_complete_per_proposer` hand over the `commit_assign_*`
   preconditions as on the commit route.

**The assumptions:**

* **(F-justice)** — phase advancement, aggregation, and per-validator
  honest actions are weakly fair. Weak fairness suffices *because* the
  model is monotone: enabledness itself is monotone, so the
  enable/disable flicker that strong fairness exists for cannot occur.
  ((F-compassion) — strong fairness — is reserved vocabulary for the
  non-monotone implementation and is never invoked.)
* **(F-byz)** — Byzantine actions are unfair: no progress obligation is
  satisfied by adversarial help, which makes the discharged content
  strictly stronger than deadlock freedom.
* **The MVBA's scheduling** (`MvbaAdmissible`) — the run's MVBA steps,
  read as a run of the MVBA model, satisfy that model's own scheduling
  premises, so `Mvba.termination` applies to them. Its two caller premises
  are derived, not assumed: (i) *all correct validators propose* is chain
  step 4 (the per-validator implementation refinement of the build step is
  the receipt layer — §7.2, [Architecture.md](Architecture.md) §5); (ii)
  *no correct validator abandons before deciding* holds on the branch of
  the proof that needs the MVBA, where no correct validator ever finalizes:
  by the caller premise `NoAbandonBeforeFinalizing` none abandons Chorus,
  and the MVBA's `abandon()` is invoked only by Chorus's `abandon`
  (Algorithm 5, line 48 (`line:fb-abandon`)). Within Cadence the glue abandons only after
  finalizing (Algorithm 1, line 23 (`line:abandon`)).
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
else. Whether they can all hold at once is the open non-vacuity question
([TODO.md](TODO.md) § Liveness).

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
propose it, once (`mvbaInvoked`). The receipt rules are what carry the
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
entry rather than valid evidence — with `mvbaInvoked` once-only, never
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
the model depends on it: a positive vote is accepted only if it carries its
*sender's assigned* chunk (`byz_sign_vote_pos` requires
`msg_chunk_received r j m`), which is what makes
`vote_pos_quorum_implies_decodable`'s reading of `isDecoded` honest —
f+1 accepted positive votes pin f+1 *distinct* chunks.

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

* **`fbCommitQC` entries are implicit.** `msg_fbcommit_sig r` records
  that `r` broadcast a `FallbackCommitVote` (Algorithm 5, line 41 (`line:fb-commitvote`))
  without recording the signed entry vector. An honest vote is over the
  entries of the validator's MVBA decision, which the MVBA contract's
  agreement makes the same for every correct validator; a Byzantine vote on a different vector — which the
  paper's same-entries aggregation would reject — can only *add*
  certificates in the model (`fbcommitqc` over-approximates in the
  adversary's favour), and `commit_assign_*` conjoins `fbcommitqc` with
  the decision itself, so commit content is unaffected. Flagged because
  the abstraction silently leans on the MVBA's agreement: in an extension
  with several concurrent MVBA instances or an explicit view-change,
  the vector would have to become explicit.

* **Byzantine chunk delivery.** `byz_deliver_chunk` lets a Byzantine
  proposer deliver any chunk attributed to itself to any recipient,
  capturing chunk equivocation (§5).

* **`fb_sign_neg`'s witnessed quorum.** A scoped exception to the
  positive-position contract, alongside the seven self-row reads of
  `msg_proposer_signed`/`msg_commit_cast` — see §3.1 and §3.1.1.

## 9. What is left for the next iteration

These are places the model could go further. Nothing here is a gap in what
the development *claims* — see [TODO.md](TODO.md) for the cross-cutting
list, and §§10.1–10.3 below for the bigger lifts.

1. Instantiate the abstract classes of [Cadence/Primitives.lean](../Cadence/Primitives.lean) (for
   instance an example model instantiation of the whole module) to
   demonstrate satisfiability of the axioms end-to-end. `ThresholdIBE` is the
   one primitive class still without a model instance; the `MVBA` contract,
   which lives in [Cadence/Interfaces.lean](../Cadence/Interfaces.lean), has `Mvba.mvbaSafety` /
   `Mvba.mvba_of_temporal` ([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)),
   consumed by Chorus (§4).

2. Move the explicit `is_proposer` immutable relation to a derivation
   from a VRF-output relation, once a `VRF` primitive class exists in
   [Cadence/Primitives.lean](../Cadence/Primitives.lean). Epochs and proposer rotation stay out of
   scope (outside the papers' consensus-layer treatment).

3. An automated syntactic audit of the §3.1.1 positive-position
   contract. Per the 2026-08 external audit: it should *classify*
   occurrences (positive / self-row / documented exception) rather than
   merely reject — see §3.1.1.

4. An in-build reachability witness (`sat trace`) for Chorus. Blocked
   twice over today (the disabled model-check scaffolding; `decide` in
   `vote`'s bulk update); until a refactor clears both, the non-vacuity
   witness is the monitor fixture run in CI — [TODO.md](TODO.md)
   § Soundness has the full record, [Monitor.md](Monitor.md) the
   mechanism.

## 10. Bigger lifts — what would need new machinery

### 10.1 Making the network assumption explicit and proven

The async-soundness argument in §3.2–§3.3 is a **meta-level claim**: it
depends on the (M-update)+(M-frame) contract of §3.1.1, which Veil does not
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
([Liveness.md](Liveness.md) §3 points to it). Out of scope even
then: real-time / GST-style bounded delivery, and probabilistic
termination (axiomatise the randomised primitive, discharge the
probability argument on paper — the treatment the retired (A-mvba) gave
it).
