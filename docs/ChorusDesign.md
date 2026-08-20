# Chorus — Veil model design notes

*(The per-model design rationale. The top-level architecture document — with
the methods, the trust bases and the meta-assumption inventory — is
[`Architecture.md`](./Architecture.md); the entry point for the repository is
[`README.md`](../README.md).)*

This document explains the modelling choices in
[`Cadence/Chorus.lean`](../Cadence/Chorus.lean) and [`Cadence/Primitives.lean`](../Cadence/Primitives.lean):
what is in scope, what is abstracted, and what limitations the chosen
abstractions impose on the kind of properties that can be proven.

## 1. Scope

Chorus is the inner *per-slot one-shot* BFT consensus layer of Cadence. The
reference is the Cadence paper, `arXiv:2607.02275v2`; the root
[`README.md`](../README.md) gives the citation and how to resolve the label
names used below. With the source unpacked at `papers/cadence`, the Chorus
chapter is `src/p2_chorus.tex`, with pseudocode in `src/alg_proposer.tex`,
`src/alg_voting.tex`, `src/alg_fast.tex`, `src/alg_fallback.tex`,
`src/alg_da.tex`, and the MVBA module specification in `src/p2_mvba.tex`.

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
(`lemma:chorus-agreement`):

* **Fast path** (`alg:fast-path-certification`): two voting rounds
  produce a `commitQC` (2f+1 matching broadcast fast commit votes).
  A validator that holds FastQCs for every proposer may additionally
  commit *speculatively* before the commitQC forms; speculation is not
  finalization and is revertible under equivocation (see §8).
* **Fallback path** (`alg:fallback`): a third round of fallback votes
  enables the slot's MVBA instance, whose decided certificate finalizes
  the slot.

The model is **single-slot**: state and messages are not
slot-parameterised, since per-slot instances are independent. (An earlier
revision carried an explicit `slot` parameter on every relation; it was
dropped as redundant. The `slot` type is retained as a placeholder.)

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
[`Cadence/Primitives.lean`](../Cadence/Primitives.lean) `HashFunction` and `MerkleTree`).

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
`local_committed*`), and the abstract/oracle state (`mvba_decided_*`,
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
| `mvba_decided_*`, `mvba_complete` | ✓ | ✓ for honest actions' network-style reads; the oracle-internal agreement guards and `cast_fb_commit`'s post-freeze read are scoped exceptions (see below) |
| `phase : Phase` enum | (forward-only, see below) | ✓ |
| `local_entry_pos/neg`, `local_voted`, `local_path`, `local_committed*` | ✓ | ✗ |

`phase` is a 4-valued enum (`pre_deadline → post_deadline →
post_fb_arm → post_mvba_arm`); it advances only through explicit
`advance_to_*` actions whose preconditions force the forward direction.

**The `fb_sign_neg` guard.** One action deliberately deviates from pure
(M-frame): the paper's validator signs a *negative* fallback entry for
`j` exactly when, among the ≥ 2f+1 votes it received, no root has an
f+1 positive sub-quorum with decodable data (`alg:fallback`
`line:fb-cast-entry`, else-branch). A per-validator "received" set does
not exist in the monotone model, so the guard is stated relative to a
*witnessed* supermajority `qv` of broadcast votes (the action's
parameter): `∀ M q, ¬(q ⊆ qv ∧ q positive-signs M ∧ …)`. The negation
ranges over the witnessed subset only, so a validator may still
negative-sign although a positive quorum exists outside `qv` — the
behaviours asynchrony makes real are retained (the abstraction stays
conservative). This replaces an earlier guard that negated over the
*global* signature state, which excluded real behaviours.

**The `cast_fb_commit` decided-vector read (added 2026-07-07 with the
fallback commit round).** The commit-round action universally
quantifies over the decided entries
(`∀ J M, is_proposer J → mvba_decided_pos J M → msg_chunk_received i J M`),
i.e. consults `mvba_decided_pos` on the left of an implication.
`mvba_decided_*` is not a network relation (category (A) oracle state,
§3.5) and the read is sound: the action also requires `mvba_complete`,
after which the decided vector is *frozen* (`mvba_decide_*` require
`¬ mvba_complete`), and the real validator holds the complete vector
`B'` from its single `decide(B')` delivery — the paper's handler
enumerates exactly this frozen, locally-known object
(`line:fb-commit-foreach`). Growth of the decided set can therefore
never disable the action at any state where it is enabled. (The
oracle's own agreement/integrity guards in `mvba_decide_*` likewise
consult prior decisions negatively; both are oracle-internal semantics,
not honest observations of network absence.)

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
disable these guards. (Recorded explicitly after the 2026-08 external
audit, whose re-run of this hand audit found the two relations
previously mis-tabled as pure (M-frame) ✓.)

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

> Actions in `Cadence/Chorus.lean` must consult the **network relations**
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

(The hand audit's third carve-out — `cast_fb_commit`'s frozen
decided-vector read, listed alongside these two in `Architecture.md`
§4 item 1 — consults *oracle* state, not a network relation, so it
sits outside this contract's scope; §3.1 documents it.)

The robust semantic formulation is *action monotonicity w.r.t. network
tuples produced by other participants*: adding such tuples to the
pre-state should never disable an action nor change its update
behaviour. The self-row reads satisfy this through the writer
condition — only the acting validator's own firing adds the tuple the
guard consults — and `fb_sign_neg` deviates knowingly: a larger
pre-state can disable the action for a given `qv` exactly as more
received votes can in the real protocol. When adding or modifying an
action, audit it against this contract. A future improvement (tracked
in [`TODO.md`](./TODO.md) § Soundness and as §9 item 3 below) is an
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
(`prop:agreement-entries`) is asynchronous: two commitQCs agree by
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
  reverted only under equivocation" is stated relative to the
  `no_equivocation` state predicate.

### 3.4 What is omitted

* **Message delivery order** — any signature, once produced, is visible
  to any action that wishes to consume it. This subsumes the worst
  case of an adversarial scheduler.
* **Timeouts as such** — timing is only the four-valued `Phase` enum,
  advancing non-deterministically in order. This is enough to express
  preconditions like "fallback entries are signed at or after the
  fallback arm" without committing to a clock model.
* **The Conductor layer** — Chorus is one slot. Pipelining via the
  Conductor and the `participate()`/`abandon()` interface through which
  Cadence drives slot instances are out of scope *of this module*; they
  are modelled separately in [`Cadence/Conductor.lean`](../Cadence/Conductor.lean) and
  [`Cadence/Cadence.lean`](../Cadence/Cadence.lean) against the module contracts of
  [`Cadence/Interfaces.lean`](../Cadence/Interfaces.lean) (see
  [`ConductorDesign.md`](./ConductorDesign.md) and those files' headers).
* **`FastBlock` dissemination/adoption** (`alg:fast-path-certification`,
  FastBlock handler) — the paper broadcasts a formed fast meta-block so
  peers can adopt `Ev(pid) ← B(pid)` without re-aggregating. In the
  monotone model a certificate exists iff its backing signatures do, so
  adoption and re-aggregation coincide: `aggregate_fastqc_*` covers
  both.
* **DA re-encode consistency check** (`alg:da` `line:da-reencode`) —
  after decoding `f+1` chunks the paper re-encodes and compares the
  root, marking inconsistent roots `invalid`. With `merkle_root` opaque
  we cannot model this, so "`f+1` chunks for root `m`" is taken as
  decodable. A Byzantine proposer can thus deliver `f+1`
  mutually-inconsistent chunks the real DA would reject. This weakens
  the DA-decodability auxiliaries (`*_decodable`) but not agreement
  (the paper's `prop:recovery-consistency` guarantees all honest
  validators reach the *same* verdict on such a root, which is the part
  agreement needs; the model inherits it through root-opacity), and not
  proposal inclusion (an on-time honest proposer's proposal is
  correctly encoded, so its re-encode check always passes — the paper's
  `prop:honest-positive-entry` argument says exactly this).

  The abstraction **is load-bearing for the speculative-finality
  properties** (`speculative_agreement_pos`,
  `speculative_agreement_pos_neg`), and this is a *scope* caveat on
  what those two theorems mean. The paper admits an honest fallback-no
  cast after gathering `f+1` yes votes on a root whose chunks fail to
  re-encode (the parenthetical closing the "Safety of speculative
  finalization" paragraph, `subsection:chorus-proof`) — a culprit case
  that involves **no equivocation**, only an invalidly encoded root. In
  the model that case cannot arise: `fb_sign_neg`'s guard forbids a
  negative entry whenever an `f+1` positive sub-quorum with decodable
  data exists within the witnessed quorum, which — via
  `vote_pos_quorum_implies_decodable` — collapses to "no `f+1` positive
  sub-quorum", the fact `fb_neg_qv_no_pos_quorum` and the keystone
  `fb_neg_no_pos_quorum` record and the speculative properties consume.
  Transported to the real protocol, the speculative properties
  therefore hold under the paper's full "proposer is the culprit"
  hypothesis — no equivocation **and** no invalidly encoded root — not
  under `no_equivocation` alone. Closing this at the model level (a
  `well_encoded` predicate on roots, required by honest `propose` and
  consulted by `fb_sign_pos`/`fb_sign_neg`, with the speculative
  hypothesis extended to match) is §9 item 4. Surfaced by the 2026-08
  external audit (Finding 1).

## 3.5 State locality contract

Every state item in [`Cadence/Chorus.lean`](../Cadence/Chorus.lean) falls into one of
four categories. The category determines what it **stands for** in the
real protocol and what part of the soundness argument lifts it back to
the asynchronous-network world.

### (N) Network state — broadcast, globally visible

Signed messages observed on the gossip overlay. Under the monotone
idealisation of §3.1 they become globally visible the moment they
exist. Naming convention: `msg_*`.

| Relation | Paper analogue |
|---|---|
| `msg_proposer_signed j m` | outer chunk-header signature `σ` on `⟨s, j, mroot⟩` (`alg:proposer-dissemination`). |
| `msg_chunk_received i j m` | the chunk **assigned to validator `i`** has reached `i` (proposer unicast, vote-carried, fallback re-dissemination `line:fb-redisseminate`, or commit-round broadcast `line:fb-commit-wait`; the receive-time rebroadcast `line:da-rebroadcast`, a v1 rule, was removed in v2 — chunk redistribution is now vote-carried, matching this model's `vote_pos_sig_chunk` chain). The **only** per-recipient network relation — see §3.5.1. |
| `msg_vote_pos_sig r j m`, `msg_vote_neg_sig r j` | per-proposer signed entries of the `Vote` broadcast (`alg:voting`). |
| `msg_vote_cast r` | `r` has broadcast its `Vote` (`line:vote-broadcast`). Receivers discard votes without an entry per proposer, so a cast vote implies per-proposer signatures (`vote_cast_entries`). |
| `msg_fb_pos_sig r j m`, `msg_fb_neg_sig r j` | per-proposer signed fallback entries in the `FallbackVote` broadcast (`alg:fallback`). |
| `msg_fallback_sig r` | the `σ_r` on `⟨fallback, s⟩` in the `FallbackVote` broadcast. |
| `msg_commit_pos_sig r j m`, `msg_commit_neg_sig r j` | per-proposer signature inside the `CommitVote` (`alg:fast-path-certification`). |
| `msg_commit_cast r` | `r` has broadcast its `CommitVote` (`line:fast-commitvote`). Only broadcast commit signatures count toward a commitQC. |
| `msg_decrypt_share r` | the extraction share released with `r`'s `Vote`. |
| `msg_fbcommit_sig r` | `r`'s `FallbackCommitVote` broadcast (`line:fb-commitvote`). The entry vector it signs is implicit — an honest vote is over the MVBA-decided entries, unique by oracle agreement; see the relation's comment in `Cadence/Chorus.lean` for why this over-approximates only the adversary. |

The contract from §3.1.1 applies to all of these.

### (D) Derived certificates — ghost relations

Transferable certificates are definitional predicates over (N):
`vote_quorum_pos/neg` (FastQC certificates), `fb_quorum_pos/neg`
(FallbackQCs), `equiv_evidence` (EquivCert — the proposer's signatures
on two distinct roots), `fbcert` (FBCert), `commitqc_pos/neg`
(commitQC validity), `fbcommitqc` (fbCommitQC — `2f+1` fallback commit
votes, `line:fb-formcommitqc`), `chunk_quorum` (`isDecoded`),
`slot_key_released` (f+1 extraction shares),
`complete_fast_metablock` / `mvba_invoked` (MVBA proposal triggers),
plus the hypothesis predicates `no_equivocation` and
`all_honest_recorded`. A certificate "exists"
iff its aggregated signatures are observable — which matches the
protocol, where any holder of the signatures (honest or Byzantine)
can assemble the certificate and any receiver can verify it. Nothing
needs to *own* a transferable certificate, so they carry no validator
index.

One certificate additionally has an *assembled-and-broadcast* network
form: `msg_commitqc_pos/neg` (category (N)), set by the
`broadcast_commitqc_*` actions whose precondition is exactly the
certificate's validity check (`alg:fast-path-certification`
`line:fast-broadcast-commitqc`). Finalization (`commit_assign_*`)
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
| `local_entry_pos i j m`, `local_entry_neg i j` | validator `i`'s per-proposer `Entry(pid)` (`alg:voting`). |
| `local_voted i` | `i` has executed the deadline vote handler. |
| `local_path i : PathChoice` | `i`'s `pathVote ∈ {none, fast, fallback}`. |
| `local_fastqc_pos i j m`, `local_fastqc_neg i j` | `i` has aggregated `Ev(j)` as a FastQC (`line:fast-formqc`). Kept per-validator (unlike the transferable certificates) because an honest commit signature is justified by *the signer's own* FastQC observation. |
| `local_committed i`, `local_committed_pos i j m`, `local_committed_neg i j` | `i`'s finalization decision. |
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
| `mvba_decided_pos j m`, `mvba_decided_neg j` | per-proposer projection of the MVBA's decided meta-block (`mod:mvba`). MVBA agreement makes a single global view sound. |
| `mvba_complete : Bool` | the MVBA instance has decided every entry. |

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
  discard unbacked positive entries (`alg:fast-path-certification`,
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
"`recoverProposals` does not block" (`alg:da` `line:da-wait`).

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

[`Cadence/Primitives.lean`](../Cadence/Primitives.lean) declares type classes that state
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
(`p2_chorus.tex` §`appendix:encryption`) — is axiomatised as
`ThresholdIBE.decrypt_secret`: decryption succeeds only with a
threshold of correct shares. The protocol layer is proven in the model:
`safety [hiding_until_deadline]` shows the share threshold cannot be
reached while the slot is `pre_deadline`, because at most `f` shares
are Byzantine and honest validators release shares only with their
deadline vote.

### MVBA as an oracle

The MVBA primitive (`mod:mvba`, `p2_mvba.tex`) is modelled as three
mutable relations (`mvba_decided_pos/neg`, `mvba_complete`) populated
by three oracle actions. Its correctness properties are *not*
axiomatised via Veil `assumption`s (those may only refer to immutable
parameters); they are baked into the `require` clauses of
`mvba_decide_*` and lifted to invariants:

* **Agreement** — per-proposer: no decision contradicts a prior
  decision (`mvba_decided_pos_unique`, `mvba_decided_pos_neg_excl`).
* **External validity** — a decided entry is backed by a *publicly
  verifiable certificate*: a FastQC-shaped entry needs a `2f+1` vote
  quorum (`vote_quorum_pos/neg`); a fallback-shaped entry (FallbackQC
  or EquivCert) additionally needs `fbcert`, because only fallback
  meta-blocks may carry such entries and every valid fallback
  meta-block includes `FBCert` (§`subsection:fallback_path`). The
  evidence conditions are deliberately certificate-checkable network
  predicates — *not* conditions on honest validators' internal state —
  because the MVBA can only verify what a proposal carries. (An
  earlier revision instead required MVBA decisions to be consistent
  with every honest validator's aggregated FastQCs — a
  non-implementable oracle gate, then documented as a "model fidelity
  concession". It is gone: with commitQC-based finalization the
  paper's own asynchronous agreement argument goes through, see §6.)

**Two invocation triggers.** The paper invokes MVBA under two triggers
(`alg:fallback`): the fallback trigger — `|M_i| ≥ 2f+1` fallback votes,
whose monotone-network shadow is `fbcert` — and the case-(a) trigger — a
complete fast meta-block held at the MVBA arm. Both are modelled: the
oracle actions require `mvba_invoked = fbcert ∨ (∃ honest I,
complete_fast_metablock I)`. The case-(a) trigger is load-bearing for
liveness in the *mixed* regime where between 1 and 2f honest validators
took the fast path — there neither a commitQC nor an FBCert is
guaranteed, and termination flows through MVBA proposals of fast
meta-blocks (see §7).

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
  chunk are discarded (`alg:fast-path-certification`, receive handler);
* `byz_cast_vote` requires a signed entry per proposer — incomplete
  votes are discarded;
* `byz_sign_fb_pos` requires `msg_proposer_signed j m` — the positive
  fallback entry carries the proposer signature `σ_p`, which receivers
  verify.

These preconditions do not weaken the adversary: they exclude only
messages that could never influence an honest participant.

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

The `ByzNodeSet` class provides, and its `byzNodeSetFin` instance
proves (`Veil/Frontend/Std.lean`), the counting facts the proofs use:

* `supermajorities_intersect_in_honest` — two supermajorities share an
  honest member (`2(2f+1) − (3f+1) = f+1 > f`).
* `greater_than_third_one_honest` — an `f+1`-set contains an honest
  member.
* `supermajority_contains_honest_greater_than_third` — a supermajority
  contains an *all-honest `f+1`-subset* (`2f+1 − f = f+1`). Used where
  an honest sub-quorum is needed (e.g. pinning fallback entries under
  the proposal-inclusion premise).
* `supermajority_greater_than_third_intersect` — a supermajority and an
  `f+1`-set share a (possibly Byzantine) member
  (`(2f+1) + (f+1) − (3f+1) = 1`). Used by the speculative-safety
  argument, whose per-member consistency comes from `no_equivocation`
  rather than honesty.
* `supermajorities_intersect_in_greater_than_third` — two
  supermajorities share an `f+1`-subset. Used to intersect a
  fallback signer's witnessed vote quorum with a FastQC's backing.

Note the *honest* variant of the fourth fact — "a supermajority and an
`f+1`-set share an honest member" — is false in general (the single
guaranteed intersection element can be Byzantine); the speculative
invariants work around it via `no_equivocation`.

## 6. Invariants

Grouped by purpose. See `Cadence/Chorus.lean` for the statements; this is a map.

### 6.1 Safety properties

| Property | Paper analogue |
|---|---|
| `agreement_pos`, `agreement_pos_neg` | Agreement (`lemma:chorus-agreement`), at the granularity of per-proposer committed entries. |
| `integrity_pos`, `integrity_pos_neg` | per-validator commit integrity. |
| `hiding_until_deadline` | Hiding (`lemma:chorus-hiding`), protocol layer: the slot key is not reconstructible pre-deadline. |
| `proposal_inclusion`, `proposal_inclusion_no_neg` | Proposal inclusion (`lemma:chorus-proposal-inclusion`), relative to the premise `all_honest_recorded`. |
| `speculative_agreement_pos`, `speculative_agreement_pos_neg` | the speculative-finality claim (`p1_informal.tex`), relative to `no_equivocation`. |

Slot safety (`lemma:chorus-slot-safety`) is trivial in the single-slot
model; termination is §7.

**Verification note.** Most obligations discharge automatically; eleven
VCs — those needing one or two explicit `ByzNodeSet` counting-axiom
instantiations against witnessed quorums, at actions with bulk or
quorum-completing updates — are discharged by manual `@[veil]` theorems
at the end of `Cadence/Chorus.lean` (Veil's interactive-discharger mechanism).

**How agreement is proven (the paper's `prop:agreement-entries`).**
`local_committed_pos_backed` reduces every honest commit to a
`commitqc_pos` or an `mvba_decided_pos`. Case commitQC–commitQC:
`supermajorities_intersect_in_honest` + `commit_pos_sig_unique`. Case
MVBA–MVBA: the oracle's agreement requires. Case commitQC–MVBA
(`commitqc_pos_mvba_consistent` and the two exclusion variants): by
`mvba_decided_pos_backed`, the decision carried either a vote
supermajority — which intersects the commitQC's honest member's own
FastQC backing in an honest double-voter (`vote_unique_pos`) — or a
fallback certificate together with `fbcert` — which intersects the
commitQC in an honest validator with both `msg_commit_cast` and
`msg_fallback_sig`, contradicting the `pathVote` exclusion
(`commit_cast_fallback_sig_excl`). Pure quorum reasoning, valid under
full asynchrony.

*Correspondence note (2026-07-07 revision).* The paper's restructured
`prop:agreement-entries` argues the fallback cases through the *commit
round*: two `fbCommitQC`s intersect in an honest commit-voter, who
commit-votes once, for the entries of its single MVBA decision (MVBA
Integrity); an `fbCommitQC` and a `commitQC` intersect as in case 3
above. The model reaches the same conclusion one layer lower: its
fallback finalization route (`fbcommitqc ∧ mvba_decided_*`,
`commit_assign_*`) consumes the *decision* directly, and decision
agreement is baked into the oracle — so the model's proof does not need
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
`fb_sig_phase`, `mvba_decided_phase`, `fbcommit_sig_phase`,
`mvba_complete_phase` — every protocol artefact postdates the landmark
that produces it; used by `hiding_until_deadline` and by the
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

### 6.4 MVBA correctness lifted

`mvba_decided_pos_unique`, `mvba_decided_pos_neg_excl`,
`mvba_decided_pos_backed`, `mvba_decided_neg_backed`,
`mvba_decided_phase`, `mvba_complete_per_proposer`,
`mvba_decided_pos_proposer_signed`. The `*_backed` invariants persist
the external-validity evidence a decision carried; they are what keeps
the commitQC-consistency family inductive when commit votes are cast
*after* a decision. `mvba_decided_pos_proposer_signed` materialises one
consequence (a decided-positive root is proposer-signed) so the
commit-round VCs need not re-derive it.

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
`fb_neg_qv_backed`, and (relative to `no_equivocation`)
`fb_neg_qv_no_pos_quorum` — together the persistent residue of
`fb_sign_neg`'s witnessed-quorum guard, anchored on the
`local_fb_neg_qv` history variable — plus `fb_neg_no_pos_quorum`,
`spec_fastqc_pos_no_mvba_neg`, `spec_fastqc_pos_mvba_pos_unique`.

### 6.7 Fallback commit round (added 2026-07-07)

`fbcommit_sig_backed` (an honest commit vote postdates the decision
vector it signs — `line:fb-mvba-decide` precedes `line:fb-commitvote`),
`fbcommit_sig_phase` and `mvba_complete_phase` (filed under the phase
timestamps, §6.2), `fbcommitqc_implies_mvba_complete` (an `fbCommitQC`
certifies the decision vector: its `2f+1` votes contain an honest one),
and `mvba_decided_pos_proposer_signed` (filed under §6.4). Together
with `mvba_decided_pos_chunks_decodable` and `mvba_decided_is_proposer`
these are the backing and fair-progress content of the commit round —
see the "Commit-round epilogue" in §7 and the invariant block's header
comment in `Cadence/Chorus.lean`.

## 7. Liveness

The *fair-progress layer* in [`Cadence/Chorus.lean`](../Cadence/Chorus.lean) (section
"Liveness — meta-argument and fair-progress invariants") encodes the
safety content of the classical verification-diagram liveness argument
(cf. McMillan, *"Toward Liveness Proofs at Scale"*, CAV 2024): in every
reachable non-terminal state, some **fairly-scheduled** action is
enabled — strictly stronger than deadlock freedom, since Byzantine
actions are unfair and cannot satisfy the obligation. The temporal
layer is stated as meta-axioms:

* **(F-justice)** — phase advancement, aggregation, and per-validator
  honest actions are weakly fair. (Strong fairness — (F-compassion) —
  is reserved vocabulary for the non-monotone implementation; in the
  monotone model enabledness is itself monotone, so weak fairness
  suffices.)
* **(F-byz)** — Byzantine actions are unfair.
* **(A-mvba)** — once `mvba_invoked` holds and certificate evidence
  exists per proposer, the MVBA eventually decides every proposer and
  terminates (probability-1 termination of the randomised primitive is
  a paper-level argument). This stands in for `mod:mvba`'s
  `ℓ_MVBA`-Termination, whose premise since the 2026-07-07 revision is
  (i) *all correct validators propose* — the per-validator
  implementability content behind the §7.2 finding, bridged from this
  model's network-global evidence premise by the atomic-build argument
  (mechanised separately in the receipt layer, `Architecture.md` §5) — and
  (ii) *no correct validator
  abandons before the bound* — moot in this single-slot model (no
  `abandon()`), discharged within Cadence by Conductor totality
  (`cor:chorus-correctness-within-cadence`).

The well-founded ranking is structural: per-slot state is finite and
all relations are monotone, so the residual count of unset tuples
decreases with every helpful firing. The (D) obligation of the
verification diagram is therefore discharged by the monotonicity audit,
not by SMT; stating it as invariants yields only tautologies of the
form `… ∧ ¬X → ¬X`, so do not add them back.

**Case split** on the number `x` of honest validators that cast a fast
commit vote:

* `x ≥ 2f+1`: honest commit votes agree per proposer (FastQC
  cross-uniqueness), so a commitQC forms from honest votes alone;
  everyone commits via `commit_assign_*` (F-justice).
* `1 ≤ x ≤ 2f` (mixed): neither commitQC nor FBCert is guaranteed
  (Byzantine help is unfair; only `2f+1 − x` honest validators can
  still fallback-vote). The paper's case-(a) MVBA trigger closes this
  regime: any fast-path validator's FastQCs are backed by
  network-visible vote supermajorities
  (`fast_path_implies_vote_quorums`), every honest validator eventually
  aggregates a complete fast meta-block, `mvba_invoked` holds, evidence
  exists per proposer (`fastqc_complete_implies_mvba_evidence`), and
  (A-mvba) delivers the complete decision vector.
* `x = 0`: all `≥ 2f+1` honest validators eventually cast fallback
  votes (per-proposer fallback signing is always enabled one way or the
  other — `progress_fallback_signing`), `fbcert` forms, and (A-mvba)
  delivers the decisions, given per-proposer evidence — see the
  pigeonhole below.

**Commit-round epilogue (both MVBA branches, added 2026-07-07).**
Decisions no longer finalize directly: the fallback commit round
(`line:fb-mvba-decide`–`line:fb-finalize`) sits in between. Its
fair-progress content is materialised by the appended invariant block in
`Cadence/Chorus.lean` ("Fallback commit round — backing, confinement, and fair
progress"): once `mvba_complete` holds, `redisseminate_chunk` is enabled
for every decided-positive root (`mvba_decided_is_proposer` +
`mvba_decided_pos_chunks_decodable` + `mvba_decided_pos_proposer_signed`)
and delivers each honest validator's assigned chunks (F-justice), after
which `cast_fb_commit` is enabled (`mvba_complete_phase` closes the
phase leg); `2f+1` honest commit votes form `fbcommitqc` (the honest
population is a supermajority — the same meta-level counting step the
`FBCert` formation in the `x = 0` branch already uses), and
`fbcommitqc_implies_mvba_complete` + `mvba_complete_per_proposer` hand
over the `commit_assign_*` preconditions exactly as in the pre-round
argument.

**Evidence pigeonhole (mechanised 2026-07-07).** In the `x = 0`
branch, the `2f+1` honest fallback entries for a proposer split as: an
f+1 negative sub-quorum (a negative FallbackQC), or an f+1 positive
sub-quorum on one root (a positive FallbackQC), or positive entries on
two roots — whose backing vote quorums pin two proposer-signed roots,
i.e. `equiv_evidence`. This split-counting partitions a quorum by the
value its members signed, which is outside the `ByzNodeSet` language
(no set comprehension), so it is not SMT-discharged in the invariant
clump — but it is no longer a meta step: the theorem
`Chorus.evidence_pigeonhole_of_reachable`
([`Cadence/Chorus/Pigeonhole.lean`](../Cadence/Chorus/Pigeonhole.lean)) proves exactly
this split-counting over reachable states, for every `n = 3f+1` and
any Byzantine set of size `≤ f` (the concrete instance family — the
abstract `ByzNodeSet` axioms cannot express the counting, which is why
the step used to be meta): from a supermajority of honest per-proposer
fallback entries, `fb_quorum_pos`/`fb_quorum_neg`/`equiv_evidence`
follows, via the `two_cover` pigeonhole and the
`msg_fb_pos_sig_backed → vote_pos_from_local → local_entry_pos_signed`
chain over the named reachability projections. The remaining meta
content of the fair-progress argument is only the temporal glue
((F-justice)/(F-byz)/(A-mvba)).

### 7.1 Limitations of the current encoding

The temporal/fairness layer (fair executions, the ranking recursion)
is not encoded inside Veil. Phase markers never *must* advance; the
network has no GST marker; MVBA termination is an oracle. The
discharged invariants are the safety content only.

Nor is *aggregation enablement* invariant-checked: `aggregate_fastqc_*`
and the other aggregation actions enable on the existence of `2f+1`
honest signatures, and whether such a quorum ever accumulates is a
quorum-availability question about participation and partial synchrony.
(A-mvba) absorbs it — assuming quorum availability the MVBA terminates,
and `mvba_complete_per_proposer` closes the chain to `committed I S`. A future extension would internalise the
meta-axioms via an L2S desugaring (sketched in
[`Liveness.md`](./Liveness.md)) or a verification-diagram tactic
family. Safety properties are unaffected by all of this: they hold in
every reachable state regardless of scheduling.

### 7.2 Confirmed paper-side bug behind (A-mvba) — EquivCert harvest omission (2026-07-06; fixed upstream 2026-07-07)

An external report (independently re-verified against the LaTeX sources
in `papers/cadence`, 2026-07-06) shows that **(A-mvba) is not
implementable by the paper's pseudocode as written**. The bug is a
liveness/termination bug in `alg_fallback.tex`; safety is unaffected.

**The bug.** The `FallbackVote` receive handler accepts a carried
EquivCert as valid evidence but never harvests it into `Ev(pid)` — the
harvest rules cover only received FastQCs and FallbackQCs
(`alg_fallback.tex`, the two harvest loops after `M_i ← M_i ∪ {m}`).
The MVBA-propose rule then fires unconditionally on `|M_i| ≥ 2f+1`
with a once-only `mvbaInvoked`, so its comment "by the rules above,
every `Ev(pid)` is a FastQC, FallbackQC, or EquivCert" is false.
Counterexample (n = 4, f = 1): Byzantine proposer/validator D
equivocates roots `r1 ≠ r2`; honest A holds a positive fallback signed
entry for `r1`, honest C a negative one; A receives {A's vote, C's
vote, D's vote carrying EquivCert(r1,r2)} before honest B's `r2` vote.
At `|M_A| = 3 = 2f+1` neither local-formation rule is enabled (one
bare positive, one bare negative, one non-signed-entry EquivCert), so
A proposes a meta-block whose entry for D is a *bare* fallback signed
entry — not a valid fallback meta-block
(`p2_chorus.tex` §`subsection:fallback_path`) — and, `mvbaInvoked`
being once-only, never re-proposes when B's vote later arrives. Since
`mod:mvba`'s `ℓ_MVBA`-termination presumes all correct validators
propose *valid* meta-blocks, the paper's claims "B is valid by
construction" and the termination-proof step "assembled a valid
meta-block and proposed it" (`prop:chorus-finalization-time`) are
unsupported, and `lemma:chorus-termination` inherits the gap.

**Why this model cannot see it.** The propose step and the
per-validator `Ev`/`M_i` state are exactly the "visibility plumbing"
the monotone network abstracts away (§8, "EquivCert is the pair of
proposer signatures"): here `equiv_evidence j` holds the moment the
proposer has signed two roots, the MVBA is an oracle deciding from
network-global certificates, and (A-mvba)'s premise is *global*
evidence existence. The real MVBA's premise is *per-validator*: every
correct validator must assemble locally-held certified evidence into
its proposal. The paper's harvest rules are the intended bridge from
the former to the latter, and the report shows that bridge is broken.
Note the counting asymmetry that makes the omission load-bearing: the
evidence pigeonhole of §7 splits the `2f+1` *honest* fallback entries
globally, but a validator's `M_i` guarantees only `f+1` honest votes —
closing the argument per-validator requires counting the Byzantine
votes' entries too, i.e. harvesting carried certificates *including
EquivCerts*.

**Resolution (2026-07-07).** Fixed upstream and published as
**`arXiv:2607.02275v2`**, so the before/after is a public diff:
`arxiv.org/e-print/2607.02275v1` against `…v2`, where `alg_fallback.tex`
carries both changes below.

* *Receipt restriction* (`line:fb-accept`): a fallback vote is accepted
  only if every carried entry is a valid FastQC or the **sender's own**
  valid fallback signed entry, one vote counted per sender. Carried
  FallbackQCs/EquivCerts are gone from the wire format; the receipt
  rule harvests FastQCs only (`line:fb-harvest`), and the `Ev` chain
  shrinks to `⊥ →` own signed entry `→ FastQC` (`alg_fast.tex`).
* *Atomic build at propose time*
  (`line:fb-build-entry`–`line:fb-formqc`): the standing
  FallbackQC/EquivCert formation rules are deleted; when
  `|M_i| ≥ 2f+1` fires, the meta-block is assembled per proposer
  directly from `M_i` — FastQC if harvested, else EquivCert from two
  conflicting positive entries, else a FallbackQC from `f+1` matching
  entries. The counting argument (if neither of the first two cases
  applies, the `2f+1` bare entries span at most two values — one root
  and `⊥` — so one value has `f+1` matching copies) is now inline in
  the paper (§`subsection:fallback_path`, meta-block paragraph) and
  spelled out in the `M+3Δ` step of `prop:chorus-finalization-time`.

Against v2 the counterexample above is dead — the EquivCert-carrying
vote is rejected at `line:fb-accept`, every variant of D's own entry
feeds one of the three build cases, and the upgrade/propose race is
structurally eliminated (no standing upgrade rules remain). "`B` is
valid by construction" is a proved statement.

**Which half of the fix is load-bearing:** the atomic build alone is
not enough. Without the receipt restriction a validator still *accepts*
carried EquivCerts without counting them, leaving the counting hole
open; it is the restriction at `line:fb-accept` that closes it. The
algorithm description in the paragraphs above is the v1 one, retained
as the record of the finding.

**Mechanised:**
[`Cadence/FallbackReceipt/PreFix.lean`](../Cadence/FallbackReceipt/PreFix.lean)
reproduces the counterexample above mechanically (a model-checker
violation at `n = 4, f = 1` whose trace is exactly this scenario), and
[`Cadence/FallbackReceipt.lean`](../Cadence/FallbackReceipt.lean) verifies the shipped
design ("valid by construction" by SMT for all `n`; the per-validator
counting argument exhaustively at `n = 4, f = 1`).

The v2 revision that fixed this also reshaped the surrounding
machinery — the MVBA module interface (§`mod:mvba`), the fallback
commit round (§6.7), and an explicit participation convention. The
model tracks all three, and no proven safety invariant of it is
contradicted by any of them. One v2 guard is worth naming because the
model depends on it: a positive vote is accepted only if it carries its
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
  on `no_equivocation`, matching the paper's revertibility claim.

* **TIBE / encrypted payload.** Payload bytes are not modelled.
  `msg_decrypt_share` and the `slot_key_released` ghost capture the
  share-release discipline; `hiding_until_deadline` is the protocol
  half of hiding, `ThresholdIBE` in
  [`Cadence/Primitives.lean`](../Cadence/Primitives.lean) the cryptographic half.

* **EquivCert is the pair of proposer signatures.** `equiv_evidence j`
  holds iff the proposer signed two distinct roots — the content of
  the certificate `⟨equiv, s, j, ρ₁, σ_{p,1}, ρ₂, σ_{p,2}⟩`. The
  fallback votes through which an implementation *observes* the two
  signed roots are visibility plumbing the monotone network abstracts
  away. This abstraction is where the paper-side liveness bug of §7.2
  hid (received EquivCerts were dropped by the harvest rules — a
  failure of the observation step this model cannot express). Since
  the 2026-07-07 paper revision the abstraction is *aligned* rather
  than merely benign: fallback votes carry only FastQCs or the
  sender's own signed entry — exactly this model's
  `msg_fb_pos_sig`/`msg_fb_neg_sig` vocabulary — and EquivCerts /
  FallbackQCs exist only as objects assembled at propose time from the
  signed entries in `M_i`, i.e. the paper itself now treats these
  certificates as derived from network-visible signatures, which is
  precisely the ghost-relation view here.

* **`fbCommitQC` entries are implicit.** `msg_fbcommit_sig r` records
  that `r` broadcast a `FallbackCommitVote` (`line:fb-commitvote`)
  without recording the signed entry vector. An honest vote is over the
  validator's single MVBA decision, which oracle agreement makes
  globally unique; a Byzantine vote on a different vector — which the
  paper's same-entries aggregation would reject — can only *add*
  certificates in the model (`fbcommitqc` over-approximates in the
  adversary's favour), and `commit_assign_*` conjoins `fbcommitqc` with
  the decision itself, so commit content is unaffected. Flagged because
  the abstraction silently leans on oracle agreement: in an extension
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
the development *claims* — see [`TODO.md`](./TODO.md) for the cross-cutting
list, and §§10.1–10.3 below for the bigger lifts.

1. Instantiate the abstract classes of `Cadence/Primitives.lean` (e.g. an
   example `ByzNodeSet` model instantiation of the whole module) to
   demonstrate satisfiability of the axioms end-to-end.

2. Move the explicit `is_proposer` immutable relation to a derivation
   from a VRF-output relation, once a `VRF` primitive class exists in
   `Cadence/Primitives.lean`. Epochs and proposer rotation stay out of
   scope (outside the papers' consensus-layer treatment).

3. An automated syntactic audit of the §3.1.1 positive-position
   contract. Per the 2026-08 external audit: it should *classify*
   occurrences (positive / self-row / documented exception) rather than
   merely reject — see §3.1.1.

4. Model the DA re-encode consistency check: an immutable
   `well_encoded` predicate on roots, required by honest `propose`
   (and, per the paper, by `fb_sign_pos`) and consulted by
   `fb_sign_neg`, with the speculative-finality hypothesis extended
   from `no_equivocation` to the paper's full culprit set ("no
   equivocation and no invalidly encoded root") — see §3.4. Until then
   the speculative properties carry the §3.4 scope caveat.

5. An in-build reachability witness (`sat trace`) for Chorus. Blocked
   twice over today: the trace pipeline needs the model-check
   scaffolding's label enumeration, which this model disables for its
   O(n^k) elaboration cost over ~38 actions, and `vote`'s bulk update
   uses `decide (…)`, which the trace pipeline cannot translate. Until
   a refactor clears both, the non-vacuity witness is the monitor
   fixture run in CI — [`TODO.md`](./TODO.md) § Soundness has the full
   record, [`Monitor.md`](./Monitor.md) the mechanism.

## 10. Bigger lifts — what would need new machinery

### 10.1 Making the network assumption explicit and proven

The async-soundness argument in §3.2–§3.3 is currently a **meta-level
claim**: it depends on the (M-update)+(M-frame) contract of §3.1.1,
which Veil does not enforce. We would much rather have the simulation
be a *theorem in the system*. Two avenues:

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

See §7.1. A concrete extension proposal — ω-acceptance annotations on
actions, discharged via a liveness-to-safety (L2S) reduction reusing
the existing safety-VC machinery — is sketched in
[`Liveness.md`](./Liveness.md). Out of scope even then: real-time /
GST-style bounded delivery and probabilistic termination (axiomatise
the randomised primitive, discharge the probability argument on
paper — the current (A-mvba) treatment).
