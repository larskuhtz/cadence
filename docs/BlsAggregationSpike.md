# Spike: BLS aggregation and adversarial key relations

*Research note, 2026-09-24. Not a specification and not machine-checked; the
open items it produced are tracked in [`docs/TODO.md`](./TODO.md).*

**Question.** Chorus keeps certificates small by aggregating BLS signatures
(proof-of-possession variant, one bitmask of signers per certificate). The
model's attacker cannot forge signatures. With proof-of-possession an
attacker still chooses the secret keys of the validators it controls, so it
can build *relations* among those keys: a set whose public keys sum to the
identity (the "splitting zeros" trick on Ethereum), or two different sets
with the same aggregate key. The note asks three things:

1. Which attacks does that enable?
2. Which perimeter defences exclude whole classes of them, with an argument
   that the exclusion is complete?
3. Can the project model them, and what would that cost?

## 0. Bottom line

* **The stated safety properties are not attacked.** They include agreement,
  proposal inclusion, hiding and speculative safety. Every safety argument
  in the models reads a certificate only as "its honest members signed this
  message, and there are enough members". The proof-of-possession scheme
  guarantees exactly that for any keys the adversary picks (§1). A certificate
  that one honest validator accepts and another rejects only *removes*
  behaviour. The monotone model already covers that, because it never forces
  anyone to act on a certificate (§2.1).
* **The attacks are elsewhere.** An attacker can stall the slot by getting
  honest validators to disagree about validity, which breaks the liveness
  premise `ValidBridge`. It can get honest aggregators blamed, which is the
  MonadBFT pattern. It can exploit certificate byte-malleability (dedup,
  identity, randomness). And it can take unearned credit in bitmask-based
  accounting (§2.2, §2.3). Most of these need **no key relation at all**: two
  colluding keys already make an aggregate valid whose parts are invalid. Key
  relations add the *invisible* variant, where the colluding keys leave no
  trace in the aggregate key.
* **A perimeter of five rules closes the classes (§3).** (P1) key hygiene;
  (P2) one validity predicate per object, and batch verification only with
  random coefficients; (P3) verify before aggregating or sending; (P4)
  aggregates used only positively; (P5) certificates are proofs, never
  identifiers. P4 is the cryptographic counterpart of the model's
  positive-use rule (M-frame), and it is why the model's safety was immune
  in the first place.
* **Two modelling gaps turned up on the way (§2.1).** Neither falsifies a
  stated theorem on a first reading. First, (C1): Byzantine members of an
  aggregate skip the receiver-side checks the model's Byzantine actions
  carry. Second, (C2), which is independent of BLS: when a Byzantine *voter*
  equivocates, the argument that the model's `fb_sign_neg` guard is
  conservative fails. The concrete case needs only `n = 4`.
* **Modelling is feasible and cheap where it matters (§4).** Change the
  certificate definitions to constrain honest members only. That puts the
  whole adversarial-key capability inside the model and removes (C1) by
  construction. The cryptographic core (group arithmetic) lies outside Veil's
  first-order fragment and is textbook material; the accountability rule of
  `pc:accountability` is the one protocol-level place where modelling blame
  would verify a paper claim that is currently unverified.

## 1. The capability, stated precisely

Setting: BLS12-381 min-pk as in `monad-bft`, public keys registered with a
proof of possession (PoP), and certificates of the form (message, bitmask,
aggregate signature). Chorus has *same-message* aggregates: FastQC,
FallbackQC, FBCert, commitQC, fbCommitQC, and the MVBA's prepare and commit
certificates. It has *multi-message* aggregates in two places: the MVBA's
timeout certificate, where each signer's message carries its own highest
prepare-certificate view, and both proposals of the paper repository's
`vote-compression` note (single core signature; locally aggregated
per-proposer signatures).

The attacker controls at most `f` keys and knows their secrets, which it may
choose freely subject to PoP. So it can realise any linear relation *among
its own keys*:

* a **zero-sum set** `Z`, where the public keys of `Z` sum to the identity. Its
  aggregate signature on *every* message is the identity, so `Z`'s bits can be
  set on any certificate at no cost and without anyone signing;
* **equal-sum sets** `S1 ≠ S2`. A certificate listing `S1` verifies unchanged
  when it lists `S2` instead;
* **copied keys.** A PoP is a signature on the public key alone. If it is not
  bound to a validator identity, the attacker can register an honest
  validator's key under its own validator slot by reusing the honest PoP.

**What PoP rules out** is any relation that involves an honest key, because
such a relation would reveal that key's secret. The formal statement is the
security theorem of the PoP scheme (Ristenpart–Yilek 2007; Boneh–Drijvers–Neven
2018; the IETF CFRG BLS draft's PoP ciphersuite): if an aggregate verifies,
every claim `(pk_h, m)` for an honest `h` was signed by `h`, *whatever
relations hold among the adversarial keys*. This holds for multi-message
aggregates too; the distinct-message restriction applies only to the scheme
without PoP. Below this property is called **honest soundness**.

**What aggregation never provided**, and what the relations exploit:

1. **Membership malleability.** A certificate's bitmask can change within the
   Byzantine part without changing the signature: add or remove `Z`, or swap
   `S1` for `S2`. One certificate has many valid encodings.
2. **No Byzantine soundness.** A Byzantine bit is not evidence that any
   individual message was ever sent. With `Z`, none was.
3. **Individual and aggregate validity differ.** Two colluders send
   `σ₁ + X` and `σ₂ − X`. Each is invalid on its own; their sum is valid. This
   needs **no key relation**, only two keys signing the same message. With a
   zero-sum pair, the pair's keys also drop out of the aggregate key, so the
   aggregate carries no trace of who supplied the compensating parts.

Relative to "a Byzantine validator signs anything", items 1–3 are the entire
added capability. So every attack has to exploit one of three things: a rule
that tells apart two encodings of the same certificate, a rule that reads a
Byzantine bit or its absence as evidence, or two verification procedures that
disagree.

## 2. Attacks (question 1)

### 2.1 Level 0 — the modelled protocol and its stated properties

**No attack.** There are three reasons, each of which applies to the MVBA's
certificates as well:

* Certificates in the model are *derived predicates* over per-signer
  signature relations (`vote_quorum_pos`, `fbcert`, `commitqc_pos`, …;
  [`ChorusDesign.md`](./ChorusDesign.md) §3.5 (D)). The safety arguments use
  them in two ways only. Two quorums intersect in an honest member
  (`supermajorities_intersect_in_honest`), or an `f+1` set contains one
  (`greater_than_third_one_honest`). The conclusion is then drawn about
  *that honest member's* signature, which is honest soundness. Byzantine
  members contribute only to the count, and the count is over a bitmask
  indexed by the validator set, so relations cannot push it past `f`
  Byzantine members.
* Byzantine signatures are already unconstrained in the model, apart from
  the receiver checks listed under (C1) below.
* A certificate that some honest validators accept and others reject means
  that some validator does not act on it. The model has no `received`
  predicate and never forces an action ([`ChorusDesign.md`](./ChorusDesign.md)
  §3.1), so such a disagreement removes behaviour, and the over-approximation
  of §3.2 already covers that.

Two caveats turned up. They concern the soundness *argument*, not the stated
theorems.

**(C1) Byzantine members of an aggregate skip the receiver checks.** Three
Byzantine actions carry validity preconditions that mirror receiver checks
on *individual* messages:

* `byz_sign_vote_pos` requires the signer's chunk;
* `byz_sign_fb_pos` requires the proposer's signature;
* `byz_cast_vote` requires a complete vote.

A validator adopting a fast block, checking `Valid B` in the MVBA, or
receiving a broadcast commitQC checks only the aggregate. The Byzantine
members of that aggregate were never filtered, and with `Z` they never sent
anything. Yet the certificate predicates require `msg_*_sig` for *every*
member. The simulation argument of §3.2 therefore needs one step it does not
state: every real certificate must be reproducible in the model by firing
the Byzantine actions for its Byzantine members retroactively.

For the certificates the protocol actually consumes, this looks achievable:

* each has an honest member, whose own guard establishes the message-level
  part of the check (the proposer signed `m`);
* `deliver_chunk_assigned` has no phase guard, so a Byzantine member's chunk
  can be delivered after the fact.

However, retroactive delivery raises `chunk_quorum`, and `fb_sign_neg`'s
guard reads `chunk_quorum` negatively. That was not followed to the end. §4
M1 removes the question entirely.

**(C2) Byzantine voter equivocation and `fb_sign_neg`'s guard** (independent
of BLS; found while tracing how the model treats Byzantine signatures).

The guard asks whether any `f+1` set `q ⊆ qv` of voters exists that all carry
`msg_vote_pos_sig r j M`. That relation is *global*: a Byzantine voter that
signed positive for *someone* counts as positive in every `qv` it belongs to.
A real validator counts only the votes it received.

Concrete case with `n = 4`, `f = 1`:

* the proposer `j` is honest;
* two honest validators receive `j`'s chunk in time and vote positive;
* the honest validator `i` does not receive it and votes negative;
* the Byzantine validator signs both a positive and a negative entry for `j`,
  and sends the negative one to `i`.

The real `i` holds three votes, one of them positive, and signs a negative
fallback entry. In the model, every three-member `qv` contains two global
positive signers, and `j`'s root is decodable and well encoded, so no `qv`
satisfies the guard. The claim in §3.2, "the paper's guard implies the model's
`qv`-relative guard", therefore fails whenever a voter equivocates.

On a first reading, no stated theorem depends on the missing behaviour:

* the speculative-safety theorems assume `no_equivocation`, whose first two
  conjuncts exclude voter equivocation;
* proposal inclusion's premise puts at least `f+1` honest positive votes into
  any `2f+1` received set, so the real guard is false as well;
* agreement never consults the fallback guards.

The gap still needs closing (§4 M3).

### 2.2 Level 1 — liveness, where the models carry it as a premise

* **L1 — disagreement about `Valid`.** Chorus's liveness target
  (`TerminationClaim`, branch `worktree-chorus-liveness`) assumes
  `ValidBridge`: one `Valid` predicate that agrees with the network in both
  directions. The *completeness* direction says that a decided meta-block
  passes every correct validator's certificate check. It fails as soon as two
  honest code paths judge the same bytes differently. Examples: a validator
  that re-derives an aggregate from individually cached signatures and one
  that verifies the aggregate; batch verification versus single verification;
  two client implementations. A validator whose check rejects the decided
  meta-block never fires its decision handler and never finalizes the slot.
  Item 3 of §1 supplies the disagreeing object on demand.
* **L2 — framing an honest aggregator (the MonadBFT pattern,
  reconstructed).** Every certificate has honest assemblers: FastQCs and
  fast blocks, broadcast commitQCs, FBCert, fbCommitQC, and the MVBA leader's
  prepare, commit and timeout certificates. Suppose an assembler checks
  incoming signatures by *summing* a batch. Two colluders send `σ₁ + X` and
  `σ₂ − X`, and the batch passes. The assembler then uses one of the two,
  because it needs only a threshold or a particular subset, and broadcasts an
  invalid certificate under its own transport identity. Peers that blame,
  score or disconnect the sender hit an honest validator, and an invalid
  timeout certificate stalls the view change. With a zero-sum pair, nothing
  in the certificate points at the colluders.
* **L3 — cost amplification.** Optimistic "verify the aggregate, fall back
  to individual checks on failure" lets the attacker force the slow path
  every time.

### 2.3 Level 2 — beyond what is modelled (recorded, not followed)

* **A1 Accountability** (`pc:accountability`, local paper repository). The
  split-vote certificate is sound when its entries are honest-sound. Counting
  Byzantine bits is harmless because the reader's `f/2` bound already
  includes them. Framing becomes possible only through *negative*
  inferences: "absent from the bitmask, so did not vote", or "the
  certificate is invalid, so the culprit is …".
* **A2 Equivocation evidence records** (internal supplement, "Record
  equivocation evidence even without slashing"). Batch acceptance can store
  individually invalid signatures as evidence that later fails to verify.
  That harms no honest validator, but the evidence store must be verified
  signature by signature. An EquivCert against an honest proposer stays
  unforgeable.
* **A3 Byte-malleability.** Anything that hashes, deduplicates, orders by
  first arrival, or commits to certificate *bytes* sees many distinct valid
  encodings of one certificate. Affected are gossip dedup (a bandwidth
  amplifier), the "first FastBlock seen" choice, and MVBA values that embed
  relay-mutable certificate bytes. The model is blind to this by design: its
  MVBA value is the entry vector `node → Option merkle_root`.
* **A4 Randomness from aggregates.** A leader choice or coin derived from
  multi-signature bytes can be ground over the encodings of one certificate.
  Unique threshold signatures are not affected.
* **A5 Participation and reward accounting from bitmasks.** Byzantine bits
  are free, and with `Z` invisible. The attacker earns participation credit
  or evades inactivity penalties without participating. The effect is
  economic and bounded by the attacker's stake.
* **A6 Registration.** A copied PoP produces a duplicate key: a mirror
  validator for which every signature of the honest owner also counts, and
  lookups indexed by key become ambiguous. An identity key (secret `0`)
  becomes a permanent invisible member. Keys or signatures outside the
  prime-order subgroup carry torsion components that cancel in sums, which
  is another way for two implementations to disagree (see L1).
* **A7 Decryption shares** (TIBE). If shares are batch-verified by summation,
  the item-3 trick lets invalid shares through; this needs no key relation,
  and the shares come from a DKG. Honest validators combining different
  share sets then reconstruct different slot keys. Some decrypt and some
  fail, so the *revealed payload* diverges although consensus on the roots
  holds. The model's `ThresholdIBE.decrypt_sound` assumes valid shares.
* **A8 Light clients and bridges** verify commitQCs with their own code.
  Honest soundness still rules out forged finality, but chain and bridge can
  disagree about acceptance (L1 across a trust boundary).
* **A9 Domain separation.** Aggregation merges equal byte strings. If two
  message types, slots, epochs or chains share an encoding, aggregates mix
  them. This is not specific to key relations, but aggregation widens the
  damage.
* **Vote compression** (the `vote-compression` note). Both proposals turn a
  fast block into one multi-message aggregate plus a map from validators to
  cores. Honest soundness still holds under PoP (`AggregateVerify` in the PoP
  setting). But the Byzantine entries of the map are malleable (A3, A5), and a
  per-proposer FastQC can no longer be separated from the fast block, so a
  fallback meta-block that cites one carries the whole block's verification
  material.

## 3. Perimeter defences (question 2)

The principle is to make every protocol rule invariant under the
malleability of §1 and to give validity one definition. Five rules follow.
Each closes a class, with the argument that the closure is complete.

**P1 — Key hygiene.** Closes: relations involving honest keys, copied keys,
degenerate keys (A6).

* Validate keys on registration: subgroup membership, and not the identity.
* Use a PoP-only domain separation tag (the IETF PoP ciphersuite).
* Bind the PoP to (validator identity, epoch), or have the registry reject
  duplicate keys.
* Check every signature for subgroup membership.

*Completeness:* with these checks the PoP security theorem applies, and it
guarantees honest soundness for **arbitrary** adversarial keys. §2.1 shows the
safety proofs need nothing more. Nothing more is available from registration
either: relations among keys whose secrets the attacker chose cannot be
detected. P2–P5 therefore make those relations *harmless* rather than
impossible.

**P2 — One validity predicate per object.** Closes: splitting-zeros
disagreement, L1, A7, A8, the torsion part of A6.

* Validity of each object type is one deterministic function of its bytes:
  `Verify` for an individual signature, `FastAggregateVerify` or
  `AggregateVerify` against the bitmask's aggregate key for a certificate.
  Every code path computes that function.
* Batch verification uses verifier-chosen random coefficients (the
  small-exponent test), never plain summation.
* No rule relates the validity of individual signatures to the validity of
  an aggregate.

*Completeness:* a disagreement needs two honest parties evaluating different
predicates on the same bytes. With one deterministic predicate there are none;
randomised batching agrees with it except with probability `2^-λ`. P2 is
exactly the assumption that discharges `ValidBridge`'s completeness direction.

**P3 — Verify before aggregating, verify before sending.** Closes the honest
side of L2. An honest node aggregates only signatures that pass P2, and never
sends an aggregate that fails the canonical check. *Completeness:* then no
honest node ever emits an invalid object, so P4's sender rule can never hit
an honest one.

**P4 — Aggregates are used positively only.** Closes framing and blame (the
MonadBFT class, A1, A2) and the evidence half of A5.

A certificate may serve only as evidence that its *honest* members signed
its message and that the threshold is met. Three inferences are forbidden:

* (a) any inference from a bit about a *specific* signer: blame, reward,
  liveness scoring, "is online";
* (b) any inference from *absence* from a bitmask;
* (c) any inference from a failed verification about anyone other than the
  transport-authenticated sender of the failed object.

Evidence against an accused validator consists of that validator's own
signatures, each verified individually (the EquivCert shape).

*Completeness:* an inference from an aggregate concerns a member, a
non-member, or a failure. The member case is a positive statement, true of
honest members by P1 and harmless for Byzantine ones. The other two are (b)
and (c), and a positive statement about one specific Byzantine member is (a).
So framing an honest validator requires one of (a)–(c), and all three are
excluded. P4 is (M-frame) moved to the cryptographic level. The models
already consume certificates positively only, which is why safety was immune.

**P5 — Certificates are proofs, not identifiers.** Closes A3 and A4.

* Equality, deduplication, hashing and randomness range over (type, signed
  message), never over (bitmask, signature) bytes.
* Bytes that must be committed are committed under the committing party's
  signature.
* Randomness comes from unique (threshold) signatures only.

*Completeness:* a rule that is a function of semantic content is invariant
under malleability by definition.

**Why not remove the relations themselves?** There are two ways to try, and
neither works:

* **Per-aggregate key coefficients** (Boneh–Drijvers–Neven:
  `apk = Σ tᵢ·pkᵢ`, with `tᵢ` hashed over the signer set) make membership
  non-malleable. They cost a scalar multiplication instead of a point
  addition per signer and verification. They still leave splitting open: the
  coefficients are public, so the colluders scale their compensating terms
  to match.
* **Per-epoch fixed coefficients** can be precomputed. But with `f` in the
  hundreds, relations with coefficients in `{-1,0,1}` among the weighted keys
  exist by counting (`3^f ≫ q`), and whether one can be *found* becomes a
  matter of lattice parameters.

Neither replaces P2–P5, and with P2–P5 in place neither is needed.

## 4. Modelling (question 3)

| Item | What it models | Where | Cost | Benefit |
|---|---|---|---|---|
| **M1** certificates constrain honest members only | Honest soundness exactly: malleability, invisible sets, unfiltered Byzantine members | Certificate predicates in Chorus, Mvba, FallbackReceipt | Moderate: every certificate-bearing VC statement changes, so the families re-solve cold (the measurements are in `CLAUDE.md` § Build); manual cells may need rework | High: closes (C1) by construction |
| **M2** name P1/P2 as meta-assumptions | That `ValidBridge` rests on P2 | [`Architecture.md`](./Architecture.md) §4, `Liveness.lean` header | Hours | The trust list names the cryptographic premise |
| **M3** close (C2) | A conservative `fb_sign_neg` guard | `Chorus.lean` | Small: one guard, plus re-solving its action and the invariants that cite it | Restores §3.2's claim |
| **M4** accountability soundness | `pc:accountability`'s split-vote rule and P4 | Chorus plus a new threshold class | Medium | Verifies a paper claim that is currently unverified |
| **M5** algebraic core | §1 items 1–3, and honest soundness in the known-secret-key model | Plain Lean, or Tamarin | 1–2 days for the linear-algebra core | Low to moderate: textbook results, restated in this repository's vocabulary |
| — malleability (P5) | — | Nothing to do | — | The models are P5-compliant by construction: values are semantic (entry vectors) |

* **M1.** Replace `∀ r, member r q → msg_x_sig r …` with `∀ r, member r q →
  (¬ is_byz r → msg_x_sig r …)` in every certificate predicate. Reads of
  individual messages (`qv`, `msg_vote_cast`) keep the current relations.
  The model's certificates then say exactly what BLS-PoP guarantees, and the
  resulting theorem reads "safety holds for any Byzantine participation in
  certificates that the signature scheme cannot rule out".
  * Invariants that pass through Byzantine members must be restated through
    honest ones; for example, `local_fastqc_pos_chunks_decodable` becomes
    `2f+1` members, hence `f+1` honest, with chunks.
  * The step to watch is the speculative-safety argument's
    possibly-Byzantine intersection member
    (`supermajority_greater_than_third_intersect`). Either it survives under
    `no_equivocation`, or it shows the claim needs Byzantine soundness, which
    would be a finding in its own right.
  * Try FallbackReceipt first, as the cheap validation leg, then Mvba, then
    Chorus. Add an `AggregateSignature` class to
    [`Primitives.lean`](../Cadence/Primitives.lean) whose *only* property is
    honest soundness, with no Byzantine soundness and no uniqueness, so that
    the documented assumption matches what M1 uses. That part is a few hours.
* **M3.** Inside the guard's negated conjunction, require `msg_vote_pos_sig r
  j M ∧ ¬ msg_vote_neg_sig r j`. The relation appears twice negated, hence
  positively: adding tuples can only *enable* the action, so (M-frame) in
  its robust form still holds, but §3.1.1's enumeration must record it.
  * An equivocating voter no longer counts as positive, so the model's guard
    admits at least the real behaviour.
  * Under `no_equivocation` the extra conjunct is implied, so the
    speculative-safety invariants should adapt.
  * This needs confirming before it is relied on.
* **M4.** State it as a safety property: a split-vote certificate for `j`
  implies an honest positive voter and an honest negative voter for `j`.
  * It needs an `f/2+1` threshold that `ByzNodeSet` does not have: a new
    class with a non-vacuity witness in [`ByzQuorum.lean`](../Cadence/ByzQuorum.lean).
  * A mutation test in the style of `PreFix.lean` / `NoLock.lean` — blame on
    absence from a bitmask, refuted by `#model_check` and pinned — would
    demonstrate the P4 class machine-checked.
* **M5.** Signatures as elements of a `ZMod q`-module and adversarial
  secrets as known values give items 1–3 and honest soundness as short Lean
  theorems. They also show that summed batch verification differs from the
  conjunction of the individual checks. The probabilistic half (`2^-λ` for
  random batching) is not worth formalising. The blame flow at the protocol
  level fits Tamarin's bilinear-pairing theory better than Veil, whose
  first-order fragment cannot express group arithmetic.

**Recommended order:** M3 (smallest; closes a gap in a documented argument),
then M1 on FallbackReceipt and afterwards on Chorus, then M2 with the
`AggregateSignature` class, then M4 if accountability is a deployment goal.
