import Veil

/-! # Cryptographic primitive abstractions for the Cadence protocol

This file collects type-class abstractions for the cryptographic and agreement
primitives the Chorus sub-protocol depends on. They serve two purposes:

1. Documentation: each class states the *signatures* and *properties* of the
   primitive that Chorus relies on, lifted from the Cadence paper
   (`arXiv:2607.02275v2`): §Cryptographic Primitives `appendix:crypto`.
2. Targets for instantiation: a concrete implementation of Chorus would
   discharge each class by an actual scheme. For verification we only use the
   algebraic properties stated here.

The Veil protocol model in `Chorus.lean` does **not** instantiate these
classes directly. Instead it models the *observable effects* of the
primitives via first-order relations on signed messages, decryption shares,
etc. The classes in this file are therefore best read as the specification
the protocol model assumes the primitives satisfy.
-/

/-! ## Collision-resistant hash function

For a message space `msg` and digest space `hash`, we expect an injective hash
function (collision resistance is *computational*; for verification we model
it as exact injectivity, which is sound under a computationally-bounded
adversary). -/
class HashFunction (msg : Type) (hash : Type) where
  hash : msg → hash
  collision_resistant : ∀ m m', hash m = hash m' → m = m'

/-! ## Digital signature scheme

We model an EUF-CMA signature scheme abstractly. Each node has its own
keypair; we identify the public key with the node itself. A signature carries
with it the identity of its signer (`signer σ`).

Two cryptographic guarantees are stated as axioms:

* `sound`: a correctly-formed signature verifies.
* `unforgeable`: a signature that verifies under public key `pk_n'` must have
  been produced by `n'` itself.

Aggregation of signatures is not modelled at this level; the protocol talks
about aggregated certificates `Σ` directly as derived predicates over the
underlying signed-message relations. -/
class SignatureScheme (node : Type) (msg : Type) (signature : Type) where
  Sign : node → msg → signature
  Verify : node → msg → signature → Bool
  signer : signature → node

  sound (n : node) (m : msg) (σ : signature) :
    Sign n m = σ → Verify n m σ = true
  unforgeable (n n' : node) (m : msg) (σ : signature) :
    Sign n m = σ → Verify n' m σ = true → n' = n

  sound_signer (n : node) (m : msg) (σ : signature) :
    Sign n m = σ → signer σ = n
  unforgeable_signer (n : node) (m : msg) (σ : signature) :
    Verify n m σ = true → signer σ = n

section SignatureSchemeLemmas
variable [s : SignatureScheme node msg signature]

theorem SignatureScheme.honest_signer_unique
    (n n' : node) (m : msg) (σ : signature) :
    n ≠ n' → s.Sign n m = σ → s.Verify n' m σ = false := by
  intro _ hsign
  have hverify := s.unforgeable n n' m σ hsign
  grind

theorem SignatureScheme.signer_self_verifies (n : node) (m : msg) :
    s.Verify (s.signer (s.Sign n m)) m (s.Sign n m) = true := by
  have hsign := s.sound n m (s.Sign n m)
  have signer_eq := s.sound_signer n m (s.Sign n m)
  grind

end SignatureSchemeLemmas

/-! ## Threshold Identity-Based Encryption (TIBE)

`Setup` runs once per epoch (we model it implicitly via the `mpk`/`msk`
projections; in the actual protocol the master secret-key shares are
distributed during the epoch handover).

The two axioms we rely on are:

* `decrypt_sound`: with `t = f + 1` valid decryption shares from the intended
  identity, decryption of `Enc(mpk, id, m)` recovers `m`.
* `decrypt_secret`: decryption only succeeds via a verified set of `≥ t`
  shares — the payload remains hidden until that threshold is reached.

The protocol uses TIBE for *hiding*; safety of Chorus does **not** depend on
TIBE in any essential way (a different mechanism, or no encryption, would
yield the same safety story but would weaken hiding). We expose the class
here for completeness and so a concrete implementation has a clear target. -/
class ThresholdIBE
    (node pk sk id message ciphertext share : Type) where
  /-- `Enc(mpk, id, m)` -/
  Enc : pk → id → message → ciphertext
  /-- `KeyShare(id, msk_i)` -/
  KeyShare : id → sk → share
  /-- `VerifyShare(mpk, id, p_i, share_i)` -/
  VerifyShare : pk → id → node → share → Bool
  /-- `Dec(mpk, c, id, {share_i})` returns the plaintext or fails. -/
  Dec : pk → ciphertext → id → List share → Option message

  /-- Master public/secret key projections (per-epoch). -/
  mpk : Finset node → Nat → pk
  msk : Finset node → Nat → node → sk

  /-- Soundness: with `≥ t` valid decryption shares from the intended
      identity, decryption of `Enc(mpk, id, m)` recovers `m`. -/
  decrypt_sound :
    ∀ (validators : Finset node) (t : Nat) (i : id) (m : message),
      let mpk_e := mpk validators t
      ∀ (S : Finset node),
        S ⊆ validators → S.card ≥ t →
          (∀ p ∈ S, VerifyShare mpk_e i p (KeyShare i (msk validators t p)) = true) →
          Dec mpk_e (Enc mpk_e i m) i
            (S.toList.map (fun p => KeyShare i (msk validators t p))) = some m

  /-- Secrecy: decryption succeeds only when a threshold of correct key
      shares is supplied. If `Dec` returns a plaintext, then some
      `S ⊆ validators` with `|S| ≥ t` has every `KeyShare i (msk validators t
      p)` (for `p ∈ S`) present in the input share list. Equivalently, the
      payload remains hidden from any party that controls fewer than `t`
      correct shares for the intended identity. -/
  decrypt_secret :
    ∀ (validators : Finset node) (t : Nat) (i : id)
      (c : ciphertext) (m : message) (shares : List share),
      Dec (mpk validators t) c i shares = some m →
        ∃ (S : Finset node), S ⊆ validators ∧ S.card ≥ t ∧
          ∀ p ∈ S, KeyShare i (msk validators t p) ∈ shares

/-! ## Erasure coding

`Encode` splits a ciphertext into `n` fragments and `Decode` reconstructs the
ciphertext from any `f + 1` of them. Used to amortise the cost of
disseminating the encrypted proposal across all validators.

The Veil protocol model treats decoded-payload availability abstractly: once
`≥ f + 1` chunks have been ingested by honest validators, the ciphertext is
recoverable. The actual codec is not modelled. -/
class ErasureCoding (cipher : Type) (fragment : Type) where
  /-- `Encode(c)` produces `n` fragments. -/
  Encode : cipher → Nat → List fragment
  /-- `Decode({d_i})` returns the original ciphertext or fails. -/
  Decode : List fragment → Option cipher

  /-- Decoding is the left inverse of encoding on any sufficiently large
      subset of the encoded fragments (size `≥ f + 1`). -/
  decode_sound :
    ∀ (c : cipher) (n f : Nat),
      ∀ (S : List fragment), S.length ≥ f + 1 →
        (∀ x ∈ S, x ∈ Encode c n) → Decode S = some c

  /-- Encoding is injective: two ciphertexts that yield the same
      collection of fragments must be equal. This is the "Merkle
      binding" property as enforced at decode time in the DA module. -/
  encode_inj :
    ∀ (c c' : cipher) (n : Nat), Encode c n = Encode c' n → c = c'

/-! ## Merkle trees

`MerkleRoot(d_1, …, d_n)` commits to the leaves; `MerkleProof i` is the
authentication path for the `i`-th leaf; `VerifyMerkle` checks the path.

Binding: a Merkle root determines its leaves — given two valid proofs for the
same root and same index, the leaf values agree. -/
class MerkleTree (leaf : Type) (root : Type) (proof : Type) where
  /-- Commit to a list of leaves. -/
  MerkleRoot : List leaf → root
  /-- Authentication path for the `i`-th leaf. -/
  MerkleProof : List leaf → Nat → proof
  /-- Verify that `d` is the `i`-th leaf under `r`. -/
  VerifyMerkle : root → Nat → leaf → proof → Bool

  /-- A correctly-produced proof verifies. -/
  sound :
    ∀ (leaves : List leaf) (i : Nat) (h : i < leaves.length),
      VerifyMerkle (MerkleRoot leaves) i leaves[i]
        (MerkleProof leaves i) = true

  /-- Binding: a root determines each indexed leaf — two leaves that
      both verify against the same root at the same index are equal. -/
  binding :
    ∀ (r : root) (i : Nat) (d d' : leaf) (π π' : proof),
      VerifyMerkle r i d π = true →
      VerifyMerkle r i d' π' = true →
      d = d'

/-! ## Where the MVBA contract lives

The MVBA is a *module* contract (`mod:mvba`), not a cryptographic primitive,
and it is stated with the other module contracts in
[`Interfaces.lean`](./Interfaces.lean) (`MVBASafety`/`MVBA`) since 2026-09.
It used to live here; it moved because `Chorus.lean` imports this file, so
any edit to a contract kept here would force the whole Chorus proof family
to rebuild. Chorus consumes the MVBA as an inlined oracle
(`Chorus.lean`, "MVBA oracle"); why it does not yet take the class as a
constraint is recorded at the class. -/
