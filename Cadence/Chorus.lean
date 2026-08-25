import Veil
import Cadence.Primitives
import Cadence.Tooling

/-! # Chorus — per-slot one-shot BFT consensus for Cadence

*This is a **model file** of the verified-module file family
(`docs/Architecture.md` §6): it elaborates the transition system and
persists the VC registry, but runs **no invariant sweep** — the 3 783
invariant VCs are proven in the per-action files under
[`Chorus/Proofs/`](./Chorus/Proofs) and composed into the reachability
certificate by [`Chorus/Certify.lean`](./Chorus/Certify.lean). Opening
this file in an editor costs the model elaboration plus the (cheap)
background `doesNotThrow` checks — no SMT sweep (set `VEIL_NO_VERIFY=1`
in the editor environment to skip even that). To work on the module,
read `CLAUDE.md` first.

Chorus is the inner consensus layer of Cadence: for each slot `s` it runs an
independent one-shot Byzantine-fault-tolerant agreement instance among a set
`Π` of `n = 3f + 1` validators, with `k` concurrent *proposers* `Ps ⊆ Π`. The
slot terminates either via the fast path (two voting rounds) or via the
fallback path (one extra round of voting, an invocation of MVBA, and a
final round of commit votes on the decided entries).
This file specifies the Chorus protocol as a Veil transition system for a
*single* slot instance: state and messages are not slot-parameterised, since
the per-slot agreement instances are independent. The `slot` type below is
retained only as a placeholder for a possible multi-slot extension — see the
`is_proposer` TODO, which also notes that cross-slot independence is not
guaranteed in practice.

The reference document is the Cadence paper, `arXiv:2607.02275v2`; the root
`README.md` gives the citation and how to resolve the LaTeX label names used
throughout (e.g. `line:fb-pathvote-guard`). In the paper source, the Chorus
chapter is `src/p2_chorus.tex`, with pseudocode in `src/alg_proposer.tex`,
`src/alg_voting.tex`, `src/alg_fast.tex`, `src/alg_fallback.tex`,
`src/alg_da.tex`, and the MVBA module specification in `src/p2_mvba.tex`.

## Property coverage

The paper establishes six slot-consensus properties for Chorus
(`p2_chorus.tex` §`subsection:proof_sketches`); their status in this model:

* **Agreement** (`lemma:chorus-agreement`) — `safety [agreement_pos]`,
  `[agreement_pos_neg]`, proven for the paper's *full-finality* commit rule
  (commitQC or MVBA certificate) by the paper's own asynchronous quorum
  argument (`prop:agreement-entries`). No timing assumptions.
* **Proposal inclusion** (`lemma:chorus-proposal-inclusion`, a.k.a.
  censorship resistance) — `safety [proposal_inclusion]`,
  `[proposal_inclusion_no_neg]`. The paper's synchrony premise ("a correct
  proposer disseminates at `s.deadline − Δ ≥ GST`") is abstracted to its
  protocol-level consequence: *every honest validator records the positive
  entry* (`all_honest_recorded`).
* **Hiding** (`lemma:chorus-hiding`, `def:hiding`) — split across two layers.
  The cryptographic layer (TIBE unpredictability, the random-oracle
  simulation of `p2_chorus.tex` §`appendix:encryption`) is axiomatised in
  [`Primitives.lean`](./Primitives.lean) (`ThresholdIBE.decrypt_secret`).
  The protocol layer — the slot key cannot be reconstructed before the
  deadline because reconstruction needs `f+1` shares and honest validators
  release shares only with their deadline vote — is `safety [hiding_until_deadline]` here.
* **Slot safety** (`lemma:chorus-slot-safety`) — trivial in this model: it
  is single-slot, so every commit is a commit *for this slot* by
  construction.
* **Termination** (`lemma:chorus-termination`) — the model is untimed, so
  the `ℓ = 5Δ + ℓ_MVBA` bound is out of scope. Since the 2026-07-07
  revision the paper's termination is *conditioned* on Δ-synchronized
  participation (`def:delta-synchronized-participation`), discharged
  within Cadence by Conductor totality
  (`cor:chorus-correctness-within-cadence`); this single-slot model has
  no participation machinery (no `abandon()`), so the premise is
  implicit. The *fair-progress* safety content of the liveness argument
  is SMT-discharged in the "Liveness" section near the end of this file;
  the temporal glue is stated there as meta-axioms.
* **Quiescence** (`lemma:chorus-quiescence`) — no correct validator sends
  protocol messages outside its participation window. A timing/
  participation property, out of scope for this untimed single-slot
  model; its in-model shadow is phase confinement of the honest message
  relations (`fb_sig_phase`, `mvba_decided_phase`, `fbcommit_sig_phase`,
  `voted_post_deadline`). The full property is Cadence/Conductor-level
  (see `Interfaces.lean` / the participation convention,
  §`subsection:chorus-protocol-overview`).

Additionally, `safety [speculative_agreement_pos]` / `[..._pos_neg]` check
the paper's speculative-finality claim (`p1_informal.tex`: a speculative
commit "may be reverted ... only if some validator equivocated" — widened by
the proof sketch's closing parenthetical, `subsection:chorus-proof`, to a
proposer committing to an invalidly encoded root): in any state free of vote
or proposer equivocation (`no_equivocation`) in which no proposer has
committed to an invalidly encoded root (`no_invalid_encoding`), a
validator's speculative value (its own FastQC) agrees with every final
commit.

See `docs/ChorusDesign.md` for a higher-level discussion of the
modelling choices, the abstractions made over the cryptographic primitives,
and the limitations of the model with respect to liveness.
-/

veil module Chorus

/-! ## Types -/

-- A slot identifier (cf. `s ∈ Slot`, §`subsection:mcp-preliminaries`).
-- Currently unused (the model is single-slot — see the module header); kept as
-- a placeholder for a possible multi-slot extension.
type slot
-- A validator node identity.
type node
-- A set of nodes; the `ByzNodeSet` instance gives supermajority/
-- greater-than-third quorum predicates plus the standard Byzantine
-- intersection axioms.
type nodeset
-- A Merkle commitment to an erasure-coded encrypted proposal.
-- Modelled as an opaque token; binding properties are captured by
-- requiring the proposer's signature on `⟨s, j, m⟩` together with
-- the chunks themselves to determine the proposal.
type merkle_root

/-! ## Byzantine quorum abstraction

`ByzNodeSet` packages the `is_byz` predicate together with the two quorum
sizes that arise in Chorus:

* `supermajority s ↔ |s| ≥ 2f + 1` (FastQCs, CommitQCs, FBCerts)
* `greater_than_third s ↔ |s| ≥ f + 1` (FallbackQCs, erasure decode)

Besides the standard intersection axioms, the proofs below use three
counting axioms added to `ByzNodeSet` for this model (each proven for the
concrete `byzNodeSetFin` instance in `Veil/Frontend/Std.lean`):

* `supermajority_contains_honest_greater_than_third` — a supermajority
  contains an all-honest `f+1`-subset (`2f+1 − f = f+1`);
* `supermajority_greater_than_third_intersect` — a supermajority and an
  `f+1`-set share a (possibly Byzantine) member
  (`(2f+1) + (f+1) − (3f+1) = 1`);
* `supermajorities_intersect_in_greater_than_third` — two supermajorities
  share an `f+1`-subset (`2(2f+1) − (3f+1) = f+1`). -/

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet

/-! ## Immutable configuration

`is_proposer j` says that `j ∈ Ps` for slot `s`. In a faithful implementation
this would be derived from a VRF; here we abstract it as an immutable
relation. -/

-- TODO consider declaring as immutable individual. We need it mostly
-- for TIBE. It may however become relevant if we wanted to model parallel
-- execution of multiple slots. It is not guaranteed that those are independent
-- from each other: e.g. network outages for one slot most likely also affect
-- other slots. The same holds for other byzantine behavior.

immutable relation is_proposer (j : node)

/- Whether the chunk set committed under root `m` forms a valid erasure
encoding — decoding any `f+1` of its chunks and re-encoding reproduces `m`
(`alg:da` `line:da-reencode`). Validity is a property of the whole committed
set the root binds, identical at every validator
(`prop:recovery-consistency`), hence immutable configuration. Honest
proposers only commit well-encoded roots (`propose` requires it — the
paper's recovery guarantee (ii) premise); a Byzantine proposer may sign a
root that is not well-encoded and disseminate individually-valid chunks for
it — the paper's "invalidly encoded root" culprit case
(`subsection:chorus-proof`, closing parenthetical), which the fallback
signing rules below consult. -/
immutable relation well_encoded (m : merkle_root)

/-! ## Abstract phase

Chorus is naturally an event-driven protocol with three time landmarks per
slot: the deadline `Ds`, the fallback arm time `Ds + Δ`, and the MVBA arm time
`Ds + 2Δ`. We do **not** model wall-clock time directly; instead we expose a
single per-slot phase that advances non-deterministically through four
values in order:
`pre_deadline → post_deadline → post_fb_arm → post_mvba_arm`. -/

enum Phase = { pre_deadline, post_deadline, post_fb_arm, post_mvba_arm }
individual phase : Phase

/-! ## Signed-message relations (the "network")

Each relation below stands for "this signed message has been produced and is
observable on the network". Once produced they remain — the network is
monotone — which is the standard idealisation for asynchronous BFT proofs.
Honest signers are constrained by their local state in the actions below; the
Byzantine actions allow Byzantine signers to produce any *network-valid*
signature attributed to themselves (unforgeability prevents them from
producing signatures attributed to honest signers; the validity checks that
every honest receiver performs — chunk backing for positive vote entries,
`σ_p` for positive fallback entries, entry-completeness for broadcast votes —
are mirrored as preconditions of the Byzantine actions, because messages
failing them are discarded on receipt and thus never observable as valid). -/

-- Proposer `j` has signed a chunk header `⟨s, j, m⟩` (`alg:proposer-dissemination`).
relation msg_proposer_signed (j : node) (m : merkle_root)

-- A chunk from proposer `j` for slot `s` under root `m` has been
-- delivered to validator `i` (the network "in-flight" relation; see
-- `docs/ChorusDesign.md` §3.5.1 for why chunks are the only per-recipient network
-- relation).
relation msg_chunk_received (i : node) (j : node) (m : merkle_root)

-- Validator `r` has signed a positive `vote`-tagged entry `⟨s, j, m⟩`.
relation msg_vote_pos_sig (r : node) (j : node) (m : merkle_root)
-- Validator `r` has signed a negative `vote`-tagged entry `⟨s, j, ⊥⟩`.
relation msg_vote_neg_sig (r : node) (j : node)
-- Validator `r` has broadcast its proposal vote (`alg:voting`
-- `line:vote-broadcast`). A broadcast vote carries a signed entry for
-- *every* proposer (plus the chunks backing the positive entries and the
-- decryption share); receivers discard incomplete votes, so a cast vote
-- implies per-proposer signatures on the network.
relation msg_vote_cast (r : node)

-- Validator `r` has signed a positive `fb`-tagged entry.
relation msg_fb_pos_sig (r : node) (j : node) (m : merkle_root)
-- Validator `r` has signed a negative `fb`-tagged entry.
relation msg_fb_neg_sig (r : node) (j : node)

-- Validator `r` has signed `⟨fallback, s⟩` (its fallback vote,
-- `alg:fallback` `line:fb-pathvote-guard` block).
relation msg_fallback_sig (r : node)

-- Validator `r` has signed a fast commit vote whose core has a
-- positive entry `⟨s, j, m⟩` for proposer `j`.
relation msg_commit_pos_sig (r : node) (j : node) (m : merkle_root)
-- Validator `r` has signed a fast commit vote whose core has a
-- negative entry for proposer `j`.
relation msg_commit_neg_sig (r : node) (j : node)
-- Validator `r` has actually broadcast its fast commit vote
-- (`alg:fast-path-certification` `line:fast-commitvote`). Only broadcast
-- commit signatures count toward a commitQC.
relation msg_commit_cast (r : node)

-- An assembled positive fast commit certificate for `(j, m)` has been
-- broadcast (`alg:fast-path-certification` `line:fast-broadcast-commitqc`):
-- an aggregate of `2f+1` matching *broadcast* commit votes. Anyone holding
-- the underlying signatures — honest or Byzantine — can assemble it, and
-- every receiver can verify it, so its existence is a network fact; the
-- assembly step is the `broadcast_commitqc_*` action, whose precondition
-- is exactly the certificate's validity check.
relation msg_commitqc_pos (j : node) (m : merkle_root)
-- The negative counterpart.
relation msg_commitqc_neg (j : node)

-- TIBE extraction (decryption) share released by validator `r` for the slot
-- (`alg:voting`: released together with the proposal vote).
relation msg_decrypt_share (r : node)

-- Validator `r` has signed and broadcast a fallback commit vote
-- `⟨FallbackCommitVote, s, entries(B'), σ_r⟩` (`alg:fallback`
-- `line:fb-commitvote`) — the extra commit round the fallback path runs
-- after an MVBA decision (2026-07-07 paper revision; an MVBA decision no
-- longer finalizes by itself). The entry vector is left implicit in the
-- relation: an honest validator signs exactly the MVBA-decided entries
-- (`line:fb-mvba-decide` binds `E = entries(B')`), which the oracle's
-- baked-in agreement makes unique, so "2f+1 votes carrying the *same*
-- entries" (`line:fb-collect-commit`) needs no vote-level argument. A
-- Byzantine signer's vote on any *other* vector could never aggregate
-- into an fbCommitQC in the paper (2f+1 matching votes contain an honest
-- co-signer); dropping the vector from the relation lets such votes count
-- toward the model's `fbcommitqc` ghost, which only *over-approximates*
-- adversary power — the sound direction for safety — and `commit_assign_*`
-- requires the MVBA decision itself in conjunction, so a commit's
-- *content* always comes from the decided vector.
relation msg_fbcommit_sig (r : node)

/-! ## Per-validator certificate state

`local_fastqc_*` is the one aggregated certificate we track per validator:
an honest validator's fast commit vote is justified by *its own* FastQC
observation (`alg:fast-path-certification` `line:fast-formqc`), so the
signer's local aggregate is protocol state. All other certificates
(FallbackQC, EquivCert, FBCert, commitQC) are *transferable*: any
holder of the underlying signatures can assemble and verify them, so in the
monotone-network model they are represented as derived predicates over the
signature relations (the `ghost relation`s below) rather than as
per-validator state. -/

-- `local_fastqc_pos i j m` ≡ validator `i` has aggregated `2f+1`
-- positive-vote signatures into a positive FastQC for proposer `j`
-- under root `m`. Cross-validator agreement (any two honest validators'
-- FastQCs for the same proposer agree on the root) is recovered as an
-- invariant from quorum intersection (`local_fastqc_pos_cross_unique`).
relation local_fastqc_pos (i : node) (j : node) (m : merkle_root)

-- `local_fastqc_neg i j` ≡ validator `i` has aggregated `2f+1`
-- negative-vote signatures for proposer `j`.
relation local_fastqc_neg (i : node) (j : node)

/-! ## Multi-Value Byzantine Agreement (MVBA)

The fallback path invokes one MVBA instance per slot (`mod:mvba`,
`p2_mvba.tex`). We abstract it as an oracle: actions
`mvba_decide_pos`/`mvba_decide_neg` populate the per-proposer decision
relations, and `mvba_terminate` marks termination. The oracle's preconditions
encode exactly the properties the MVBA module specification grants:

* *Agreement* — a decision never contradicts an earlier decision for the
  same proposer;
* *Integrity* — the oracle decides each proposer at most once, and
  `mvba_complete` closes it;
* *External validity* — a decided entry is backed by a publicly verifiable
  certificate: a FastQC (a `2f+1` vote quorum), or a fallback-metablock
  entry (FallbackQC / EquivCert) together with the `FBCert` that every
  fallback meta-block must carry.

(The full mapping of the `mod:mvba` interface — `propose`/`abandon`/
`decide`, conditioned `ℓ_MVBA`-Termination, Quiescence — onto this
oracle is spelled out at the "MVBA oracle" section before the decide
actions.)

Because `mvba_decided_*` are mutable Veil relations rather than immutable
parameters, we cannot use `assumption` to axiomatise these properties at the
module level; they are baked into the firing rules and then lifted to
invariants (`mvba_decided_pos_unique` etc.) for use by downstream actions. -/

relation mvba_decided_pos (j : node) (m : merkle_root)
relation mvba_decided_neg (j : node)
individual mvba_complete : Bool

/-! ## Validator-local state -/

relation local_entry_pos (i : node) (j : node) (m : merkle_root)
relation local_entry_neg (i : node) (j : node)

relation local_voted (i : node)

/- `local_path i` is the path validator `i` has committed to (the paper's
`pathVote`, `alg:fast-path-certification` local variables). `none` until
either `cast_fast_commit` (→ `fast`) or `cast_fallback_vote` (→ `fallback`)
fires; the enum value gives structural mutual exclusion of the two terminal
vote-cast actions without an explicit invariant. -/
enum PathChoice = { none, fast, fallback }
function local_path : node → PathChoice

relation local_committed (i : node)
relation local_committed_pos (i : node) (j : node) (m : merkle_root)
relation local_committed_neg (i : node) (j : node)

/- Auxiliary (proof-only) history variable: the witnessed quorum of
broadcast votes against which validator `i` cast its negative fallback
entry for proposer `j` (the `qv` parameter of `fb_sign_neg` at firing
time). Written by `fb_sign_neg`, read by no action — it exists so that
the speculative-safety argument can refer to the quorum after the fact
without an `∃ qv (… ∧ ∀ …)` invariant, whose quantifier alternation
sends the SMT matcher into a loop on the bulk-update actions. -/
relation local_fb_neg_qv (i : node) (j : node) (qv : nodeset)

/- `#gen_state` assembles the ~50-component `State` and its
FieldRepresentation/SubState instances; at this component count the
elaboration needs a raised heartbeat budget in one `isDefEq` inside the
machinery. The raise lives
*inside the elaborator* (`Module.ensureStateIsDefined`, scoped to state
generation), so the module default (`veilDefaultOptions`, 500k) applies
to everything else — in particular the sweep dischargers. A file-level
`set_option maxHeartbeats` here does NOT reach the failing elaboration,
and never use `set_option … in
<veil command>` — the scope pop reverts Veil's module state and the next
DSL command regenerates the State into "already declared" errors. -/
#gen_state

/-! ## Derived certificates (ghost relations)

Transferable certificates are predicates over the signature relations: a
certificate "exists" iff the signatures it aggregates are observable on the
network. Any validator — honest or Byzantine — holding the signatures can
assemble the certificate, and any receiver can verify it, so existence on
the network is the faithful notion. -/

-- A positive FastQC certificate for `(j, m)`: `2f+1` matching positive
-- vote signatures (`alg:fast-path-certification` `line:fast-formqc`).
ghost relation vote_quorum_pos (j : node) (m : merkle_root) :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_vote_pos_sig r j m

-- A negative FastQC certificate for `j`.
ghost relation vote_quorum_neg (j : node) :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_vote_neg_sig r j

-- A positive FallbackQC certificate for `(j, m)`: `f+1` matching positive
-- fallback signed entries (`alg:fallback` `line:fb-formqc`).
ghost relation fb_quorum_pos (j : node) (m : merkle_root) :=
  ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_fb_pos_sig r j m

-- A negative FallbackQC certificate for `j`.
ghost relation fb_quorum_neg (j : node) :=
  ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_fb_neg_sig r j

-- An EquivCert for proposer `j`: the proposer's signatures on two distinct
-- roots (`⟨equiv, s, j, ρ₁, σ_{p,1}, ρ₂, σ_{p,2}⟩`, §`subsection:fallback_path`).
-- The fallback votes through which the two signed roots are *observed* are a
-- liveness/visibility matter that the monotone network abstracts away; the
-- certificate itself consists of the two proposer signatures.
ghost relation equiv_evidence (j : node) :=
  ∃ m1 m2, m1 ≠ m2 ∧ msg_proposer_signed j m1 ∧ msg_proposer_signed j m2

-- The fallback certificate `FBCert_s`: `2f+1` fallback signatures
-- (§`subsection:fallback_path`). Every fallback meta-block carries it; it
-- certifies that the fast path can no longer commit the slot.
ghost relation fbcert :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_fallback_sig r

-- A positive fast commit certificate entry for `(j, m)`: `2f+1` matching
-- *broadcast* fast commit votes (`alg:fast-path-certification`
-- `line:fast-collect-commit`). Signatures that were produced but never
-- broadcast (an honest validator signs per-proposer entries before casting
-- the vote) do not count: in the protocol they never reach the network.
ghost relation commitqc_pos (j : node) (m : merkle_root) :=
  ∃ q, nset.supermajority q ∧
    ∀ r, nset.member r q → msg_commit_pos_sig r j m ∧ msg_commit_cast r

-- A negative fast commit certificate entry for `j`.
ghost relation commitqc_neg (j : node) :=
  ∃ q, nset.supermajority q ∧
    ∀ r, nset.member r q → msg_commit_neg_sig r j ∧ msg_commit_cast r

-- The fallback commit certificate `fbCommitQC` (`alg:fallback`
-- `line:fb-collect-commit` / `line:fb-formcommitqc`): `2f+1` fallback
-- commit votes over the same entries. Transferable
-- (`line:fb-commit-broadcast`); finalization fires on its receipt
-- (`line:fb-recv-commit` / `line:fb-finalize`). The entries it carries
-- are the MVBA-decided vector — see `msg_fbcommit_sig` for why the
-- vector is implicit in the signature relation.
ghost relation fbcommitqc :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_fbcommit_sig r

-- Data availability for `(j, m)`: `f+1` delivered chunks — the erasure-code
-- reconstruction threshold (`alg:da` `isDecoded`).
ghost relation chunk_quorum (j : node) (m : merkle_root) :=
  ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_chunk_received r j m

-- The slot key can be reconstructed: `f+1` extraction shares released
-- (§`appendix:encryption`).
ghost relation slot_key_released :=
  ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_decrypt_share r

-- MVBA has been invoked by some honest validator, along one of the paper's
-- two proposal triggers (`alg:fallback`): the fallback trigger (`|M_i| ≥
-- 2f+1` fallback votes, whose monotone-network shadow is `fbcert`), or the
-- case-(a) trigger (a complete fast meta-block — a FastQC for every
-- proposer — held at the MVBA arm time).
ghost relation complete_fast_metablock (i : node) :=
  ∀ j, is_proposer j → ((∃ m, local_fastqc_pos i j m) ∨ local_fastqc_neg i j)
ghost relation mvba_invoked :=
  fbcert ∨ (∃ i, ¬ is_byz i ∧ complete_fast_metablock i)

/-! ## Hypothesis predicates for conditional properties -/

-- No signer has equivocated: no validator carries two different vote
-- entries for the same proposer, and no proposer has signed two different
-- roots. The paper's speculative-finality claim (`p1_informal.tex`:
-- "reverted ... only if some validator equivocated") is stated relative to
-- this predicate. It is anti-monotone (once violated, violated forever), so
-- invariants conditioned on it remain inductive.
ghost relation no_equivocation :=
  (∀ r j m1 m2, msg_vote_pos_sig r j m1 ∧ msg_vote_pos_sig r j m2 → m1 = m2) ∧
  (∀ r j m, ¬ (msg_vote_pos_sig r j m ∧ msg_vote_neg_sig r j)) ∧
  (∀ j m1 m2, msg_proposer_signed j m1 ∧ msg_proposer_signed j m2 → m1 = m2)

-- No proposer has committed to an invalidly encoded root: every
-- proposer-signed root is well-encoded. Together with `no_equivocation`
-- this is exactly the paper's "proposer is the culprit" set for
-- speculative finality (`subsection:chorus-proof`, closing parenthetical:
-- "committing to an invalidly encoded root or disseminating several
-- distinct proposals"). Anti-monotone like `no_equivocation` (signatures
-- only accrue and `well_encoded` is immutable), so invariants conditioned
-- on it remain inductive.
ghost relation no_invalid_encoding :=
  ∀ j m, msg_proposer_signed j m → well_encoded m

-- The protocol-level shadow of the paper's proposal-inclusion premise
-- (`prop:honest-positive-entry`): a correct proposer `j` disseminated its
-- proposal `m` on time under synchrony, so *every* honest validator
-- recorded the positive entry `⟨s, j, m⟩` before the deadline. The timing
-- content ("`s.deadline − Δ ≥ GST` and dissemination at the slot's starting
-- time") is exactly what makes this premise true in the real protocol; the
-- model takes the premise itself as the hypothesis. The `well_encoded`
-- conjunct is the premise's encoding half: a correct proposer encodes the
-- ciphertext into a valid erasure encoding (the paper's recovery
-- guarantee (ii)), so its root always passes the re-encode check.
ghost relation all_honest_recorded (j : node) (m : merkle_root) :=
  ¬ is_byz j ∧ is_proposer j ∧ (∀ i, ¬ is_byz i → local_entry_pos i j m) ∧
  well_encoded m

/-! ## Initial state -/

after_init {
  phase := pre_deadline

  msg_proposer_signed J M := false
  msg_chunk_received I J M := false
  msg_vote_pos_sig R J M := false
  msg_vote_neg_sig R J := false
  msg_vote_cast R := false
  msg_fb_pos_sig R J M := false
  msg_fb_neg_sig R J := false
  msg_fallback_sig R := false
  msg_commit_pos_sig R J M := false
  msg_commit_neg_sig R J := false
  msg_commit_cast R := false
  msg_commitqc_pos J M := false
  msg_commitqc_neg J := false
  msg_decrypt_share R := false
  msg_fbcommit_sig R := false

  local_fastqc_pos I J M := false
  local_fastqc_neg I J := false

  mvba_decided_pos J M := false
  mvba_decided_neg J := false
  mvba_complete := false

  local_entry_pos I J M := false
  local_entry_neg I J := false
  local_voted I := false
  local_path I := none
  local_committed I := false
  local_committed_pos I J M := false
  local_committed_neg I J := false
  local_fb_neg_qv I J QV := false
}

/-! ## Phase advancement

Phase markers advance monotonically and non-deterministically. -/

action advance_to_deadline {
  require phase = pre_deadline
  phase := post_deadline
}

action advance_to_fb_arm {
  require phase = post_deadline
  phase := post_fb_arm
}

action advance_to_mvba_arm {
  require phase = post_fb_arm
  phase := post_mvba_arm
}

/-! ## Phase I — Proposer dissemination (`alg:proposer-dissemination`)

An honest proposer `j` commits to a single Merkle root `m` and produces a
chunk per validator under that root. At the protocol level we only observe
two effects: the proposer's signature `msg_proposer_signed j m` and the
per-recipient chunk arrival `msg_chunk_received i j m` (see
`docs/ChorusDesign.md` §3.5.1).

We split the paper's atomic "propose" into two actions to surface the
per-recipient nature of chunk delivery:

* `propose j m` — proposer's root commitment. Sets only `msg_proposer_signed`.
  Honest proposers are bound to a *single* `m` per slot via the precondition
  `∀ m2, msg_proposer_signed j m2 → m2 = m`; Byzantine proposers can
  equivocate via `byz_sign_proposer` / `byz_deliver_chunk`.
* `deliver_chunk_assigned i j m` — the chunk assigned to validator `i` under
  root `m` is delivered to `i`. For honest `j`, the proposer must have
  committed to `m` (`require msg_proposer_signed j m`), so honest delivery
  cannot fabricate chunks. Byzantine proposer delivery is covered by the
  separate `byz_deliver_chunk` action (which lifts the
  `msg_proposer_signed` requirement, modelling chunk equivocation; see §5
  of `docs/ChorusDesign.md`).

Note that `deliver_chunk_assigned` is unguarded by `phase`: chunks may
arrive at any time (the DA module continues to ingest and decode them
post-deadline). `record_chunk` (which turns chunk delivery into the
validator's `local_entry_pos`) is the action that enforces the
`pre_deadline` cutoff. -/
action propose (j : node) (m : merkle_root) {
  require ¬ is_byz j
  require is_proposer j
  -- A correct proposer encodes the ciphertext into a valid erasure
  -- encoding (recovery guarantee (ii)); only Byzantine proposers
  -- (`byz_sign_proposer`) can commit to an ill-encoded root.
  require well_encoded m
  require phase = pre_deadline
  require ∀ m2, msg_proposer_signed j m2 → m2 = m
  msg_proposer_signed j m := true
}

action deliver_chunk_assigned (i : node) (j : node) (m : merkle_root) {
  require ¬ is_byz j
  require msg_proposer_signed j m
  msg_chunk_received i j m := true
}

/- A chunk that arrives at honest validator `i` before the deadline is recorded
as a positive local entry (`alg:da` `tryIngestChunk` → `alg:voting`
`onChunkValidated`, `line:vote-positive`). An honest validator only records
the first chunk per proposer; subsequent chunks are ignored. -/
action record_chunk (i : node) (j : node) (m : merkle_root) {
  require ¬ is_byz i
  -- `tryIngestChunk` rejects chunks whose sender is not a proposer of the
  -- slot (`alg:da`: "if j ∉ s.proposers … return false").
  require is_proposer j
  require msg_chunk_received i j m
  require msg_proposer_signed j m
  require phase = pre_deadline
  require ∀ m2, ¬ local_entry_pos i j m2
  require ¬ local_entry_neg i j
  local_entry_pos i j m := true
}

/-! ## Phase II — Voting at the deadline (`alg:voting`)

At time `Ds`, each honest validator broadcasts a single proposal vote
(`line:vote-broadcast`). For each proposer `j ∈ Ps`, the validator's
per-proposer entry is positive `⟨s, j, m⟩` iff it recorded some chunk from
`j` under `m` before the deadline, and negative otherwise. The vote message
also carries the chunks backing the positive entries and releases the
validator's decryption share.

We collapse `alg:voting`'s "for all pj ∈ Ps" loop into a single atomic `vote`
action whose body uses Veil's auto-quantified capitals (`J`, `M`) to express
the per-proposer bulk update on the message-signature relations and the local
entries. The broadcast itself is `msg_vote_cast`; receivers accept a vote
only if it carries an entry for every proposer, which is why `msg_vote_cast`
implies per-proposer signatures (invariant `vote_cast_entries`). -/

action vote (i : node) {
  require ¬ is_byz i
  require phase ≠ pre_deadline
  require ¬ local_voted i

  msg_vote_pos_sig i J M := is_proposer J && local_entry_pos i J M
  msg_vote_neg_sig i J := is_proposer J && decide (∀ M, ¬ local_entry_pos i J M)
  local_entry_neg i J := is_proposer J && decide (∀ M, ¬ local_entry_pos i J M)

  local_voted i := true
  msg_vote_cast i := true
  msg_decrypt_share i := true
}

/-! ## Phase III — Fast Path (`alg:fast-path-certification`)

When 2f+1 vote-positive (resp. vote-negative) signatures exist for the same
`(s, j, m)` (resp. `(s, j)`), a FastQC can be aggregated. A validator that
observes a FastQC for every proposer broadcasts a fast commit vote (and may
*speculatively* commit — see the speculative-safety invariants below); 2f+1
broadcast fast commit votes for the same core then form a commitQC, the fast
path's finalization certificate. -/

/- Per-validator FastQC aggregation: `i` observes a supermajority of
positive vote signatures for `(j, m)` and records the resulting FastQC
in its own `local_fastqc_pos i j m` (`line:fast-formqc`). Aggregation is
unilateral — any validator that has seen the underlying signatures can
perform it at any time; this includes adopting a FastQC received inside a
`FastBlock` or `FallbackVote` message, since a transferred certificate is
valid exactly when its `2f+1` signatures are. Aggregation is honest-only; a
Byzantine validator's internal certificate state is not modelled (and would
not be relied on by honest actions anyway). -/
action aggregate_fastqc_pos (i : node) (j : node) (m : merkle_root) (q : nodeset) {
  require ¬ is_byz i
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_vote_pos_sig r j m
  local_fastqc_pos i j m := true
}

action aggregate_fastqc_neg (i : node) (j : node) (q : nodeset) {
  require ¬ is_byz i
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_vote_neg_sig r j
  local_fastqc_neg i j := true
}

/- Per-proposer fast commit signing: validator `i` signs a positive fast
commit vote entry for proposer `j` with root `m`, justified by `i`'s own
FastQC observation. The signature reaches the network only with
`cast_fast_commit` (the paper's commit vote is a single broadcast); the
`commitqc_*` certificates therefore additionally require `msg_commit_cast`
of every contributor. -/
action commit_sign_pos (i : node) (j : node) (m : merkle_root) {
  require ¬ is_byz i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require is_proposer j
  require local_fastqc_pos i j m
  msg_commit_pos_sig i j m := true
}

action commit_sign_neg (i : node) (j : node) {
  require ¬ is_byz i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require is_proposer j
  require local_fastqc_neg i j
  msg_commit_neg_sig i j := true
}

/- Cast (broadcast) the fast commit vote once every proposer has been signed.
This sets `pathVote = fast` (`line:fast-pathvote`): the commit vote and the
fallback vote are mutually exclusive. -/
action cast_fast_commit (i : node) {
  require ¬ is_byz i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require ∀ J, is_proposer J →
    ((∃ M, msg_commit_pos_sig i J M) ∨ msg_commit_neg_sig i J)
  msg_commit_cast i := true
  local_path i := fast
}

/- Assemble and broadcast a fast commit certificate entry
(`line:fast-collect-commit` / `line:fast-broadcast-commitqc`): `2f+1`
matching broadcast commit votes aggregate into a transferable certificate.
No honesty requirement — a Byzantine holder of the signatures can assemble
the same (valid) certificate, and receivers verify it against the
signatures, so the action's precondition is the validity check itself. -/
action broadcast_commitqc_pos (j : node) (m : merkle_root) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit_pos_sig r j m ∧ msg_commit_cast r
  msg_commitqc_pos j m := true
}

action broadcast_commitqc_neg (j : node) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit_neg_sig r j ∧ msg_commit_cast r
  msg_commitqc_neg j := true
}

/-! ## Phase III — Fallback Path (`alg:fallback`)

From time `Ds + Δ`, a validator that has received at least `2f+1` proposal
votes and has not cast a fast commit vote enters the fallback path
(`line:fb-pathvote-guard`): for each proposer it casts a fallback signed
entry, then broadcasts its fallback vote. On the wire a fallback vote
carries, per proposer, only a FastQC or the *sender's own* signed entry —
the receipt rule rejects anything else (`line:fb-accept`, the 2026-07-07
receipt restriction) and harvests carried FastQCs (`line:fb-harvest`).
EquivCerts and FallbackQCs exist only as objects assembled at propose
time from the signed entries in `M_i` (the atomic build,
`line:fb-build-entry`–`line:fb-formqc`), where the per-proposer evidence
precedence `FastQC ≻ EquivCert ≻ FallbackQC` orders the build cases; in
the monotone model the certificates are ghost predicates over the
signature relations — precisely that derived-at-build-time reading — and
the precedence is resolved at the MVBA validity check.

The "received ≥ 2f+1 votes" guard is modelled as a witnessed supermajority
of *broadcast* votes (`msg_vote_cast`). This guard is load-bearing for
proposal inclusion (`prop:honest-positive-entry`): any 2f+1 broadcast votes
contain f+1 honest ones, which pin an on-time honest proposer's entry. -/

/- Per-proposer fallback signing, positive case (`line:fb-positive-entry`).
Per the paper an honest validator's fallback signed entry for proposer `j`
is positive `⟨s, j, m⟩` iff *all* of:

  (b) it collected `f+1` valid positive votes for `(j, m)`;
  (c) the data is reconstructible — `alg:da.isDecoded(m)` — i.e. `f+1`
      chunks for `(j, m)` are available (delivered somewhere on the
      network, in the monotone chunk-delivery abstraction of
      `docs/ChorusDesign.md` §3.5.2);
  (d) the reconstructed data re-encodes to `m` (`alg:da`
      `line:da-reencode`; the paper's proof sketch: an honest validator
      casts fallback-yes only after reconstructing the proposal and
      checking that it re-encodes to the root) — the model's
      `well_encoded m`.

The signer needs no positive entry of its own (`local_entry_pos i j m`): a
validator that missed its assigned chunk before the deadline may still
positive-sign once it observes f+1 votes and the data decodes. The proposer
signature `σ_p` the positive entry carries is the network fact
`msg_proposer_signed j m`, recovered from the f+1 vote quorum — which holds
≥ 1 honest voter whose `local_entry_pos` implies `msg_proposer_signed`
(`local_entry_pos_signed`).

Note that (c) is implied by (b) at the network level (invariant
`vote_pos_quorum_implies_decodable`): every *valid* positive vote carries
its chunk, so f+1 positive votes put f+1 chunks on the network. We keep (c)
as an explicit precondition because `isDecoded` is a real check the
protocol performs. -/
action fb_sign_pos (i : node) (j : node) (m : merkle_root) (q qc : nodeset) {
  require ¬ is_byz i
  require phase = post_fb_arm ∨ phase = post_mvba_arm
  require local_voted i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require is_proposer j
  -- (guard) ≥ 2f+1 proposal votes received (`line:fb-pathvote-guard`).
  require ∃ qv, nset.supermajority qv ∧ ∀ r, nset.member r qv → msg_vote_cast r
  -- (b) f+1 positive votes for (j, m).
  require nset.greater_than_third q
  require ∀ r, nset.member r q → msg_vote_pos_sig r j m
  -- (c) Data-availability threshold (`isDecoded`): f+1 chunks for (j, m).
  require nset.greater_than_third qc
  require ∀ r, nset.member r qc → msg_chunk_received r j m
  -- (d) Re-encode consistency: the decoded data reproduces `m`.
  require well_encoded m
  msg_fb_pos_sig i j m := true
}

/- Per-proposer fallback signing, negative case. The paper's validator signs
negative for `j` iff, *among the ≥ 2f+1 votes it received*, no root has
f+1 positive votes with decodable data that re-encodes to the root. The
witnessed quorum `qv` of broadcast votes stands for the votes the validator
has received; the complement condition is stated relative to `qv`. (A
validator may have received more than `qv`; behaviours in which it
negative-signs although a positive quorum exists outside `qv` are
deliberately retained — they are real under asynchrony.)

The `well_encoded M` conjunct inside the negation admits the paper's
re-encode-failure case (`subsection:chorus-proof`, closing parenthetical):
an honest validator that gathers `f+1` yes votes on a root whose chunks
fail to re-encode marks the root invalid and signs negative anyway. This
is the culprit case that involves no equivocation — only an invalidly
encoded root — which is why the speculative-finality properties below take
`no_invalid_encoding` alongside `no_equivocation`. -/
action fb_sign_neg (i : node) (j : node) (qv : nodeset) {
  require ¬ is_byz i
  require phase = post_fb_arm ∨ phase = post_mvba_arm
  require local_voted i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require is_proposer j
  -- (guard) ≥ 2f+1 proposal votes received (`line:fb-pathvote-guard`).
  require nset.supermajority qv
  require ∀ r, nset.member r qv → msg_vote_cast r
  -- Negative iff no root has, within the received votes, an f+1 positive
  -- quorum with decodable data that re-encodes to the root (the `else`
  -- branch of `line:fb-cast-entry`, with `line:da-reencode` marking
  -- ill-encoded roots invalid).
  require ∀ M q qc, ¬ (nset.greater_than_third q ∧
    (∀ r, nset.member r q → nset.member r qv ∧ msg_vote_pos_sig r j M) ∧
    nset.greater_than_third qc ∧
    (∀ r, nset.member r qc → msg_chunk_received r j M) ∧
    well_encoded M)
  msg_fb_neg_sig i j := true
  local_fb_neg_qv i j qv := true
}

/- Broadcast the fallback vote once every proposer carries a fallback signed
entry; this signs `⟨fallback, s⟩` and sets `pathVote = fallback`. -/
action cast_fallback_vote (i : node) {
  require ¬ is_byz i
  require phase = post_fb_arm ∨ phase = post_mvba_arm
  require local_voted i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require ∀ J, is_proposer J →
    ((∃ M, msg_fb_pos_sig i J M) ∨ msg_fb_neg_sig i J)
  msg_fallback_sig i := true
  local_path i := fallback
}

/-! ## MVBA oracle (`mod:mvba`)

The paper's MVBA module (`p2_mvba.tex`) exposes `propose(B)` (a validator
proposes a valid meta-block, thereby *starting to participate*),
`abandon()` (it stops participating), and the output `decide(B)`; it has
**no certificate output** — its guarantees are the five properties
*Agreement*, *Integrity*, *External validity*,
*`ℓ_MVBA`-Termination* (conditioned on all correct validators proposing
and none abandoning before the bound), and *Quiescence* (no protocol
message outside the propose–abandon window). The oracle here maps onto
that interface as follows:

* `propose` has no dedicated action: the *existence* of an honest
  proposal is the ghost `mvba_invoked` (the fallback trigger or the
  paper's case-(a) trigger at the MVBA arm), which gates every decide.
* `abandon` is absent — this is a single-slot model and abandonment is
  Cadence/Conductor-driven (`line:fb-abandon` merely forwards it); the
  conditioning of `ℓ_MVBA`-Termination on non-abandonment is therefore
  moot here and is absorbed into the (A-mvba) meta-axiom's wording (see
  the Liveness section).
* `decide(B')` is decomposed per proposer into `mvba_decide_pos` /
  `mvba_decide_neg`, with `mvba_terminate` marking delivery of the full
  vector. Each decision is gated by:
  * **External validity** — the decided entry is certificate-backed: a
    FastQC-shaped entry needs a `2f+1` vote quorum; a fallback-shaped
    entry (FallbackQC or EquivCert) additionally needs `FBCert` (`2f+1`
    fallback signatures), because only fallback meta-blocks may carry
    such entries and every valid fallback meta-block includes `FBCert`
    (§`subsection:fallback_path`). Note the certificates a proposal
    carries are *assembled at propose time* from the signed entries in
    `M_i` (`line:fb-build-entry`–`line:fb-formqc`) — network-visible
    signatures, which is exactly the ghost-relation reading here.
  * **Agreement** — no conflicting prior decision for the same proposer.
  * **Integrity** (decide at most once) — per-proposer: a prior decision
    for `j` pins any further one, and `mvba_complete` closes the oracle.
* *Quiescence*'s model shadow is phase confinement (`mvba_decided_phase`,
  `fbcommit_sig_phase`); the timing content is out of scope (untimed
  model).

The paper's agreement proof (`prop:agreement-entries`, restructured in
the 2026-07-07 revision) runs through `fbCommitQC`/`commitQC` quorum
intersections plus MVBA Integrity; the model bakes oracle agreement into
the firing rules and recovers the fast-vs-fallback case as a pure quorum
argument: a commitQC and an `FBCert` are two supermajorities whose honest
common member would have had to vote both paths — structurally
impossible.

The evidence conditions are deliberately *certificate-checkable* (network
predicates), not conditions on honest validators' internal state: the MVBA
can only verify what a proposal carries. -/

action mvba_decide_pos (j : node) (m : merkle_root) {
  require phase = post_mvba_arm
  require ¬ mvba_complete
  require is_proposer j
  require mvba_invoked
  -- External validity.
  require vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)
  -- MVBA agreement (per-proposer).
  require ∀ m2, mvba_decided_pos j m2 → m = m2
  require ¬ mvba_decided_neg j
  mvba_decided_pos j m := true
}

action mvba_decide_neg (j : node) {
  require phase = post_mvba_arm
  require ¬ mvba_complete
  require is_proposer j
  require mvba_invoked
  -- External validity: a negative FastQC, or (with FBCert) a negative
  -- FallbackQC or an EquivCert (equivocation excludes the proposer,
  -- §`subsection:fallback_path`).
  require vote_quorum_neg j ∨ ((fb_quorum_neg j ∨ equiv_evidence j) ∧ fbcert)
  -- MVBA agreement.
  require ∀ m, ¬ mvba_decided_pos j m
  mvba_decided_neg j := true
}

action mvba_terminate {
  require phase = post_mvba_arm
  require ¬ mvba_complete
  require mvba_invoked
  -- every proposer has a decided entry
  require ∀ J, is_proposer J →
    ((∃ M, mvba_decided_pos J M) ∨ mvba_decided_neg J)
  mvba_complete := true
}

/-! ## Fallback commit round (`alg:fallback`,
`line:fb-mvba-decide`–`line:fb-finalize`)

An MVBA decision does not finalize by itself (2026-07-07 paper revision):
upon `MVBA[s].decide(B')` each decider first waits, for every positive
FallbackQC entry `⟨s, j, m⟩` in `B'`, until it has received and validated
its own assigned chunk under `m` — re-broadcasting that chunk, so the
eventual certificate also attests data availability
(`line:fb-commit-wait`) — and then broadcasts a `FallbackCommitVote` over
the decided entries (`line:fb-commitvote`). `2f+1` such votes aggregate
into the transferable `fbCommitQC` (`line:fb-collect-commit` /
`line:fb-formcommitqc`), and finalization happens on `fbCommitQC` receipt
(`line:fb-recv-commit` / `line:fb-finalize`).

Modelling notes:

* **Chunk re-dissemination is its own action** (`redisseminate_chunk`):
  once `f+1` chunks for `(j, m)` are on the network (`chunk_quorum` —
  the erasure-decode threshold, the model's `alg:da.isDecoded`), any
  holder of the reconstruction can re-encode the proposal and send
  validator `i` its assigned chunk. This is the protocol content of
  `line:fb-redisseminate` and of the chunk re-broadcast in
  `line:fb-commit-wait`. Without it the DA wait below could starve for a
  *Byzantine* proposer's decided root: honest `deliver_chunk_assigned`
  requires an honest proposer, and `byz_deliver_chunk` is unfair
  ((F-byz)). Like `deliver_chunk_assigned` it is unguarded by `phase`
  and carries no honesty requirement on an (anonymous) sender — its
  precondition is the network-level capability itself, the same idiom as
  `broadcast_commitqc_*`.
* **The DA wait covers every decided-positive root.** The paper waits
  only under positive *FallbackQC* entries (`line:fb-commit-foreach`;
  FastQC entries already carry chunk-backed vote supermajorities). The
  model does not track which certificate backed an MVBA decision, so
  `cast_fb_commit` waits for the validator's chunk under *every*
  decided-positive root. This is a strictly stronger guard on an honest
  action: safety-neutral (it only removes behaviours), and fair progress
  is preserved because every decided-positive root is decodable
  (`mvba_decided_pos_chunks_decodable`) and proposer-signed
  (`mvba_decided_pos_proposer_signed`), so `redisseminate_chunk` can
  always deliver the missing chunk ((F-justice)).
* **Participation gating** (the paper's standing convention that every
  message-sending rule requires active participation,
  §`subsection:chorus-protocol-overview`) lives at the Cadence/Conductor
  layer: this single-slot model has no `abandon()` input, so
  participation is implicit; the phase guard is the in-model shadow of
  the MVBA-window confinement (cf. `lemma:chorus-quiescence`). -/
action redisseminate_chunk (i : node) (j : node) (m : merkle_root) {
  -- `alg:da` ingests chunks only for the slot's proposers.
  require is_proposer j
  -- Chunk validation: the chunk header must verify against the
  -- proposer's signed root.
  require msg_proposer_signed j m
  -- Reconstructability (`alg:da.isDecoded`): f+1 chunks for `(j, m)`
  -- delivered on the network. The (anonymous) sender re-encodes and
  -- sends `i` its assigned chunk.
  require chunk_quorum j m
  msg_chunk_received i j m := true
}

action cast_fb_commit (i : node) {
  require ¬ is_byz i
  require phase = post_mvba_arm
  -- The validator has decided: `line:fb-mvba-decide` delivers the full
  -- entry vector `B'` at once, whose model shadow is the completed
  -- per-proposer decision relation (`mvba_complete_per_proposer`).
  require mvba_complete
  -- DA wait (`line:fb-commit-wait`): own assigned chunk received and
  -- validated under every decided-positive root (see the section note
  -- on why this covers all positives, not only FallbackQC-backed ones).
  require ∀ J M, is_proposer J → mvba_decided_pos J M → msg_chunk_received i J M
  msg_fbcommit_sig i := true
}

/-! ## Commit decision (finalization)

A validator finalizes only on a *commitment proof* (`lemma:chorus-agreement`
proof): a fast commit certificate (`line:fast-recv-commitqc` /
`line:fast-finalize`) or a fallback commit certificate `fbCommitQC`
(`line:fb-recv-commit` / `line:fb-finalize`). Both are transferable, and
finalization on receipt has no active-participation precondition, so the
precondition is existence of the certificate on the network. An MVBA
decision alone does *not* finalize (2026-07-07 paper revision — the
fallback commit round above sits between decision and finalization);
since the entries an `fbCommitQC` carries are the MVBA-decided vector
(see `msg_fbcommit_sig`), the model's fallback finalization route is the
conjunction `fbcommitqc ∧ mvba_decided_*`.

Holding a FastQC for every proposer without a commitQC permits only a
*speculative* commit (`alg:fast-path-certification`, "speculatively commit"),
which the paper allows to be reverted under equivocation; it is
deliberately *not* a finalization route here. See the speculative-safety
invariants below for the checked claim about when speculation is safe.

We decompose the per-entries finalization into per-proposer assignment
actions `commit_assign_pos` / `commit_assign_neg` followed by a
`finalize_commit` umbrella action (the standard Veil idiom for atomic
for-loops). -/
action commit_assign_pos (i : node) (j : node) (m : merkle_root) {
  require ¬ is_byz i
  require ¬ local_committed i
  require is_proposer j
  -- A broadcast fast commit certificate for (j, m), or a fallback commit
  -- certificate over the decided entries (`line:fb-recv-commit`).
  require msg_commitqc_pos j m ∨ (fbcommitqc ∧ mvba_decided_pos j m)
  -- Per-proposer single-choice: cannot overwrite a different root.
  require ∀ m', local_committed_pos i j m' → m' = m
  -- Cannot conflict with an already-decided negative.
  require ¬ local_committed_neg i j
  local_committed_pos i j m := true
}

action commit_assign_neg (i : node) (j : node) {
  require ¬ is_byz i
  require ¬ local_committed i
  require is_proposer j
  require msg_commitqc_neg j ∨ (fbcommitqc ∧ mvba_decided_neg j)
  -- Cannot conflict with an already-decided positive entry.
  require ∀ m, ¬ local_committed_pos i j m
  local_committed_neg i j := true
}

action finalize_commit (i : node) {
  require ¬ is_byz i
  require ¬ local_committed i
  require ∀ J, is_proposer J →
    ((∃ M, local_committed_pos i J M) ∨ local_committed_neg i J)
  local_committed i := true
}

/-! ## Byzantine adversary

### Threat model

The adversary controls some set of nodes `B ⊆ Π` with `|B| ≤ f` (captured by
the `ByzNodeSet.is_byz` predicate and its quorum-intersection axioms). Within
that bound the adversary is *fully Byzantine*:

* It may **sign any network-valid message attributed to a Byzantine
  signer**. Cryptographic unforgeability prevents it from signing as an
  honest node: the `msg_*` relations grow for Byzantine signers only via
  the actions below, and for honest signers only via honest actions.
* **Network validity is enforced.** Honest receivers discard malformed
  messages, so a message that no honest receiver would accept never enters
  any quorum an honest validator (or the MVBA) observes. The Byzantine
  actions therefore mirror the receivers' validity checks:
  - a positive vote entry must carry the signer's valid assigned chunk
    (`alg:fast-path-certification`, receive handler) — `byz_sign_vote_pos`
    requires `msg_chunk_received r j m`;
  - a broadcast vote must carry an entry for every proposer —
    `byz_cast_vote` requires per-proposer signatures;
  - a positive fallback entry must carry a verifying proposer signature
    `σ_p` — `byz_sign_fb_pos` requires `msg_proposer_signed j m`.
* It may **equivocate**. A Byzantine proposer may produce two distinct
  signed chunk headers `⟨s, j, m₁⟩` and `⟨s, j, m₂⟩` with `m₁ ≠ m₂` (two
  firings of `byz_sign_proposer`), and may selectively deliver the
  corresponding chunks to disjoint subsets of validators via
  `byz_deliver_chunk`. The protocol-level evidence of this equivocation is
  the `equiv_evidence` certificate, which lets the MVBA decide negative on
  `j`'s output. A Byzantine *validator* may likewise cast inconsistent
  votes / fallback signatures / commit votes through the per-relation
  actions below.
* It has **no power over** honest validators' local state, aggregated
  honest certificates, MVBA decisions, or the phase — these are set only by
  their explicit honest/oracle actions.

### Why per-relation actions rather than a single `transition`

A single monolithic `transition byz_step` listing per-relation "pin honest"
and "monotone Byzantine" clauses produced an O(#relations)-conjunct
disjunctive formula whose elaboration exceeded Lean's heartbeat budget.
Splitting into per-relation actions gives the Veil frame condition for free
— each action only updates one relation — and is conceptually clearer (one
action per adversarial *capability*). The reachable-state semantics is
preserved: any combined change decomposes into a sequence of these actions. -/

action byz_sign_proposer (j : node) (m : merkle_root) {
  require is_byz j
  msg_proposer_signed j m := true
}

action byz_deliver_chunk (i : node) (j : node) (m : merkle_root) {
  require is_byz j
  msg_chunk_received i j m := true
}

action byz_sign_vote_pos (r : node) (j : node) (m : merkle_root) {
  require is_byz r
  -- A positive vote entry is network-valid only with the signer's valid
  -- *assigned* chunk attached; votes with unbacked positive entries are
  -- discarded by every honest receiver. (The receive handler's guard —
  -- `alg:fast-path-certification`: the carried chunk must have the
  -- sender's chunk index and match the entry's root — was tightened to
  -- say exactly this in the 2026-07-07 paper revision; this requirement
  -- anticipated it, and it is what makes `f+1` accepted positive votes
  -- pin `f+1` *distinct* chunks, i.e. `vote_pos_quorum_implies_decodable`
  -- honest about `isDecoded`.)
  require msg_chunk_received r j m
  msg_vote_pos_sig r j m := true
}

action byz_sign_vote_neg (r : node) (j : node) {
  require is_byz r
  msg_vote_neg_sig r j := true
}

action byz_cast_vote (r : node) {
  require is_byz r
  -- A broadcast vote is network-valid only if it carries a signed entry
  -- for every proposer.
  require ∀ J, is_proposer J →
    ((∃ M, msg_vote_pos_sig r J M) ∨ msg_vote_neg_sig r J)
  msg_vote_cast r := true
}

action byz_sign_fb_pos (r : node) (j : node) (m : merkle_root) {
  require is_byz r
  -- A positive fallback signed entry carries the proposer's signature σ_p
  -- on ⟨s, j, m⟩; receivers verify it. Re-encode validity is deliberately
  -- NOT required here: it is the caster's local computation over the
  -- reconstructed data, which a receiver cannot re-check at receipt time,
  -- so a Byzantine caster may fallback-yes an ill-encoded root.
  require msg_proposer_signed j m
  msg_fb_pos_sig r j m := true
}

action byz_sign_fb_neg (r : node) (j : node) {
  require is_byz r
  msg_fb_neg_sig r j := true
}

action byz_sign_fallback (r : node) {
  require is_byz r
  msg_fallback_sig r := true
}

action byz_sign_commit_pos (r : node) (j : node) (m : merkle_root) {
  require is_byz r
  msg_commit_pos_sig r j m := true
}

action byz_sign_commit_neg (r : node) (j : node) {
  require is_byz r
  msg_commit_neg_sig r j := true
}

action byz_cast_commit (r : node) {
  require is_byz r
  msg_commit_cast r := true
}

action byz_sign_fbcommit (r : node) {
  require is_byz r
  -- No validity requirement: receivers verify only the signature, and
  -- "matching entries" is enforced at aggregation — which the nullary
  -- relation over-approximates in the adversary's favour (see
  -- `msg_fbcommit_sig`).
  msg_fbcommit_sig r := true
}

action byz_release_msg_decrypt_share (r : node) {
  require is_byz r
  msg_decrypt_share r := true
}

/-! ## Safety properties

The principal property is *agreement* (`lemma:chorus-agreement`): any two
honest validators that commit slot `s` commit the same core. -/

safety [agreement_pos]
  ∀ (I1 I2 : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 ∧
    local_committed I1 ∧ local_committed I2 ∧
    local_committed_pos I1 J M1 ∧ local_committed_pos I2 J M2 →
    M1 = M2

safety [agreement_pos_neg]
  ∀ (I1 I2 : node) (J : node) (M : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 ∧
    local_committed I1 ∧ local_committed I2 ∧
    local_committed_pos I1 J M →
    ¬ local_committed_neg I2 J

safety [integrity_pos]
  ∀ (I : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I ∧ local_committed_pos I J M1 ∧ local_committed_pos I J M2 →
    M1 = M2

safety [integrity_pos_neg]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I → ¬ (local_committed_pos I J M ∧ local_committed_neg I J)

/-! ### Hiding (`lemma:chorus-hiding`, protocol layer)

The slot key opens every proposal ciphertext of the slot, and reconstructing
it takes `f+1` extraction shares (§`appendix:encryption`). At most `f`
shares can come from Byzantine validators, and an honest validator releases
its share only with its deadline vote — so the key cannot be reconstructed
while the slot is still `pre_deadline`. Together with the TIBE secrecy
axiom (`ThresholdIBE.decrypt_secret` in [`Primitives.lean`](./Primitives.lean),
which reduces payload secrecy to share-threshold reconstruction) and the
paper's random-oracle simulation (§`appendix:encryption`), this yields the
hiding property: proposal contents are hidden until the deadline. -/

safety [hiding_until_deadline]
  slot_key_released → phase ≠ pre_deadline

/-! ### Proposal inclusion (`lemma:chorus-proposal-inclusion`)

If a correct proposer's on-time dissemination reached every honest
validator (`all_honest_recorded j m` — the protocol-level shadow of the
paper's `s.deadline − Δ ≥ GST` premise, see `prop:honest-positive-entry`),
then no honest validator ever commits a negative entry for `j`, and every
committed positive entry for `j` carries the proposer's root `m`. -/

safety [proposal_inclusion]
  ∀ (J I : node) (M M' : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz I ∧ local_committed_pos I J M' →
    M' = M

safety [proposal_inclusion_no_neg]
  ∀ (J I : node) (M : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz I →
    ¬ local_committed_neg I J

/-! ### Speculative finality (`p1_informal.tex`, speculative commit)

A validator holding FastQCs for every proposer may speculatively commit
before the commitQC forms. The paper's headline claim is that a
speculative commit "may be reverted ... only if some validator
equivocated"; the proof sketch's closing parenthetical
(`subsection:chorus-proof`) widens the culprit set to the proposer
*committing to an invalidly encoded root*: an honest validator that
gathers `f+1` yes votes on a root whose chunks fail to re-encode casts
fallback-no with no equivocation anywhere — "either way the proposer is
the culprit". Checked here against exactly that culprit set: in any
reachable state free of vote and proposer equivocation
(`no_equivocation`) in which no proposer has committed to an
invalidly encoded root (`no_invalid_encoding`), a validator's own
positive FastQC — its speculative value — agrees with every finalized
commit. (Formerly stated under `no_equivocation` alone, which sufficed
only while the DA re-encode check was unmodelled — the 2026-08 external
audit's Finding 1; `fb_sign_neg` now admits the re-encode-failure case
and the hypothesis matches the paper's.) -/

safety [speculative_agreement_pos]
  no_equivocation → no_invalid_encoding →
  ∀ (I1 I2 : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 ∧
    local_fastqc_pos I1 J M1 ∧ local_committed_pos I2 J M2 →
    M1 = M2

safety [speculative_agreement_pos_neg]
  no_equivocation → no_invalid_encoding →
  ∀ (I1 I2 : node) (J : node) (M : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 ∧ local_fastqc_pos I1 J M →
    ¬ local_committed_neg I2 J

/-! ## Auxiliary invariants

Inductive supports for the safety properties. They state local consistency
between signed messages and validator local state, plus quorum-intersection
consequences. -/

invariant [proposer_unique_root]
  ∀ (J : node) (M1 M2 : merkle_root),
    ¬ is_byz J ∧ msg_proposer_signed J M1 ∧ msg_proposer_signed J M2 →
    M1 = M2

invariant [local_entry_pos_signed]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_entry_pos I J M → msg_proposer_signed J M

invariant [local_entry_unique]
  ∀ (I : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I ∧ local_entry_pos I J M1 ∧ local_entry_pos I J M2 →
    M1 = M2

invariant [local_entry_pos_neg_excl]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I → ¬ (local_entry_pos I J M ∧ local_entry_neg I J)

-- Every recorded positive entry is backed by the recorded chunk
-- (`record_chunk` requires delivery). Basis of the data-availability chain.
invariant [local_entry_pos_chunk]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_entry_pos I J M → msg_chunk_received I J M

/- The atomic `vote` action sets `local_voted R` together with the per-proposer
`msg_vote_*_sig` entries and `local_entry_neg`, so the link "`local_voted ↔
honest signer has signed`" holds structurally after `vote` fires — and the
invariants below need only constrain honest signers' signatures (Byzantine
signers go through the `byz_sign_vote_*` actions).

The "signed-implies-voted" invariants make that structural link explicit.
Without them, the SMT-inductive argument for the `*_backed` invariants
fails: the `vote` action's body uses a plain assignment, not a monotone
disjunction, so the solver cannot rule out a state in which an honest
validator had `msg_vote_pos_sig` set before voting; with these invariants in
scope, that state is contradictory. -/
invariant [vote_sig_pos_implies_voted]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ msg_vote_pos_sig R J M → local_voted R

invariant [vote_sig_neg_implies_voted]
  ∀ (R : node) (J : node),
    ¬ is_byz R ∧ msg_vote_neg_sig R J → local_voted R

invariant [local_entry_neg_implies_voted]
  ∀ (R : node) (J : node),
    ¬ is_byz R ∧ local_entry_neg R J → local_voted R

invariant [vote_cast_implies_voted]
  ∀ (R : node),
    ¬ is_byz R ∧ msg_vote_cast R → local_voted R

invariant [voted_implies_cast]
  ∀ (R : node),
    ¬ is_byz R ∧ local_voted R → msg_vote_cast R

-- An honest validator votes only after the deadline; with monotone phase
-- this timestamps every voting artefact. Basis of `hiding` and of the
-- phase reasoning in the proposal-inclusion invariants.
invariant [voted_post_deadline]
  ∀ (R : node),
    ¬ is_byz R ∧ local_voted R → phase ≠ pre_deadline

-- Decryption shares are released only with the vote (honest signers).
invariant [share_implies_voted]
  ∀ (R : node),
    ¬ is_byz R ∧ msg_decrypt_share R → local_voted R

invariant [vote_pos_from_local]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ msg_vote_pos_sig R J M →
    local_entry_pos R J M

invariant [vote_neg_from_local]
  ∀ (R : node) (J : node),
    ¬ is_byz R ∧ msg_vote_neg_sig R J →
    (∀ M, ¬ local_entry_pos R J M) ∧ local_entry_neg R J

invariant [vote_unique_pos]
  ∀ (R : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz R ∧ msg_vote_pos_sig R J M1 ∧ msg_vote_pos_sig R J M2 →
    M1 = M2

invariant [vote_unique_pos_neg]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R → ¬ (msg_vote_pos_sig R J M ∧ msg_vote_neg_sig R J)

-- An honest validator that has voted and holds a positive entry has that
-- entry's signature on the network (the vote is atomic over all
-- proposers, and entries are frozen at the deadline while voting happens
-- after it).
invariant [voted_entry_pos_signed]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ is_proposer J ∧ local_voted R ∧ local_entry_pos R J M →
    msg_vote_pos_sig R J M

-- A broadcast vote carries an entry for every proposer (receivers discard
-- incomplete votes; `byz_cast_vote` mirrors the check).
invariant [vote_cast_entries]
  ∀ (R : node) (J : node),
    msg_vote_cast R ∧ is_proposer J →
    ((∃ M, msg_vote_pos_sig R J M) ∨ msg_vote_neg_sig R J)

-- Every network-valid positive vote signature — honest or Byzantine — is
-- backed by the signer's delivered chunk: honest votes by
-- `local_entry_pos_chunk`, Byzantine ones by the validity precondition of
-- `byz_sign_vote_pos`. This is the σ/chunk-carrying discipline of the
-- vote message (`alg:voting`), and it is what makes the erasure-decode
-- threshold (c) a consequence of the vote threshold (b) at the network
-- level.
invariant [vote_pos_sig_chunk]
  ∀ (R : node) (J : node) (M : merkle_root),
    msg_vote_pos_sig R J M → msg_chunk_received R J M

/- "Backing-quorum" auxiliaries link each aggregated FastQC to a supermajority
of underlying signed votes. These are *not* in EPR (they have an `∃ q :
nodeset` binder), but they are the standard idiom in Veil for recovering
quorum-intersection arguments on derived certificates; compare
`voted_requires_echo_quorum_or_vote_quorum` in Veil's own
`Examples/Ivy/ReliableBroadcast.lean`. -/
invariant [local_fastqc_pos_backed]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_fastqc_pos I J M → vote_quorum_pos J M

invariant [local_fastqc_neg_backed]
  ∀ (I : node) (J : node),
    ¬ is_byz I ∧ local_fastqc_neg I J → vote_quorum_neg J

-- FastQC uniqueness: a single honest validator cannot hold two FastQCs
-- for the same proposer with different roots. Follows from the backing
-- quorum's existence and vote_unique_pos applied to the supermajority.
invariant [local_fastqc_pos_self_unique]
  ∀ (I : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I ∧ local_fastqc_pos I J M1 ∧ local_fastqc_pos I J M2 → M1 = M2

-- Cross-validator FastQC agreement: any two honest validators' positive
-- FastQCs for the same proposer agree on the root. Follows from quorum
-- intersection (any two supermajorities share an honest validator) +
-- vote_unique_pos. This is the paper's `prop:agreement-entries`, case 1.
invariant [local_fastqc_pos_cross_unique]
  ∀ (I1 I2 : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 ∧
    local_fastqc_pos I1 J M1 ∧ local_fastqc_pos I2 J M2 → M1 = M2

-- Positive/negative FastQC exclusion: same proposer cannot have an honest
-- positive FastQC and an honest negative FastQC. Follows from the
-- intersecting-supermajority + vote_unique_pos_neg argument.
invariant [local_fastqc_pos_neg_excl]
  ∀ (I1 I2 : node) (J : node) (M : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 →
    ¬ (local_fastqc_pos I1 J M ∧ local_fastqc_neg I2 J)

-- An honest FastQC (either polarity) postdates the deadline: its backing
-- quorum contains an honest voter, and honest votes are post-deadline.
invariant [fastqc_post_deadline]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ (local_fastqc_pos I J M ∨ local_fastqc_neg I J) →
    phase ≠ pre_deadline

-- An honest positive fallback signed entry is backed by an f+1 quorum of
-- positive votes (`fb_sign_pos` (b)); persistent because signatures are.
invariant [msg_fb_pos_sig_backed]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ msg_fb_pos_sig R J M →
    ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_vote_pos_sig r J M

-- Honest fallback entries exist only for proposers (`fb_sign_*` require
-- `is_proposer`). Scopes the fallback-witness invariants below to
-- proposers without altering their quantifier shape.
invariant [fb_sig_is_proposer]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ (msg_fb_pos_sig R J M ∨ msg_fb_neg_sig R J) → is_proposer J

-- Honest fallback-path signatures postdate the fallback arm. Needed to
-- show that the proposal-inclusion premise (recorded strictly
-- pre-deadline) cannot become true after a conflicting fallback entry
-- already exists.
invariant [fb_sig_phase]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ (msg_fb_pos_sig R J M ∨ msg_fb_neg_sig R J ∨ msg_fallback_sig R) →
    (phase = post_fb_arm ∨ phase = post_mvba_arm)

/-! ### Path exclusion

The fast commit vote and the fallback vote are mutually exclusive per
honest validator (`pathVote`, `line:fast-pathvote` / the fallback guard).
This is the pivot of the paper's cross-path agreement argument
(`prop:agreement-entries`, case 3): a commitQC and an FBCert are both
supermajorities, so they share an honest validator — which would have had
to cast both votes. -/

invariant [commit_cast_path_fast]
  ∀ (R : node),
    ¬ is_byz R ∧ msg_commit_cast R → local_path R = fast

invariant [fallback_sig_path_fallback]
  ∀ (R : node),
    ¬ is_byz R ∧ msg_fallback_sig R → local_path R = fallback

invariant [commit_cast_fallback_sig_excl]
  ∀ (R : node),
    ¬ is_byz R → ¬ (msg_commit_cast R ∧ msg_fallback_sig R)

/-! ### Fast-path commit signatures are backed by the signer's own FastQC

`commit_sign_pos` / `commit_sign_neg` are the only honest producers of
`msg_commit_*_sig`, and each requires the signer's own `local_fastqc_*`.
So an honest validator's commit signature is a witness that *that
validator* has aggregated the matching FastQC. -/
invariant [commit_pos_sig_from_local_fastqc]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ msg_commit_pos_sig I J M → local_fastqc_pos I J M

invariant [commit_neg_sig_from_local_fastqc]
  ∀ (I : node) (J : node),
    ¬ is_byz I ∧ msg_commit_neg_sig I J → local_fastqc_neg I J

/-! ### Honest commit signatures are unique per (validator, proposer)

Mirrors `vote_unique_pos` / `vote_unique_pos_neg` for the commit phase.
Derivable from `commit_*_sig_from_local_fastqc` + the FastQC self-uniqueness
invariants, but stating them explicitly saves cvc5 from re-deriving the
same chain on every VC that touches honest commit signatures. -/
invariant [commit_pos_sig_unique]
  ∀ (I : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I ∧ msg_commit_pos_sig I J M1 ∧ msg_commit_pos_sig I J M2 →
    M1 = M2

invariant [commit_pos_sig_neg_excl]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I → ¬ (msg_commit_pos_sig I J M ∧ msg_commit_neg_sig I J)

/-! ### CommitQC-level consequences (`prop:agreement-entries`)

The per-proposer projections of the paper's agreement argument, stated over
the broadcast certificates `msg_commitqc_*`. Case 1 (two commitQCs) is
quorum intersection + per-validator commit-signature uniqueness; case 3
(commitQC vs. MVBA) splits on the MVBA evidence: a FastQC-shaped decision
meets the commitQC in an honest double-voter of two vote supermajorities,
and a fallback-shaped decision carries `FBCert`, which meets the commitQC
in an honest validator whose `pathVote` would have to be both `fast` and
`fallback`. All arguments are asynchronous quorum arguments — no timing is
involved. The `*_backed` / `*_votes` invariants persist, per certificate,
the two quorums those arguments intersect: the aggregated cast commit
votes, and the vote supermajority behind the honest signers' FastQCs. -/

invariant [msg_commitqc_pos_backed]
  ∀ (J : node) (M : merkle_root),
    msg_commitqc_pos J M → commitqc_pos J M

invariant [msg_commitqc_neg_backed]
  ∀ (J : node),
    msg_commitqc_neg J → commitqc_neg J

invariant [msg_commitqc_pos_votes]
  ∀ (J : node) (M : merkle_root),
    msg_commitqc_pos J M → vote_quorum_pos J M

invariant [msg_commitqc_neg_votes]
  ∀ (J : node),
    msg_commitqc_neg J → vote_quorum_neg J

invariant [commitqc_pos_unique]
  ∀ (J : node) (M1 M2 : merkle_root),
    msg_commitqc_pos J M1 ∧ msg_commitqc_pos J M2 → M1 = M2

invariant [commitqc_pos_neg_excl]
  ∀ (J : node) (M : merkle_root),
    ¬ (msg_commitqc_pos J M ∧ msg_commitqc_neg J)

invariant [commitqc_pos_mvba_consistent]
  ∀ (J : node) (M1 M2 : merkle_root),
    msg_commitqc_pos J M1 ∧ mvba_decided_pos J M2 → M1 = M2

invariant [commitqc_pos_mvba_neg_excl]
  ∀ (J : node) (M : merkle_root),
    ¬ (msg_commitqc_pos J M ∧ mvba_decided_neg J)

invariant [commitqc_neg_mvba_pos_excl]
  ∀ (J : node) (M : merkle_root),
    ¬ (msg_commitqc_neg J ∧ mvba_decided_pos J M)

/-! ### MVBA correctness lifted to invariants

Enforced by the `require` clauses of `mvba_decide_*`; lifted so the
inductive check on downstream actions can rely on them. The `*_backed`
invariants record the external-validity evidence a decision carried —
that record is what keeps the commitQC-consistency invariants above
inductive when commit votes are cast *after* the decision. -/

invariant [mvba_decided_pos_unique]
  ∀ (J : node) (M1 M2 : merkle_root),
    mvba_decided_pos J M1 ∧ mvba_decided_pos J M2 → M1 = M2

invariant [mvba_decided_pos_neg_excl]
  ∀ (J : node) (M : merkle_root),
    ¬ (mvba_decided_pos J M ∧ mvba_decided_neg J)

invariant [mvba_decided_pos_backed]
  ∀ (J : node) (M : merkle_root),
    mvba_decided_pos J M →
    vote_quorum_pos J M ∨ (fb_quorum_pos J M ∧ fbcert)

invariant [mvba_decided_neg_backed]
  ∀ (J : node),
    mvba_decided_neg J →
    vote_quorum_neg J ∨ ((fb_quorum_neg J ∨ equiv_evidence J) ∧ fbcert)

-- MVBA decisions exist only for proposers (the meta-block has one entry
-- per proposer; the oracle actions require `is_proposer`). Excludes
-- unreachable non-proposer decisions from the inductive state space.
invariant [mvba_decided_is_proposer]
  ∀ (J : node) (M : merkle_root),
    (mvba_decided_pos J M ∨ mvba_decided_neg J) → is_proposer J

-- MVBA decisions happen only at the MVBA arm (phase timestamping, used by
-- the proposal-inclusion preservation argument).
invariant [mvba_decided_phase]
  ∀ (J : node) (M : merkle_root),
    (mvba_decided_pos J M ∨ mvba_decided_neg J) → phase = post_mvba_arm

/-! ### Commit backing -/

invariant [local_committed_pos_backed]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_committed_pos I J M →
    msg_commitqc_pos J M ∨ mvba_decided_pos J M

invariant [local_committed_neg_backed]
  ∀ (I : node) (J : node),
    ¬ is_byz I ∧ local_committed_neg I J →
    msg_commitqc_neg J ∨ mvba_decided_neg J

invariant [local_committed_pos_unique]
  ∀ (I : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I ∧ local_committed_pos I J M1 ∧ local_committed_pos I J M2 →
    M1 = M2

invariant [local_committed_pos_neg_excl]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I → ¬ (local_committed_pos I J M ∧ local_committed_neg I J)

/-! ### Data availability

Every honest positive commit is backed by `f+1` chunks for the committed
root — the model-level counterpart of "`recoverProposals` does not block"
(`alg:da` `line:da-wait`; `prop:chorus-totality`). The chain runs through
`vote_pos_sig_chunk`: every network-valid positive vote carries its chunk,
so every vote quorum is itself a chunk quorum. -/

-- (b) ⇒ (c) at the network level: an f+1 positive-vote quorum makes the
-- data decodable, because valid positive votes carry chunks.
invariant [vote_pos_quorum_implies_decodable]
  ∀ (J : node) (M : merkle_root),
    (∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_vote_pos_sig r J M) →
    chunk_quorum J M

invariant [local_fastqc_pos_chunks_decodable]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_fastqc_pos I J M → chunk_quorum J M

invariant [mvba_decided_pos_chunks_decodable]
  ∀ (J : node) (M : merkle_root),
    mvba_decided_pos J M → chunk_quorum J M

invariant [msg_commitqc_pos_chunks_decodable]
  ∀ (J : node) (M : merkle_root),
    msg_commitqc_pos J M → chunk_quorum J M

invariant [local_committed_pos_implies_decodable]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_committed_pos I J M → chunk_quorum J M

/-! ### Proposal inclusion — inductive support

All invariants below are relativised to the premise
`all_honest_recorded J M`. Since honest entries are recorded strictly
pre-deadline and every conflicting artefact (vote, fallback entry, FastQC,
MVBA decision) postdates the deadline, the premise cannot become true
*after* a conflicting artefact exists — which is what keeps these
invariants inductive (the phase-timestamp invariants above supply that
argument to the solver).

The chain mirrors `prop:honest-positive-entry`: honest votes for `J` are
positive on `M` (entries are pinned), so no negative vote quorum, no
conflicting positive vote quorum, no honest negative fallback entry (any
witnessed 2f+1-vote quorum contains f+1 honest positive votes on `M`,
whose chunks make `M` decodable — this step uses
`supermajority_contains_honest_greater_than_third`), no conflicting
fallback quorum, no EquivCert (a correct proposer signs one root), hence
no conflicting MVBA decision and no conflicting commitQC. -/

invariant [inclusion_no_honest_vote_neg]
  ∀ (J R : node) (M : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz R → ¬ msg_vote_neg_sig R J

invariant [inclusion_vote_pos_unique]
  ∀ (J R : node) (M M' : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz R ∧ msg_vote_pos_sig R J M' → M' = M

invariant [inclusion_no_honest_fb_neg]
  ∀ (J R : node) (M : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz R → ¬ msg_fb_neg_sig R J

invariant [inclusion_fb_pos_unique]
  ∀ (J R : node) (M M' : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz R ∧ msg_fb_pos_sig R J M' → M' = M

invariant [inclusion_no_fastqc_neg]
  ∀ (J I : node) (M : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz I → ¬ local_fastqc_neg I J

invariant [inclusion_fastqc_pos_unique]
  ∀ (J I : node) (M M' : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz I ∧ local_fastqc_pos I J M' → M' = M

invariant [inclusion_no_commitqc_neg]
  ∀ (J : node) (M : merkle_root),
    all_honest_recorded J M → ¬ msg_commitqc_neg J

invariant [inclusion_commitqc_pos_root]
  ∀ (J : node) (M M' : merkle_root),
    all_honest_recorded J M ∧ msg_commitqc_pos J M' → M' = M

invariant [inclusion_no_mvba_neg]
  ∀ (J : node) (M : merkle_root),
    all_honest_recorded J M → ¬ mvba_decided_neg J

invariant [inclusion_mvba_pos_unique]
  ∀ (J : node) (M M' : merkle_root),
    all_honest_recorded J M ∧ mvba_decided_pos J M' → M' = M

/-! ### Speculative finality — inductive support

The paper's claim is temporal ("reverted only if ..."); its state-level
content is: while no proposer misbehaviour has occurred, nothing that
contradicts an existing FastQC can be certified. The one non-obvious step
is the negative fallback entry: an honest validator signs negative for `J`
only against a witnessed 2f+1-vote quorum `qv` in which no root had an f+1
positive sub-quorum with decodable, well-encoded data. `qv` is recorded as
the auxiliary history variable `local_fb_neg_qv`, and under
`no_equivocation` its content is pinned: every member of `qv` had cast a
complete vote, votes are monotone, and a signer has at most one entry per
proposer — so the absence of a positive sub-quorum *within qv* persists
(`fb_neg_qv_no_pos_quorum`). `no_invalid_encoding` closes the re-encode
leg: an f+1 positive sub-quorum contains an honest voter, whose entry pins
the proposer's signature on the root (`vote_pos_from_local` →
`local_entry_pos_signed`), so the root is well-encoded and its chunks are
on the network (`vote_pos_quorum_implies_decodable`) — the guard's negated
conjunction is then fully witnessed. Intersecting `qv` with any later
positive vote supermajority
(`supermajorities_intersect_in_greater_than_third`) yields an f+1 positive
sub-quorum of `qv` — contradiction. -/

invariant [fb_neg_sig_has_witness]
  ∀ (R J : node),
    ¬ is_byz R ∧ msg_fb_neg_sig R J → ∃ qv, local_fb_neg_qv R J qv

invariant [fb_neg_qv_is_proposer]
  ∀ (R J : node) (QV : nodeset),
    ¬ is_byz R ∧ local_fb_neg_qv R J QV → is_proposer J

invariant [fb_neg_qv_backed]
  ∀ (R J : node) (QV : nodeset),
    ¬ is_byz R ∧ local_fb_neg_qv R J QV →
    nset.supermajority QV ∧ (∀ r, nset.member r QV → msg_vote_cast r)

invariant [fb_neg_qv_no_pos_quorum]
  no_equivocation → no_invalid_encoding →
  ∀ (R J : node) (QV q : nodeset) (M : merkle_root),
    ¬ is_byz R ∧ local_fb_neg_qv R J QV →
    ¬ (nset.greater_than_third q ∧
       ∀ r, nset.member r q → (nset.member r QV ∧ msg_vote_pos_sig r J M))

/- The keystone lemma of the speculative argument: an honest negative
fallback entry excludes any positive vote supermajority for the same
proposer, absent equivocation. From `fb_neg_sig_has_witness` +
`supermajorities_intersect_in_greater_than_third` (intersect `qv` with
the supermajority) + `fb_neg_qv_no_pos_quorum`. -/
invariant [fb_neg_no_pos_quorum]
  no_equivocation → no_invalid_encoding →
  ∀ (R J : node) (M : merkle_root),
    ¬ is_byz R ∧ msg_fb_neg_sig R J → ¬ vote_quorum_pos J M

invariant [spec_fastqc_pos_no_mvba_neg]
  no_equivocation → no_invalid_encoding →
  ∀ (I J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_fastqc_pos I J M → ¬ mvba_decided_neg J

invariant [spec_fastqc_pos_mvba_pos_unique]
  no_equivocation → no_invalid_encoding →
  ∀ (I J : node) (M M' : merkle_root),
    ¬ is_byz I ∧ local_fastqc_pos I J M ∧ mvba_decided_pos J M' → M = M'

/-! ## Liveness — meta-argument and fair-progress invariants

This section formalises the safety-invariant ingredients of the protocol's
liveness claim:

> **(Liveness)** Under the standard fairness assumptions and the meta-theoretic
> MVBA-termination assumption stated below, every honest validator eventually
> commits every slot.

We follow the classical verification-diagrams approach for liveness in
deductive verification of distributed protocols; for a recent high-level
account see Kenneth L. McMillan, *"Toward Liveness Proofs at Scale"*, CAV
2024, §2 (Background and related work).

### Meta-argument structure

The argument has three ingredients, of which (1) and (2) are meta-level and
(3) is SMT-discharged here.

**(1) Fairness as meta-axioms.** Veil has no first-class fairness annotations
on actions. We attach the standard scheduling assumptions externally to the
model, indexed by the action's category:

* **(F-justice)** — every phase-advancement action (`advance_to_*`), every
  aggregation/observation action (`aggregate_fastqc_*`, `record_chunk`,
  `redisseminate_chunk`), and every per-validator honest action
  (`propose`, `vote`, `fb_sign_*`, `cast_fallback_vote`, `commit_sign_*`,
  `cast_fast_commit`, `cast_fb_commit`, `commit_assign_*`,
  `finalize_commit`) that is *continuously enabled* is fired eventually.
  Fairness on `redisseminate_chunk` is the model form of "re-disseminated
  chunks are eventually delivered"; its paper backing is that the
  re-encode-and-send is performed by *honest* parties
  (`line:fb-redisseminate` by every honest positive fallback signer,
  `line:fb-commit-wait` by every honest decider), so under the
  conditioned-termination premises some honest holder keeps every
  assignee's chunk in flight.
* **(F-compassion)** — strong fairness is part of the modelling vocabulary
  for the underlying implementation (whose per-validator local state is
  not monotone), but it is **not invoked** here: in Veil's
  monotone-relation framework enabledness is itself monotone — once an
  action's preconditions hold they stay holding until a negative atom
  flips false, after which the action is *permanently* disabled — so weak
  (F-justice) suffices.
* **(F-byz)** — Byzantine actions (`byz_*`) carry no scheduling preference;
  they are unfair.
* **(A-mvba)** — once `mvba_invoked` holds (either invocation trigger) and
  certificate evidence exists for every proposer, the MVBA oracle
  eventually fires `mvba_decide_pos` / `mvba_decide_neg` for every
  proposer and subsequently `mvba_terminate`. This stands in for the
  paper's `ℓ_MVBA`-Termination (`mod:mvba`, `p2_mvba.tex`), whose premise
  since the 2026-07-07 revision is twofold: (i) *all correct validators
  propose* — the per-validator implementability of which is exactly the
  receipt/propose-layer content behind the §7.2 finding (`docs/ChorusDesign.md`
  §7.2: the model's premise is network-global evidence, and
  the bridge from global evidence to every correct validator assembling
  a valid proposal is the atomic-build argument, mechanised separately);
  and (ii) *no correct validator abandons before the bound* — moot in
  this single-slot model (no `abandon()` action), and within Cadence
  discharged by Conductor totality
  (`cor:chorus-correctness-within-cadence`). The probability-1
  termination of the underlying randomised primitive remains a
  paper-level argument; see `docs/Liveness.md` and `docs/ChorusDesign.md` §7.

  (A-mvba) is **not** unconditional: whether the invocation trigger and the
  per-proposer evidence ever materialise is handled by the case split in
  (3) below.

**(2) Well-founded ranking (structural).** Chorus is a one-shot per-slot
protocol: per slot, `node`, `nodeset`, the proposer set and the set of
*active* Merkle roots are fixed a priori, so the per-slot state space is
finite. Every mutable relation is monotone (actions only add tuples — the
audit is in `docs/ChorusDesign.md` §3.1) and the phase advances in one direction. The
residual count of unset tuples is therefore a well-founded ranking that
every *helpful* firing strictly decreases; this is structural in Veil's
monotone-update semantics and needs no per-action SMT discharge. The (D)
obligation of the verification diagram is therefore discharged by the
monotonicity audit, not by SMT: stating it as `decrease_*` invariants
yields only tautologies of the form `… ∧ ¬X → ¬X`, so do not add them.

**(3) Fair progress (safety, SMT-discharged here).** Under (1) and (2), the
temporal claim reduces to: in every reachable state in which some honest
validator has not yet committed, some **fairly-scheduled** action is
enabled whose firing strictly shrinks the residual ranking. This is
strictly stronger than deadlock freedom: under (F-byz) the Byzantine
actions are unfair, so a livelock in which only Byzantine actions fire
forever would not violate plain deadlock freedom, but does violate fair
progress.

### Case split over the honest fast-path population

Let `x` be the number of honest validators that cast a fast commit vote.

* **`x ≥ 2f+1` (fast-dominant).** The honest commit votes agree per
  proposer (`local_fastqc_pos_cross_unique`), so a commitQC forms from
  honest votes alone; every honest validator then commits via
  `commit_assign_*` (whose precondition is the commitQC certificate) and
  `finalize_commit`. No MVBA needed.
* **`1 ≤ x ≤ 2f` (mixed).** Neither certificate is guaranteed from honest
  participation alone: a commitQC needs `2f+1` matching cast commit votes
  (`x` may fall short and Byzantine help is unfair), and `FBCert` needs
  `2f+1` fallback votes while only `2f+1 − x` honest validators can still
  cast one. This is exactly the regime the paper's case-(a) MVBA trigger
  covers: any honest fast-path validator's FastQCs are backed by network-
  visible vote supermajorities (`fast_path_implies_vote_quorums`), so
  every honest validator eventually aggregates a complete fast meta-block
  (F-justice on `aggregate_fastqc_*`), `mvba_invoked`'s case-(a) disjunct
  holds, per-proposer evidence exists
  (`fastqc_complete_implies_mvba_evidence`), and (A-mvba) delivers the
  complete decision vector; the *fallback commit round* then carries the
  decisions to finalization — (F-justice) on `redisseminate_chunk` and
  `cast_fb_commit` forms `fbcommitqc`, enabling `commit_assign_*` — see
  the fair-progress notes at the "Fallback commit round" invariant block.
* **`x = 0` (fallback).** All `≥ 2f+1` honest validators eventually cast
  fallback votes (per-proposer fallback signing is always enabled one way
  or the other — see `progress_fallback_signing`), so `FBCert` forms and
  `mvba_invoked` holds via the fallback trigger. Per-proposer evidence
  formation is the pigeonhole below; decisions then reach finalization
  through the commit round exactly as in the mixed branch.

**Evidence pigeonhole (mechanised).** In the `x = 0` branch, the `2f+1`
honest fallback entries for a proposer `j` split as: `f+1` negative (→ a
negative FallbackQC certificate), or `f+1` positive on one root (→ a
positive FallbackQC), or positive entries on ≥ 2 roots — each backed by an
f+1 vote quorum containing an honest voter whose entry pins a
proposer-signed root, so two distinct roots are proposer-signed and
`equiv_evidence` holds. This split-counting is not SMT-discharged in the
invariant clump — the `ByzNodeSet` abstraction cannot partition a quorum
by the value its members signed (set comprehension is outside its
language) — but it is no longer a meta step either: it is the Lean
theorem `Chorus.evidence_pigeonhole_of_reachable`
(`Cadence/Chorus/Pigeonhole.lean`), proved over reachable states for the
concrete instance family at every `n = 3f+1` and removed from the
assumption inventory (`docs/Architecture.md` §4).

### What is not encoded inside Veil

The temporal/fairness layer itself — the existential quantification over a
fair execution, the well-founded recursion on the ranking — is not encoded
inside the Veil module. That extension would require either an L2S
desugaring (see `docs/Liveness.md`) or a verification-diagram tactic family;
both are out of scope. The invariants below discharge the *fair-progress*
safety content. -/

/-! ### MVBA completion implies per-proposer decision

Lifted postcondition of `mvba_terminate`: the link between (A-mvba) and the
commit route — once `mvba_complete` holds, every honest non-committed
validator has, for every proposer, an MVBA decision supplying the
`mvba_decided_*` leg of the `commit_assign_*` precondition. The
certificate leg (`fbcommitqc`) is produced by the fallback commit round
((F-justice) on `cast_fb_commit`; see the "Fallback commit round"
invariant block below). -/
invariant [mvba_complete_per_proposer]
  mvba_complete →
    ∀ J, is_proposer J →
      ((∃ M, mvba_decided_pos J M) ∨ mvba_decided_neg J)

/-! ### Fair progress — voting

Once past the deadline, an honest validator that has not yet voted can
always fire `vote` (its precondition is phase + not-voted only); the
per-proposer positive/negative split inside the atomic action is the
excluded middle on `local_entry_pos`. Stated to make that case analysis
explicit. -/
invariant [progress_voting]
  ∀ (I J : node),
    ¬ is_byz I ∧ phase ≠ pre_deadline ∧ ¬ local_voted I ∧ is_proposer J →
    (∃ M, msg_vote_pos_sig I J M) ∨
    msg_vote_neg_sig I J ∨
    (∃ M, local_entry_pos I J M) ∨
    (∀ M, ¬ local_entry_pos I J M)

/-! ### Fair progress — fallback signing

Once some 2f+1 validators have broadcast votes, an honest validator on the
fallback path can always cast its per-proposer fallback entry: for any
witnessed quorum `qv`, either some root has an f+1 positive sub-quorum
within `qv` with decodable (`chunk_quorum`; implied at the network level,
`vote_pos_quorum_implies_decodable`), well-encoded data — then
`fb_sign_pos` is enabled — or no root has all three, which is
`fb_sign_neg`'s guard for `qv` (its `qc` witness is the `chunk_quorum`
witness). Excluded middle over the guard's evidence shape, stated to make
the case analysis explicit. -/
invariant [progress_fallback_signing]
  ∀ (I J : node) (qv : nodeset),
    ¬ is_byz I ∧ is_proposer J ∧
    nset.supermajority qv ∧ (∀ r, nset.member r qv → msg_vote_cast r) →
    (∃ (M : merkle_root) (q : nodeset), nset.greater_than_third q ∧
      (∀ r, nset.member r q → nset.member r qv ∧ msg_vote_pos_sig r J M) ∧
      chunk_quorum J M ∧ well_encoded M) ∨
    (∀ (M : merkle_root) (q : nodeset), ¬ (nset.greater_than_third q ∧
      (∀ r, nset.member r q → nset.member r qv ∧ msg_vote_pos_sig r J M) ∧
      chunk_quorum J M ∧ well_encoded M))

/-! ### Path-fast implies the validator's own FastQCs for every proposer

Honest `cast_fast_commit i` requires `msg_commit_*_sig i J _` for every
proposer `J`; each such honest signature carries the validator's own
matching local FastQC. So an honest validator on the fast path is itself a
witness that FastQC certificates exist for every proposer. -/
invariant [local_path_fast_implies_fastqcs]
  ∀ (I : node),
    ¬ is_byz I ∧ local_path I = fast →
    ∀ J, is_proposer J →
      (∃ M, local_fastqc_pos I J M) ∨ local_fastqc_neg I J

/-! ### Fair progress — the mixed branch (case-(a) bridge)

If any honest validator has taken the fast path, the backing vote
supermajorities for a full set of FastQCs are on the network: every other
honest validator can aggregate them (F-justice on `aggregate_fastqc_*`),
reach a complete fast meta-block, and thereby (i) satisfy `mvba_invoked`'s
case-(a) disjunct and (ii) supply the MVBA with per-proposer evidence. -/
invariant [fast_path_implies_vote_quorums]
  ∀ (I0 : node),
    ¬ is_byz I0 ∧ local_path I0 = fast →
    ∀ J, is_proposer J →
      (∃ M, vote_quorum_pos J M) ∨ vote_quorum_neg J

invariant [fastqc_complete_implies_mvba_evidence]
  ∀ (I : node),
    ¬ is_byz I ∧ complete_fast_metablock I →
    ∀ J, is_proposer J →
      (∃ M, vote_quorum_pos J M) ∨ vote_quorum_neg J

/-! ### Commit completeness (composition support)

A committed validator holds a decision for *every* proposer — the
persisted form of `finalize_commit`'s precondition. Needed by the
composition layer (`Chorus/Compose.lean`): the `SlotConsensus` instance
theorem assembles a committed validator's per-proposer decisions into a
total proposal vector, which requires this completeness fact about
reachable states.

NOTE: the manual cells in `Chorus/Proofs/` project the assembled
`Invariants` clump *by declaration name* (`inv_have`,
`Cadence/ProofPrelude.lean`), so new `safety`/`invariant` declarations
may go wherever they read best — the lookup re-derives every index at
elaboration time and fails loudly if a name disappears. -/
invariant [local_committed_complete]
  ∀ (I : node),
    ¬ is_byz I ∧ local_committed I →
    ∀ J, is_proposer J →
      (∃ M, local_committed_pos I J M) ∨ local_committed_neg I J

/-! ### Fallback commit round — backing, confinement, and fair progress

Support for the fallback commit round (`line:fb-mvba-decide`–
`line:fb-finalize`; appended 2026-07-07 with the round's modelling —
see the append-only NOTE above).

The fair-progress leg for the round needs no dedicated `progress_*`
case-analysis invariant: once `mvba_complete` holds, `cast_fb_commit i`'s
only non-derived precondition is the DA wait, and its satisfiability is
materialised by three enabledness facts for `redisseminate_chunk` —
`mvba_decided_is_proposer`, `mvba_decided_pos_chunks_decodable` (both
above) and `mvba_decided_pos_proposer_signed` (below) — plus the phase
confinement `mvba_complete_phase`. (F-justice) on `redisseminate_chunk`
and `cast_fb_commit` then yields `2f+1` honest commit votes, i.e.
`fbcommitqc`; `fbcommitqc_implies_mvba_complete` +
`mvba_complete_per_proposer` hand the per-proposer `commit_assign_*`
preconditions over, exactly as in the pre-round argument. -/

/- An honest fallback commit vote exists only after its signer decided,
i.e. only once the MVBA reached its complete decision vector
(`line:fb-mvba-decide` precedes `line:fb-commitvote`). -/
invariant [fbcommit_sig_backed]
  ∀ (R : node), ¬ is_byz R ∧ msg_fbcommit_sig R → mvba_complete

/- Honest fallback commit votes are confined to the MVBA phase — the
model shadow of the participation-window confinement
(`lemma:chorus-quiescence`) for the commit round. -/
invariant [fbcommit_sig_phase]
  ∀ (R : node), ¬ is_byz R ∧ msg_fbcommit_sig R → phase = post_mvba_arm

/- An `fbCommitQC` certifies the MVBA decision vector: any `2f+1` commit
votes contain an honest one (`supermajority_greater_than_third` +
`greater_than_third_one_honest`), whose vote implies `mvba_complete`
(`fbcommit_sig_backed`). Bridges the certificate to the per-proposer
`commit_assign_*` preconditions via `mvba_complete_per_proposer`. -/
invariant [fbcommitqc_implies_mvba_complete]
  fbcommitqc → mvba_complete

/- MVBA termination is confined to the MVBA phase (the phase is
terminal, so this pins it exactly). Needed as the phase leg of
`cast_fb_commit`'s enabledness. -/
invariant [mvba_complete_phase]
  mvba_complete → phase = post_mvba_arm

/- Every decided-positive root is proposer-signed: the chunk-validation
leg of `redisseminate_chunk`'s enabledness (its other leg is
`mvba_decided_pos_chunks_decodable`). Derivable on the fly — a decision
is backed by a vote or fallback quorum whose honest member's entry pins
the proposer signature — but materialised so downstream VCs need not
re-derive it (the `msg_commitqc_*` / `local_fb_neg_qv` pattern). -/
invariant [mvba_decided_pos_proposer_signed]
  ∀ (J : node) (M : merkle_root),
    mvba_decided_pos J M → msg_proposer_signed J M

/- We disable the model-check scaffolding (FinEncodableInjOnly / Enumeration
deriving on the action Label, EnumerableTransitionSystem assembly) because
(a) Chorus does not use `#model_check`, and (b) the derived
FinEncodableInjOnly instances are O(n^k) in number of actions and would blow
Lean's whnf heartbeat budget for our ~38 actions. VC generation and the
cross-file check/prove commands are unaffected. -/
set_option veil.gen.modelCheckScaffolding false
-- Emit the per-action executable extraction (`Chorus.NextAct.extracted`, a
-- `Label → VeilMultiExecM` dispatcher) for the trace-conformance monitor. This
-- is O(n) in the actions and, unlike the scaffolding above, does NOT derive the
-- O(n^k) `Enumeration`/`FinEncodableInjOnly` label instances.
set_option veil.gen.executableActions true

/- The assembled `Invariants` conjunction is large (~97 conjuncts); the
`LocalRProp` instance chain over it exceeds Lean's default instance-search
budgets, and without that instance every VC re-simplifies the full clump
(a large constant-factor slowdown of the sweep). Raise the budgets so the
pre-simplification succeeds. -/
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192

/- Witness-size instrumentation (diagnostic, cheap): the sweep reports the
per-VC proof-witness sizes, quantifying the O(action × clump) blow-up that
motivates the per-action factoring of the WP normalisation. Captured at
discharger creation, i.e. file-level like the `veil.smt.*` options. -/
set_option veil.report.witnessSizes true

/- Proof reconstruction: every cvc5 `unsat` verdict is reconstructed and
kernel-checked in Lean — cvc5 is not in the trust base of the
verification. In this file the option governs only the background
`doesNotThrow` dischargers; the invariant proofs live in the proof-file
family, which sets it itself. File-level so the dischargers capture it at
`#gen_spec` (solver options are captured there, not at the command). -/
set_option veil.smt.trust false

/- This file persists NO per-VC theorems, and cannot: real-proof
persistence here would need the environment to hold ~3.8 K reconstructed
witnesses until olean serialization, which does not fit the 32 GB
reference machine. The per-action proof files under `Chorus/Proofs/` are
the answer to that. So a VC in this development is either registry data
(claim-free by construction) or a real, kernel-checked theorem in a
`Chorus/Proofs/` olean — nothing here is proven-but-isn't. -/

/- VC registry (`docs/Dependencies.md` §1): `#gen_spec`
persists every VC's statement (as an `Expr`) plus its action/property/
style metadata into the olean, enabling the cross-file commands
(`#check_action Chorus <action>`, `#check_vc Chorus <action> <prop>`,
`#prove_action Chorus <action>`) in importing files. Solve-free, and the
eager statement elaboration it does here measures as ≈ free at this
file's scale. The registry is the proof-file family's entire statement
source: the `#prove_action`s under `Chorus/Proofs/` re-create every VC
from it. -/
set_option veil.gen.vcRegistry true

/- Proof cache (`docs/Dependencies.md` §2): consult the
content-addressed cache (`.lake/build/veilcache/`) for
the background `doesNotThrow` dischargers this file still runs, and store
their proofs. The proof-file family enables the cache itself and is the
main beneficiary: statement-unchanged rebuilds kernel-replay every cell
(~0.35 s/hit at this module's witness scale) instead of re-solving.
File-level so the dischargers capture it at `#gen_spec` (§1.9
semantics). -/
set_option veil.cache.proofs true

/- Solver configuration: Veil defaults (60 s per-goal budget,
finite-model-find ON), deliberately not overridden.

IMPORTANT: in-file dischargers capture solver options at `#gen_spec` (VC
generation), NOT at check commands — options set only around a check
command silently do not apply to solving, and Veil warns about it; on the
cross-file path the proof files read solver options at tactic runtime, so
`set_option` there works as written.

Do not "improve" the budget: a sweep at 900 s with fmf off was measured
strictly worse than the 60 s/fmf-on default — divergent queries e-match
for the full 900 s while accumulating instantiations in-process, and the
sweep exceeded 17 CPU-hours and 50 GB (swap thrash) before being killed.
The defaults are the validated configuration; seed-luck timeouts are
healed by `veil.smt.retries`
(retry with a perturbed seed, reported as "(retry k, seed k)"), with the
TR-form fallback behind that; the cells SMT cannot solve at all are
manual `#prove_vc … by <tactic>` cells in their actions' proof files
(`Chorus/Proofs/FbSignNeg.lean` records three the `well_encoded` refactor
made tractable; the current count is pinned by `#veil_status` and tabled
in `docs/Architecture.md`). -/

#gen_spec

/-! ## Verification — in the proof-file family, not here

This is a **model file** of the verified-module file family
(`docs/Architecture.md` §6): `#gen_spec` above elaborated the transition
system and persisted the VC registry — the model's entire proof
interface — and started only the (cheap) background `doesNotThrow`
checks. The 3 783 invariant VCs are proven cross-file:

* one `#prove_action Chorus <action>` per action in
  [`Chorus/Proofs/`](./Chorus/Proofs) — every registered VC re-created
  from the registry statement (identical to what an in-file sweep would
  check, by construction), solved with proof reconstruction, persisted as
  a kernel-checked theorem, and assembled into the per-action
  preservation lemma `step_<action>`. The manual quorum-intersection
  cells (SMT's e-matching diverges on them) live in their actions' proof
  files as `#prove_vc … by <tactic>` cells the command consumes as-is
  after a statement check.
* [`Chorus/Certify.lean`](./Chorus/Certify.lean) composes the
  preservation lemmas into `Chorus.invariants_of_reachable` + named
  `reachable_<property>` projections (`#gen_composition`), at the
  standard `propext`/`Classical.choice`/`Quot.sound` trust base — pinned
  there and consumed by `Chorus/Compose.lean`/`Chorus/Pigeonhole.lean`.

Interactive spot checks: `#check_vc Chorus <action> <property>` (or
`#check_action Chorus <action>`) in any importing scratch file — one at a
time; multiple concurrent check commands contend for the same discharger
scheduler and slow each other down.

IMPORTANT: Veil's own library must be built with `precompileModules := true`
(it is, in the Veil fork this project pins — `docs/Dependencies.md` §2).
Without it, Veil's discharger tactics run in the Lean IR interpreter, which
serializes tactic interpretation and caps effective parallelism at ~2–3x. -/

end Chorus
