import Veil
import Cadence.Primitives
import Cadence.QuorumCounting
import Cadence.Interfaces
import Cadence.Tooling

-- Opening this file in an editor costs the model elaboration plus the cheap
-- background `doesNotThrow` checks, and no SMT sweep; `VEIL_NO_VERIFY=1` in
-- the editor's environment skips even those. Working on the module:
-- [CLAUDE.md](../CLAUDE.md) and the `cadence-verification` skill.

/-! # Chorus — per-slot one-shot BFT consensus for Cadence

*This is a **model file** of the verified-module file family
([Architecture.md](../docs/Architecture.md) §6): it elaborates the
transition system and persists the VC registry. Its invariant VCs are
proven in the per-action files under [Chorus/Proofs](Chorus/Proofs) and
composed into the reachability certificate by
[Chorus/Certify.lean](Chorus/Certify.lean), whose `#veil_status Chorus`
pins their count.*

Chorus is the inner consensus layer of Cadence: for each slot `s` it runs an
independent one-shot Byzantine-fault-tolerant agreement instance among a set
`Π` of `n = 3f + 1` validators, with `k` concurrent *proposers* `Ps ⊆ Π`. The
slot terminates either via the fast path (two voting rounds) or via the
fallback path (one extra round of voting, an invocation of MVBA — consumed
here as the module contract `MVBASafety`, a class constraint over an
abstract state, instantiated at the verified `Mvba` model by
[System.lean](System.lean) — and a final round of commit votes on the decided entries).
This file specifies the Chorus protocol as a Veil transition system for a
*single* slot instance: state and messages are not slot-parameterised, since
the per-slot agreement instances are independent. The `slot` type below is
retained only as a placeholder for a possible multi-slot extension — see the
`is_proposer` TODO, which also notes that cross-slot independence is not
guaranteed in practice.

Paper target: [docs/PaperAlignment.md](../docs/PaperAlignment.md) §0.
Citations name what the
target's rendered PDF shows, with the LaTeX label in parentheses; the root
[README.md](../README.md) says how to resolve them (e.g. Algorithm 5, line 7 (`line:fb-pathvote-guard`)). The Chorus
chapter is Appendix C (`section:slot_agreement`), with pseudocode in Algorithm 2
(`alg:proposer-dissemination`) to Algorithm 6 (`alg:da`), and the MVBA
module specification is Module 3 (`mod:mvba`).

## Property coverage

The paper establishes six slot-consensus properties for Chorus
(Appendix C.4 (`subsection:proof_sketches`)); their status in this model:

* **Agreement** (Lemma 9 (`lemma:chorus-agreement`)) — `safety [agreement_pos]`,
  `[agreement_pos_neg]`, proven for the paper's *full-finality* commit rule
  (commitQC or MVBA certificate) by the paper's own asynchronous quorum
  argument (Proposition 1 (`prop:agreement-entries`)). No timing assumptions.
* **Proposal inclusion** (Lemma 10 (`lemma:chorus-proposal-inclusion`), a.k.a.
  censorship resistance) — `safety [proposal_inclusion]`,
  `[proposal_inclusion_no_neg]`. The paper's synchrony premise ("a correct
  proposer disseminates at `s.deadline − Δ ≥ GST`") is abstracted to its
  protocol-level consequence: *every honest validator records the positive
  entry* (`all_honest_recorded`).
* **Hiding** (Lemma 7 (`lemma:chorus-hiding`), Definition 4 (`def:hiding`)) — split across two layers.
  The cryptographic layer (TIBE unpredictability, the random-oracle
  simulation of Appendix C.2 (`appendix:encryption`)) is axiomatised in
  [Primitives.lean](Primitives.lean) (`ThresholdIBE.decrypt_secret`).
  The protocol layer — the slot key cannot be reconstructed before the
  deadline because reconstruction needs `f+1` shares and honest validators
  release shares only with their deadline vote — is `safety [hiding_until_deadline]` here.
* **Slot safety** (Lemma 8 (`lemma:chorus-slot-safety`)) — trivial in this model: it
  is single-slot, so every commit is a commit *for this slot* by
  construction.
* **Termination** (Lemma 11 (`lemma:chorus-termination`)) — proven without its bound
  as `Chorus.termination` ([Chorus/Termination.lean](Chorus/Termination.lean)).
  If every correct validator eventually invokes `participate()` and none
  invokes `abandon()` before it has finalized, then every correct validator
  finalizes, in every run under the premises
  [Chorus/Liveness.lean](Chorus/Liveness.lean) names. Those are the
  paper's caller conditions. The model has the paper's participation
  interface (`participate`, `abandon`, and `propose` as the third input,
  "Participation inputs" below), so they are stated over the model's own
  state. The model is untimed, so the `ℓ = 5Δ + ℓ_MVBA` bound and the
  Δ-synchronized-participation premise it needs
  (Definition 5 (`def:delta-synchronized-participation`)) are the timed claims'
  ([Bounds.md](../docs/Bounds.md) §6.4). The *fair-progress* safety content of the
  argument is SMT-discharged in the "Liveness" section near the end of
  this file.
* **Quiescence** (Lemma 6 (`lemma:chorus-quiescence`)) — no correct validator sends
  protocol messages outside its participation window. The model enforces
  the paper's standing convention rule for rule: every sending rule
  requires `participating i ∧ ¬ abandoned i` of its sender, and `abandon`
  forwards to the MVBA's `abandon()` (Algorithm 5, line 48 (`line:fb-abandon`)), whose own
  Quiescence (a field of `MVBASafety`) confines the MVBA's messages. The
  contract's one-step `quiescence` over these gates is proven in the
  `SlotConsensusTemporal` instance (`Chorus.own_sent_new`,
  `Chorus.mvba_sent_new`; [Chorus/Temporal.lean](Chorus/Temporal.lean)).

Additionally, `safety [speculative_agreement_pos]` / `[..._pos_neg]` check
the paper's speculative-finality claim (Section 4.2
(`subsection:fast-path-overview`): a speculative
commit "may be reverted ... only if some validator equivocated" — widened by
the proof sketch's closing parenthetical, Section 4.5 (`subsection:chorus-proof`), to a
proposer committing to an invalidly encoded root): in any state free of vote
or proposer equivocation (`no_equivocation`) in which no proposer has
committed to an invalidly encoded root (`no_invalid_encoding`), a
validator's speculative value (its own FastQC) agrees with every final
commit.

See [ChorusDesign.md](../docs/ChorusDesign.md) for a higher-level discussion of the
modelling choices, the abstractions made over the cryptographic primitives,
and the limitations of the model with respect to liveness.
-/

veil module Chorus

/-! ## Types -/

/-- A slot identifier (cf. `s ∈ Slot`, Appendix A.1 (`subsection:mcp-preliminaries`)).
Unused, since the model is single-slot (see the module header); a
placeholder for a possible multi-slot extension. -/
type slot
/-- A validator node identity. -/
type node
/-- A set of nodes; the `ByzNodeSet` instance gives supermajority/
greater-than-third quorum predicates plus the standard Byzantine
intersection axioms. -/
type nodeset
/-- A Merkle commitment to an erasure-coded encrypted proposal.
Modelled as an opaque token; binding properties are captured by
requiring the proposer's signature on `⟨s, j, m⟩` together with
the chunks themselves to determine the proposal. -/
type merkle_root

/-! The abstract state, value, entry-vector and message sorts of the MVBA
instance the fallback path consumes (Module 3 (`mod:mvba`); the "Multi-Value
Byzantine Agreement" section below). Opaque here: Chorus reads the state
only through the contract's observables, a value through the contract's
`entries` and the immutable `mval_fb`, and an entry vector through the two
immutable projections `mval_pos` / `mval_neg`. -/

/-- The MVBA instance's abstract state. -/
type mstate
/-- The MVBA's value: a meta-block representation `B′`, its entry vector
together with each positive entry's certificate kind. -/
type mvalue
/-- An entry vector `entries(B′)`, read through `mval_pos` / `mval_neg`. -/
type mentries
/-- The MVBA's messages. -/
type mmsg

/-! ## Byzantine quorum abstraction

`ByzNodeSet` packages the `is_byz` predicate together with the two quorum
sizes that arise in Chorus:

* `supermajority s ↔ |s| ≥ 2f + 1` (FastQCs, CommitQCs, FBCerts)
* `greater_than_third s ↔ |s| ≥ f + 1` (FallbackQCs, erasure decode)

Besides the standard intersection axioms, the proofs below use three
counting facts, stated as the class `Cadence.ByzNodeSetCounting`
([QuorumCounting.lean](QuorumCounting.lean)) and proven for both
concrete quorum families in [ByzQuorum.lean](ByzQuorum.lean):

* `honest_third_in_supermajority` — a supermajority contains an all-honest
  `f+1`-subset (`2f+1 − f = f+1`);
* `supermajority_meets_third` — a supermajority and an `f+1`-set share a
  (possibly Byzantine) member (`(2f+1) + (f+1) − (3f+1) = 1`);
* `supermajorities_share_third` — two supermajorities share an
  `f+1`-subset (`2(2f+1) − (3f+1) = f+1`). -/

instantiate nset : ByzNodeSet node nodeset
instantiate cnt : Cadence.ByzNodeSetCounting node nodeset nset
open ByzNodeSet

/-! ## The MVBA contract, as a class constraint -/

/-- The fallback path's MVBA instance (Module 3 (`mod:mvba`)), consumed
the way the glue consumes the slot consensus and the Conductor the ACS
([CompositionContracts.md](../docs/CompositionContracts.md) §3): as the state-level fragment
`MVBASafety` of [Interfaces.lean](Interfaces.lean), instantiated over
an abstract state `mstate` this module holds (`mvba_st` below) and advances
only by the contract's transitions. Veil hands every axiom of the class to
the solver, so agreement, integrity, external validity, the monotonicity of
`decided` and the frames are *used* in the verification conditions, never
restated as guards or invariants. The fault pattern is the module's own
`nset.is_byz`, so the contract and the quorum interface speak about the
same correct validators. The instance is `Mvba.mvbaSafety`
([Mvba/Compose.lean](Mvba/Compose.lean)), plugged in by
[System.lean](System.lean) with `mvalue := MetaBlock node merkle_root` and
`mentries := node → Option merkle_root`. The quorum family the contract's
availability field counts with is the module's own `nset`. -/
instantiate mvba : MVBASafety node mvalue mentries mmsg mstate nodeset nset
  (fun i => nset.is_byz i = true)

/-! ## Immutable configuration -/

-- TODO consider declaring as immutable individual. We need it mostly
-- for TIBE. It may however become relevant if we wanted to model parallel
-- execution of multiple slots. It is not guaranteed that those are independent
-- from each other: e.g. network outages for one slot most likely also affect
-- other slots. The same holds for other byzantine behavior.

/-- `is_proposer j` says that `j ∈ Ps` for slot `s`. In a faithful
implementation this is derived from a VRF; here it is abstracted as an
immutable relation. -/
immutable relation is_proposer (j : node)

/-- Whether the chunk set committed under root `m` forms a valid erasure
encoding — decoding any `f+1` of its chunks and re-encoding reproduces `m`
(Algorithm 6, line 24 (`line:da-reencode`)). Validity is a property of the whole committed
set the root binds, identical at every validator
(Proposition 2 (`prop:recovery-consistency`)), hence immutable configuration. Honest
proposers only commit well-encoded roots (`propose` requires it — the
paper's recovery guarantee (ii) premise); a Byzantine proposer may sign a
root that is not well-encoded and disseminate individually-valid chunks for
it — the paper's "invalidly encoded root" culprit case
(Section 4.5 (`subsection:chorus-proof`), closing parenthetical), which the fallback
signing rules below consult. -/
immutable relation well_encoded (m : merkle_root)

/-- The MVBA decides a meta-block representation, and agreement is over its
entries: two correct validators may decide representations whose
certificates differ (Supplement, Section 1.2 (`subsec:mvba-protocol`),
"Agreement and Integrity over entries"). A Veil module needs first-order
sorts for both, so `mvalue` and `mentries` are opaque, joined by the
contract's `mvba.entries`. An entry vector is read through two immutable
projections: `mval_pos e j m` says entry `j` of `e` is the positive entry
`⟨s, j, m⟩`, `mval_neg e j` that it is the negative entry `⟨s, j, ⊥⟩`. The
two assumptions after `#gen_state` (`[mval_pos_functional]`,
`[mval_pos_neg_excl]`) are the only facts about them this module uses, and
[System.lean](System.lean) discharges both at `e j = some m` / `e j = none`. -/
immutable relation mval_pos (e : mentries) (j : node) (m : merkle_root)
/-- Entry `j` of the entry vector `e` is the negative entry `⟨s, j, ⊥⟩`; see
`mval_pos`. -/
immutable relation mval_neg (e : mentries) (j : node)
/-- The positive entry `j` of the representation `v` is certified by a
`FallbackQC`; otherwise by a `FastQC`. This is what the fallback commit
wait reads ("for each `FallbackQC` in `B′`", Algorithm 5, line 38
(`line:fb-commit-foreach`)). -/
immutable relation mval_fb (v : mvalue) (j : node)

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

/-- Proposer `j` has signed a chunk header `⟨s, j, m⟩` (Algorithm 2 (`alg:proposer-dissemination`)). -/
relation msg_proposer_signed (j : node) (m : merkle_root)

/-- Sender `s` has sent validator `i` its assigned chunk under proposer `j`'s
root `m`: the proposer's own send (Algorithm 2 (`alg:proposer-dissemination`),
`s = j`), or a re-dissemination (Algorithm 5, line 12
(`line:fb-redisseminate`)). The only point-to-point message of the model,
indexed by its sender first and its recipient second; a correct validator
reads it only as its recipient ([Locality.md](../docs/Locality.md) R2, and
[ChorusDesign.md](../docs/ChorusDesign.md) §3.5.1 for why chunks are
point-to-point). -/
relation msg_chunk (s : node) (i : node) (j : node) (m : merkle_root)

/-- Validator `r` has signed a positive `vote`-tagged entry `⟨s, j, m⟩`. -/
relation msg_vote_pos_sig (r : node) (j : node) (m : merkle_root)
/-- Validator `r` has signed a negative `vote`-tagged entry `⟨s, j, ⊥⟩`. -/
relation msg_vote_neg_sig (r : node) (j : node)
/-- Validator `r` has broadcast its proposal vote (Algorithm 3, line 14 (`line:vote-broadcast`)). A broadcast vote carries a signed entry for
*every* proposer (plus the chunks backing the positive entries and the
decryption share); receivers discard incomplete votes, so a cast vote
implies per-proposer signatures on the network. -/
relation msg_vote_cast (r : node)

/-- Validator `r` has signed a positive `fb`-tagged entry. -/
relation msg_fb_pos_sig (r : node) (j : node) (m : merkle_root)
/-- Validator `r` has signed a negative `fb`-tagged entry. -/
relation msg_fb_neg_sig (r : node) (j : node)

/-- Validator `r` has signed `⟨fallback, s⟩` (its fallback vote,
Algorithm 5, line 7 (`line:fb-pathvote-guard`) block). -/
relation msg_fallback_sig (r : node)

/-- Validator `r` has signed a fast commit vote whose core has a
positive entry `⟨s, j, m⟩` for proposer `j`. -/
relation msg_commit_pos_sig (r : node) (j : node) (m : merkle_root)
/-- Validator `r` has signed a fast commit vote whose core has a
negative entry for proposer `j`. -/
relation msg_commit_neg_sig (r : node) (j : node)
/-- Validator `r` has actually broadcast its fast commit vote
(Algorithm 4, line 24 (`line:fast-commitvote`)). Only broadcast
commit signatures count toward a commitQC. -/
relation msg_commit_cast (r : node)

/-- Sender `c` has broadcast a positive fast commit certificate for `(j, m)`
(Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)): an aggregate of
`2f+1` matching *broadcast* commit votes, formed by `c` from the votes it
received (`broadcast_commitqc_pos`), or re-broadcast by a validator that
finalized on it (Algorithm 4, line 35 (`line:fast-rebroadcast-commitqc`),
`commit_assign_pos_fast`). -/
relation msg_commitqc_pos (c : node) (j : node) (m : merkle_root)
/-- The negative counterpart. -/
relation msg_commitqc_neg (c : node) (j : node)

/-- TIBE extraction (decryption) share released by validator `r` for the slot
(Algorithm 3 (`alg:voting`): released together with the proposal vote). -/
relation msg_decrypt_share (r : node)

/-- Validator `r` has signed and broadcast a fallback commit vote
`⟨FallbackCommitVote, s, e, σ_r⟩` over the entry vector `e`
(Algorithm 5, line 41 (`line:fb-commitvote`)) — the extra commit round the
fallback path runs after an MVBA decision (an MVBA decision does not
finalize by itself). A correct validator signs the entries of its own
decision (Algorithm 5, line 37 (`line:fb-mvba-decide`) binds
`E = entries(B′)`); a Byzantine one signs any vector. -/
relation msg_fbcommit_sig (r : node) (e : mentries)

/-- Sender `c` has broadcast a fallback commit certificate
`fbCommitQC = ⟨FallbackCommit, s, e, Σ⟩` over the entry vector `e`
(Algorithm 5, line 44 (`line:fb-commit-broadcast`)): `2f+1` fallback commit
votes over the same `e`, formed by `c` from the votes it received
(`broadcast_fbcommitqc`), or re-broadcast by a validator that finalized on
it (Algorithm 5, line 46 (`line:fb-commit-rebroadcast`)). The receiver
finalizes on the entries the certificate carries (Algorithm 5, line 45
(`line:fb-recv-commit`)). -/
relation msg_fbcommitqc (c : node) (e : mentries)

/-- Sender `i` has broadcast the MVBA's commit certificate `c`: the
certificate its own decision outputs (`decide(x, CommitQC)`, Supplement,
Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"), or one
it finalized on and re-broadcasts. A receiver checks it with the contract's
validity predicate `mvba.certifies` and finalizes on the certified entries. -/
relation msg_mvba_cert (i : node) (c : mmsg)

/-! ## Per-validator certificate state

`local_fastqc_*` is the one aggregated certificate we track per validator:
an honest validator's fast commit vote is justified by *its own* FastQC
observation (Algorithm 4, line 18 (`line:fast-formqc`)), so the
signer's local aggregate is protocol state. All other certificates
(FallbackQC, EquivCert, FBCert, commitQC) are *transferable*: any
holder of the underlying signatures can assemble and verify them, so in the
monotone-network model they are represented as derived predicates over the
signature relations (the `ghost relation`s below) rather than as
per-validator state. -/

/-- `local_fastqc_pos i j m` ≡ validator `i` has aggregated `2f+1`
positive-vote signatures into a positive FastQC for proposer `j`
under root `m`. Cross-validator agreement (any two honest validators'
FastQCs for the same proposer agree on the root) is recovered as an
invariant from quorum intersection (`local_fastqc_pos_cross_unique`). -/
relation local_fastqc_pos (i : node) (j : node) (m : merkle_root)

/-- `local_fastqc_neg i j` ≡ validator `i` has aggregated `2f+1`
negative-vote signatures for proposer `j`. -/
relation local_fastqc_neg (i : node) (j : node)

/-! ## Multi-Value Byzantine Agreement (MVBA)

The fallback path invokes one MVBA instance per slot (Module 3
(`mod:mvba`)). Its state is the abstract `mvba_st : mstate`, held here and
read only through the contract `mvba` (the class constraint above), on the
pattern of the glue's `sc_state` and the Conductor's `acs_state`: the
oracle action `mvba_step` advances it by any internal transition the
contract allows, `mvba_propose` drives the contract's `propose` input, and
the two **decision handlers** `on_mvba_decide_pos` / `on_mvba_decide_neg`
handle a correct validator's decision entry by entry, each in its own
fired-once row `local_mvba_recorded i j`. `mvba_terminate i` records that
`i` has handled every entry of its decision (Algorithm 5, line 37
(`line:fb-mvba-decide`) delivers the whole vector at once), and gates `i`'s
fallback commit vote, which signs the decided entries themselves.

The entries the MVBA certified are also kept in two **auxiliary records**,
`aux_mvba_decided_pos` / `aux_mvba_decided_neg`, which no action reads
([Locality.md](../docs/Locality.md) §2): the invariants state agreement
between the commit routes over them. Their agreement —
`mvba_decided_pos_unique`, `mvba_decided_pos_neg_excl` — is *proven* from
the class's `agreement` at the reachable abstract state, through the two tie
invariants (`mvba_decided_pos_tied`, `mvba_decided_neg_tied`) that every
record is the projection of some correct validator's decision or of a valid
commit certificate. This is how `Mvba.mvbaSafety` enters Chorus's trust
base.

`mvba_st` is the consumed sub-protocol's state: actions use it only through
the contract's operations at the actor's index, or to check a certificate
the actor holds ([Locality.md](../docs/Locality.md) §5). -/

/-- The instance's initial state: per-execution data, constrained by the
assumption `[mvba_init]` (an `assumption` may mention immutable
components only, so the mutable `mvba_st` is seeded from this). -/
immutable individual mvba_init_state : mstate
/-- The abstract MVBA state. -/
individual mvba_st : mstate
/-- Auxiliary record ([Locality.md](../docs/Locality.md) §2) that the MVBA
certified the positive entry `⟨s, j, m⟩`: written by a correct validator's
decision handler `on_mvba_decide_pos`, and by finalization on an MVBA commit
certificate (`commit_assign_pos_mvba`). No action reads it; the invariants
use it to state agreement between the commit routes. -/
relation aux_mvba_decided_pos (j : node) (m : merkle_root)
/-- Auxiliary record that the MVBA certified the negative entry `⟨s, j, ⊥⟩`;
see `aux_mvba_decided_pos`. -/
relation aux_mvba_decided_neg (j : node)

/-! ## Validator-local state -/

/-- Validator `i` recorded the positive entry `⟨s, j, m⟩`: a chunk from
proposer `j` under root `m` arrived before the deadline (`record_chunk`). -/
relation local_entry_pos (i : node) (j : node) (m : merkle_root)
/-- Validator `i` recorded the negative entry `⟨s, j, ⊥⟩`: it voted without a
positive entry for `j` (`vote`). -/
relation local_entry_neg (i : node) (j : node)

/-- Validator `i` has cast its proposal vote (`vote`). -/
relation local_voted (i : node)

/-- The two paths a validator can commit to, plus `none` for "not yet". -/
enum PathChoice = { none, fast, fallback }
/-- `local_path i` is the path validator `i` has committed to (the paper's
`pathVote`, Algorithm 4 (`alg:fast-path-certification`) local variables). `none` until
either `cast_fast_commit` (→ `fast`) or `cast_fallback_vote` (→ `fallback`)
fires; the enum value gives structural mutual exclusion of the two terminal
vote-cast actions without an explicit invariant. -/
function local_path : node → PathChoice

/-- Validator `i` has finalized the slot: it holds a committed entry for
every proposer (`finalize_commit`). -/
relation local_committed (i : node)
/-- Validator `i` committed the positive entry `⟨s, j, m⟩` (`commit_assign_pos_*`). -/
relation local_committed_pos (i : node) (j : node) (m : merkle_root)
/-- Validator `i` committed the negative entry `⟨s, j, ⊥⟩` (`commit_assign_neg_*`). -/
relation local_committed_neg (i : node) (j : node)

/-- Auxiliary record ([Locality.md](../docs/Locality.md) §2): the quorum of
received votes against which validator `i` cast its negative fallback entry
for proposer `j` (the `qv` parameter of `fb_sign_neg` at firing time).
Written by `fb_sign_neg`, read by no action — it exists so that the
speculative-safety argument can refer to the quorum after the fact without
an `∃ qv (… ∧ ∀ …)` invariant, whose quantifier alternation sends the SMT
matcher into a loop on the bulk-update actions. -/
relation aux_fb_neg_qv (i : node) (j : node) (qv : nodeset)

/-- Validator `i` has received sender `r`'s vote, whose entry for proposer
`j` is positive on root `m`. A vote is one message per sender
(Algorithm 3, line 14 (`line:vote-broadcast`)), so `i` keeps one entry per
sender and proposer: the first it receives (`receive_vote_pos`). -/
relation local_vote_rcv_pos (i : node) (r : node) (j : node) (m : merkle_root)
/-- Validator `i` has received sender `r`'s vote, whose entry for proposer
`j` is negative (`receive_vote_neg`). -/
relation local_vote_rcv_neg (i : node) (r : node) (j : node)

/-! ## Fired-once records

The paper's handlers run once: a validator sends its commit vote, its
fallback vote or its fallback commit vote once,
and handles its MVBA decision once. The model splits several of those
handlers into per-proposer steps (the Veil idiom for a `for each` loop),
and the effect of such a step is a network tuple, which the acting
validator may not read negatively unless it is its own send. So each of
them keeps a record of its own that it has already fired, and its guard is
that record's absence: a read of its own local state
([Locality.md](../docs/Locality.md) R1).
The records remove only steps that would change nothing else, so they
remove no reachable network state; what they buy is that no fair action
stays enabled after it has fired ([Bounds.md](../docs/Bounds.md) §6.4.7,
`Chorus.justice_enabledMove`). -/

/-- Validator `i` has signed its fast commit vote's entry for proposer `j`
(`commit_sign_pos` / `commit_sign_neg`): the commit vote carries one entry
per proposer (Algorithm 4, line 24 (`line:fast-commitvote`)). -/
relation local_commit_entry (i : node) (j : node)
/-- Validator `i` has signed its fallback entry for proposer `j`
(`fb_sign_pos` / `fb_sign_neg`, Algorithm 5, line 8 (`line:fb-cast-entry`)). -/
relation local_fb_entry (i : node) (j : node)
/-- Collector `c` has broadcast its commit certificate's entry for proposer
`j` (`broadcast_commitqc_pos` / `broadcast_commitqc_neg`,
Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)). -/
relation local_commitqc_sent (c : node) (j : node)
/-- Collector `c` has broadcast a fallback commit certificate
(`broadcast_fbcommitqc`, Algorithm 5, line 44 (`line:fb-commit-broadcast`)). -/
relation local_fbcommitqc_sent (c : node)
/-- Validator `i` has broadcast the commit certificate its MVBA decision
output (`send_mvba_cert`). -/
relation local_mvba_cert_sent (i : node)
/-- Validator `i` has recorded entry `j` of its MVBA decision
(`on_mvba_decide_pos` / `on_mvba_decide_neg`, Algorithm 5, line 37 (`line:fb-mvba-decide`)). -/
relation local_mvba_recorded (i : node) (j : node)
/-- Validator `i` has handed a transferred MVBA commit certificate to its
MVBA (`accept_mvba_commitqc`, the supplement's "Decision output and
handoff"). -/
relation local_mvba_qc_accepted (i : node)
/-- Validator `i` has transported its full MVBA decision: every proposer's
entry of its decision is recorded (`mvba_terminate`, the model's shadow of
Algorithm 5, line 37 (`line:fb-mvba-decide`) delivering `B′` at once). -/
relation local_mvba_complete (i : node)
/-- Validator `i` has cast its fallback commit vote (`cast_fb_commit`,
Algorithm 5, line 41 (`line:fb-commitvote`)). -/
relation local_fbcommit_voted (i : node)
/-- Validator `i` has reported to its MVBA that it is `AvailReady` for the
representation `v` (`mvba_avail_ready`). -/
relation local_avail_marked (i : node) (v : mvalue)

/-! ## Participation (Module 1 (`mod:slotconsensus`)'s inputs)

The slot-consensus module has three inputs: `participate()`, `abandon()` and
`propose(P)`. The paper's standing convention
(Appendix C.3 (`subsection:chorus-protocol-overview`)) makes a validator send nothing
unless it is *actively participating*, which means it has invoked
`participate()` and not yet `abandon()`. The two records below are that
state, one row per validator, and the input actions `participate` and
`abandon` are their only writers. The third input is the existing
`propose j m`. Every rule that sends is gated on `participating i ∧ ¬
abandoned i`; the rules that only process are exempt (see "Participation
inputs" below for the list). Both records are local state
([Locality.md](../docs/Locality.md) §2). They carry the contract's
observable names rather than a `local_` prefix, because they are exactly
the contract's `participating` and `abandoned`. -/

/-- Validator `i` has invoked `participate()` (the glue does so when it opens
the slot, Algorithm 1, line 17 (`line:participate`)). -/
relation participating (i : node)
/-- Validator `i` has invoked `abandon()` (the glue does so once it has
finalized the slot, Algorithm 1, line 23 (`line:abandon`)). -/
relation abandoned (i : node)

/- At this component count `#gen_state` needs a raised heartbeat budget in
one `isDefEq`. Veil raises it inside the elaborator, scoped to state
generation (`Module.ensureStateIsDefined`), so the module default applies to
everything else. A file-level `set_option maxHeartbeats` does not reach that
elaboration, and a `set_option … in` around a Veil command breaks the module
state ("already declared" on the next command). -/
#gen_state

/-! ## Assumptions

The instance starts in one of its initial states; and the two facts about
the entry-vector projections (`mval_pos` / `mval_neg`) that the agreement
argument needs: an entry carries at most one root, and is not both positive
and negative. [System.lean](System.lean) discharges all three at the concrete
instantiation (`Mvba.mvbaSafety`; `v j = some m` / `v j = none`). -/

assumption [mvba_init] mvba.init mvba_init_state
assumption [mval_pos_functional]
  ∀ (E : mentries) (J : node) (M1 M2 : merkle_root),
    mval_pos E J M1 → mval_pos E J M2 → M1 = M2
assumption [mval_pos_neg_excl]
  ∀ (E : mentries) (J : node) (M : merkle_root), ¬ (mval_pos E J M ∧ mval_neg E J)

/-! ## Derived certificates (ghost relations)

Transferable certificates are predicates over the signature relations: a
certificate "exists" iff the signatures it aggregates are observable on the
network. Any validator — honest or Byzantine — holding the signatures can
assemble the certificate, and any receiver can verify it, so existence on
the network is the faithful notion. -/

/-- A positive FastQC certificate for `(j, m)`: `2f+1` matching positive
vote signatures (Algorithm 4, line 18 (`line:fast-formqc`)). -/
ghost relation vote_quorum_pos (j : node) (m : merkle_root) :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_vote_pos_sig r j m

/-- A negative FastQC certificate for `j`. -/
ghost relation vote_quorum_neg (j : node) :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_vote_neg_sig r j

/-- A positive FallbackQC certificate for `(j, m)`: `f+1` matching positive
fallback signed entries (Algorithm 5, line 30 (`line:fb-formqc`)). -/
ghost relation fb_quorum_pos (j : node) (m : merkle_root) :=
  ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_fb_pos_sig r j m

/-- A negative FallbackQC certificate for `j`. -/
ghost relation fb_quorum_neg (j : node) :=
  ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_fb_neg_sig r j

/-- An EquivCert for proposer `j`: the proposer's signatures on two distinct
roots (`⟨equiv, s, j, ρ₁, σ_{p,1}, ρ₂, σ_{p,2}⟩`, Appendix C.3 (`subsection:fallback_path`)).
The fallback votes through which the two signed roots are *observed* are a
liveness/visibility matter that the monotone network abstracts away; the
certificate itself consists of the two proposer signatures. -/
ghost relation equiv_evidence (j : node) :=
  ∃ m1 m2, m1 ≠ m2 ∧ msg_proposer_signed j m1 ∧ msg_proposer_signed j m2

/-- The fallback certificate `FBCert_s`: `2f+1` fallback signatures
(Appendix C.3 (`subsection:fallback_path`)). Every fallback meta-block carries it; it
certifies that the fast path can no longer commit the slot. -/
ghost relation fbcert :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_fallback_sig r

/-- A positive fast commit certificate entry for `(j, m)`: `2f+1` matching
*broadcast* fast commit votes (Algorithm 4, line 31 (`line:fast-collect-commit`)). Signatures that were produced but never
broadcast (an honest validator signs per-proposer entries before casting
the vote) do not count: in the protocol they never reach the network. -/
ghost relation commitqc_pos (j : node) (m : merkle_root) :=
  ∃ q, nset.supermajority q ∧
    ∀ r, nset.member r q → msg_commit_pos_sig r j m ∧ msg_commit_cast r

/-- A negative fast commit certificate entry for `j`. -/
ghost relation commitqc_neg (j : node) :=
  ∃ q, nset.supermajority q ∧
    ∀ r, nset.member r q → msg_commit_neg_sig r j ∧ msg_commit_cast r

/-- The fallback commit certificate `fbCommitQC` over the entry vector `e`
(Algorithm 5, line 42 (`line:fb-collect-commit`) / Algorithm 5, line 43
(`line:fb-formcommitqc`)): `2f+1` fallback commit votes over the same
entries. Its validity check, which `broadcast_fbcommitqc` performs when it
forms one. -/
ghost relation fbcommitqc (e : mentries) :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_fbcommit_sig r e

/-- Validator `i` has received its assigned chunk under proposer `j`'s root
`m`, from some sender. -/
ghost relation chunk_received (i : node) (j : node) (m : merkle_root) :=
  ∃ s, msg_chunk s i j m

/-- Data availability for `(j, m)`: `f+1` validators hold their assigned
chunk — the erasure-code reconstruction threshold (Algorithm 6 (`alg:da`)
`isDecoded`). A statement about the run, read by no correct validator's
action. -/
ghost relation chunk_quorum (j : node) (m : merkle_root) :=
  ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → chunk_received r j m

/-- The slot key can be reconstructed: `f+1` extraction shares released
(Appendix C.2 (`appendix:encryption`)). -/
ghost relation slot_key_released :=
  ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_decrypt_share r

/-- Validator `i` holds a complete fast meta-block: a FastQC for every
proposer. -/
ghost relation complete_fast_metablock (i : node) :=
  ∀ j, is_proposer j → ((∃ m, local_fastqc_pos i j m) ∨ local_fastqc_neg i j)
/-- MVBA has been invoked by some honest validator, along one of the paper's
two proposal triggers (Algorithm 5 (`alg:fallback`)): the fallback trigger (`|M_i| ≥
2f+1` fallback votes, whose monotone-network shadow is `fbcert`), or the
case-(a) trigger (a complete fast meta-block — a FastQC for every
proposer — held at the MVBA arm time). A statement about the run, read by
no action: it ranges over every validator's FastQC rows and the fault
pattern, which no single validator observes. -/
ghost relation mvba_invoked :=
  fbcert ∨ (∃ i, ¬ is_byz i ∧ complete_fast_metablock i)

/-- Some validator has transported its full MVBA decision
(`local_mvba_complete`). A statement about the run, read by no action: each
validator's fallback commit vote waits for its own record. -/
ghost relation mvba_complete :=
  ∃ i, local_mvba_complete i

/-! ## Hypothesis predicates for conditional properties -/

/-- No signer has equivocated: no validator carries two different vote
entries for the same proposer, and no proposer has signed two different
roots. The paper's speculative-finality claim (Section 4.2
(`subsection:fast-path-overview`): "reverted ... only if some validator equivocated") is stated relative to
this predicate. It is anti-monotone (once violated, violated forever), so
invariants conditioned on it remain inductive. -/
ghost relation no_equivocation :=
  (∀ r j m1 m2, msg_vote_pos_sig r j m1 ∧ msg_vote_pos_sig r j m2 → m1 = m2) ∧
  (∀ r j m, ¬ (msg_vote_pos_sig r j m ∧ msg_vote_neg_sig r j)) ∧
  (∀ j m1 m2, msg_proposer_signed j m1 ∧ msg_proposer_signed j m2 → m1 = m2)

/-- No proposer has committed to an invalidly encoded root: every
proposer-signed root is well-encoded. Together with `no_equivocation`
this is exactly the paper's "proposer is the culprit" set for
speculative finality (Section 4.5 (`subsection:chorus-proof`), closing parenthetical:
"committing to an invalidly encoded root or disseminating several
distinct proposals"). Anti-monotone like `no_equivocation` (signatures
only accrue and `well_encoded` is immutable), so invariants conditioned
on it remain inductive. -/
ghost relation no_invalid_encoding :=
  ∀ j m, msg_proposer_signed j m → well_encoded m

/-- The protocol-level shadow of the paper's proposal-inclusion premise
(Proposition 3 (`prop:honest-positive-entry`)): a correct proposer `j` disseminated its
proposal `m` on time under synchrony, so *every* honest validator
recorded the positive entry `⟨s, j, m⟩` before the deadline. The timing
content ("`s.deadline − Δ ≥ GST` and dissemination at the slot's starting
time") is exactly what makes this premise true in the real protocol; the
model takes the premise itself as the hypothesis. The `well_encoded`
conjunct is the premise's encoding half: a correct proposer encodes the
ciphertext into a valid erasure encoding (the paper's recovery
guarantee (ii)), so its root always passes the re-encode check. -/
ghost relation all_honest_recorded (j : node) (m : merkle_root) :=
  ¬ is_byz j ∧ is_proposer j ∧ (∀ i, ¬ is_byz i → local_entry_pos i j m) ∧
  well_encoded m

/- Action bodies elaborate one nested `openStateAround` per statement — each
statement re-opens the state from a fresh monadic `get` — so elaboration
depth scales with the number of statements in the longest body. `after_init`
(~50 bulk assignments) and the longest guarded actions exceed the default
budget of 512. The `#gen_spec` block near the end of the file raises the
same option again for the invariant clump's instance search; this raise is
for the action language and has to come before the declarations. -/
set_option maxRecDepth 8192

/-! ## Initial state -/

/- `after_init` is one `isDefEq`-heavy command over every component, and at
this component count it needs more than the module's default heartbeat
budget. The raise is scoped by hand: it is set here and restored to Veil's
module default (500000) right after the block, so no later command sees it
(a `set_option … in` around a Veil command breaks the module state). -/
set_option maxHeartbeats 3000000

after_init {
  phase := pre_deadline

  msg_proposer_signed J M := false
  msg_chunk S I J M := false
  msg_vote_pos_sig R J M := false
  msg_vote_neg_sig R J := false
  msg_vote_cast R := false
  msg_fb_pos_sig R J M := false
  msg_fb_neg_sig R J := false
  msg_fallback_sig R := false
  msg_commit_pos_sig R J M := false
  msg_commit_neg_sig R J := false
  msg_commit_cast R := false
  msg_commitqc_pos C J M := false
  msg_commitqc_neg C J := false
  msg_decrypt_share R := false
  msg_fbcommit_sig R E := false
  msg_fbcommitqc C E := false
  msg_mvba_cert I C := false

  local_fastqc_pos I J M := false
  local_fastqc_neg I J := false

  mvba_st := mvba_init_state
  aux_mvba_decided_pos J M := false
  aux_mvba_decided_neg J := false

  local_entry_pos I J M := false
  local_entry_neg I J := false
  local_voted I := false
  local_path I := none
  local_committed I := false
  local_committed_pos I J M := false
  local_committed_neg I J := false
  aux_fb_neg_qv I J QV := false
  local_vote_rcv_pos I R J M := false
  local_vote_rcv_neg I R J := false

  local_commit_entry I J := false
  local_fb_entry I J := false
  local_commitqc_sent C J := false
  local_fbcommitqc_sent C := false
  local_mvba_cert_sent I := false
  local_mvba_recorded I J := false
  local_mvba_qc_accepted I := false
  local_mvba_complete I := false
  local_fbcommit_voted I := false
  local_avail_marked I V := false

  participating I := false
  abandoned I := false
}

set_option maxHeartbeats 500000

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

/-! ## Participation inputs (Module 1 (`mod:slotconsensus`))

`participate i` and `abandon i` are the module's two participation inputs.
They are invoked by the caller (the Cadence glue, Algorithm 1 (`algorithm:cadence`)), so
they carry no fairness: [Chorus/Liveness.lean](Chorus/Liveness.lean) classifies them as
inputs, outside (F-justice). The third input, `propose(P)`, is the
proposer's `propose j m` below.

**The gate.** Every rule that sends a message requires the acting validator
to be actively participating, `participating i ∧ ¬ abandoned i`. These are:

* `propose` (at the proposer; it sends every chunk);
* `vote`;
* `commit_sign_*` and `cast_fast_commit`;
* `broadcast_commitqc_*` and `broadcast_fbcommitqc` (at the collector);
* `fb_sign_*` (`fb_sign_pos` also sends every validator its chunk) and
  `cast_fallback_vote`;
* `mvba_propose`, which the convention names explicitly;
* `send_mvba_cert`, the broadcast of the MVBA's commit certificate;
* `cast_fb_commit`;
* `commit_assign_*`, because the paper's finalization rules re-broadcast
  the commitment proof (Algorithm 4, line 35 (`line:fast-rebroadcast-commitqc`),
  Algorithm 5, line 46 (`line:fb-commit-rebroadcast`)), and `finalize_commit`,
  the output, so that a validator that has abandoned the slot does not
  finalize it afterwards.

The rules that only process a received message are exempt: `record_chunk`,
the vote receipts `receive_vote_*`, `aggregate_fastqc_*`, the decision
handlers `on_mvba_decide_*` and `mvba_terminate`, the certificate handoff
`accept_mvba_commitqc`, and the availability report `mvba_avail_ready`. So
are the phase markers and the MVBA's oracle step, which are not a
validator's rules. The gates read only the acting validator's own local
state ([Locality.md](../docs/Locality.md) R1).

**Forwarding to the MVBA.** `abandon i` also invokes the MVBA's `abandon()`
at `i` (Algorithm 5, line 48 (`line:fb-abandon`)), through the contract's `mvba.abandon` input, the
way `mvba_propose` drives its `propose`. The paper forwards only when `i`
has invoked the MVBA (`mvbaInvoked`). Here it forwards every time. The
difference is not observable: the MVBA's own `abandon()` has no
precondition, a party that has not proposed sends no MVBA message (the
contract's `quiescence`), and after `abandon i` Chorus never proposes to
the MVBA for `i` (`mvba_propose` is gated). Forwarding every time keeps the
action free of a negative read of the MVBA's state. -/

action participate (i : node) {
  participating i := true
}

action abandon (i : node) (mvba_next : mstate) {
  -- `MVBA[s].abandon()` (Algorithm 5, line 48 (`line:fb-abandon`)).
  require mvba.abandon mvba_st i mvba_next
  abandoned i := true
  mvba_st := mvba_next
}

/-! ## Phase I — Proposer dissemination (Algorithm 2 (`alg:proposer-dissemination`))

An honest proposer `j` commits to a single Merkle root `m` and sends every
validator its chunk under that root, in one step: the `send` of
Algorithm 2 (`alg:proposer-dissemination`)'s "for each validator `p_r`"
loop. Its effects are the proposer's signature `msg_proposer_signed j m` and
one point-to-point message `msg_chunk j I j m` per validator `I`. Honest
proposers are bound to a *single* `m` per slot by the precondition
`∀ m2, msg_proposer_signed j m2 → m2 = m`, a read of the proposer's own
sends; Byzantine proposers can equivocate via `byz_sign_proposer` and
`byz_send_chunk`.

A chunk may reach its recipient at any time, or never: the network is
monotone, and nothing forces a validator to act on a message
([Locality.md](../docs/Locality.md) §1). `record_chunk`, the recipient's
step, is what turns a received chunk into its positive entry, and it
enforces the `pre_deadline` cutoff. That an on-time chunk is recorded in
time is a premise about runs (the receiver's row of the timing premise),
not a step of the model. -/
action propose (j : node) (m : merkle_root) {
  require ¬ is_byz j
  require participating j
  require ¬ abandoned j
  require is_proposer j
  -- A correct proposer encodes the ciphertext into a valid erasure
  -- encoding (recovery guarantee (ii)); only Byzantine proposers
  -- (`byz_sign_proposer`) can commit to an ill-encoded root.
  require well_encoded m
  require phase = pre_deadline
  require ∀ m2, msg_proposer_signed j m2 → m2 = m
  msg_proposer_signed j m := true
  -- Send every validator its chunk under `m`.
  msg_chunk j I j m := true
}

/-- A chunk that reaches honest validator `i` before the deadline is recorded
as a positive local entry (Algorithm 6 (`alg:da`) `tryIngestChunk` → Algorithm 3 (`alg:voting`)
`onChunkValidated`, Algorithm 3, line 5 (`line:vote-positive`)). An honest validator only records
the first chunk per proposer; subsequent chunks are ignored. -/
action record_chunk (i : node) (j : node) (m : merkle_root) {
  require ¬ is_byz i
  -- `tryIngestChunk` rejects chunks whose sender is not a proposer of the
  -- slot (Algorithm 6 (`alg:da`): "if j ∉ s.proposers … return false").
  require is_proposer j
  -- A chunk addressed to `i`, from any sender, under a root `j` signed.
  require chunk_received i j m
  require msg_proposer_signed j m
  require phase = pre_deadline
  require ∀ m2, ¬ local_entry_pos i j m2
  require ¬ local_entry_neg i j
  local_entry_pos i j m := true
}

/-! ## Phase II — Voting at the deadline (Algorithm 3 (`alg:voting`)) -/

/-- At time `Ds`, each honest validator broadcasts a single proposal vote
(Algorithm 3, line 14 (`line:vote-broadcast`)). For each proposer `j ∈ Ps`, the validator's
per-proposer entry is positive `⟨s, j, m⟩` iff it recorded some chunk from
`j` under `m` before the deadline, and negative otherwise. The vote message
also carries the chunks backing the positive entries and releases the
validator's decryption share.

Algorithm 3 (`alg:voting`)'s "for all pj ∈ Ps" loop is collapsed into this single atomic
action, whose body uses Veil's auto-quantified capitals (`J`, `M`) to express
the per-proposer bulk update on the message-signature relations and the local
entries. The broadcast itself is `msg_vote_cast`; receivers accept a vote
only if it carries an entry for every proposer, which is why `msg_vote_cast`
implies per-proposer signatures (invariant `vote_cast_entries`).

Each bulk update is a disjunction with the relation's old value, so it only
ever adds tuples, by its syntax alone — the (M-update) half of the network
contract ([ChorusDesign.md](../docs/ChorusDesign.md) §3.1) holds per step, not merely at
reachable states. At a reachable state the old value is `false` anyway (the
voter's row is empty before its vote: `vote_sig_pos_implies_voted`,
`vote_sig_neg_implies_voted`, `local_entry_neg_implies_voted`), so the
disjunction changes no reachable behaviour. -/
action vote (i : node) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require phase ≠ pre_deadline
  require ¬ local_voted i

  msg_vote_pos_sig i J M := msg_vote_pos_sig i J M || (is_proposer J && local_entry_pos i J M)
  msg_vote_neg_sig i J := msg_vote_neg_sig i J || (is_proposer J && decide (∀ M, ¬ local_entry_pos i J M))
  local_entry_neg i J := local_entry_neg i J || (is_proposer J && decide (∀ M, ¬ local_entry_pos i J M))

  local_voted i := true
  msg_vote_cast i := true
  msg_decrypt_share i := true
}

/-! ## Phase III — Fast Path (Algorithm 4 (`alg:fast-path-certification`))

When 2f+1 vote-positive (resp. vote-negative) signatures exist for the same
`(s, j, m)` (resp. `(s, j)`), a FastQC can be aggregated. A validator that
observes a FastQC for every proposer broadcasts a fast commit vote (and may
*speculatively* commit — see the speculative-safety invariants below); 2f+1
broadcast fast commit votes for the same core then form a commitQC, the fast
path's finalization certificate. -/

/-- Per-validator FastQC aggregation: `i` observes a supermajority of
positive vote signatures for `(j, m)` and records the resulting FastQC
in its own `local_fastqc_pos i j m` (Algorithm 4, line 18 (`line:fast-formqc`)). Aggregation is
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
  -- Fired once: `i` does not hold this FastQC yet.
  require ¬ local_fastqc_pos i j m
  local_fastqc_pos i j m := true
}

action aggregate_fastqc_neg (i : node) (j : node) (q : nodeset) {
  require ¬ is_byz i
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_vote_neg_sig r j
  require ¬ local_fastqc_neg i j
  local_fastqc_neg i j := true
}

/-- Per-proposer fast commit signing: validator `i` signs a positive fast
commit vote entry for proposer `j` with root `m`, justified by `i`'s own
FastQC observation. The signature reaches the network only with
`cast_fast_commit` (the paper's commit vote is a single broadcast); the
`commitqc_*` certificates therefore additionally require `msg_commit_cast`
of every contributor. -/
action commit_sign_pos (i : node) (j : node) (m : merkle_root) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require is_proposer j
  require local_fastqc_pos i j m
  -- Fired once: `i` has not signed an entry for `j` yet.
  require ¬ local_commit_entry i j
  msg_commit_pos_sig i j m := true
  local_commit_entry i j := true
}

action commit_sign_neg (i : node) (j : node) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require is_proposer j
  require local_fastqc_neg i j
  require ¬ local_commit_entry i j
  msg_commit_neg_sig i j := true
  local_commit_entry i j := true
}

/-- Cast (broadcast) the fast commit vote once every proposer has been signed.
This sets `pathVote = fast` (Algorithm 4, line 25 (`line:fast-pathvote`)): the commit vote and the
fallback vote are mutually exclusive. -/
action cast_fast_commit (i : node) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require ∀ J, is_proposer J →
    ((∃ M, msg_commit_pos_sig i J M) ∨ msg_commit_neg_sig i J)
  msg_commit_cast i := true
  local_path i := fast
}

/-- Assemble and broadcast a fast commit certificate entry
(Algorithm 4, line 31 (`line:fast-collect-commit`) / Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)): `2f+1`
matching broadcast commit votes aggregate into a transferable certificate.
The collector `c` is a correct validator that forms the certificate from
the commit votes it has received and broadcasts it under its own name. It
sends only while actively participating, like every other sending rule, and
once per proposer: the `upon` handler runs once (`local_commitqc_sent`).
Apart from those, the action's precondition is the validity check itself.
A Byzantine validator can form and send the same (valid) certificate at any
time: `byz_broadcast_commitqc_*` below, which is not fair. -/
action broadcast_commitqc_pos (c : node) (j : node) (m : merkle_root) (q : nodeset) {
  require ¬ is_byz c
  require participating c
  require ¬ abandoned c
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit_pos_sig r j m ∧ msg_commit_cast r
  -- Fired once: `c` has not broadcast a certificate entry for `j` yet.
  require ¬ local_commitqc_sent c j
  msg_commitqc_pos c j m := true
  local_commitqc_sent c j := true
}

action broadcast_commitqc_neg (c : node) (j : node) (q : nodeset) {
  require ¬ is_byz c
  require participating c
  require ¬ abandoned c
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit_neg_sig r j ∧ msg_commit_cast r
  require ¬ local_commitqc_sent c j
  msg_commitqc_neg c j := true
  local_commitqc_sent c j := true
}

/-! ## Phase III — Fallback Path (Algorithm 5 (`alg:fallback`))

From time `Ds + Δ`, a validator that has received at least `2f+1` proposal
votes and has not cast a fast commit vote enters the fallback path
(Algorithm 5, line 7 (`line:fb-pathvote-guard`)): for each proposer it casts a fallback signed
entry, then broadcasts its fallback vote. On the wire a fallback vote
carries, per proposer, only a FastQC or the *sender's own* signed entry —
the receipt rule rejects anything else (Algorithm 5, line 18 (`line:fb-accept`)) and harvests carried FastQCs (Algorithm 5, line 20 (`line:fb-harvest`)).
EquivCerts and FallbackQCs exist only as objects assembled at propose
time from the signed entries in `M_i` (the atomic build,
Algorithm 5, lines 26–30 (`line:fb-build-entry`–`line:fb-formqc`)), where the per-proposer evidence
precedence `FastQC ≻ EquivCert ≻ FallbackQC` orders the build cases; in
the monotone model the certificates are ghost predicates over the
signature relations — precisely that derived-at-build-time reading — and
the precedence is resolved at the MVBA validity check.

The "received ≥ 2f+1 votes" guard is modelled as a witnessed supermajority
of *broadcast* votes (`msg_vote_cast`). This guard is load-bearing for
proposal inclusion (Proposition 3 (`prop:honest-positive-entry`)): any 2f+1 broadcast votes
contain f+1 honest ones, which pin an on-time honest proposer's entry. -/

/-- Vote receipt, positive entry: validator `i` receives sender `r`'s vote
(Algorithm 3, line 14 (`line:vote-broadcast`)), whose entry for proposer
`j` is positive on `m`, and keeps it. A vote is one message per sender, so
a correct receiver keeps one entry per sender and proposer: the first it
receives. A Byzantine sender that signed conflicting entries reaches
different receivers with different votes, and each receiver keeps the one
it got. The read of the network is positive, and the record is `i`'s own
([Locality.md](../docs/Locality.md) R1, R2). It sends nothing, so it is
not participation-gated. The receipt is what `fb_sign_neg` reads: "among
the votes it received" is a statement about `i`'s own state. -/
action receive_vote_pos (i : node) (r : node) (j : node) (m : merkle_root) {
  require ¬ is_byz i
  require is_proposer j
  require msg_vote_cast r
  require msg_vote_pos_sig r j m
  -- Fired once per sender and proposer: the first entry received is kept.
  require ∀ m2, ¬ local_vote_rcv_pos i r j m2
  require ¬ local_vote_rcv_neg i r j
  local_vote_rcv_pos i r j m := true
}

/-- Vote receipt, negative entry; see `receive_vote_pos`. -/
action receive_vote_neg (i : node) (r : node) (j : node) {
  require ¬ is_byz i
  require is_proposer j
  require msg_vote_cast r
  require msg_vote_neg_sig r j
  require ∀ m2, ¬ local_vote_rcv_pos i r j m2
  require ¬ local_vote_rcv_neg i r j
  local_vote_rcv_neg i r j := true
}

/-- Per-proposer fallback signing, positive case (Algorithm 5, line 11 (`line:fb-positive-entry`)).
Per the paper an honest validator's fallback signed entry for proposer `j`
is positive `⟨s, j, m⟩` iff *all* of:

  (b) it collected `f+1` valid positive votes for `(j, m)`;
  (c) the data is reconstructible — `alg:da.isDecoded(m)`;
  (d) the reconstructed data re-encodes to `m` (Algorithm 6, line 24 (`line:da-reencode`); the paper's proof sketch: an honest validator
      casts fallback-yes only after reconstructing the proposal and
      checking that it re-encodes to the root) — the model's
      `well_encoded m`.

(c) needs no guard of its own: a valid positive vote carries its signer's
assigned chunk (Algorithm 4 (`alg:fast-path-certification`), receive
handler; `byz_sign_vote_pos` mirrors the check), so the `f+1` positive votes
of (b) put `f+1` distinct chunks in the validator's hands, which is
`isDecoded(m)`. The network-level shadow of that step is the invariant
`vote_pos_quorum_implies_decodable`.

The signer needs no positive entry of its own (`local_entry_pos i j m`): a
validator that missed its assigned chunk before the deadline may still
positive-sign once it observes f+1 votes and the data decodes. The proposer
signature `σ_p` the positive entry carries is the network fact
`msg_proposer_signed j m`, recovered from the f+1 vote quorum — which holds
≥ 1 honest voter whose `local_entry_pos` implies `msg_proposer_signed`
(`local_entry_pos_signed`).

**The rule re-disseminates in the same step** (Algorithm 5, line 12
(`line:fb-redisseminate`)): having decoded the proposal, the signer
re-encodes it and sends every validator its assigned chunk under `m`, one
point-to-point message per validator under its own name,
`msg_chunk i I j m`. The sends happen while `i` actively participates,
inside this gated step, and never after it abandons. -/
action fb_sign_pos (i : node) (j : node) (m : merkle_root) (q : nodeset) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require phase = post_fb_arm ∨ phase = post_mvba_arm
  require local_voted i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require is_proposer j
  -- (guard) ≥ 2f+1 proposal votes received (Algorithm 5, line 7 (`line:fb-pathvote-guard`)).
  require ∃ qv, nset.supermajority qv ∧ ∀ r, nset.member r qv → msg_vote_cast r
  -- (b) f+1 positive votes for (j, m), which carry their chunks: (c).
  require nset.greater_than_third q
  require ∀ r, nset.member r q → msg_vote_pos_sig r j m
  -- (d) Re-encode consistency: the decoded data reproduces `m`.
  require well_encoded m
  -- Fired once: `i` has not signed its fallback entry for `j` yet.
  require ¬ local_fb_entry i j
  msg_fb_pos_sig i j m := true
  local_fb_entry i j := true
  -- Re-encode, and send every validator its assigned chunk under `m`
  -- (Algorithm 5, line 12 (`line:fb-redisseminate`)).
  msg_chunk i I j m := true
}

/-- Per-proposer fallback signing, negative case. The paper's validator signs
negative for `j` iff, *among the ≥ 2f+1 votes it received*, no root has
f+1 positive votes with decodable data that re-encodes to the root
(Algorithm 5, line 8 (`line:fb-cast-entry`), else-branch). The votes it
received are its own receipt rows (`receive_vote_*`): the parameter `qv` is
a supermajority of senders whose votes `i` has received, and the condition
reads `i`'s receipts, negatively, which is a read of its own state
([Locality.md](../docs/Locality.md) R1). As in `fb_sign_pos`, `f+1`
received positive votes carry `f+1` chunks, so "with decodable data" adds
no condition.

The `well_encoded M` conjunct inside the negation admits the paper's
re-encode-failure case (Section 4.5 (`subsection:chorus-proof`), closing parenthetical):
an honest validator that gathers `f+1` yes votes on a root whose chunks
fail to re-encode marks the root invalid and signs negative anyway. This
is the culprit case that involves no equivocation — only an invalidly
encoded root — which is why the speculative-finality properties below take
`no_invalid_encoding` alongside `no_equivocation`. -/
action fb_sign_neg (i : node) (j : node) (qv : nodeset) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require phase = post_fb_arm ∨ phase = post_mvba_arm
  require local_voted i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require is_proposer j
  -- (guard) ≥ 2f+1 proposal votes received (Algorithm 5, line 7 (`line:fb-pathvote-guard`)):
  -- `i` holds the entry for `j` of every vote in `qv`.
  require nset.supermajority qv
  require ∀ r, nset.member r qv → ((∃ m2, local_vote_rcv_pos i r j m2) ∨ local_vote_rcv_neg i r j)
  -- Negative iff no root has, within the received votes, f+1 positive
  -- entries that re-encode to the root (the `else` branch of
  -- Algorithm 5, line 8 (`line:fb-cast-entry`), with
  -- Algorithm 6, line 24 (`line:da-reencode`) marking ill-encoded roots invalid).
  require ∀ M q, ¬ (nset.greater_than_third q ∧
    (∀ r, nset.member r q → nset.member r qv ∧ local_vote_rcv_pos i r j M) ∧
    well_encoded M)
  require ¬ local_fb_entry i j
  msg_fb_neg_sig i j := true
  aux_fb_neg_qv i j qv := true
  local_fb_entry i j := true
}

/-- Broadcast the fallback vote once every proposer carries a fallback signed
entry; this signs `⟨fallback, s⟩` and sets `pathVote = fallback`. -/
action cast_fallback_vote (i : node) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require phase = post_fb_arm ∨ phase = post_mvba_arm
  require local_voted i
  require ¬ msg_commit_cast i
  require local_path i ≠ fallback
  require ∀ J, is_proposer J →
    ((∃ M, msg_fb_pos_sig i J M) ∨ msg_fb_neg_sig i J)
  msg_fallback_sig i := true
  local_path i := fallback
}

/-! ## The MVBA instance: oracle step, proposal, decision handlers (Module 3 (`mod:mvba`))

The paper's MVBA module (Module 3 (`mod:mvba`)) exposes `propose(B)` (a validator
proposes a valid meta-block, thereby *starting to participate*),
`abandon()` (it stops participating), and the output `decide(B)`; the
paper repository's internal supplement strengthens the output to
`decide(B, CommitQC)`, whose certificate Chorus hands to the other
validators' MVBAs (`accept_mvba_commitqc` below, and the contract's
`certifies`/`accept` fields). Its guarantees are the five properties
*Agreement*, *Integrity*, *External validity*,
*`ℓ_MVBA`-Termination* (conditioned on all correct validators proposing
and none abandoning before the bound), and *Quiescence* (no protocol
message outside the propose–abandon window). All five are fields of
`MVBASafety` / `MVBATemporal` ([Interfaces.lean](Interfaces.lean)),
and the module consumes the state-level fragment as the class constraint
`mvba` over the abstract state `mvba_st`:

* **`mvba_step`** — the oracle step: any internal transition
  `MVBASafety.step` allows, including the ones that output `decide(B)` at
  some correct validators. What Chorus knows about the new state is
  exactly the contract: reachability is preserved, decisions stay decided
  (`decided_mono`), correct validators' inputs are unchanged (the frames),
  and agreement, integrity and external validity hold at every reachable
  state.
* **`mvba_propose`** — the paper's `MVBA[s].propose(B_i)`. It is one of
  the two MVBA inputs Chorus drives; the other, `abandon()`, is forwarded
  by Chorus's own `abandon` input (Algorithm 5, line 48 (`line:fb-abandon`), "Participation
  inputs" above). A correct, actively participating validator proposes
  under one of the paper's two triggers
  (Algorithm 5 (`alg:fallback`)): the fallback trigger — `|M_i| ≥ 2f+1` fallback votes,
  whose monotone-network shadow is `fbcert` — from the fallback arm on, or
  the case-(a) trigger — a complete fast meta-block of its own — at the
  MVBA arm. Its trigger implies `mvba_invoked`. The proposal is a
  *certified* meta-block: every entry is a proposer's and carries the
  certificate `Valid B_i` checks — a FastQC-shaped entry a `2f+1` vote
  quorum; a fallback-shaped entry (FallbackQC or EquivCert) additionally
  `FBCert`, because only fallback meta-blocks may carry such entries and
  every valid fallback meta-block includes `FBCert`
  (Appendix C.3 (`subsection:fallback_path`)) — and every proposer has an entry. These
  are the caller's `Valid B_i` obligation, stated as guards; the
  certificates a proposal carries are *assembled at propose time* from the
  signed entries in `M_i` (Algorithm 5, lines 26–30 (`line:fb-build-entry`–`line:fb-formqc`)), which
  is exactly the ghost-relation reading. Safety needs nothing from this
  action; it is what gives the instance's Termination premise ("all
  correct validators propose") its meaning for the liveness step.
* **`on_mvba_decide_pos` / `on_mvba_decide_neg`** — the decision handlers,
  per entry: a correct validator `i` has decided its own representation `v`
  (`mvba.decided mvba_st i v`, read off the abstract state), entry `j` of
  `entries(v)` is `⟨s, j, m⟩` resp. `⟨s, j, ⊥⟩`
  (`mval_pos (mvba.entries v) j m` / `mval_neg (mvba.entries v) j`), and
  the handler marks entry `j` handled in its own row `local_mvba_recorded
  i j`, and the entry in the auxiliary records `aux_mvba_decided_*`.
  Per entry rather than in one step for the vector, so every update
  stays a `:= true` and every downstream invariant keeps its
  form. The handler has no condition beyond the decision itself, as the
  paper's handler is "upon `MVBA[s].decide(B′)`" (Algorithm 5, line 37
  (`line:fb-mvba-decide`)): no phase gate, since a case-2 proposal can be
  decided before the MVBA arm, and no requirement that the MVBA was invoked,
  since Module 3 (`mod:mvba`) does not order a decision after a proposal.
* **`send_mvba_cert`** — the `CommitQC` route of the supplement's handoff:
  a correct validator's decision outputs the commit certificate that
  commits it (`mvba.decidedCert`, an output at its own index), and the
  validator broadcasts that certificate (`msg_mvba_cert i c`). A
  receiver hands it to its own MVBA (`accept_mvba_commitqc`), and finalizes
  on the entries it certifies (`commit_assign_*_mvba`), after the same
  bridge check on a representation of them. The auxiliary records then hold
  the *certified* entries, from a correct decision or from a certificate;
  the tie invariants say which, and their uniqueness comes from
  `mvba.agreement`, `mvba.certified_decided` and `mvba.certified_unique`.
* **`mvba_avail_ready`** — the contract's availability input, driven by
  Chorus with its chunk wait as the guard (`avail_ready_chunks`).
* **The one stated bridge.** Before acting on an entry, each handler, and
  the finalization on an MVBA commit certificate,
  verifies the certificate its own representation names for the entry
  against the network: a vote quorum for a `FastQC`, `fb_quorum_pos j m ∧
  fbcert` for a `FallbackQC` (`mval_fb v j`), resp. the negative form. This is a **bridge, not a restatement**
  ([MvbaPlan.md](../docs/MvbaPlan.md) §1.1, [CompositionContracts.md](../docs/CompositionContracts.md) §7): the
  class's `external_validity` says the decided value is `Valid`; the guard
  says what a valid certificate *means* in a model whose signatures are
  network relations — `Valid` is a class parameter fixed before this
  module's state exists, so it cannot mention Chorus's network. It has
  exactly the shape of the Conductor's ACS median bridge (`acs_decide`),
  and it is sound in both directions that matter: it removes no real
  behaviour (certificates are publicly verifiable, so the receiver *can*
  re-check, and a correct MVBA's decision passes the check), and if the
  MVBA were wrong the handler would simply not fire — safety-conservative.
  `mvba_decided_pos_backed` / `mvba_decided_neg_backed` persist the
  evidence in the auxiliary records.
* **`mvba_terminate`** — records that `i` has its full vector: `i` has
  decided `v` and has handled every proposer's entry in its own rows
  (`local_mvba_complete i`). This is the model shadow of
  Algorithm 5, line 37 (`line:fb-mvba-decide`) delivering `B'` at once, and it is what gates `i`'s
  fallback commit vote (`cast_fb_commit i` requires `local_mvba_complete i`).
* **What the class buys.** No handler asserts an agreement property of its
  own. `mvba_decided_pos_unique` and `mvba_decided_pos_neg_excl` are kept as
  invariants (downstream cells e-match on them) and are *proven* from
  `mvba.agreement` at `mvba_reachable`, through the tie invariants and the
  two `mval_*` assumptions: records from different correct validators'
  decisions agree *because* the instance's agreement says so.
* *Quiescence* is a field of `MVBASafety` the instance proves. Its one
  model shadow here is `mvba_decided_phase`: a record carries a
  certificate, whose correct signers signed after the deadline. Nothing
  places a correct decision or `local_mvba_complete` after the deadline: the
  module promises no "a correct validator decides only after proposing"
  (Module 3 (`mod:mvba`) states Quiescence for messages only).

The paper's agreement proof (Proposition 1 (`prop:agreement-entries`)) runs through
`fbCommitQC`/`commitQC` quorum intersections plus MVBA Integrity; the model
takes the MVBA's agreement
from the class and recovers the fast-vs-fallback case as a pure quorum
argument: a commitQC and an `FBCert` are two supermajorities whose honest
common member would have had to vote both paths — structurally
impossible.

Every read of `mvba.decided` and of the network here is in positive
position, and every operation of the contract is used at the actor's index
or to check a certificate the actor holds
([Locality.md](../docs/Locality.md) §5). -/

action mvba_step (mvba_next : mstate) {
  require mvba.step mvba_st mvba_next
  mvba_st := mvba_next
}

action mvba_propose (i : node) (v : mvalue) (mvba_next : mstate) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  -- The proposer's own trigger (Algorithm 5 (`alg:fallback`)): the fallback trigger from
  -- the fallback arm on, or the case-(a) trigger at the MVBA arm.
  require (fbcert ∧ (phase = post_fb_arm ∨ phase = post_mvba_arm)) ∨
    (complete_fast_metablock i ∧ phase = post_mvba_arm)
  -- `Valid B_i`, the caller's obligation: every entry is a proposer's and
  -- carries the certificate its kind names, and every proposer has an entry.
  require ∀ J M, mval_pos (mvba.entries v) J M →
    is_proposer J ∧
      ((¬ mval_fb v J ∧ vote_quorum_pos J M) ∨ (mval_fb v J ∧ fb_quorum_pos J M ∧ fbcert))
  require ∀ J, mval_neg (mvba.entries v) J →
    is_proposer J ∧ (vote_quorum_neg J ∨ ((fb_quorum_neg J ∨ equiv_evidence J) ∧ fbcert))
  require ∀ J, is_proposer J → (∃ M, mval_pos (mvba.entries v) J M) ∨ mval_neg (mvba.entries v) J
  -- `MVBA[s].propose(B_i)`.
  require mvba.propose mvba_st i v mvba_next
  mvba_st := mvba_next
}

/-- **The decision output** (the supplement's "Decision output and handoff",
Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)). A correct
validator's MVBA decision outputs the commit certificate that commits it
(`decide(x, CommitQC)`: the contract's output `mvba.decidedCert` at `i`'s
index), and Chorus broadcasts it: "Upon receiving this output, Chorus
broadcasts the `CommitQC`". `i` sends, under its own name, the certificate
its own decision output. A send, so gated on participation; once
(`local_mvba_cert_sent`). -/
action send_mvba_cert (i : node) (c : mmsg) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require mvba.decidedCert mvba_st i c
  require ¬ local_mvba_cert_sent i
  msg_mvba_cert i c := true
  local_mvba_cert_sent i := true
}

/-- **The decision handoff** (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Decision output and handoff"). A correct
validator that receives a commit certificate `c` from sender `s` hands it to
its own MVBA through the contract's transfer input `mvba.accept`, which
accepts a valid certificate of any view and decides its value. The read of
the message is positive, and the input is at `i`'s index. The finalization
the supplement attaches to the certificate is `commit_assign_*_mvba` below,
beside the main body's fallback commit round. Fired once
(`local_mvba_qc_accepted`). -/
action accept_mvba_commitqc (i : node) (s : node) (c : mmsg) (mvba_next : mstate) {
  require ¬ is_byz i
  -- Fired once: `i` has not handed a certificate to its MVBA yet.
  require ¬ local_mvba_qc_accepted i
  -- `i` has received the certificate `c`.
  require msg_mvba_cert s c
  -- `MVBA[s]` accepts the transferred certificate `c`.
  require mvba.accept mvba_st i c mvba_next
  mvba_st := mvba_next
  local_mvba_qc_accepted i := true
}

/-- **Availability, reported to the MVBA** (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Commit availability condition"):
"`AvailReady_i(x)` hold[s] if, for every positive entry `⟨s, j, ρ⟩` of `x`
that is certified by a `FallbackQC`, validator `p_i` holds its assigned
availability share for `ρ`", and "the MVBA treats availability
synchronization as a service of the composing dissemination and ChunkSync
layer". That layer is Chorus's, so Chorus decides when `i` is
`AvailReady` for `v`, and says so through the contract's input
`mvba.markAvail`. The guard is the definition: `i` has received its
assigned chunk under every positive `FallbackQC` entry of `v`, the same
wait as the fallback commit vote's (Algorithm 5, line 39
(`line:fb-commit-wait`)). Both reads are positive. It sends nothing, so it
is not participation-gated. Fired once per representation
(`local_avail_marked`). -/
action mvba_avail_ready (i : node) (v : mvalue) (mvba_next : mstate) {
  require ¬ is_byz i
  require ∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → chunk_received i J M
  require ¬ local_avail_marked i v
  require mvba.markAvail mvba_st i v mvba_next
  mvba_st := mvba_next
  local_avail_marked i v := true
}

action on_mvba_decide_pos (i : node) (j : node) (m : merkle_root) (v : mvalue) {
  require ¬ is_byz i
  require is_proposer j
  -- The output has occurred: `i` has decided `v`, whose entry for `j` is `m`.
  require mvba.decided mvba_st i v
  require mval_pos (mvba.entries v) j m
  -- The bridge: the certificate `v` names for the entry verifies against
  -- the network.
  require (¬ mval_fb v j ∧ vote_quorum_pos j m) ∨ (mval_fb v j ∧ fb_quorum_pos j m ∧ fbcert)
  -- Fired once: `i` has not recorded entry `j` of its decision yet.
  require ¬ local_mvba_recorded i j
  aux_mvba_decided_pos j m := true
  local_mvba_recorded i j := true
}

action on_mvba_decide_neg (i : node) (j : node) (v : mvalue) {
  require ¬ is_byz i
  require is_proposer j
  require mvba.decided mvba_st i v
  require mval_neg (mvba.entries v) j
  -- The bridge, negative form: a negative FastQC, or (with FBCert) a
  -- negative FallbackQC or an EquivCert (equivocation excludes the
  -- proposer, Appendix C.3 (`subsection:fallback_path`)).
  require vote_quorum_neg j ∨ ((fb_quorum_neg j ∨ equiv_evidence j) ∧ fbcert)
  require ¬ local_mvba_recorded i j
  aux_mvba_decided_neg j := true
  local_mvba_recorded i j := true
}

/-- Validator `i` has handled every proposer's entry of its decision `v`,
each in its own row (`on_mvba_decide_*`): the model shadow of the decision
delivering `B′` at once (Algorithm 5, line 37 (`line:fb-mvba-decide`)). It
reads only `i`'s own state and its own decision. -/
action mvba_terminate (i : node) (v : mvalue) {
  require ¬ is_byz i
  -- Fired once: `i` has not transported its decision yet.
  require ¬ local_mvba_complete i
  require mvba.decided mvba_st i v
  -- `i` has handled every proposer's entry of its decision.
  require ∀ J, is_proposer J → local_mvba_recorded i J
  local_mvba_complete i := true
}

/-! ## Fallback commit round (Algorithm 5 (`alg:fallback`),
Algorithm 5, lines 37–47 (`line:fb-mvba-decide`–`line:fb-finalize`))

An MVBA decision does not finalize by itself:
upon `MVBA[s].decide(B')` each decider first waits, for every positive
FallbackQC entry `⟨s, j, m⟩` in `B'`, until it has received and validated
its own assigned chunk under `m` — re-broadcasting that chunk, so the
eventual certificate also attests data availability
(Algorithm 5, line 39 (`line:fb-commit-wait`)) — and then broadcasts a `FallbackCommitVote` over
the decided entries (Algorithm 5, line 41 (`line:fb-commitvote`)). `2f+1` such votes aggregate
into the transferable `fbCommitQC` (Algorithm 5, line 42 (`line:fb-collect-commit`) /
Algorithm 5, line 43 (`line:fb-formcommitqc`)), and finalization happens on `fbCommitQC` receipt
(Algorithm 5, line 45 (`line:fb-recv-commit`) / Algorithm 5, line 47 (`line:fb-finalize`)).

Modelling notes:

* **Chunk re-dissemination happens inside the fallback-entry rule**
  (`fb_sign_pos`, Algorithm 5, line 12 (`line:fb-redisseminate`)): a
  correct signer of a positive entry has decoded the proposal, and in the
  same step it re-encodes it and sends every validator its assigned chunk.
  Without it the DA wait below could starve for a *Byzantine* proposer's
  decided root: only a correct proposer is bound to send every chunk, and
  `byz_send_chunk` is unfair ((F-byz)). The re-broadcast of
  Algorithm 5, line 39 (`line:fb-commit-wait`) sends the validator's *own*
  chunk, which `chunk_quorum` already counts once the validator holds it,
  so it changes no relation and has no step.
  A Byzantine validator can send any chunk under its own name at any time,
  unfairly, as `byz_redisseminate_chunk`.
* **The DA wait is the paper's, under the `FallbackQC` entries of the
  validator's own `B′`** (Algorithm 5, line 38 (`line:fb-commit-foreach`)). Correct validators agree
  on entries but may decide representations whose certificates differ, so
  each waits under its own decision: `cast_fb_commit i v` takes `i`'s
  decided `v` as a parameter and waits for its own chunk under exactly the
  positive entries `v` certifies by a `FallbackQC` (`mval_fb v j`). Both
  reads are positive. A root `FastQC`-certified elsewhere but
  `FallbackQC`-certified in `v` is waited for, as in the paper. Fair
  progress needs no chunk under a `FastQC`; under a `FallbackQC` one of its
  `f+1` signers is correct and re-disseminated the chunk when it signed
  (Algorithm 5, line 12 (`line:fb-redisseminate`)).
* **A redelivered decision** (the contract's Integrity permits outputs
  with one entry vector and different representations;
  [PaperAlignment.md](../docs/PaperAlignment.md) §6, P11). The vote fires
  once per validator (`local_fbcommit_voted`), its content is the entry
  vector, and its wait reads the representation it is cast for, so every
  reading of the paper's handler is a run of the model.
* **Participation gating** (the paper's standing convention that every
  message-sending rule requires active participation,
  Appendix C.3 (`subsection:chorus-protocol-overview`)) is modelled directly:
  `cast_fb_commit` requires its sender to be actively participating, like
  every other sending rule ("Participation inputs" above). -/

/-- Validator `i` casts its fallback commit vote over the decided entries
(Algorithm 5, line 41 (`line:fb-commitvote`)), after the DA wait under the
`FallbackQC` entries of its own decision `v`. -/
action cast_fb_commit (i : node) (v : mvalue) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  -- Upon `MVBA[s].decide(B′)` (Algorithm 5, line 37 (`line:fb-mvba-decide`)): `v` is `i`'s own
  -- decided meta-block `B′`.
  require mvba.decided mvba_st i v
  -- The decision delivers the full entry vector at once, whose model
  -- shadow is `i`'s own transport record (`mvba_terminate i`).
  require local_mvba_complete i
  -- DA wait (Algorithm 5, line 38 (`line:fb-commit-foreach`), Algorithm 5, line 39 (`line:fb-commit-wait`)): for each
  -- positive entry ⟨s, J, M⟩ of `B′` held by a FallbackQC, wait until the
  -- own assigned chunk for `M` is received and validated. An entry held by
  -- a FastQC needs no wait.
  require ∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → chunk_received i J M
  -- Fired once: `i` has not cast its fallback commit vote yet.
  require ¬ local_fbcommit_voted i
  -- The vote signs the decided entries `entries(B′)`.
  msg_fbcommit_sig i (mvba.entries v) := true
  local_fbcommit_voted i := true
}

/-- Form and broadcast a fallback commit certificate (Algorithm 5, line 42
(`line:fb-collect-commit`) – Algorithm 5, line 44
(`line:fb-commit-broadcast`)): collector `c` has received `2f+1` fallback
commit votes over the same entries `e`, aggregates them into
`fbCommitQC = ⟨FallbackCommit, s, e, Σ⟩`, and broadcasts it under its own
name. The guard is the certificate's validity check. A send, so gated on
participation; once (`local_fbcommitqc_sent`). A Byzantine validator can
form and send a valid certificate at any time
(`byz_broadcast_fbcommitqc`). -/
action broadcast_fbcommitqc (c : node) (e : mentries) (q : nodeset) {
  require ¬ is_byz c
  require participating c
  require ¬ abandoned c
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_fbcommit_sig r e
  require ¬ local_fbcommitqc_sent c
  msg_fbcommitqc c e := true
  local_fbcommitqc_sent c := true
}

/-! ## Commit decision (finalization)

A validator finalizes only on a *commitment proof* (Lemma 9 (`lemma:chorus-agreement`)
proof) it has received, and the certificate carries the entries it
commits. There are three, one per receive handler, so each per-proposer
assignment comes in three routes:

* `commit_assign_*_fast` — a fast commit certificate for the entry
  (Algorithm 4, line 34 (`line:fast-recv-commitqc`) / Algorithm 4, line 36 (`line:fast-finalize`));
* `commit_assign_*_fb` — a fallback commit certificate
  `fbCommitQC = ⟨FallbackCommit, s, e, Σ⟩` whose entry vector `e` has the
  entry (Algorithm 5, line 45 (`line:fb-recv-commit`) / Algorithm 5, line 47 (`line:fb-finalize`));
* `commit_assign_*_mvba` — the MVBA's own commit certificate, checked with
  the contract's `mvba.certifies` against a representation `v` of the
  entries it certifies, and with the bridge on the entry's certificate:
  "A correct validator that receives a valid such certificate re-broadcasts
  it and finalizes the certified outcome" (Supplement, Section 1.2
  (`subsec:mvba-protocol`), "Decision output and handoff").

Every route reads a message the validator received, from any sender,
positively ([Locality.md](../docs/Locality.md) R2), and **re-broadcasts the
certificate under its own name** in the same step (Algorithm 4, line 35
(`line:fast-rebroadcast-commitqc`), Algorithm 5, line 46 (`line:fb-commit-rebroadcast`),
and the supplement's "re-broadcasts it"). Finalizing is therefore a sending
rule, gated on participation like every other ("Participation inputs"
above). A validator that has abandoned the slot does not finalize it
afterwards; the caller abandons only after finalizing (Algorithm 1, line 23
(`line:abandon`)).

Holding a FastQC for every proposer without a commitQC permits only a
*speculative* commit (Algorithm 4 (`alg:fast-path-certification`), "speculatively commit"),
which the paper allows to be reverted under equivocation; it is
deliberately *not* a finalization route here. See the speculative-safety
invariants below for the checked claim about when speculation is safe.

The per-entries finalization is decomposed into per-proposer assignment
actions followed by a `finalize_commit` umbrella action (the standard Veil
idiom for atomic for-loops). -/

/-- Validator `i` commits the positive entry `⟨s, j, m⟩` on a fast commit
certificate received from `c`, and re-broadcasts it. -/
action commit_assign_pos_fast (i : node) (j : node) (m : merkle_root) (c : node) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require ¬ local_committed i
  require is_proposer j
  require msg_commitqc_pos c j m
  -- Per-proposer single choice, and fired once: `i` has committed no
  -- entry for `j` yet.
  require ∀ m', ¬ local_committed_pos i j m'
  require ¬ local_committed_neg i j
  local_committed_pos i j m := true
  msg_commitqc_pos i j m := true
}

/-- Validator `i` commits the positive entry `⟨s, j, m⟩` of the entry vector
`e` a fallback commit certificate received from `c` carries, and
re-broadcasts the certificate. -/
action commit_assign_pos_fb (i : node) (j : node) (m : merkle_root) (c : node) (e : mentries) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require ¬ local_committed i
  require is_proposer j
  require msg_fbcommitqc c e
  require mval_pos e j m
  require ∀ m', ¬ local_committed_pos i j m'
  require ¬ local_committed_neg i j
  local_committed_pos i j m := true
  msg_fbcommitqc i e := true
}

/-- Validator `i` commits the positive entry `⟨s, j, m⟩` certified by an
MVBA commit certificate `c` received from `s`, for the entries of the
representation `v`, after the bridge check on the entry's certificate, and
re-broadcasts the certificate. -/
action commit_assign_pos_mvba (i : node) (j : node) (m : merkle_root) (s : node) (c : mmsg) (v : mvalue) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require ¬ local_committed i
  require is_proposer j
  require msg_mvba_cert s c
  require mvba.certifies mvba_st c (mvba.entries v)
  require mval_pos (mvba.entries v) j m
  -- The bridge: the certificate `v` names for the entry verifies against
  -- the network.
  require (¬ mval_fb v j ∧ vote_quorum_pos j m) ∨ (mval_fb v j ∧ fb_quorum_pos j m ∧ fbcert)
  require ∀ m', ¬ local_committed_pos i j m'
  require ¬ local_committed_neg i j
  local_committed_pos i j m := true
  msg_mvba_cert i c := true
  aux_mvba_decided_pos j m := true
}

/-- Validator `i` commits the negative entry `⟨s, j, ⊥⟩` on a fast commit
certificate received from `c`, and re-broadcasts it. -/
action commit_assign_neg_fast (i : node) (j : node) (c : node) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require ¬ local_committed i
  require is_proposer j
  require msg_commitqc_neg c j
  require ∀ m, ¬ local_committed_pos i j m
  require ¬ local_committed_neg i j
  local_committed_neg i j := true
  msg_commitqc_neg i j := true
}

/-- Validator `i` commits the negative entry `⟨s, j, ⊥⟩` of the entry vector
`e` a fallback commit certificate received from `c` carries, and
re-broadcasts the certificate. -/
action commit_assign_neg_fb (i : node) (j : node) (c : node) (e : mentries) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require ¬ local_committed i
  require is_proposer j
  require msg_fbcommitqc c e
  require mval_neg e j
  require ∀ m, ¬ local_committed_pos i j m
  require ¬ local_committed_neg i j
  local_committed_neg i j := true
  msg_fbcommitqc i e := true
}

/-- Validator `i` commits the negative entry `⟨s, j, ⊥⟩` certified by an
MVBA commit certificate; see `commit_assign_pos_mvba`. -/
action commit_assign_neg_mvba (i : node) (j : node) (s : node) (c : mmsg) (v : mvalue) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
  require ¬ local_committed i
  require is_proposer j
  require msg_mvba_cert s c
  require mvba.certifies mvba_st c (mvba.entries v)
  require mval_neg (mvba.entries v) j
  -- The bridge, negative form.
  require vote_quorum_neg j ∨ ((fb_quorum_neg j ∨ equiv_evidence j) ∧ fbcert)
  require ∀ m, ¬ local_committed_pos i j m
  require ¬ local_committed_neg i j
  local_committed_neg i j := true
  msg_mvba_cert i c := true
  aux_mvba_decided_neg j := true
}

/-- Validator `i` finalizes the slot once it has committed an entry for
every proposer. -/
action finalize_commit (i : node) {
  require ¬ is_byz i
  require participating i
  require ¬ abandoned i
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
    (Algorithm 4 (`alg:fast-path-certification`), receive handler) — `byz_sign_vote_pos`
    requires `chunk_received r j m`;
  - a broadcast vote must carry an entry for every proposer —
    `byz_cast_vote` requires per-proposer signatures;
  - a positive fallback entry must carry a verifying proposer signature
    `σ_p` — `byz_sign_fb_pos` requires `msg_proposer_signed j m`.
* It may **equivocate**. A Byzantine proposer may produce two distinct
  signed chunk headers `⟨s, j, m₁⟩` and `⟨s, j, m₂⟩` with `m₁ ≠ m₂` (two
  firings of `byz_sign_proposer`), and may selectively deliver the
  corresponding chunks to disjoint subsets of validators via
  `byz_send_chunk`. The protocol-level evidence of this equivocation is
  the `equiv_evidence` certificate, which lets the MVBA decide negative on
  `j`'s output. A Byzantine *validator* may likewise cast inconsistent
  votes / fallback signatures / commit votes through the per-relation
  actions below.
* It has **no power over** honest validators' local state or the phase,
  and it sends messages only under its own name
  ([Locality.md](../docs/Locality.md) §4). Inside the MVBA instance the adversary's power is
  whatever `MVBASafety` leaves unconstrained: Byzantine parties' inputs
  and outputs, which the handlers never read (`¬ is_byz i`).

### Why per-relation actions rather than a single `transition`

A single monolithic `transition byz_step` listing per-relation "pin honest"
and "monotone Byzantine" clauses is an O(#relations)-conjunct
disjunctive formula whose elaboration exceeds Lean's heartbeat budget.
Per-relation actions give the Veil frame condition for free
— each action only updates one relation — and is conceptually clearer (one
action per adversarial *capability*). The reachable-state semantics is
preserved: any combined change decomposes into a sequence of these actions. -/

action byz_sign_proposer (j : node) (m : merkle_root) {
  require is_byz j
  msg_proposer_signed j m := true
}

/- A Byzantine proposer sends any validator any chunk under its own name:
selective delivery, and chunks of roots it never signed. -/
action byz_send_chunk (i : node) (j : node) (m : merkle_root) {
  require is_byz j
  msg_chunk j i j m := true
}

/- A Byzantine sender sends any chunk of any root, under its own name. The
receiver checks the proposer and its signature (`record_chunk`); nothing
limits which chunks the adversary knows. The correct signer's
re-dissemination is part of `fb_sign_pos`. -/
action byz_redisseminate_chunk (r : node) (i : node) (j : node) (m : merkle_root) {
  require is_byz r
  msg_chunk r i j m := true
}

action byz_sign_vote_pos (r : node) (j : node) (m : merkle_root) {
  require is_byz r
  -- A positive vote entry is network-valid only with the signer's valid
  -- *assigned* chunk attached; votes with unbacked positive entries are
  -- discarded by every honest receiver (Algorithm 4 (`alg:fast-path-certification`),
  -- receive handler: the carried chunk must have the sender's chunk index
  -- and match the entry's root). This is what makes `f+1` accepted
  -- positive votes pin `f+1` *distinct* chunks, i.e.
  -- `vote_pos_quorum_implies_decodable` honest about `isDecoded`.
  -- This is the receiver's check stated on the sender; it moves to the
  -- honest receivers ([Locality.md](../docs/Locality.md) §4, B4).
  require chunk_received r j m
  msg_vote_pos_sig r j m := true
}

action byz_sign_vote_neg (r : node) (j : node) {
  require is_byz r
  msg_vote_neg_sig r j := true
}

action byz_cast_vote (r : node) {
  require is_byz r
  -- A broadcast vote is network-valid only if it carries a signed entry
  -- for every proposer. This is the receiver's check stated on the sender;
  -- it moves to the honest receivers ([Locality.md](../docs/Locality.md) §4,
  -- B4).
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
  -- The signature is unforgeable ([Locality.md](../docs/Locality.md) §4, B2).
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

/- A Byzantine holder of `2f+1` broadcast commit votes forms and broadcasts
the (valid) commit certificate under its own name, at any time and any
number of times (the capability of `broadcast_commitqc_*`). -/
action byz_broadcast_commitqc_pos (r : node) (j : node) (m : merkle_root) (q : nodeset) {
  require is_byz r
  require nset.supermajority q
  require ∀ a, nset.member a q → msg_commit_pos_sig a j m ∧ msg_commit_cast a
  msg_commitqc_pos r j m := true
}

action byz_broadcast_commitqc_neg (r : node) (j : node) (q : nodeset) {
  require is_byz r
  require nset.supermajority q
  require ∀ a, nset.member a q → msg_commit_neg_sig a j ∧ msg_commit_cast a
  msg_commitqc_neg r j := true
}

action byz_sign_fbcommit (r : node) (e : mentries) {
  require is_byz r
  -- Any entry vector: receivers verify only the signature, and "matching
  -- entries" is enforced when a certificate is formed.
  msg_fbcommit_sig r e := true
}

/- A Byzantine holder of `2f+1` fallback commit votes over the same entries
forms and broadcasts the (valid) fallback commit certificate under its own
name (the capability of `broadcast_fbcommitqc`). -/
action byz_broadcast_fbcommitqc (r : node) (e : mentries) (q : nodeset) {
  require is_byz r
  require nset.supermajority q
  require ∀ a, nset.member a q → msg_fbcommit_sig a e
  msg_fbcommitqc r e := true
}

/- A Byzantine validator sends any MVBA message as a commit certificate
under its own name: a receiver checks it (`mvba.certifies`, `mvba.accept`)
before acting on it. -/
action byz_send_mvba_cert (r : node) (c : mmsg) {
  require is_byz r
  msg_mvba_cert r c := true
}

action byz_release_msg_decrypt_share (r : node) {
  require is_byz r
  msg_decrypt_share r := true
}

/-! ## Safety properties

The principal property is *agreement* (Lemma 9 (`lemma:chorus-agreement`)): any two
honest validators that commit slot `s` commit the same core. -/

/-- Agreement on positive entries: two honest validators that finalized the
slot committed the same root for proposer `J`. -/
safety [agreement_pos]
  ∀ (I1 I2 : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 ∧
    local_committed I1 ∧ local_committed I2 ∧
    local_committed_pos I1 J M1 ∧ local_committed_pos I2 J M2 →
    M1 = M2

/-- Agreement across polarities: when one honest validator finalized with a
positive entry for proposer `J`, no honest validator finalized with the
negative entry for `J`. -/
safety [agreement_pos_neg]
  ∀ (I1 I2 : node) (J : node) (M : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 ∧
    local_committed I1 ∧ local_committed I2 ∧
    local_committed_pos I1 J M →
    ¬ local_committed_neg I2 J

/-- An honest validator commits at most one root per proposer. -/
safety [integrity_pos]
  ∀ (I : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I ∧ local_committed_pos I J M1 ∧ local_committed_pos I J M2 →
    M1 = M2

/-- An honest validator never commits both a positive and the negative entry
for the same proposer. -/
safety [integrity_pos_neg]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I → ¬ (local_committed_pos I J M ∧ local_committed_neg I J)

/-! ### Hiding (Lemma 7 (`lemma:chorus-hiding`), protocol layer) -/

/-- The slot key opens every proposal ciphertext of the slot, and reconstructing
it takes `f+1` extraction shares (Appendix C.2 (`appendix:encryption`)). At most `f`
shares can come from Byzantine validators, and an honest validator releases
its share only with its deadline vote — so the key cannot be reconstructed
while the slot is still `pre_deadline`. Together with the TIBE secrecy
axiom (`ThresholdIBE.decrypt_secret` in [Primitives.lean](Primitives.lean),
which reduces payload secrecy to share-threshold reconstruction) and the
paper's random-oracle simulation (Appendix C.2 (`appendix:encryption`)), this yields the
hiding property: proposal contents are hidden until the deadline. -/
safety [hiding_until_deadline]
  slot_key_released → phase ≠ pre_deadline

/-! ### Proposal inclusion (Lemma 10 (`lemma:chorus-proposal-inclusion`))

If a correct proposer's on-time dissemination reached every honest
validator (`all_honest_recorded j m` — the protocol-level shadow of the
paper's `s.deadline − Δ ≥ GST` premise, see Proposition 3 (`prop:honest-positive-entry`)),
then no honest validator ever commits a negative entry for `j`, and every
committed positive entry for `j` carries the proposer's root `m`. -/

/-- Under the inclusion premise for `(J, M)`, every honest positive commit for
`J` carries the root `M`. -/
safety [proposal_inclusion]
  ∀ (J I : node) (M M' : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz I ∧ local_committed_pos I J M' →
    M' = M

/-- Under the inclusion premise for `J`, no honest validator commits the
negative entry for `J`. -/
safety [proposal_inclusion_no_neg]
  ∀ (J I : node) (M : merkle_root),
    all_honest_recorded J M ∧ ¬ is_byz I →
    ¬ local_committed_neg I J

/-! ### Speculative finality (Section 4.2 (`subsection:fast-path-overview`), speculative commit)

A validator holding FastQCs for every proposer may speculatively commit
before the commitQC forms. The paper's headline claim is that a
speculative commit "may be reverted ... only if some validator
equivocated"; the proof sketch's closing parenthetical
(Section 4.5 (`subsection:chorus-proof`)) widens the culprit set to the proposer
*committing to an invalidly encoded root*: an honest validator that
gathers `f+1` yes votes on a root whose chunks fail to re-encode casts
fallback-no with no equivocation anywhere — "either way the proposer is
the culprit". Checked here against exactly that culprit set: in any
reachable state free of vote and proposer equivocation
(`no_equivocation`) in which no proposer has committed to an
invalidly encoded root (`no_invalid_encoding`), a validator's own
positive FastQC — its speculative value — agrees with every finalized
commit. Both hypotheses are needed: `no_equivocation` alone would suffice
only in a model where invalid encodings cannot exist, and `fb_sign_neg`
admits the re-encode-failure case ([ChorusDesign.md](../docs/ChorusDesign.md) §3.4). -/

/-- Speculative agreement, positive: absent equivocation and invalid
encodings, an honest validator's positive FastQC for `J` agrees with every
honest positive commit for `J`. -/
safety [speculative_agreement_pos]
  no_equivocation → no_invalid_encoding →
  ∀ (I1 I2 : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 ∧
    local_fastqc_pos I1 J M1 ∧ local_committed_pos I2 J M2 →
    M1 = M2

/-- Speculative agreement across polarities: under the same hypotheses, an
honest positive FastQC for `J` excludes every honest negative commit for `J`. -/
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

/-- Every recorded positive entry is backed by the recorded chunk
(`record_chunk` requires delivery). Basis of the data-availability chain. -/
invariant [local_entry_pos_chunk]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_entry_pos I J M → chunk_received I J M

/-! The atomic `vote` action sets `local_voted R` together with the per-proposer
`msg_vote_*_sig` entries and `local_entry_neg`, so the link "`local_voted ↔
honest signer has signed`" holds structurally after `vote` fires — and the
invariants below need only constrain honest signers' signatures (Byzantine
signers go through the `byz_sign_vote_*` actions).

The "signed-implies-voted" invariants make that structural link explicit.
Without them, the SMT-inductive argument for the `*_backed` invariants
fails: the solver cannot rule out a state in which an honest validator had
`msg_vote_pos_sig` set before voting (`vote`'s update keeps such a tuple);
with these invariants in scope, that state is contradictory. They are also
what makes `vote`'s monotone disjunctions coincide with a plain overwrite at
reachable states. -/

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

/-- An honest validator votes only after the deadline; with monotone phase
this timestamps every voting artefact. Basis of `hiding` and of the
phase reasoning in the proposal-inclusion invariants. -/
invariant [voted_post_deadline]
  ∀ (R : node),
    ¬ is_byz R ∧ local_voted R → phase ≠ pre_deadline

/-- Decryption shares are released only with the vote (honest signers). -/
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

/-- An honest validator that has voted and holds a positive entry has that
entry's signature on the network (the vote is atomic over all
proposers, and entries are frozen at the deadline while voting happens
after it). -/
invariant [voted_entry_pos_signed]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ is_proposer J ∧ local_voted R ∧ local_entry_pos R J M →
    msg_vote_pos_sig R J M

/-- A broadcast vote carries an entry for every proposer (receivers discard
incomplete votes; `byz_cast_vote` mirrors the check). -/
invariant [vote_cast_entries]
  ∀ (R : node) (J : node),
    msg_vote_cast R ∧ is_proposer J →
    ((∃ M, msg_vote_pos_sig R J M) ∨ msg_vote_neg_sig R J)

/-- Every network-valid positive vote signature — honest or Byzantine — is
backed by the signer's delivered chunk: honest votes by
`local_entry_pos_chunk`, Byzantine ones by the validity precondition of
`byz_sign_vote_pos`. This is the σ/chunk-carrying discipline of the
vote message (Algorithm 3 (`alg:voting`)), and it is what makes the erasure-decode
threshold (c) a consequence of the vote threshold (b) at the network
level. -/
invariant [vote_pos_sig_chunk]
  ∀ (R : node) (J : node) (M : merkle_root),
    msg_vote_pos_sig R J M → chunk_received R J M

/-! "Backing-quorum" auxiliaries link each aggregated FastQC to a supermajority
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

/-- FastQC uniqueness: a single honest validator cannot hold two FastQCs
for the same proposer with different roots. Follows from the backing
quorum's existence and vote_unique_pos applied to the supermajority. -/
invariant [local_fastqc_pos_self_unique]
  ∀ (I : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I ∧ local_fastqc_pos I J M1 ∧ local_fastqc_pos I J M2 → M1 = M2

/-- Cross-validator FastQC agreement: any two honest validators' positive
FastQCs for the same proposer agree on the root. Follows from quorum
intersection (any two supermajorities share an honest validator) +
vote_unique_pos. This is the paper's Proposition 1 (`prop:agreement-entries`), case 1. -/
invariant [local_fastqc_pos_cross_unique]
  ∀ (I1 I2 : node) (J : node) (M1 M2 : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 ∧
    local_fastqc_pos I1 J M1 ∧ local_fastqc_pos I2 J M2 → M1 = M2

/-- Positive/negative FastQC exclusion: same proposer cannot have an honest
positive FastQC and an honest negative FastQC. Follows from the
intersecting-supermajority + vote_unique_pos_neg argument. -/
invariant [local_fastqc_pos_neg_excl]
  ∀ (I1 I2 : node) (J : node) (M : merkle_root),
    ¬ is_byz I1 ∧ ¬ is_byz I2 →
    ¬ (local_fastqc_pos I1 J M ∧ local_fastqc_neg I2 J)

/-- An honest FastQC (either polarity) postdates the deadline: its backing
quorum contains an honest voter, and honest votes are post-deadline. -/
invariant [fastqc_post_deadline]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ (local_fastqc_pos I J M ∨ local_fastqc_neg I J) →
    phase ≠ pre_deadline

/-- An honest positive fallback signed entry is backed by an f+1 quorum of
positive votes (`fb_sign_pos` (b)); persistent because signatures are. -/
invariant [msg_fb_pos_sig_backed]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ msg_fb_pos_sig R J M →
    ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_vote_pos_sig r J M

/-- Every network-valid positive fallback entry — honest or Byzantine — pins
a proposer-signed root: a positive entry carries the proposer's signature
σ_p on ⟨s, j, m⟩ and receivers verify it (Appendix C.3 (`subsection:fallback_path`)).
Honest entries via their f+1 vote-quorum backing (the quorum's honest
voter's `local_entry_pos_signed`), Byzantine ones by the validity
precondition of `byz_sign_fb_pos`. The σ_p-carrying discipline of the
entry, mirroring `vote_pos_sig_chunk`'s σ/chunk discipline for votes.
Deliberately unrestricted by honesty: it is what makes the network-level
build totality ([Chorus/Counting.lean](Chorus/Counting.lean)) hold over an *arbitrary* accepted
receipt supermajority, Byzantine members included. -/
invariant [fb_pos_sig_proposer_signed]
  ∀ (R : node) (J : node) (M : merkle_root),
    msg_fb_pos_sig R J M → msg_proposer_signed J M

/-- Honest fallback entries exist only for proposers (`fb_sign_*` require
`is_proposer`). Scopes the fallback-witness invariants below to
proposers without altering their quantifier shape. -/
invariant [fb_sig_is_proposer]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ (msg_fb_pos_sig R J M ∨ msg_fb_neg_sig R J) → is_proposer J

/-- Honest fallback-path signatures postdate the fallback arm. Needed to
show that the proposal-inclusion premise (recorded strictly
pre-deadline) cannot become true after a conflicting fallback entry
already exists. -/
invariant [fb_sig_phase]
  ∀ (R : node) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ (msg_fb_pos_sig R J M ∨ msg_fb_neg_sig R J ∨ msg_fallback_sig R) →
    (phase = post_fb_arm ∨ phase = post_mvba_arm)

/-! ### Path exclusion

The fast commit vote and the fallback vote are mutually exclusive per
honest validator (`pathVote`, Algorithm 4, line 25 (`line:fast-pathvote`) / the fallback guard).
This is the pivot of the paper's cross-path agreement argument
(Proposition 1 (`prop:agreement-entries`), case 3): a commitQC and an FBCert are both
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

/-! ### CommitQC-level consequences (Proposition 1 (`prop:agreement-entries`))

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
  ∀ (C J : node) (M : merkle_root),
    msg_commitqc_pos C J M → commitqc_pos J M

invariant [msg_commitqc_neg_backed]
  ∀ (C J : node),
    msg_commitqc_neg C J → commitqc_neg J

invariant [msg_commitqc_pos_votes]
  ∀ (C J : node) (M : merkle_root),
    msg_commitqc_pos C J M → vote_quorum_pos J M

invariant [msg_commitqc_neg_votes]
  ∀ (C J : node),
    msg_commitqc_neg C J → vote_quorum_neg J

invariant [commitqc_pos_unique]
  ∀ (C1 C2 J : node) (M1 M2 : merkle_root),
    msg_commitqc_pos C1 J M1 ∧ msg_commitqc_pos C2 J M2 → M1 = M2

invariant [commitqc_pos_neg_excl]
  ∀ (C1 C2 J : node) (M : merkle_root),
    ¬ (msg_commitqc_pos C1 J M ∧ msg_commitqc_neg C2 J)

invariant [commitqc_pos_mvba_consistent]
  ∀ (C J : node) (M1 M2 : merkle_root),
    msg_commitqc_pos C J M1 ∧ aux_mvba_decided_pos J M2 → M1 = M2

invariant [commitqc_pos_mvba_neg_excl]
  ∀ (C J : node) (M : merkle_root),
    ¬ (msg_commitqc_pos C J M ∧ aux_mvba_decided_neg J)

invariant [commitqc_neg_mvba_pos_excl]
  ∀ (C J : node) (M : merkle_root),
    ¬ (msg_commitqc_neg C J ∧ aux_mvba_decided_pos J M)

/-! ### MVBA correctness, from the class

The abstract MVBA state is reachable (`[mvba_init]` and the contract's
closure axioms, through `mvba_step` and `mvba_propose`), and every record
Chorus holds is the projection of some correct validator's decision on it
— the **tie invariants**, inductive under the oracle step because
`decided_mono` keeps decisions decided along every transition. Uniqueness
and pos/neg exclusion of the records then follow from `mvba.agreement` at
the reachable state plus the two `mval_*` assumptions: this is the
contract's agreement *used*, not restated. They stay as invariants because
the downstream cells e-match on them. The `*_backed` invariants record the
bridge evidence a record carried — that record is what keeps the
commitQC-consistency invariants above inductive when commit votes are cast
*after* the decision. -/

invariant [mvba_reachable] mvba.reachable mvba_st

invariant [mvba_decided_pos_tied]
  ∀ (J : node) (M : merkle_root),
    aux_mvba_decided_pos J M →
    (∃ I V, ¬ is_byz I ∧ mvba.decided mvba_st I V ∧ mval_pos (mvba.entries V) J M) ∨
    (∃ C E, mvba.certifies mvba_st C E ∧ mval_pos E J M)

invariant [mvba_decided_neg_tied]
  ∀ (J : node),
    aux_mvba_decided_neg J →
    (∃ I V, ¬ is_byz I ∧ mvba.decided mvba_st I V ∧ mval_neg (mvba.entries V) J) ∨
    (∃ C E, mvba.certifies mvba_st C E ∧ mval_neg E J)

invariant [mvba_decided_pos_unique]
  ∀ (J : node) (M1 M2 : merkle_root),
    aux_mvba_decided_pos J M1 ∧ aux_mvba_decided_pos J M2 → M1 = M2

invariant [mvba_decided_pos_neg_excl]
  ∀ (J : node) (M : merkle_root),
    ¬ (aux_mvba_decided_pos J M ∧ aux_mvba_decided_neg J)

invariant [mvba_decided_pos_backed]
  ∀ (J : node) (M : merkle_root),
    aux_mvba_decided_pos J M →
    vote_quorum_pos J M ∨ (fb_quorum_pos J M ∧ fbcert)

invariant [mvba_decided_neg_backed]
  ∀ (J : node),
    aux_mvba_decided_neg J →
    vote_quorum_neg J ∨ ((fb_quorum_neg J ∨ equiv_evidence J) ∧ fbcert)

/-- **What `AvailReady` means** (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Commit availability condition"): a correct
validator is `AvailReady` for a representation only once it has received
its assigned chunk under every positive `FallbackQC` entry of it. Chorus is
the input's only caller (`mvba_avail_ready`), and the contract's frames
say nothing else sets it. -/
invariant [avail_ready_chunks]
  ∀ (I : node) (V : mvalue) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ mvba.availReady mvba_st I V →
    mval_pos (mvba.entries V) J M → mval_fb V J → chunk_received I J M

/-- MVBA decisions exist only for proposers (the meta-block has one entry
per proposer; the handlers require `is_proposer`). Excludes
unreachable non-proposer decisions from the inductive state space. -/
invariant [mvba_decided_is_proposer]
  ∀ (J : node) (M : merkle_root),
    (aux_mvba_decided_pos J M ∨ aux_mvba_decided_neg J) → is_proposer J

/-- Recorded MVBA entries postdate the deadline (phase timestamping, used by
the proposal-inclusion preservation argument). The decision handler has no
phase gate ("upon `MVBA[s].decide(B′)`", Algorithm 5, line 37
(`line:fb-mvba-decide`)), and neither has the certificate rule; the
deadline follows from the certificate every record is backed by, which has
a correct signer who signed after the deadline. -/
invariant [mvba_decided_phase]
  ∀ (J : node) (M : merkle_root),
    (aux_mvba_decided_pos J M ∨ aux_mvba_decided_neg J) → phase ≠ pre_deadline

/-! ### Commit backing -/

invariant [local_committed_pos_backed]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_committed_pos I J M →
    (∃ C, msg_commitqc_pos C J M) ∨ aux_mvba_decided_pos J M

invariant [local_committed_neg_backed]
  ∀ (I : node) (J : node),
    ¬ is_byz I ∧ local_committed_neg I J →
    (∃ C, msg_commitqc_neg C J) ∨ aux_mvba_decided_neg J

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
(Algorithm 6, line 12 (`line:da-wait`); Proposition 4 (`prop:chorus-totality`)). The chain runs through
`vote_pos_sig_chunk`: every network-valid positive vote carries its chunk,
so every vote quorum is itself a chunk quorum. -/

/-- (b) ⇒ (c) at the network level: an f+1 positive-vote quorum makes the
data decodable, because valid positive votes carry chunks. -/
invariant [vote_pos_quorum_implies_decodable]
  ∀ (J : node) (M : merkle_root),
    (∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q → msg_vote_pos_sig r J M) →
    chunk_quorum J M

invariant [local_fastqc_pos_chunks_decodable]
  ∀ (I : node) (J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_fastqc_pos I J M → chunk_quorum J M

invariant [mvba_decided_pos_chunks_decodable]
  ∀ (J : node) (M : merkle_root),
    aux_mvba_decided_pos J M → chunk_quorum J M

invariant [msg_commitqc_pos_chunks_decodable]
  ∀ (C J : node) (M : merkle_root),
    msg_commitqc_pos C J M → chunk_quorum J M

/- That every correct positive commit is decodable follows from the two
invariants above and `local_committed_pos_backed`; it is the theorem
`Chorus.local_committed_pos_implies_decodable`
([Chorus/Compose.lean](Chorus/Compose.lean)), proven once at every reachable
state rather than re-derived by the solver at every action. -/

/-! ### Proposal inclusion — inductive support

All invariants below are relativised to the premise
`all_honest_recorded J M`. Since honest entries are recorded strictly
pre-deadline and every conflicting artefact (vote, fallback entry, FastQC,
MVBA decision) postdates the deadline, the premise cannot become true
*after* a conflicting artefact exists — which is what keeps these
invariants inductive (the phase-timestamp invariants above supply that
argument to the solver).

The chain mirrors Proposition 3 (`prop:honest-positive-entry`): honest votes for `J` are
positive on `M` (entries are pinned), so no negative vote quorum, no
conflicting positive vote quorum, no honest negative fallback entry (any
witnessed 2f+1-vote quorum contains f+1 honest positive votes on `M`,
whose chunks make `M` decodable — this step uses
`honest_third_in_supermajority`), no conflicting
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
  ∀ (C J : node) (M : merkle_root),
    all_honest_recorded J M → ¬ msg_commitqc_neg C J

invariant [inclusion_commitqc_pos_root]
  ∀ (C J : node) (M M' : merkle_root),
    all_honest_recorded J M ∧ msg_commitqc_pos C J M' → M' = M

invariant [inclusion_no_mvba_neg]
  ∀ (J : node) (M : merkle_root),
    all_honest_recorded J M → ¬ aux_mvba_decided_neg J

invariant [inclusion_mvba_pos_unique]
  ∀ (J : node) (M M' : merkle_root),
    all_honest_recorded J M ∧ aux_mvba_decided_pos J M' → M' = M

/-! ### Speculative finality — inductive support

The paper's claim is temporal ("reverted only if ..."); its state-level
content is: while no proposer misbehaviour has occurred, nothing that
contradicts an existing FastQC can be certified. The one non-obvious step
is the negative fallback entry: an honest validator signs negative for `J`
only against a witnessed 2f+1-vote quorum `qv` in which no root had an f+1
positive sub-quorum with decodable, well-encoded data. `qv` is recorded as
the auxiliary history variable `aux_fb_neg_qv`, and under
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
(`supermajorities_share_third`) yields an f+1 positive
sub-quorum of `qv` — contradiction. -/

invariant [fb_neg_sig_has_witness]
  ∀ (R J : node),
    ¬ is_byz R ∧ msg_fb_neg_sig R J → ∃ qv, aux_fb_neg_qv R J qv

invariant [fb_neg_qv_is_proposer]
  ∀ (R J : node) (QV : nodeset),
    ¬ is_byz R ∧ aux_fb_neg_qv R J QV → is_proposer J

invariant [fb_neg_qv_backed]
  ∀ (R J : node) (QV : nodeset),
    ¬ is_byz R ∧ aux_fb_neg_qv R J QV →
    nset.supermajority QV ∧ (∀ r, nset.member r QV → msg_vote_cast r)

/-- A correct validator's vote receipt holds what the sender signed and
broadcast. -/
invariant [vote_rcv_pos_backed]
  ∀ (I R J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_vote_rcv_pos I R J M → msg_vote_cast R ∧ msg_vote_pos_sig R J M

invariant [vote_rcv_neg_backed]
  ∀ (I R J : node),
    ¬ is_byz I ∧ local_vote_rcv_neg I R J → msg_vote_cast R ∧ msg_vote_neg_sig R J

/-- The negative entry was signed against votes `R` had received: one entry
of each sender in `QV`. Receipts are never withdrawn. -/
invariant [fb_neg_qv_received]
  ∀ (R J : node) (QV : nodeset),
    ¬ is_byz R ∧ aux_fb_neg_qv R J QV →
    ∀ r, nset.member r QV → ((∃ M, local_vote_rcv_pos R r J M) ∨ local_vote_rcv_neg R r J)

/-- What the negative entry's guard saw stays true: among the received
votes of `QV`, no root has `f+1` positive entries that re-encode to it.
Every sender in `QV` has already been received from, and a receipt is kept
once (the receive steps' fired-once guards), so the receipts of `QV` are
frozen. -/
invariant [fb_neg_qv_no_rcv_quorum]
  ∀ (R J : node) (QV q : nodeset) (M : merkle_root),
    ¬ is_byz R ∧ aux_fb_neg_qv R J QV →
    ¬ (nset.greater_than_third q ∧
       (∀ r, nset.member r q → (nset.member r QV ∧ local_vote_rcv_pos R r J M)) ∧
       well_encoded M)

invariant [fb_neg_qv_no_pos_quorum]
  no_equivocation → no_invalid_encoding →
  ∀ (R J : node) (QV q : nodeset) (M : merkle_root),
    ¬ is_byz R ∧ aux_fb_neg_qv R J QV →
    ¬ (nset.greater_than_third q ∧
       ∀ r, nset.member r q → (nset.member r QV ∧ msg_vote_pos_sig r J M))

/-- The keystone lemma of the speculative argument: an honest negative
fallback entry excludes any positive vote supermajority for the same
proposer, absent equivocation. From `fb_neg_sig_has_witness` +
`supermajorities_share_third` (intersect `qv` with
the supermajority) + `fb_neg_qv_no_pos_quorum`. -/
invariant [fb_neg_no_pos_quorum]
  no_equivocation → no_invalid_encoding →
  ∀ (R J : node) (M : merkle_root),
    ¬ is_byz R ∧ msg_fb_neg_sig R J → ¬ vote_quorum_pos J M

invariant [spec_fastqc_pos_no_mvba_neg]
  no_equivocation → no_invalid_encoding →
  ∀ (I J : node) (M : merkle_root),
    ¬ is_byz I ∧ local_fastqc_pos I J M → ¬ aux_mvba_decided_neg J

invariant [spec_fastqc_pos_mvba_pos_unique]
  no_equivocation → no_invalid_encoding →
  ∀ (I J : node) (M M' : merkle_root),
    ¬ is_byz I ∧ local_fastqc_pos I J M ∧ aux_mvba_decided_pos J M' → M = M'

/-! ## Liveness — fairness and the fair-progress invariants

This section formalises the safety-invariant ingredients of the protocol's
liveness claim:

> **(Liveness)** Under the fairness assumptions stated below, the MVBA's
> own scheduling premises, the certificate bridge, and the caller's two
> conditions (every correct validator eventually participates, and none
> abandons before finalizing), every honest validator eventually commits
> the slot.

That statement is proven as `Chorus.termination`
([Chorus/Termination.lean](Chorus/Termination.lean)); its premises are the named
definitions of [Chorus/Liveness.lean](Chorus/Liveness.lean). This section is the
model-side half of the argument.

We follow the classical verification-diagrams approach for liveness in
deductive verification of distributed protocols; for a recent high-level
account see Kenneth L. McMillan, *"Toward Liveness Proofs at Scale"*, CAV
2024, §2 (Background and related work).

### The argument's structure

The argument has three ingredients: (1) is a premise of the theorem, (2)
is structural, and (3) is SMT-discharged here.

**(1) Fairness, a premise of the theorem.** Veil has no first-class
fairness annotations on actions, so the scheduling assumptions are stated
outside the model, as named hypotheses of `Chorus.termination`
([Chorus/Liveness.lean](Chorus/Liveness.lean)), indexed by the action's
category:

* **(F-justice)** — every phase-advancement action (`advance_to_*`), and
  every correct validator's action — the receipts and aggregations
  (`record_chunk`, `receive_vote_*`, `aggregate_fastqc_*`), the
  certificate sends (`broadcast_commitqc_*`, `broadcast_fbcommitqc`,
  `send_mvba_cert`), and the protocol rules (`vote`, `fb_sign_*`,
  `cast_fallback_vote`, `commit_sign_*`, `cast_fast_commit`,
  `mvba_propose`, the handoff `accept_mvba_commitqc`, the handlers
  `on_mvba_decide_*`, `mvba_terminate`, `cast_fb_commit`,
  `commit_assign_*`, `finalize_commit`) — that is *continuously enabled*,
  and whose messages came from correct senders (`Chorus.Owed`: the paper's
  network delivers only between correct validators), is fired eventually.
  That is every action that is neither Byzantine, nor the oracle step, nor
  one of the module's three inputs, which is how `Chorus.JusticeLabel`
  ([Chorus/Liveness.lean](Chorus/Liveness.lean)) states it. A message is
  acted on by its receiver's own step, so the eventual delivery of a
  correct sender's message is the fairness of that step.
  Every action on the list disables itself once it has fired (its
  "not already" guard, "Fired-once records"), so "continuously enabled"
  here means the same as "continuously able to change the state"
  (`Chorus.justice_enabledMove`). Three kinds of action are
  not on it. The inputs `participate`, `abandon` and `propose` are the
  caller's to invoke, so they carry no fairness; fairness of `abandon` would
  force every validator to abandon. The caller's conditions on them are
  premises of the claim instead. The oracle step `mvba_step` is scheduled
  by the MVBA's own admissible-execution model, which the claim assumes of
  the run's MVBA projection (`Chorus.MvbaAdmissible`). The Byzantine
  actions are (F-byz) below.
  Re-disseminated chunks need no fairness of their own: an honest positive
  fallback signer sends every validator its chunk inside its signing step
  (Algorithm 5, line 12 (`line:fb-redisseminate`)), so the fairness of
  `fb_sign_pos` covers them.
* **(F-compassion)** — strong fairness is part of the modelling vocabulary
  for the underlying implementation (whose per-validator local state is
  not monotone), but it is **not invoked** here: in Veil's
  monotone-relation framework enabledness is itself monotone — once an
  action's preconditions hold they stay holding until a negative atom
  flips false, after which the action is *permanently* disabled — so weak
  (F-justice) suffices.
* **(F-byz)** — Byzantine actions (`byz_*`) carry no scheduling preference;
  they are unfair.
* **The MVBA's termination** — a theorem of the `Mvba` model, `Mvba.termination`
  ([Mvba/Liveness.lean](Mvba/Liveness.lean)), which `Chorus.termination`
  ([Chorus/Termination.lean](Chorus/Termination.lean)) applies to the run's MVBA
  projection. What `Chorus.termination` assumes about the MVBA is how the
  projection's steps were scheduled (`Chorus.MvbaAdmissible`). It also
  assumes the certificate bridge (`Chorus.ValidBridge`). The MVBA's three
  caller premises are derived, not assumed:

  * *every correct validator proposes*. The enabledness of
    `mvba_propose`, meaning the invocation trigger plus per-proposer
    evidence in the proposal guards' own form, is the conclusion of
    `progress_dichotomy_of_saturation`
    ([Chorus/Progress.lean](Chorus/Progress.lean)); with it, (F-justice) on
    `mvba_propose` delivers the premise. Building the proposal is
    state-level: a fallback meta-block entry from **any** supermajority of
    accepted receipts, Byzantine members included
    (`build_totality_of_reachable`, [Chorus/Counting.lean](Chorus/Counting.lean); the
    per-validator implementation refinement is the receipt layer —
    [ChorusDesign.md](../docs/ChorusDesign.md) §7.2, [Architecture.md](../docs/Architecture.md) §5), and a
    fast meta-block by aggregation, whose guard witness is
    *definitionally* the dichotomy's vote-quorum evidence — compare
    `vote_quorum_pos` with `aggregate_fastqc_pos`'s requires;
  * *no correct validator abandons the MVBA before deciding*. The MVBA's
    `abandon()` is invoked only by Chorus's `abandon` input, and the
    caller abandons only after finalizing. So the premise holds on the
    branch of the proof where no correct validator has finalized, which is
    the only branch that needs the MVBA; the other branch finalizes
    through the commit route;
  * *every decided certificate is handed on* ((F-relay)). The MVBA's
    `decide` on a transferred certificate is the contract's `accept`
    input, which only `accept_mvba_commitqc` invokes; (F-justice) on it,
    owed once a correct validator has decided, delivers the premise.

  The *transport* of a decision into Chorus's records is (F-justice) on the
  handlers and `mvba_terminate`. Their enabledness has one leg the class
  does not give: the bridge `require` needs the decided entry's
  certificate on Chorus's network, where the class gives `Valid v`. That a
  `Valid` vector's certificates are network-visible is the completeness
  direction of the bridge — what "publicly verifiable" means — and it is
  `ValidBridge`'s completeness clause (the safety direction needs nothing:
  the guard only removes behaviours).

**(2) Well-founded ranking (structural).** Chorus is a one-shot per-slot
protocol: per slot, `node`, `nodeset`, the proposer set and the set of
*active* Merkle roots are fixed a priori, so the per-slot state space is
finite. Every mutable relation is monotone (actions only add tuples — the
audit is in [ChorusDesign.md](../docs/ChorusDesign.md) §3.1) and the phase advances in one direction. The
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
The whole split is a single theorem over reachable states —
`progress_dichotomy_of_saturation` ([Chorus/Progress.lean](Chorus/Progress.lean)): once every
honest validator has cast its path vote, either commitQCs exist for every
proposer from honest votes alone, or `mvba_invoked` holds with
per-proposer evidence in exactly the form of the handlers' bridge and of
`mvba_propose`'s validity guards. The
bullets below narrate its three branches. The run-level proof uses the
dichotomy on one branch only: the one on which no correct validator ever
finalizes, so none ever abandons, and every correct validator is actively
participating from some point on. If some correct validator finalizes, its
commit certificates are already on the network, and the other validators
finalize from them through the commit route (`Chorus.termination`).

* **`x ≥ 2f+1` (fast-dominant).** The honest commit votes agree per
  proposer (`local_fastqc_pos_cross_unique`), so a commitQC forms from
  honest votes alone (`commitqc_of_honest_fast_dominant`,
  [Chorus/Counting.lean](Chorus/Counting.lean)); every honest validator then commits via
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
  (`fastqc_complete_implies_mvba_evidence`), every honest validator can
  propose (`mvba_propose`), and the MVBA's own termination
  (`Mvba.termination`) delivers the complete decision vector, which the
  handlers transport; the *fallback commit round* then carries the
  decisions to finalization — (F-justice) on `cast_fb_commit`, whose DA
  wait the correct FallbackQC signers' re-dissemination meets, forms
  `fbcommitqc`, enabling `commit_assign_*` — see
  the fair-progress notes at the "Fallback commit round" invariant block.
* **`x = 0` (fallback).** All `≥ 2f+1` honest validators eventually cast
  fallback votes (per-proposer fallback signing is always enabled one way
  or the other — see `progress_fallback_signing`), so `FBCert` forms
  (`fbcert_of_honest_fallback_votes`, [Chorus/Counting.lean](Chorus/Counting.lean)) and
  `mvba_invoked` holds via the fallback trigger. Per-proposer evidence
  formation is the pigeonhole below; decisions then reach finalization
  through the commit round exactly as in the mixed branch.

**Evidence pigeonhole.** In the `x = 0` branch, the per-proposer evidence
is the theorem `Chorus.evidence_pigeonhole_of_reachable`
([Chorus/Pigeonhole.lean](Chorus/Pigeonhole.lean)): the `2f+1` honest fallback entries for
a proposer `j` split as `f+1` negative (a negative FallbackQC), `f+1`
positive on one root (a positive FallbackQC), or positive entries on two
roots — each pinning a proposer-signed root, i.e. `equiv_evidence`. This
split-counting partitions a quorum by the value its members signed — set
comprehension, outside the abstract `ByzNodeSet` language — which is why
it is plain Lean over the concrete instance family at every `n = 3f+1`
rather than an SMT-discharged invariant.

### What is not encoded inside Veil

The temporal/fairness layer itself — runs, weak fairness, and the chains
from fairness to finalization — is not encoded inside the Veil module. It
is plain Lean over labelled runs ([Fairness.lean](Fairness.lean),
[Chorus/Termination.lean](Chorus/Termination.lean)), consuming the invariants below at
reachable states. The invariants below discharge the *fair-progress*
safety content. -/

/-! ### MVBA completion implies per-proposer decision -/

/-- Lifted postcondition of `mvba_terminate` (whose guard is that every
proposer's entry of the decision is handled): once some validator has
transported its decision (`mvba_complete`), every proposer has a certified
entry in the auxiliary records. The certificate that carries the entries to
the other validators is produced by the fallback commit round ((F-justice)
on `cast_fb_commit` and `broadcast_fbcommitqc`; see the "Fallback commit
round" invariant block below). -/
invariant [mvba_complete_per_proposer]
  mvba_complete →
    ∀ J, is_proposer J →
      ((∃ M, aux_mvba_decided_pos J M) ∨ aux_mvba_decided_neg J)

/-! ### Fair progress — voting -/

/-- Once past the deadline, an honest validator that has not yet voted can
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

/-! ### Fair progress — fallback signing -/

/-- Once an honest validator on the fallback path has received the votes of
some supermajority `qv`, it can always cast its per-proposer fallback entry:
either some root has `f+1` received positive entries within `qv` that
re-encode to it — then `fb_sign_pos` is enabled, since the receipts are
backed by the signatures (`vote_rcv_pos_backed`) — or no root has, which
is `fb_sign_neg`'s guard for `qv`. Excluded middle over the guard's
evidence shape, stated to make the case analysis explicit. -/
invariant [progress_fallback_signing]
  ∀ (I J : node) (qv : nodeset),
    ¬ is_byz I ∧ is_proposer J ∧ nset.supermajority qv ∧
    (∀ r, nset.member r qv → ((∃ M, local_vote_rcv_pos I r J M) ∨ local_vote_rcv_neg I r J)) →
    (∃ (M : merkle_root) (q : nodeset), nset.greater_than_third q ∧
      (∀ r, nset.member r q → nset.member r qv ∧ local_vote_rcv_pos I r J M) ∧
      well_encoded M) ∨
    (∀ (M : merkle_root) (q : nodeset), ¬ (nset.greater_than_third q ∧
      (∀ r, nset.member r q → nset.member r qv ∧ local_vote_rcv_pos I r J M) ∧
      well_encoded M))

/-! ### Path-fast implies the validator's own FastQCs for every proposer -/

/-- Honest `cast_fast_commit i` requires `msg_commit_*_sig i J _` for every
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

/-! ### Commit completeness (composition support) -/

/-- A committed validator holds a decision for *every* proposer — the
persisted form of `finalize_commit`'s precondition. Needed by the
composition layer ([Chorus/Compose.lean](Chorus/Compose.lean)): the `SlotConsensus` instance
theorem assembles a committed validator's per-proposer decisions into a
total proposal vector, which requires this completeness fact about
reachable states. -/
invariant [local_committed_complete]
  ∀ (I : node),
    ¬ is_byz I ∧ local_committed I →
    ∀ J, is_proposer J →
      (∃ M, local_committed_pos I J M) ∨ local_committed_neg I J

/-! ### Fallback commit round — backing, confinement, and fair progress

Support for the fallback commit round (Algorithm 5, line 37 (`line:fb-mvba-decide`)–
Algorithm 5, line 47 (`line:fb-finalize`)).

The fair-progress leg for the round needs no dedicated `progress_*`
case-analysis invariant: once `local_mvba_complete i` holds, `cast_fb_commit i`'s
only non-derived precondition is the DA wait, which a correct signer of
each FallbackQC entry met when it signed: `fb_sign_pos` sends every
validator its chunk (Algorithm 5, line 12 (`line:fb-redisseminate`)). The round has no
phase gate: the paper's handler is "upon `MVBA[s].decide(B′)`"
(Algorithm 5, line 37 (`line:fb-mvba-decide`)). (F-justice) on `cast_fb_commit`
then yields `2f+1` honest commit votes over the decided entries, i.e.
`fbcommitqc e` (the counting is `fbcommitqc_of_honest_commit_votes`,
[Chorus/Counting.lean](Chorus/Counting.lean)); a correct collector forms and
sends the certificate (`broadcast_fbcommitqc`), and every validator
finalizes on the entries it carries (`commit_assign_*_fb`). -/

/-- An honest fallback commit vote exists only after its signer decided
and transported its complete decision vector
(Algorithm 5, line 37 (`line:fb-mvba-decide`) precedes Algorithm 5, line 41 (`line:fb-commitvote`)). -/
invariant [fbcommit_sig_backed]
  ∀ (R : node) (E : mentries), ¬ is_byz R ∧ msg_fbcommit_sig R E → local_mvba_complete R

/-- A correct validator's fallback commit vote signs certified entries: every
proposer's entry of the signed vector is in the auxiliary records. From its
own decision, whose every proposer entry its handlers recorded
(`mvba_recorded_entries`). -/
invariant [fbcommit_sig_entries]
  ∀ (R : node) (E : mentries) (J : node) (M : merkle_root),
    ¬ is_byz R ∧ msg_fbcommit_sig R E ∧ is_proposer J →
    (mval_pos E J M → aux_mvba_decided_pos J M) ∧ (mval_neg E J → aux_mvba_decided_neg J)

/-- A correct validator that has handled entry `J` of its decision has that
entry in the auxiliary records, for every representation it decided. Agreement
of the correct decisions (`mvba.agreement`) makes them one entry vector. -/
invariant [mvba_recorded_entries]
  ∀ (I J : node) (V : mvalue) (M : merkle_root),
    ¬ is_byz I ∧ local_mvba_recorded I J ∧ mvba.decided mvba_st I V →
    (mval_pos (mvba.entries V) J M → aux_mvba_decided_pos J M) ∧
    (mval_neg (mvba.entries V) J → aux_mvba_decided_neg J)

/-- A correct validator's handled entry is recorded (`on_mvba_decide_*` write
both rows). -/
invariant [local_mvba_recorded_backed]
  ∀ (I J : node),
    ¬ is_byz I ∧ local_mvba_recorded I J →
    (∃ M, aux_mvba_decided_pos J M) ∨ aux_mvba_decided_neg J

/-- A correct validator that has transported its decision has handled every
proposer's entry (`mvba_terminate`'s guard). -/
invariant [mvba_complete_recorded]
  ∀ (I J : node),
    ¬ is_byz I ∧ local_mvba_complete I ∧ is_proposer J → local_mvba_recorded I J

/-- A broadcast fallback commit certificate is valid: `2f+1` matching votes
(the guard of every action that sends one). -/
invariant [msg_fbcommitqc_backed]
  ∀ (C : node) (E : mentries), msg_fbcommitqc C E → fbcommitqc E

/-- A fallback commit certificate carries certified entries: its `2f+1`
votes contain a correct one (`supermajority_greater_than_third` +
`greater_than_third_one_honest`), whose entries are recorded
(`fbcommit_sig_entries`). -/
invariant [fbcommitqc_entries]
  ∀ (E : mentries) (J : node) (M : merkle_root),
    fbcommitqc E ∧ is_proposer J →
    (mval_pos E J M → aux_mvba_decided_pos J M) ∧ (mval_neg E J → aux_mvba_decided_neg J)

/-- An `fbCommitQC` certifies the MVBA decision vector: any `2f+1` commit
votes contain an honest one (`supermajority_greater_than_third` +
`greater_than_third_one_honest`), whose signer has transported its decision
(`fbcommit_sig_backed`). Bridges the certificate to the per-proposer
`commit_assign_*` preconditions via `mvba_complete_per_proposer`. -/
invariant [fbcommitqc_implies_mvba_complete]
  ∀ (E : mentries), fbcommitqc E → mvba_complete

/-- Every decided-positive root is proposer-signed: chunk validation for a
decided root. Derivable on the fly — a decision
is backed by a vote or fallback quorum whose honest member's entry pins
the proposer signature — but materialised so downstream VCs need not
re-derive it (the `msg_commitqc_*` / `aux_fb_neg_qv` pattern). -/
invariant [mvba_decided_pos_proposer_signed]
  ∀ (J : node) (M : merkle_root),
    aux_mvba_decided_pos J M → msg_proposer_signed J M

/- The model-check scaffolding (FinEncodableInjOnly / Enumeration deriving on
the action Label, EnumerableTransitionSystem assembly) is off: Chorus does
not use `#model_check`, and the derived FinEncodableInjOnly instances are
O(n^k) in the number of actions, beyond Lean's whnf heartbeat budget at this
action count. VC generation and the cross-file check/prove commands are
unaffected. -/
set_option veil.gen.modelCheckScaffolding false
-- Emit the per-action executable extraction (`Chorus.NextAct.extracted`, a
-- `Label → VeilMultiExecM` dispatcher) for the trace-conformance monitor. This
-- is O(n) in the actions and, unlike the scaffolding above, does NOT derive the
-- O(n^k) `Enumeration`/`FinEncodableInjOnly` label instances.
set_option veil.gen.executableActions true

/- The assembled `Invariants` conjunction is large; the
`LocalRProp` instance chain over it exceeds Lean's default instance-search
budgets, and without that instance every VC re-simplifies the full clump
(a large constant-factor slowdown of the sweep). Raise the budgets so the
pre-simplification succeeds. -/
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
-- The `simp` inside that instance's construction runs under the general
-- heartbeat budget, which the clump's size exceeds at the module default.
set_option maxHeartbeats 2000000

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

/- This file persists no per-VC theorems: holding every reconstructed
witness in one environment until olean serialization does not fit a
workstation's memory, so the per-action proof files under
[Chorus/Proofs](Chorus/Proofs) carry them. A VC in this development is
either registry data (claim-free by construction) or a kernel-checked
theorem in a [Chorus/Proofs](Chorus/Proofs) olean. -/

/- VC registry ([Dependencies.md](../docs/Dependencies.md) §1): `#gen_spec`
persists every VC's statement (as an `Expr`) plus its action/property/
style metadata into the olean, enabling the cross-file commands
(`#check_action Chorus <action>`, `#check_vc Chorus <action> <prop>`,
`#prove_action Chorus <action>`) in importing files. Solve-free, and the
eager statement elaboration it does here measures as ≈ free at this
file's scale. The registry is the proof-file family's entire statement
source: the `#prove_action`s under [Chorus/Proofs](Chorus/Proofs) re-create every VC
from it. -/
set_option veil.gen.vcRegistry true

/- Proof cache ([Dependencies.md](../docs/Dependencies.md) §2): consult the
content-addressed cache (`.lake/build/veilcache/`) for
the background `doesNotThrow` dischargers this file still runs, and store
their proofs. The proof-file family enables the cache itself and is the
main beneficiary: statement-unchanged rebuilds kernel-replay every cell
instead of re-solving. File-level so the dischargers capture it at
`#gen_spec`. -/
set_option veil.cache.proofs true

/- Solver configuration: Veil's defaults. In this file they govern only the
background `doesNotThrow` checks; the proof files set their own budget
(`veil_proof_options`, [ProofPrelude.lean](ProofPrelude.lean)). In-file
dischargers capture solver options at `#gen_spec`, so a `set_option` around
a later check command does not apply — see [CLAUDE.md](../CLAUDE.md),
"Build". -/

/-! ## Step property -/

/-- A committed validator's positive entries are frozen
(every `commit_assign_pos_*` requires `¬ local_committed i`). -/
step_property [committed_pos_frozen] {
  local_committed I ∧ local_committed_pos' I J M → local_committed_pos I J M }

#gen_spec

/-! ## Verification — in the proof-file family, not here

This is a **model file** of the verified-module file family
([Architecture.md](../docs/Architecture.md) §6): `#gen_spec` above elaborated the transition
system and persisted the VC registry — the model's entire proof
interface — and started only the (cheap) background `doesNotThrow`
checks. The invariant VCs are proven cross-file:

* one `#prove_action Chorus <action>` per action in
  [Chorus/Proofs](Chorus/Proofs) — every registered VC re-created
  from the registry statement (identical to what an in-file sweep would
  check, by construction), solved with proof reconstruction, persisted as
  a kernel-checked theorem, and assembled into the per-action
  preservation lemma `step_<action>`. The manual quorum-intersection
  cells (SMT's e-matching diverges on them) live in their actions' proof
  files as `#prove_vc … by <tactic>` cells the command consumes as-is
  after a statement check.
* [Chorus/Certify.lean](Chorus/Certify.lean) composes the
  preservation lemmas into `Chorus.invariants_of_reachable` + named
  `reachable_<property>` projections (`#gen_composition`), at the
  standard `propext`/`Classical.choice`/`Quot.sound` trust base — pinned
  there and consumed by [Chorus/Compose.lean](Chorus/Compose.lean) and
  [Chorus/Pigeonhole.lean](Chorus/Pigeonhole.lean).

Interactive spot checks: `#check_vc Chorus <action> <property>` (or
`#check_action Chorus <action>`) in any importing scratch file — one at a
time; multiple concurrent check commands contend for the same discharger
scheduler and slow each other down. -/

end Chorus
