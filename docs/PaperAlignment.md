# Paper alignment — the target revision, and the review against it

*The paper target and the review of the models against it.
[The guide's chapters 1](https://larskuhtz.github.io/cadence/guide/approach/) and [2](https://larskuhtz.github.io/cadence/guide/claims/) introduce the target and
summarise the findings; this page is the authority for the target (§0) and
for the findings for the paper's authors (§6).*

The models claim to verify the Cadence paper: which paper, and is it still
that paper? §0 names the target revision. §1 gives the mechanical check anyone can re-run against it. §§3–5 hold the
review of what the models rest on, item by item, and §5.10 what still
differs and why. §6 is the page of findings for the paper's authors. §8
states the design of the two largest changes the target asked of the
models. Earlier targets, and the sessions that moved the models onto this
one, are recorded in [History.md](History.md) § "Paper alignment before the
single target".

## 0. The target

The development targets **one revision of the paper repository: `48cac9a`**
(`48cac9a41efac2fb58f32f61ff21fd89db7c7d98`, branch `master`, committed
2026-10-02 00:40 UTC). The target is
the revision as a whole: the main body (`main.tex` and `src/*.tex`, the
paper whose arXiv versions are `2607.02275v1`/`v2`) and the internal
supplement (`supplementary-internal.tex` with
`src/supplementary-internal/`). Claims are stated about that revision, and
a protocol bug found here is a bug in that revision.

**Status: the development corresponds to paper revision `48cac9a` (main
body plus internal supplement).** Every item of the review (§§3–4) is
modelled, below the model's abstraction with its argument, or
documentation (§5.10). What the paper side should look at is §6. The tag
`paper-target/48cac9a` marks the commit from which this holds. The previous
target, arXiv v2 with the MVBA from the supplement at `eb1bb51`, is tagged
`paper-target/arxiv-v2`.

This section is the one home of the target revision. Model headers point
here and name no revision, so a later re-pin edits this section, the label
map, the README (its opening and § "The protocol paper"), the guide (the claims
box in [CadenceGuide.lean](guide/CadenceGuide.lean), and chapters 1 and 2) and
[Cadence.lean](../Cadence.lean), and no model file.

The target does not follow the paper repository's `master`. A later paper
commit is a new target only when a session moves it, by running §1 against
the new commit and modelling the difference, as the move to `48cac9a` did
([History.md](History.md) § "The realignment to `48cac9a` (R14–R17), and
its designs"). §9 lists the paper commits after the target that the next
cycle has to read.

## 1. The verified surface, and how to re-check it

The models cite the paper as a reader sees it in the target's rendered PDF,
with the LaTeX label in parentheses as the secondary key, and name the
supplement where it is the supplement: "Lemma 9
(`lemma:chorus-agreement`)", "Algorithm 5, line 7
(`line:fb-pathvote-guard`)", "Supplement, Lemma 13
(`lem:decision-propagation`)". The authority for every such reference is
the **label map** [paper-labels.tsv](paper-labels.tsv): each label of the
two documents at the target, with its rendered reference and page, read
by machine from the `.aux` files of a build of the target.

* **Main body:** Chorus's algorithms, Algorithm 2
  (`alg:proposer-dissemination`) to Algorithm 6 (`alg:da`); Module 3
  (`mod:mvba`); Appendix A (`section:formal_problem_definition`), Appendix B
  (`section:framework`) and Appendix C (`section:slot_agreement`); Appendix
  D (`section:conductor-formal`), which carries the Conductor's module,
  algorithm and proofs; and one overview, Section 5
  (`section:conductor-overview`).
* **Supplement:** Supplement, Section 1 (`sec:mvba-instantiation`), up to
  the end of Supplement, Section 1.3 (`subsec:mvba-correctness`), which is
  what [Mvba.lean](../Cadence/Mvba.lean) models. Two further supplement
  sections are cited as context, not as something a model rests on:
  Supplement, Section 7.4 (`sec:fallback-transition`) and Supplement,
  Section 10.5 (`sec:domain-separation`) (§5).
* **Not in the surface:** the supplement's practical Conductor
  (Supplement, Algorithm 2 (`alg:conductor-practical`) and its sections).
  The verified Conductor is the main body's Algorithm 7
  (`algorithm:conductor`) (§9).

**The check, in two halves.**

*References.* `scripts/paper-labels.sh` exports the target with `git
archive` (the paper checkout is only read), builds the main body and then
the supplement with `tectonic`, and writes the map. `scripts/paper-cites.sh`
then checks every citation in the repository's Lean comments and Markdown
against it: the label must be in the map, and the reference in front of it
must be the map's. At a new target, regenerating the map and running the
check re-numbers nothing by hand: every reference that moved is reported
with the reference it should now read. The two frozen records
([History.md](History.md), [AuditReport.md](AuditReport.md)) are not
checked; they cite the paper as it was when they were written. A few
labels are cited on purpose although the target does not have them, each
cited as removed or folded (`line:da-rebroadcast`, a v1 rule;
`line:mvba:td-decide`, `line:mvba:hp-pool` and `line:mvba:tfp-commit`,
removed at `eb1bb51`; `eq:predecessor-deadline`, folded at the target;
`lem:certified-prefix`, unlabelled at the target). The check lists them with
their reasons.

*Content.* A changed reference says only that something moved. Whether the
text changed is the source diff, in the paper repository:

```bash
git -C <paper-repo> fetch
git -C <paper-repo> diff 48cac9a <new> -- src/alg_*.tex src/p2_*.tex src/p1_informal.tex \
    src/supplementary-internal/alg_mvba.tex supplementary-internal.tex
```

then, for the supplement, compare its Section 1 alone (from
`\section{Concrete MVBA Instantiation}` to `\subsection{The First ``Dummy''
View}`), and each `lem:`/`thm:`/`cor:`/`rem:` statement text after
collapsing whitespace.

**Result at the target.** The map has every label of the two documents,
and every citation outside the two frozen records checks against it, in
label and in rendered reference: `scripts/paper-cites.sh` reports no
problem, and the docs build runs it. Regenerating the map from `48cac9a`
with `scripts/paper-labels.sh` reproduces the committed one byte for
byte.

Cautions for the content diff:

* `supplementary-internal-bkp.tex` is a stale snapshot that duplicates
  labels (P7). The map is built from `supplementary-internal.tex`, which
  does not include it.
* The MVBA algorithm source carries commented-out drafts with labels in
  them, so a label diff over raw text reports phantom additions and
  removals. Drop `%` lines first. The map is built from the rendered
  documents, so it has no such phantoms.
* An older deadline-MVBA draft of the Conductor is in the source tree but
  commented out of `main.tex`, so it is not part of the paper and its
  labels are not in the map. Its text (`p` as a fraction in `(0,1)`) is not
  the Conductor the paper proves.

## 2. One revision, two documents, two parts

The target revision contains two documents.

* **The main body** (`main.tex`): the paper. It specifies Chorus by its
  algorithm floats (Algorithm 2 (`alg:proposer-dissemination`), Algorithm 3 (`alg:voting`),
  Algorithm 4 (`alg:fast-path-certification`), Algorithm 5 (`alg:fallback`), Algorithm 6 (`alg:da`)), the MVBA as a
  module (Module 3 (`mod:mvba`), no algorithm), the Conductor (Algorithm 7 (`algorithm:conductor`))
  and the framework, and proves their properties.
* **The internal supplement** (`supplementary-internal.tex`). Its two parts
  play different roles:
  * **Part I, "Component Specifications"**, gives protocols for components
    the main body leaves abstract. These include the leader-based MVBA
    (Supplement, Section 1 (`sec:mvba-instantiation`)), which [Mvba.lean](../Cadence/Mvba.lean)
    models, a practical Conductor, chain-state certification, and an ACS
    built from the MVBA. Part I is specification. Where it touches the main
    body's protocol it changes it: the MVBA's `decide` also outputs a
    commit certificate on which Chorus finalizes (§5.7).
  * **Part II, "Implementation Notes and Guidance"**, says how a deployment
    departs from the pseudocode, and says so ("Unlike in the pseudocode",
    "Don't implement the post-MVBA commit round", in Supplement, Section 7 (`sec:implementationnotes`)). Part II describes the
    implementation, not the protocol whose claims the paper proves.

What the development verifies is therefore **the main body's protocol,
with the MVBA instantiated by Part I's MVBA and with the changes Part I
makes to how Chorus uses it**. Part II's departures are recorded (§5) but
not modelled, and where a model covers a Part II variant as well this
document says so. Part I components the main body does not use (the
practical Conductor, chain-state certification, the ACS instantiation) are
outside the verified surface. For the Conductor in particular, the
development verifies the main body's Algorithm 7 (`algorithm:conductor`); the practical
Conductor is outside the verified surface (§9).

**Access.** The main body is public up to v2. Auditors are assumed to have,
or to be able to obtain, the paper sources at the target, the supplement
included (§9).

## 3. Review: the main body, arXiv v2 (`3efdbfe`) → `48cac9a`

Files byte-identical at the target: `alg_fast`, `alg_voting`,
`p2_framework`, `p2_problem_definition`, `p2_conductor_alg`,
`p2_conductor_module`, `appendix_chorus`. Files changed only in
`\input{src/…}` paths: `p2_conductor_proofs`. Files changed in content:
`alg_proposer`, `alg_da`, `alg_fallback`, `p2_mvba`, `p2_chorus`,
`p1_informal`, plus macros in `defs` and paths in `main.tex` and
`introduction`.

The classes are: **(a)** below the model's abstraction; **(b)** to be
modelled; **(c)** a statement or contract change
([Interfaces.lean](../Cadence/Interfaces.lean)); **(d)** documentation only.

| # | Change (anchor) | Class | Why, or what |
|---|---|---|---|
| M1 | Domain tags on the proposer's two signatures, `⟨Prop, s, j, H(payload)⟩` and `⟨Root, s, j, ρ⟩` (Algorithm 2 (`alg:proposer-dissemination`), Algorithm 6 (`alg:da`), Algorithm 5, line 8 (`line:fb-cast-entry`)'s `σ_p`, the prose of Appendix C (`section:slot_agreement`)) | (a) | Each model relation is per message type (`msg_proposer_signed`, `msg_fb_pos_sig`, …), so a signature of one type cannot stand for another in the model. The tags are how an implementation gets that. §5.1 |
| M2 | Positional fragments: `Data(ρ)` holds `(r, d_r)`; `VerifyMerkle(ρ, r, H(r, d_r), π_r)`; `Decode` needs `f+1` distinct indices; Algorithm 6, line 24 (`line:da-reencode`) compares positional leaf hashes; `MerkleProof((…), r)` | (a) for the models | A chunk is `(assignee, proposer, root)` in the model, and `chunk_quorum` counts distinct assignees. The target's Algorithm 6 (`alg:da`) now says what the model assumed. §5.2 |
| M3 | The same, for `Primitives.ErasureCoding` | (b) | `Decode : List fragment → Option cipher` and `decode_sound` count list entries, v2's unindexed reading. At the target `Decode` takes indexed fragments with `f+1` distinct indices. A Lean statement change in an uninstantiated class; no VC moves. §5.2 |
| M4 | Slot checks: Algorithm 6 (`alg:da`) rejects a chunk whose header slot `s' ≠ s`; the decrypted proposal must be "for this slot"; `TIBE.Dec` checks slot and label | (a) | One Chorus model is one slot's instance. §5.3 |
| M5 | Per-slot dispatch: "every message and signed object of Chorus carries its slot … messages for other slots go to their own instances" (Appendix C.3 (`subsection:chorus-protocol-overview`)) | (d) | This is the glue's slot-indexed `sc_state s` ([Cadence.lean](../Cadence/Cadence.lean)). One sentence there. §5.3 |
| M6 | The TIBE interface paragraph: the four `TIBE.*` operations, the label `ℓ = j`, the context, the simulator's programming of `H_pad` (Appendix C.2 (`appendix:encryption`)) | (a) | Hiding is not a Veil property; `Primitives.ThresholdIBE` stays an uninstantiated class. |
| M7 | Algorithm 6 (`alg:da`)'s decryption guard counts shares "from at least `f+1` validators" | (a) | The model does not model decryption shares individually. |
| M8 | `propose` is an input "given only to proposers" (Algorithm 2 (`alg:proposer-dissemination`)) | (a) | The model's `propose` requires `is_proposer j`. |
| M9 | Module 3 (`mod:mvba`) Agreement: `entries(B) = entries(B')` (paper commit `d598c5a`) | (c) | Together with S6: the class's `value` becomes the decided representation and Agreement is stated over its entries. §5.5 |
| M10 | The MVBA summary of Appendix C.3 (`subsection:fallback_path`): "decide meta-blocks with the same entries" | (d) | Prose. |
| M11 | The informal part, Section 2 (`subsection:mcp-overview`) to Section 5 (`section:conductor-overview`): the fast vote is cast "on its entries"; the DA sentence; the Conductor's parameters and the ACS citation; slot independence | (d) | Prose, already true of the models (Algorithm 4 (`alg:fast-path-certification`) signs `entries(B)` at v2 too). |

Count: (a) 6, (b) 1, (c) 1, (d) 3.

## 4. Review: the supplement, `eb1bb51` → `48cac9a`, and the MVBA section in full

Two Overleaf commits (`d40bb61`, `48cac9a`) change the supplement. Three
further commits in the range touch only `STYLE.md` and the pre-commit
hook. The source of Supplement, Algorithm 1 (`alg:mvba`–`alg:mvba-cont3`) is byte-identical. In the MVBA
section, the changes are three edits to its prose and the removal of the
explicit `\qed`s. The Conductor sections change more.

| # | Change (anchor) | Class | Why, or what |
|---|---|---|---|
| S1 | `CE.verify`: a `FastQC` verifies over `⟨vote, E⟩`, a `FallbackQC` over `⟨fb, E⟩` (was: both over "the tagged entry `⟨s, j, ρ⟩`") (Supplement, Section 1.1 (`subsec:mvba-datatypes`)) | (a) | The model's `Valid` reads a vote quorum and a fallback quorum through separate relations. The edit corrects the text to what Algorithm 5 (`alg:fallback`) signs. |
| S2 | `EquivCert`'s leading `equiv` is "a structure discriminator, not a signature tag" | (d) | |
| S3 | `propose(B_i)` requires a valid meta-block, established by "the composing Chorus fallback transition" (Supplement, Section 1.2 (`subsec:mvba-protocol`)) | (d) | Already the contract's rely form: `Valid` inputs are an antecedent of `MVBATemporal.termination`. The cross-reference to Part II is a paper finding (§6, P8). |
| S4 | The retransmission interval `ρ` is renamed `ρ_mvba` | (d) | `Mvba.Schedule`'s field keeps its name; prose says which `ρ`. |
| S5 | Explicit `\qed`s removed | (d) | Editorial. |
| S6 | (in full) The MVBA's value is a meta-block *with its certificates*; `decide(x, CommitQC)` outputs one representation `x`; Agreement and Integrity are over `entries` ("Agreement and Integrity over entries") | (b) | The model's value is the bare entry vector, so a validator's decision carries no certificate kinds. The value becomes the representation (entries plus each positive entry's certificate kind). The representation omits negative entries' certificate kinds and the `FBCert`, an abstraction of class (a): no rule of either document reads them, and whether they verify is part of `Valid`. §5.5, §8.1 |
| S7 | (in full) The `Commit` availability condition `AvailReady_i(x)`: before its `Commit`, a validator waits for its share under every positive entry *of `x` certified by a `FallbackQC`*, and broadcasts it | (b) | The model's `avail_ready i e` is indexed by the entry vector. With S6 it is indexed by the representation. Safety is unaffected, because the relation is an environment relation. The liveness premise (F-avail) is restated over the representation. §5.5 |
| S8 | (in full) "Decision output and handoff": Chorus broadcasts the decided `CommitQC`; a correct validator that receives a valid one re-broadcasts it and **finalizes**; the MVBA's `Commit` round "also serves as the fallback commitment-certification round" | (b) + (c) | A second finalization route in Chorus, and the contract fields it needs. §5.7 |
| S9 | (in full) Everything else in Supplement, Section 1 (`sec:mvba-instantiation`): views, leader schedule, the lock, timeout certificates, `SyncView`, retention, the execution model, crash recovery, `Recover`, `Δ_R`, `Δ_sync` | (a) | Unchanged since `eb1bb51`. The model's coverage of each is recorded in the [Mvba.lean](../Cadence/Mvba.lean) header and in [History.md](History.md) § "The supplement at `eb1bb51`, reviewed against the pin `026dc8b`". |
| S10 | The practical Conductor (Part I): the window-admission lemma moved; the agreed-first-deadline argument rewritten; `eq:predecessor-deadline` folded into Supplement, Equation (1) (`eq:slot-deadline`); `offset(s)` defined; `2 ≤ p ≤ W−1` in the relation lemmas; the `H_ω` slack explained; Supplement, Equation (6) (`eq:ticket-freshness`); `ass:` → Supplement, Section 4.1 (`assum:recovery-data-availability`); `lem:certified-prefix` unlabelled | (a) | Outside the verified surface: the Conductor model follows Algorithm 7 (`algorithm:conductor`), which did not change. None of these labels is cited. §5.8, §9 |
| S11 | The set-agreement ACS as an MVBA instance: "the decided value is the candidate set `S`; `entries(S)` is the canonical ordered list …" | (a) | The Conductor consumes `ACSSafety` abstractly. §5.8 |
| S12 | The fast-path proposition of the Conductor's relation section: "This branch must close on the fast path" | (d) | |
| S13 | (in full, Part II) Supplement, Section 7.4 (`sec:fallback-transition`): entries evaluated continuously over all votes; `EquivCert` from two witness chunks; no re-encode-and-send | (d) | An implementation variant. The model follows Algorithm 5 (`alg:fallback`). §5.9, and §6 P3 |
| S14 | (in full, Part II) Supplement, Section 7 (`sec:implementationnotes`), "Don't implement the post-MVBA commit round" | (d) | Implementation guidance. After S8 the model has both routes, so implementation runs are among its runs for safety. §5.7 |
| S15 | (in full, Part II) Supplement, Section 10.5 (`sec:domain-separation`) | (d) | Cited at M1. |

Count: (a) 4, (b) 3 (one of them also (c)), (c) 1, (d) 8.

**Over both tables:** (a) 10, (b) 4, (c) 2, (d) 11. The (b) and (c)
items are in the models (§8 states the design of the two largest):

* **(b) M3.** `Primitives.ErasureCoding` decodes from indexed fragments
  with `f+1` distinct indices.
* **(b) S6, with F13.** The MVBA's value is the representation, an entry
  vector together with each positive entry's certificate kind
  (`MetaBlock`). Chorus's decision handlers check the certificate their
  own representation names, and `cast_fb_commit` waits exactly under the
  `FallbackQC` entries of its own `B′` (§8.1).
* **(b) S7.** `AvailReady` is indexed by the representation
  (`avail_ready i x`).
* **(b) S8.** Chorus finalizes on a received MVBA `CommitQC`
  (`commit_assign_pos_mvba` / `_neg_mvba`), as well as on the `fbCommitQC`
  (§8.2).
* **(c) M9/S6.** `MVBASafety` has the `entries` projection, and Agreement
  and Integrity are stated over it, in the supplement's forms.
* **(c) S8.** `MVBASafety` has the certificate-level facts the second
  route needs (`certified_unique`, `certified_decided`, `certified_valid`,
  `certified_available`, `certified_mono`), and `AvailReady` as an input
  the caller drives.

## 5. The items in detail

### 5.1 Signature domain tags

At the target every signature of the main body is over a tagged message:
`Prop` and `Root` for the proposer, `vote`, `fb`, `fallback`,
`FallbackCommit`, `Commit` for the votes and certificates, and `Prepare`,
`Commit`, `Timeout` and `Pre-Prepare` inside the MVBA.
Supplement, Section 10.5 (`sec:domain-separation`) makes it a rule: "the bytes signed for each message
type begin with a tag unique to that type". The models never had a way to
confuse two types. Each signed object is its own network relation, and a
guard reads the relation of the type it needs. The tags are the
implementation's side of that modelling choice. **Class (a)**, and
[ChorusDesign.md](ChorusDesign.md) §3.1's relation inventory cites
Supplement, Section 10.5 (`sec:domain-separation`) for it.

### 5.2 Positional fragments and Merkle hashing

At v2, Algorithm 2 (`alg:proposer-dissemination`) already bound each chunk to its
position (`MerkleRoot(H(1, d_1), …, H(n, d_n))`), but Algorithm 6 (`alg:da`) verified a
chunk with `VerifyMerkle(ρ, d_r, π_r)` and decoded from an unindexed set of
symbols. At the target Algorithm 6 (`alg:da`) checks the leaf at its index, stores
`(r, d_r)`, and decodes from `f+1` distinct indices. The re-encode check
of Algorithm 6, line 24 (`line:da-reencode`) compares positional leaf hashes.

Chorus identifies a chunk by `(assignee, proposer, root)`, and its
decode threshold `chunk_quorum` counts distinct assignees. So the model
already had the positional reading, and the target's Algorithm 6 (`alg:da`) now states
it. **Class (a)** for the models. `Primitives.MerkleTree` is already
positional (`VerifyMerkle : root → Nat → leaf → proof → Bool`).
`Primitives.ErasureCoding` is not. Its `decode_sound` holds for any list
of `f+1` entries, duplicates included. **Class (b)** for that class, done:
`Decode` is stated over indexed fragments with `f+1` distinct indices.

### 5.3 Slot checks and per-slot dispatch

The target adds two things. One is explicit slot checks: a chunk header for
another slot is rejected in Algorithm 6 (`alg:da`), and a decrypted proposal must be for
this slot. The other is a dispatch convention in Appendix C.3
(`subsection:chorus-protocol-overview`): a pattern
matches only objects of this slot, and other slots' messages go to their
own instances. One Chorus model is one slot's instance, so the checks are
vacuous in it. **Class (a).** The glue holds one abstract slot-consensus
state per slot (`sc_state s`) and drives each through its own contract
instance, which is the dispatch convention. **Class (d):** the
[Cadence.lean](../Cadence/Cadence.lean) model header cites the sentence.

### 5.4 Integrity over entries

The supplement (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Agreement and Integrity over entries") states Integrity as
"all decision outputs of a correct validator carry the same entry vector,
and redelivery of a decision with that entry vector … is permitted", and
says the main-body module "should be revised to these forms". `d598c5a`
revised Agreement only. At the target Module 3 (`mod:mvba`) still says "decides at most
once" (§6, P1).

For the model: `value` is the representation (§5.5), so "at most one
value" would say "at most one representation", which is stronger than the
supplement: it permits redelivery with a different representation after a
restart. **Class (c), done:** `MVBASafety.integrity` is stated over
`entries`, like Agreement (§8.1 (b)). The instance proves the strong form,
since the model has no crashes and a decided validator halts; how Chorus
treats a redelivered decision is P11 and §8.1 (d).

### 5.5 The meta-block, its certificates, and F13

**What the target says.** A meta-block carries, for each proposer, an
entry and a certificate: a `FastQC`, a `FallbackQC`, or an `EquivCert`. The
MVBA votes and decides over `entries(B)`. Agreement is over entries in the
main body (Module 3 (`mod:mvba`)) and in the supplement. Two correct validators may
therefore decide representations that differ in certificates. Concretely,
a root `ρ` of proposer `j` can be `FastQC`-certified in one validator's
`B′` and `FallbackQC`-certified in another's. Each validator then runs
Algorithm 5 (`alg:fallback`)'s decision handler on **its own `B′`**:
Algorithm 5, line 38 (`line:fb-commit-foreach`) waits for the assigned chunk "for each
`FallbackQC` in `B′`". The MVBA's own `Commit` does the same over the
accepted proposal `x_v` (`AvailReady_i(x)`). Both rules are well defined
per validator.

**What the model does.** The class's `value` is the representation:
each proposer's entry with, for a positive entry, its certificate kind
(`MetaBlock`, §8.1 (a)). Each correct validator decides its own, and
`cast_fb_commit i v` waits under exactly the `FallbackQC` entries of its own
decision `v` (§8.1 (d)), as Algorithm 5, line 38 (`line:fb-commit-foreach`)
does. **Classes (b) and (c).** Because only entries are agreed,
certificate kinds legitimately differ between validators, and a faithful
model has to carry each validator's own representation; a model that kept
the bare entry vector could not express the paper's wait for a root that
is `FastQC`-certified for one validator and `FallbackQC`-certified in
another's `B′` (finding F13, [Bounds.md](Bounds.md) §6.4.2; how it arose is
[History.md](History.md) § "The realignment to `48cac9a` (R14–R17), and its
designs"). On the paper side there is a related finding. The main body's
own proofs still argue from a common `B′` (§6, P2).

### 5.6 F14

`Owed (.redisseminate_chunk k i j m)` was `(CorrectChunkQuorum j m ∧ k has
decided) ∨ msg_fb_pos_sig k j m` ([Bounds.md](Bounds.md) §6.4.2). The left
disjunct owed chunks to other validators after a decision. At the target,
a decided validator broadcasts only *its own* chunk, and only under
`FallbackQC` entries of its `B′` (Algorithm 5, line 39 (`line:fb-commit-wait`), unchanged). A
correct MVBA `Commit` signer does the same under `AvailReady`. Neither
re-encodes for others. **Closed:** the chunk a correct validator owes is
the fallback-entry rule's re-dissemination (Algorithm 5, line 12
(`line:fb-redisseminate`)), and nothing else; since F15 it is sent inside
the signing step itself (§5.9).

### 5.7 How the fallback path ends

**What the target prescribes, with both documents read together:**

* **The main body** (Algorithm 5 (`alg:fallback`), unchanged since v2). On
  `MVBA[s].decide(B′)` a validator waits for its chunks under `B′`'s
  `FallbackQC` entries, casts a `FallbackCommitVote` over `entries(B′)`
  (Algorithm 5, line 41 (`line:fb-commitvote`)), and finalizes on a valid `fbCommitQC`
  (Algorithm 5, line 45 (`line:fb-recv-commit`), Algorithm 5, line 47 (`line:fb-finalize`)). Module 3 (`mod:mvba`)'s `decide` outputs
  the meta-block alone. Proposition 1 (`prop:agreement-entries`) and
  Proposition 5 (`prop:chorus-finalization-time`) argue over exactly two commitment proofs:
  the fast `commitQC` and the `fbCommitQC`.
* **Supplement Part I** (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"). `decide(x,
  CommitQC)` also outputs the MVBA's commit certificate, and Chorus
  broadcasts it. A correct validator that receives a valid one
  re-broadcasts it and finalizes. The MVBA accepts a transferred certificate
  of any view. "Thus the concrete MVBA's internal `Commit` round **also**
  serves as the fallback commitment-certification round." The word "also"
  adds a route and removes none. The MVBA's `Commit` carries the
  availability wait the fallback commit vote has (`AvailReady`, "inherited
  from Chorus's fallback-commit vote").
* **Supplement Part II** (Supplement, Section 7 (`sec:implementationnotes`), "Don't implement the post-MVBA
  commit round").
  The implementation drops `FallbackCommitVote`/`fbCommitQC` and keeps the
  `CommitQC` broadcast.

So the target **specifies a protocol with two fallback finalization
routes**: the main body's `fbCommitQC` route, and Part I's `CommitQC` route.
The implementation runs only the second. The main body proves agreement and
termination for the first route, but agreement of the second with the fast
path and with the first is argued only in one sentence of Part I (§6, P2).

**What the model does** (§8.2). It has both routes. The main
body's is the fallback commit round (`cast_fb_commit`, the collector's
`broadcast_fbcommitqc`, and `commit_assign_pos_fb` / `_neg_fb`). Part
I's is the handoff into the MVBA (`accept_mvba_commitqc`) together with the
`CommitQC` route: a correct validator broadcasts the `CommitQC` its
decision outputs (`send_mvba_cert`), and a validator that receives one
recovers a matching representation, checks the certificates it names, and
finalizes on the certified entries, re-broadcasting the certificate
(`commit_assign_pos_mvba` / `_neg_mvba`). So the model has every run
of the specified protocol, and every run of the Part II implementation as
far as safety goes, since that implementation is the specified protocol
without the `fbCommitQC` route.

**What safety rests on.** The route's agreement with the fast path is the
fast-path argument of Proposition 1 (`prop:agreement-entries`), applied
to the certificates of the recovered representation: a vote quorum
intersects the commit certificate's quorum, and an `FBCert` intersects it
in a validator that would have cast both votes. Its agreement with the
`fbCommitQC` route and with itself comes from the contract:
`certified_unique` (two certificates certify one entry vector) and
`certified_decided` (that is the vector every correct validator decides).
Data availability on the route needs no second bridge. The certificate check
that agreement needs already gives every recorded positive entry a vote
quorum or a `FallbackQC`, so its chunks are on the network
(`local_committed_pos_implies_decodable`). The contract's
`certified_available` is not used by the safety proofs. Read in Chorus's
vocabulary it is now a theorem, not a bridge, because `AvailReady` is a
Chorus-driven input whose meaning Chorus proves (`avail_ready_chunks`).
Liveness keeps the main body's route and the paper's bound. Proving a bound
through the `CommitQC` route as well is optional; it would record how the
implementation's latency compares.

### 5.8 Conductor and ACS

The main body's Conductor (Algorithm 7 (`algorithm:conductor`), Appendix D (`section:conductor-formal`)) has
no content change since v2. The models are unaffected: the
[Conductor.lean](../Cadence/Conductor.lean) model, `Windows.lean`'s median
lemma, and the `ACSSafety` contract. **No item.**

The supplement's Part I has a **practical Conductor** (Supplement, Algorithm 2 (`alg:conductor-practical`),
with its own relation to the paper's proofs) and an ACS instantiated as an
MVBA over candidate sets. Both are rewritten in places between `eb1bb51` and
the target (S10, S11). Neither is modelled, so the target's practical
Conductor is outside the verified surface. Its relation lemmas assume
`2 ≤ p ≤ W−1` where the main body allows `p ∈ {0, …, W−1}` (§6, P9).
The development verifies the main body's Conductor and not the practical
one (§9). The module interfaces the main-body Conductor uses gave P15–P17
([ConductorBounds.md](ConductorBounds.md)).

### 5.9 The `EquivCert` rule

Algorithm 5 (`alg:fallback`) builds an `EquivCert` only from two positive fallback entries
with distinct roots (Algorithm 5, line 29 (`line:fb-build-equiv`)). Algorithm 5, line 26 (`line:fb-build-entry`) comments
"one of the three cases always applies, by counting".
[FallbackReceipt.lean](../Cadence/FallbackReceipt.lean)'s `equiv_available`
and the exclusivity invariants mirror that cascade.

At the target, Supplement, Section 7.4 (`sec:fallback-transition`) (Part II) builds it from two
validated witness chunks instead. Both rules fire only on a proposer's own
signatures on distinct roots, so agreement and honest-proposer inclusion do
not depend on the choice. The rule matters only for a Byzantine proposer's
fate and for certifiability. Since Part II describes the implementation,
**the main body's rule is the target's protocol**, and the models follow it.
**Class (d).** The supplement still contradicts itself on the point: its
equivocation-evidence subsection says `EquivCert`s "are assembled only when
an MVBA input is built from two conflicting positive fallback entries"
(§6, P3).

Two other Part II departures bear on fairness justifications. A signer of
a positive fallback entry no longer re-encodes and sends each validator its
chunk; ChunkSync pulls instead. Chunks are also disseminated
unconditionally (Supplement, Section 8 (`sec:raptorcast`), "Disseminate
assigned chunks unconditionally"). The model follows the main body's
Algorithm 5, line 12 (`line:fb-redisseminate`), which holds at the target:
the positive fallback signer sends every validator its chunk inside its
signing step (`fb_sign_pos`, F15), and the broadcast of
Algorithm 5, line 39 (`line:fb-commit-wait`) needs no step of its own.
**Class (d).**

### 5.10 What remains different, and why

Every (b) and (c) item is modelled (the list at the end of §4 says
where). Every remaining difference between a model and the target is in
the table below: below the model's abstraction, with its argument, or a
finding of §6. None needs a model change. The differences the development
found and removed (F15 in Chorus's chunk sending; F25, the Conductor's
`p = 0`) are recorded with their findings ([Bounds.md](Bounds.md) §6.4.2,
[ConductorBounds.md](ConductorBounds.md) §7).

| Difference | Model | Why it is sound, or the finding |
|---|---|---|
| No signature tags, slot checks, TIBE operations or decryption shares (M1, M4, M6, M7) | Chorus | Each message type is its own relation; one model is one slot's instance; hiding is not a Veil property; shares are not modelled individually (§3). |
| The representation leaves out negative entries' certificate kinds and the `FBCert` | Chorus, Mvba | No rule of either document reads them, and whether they verify is part of `Valid` (§8.1 (a)). |
| `Recover` is a choice among valid representations | Mvba | It includes the supplement's choice, so the model has every run of the supplement and more; the liveness proofs use only what the supplement's `Recover` guarantees (§8.1 (c)). |
| No crashes and no persistence | Mvba, Chorus | With the state persisted before each send and reloaded atomically, a crash and restart is, to every other validator, a pause, and the model's runs pause. Termination under crashes (Supplement, Corollary 1 (`cor:mvba-recovery-termination`)) is not claimed. |
| `propose` enters the first view, not the view of the highest retained timeout certificate | Mvba | The faithful rule needs a negative read of the network, which the locality rules forbid ([Locality.md](Locality.md) R2). The model's rule adds runs, which is sound for safety, and no liveness argument uses them ([History.md](History.md) § "The supplement at `eb1bb51`, reviewed against the pin `026dc8b`", C7). |
| `SyncView` is its own step; the view timer is a phase marker; one action covers the timer and the `f+1` echo timeout | Mvba | The same reachable states in two steps, or a guard that only removes behaviours (the [Mvba.lean](../Cadence/Mvba.lean) header, "Abstractions"). |
| An `upon` handler runs once | Chorus | The target states no convention: P6. |
| A Byzantine step may read every validator's state, a correct one's included, where the target's adversary sees only what is sent to it | all | A stronger adversary: every claim holds against it, and no proof relies on what a Byzantine validator does not know ([Locality.md](Locality.md) §4.2). Whether the target's channels are private is not stated: P20. |
| A fallback entry may be cast for a proposer the validator already holds a FastQC for; the target casts them only "with `Ev(pid) = ⊥`" (Algorithm 5, line 8 (`line:fb-cast-entry`)) | Chorus | An over-approximation: the paper's runs, which cast fewer entries, are among the model's, so every safety claim covers them. The fallback vote (`cast_fallback_vote`) then carries an entry per proposer either way. |
| The FastQC aggregation counts `2f+1` vote signatures on the network, where the target forms a FastQC from the entries of received valid `Vote` messages or adopts one from a `FastBlock` or a fallback vote | Chorus | The adoption check is the signatures alone, and the adversary can send any FastQC the network's signatures form, so the target's runs are among the model's ([ChorusDesign.md](ChorusDesign.md) §3.5.3). The fallback entries count valid votes, as the target does: the positive one reads the senders' broadcast rows through the receiver's check, the negative one the validator's own receipts. |
| A prepare certificate is a row under its former's name (`msg_prepqc s`), where the supplement's travels only inside a `Timeout` or a TC | Mvba | The row is read only to check a certificate another message carries, never acted on by itself, so a receiver gains nothing by seeing it early ([MvbaPlan.md](MvbaPlan.md) §11.2). |
| A decision's output certificate is a row under the decider's name (`msg_commitqc i`), where the supplement's MVBA outputs it and Chorus broadcasts it | Mvba | The row is the output, checked only by the transfer input `decide` (the contract's `accept`), which only the caller invokes; the broadcast is Chorus's `send_mvba_cert` ([MvbaPlan.md](MvbaPlan.md) §11.2). |
| The glue's handlers are separate, later actions (`on_open`, `on_propose`, `on_finalize`, `record_skip`), where Algorithm 1 (`algorithm:cadence`) runs each atomically with its event | Cadence (glue) | An over-approximation: the paper's runs, in which each handler fires at once with its event, are among the model's, so every safety claim covers them. One statement follows the larger model: `[bounded_concurrency_interval]` states only that an active instance is opened and not completed, the direction Lemma 5 (`lemma:cadence-bounded-concurrency`) uses; the converse holds of the atomic runs only. |
| A redelivered decision casts the vote once, after the wait under the `B′` it is cast for | Chorus | The target does not say: P11. Safe under each reading (§8.1 (d)). |
| `AvailReady` is an input that Chorus drives; two liveness premises read the MVBA's accepted value | Chorus, Mvba | P12. |
| Termination's abandon condition and the timed claims' start condition are contract antecedents | Interfaces | P13. |
| Quiescence is a one-step statement from a reachable state | Interfaces | The paper's Quiescence is about executions; the contract states it per step, from every state an execution reaches ([CompositionContracts.md](CompositionContracts.md) §5). |
| Chorus's contract instance assumes the slot's proposer set is non-empty | Chorus | The target allows an empty set: P14. Used only for `admissible_exists`; proposers may all stay silent. |
| Both fallback finalization routes are modelled | Chorus | The target specifies both (§5.7); P2. |
| The `EquivCert` rule is Algorithm 5's, not Part II's | FallbackReceipt, Chorus | The main body's rule is the specified protocol (§5.9); P3. |
| An `open(s)` may fire later than the slot's starting time, and openings fire in slot order ("Timing relaxation" in the model's header) | Conductor | An over-approximation. The paper fires each opening at the later of its scheduling and its starting time (Algorithm 7, line 27 (`line:conductor-wait-for-open`)), and those openings come in slot order (Proposition 10 (`prop:fate-order`)), so the paper's runs are among the model's. The timed claims close the freedom with `open_slot`'s punctual row ([ConductorBounds.md](ConductorBounds.md) §6.4). |
| Window widths and slot spacing are uninterpreted: `win_last`, `win_boundary` and `start_time` are functions constrained only by order facts (`[shift_shape]`, `[start_time_strict]`) | Conductor | The paper's `+ (W − 1)`, `+ (p − 1)` and τ-spaced starting times (Appendix A.1 (`subsection:mcp-preliminaries`)) are one interpretation, so every paper run is a model run. The timed claims fix the arithmetic at the instance at `slot := ℕ` ([ConductorBounds.md](ConductorBounds.md) §6.3). |
| The fault bound is not a separate hypothesis of the Conductor's timed claims or of the composed Liveness and Censorship claims. The paper assumes `n = 3f + 1` with at most `f` Byzantine throughout (Section 2 (`subsection:mcp-overview`), the setting), and its Lemma 16 (`lemma:conductor-recovery`), Theorem 2 (`thm:conductor-correctness`), Lemma 2 (`lemma:cadence-liveness`) and Definition 3 (`def:censorship-resistance`) rest on it | Conductor, composed | The bound is supplied by the configuration rather than restated. The composed claims (`Composed.liveness`, `Composed.censorship`, `Composed.corollary4`, `Composed.boundedConcurrency`) are stated at the fault pattern `fmF n f hf is_byz hbyz`, whose `hbyz` and `hf` are at most `f` Byzantine of `n = 3f + 1`. The ACS's validity counts `2f + 1` distinct validators (C6). The Conductor's own claims (`Conductor.totality`, `Conductor.boundedness`, `Conductor.recovery`) are stated for any fault pattern, and use it only through the model's assumption `[acs_first_bracket]` on the first slot. The paper's lower median meets that assumption when at most the ACS's `fault_bound` validators are Byzantine (`Cadence.lowerMedian_first_assumptions`). With more, a theory using the median has no initial states, and the claims about it hold vacuously. At the paper's rule, then, the bound is used exactly where the paper uses it. They hold beyond the bound only for a first-slot rule that stays bracketed by correct proposals, which is a generalisation in the rule, not in the adversary the paper's protocol tolerates ([ConductorBounds.md](ConductorBounds.md) §10.4). |
| Part II's implementation variants; the practical Conductor | — | Outside the verified surface (§2, §7, §9). |

**No rule of the target is unmodellable.** Every protocol rule of the main
body and of Part I's MVBA can be modelled faithfully within the
locality rules ([Locality.md](Locality.md)), with the one exception in the table: the MVBA's
"enter the view of the highest retained timeout certificate", which the
model over-approximates.

## 6. Findings for the paper's authors

*This section is written to be sent to the authors as it stands.*

The Cadence protocol has a machine-checked formal development in Lean 4:
Chorus, the Conductor, the extreme-pipelining layer that composes them, the
supplement's leader-based MVBA and the fallback receipt rules are modelled,
and the paper's safety properties, its timed liveness lemmas, Corollary 4
(`cor:chorus-correctness-within-cadence`), Lemma 2
(`lemma:cadence-liveness`) and censorship resistance are proven, with every
proof checked by Lean's kernel. The ACS is taken as a module meeting
Module 4 (`mod:acs`). The development is against one revision of the paper
repository, **`48cac9a`** (2026-10-02): the main body, whose public
versions are `arXiv:2607.02275`, together with the internal supplement. The
findings concern statements, proofs, module interfaces and conventions, not
the protocol: the properties above are proven of the modelled protocol, and
where a finding names a condition the paper uses without stating it, they
are proven under that condition.

Each finding below quotes the paper and cites it as the rendered PDF shows
it, with the LaTeX label in parentheses; a citation that starts with
"Supplement" is to the supplement, every other one to the main body. Each
then says why it matters for a claim, and gives its status: whether it is
open on the paper side, and how the formal development handles it ("the
model" is the Lean development). The findings fall into three groups:

* **They affect the paper's correctness argument** — a proof step rests on
  something the cited statement or module does not provide, although the
  claim itself holds: P1, P2, P12, P13, P15, P16, P19.
* **They are open questions for the authors** — the paper leaves a rule, a
  convention or a choice unstated, and the model takes one reading: P3, P6,
  P9, P11, P14, P17, P20.
* **They are presentation, source hygiene or slack** — the claims and their
  proofs stand as written: P4, P7, P8, P10; and two places where the proof
  gives more than the statement says, both confirmed by proof in the model,
  P5 (a bound one `Δ` loose) and P18 (assumptions and a recovery time that
  are not tight).

| # | Finding | Group | Kind | Status |
|---|---|---|---|---|
| P1 | Module 3's Integrity was not revised with its Agreement | correctness argument | main body vs supplement | open; the model states Integrity over entries |
| P2 | Two proofs argue from a common `B′` and from two commitment proofs | correctness argument | proof gap | open; the model proves the claims without either |
| P3 | The supplement contradicts itself on `EquivCert` construction | open question | supplement, internal | open; the model follows the main body |
| P4 | A Part I obligation cites a Part II argument | presentation | supplement, internal | open; the model proves the main body's form |
| P5 | Lemma 11 claims `5Δ + ℓ_MVBA`; its proof gives `4Δ + ℓ_MVBA` | slack | statement vs proof | open; **confirmed by proof**: the model proves the paper's bound and the sharper one |
| P6 | No convention says how often an `upon` handler runs | open question | missing convention | open; the model reads "once" |
| P7 | A stale backup of the supplement is in the tree | hygiene | source hygiene | open |
| P8 | A stub still lists a backoff policy for the MVBA timeout | presentation | stale text | open; the model uses the fixed timeout |
| P9 | The practical Conductor assumes `2 ≤ p ≤ W−1` without saying so | open question | unstated assumption | open; outside the verified surface |
| P10 | arXiv v2's Algorithm 6 and Algorithm 2 hash chunks differently | presentation | fixed at `48cac9a` | for the next public version |
| P11 | What Chorus does with a redelivered MVBA decision is not stated | open question | missing rule | open; the model is safe under every reading |
| P12 | The MVBA's availability crosses Module 3's interface | correctness argument | module interface | open; the model states the dependency |
| P13 | Module 1 states Termination without the conditions Chorus needs | correctness argument | module interface | open; the model's contract carries the conditions as antecedents, and Chorus's instance proves the fields under them |
| P14 | A slot's proposer set may be empty | open question | unstated assumption | open; the model's instance assumes a non-empty proposer set |
| P15 | Module 2's Totality and Recovery rest on conditions the module does not state | correctness argument | module interface | open; the model's contract states them as antecedents, and the Conductor's Totality and Recovery are proven under them |
| P16 | Module 4's Validity lacks the per-validator bound the median argument needs | correctness argument | module interface, proof gap | open; the model's contract carries the bound, and the median argument is a theorem from it |
| P17 | The ACS the Conductor uses is unspecified | open question | missing instantiation | open; the model takes the ACS as a module meeting Module 4 |
| P18 | The recovery chain needs less than Algorithm 7's assumptions (1)–(3), and `𝓡 = 2Wτ` is not tight | slack | slack | open; **confirmed by proof**: the model proves Lemma 16, and the composed `𝓡`-Liveness, at `2Wτ` and at `(W + p − 1)τ` |
| P19 | A chunk that arrives exactly at the deadline is counted as on time without a stated rule | correctness argument | missing convention | open; the model states the inclusive reading as a premise and proves censorship resistance under it |
| P20 | Whether channels between correct validators are private is not stated | open question | unstated assumption | open; the model's claims hold without privacy |

P1–P4 are inconsistencies between the main body and the supplement, or
within the supplement. P12, P13, P15 and P16 are about module boundaries:
a claim takes from a module something the module's interface does not
state; §6.1 checks every module boundary the development's claims cross.

**P1. Module 3 (`mod:mvba`) Integrity was not revised with Agreement.**
* *Quote.* The supplement (Supplement, Section 1.2
  (`subsec:mvba-protocol`), "Agreement and Integrity over entries"):
  "*Integrity:* all decision outputs of a correct validator carry the same
  entry vector, and redelivery of a decision with that entry vector, for
  instance after a restart, is permitted … The abstract module in the main
  paper should be revised to these forms". Module 3 (`mod:mvba`):
  "*Integrity:* Every correct validator decides at most once." Agreement
  was revised (paper commit `d598c5a`); Integrity was not. Proposition 1
  (`prop:agreement-entries`) uses the old form: "A correct validator sends
  a single fallback commit vote — one per MVBA decision …, and the MVBA
  decides at most once by its integrity property".
* *Why it matters.* Under the supplement's Integrity a redelivered
  decision could trigger a second fallback commit vote, so the agreement
  argument of Proposition 1 (`prop:agreement-entries`) should rest on "all
  of a correct validator's fallback commit votes carry the same entries".
  That holds under the revised Integrity, and it is what the argument uses.
* *Status.* Open. The model states Integrity in the supplement's form
  (over entries), and nothing in it relies on "decides at most once".

**P2. The main body's proofs argue from a common `B′` and from two
commitment proofs.**
* *Quote.* Proposition 5 (`prop:chorus-finalization-time`): "by the MVBA's
  agreement and external validity, they all decide the same valid
  meta-block `B′`", then "each holds its assigned chunk for every positive
  `FallbackQC` of `B′`". Since `d598c5a`, Module 3 (`mod:mvba`)'s Agreement
  gives only `entries(B) = entries(B′)`. Proposition 1
  (`prop:agreement-entries`) enumerates two commitment proofs, the fast
  `commitQC` and the `fbCommitQC`, while the supplement adds a third: "A
  correct validator that receives a valid such certificate re-broadcasts it
  and finalizes the certified outcome" (Supplement, Section 1.2
  (`subsec:mvba-protocol`), "Decision output and handoff"). Its agreement
  with the other two is argued only as "a fallback decision agrees with a
  fast-path commitment whenever the two certify the same entry vector".
* *Why it matters.* Two correct validators may decide representations of
  one entry vector with different certificates, so a root can be
  `FastQC`-backed for one and `FallbackQC`-backed for the other. The
  conclusion of Proposition 5 (`prop:chorus-finalization-time`) still
  holds — a `FastQC` puts the chunks of `f+1` correct voters on the network,
  and under a `FallbackQC` the waiting validators re-broadcast — but the
  proof relies on an Agreement the module no longer states. The third
  commitment proof is a finalization route that the paper's agreement
  proof does not cover: the supplement's sentence is conditional, and it
  is not the fast-path argument the main body gives for its second case.
  Either the main body takes the route in (a certificate in Module 3
  (`mod:mvba`)'s `decide`, a finalize rule in Algorithm 5 (`alg:fallback`),
  a third case in Proposition 1 (`prop:agreement-entries`)), or Part I
  presents it as an implementation variant, as Part II does.
* *Status.* Open. The model has both routes (§5.7), assumes no common
  `B′`, and proves the third route's agreement by the main body's
  fast-path argument (vote-quorum intersection, and the `FBCert`/commit
  intersection). Termination is proven per validator, each on its own
  `B′`.

**P3. `EquivCert` construction, contradicted within the supplement.**
* *Quote.* Supplement, Section 7.4 (`sec:fallback-transition`) (item 2):
  "the two validated witness chunks themselves provide the conflicting
  proposer-signed roots required to construct an `EquivCert`; two
  conflicting positive fallback entries are not required." Supplement,
  Section 7 (`sec:implementationnotes`), "Record equivocation evidence even
  without slashing": "the `EquivCert` rarely becomes public, since
  `EquivCert`s are assembled only when an MVBA input is built from two
  conflicting positive fallback entries". The second matches the main body
  (Algorithm 5, line 29 (`line:fb-build-equiv`)).
* *Why it matters.* The two certifiability arguments are for two different
  rules. The main body's "one of the three cases always applies, by
  counting" (Algorithm 5, line 26 (`line:fb-build-entry`)) is argued over
  the first `2f+1` fallback votes; the supplement's replacement
  (Supplement, Section 7.4 (`sec:fallback-transition`),
  "Fallback-entry certifiability") needs entries evaluated continuously
  over all votes, and witness chunks. Agreement and honest-proposer
  inclusion do not depend on the choice; a Byzantine proposer's fate and
  certifiability do.
* *Status.* Open. The model follows the main body's rule, which is the
  specified protocol (§5.9).

**P4. Part I relies on a Part II argument.**
* *Quote.* Supplement, Section 1.2 (`subsec:mvba-protocol`) (Part I):
  "`propose(B_i)` requires `B_i` to be a valid meta-block for `s`; the
  composing Chorus fallback transition establishes that every correct
  validator eventually holds one (Supplement, Section 7.4
  (`sec:fallback-transition`))".
* *Why it matters.* The cited section is Part II's implementation variant
  (P3). For the main body's protocol the precondition is established by
  Algorithm 5 (`alg:fallback`)'s counting argument (Algorithm 5, line 26
  (`line:fb-build-entry`)).
* *Status.* Open. The model proves the main body's form
  (`Chorus.build_totality_of_reachable`).

**P5. Lemma 11 (`lemma:chorus-termination`) claims `5Δ + ℓ_MVBA` where its
proof gives `4Δ + ℓ_MVBA`.**
* *Quote.* Lemma 11 (`lemma:chorus-termination`): "satisfies
  `ℓ`-termination with `ℓ = 5Δ + ℓ_MVBA`". Its proof sets "`T₀ =
  max(t, GST) + 4Δ + ℓ_MVBA`" and adds totality's `Δ` in the first case.
* *Why it matters.* The inner split of Proposition 5
  (`prop:chorus-finalization-time`) at `T₀ − Δ` already handles early
  finalizers, so a single split gives `max(t, GST) + 4Δ + ℓ_MVBA`. A
  commented-out draft next to the lemma states that bound. The Conductor's
  timing (`Φ_oc = ℓ_chorus + d_tot`) inherits the extra `Δ`.
* *Status.* Open for the authors; the lemma is unchanged since arXiv v2.
  **Confirmed by proof.** The model proves the lemma as
  stated, `ℓ = 5Δ + ℓ_MVBA` plus the local steps (`Chorus.timed_termination`,
  `5Δ + ℓ_MVBA + 9δ`), and from the same premises the sharper bound
  `4Δ + ℓ_MVBA` plus local steps (`Chorus.timed_termination_tight`,
  `4Δ + ℓ_MVBA + 9δ`), which implies it; at `δ = 0` that is the
  `4Δ + ℓ_MVBA` of Lemma 11's proof. The single split is at the fallback
  commit votes' deadline `max(t, GST) + 3Δ + ℓ_MVBA` (plus `7δ`): an
  earlier finalizer gives everyone totality's `Δ`, and otherwise nobody
  has abandoned before the votes, so Proposition 5
  (`prop:chorus-finalization-time`)'s chain finalizes everyone by
  `T₀ = max(t, GST) + 4Δ + ℓ_MVBA`: the finalizer collects the fallback
  commit votes into its own certificate (Algorithm 5, lines 42–44
  (`line:fb-collect-commit`–`line:fb-commit-broadcast`)) and finalizes on
  its own broadcast (Algorithm 5, line 45 (`line:fb-recv-commit`)), a local
  step. No step of the proof uses the outer split. **Suggested correction:** state Lemma 11 with
  `ℓ = 4Δ + ℓ_MVBA`, the bound of the commented-out draft, and split once,
  at `T₀ − Δ`; `Φ_oc = ℓ_chorus + d_tot` then loses its extra `Δ`.

**P6. When does an `upon` handler run?**
* *Quote.* Algorithm 4, line 18 (`line:fast-formqc`) and Algorithm 4,
  line 31 (`line:fast-collect-commit`) are `upon` rules without "first
  time"; only the fast meta-block rule says "first time". Neither document
  states a convention for `upon`. The supplement's execution model covers
  MVBA handlers only, and the MVBA's own rules say it explicitly ("has not
  already formed …", "upon first collecting …").
* *Why it matters.* Liveness arguments and message counts depend on it.
  Read as "every time", a handler whose condition stays true re-sends its
  message indefinitely, and a fairness assumption is met by repeating it;
  read as "once", it is one step that a fair scheduler must take.
* *Status.* Open; Algorithm 4 (`alg:fast-path-certification`) is unchanged
  since arXiv v2. The model reads an `upon` handler as running once, when
  its condition becomes true ([Bounds.md](Bounds.md) §6.4.7). A one-line
  convention in the main body would settle it.

**P7. `supplementary-internal-bkp.tex` is still in the tree.**
* *Where.* The repository root, beside `supplementary-internal.tex`.
* *Why it matters.* It duplicates the supplement's labels, so any
  grep-based anchor audit finds two definitions of each.
* *Status.* Open. The development's label map is built from the rendered
  documents, which do not include it (§1).

**P8. A stub still lists a backoff policy for the MVBA view timeout.**
* *Quote.* Supplement, Section 10.1 (`sec:timing-constants`), a stub,
  lists among the constants to tabulate "the MVBA view timeout and its
  backoff policy". Supplement, Section 1.2 (`subsec:mvba-protocol`) fixes
  the timeout at `T := Δ_R + 4Δ + max{Δ, Δ_sync}`, and Supplement,
  Theorem 2 (`thm:termination`) counts with it.
* *Why it matters.* A backoff would contradict the fixed `ℓ_MVBA` of
  Supplement, Theorem 2 (`thm:termination`).
* *Status.* Open. The model uses the fixed `T`.

**P9. The practical Conductor's parameter range.**
* *Quote.* Supplement, Section 3 (`sec:practical-conductor`), "Relation to
  the Cadence Proofs": "Since `2 ≤ p ≤ W−1`, the threshold …", and later
  "The denominators are positive because `2 ≤ p ≤ W−1`". The main body's
  Conductor allows `p ∈ {0, …, W−1}` (Appendix D
  (`section:conductor-formal`), Algorithm 7 (`algorithm:conductor`)).
* *Why it matters.* The restriction is not stated as an assumption of the
  practical Conductor, so its relation to Algorithm 7
  (`algorithm:conductor`) covers only `p ≥ 2`, without saying so.
* *Status.* Open. Outside the verified surface: the development verifies
  Algorithm 7 (`algorithm:conductor`) (§9). One note: the main body's own
  recovery assumptions force `p ≥ 2` too. Assumption (4),
  Algorithm 7, line 10 (`line:assumption-four`), `d_tot + ℓ ≤ (p − 1)τ`, has
  a positive left side, because assumption (3) makes `ℓ > Δ`. So the wider
  range only matters for the safety properties
  ([ConductorBounds.md](ConductorBounds.md) §6.3).

**P10. arXiv v2's Algorithm 6 and Algorithm 2 hash chunks differently.**
* *Quote.* At `48cac9a` Algorithm 6 (`alg:da`) checks a chunk with
  `VerifyMerkle(ρ, r, H(r, d_r), π_r)`, the positional leaf hash Algorithm
  2 (`alg:proposer-dissemination`) commits to
  (`MerkleRoot(H(1, d_1), …, H(n, d_n))`). In arXiv v2, Algorithm 6
  (`alg:da`) checked `VerifyMerkle(ρ, d_r, π_r)`.
* *Why it matters.* In v2 the receiver's check did not match what the
  proposer commits to.
* *Status.* Fixed at `48cac9a`. Recorded because v2 is the public version:
  the next public version carries the fix. The model's chunks are
  positional, so it is unaffected (§5.2).

**P11. What Chorus does with a redelivered decision is not stated.**
* *Quote.* The supplement's Integrity permits redelivery: "all decision
  outputs of a correct validator carry the same entry vector, and
  redelivery of a decision with that entry vector, for instance after a
  restart, is permitted" (Supplement, Section 1.2 (`subsec:mvba-protocol`),
  "Agreement and Integrity over entries"). The consumer's rule is "upon
  `MVBA[s].decide(B′)`: for each `FallbackQC` in `B′` with a positive entry
  …: wait until …" (Algorithm 5, line 37 (`line:fb-mvba-decide`) to
  Algorithm 5, line 39 (`line:fb-commit-wait`)), written against Module 3
  (`mod:mvba`)'s "decides at most once".
* *Why it matters.* Two valid representations may carry different
  certificates, so a redelivered output can name a different `B′`. Neither
  document says whether a second output re-runs the handler, is ignored,
  or replaces the first `B′`. Agreement does not depend on the choice,
  since the vote's content is `entries(B′)`. The data the vote attests
  does: the chunks waited for are those of the `B′` the handler ran on.
* *Status.* Open. The model casts the vote once, after the wait under the
  `B′` it is cast for, which is safe under all three readings (§8.1 (d)).

**P12. The MVBA's availability couples it to the dissemination layer
through state Module 3 (`mod:mvba`) does not expose.**
* *Quote.* Module 3 (`mod:mvba`) has the interface `propose(B)`,
  `abandon()` and `decide(B)`, and no other observable. The supplement's
  MVBA waits, before its `Commit`, on `AvailReady_i(x)`, which holds "if,
  for every positive entry `⟨s, j, ρ⟩` of `x` that is certified by a
  `FallbackQC`, validator `p_i` holds its assigned availability share for
  `ρ`" (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Commit
  availability condition"), and its termination assumes: "whenever a
  correct validator `p_i` holds a valid meta-block `x`, all availability
  shares required for `AvailReady_i(x)` that it does not already hold
  become available to `p_i` within at most `Δ_sync`"
  ("Availability-synchronization assumption").
* *Why it matters.* `AvailReady` is a predicate on the dissemination
  layer's state, and the trigger of the assumption, "holds a valid
  meta-block `x`", is the MVBA's internal accepted value `x_v`. So the
  concrete MVBA's `ℓ_MVBA`-Termination is conditional on a service of the
  composing layer, owed on an event internal to the MVBA. Lemma 11
  (`lemma:chorus-termination`) uses `ℓ_MVBA`-Termination through Module 3
  (`mod:mvba`) as if the MVBA were self-contained. The composition is
  sound, since Chorus provides the service, but the module boundary the
  main body claims does not carry it. Either the module states the
  dependency (an `AvailReady` input and a "holds `x`" observable, or an
  `ℓ_MVBA` conditional on the caller's `Δ_sync`), or the supplement states
  its assumption over an event the module exposes.
* *Status.* Open. The model takes the first reading. `AvailReady` is an
  input of the MVBA contract that Chorus drives, with its chunk wait as
  the guard. The untimed availability premise is derived from Chorus's
  fairness. The two premises that need the trigger read the MVBA's
  internal accepted value at the system's instance, the honest form: the
  fairness owed to the availability report, and the validity bridge at a
  held value. The timed form of the assumption, (Δ-avail), is **derived**
  (`Chorus.availWithin_of_timedJustice`). It follows from
  Chorus's timed rows and the bridge under one property of the composed
  timing model, that the MVBA's availability window covers one Chorus
  network hop (`Δ ≤ Δ_sync`, `Chorus.Schedule.Δ_le_Δsync`). The proven
  timed claim at the system's MVBA (`Chorus.timed_termination_atMvba`)
  therefore assumes of the MVBA only its own scheduling. The coupling
  itself remains the finding: the module boundary of Module 3
  (`mod:mvba`) does not carry it, and the composition needs `Δ_sync` to
  cover a hop of the caller's. Safety does not depend on any of this.

**P13. Module 1 (`mod:slotconsensus`) states Termination without the
conditions Chorus needs.**
* *Quote.* Module 1 (`mod:slotconsensus`): "*Termination:* If every
  correct validator starts participating, then every correct validator
  eventually finalizes a proposal vector." Its block "Assumed behavior of
  correct validators", with "No correct validator starts participating
  before `s.deadline − Δ`" and "A correct validator stops participating
  only after having previously started participating and finalized a
  block", is commented out of the source. Lemma 11
  (`lemma:chorus-termination`) is conditional: "When run within Cadence,
  and provided participation is `Δ`-synchronized, Chorus … satisfies
  `ℓ`-termination", and its proof begins "Within Cadence a correct
  validator invokes `abandon()` only after it has finalized (Algorithm 1,
  line 23 (`line:abandon`))". Proposition 4 (`prop:chorus-totality`) uses
  the same fact.
* *Why it matters.* Chorus does not satisfy Module 1's Termination as
  stated: if a correct validator abandons before finalizing, the others
  can be left one correct vote short of every quorum. The composition is
  sound, because Algorithm 1 (`algorithm:cadence`) abandons only after
  finalizing and Module 2 (`mod:orchestrator_2`)'s Integrity says "no
  correct validator opens slot `s` before time `s.deadline − Δ`". But the
  module boundary does not carry the conditions, while Module 3
  (`mod:mvba`) ("no correct validator abandons before …") and Module 4
  (`mod:acs`) ("*Assumptions:* … *No premature abandonment*") state
  theirs. Restoring the block as Module 1's assumptions, in the form Module
  4 (`mod:acs`) uses, would settle it. Module 2 (`mod:orchestrator_2`)'s
  assumed-behaviour block (the open-to-complete delay `Φ_oc`) is commented
  out the same way.
* *Status.* Open. The model's contract states both conditions as
  antecedents, and Chorus's instance proves the fields under them.
  `SlotConsensusTemporal.termination` requires that no correct validator
  abandons before finalizing (C1), and `Chorus.chorusTemporal` proves it
  from `Chorus.termination`, which takes C1 as a caller's premise
  (`NoAbandonBeforeFinalizing`), met by the glue.
  `SlotConsensusWithTotality.bounded_termination` takes C1 and the start
  condition (C2), which the composition discharges from the
  Orchestrator's Integrity (`OrchestratorSafety.integrity_timing`), and
  `Chorus.chorusWithTotality` proves it, and `totality` under C1. No
  result proven here relies on Module 2 (`mod:orchestrator_2`)'s
  commented-out block.

**P14. A slot's proposer set may be empty.**
* *Quote.* Appendix A.1 (`subsection:mcp-preliminaries`): each slot has "a
  set of proposers `s.proposers`, which is a subset of the entire set of
  validators." Nothing requires the set to be non-empty.
* *Why it matters.* With no proposer, a meta-block has no entry, the only
  one a correct validator can build is the empty one, and it carries every
  certificate it needs vacuously. Whether the slot's MVBA can decide then
  rests on its validity predicate accepting the empty meta-block, which
  neither document says. A slot whose proposers all stay silent is a
  different case and is fine: every entry is then a proposer's explicit
  absence, certified by a negative FastQC or the `FBCert`.
* *Status.* Open, and harmless to every claim: `Chorus.chorusTemporal`
  takes "the slot's proposer set is non-empty" as a hypothesis, used only
  to show that its admissible runs exist ([Bounds.md](Bounds.md) §6.4.5).
  Stating `s.proposers ≠ ∅` in Appendix A.1
  (`subsection:mcp-preliminaries`) would settle it.

**P15. Module 2 (`mod:orchestrator_2`)'s Totality and Recovery rest on
conditions the module does not state.**
* *Quote.* Module 2 (`mod:orchestrator_2`): "*Totality:* If some correct
  validator opens any slot `s`, then every correct validator eventually
  opens `s`", and `𝓡`-Recovery, both stated unconditionally. Its "Assumed
  behavior of correct validators" block, "(ii) … if a correct validator
  opens `s` at time `t`, it completes `s` by time `max(t, GST) + Φ_oc`", is
  commented out of the source. Appendix D.2 (`subsection:conductor-proof`):
  "We therefore establish totality and recovery only for Conductor run
  *within Cadence*". Lemma 15 (`lemma:conductor-totality`) proves "more
  specifically" a `d_tot` bound, and Corollary 4
  (`cor:chorus-correctness-within-cadence`) consumes that bound.
* *Why it matters.* There are two gaps at the module boundary.
  * The Conductor does not satisfy Module 2 as stated: a caller that never
    completes a slot leaves it in window 1. P13 found the same pattern for
    Module 1 (`mod:slotconsensus`).
  * Restoring the commented-out block would not repair it. The proofs use
    two *conditional* facts about the caller: completions of a slot are
    `d_tot`-total if its openings are synchronized, and all complete within
    `ℓ_chorus` if all open. An unconditional `Φ_oc` bound is itself a
    consequence of the Conductor's totality (Proposition 14
    (`prop:conductor-open-to-complete`)), so stating it as a module
    assumption would assume part of the conclusion.

  The `d_tot` form Corollary 4 needs is a property of the Conductor, not of
  Module 2, as `d_tot`-totality is of Chorus and not of Module 1.
* *Status.* Open for the paper. The contract states the two conditional
  facts as antecedents of its Totality and Recovery
  (`OrchestratorSafety.CallerTotality`, `CallerTermination`), and a
  Conductor-specific level, `OrchestratorWithTotality`, carries the `d_tot`
  form ([Interfaces.lean](../Cadence/Interfaces.lean);
  [ConductorBounds.md](ConductorBounds.md) §2.3, F16, F17). Under these
  two antecedents the Conductor's Totality and Recovery are proven
  (`Conductor.totality`, `Conductor.recovery`), so the two conditional
  facts suffice. The full contract instance carries them as the fields'
  antecedents (`Conductor.conductorFull`).

**P16. Module 4 (`mod:acs`)'s Validity lacks the per-validator bound the
median argument needs.**
* *Quote.* Module 4 (`mod:acs`): "*Validity:* If a correct validator decides
  a set `set`, then `|set| ≥ 2f + 1`, and for every validator-slot pair
  `(p_i, s_i) ∈ set` such that `p_i` is a correct validator, `p_i` proposed
  slot `s_i`." The interface's output is `Set(Validator × Slot)`. Appendix
  D.2 (`subsection:conductor-proof`), before Proposition 7
  (`prop:acs-nonoverlap`): "the slot number of `s` lies between the minimum
  and maximum slot numbers proposed by correct validators (since the decided
  vector contains at least `f + 1` pairs contributed by correct
  validators)".
* *Why it matters.* Nothing in the module stops a Byzantine validator from
  contributing several pairs. A set of `2f + 1` pairs, all from one Byzantine
  validator, meets Validity as stated, and its median is the adversary's
  choice. The next window could then overlap the previous one, and the
  proofs of Integrity (Lemma 12 (`lemma:conductor-integrity`)) and
  Monotonicity (Lemma 13 (`lemma:conductor-monotonicity`)), through
  Proposition 7 (`prop:acs-nonoverlap`) and Proposition 8
  (`prop:acs-fate-range`), would not go through. The proof's word "vector"
  shows the intended reading. Any ACS that collects one signed proposal per
  validator meets it. Stating "at most one pair per validator" in Validity
  would settle it.
* *Status.* Open for the paper. The development's contract carries the
  bound (C6, [ConductorBounds.md](ConductorBounds.md) §3.4, F18): `ACSSafety.decided_unique` ("a correct decider's set holds at most
  one slot per validator"), and `ACSTemporal.validity_quantitative` counts
  `2f + 1` distinct validators. The median bracket is a stated bridge, the
  model assumption `[acs_first_bracket]` on the first slot each validator
  computes from its own decided set, and that the lower median
  meets it is a theorem from the contract and the system's fault bound
  (`Cadence.lowerMedian_first_assumptions`, through
  `Cadence.acs_median_bracket`, [AcsMedian.lean](../Cadence/AcsMedian.lean)). Without the bound that
  theorem is false. The assumed ACS is therefore one that meets Module 4
  with this sentence added.

**P17. The ACS the Conductor uses is unspecified.**
* *Quote.* The supplement's Section 2, "Concrete Instantiation of ACS", has
  no text at `48cac9a`, only two margin notes: the MVBA "seems like a good
  candidate", and a multi-shot consensus is an alternative. Algorithm 7
  (`algorithm:conductor`)'s "Uses" line names "ACS (`ℓ`-termination)"
  (Algorithm 7, line 12 (`line:acs-instances`)), while the proofs also use
  its `Δ`-Totality (Proposition 13 (`prop:window-synchronization`),
  Proposition 17 (`prop:window-progression`)).
* *Why it matters.* The Conductor's `𝓡 = 2Wτ` depends on the ACS's `ℓ`
  through assumptions (1), (3) and (4). Neither document says which ACS
  achieves the module, or with which `ℓ`. As with the MVBA before the
  supplement's instantiation, the module is an idealisation with a
  deterministic bound ([Bounds.md](Bounds.md) §1).
* *Status.* Open. The model takes the ACS as an assumed module: the timed
  claims are relative to an instance of its contract, and a plain-Lean ideal
  ACS shows that the premises are consistent
  ([ConductorBounds.md](ConductorBounds.md) §3).

**P18. The recovery chain needs less than Algorithm 7's assumptions (1)–(3),
and `𝓡 = 2Wτ` is not tight.**
* *Quote.* Algorithm 7 (`algorithm:conductor`)'s parameter assumptions
  (Algorithm 7, lines 7–10 (`line:assumption-one`–`line:assumption-four`)):
  "(1) `(p − 1)τ + Φ_oc + ℓ ≤ Wτ`, (2) `(p − 1)τ + Φ_oc ≤ (W − 1)τ`,
  (3) `Δ < ℓ`, (4) `d_tot + ℓ ≤ (p − 1)τ`", with
  `Φ_oc = ℓ_chorus + d_tot`. Theorem 2 (`thm:conductor-correctness`):
  "`𝓡 = 2Wτ`".
* *Why it matters.* The model proves Lemma 16 (`lemma:conductor-recovery`)
  through Propositions 14–19 as the paper states them, and the proof shows
  four kinds of slack:
  * **(1) and (2) hold with `ℓ_chorus` in place of `Φ_oc`.** Proposition 17
    (`prop:window-progression`) and Proposition 19
    (`prop:first-post-gst-window-time`) apply Proposition 14
    (`prop:conductor-open-to-complete`), whose `d_tot` covers one
    validator's opening reaching the others. In both places every correct
    validator has already opened the slots, by `T_p(ω)` and by
    `GST + (p − 1)τ` respectively, so Chorus's `ℓ_chorus`-termination
    (Lemma 11 (`lemma:chorus-termination`)) applies at that time directly.
  * **(2) is needed only by Proposition 19.** Proposition 17, point 1,
    needs the proposal trigger only by `T₁(ω + 1)`, not by
    `slot(ω, W).deadline − Δ`: the `s*` rule then still picks
    `slot(ω, W) + 1`. (1) already implies that.
  * **(3) is needed only for `ℓ > 0`.** It enters Proposition 16
    (`prop:window-open-time`) and Proposition 17, point 2, through a case
    split on an early correct entry or decision. The ACS's
    `ℓ`-termination needs only that every correct validator proposes, and
    both proofs show that, so the other case covers both.
  * **`𝓡 = (W + p − 1)τ` suffices.** The smallest post-GST window `ω*`
    is itself entered by `T_p(ω*)` (Proposition 18's base case), so its
    slots from the `p`-th on are opened at their starting times as well.
    Those start by `GST + (W + p − 1)τ`, using Proposition 19. Since
    `p < W`, this is at most `2Wτ`.

  With P5's `ℓ_chorus = 4Δ + ℓ_MVBA` as well, (1) and (2) would read with
  `4Δ + ℓ_MVBA` where the paper has `Φ_oc = 6Δ + ℓ_MVBA`. Smaller windows
  and an earlier recovery then satisfy the assumptions.
* *Status.* Open for the authors. **Confirmed by proof:**
  `Conductor.recovery` proves Lemma 16 at `2Wτ` from (1)–(4)
  as stated, and `Conductor.recovery_sharp` proves it at `(W + p − 1)τ`
  from the same premises. Both use (1) and (2) only in their `ℓ_chorus`
  form and (3) only as `ℓ > 0`
  ([ConductorBounds.md](ConductorBounds.md) §9). **Suggested
  correction:** state (1) and (2) with `ℓ_chorus` and (3) as `ℓ > 0`, and
  `𝓡 = (W + p − 1)τ`, or note that they are sufficient, not tight. The
  sharper value carries through the composition: the composed system's
  `𝓡`-Liveness (Lemma 2 (`lemma:cadence-liveness`)) is proven at
  `(W + p − 1)τ` too (`Composed.liveness_sharp`).

**P19. A chunk that arrives exactly at the deadline is counted as on time
without a stated rule.**
* *Quote.* Proposition 3 (`prop:honest-positive-entry`): "Since
  `s.deadline − Δ ≥ GST` and `p_j` disseminates at the slot's starting time,
  every correct validator receives and validates its assigned chunk under
  `root_P` by the deadline [...] setting its entry for `p_j` to the positive
  entry". The proof of censorship resistance for Algorithm 1
  (`algorithm:cadence`), in Appendix B.3 (`subsection:correctness_cadence`),
  has the proposer propose "at that same time", the slot's starting time.
* *Why it matters.* A message sent at `D − Δ ≥ GST` arrives by `D`, so in
  the worst case exactly at `D`, the instant at which a correct validator's
  deadline handler fires and it votes with the entries it holds
  (Algorithm 3 (`alg:voting`)). The proposition needs the chunk to be
  recorded before that handler runs. With local computation instantaneous,
  both events happen at `D`, and no rule says which runs first. Under the
  other order the validator votes without the entry, and Proposition 3's
  conclusion fails for that run. Censorship resistance at any `c` rests on
  it, since the proposal is always made exactly `Δ` before the deadline.
* *Status.* Open for the authors. The model's
  punctual deadline marker may fire at clock `D`, so the existing
  milestone needs the recording strictly before `D`
  (`Chorus.within_proposal_recorded`). The model states the paper's
  inclusive reading as a premise of Chorus's timing model, (P-incl)
  `DeadlineInclusive`, and proves censorship
  resistance under it (`Composed.censorship`;
  [ConductorBounds.md](ConductorBounds.md) F31). **Suggested
  correction:** state the convention, e.g. that messages delivered at the
  deadline are processed before the deadline handler; or have the
  proposer disseminate before the starting time.

**P20. Whether channels between correct validators are private is not
stated.**
* *Quote.* Appendix A (`section:formal_problem_definition`), on hiding:
  "The environment also plays the role of the adversary: in the real world
  it directly controls the faulty validators [...] We assume *static*
  corruption". No rule says what the adversary sees of the messages
  between correct validators; a commented-out note in the same section
  asks for "some kind of 'secure channel' built in to the model".
* *Why it matters.* An adversary that reads the traffic between correct
  validators, or their state, is stronger than one that sees only what is
  sent to it. A proof that relied on the weaker adversary would not hold
  of the stronger one, and a reader cannot tell which one the paper
  means. The safety and liveness arguments appear not to use privacy, and
  hiding rests on encryption rather than on the channel, but neither is
  said.
* *Status.* Open for the authors. The model lets a Byzantine validator
  read every validator's state and every message
  ([Locality.md](Locality.md) §4.2), and its safety and liveness claims
  hold against that adversary, so they need no privacy. Hiding is not a
  property of the models (§3). **Suggested correction:** state the
  channel assumption, e.g. authenticated channels with no privacy, and
  note where hiding relies on encryption alone.

### 6.1 The interface check

Every claimed result takes facts from module contracts. This table lists
each fact that is not plainly a property of the paper's module, what uses
it, and whether the target's module interface provides it. A "no" is a
finding, unless the fact is the development's own stated bridge.

| Fact the development uses | Used by | Provided by the target's module? | Finding |
|---|---|---|---|
| The MVBA's commit certificate: `certifies`, `decidedCert`, `decided_certified`, `decidedCert_certifies`, `accept` and its effect, `certified_mono`, `certified_unique`, `certified_decided`, `certified_valid` | the `CommitQC` finalization route (Chorus safety); the decision's broadcast (`send_mvba_cert`) and the handoff (`Chorus.termination`) | not by Module 3 (`mod:mvba`), whose `decide` outputs the meta-block alone; by the supplement's Part I ("`decide(x, CommitQC)`", a transferable certificate the MVBA accepts from any view) | P2 |
| `availReady`, the input `markAvail`, their frames; `certified_available` | Chorus's availability report; the MVBA's termination | no: the supplement states `AvailReady` over the dissemination layer's state | P12 |
| `availOwed` and the validity bridge at a held value, both reading the MVBA's accepted value | `Chorus.termination` (premises `FJustice`, `ValidBridge`) | no: neither document exposes `x_v` | P12 |
| (Δ-avail), the MVBA's timing premise on its caller | the timed Chorus claim at the system's MVBA (`Chorus.timed_termination_atMvba`), derived there from Chorus's rows (`availWithin_of_timedJustice`) under `Δ ≤ Δ_sync` | no: the supplement's assumption is triggered by `x_v` | P12 |
| No correct validator abandons before finalizing | `Chorus.termination`, `Chorus.totality` | not by Module 1 (`mod:slotconsensus`) (commented out); the composition meets it (Algorithm 1, line 23 (`line:abandon`)), as the glue's invariant `[abandoned_after_finalize]` over the instance's own record | P13 |
| No correct validator starts before `s.deadline − Δ` | the timed Chorus claims and `SlotConsensusWithTotality.bounded_termination` | not by Module 1 (`mod:slotconsensus`) (commented out); by Module 2 (`mod:orchestrator_2`)'s Integrity, through the glue's invariant `[participating_opened]` | P13 |
| A slot has at least one proposer | `admissible_exists` of Chorus's contract instance | no: `s.proposers` is any subset of the validators | P14 |
| The validity bridge: a valid meta-block's certificates verify against the network, and genuine certificates make it valid | Chorus safety at the decision handlers and the `CommitQC` route; `Chorus.termination` | `Valid` is "publicly verifiable" in both documents; the bridge says what that means for a network of relations | none: Chorus's one stated bridge ([Architecture.md](Architecture.md) §4) |
| The MVBA's abandon antecedent and Quiescence | `Chorus.termination` (through `Mvba.termination`) | yes, Module 3 (`mod:mvba`) | — |
| ACS Agreement, Validity (genuine pairs), Integrity | `Conductor ⊨ OrchestratorSafety` | yes, Module 4 (`mod:acs`) | — |
| At most `f` Byzantine-attributed pairs in a decided ACS set | that the lower median meets the model's first-slot assumption `[acs_first_bracket]` (`Cadence.lowerMedian_first_assumptions`, through `Cadence.acs_median_bracket`) | no: Module 4 (`mod:acs`) bounds the set's size, not the pairs per validator; the contract adds the bound (`decided_unique`) | P16 |
| The Orchestrator's `d_tot`-Totality of openings | Corollary 4 (`cor:chorus-correctness-within-cadence`); the Conductor's recovery (`Conductor.recovery`, through `Conductor.open_sync`) | not by Module 2 (`mod:orchestrator_2`), whose Totality is eventual; Lemma 15 (`lemma:conductor-totality`) proves it of the Conductor within Cadence, as does `Conductor.totality` | P15 |
| The conditional completion guarantees of the Orchestrator's caller | the Conductor's Totality (`Conductor.totality`, through (R-tot)) and Recovery (`Conductor.recovery`, through (R-tot) and (R-term)) | no: Module 2 (`mod:orchestrator_2`)'s assumed-behaviour block is commented out, and is unconditional | P15 |
| Unbounded starting times: whatever the time, some slot has not started (`StartsUnbounded`) | `Conductor.totality`, for the ACS proposal's `s*`, and `Conductor.recovery`, which also needs a window of the chain after GST | yes, implicitly: the slots are infinitely many and τ-spaced on the real line (Appendix A.1 (`subsection:mcp-preliminaries`)), and Algorithm 7, line 39 (`line:sstar-compute`)'s `s*` presumes one | none: the development's own statement first lacked it (F28) |
| Every window has a successor (`WindowsUnbounded`) | `Conductor.recovery`: the chain of windows Propositions 15–19 run along | yes: the windows are the numbers `ω ∈ ℕ≥1`, one ACS instance for each `ω ≥ 2` (Algorithm 7, line 12 (`line:acs-instances`)) | none: the development's own statement first lacked it (F30) |
| The ACS accepts its two inputs (`ACSTemporal.propose_enabled`, `abandon_enabled`) | the Conductor's timed claims, through its handlers' rows (`Conductor.totality`) | yes, implicitly: Module 4 (`mod:acs`)'s interface makes `propose(s)` and `abandon()` inputs, which the caller invokes, and the module formalism has no refusal; the proofs (Proposition 15 (`prop:enters-every-window`): "`p_j` proposes to `ACS[ω]`") rely on exactly that | none: the module convention states it, the contract spells it out (F26) |
| Open-prefix agreement of the Orchestrator | the glue's safety | derived: the safety residue of Module 2 (`mod:orchestrator_2`)'s Totality and Monotonicity | — |
| "A correct validator decides only after proposing", for the MVBA | nothing | not by Module 3 (`mod:mvba`); Module 4 (`mod:acs`)'s Integrity states it for the ACS | none: no claim uses it |

## 7. Implementation variants the models cover

For reference, the Part II departures and how the models stand to them:

* the post-MVBA commit round dropped: covered for safety, because the model
  has both routes (§5.7);
* the finalize wait moved outside consensus (recovery asynchronous): the
  model's finalization is the commit, and `local_committed_pos_implies_decodable`
  is the availability fact recovery rests on;
* decryption shares travelling separately from votes: below the model,
  which does not model shares individually;
* the fallback transition under separate chunk dissemination (§5.9): not
  covered, because the model follows the main body's rule;
* MVBA entry postponed until the slot's ticket is held: not covered.
  "Ticket" exists only in the supplement.

## 8. What the realignment built

The (b) and (c) items of §§3–4 are in the models (the list at the end of
§4). This section states the design of the two that changed the most, the
meta-block representation (§8.1) and the `CommitQC` route (§8.2), with the
reason for each choice. The session records of the realignment (R14–R17),
the designs as they were written before each model edit, and the pin
arithmetic of each build are [History.md](History.md) § "The realignment
to `48cac9a` (R14–R17), and its designs".

### 8.1 The meta-block representation

**(a) The value.** The MVBA's value is the target's meta-block
representation: an entry vector together with the certificate kind of each
positive entry. The MVBA "votes and decides over `entries(B)`"
(Supplement, Section 1.1 (`subsec:mvba-datatypes`)), and two valid
meta-blocks "may carry different certificates for the same verdicts"
(Supplement, Section 1.2 (`subsec:mvba-protocol`), "Agreement and Integrity
over entries"). At the system's instantiation the value is
`MetaBlock node merkle_root`, each proposer's optional root with its
`CertKind` (`fastQC` or `fallbackQC`), and `MetaBlock.entries` is
`entries(B)` ([Interfaces.lean](../Cadence/Interfaces.lean), beside the
MVBA classes). The representation leaves out what no rule of either
document reads: the certificate kinds of negative entries, and the
`FBCert`. `AvailReady` (Supplement, Algorithm 1, line 90
(`line:mvba:commit-send`)) and the fallback commit wait (Algorithm 5,
line 38 (`line:fb-commit-foreach`)) read only the positive `FallbackQC`
entries. Whether the left-out certificates verify is part of `Valid`, a
predicate on the representation.

**(b) The contract.** `MVBASafety` has the projection
`entries : value → entryvec`. Agreement and Integrity are the supplement's
sentences, over entries: "if correct validators decide `x` and `x′`, then
`entries(x) = entries(x′)`", and "all decision outputs of a correct
validator carry the same entry vector". Redelivery with the same entry
vector is permitted, which is why Integrity is not "at most one
representation" (§5.4). The commit certificate is over entries, "an
aggregate of `2f+1` Commit signatures over `entries(x)`" (Supplement,
Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"):
`certifies` takes an entry vector, a decision exposes a certificate for its
entries, and accepting a certificate decides some representation with
those entries, the supplement's `Recover(e)`. The certificate-level fields
(`certified_unique`, `certified_decided`, `certified_valid`,
`certified_available`, `certified_mono`) say that a certified entry vector
is the only one, is what every correct validator decides, has a valid
representation, was signed by correct validators that each held their
availability share, and stays certified. The availability field counts a
supermajority, so the class takes the system's quorum family as a
parameter. Every field is first-order; those with an `∃` in their
conclusion that no Chorus cell reads are withheld from the solver
(`veil_smt_ignore`) and stay declared axioms of the class, proven by
`Mvba.mvbaSafety`.

**(c) The MVBA model.** [Mvba.lean](../Cadence/Mvba.lean) has two sorts:
`value`, the representation, and `evec`, the entry vector, joined by the
immutable `ent`, which the instance exports as `entries`. Every relation of
the supplement that carries a meta-block carries the representation
(`input`, `msg_preprepare`, `accepted`, `decided`, `avail_ready`, `valid`);
every signed vote and certificate carries the entry vector. This is the
split of Supplement, Algorithm 1 (`alg:mvba`–`alg:mvba-cont3`).
**`Recover` is a choice among valid representations**: `leader_repropose`
re-proposes any valid `x` whose entries are the lock, and
`form_own_commitqc` and `decide` decide any valid `x` whose entries the
certificate certifies. The supplement's `Decide` takes `x_v` when its
entries match and `Recover(e)` otherwise, and `Recover(e)` returns "a valid
meta-block with entry vector `e`" from any holder (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Crash-recovery contract"). The model's choice
includes both, so it has every run of the supplement and more. The safety
argument is about votes and certificates, which are over entry vectors, so
it is unaffected; the liveness proofs use only what the supplement's
`Recover` guarantees, a valid representation of a certified entry vector
(`prepqc_valid`, `commitqc_valid`).

**(d) Chorus.** [Chorus.lean](../Cadence/Chorus.lean) reads the MVBA's
value through the class (`mval_pos (mvba.entries v) j m`), and the
immutable `mval_fb v j` says entry `j` of the representation is certified by
a `FallbackQC`.
* **The decision handlers read the validator's own representation.**
  `on_mvba_decide_pos i j m v` requires `mvba.decided mvba_st i v`, and its
  bridge checks the certificate `v` names for the entry: a vote quorum for
  a `FastQC` entry, a fallback quorum and the `FBCert` for a `FallbackQC`
  entry. The shared per-entry records hold the agreed entries; their
  uniqueness follows from `agreement`, over entries.
* **`cast_fb_commit i v` waits exactly under its own `B′`**: for every
  positive entry of its decided `v` held by a `FallbackQC`, the validator's
  assigned chunk, as Algorithm 5, lines 37–39
  (`line:fb-mvba-decide`–`line:fb-commit-wait`) prescribe. The vote's
  content is the entry vector.
* **A redelivered decision** (P11). The contract's Integrity lets a correct
  validator output several representations with one entry vector, and the
  target does not say whether the handler of Algorithm 5, line 37
  (`line:fb-mvba-decide`) re-runs, ignores the second output, or replaces
  the first `B′`. The model's rule is safe under all three readings. The
  vote is cast once (the fired-once guard `¬ local_fbcommit_voted i`), and
  every reading casts the same message, because its content is the entry
  vector. The wait reads the `FallbackQC` entries of the `v` the vote is
  cast for, which is one of the validator's decided `B′`s, so every paper
  vote is a model vote; the model may cast under a later `v` as well, which
  adds runs, and no safety property reads the wait. The fairness premise
  owes the vote only to a validator with one decided representation
  (`Owed (.cast_fb_commit i v)`), so it never owes a vote the paper might
  not cast. At the system's instance the case does not arise: `Mvba`
  decides once per validator.
* **No common `B′` is assumed** anywhere (P2): termination is proven per
  validator, each on its own decision.

### 8.2 The `CommitQC` route

**(a) The route.** The supplement: "Upon receiving this output, Chorus
broadcasts the `CommitQC`. A correct validator that receives a valid such
certificate re-broadcasts it and finalizes the certified outcome,
recovering a matching meta-block or the underlying proposals as required by
the ordinary commitment-proof recovery path" (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Decision output and handoff"). In the model a
correct validator broadcasts the certificate its decision outputs
(`send_mvba_cert`, the message `msg_mvba_cert`). A validator that receives
one recovers a matching representation, checks the certificates it names
(the same bridge as at the decision handlers), commits the certified
entries and re-broadcasts the certificate (`commit_assign_pos_mvba` /
`_neg_mvba`), then finalizes by the ordinary `finalize_commit`. The route is a handler
and not only a guard disjunct because a certificate can exist before any
correct validator decides (the adversary can aggregate `2f+1` `Commit`s),
and the paper's validator finalizes on it then. The handlers write the
records the decision handlers write, so every invariant downstream of the
records covers the route. Every read is positive, and the handlers have no
phase gate, as the target's rule has none.

**(b) Agreement and availability.** The route's agreement with the fast
path is the fast-path argument of Proposition 1
(`prop:agreement-entries`), applied to the certificates of the recovered
representation; its agreement with the `fbCommitQC` route and with itself
comes from `certified_unique` and `certified_decided` (§5.7). Data
availability needs no second bridge: the certificate check gives every
recorded positive entry a vote quorum or a `FallbackQC`, so its chunks are
on the network (`local_committed_pos_implies_decodable`).

**(c) `AvailReady` is an MVBA input that Chorus drives.** The supplement
makes the dissemination layer the source of availability: the MVBA "treats
availability synchronization as a service of the composing dissemination
and ChunkSync layer" (Supplement, Section 1.2 (`subsec:mvba-protocol`),
"Availability-synchronization assumption"). So `AvailReady` is an input of
the contract (`markAvail`, its effect and frames), and Chorus drives it
(`mvba_avail_ready`) with the chunk wait as its guard. The invariant
`avail_ready_chunks` says what it means, and with `certified_available`
gives `Chorus.certified_available_chunks`: a certified entry vector has a
supermajority whose correct members each received their chunk under every
`FallbackQC` entry of their own representation. The untimed availability
premise (F-avail) and the timed one (Δ-avail) are derived from Chorus's
fairness and rows (`Chorus.fAvail_of_fJustice`,
`Chorus.availWithin_of_timedJustice`). The coupling itself is P12.

**(d) No MVBA-arm gate, and no invocation gate.** The decision handlers,
`mvba_terminate` and `cast_fb_commit` have no phase gate, and they do not
require that the MVBA was invoked, because the target's rules have neither:
the decision handler runs "upon `MVBA[s].decide(B′)`" (Algorithm 5, line 37
(`line:fb-mvba-decide`)), and the paper's `mvbaInvoked` is the proposer's
own flag, read by its two proposal rules and by the forwarding of
`abandon()` (Algorithm 5, line 48 (`line:fb-abandon`)). The fallback commit
vote reads the voter's own decision and its own transport record
(`local_mvba_complete`), as Algorithm 5, line 41 (`line:fb-commitvote`) signs the
voter's own `entries(B′)`. The model's remaining phase guards are the
target's own: the deadline (`propose`, `record_chunk`, `vote`), the
fallback arm (`fb_sign_*`, `cast_fallback_vote`), and the two triggers of
`mvba_propose`. The one phase invariant the records need,
`mvba_decided_phase`, reads `phase ≠ pre_deadline`: a record carries a
certificate whose correct signers voted after the deadline.

## 9. Scope and access

* **Access to the target.** Auditors are assumed to have, or to be able to
  obtain, the paper sources at `48cac9a`, the internal supplement included.
  All of it is to be made public. The supplement's MVBA is a standard,
  well-understood leader-based BFT primitive, so nothing sensitive is
  involved.
* **The Conductor.** The development verifies the main body's
  Algorithm 7 (`algorithm:conductor`). The supplement's practical Conductor
  (Supplement, Algorithm 2 (`alg:conductor-practical`), §5.8) is outside the verified surface. It has
  not been reviewed for this development, and it is still changing: its
  algorithm file changed between `eb1bb51` and `48cac9a`, and P9 applies to
  it. Once it stabilises, a check of its compatibility with the main-body
  Conductor at the interface level, the `OrchestratorSafety` contract, is
  on [TODO.md](TODO.md). If the two are compatible there, the simpler
  main-body Conductor stays the verified one.
* **Paper commits after the target.** None is known: at the last check
  (2026-10-02) the paper repository's `master` was `48cac9a` itself. A
  later commit is listed here, with a one-line summary, by the session that
  finds it; it does not move the target (§0).
