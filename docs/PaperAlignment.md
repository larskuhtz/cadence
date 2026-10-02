# Paper alignment — the target revision, the review against it, and the plan

*What an auditor asks first: the models claim to verify the Cadence paper,
but which paper, and is it still that paper? §0 names the target revision.
§1 gives the mechanical check anyone can re-run against it. §§3–5 hold the
review of what the models rest on, item by item, and §5.10 what still
differs and why. §6 is the page of findings for the paper's authors. §8 is
the realignment that brought the models onto the target, with the designs
it rests on. Earlier targets are recorded in [History.md](History.md)
§ "Paper alignment before the single target".*

## 0. The target

The development targets **one revision of the paper repository: `48cac9a`**
(`48cac9a41efac2fb58f32f61ff21fd89db7c7d98`, branch `master`, committed
2026-10-02 00:40 UTC, frozen on 2026-10-01 in session R13). The target is
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
map, and the status sentence of the README and of
[Cadence.lean](../Cadence.lean), and no model file.

The target does not follow the paper repository's `master`. A later paper
commit is a new target only when a session moves it, by running §1 against
the new commit and planning the difference as §8 did. §9 lists the paper
commits after the target that the next cycle has to read.

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

**Result at the target** (2026-10-02, R14, R15 and R17). The map has every
label of the two documents, and every citation outside the two frozen
records checks against it, in label and in rendered reference. R17
regenerated the map from `48cac9a` with `scripts/paper-labels.sh`: it is
byte-identical to the committed one (377 labels), and
`scripts/paper-cites.sh` reports no problem.

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
| S9 | (in full) Everything else in Supplement, Section 1 (`sec:mvba-instantiation`): views, leader schedule, the lock, timeout certificates, `SyncView`, retention, the execution model, crash recovery, `Recover`, `Δ_R`, `Δ_sync` | (a) | Unchanged since `eb1bb51`. The model's coverage of each is recorded in the [Mvba.lean](../Cadence/Mvba.lean) header and in [MvbaPlan.md](MvbaPlan.md) §11. |
| S10 | The practical Conductor (Part I): the window-admission lemma moved; the agreed-first-deadline argument rewritten; `eq:predecessor-deadline` folded into Supplement, Equation (1) (`eq:slot-deadline`); `offset(s)` defined; `2 ≤ p ≤ W−1` in the relation lemmas; the `H_ω` slack explained; Supplement, Equation (6) (`eq:ticket-freshness`); `ass:` → Supplement, Section 4.1 (`assum:recovery-data-availability`); `lem:certified-prefix` unlabelled | (a) | Outside the verified surface: the Conductor model follows Algorithm 7 (`algorithm:conductor`), which did not change. None of these labels is cited. §5.8, §9 |
| S11 | The set-agreement ACS as an MVBA instance: "the decided value is the candidate set `S`; `entries(S)` is the canonical ordered list …" | (a) | The Conductor consumes `ACSSafety` abstractly. §5.8 |
| S12 | The fast-path proposition of the Conductor's relation section: "This branch must close on the fast path" | (d) | |
| S13 | (in full, Part II) Supplement, Section 7.4 (`sec:fallback-transition`): entries evaluated continuously over all votes; `EquivCert` from two witness chunks; no re-encode-and-send | (d) | An implementation variant. The model follows Algorithm 5 (`alg:fallback`). §5.9, and §6 P3 |
| S14 | (in full, Part II) Supplement, Section 7 (`sec:implementationnotes`), "Don't implement the post-MVBA commit round" | (d) | Implementation guidance. After S8 the model has both routes, so implementation runs are among its runs for safety. §5.7 |
| S15 | (in full, Part II) Supplement, Section 10.5 (`sec:domain-separation`) | (d) | Cited at M1. |

Count: (a) 4, (b) 3 (one of them also (c)), (c) 1, (d) 8.

**Over both tables:** (a) 10, (b) 4, (c) 2, (d) 11. The (b) and (c)
items, each now in the models (§8 has the sessions):

* **(b) M3** (R14). `Primitives.ErasureCoding` decodes from indexed
  fragments with `f+1` distinct indices.
* **(b) S6, with F13** (R15). The MVBA's value is the representation, an
  entry vector together with each positive entry's certificate kind
  (`MetaBlock`). Chorus's decision handlers check the certificate their
  own representation names, and `cast_fb_commit` waits exactly under the
  `FallbackQC` entries of its own `B′`.
* **(b) S7** (R15). `AvailReady` is indexed by the representation
  (`avail_ready i x`).
* **(b) S8** (R16). Chorus finalizes on a valid MVBA `CommitQC`
  (`on_mvba_commitqc_pos` / `_neg`), as well as on the `fbCommitQC`.
* **(c) M9/S6** (R15). `MVBASafety` has the `entries` projection, and
  Agreement and Integrity are stated over it, in the supplement's forms.
* **(c) S8** (R15, R16). `MVBASafety` has the certificate-level facts the
  second route needs (`certified_unique`, `certified_decided`,
  `certified_valid`, `certified_available`, `certified_mono`), and
  `AvailReady` as an input the caller drives.

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
implementation's side of that modelling choice. **Class (a)**, with one
documentation step: [ChorusDesign.md](ChorusDesign.md) §3.1's relation
inventory is to cite Supplement, Section 10.5 (`sec:domain-separation`) for it (§8, R14; the item is
also in [TODO.md](TODO.md)).

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
of `f+1` entries, duplicates included. **Class (b)** for that class: state
`Decode` over indexed fragments with `f+1` distinct indices (§8, R14).

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
restart. **Class (c), done in R15:** `MVBASafety.integrity` is stated over
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
does. Before R15 the value was the bare entry vector, and the wait read
"held by a `FallbackQC`" as "no positive `FastQC` exists for it". That
differed from the paper for a root with both certificates where the
validator's own `B′` carries the `FallbackQC`: F13
([Bounds.md](Bounds.md) §6.4.2, "F13 closed").

**F13 was an artefact of the hybrid target.** Under v2, Module 3 (`mod:mvba`)'s
Agreement was `B = B′`, so every correct validator decided the same
representation. A model of v2 would have carried the certificate kinds in
the value, and its wait would have matched the paper's exactly. The residual
arose because the value was taken at the supplement's entries level while
the wait follows v2's certificate-dependent rule. At the target, both
documents agree that only entries are agreed, so certificate kinds
legitimately differ between validators, and the faithful model carries each
validator's own representation. With that, F13 disappears:
`cast_fb_commit` waits exactly under the `FallbackQC` entries of its own
decided value, and the timed premise owes the vote as the paper does.
**Classes (b) and (c)**, done in R15 (§8). On the paper side there is a related
finding. The main body's own proofs still argue from a common `B′`
(§6, P2).

### 5.6 F14

`Owed (.redisseminate_chunk k i j m)` was `(CorrectChunkQuorum j m ∧ k has
decided) ∨ msg_fb_pos_sig k j m` ([Bounds.md](Bounds.md) §6.4.2). The left
disjunct owed chunks to other validators after a decision. At the target,
a decided validator broadcasts only *its own* chunk, and only under
`FallbackQC` entries of its `B′` (Algorithm 5, line 39 (`line:fb-commit-wait`), unchanged). A
correct MVBA `Commit` signer does the same under `AvailReady`. Neither
re-encodes for others. **Closed in R14:** the row is `msg_fb_pos_sig k j m`,
the fallback-entry rule's re-dissemination (Algorithm 5, line 12 (`line:fb-redisseminate`)), and
nothing else. No Veil statement moved.

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

**What the model does** (since R16, §8.2). It has both routes. The main
body's is the fallback commit round (`cast_fb_commit`, `fbcommitqc`). Part
I's is the handoff into the MVBA (`accept_mvba_commitqc`) together with the
`CommitQC` route: a correct validator holding a valid MVBA `CommitQC`
recovers a matching representation, checks the certificates it names, and
records the certified entries (`on_mvba_commitqc_pos` / `_neg`). It then
finalizes on them, because `commit_assign_*` accept "a valid MVBA
`CommitQC` exists" in place of `fbcommitqc`. The re-broadcast is folded
into the handoff, as the decision broadcast is. So the model has every run
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
one (§9).

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
assigned chunks unconditionally"). The model
justifies (F-justice) on `redisseminate_chunk` by Algorithm 5, line 12 (`line:fb-redisseminate`)
and Algorithm 5, line 39 (`line:fb-commit-wait`), both main-body rules that hold at the target.
**Class (d).**

### 5.10 What remains different, and why

The re-check of R17 walked §§3–4 once more against the realigned models.
Every (b) and (c) item is modelled (the list at the end of §4 says where).
Every remaining difference between a model and the target is one of the
following: below the model's abstraction, with its argument, or a finding
of §6. One needs a model change, F15, found by R18 after the re-check (the
last row); the others do not.

| Difference | Model | Why it is sound, or the finding |
|---|---|---|
| No signature tags, slot checks, TIBE operations or decryption shares (M1, M4, M6, M7) | Chorus | Each message type is its own relation; one model is one slot's instance; hiding is not a Veil property; shares are not modelled individually (§3). |
| The representation leaves out negative entries' certificate kinds and the `FBCert` | Chorus, Mvba | No rule of either document reads them, and whether they verify is part of `Valid` (§8.1 (a)). |
| `Recover` is a choice among valid representations | Mvba | It includes the supplement's choice, so the model has every run of the supplement and more; the liveness proofs use only what the supplement's `Recover` guarantees (§8.1 (c)). |
| No crashes and no persistence | Mvba, Chorus | With the state persisted before each send and reloaded atomically, a crash and restart is, to every other validator, a pause, and the model's runs pause. Termination under crashes (Supplement, Corollary 1 (`cor:mvba-recovery-termination`)) is not claimed. |
| `propose` enters the first view, not the view of the highest retained timeout certificate | Mvba | The faithful rule needs a negative read of the network, which the monotone-network contract forbids. The model's rule adds runs, which is sound for safety, and no liveness argument uses them ([MvbaPlan.md](MvbaPlan.md) §11.3, C7). |
| `SyncView` is its own step; the view timer is a phase marker; one action covers the timer and the `f+1` echo timeout | Mvba | The same reachable states in two steps, or a guard that only removes behaviours (the [Mvba.lean](../Cadence/Mvba.lean) header, "Abstractions"). |
| The `CommitQC` re-broadcast is folded into the handoff | Chorus | A certificate is transferable and stays valid (`certified_mono`), so its existence is its availability to every validator (§8.2 (a)). |
| An `upon` handler runs once | Chorus | The target states no convention: P6. |
| A redelivered decision casts the vote once, after the wait under the `B′` it is cast for | Chorus | The target does not say: P11. Safe under each reading (§8.1 (d)). |
| `AvailReady` is an input that Chorus drives; two liveness premises read the MVBA's accepted value | Chorus, Mvba | P12. |
| Termination's abandon condition and the timed claims' start condition are contract antecedents | Interfaces | P13. |
| Both fallback finalization routes are modelled | Chorus | The target specifies both (§5.7); P2. |
| The `EquivCert` rule is Algorithm 5's, not Part II's | FallbackReceipt, Chorus | The main body's rule is the specified protocol (§5.9); P3. |
| Part II's implementation variants; the practical Conductor | — | Outside the verified surface (§2, §7, §9). |
| **F15**: the fallback signer's chunk is a separate step, gated on the signer's participation at delivery, where the paper sends it inside the fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`)) | Chorus | **Our divergence, open; closed in R19** (a model change and a cold Chorus re-solve). An abandonment between signing and delivery drops a message the paper has already sent, so the MVBA's (Δ-avail) cannot be derived from the rows and stays assumed in the timed MVBA premise. Safety is unaffected (fewer deliveries), and `Chorus.timed_termination` does not meet it. The counterexample and R19's two designs: [Bounds.md](Bounds.md) §6.4.2, "F15". |

**No rule of the target is unmodellable.** Every protocol rule of the main
body and of Part I's MVBA can be modelled faithfully within the
monotone-network contract, with the one exception in the table: the MVBA's
"enter the view of the highest retained timeout certificate", which the
model over-approximates.

## 6. Findings for the paper's authors

*This section can be sent to the authors as it stands. It lists what the
machine-checked development found on the paper side, at the paper
repository's revision `48cac9a` (§0): the main body and the internal
supplement. Each finding quotes the paper and cites it as the rendered PDF
shows it, with the LaTeX label in parentheses; a citation that starts with
"Supplement" is to the supplement, every other one to the main body. Each
finding then says why it matters for a claim, and gives its status: open
for the authors, and how the formal development handles it. "The model" is
the Lean development of this repository.*

| # | Finding | Kind | Status |
|---|---|---|---|
| P1 | Module 3's Integrity was not revised with its Agreement | main body vs supplement | open |
| P2 | Two proofs argue from a common `B′` and from two commitment proofs | proof gap | open; the model proves the claims without either |
| P3 | The supplement contradicts itself on `EquivCert` construction | supplement, internal | open; the model follows the main body |
| P4 | A Part I obligation cites a Part II argument | supplement, internal | open |
| P5 | Lemma 11 claims `5Δ + ℓ_MVBA`; its proof gives `4Δ + ℓ_MVBA` | statement vs proof | open; **confirmed by proof**: the model proves the paper's bound and the sharper one |
| P6 | No convention says how often an `upon` handler runs | missing convention | open; the model reads "once" |
| P7 | A stale backup of the supplement is in the tree | source hygiene | open |
| P8 | A stub still lists a backoff policy for the MVBA timeout | stale text | open |
| P9 | The practical Conductor assumes `2 ≤ p ≤ W−1` without saying so | unstated assumption | open; outside the verified surface |
| P10 | arXiv v2's Algorithm 6 and Algorithm 2 hash chunks differently | fixed at `48cac9a` | for the next public version |
| P11 | What Chorus does with a redelivered MVBA decision is not stated | missing rule | open; the model is safe under every reading |
| P12 | The MVBA's availability crosses Module 3's interface | module interface | open; the model states the dependency |
| P13 | Module 1 states Termination without the conditions Chorus needs | module interface | open; the model states the conditions |

P1–P4 are inconsistencies between the main body and the supplement, or
within the supplement. P5 and P6 date from the review of arXiv v2 and hold
at `48cac9a`. P7–P11 are smaller. P12 and P13 are about module
boundaries: a claim takes from a module something the module's interface
does not state. §6.1 checks every module boundary the development's claims
cross.

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
  **Confirmed by proof** (R18, 2026-10-02). The model proves the lemma as
  stated, `ℓ = 5Δ + ℓ_MVBA` plus the local steps (`Chorus.timed_termination`,
  `5Δ + ℓ_MVBA + 9δ`), and from the same premises the sharper bound
  `4Δ + ℓ_MVBA` plus local steps (`Chorus.timed_termination_tight`,
  `4Δ + ℓ_MVBA + 8δ`), which implies it. The single split is at the
  fallback commit votes' deadline `max(t, GST) + 3Δ + ℓ_MVBA` (plus `6δ`):
  an earlier finalizer gives everyone totality's `Δ`, and otherwise nobody
  has abandoned before the votes, so Proposition 5
  (`prop:chorus-finalization-time`)'s chain finalizes everyone by
  `T₀ = max(t, GST) + 4Δ + ℓ_MVBA`. No step of the proof uses the outer
  split. **Suggested correction:** state Lemma 11 with
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
  Algorithm 7 (`algorithm:conductor`) (§9).

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
  held value. The timed form of the assumption, (Δ-avail), is still assumed
  in the timed MVBA premise of the proven timed Chorus claim
  (`Chorus.timed_termination`). The paper's Chorus does provide it, but
  the model cannot derive it from Chorus's own timed rows yet: the model's
  re-dissemination diverges from the paper's (F15, our divergence, §5.10),
  and R19 fixes the model and derives it. Safety does not depend on any of
  this.

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
  antecedents. `SlotConsensusTemporal.termination` requires that no
  correct validator abandons before finalizing, and `Chorus.termination`
  takes it as a caller's premise (`NoAbandonBeforeFinalizing`), which the
  glue meets. The timed claims take the start condition, which the
  composition discharges from the Orchestrator's Integrity
  (`OrchestratorSafety.integrity_timing`). No result proven here relies
  on Module 2 (`mod:orchestrator_2`)'s commented-out block.

### 6.1 The interface check

Every claimed result takes facts from module contracts. This table lists
each fact that is not plainly a property of the paper's module, what uses
it, and whether the target's module interface provides it. A "no" is a
finding, unless the fact is the development's own stated bridge.

| Fact the development uses | Used by | Provided by the target's module? | Finding |
|---|---|---|---|
| The MVBA's commit certificate: `certifies`, `decided_certified`, `accept` and its effect, `certified_mono`, `certified_unique`, `certified_decided`, `certified_valid` | the `CommitQC` finalization route (Chorus safety); the decision handoff (`Chorus.termination`) | not by Module 3 (`mod:mvba`), whose `decide` outputs the meta-block alone; by the supplement's Part I ("`decide(x, CommitQC)`", a transferable certificate the MVBA accepts from any view) | P2 |
| `availReady`, the input `markAvail`, their frames; `certified_available` | Chorus's availability report; the MVBA's termination | no: the supplement states `AvailReady` over the dissemination layer's state | P12 |
| `availOwed` and the validity bridge at a held value, both reading the MVBA's accepted value | `Chorus.termination` (premises `FJustice`, `ValidBridge`) | no: neither document exposes `x_v` | P12 |
| (Δ-avail), in the timed MVBA premise | the timed Chorus claim (`Chorus.timed_termination`, through `T.Admissible`) | no: the supplement's assumption is triggered by `x_v` | P12; still assumed: the derivation from Chorus's timed rows is blocked by F15, our divergence (§5.10), and is R19's |
| No correct validator abandons before finalizing | `Chorus.termination`, `Chorus.totality` | not by Module 1 (`mod:slotconsensus`) (commented out); the composition meets it (Algorithm 1, line 23 (`line:abandon`)) | P13 |
| No correct validator starts before `s.deadline − Δ` | the timed Chorus claims (stated) | not by Module 1 (`mod:slotconsensus`) (commented out); by Module 2 (`mod:orchestrator_2`)'s Integrity | P13 |
| The validity bridge: a valid meta-block's certificates verify against the network, and genuine certificates make it valid | Chorus safety at the decision handlers and the `CommitQC` route; `Chorus.termination` | `Valid` is "publicly verifiable" in both documents; the bridge says what that means for a network of relations | none: the development's one stated bridge ([Architecture.md](Architecture.md) §4) |
| The MVBA's abandon antecedent and Quiescence | `Chorus.termination` (through `Mvba.termination`) | yes, Module 3 (`mod:mvba`) | — |
| ACS Agreement, Validity (genuine pairs), Integrity | `Conductor ⊨ OrchestratorSafety` | yes, Module 4 (`mod:acs`) | — |
| Open-prefix agreement of the Orchestrator | the glue's safety | derived: the safety residue of Module 2 (`mod:orchestrator_2`)'s Totality and Monotonicity | — |
| "A correct validator decides only after proposing", for the MVBA | nothing since R16 (the two helper invariants that needed it were deleted) | not by Module 3 (`mod:mvba`); Module 4 (`mod:acs`)'s Integrity states it for the ACS | none: no claim uses it |

## 7. Implementation variants the models cover

For reference, the Part II departures and how the models stand to them once
the plan is done:

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

## 8. The realignment

Sessions in order. Each is one PR off `master`, and the next starts after
the last one merges. "Cold" means the Veil family re-solves from scratch,
because VC statements move. "Warm" means only kernel replay. One
Interfaces.lean edit moves every Chorus VC, since class fields are
hypotheses of every cell, so the plan makes exactly **one** contract edit,
and puts the Chorus model changes in the same session.

**R14 · Statements that need no Veil re-solve. Done** (2026-10-02; the
build is [History.md](History.md)'s R14 row).
* `Primitives.ErasureCoding` (M3). Before, `Decode : List fragment →
  Option cipher`, and `decode_sound` held for any list of `f+1` encoded
  fragments, duplicates included, at every `f`. After, the class takes the
  system's `n` and `f`, `Encode : cipher → Fin n → fragment`, `Decode`
  takes a `Finset (Fin n × fragment)`, and `decode_sound` requires `f+1`
  distinct indices, each fragment at its own index, as Appendix C.1
  (`appendix:crypto`) states the interface. No Chorus VC statement moved:
  a warm Chorus proof file replayed with no new cache entry.
* F14 (§5.6): `Owed (.redisseminate_chunk k i j m)` is
  `msg_fb_pos_sig k j m`. `Chorus.termination`, the timeline milestones,
  `Chorus.totality` and the three witness theorems re-checked in plain
  Lean at `[propext, Classical.choice, Quot.sound]`.
* The (d) items: the per-slot dispatch sentence in the
  [Cadence.lean](../Cadence/Cadence.lean) header (M5); domain separation in
  [ChorusDesign.md](ChorusDesign.md) §3.1 and in
  [Architecture.md](Architecture.md) §4 item 3 (M1, S15); the
  positional-fragment remark beside ChorusDesign's network table (M2);
  `ρ_mvba` in the MVBA schedule's prose (S4); and, from
  [TODO.md](TODO.md), ChunkSync and `Δ_sync` beside the (F-justice)
  justification of re-dissemination (`Chorus.Owed`).
* Families: none cold. The pins are unchanged.
* F13, F14, S4: F14 closed; F13 and S4 untouched.

*Plan changes made in R14:*
* **Citations to the rendered PDF** (Lars, 2026-10-02), added to R14. Every
  citation reads as the target's rendered PDF shows it, with the label in
  parentheses, and names the supplement where it is the supplement. The
  label map [paper-labels.tsv](paper-labels.tsv) is generated from the
  target by `scripts/paper-labels.sh`, and `scripts/paper-cites.sh` checks
  every citation against it (§1). Citations by `.tex` path or by paragraph
  title are replaced by the enclosing numbered unit; an unlabelled unit
  (several of the supplement's Part II subsections) is cited by its
  labelled parent, with its title as a description. The model headers now
  say that citations name the target's references, while the statement
  that the models were built against v2 stays until R17.
* **Two files keep the bare-label form until R15**:
  [Interfaces.lean](../Cadence/Interfaces.lean) and
  [System.lean](../Cadence/System.lean), which R14 does not touch.
  `scripts/paper-cites.sh` checks their labels against the map but not
  their form. R15 rewrites their citations in the same edit and removes
  the exemption.
* **The citation check runs in the docs build.** `scripts/docs.sh` runs
  `scripts/paper-cites.sh` beside the link resolution, so the docs workflow
  fails on a cited label missing from the map as it fails on a dead link.
  No workflow file or limit changed.
* **R17's anchor re-check** is §1's check: regenerate the map at the new
  pin and run the citation check.

**R15 · The meta-block representation, and the contract. Done**
(2026-10-02; the builds are [History.md](History.md)'s R15 row). The one
Interfaces.lean edit, together with every model change it needs; the design
is §8.1.
* **Contract (c).** `MVBASafety` has the `entries` projection; Agreement
  and Integrity are stated over it in the supplement's words (M9, S6,
  §5.4); the commit certificate is over entries; the four certificate-level
  fields of §5.7 (`certified_unique`, `certified_decided`, `certified_valid`,
  `certified_available` over the observable `availReady`) are proven by
  `Mvba.mvbaSafety` and withheld from the solver with the three handoff
  facts. The class takes the system's quorum family as a parameter, which
  the availability field counts with.
* **Mvba (b).** `value` is the representation and `evec` the entry vector,
  joined by `ent`; votes, certificates and locks are over `evec`; `Recover`
  is a choice among valid representations (`leader_repropose`,
  `form_own_commitqc`, `decide`); `avail_ready` is indexed by the
  representation (S7). Every property keeps its name; a fourth trace
  shows two correct validators deciding different representations of one
  entry vector.
* **Chorus (b).** The decision handlers check the certificate the
  validator's own representation names, and `cast_fb_commit i v` waits
  exactly under the `FallbackQC` entries of its own decision `v`. F13 is
  closed with no residual (§5.5, [Bounds.md](Bounds.md) §6.4.2).
* **System.lean** re-instantiates at `MetaBlock node merkle_root` and
  defines the MVBA configuration `Cadence.mvbaTheory` beside
  `Cadence.chorusTheory`.
* **Citations** of Interfaces.lean and System.lean are in the rendered form,
  and `scripts/paper-cites.sh` has no exemption left.
* Families cold: Mvba (`Mvba/NoLock.lean` re-run, its witness the same 25
  transitions, re-pinned with `(sequential := true)` because labels print
  the representation as `x`) and Chorus. FallbackReceipt, Cadence and
  Conductor warm.
* Pins: unchanged, as §8.1 (f) wrote down before the build — Mvba
  `29 · 51 + 28 = 1507`, Chorus `47 · 102 + 46 = 4840`, FallbackReceipt
  `220`.
* Re-established at `[propext, Classical.choice, Quot.sound]`:
  `Mvba.mvbaSafety`, `Mvba.mvba_of_temporal`, `Mvba.termination`,
  `Mvba.bounded_termination`, `Mvba.mvbaTemporal`, `Mvba.mvbaFull` and both
  Mvba witnesses (`Mvba.Witness.ell = 24`); `Chorus.slotConsensusSafety`,
  `Chorus.termination`, the timeline, `Chorus.totality`, the three Chorus
  witnesses, System.lean's end theorem and every pin of
  [Cadence.lean](../Cadence.lean). The monitor suites pass.
* F13: closed. F14: closed in R14. S4: re-based on the new model; its
  fallback commit round rows owe `cast_fb_commit` under the validator's own
  `B′`.

*Plan changes made in R15:*
* **The pins do not move.** The plan expected new counts; the design keeps
  every action and property, restating them over the split, and the
  availability fact rides on the restated `honest_commit_accepted`. Both
  families still re-solved cold, since every statement changed.
* **The contract takes the quorum family as a parameter** (§8.1 (b)), for
  `certified_available`.
* **A redelivered decision** (P11, new): the target does not say what
  Chorus's decision handler does with a second decision output that has
  the same entries and another representation. The model's rule is safe
  under every reading (§8.1 (d)), and `Owed (.cast_fb_commit i v)` owes
  the vote only to a validator with one representation.
* **No per-validator Chorus record.** The plan said the handlers "record
  the validator's own representation"; `cast_fb_commit` reads it directly
  from the positive observable `mvba.decided mvba_st i v` instead (§8.1
  (d)).
* **`Chorus.termination` is stated at the system's MVBA configuration**
  `Cadence.mvbaTheory`, where `ent := MetaBlock.entries`; before, it held
  for every MVBA theory. A validator must be able to propose a certified
  meta-block, and under an arbitrary `ent` no representation need have the
  certified entries. It fixes configuration, as `Cadence.chorusTheory`
  does; it adds no premise. System.lean's safety theorem stays generic.
* **One scoped exception of the monotone-network audit is gone.**
  `cast_fb_commit` no longer reads the shared decision records under a
  universal, so [ChorusDesign.md](ChorusDesign.md) §3.1 and
  [Architecture.md](Architecture.md) §4 item 1 list two categories.
* **The monitor's MVBA value** is a representation; a `FallbackQC`-held
  positive entry is written `{"fallback": k}` ([Monitor.md](Monitor.md)).
* **One session.** The plan expected two sessions on one branch; R15 and
  its Chorus side fit one.

**R16 · The `CommitQC` finalization route (S8). Done** (2026-10-02; the
builds are [History.md](History.md)'s R16 row). The design and what the
build decided are §8.2.
* **Chorus has Part I's route.** `on_mvba_commitqc_pos` / `_neg` record a
  valid MVBA certificate's entries after the certificate bridge on the
  recovered representation. `commit_assign_*` finalize on `fbcommitqc ∨
  mvba_commitqc` together with the records. The re-broadcast is folded
  into the handoff. The main body's route stays.
* **Contract.** `certified_mono`, and `AvailReady` as an input the caller
  drives: `markAvail`, its effect, its own-party frame, `init_availReady`
  and four frames. `certified_unique` and `certified_decided` reach the
  solver. `Mvba.mvbaSafety` proves every field, with no Mvba model
  change.
* **Chorus drives `AvailReady`** (`mvba_avail_ready`, the chunk wait as its
  guard). `avail_ready_chunks` proves what it means, and
  `Chorus.certified_available_chunks` reads `certified_available` in
  Chorus's vocabulary.
* **Gates.** The MVBA-arm gates of the decision handlers, `mvba_terminate`
  and `cast_fb_commit` are gone: our modelling error, since the target has
  none. `mvba_decided_phase` reads `phase ≠ pre_deadline`, and the two
  helpers `mvba_complete_phase` and `fbcommit_sig_phase` are deleted.
* **Liveness.** (F-avail) is derived (`Chorus.fAvail_of_fJustice`) and has
  left `MvbaAdmissible`. `ValidBridge`'s completeness covers held
  (accepted) meta-blocks. The availability report is a fair family, owed
  for a held meta-block (`availOwed`). The timed premise has its δ-row, and
  (Δ-avail) is assumed inside `TimedMvbaAdmissible` until S4.
* **Findings.** P12 (§6): the MVBA's availability couples it to the
  dissemination layer through state Module 3 (`mod:mvba`) does not
  expose. The interface check is §8.2 (h).
* Families: Chorus cold; Mvba warm (instance proofs and liveness in plain
  Lean); FallbackReceipt warm.
* Pins: `#veil_status Chorus` 4840 → **5099** (§8.2 (i)); Mvba 1507 and
  FallbackReceipt 220 unchanged.
* Re-established at `[propext, Classical.choice, Quot.sound]`:
  `Chorus.slotConsensusSafety`, `Chorus.termination`, the timeline,
  `Chorus.totality`, the three Chorus witnesses, System.lean's end theorems
  and every pin of [Cadence.lean](../Cadence.lean). The monitor suites
  pass.
* S4: the paper's bound still uses the main body's route. (Δ-avail) is now
  S4's to derive ([TODO.md](TODO.md) § Liveness).

*Plan changes made in R16:*
* **No second stated bridge.** §5.7 expected the route's data availability
  to need one. The certificate bridge the route needs for agreement also
  gives DA.
* **AvailReady is an input**, which the plan left open. On Lars's decision
  it is driven by Chorus, which needed one premise change (`ValidBridge` at
  held values) and the owed condition `availOwed`. Both read the MVBA's
  internal `accepted` (P12).
* **The gates.** The plan did not foresee them. Dropping them deleted two
  helper invariants, so the pin is 5099, not the designed 5199.
* **Contract shape.** `availReady_markAvail_frame` was added after the
  first cold solve found it missing (❌). `markAvail_enabled` was dropped,
  because no cell reads it and the monitor stub could not satisfy it.
* **The design's new invariants were fewer than planned.** The route's
  agreement and DA are covered by the existing invariants, restated over
  the widened ties. The one new invariant is `avail_ready_chunks`.

**R17 · Close the realignment. Done** (2026-10-02; the build is
[History.md](History.md)'s R17 row).
* **Re-check by §1.** The map regenerated from `48cac9a` is byte-identical,
  and the citation check is clean. Paper `master` has not moved (§9).
* **The classification walked once more** against the realigned models:
  every (b) and (c) item is modelled (§4), and every remaining difference
  is an abstraction with its argument or a finding (§5.10). None needs a
  model change.
* **The interface check** (§6.1): one new finding, P13. Module 1's
  Termination is stated without the abandon and start conditions Chorus
  needs; the contract already states both as antecedents.
* **§6 is the findings page for the authors**, P1–P13.
* **Status flipped.** §0, the README's paper section and the
  [Cadence.lean](../Cadence.lean) header say "corresponds to paper
  revision `48cac9a` (main body plus internal supplement)", and §0 is the
  one home of the target. Every model header has one pointer to §0 in
  place of its paper pin. The edit is comment-only, but it rebuilt every
  family, warm.
* **Verification.** A full warm re-validation: lake exit 0, ✅ 6 209 /
  ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 082, no warnings. Every pin is unchanged, and
  the three monitor suites pass.
* **The tag** `paper-target/48cac9a` is on the merge commit of this
  session's PR.

*Plan change made in R17:* the plan had each model header's pin become
`48cac9a`. Instead, every model header points to §0 and names no
revision, so a later re-pin edits no model file and rebuilds no family.

**After the realignment: the Chorus bounds leg resumes** at the stage it
stopped ([Bounds.md](Bounds.md) §6.4.6):

* **S4: the MVBA tail and the assembly.** `T.termination` through the
  projection, the fallback commit round (rows over the validator's own
  `B′`), the case split, and the bound. **F4 is decided here** (P5).
  **Done in R18** (2026-10-02): `Chorus.timed_termination` and
  `Chorus.timed_termination_tight`; F4 and P5 confirmed. (Δ-avail) was not
  derived: F15 (§5.10) needs a model change, R19.
* **S5: the contract instances.** `SlotConsensusTemporal` at the new
  fragment (Quiescence, `admissible_exists`, Termination as the unbounded
  corollary), then `SlotConsensusWithTotality` and the `…_of_temporal` join
  with its `rfl` lemma. After that: the [Cadence.lean](../Cadence.lean)
  rows, and (A-sc-termination) moving from assumed to discharged.

### 8.1 R15: the design

Written before any model edit. [spikes/13_metablock_consumer_ok.lean](../spikes/13_metablock_consumer_ok.lean)
checks the two Veil mechanisms the design rests on: a class field
`entries : value → entryvec` read inside a consumer's guards and invariants,
and a class that takes the system's quorum family as a parameter. It
reconstructs every cell, and the withheld field is reported as withheld.

**(a) The value.** The MVBA's value is the target's meta-block
representation: an entry vector together with the certificate kind of each
positive entry. The MVBA "votes and decides over `entries(B)`"
(Supplement, Section 1.1 (`subsec:mvba-datatypes`)), and two valid
meta-blocks "may carry different certificates for the same verdicts"
(Supplement, Section 1.2 (`subsec:mvba-protocol`), "Agreement and Integrity
over entries"). At the system's instantiation
([Interfaces.lean](../Cadence/Interfaces.lean), beside the MVBA classes):

```lean
inductive CertKind | fastQC | fallbackQC
abbrev MetaBlock (node merkle_root : Type) := node → Option (merkle_root × CertKind)
def MetaBlock.entries (b : MetaBlock node merkle_root) : node → Option merkle_root :=
  fun j => (b j).map Prod.fst
```

`MetaBlock.entries` is `entries(B)`. The representation leaves out what no
rule of either document reads: the certificate kinds of negative entries,
and the `FBCert`. `AvailReady` (Supplement, Algorithm 1, line 90
(`line:mvba:commit-send`)) and the fallback commit wait (Algorithm 5,
line 38 (`line:fb-commit-foreach`)) read only the positive `FallbackQC`
entries. Whether the left-out certificates verify is part of `Valid`, which
stays a predicate on the representation.

**(b) The contract.** One edit of `MVBASafety`. Unchanged fields are elided.

```lean
class MVBASafety (party value entryvec message state pset : Type)
    (B : ByzNodeSet party pset) (byz : party → Prop)
    extends TransitionSystemSafety state where
  Valid : value → Prop
  entries : value → entryvec
  …
  agreement : ∀ st, reachable st → ∀ p q v v',
    ¬ byz p → ¬ byz q → decided st p v → decided st q v' → entries v = entries v'
  integrity : ∀ st, reachable st → ∀ p v v',
    ¬ byz p → decided st p v → decided st p v' → entries v = entries v'
  external_validity : ∀ st, reachable st → ∀ p v, ¬ byz p → decided st p v → Valid v
  availReady : state → party → value → Prop
  certifies : state → message → entryvec → Prop
  decided_certified : ∀ st, reachable st → ∀ p v, ¬ byz p → decided st p v →
    ∃ c, certifies st c (entries v)
  accept : state → party → message → state → Prop
  accept_trans : ∀ st p c st', accept st p c st' → trans st st'
  accept_effect : ∀ st p c st' e, accept st p c st' → certifies st c e →
    ∃ v, entries v = e ∧ decided st' p v
  accept_enabled : ∀ st p c e, reachable st → ¬ byz p → certifies st c e →
    (∃ v', proposed st p v') → ¬ abandoned st p → (∀ v', ¬ decided st p v') →
    ∃ st', accept st p c st'
  certified_unique : ∀ st, reachable st → ∀ c c' e e',
    certifies st c e → certifies st c' e' → e = e'
  certified_decided : ∀ st, reachable st → ∀ c e p v,
    certifies st c e → ¬ byz p → decided st p v → entries v = e
  certified_valid : ∀ st, reachable st → ∀ c e,
    certifies st c e → ∃ v, entries v = e ∧ Valid v
  certified_available : ∀ st, reachable st → ∀ c e, certifies st c e →
    ∃ q, B.supermajority q ∧ ∀ p, B.member p q = true → ¬ byz p →
      ∃ v, entries v = e ∧ Valid v ∧ availReady st p v
```

* **Agreement and Integrity** are the supplement's sentences: "if correct
  validators decide `x` and `x′`, then `entries(x) = entries(x′)`", and
  "all decision outputs of a correct validator carry the same entry
  vector". Redelivery with the same entry vector is permitted, which is why
  Integrity is not "at most one representation" (§5.4).
* **The commit certificate is over entries.** It is "an aggregate of
  `2f+1` Commit signatures over `entries(x)`" (Supplement, Section 1.2
  (`subsec:mvba-protocol`), "Decision output and handoff"). So `certifies`
  takes an entry vector, a decision exposes a certificate for its entries,
  and accepting a certificate decides *some* representation with those
  entries. That representation is `Recover(e)` (Supplement, Algorithm 1,
  line 79 (`line:mvba:decide-guard`)).
* **The certificate-level fields of §5.7.** A certified entry vector is the
  only one: `certified_unique` against another certificate and
  `certified_decided` against every correct decision. Both are needed: a
  certificate can exist before any correct validator decides, because the
  adversary can aggregate it. A certified entry vector has a valid
  representation (`certified_valid`). The **availability field**
  (`certified_available`): a certificate's `2f+1` signers include, among
  their correct members, only validators that were `AvailReady` for a valid
  representation of the certified entries. That is the supplement's "the
  MVBA ensures that each correct Commit signer holds and broadcasts its
  assigned share before sending its vote" (Supplement, Section 1.2
  (`subsec:mvba-protocol`), "Commit availability condition").
  `availReady` is the observable `AvailReady_p(v)`, indexed by the
  representation (S7).
* **All first-order.** The availability field needs a quorum: a certified
  meta-block's entries are available because a supermajority signed the
  certificate and each of its correct members held its share. So the class
  takes the system's quorum family `B` as a parameter, as
  `Cadence.ByzNodeSetCounting` does. Chorus passes its own `nset`, and
  `Mvba.mvbaSafety` passes the model's. `byz` stays the class's notion of
  correct; `B` is used only for counting.
* **`veil_smt_ignore`:** `decided_certified`, `accept_effect` and
  `accept_enabled`, as now, and the four `certified_*` fields. No Chorus
  cell in R15 reads a certificate (`accept_mvba_commitqc` needs only
  `accept` and `accept_trans`). Every field that reaches the solver is a
  hypothesis of every one of Chorus's cells, and three of the four have an
  `∃` in their conclusion. Withheld fields stay declared axioms of the
  class, proven by `Mvba.mvbaSafety`. R16 lifts the attribute on exactly
  the fields its new cells use. That changes no statement, and R16 re-solves
  Chorus cold anyway.
* **Nothing is weakened.** `external_validity`, the inputs, the frames and
  Quiescence keep their statements. Agreement is the module's
  (Module 3 (`mod:mvba`)), Integrity is the supplement's (§5.4, P1), and
  every certificate field is new. `MVBATemporal` and `MVBA` take the new
  parameters and keep their fields, so Termination still says every correct
  party decides *some* representation.

**(c) The MVBA model.** [Mvba.lean](../Cadence/Mvba.lean) gets two sorts:
`value`, the representation, and `evec`, the entry vector. They are joined
by `immutable function ent : value → evec`, which the instance exports as
`entries`. Every relation of the supplement that carries a meta-block
carries the representation: `input`, `msg_preprepare` (the `Pre-Prepare`
carries `x` and signs `H(entries(x))`), `accepted` (`x_v`), `decided`,
`avail_ready` and `valid`. Every signed vote and every certificate carries
the entry vector: `msg_prepare`, `msg_commit`, `msg_timeout_qc`,
`msg_prepqc`, `msg_commitqc`, `tc_lock` and `local_prepqc`. This is exactly
the split of Supplement, Algorithm 1 (`alg:mvba`–`alg:mvba-cont3`).

* `handle_preprepare*` accept a valid `x`, check the lock against
  `ent x` (Supplement, Algorithm 1, line 17 (`line:mvba:pp-guard`):
  "`entries(x) = lock(J)` whenever `lock(J) ≠ ⊥`"), and send the `Prepare`
  on `ent x`. `adopt_prepqc (i v x q)` and `send_commit (i v x)` take the
  accepted `x` and act on `ent x`. `send_commit` requires `avail_ready i x`,
  the supplement's `AvailReady_i(x_v)`.
* **`Recover` is a choice among valid representations.**
  `leader_repropose (l pv v w x)` re-proposes any valid `x` with
  `ent x` the lock. `form_own_commitqc (i v q x)` and `decide (i v x)`
  decide any valid `x` whose entries the certificate certifies. The
  supplement's `Decide` takes `x_v` when its entries match and `Recover(e)`
  otherwise, and `Recover(e)` returns "a valid meta-block with entry vector
  `e`" from any holder (Supplement, Section 1.2 (`subsec:mvba-protocol`),
  "Crash-recovery contract"). The model's choice includes both, so the
  model has every run of the supplement and some where a validator decides
  a representation it fetched although it held one.
* **How two correct validators decide different representations with the
  same entries.** A Byzantine leader sends two valid representations with
  one entry vector to different validators. Both pass the guard, both
  validators prepare and commit the same entries, and each decides its own
  `x_v`. The `Recover` choices in a re-proposal and in `decide` give
  further runs of the same kind.
* **Why every safety property survives.** The safety argument
  (`prepqc_blocks_lower_commits`, `commitqc_agree`, Supplement, Theorem 1
  (`thm:agreement`)) is about votes and certificates, and those are over
  entry vectors exactly as before. Agreement over `ent` follows from
  `decided_backed` (a decision's entries carry a commit certificate) and
  `commitqc_agree`. Integrity is still by construction: one decision per
  validator, so the model proves the stronger at-most-once. External
  validity is now the decide guards' `valid x`. Every invariant keeps its
  name and is restated over the split. Where a fact links a vote to the
  meta-block behind it, the conclusion is existential. One example is
  `honest_commit_accepted`: `msg_commit R V E → local_prepqc R V E ∧ ∃ X,
  ent X = E ∧ accepted R V X ∧ avail_ready R X`, the lifted `TrySendCommit`
  guard. That invariant is what `certified_available` is proven from.
  Others are `prepqc_valid` and `commitqc_valid`: a certified entry vector
  has a valid representation, which is `Recover`'s correctness ("any
  correct signer of a valid prepare certificate on `e` is such a peer").
* **NoLock.** [Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) is the same
  model with the lock check removed, so it takes the same split. Its theory
  sets `value = evec = Fin 2` and `ent = id`: one representation per entry
  vector, since the mutation test is about the lock and not about
  representations. The scenario is unchanged. The pinned message is
  expected to change, because labels print the new parameter lists. It is
  re-pinned with `(sequential := true)`, and the reason is recorded in the
  file.
* **The witness and liveness.** [Mvba/Witness.lean](../Cadence/Mvba/Witness.lean)
  instantiates `value = evec = Unit`. The liveness chain needs a `Recover`
  output wherever a re-proposal or a decision fires: `prepqc_valid` and
  `commitqc_valid` supply it. (Δ-avail) is indexed by the representation, as
  the supplement's synchronization assumption is ("whenever a correct
  validator holds a valid meta-block `x`"). `Mvba.termination`,
  `Mvba.bounded_termination`, `Mvba.mvbaTemporal` and both witnesses are
  re-proven on the new labels.

**(d) Chorus.** [Chorus.lean](../Cadence/Chorus.lean) gets the sort
`mentries` beside `mvalue`, and
`instantiate mvba : MVBASafety node mvalue mentries mmsg mstate nodeset nset
(fun i => nset.is_byz i = true)`.

* `mval_pos (e : mentries) j m` and `mval_neg (e : mentries) j` project the
  entry vector, and every read goes through the class:
  `mval_pos (mvba.entries v) j m`. The new immutable relation
  `mval_fb (v : mvalue) j` says entry `j` of the representation is
  certified by a `FallbackQC`. The two assumptions are unchanged, now over
  `mentries`, and System.lean proves them as before.
* **The decision handlers read the validator's own representation.**
  `on_mvba_decide_pos (i j m v)` requires `mvba.decided mvba_st i v` and
  `mval_pos (mvba.entries v) j m`. Its bridge now checks the certificate the
  representation names:
  `(¬ mval_fb v j ∧ vote_quorum_pos j m) ∨ (mval_fb v j ∧ fb_quorum_pos j m ∧ fbcert)`.
  This implies the old disjunction, so `mvba_decided_pos_backed` and every
  invariant downstream keep their statements. The shared per-entry records
  stay. They hold the agreed entries, and their uniqueness is still proven
  from `agreement`, now over entries, through the tie invariants (spike 13
  checks this shape).
* **`cast_fb_commit (i v)` waits exactly under its own `B′`:**

  | | the fallback commit wait |
  |---|---|
  | target | "upon `MVBA[s].decide(B′)`: for each `FallbackQC` in `B′` with a positive entry `⟨s, j, root⟩`: wait until `p_i` has received and validated its assigned chunk for `root`" (Algorithm 5, line 37 (`line:fb-mvba-decide`) to Algorithm 5, line 39 (`line:fb-commit-wait`)) |
  | before (R12) | `∀ J M, is_proposer J → mvba_decided_pos J M → vote_quorum_pos J M ∨ msg_chunk_received i J M` |
  | after | `require mvba.decided mvba_st i v` and `∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → msg_chunk_received i J M` |

  The `B′` is the validator's own decision, a parameter of the label, and
  the wait runs over its `FallbackQC` entries and no others. F13 closes
  with no residual: a root that is `FastQC`-certified elsewhere but
  `FallbackQC`-certified in this `B′` is waited for, as in the paper.
  `require mvba_complete`, the transport of the vector, stays as it is. The
  vote's content is the entry vector, so `msg_fbcommit_sig` is unchanged.
* **A redelivered decision** (P11). The contract's Integrity lets a correct
  validator output several representations with one entry vector, so
  `mvba.decided mvba_st i v` may hold for two `v`. The target does not say
  what the handler of Algorithm 5, line 37 (`line:fb-mvba-decide`) does with
  the second output. It may re-run, be ignored, or replace the first `B′`.
  The model's rule is safe under all three readings:
  1. **The vote is cast once per validator.** The fired-once guard
     `¬ local_fbcommit_voted i` stays, so `cast_fb_commit` moves the state
     whenever it fires, and `Chorus.justice_enabledMove` keeps its proof.
     Every reading casts the same message, because the vote's content is
     the entry vector.
  2. **The wait reads the `FallbackQC` entries of the `v` it is cast for.**
     That `v` is some representation `i` decided. Under every reading the
     paper's validator casts after waiting under the `FallbackQC` entries of
     one of its decided `B′`s, so every paper vote is a model vote. The
     model may also cast under a later `v` where the "first `B′` only"
     reading would not. That adds runs, which is safe, because no safety
     property reads the wait.
  3. **The premise owes the vote only for a validator with one
     representation:** `Owed (.cast_fb_commit i v)` is
     `mvba.decided s.mvba_st i v ∧ ∀ v', mvba.decided s.mvba_st i v' → v' = v`.
     With one decision output, all three readings cast after the wait under
     that `B′`, and the δ-row owes exactly that vote. With several, the row
     owes nothing, so the premise never owes a vote the paper might not
     cast. At the system's instance the case does not arise: `Mvba` decides
     once per validator (it proves the stronger at-most-once Integrity), so
     the conjunct costs `Chorus.termination` one application of
     `reachable_integrity`.
* **No new per-validator record.** The validator's own representation is
  already a per-validator observable that the model reads positively,
  `mvba.decided mvba_st i v`, which the handlers read too. A Chorus-side
  copy would need its own tie invariant and would say nothing more.
* `mvba_propose` checks `Valid B_i` per kind, the same way as the handlers,
  for positive entries. `mvba_terminate` reads through `mvba.entries`.
* **Reads and sizes.** Every new read is positive. `mvba.decided` is read in
  positive position (oracle state, category (A) of
  [ChorusDesign.md](ChorusDesign.md) §3.5), as are `msg_chunk_received` and
  the network ghosts. `mval_*` are immutable. Parameters: `cast_fb_commit`
  2, `on_mvba_decide_pos` 4, `on_mvba_decide_neg` 3, `mvba_propose` 3.
* **P1 and P2 do not block.** P1: the contract states Integrity in the
  supplement's form. The vote fires once and its content is the entry
  vector, so a redelivered decision with another representation would cast
  the same message. Nothing in the model relies on the main body's "decides
  at most once". P2: the model never assumes a common `B′`. Termination is
  re-proven per validator, which is the repair P2 describes.

**(e) What the liveness vocabulary becomes.**

* **`ValidBridge`** keeps its two directions over the representation, and
  `Certified st x` names the certificate per kind. For a positive entry
  `(j, m)` of `entries x`, a `FastQC`-kind entry has `vote_quorum_pos j m`
  and a `FallbackQC`-kind entry has `fb_quorum_pos j m ∧ fbcert`. Negative
  entries are unchanged. This is sharper than before, where either
  certificate would do. It is still the cryptographic content of the seam:
  a valid meta-block's certificates are genuine, and genuine certificates
  make it valid.
* **The handoff.** `accept_mvba_commitqc` is unchanged. `relayOwed` is
  unchanged ("a correct validator has decided"). The MVBA's `Relayed`
  premise reads the `decide` family, whose representation is the `Recover`
  choice. `relayed_of_timedJustice` and `fRelay_of_fJustice` are re-proven.
* **`Owed`:** the one row that changes is
  `.cast_fb_commit i v => mvba.decided s.mvba_st i v ∧ ∀ v', mvba.decided s.mvba_st i v' → v' = v`
  (was `∃ v, mvba.decided s.mvba_st i v`). (d) gives the reason.
* **The hop rows:** `cast_fb_commit` stays a δ-row with the same gate. Its
  chunk is delivered by `redisseminate_chunk`'s own Δ-row from the correct
  `FallbackQC` signer (`Owed` is `msg_fb_pos_sig k j m`, F14). So the
  premise owes the vote δ after the wait is over, which is when the paper's
  validator casts it. The run F13 excluded from the timed claim's premise
  is now a run of the premise.

**(f) The pins, written down before the build.** Cells are
`(A + 1)(I + 1) + A·S`: invariant-type properties and one does-not-throw
cell at every action and at the initializer, and each step property at
every action.

* `#veil_status Mvba`: `A = 28`, `I = 50`, `S = 1`, all unchanged. No action
  or property is added or removed, and the availability fact rides on the
  restated `honest_commit_accepted`. **`29 · 51 + 28 = 1507` → 1507.**
* `#veil_status Chorus`: `A = 46`, `I = 101`, `S = 1`, all unchanged.
  **`47 · 102 + 46 = 4840` → 4840.**
* `#veil_status FallbackReceipt`: 220, warm.
* Every Mvba and Chorus VC statement changes, so both families re-solve
  cold although the counts stay. If the cold solve needs a helper
  invariant, each one costs `A + 1` cells (29 on Mvba, 47 on Chorus). It is
  recorded as a plan change with the new arithmetic.

### 8.2 R16: the design

Written before any model edit, and sent to the coordinator before one.

**(a) The route, as the target states it.**

| | the `CommitQC` finalization route |
|---|---|
| target | "Upon receiving this output, Chorus broadcasts the `CommitQC`. A correct validator that receives a valid such certificate re-broadcasts it and finalizes the certified outcome, recovering a matching meta-block or the underlying proposals as required by the ordinary commitment-proof recovery path. Thus the concrete MVBA's internal Commit round also serves as the fallback commitment-certification round." (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff") |
| the MVBA's side | "upon receiving a valid `CommitQC` … if `DecidedQC_i = ⊥`: `Decide(CommitQC)`" (Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)); every correct validator decides within `2Δ_R + Δ` of the first learner (Supplement, Lemma 13 (`lem:decision-propagation`)) |
| the recovery path | "A correct validator finalizes only the proposal vector `recoverProposals(entries(B))` (Algorithm 6, line 14 (`line:da-recover-slot`)) for a meta-block `B` whose entries are backed by a commitment proof it holds" (Lemma 9 (`lemma:chorus-agreement`), proof) |
| model | a correct validator `i` that holds a valid MVBA certificate `c` recovers a matching representation `v` (`mvba.certifies mvba_st c (mvba.entries v)`), checks the certificates `v` names, and records the certified entries (`on_mvba_commitqc_pos` / `_neg`). It then commits and finalizes them by the ordinary `commit_assign_*` / `finalize_commit`, whose certificate disjunct gains "a valid MVBA `CommitQC` exists" |

The re-broadcast is folded into the handoff, as the decision broadcast is
today: a certificate is transferable and stays valid, so its existence is
its availability to every validator, and nothing is written. The handoff
into the MVBA (`accept_mvba_commitqc`) is unchanged. The main body's
`fbCommitQC` route stays.

**(b) The new actions.** Two handlers and one guard disjunct.

```lean
ghost relation mvba_commitqc := ∃ C E, mvba.certifies mvba_st C E

action on_mvba_commitqc_pos (i : node) (j : node) (m : merkle_root) (c : mmsg) (v : mvalue) {
  require ¬ is_byz i
  require is_proposer j
  -- `i` holds a valid commit certificate, and `v` is a representation of
  -- its entries whose entry for `j` is `m` (`Recover(e)`).
  require mvba.certifies mvba_st c (mvba.entries v)
  require mval_pos (mvba.entries v) j m
  -- The bridge, as at the decision handlers: the certificate `v` names for
  -- the entry verifies against the network.
  require (¬ mval_fb v j ∧ vote_quorum_pos j m) ∨ (mval_fb v j ∧ fb_quorum_pos j m ∧ fbcert)
  require ¬ local_mvba_recorded i j
  mvba_decided_pos j m := true
  local_mvba_recorded i j := true
}
-- on_mvba_commitqc_neg (i j c v): the same with `mval_neg` and the
-- negative bridge of `on_mvba_decide_neg`.
```

`commit_assign_pos` requires
`msg_commitqc_pos j m ∨ ((fbcommitqc ∨ mvba_commitqc) ∧ mvba_decided_pos j m)`
(was `… ∨ (fbcommitqc ∧ mvba_decided_pos j m)`), and `commit_assign_neg`
likewise. `finalize_commit` is unchanged.

* **The records stay shared and keep their meaning**, "the agreed
  entries". They now have two sources: a correct validator's decision, and
  a valid certificate. The new handlers write the records the decision
  handlers write, so every invariant downstream of the records
  (`*_backed`, `*_chunks_decodable`, `*_proposer_signed`, the
  commitQC-consistency invariants, proposal inclusion, speculative safety)
  keeps its statement and now covers the route. A separate pair of records
  would duplicate about twenty of them.
* **Why a handler, and not only the guard disjunct.** A certificate can
  exist before any correct validator decides (the adversary aggregates
  `2f+1` `Commit`s), and the paper's validator finalizes on it then. With
  only the disjunct, finalization would wait for a correct decision's
  records. The handler records from the certificate itself.
* **Reads.** All positive. `mvba.certifies` is oracle state read in
  positive position (category (A) of [ChorusDesign.md](ChorusDesign.md)
  §3.5), and the ghosts and `mval_*` are read as at the decision handlers.
  The one negative read is the fired-once record `local_mvba_recorded i j`,
  which is local state (category (L)). No network relation is read
  negatively, so the §3.1.1 audit gains no entry.
* **Parameters**: 5 and 4.
* **Fired once.** `local_mvba_recorded i j` is shared with the decision
  handlers: a validator records entry `j` once, from whichever source comes
  first, and both sources write the same value (`mvba_decided_pos_unique`).
  Every firing sets the record, so `Chorus.justice_enabledMove` keeps its
  proof.
* **Gates.** `¬ is_byz i` and `is_proposer j`, as at the decision handlers.
  **No phase gate**: the target's rule has none ("A correct validator that
  receives a valid such certificate re-broadcasts it and finalizes",
  Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and
  handoff"), so the sketch above loses its `require phase = post_mvba_arm`
  (see "The MVBA-arm gates" below). `mvba_invoked` is **not** required: a
  validator on the fast path that receives a `CommitQC` finalizes on it,
  and no safety invariant relies on the condition. There is no
  participation gate, because the handler only processes, like the
  decision handlers. `commit_assign_*` and `finalize_commit` keep theirs.
* **Liveness classification.** Both handlers are honest labels, so they
  are under (F-justice). Their `Owed` is the handoff's `relayOwed` ("a
  correct validator has decided", and Chorus broadcasts that decision's
  certificate). The premise asks nothing on a certificate the adversary
  assembled and showed to nobody (F5). `Owed` of `commit_assign_*` is
  unchanged, so the liveness argument keeps the main body's route, and S4
  is unaffected.

**The bridge is the existing one, at one more site. This is for Lars.**
The route needs the certificate check on the recovered `v`, and there is
no way around it. Chorus's agreement with the fast path needs the
certified entries' certificates to be genuine. The contract's only
statement about a certified entry vector's certificates is
`certified_valid` (`Valid v` for some representation), and `Valid` is a
predicate fixed before Chorus's network exists. That is exactly the gap
the decision handlers' bridge closes. The route uses the same statement
("a valid meta-block's certificates verify against the network") with the
same soundness argument: the check removes no real behaviour, because
`Recover(e)` returns a valid representation (`certified_valid`) and a valid
one passes it. The content of the trust-base item does not change. Its
sites become the two decision handlers and the two route handlers, and its
wording in [CompositionContracts.md](CompositionContracts.md) §3/§7 and
[Architecture.md](Architecture.md) §4 says "at the decision handlers and
the `CommitQC` route". **No second bridge is needed for data
availability**, although §5.7 expected one: the route's DA follows from
the same check, through `mvba_decided_pos_chunks_decodable` (see (e)).

**(c) `AvailReady`: an MVBA input that Chorus drives.** The target makes
the DA layer the source of availability. `AvailReady_i(x)` holds "if, for
every positive entry `⟨s, j, ρ⟩` of `x` that is certified by a
`FallbackQC`, validator `p_i` holds its assigned availability share for
`ρ`", and "the MVBA treats availability synchronization as a service of the
composing dissemination and ChunkSync layer" (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Commit availability condition" and
"Availability-synchronization assumption"). So `become_avail_ready`
becomes the contract's fourth input, and Chorus drives it with the chunk
wait as its guard:

```lean
-- Interfaces.lean, MVBASafety
  markAvail : state → party → value → state → Prop
  markAvail_trans : ∀ st p v st', markAvail st p v st' → trans st st'
  markAvail_effect : ∀ st p v st', markAvail st p v st' → availReady st' p v
  markAvail_enabled : ∀ st p v, ∃ st', markAvail st p v st'           -- withheld
  init_availReady : ∀ st p v, init st → ¬ availReady st p v
  availReady_frame : ∀ st st' p v, ¬ byz p →
    (step st st' ∨ (∃ q w, propose st q w st') ∨ (∃ q, abandon st q st') ∨
      (∃ q c, accept st q c st')) → (availReady st' p v ↔ availReady st p v)

-- Chorus.lean
action mvba_avail_ready (i : node) (v : mvalue) (mvba_next : mstate) {
  require ¬ is_byz i
  require ∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → msg_chunk_received i J M
  require ¬ local_avail_marked i v
  require mvba.markAvail mvba_st i v mvba_next
  mvba_st := mvba_next
  local_avail_marked i v := true
}
```

* **On the MVBA side the model does not change.** `become_avail_ready` is
  already an unguarded action, and the instance classifies it as an input
  (`Label.isInput` in [Mvba/Compose.lean](../Cadence/Mvba/Compose.lean),
  and `InputLabel` in place of `AvailLabel` in
  [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)). (F-avail) stays a
  premise of `Mvba.termination`, now as a caller's premise beside
  `AllPropose`. The Mvba family stays warm. The instance proofs,
  `Mvba.Liveness`, `Mvba.Temporal` and the Mvba witnesses re-check in plain
  Lean.
* **On the Chorus side the premise `MvbaAdmissible` loses `Mvba.FAvail`.**
  `Chorus.termination` derives it instead, as it derives `AllPropose`. The
  derivation uses (F-justice) on the new family (per validator and value,
  with `Owed` true, since it consumes only the validator's own chunk
  receipts), and the chunk under a `FallbackQC` entry reaches `i` by
  `redisseminate_chunk` from the entry's correct signer (`Owed` is
  `msg_fb_pos_sig k j m`, F14). The derivation needs the accepted value's
  `FallbackQC` entries to be genuine. That is the bridge's completeness
  direction at an **accepted** value, and `ValidBridge` states it today at a
  decided one. So `ValidBridge`'s second clause is extended from decided to
  accepted values. **This is a premise change, for Lars.** In the timed
  claim ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)), the
  `Mvba.AvailWithin` premise is replaced by a δ-row for the new family.
  That is a statement change; the proof is S4's. The three Chorus witnesses
  fire the new family where the MVBA's environment marked availability
  before.
* **What this buys.** The supplement's `Δ_sync` assumption becomes a
  consequence of Chorus's rows (§8, R16's "to decide"). One premise of the
  composed liveness claim is removed and one is extended.
* **The alternative** is to keep `AvailReady` the MVBA's environment
  relation. It needs no bridge either (by (e)), and it costs nothing in
  Chorus's liveness. But (F-avail) then stays an assumption, in the
  composed system, about a step that is Chorus's own. It has one action and
  one invariant fewer: `#veil_status Chorus` is then 5046 instead of 5199.

**(d) Fields that reach the solver.** The new cells read
`certified_unique` (two certificate-sourced records), `certified_decided`
(a certificate-sourced record against a decision-sourced one), the new
`certified_mono` (the certificate tie survives every transition, below)
and, for (c), `markAvail_trans`, `markAvail_effect`, `init_availReady` and
`availReady_frame`. All of them are universally quantified implications,
so they are first-order. They leave `veil_smt_ignore`, or are added
outside it. `decided_certified`, `accept_effect`, `accept_enabled`,
`certified_valid`, `certified_available` and the new `markAvail_enabled`
stay withheld: each has an `∃` in its conclusion, and no cell reads it.

```lean
  certified_mono : ∀ st st' c e, trans st st' → certifies st c e → certifies st' c e
```

`certified_mono` is new: "a valid certificate stays valid", which is what
makes it transferable. `Mvba.mvbaSafety` proves it from the generated
monotonicity of `msg_commitqc`. Together with (c) this is the one contract
edit of R16. Nothing is weakened.

**(e) Invariants.**

* **Restated: the tie invariants.** A record is now the projection of a
  correct decision *or* of a valid certificate:

  ```lean
  invariant [mvba_decided_pos_tied]
    ∀ J M, mvba_decided_pos J M →
      (∃ I V, ¬ is_byz I ∧ mvba.decided mvba_st I V ∧ mval_pos (mvba.entries V) J M) ∨
      (∃ C E, mvba.certifies mvba_st C E ∧ mval_pos E J M)
  ```

  The negative form is the same. Uniqueness of the records then follows
  from `agreement` (two decisions), `certified_decided` (a decision and a
  certificate) and `certified_unique` (two certificates). The ties are read
  nowhere outside [Chorus.lean](../Cadence/Chorus.lean).
* **Agreement of the route with the fast path and with the `fbCommitQC`
  route needs no new invariant.** Every route finalizes either on
  `msg_commitqc_*` or on a record, and the existing invariants relate the
  two: `local_committed_pos_unique`, `local_committed_pos_neg_excl`,
  `commitqc_pos_mvba_consistent` and its two exclusion siblings, then the
  `safety` statements `agreement_pos` and `agreement_pos_neg`. Their cells
  at the new handlers are the decision handlers' cells, from the same
  bridge evidence. The four manual cells there (two per handler) are
  mirrored.
* **DA on the route needs no new invariant either.**
  `local_committed_pos_implies_decodable` covers the route through
  `mvba_decided_pos_chunks_decodable`, which follows from the bridge
  evidence as at the decision handlers.
* **New, for (c): what `AvailReady` means.**

  ```lean
  invariant [avail_ready_chunks]
    ∀ I V J M, ¬ is_byz I ∧ mvba.availReady mvba_st I V →
      mval_pos (mvba.entries V) J M → mval_fb V J → msg_chunk_received I J M
  ```

  With `certified_available`, this turns §5.7's reading of the R15 field
  in Chorus's vocabulary from a stated bridge into a theorem. A certified
  entry vector has a supermajority whose correct members each received
  its assigned chunk under every `FallbackQC` entry of its own
  representation. That is a plain-Lean corollary,
  `Chorus.certified_available_chunks`.
* **P2.** The proofs assume no common `B′`. Records and certificates are
  over entries, and the bridge is per representation. The agreement case
  P2 says the main body omits, a `CommitQC` against a fast `commitQC`, is
  `commitqc_pos_mvba_consistent` at the new handler. It is proven by the
  main body's fast-path argument (vote-quorum intersection, and the
  `FBCert`/commit intersection), not by Part I's conditional sentence. P2's
  representation divergence does matter for
  `Chorus.certified_available_chunks`: two `Commit` signers may have waited
  under different certificate kinds for one root. So the corollary is
  stated per signer's own representation, and for a root a signer held by
  a `FastQC` the chunks come from the vote quorum instead.

**The MVBA-arm gates.** Before R16, four actions required
`phase = post_mvba_arm`: `on_mvba_decide_pos`, `on_mvba_decide_neg`,
`mvba_terminate` and `cast_fb_commit`. The target's rules have no such
gate. The decision handler is "upon `MVBA[s].decide(B′)`" (Algorithm 5,
line 37 (`line:fb-mvba-decide`)), and the receipt rules are "upon
receiving a valid `fbCommitQC`" (Algorithm 5, line 45
(`line:fb-recv-commit`)) and the supplement's sentence quoted under
"Gates". `Ds + 2Δ` gates only the case-1 *proposal* (Algorithm 5, line 23
(`line:fb-mvba-propose-fast`)), and the case-2 proposal needs only
`2f+1` fallback votes, which exist from `Ds + Δ` on. So a paper validator
can decide, cast its fallback commit vote and hold a `CommitQC` before
`Ds + 2Δ`, and the gate delayed all of that to the MVBA arm. That is a gap
of the same kind as the new handlers' gate, and R16 closes both: none of
the four existing actions and neither new handler has a phase gate. The
remaining phase guards are the target's own: the deadline (`propose`,
`record_chunk`, `vote`), the fallback arm (`fb_sign_*`,
`cast_fallback_vote`), and the two triggers of `mvba_propose`.

*What dropping the gates breaks, by analysis* (the trial build waits for
the go-ahead on the model edit). Exactly three invariants state the gate
and so fail by construction: `mvba_decided_phase` (records exist only at
the MVBA arm), `fbcommit_sig_phase` and `mvba_complete_phase`. Each is
restated as `phase ≠ pre_deadline`, and in that form it follows from the
bridge evidence every record carries. A positive record has a vote
quorum, or a `FallbackQC` under `FBCert`. A negative one has a negative
vote quorum, or `FBCert`. Each of these contains a correct signer, whose
signature postdates the deadline (`voted_post_deadline`, `fb_sig_phase`).
`mvba_complete` and an honest fallback commit vote come after records.
Only the deadline is needed, by the one consumer: proposal inclusion uses
`mvba_decided_phase` to show that `all_honest_recorded`, which can only
become true before the deadline (`record_chunk`), never becomes true after
a conflicting record exists. `mvba_complete_phase` was the phase leg of
`cast_fb_commit`'s enabledness, which no longer has one. No file outside
[Chorus.lean](../Cadence/Chorus.lean) reads the three, so the plain-Lean
liveness proofs are unaffected. Their frames cover the new labels, and
the derivations that stepped through the MVBA arm only lose a premise.
No monotone-network exception is needed, since a gate removed is a guard
removed. The restatement keeps every count, so (f) is unchanged. What
analysis cannot settle is whether a cold solve finds the restated
invariants' cells at the four actions. If one diverges, it is made manual
from the derivation above, and if one turns out false, the counterexample
is reported before anything else changes.

**(f) The pins, written down before the build.** Cells are
`(A + 1)(I + 1) + A·S`.

* `#veil_status Chorus`: `A = 46 + 3 = 49` (`on_mvba_commitqc_pos`,
  `on_mvba_commitqc_neg`, `mvba_avail_ready`), `I = 101 + 1 = 102`
  (`avail_ready_chunks`), `S = 1`. **`50 · 103 + 49 = 5199`**, which is
  `4840 + 3 · 103 + 1 · 50`. Each new action adds one cell per property and
  step property plus its does-not-throw cell (`102 + 1`), and the new
  invariant adds one cell per action and one at the initializer
  (`49 + 1`). Without (c): `A = 48`, `I = 101`, `49 · 102 + 48 = 5046`.
* `#veil_status Mvba`: 1507, warm (no model change).
* `#veil_status FallbackReceipt`: 220, warm.
* A helper invariant found during the cold solve costs `A + 1 = 50` cells,
  and is recorded as a plan change.

**(g) What the cold solve found, and what was decided** (after the
go-ahead; Lars's decisions relayed by the coordinator).

* **The MVBA-arm gates were our modelling error**, not a paper finding.
  The target is clear that the decision handler runs "upon
  `MVBA[s].decide(B′)`" with no time condition (Algorithm 5, line 37
  (`line:fb-mvba-decide`)). The four gates are dropped, and the new
  handlers have none.
* **Two helper invariants are deleted**: `mvba_complete_phase` and
  `fbcommit_sig_phase`. Without the gate they are false. With no
  proposers, `complete_fast_metablock` holds vacuously, so `mvba_invoked`
  holds before the deadline. The contract lets a correct decision appear
  there, and `mvba_terminate`'s per-proposer check is vacuous, so
  `mvba_complete` and then a fallback commit vote can precede the
  deadline. Proving the helpers would need "a correct party decides only
  after proposing". Module 3 (`mod:mvba`) does not state that: its
  interface says only that `propose(B)` is how a validator "thereby
  start[s] to participate", and its Quiescence covers messages, not
  outputs. So the helpers relied on more than the module promises, and
  deleting them is correct. Nothing consumed them: their one use was the
  phase leg of `cast_fb_commit`'s enabledness, which no longer exists.
  `mvba_decided_phase` stays, in the form `phase ≠ pre_deadline`, because
  a record carries a certificate whose correct signers postdate the
  deadline.
* **One contract frame was missing**: `availReady_markAvail_frame` (the
  report concerns its own party and representation). Without it
  `avail_ready_chunks` failed at `mvba_avail_ready` (❌). It is first-order,
  and `Mvba` proves it from the transition body.
* **`markAvail_enabled` is not a contract field.** No Chorus cell reads
  it, and the monitor's silent stub, whose state is `Unit`, could not
  satisfy it together with `init_availReady`. The one liveness proof that
  needs the input to be enabled runs at the `Mvba` instance, where
  `become_avail_ready` is unguarded.
* **The availability report is owed for a meta-block the validator holds**
  (`availOwed i v := ∃ w, accepted i w v`, at the `Mvba` instance). The
  supplement's assumption is about "a correct validator `p_i` [that]
  holds a valid meta-block `x`". Owing the report for every
  representation would make (F-justice) demand reports nobody makes.
* **(Δ-avail) stays assumed inside `TimedMvbaAdmissible` until S4 derives
  it.** The timed premise gains the δ-row (`TimedJustice.avail`).
  Deriving the MVBA's timed clause from it and from the re-dissemination
  rows is a timed proof of the `relayed_of_timedJustice` kind, and it
  belongs to the bounds leg ([TODO.md](TODO.md) § Liveness). The untimed
  (F-avail) is derived (`fAvail_of_fJustice`) and has left
  `MvbaAdmissible`.

**(h) The interface check.** Each R16 addition, against what Module 3
(`mod:mvba`) and the supplement's concrete MVBA expose:

| addition | exposed by the target? | verdict |
|---|---|---|
| `AvailReady` as an input (`markAvail` and its frames) | not by Module 3 (`mod:mvba`); the supplement defines it over the dissemination layer's shares and calls synchronization "a service of the composing dissemination and ChunkSync layer" | the composition needs more than the abstract module states: P12 |
| `availOwed` and `ValidBridge`'s accepted clause, reading `accepted` | neither document exposes the MVBA's `x_v`; the supplement's `Δ_sync` is stated over it | the same seam, P12. Read at the system's instance; no class field carries it |
| `certified_mono` | the commit certificate is the supplement's strengthened interface ("serves as a transferable commitment proof"); transferability is persistence | stated by the supplement, not extra |
| the certificate bridge at the route | `Valid` is "publicly verifiable" in both documents; the bridge says what a valid certificate means in a network of relations | the existing bridge, one more site, not extra |

P12 does not break the claimed abstraction for **safety**. The safety
proofs read the MVBA only through the contract, and the `AvailReady`
input changes no safety statement of the MVBA. It does for **liveness**:
the main body's `ℓ_MVBA` is a constant of a self-contained module, while
the supplement's depends on the composing layer's `Δ_sync`, triggered by
MVBA-internal state. The model states that dependency rather than hiding
it.

**(i) The pins, after the build.** `A = 49`, `I = 100` (101 + 1 new − 2
deleted), `S = 1`: **`50 · 101 + 49 = 5099`**. `#veil_status Mvba` 1507
and `#veil_status FallbackReceipt` 220, both warm.

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
* **Paper commits after the target.** At R17 (2026-10-02) the paper
  repository's `master` was `48cac9a` itself, after a fetch: there is no
  later commit for the next cycle to read yet. A later commit is listed
  here, with a one-line summary, by the session that finds it; it does not
  move the target (§0).
