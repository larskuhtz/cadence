# Paper alignment — the target revision, the review against it, and the plan

*What an auditor asks first: the models claim to verify the Cadence paper,
but which paper, and is it still that paper? §0 names the target revision.
§1 gives the mechanical check anyone can re-run against it. §§3–5 hold the
review of what the models rest on, item by item. §6 lists what the review
found on the paper side. §8 is the plan that brings the models onto the
target. Earlier comparisons, against arXiv v2 and the supplement at
`eb1bb51`, are recorded in [History.md](History.md) § "Paper alignment
before the single target".*

## 0. The target

The development targets **one revision of the paper repository: `48cac9a`**
(`48cac9a41efac2fb58f32f61ff21fd89db7c7d98`, branch `master`, committed
2026-10-02 00:40 UTC, frozen on 2026-10-01 in session R13). The target is
the revision as a whole: the main body (`main.tex` and `src/*.tex`, the
paper whose arXiv versions are `2607.02275v1`/`v2`) and the internal
supplement (`supplementary-internal.tex` with
`src/supplementary-internal/`). Claims are stated about that revision, and
a protocol bug found here is a bug in that revision.

**Status: realignment in progress.** The models do not yet correspond to the
target. Chorus, the Conductor, the glue and the receipt layer were built
against arXiv v2, and the MVBA against the supplement at `eb1bb51`. That
earlier target is marked by the tag `paper-target/arxiv-v2`. §§3–5
classify every difference between it and `48cac9a`. Four items need model
changes, two need contract changes, and the rest need nothing or only
documentation. §8 is the plan that closes them. Its last session makes the
tag `paper-target/48cac9a` and changes this paragraph to "corresponds".

The target does not follow the paper repository's `master`. A later paper
commit is a new target only when a session moves it, by running §1 against
the new commit and planning the difference as §8 does.

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

**Result at the target** (2026-10-02, R14). The map has every label of the
two documents, and every citation outside the two frozen records checks
against it. The citations of [Interfaces.lean](../Cadence/Interfaces.lean)
and [System.lean](../Cadence/System.lean) are checked for their labels only:
their rendered references are added in R15, the session that edits those
files (§8).

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
| S6 | (in full) The MVBA's value is a meta-block *with its certificates*; `decide(x, CommitQC)` outputs one representation `x`; Agreement and Integrity are over `entries` ("Agreement and Integrity over entries") | (b) | The model's value is the bare entry vector, so a validator's decision carries no certificate kinds. The value becomes the representation (entries plus each entry's certificate kind). §5.5 |
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
items, which the plan in §8 carries out:

* **(b) M3.** `Primitives.ErasureCoding` decodes from indexed fragments.
* **(b) S6, with F13.** The MVBA's value is the representation: an entry
  vector together with each positive entry's certificate kind. Chorus's
  decision handlers record the validator's own representation, and
  `cast_fb_commit` waits exactly under the `FallbackQC` entries of its own
  `B′`.
* **(b) S7.** `AvailReady` is indexed by the representation.
* **(b) S8.** Chorus finalizes on a valid MVBA `CommitQC`, as well as on
  the `fbCommitQC`.
* **(c) M9/S6.** `MVBASafety` gains an `entries` projection. Agreement and
  Integrity are stated over it, in the supplement's forms.
* **(c) S8.** `MVBASafety` gains the certificate-level facts the second
  route needs: a certified value agrees with every correct decision, is
  `Valid`, and comes with the availability its correct `Commit` signers
  established.

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

For the model: today `MVBASafety.integrity` is `decided p v → decided p v' →
v = v'` over the entry vector, which is the supplement's form. Once `value`
is the representation (§5.5), the same sentence would say "at most one
representation". That is stronger than the supplement, which permits
redelivery with a different representation after a restart. **Class (c):**
Integrity is stated over `entries`, like Agreement. The instance keeps
proving the strong form, since the model has no crashes and a decided
validator halts.

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

**What the model does today.** The class's `value` is the bare entry
vector, so a decision carries no certificate kinds. Since R12,
`cast_fb_commit` reads "held by a `FallbackQC`" as "no positive `FastQC`
exists for it". The two readings differ only for a root that has both
certificates, while the validator's own `B′` carries the `FallbackQC`. The
model does not wait there, and the paper's validator does. That is F13
([Bounds.md](Bounds.md) §6.4.2).

**F13 is an artefact of the hybrid target.** Under v2, Module 3 (`mod:mvba`)'s
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
**Classes (b) and (c)**, §8 R15. On the paper side there is a related
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

**What the model does today.** It has the main body's route, plus Part I's
handoff of the certificate into the MVBA (`accept_mvba_commitqc`, R8). It
does not finalize on the MVBA's certificate.

**What realignment does** (§8, R16). Chorus gains Part I's route: a correct
validator holding a valid MVBA `CommitQC` for `e` finalizes `e`. Its
re-broadcast is folded into the handoff, as the decision broadcast is
today. The main body's route stays. The model then has every run of the
specified protocol, and every run of the Part II implementation as far as
safety goes, since that implementation is the specified protocol without
the `fbCommitQC` route. Safety needs the route's agreement with the fast
path and with the `fbCommitQC` route. These are the fast-path argument of
Proposition 1 (`prop:agreement-entries`) (no valid fallback meta-block exists once `f+1`
correct validators cast a fast commit vote) and MVBA agreement. Both are
available once the contract states that a certified value is agreed and
`Valid` (§4, (c) S8). Data availability on the new route needs the
contract to export `AvailReady`'s guarantee to Chorus. The guarantee is
that each positive entry of a certified `e` is either `FastQC`-backed
somewhere or was waited for by the `f+1` correct `Commit` signers. This is
a second stated bridge, beside the certificate check at the decision
handlers. Liveness keeps the main body's route and the paper's bound.
Proving a bound through the `CommitQC` route as well is optional, and
records how the implementation's latency compares.

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

## 6. Paper-side findings at the target

For the paper's authors. Each item quotes the target `48cac9a` and names
anchors. P1–P4 are inconsistencies between the main body and the supplement,
or within one of them. P5–P6 are carried from earlier reviews and
re-checked. P7–P10 are smaller.

**P1. Module 3 (`mod:mvba`) Integrity was not revised with Agreement.** The supplement
(Supplement, Section 1.2 (`subsec:mvba-protocol`), "Agreement and Integrity over entries"): "*Integrity:* all decision outputs
of a correct validator carry the same entry vector, and redelivery of a
decision with that entry vector, for instance after a restart, is permitted
… The abstract module in the main paper should be revised to these forms".
Module 3 (`mod:mvba`): "*Integrity:* Every correct validator
decides at most once." `d598c5a` revised Agreement only. The main body
uses the at-most-once form in Proposition 1 (`prop:agreement-entries`): "A correct validator
sends a single fallback commit vote — one per MVBA decision …, and the MVBA
decides at most once by its integrity property". Under the supplement's
Integrity, a redelivery could trigger a second fallback commit vote, so the
argument should say that all of a correct validator's fallback commit votes
carry the same entries. That is true under the revised Integrity, and it is
what the argument uses.

**P2. The main body's proofs argue from a common `B′` and from one fallback
commitment proof.**
* Proposition 5 (`prop:chorus-finalization-time`): "by the MVBA's agreement and external
  validity, they all decide the same valid meta-block `B′`". Since
  `d598c5a`, Module 3 (`mod:mvba`)'s Agreement gives only `entries(B) = entries(B′)`.
  The proof goes on to use one `B′` for all validators: "each holds its
  assigned chunk for every positive `FallbackQC` of `B′`", and "for every
  `FastQC` entry of `B′` …; for every positive `FallbackQC` entry, the `f+1`
  correct commit voters' re-broadcast chunks arrive by `T`". When
  representations differ, a root can be `FastQC`-backed for one validator
  and `FallbackQC`-backed for another. The conclusion still holds: a
  `FastQC` puts the chunks of `f+1` correct voters on the network, and
  under a `FallbackQC` the waiting validators re-broadcast. But the proof as
  written relies on the Agreement the module no longer states.
* Proposition 1 (`prop:agreement-entries`) enumerates two kinds of commitment proof, the
  fast `commitQC` and the `fbCommitQC`. At the target, supplement Part I
  adds a third: a valid MVBA `CommitQC`, on which a correct validator
  finalizes (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"). Its agreement with the fast
  path and with the `fbCommitQC` is argued only as "a fallback decision
  agrees with a fast-path commitment whenever the two certify the same entry
  vector" (Supplement, Section 1.2 (`subsec:mvba-protocol`)). That sentence is conditional, and it is
  not the fast-path argument the main body gives for its second case.
  Either the main body takes the route in (Module 3 (`mod:mvba`)'s `decide` with a
  certificate, a finalize rule in Algorithm 5 (`alg:fallback`), a third case in
  Proposition 1 (`prop:agreement-entries`)), or Part I presents it as an implementation
  variant, as Part II does. As written, the specified protocol has a
  finalization route the paper's agreement proof does not cover. §5.7 has
  the model side.

**P3. `EquivCert` construction, contradicted within the supplement.**
Supplement, Section 7.4 (`sec:fallback-transition`) (item 2): "the two validated witness chunks
themselves provide the conflicting proposer-signed roots required to
construct an `EquivCert`; two conflicting positive fallback entries are not
required." Supplement, Section 7 (`sec:implementationnotes`), "Record equivocation evidence even without
slashing": "the
`EquivCert` rarely becomes public, since `EquivCert`s are assembled only when
an MVBA input is built from two conflicting positive fallback entries". The
second sentence matches the main body (Algorithm 5, line 29 (`line:fb-build-equiv`)), and the
first replaces it. Unchanged since the 2026-09-03 review. Relatedly, the
main body's "one of the three cases always applies, by counting"
(Algorithm 5, line 26 (`line:fb-build-entry`)) is argued over the first `2f+1` fallback votes. The
supplement's replacement argument (Supplement, Section 7.4
(`sec:fallback-transition`), "Fallback-entry certifiability") needs
entries evaluated continuously over all votes, and witness chunks. The two
certifiability arguments are for two different rules.

**P4. Part I relies on a Part II argument.** Supplement, Section 1.2 (`subsec:mvba-protocol`)
(Part I): "`propose(B_i)` requires `B_i` to be a valid meta-block for `s`;
the composing Chorus fallback transition establishes that every correct
validator eventually holds one (Supplement, Section 7.4 (`sec:fallback-transition`))". The cited
section is Part II's implementation variant (P3). For the main body's
protocol, the precondition is established by Algorithm 5 (`alg:fallback`)'s counting
argument (Algorithm 5, line 26 (`line:fb-build-entry`)) instead.

**P5 (F4, carried). Lemma 11 (`lemma:chorus-termination`) claims `5Δ + ℓ_MVBA` where its
proof gives `4Δ + ℓ_MVBA`.** Re-checked at the target: the lemma is
byte-identical to v2. It splits at `T₀ = max(t, GST) + 4Δ + ℓ_MVBA` and adds
totality's `Δ` in the first case. The inner split of
Proposition 5 (`prop:chorus-finalization-time`) at `T₀ − Δ` already handles early
finalizers, so a single split gives `M + 4Δ + ℓ_MVBA`. A commented-out
draft next to the lemma states that bound. The model-side decision is S4's
([Bounds.md](Bounds.md) §6.4.3). The claim is stated at the paper's `5Δ`,
which follows by monotonicity, and the sharper bound is a named lemma.

**P6 (carried). When does an `upon` handler run?** Algorithm 4 (`alg:fast-path-certification`)'s
Algorithm 4, line 18 (`line:fast-formqc`) and Algorithm 4, line 31 (`line:fast-collect-commit`) are `upon` rules without
"first time", and only the fast meta-block rule says "first time". Neither
document states a convention for `upon`. Re-checked at the target:
the source of Algorithm 4 (`alg:fast-path-certification`) is byte-identical to v2. The supplement's execution-model
paragraph covers MVBA handlers only. The model reads an `upon` handler as
running once, when its condition becomes true ([Bounds.md](Bounds.md)
§6.4.7; the "Fired-once records" of [Chorus.lean](../Cadence/Chorus.lean)).
The MVBA's rules say so explicitly ("has not already formed …", "upon first
collecting …"). A one-line convention in the main body would settle it.

**P7. `supplementary-internal-bkp.tex` is still in the tree.** It
duplicates labels and misleads any grep-based anchor audit (§1).

**P8. The Supplement, Section 10.1 (`sec:timing-constants`) stub still lists "the MVBA view timeout and
its backoff policy"**, while Supplement, Section 1.2 (`subsec:mvba-protocol`) fixes the timeout at
`T := Δ_R + 4Δ + max{Δ, Δ_sync}` and Supplement, Theorem 2 (`thm:termination`) counts with it.

**P9. The practical Conductor's parameter range.** The relation lemmas of
the practical Conductor (Supplement, Section 3 (`sec:practical-conductor`),
"Relation to the Cadence Proofs") use "Since
`2 ≤ p ≤ W−1`" twice. The main body's Conductor has `p ∈ {0, …, W−1}`
(Appendix D (`section:conductor-formal`), Algorithm 7 (`algorithm:conductor`)). The restriction is not
stated as an assumption of the practical Conductor, so its relation to
Algorithm 7 (`algorithm:conductor`) covers only `p ≥ 2`, and it does not say so.

**P10. Algorithm 6 (`alg:da`)'s re-encode check and the proposer's encoding.** At the
target both use positional leaf hashes. That makes v2's Algorithm 6 (`alg:da`)
inconsistent with v2's Algorithm 2 (`alg:proposer-dissemination`), an inconsistency the
target fixes. It is recorded because v2 is the public version: a v3 would
carry the fix.

**No item of the target is unmodellable.** Every protocol rule of the main
body and of Part I's MVBA can be modelled faithfully within the
monotone-network contract, with one exception that predates this review:
the MVBA's "enter the view of the highest retained timeout certificate"
(C7 of [MvbaPlan.md](MvbaPlan.md) §11.3) needs a negative network read, and
the model over-approximates it, which is sound for safety and unused by
liveness.

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

## 8. The realignment plan

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
* **The citation check is not in CI.** CI's settings were not changed in
  R14. The check needs Python only (the map is committed, so `tectonic` is
  not needed), and running it beside `scripts/site-links.sh check` is
  proposed for the next session that edits CI.
* **R17's anchor re-check** is §1's check: regenerate the map at the new
  pin and run the citation check.

**R15 · The meta-block representation, and the contract.** The one
Interfaces.lean edit, together with every model change it needs.
* **Contract (c).** `MVBASafety` gains an `entries` projection from
  `value`. Agreement and Integrity are stated over it, in the supplement's
  words (M9, S6, §5.4). It also gains the certificate-level fields of
  §5.7: a certified value's entries equal every correct decision's, a
  certified value is `Valid`, and the availability bridge. The
  `veil_smt_ignore` discipline applies to any field the Chorus cells do not
  need.
* **Mvba (b).** The value carries each positive entry's certificate kind
  (S6). `Prepare`/`Commit`/certificates stay over entries. A decision
  outputs a representation with the certified entries (`Recover` as a
  choice among valid representations). `avail_ready` is indexed by the
  representation (S7).
* **Chorus (b).** The decision handlers record the validator's own
  representation, and `cast_fb_commit` waits exactly under its own `B′`'s
  `FallbackQC` entries. This closes F13 with no residual (§5.5).
  `mval_pos`/`mval_neg` read through `entries`.
* **System.lean** re-instantiates at the new value type.
* **Citations** of Interfaces.lean and System.lean move to the rendered
  form, and `scripts/paper-cites.sh` drops its exemption for them (R14's
  plan change).
* Families cold: **Mvba** (with `Mvba/NoLock.lean` re-run; its pinned
  witness must survive or be re-pinned with the reason recorded) and
  **Chorus**. FallbackReceipt, Cadence and Conductor stay warm.
* Pins move, and the new counts are written down before the build:
  `#veil_status Mvba` and `#veil_status Chorus`. FallbackReceipt stays at
  220.
* Re-established:
  * `Mvba.mvbaSafety`, `Mvba.termination`, `Mvba.bounded_termination`,
    `Mvba.mvbaTemporal` and the Mvba witness;
  * `Chorus ⊨ SlotConsensusSafety`, `Chorus.termination`, the Chorus
    timed milestones, Totality and the Chorus witness;
  * System.lean's end theorems and every axiom pin in
    [Cadence.lean](../Cadence.lean);
  * the monitor decoders for the changed actions.
* Size: probably two sessions on one branch, since the Mvba side and the
  Chorus side can be proven in sequence before the PR.
* F13: closed. F14: closed in R14. S4: re-based on the new model. Its
  fallback commit round rows owe `cast_fb_commit` under its own `B′`, and
  the F13 residual it excluded is gone.

**R16 · The `CommitQC` finalization route (S8).**
* Chorus gains Part I's route: a correct validator holding a valid MVBA
  `CommitQC` finalizes its entries, with the re-broadcast folded into the
  handoff.
* New invariants: the route agrees with the fast path and the
  `fbCommitQC` route, and has the DA property through the R15 bridge.
* Families: **Chorus** cold (a model change). Mvba stays warm, because the
  contract fields came in R15.
* Pins: `#veil_status Chorus` moves.
* Re-established: as R15 on the Chorus side.
* Option: bundle R16 into R15's Chorus re-solve if R15's Chorus side fits
  one session. The plan keeps them apart because R16's invariants are new
  safety work, and R15's are a re-statement.
* S4: unaffected (the paper's bound uses the main body's route).

**R17 · Close the realignment.**
* A full re-validation, and the four markers counted.
* The [Cadence.lean](../Cadence.lean) header, the README paper section
  and §0 here change from "in progress" to "corresponds to `48cac9a`".
* Anchors and references re-checked by §1 (the map regenerated, the
  citation check clean). Each model header's paper pin becomes
  `48cac9a`, with [Mvba.lean](../Cadence/Mvba.lean) moving from `eb1bb51`.
* Create and push the tag `paper-target/48cac9a`, with Lars's approval.

**After the realignment: the Chorus bounds leg resumes** at the stage it
stopped ([Bounds.md](Bounds.md) §6.4.6):

* **S4: the MVBA tail and the assembly.** `T.termination` through the
  projection, the fallback commit round (rows over the validator's own
  `B′`), the case split, and the bound. **F4 is decided here** (P5).
* **S5: the contract instances.** `SlotConsensusTemporal` at the new
  fragment (Quiescence, `admissible_exists`, Termination as the unbounded
  corollary), then `SlotConsensusWithTotality` and the `…_of_temporal` join
  with its `rfl` lemma. After that: the [Cadence.lean](../Cadence.lean)
  rows, and (A-sc-termination) moving from assumed to discharged.

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
