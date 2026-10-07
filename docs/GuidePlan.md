# Guide plan — the design of the Verso guide

*The design for growing the Verso guide ([CadenceGuide.lean](guide/CadenceGuide.lean))
into the entry point for every reader of this project. Written by session
D1 of the documentation line and revised after Lars's review: §3 is the
claims box as the front page will carry it, §10 records the decisions, and
everything else is the plan the sessions D2 onwards follow. This page is a
plan: once the last D session lands, it moves
to [History.md](History.md) as a pointer, and the guide and the README
describe the result.*

## Contents

1. [Information architecture](#1-information-architecture)
2. [Navigation by structure](#2-navigation-by-structure)
3. [The claims box](#3-the-claims-box)
4. [The running example](#4-the-running-example)
5. [Curated items from docs/](#5-curated-items-from-docs)
6. [The docs/ cleanup plan](#6-the-docs-cleanup-plan)
7. [Diagrams](#7-diagrams)
8. [Machinery the guide needs](#8-machinery-the-guide-needs)
9. [Session plan](#9-session-plan)
10. [Open questions](#10-open-questions)

## 1. Information architecture

### 1.1 Who carries what

| Layer | Reader | Carries | Authority for |
|---|---|---|---|
| **The guide** (site, `guide/`) | everyone who cares about the content: protocol researchers, auditors, verifiers | the claims, the structure of the proof, how to read a model and a contract, what has to be believed, short summaries of the curated lists, how the proofs are checked | nothing that changes often; every statement it shows is embedded from the compiled development, and every list it summarises links to its home |
| **README.md** (GitHub) | developers and maintainers | a landing section with pointers, then building, development, CI, the images, maintenance, citing the paper | how to build, develop and maintain |
| **docs/** | readers who dig deeper, and developers | the reference documents (premise ledger, findings, design rationale, contracts, bounds), the records (history, audit report) | each list and table it owns (§5) |
| **Rendered sources** (site, `sources/`) | readers who want the full model | every published module as written | the models, the statements |
| **Trust boundary** (site) | auditors, verifiers | the axiom footprint of every end result, and which contracts have an instance, derived from the compiled environment | itself (generated) |
| **[Cadence.lean](../Cadence.lean)** | verifiers | the end results and their axiom pins on one page | the axiom pins |

Links run one way where possible: the README lands readers on the guide;
the guide links down into docs/ and the sources; docs/ pages open with a
pointer back to the guide chapter that introduces them (§6). docs/ never
repeats what the guide says in full; it either owns a list or explains a
design.

### 1.2 Page map

The guide becomes a multi-page Manual, one page per chapter (§10, Q1).
Lengths are rough reading lengths, prose plus tables; embedded declarations
and status boxes come on top.

| # | Chapter | Sections | Length | Goal |
|---|---|---|---|---|
| 0 | **Cadence Verification** (the front page) | the claims box (§3); one paragraph on what the project is; the overview diagram; the chapter list with each chapter's opener (§2) | 700 words | 1 |
| 1 | **How the verification is built** | the approach in one paragraph (protocol models in Veil, proven by induction, composed through the paper's module specifications); the modules and their contracts (overview diagram, a table: paper module → contract class → model → instance); the composition: how a model consumes a contract and how instances fill it; where the paper fits (the target revision, the citation form); the four kinds of evidence (inductive invariants, composition, timed runs, the model checker) in one table | 1 500 | 2 |
| 2 | **Claims, premises, witnesses** | the composed claims, each with its statement embedded; the claim → premise → witness picture; the premises in plain words (a simplified list, §5 item 1); what "non-vacuous" means here; the paper target and the findings for the authors, summarised (§5 items 2–3) | 1 800 | 5, 8 |
| 3 | **Reading a model: Chorus** | what a Veil model is (state, actions, properties); Chorus's state (§4.1); four honest actions; one network relation; one adversary action; the MVBA as a consumed contract; one safety property with its proof; one liveness claim with its premises; where the rest is | 2 500 | 2 |
| 4 | **What a model asks you to accept** | one flat state space, and how distribution is encoded; Chorus's shared `phase`, a global read every validator's timer guards make, and why it stands for local clocks; the monotone network; the adversary as explicit actions, and why it must be at least that strong; how a departure from the idiom makes a theorem true for the wrong reason, with an example of each kind; what an auditor checks; the Chorus audit table (§4.2) | 1 800 + table | 3 |
| 5 | **Reviewing the contracts** | what a contract is (a class over an abstract state, two levels); the escape-hatch question; the checklist, one table per contract with a "proven by" column (§8, M3); the ACS, assumed, and its ideal instance; what a machine check of this would need (the V line) | 1 500 + tables | 4 |
| 6 | **The components** | one section each: Chorus, the MVBA, the Conductor, the glue, the receipt layer, the composition. Each: what the paper says, what the model covers and abstracts, the end results (embedded), where the details are | 1 800 | 6 |
| 7 | **How the proofs are checked** | the pipeline from model to pinned theorem (diagram); solver discharge with kernel reconstruction; the axiom pins and the `#veil_status` pins; the proof cache, and why a hit is still checked; the mutation test; the monitor (outside every trust base); the docs checks; CI; re-checking it yourself (the container commands, the audit ladder) | 1 300 | 7 |
| 8 | **Open issues and further work** | the open issues, summarised and linked (§5 item 4); ongoing work (the V and A lines, once they exist) and future work, linked | 500 | 8 |

Total about 13 000 words of prose. Chapter 0 is readable alone; chapters
1–2 need no Lean; chapters 3–5 teach the reading of Lean and Veil as they
go; chapters 6–8 are reference.

### 1.3 Narrative order

0 → 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8, one story. The order answers the
reader's questions in the order they come: what is claimed (0), how it is
put together (1), what exactly it rests on (2), how to check the models
(3–4) and the contracts between them (5), where each part is (6), why the
machine part can be trusted (7), and what is left (8). Chapter 2 comes
before the model chapters because it needs no Lean, so a reader who does
not need the models has the whole claim and its premises by then.

### 1.4 The README

**Its role** (decided by Lars): the entry document of the GitHub project,
which is the home of the sources and of development. It covers building,
development, CI, the container images and maintenance, and opens with a
short landing section. Content readers go to the guide.

**Proposed landing section** (replaces everything above today's "Checking
the proofs"; its links are written relative to this page, and become
README-relative in D8):

> # Cadence — machine-checked verification (Veil / Lean 4)
>
> A formal verification of the [Cadence](https://www.category.xyz/cadence)
> BFT consensus protocol (arXiv:2607.02275) in [Veil](https://github.com/larskuhtz/veil)
> on Lean 4: the per-slot consensus Chorus, the leader-based MVBA inside
> it, the window-based orchestrator Conductor, the extreme-pipelining layer
> that composes them, and the fallback receipt layer. The development
> corresponds to revision `48cac9a` of the paper repository.
>
> Every theorem is checked by Lean's kernel from Lean's three standard
> axioms. SMT solver results are rebuilt as Lean proofs and checked by the
> kernel too, so the solver is not trusted.
>
> **To read what is proven, start with the guide** — *link to the site*. It
> states the claims and what they rest on, and shows how to audit the models
> and the contracts. [Cadence.lean](../Cadence.lean) lists every end result
> with its axiom pin.
>
> **To re-check the proofs**, see [Checking the proofs](../README.md#checking-the-proofs).
> **To work on the models**, see [Working on the models](../README.md#working-on-the-models)
> and [CLAUDE.md](../CLAUDE.md).

The second paragraph stays because about a hundred proof files link to the
README for the no-trusted-solver rule (their header comment), and the
README keeps the citation section because [Chorus.lean](../Cadence/Chorus.lean)
and [Primitives.lean](../Cadence/Primitives.lean) link to it for resolving
citations. Keeping both avoids any model-file edit (§9).

**Where today's README sections go:**

| README section | Destination | Note |
|---|---|---|
| Title + intro paragraphs, Status box | **replaced** by the landing section | the status sentences move into the claims box |
| "Start here: Cadence.lean" | **stays**, in the landing section | |
| Map of the development (mermaid + layer table) | **moves to the guide**, chapter 1 | the diagram becomes the SVG overview (§7), also shown in the landing section |
| Audit Guide A, "Machine-checked" | **moves to the guide**, chapter 7 | the table is the core of "how the proofs are checked" |
| Audit Guide B, "To be checked by an auditor" | **moves to the guide**, chapters 2, 4 and 5 | |
| AuditReport paragraph | **moves to the guide**, chapter 8 ("records"); README keeps a one-line pointer under Records | |
| What is proven (the big table) | **moves to the guide** as the claims box (chapter 0) and the per-component results (chapter 6); the full index is [Cadence.lean](../Cadence.lean) | the table repeats Cadence.lean's index; one home is enough |
| Checking the proofs | **stays** | link the guide's chapter 7 for what each tier establishes |
| Working on the models, Building natively | **stay** | |
| How the proof fits together: the commands | **moves to the guide**, chapter 7 | the README keeps a two-line pointer for developers |
| How the files feed each other (ASCII) | **moves to the guide**, chapter 7, as the pipeline diagram (§7) | |
| What depends on what (import graph, mermaid) | **stays** in the README, as developer material (it is about build dependencies), kept as mermaid (§10, Q6) | |
| What is where (the file tree) | **stays** | developer material; refreshed |
| Model-conformance monitor | **stays**, shortened to the commands; the guide's chapter 7 explains what it is | |
| Reading guide (levels 1–4, records) | **replaced** by the guide, whose chapter list is the map (§2); README keeps a short "Documentation" table pointing at the guide and at the developer docs (Container, Images, Dependencies, Documentation, VersoIssues, Monitor, CLAUDE.md, History) | |
| The protocol paper, the target, access, Conductor scope, receipt layer and v1 | **target and access move to the guide**, chapter 2; the citation record stays in the README | the v1 paragraph shortens to the tag pointer |
| Resolving a citation | **stays** | developers write citations; two model headers link here |

## 2. Navigation by structure

The guide is one story, read front to back, and every reader drills in or
skips by interest. There are no per-audience paths; the audiences (protocol
researchers such as the paper's authors, security auditors, Lean-literate
verifiers) shape the writing, not the navigation. Navigation comes from the
structure itself:

* **Chapter titles that name the content**, listed on the front page.
* **A one-line opener per chapter**, in italics under its title: what the
  chapter covers, and what it assumes of the reader. The front page's
  chapter list shows the same line, so the list doubles as the map.
* **Signposts to deeper material** at the end of a section, never in the
  middle of an argument: "The full list: [Premises.md] §0", "Every action:
  the rendered model". The story reads without following them.
* **Stopping points.** Each chapter ends where its question is answered;
  the opener of the next says what it adds, so a reader can tell whether to
  go on.

The openers, as the chapter sessions start from them:

| # | Title | Opener |
|---|---|---|
| 0 | Cadence Verification | What is proven about the Cadence protocol, and what it rests on. |
| 1 | How the verification is built | The modules, the contracts between them, and how the proofs compose; no Lean needed. |
| 2 | Claims, premises, witnesses | Each end claim with its premises in plain words, the model that meets them all, and what the review found in the paper; no Lean needed. |
| 3 | Reading a model: Chorus | How a Veil model states a protocol, taught on selected parts of Chorus; assumes chapter 1, no prior Lean. |
| 4 | What a model asks you to accept | The modelling idioms a theorem relies on, how a model can break them, and the per-action table that checks Chorus; assumes chapter 3. |
| 5 | Reviewing the contracts | How to check that each module contract asks only for what a real protocol delivers, field by field; assumes chapters 1 and 3. |
| 6 | The components | One section per model: what it covers, what it abstracts, its results, and where its details are. |
| 7 | How the proofs are checked | What the machine checks and how, what is trusted, and how to re-check it yourself. |
| 8 | Open issues and further work | What is open, and what is planned. |

## 3. The claims box

The text below is the box as it would appear on the front page, for
word-by-word review. In the guide each declaration name is a `{decl}`
link, so a renamed theorem fails the build; the paper citations are checked
by `scripts/paper-cites.sh` like every other.

> **What this project claims**
>
> **The paper.** The development corresponds to revision `48cac9a` of the
> Cadence paper repository: the main body of *Cadence: Extreme Pipelining
> with Multiple Concurrent Proposers* (arXiv:2607.02275), together with its
> internal supplement, which specifies the MVBA.
>
> **The composed system.** Cadence runs one Chorus instance per slot,
> scheduled by the Conductor, with the supplement's MVBA inside each Chorus
> instance. For `n = 3f + 1` validators, at most `f` of them Byzantine, the
> composed system satisfies:
>
> * **MCP Safety**, Definition 1 (`def:safety`): two correct validators
>   never hold different entries at the same position of their logs. It
>   holds in every reachable state, with no timing premise.
>   `Cadence.system_positional_log_safety`
> * **Corollary 4 (`cor:chorus-correctness-within-cadence`)**: within
>   Cadence, every slot's Chorus instance gets everything it needs from its
>   caller. So every slot is finalized by every correct validator within
>   `5Δ + ℓ_MVBA` after all correct validators have joined it, counted from
>   GST at the earliest, and within `Δ` of the first correct validator to
>   finalize it. `Composed.corollary4`
> * **Bounded concurrency**, Lemma 5 (`lemma:cadence-bounded-concurrency`):
>   no correct validator takes part in more than `2W − p` slot instances at
>   once, where `W` and `p` are the Conductor's window parameters.
>   `Composed.boundedConcurrency`
> * **𝓡-Liveness**, Lemma 2 (`lemma:cadence-liveness`) for
>   Definition 2 (`def:liveness`): every slot that starts at least `𝓡 = 2Wτ` after GST
>   is in the log of every correct validator, where `τ` is the time between
>   consecutive slot starts. The same holds at the smaller
>   `𝓡 = (W + p − 1)τ`. `Composed.liveness`, `Composed.liveness_sharp`
> * **𝓡-Censorship resistance**, Definition 3 (`def:censorship-resistance`):
>   for every such slot, each correct proposer's proposal is in that slot's
>   entry of every correct validator's log. `Composed.censorship`,
>   `Composed.censorship_sharp`
>
> **The modules.** Each module meets the paper's specification of it, every
> property proven:
>
> * **Chorus** meets Module 1 (`mod:slotconsensus`): agreement, proposal
>   inclusion, hiding (its protocol half), quiescence, termination within
>   `5Δ + ℓ_MVBA` (Lemma 11 (`lemma:chorus-termination`)) and totality within
>   `Δ` (Proposition 4 (`prop:chorus-totality`)). `Chorus.slotConsensusFull`
> * **The Conductor**, Algorithm 7 (`algorithm:conductor`), meets
>   Module 2 (`mod:orchestrator_2`) for every ACS that meets Module 4:
>   agreement on the open slots, integrity, totality within `Δ`
>   (Lemma 15 (`lemma:conductor-totality`)), `(2W − p)`-boundedness
>   (Lemma 14 (`lem:boundedness`)) and `(2Wτ)`-recovery
>   (Lemma 16 (`lemma:conductor-recovery`)). `Conductor.conductorFull`
> * **The MVBA**, the supplement's leader-based protocol, meets
>   Module 3 (`mod:mvba`): agreement, integrity, external validity, quiescence, and
>   termination within an explicit `ℓ_MVBA` of order `fΔ`. `Mvba.mvbaFull`
>
> **What the claims rest on.**
>
> * **The ACS is an assumed module.** The paper leaves the ACS protocol
>   open (finding P17), so the Conductor and the composed system are proven
>   for every ACS that meets Module 4 (`mod:acs`). An idealized ACS, with
>   global knowledge and no adversary, shows that Module 4 can be met; a
>   message-passing protocol that meets it is outside this development.
> * **Environment premises**, for every claim except MCP Safety: partial
>   synchrony, in which every step a correct validator owes after GST
>   happens within `Δ`; timers that fire on time; and the configuration's
>   constraints on the window parameters. The composed claims and the
>   Conductor's bounds also take local steps to need no time (`δ = 0`), as
>   the paper does; Chorus's bounds are proven with an explicit `δ` term
>   and are quoted above at `δ = 0`, and the MVBA's bound holds for any `δ`.
>   Censorship resistance also reads "by the deadline" as inclusive
>   (finding P19). The full list is one page, [Premises.md](Premises.md) §0,
>   and one model of the composed system meets all of it at once.
> * **Cryptography**, stated as assumptions: each signed message is
>   attributed to its signer, so signatures cannot be forged; threshold
>   encryption keeps a proposal hidden until the decryption shares are
>   released.
> * **Modelling idioms**, which chapter 4 explains: the network keeps every
>   message once sent, and protocol steps react only to the presence of
>   messages; the state of all validators is one global state, in which each
>   step reads its own validator's records and the network; Chorus's timers
>   are one shared phase that the environment advances and every
>   validator's guards read, a global read standing for each validator's
>   own clock; Byzantine
>   validators act through explicit adversary actions; Chorus is modelled
>   for one slot, with erasure coding abstracted.
> * **Trusted tools**: Lean's kernel, and Veil's translation of each model
>   into the conditions proven about it. SMT solver results are rebuilt as
>   Lean proofs and checked by the kernel.
>
> Every theorem is checked by Lean's kernel from Lean's three standard
> axioms, and [Cadence.lean](../Cadence.lean) pins the axioms of each.

**The two negative statements, and why.** "A message-passing protocol that
meets it is outside this development" is stated because a reader who sees
four paper modules and three proven ones will otherwise assume the fourth is
proven too; that is the one misreading the box most needs to prevent.
"Signatures cannot be forged" is the plain form of the unforgeability
assumption and has no shorter positive form.

**Choices the box makes.** It lists MCP Safety first, because it is the
safety headline and the only claim with no environment premise (§10, Q4).
It names Chorus's shared `phase` among the idioms because every timer guard
of every validator reads it, a global read the auditor has to accept;
chapter 4 explains it. It
states Corollary 4 by its consequences (termination and totality for every
slot) rather than its literal statement (every caller condition holds),
because the consequences are what a reader cares about; chapter 2 gives the
literal one. It omits `hbyz`, MCP Safety's hypothesis that the Conductor and
Chorus agree on who is faulty, as a configuration fact; chapter 2 names it.

## 4. The running example

### 4.1 The Chorus declarations the guide shows

Chapter 3 quotes each declaration with `{model}` (Veil commands) or
`{claim}` (Lean theorems), so every quotation is the source as built.

| Declaration | Kind | What it teaches |
|---|---|---|
| `immutable relation is_proposer` | configuration | fixed data: who proposes in this slot; immutable relations never change in a run |
| `individual phase` | abstract state (category A) | one global landmark for the slot's timers (deadline, fallback arm, MVBA arm), advanced by environment actions; a validator's timer firing is "the phase has passed" |
| `relation msg_vote_pos_sig` | network relation (category N) | **the network relation.** Indexed by the signer; a tuple is a signed message that exists; it is only ever set to true |
| `relation local_entry_pos` | local state (category L) | indexed by the validator that owns it; only that validator's actions write its row |
| `ghost relation vote_quorum_pos` | derived certificate (category D) | a certificate is a fact about the network (a quorum of signatures), not a stored object |
| `action propose` | honest action, proposer | the shape of an action: guards (`require`) and updates; the actor guard `¬ is_byz j`; a self-row negative read (fired once) |
| `action record_chunk` | honest action, receiver | a guard that reads the network positively and the validator's own row negatively; the deadline as `phase` |
| `action vote` | honest action, bulk update | Algorithm 3 (`alg:voting`)'s per-proposer loop as one atomic step; updates that only add tuples |
| `action finalize_commit` | honest action, decision | the protocol's output, written to the validator's own row |
| `action byz_sign_vote_pos` | **the adversary action** | a Byzantine validator signs a vote for any root, constrained only by what an honest receiver checks (the attached chunk); one action per adversarial capability |
| `instantiate mvba : MVBASafety …` | **the consumed contract** | the MVBA enters as a class over an abstract state; its properties are hypotheses of every proof, and the model reaches the MVBA only through the class's operations |
| `action on_mvba_decide_pos` | contract handler | the one stated bridge: the guard that checks a decided entry's certificate against the network |
| `safety [agreement_pos]`, proven as `Chorus.reachable_agreement_pos` | **the safety property** | a property is a formula over the state; "proven" means: holds in every reachable state |
| `Chorus.termination` | **the liveness claim** | a theorem over runs, with its five premises as named hypotheses, none of them an axiom |

Everything else in [Chorus.lean](../Cadence/Chorus.lean) is linked, not
shown: the chapter ends with a pointer to the rendered model and to
[ChorusDesign.md](ChorusDesign.md).

### 4.2 The Chorus audit table

**What it is.** One row per action of the model, saying who acts and what
the action reads and writes, in the four state categories of
[ChorusDesign.md](ChorusDesign.md) §3.5. It is the table an auditor fills
in when checking that the model respects its idioms (chapter 4), filled in
for them.

**Columns.**

| Column | Content |
|---|---|
| Action | the action name, linked into the rendered model |
| Paper | the algorithm line it models (rendered citation) |
| Actor | the validator the action belongs to (`i`, a correct validator; `r`, a Byzantine one), or the environment: the network, the clock, the MVBA |
| Reads, own | local relations of the actor read in the guards |
| Reads, network | network relations read in the guards, positive |
| Negative network reads | each negative read, with its category: self-row, or the documented `fb_sign_neg` exception |
| Fault pattern | where `is_byz` is consulted: the actor's own status only, or another validator's |
| Writes | each relation written, and whose row |
| Note | a one-line verdict, and the exception it relies on, if any |

**Coverage.** All 48 actions: the 33 honest and environment actions in
full, grouped by protocol phase as the model groups them, and the 15
`byz_*` actions in one compact block (they share a shape: actor Byzantine,
writes its own network rows, reads only what an honest receiver checks).
Sample rows:

| Action | Paper | Actor | Reads, own | Reads, network | Negative network reads | Fault pattern | Writes | Note |
|---|---|---|---|---|---|---|---|---|
| `propose` | Algorithm 2 (`alg:proposer-dissemination`) | proposer `j` | `participating`, `abandoned` | — | `msg_proposer_signed j` (self-row) | `¬ is_byz j` (actor) | `msg_proposer_signed j m` | sign once |
| `deliver_chunk_assigned` | Algorithm 2 | network, for sender `j` | — | `msg_proposer_signed j m` | — | `¬ is_byz j` (sender) | `msg_chunk_received i j m`, the fired-once record | delivery of a correct sender's send |
| `record_chunk` | Algorithm 3 (`alg:voting`) | `i` | `local_entry_pos i`, `local_entry_neg i` | `msg_chunk_received i j m`, `msg_proposer_signed j m` | — | `¬ is_byz i` (actor) | `local_entry_pos i j m` | reads `phase` |
| `fb_sign_neg` | Algorithm 5 (`alg:fallback`) | `i` | own rows | `msg_vote_cast`, `msg_vote_pos_sig`, `msg_chunk_received` within `qv` | absence of a quorum within the received set `qv` | `¬ is_byz i` | `msg_fb_neg_sig i j`, own rows | documented exception (ChorusDesign §3.1.1 (i)) |
| `byz_sign_vote_pos` | — | Byzantine `r` | — | `msg_chunk_received r j m` | — | `is_byz r` (actor) | `msg_vote_pos_sig r j m` | mirrors the receiver's check |
| `advance_to_deadline` | — | the clock | — | — | — | — | `phase` | environment |

**How it is produced now.** By hand, in one session (§9, D5), from the
action bodies; stored as a data file beside the guide's sources and
rendered by a block command (§8, M4). The command checks the table's
action names against the model's own label type, `Chorus.Label`, so an
added, removed or renamed action fails the guide's build until the table is
updated. The relation names in the cells are checked as declarations of
the model.

**How it switches to the V checker.** The columns Actor, Reads, Negative
network reads, Fault pattern and Writes are the per-action read/write data
the V line's checker is planned to produce. When it lands, the block command
reads the checker's output for those columns instead of the data file, and
the data file keeps only the human columns (Paper, Note). The rendered table
keeps its shape, and the other models' tables come from the same command
at no extra authoring cost. Until then the hand table is the guide's
evidence, and chapter 4 says it is checked by hand.

## 5. Curated items from docs/

| Item | In the guide | Authoritative home |
|---|---|---|
| 1. The premises of the top-level theorems, marking those the paper does not state | **both**: chapter 2 has a plain-words list of about ten lines (the timing model, fairness, the ACS, the configuration, the inclusive deadline, the certificate bridge), each marked "paper" or "not stated in the paper", each linked to its ledger entry | [Premises.md](Premises.md) §0 (the composed claims) and §1–§9 (per claim) |
| 2. Alignment with the paper | **both**: chapter 1 states the target and the citation form in three sentences; chapter 2 lists the five abstractions an auditor must accept against the paper, linked | [PaperAlignment.md](PaperAlignment.md) §0 (the target), §1 (the check), §5.10 (what still differs) |
| 3. The findings for the paper's authors | **both**: chapter 2 gives the three groups with their counts and the five findings of the "correctness argument" group as one line each; link to the full page | [PaperAlignment.md](PaperAlignment.md) §6 |
| 4. Open issues of the project | **linked**, with a three-line summary of the kinds (paper, soundness instruments, scope) | [TODO.md](TODO.md) |
| 5. Ongoing and future work | **linked**; the V and A lines get one sentence each once they have started | [TODO.md](TODO.md) |
| 6. The assumption inventory | **summarised** in the claims box and chapter 4; **linked** for the full list | [Architecture.md](Architecture.md) §4 |
| 7. The named composition seams | **summarised** in chapter 5 (the two bridges, the fault-pattern hypothesis) | [CompositionContracts.md](CompositionContracts.md) §7 |
| 8. The network contract and its exceptions | **summarised** in chapter 4 | [ChorusDesign.md](ChorusDesign.md) §3.1.1 |
| 9. Per-module counts (actions, properties, VCs, manual cells) | **linked**; the `#veil_status` pins are embedded in chapter 7 as the evidence | [Architecture.md](Architecture.md) §2; the pins |
| 10. The audit ladder (what a prebuilt olean proves) | **summarised** in chapter 7 | [Container.md](Container.md) §3–§4 |
| 11. The external audit report | **linked** from chapter 8, with its date and revision | [AuditReport.md](AuditReport.md) |
| 12. The timing models and the bound derivations | **linked** from chapter 6 | [Bounds.md](Bounds.md), [ConductorBounds.md](ConductorBounds.md) |
| 13. History | **linked** from chapter 8 only | [History.md](History.md) |

The rule for the guide's summaries: a summary names no count that changes
(the number of premises, findings or open items) unless it is generated,
and every summary ends with its link.

## 6. The docs/ cleanup plan

Roles: **landing** (the guide links into it, so it opens with an
orientation and reads on its own), **reference** (developers and deep
readers; linked from the README or other docs), **record** (frozen or
historical), **merge/remove**.

| File | Role | Edits |
|---|---|---|
| [README.md](../README.md) | entry document for developers | rewrite per §1.4; refresh "What is where"; the reading guide becomes a short documentation table |
| [Premises.md](Premises.md) | landing (chapter 2) | opener: one line pointing to the guide's chapter 2 for the plain-words version; otherwise current |
| [PaperAlignment.md](PaperAlignment.md) | landing (chapters 1, 2) | opener names the guide; §8 "What the realignment built" is design record, check it is framed as such; §9 current |
| [Architecture.md](Architecture.md) | landing (chapters 1, 4, 7) | **stale**: §1 says the supplement is unpinned and that the model pins a commit (now PaperAlignment §0's job); §1.1's table lists `SlotConsensusTemporal` as still owed for Module 1 and `Conductor.conductorFull` but not `Chorus.slotConsensusFull`; the mermaid chart lacks the composed claims. Replace the chart with the overview SVG; opener points to the guide for the overview and keeps §4 as the checklist |
| [CompositionContracts.md](CompositionContracts.md) | landing (chapter 5) | opener names the guide's chapter 5; check §3–§7 against the current instances (the decision handoff text is current) |
| [ChorusDesign.md](ChorusDesign.md) | landing (chapters 3, 4) | opener points to the guide's chapters 3–4; §9 "What is left" overlaps TODO.md: keep the Chorus-specific items there, link from TODO |
| [TODO.md](TODO.md) | landing (chapter 8) | opener names the guide; add "ongoing work" when the V and A lines start |
| [Liveness.md](Liveness.md) | reference | opener; §4 is a proof walkthrough (step log), keep, framed as such |
| [Bounds.md](Bounds.md) | reference | opener names the guide's chapter 6; long; no structural change |
| [ConductorBounds.md](ConductorBounds.md) | reference | opener names the guide's chapter 6 |
| [ConductorDesign.md](ConductorDesign.md) | reference | opener says "for what is proven read README and Architecture": point to the guide instead |
| [Container.md](Container.md) | reference (users) | opener names the guide's chapter 7 for what each tier establishes; current |
| [Images.md](Images.md) | reference (maintainers) | none |
| [Dependencies.md](Dependencies.md) | reference | none |
| [Documentation.md](Documentation.md) | reference (maintainers) | update "The guide" section: multi-page, chapter files, new block commands; record the diagram mechanism |
| [VersoIssues.md](VersoIssues.md) | reference (maintainers) | add whatever the diagram and multi-page work runs into |
| [Monitor.md](Monitor.md) | reference | opener names the guide's chapter 7 |
| [MvbaPlan.md](MvbaPlan.md) | record | opener already says "decision record"; no change |
| [Scenario.md](Scenario.md) | record | opener points to README for what is proven: point to the guide; §10, Q7 |
| [AuditReport.md](AuditReport.md) | record (frozen) | none |
| [History.md](History.md) | record | add the D line's row when it ends; receive this plan's pointer |
| GuidePlan.md (this file) | plan | moves to History.md as a pointer when the D line ends |
| [paper-labels.tsv](paper-labels.tsv) | generated | none |

Every landing opener follows one pattern, one or two sentences in italics:
what the page is, which guide chapter introduces it, and what it is the
authority for.

## 7. Diagrams

### 7.1 What the toolchain accepts (measured)

D1 rendered a throwaway guide page with a draft of the overview diagram
(§7.2, item 1) as an SVG file, built with `scripts/docs.sh` and
`scripts/guide.sh` at master `5bea8c7`, and a throwaway sources module
through Verso's literate renderer. What happened:

| Route | Where | Result |
|---|---|---|
| **Inline SVG** through a block command that reads the file while the guide elaborates and emits it as raw HTML (the mechanism `{claim}`'s status box already uses) | guide | **works**: the SVG is in the page, uses the page's fonts, scales with the column; a missing file fails the guide's build |
| **Verso image syntax**, `![alt](file.svg)`, with the file copied next to the page by `extraFilesHtml` in [GuideMain.lean](guide/GuideMain.lean) | guide | **works**: `<img src="file.svg">`, the file copied into `site/guide/`; a missing file fails the render |
| **Raw HTML block** in a module doc (`/-! … -/`): inline `<svg>` at the left margin, no blank lines inside | sources page | **works**: passed through verbatim |
| Raw `<img>` in a module doc, and a Markdown image | sources page | **works** as HTML, but the path is not resolved: [site-links.sh](../scripts/site-links.sh) rewrites links, not image sources, so a file-relative path is dead on the site |
| Docs CI ([docs.yml](../.github/workflows/docs.yml)) | site | runs `scripts/docs.sh` in the `verified` image and uploads `site/` as it is, so a file the guide copies or inlines ships with no CI change |
| Mermaid | GitHub only | renders on GitHub, nowhere on the site ([Documentation.md](Documentation.md), [VersoIssues.md](VersoIssues.md)) |
| SVG through `![](…svg)` in Markdown | GitHub | renders as an image; the SVG's own `prefers-color-scheme` rules follow the reader's scheme |

**Dark mode, measured both ways.** The site is light-only (neither the
guide's [theme.css](guide/theme.css) nor [literate.toml](../literate.toml)
defines a dark theme). An SVG that carries its own
`@media (prefers-color-scheme: dark)` rules — needed for GitHub's dark
mode — switches to dark boxes on the light guide page when the reader's
system is dark, in both the inline and the `<img>` route. And an inline
SVG's `<style>` applies to the whole page, so its class names can collide
with the page's (the draft's did not, but nothing prevents it).

### 7.2 Format and mechanism

**One source per diagram: a hand-written SVG file under docs/diagrams.**
Each file:

* draws in the page's palette, light by default, with its own dark rules
  inside one `@media (prefers-color-scheme: dark)` block, for GitHub;
* prefixes every class with `dg-`, so it cannot style the page around it;
* carries a `<title>` and a `<desc>`, for screen readers and for GitHub's
  image alt.

**In the guide**, `{figure "docs/diagrams/x.svg"}` (§8, M2) inlines the
file and drops its dark-scheme block while doing so, because the site is
light-only. If the site gets a dark theme, the command keeps the block and
the guide's dark theme matches it. **On GitHub** (README, docs/), the same
file as a Markdown image, `![…](diagrams/x.svg)`. **No diagram goes into a
model file** (§9.3), so the sources pages need no image support.

### 7.3 The diagrams

| # | Diagram | Shows | Used in |
|---|---|---|---|
| 1 | **Modules and contracts** (goal 2) | the composed claims on top; the glue; Chorus and the Conductor with the contract each meets; the MVBA under Chorus and the assumed ACS (dashed) under the Conductor, with its ideal witness named; the receipt layer beside Chorus; each arrow "fills `orch` / `sc` / `mvba` / `acs`" | guide chapters 0 and 1; README landing section; [Architecture.md](Architecture.md) §1.1 (replacing its mermaid chart) |
| 2 | **Claim → premise → witness** (goal 5) | one claim with its premise list, the proof that consumes each premise, and the witness model that meets all of them; the auditor's judgement (plausibility) marked as the part no tool checks | guide chapter 2; [Premises.md](Premises.md) opener |
| 3 | **From model to pinned theorem** (goal 7) | model file → VC registry → per-action proof files (solver, kernel reconstruction, cache) → `#gen_composition` → contract instance → axiom pin and `#veil_status` pin; what is trusted at each step | guide chapter 7; README "How the proof fits together" pointer |
| 4 | **One Chorus slot** (optional, for chapter 3) | the phases of a slot, fast path and fallback path, with the actions of §4.1 placed on it | guide chapter 3 |

The README's import graph stays mermaid (§10, Q6): it is build
documentation and never appears on the site.

The probe page is in D1's local render (`site/guide/`, section "D1 probe:
diagrams"); the probe's sources are not in this change.

## 8. Machinery the guide needs

Beyond `{claim}`, `{model}`, `{decl}` and `{contracts}` in
[Audit.lean](guide/CadenceGuide/Audit.lean):

| # | Element | Reads | Fails the build when |
|---|---|---|---|
| M1 | **Multi-page output** with depth-aware links: chapters as pages; links into the sources computed relative to each page | the page's depth, at render time in [guide.sh](../scripts/guide.sh) | a link does not resolve (the existing link check in [docs.sh](../scripts/docs.sh), extended to every guide page) |
| M2 | **`{figure "…svg"}`**: an SVG file inlined into the page (§7) | the SVG file, while the guide elaborates | the file is missing |
| M3 | **`{contractFields C}`**: one row per field of a contract class: the field, its docstring's first sentence, its level (safety fragment or temporal), and **proven by**: the instance that provides it, classified as a protocol model, an ideal model (the ACS's), or none | the class's structure fields and their docstrings; the providers, as `{contracts}` finds them; a list of the modules holding ideal models (today [IdealAcs.lean](../Cadence/Conductor/IdealAcs.lean)) | a field has no docstring; a class has a field no instance provides and the class is not on the guide's list of assumed modules; a module on the ideal list disappears |
| M4 | **`{auditTable Chorus "…tsv"}`**: the audit table (§4.2) | the data file; the model's label type for the action names; the environment for the relation names | the action set differs from `Chorus.Label`'s constructors; a relation named in a cell is not a declaration of the model |
| M5 | **`:::claims`** box: a styled block for the front page's claims box and for the "what you check" boxes of chapters 4–5 | its contents | — (presentation only; the `{decl}` links inside it carry the checks) |
| M6 | **`{premiseFields S}`** (optional): the fields of a premise structure, such as `Composed.SysSync`, with their docstrings' role line, as a generated table | the structure's fields and docstrings | a field has no docstring; with `(covers := true)`, a field is not mentioned by a `{decl}` on the page, so the plain-words list cannot silently drop a premise |
| M7 | **Ideal-model classification in `{contracts}` and the trust boundary** | the same ideal-module list as M3 | a contract whose only providers are ideal models or witnesses is shown as anything but assumed |

**Why M7 is needed: a finding of the D1 render.** Both derived pages
overstate the ACS today. The trust boundary page marks `ACSSafety` and
`ACSTemporal` **"proven"**, listing `Cadence.IdealAcs.acsSafety` and
`Composed.Witness.AS` (resp. `Cadence.IdealAcs.acsTemporal` and
`Composed.Witness.TA`) as providers; the guide's `{contracts}` table says
"discharged by" the same four. Both tests count any declaration of this
development whose type has the class at its head, so the ideal ACS and the
composed witness's instance of it count as implementations. The published
site at master carries the same rows. The fix is a classification, not a
special case: providers in ideal-model or witness modules are reported as
"consistency witness", and a contract with only such providers as assumed.
Session D1.2 makes that fix, ahead of the rest of the line (§10, Q8).

M3 and M7 share one list of ideal-model modules, kept in
[Audit.lean](guide/CadenceGuide/Audit.lean) next to the contract classes,
which it already names. [TrustSurface.lean](../scripts/TrustSurface.lean)
has its own copy of the classification and gets the same list.

## 9. Session plan

### 9.1 The sessions

One topic per session. "Shared" marks a file on the shared list, which
needs Lars's approval in that session.

| Session | Topic | Files | Size | Depends on |
|---|---|---|---|---|
| **D2** · Guide machinery | M1–M5 (§8), reusing D1.2's ideal-model list for M3 (M7 itself is D1.2); the guide split into one Lean file per chapter, each a stub with its section headings, so that chapter sessions never edit the same file; [Documentation.md](Documentation.md) "The guide" updated | [CadenceGuide.lean](guide/CadenceGuide.lean), [Audit.lean](guide/CadenceGuide/Audit.lean) and new chapter files under docs/guide/CadenceGuide; [GuideMain.lean](guide/GuideMain.lean); [guide.sh](../scripts/guide.sh), [docs.sh](../scripts/docs.sh) and [TrustSurface.lean](../scripts/TrustSurface.lean) (shared); [Documentation.md](Documentation.md), [VersoIssues.md](VersoIssues.md) | L | Lars's review of this plan |
| **D3** · Diagrams | the SVG files of §7, one source each; nothing embeds them yet | new files under docs/diagrams | M | Lars's review of this plan |
| **D4** · Front page and approach | chapters 0 and 1: the claims box as reviewed, the chapter list with the openers of §2, the overview diagram, the module and contract table | the two chapter files | M | D2, D3 |
| **D5** · Reading a model | chapters 3 and 4, and the Chorus audit table (all 48 actions, by hand) | the two chapter files; the audit table's data file | L | D2 |
| **D6** · Claims and contracts | chapters 2 and 5: the claim → premise → witness picture, the plain-words premise list, the findings summary, the contract checklists | the two chapter files | M | D2, D3 (the picture) |
| **D7** · Components, checking, status | chapters 6, 7 and 8 | the three chapter files | M | D2, D3 (the pipeline) |
| **D8** · README and docs/ | the README per §1.4; the openers and stale content of §6; the overview SVG in the README and in [Architecture.md](Architecture.md) §1.1; the comment edits of §9.3 | [README.md](../README.md), [Architecture.md](Architecture.md), [TODO.md](TODO.md), [Cadence.lean](../Cadence.lean), [CLAUDE.md](../CLAUDE.md) (all shared); the docs/ files of §6 | M | D4–D7 merged (the README links into their pages) |
| **D9** · Read-through | read the guide front to back as one story; check that each chapter delivers what its opener says, and fix seams, signposts and cross-links; this plan becomes a pointer in [History.md](History.md) (shared) | chapter files; [History.md](History.md) | S | D8 |

### 9.2 Launch order

1. **D2 and D3 in parallel**: their files are disjoint.
2. **D4, D5, D6 and D7 in parallel**, once D2 has merged: each owns its
   chapter files and edits no other guide file. A chapter session that
   needs new machinery adds it in a module of its own under
   docs/guide/CadenceGuide and imports it from its chapter, so
   [Audit.lean](guide/CadenceGuide/Audit.lean) stays D2's. D4, D6 and D7
   take D3's diagrams when it has merged; until then they leave a marked
   placeholder.
3. **D8**, after D4–D7 have merged.
4. **D9**, last.

### 9.3 Comment edits to model files

**None to the Veil model files.** The two README pointers they carry stay
valid because the README keeps the no-trusted-solver sentence and the
citation section (§1.4). Two comment edits to plain-Lean files are batched
into D8:

| File | Edit | Rebuild |
|---|---|---|
| [Cadence.lean](../Cadence.lean) | the header calls the README "the orientation document": point to the guide | the audit root only (its pins re-run in seconds) |
| [IdealAcs.lean](../Cadence/Conductor/IdealAcs.lean) | the header carries history ("option (c1), decided 2026-10-03", "the composed witness of K8"): state what the file is, move the history to [History.md](History.md) | the plain-Lean files that import it, in the Conductor's and the composed system's legs (no solver work) |

### 9.4 Rules for every session

* A fresh worktree `d<n>-<topic>` off `origin/master`, after fetching;
  PR title `D<n> · <topic>`, opened as a draft. Never force-push; do not
  wait for CI.
* A private build tree: `cp -Rc` the `.lake` of the newest built session
  tree; if its veil revision differs from lake-manifest.json's, check out
  the manifest's revision in the copy and rebuild. Never touch a shared
  tree; never an unscoped `pkill`; one expensive build at a time.
* Docs and the guide's Lean sources only: no proofs, no models (except the
  batch of §9.3, in D8).
* `scripts/paper-cites.sh` and `bash scripts/site-links.sh check` clean.
* **A local render for review.** Every session ends with a full, current
  site in its worktree (`scripts/docs.sh`, then `scripts/guide.sh` after
  the last change) and reports the command to view it,
  `python3 -m http.server 8000 -d <worktree>/site`, with the URLs of the
  pages it changed. After every review round it renders again and reports
  again. Docs CI renders the site only after a merge, so this local render
  is what Lars reviews.
* Report to "cadence docs coordinator".

## 10. Decisions

Lars's answers to the review questions of the first draft (2026-10-06).

| # | Question | Decision |
|---|---|---|
| Q1 | One page or one page per chapter? | **One page per chapter** (M1). |
| Q2 | The guide's title | **"Cadence Verification"**, no subtitle. |
| Q3 | Drop the README's "What is proven" table? | **Yes.** The claims box and chapter 6 carry the content; [Cadence.lean](../Cadence.lean) stays the index. |
| Q4 | MCP Safety in the claims box? | **Yes**, first. |
| Q5 | Audit table coverage | **All 48 Chorus actions**, by hand until the V checker lands. |
| Q6 | Diagram format | **One SVG per content diagram**, shown in the guide and on GitHub; **mermaid stays only for the README's import graph**. |
| Q7 | [Scenario.md](Scenario.md) | **Kept as a record**, linked from the README's documentation table, its opener pointing to the guide. |
| Q8 | The ACS overstatement on the trust boundary page (M7) | **Fixed ahead of the line**, in its own change, D1.2 (PR #88), which touches [TrustSurface.lean](../scripts/TrustSurface.lean) and [Audit.lean](guide/CadenceGuide/Audit.lean) only. |
| Q9 | How the SVGs are made | **By hand**, reviewed in the local render. |
| Q10 | This plan when the line ends | **A pointer in [History.md](History.md)**; the file is removed. |
| — | Reading paths per audience | **None.** The guide is one story that readers drill into or skip by interest; navigation comes from the structure (§2). |
