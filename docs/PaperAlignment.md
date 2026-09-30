# Paper alignment — what the models verify, and where the paper has moved

*Audit record, not a status document. It answers one question an auditor
will ask: the models claim to verify the Cadence paper — is that still the
paper? Section 1 gives a mechanical check anyone can re-run. The rest
records what the 2026-09-03 audit found, and is dated: re-run §1 rather
than trusting §3 to still be current.*

The short answer, as of **2026-09-03**: yes, exactly. Every algorithm and
proof the models mirror is byte-identical to the published preprint. All
movement in the paper repository since 2026-07-09 is in a second,
implementation-oriented document that this repository does not cite and
that is part of no trust base here.

**Re-check of 2026-09-29** (§7), against the paper repository's head
`eb1bb51`. The MVBA supplement was rewritten. The model's safety side is
unaffected, and the upgrade is planned in [MvbaPlan.md](MvbaPlan.md) §11.
The main body has moved too: `mod:mvba`'s Agreement is now stated over
entries, and six of the eleven verified-surface files differ from v2. The
models still verify v2, but the repository head is no longer v2, and the
Chorus side of that drift has not yet been analysed (§7.3).

## 1. The verified surface, and how to re-check it

The models cite the paper by stable LaTeX anchor (never by page or line —
see [../CLAUDE.md](../CLAUDE.md)). Every anchor cited by a model or a
design document resolves in one of eleven files:

`src/alg_proposer.tex`, `src/alg_voting.tex`, `src/alg_fast.tex`,
`src/alg_fallback.tex`, `src/alg_da.tex`, `src/p2_problem_definition.tex`,
`src/p2_framework.tex`, `src/p2_mvba.tex`, `src/p2_chorus.tex`,
`src/p2_conductor_proofs.tex`, and — for one anchor only,
`section:conductor-overview`, cited where
[ConductorDesign.md](ConductorDesign.md) contrasts the paper's informal
and formal presentations of the Conductor — `src/p1_informal.tex`.

That set *is* the verified surface: Part 2, the algorithm floats, and a
single Part 1 overview anchor. No model and no design document cites the
internal supplement (§2) — with two deliberate exceptions, both introduced
by this audit and both about the supplement rather than resting on it:
§§3–4 below, and the `sec:domain-separation` item in
[TODO.md](TODO.md). A future check should expect supplement anchors in
exactly those two places.

So the alignment question reduces to whether those eleven files have
changed, which is mechanically checkable against the published source:

```
mkdir -p papers/cadence && curl -sL https://arxiv.org/e-print/2607.02275v2 | tar -xz -C papers/cadence
```

then diff each extracted file against its `src/` counterpart in the paper
repository. (`papers/` is gitignored. Note the flat layout: the e-print has
`alg_da.tex` where the paper repository now has `src/alg_da.tex`.)

The paper repository carries **no release tags**, so which commit is which
arXiv version is recorded once, in [../README.md](../README.md)
§ "Paper Revisions" — established by exactly this comparison, run over every
`.tex` file rather than a sample. Tagging that repository would make the
table redundant.

**Result on 2026-09-03.** All five algorithm floats, `p2_framework`,
`p2_mvba` and `p2_problem_definition` are byte-identical. `p2_chorus` and
`p2_conductor_proofs` differ only in `\input{src/…}` path prefixes, and
`p1_informal` only in one figure path, from the paper repository's July
source reorganisation. Elsewhere: two new formatting macros and one
reviewer note in `related_work.tex`. No protocol rule, definition, lemma
statement or proof has moved.

Four cautions for whoever automates the anchor half of this check, each of
which cost time once:

* `sec:` and `section:` are **different** prefixes, as are `mod:` and
  `module:`. A prefix list missing `section:` silently skips
  `section:conductor-overview` and `section:conductor-formal`.
* A regex alternation listing both `sec` and `section` can emit truncated
  phantoms (`section:co` from `section:conductor-overview`). Verify any
  apparent dangler by grepping for it literally before believing it.
* Some anchor-shaped strings are deliberately not labels:
  `alg:da.isDecoded` names a function *inside* `alg:da`, and
  `line:assumption-one..four` is range shorthand for four labels that each
  exist. `line:da-rebroadcast` names a **v1 rule removed in v2**, cited as
  such in [ChorusDesign.md](ChorusDesign.md).
* Exclude `supplementary-internal-bkp.tex` (§6), and be aware the
  supplement redefines some main-body label names, so "defined somewhere"
  is the wrong test — resolve against `main.tex` and `src/*.tex` only.

## 2. The paper repository has two tracks

* **`main.tex`** — the public paper, `arXiv:2607.02275`, v2. Part 2 and the
  algorithm floats are what the models verify.
* **`supplementary-internal.tex`** plus `src/supplementary-internal/` — an
  internal document describing the *implementation*: how a deployment
  realises the abstract protocol, which idealisations it must fill in, and
  which pseudocode steps it changes and why.

Since 2026-07-09 every substantive paper commit has been in the second
track. This repository cites it nowhere and depends on it in no way; it is
recorded here because it is where the protocol's engineering intent now
lives, and because a reader comparing the two documents will find
differences that are neither errors in this development nor errors in the
paper.

**Visibility.** Everything the models verify is public. The supplement is
not: an auditor can read `arXiv:2607.02275v2` but not the implementation
track. The algorithms it describes are not secret — they are realised in
the Rust implementation in the `monad-bft` repository — but the *prose
specification* the models would be read against, were they ever extended to
cover the supplement, is internal. Nothing in §1 depends on this; it matters
only for work that targets supplement content — the MVBA instantiation
being the first candidate — where the spec an auditor would check against is
unavailable to them.

## 3. Where the implementation track diverges from the verified algorithms

Seven divergences were found. The classification that matters: in every
case where the supplement and a model disagree, **the model follows the
published algorithm**. None of these is a case of this development having
abstracted differently from a faithful reading of the paper; the model's own
modelling choices are not implicated in any of them. Five are declared as
divergences by the supplement itself, in its own words.

| Divergence | Where | Declared? | Bearing here |
|---|---|---|---|
| An `EquivCert` may be built from two validated witness chunks; "two conflicting positive fallback entries are not required" | `sec:fallback-transition` | **no** | Changes the middle guard of `alg:fallback`'s cascade — see below |
| A revised Conductor differing from `algorithm:conductor` in six named ways, forfeiting no-premature-abandonment of superseded ACS instances | `alg:conductor-practical` | yes, with its own obligation list | Readiness moves off `line:ready-check`; the ACS median moves from slot numbers to deadlines |
| MVBA: an availability precondition on `Commit` under a new `Δ_sync` assumption; payload recovery pushed to the composing layer | `sec:mvba-instantiation` | yes | `mod:mvba`'s termination carries no such precondition — see §4 |
| The positive-entry signer no longer re-encodes and sends each validator its chunk; ChunkSync pulls instead | `sec:fallback-transition` | yes | One of the two paper backings this repository cites for fairness on `redisseminate_chunk` |
| The finalize wait moves outside consensus: commit on certificate, recovery asynchronous | post-MVBA subsection | yes | Shifts the operational reading of `local_committed_pos_implies_decodable` |
| All signatures domain-separated by a message-type tag | `sec:domain-separation` | n/a — below the paper's abstraction | Names an assumption the Chorus model already makes structurally |
| MVBA entry gated on holding the slot's ticket | "Postpone MVBA entry…" | supplement-only mechanism | "ticket" appears nowhere in Part 2 |

Three of these deserve more than a table row.

**The `EquivCert` guard.** `alg:fallback` builds a per-proposer entry by an
exclusive cascade — a held `FastQC`, else an `EquivCert` when two messages
carry positive fallback signed entries with distinct roots
(`line:fb-build-equiv`), else a `FallbackQC` (`line:fb-formqc`) — and
`line:fb-build-entry` is commented "one of the three cases always applies,
by counting". [FallbackReceipt.lean](../Cadence/FallbackReceipt.lean)'s `equiv_available` mirrors that middle
guard, and the model's exclusivity invariants mirror the cascade. The
supplement now admits witness chunks as the source of the two conflicting
proposer-signed roots, which *reassigns* branches: in a state with two
validated witness chunks but no two conflicting positive entries, the
published algorithm falls through and may build a positive `FallbackQC`
where the supplement builds an `EquivCert`. Both rules fire only on genuine
equivocation — each requires the proposer's own signatures on distinct
roots — so agreement and honest-proposer inclusion are unaffected, and only
a Byzantine proposer's fate differs. But the paper's counting comment and
this repository's totality result are stated over the published guards, and
the supplement supplies its own replacement certifiability argument. This is
the one divergence with no written reconciliation, and it sits in the
neighbourhood of the one real protocol bug this development has found
([ChorusDesign.md](ChorusDesign.md) §7.2).

**Chunk re-dissemination.** [Chorus.lean](../Cadence/Chorus.lean) justifies (F-justice) on
`redisseminate_chunk` by the re-encode-and-send being performed by honest
parties at `line:fb-redisseminate` and `line:fb-commit-wait`. The
implementation drops the first. The second survives, chunks are
disseminated unconditionally, and the supplement's new `Δ_sync` argues
availability from the `f+1` signers of a positive `FallbackQC` — the same
chain the model's `redisseminate_chunk` encodes. So the assumption holds,
but its implementation-side discharge now routes through ChunkSync, which
the supplement flags as required for liveness and has not yet specified.

**The ACS median.** [Windows.lean](../Cadence/Windows.lean)'s median
lemma is abstract over a total order, so it transfers to deadlines
unchanged; what does not transfer is the reading, since `win_first` is the
ACS-decided slot-number median and `prop:acs-nonoverlap` is stated over
slot numbers.

## 4. The MVBA: a contract here, an algorithm there

`mod:mvba` in the published paper is an interface — `propose`, `abandon`,
`decide` — plus five properties (Agreement, Integrity, External validity,
`ℓ_MVBA`-Termination, Quiescence). It specifies no algorithm. Chorus therefore
consumes the class `MVBASafety`, instantiated at the supplement's
leader-based model (`Mvba.mvbaSafety`, plugged in by [Cadence/System.lean](../Cadence/System.lean)),
whose own termination theorem Chorus's termination consumes
(`Chorus.termination`, [Architecture.md](Architecture.md) §4 item 2), and its latency `ℓ_MVBA`
is the one paper bound this development proves
([Bounds.md](Bounds.md) §6.2).

The supplement is where that algorithm comes from. `sec:mvba-instantiation`
gives a concrete leader-based protocol across `alg:mvba`, `alg:mvba-cont`
and `alg:mvba-cont2`: views with a leader, Pre-Prepare/Prepare/Commit with
`PrepQC` and `CommitQC`, timeout certificates, view synchronisation
adopting the highest `PrepQC` as a lock, and persist-before-send with
atomic reload. `subsec:mvba-correctness` discharges the module's properties
with roughly fifteen lemmas, `thm:agreement` and `thm:termination`, the
latter at `O(fΔ)`.

Four consequences for this repository:

1. `ℓ_MVBA` has a concrete value, `O(fΔ)`, and a machine-checked
   counterpart: `Mvba.bounded_termination`
   ([Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean)),
   a plain-Lean theorem over timed runs of the untimed model, and through it
   the `MVBATemporal` instance `Mvba.mvbaTemporal`
   ([Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)).
2. The open item of instantiating the primitive classes end-to-end
   ([ChorusDesign.md](ChorusDesign.md) §9) acquired a concrete target,
   and it has been carried out: [Cadence/Mvba.lean](../Cadence/Mvba.lean)
   is a Veil model of `alg:mvba` (views, timeouts, timeout certificates, the
   lock), read against paper-repository commit `026dc8b`, re-read against
   `eb1bb51` (§7; [MvbaPlan.md](MvbaPlan.md) §11) and pinned to that in
   the model's header (four algorithm blocks since then), and [Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)
   discharges `MVBASafety` (`Mvba.mvbaSafety`, every field) and, given the
   timed level, the full `MVBA` (`Mvba.mvba_of_temporal`, supplied with
   `Mvba.mvbaTemporal`); the class lives in
   [Interfaces.lean](../Cadence/Interfaces.lean). This is the one model in
   the development whose referent is the supplement rather than the published
   paper; [MvbaPlan.md](MvbaPlan.md) §0 says what that does and does not
   commit to. Chorus consumes the instance as a class constraint.
3. **An agreement-level observation.** `mod:mvba` states Agreement as
   metablock equality, and [Interfaces.lean](../Cadence/Interfaces.lean)'s `MVBASafety.agreement` mirrors
   it as value equality. The supplement's `thm:agreement` proves the weaker
   entries-level statement, and says so deliberately: agreement is over a
   metablock's entries, the certificates being carried only so validity can
   be checked. Chorus needs no more than that, and the Chorus model already
   works at that level — its records are the per-proposer
   `mvba_decided_pos`/`mvba_decided_neg`, filled by the decision handlers
   through the entry-vector projections `mval_pos`/`mval_neg`, with
   `mvba_decided_pos_unique` proven from the class's agreement. So
   the right instantiation of the class's `value` is the entry vector, not
   the metablock — which is what [Cadence/Mvba.lean](../Cadence/Mvba.lean) does (`value` is the
   entry vector, `Recover(e)` the identity; [MvbaPlan.md](MvbaPlan.md)
   §1.2). This is the one place where this development's abstraction
   matches the supplement rather than the published contract, and it is the
   sound direction: assuming the stronger contract while needing only the
   weaker one. *(2026-09-29: resolved upstream. In the paper repository,
   `mod:mvba` now states Agreement as `entries(B) = entries(B')`
   (`d598c5a`, after v2), so at this instance the class's field is the
   published sentence. See §7 and [MvbaPlan.md](MvbaPlan.md) §11.3, C1.)*
4. **A liveness-level divergence, fixed** (2026-09-29, found while
   building the non-vacuity witness, [Bounds.md](Bounds.md) §6.3.2). The
   supplement stops a validator once it decides: both decision paths end
   in `decide(…); abandon()` (the procedure `Decide` in `alg:mvba-cont3`,
   reached from `line:mvba:qc-decide`, and the restart path), and the
   timeout fires only when there is "no decision in view `v`"
   (`line:mvba:timeout-send`), at `026dc8b` and at the current pin
   `eb1bb51` alike. The model had neither, which left the timed
   Termination theorem silent about the supplement's own runs. The model
   now halts a decided validator (every honest send requires
   `∀ E, ¬ decided i E`), kept apart from the caller's `abandon`.

## 5. What this implies for the models

One model change, §4 item 4: the MVBA now halts a validator after it
decides, as the supplement does. Otherwise nothing: the published
algorithms are unchanged, and the divergences in §3 are between the
paper's two documents.

What is worth doing is documentary, and is tracked in
[TODO.md](TODO.md): cite `sec:domain-separation` where the network
relations assume message-type non-confusability; record ChunkSync and
`Δ_sync` alongside the (F-justice) justification for `redisseminate_chunk`;
and re-check the `EquivCert` guard once the paper side settles which of the
two rules is intended.

## 6. Defects observed on the paper side

Reported so they are not re-discovered; all in the supplement.

* Three `\mainref` citations truncated to bare `\mainref{mod}` and
  `\mainref{prop}` (twice) by the 2026-09-03 sync, leaving the sentence
  that names the MVBA contract ambiguous.
* An internal contradiction: the equivocation-evidence subsection still
  argues from `EquivCert`s being assembled *only* from two conflicting
  positive fallback entries, which `sec:fallback-transition` now
  supersedes. The stale sentence is the one that matches the published
  algorithm.
* `supplementary-internal-bkp.tex`, a stale snapshot committed alongside
  the 2026-09-03 sync, duplicates labels and will confuse any grep-based
  anchor audit — including the check in §1, which must exclude it.
* (Recorded 2026-09-16, after this audit.) `subsec:mvba-protocol` allows
  the view timeout to be set by *backoff* — "the timeout is eventually
  increased beyond this value" — while `thm:termination` counts with a
  fixed `O(Δ)` timeout to reach its `O(fΔ)` bound. The two are compatible
  only if the backoff is capped: under uncapped backoff the view current
  at GST, and with it the next timeout to be waited out, is unbounded
  across runs, so no run-independent bound from `max(t, GST)` exists and
  only eventual termination holds. The theorem is a fixed-timeout (or
  capped-backoff) result and should say so. [Bounds.md](Bounds.md)
  §6.2.3 has the argument; the model's schedule hypotheses (S-cap) and
  (S-ramp) are its formal shape. *(Resolved at `eb1bb51`: the timeout is
  now the fixed `T`. Only a mention in the `sec:timing-constants` stub is
  left; see §7.4.)*

## 7. Re-check of 2026-09-29: the supplement at `eb1bb51`

*This is the audit trail of the review in [MvbaPlan.md](MvbaPlan.md) §11: what was compared, and the result of each comparison. The change list and the plan are in that section. This one records the evidence.*

### 7.1 Revisions compared

The paper repository's remote branch is `master`; it has no `main`. Its newest commit is **`eb1bb51`** (2026-09-28, "Update on Overleaf."). There is only one candidate, since the branch has a single head. That head is 29 commits past `b838e17` (2026-09-11), and `b838e17` descends from the pin `026dc8b` (2026-09-03).

The repository was read without being changed. `git fetch origin` was run, then `git show <rev>:<path>` and `git diff <a> <b> -- <paths>`. Nothing was checked out and nothing was committed.

Six commits in the range touch `alg_mvba.tex`, `p2_mvba.tex` or `supplementary-internal.tex`: `dbe8ddb` (09-15), `e705b6e` (09-18), `e218a06` (09-20), `70887be` (09-21), `d598c5a` (09-21, the `mod:mvba` Agreement edit) and `eb1bb51` (09-28). Most are Overleaf syncs, and the supplement commits also carry Conductor changes, so the commit messages say little. The comparison below is therefore by content.

### 7.2 What was compared, and the result

| Compared | `026dc8b` → `b838e17` | `b838e17` → `eb1bb51` |
|---|---|---|
| `src/supplementary-internal/alg_mvba.tex` | byte-identical | rewritten (543 → 377 lines): a fourth block `alg:mvba-cont3`, `TryDecide` folded into `Decide`, `Pool` replaced by `Accepted_i`, three continuation guards, `ViewTC_i` retransmission, `SyncView` forwarding, a message-retention convention |
| `supplementary-internal.tex`, from `sec:mvba-instantiation` to the end of `subsec:mvba-correctness` | byte-identical | rewritten. The protocol prose now has 15 named paragraphs, where it had 4. The correctness section has 5 new results: `rem:execution-model`, `lem:decision-propagation`, `lem:view-sync`, `lem:convergence` and `lem:good-view` |
| Statements of every `lem:`/`thm:`/`cor:`/`rem:` in that section | — | unchanged up to whitespace, except for four: `rem:lock-monotonicity` gains one clause, and `lem:proposability`, `thm:termination` and `cor:mvba-recovery-termination` are restated |
| The timeout sentence of `subsec:mvba-protocol` | — | "exceeds `Δ_R + 3Δ + max{Δ, Δ_sync}` … backoff … eventually increased" becomes "the fixed, known value `T := Δ_R + 4Δ + max{Δ, Δ_sync}`" |
| `sec:reliable-delivery` | — | was a pointer to an external design note. It gains a "Future-view message retention" paragraph |
| `src/p2_mvba.tex` (`mod:mvba`, main body) | byte-identical | Agreement changes from `B = B'` to `entries(B) = entries(B')` (`d598c5a`). Integrity, External validity, Termination and Quiescence are unchanged |

**The method, so it can be re-run.**

* Extract both revisions with `git show` into a scratch directory.
* Cut the MVBA section at its `\section{Concrete MVBA Instantiation}` and `\subsection{The First ``Dummy'' View}` boundaries, then `cmp` and `diff` the cut sections.
* Extract `\label{…}` sets from `alg_mvba.tex` and from the cut section, and compare them with `comm`.
* Compare each result's statement text after collapsing whitespace. A short script does this: it takes the text from the label to the environment's `\end`.

Two cautions:

* `alg_mvba.tex` carries commented-out drafts. At `b838e17` these include a second `\label{alg:mvba}` and a commented `lem:vote-uniqueness` in the section. A label diff over raw text that is not deduplicated therefore reports phantom removals: `alg:mvba` and `lem:vote-uniqueness` look removed, and neither is.
* The same holds for `line:mvba:tfp-commit`, which sat in a LaTeX comment.

**The anchor verdict.** No anchor the model cites was renamed. Only one was removed: `line:mvba:td-decide`. `line:mvba:hp-pool`, also removed, is not cited as a label. All seventeen correctness anchors of [MvbaPlan.md](MvbaPlan.md) §0 resolve at `eb1bb51`. The new anchors are listed in MvbaPlan §11.1.

### 7.3 Main-body drift, found alongside the review

§1's claim is that the verified surface is byte-identical to arXiv v2. That claim was checked at `026dc8b`. At `eb1bb51` it no longer holds for the repository's head. Between `026dc8b` and `eb1bb51`, six of §1's eleven files changed: `src/alg_da.tex`, `src/alg_fallback.tex`, `src/alg_proposer.tex`, `src/p1_informal.tex`, `src/p2_chorus.tex` and `src/p2_mvba.tex`. That is 68 insertions and 38 deletions over 18 commits (2026-09-05 to 2026-09-21).

For `p2_mvba` the change is the Agreement edit above. On a first reading, the rest consists of:

* domain-separation tags on the proposer's two signatures (`Root`, `Prop`) and on `σ_p` in `line:fb-cast-entry`;
* positional erasure-code fragments with Merkle proofs in `alg:da`;
* the per-slot dispatch convention;
* prose in `p1_informal` and `p2_chorus`.

These look below the Chorus model's abstraction, but none of them was analysed here. They are Chorus-side and outside the MVBA upgrade. **The models still verify arXiv v2.** What changed is that the repository's head has moved ahead of v2, and a v3 would carry these changes.

The re-check is §1's procedure, run against `eb1bb51` instead of v2. It is due before any claim is made about the repository head, and at the latest when a v3 appears. MvbaPlan §11.3 C19 lists two MVBA-section sentences that belong to the same Chorus-side reading.

### 7.4 Paper-side observations at `eb1bb51`

These update §6.

* **Resolved:**
  * the three truncated `\mainref{mod}` and `\mainref{prop}` citations. None is left in `supplementary-internal.tex`.
  * the capped-backoff finding (§6, last item). The timeout is now the fixed `T`, and `thm:termination`'s setting says so. What remains of the old text is the `sec:timing-constants` stub, which still lists "the MVBA view timeout and its backoff policy".
* **Still present:**
  * `supplementary-internal-bkp.tex` is still in the tree, so §1's exclusion rule still applies.
  * The equivocation-evidence subsection still says that `EquivCert`s "are assembled only when an MVBA input is built from two conflicting positive fallback entries". That contradicts `sec:fallback-transition`, as before.
* **New:** the supplement's paragraph "Agreement and Integrity over entries" says that the main-body `mod:mvba` "should be revised to these forms", meaning both Agreement and Integrity. `d598c5a` revised only Agreement. Integrity in the main body still reads "decides at most once", while the supplement permits redelivery of a decision with the same entry vector. The class this development uses is unaffected (MvbaPlan §11.3 C1). The paper, however, is internally inconsistent on this point until the Integrity line follows.
