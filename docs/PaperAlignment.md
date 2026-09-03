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

## 1. The verified surface, and how to re-check it

The models cite the paper by stable LaTeX anchor (never by page or line —
see [`../CLAUDE.md`](../CLAUDE.md)). Every anchor cited by a model or a
design document resolves in one of eleven files:

`src/alg_proposer.tex`, `src/alg_voting.tex`, `src/alg_fast.tex`,
`src/alg_fallback.tex`, `src/alg_da.tex`, `src/p2_problem_definition.tex`,
`src/p2_framework.tex`, `src/p2_mvba.tex`, `src/p2_chorus.tex`,
`src/p2_conductor_proofs.tex`, and — for one anchor only,
`section:conductor-overview`, cited where
[`ConductorDesign.md`](./ConductorDesign.md) contrasts the paper's informal
and formal presentations of the Conductor — `src/p1_informal.tex`.

That set *is* the verified surface: Part 2, the algorithm floats, and a
single Part 1 overview anchor. No model and no design document cites the
internal supplement (§2) — with two deliberate exceptions, both introduced
by this audit and both about the supplement rather than resting on it:
§§3–4 below, and the `sec:domain-separation` item in
[`TODO.md`](./TODO.md). A future check should expect supplement anchors in
exactly those two places.

So the alignment question reduces to whether those eleven files have
changed, which is mechanically checkable against the published source:

```
mkdir -p papers/cadence && curl -sL https://arxiv.org/e-print/2607.02275v2 | tar -xz -C papers/cadence
```

then diff each extracted file against its `src/` counterpart in the paper
repository. (`papers/` is gitignored. Note the flat layout: the e-print has
`alg_da.tex` where the paper repository now has `src/alg_da.tex`.)

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
  such in [`ChorusDesign.md`](./ChorusDesign.md).
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
by counting". `FallbackReceipt.lean`'s `equiv_available` mirrors that middle
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
([`ChorusDesign.md`](./ChorusDesign.md) §7.2).

**Chunk re-dissemination.** `Chorus.lean` justifies (F-justice) on
`redisseminate_chunk` by the re-encode-and-send being performed by honest
parties at `line:fb-redisseminate` and `line:fb-commit-wait`. The
implementation drops the first. The second survives, chunks are
disseminated unconditionally, and the supplement's new `Δ_sync` argues
availability from the `f+1` signers of a positive `FallbackQC` — the same
chain the model's `redisseminate_chunk` encodes. So the assumption holds,
but its implementation-side discharge now routes through ChunkSync, which
the supplement flags as required for liveness and has not yet specified.

**The ACS median.** [`Windows.lean`](../Cadence/Windows.lean)'s median
lemma is abstract over a total order, so it transfers to deadlines
unchanged; what does not transfer is the reading, since `win_first` is the
ACS-decided slot-number median and `prop:acs-nonoverlap` is stated over
slot numbers.

## 4. The MVBA: a contract here, an algorithm there

`mod:mvba` in the published paper is an interface — `propose`, `abandon`,
`decide` — plus five properties (Agreement, Integrity, External validity,
`ℓ_MVBA`-Termination, Quiescence). It specifies no algorithm, which is why
this development consumes the MVBA as an oracle under (A-mvba)
([`Architecture.md`](./Architecture.md) §4 item 2) and why `ℓ_MVBA` is a
parametric hole ([`Bounds.md`](./Bounds.md) §1).

The supplement now closes that hole on paper. `sec:mvba-instantiation`
gives a concrete leader-based protocol across `alg:mvba`, `alg:mvba-cont`
and `alg:mvba-cont2`: views with a leader, Pre-Prepare/Prepare/Commit with
`PrepQC` and `CommitQC`, timeout certificates, view synchronisation
adopting the highest `PrepQC` as a lock, and persist-before-send with
atomic reload. `subsec:mvba-correctness` discharges the module's properties
with roughly fifteen lemmas, `thm:agreement` and `thm:termination`, the
latter at `O(fΔ)`.

Three consequences for this repository, none urgent:

1. `ℓ_MVBA` acquires a concrete candidate value, `O(fΔ)`. It stays a paper
   quantity — the models are untimed — but
   [`Bounds.md`](./Bounds.md)'s "parametric hole" now has a referent.
2. The open item of instantiating the primitive classes end-to-end
   ([`ChorusDesign.md`](./ChorusDesign.md) §9) acquires a concrete target:
   a Veil model of `alg:mvba` discharging `MVBA` from
   [`Primitives.lean`](../Cadence/Primitives.lean).
3. **An agreement-level observation.** `mod:mvba` states Agreement as
   metablock equality, and `Primitives.lean`'s `MVBA.agreement` mirrors it
   as value equality. The supplement's `thm:agreement` proves the weaker
   entries-level statement, and says so deliberately: agreement is over a
   metablock's entries, the certificates being carried only so validity can
   be checked. Chorus needs no more than that, and the Chorus model already
   works at that level — its oracle shadow is the per-proposer
   `mvba_decided_pos`/`mvba_decided_neg` with `mvba_decided_pos_unique`. So
   the right instantiation of the class's `value` is the entry vector, not
   the metablock. This is the one place where this development's abstraction
   matches the supplement rather than the published contract, and it is the
   sound direction: assuming the stronger contract while needing only the
   weaker one.

## 5. What this implies for the models

Nothing. No model changes, and no change to what this repository claims:
the published algorithms are unchanged, and the divergences above are
between the paper's two documents.

What is worth doing is documentary, and is tracked in
[`TODO.md`](./TODO.md): cite `sec:domain-separation` where the network
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
