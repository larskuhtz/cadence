# Conductor & Cadence — module decomposition and design record

*The design rationale for the two smaller Veil models and the composition
layer that joins them to Chorus: §1 how the paper describes the Conductor,
§2 the module decomposition and the class layer, §3 what is safety-shaped in
the Conductor versus what stays meta, §4 the Cadence glue module and where
the top-level properties live, §5 how "Chorus ⊨ SlotConsensus" is discharged.
Lean sources cite these sections by number. For what is proven read
[`../README.md`](../README.md) and [`Architecture.md`](./Architecture.md); the
models' own headers ([`../Cadence/Conductor.lean`](../Cadence/Conductor.lean),
[`../Cadence/Cadence.lean`](../Cadence/Cadence.lean)) carry the detail.
A register note: this document was written as the design plan and keeps that
voice — every "model X as …" below **is implemented**; where the prose and a
model disagree, the model headers are authoritative.*

## 1. Source map (what to read)

The rendered paper describes the Conductor twice, **consistently on ACS**:

* `p1_informal.tex` `§section:conductor-overview` (the rendered
  overview): validators propose first-slot *deadlines* for the next
  window, feed them into an off-the-shelf **ACS**, and take the
  **median** of the decided vector as the agreed deadline.
* `p2_conductor_proofs.tex` `§section:conductor-formal` (active lines
  ~285–1260; the rest of the file is commented-out older drafts): windows
  over **ACS** (`mod:acs`) — each validator proposes the next window's
  *first slot* (deadlines are fixed, read-only data), ACS decides a set
  of ≥ 2f+1 (validator, slot) pairs, and everyone opens the window
  starting at the **median** of the decided slot numbers. This is the
  version the proofs cover (`algorithm:conductor`, Lemmas Integrity /
  Monotonicity / (2W−p)-Boundedness / Totality / (2Wτ)-Recovery).

**Model the formal version** — it is what is proven. The one
informal↔formal difference is deliberate (confirmed by the paper's
authors, 2026-08-20): the overview agrees on the first slot's *deadline*,
the formal part on the first *slot* over read-only deadlines — the same
idea under the two equivalent views (moving deadlines ↔ skipping slots,
`p2_framework.tex` §orchestrator).

A source-tree trap worth recording: the Overleaf tree also carries
`p2_conductor.tex` (+ `p2_conductor_alg.tex`, `p2_conductor_module.tex`),
an older **deadline-MVBA** draft with a leftover reviewer comment ("Not
compatible with API. It assumes MVBA"). These files are **not** input by
`main.tex` and are not part of the paper — both this document (in an
earlier revision) and the 2026-08 external audit (Finding 5) mistook them
for the paper's prose. When citing, check the anchor's file is actually
rendered.

The composition lives in `p2_framework.tex`: `mod:slotconsensus` (the
interface Chorus implements), `mod:orchestrator_2` (the interface
Conductor implements: Totality, Integrity, Monotonicity, B-Boundedness,
R-Recovery), `algorithm:cadence` (the glue: opened/skipped bookkeeping,
pending set, `ready_to_append` log assembly), and
`§subsection:correctness_cadence` (MCP Safety / ℓ-Liveness /
c-Censorship-Resistance / Hiding / B-Bounded-Concurrency from the two
module contracts). The MCP problem definition (logs, consistency, the
four properties) is `p2_problem_definition.tex`.

## 2. Architecture: three modules + a class layer

```
                    ┌────────────────────────────────────────────┐
   plain Lean /     │ MCP positional-log safety, ℓ-liveness,     │
   meta layer       │ c-censorship-resistance (timed statements) │
                    └───────────────▲────────────────────────────┘
                                    │ derived from
                    ┌───────────────┴────────────────────────────┐
   Veil module      │ Cadence (glue, = algorithm:cadence)        │
   (new, small)     │ slot-indexed MCP safety, skip agreement,   │
                    │ per-slot inclusion lift, hiding reduction  │
                    └───▲──────────────────────────▲─────────────┘
              consumes  │ SlotConsensus oracle     │ Orchestrator oracle
                        │ (finalize per slot)      │ (open per slot)
        ┌───────────────┴───────────┐  ┌───────────┴───────────────┐
        │ Chorus                    │  │ Conductor                 │
        │ ⊨ SlotConsensus           │  │ ⊨ Orchestrator            │
        │ (MVBA as oracle)          │  │ (ACS as oracle)           │
        └───────────────────────────┘  └───────────────────────────┘
```

The **oracle pattern** is the one already established twice (MVBA inside
Chorus; and it is how Veil abstracts sub-routines generally): the
consumed primitive's *safety* properties become `require` clauses of
oracle actions (then lifted to invariants), its *liveness* properties
become named meta-axioms ((A-mvba)-style), and the class in
`Cadence/Interfaces.lean` documents the full contract that an implementation
must discharge. Each module is verified independently against the
oracle contract.

### The class layer (`Cadence/Interfaces.lean`)

The contracts live in their own file rather than in
`Cadence/Primitives.lean`, deliberately: `Cadence/Chorus.lean` imports
`Primitives`, so extending it would invalidate Chorus's olean and force a
full re-sweep. Obligation tables are in the class docstrings.

* `SlotConsensus` — agreement, slot safety, proposal inclusion
  (conditional on the synchrony premise), ℓ-termination, **and
  d_tot-totality**. Note: totality is *not* part of `mod:slotconsensus`;
  it is a Chorus-specific strengthening (`prop:chorus-totality`) that
  Conductor's totality proof consumes (`lemma:conductor-totality`, via
  Φ_oc = ℓ_chorus + d_tot). Model it as a separate field or an extending
  class `SlotConsensusWithTotality` so the base class stays the paper's
  module. Instance: Chorus (see §5).
* `ACS` — agreement, validity (≥ 2f+1 pairs; correct pairs genuine),
  integrity, ℓ-termination, Δ-totality (`mod:acs`). Implementation out
  of scope (standard primitive), like MVBA.
* `Orchestrator` — totality, integrity, monotonicity, B-boundedness,
  R-recovery (`mod:orchestrator_2`). Instance: Conductor.

## 3. The Conductor Veil module

### What is safety-shaped (SMT-checkable), from the paper's own proofs

* **Window-entry integrity and order** — a validator enters each window
  at most once, and window ω only after ω−1.
* **Cross-window slot monotonicity** — the decided first slot of ACS[ω]
  is ≥ last slot of window ω−1 + 1 (paper: `s ≥ s' + W`). Via the ACS
  oracle's agreement + the honest propose-guard (`s* > last[cw]`,
  `line:sstar-guard`) + median range validity (see below).
* **Window-assignment agreement** — any two correct validators that
  place slot s in a window place it in the same window; hence the same
  deadline (the Conductor-module "Safety").
* **Opened-set structure** — `opened_i` is a union of per-window
  intervals of width W; windows' intervals are disjoint and increasing.
  This replaces the paper's cardinality statement ("exactly ω·W slots")
  with an interval formulation that stays in relational logic.
* **Boundedness as interval inclusion** — from the `ready_for_next_window`
  guard: on entering ω+1, all opened slots outside the last W−p of
  window ω are completed. Invariant: every opened-but-uncompleted slot
  lies in the last two windows' tail intervals. The numeric bound
  (2W−p) is a one-line corollary at the meta/Lean level — do **not**
  attempt cardinality counting in SMT.
* **Integrity part 2** ("no open before the slot's starting time") —
  trivial given the clock-guard on the open action (see §4, clocks);
  the real content is the clock-synchronization assumption.

### What stays meta (documented axioms + fair-progress invariants)

Exactly the Chorus doctrine:

* **Totality** (d_tot) and **(2Wτ)-Recovery** — the paper's proofs are
  genuinely temporal (per-window induction "if all windows before ω went
  well…", the four parameter assumptions
  `(p−1)τ + Φ_oc + ℓ ≤ Wτ` etc., T₁/T_p bookkeeping). Mirror the
  induction as *conditional* meta-axioms, and SMT-check the
  fair-progress content: e.g. "once all slots through the sync boundary
  of ω are completed and ACS[ω+1] has decided, the enter-window action
  is enabled", "the ACS propose guard is eventually satisfiable", plus
  the (A-acs) axiom (ACS decides once all correct validators propose).
* The **parameter assumptions** (lines `assumption-one..four`) are
  arithmetic side conditions on constants — state them as documented
  assumptions; they only feed the timing lemmas.

### Modelling ingredients beyond Chorus's

1. **Ordered slot/window theory.** Chorus deliberately avoided
   arithmetic; Conductor needs slot numbers with order and *window
   structure*. The window→interval assignment **cannot** be static
   uninterpreted theory (`win_of`, `win_first/win_last` with Horn
   axioms): a window's first slot is decided at runtime by `ACS[ω]`
   (`line:median-compute`), so the assignment is execution-dependent
   state. The encoding therefore splits — static order structure only
   (`TotalOrderWithMinimum` on `slot` and `window`, no `+W` arithmetic in
   the SMT layer), with the intervals themselves as oracle state in the
   Conductor. That split introduces **no new axioms**; the details are in
   [`../Cadence/Windows.lean`](../Cadence/Windows.lean).
2. **Median / range validity.** The median of the decided ACS set lies
   between two correct proposals (≤ f faulty among ≥ 2f+1). This is
   order-statistics counting — same species as the ByzNodeSet counting
   axioms. Fold it into the window-decision oracle action as a `require`
   (`∃ honest r1 r2: proposal r1 ≤ s* ≤ proposal r2`), justified by a
   Lean-proven median lemma for the concrete instance.
3. **Abstract clock.** A monotone global `now` (ordered type, advanced
   by a nondeterministic tick action) with guards like
   `require start_time s ≤ now` on `open`. Timing *properties* stay
   meta; the clock exists only to make guards like "not before the
   starting time" and "propose on time vs late" expressible. Clock
   synchronization across validators (the paper assumes synchronized
   clocks) is thereby an explicit modeling assumption — document in the
   threat model. This is the Conductor analogue of Chorus's `Phase`
   enum, but shared across slots.
4. **Multi-slot indexing.** Conductor state is genuinely multi-slot
   (opened/completed per slot) — fine, that is ordinary Veil relation
   indexing; only Chorus was deliberately single-slot.

### Adversary

Conductor itself has no Byzantine message surface beyond ACS (its only
inputs are local `completed(s)` callbacks and ACS decisions). Byzantine
influence enters via (i) ACS decided sets containing up to f faulty
pairs — captured by the oracle validity require + median range, and
(ii) Byzantine validators' own ACS proposals — free oracle inputs. This
makes the Conductor module *much* lighter than Chorus (no quorum
machinery of its own; ByzNodeSet needed only for the median lemma).

## 4. The Cadence glue module and the top-level properties

Model `algorithm:cadence` as its own small Veil module:

* State (per validator): `opened`, `skipped`, `pending(s, v)`,
  `appended(s, v)` (the log as a slot-indexed relation — the ordered-list
  view is recovered from slot order), plus the proposer's `proposed(s)`.
* Oracle actions:
  - `orch_open(i, s)` — gated by the Orchestrator contract's safety
    requires (integrity: not opened before; monotonicity: no
    higher-numbered slot opened; totality is meta).
  - `sc_finalize(i, s, v)` — gated by the SlotConsensus contract's
    agreement (any two finalizations of s agree — cross-validator *and*
    per-validator) and slot safety.
* Protocol actions: append when `ready_to_append` (every smaller slot
  skipped-or-appended — expressible relationally), complete/abandon
  bookkeeping.

**Slot-indexed MCP safety, in the glue module (SMT):**

* per-slot log agreement: honest i, j with `appended(i, s, v)` and
  `appended(j, s, v')` ⇒ `v = v'` (from the finalize oracle's agreement);
* skip agreement: if honest i appended for s, no honest j that has
  resolved past s skipped s (from orchestrator totality+monotonicity —
  note the *safety-usable* residue of totality here is the paper's
  argument "j opened a higher slot without opening s ⇒ j never opens s,
  contradicting totality"; in the monotone model this becomes an
  invariant relating `appended`/`skipped` across validators, gated by
  the orchestrator oracle's requires);
* per-slot inclusion lift: under the `all_honest_recorded`-style premise
  the finalized v contains the correct proposer's proposal — this is
  imported through the SlotConsensus oracle's (conditional) inclusion
  require, instantiated by Chorus's `proposal_inclusion`;
* bounded concurrency: participation interval = open-to-complete —
  immediate from the orchestrator boundedness contract (interval form).

**Positional/timed MCP statements, in plain Lean / meta:**

* Def. `safety` (prefix consistency of `local_log(p, t)` as ordered
  lists) follows from per-slot agreement + skip agreement by the paper's
  own two-case argument — a small list lemma over the slot-indexed
  relations; this is naturally a plain-Lean theorem *about* the glue
  module's reachable states, not an SMT invariant (positions are list
  arithmetic).
* ℓ-liveness and c-censorship-resistance carry real-time parameters
  (GST + R, ℓ_MVBA, …) — they compose the meta-layer termination /
  recovery axioms and live at the meta layer, exactly like Chorus's
  ℓ-termination does today.
* Hiding: the paper's composition lemma is one line (proposals only
  flow through per-slot instances); at this abstraction the glue module
  simply has no other channel — document, and keep the protocol-level
  share-gating theorem in Chorus (`hiding_until_deadline`).

**Answer to the open question, explicitly:** Conductor's properties do
*not* capture the top-level properties (its interface never carries
proposal vectors, so log agreement is not even expressible there), and
the top-level properties are *not* proven from scratch in Lean either:
the slot-indexed core is SMT-checked in the glue module, and only the
formulation-level lifting (list positions, wall-clock parameters) is
plain Lean/meta. This mirrors the paper's proof structure one-to-one,
which is the property that keeps the model reviewable against it.

## 5. Connecting the layers (how "Chorus ⊨ SlotConsensus" becomes real)

Two levels, both in place.

### 5.1 Contract-mirroring

The glue module's oracle `require`s are stated to be *syntactically* the
class properties, and each class field carries a doc pointer to the
discharging theorem (`Chorus.agreement_pos`, `Chorus.proposal_inclusion`,
`Chorus.hiding_until_deadline`, meta-axiom names for
termination/totality). An obligation table in the class docstring keeps
this auditable.

### 5.2 Lean instance theorems

The class is stated over an abstract "finalization predicate" and
`Chorus ⊨ SlotConsensus`'s safety fields are proven by instantiating with
Chorus's committed-relations and citing the persisted reachable-state
theorems — the safety fields are precisely Chorus's proven invariants, so
the proofs are `exact`-level
([`../Cadence/Chorus/Compose.lean`](../Cadence/Chorus/Compose.lean)). A
full trace/refinement treatment is the `ChorusDesign.md` §10.1 research
item — out of scope here.

## 6. Stake weighting

Out of scope, but not precluded: every quorum argument in Chorus goes through
the `ByzNodeSet` *predicates* (`supermajority`, `greater_than_third`)
and its counting axioms — never through explicit cardinalities. A
stake-weighted deployment is a different *instance* of the same class
(supermajority = "> 2/3 of stake", plus re-proving the counting axioms
under weight arithmetic — all remain true with weight in place of
count). Design rules to preserve this:

* never case on set sizes or node counts in models or invariants — only
  on the quorum predicates;
* keep new counting facts as ByzNodeSet-style axioms with instance
  proofs (the weighted instance then re-proves the same fields);
* the Conductor median lemma should likewise be stated over an abstract
  "correct majority in the decided set" predicate.

The genuinely open issue — weighted DA/erasure-chunk assignment — is a
protocol-design question (chunks-per-validator proportional to stake vs.
the f+1-of-n decode threshold) and does not block the consensus-layer
model; Chorus's chunk quorums would follow whatever quorum predicate the
weighted instance provides.

## 7. Scope notes

* The rendered paper's two Conductor descriptions agree on ACS; the
  deliberate overview↔formal difference (agree on the first slot's
  *deadline* vs. on the first *slot* over read-only deadlines) is the
  deadline↔slot equivalence of §1. The model follows the formal
  version. (`p2_conductor.tex`'s deadline-MVBA variant is an unrendered
  draft — see the §1 source-tree note.)
* Validator-set changes, epochs and proposer rotation are outside the
  paper's consensus-layer treatment: `s.proposers` is an immutable
  per-slot relation (generalizing Chorus's single-slot `is_proposer`).
* Chorus's `participate()/abandon()` conformance (the glue calls
  abandon only after finalize) is currently a documented scope note in
  Chorus; the glue module makes it checkable structurally (abandon
  action gated on finalize).
