# Conductor & Cadence composition — feasibility study and plan

*Historical. Written 2026-07-03, after the Chorus Build #10 paper-alignment
refactor, as the working plan for extending the verification from the Chorus
slot consensus to the Conductor orchestrator and the Cadence composition.
**All phases C0–C4 are complete**; the plan is kept because its §2 (the
module decomposition against the paper), §3 (what is safety-shaped versus what
stays meta) and §5.2 (how "Chorus ⊨ SlotConsensus" is discharged) are still
the rationale for how the code is arranged, and because other files cite it by
section. For the current state read [`../README.md`](../README.md) and
[`Architecture.md`](./Architecture.md); where the implementation deviated from
this plan, the Status section below says so.*

## Status (updated 2026-07-03, same-day implementation session)

**C0–C3 are implemented and green.** See `History.md` ("Conductor & Cadence
composition — verification status") for the build inventory. Deviations
from the plan as written, each deliberate:

* **C0** — the contract classes live in a new file
  [`Cadence/Interfaces.lean`](../Cadence/Interfaces.lean), *not* `Cadence/Primitives.lean` as §2
  says: `Cadence/Chorus.lean` imports `Cadence/Primitives.lean`, so extending it would
  invalidate Chorus's olean and force a full re-sweep (~9 min). Obligation
  tables are in the class docstrings as planned.
* **C1** — [`Cadence/Cadence.lean`](../Cadence/Cadence.lean) (replaces the pre-Chorus
  scaffolding that file held). One decomposition: the paper's bulk
  implicit-skip recording is a separate per-slot `record_skip` action
  (bulk order-conditioned updates need `decide`d order predicates, which
  the trace pipeline cannot translate).
* **C2** — [`Cadence/Windows.lean`](../Cadence/Windows.lean). The static
  `win_of`/`win_first`/`win_last` theory of §3 turned out wrong in kind:
  window intervals are ACS-*decided at runtime*, so they are oracle
  state in the Conductor, and the static side reduces to the existing
  `TotalOrderWithMinimum` (no new axioms at all). The median lemma is
  fully proven in Lean (`lowerMedian_between_correct`), stated over an
  abstract correctness predicate per §7's stake-weighting rule.
* **C3** — [`Cadence/Conductor.lean`](../Cadence/Conductor.lean). The §3 invariant set is
  discharged fully automatically (no manual `@[veil]` theorems needed —
  the witness-materialisation discipline was applied up front: the
  ACS-decide oracle takes the predecessor window and the lower median
  witness as parameters). Boundedness is stated as the persisted
  readiness residue (contrapositive of §3's tail-interval form — more
  inductive). The upper median bracket is documented but not modelled
  (only recovery timing consumes it, which is meta).
* **C4** — done for Cadence/Conductor; Chorus leg **unblocked
  2026-07-07** (was tooling-blocked 2026-07-06). Mechanism:
  `#gen_theorems` in each module persists the discharged VCs as
  environment theorems; [`Cadence/Composition.lean`](../Cadence/Composition.lean)
  composes them by induction over the generated `reachable` relation
  into `<Module>.invariants_of_reachable`, then projects. Done: Cadence
  + Conductor inductions, the `Conductor ⊨ Orchestrator` instance
  (`orchestrator_instance`), and **the paper's positional MCP Safety**
  (`positional_log_safety` — `def:safety` over ordered logs, via the
  generic `sorted_prefix_agreement` list lemma). The former blocker —
  `#gen_theorems` on Chorus did not scale (witness retention → >40 GB;
  lazy mode → a serial second sweep; see [`Architecture.md`](./Architecture.md)
  §6) — was
  removed by Veil's trusted statement-only persistence
  (`veil.gen.trustedTheoremStubs`, Veil `2d889743`): Chorus now runs
  `#gen_theorems` at no measurable cost (Build #14, 3 784 theorems,
  +7.5 MB olean). Everything Chorus-side that the instance needs is in
  place (the `[local_committed_complete]` invariant, green; persisted
  theorems verified consumable) and the construction is worked out
  (per-proposer decision maps as proposal vectors; agreement via
  `agreement_pos`/`agreement_pos_neg` + completeness; inclusion via
  `proposal_inclusion`/`_no_neg`). ✅ **C4 COMPLETE 2026-07-07**: a
  generated composition module (the 97-declaration × 39-case
  `invariants_of_reachable` induction over the Build #14 persisted theorems,
  one bounded lemma per action case, **plus a named reachability projection
  `Chorus.reachable_<property>` per declaration**, ending positional-index
  consumption — since superseded by Veil's own `#gen_composition` in
  [`Cadence/Chorus/Certify.lean`](../Cadence/Chorus/Certify.lean), and the
  generator scripts deleted) and
  [`Cadence/Chorus/Compose.lean`](../Cadence/Chorus/Compose.lean)
  (`Chorus.slotConsensus_instance` — decision vectors gated on
  `is_proposer`, the three formal `SlotConsensus` fields discharged;
  trust base pinned by a `#guard_msgs` axiom check to exactly the
  sweep's own `sorryAx` + the standard trio). Elaboration is a
  non-event: 19 s for the generated file, 6 s for the instance.

The §1 divergence flag (prose deadline-MVBA Conductor vs. proven
slot-ACS Conductor) stands and is recorded in `Cadence/Conductor.lean`'s header;
it still needs to be raised with the paper authors.

## 0. TL;DR

* **Feasibility: high** for everything that was in scope for Chorus
  (safety proven in Veil; timing/liveness as documented meta-axioms plus
  SMT-checked fair-progress). No Veil core changes required; all Build #10
  techniques (oracle sub-protocols, certificate materialisation, history
  variables, stub dischargers) carry over.
* **Architecture: three Veil modules + a class layer**, mirroring the
  paper exactly: `Chorus` (done) ⊨ SlotConsensus; new `Conductor` ⊨
  Orchestrator (with ACS as an oracle); new `Cadence` glue module (the
  paper's `algorithm:cadence`) consuming *both* primitives as oracles and
  carrying the top-level MCP safety properties in slot-indexed form.
* **Where the top-level properties live** (the open question): neither
  "inside Conductor" nor "all in plain Lean". Conductor proves only the
  orchestrator contract — it never sees finalized values, so it *cannot*
  express log agreement. The MCP properties live in the thin `Cadence`
  glue module (slot-indexed forms, SMT-checked), with the positional-log
  and real-time-parameterised formulations (Def. safety over prefixes,
  ℓ-liveness, c-censorship-resistance) derived on top in plain Lean /
  meta — because those quantify over list positions and wall-clock time,
  which the Veil layer deliberately abstracts.
* **Effort estimate: ~4–8 focused sessions** to a green
  Conductor + Cadence-glue with documented meta layer; +1–2 optional
  sessions for Lean-level instance theorems connecting the layers
  formally. Detailed phasing in §6.

## 1. Source map (what to read)

The Conductor exists in the paper in **two not-yet-reconciled versions**:

* `p2_conductor.tex` (prose §"Conductor"): windows with a *deadline
  agreement* (median MVBA over proposed first-slot deadlines). Contains a
  reviewer comment flagging the API mismatch ("Not compatible with API.
  It assumes MVBA").
* `p2_conductor_proofs.tex` `§section:conductor-formal` (active lines
  ~285–1260; the rest of the file is commented-out older drafts): windows
  over **ACS** (`mod:acs`) — each validator proposes the next window's
  *first slot*, ACS decides a set of ≥ 2f+1 (validator, slot) pairs, and
  everyone opens the window starting at the **median** of the decided
  slot numbers. This is the version the proofs cover
  (`algorithm:conductor`, Lemmas Integrity / Monotonicity /
  (2W−p)-Boundedness / Totality / (2Wτ)-Recovery).

**Model the ACS version** — it is what is proven. Flag the divergence to
the paper authors; the prose version's "deadline agreement" and the
formal version's "slot selection" are the same idea under the two
equivalent views (moving deadlines ↔ skipping slots,
`p2_framework.tex` §orchestrator).

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
        │ Chorus (done, Build #10)  │  │ Conductor (new)           │
        │ ⊨ SlotConsensus           │  │ ⊨ Orchestrator            │
        │ (MVBA as oracle)          │  │ (ACS as oracle)           │
        └───────────────────────────┘  └───────────────────────────┘
```

The **oracle pattern** is the one already established twice (MVBA inside
Chorus; and it is how Veil abstracts sub-routines generally): the
consumed primitive's *safety* properties become `require` clauses of
oracle actions (then lifted to invariants), its *liveness* properties
become named meta-axioms ((A-mvba)-style), and the class in
`Cadence/Primitives.lean` documents the full contract that an implementation
must discharge. Each module is verified independently against the
oracle contract — exactly the modularity requested.

### Classes to add to `Cadence/Primitives.lean`

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

### New modeling ingredients (the actual technical risk)

1. **Ordered slot/window theory.** Chorus deliberately avoided
   arithmetic. Conductor needs slot numbers with order and *window
   structure*. Recommended encoding (keeps EPR-friendliness, follows the
   NOPaxos `seq_t`/TotalOrder precedent): an uninterpreted `slot` type
   with a total order, plus uninterpreted functions
   `win_of : slot → window`, `win_first/win_last : window → slot`,
   `win_next : window → window`, with Horn axioms tying them together
   (first ≤ last, slots of a window form the interval, next-window
   intervals are above, sync-boundary slot between first and last).
   Prove the axioms satisfiable with a concrete ℕ instance (same
   discipline the user set for ByzNodeSet: new axioms come with instance
   proofs). Avoid raw `+W` arithmetic in the SMT layer.
2. **Median / range validity.** The median of the decided ACS set lies
   between two correct proposals (≤ f faulty among ≥ 2f+1). This is
   order-statistics counting — same species as the ByzNodeSet counting
   axioms. Fold it into the window-decision oracle action as a `require`
   (`∃ honest r1 r2: proposal r1 ≤ s* ≤ proposal r2`), justified by a
   Lean-proven median lemma for the concrete instance (small, ~the size
   of the Build #10 ByzNodeSet additions).
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
  flow through per-slot instances); at our abstraction the glue module
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

Two levels, do the first now and treat the second as a stretch goal:

1. **Contract-mirroring (cheap, do in C1/C2):** the glue module's oracle
   `require`s are stated to be *syntactically* the class properties, and
   each class field carries a doc pointer to the discharging theorem
   (`Chorus.agreement_pos`, `Chorus.proposal_inclusion`,
   `Chorus.hiding_until_deadline`, meta-axiom names for
   termination/totality). An obligation table in the class docstring
   keeps this auditable.
2. **Lean instance theorems (stretch, C4):** state the class over an
   abstract "finalization predicate" and prove
   `Chorus ⊨ SlotConsensus.safety-fields` by instantiating with Chorus's
   committed-relations and citing the `#gen_spec`-generated
   reachable-state theorems (the safety fields are precisely Chorus's
   proven invariants, so the proofs are `exact`-level). A full
   trace/refinement treatment is the ChorusDesign.md §10.1 research item —
   explicitly out of scope here.

## 6. Phased plan with effort estimates

Calibration: the Chorus paper-alignment refactor (Build #10) took one
long session including all verification-engineering battles; the
patterns discovered there (the "editing gotchas" of [`../CLAUDE.md`](../CLAUDE.md)) transfer.

* **C0 — Classes + doc scaffolding (~½ session).**
  `SlotConsensus`, `ACS`, `Orchestrator` classes in `Cadence/Primitives.lean`
  with obligation tables; reconcile naming with `mod:*` anchors. Flag
  the two-Conductor-versions divergence to the paper authors.
* **C1 — Cadence glue module (~1–2 sessions).** Small state machine +
  two oracles; slot-indexed MCP safety invariants; fair-progress
  scaffolding for the append chain. Lowest-risk phase; all hard
  consensus content is behind oracles. Deliverable: green sweep.
* **C2 — Slot/window theory + median lemma (~1 session).** The ordered
  `slot`/`window` classes with Horn axioms + ℕ instance proofs; the
  median range-validity lemma (ByzNodeSet-style, with instance proof).
* **C3 — Conductor module (~2–4 sessions).** State machine per
  `algorithm:conductor` with ACS as oracle and the abstract clock;
  safety invariants from §3; fair-progress + (A-acs)/(A-slot-consensus)
  meta-axioms mirroring the paper's per-window induction. Risk: SMT
  behavior of the ordered-type theory (mitigations: Horn-only axioms,
  interval formulations instead of cardinalities, Build #10 stub
  workflow for stragglers). Deliverable: green sweep + updated
  Design/Notes docs.
* **C4 — Lean composition layer (optional, ~1–2 sessions).** Instance
  theorems (§5.2) + the positional-log safety corollary as a plain-Lean
  theorem. Independent of C1–C3 being useful.

Total: **4–8 sessions** for C0–C3; C4 optional on top. Nothing requires
changes to Veil itself (unlike Build #10's `modelCheckScaffolding`
option, none is currently foreseen — the one candidate would be better
support for background arithmetic types if the Horn-axiom encoding
disappoints).

## 7. Stake weighting (parked, by request)

The door is already open: every quorum argument in Chorus goes through
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

## 8. Known gaps / items to flag

* The prose Conductor (`p2_conductor.tex`) and the formal Conductor
  (`§section:conductor-formal`) disagree (deadline-MVBA vs. slot-ACS);
  the formal one is proven — model it, and surface the divergence.
* `mod:orchestrator_2`'s R-Recovery ("opens s *at* its starting time")
  vs. the Conductor-module draft's weaker "Liveness" — the proofs
  establish (2Wτ)-recovery in the strong sense; use the strong form.
* Validator-set changes / epochs / proposer rotation
  (`papers/specification` §rotation) are outside both papers'
  consensus-layer treatment — keep `s.proposers` an immutable per-slot
  relation for now (generalizing Chorus's single-slot `is_proposer`).
* Chorus's `participate()/abandon()` conformance (the glue calls
  abandon only after finalize) is currently a documented scope note in
  Chorus; the glue module makes it checkable structurally (abandon
  action gated on finalize) — a small faithfulness win of C1.
