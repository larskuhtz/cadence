import Veil

/-! # Module contracts for the Cadence composition

This file collects type-class abstractions for the three *protocol modules*
of the Cadence extreme-pipelining framework, lifted from the paper
(`papers/cadence`, `src/p2_framework.tex` and `src/p2_conductor_proofs.tex`):

* `SlotConsensus` — the per-slot consensus primitive (`mod:slotconsensus`).
  Instance: Chorus ([`Chorus.lean`](./Chorus.lean)).
* `ACS` — agreement on a core set (`mod:acs`), the primitive the Conductor
  orchestrator consumes. Implementation out of scope (a standard primitive,
  treated like `MVBA` in [`Primitives.lean`](./Primitives.lean)).
* `Orchestrator` — the slot-scheduling primitive (`mod:orchestrator_2`).
  Instance: Conductor ([`Conductor.lean`](./Conductor.lean)).

They play the same two roles as the cryptographic classes in
[`Primitives.lean`](./Primitives.lean):

1. **Documentation**: each class states the signatures and properties of the
   module contract that the consuming Veil model relies on, with an
   *obligation table* mapping every property to (a) the paper anchor and
   (b) the discharging artefact — a proven Veil invariant of the
   implementing module, or a named meta-axiom for genuinely temporal
   properties.
2. **Targets for instantiation**: the composition layer (see
   `docs/ConductorDesign.md` §5) instantiates the
   safety-shaped fields from the implementing modules' `#gen_spec`-generated
   reachable-state theorems.

The classes live in this separate file rather than in `Primitives.lean`,
**deliberately**: `Chorus.lean` imports `Primitives.lean`, so extending
that file would invalidate Chorus's compiled artefact and force a full
re-verification sweep. Keeping the module contracts here is what makes
editing the small models cheap — Chorus's oleans stay valid, and only
`Cadence` and `Conductor` import this file. Do not move them.

## Formalisation convention: safety fields vs. temporal obligations

Veil verifies safety (inductive invariants over reachable states). We follow
the established Chorus/MVBA doctrine (`docs/ChorusDesign.md` §7, `Primitives.lean`
`MVBA`):

* Properties whose content is a *state predicate* (agreement, integrity,
  inclusion, prefix consistency) are **class fields** (`Prop`s); the Veil
  implementation discharges them as proven invariants and the consuming
  module imports them as `require` clauses on its oracle actions.
* Properties that are genuinely *temporal or quantitative* (termination,
  totality latencies, `B`-boundedness cardinalities, `R`-recovery) are
  **documented obligations**: they are stated in the docstrings with a
  named meta-axiom label (in the style of Chorus's (A-mvba)) and are
  consumed by the meta-level liveness argument, never by an SMT proof.
-/

/-! ## Contract properties as shared syntax

A contract property is written **once**, as syntax over its carrier, and
then used by both sides: the class field below, and the `safety` /
`invariant` / `require` of every model that implements or consumes it.
Expansion happens before elaboration, so the two sides are the *same term*
by construction — there is no restatement to drift, and the generated
verification conditions are exactly what the models wrote by hand before.

**Why syntax and not a definition over the carrier.** The obvious
alternative — `def OpenPrefixAgreement (byz opened lt) : Prop := …`, applied
at each model's relations — does not survive Veil's SMT translation. The
carrier arrives as a *function argument*, and SMT-LIB is first-order, so the
solver call fails with "cannot translate `fun x x_1 => …`, SMT-LIB does not
support lambdas". Tagging the definition `@[invSimp]` unfolds it where the
invariant clump appears as a *hypothesis*, but not in the goal, so the
failure persists. A ghost relation does not help either: referring to one
without applying it elaborates to a state-closing lambda, which is the same
problem. Applying a ghost relation is fine, which is why the carrier
arguments below are always *applied* after expansion, never passed on.

Consequence for anyone adding a property: substitute only things that are
first-order at the point of use — a relation name, or an applied ghost
relation — and let the macro do the applying. -/

/-- Open-prefix agreement (`mod:orchestrator_2`), as shared syntax: if an
honest validator has opened `s` and another honest validator has opened a
strictly smaller `s'`, the former has opened `s'` too. -/
syntax "openPrefixAgreement% " term:max term:max term:max : term
macro_rules
  | `(openPrefixAgreement% $byz $opened $lt) =>
    `(∀ i j s s',
        ¬ $byz i ∧ ¬ $byz j ∧ $opened i s' ∧ $opened j s ∧ $lt s' s →
        $opened j s')

/-! ## Slot Consensus (`mod:slotconsensus`)

One instance per slot `s`. A validator participates (`participate()` /
`abandon()`), designated proposers submit proposals (`propose(P)`), and the
instance's sole output is the finalization of a single *proposal vector* `V`
(`finalize(V)`).

### Obligation table

| Property (paper, `mod:slotconsensus`) | Kind | Discharged by |
|---|---|---|
| Agreement (incl. per-validator integrity) | field `agreement` | Chorus `safety [agreement_pos]`, `[agreement_pos_neg]` (per-proposer granularity; see below). Formal instance: `Chorus.slotConsensus_instance` (`Chorus/Compose.lean`, 2026-07-07) |
| Slot safety | field `slot_safety` | Chorus: trivial (single-slot model — every commit is for the instance's slot by construction); in the `Cadence` glue module absorbed by slot-indexing of the `finalized` relation |
| Proposal inclusion (conditional on synchrony) | field `proposal_inclusion` | Chorus `safety [proposal_inclusion]`, `[proposal_inclusion_no_neg]` (premise `all_honest_recorded`) |
| Hiding (`def:hiding` specialised to `s`) | documented | protocol half: Chorus `safety [hiding_until_deadline]`; crypto half: `ThresholdIBE.decrypt_secret` (`Primitives.lean`) |
| ℓ-Termination | documented, **(A-sc-termination)** | Chorus fair-progress layer + (A-mvba) meta-argument (`docs/ChorusDesign.md` §7); `ℓ_chorus = 5Δ + ℓ_MVBA` is paper-level (`lemma:chorus-termination`). Since the 2026-07-07 paper revision the premise has an exact name: *Δ-synchronized participation* (`def:delta-synchronized-participation`), running within Cadence; discharged Conductor-side by `thm:conductor-correctness` via `cor:chorus-correctness-within-cadence` |
| Quiescence (no protocol message outside the participation window) | documented | joined `mod:slotconsensus` with the 2026-07-07 participation convention (`lemma:chorus-quiescence`). Temporal/participation property — out of scope for the untimed single-slot Chorus model, whose in-model shadow is phase confinement (`fb_sig_phase`, `mvba_decided_phase`, `fbcommit_sig_phase`); consumed only by the paper-level Conductor argument (ACS abandon/quiescence) |

### Granularity note

Chorus finalizes a proposal vector *per-proposer* (relations
`local_committed_pos i j m` / `local_committed_neg i j`); the abstract
`pvector` of this class corresponds to the total per-proposer map a
validator holds when `local_committed i` is set. The instance theorem
constructs `finalized`/`includes` from those relations.

### On `correct`

The paper states every property for *correct* validators only; Byzantine
validators' outputs are unconstrained. We expose the correctness predicate
as a class field so the properties can be stated faithfully (the `MVBA`
class in `Primitives.lean` leaves it implicit; here the consuming glue
module genuinely needs the distinction, since its own state is per-validator). -/
class SlotConsensus (slot validator proposal pvector : Type) where
  /-- The slot this instance is parameterized by (`s ∈ Slot`). -/
  inst_slot : slot
  /-- The slot identifier a proposal vector carries (`V.slot`). -/
  slot_of : pvector → slot
  /-- `correct i`: validator `i` is correct (non-Byzantine). -/
  correct : validator → Prop
  /-- `finalized i V`: validator `i` has output `finalize(V)`. -/
  finalized : validator → pvector → Prop
  /-- `includes V j P`: proposal vector `V` maps proposer `j` to proposal
      `P` (`V[j] = P`). -/
  includes : pvector → validator → proposal → Prop
  /-- The synchrony premise of proposal inclusion, per proposer: `j` is a
      correct proposer of the instance's slot, `s.deadline − Δ ≥ GST`, and
      `j` submitted `P` at the slot's starting time. The premise is
      per-instance data (fixed by the execution), which is what lets the
      conditional inclusion property be stated at the state level — the
      Chorus analogue is the `all_honest_recorded` hypothesis predicate. -/
  on_time_proposal : validator → proposal → Prop

  /-- **Agreement** — correct validators never finalize conflicting
      proposal vectors. Taking `i = j` also yields per-validator
      integrity ("no correct validator finalizes two different proposal
      vectors, even on separate occasions"). -/
  agreement : ∀ (i j : validator) (V V' : pvector),
    correct i → correct j → finalized i V → finalized j V' → V = V'

  /-- **Slot safety** — a finalized proposal vector carries the instance's
      slot identifier. -/
  slot_safety : ∀ (i : validator) (V : pvector),
    correct i → finalized i V → slot_of V = inst_slot

  /-- **Proposal inclusion** — under the synchrony premise, the finalized
      vector contains the correct proposer's on-time proposal. -/
  proposal_inclusion : ∀ (i j : validator) (V : pvector) (P : proposal),
    correct i → finalized i V → on_time_proposal j P → includes V j P

/-! ## Slot consensus with totality

`d_tot`-**totality** is *not* part of `mod:slotconsensus`; it is a
Chorus-specific strengthening (`prop:chorus-totality`; since the
2026-07-07 revision `d_tot = Δ` — was `2Δ` — and the proposition is
conditioned on Δ-synchronized participation and on running within
Cadence, the same premises as termination):

> **(A-sc-totality)** Under Δ-synchronized participation, within
> Cadence: if a correct validator finalizes the instance at time `t`,
> then every correct validator finalizes it by time
> `max(t, GST) + d_tot`.

The Conductor's totality proof consumes it (`lemma:conductor-totality`,
through `Φ_oc = ℓ_chorus + d_tot`); orchestrators built on a slot consensus
without this property do not achieve the paper's `d_tot`-totality. The
property is temporal, so this class adds no formal fields — it is a marker
carrying the documented obligation, kept separate so that `SlotConsensus`
remains exactly the paper's module (`docs/ConductorDesign.md` §2).

Discharge: meta-level, from Chorus's totality argument (a finalizing
validator's commitment proof — a commitQC or, since the 2026-07-07
revision, the fallback commit certificate `fbCommitQC` — is transferable
and lets every correct validator commit within `Δ`;
`prop:chorus-totality`). -/
class SlotConsensusWithTotality (slot validator proposal pvector : Type)
  extends SlotConsensus slot validator proposal pvector

/-! ## Agreement on a Core Set (`mod:acs`)

Each of the `n` validators proposes a slot; ACS outputs a single agreed set
of at least `2f + 1` (validator, slot) pairs. The Conductor consumes one
instance per window (`ACS[ω]`, `ω ≥ 2`).

Like `MVBA` in `Primitives.lean`, the implementation is out of scope — ACS
is a standard primitive; a concrete implementation would discharge this
class.

### Obligation table

| Property (paper, `mod:acs`) | Kind | Notes |
|---|---|---|
| Agreement | field `agreement` | consumed by Conductor's window-assignment agreement (`prop:window-agreement`) |
| Validity, qualitative half (correct pairs genuine) | field `validity_genuine` | consumed by the median range argument |
| Validity, quantitative half (`|set| ≥ 2f+1`, hence ≥ f+1 correct pairs) | documented | outside the first-order language (cardinality); its *consequence* — the median of the decided slot numbers lies between two correct proposals — is the `Windows.lean` median lemma (C2), which justifies the median-range `require` on the Conductor's ACS-decide oracle action |
| Integrity | field `integrity` | state-level residue of "if a correct validator decides, some correct validator has previously proposed" |
| ℓ-Termination | documented, **(A-acs-termination)** | if all correct validators propose by `t`, all decide by `max(t, GST) + ℓ` |
| Δ-Totality | documented, **(A-acs-totality)** | if a correct validator decides at `t`, all decide by `max(t, GST) + Δ` |

### Relational encoding of the decided set

`decide(set)` outputs a set of pairs; we expose it as the observation
relation `decided i p s` ("`i` has decided, and `(p, s)` is in its decided
set") plus the event marker `has_decided i`. Agreement then says all
correct deciders hold the *same* set. -/
class ACS (validator slot : Type) where
  /-- `correct i`: validator `i` is correct (non-Byzantine). -/
  correct : validator → Prop
  /-- `proposed p s`: validator `p` has input `propose(s)`. -/
  proposed : validator → slot → Prop
  /-- `decided i p s`: validator `i` has decided, with `(p, s)` in its
      decided set. -/
  decided : validator → validator → slot → Prop
  /-- `has_decided i`: validator `i` has decided (some set). -/
  has_decided : validator → Prop

  /-- Every pair observation implies the decision event. -/
  decided_has_decided : ∀ (i p : validator) (s : slot),
    correct i → decided i p s → has_decided i

  /-- **Agreement** — no two correct validators decide different sets: any
      pair in one correct decider's set is in every correct decider's set. -/
  agreement : ∀ (i j p : validator) (s : slot),
    correct i → correct j → decided i p s → has_decided j → decided j p s

  /-- **Validity (qualitative half)** — a decided pair attributed to a
      correct validator is genuine: that validator proposed that slot. -/
  validity_genuine : ∀ (i p : validator) (s : slot),
    correct i → correct p → decided i p s → proposed p s

  /-- **Integrity** (state residue) — a correct validator decides only if
      some correct validator has proposed. -/
  integrity : ∀ (i : validator),
    correct i → has_decided i → ∃ (p : validator) (s : slot), correct p ∧ proposed p s

/-! ## Orchestrator (`mod:orchestrator_2`)

The persistent slot-scheduling primitive. Single input: `complete(s)`;
single output: `open(s)` (a slot never opened is implicitly *skipped*).

### Obligation table

| Property (paper, `mod:orchestrator_2`) | Kind | Discharged by (`Conductor.lean`) |
|---|---|---|
| Totality (eventual) | documented, **(A-orch-totality)** | meta: per-window induction `lemma:conductor-totality` (strengthened to `d_tot`-totality when run within Cadence) |
| Integrity, "at most once" | documented (event counting is not state-visible) | Conductor window-entry integrity (`lemma:window-entry`: windows entered once; each window opens each of its slots once) |
| Integrity, "not before the starting time" | documented | Conductor clock guard on `open` (`line:conductor-wait-for-open`); rests on the synchronized-clocks assumption |
| Monotonicity | jointly with totality: field `open_prefix_agreement` | see below |
| `B`-Boundedness | documented, **(A-orch-boundedness)** with `B = 2W − p` | Conductor interval-inclusion invariant (uncompleted opened slots lie in the last two windows' tails); the numeric bound is a meta corollary (`lem:boundedness`) |
| `R`-Recovery | documented, **(A-orch-recovery)** with `R = 2Wτ` | meta: parameter assumptions (`line:assumption-one..four`) + per-window induction (`prop:smooth-windows`, `prop:first-post-gst-window-time`) |

### `open_prefix_agreement` — the safety residue of Totality + Monotonicity

Totality is a liveness property and per-validator monotonicity alone has no
state-level content, but their *combination* has a safety-usable residue,
stated in the paper's prose right after `mod:orchestrator_2`:

> whenever a correct validator `p_i` opens a slot `s`, every correct
> validator opens exactly the same set of slots with number at most
> `s.number`.

(The paper proves this from totality + integrity + monotonicity; it is the
fact the Cadence safety proof, `lemma:cadence-safety` case 1, actually
uses.) Its state-level form — restricted to slots the second validator has
already reached — is expressible and inductive:

> if correct `j` has opened `s` and correct `i` has opened `s' < s`, then
> `j` has (already) opened `s'`.

Contrapositive reading: once `j` opens past `s'` without opening it, no
correct validator ever opens `s'` (else the execution would violate
totality or monotonicity); and `j` opens a slot only when it holds every
smaller slot any correct validator has opened. The `Cadence` glue module
states exactly this as the `require` of its `orch_open` oracle action and
maintains it as invariant `[opened_prefix_agreement]`; the Conductor
discharges it from window-assignment agreement (`prop:window-agreement`)
plus the synchronized-clocks scheduling of openings within a window
(`prop:fate-order` and the `schedule_opening` timing). -/
class Orchestrator (validator slot : Type) where
  /-- `byz i`: validator `i` is Byzantine. Stated in the models' own
      polarity — every model carries `is_byz` — so that the contract
      property can be substituted at a relation name rather than at a
      lambda, which is what keeps it translatable (see "Contract
      properties as shared syntax"). -/
  byz : validator → Prop
  /-- `opened i s`: the orchestrator has output `open(s)` at validator `i`. -/
  opened : validator → slot → Prop
  /-- `completed i s`: validator `i` has input `complete(s)`. (No formal
      property in this class constrains it — it appears here because the
      documented `B`-boundedness and `R`-recovery obligations relate it to
      `opened`.) -/
  completed : validator → slot → Prop

  /-- The implementation's strict slot order. Carried as a field rather
      than derived from a `TotalOrder` instance so that an implementation
      supplies the very relation its own safety property is stated over,
      making the contract field it discharges the *same* statement rather
      than an equivalent one. The property below is a plain implication and
      does not depend on `lt` being an order. -/
  lt : slot → slot → Prop

  /-- **Open-prefix agreement** — the safety residue of Totality +
      Monotonicity (see the class docstring). -/
  open_prefix_agreement : openPrefixAgreement% byz opened lt
