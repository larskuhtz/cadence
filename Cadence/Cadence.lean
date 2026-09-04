import Veil
import Cadence.Interfaces
import Cadence.Tooling

/-! # Cadence — the extreme-pipelining glue (`algorithm:cadence`)

*Note: opening this file in a Lean-enabled editor re-runs its verification
sweep in the language server (~1 min, one SMT solve per VC). Prefer
`lake build Cadence.Cadence`; see `README.md` § "Opening the files in an
editor".*

This module is the paper's `algorithm:cadence`: the thin layer that wires a
single **Orchestrator** instance `O` and one **SlotConsensus** instance
`S[s]` per slot into the full MCP protocol. Both primitives are consumed as
*oracles* (the pattern established by the MVBA oracle inside
[`Chorus.lean`](./Chorus.lean)): each oracle output event is an action whose
`require` clauses are exactly the primitive's contract properties — the
class fields of [`Interfaces.lean`](./Interfaces.lean) — and those requires
are lifted to invariants. The module is verified against the contracts
only; `Chorus` (⊨ `SlotConsensus`) and `Conductor` (⊨ `Orchestrator`)
discharge them independently. See `docs/ConductorDesign.md`
§2 and §4 for the architecture and
`papers/cadence/src/p2_framework.tex` for the reference
(`mod:slotconsensus`, `mod:orchestrator_2`, `algorithm:cadence`,
`§subsection:correctness_cadence`).

## Property coverage (top-level MCP properties)

The MCP properties (`p2_problem_definition.tex` / the commented preamble of
`p2_framework.tex`) live here in **slot-indexed** form; the positional-log
and wall-clock-parameterised formulations are derived on top at the
plain-Lean / meta layer ([`Composition.lean`](./Composition.lean)), never inside SMT:

* **Safety** (`def:safety`, prefix consistency of local logs;
  `lemma:cadence-safety`) — decomposed exactly as the paper's two proof
  cases: `safety [log_agreement]` (same slot: two honest appends for slot
  `s` agree — from the finalize oracle's agreement) and
  `safety [skip_agreement]` (different slots: no slot is opened by one
  honest validator and skipped by another — from the orchestrator oracle's
  open-prefix agreement). The positional statement (`local_log(p,t)`
  prefix consistency as ordered lists) follows from these two by the
  paper's own case split — a list lemma over the slot-indexed relations,
  deferred to the composition layer because list positions are arithmetic the Veil
  layer deliberately avoids.
* **ℓ-Liveness** (`def:liveness`, `lemma:cadence-liveness`) — genuinely
  temporal (GST, `R`-recovery, ℓ-termination); meta-level, see the
  fair-progress section at the end of this file.
* **c-Censorship resistance** (`def:censorship-resistance`) — its
  protocol-level residue is `safety [inclusion_lift]`: every appended
  proposal vector contains the on-time proposal of a correct proposer for
  which the synchrony premise holds (imported through the finalize
  oracle's conditional inclusion require, discharged by Chorus
  `proposal_inclusion`). The real-time trigger of the premise
  (`s.deadline − Δ ≥ GST + c`, on-time opening via `R`-recovery) is the
  meta-level half.
* **Hiding** (`def:hiding`) — the paper's composition lemma is one line
  ("proposal contents are observable only through the per-slot
  instances"); at this abstraction the module has *no other channel* by
  construction — there is no state item carrying proposal contents other
  than the opaque `pvector`/`proposal` tokens attached to the per-slot
  finalize oracle. The protocol-level share-gating theorem stays in Chorus
  (`hiding_until_deadline`); the cryptographic half in
  [`Primitives.lean`](./Primitives.lean).
* **B-Bounded concurrency** (`lemma:cadence-bounded-concurrency`) — the
  paper's proof reduces it to `B`-boundedness of the orchestrator via one
  state-level fact: a validator actively participates in `S[s]` iff it has
  opened `s` and not yet completed it. That reduction is
  `safety [bounded_concurrency_interval]` here; the numeric bound
  (`B = 2W − p` for Conductor) stays with the orchestrator's meta
  obligations.

## State locality contract (glue edition)

The Chorus doctrine (`docs/ChorusDesign.md` §3.5.3) adapts as follows. There are no
network relations in this module — validators do not exchange messages at
the glue level; **all** cross-validator interaction is inside the two
oracles. Every state item is either

* **(L) per-validator local state** — `opened`, `skipped`, `resolved`,
  `finalized`, `completed`, `appended`, `proposed`, `sc_started`,
  `sc_abandoned`. Protocol actions (`record_skip`, `append`) read and
  write only rows of the acting validator.
* **(A) oracle events** — the `orch_open` and `sc_finalize` actions. Their
  `require` clauses *may* read other validators' rows: an oracle stands
  for a distributed service whose collective behaviour is constrained by
  the contract, so a contract property relating several validators'
  events (agreement, open-prefix agreement) is legitimately stated over
  several validators' local views. This is the same licence the MVBA
  oracle actions in Chorus use. The *updates* of an oracle action still
  touch only the acting validator's rows.

## Threat model

There are **no Byzantine actions in this module**. Byzantine validators do
not run the glue algorithm — their influence on honest validators enters
exclusively through the two oracles, and the oracle contracts (all
`require`s below) constrain only *honest* validators' events, quantifying
over honest peers only. Byzantine rows of the local relations simply stay
empty; no honest action or invariant reads them. (Rationale:
`docs/ConductorDesign.md` §3 "Adversary"; the same argument the paper makes by
stating every module property for correct validators only.) Consequently
this module needs no quorum machinery and no `ByzNodeSet` — faithful to
the paper's remark that the framework imposes no resilience threshold of
its own (`p2_framework.tex`, "On the generality of the framework"): the
`n = 3f+1` arithmetic lives entirely inside the primitives.

## Slot safety absorbed by indexing

The `finalized` relation is indexed by the slot: `sc_finalize i s v` is
the event "`S[s]` finalizes `v` at `i`". A finalized vector's slot field
equalling `s` (`mod:slotconsensus` slot safety, `SlotConsensus.slot_safety`)
is thereby definitional here; the composition instance theorem re-establishes the
connection explicitly when constructing the slot-indexed relation from
Chorus's per-instance state.
-/

veil module Cadence

/-! ## Types -/

-- Slot identifiers, totally ordered by slot number (`s.number`; we never
-- need the number itself, only the order — cf. `docs/ConductorDesign.md` §3 on
-- keeping arithmetic out of the SMT layer).
type slot
-- Validator identity.
type node
-- An opaque proposal vector (`V ∈ PVector`): the value a slot-consensus
-- instance finalizes. Its per-proposer content is exposed only through the
-- immutable `pv_includes` relation.
type pvector
-- An opaque proposal (`P ∈ Proposal`): what a proposer submits.
type proposal

instantiate slot_ord : TotalOrder slot

/-! ## Immutable configuration -/

-- Byzantine validators. No cardinality constraint is imposed at this layer
-- (see "Threat model" above).
immutable relation is_byz (i : node)
-- `j ∈ s.proposers`. Immutable per-slot proposer assignment (generalises
-- Chorus's single-slot `is_proposer`; validator-set changes / rotation are
-- out of scope — `docs/ConductorDesign.md` §7).
immutable relation is_proposer (j : node) (s : slot)
-- `V[j] = P`: proposal vector `v` maps proposer `j` to proposal `p`. A
-- vector's content is fixed data, hence immutable.
immutable relation pv_includes (v : pvector) (j : node) (p : proposal)
-- The synchrony premise of proposal inclusion for slot `s`, proposer `j`,
-- proposal `p`: "`j` is a correct proposer of `s`, `s.deadline − Δ ≥ GST`,
-- and `j` submits exactly `p` at the slot's starting time". Under the
-- premise the proposal is fixed at the starting time — before any
-- finalization can exist — so it is per-execution *data*, not events;
-- making it immutable is what keeps the conditional inclusion property
-- inductive without Chorus-style phase-timestamp machinery (cf.
-- `docs/ChorusDesign.md` §3.3 on conditional properties, and
-- `SlotConsensus.on_time_proposal` in `Interfaces.lean`).
immutable relation inclusion_premise (s : slot) (j : node) (p : proposal)

/-! ## Mutable state (all per-validator local — category (L)) -/

-- `opened_i` (`line:var-opened`): slots the orchestrator opened at `i`.
relation opened (i : node) (s : slot)
-- `skipped_i` (`line:var-skipped`): slots `i` recorded as implicitly
-- skipped (`line:implicit-skip`).
relation skipped (i : node) (s : slot)
-- Materialised "slot resolved" marker: `s` is skipped or appended
-- (the two disjuncts of `ready_to_append`, `line:func-ready-to-append-return`).
-- Kept as a real relation updated alongside `skipped`/`appended` so the
-- append guard is a single positive quantifier-free-per-instance lookup
-- instead of a `∀∃` alternation: materialising the marker keeps the deep
-- reasoning at the action that establishes it, rather than making every
-- consumer re-derive it.
relation resolved (i : node) (s : slot)
-- Finalize events: `S[s]` finalized `v` at `i` (`line:upon-finalize`).
-- The paper's `pending_i` is the ghost difference `finalized ∧ ¬ appended`
-- (`pending` below) — keeping both endpoints monotone avoids the paper's
-- non-monotone `pending_i \ {V}` deletion (`line:pending-remove`).
relation finalized (i : node) (s : slot) (v : pvector)
-- `i` has invoked `O.complete(s)` (`line:complete`).
relation completed (i : node) (s : slot)
-- `i`'s local log, as a slot-indexed relation (`line:append`). The
-- ordered-list view is recovered from slot order at the composition layer.
relation appended (i : node) (s : slot) (v : pvector)
-- `i` has invoked `S[s].propose(·)` (`line:propose`).
relation proposed (i : node) (s : slot)
-- `i` has invoked `S[s].participate()` (`line:participate`).
relation sc_started (i : node) (s : slot)
-- `i` has invoked `S[s].abandon()` (`line:abandon`).
relation sc_abandoned (i : node) (s : slot)

#gen_state

-- The premise speaks about a correct proposer of `s` ...
assumption [inclusion_premise_proposer]
  ∀ (s : slot) (j : node) (p : proposal),
    inclusion_premise s j p → is_proposer j s ∧ ¬ is_byz j
-- ... and a correct proposer submits a single proposal per slot.
assumption [inclusion_premise_unique]
  ∀ (s : slot) (j : node) (p p' : proposal),
    inclusion_premise s j p → inclusion_premise s j p' → p = p'

/-! ## Theory -/

-- Strict slot order (`s.number < s'.number`).
theory ghost relation slot_lt (s s' : slot) := slot_ord.le s s' ∧ s ≠ s'

/-! ## Derived state -/

-- The paper's `pending_i` (`line:var-pending`).
ghost relation pending (i : node) (s : slot) (v : pvector) :=
  finalized i s v ∧ ¬ appended i s v

-- `i` is actively participating in `S[s]` (started, not yet abandoned) —
-- the bounded-concurrency proxy of `subsection:memory`.
ghost relation actively_participating (i : node) (s : slot) :=
  sc_started i s ∧ ¬ sc_abandoned i s

-- `ready_to_append` for slot `s` (`line:func-ready-to-append-return`):
-- every strictly smaller slot is resolved.
ghost relation ready_to_append (i : node) (s : slot) :=
  ∀ s', slot_lt s' s → resolved i s'

after_init {
  opened I S := false
  skipped I S := false
  resolved I S := false
  finalized I S V := false
  completed I S := false
  appended I S V := false
  proposed I S := false
  sc_started I S := false
  sc_abandoned I S := false
}

/-! ## Oracle: the orchestrator opens a slot (`line:upon-open`)

The action is the oracle output `O.open(s)` at honest validator `i`
*fused with* the (atomic, local) handler at
lines `line:opened-update`–`line:propose`: record `s` opened, record every
smaller not-opened slot as skipped, start participating in `S[s]`, and — if
`i` is a designated proposer — submit its proposal.

The `require`s are the Orchestrator contract (`mod:orchestrator_2`),
state-level rendering per `Interfaces.lean`:

* *integrity* (at most once) — `¬ opened i s`;
* *monotonicity* (per-validator: slots open in increasing order) — nothing
  above `s` is open yet at `i`;
* *open-prefix agreement* (the safety residue of totality + monotonicity —
  see `Orchestrator.open_prefix_agreement`): (a) `i` already holds every
  smaller slot any honest validator has opened, and (b) no honest
  validator has opened past `s` without opening `s` (once an honest
  validator skips past `s`, the contract forbids `s` from ever being
  opened — else totality would be violated).
* integrity's clock half ("not before the starting time") needs a clock
  and lives in the Conductor module, where it is a guard on the
  open-scheduling action; it has no residue at this untimed layer.

Discharge pointers: (a)/(b) ↦ Conductor `[open_prefix_agreement]`-family
invariants, from ACS window-assignment agreement
(`prop:window-agreement`) + in-window scheduling order (`prop:fate-order`);
integrity ↦ Conductor window-entry integrity (`lemma:window-entry`). -/
action orch_open (i : node) (s : slot) {
  require ¬ is_byz i
  -- Orchestrator integrity: `s` not opened at `i` before.
  require ¬ opened i s
  -- Orchestrator monotonicity, per-validator half.
  require ∀ s', slot_lt s s' → ¬ opened i s'
  -- Open-prefix agreement (a): `i` holds every smaller honest-opened slot.
  require ∀ (j : node) (s' : slot),
    ¬ is_byz j → opened j s' → slot_lt s' s → opened i s'
  -- Open-prefix agreement (b): no honest validator skipped past `s`.
  require ∀ (j : node) (s' : slot),
    ¬ is_byz j → opened j s' → slot_lt s s' → opened j s
  -- Handler: `line:opened-update`, `line:participate`,
  -- `line:proposer-check`/`line:propose`. The paper's bulk implicit-skip
  -- recording (`line:implicit-skip`) is decomposed into the separate
  -- per-slot `record_skip` action below (same decomposition discipline as
  -- Chorus's per-proposer signing, `docs/ChorusDesign.md` §8): a bulk update over all
  -- smaller slots would need a `decide`d order predicate on the RHS, which
  -- Veil's SMT translation handles only on the induction path; the decomposed
  -- form is a strict superset of the
  -- paper's behaviours (skips may be recorded late) and is harmless for
  -- safety — no invariant demands eager skip bookkeeping — while liveness
  -- picks up an (F-justice) obligation on `record_skip` (see the liveness
  -- section).
  opened i s := true
  sc_started i s := true
  if is_proposer i s then
    proposed i s := true
}

/-! ## Protocol: record an implicitly skipped slot (`line:implicit-skip`)

When `i` has opened a slot `s_wit` and a smaller slot `s` was never opened
at `i`, the paper records `s` as skipped in the same handler that opened
`s_wit`. Decomposed here into a per-slot action (see the note inside
`orch_open`). The guards make the recording sound rather than merely
timely: `s` is genuinely below an opened slot (so, by `orch_open`'s
monotonicity require, it can never be opened at `i` any more), and not
opened at `i` (`line:implicit-skip`'s set comprehension). -/
action record_skip (i : node) (s : slot) (s_wit : slot) {
  require ¬ is_byz i
  require opened i s_wit
  require slot_lt s s_wit
  require ¬ opened i s
  skipped i s := true
  resolved i s := true
}

/-! ## Oracle: a slot-consensus instance finalizes (`line:upon-finalize`)

The oracle output `S[s].finalize(v)` at honest validator `i`, fused with
the handler at lines `line:pending-add`–`line:abandon`: buffer `v` as
pending (ghost — `finalized` is set, `appended` not yet), notify the
orchestrator (`completed`), and abandon the instance.

The `require`s are the SlotConsensus contract (`mod:slotconsensus`):

* the handler guard itself — the event fires only for slots `i` has opened
  ("early finalizations buffered", `line:upon-finalize`);
* *agreement*, per-validator half — `i` finalizes `s` at most once;
* *agreement*, cross-validator half — no honest validator has finalized a
  different vector for `s`;
* *proposal inclusion*, conditional — under the synchrony premise the
  vector contains the correct proposer's on-time proposal;
* *slot safety* — absorbed by the slot-indexing of `finalized` (see the
  module header).

Discharge pointers: agreement ↦ Chorus `safety [agreement_pos]` /
`[agreement_pos_neg]`; inclusion ↦ Chorus `safety [proposal_inclusion]` /
`[proposal_inclusion_no_neg]` (premise `all_honest_recorded`); the fused
`abandon` makes the Chorus scope note "the glue calls `abandon()` only
after finalizing" structural — checked by `[abandoned_after_finalize]`
below. -/
action sc_finalize (i : node) (s : slot) (v : pvector) {
  require ¬ is_byz i
  -- Handler guard: fires only once `s ∈ opened_i`.
  require opened i s
  -- Agreement, per-validator half: at most one finalization per slot.
  require ∀ v', ¬ finalized i s v'
  -- Agreement, cross-validator half.
  require ∀ (j : node) (v' : pvector),
    ¬ is_byz j → finalized j s v' → v' = v
  -- Conditional proposal inclusion.
  require ∀ (j : node) (p : proposal),
    inclusion_premise s j p → pv_includes v j p
  finalized i s v := true
  completed i s := true
  sc_abandoned i s := true
}

/-! ## Protocol: append a pending vector (`line:upon-ready-to-append`)

The only genuine protocol action of the glue: a pending proposal vector is
appended to the local log once every smaller slot is resolved
(skipped-or-appended), which keeps the log's slot numbers strictly
increasing. Purely local. -/
action append (i : node) (s : slot) (v : pvector) {
  require ¬ is_byz i
  -- `v ∈ pending_i` for slot `s` ...
  require finalized i s v
  require ∀ v', ¬ appended i s v'
  -- ... and `ready_to_append(v)` (`line:func-ready-to-append-return`).
  require ready_to_append i s
  appended i s v := true
  resolved i s := true
}

/-! ## Safety properties (slot-indexed MCP forms) -/

/- MCP Safety, same-slot case (`lemma:cadence-safety`, case
`V₁.slot = V₂.slot`): two honest validators never append different
proposal vectors for the same slot. From the finalize oracle's agreement,
lifted through `[finalized_agreement]` + `[appended_finalized]`. -/
safety [log_agreement]
  ∀ (i j : node) (s : slot) (v v' : pvector),
    ¬ is_byz i ∧ ¬ is_byz j ∧ appended i s v ∧ appended j s v' → v = v'

/- MCP Safety, cross-slot case (`lemma:cadence-safety`, case
`V₁.slot ≠ V₂.slot`): no slot is opened by one honest validator and
skipped by another — the state-level content of "the two validators
resolved all preceding slots identically". With `[log_agreement]` this
yields prefix consistency of the ordered logs (the composition layer's list lemma). -/
safety [skip_agreement]
  ∀ (i j : node) (s : slot),
    ¬ is_byz i ∧ ¬ is_byz j ∧ opened i s → ¬ skipped j s

/- Censorship-resistance residue (`def:censorship-resistance`,
slot-indexed): an appended proposal vector contains the on-time proposal
of every correct proposer for which the synchrony premise holds. -/
safety [inclusion_lift]
  ∀ (i j : node) (s : slot) (v : pvector) (p : proposal),
    ¬ is_byz i ∧ appended i s v ∧ inclusion_premise s j p →
    pv_includes v j p

/- The state-level reduction of `lemma:cadence-bounded-concurrency`: an
honest validator actively participates in `S[s]` exactly while `s` is
opened-but-not-completed. `B`-bounded concurrency then *is* the
orchestrator's `B`-boundedness obligation applied through this equivalence
(meta: **(A-orch-boundedness)**, `Interfaces.lean`). -/
safety [bounded_concurrency_interval]
  ∀ (i : node) (s : slot),
    ¬ is_byz i →
    (actively_participating i s ↔ (opened i s ∧ ¬ completed i s))

/-! ## Invariants — oracle contracts lifted -/

/- SlotConsensus agreement, lifted (cross- and per-validator: take `j = i`). -/
invariant [finalized_agreement]
  ∀ (i j : node) (s : slot) (v v' : pvector),
    ¬ is_byz i ∧ ¬ is_byz j ∧ finalized i s v ∧ finalized j s v' → v = v'

/- SlotConsensus conditional inclusion, lifted. -/
invariant [finalized_inclusion]
  ∀ (i j : node) (s : slot) (v : pvector) (p : proposal),
    ¬ is_byz i ∧ finalized i s v ∧ inclusion_premise s j p →
    pv_includes v j p

/- Orchestrator open-prefix agreement. Not a restatement of
`Orchestrator.open_prefix_agreement` — the *same* statement, expanded from
the shared syntax the class field also uses
([`Interfaces.lean`](./Interfaces.lean) § "Contract properties as shared
syntax"), so the assumption this glue makes and the contract an
orchestrator discharges cannot drift apart. -/
invariant [opened_prefix_agreement]
  openPrefixAgreement% is_byz opened slot_lt

/-! ## Invariants — local structure -/

/- A skipped slot has a higher opened slot behind it (`record_skip`'s
witness guard — the paper's `line:implicit-skip` fires only inside an
`open` handler). -/
invariant [skipped_witness]
  ∀ (i : node) (s : slot),
    ¬ is_byz i ∧ skipped i s → ∃ s', slot_lt s s' ∧ opened i s'

/- A validator never both opens and skips a slot (integrity across the
two fates; the paper's "either recorded as skipped or finalized"). -/
invariant [opened_skipped_excl]
  ∀ (i : node) (s : slot),
    ¬ is_byz i → ¬ (opened i s ∧ skipped i s)

/- `resolved` soundness: three invariants tying the materialised marker
to its definition `skipped ∨ appended` (split for e-matching friendliness). -/
invariant [skipped_resolved]
  ∀ (i : node) (s : slot), ¬ is_byz i ∧ skipped i s → resolved i s

invariant [appended_resolved]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ is_byz i ∧ appended i s v → resolved i s

invariant [resolved_backed]
  ∀ (i : node) (s : slot),
    ¬ is_byz i ∧ resolved i s → skipped i s ∨ ∃ v, appended i s v

/- Log structure: below an appended slot everything is resolved (the
persistent residue of the `ready_to_append` guard) — the log has no holes
that are neither skipped nor appended. -/
invariant [appended_prefix_resolved]
  ∀ (i : node) (s s' : slot) (v : pvector),
    ¬ is_byz i ∧ appended i s v ∧ slot_lt s' s → resolved i s'

/- Appends come from finalizations (`line:upon-ready-to-append` consumes
`pending_i`). -/
invariant [appended_finalized]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ is_byz i ∧ appended i s v → finalized i s v

/- Finalizations happen only for opened slots (the `line:upon-finalize`
guard, persisted). -/
invariant [finalized_opened]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ is_byz i ∧ finalized i s v → opened i s

/- `complete(s)` is invoked exactly upon finalizing `s`
(`line:complete`) — both directions. -/
invariant [finalized_completed]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ is_byz i ∧ finalized i s v → completed i s

invariant [completed_finalized]
  ∀ (i : node) (s : slot),
    ¬ is_byz i ∧ completed i s → ∃ v, finalized i s v

/- `participate()` is invoked exactly upon opening (`line:participate`). -/
invariant [sc_started_iff_opened]
  ∀ (i : node) (s : slot),
    ¬ is_byz i → (sc_started i s ↔ opened i s)

/- `abandon()` is invoked exactly upon completing (`line:abandon`). -/
invariant [sc_abandoned_iff_completed]
  ∀ (i : node) (s : slot),
    ¬ is_byz i → (sc_abandoned i s ↔ completed i s)

/- The Chorus conformance note made structural (`docs/ConductorDesign.md` §7):
the glue abandons a slot-consensus instance only after finalizing it. -/
invariant [abandoned_after_finalize]
  ∀ (i : node) (s : slot),
    ¬ is_byz i ∧ sc_abandoned i s → ∃ v, finalized i s v

/- Proposals are submitted by designated proposers, upon opening
(`line:proposer-check`–`line:propose`). -/
invariant [proposed_proposer_opened]
  ∀ (i : node) (s : slot),
    ¬ is_byz i ∧ proposed i s → is_proposer i s ∧ opened i s

/-! ## Liveness — meta-argument and fair-progress invariants

The glue inherits the Chorus liveness doctrine (`docs/ChorusDesign.md` §7; McMillan,
*"Toward Liveness Proofs at Scale"*, CAV 2024): temporal glue as named
meta-axioms, safety content SMT-discharged. The claim mirrored is
`lemma:cadence-liveness`:

> **(ℓ-Liveness)** for every slot `s` with `s.deadline − Δ ≥ GST + R`,
> every honest validator eventually appends a proposal vector for `s`.

### Meta-axioms

* **(F-justice)** — the `append` and `record_skip` actions, when
  continuously enabled, fire eventually (per honest validator; enabledness
  is monotone for `append` — all three preconditions are positive and
  persistent, see `[pending_append_enabled]` — and for `record_skip` its
  guards are positive except `¬ opened i s`, which is *stable* once the
  witness exists: `orch_open`'s monotonicity require permanently disables
  opening below an opened slot).
* **(A-orch-totality)**, **(A-orch-recovery)** — the orchestrator oracle
  eventually opens, at every honest validator, every slot any honest
  validator opened (totality), and — from `GST + R` on — every upcoming
  slot (recovery). Discharge: the Conductor module's meta layer
  (`lemma:conductor-totality`, `(2Wτ)`-recovery).
* **(A-sc-termination)** — once every honest validator has started
  participating in `S[s]`, the finalize oracle eventually fires at every
  honest validator. Discharge: Chorus fair-progress layer + (A-mvba).

### The induction (paper's proof of `lemma:cadence-liveness`)

By (A-orch-recovery) every honest validator opens `s`; by open-prefix
agreement + (A-orch-totality), for every `s' ≤ s` either all honest
validators open `s'` — then all participate (`[sc_started_iff_opened]`)
and (A-sc-termination) finalizes it everywhere — or none does, and each
records it skipped once it opens anything higher (`record_skip`, enabled
from that point on and fired by (F-justice)). Either way `s'` is resolved
at every honest validator; induction on slot order (well-founded: only
finitely many slots below `s`) then satisfies `ready_to_append`, and
(F-justice) on `append` appends `s`. The per-step SMT content is
`[pending_append_enabled]` below; the ranking is structural — all nine
relations are monotone (the paper's `pending \ {V}` deletion is modelled
as the monotone pair `finalized`/`appended`), so the residual count of
unresolved slots below `s` decreases with every helpful firing. -/

/- Fair progress — the append chain: a pending vector whose slot prefix
is resolved satisfies *all* of `append`'s preconditions. The one
non-definitional step is uniqueness: `v` pending implies *nothing* is
appended for `s` (via `[appended_finalized]` + `[finalized_agreement]`),
so the `∀ v', ¬ appended` guard cannot be blocked by a *different* vector.
Guards future edits of `append` against silently strengthening the
enabling condition. -/
invariant [pending_append_enabled]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ is_byz i ∧ pending i s v → ∀ v', ¬ appended i s v'

/- Proof reconstruction ON: the module is small enough
(115 VCs, all sub-second) that Lean re-checks every cvc5 proof — the
sweep and the persisted VC theorems below then carry **no** trusted-SMT
step, which makes the downstream `Composition.lean` theorems
kernel-checked (axiom-pinned there). Captured at `#gen_spec` like all
`veil.smt.*` options. -/
set_option veil.smt.trust false

/- Streaming theorem persistence (pairs with `trust false`):
dischargers retain their reconstructed witnesses and `#gen_theorems`
persists each proven VC incrementally, releasing witnesses as it goes —
instead of re-running every reconstruction serially at `#gen_theorems`
(which is what lazy witness regeneration would do, and what Veil now
warns about). Captured at `#gen_spec`. -/
set_option veil.gen.streamTheorems true

/- VC registry (`docs/Dependencies.md` §1): persist the VC
statements + metadata for the cross-file check/prove commands. -/
set_option veil.gen.vcRegistry true

/- Proof cache (`docs/Dependencies.md` §2): store every
reconstructed proof this sweep produces in the content-addressed on-disk
cache (`.lake/build/veilcache/`) and consult it before every solve — a
statement-unchanged rebuild re-checks cached proofs instead of re-solving,
and slice/consumer files hit the entries this sweep stores. The key is the
statement itself (solver-independent); every hit is re-checked against the
live goal, and the kernel still checks at every persistence point.
File-level so the dischargers capture it at `#gen_spec` (§1.9 semantics). -/
set_option veil.cache.proofs true

#gen_spec

/- The sweep runs at Veil's solver defaults (60 s, finite-model-find on).
Do not try to override them around this command: dischargers capture
solver options at `#gen_spec`, so a `set_option veil.smt.* ... in` here is
silently inert (Veil warns about the mismatch; see the "Solver
configuration" note in `Chorus.lean`). -/
#check_invariants

/- Persist the discharged VCs as theorems in the environment (named
`Cadence.<action>_<property>` / `Cadence.<init>_…`), so the
composition layer ([`Composition.lean`](./Composition.lean)) can cite
them in plain-Lean proofs about reachable states. With
`veil.smt.trust = false` above, these are real reconstructed proofs, no
`sorryAx`. With `veil.gen.streamTheorems` above, the witnesses retained
by the sweep are persisted here incrementally, with no re-elaboration. -/
#gen_theorems

/-! ## Reachability sanity checks

Guards against a vacuous safety claim (`docs/TODO.md` § "Soundness"): the
states the safety properties quantify over are actually reachable. The
first trace exercises the full happy path of one slot
(open → finalize → append); the second reaches a skip (open a slot, then
record a smaller never-opened slot as skipped).

(Placement note: these must not be immediately followed by a
`set_option … in` command — the trace command's optional proof-term
suffix would greedily parse it; see `CLAUDE.md`.) -/

sat trace {
  any 3 actions
  assert (∃ i s v, appended i s v)
}

sat trace {
  any 2 actions
  assert (∃ i s, skipped i s)
}

end Cadence
