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
`S[s]` per slot into the full MCP protocol. It is verified **against the
module contracts alone**: the two primitives enter as class constraints —
`instantiate orch : OrchestratorSafety …` and `instantiate sc :
SlotConsensusSafety …` ([`Interfaces.lean`](./Interfaces.lean)) — over
abstract state types `ostate` and `scstate` that this module holds as its own
state (`os`, one `sc_state s` per slot) and reads only through the contracts'
observables. The contract properties are *not* restated here as guards or
invariants: they are the classes' axioms, which Veil hands to the solver, so
every verification condition below is discharged from the contract as
written in `Interfaces.lean` — the same mechanism by which `Chorus.lean`
consumes `ByzNodeSet`. `Chorus` (⊨ `SlotConsensusSafety`,
[`Chorus/Compose.lean`](./Chorus/Compose.lean)) and `Conductor`
(⊨ `OrchestratorSafety`, [`Composition.lean`](./Composition.lean)) discharge
the constraints independently, and [`System.lean`](./System.lean)
instantiates the end theorems at those instances. See
`docs/ConductorDesign.md` §2 and §4 for the architecture,
`docs/CompositionContracts.md` for this encoding, and
`papers/cadence/src/p2_framework.tex` for the reference
(`mod:slotconsensus`, `mod:orchestrator_2`, `algorithm:cadence`,
`§subsection:correctness_cadence`).

## How the sub-protocols appear

Each sub-protocol is a transition system the glue does not see inside:

* an **oracle step** action (`orch_step`, `sc_step`) advances the abstract
  state by any internal transition the contract allows — the paper's module
  running "in the background";
* the glue's **inputs** to a sub-protocol are its input transitions, driven
  by the glue's handlers (`on_finalize` performs `O.complete(s)` through
  `orch.complete`);
* the glue **reads** the sub-protocols' outputs as observables of the
  abstract state (`orch.opened os i s`, `sc.finalized s (sc_state s) i v`)
  and reacts to them in **handlers** (`on_propose`, `on_finalize`, and the
  bookkeeping actions `record_skip`, `append`).

The paper runs each handler atomically *upon* the output event; here the
event is the oracle step and the handler a later, separate action. That
admits strictly more behaviours (a handler may run late), so every safety
property proven here holds a fortiori of the atomic algorithm; what the
relaxation costs is one liveness obligation ((F-justice) on the handlers,
liveness section); no safety property had to be weakened for it — see the
note at `[bounded_concurrency_interval]`. The `participate()` call needs no handler:
it is issued in the same handler that reacts to `open(s)`, so "`i` has
started participating in `S[s]`" is *by definition* "`O` has opened `s` at
`i`" (ghost `sc_started`). Three inputs are not driven into the
`SlotConsensusSafety` fragment at all — `participate`, `abandon` and
`propose` are inputs the paper's *safety* properties never refer to, so they
live in the upper class `SlotConsensus` (temporal level) and the glue keeps
its own record of having issued them (`sc_abandoned`, `proposed`), exactly as
the paper's local variables do. That the glue's record and the instance's
input coincide is the trace-level seam declared out of scope in
[`Composition.lean`](./Composition.lean)'s header.

## Property coverage (top-level MCP properties)

The MCP properties (`p2_problem_definition.tex` / the commented preamble of
`p2_framework.tex`) live here in **slot-indexed** form; the positional-log
and wall-clock-parameterised formulations are derived on top at the
plain-Lean / meta layer ([`Composition.lean`](./Composition.lean)), never inside SMT:

* **Safety** (`def:safety`, prefix consistency of local logs;
  `lemma:cadence-safety`) — decomposed exactly as the paper's two proof
  cases: `safety [log_agreement]` (same slot: two honest appends for slot
  `s` agree — from `SlotConsensusSafety.agreement`) and
  `safety [skip_agreement]` (different slots: no slot is opened by one
  honest validator and skipped by another — from
  `OrchestratorSafety.open_prefix_agreement` and `.monotonicity`). The
  positional statement (`local_log(p,t)` prefix consistency as ordered
  lists) follows from these two by the paper's own case split — a list
  lemma over the slot-indexed relations, deferred to the composition layer
  because list positions are arithmetic the Veil layer deliberately avoids.
* **ℓ-Liveness** (`def:liveness`, `lemma:cadence-liveness`) — genuinely
  temporal (GST, `R`-recovery, ℓ-termination); meta-level, see the
  fair-progress section at the end of this file.
* **c-Censorship resistance** (`def:censorship-resistance`) — its
  protocol-level residue is `safety [inclusion_lift]`: every appended
  proposal vector contains the on-time proposal of a correct proposer for
  which the synchrony premise holds — the premise being the contract's
  `on_time` observable (for Chorus, `all_honest_recorded`), the conclusion
  the contract's `includes`. From `SlotConsensusSafety.proposal_inclusion`.
  The real-time trigger of the premise (`s.deadline − Δ ≥ GST + c`, on-time
  opening via `R`-recovery) is the meta-level half.
* **Hiding** (`def:hiding`) — the paper's composition lemma is one line
  ("proposal contents are observable only through the per-slot
  instances"); at this abstraction the module has *no other channel* by
  construction — there is no state item carrying proposal contents other
  than the opaque `pvector`/`proposal` tokens attached to the per-slot
  finalization observable. The protocol-level share-gating theorem stays in
  Chorus (`hiding_until_deadline`, the contract's `hiding_residue`); the
  cryptographic half in [`Primitives.lean`](./Primitives.lean).
* **B-Bounded concurrency** (`lemma:cadence-bounded-concurrency`) — the
  paper's proof reduces it to `B`-boundedness of the orchestrator via one
  state-level fact: a validator actively participates in `S[s]` iff it has
  opened `s` and not yet completed it. That reduction is
  `safety [bounded_concurrency_interval]` here, stated over the
  *orchestrator's own* `completed` observable — so the orchestrator's
  `Orchestrator.boundedness` obligation applies to it directly, with no
  bridge between two notions of "completed". The numeric bound
  (`B = 2W − p` for Conductor) is that obligation's `bound`.

## State locality contract (glue edition)

The Chorus doctrine (`docs/ChorusDesign.md` §3.5.3) adapts as follows. There are no
network relations in this module — validators do not exchange messages at
the glue level; **all** cross-validator interaction is inside the two
sub-protocols. Every state item is either

* **(L) per-validator local state** — `skipped`, `resolved`, `delivered`,
  `appended`, `sc_abandoned`, `proposed`. Handlers and protocol actions read
  and write only rows of the acting validator, plus the sub-protocol
  observables they react to.
* **(A) sub-protocol state** — `os` and `sc_state s`, advanced by the oracle
  steps (any contract-legal internal transition) and by the glue's input
  transitions. Cross-validator facts (agreement, open-prefix agreement) are
  facts *about* these states, supplied by the contracts' axioms at reachable
  states — never read by a glue action as a guard.

## Threat model

There are **no Byzantine actions in this module**. Byzantine validators do
not run the glue algorithm — their influence on honest validators enters
exclusively through the two sub-protocols, whose contracts constrain only
*correct* validators' observables. Byzantine rows of the local relations
simply stay empty; no honest action or invariant reads them. (Rationale:
`docs/ConductorDesign.md` §3 "Adversary"; the same argument the paper makes by
stating every module property for correct validators only.) The fault
pattern is the shared `FaultModel` the two contracts are stated against, so
"correct" means the same thing in the glue, in the orchestrator and in every
slot-consensus instance. Consequently this module needs no quorum machinery
and no `ByzNodeSet` — faithful to the paper's remark that the framework
imposes no resilience threshold of its own (`p2_framework.tex`, "On the
generality of the framework"): the `n = 3f+1` arithmetic lives entirely
inside the primitives.

## Slot safety

`sc.finalized s (sc_state s) i v` is the event "`S[s]` finalizes `v` at
`i`"; that `v` carries slot `s` is the contract's `slot_safety`, which this
module never needs — the instance index already says which slot a
finalization belongs to.
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
-- contract's `includes`.
type pvector
-- An opaque proposal (`P ∈ Proposal`): what a proposer submits.
type proposal
-- The abstract state of the orchestrator instance `O`.
type ostate
-- The abstract state of a slot-consensus instance `S[s]` (one per slot).
type scstate

instantiate slot_ord : TotalOrder slot

/-! ## The contracts

One fault model, shared by both contracts, so "correct" is one notion. Then
the two sub-protocols, as the state-level fragments of their contracts. Every
axiom of these classes is available to the solver in every verification
condition below. -/

instantiate fm : FaultModel node
instantiate orch : OrchestratorSafety node slot ostate fm.byz
instantiate sc : SlotConsensusSafety slot node proposal pvector scstate fm.byz

/-! ## Immutable configuration -/

-- `j ∈ s.proposers`. Immutable per-slot proposer assignment (generalises
-- Chorus's single-slot `is_proposer`; validator-set changes / rotation are
-- out of scope — `docs/ConductorDesign.md` §7).
immutable relation is_proposer (j : node) (s : slot)
-- The sub-protocols' initial states: per-execution data, constrained below
-- to be initial states of the respective contracts.
immutable individual orch_init_state : ostate
immutable function sc_init_state : slot → scstate

/-! ## Mutable state -/

-- (A) The orchestrator's state, and one slot-consensus state per slot.
individual os : ostate
function sc_state (s : slot) : scstate

-- (L) Per-validator local state.
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
-- `S[s].finalize(v)` has been *delivered* to `i`'s handler
-- (`line:upon-finalize`): `v` entered `pending_i`. The paper's `pending_i`
-- is the ghost difference `delivered ∧ ¬ appended` (`pending` below) —
-- keeping both endpoints monotone avoids the paper's non-monotone
-- `pending_i \ {V}` deletion (`line:pending-remove`).
relation delivered (i : node) (s : slot) (v : pvector)
-- `i`'s local log, as a slot-indexed relation (`line:append`). The
-- ordered-list view is recovered from slot order at the composition layer.
relation appended (i : node) (s : slot) (v : pvector)
-- `i` has invoked `S[s].abandon()` (`line:abandon`).
relation sc_abandoned (i : node) (s : slot)
-- `i` has invoked `S[s].propose(·)` (`line:propose`).
relation proposed (i : node) (s : slot)

#gen_state

-- The sub-protocols start in initial states of their contracts.
assumption [orch_init]
  orch.init orch_init_state
assumption [sc_init]
  ∀ (s : slot), sc.init s (sc_init_state s)

/-! ## Theory -/

-- Strict slot order (`s.number < s'.number`).
theory ghost relation slot_lt (s s' : slot) := slot_ord.le s s' ∧ s ≠ s'

/-! ## Derived state — the sub-protocols' outputs, read through the contracts -/

-- `opened_i` (`line:var-opened`): `O` has output `open(s)` at `i`.
ghost relation opened (i : node) (s : slot) := orch.opened os i s
-- `i` has input `O.complete(s)` (`line:complete`) — the orchestrator's own
-- record of it.
ghost relation completed (i : node) (s : slot) := orch.completed os i s
-- `S[s]` has output `finalize(v)` at `i`.
ghost relation finalized (i : node) (s : slot) (v : pvector) :=
  sc.finalized s (sc_state s) i v
-- `i` has invoked `S[s].participate()` (`line:participate`) — issued in
-- the handler of `open(s)`, hence definitionally the opening.
ghost relation sc_started (i : node) (s : slot) := opened i s

/-! ## Derived state — local -/

-- The paper's `pending_i` (`line:var-pending`).
ghost relation pending (i : node) (s : slot) (v : pvector) :=
  delivered i s v ∧ ¬ appended i s v

-- `i` is actively participating in `S[s]` (started, not yet abandoned) —
-- the bounded-concurrency proxy of `subsection:memory`.
ghost relation actively_participating (i : node) (s : slot) :=
  sc_started i s ∧ ¬ sc_abandoned i s

-- `ready_to_append` for slot `s` (`line:func-ready-to-append-return`):
-- every strictly smaller slot is resolved.
ghost relation ready_to_append (i : node) (s : slot) :=
  ∀ s', slot_lt s' s → resolved i s'

after_init {
  os := orch_init_state
  sc_state S := sc_init_state S
  skipped I S := false
  resolved I S := false
  delivered I S V := false
  appended I S V := false
  sc_abandoned I S := false
  proposed I S := false
}

/-! ## Oracle: the orchestrator takes an internal step

Any transition `OrchestratorSafety.step` allows — in particular the ones
that output `open(s)` at some validators. What the glue knows about the new
state is exactly the contract: reachability is preserved, opened slots stay
opened, `completed` is unchanged (internal steps do not fabricate inputs),
a slot below an opened slot that was not opened stays unopened
(`monotonicity`), and open-prefix agreement holds at every reachable state. -/
action orch_step (os_next : ostate) {
  require orch.step os os_next
  os := os_next
}

/-! ## Oracle: a slot-consensus instance takes an internal step

Any transition `SlotConsensusSafety.step s` allows — including the ones
that output `finalize(v)` at some validators. Finalizations stay finalized
and the contract's agreement and inclusion hold at every reachable state. -/
action sc_step (s : slot) (sc_next : scstate) {
  require sc.step s (sc_state s) sc_next
  sc_state s := sc_next
}

/-! ## Handler: a designated proposer submits its proposal
(`line:proposer-check`–`line:propose`)

The `open(s)` handler's proposing half: once `i` has opened `s` and is one
of its proposers, it invokes `S[s].propose(·)`. Recorded locally
(`proposed`); the contents are the slot-consensus instance's business
(`SlotConsensus.propose`, temporal level). -/
action on_propose (i : node) (s : slot) {
  require ¬ fm.byz i
  require opened i s
  require is_proposer i s
  require ¬ proposed i s
  proposed i s := true
}

/-! ## Protocol: record an implicitly skipped slot (`line:implicit-skip`)

When `i` has opened a slot `s_wit` and a smaller slot `s` was never opened
at `i`, the paper records `s` as skipped in the same handler that opened
`s_wit`. Decomposed here into a per-slot action. The guards make the
recording sound rather than merely timely: `s` is genuinely below an opened
slot — so, by the orchestrator's `monotonicity`, it can never be opened at
`i` any more — and not opened at `i` (`line:implicit-skip`'s set
comprehension). -/
action record_skip (i : node) (s : slot) (s_wit : slot) {
  require ¬ fm.byz i
  require opened i s_wit
  require slot_lt s s_wit
  require ¬ opened i s
  skipped i s := true
  resolved i s := true
}

/-! ## Handler: a slot-consensus instance has finalized (`line:upon-finalize`)

The handler of the output `S[s].finalize(v)` at honest validator `i`, lines
`line:pending-add`–`line:abandon`: buffer `v` as pending (`delivered`),
notify the orchestrator — `O.complete(s)` is an *input transition* of the
orchestrator's state, `orch.complete`, whose post-state the action picks —
and abandon the instance (recorded locally). The handler fires only for
slots `i` has opened ("early finalizations buffered", `line:upon-finalize`)
and once per slot. Everything the old oracle action *required* of the
finalization — agreement, inclusion — is now the contract's business, not a
guard. -/
action on_finalize (i : node) (s : slot) (v : pvector) (os_next : ostate) {
  require ¬ fm.byz i
  -- Handler guard: fires only once `s ∈ opened_i`.
  require opened i s
  -- The output has occurred.
  require finalized i s v
  -- Once per slot.
  require ∀ v', ¬ delivered i s v'
  -- `O.complete(s)`.
  require orch.complete os i s os_next
  delivered i s v := true
  os := os_next
  sc_abandoned i s := true
}

/-! ## Protocol: append a pending vector (`line:upon-ready-to-append`)

The only genuine protocol action of the glue: a pending proposal vector is
appended to the local log once every smaller slot is resolved
(skipped-or-appended), which keeps the log's slot numbers strictly
increasing. Purely local. -/
action append (i : node) (s : slot) (v : pvector) {
  require ¬ fm.byz i
  -- `v ∈ pending_i` for slot `s` ...
  require delivered i s v
  require ∀ v', ¬ appended i s v'
  -- ... and `ready_to_append(v)` (`line:func-ready-to-append-return`).
  require ready_to_append i s
  appended i s v := true
  resolved i s := true
}

/-! ## Safety properties (slot-indexed MCP forms) -/

/- MCP Safety, same-slot case (`lemma:cadence-safety`, case
`V₁.slot = V₂.slot`): two honest validators never append different
proposal vectors for the same slot. From the slot-consensus contract's
agreement, through `[appended_delivered]` + `[delivered_finalized]`. -/
safety [log_agreement]
  ∀ (i j : node) (s : slot) (v v' : pvector),
    ¬ fm.byz i ∧ ¬ fm.byz j ∧ appended i s v ∧ appended j s v' → v = v'

/- MCP Safety, cross-slot case (`lemma:cadence-safety`, case
`V₁.slot ≠ V₂.slot`): no slot is opened by one honest validator and
skipped by another — the state-level content of "the two validators
resolved all preceding slots identically". From the orchestrator contract's
open-prefix agreement and monotonicity. With `[log_agreement]` this
yields prefix consistency of the ordered logs (the composition layer's list lemma). -/
safety [skip_agreement]
  ∀ (i j : node) (s : slot),
    ¬ fm.byz i ∧ ¬ fm.byz j ∧ opened i s → ¬ skipped j s

/- Censorship-resistance residue (`def:censorship-resistance`,
slot-indexed): an appended proposal vector contains the on-time proposal
of every correct proposer for which the synchrony premise holds — both
sides in the contract's vocabulary. -/
safety [inclusion_lift]
  ∀ (i j : node) (s : slot) (v : pvector) (p : proposal),
    ¬ fm.byz i ∧ appended i s v ∧ sc.on_time s (sc_state s) j p →
    sc.includes v j p

/- The state-level reduction of `lemma:cadence-bounded-concurrency`: an
honest validator actively participates in `S[s]` exactly while `s` is
opened-but-not-completed — `completed` being the *orchestrator's* record of
the `complete(s)` input, so the orchestrator's `B`-boundedness obligation
(`Orchestrator.boundedness`, temporal level) bounds the participations
directly. The biconditional survives the handler relaxation because the
`participate()` call is definitionally the opening (`sc_started`) and
`abandon()` is issued in the same handler as `complete(s)`
(`[completed_iff_abandoned]`). -/
safety [bounded_concurrency_interval]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i →
    (actively_participating i s ↔ (opened i s ∧ ¬ completed i s))

/-! ## Invariants — the sub-protocols' states stay reachable

Everything the contracts promise is promised at *reachable* states, so the
glue tracks that its abstract states are reachable: initially by
`[orch_init]`/`[sc_init]`, then by the contracts' closure axioms. -/

invariant [orch_reachable]
  orch.reachable os

invariant [sc_reachable]
  ∀ (s : slot), sc.reachable s (sc_state s)

/-! ## Invariants — contract properties at the glue's states

These three are the contracts' own properties instantiated at `os` and
`sc_state s`. They are *proven* here — the solver derives each from the
class axiom at the reachable state — and kept as named invariants because
downstream verification conditions e-match on them more readily than on the
quantified class axioms. Nothing here is assumed. -/

/- `SlotConsensusSafety.agreement` at every instance (cross- and
per-validator: take `j = i`). -/
invariant [finalized_agreement]
  ∀ (i j : node) (s : slot) (v v' : pvector),
    ¬ fm.byz i ∧ ¬ fm.byz j ∧ finalized i s v ∧ finalized j s v' → v = v'

/- `SlotConsensusSafety.proposal_inclusion` at every instance. -/
invariant [finalized_inclusion]
  ∀ (i j : node) (s : slot) (v : pvector) (p : proposal),
    ¬ fm.byz i ∧ finalized i s v ∧ sc.on_time s (sc_state s) j p →
    sc.includes v j p

/- `OrchestratorSafety.open_prefix_agreement` at `os`. -/
invariant [opened_prefix_agreement]
  ∀ (i j : node) (s s' : slot),
    ¬ fm.byz i ∧ ¬ fm.byz j ∧ opened i s' ∧ opened j s ∧ slot_lt s' s →
    opened j s'

/-! ## Invariants — local structure -/

/- A skipped slot has a higher opened slot behind it (`record_skip`'s
witness guard — the paper's `line:implicit-skip` fires only inside an
`open` handler). -/
invariant [skipped_witness]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i ∧ skipped i s → ∃ s', slot_lt s s' ∧ opened i s'

/- A validator never both opens and skips a slot (integrity across the
two fates; the paper's "either recorded as skipped or finalized"). Preserved
across orchestrator steps by the contract's `monotonicity`. -/
invariant [opened_skipped_excl]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i → ¬ (opened i s ∧ skipped i s)

/- `resolved` soundness: three invariants tying the materialised marker
to its definition `skipped ∨ appended` (split for e-matching friendliness). -/
invariant [skipped_resolved]
  ∀ (i : node) (s : slot), ¬ fm.byz i ∧ skipped i s → resolved i s

invariant [appended_resolved]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ fm.byz i ∧ appended i s v → resolved i s

invariant [resolved_backed]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i ∧ resolved i s → skipped i s ∨ ∃ v, appended i s v

/- Log structure: below an appended slot everything is resolved (the
persistent residue of the `ready_to_append` guard) — the log has no holes
that are neither skipped nor appended. -/
invariant [appended_prefix_resolved]
  ∀ (i : node) (s s' : slot) (v : pvector),
    ¬ fm.byz i ∧ appended i s v ∧ slot_lt s' s → resolved i s'

/- Appends come from delivered finalizations (`line:upon-ready-to-append`
consumes `pending_i`). -/
invariant [appended_delivered]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ fm.byz i ∧ appended i s v → delivered i s v

/- A delivered finalization is a finalization of the instance (persisted
across instance steps by the contract's `finalized_mono`). -/
invariant [delivered_finalized]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ fm.byz i ∧ delivered i s v → finalized i s v

/- Finalizations are delivered only for opened slots (the
`line:upon-finalize` guard, persisted). -/
invariant [delivered_opened]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ fm.byz i ∧ delivered i s v → opened i s

/- `complete(s)` is input exactly upon delivering `s`'s finalization
(`line:complete`) — both directions. The orchestrator's `completed` is
frozen across its internal steps (`completed_step_frame`) and moved only by
the glue's `complete` inputs. -/
invariant [delivered_completed]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ fm.byz i ∧ delivered i s v → completed i s

invariant [completed_delivered]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i ∧ completed i s → ∃ v, delivered i s v

/- `abandon()` is invoked exactly upon completing (`line:abandon`): the
glue's record and the orchestrator's record move together. -/
invariant [completed_iff_abandoned]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i → (completed i s ↔ sc_abandoned i s)

/- The Chorus conformance note made structural (`docs/ConductorDesign.md` §7):
the glue abandons a slot-consensus instance only after it finalized. -/
invariant [abandoned_after_finalize]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i ∧ sc_abandoned i s → ∃ v, finalized i s v

/- Proposals are submitted by designated proposers, upon opening
(`line:proposer-check`–`line:propose`). -/
invariant [proposed_proposer_opened]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i ∧ proposed i s → is_proposer i s ∧ opened i s

/-! ## Liveness — meta-argument and fair-progress invariants

The glue inherits the Chorus liveness doctrine (`docs/ChorusDesign.md` §7; McMillan,
*"Toward Liveness Proofs at Scale"*, CAV 2024): temporal glue as named
meta-axioms, safety content SMT-discharged. The claim mirrored is
`lemma:cadence-liveness`:

> **(ℓ-Liveness)** for every slot `s` with `s.deadline − Δ ≥ GST + R`,
> every honest validator eventually appends a proposal vector for `s`.

### Meta-axioms

* **(F-justice)** — the handler and protocol actions `on_finalize`,
  `on_propose`, `record_skip` and `append`, when continuously enabled, fire
  eventually (per honest validator). Enabledness is monotone for all of
  them: their guards are positive observables and local relations, except
  the once-guards (`¬ delivered`, `¬ proposed`, `¬ opened i s` in
  `record_skip`), each of which is *stable* — the first two because the
  action itself is what falsifies them, the last by the orchestrator's
  `monotonicity` once the witness exists. The handler relaxation (module
  header) is what puts `on_finalize` on this list; in the paper it is
  atomic with the output.
* **(A-orch-totality)**, **(A-orch-recovery)** — `Orchestrator.totality` and
  `.recovery` ([`Interfaces.lean`](./Interfaces.lean)): the orchestrator
  eventually opens, at every honest validator, every slot any honest
  validator opened, and — from `GST + R` on — every upcoming slot.
  Discharge: residual for the Conductor (`Conductor.OrchestratorResidual`,
  [`Composition.lean`](./Composition.lean)); the paper's
  `lemma:conductor-totality` and `(2Wτ)`-recovery.
* **(A-sc-termination)** — `SlotConsensus.termination`: once every honest
  validator participates in `S[s]`, every honest validator's instance
  eventually finalizes. Discharge: residual for Chorus
  (`Chorus.SlotConsensusResidual`, [`Chorus/Compose.lean`](./Chorus/Compose.lean));
  Chorus's fair-progress layer + (A-mvba).

### The induction (paper's proof of `lemma:cadence-liveness`)

By (A-orch-recovery) every honest validator opens `s`; by open-prefix
agreement + (A-orch-totality), for every `s' ≤ s` either all honest
validators open `s'` — then all participate (`sc_started` is the opening)
and (A-sc-termination) finalizes it everywhere, (F-justice) delivers it
(`on_finalize`) — or none does, and each records it skipped once it opens
anything higher (`record_skip`, enabled from that point on and fired by
(F-justice)). Either way `s'` is resolved at every honest validator;
induction on slot order (well-founded: only finitely many slots below `s`)
then satisfies `ready_to_append`, and (F-justice) on `append` appends `s`.
The per-step SMT content is `[pending_append_enabled]` below; the ranking is
structural — every local relation and every observable is monotone (the
paper's `pending \ {V}` deletion is modelled as the monotone pair
`delivered`/`appended`), so the residual count of unresolved slots below `s`
decreases with every helpful firing. -/

/- Fair progress — the append chain: a pending vector whose slot prefix
is resolved satisfies *all* of `append`'s preconditions. The one
non-definitional step is uniqueness: `v` pending implies *nothing* is
appended for `s` (via `[appended_delivered]`, `[delivered_finalized]` and
the contract's agreement), so the `∀ v', ¬ appended` guard cannot be
blocked by a *different* vector. Guards future edits of `append` against
silently strengthening the enabling condition. -/
invariant [pending_append_enabled]
  ∀ (i : node) (s : slot) (v : pvector),
    ¬ fm.byz i ∧ pending i s v → ∀ v', ¬ appended i s v'

/- Proof reconstruction ON: the module is small enough that Lean re-checks
every cvc5 proof — the sweep and the persisted VC theorems below then carry
**no** trusted-SMT step, which makes the downstream `Composition.lean`
theorems kernel-checked (axiom-pinned there). Captured at `#gen_spec` like
all `veil.smt.*` options. -/
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
states the safety properties quantify over are actually reachable *for
some* pair of sub-protocols satisfying the contracts — the solver
constructs the abstract states. The first trace exercises the full happy
path of one slot (the orchestrator opens → the instance finalizes → the
handler delivers and completes → append); the second reaches a skip (open a
slot, then record a smaller never-opened slot as skipped).

(Placement note: these must not be immediately followed by a
`set_option … in` command — the trace command's optional proof-term
suffix would greedily parse it; see `CLAUDE.md`.) -/

sat trace {
  orch_step
  sc_step
  on_finalize
  append
  assert (∃ i s v, appended i s v)
}

sat trace {
  orch_step
  record_skip
  assert (∃ i s, skipped i s)
}

end Cadence
