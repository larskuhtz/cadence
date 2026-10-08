import Veil
import Cadence.Interfaces
import Cadence.Windows
import Cadence.Tooling

-- Opening this file in a Lean-enabled editor re-runs its verification sweep
-- in the language server (~1 min, one SMT solve per VC). Prefer
-- `lake build Cadence.Conductor`; see [README.md](../README.md),
-- "Working on the models".

/-! # Conductor — the window-based orchestrator (Algorithm 7 (`algorithm:conductor`))

Paper target: [docs/PaperAlignment.md](../docs/PaperAlignment.md) §0.

Veil model of the Conductor, the orchestrator instantiation of the Cadence
extreme-pipelining framework. Reference: Appendix D
(`section:conductor-formal`) — the **ACS-based formal version** (windows over Module 4 (`mod:acs`)), which is the one the
paper proves. The overview, Section 5 (`section:conductor-overview`), uses the same ACS + median mechanism; its
one deliberate difference — agreeing on the first slot's *deadline* rather
than on the first *slot* over read-only deadlines — is the deadline↔slot
equivalence of [ConductorDesign.md](../docs/ConductorDesign.md) §1. (The
paper repository's deadline-MVBA Conductor is an unrendered draft, not the
paper — see that section's source-tree note.) Design:
[ConductorDesign.md](../docs/ConductorDesign.md) §3; contracts:
[Interfaces.lean](Interfaces.lean) — this module *implements* `Orchestrator`
(its state-level fragment is proven in [Composition.lean](Composition.lean),
`Conductor.orchestratorSafety`) and *consumes* `ACS` as a class constraint
(`instantiate acs : ACSSafety …` below, one abstract instance state per
window); support theory: [Windows.lean](Windows.lean).

## Protocol summary (Algorithm 7 (`algorithm:conductor`))

Slots are scheduled in *windows* of `W` consecutive slots. Every validator
starts in window 1 (slots `1..W`, opened at their starting times). Once a
validator has completed all scheduled slots below the current window's
readiness boundary (its `(p + 1)`-th slot: every earlier window and the
window's first `p` slots — Algorithm 7, line 23 (`line:ready-check`)), it proposes a
first slot for the next window to that window's ACS instance
(Algorithm 7, line 42 (`line:acs-propose`)): the earliest slot whose starting time has not
passed, or the first slot beyond the current window if that one lies within
it (Algorithm 7, lines 39–41 (`line:sstar-compute`–`line:sstar-update`)). When ACS decides, the next
window's first slot is the **median** of the decided proposals
(Algorithm 7, line 48 (`line:median-compute`)), and the validator enters the window and schedules
its `W` slots (Algorithm 7, line 49 (`line:open-foreach`)), each opening at its starting time
(Algorithm 7, line 27 (`line:conductor-wait-for-open`)).

## What is modelled vs. meta (per [ConductorDesign.md](../docs/ConductorDesign.md) §3)

SMT-checked here (the safety-shaped content):
* window-entry order (Proposition 6 (`lemma:window-entry`)) — `[entered_prefix]`;
* cross-window slot monotonicity (Proposition 7 (`prop:acs-nonoverlap`)) —
  `safety [win_separation]` (+ the transitive `[win_bounds_ordered]`);
* window-assignment agreement (Proposition 9 (`prop:window-agreement`)) —
  `safety [window_assignment_agreement]`: each validator computes its
  intervals from its own ACS decision, and any two correct validators hold
  the same one, by the ACS's agreement;
* opened-set structure (interval form of Proposition 8 (`prop:acs-fate-range`) /
  Proposition 11 (`prop:open-count-window`)) — `[opened_win_contained]`,
  `[open_local_order]`;
* open-prefix agreement — `safety [open_prefix_agreement]`, discharging
  the `OrchestratorSafety.open_prefix_agreement` contract field, which the
  `Cadence` glue module consumes through its `orch` class constraint;
* boundedness as interval inclusion (Lemma 14 (`lem:boundedness`), interval form) —
  `safety [bounded_tail]`: every scheduled-but-uncompleted slot lies at
  or above the *previous* window's readiness boundary. The numeric
  `(2W − p)` bound adds the window widths: the region from
  `boundary(ω−1)` on within scheduled intervals is the last `W − p` slots of
  window `ω−1` plus the `W` slots of window `ω` (`Conductor.boundedness`,
  [Conductor/Boundedness.lean](Conductor/Boundedness.lean));
* integrity's clock half ("no open before the slot's starting time",
  Algorithm 7, line 27 (`line:conductor-wait-for-open`)) — `safety [opened_after_start]`, via the
  abstract monotone clock.

Proven outside the model, in plain Lean over its timed runs
([Conductor/Temporal.lean](Conductor/Temporal.lean) and the files it
imports):
* totality (Lemma 15 (`lemma:conductor-totality`), `d_tot`-totality) and
  `(2Wτ)`-recovery (Lemma 16 (`lemma:conductor-recovery`)) — the paper's
  per-window induction, under the four parameter assumptions (Algorithm 7,
  lines 7–10 (`line:assumption-one`–`line:assumption-four`)), which are
  fields of the schedule.

Meta (assumed; the ACS is an assumed module):
* `ℓ`-termination / `Δ`-totality of ACS — **(A-acs-termination)** /
  **(A-acs-totality)** ([Interfaces.lean](Interfaces.lean) `ACS.termination`,
  `ACS.totality` — the upper level of the contract this module's `acs`
  constraint is the state-level fragment of);
* every cardinality statement (interval formulations replace them). The
  window width is a fact of the model, `[win_bounds_shift]`, over the shift
  functions `win_last` and `win_boundary`, whose arithmetic the instance at
  `slot := ℕ` fixes.

## The eager `opened_i` variable vs. the `open(s)` output

Algorithm 7 (`algorithm:conductor`) adds all `W` slots to the *variable* `opened_i`
eagerly upon window entry (Algorithm 7, line 51 (`line:acs-opened-update`)), while the `open(s)`
*outputs* fire later, each at its slot's starting time
(Algorithm 7, line 27 (`line:conductor-wait-for-open`)). The model keeps the two apart:

* the eager variable is the **ghost** `slot_scheduled` — the union of the
  entered windows' intervals (no state, no bulk updates);
* the relation `opened` records the **outputs** (what Module 2 (`mod:orchestrator_2`)
  specifies and the glue reads as the contract's `orch.opened`).

The readiness check (Algorithm 7, line 23 (`line:ready-check`), "all but the last `W − p` of
`opened_i` complete" ⟺ every slot of the earlier windows and the first
`p` of the current one is complete) is stated over the *eager* set
(`ready_next`), exactly as the paper computes it.

## Timing relaxation (load-bearing modelling note)

In the real protocol a scheduled opening *fires* at
`max(entry time, starting time)` — it cannot be delayed. Veil actions fire
nondeterministically, so this model admits *more* behaviours: an enabled
opening may stay unfired while the clock advances. Two consequences:

* Safety is unaffected (extra behaviours only): all invariants above hold
  under arbitrary delay, **except** where the paper's argument leans on
  punctual firing — those places are gated structurally instead:
  `open_slot` requires all smaller scheduled slots already opened
  (Proposition 10 (`prop:fate-order`)'s conclusion: with synchronized clocks and punctual
  triggers, openings occur in slot order). This converts the paper's
  timing argument into an explicit scheduling assumption of the model,
  documented here; it is the Conductor analogue of Chorus's `Phase`
  ordering.
* The clock (`now`, advanced by `tick`) exists only to make the guards
  "not before the starting time" (`open_slot`) expressible. Quantitative
  timing is stated over timed runs of this model
  ([Conductor/Schedule.lean](Conductor/Schedule.lean)), whose punctual
  opening row closes the freedom.

## Adversary

Conductor has **no Byzantine message surface beyond ACS**
([ConductorDesign.md](../docs/ConductorDesign.md) §3): its only inputs are
local `completed(s)` callbacks and ACS decisions. Byzantine influence enters
as (i) Byzantine validators' own ACS proposals — internal steps of the ACS
instance (`acs_step`), which the contract leaves unconstrained for Byzantine
validators — and (ii) up to `f` Byzantine pairs inside the decided core
set, captured by the assumption `[acs_first_bracket]` on the first slot a
validator computes (two *correct* pairs of its decided set bracketing it
from below and from above). The lower median meets it under the fault
bound (`Cadence.lowerMedian_first_assumptions`,
[AcsMedian.lean](AcsMedian.lean)). No quorum machinery and no `ByzNodeSet`
are needed; the fault pattern is the `FaultModel` the ACS contract is stated
against, otherwise unconstrained, and the resilience arithmetic (`≤ f`
Byzantine validators, one pair each in a core set of `2f + 1` validators)
lives in the ACS contract (`ACSSafety.decided_unique`,
`ACSTemporal.validity_quantitative`) and that theorem's fault-bound
hypothesis.

## Locality

Every action follows [Locality.md](../docs/Locality.md)'s rules. A correct
validator reads only its own rows (`entered`, `local_bounds`, `opened`,
`completed`), the clock, and its own index of the ACS. It writes only its
own rows and the ACS through its inputs at its own index. Each validator
computes its windows' intervals from its own decision (`enter_window`), and
agreement on them is a property (`[window_assignment_agreement]`), not a
shared write. `aux_opened_win` is auxiliary: no action reads it.

## Obligation discharge map (→ [Interfaces.lean](Interfaces.lean) `Orchestrator`)

The safety rows are `Conductor.orchestratorSafety`
([Composition.lean](Composition.lean)); the temporal rows are
`Conductor.conductorTemporal`
([Conductor/Temporal.lean](Conductor/Temporal.lean)), for an arbitrary ACS
meeting its contract. Both are proven, and `Conductor.conductorFull` joins
them.

Each entry is a contract item and what discharges it.

* **`open_prefix_agreement`** — `safety [open_prefix_agreement]`
* **Integrity "at most once" (`opened_mono`)** — `opened` is only ever set
  (the generated lemma `Conductor.opened.mono`)
* **Integrity "not before starting time" (`integrity_timing`)** — `safety
  [opened_after_start]` (+ synchronized-clocks assumption); first-order, so it
  is a field of the *fragment*
* **Monotonicity (`monotonicity`)** — `step_property [monotonicity]`, from
  `[open_local_order]` and the `open_slot` guard
* **the observables' frames (`completed_step_frame`, `complete_frame`,
  `complete_effect`)** — the transition bodies: only `complete_slot` touches
  `completed`, and only its own pair
* **`B`-boundedness, `B = 2W − p`** — `Conductor.boundedness`, from
  `safety [bounded_tail]`, the interval form, and the widths
  (`[win_bounds_shift]`) at the instance at `slot := ℕ`
* **Totality / `R`-recovery, `R = 2Wτ`** — `Conductor.totality` and
  `Conductor.recovery`, over the timed runs of
  [Conductor/Schedule.lean](Conductor/Schedule.lean)
-/

veil module Conductor

/-! ## Types -/

/-- Slot identifiers with a total order, a least slot (the paper's slot 1),
and a derived successor. No `+W` arithmetic
([ConductorDesign.md](../docs/ConductorDesign.md) §3, "Modelling ingredients
beyond Chorus's", item 1). -/
type slot
/-- Window indices (the paper's `ω ∈ ℕ≥1`): least window = window 1,
`next` = the `ω + 1` of Algorithm 7, line 46 (`line:window-increment`). -/
type window
/-- Abstract clock values. -/
type time
/-- Validator identity. -/
type node
/-- The abstract state of an ACS instance `ACS[w]` (one per window). -/
type acsstate

instantiate slot_ord : TotalOrderWithMinimum slot
instantiate win_ord : TotalOrderWithMinimum window
instantiate time_ord : TotalOrder time

/-! ## The contracts

The fault pattern, and the ACS as the state-level fragment of its contract
([Interfaces.lean](Interfaces.lean) `ACSSafety`): one abstract state per
window, advanced by the oracle step `acs_step` and by this module's own
`propose` inputs, read through the contract's observables. Every axiom of the
class is available to the solver in every verification condition below; the
ACS properties are consumed, not restated. -/

instantiate fm : FaultModel node
instantiate acs : ACSSafety node slot acsstate fm.byz

/-! ## Immutable configuration -/

/-- The slot's starting time `s.deadline − Δ` (Algorithm 7, line 27 (`line:conductor-wait-for-open`)). -/
immutable function start_time : slot → time
/-- A window's last slot, as a function of its first: the shift `+ (W − 1)`
of Algorithm 7, line 52 (`line:last-update`) ("the slot whose number is
`s⋆.number + W − 1`") and Algorithm 7, line 34 (`line:startup-last`) for
window 1. The model's slot order has no arithmetic, so the shift is an
immutable function; the instance at `slot := ℕ` fixes it to `s + (W − 1)`. -/
immutable function win_last : slot → slot
/-- A window's readiness boundary, its `(p + 1)`-th slot, as a function of
its first: the shift `+ p`. Algorithm 7, line 23 (`line:ready-check`) asks
for completion of "all but the last `W − p`" opened slots, which in window
`ω` are every slot of the earlier windows and the window's first `p`: the
scheduled slots *strictly below* the boundary (`ready_next`). At `p = 0`
the boundary is the window's first slot, and readiness asks for the
earlier windows only. Fixed to `s + p` at the instance at `slot := ℕ`, as
`win_last`. -/
immutable function win_boundary : slot → slot
/-- Window 1's readiness boundary: the paper's slot `p + 1` of window 1
(Algorithm 7, line 34 (`line:startup-last`)), `win_boundary` of slot 1
(`[genesis_window]`). Later windows' bounds each validator computes from
its own ACS decision (`enter_window`). -/
immutable individual genesis_boundary : slot
/-- Window 1's last slot: its interval is `[slot 1, genesis_last]`, the
paper's slot `W` (Algorithm 7, line 34 (`line:startup-last`)), `win_last`
of slot 1 (`[genesis_window]`). -/
immutable individual genesis_last : slot
/-- Initial clock value: slot 1's starting time (`[genesis_window]`). -/
immutable individual genesis_time : time
/-- The ACS instances' initial states: per-execution data, constrained below
to be initial states of the contract. -/
immutable function acs_init_state : window → acsstate
/-- The first slot a validator computes from its own decision: at ACS state
`st`, `acs_first st i` is the median of `i`'s decided set (Algorithm 7,
line 48 (`line:median-compute`)). The model does not compute medians:
cardinality is outside the solver's first-order fragment. What it uses of
the function are the two assumptions `[acs_first_local]` and
`[acs_first_bracket]` below; the lower median meets both
(`Cadence.lowerMedian_first_assumptions`, [AcsMedian.lean](AcsMedian.lean)). -/
immutable function acs_first : acsstate → node → slot

/-! ## Mutable state -/

/-- The abstract global clock (synchronized clocks are a protocol
assumption — Algorithm 7 (`algorithm:conductor`) preamble "recall that validators'
clocks are synchronized"). -/
individual now : time

/-! ### (A) The ACS instances -/

/-- The ACS instances' states, per window `ACS[w]` (Algorithm 7, line 12 (`line:acs-instances`)).
Honest proposals are this module's `propose` inputs (`acs_propose`);
Byzantine proposals and the decision itself are the instance's own
internal steps (`acs_step`), constrained only by the contract. -/
function acs_state (w : window) : acsstate

/-! ### (L) Per-validator local state

The paper's `proposed_i` set (Algorithm 7, line 43 (`line:proposed-update`)) is the ACS state's own
record of `i`'s input — `acs.proposed (acs_state w) i s` — and needs no local
copy. -/

/-- `i` has entered window `w` (Algorithm 7, line 30 (`line:enter_window_1`), Algorithm 7, line 47 (`line:enter_window_omega`)). -/
relation entered (i : node) (w : window)
/-- `i`'s interval of window `w`: its first slot (the median of `i`'s own
decided set, Algorithm 7, line 48 (`line:median-compute`)), its readiness
boundary (the window's `(p + 1)`-th slot) and its last slot (`last_i[w]`,
Algorithm 7, line 52 (`line:last-update`)). Window 1's from the
configuration (Algorithm 7, lines 31–34
(`line:startup-foreach`–`line:startup-last`)), later windows' written by
`i`'s own entry step. Every correct validator holds the same interval of a
window (`[window_assignment_agreement]`), by the ACS's agreement. -/
relation local_bounds (i : node) (w : window) (first : slot) (boundary : slot) (last : slot)
/-- The `open(s)` *output* has fired at `i` (Algorithm 7, line 28 (`line:trigger-open`)). -/
relation opened (i : node) (s : slot)
/-- Auxiliary: the window `i` opened `s` under. Read by no action. -/
relation aux_opened_win (i : node) (s : slot) (w : window)
/-- `i` has received the `completed(s)` input (Algorithm 7, line 35 (`line:upon-completed`);
within Cadence: `i` finalized `S[s]`). -/
relation completed (i : node) (s : slot)

#gen_state

/-- The ACS instances start in initial states of their contract. -/
assumption [acs_init]
  ∀ (w : window), acs.init (acs_init_state w)
/-- A window's first slot, readiness boundary and last slot are in order:
`s ≤ s + p ≤ s + (W − 1)`, which is `0 ≤ p ≤ W − 1`, the parameter range
of Algorithm 7 (`algorithm:conductor`). -/
assumption [shift_shape]
  ∀ (s : slot), slot_ord.le s (win_boundary s) ∧
    slot_ord.le (win_boundary s) (win_last s)
/-- Window 1 is the window whose first slot is slot 1 (Algorithm 7, lines
31–34 (`line:startup-foreach`–`line:startup-last`)): its boundary and last
slot are the shifts of slot 1, and every validator enters it at slot 1's
starting time ("every correct validator enters window 1 at time
`0 = T₁(1)`", the proof of Proposition 16 (`prop:window-open-time`); slot 1
starts at time 0, Appendix A.1 (`subsection:mcp-preliminaries`)). -/
assumption [genesis_window]
  genesis_boundary = win_boundary slot_ord.zero ∧
  genesis_last = win_last slot_ord.zero ∧
  genesis_time = start_time slot_ord.zero
/-- Starting times strictly increase in slot order. Appendix A.1
(`subsection:mcp-preliminaries`) spaces consecutive deadlines a fixed
`τ > 0` apart within the extreme-pipelining framework, so later slots start
strictly later. The spacing itself, `start_time s = start_time 1 + (s − 1)τ`,
is arithmetic and is fixed at the instance at `slot := ℕ`
([ConductorBounds.md](../docs/ConductorBounds.md) §6.3). Under it,
`acs_propose`'s `require`s on `s_star` determine the paper's `s*`; no safety
property reads it. -/
assumption [start_time_strict]
  ∀ (s s' : slot), slot_ord.lt s s' →
    time_ord.le (start_time s) (start_time s') ∧ start_time s ≠ start_time s'
/-- The first slot is a function of the decided set alone: whenever `i`'s
decided set at `st` and `j`'s at `st'` hold the same pairs, `i` and `j`
compute the same first slot. This is what makes `enter_window`'s
computation local to `i` ([Locality.md](../docs/Locality.md) §5, a pure
function of data the node holds), and, with the ACS's agreement, what makes
every correct validator compute the same interval. -/
assumption [acs_first_local]
  ∀ (st st' : acsstate) (i j : node),
    (∀ (p : node) (s : slot), acs.decided st i p s ↔ acs.decided st' j p s) →
    acs_first st i = acs_first st' j
/-- **The median bracket.** A correct validator's first slot lies between
two correct validators' pairs of its decided set: one at or below it, one
at or above it. The paper's one sentence before Algorithm 7
(`algorithm:conductor`): "since at most `f` of the `2f + 1` decided values
are faulty, the median lies between the smallest and largest honest
estimate". The lower half separates the windows (`[win_separation]`); the
upper half bounds the first slot by a correct estimate, which recovery's
timing reads (Proposition 17 (`prop:window-progression`), point 1, and
Proposition 19 (`prop:first-post-gst-window-time`)). The lower median meets
it under the fault bound (`Cadence.lowerMedian_first_assumptions`,
[AcsMedian.lean](AcsMedian.lean)). -/
assumption [acs_first_bracket]
  ∀ (st : acsstate) (i : node),
    acs.reachable st ∧ ¬ fm.byz i ∧ acs.has_decided st i →
    (∃ (r1 : node) (s1 : slot), ¬ fm.byz r1 ∧ acs.decided st i r1 s1 ∧
      slot_ord.le s1 (acs_first st i)) ∧
    (∃ (r2 : node) (s2 : slot), ¬ fm.byz r2 ∧ acs.decided st i r2 s2 ∧
      slot_ord.le (acs_first st i) s2)

/-! ## Derived state -/

/-- The paper's eager `opened_i` variable (Algorithm 7, line 33 (`line:startup-opened-update`),
Algorithm 7, line 51 (`line:acs-opened-update`)): the union of the entered windows' intervals. -/
ghost relation slot_scheduled (i : node) (s : slot) :=
  ∃ w f b l, entered i w ∧ local_bounds i w f b l ∧
    slot_ord.le f s ∧ slot_ord.le s l

/-- `i` is *in* window `w`: entered it, not yet entered its successor
(the `current_window_i` variable, Algorithm 7, line 14 (`line:current_window_init`) /
Algorithm 7, line 46 (`line:window-increment`); negative observation of own local state only). -/
ghost relation in_window (i : node) (w : window) :=
  entered i w ∧ ∀ w', win_ord.next w w' → ¬ entered i w'

/-- `ready_for_next_window()` (Algorithm 7, line 23 (`line:ready-check`)) while in window `w`:
every scheduled slot strictly below `w`'s readiness boundary is completed:
every slot of the earlier windows and the first `p` of `w` (equivalently,
per the paper: all but the last `W − p` of the eager `opened_i` are
complete). At `p = 0` this is the earlier windows only, and in window 1
it holds from the start, as `k − j ≤ W − 0` does there. -/
ghost relation ready_next (i : node) (w : window) :=
  ∀ (f b l : slot), local_bounds i w f b l →
    ∀ (s : slot) (w0 : window) (f0 b0 l0 : slot),
      entered i w0 → local_bounds i w0 f0 b0 l0 →
      slot_ord.le f0 s → slot_ord.le s l0 → slot_ord.lt s b →
      completed i s

/-- Every validator starts in window 1 (Algorithm 7, line 30 (`line:enter_window_1`)), with
window 1's interval (Algorithm 7, lines 31–34
(`line:startup-foreach`–`line:startup-last`)) and nothing opened or
completed. -/
after_init {
  now := genesis_time
  -- Capitalized single letters are universal indices. `V` ranges over
  -- windows: `W` is the paper's window *width* throughout this file, and it
  -- also resolves to a Mathlib declaration, which Veil warns about.
  acs_state V := acs_init_state V
  -- Every validator enters window 1 at startup (Algorithm 7, line 30 (`line:enter_window_1`)).
  entered I V := V == win_ord.zero
  local_bounds I V F B L := V == win_ord.zero && F == slot_ord.zero &&
    B == genesis_boundary && L == genesis_last
  opened I S := false
  aux_opened_win I S V := false
  completed I S := false
}

/-! ## Clock -/

/-- The abstract clock advances monotonically and nondeterministically.
(Only the guard "not before the starting time" consumes it.) -/
action tick (t : time) {
  require time_ord.le now t
  now := t
}

/-! ## ACS proposal (Algorithm 7, lines 37–43 (`line:ready`–`line:proposed-update`)) -/

/-- An honest validator in window `w`, once ready, proposes a first slot for
the successor window `w'`, at most once. The `require`s on `s_star` are
Algorithm 7, lines 38–41 (`line:ready-time`–`line:sstar-update`), read at
the current time `now`: `s_star` is the earliest slot whose starting time
has not passed, moved to the first slot beyond the current window if that
one lies within it. With `l0` the current window's last slot, that is
`max(earliest not passed, l0 + 1)`, and the three `require`s say exactly
this: `s_star` lies beyond `l0`, its starting time has not passed, and every
slot strictly between `l0` and `s_star` has started. (If the earliest slot
not passed lies within the window, `s_star` is `l0`'s successor, whose
starting time is later still because starting times strictly increase; the
third `require` is then vacuous. Otherwise `s_star` is that earliest slot.)
Recovery's timing (Proposition 17 (`prop:window-progression`) and
Proposition 19 (`prop:first-post-gst-window-time`)) reads the second and
third. -/
action acs_propose (i : node) (w : window) (w' : window) (s_star : slot)
    (acs_next : acsstate) {
  require ¬ fm.byz i
  require in_window i w
  require win_ord.next w w'
  -- At most once per window (`proposed_i`, Algorithm 7, line 43 (`line:proposed-update`)).
  require ∀ (s : slot), ¬ acs.proposed (acs_state w') i s
  require ready_next i w
  -- Algorithm 7, line 40 (`line:sstar-guard`)/Algorithm 7, line 41
  -- (`line:sstar-update`): strictly beyond the current window, read off
  -- `i`'s own interval of it.
  require ∀ (f0 b0 l0 : slot), local_bounds i w f0 b0 l0 → slot_ord.lt l0 s_star
  -- Algorithm 7, line 39 (`line:sstar-compute`): `s_star`'s starting time
  -- has not passed ...
  require time_ord.le now (start_time s_star)
  -- ... and it is the earliest such slot beyond the current window.
  require ∀ (s : slot) (f0 b0 l0 : slot), local_bounds i w f0 b0 l0 →
    slot_ord.lt l0 s → slot_ord.lt s s_star →
    ¬ time_ord.le now (start_time s)
  -- `ACS[w'].propose(s_star)`: an input transition of the instance's state.
  require acs.propose (acs_state w') i s_star acs_next
  acs_state w' := acs_next
}

/-! ## Oracle: an ACS instance takes an internal step -/

/-- Any transition `ACSSafety.step` allows — a Byzantine validator's proposal
appearing (the contract constrains only *correct* validators' proposals), or
the instance deciding. What this module knows about the new state is exactly
the contract: reachability is preserved, correct validators' proposals are
unchanged, decisions stand, and agreement, validity and integrity hold at
every reachable state. -/
action acs_step (w : window) (acs_next : acsstate) {
  require acs.step (acs_state w) acs_next
  acs_state w := acs_next
}

/-! ## Window entry (Algorithm 7, lines 44–52
(`line:acs-decide`–`line:last-update`)) -/

/-- The handler of `p_i`'s own decision: an honest validator in window `w`
enters the successor `w'` once *its own* `ACS[w']` has decided and the
readiness condition holds (the two activation conditions of Algorithm 7,
line 44 (`line:acs-decide`)). In the same step it

* abandons the instance (Algorithm 7, line 45 (`line:acs-abandon`)), which
  is why abandonment never precedes decision (`[acs_abandoned_decided]`);
* computes the window's first slot from its own decided set, `f =
  acs_first (acs_state w') i` (the median, Algorithm 7, line 48
  (`line:median-compute`)), and records the window's interval, its `W`
  slots from `f` with the boundary at the `(p + 1)`-th (Algorithm 7,
  lines 49–52 (`line:open-foreach`–`line:last-update`)). The widths are the
  shift functions', fixed at the instance at `slot := ℕ`;
* enters the window. Entry *schedules* the window's slots (the eager
  `opened_i` update: the ghost `slot_scheduled` grows by the recorded
  interval); the `open` outputs fire later via `open_slot`.

Every read is `i`'s own: its windows and intervals, its completions, and
its own decision. That every correct validator records the same interval is
`[window_assignment_agreement]`, from the ACS's agreement. -/
action enter_window (i : node) (w : window) (w' : window) (f : slot)
    (acs_next : acsstate) {
  require ¬ fm.byz i
  require in_window i w
  require win_ord.next w w'
  -- `i`'s own `ACS[w']` has decided.
  require acs.has_decided (acs_state w') i
  require ready_next i w
  -- The median of `i`'s decided set (Algorithm 7, line 48).
  require f = acs_first (acs_state w') i
  -- `ACS[w'].abandon()`: an input transition of the instance's state.
  require acs.abandon (acs_state w') i acs_next
  local_bounds i w' f (win_boundary f) (win_last f) := true
  acs_state w' := acs_next
  entered i w' := true
}

/-! ## Opening a slot (`schedule_opening` trigger,
Algorithm 7, lines 27–28 (`line:conductor-wait-for-open`–`line:trigger-open`)) -/

/-- The `open(s)` output fires at honest validator `i` for a slot of an
entered window's interval, guarded by:

* integrity — not opened before, and not before the slot's starting time
  (the clock guard; Module 2 (`mod:orchestrator_2`) Integrity, second half);
* in-order firing — every smaller scheduled slot has already been opened.
  This is the structural rendering of the paper's timing argument
  (Proposition 10 (`prop:fate-order`) + Lemma 13 (`lemma:conductor-monotonicity`)): with synchronized
  clocks, triggers fire at `max(entry, start)`, which is monotone in the
  slot number across entered windows. See "Timing relaxation" in the
  module header. -/
action open_slot (i : node) (s : slot) (w : window)
    (f : slot) (b : slot) (l : slot) {
  require ¬ fm.byz i
  require entered i w
  require local_bounds i w f b l
  require slot_ord.le f s
  require slot_ord.le s l
  require ¬ opened i s
  require time_ord.le (start_time s) now
  require ∀ (s' : slot) (w0 : window) (f0 b0 l0 : slot),
    entered i w0 → local_bounds i w0 f0 b0 l0 →
    slot_ord.le f0 s' → slot_ord.le s' l0 → slot_ord.lt s' s →
    opened i s'
  opened i s := true
  aux_opened_win i s w := true
}

/-! ## Completion input (Algorithm 7, line 35 (`line:upon-completed`)) -/

/-- The `completed(s)` callback — within Cadence, `i`'s finalization of
`S[s]`: the glue module's `on_finalize` handler drives this action as the
contract's `complete` input (`OrchestratorSafety.complete`, which
`Conductor.orchestratorSafety` defines as exactly this action's
transition). Asynchronous and unforced; only opened slots complete (the
assumed behaviour verified structurally on the glue side, the glue's
`[delivered_opened]`). -/
action complete_slot (i : node) (s : slot) {
  require ¬ fm.byz i
  require opened i s
  require ¬ completed i s
  completed i s := true
}

/-! ## Safety properties -/

/-- Window-assignment agreement (Proposition 9 (`prop:window-agreement`), and the
Conductor-module "Safety"): any two correct validators hold the same
interval of a window. Each computes its interval from its own ACS decision
(`enter_window`); they agree because the ACS's agreement gives them the same
decided set, a decision is final (`ACSSafety.decided_stable`), and the first
slot is a function of the decided set (`[acs_first_local]`). -/
safety [window_assignment_agreement]
  ∀ (i j : node) (w : window) (f b l f' b' l' : slot),
    ¬ fm.byz i ∧ ¬ fm.byz j ∧ local_bounds i w f b l ∧ local_bounds j w f' b' l' →
    f = f' ∧ b = b' ∧ l = l'

/-- Cross-window slot monotonicity (Proposition 7 (`prop:acs-nonoverlap`)): a
window's interval lies strictly above its predecessor's (the paper's
`s.number ≥ s'.number + W`, in interval form), in every correct validator's
records. -/
safety [win_separation]
  ∀ (i : node) (w0 w : window) (f0 b0 l0 f b l : slot),
    ¬ fm.byz i ∧ win_ord.next w0 w ∧ local_bounds i w0 f0 b0 l0 ∧
    local_bounds i w f b l →
    slot_ord.lt l0 f

/-- Open-prefix agreement — the `OrchestratorSafety.open_prefix_agreement`
contract field ([Interfaces.lean](Interfaces.lean)), which the Cadence glue
module consumes through the class: if honest `j` has opened `s` and honest
`i` has opened a smaller `s'`, then `j` has opened `s'` too. The instance
`Conductor.orchestratorSafety` ([Composition.lean](Composition.lean))
projects this property out of `invariants_of_reachable`, converting
`slot_ord.lt` to the contract's `le ∧ ≠` by `TotalOrderWithMinimum.le_lt`. -/
safety [open_prefix_agreement]
  ∀ (i j : node) (s s' : slot),
    ¬ fm.byz i ∧ ¬ fm.byz j ∧ opened i s' ∧ opened j s ∧ slot_ord.lt s' s →
    opened j s'

/-- Integrity, clock half (Module 2 (`mod:orchestrator_2`) Integrity; the
Algorithm 7, line 27 (`line:conductor-wait-for-open`) guard persisted): no slot is opened before
its starting time. -/
safety [opened_after_start]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i ∧ opened i s → time_ord.le (start_time s) now

/-- Boundedness, interval form (Lemma 14 (`lem:boundedness`)), stated as the
persisted readiness residue: once a validator has entered window `w'`,
every scheduled slot strictly below the readiness boundary of `w'`'s
predecessor is completed. Contrapositive reading for the *current* window
`ω`: every scheduled-but-uncompleted slot lies at or above `boundary(ω−1)` —
within the scheduled intervals that region is the last `W − p` slots of
window `ω−1` plus the (at most `W`) slots of window `ω`, so at most
`2W − p` slots are open-but-uncompleted; the numeric bound is that
one-line meta corollary: the model states intervals, never cardinalities.
(For `ω` = window 1 the paper's `k ≤ W ≤ 2W − p` base case needs no
statement — window 1 has no predecessor.) -/
safety [bounded_tail]
  ∀ (i : node) (s : slot) (w' w ws : window) (f b l fs bs ls : slot),
    ¬ fm.byz i ∧
    -- i has entered w', whose predecessor w has boundary b
    entered i w' ∧ win_ord.next w w' ∧ local_bounds i w f b l ∧
    -- s is scheduled (in entered window ws's interval), strictly below b
    entered i ws ∧ local_bounds i ws fs bs ls ∧
    slot_ord.le fs s ∧ slot_ord.le s ls ∧ slot_ord.lt s b →
    completed i s

/-! ## Invariants — window structure -/

/-- Windows are entered in order, prefix-closed (Proposition 6 (`lemma:window-entry`)):
whoever is in window `w` has entered every window below. ("At most once"
needs no statement — `entered` is a set.) -/
invariant [entered_prefix]
  ∀ (i : node) (w w' : window),
    ¬ fm.byz i ∧ entered i w' ∧ win_ord.lt w w' → entered i w

/-- Everyone starts in window 1 (Algorithm 7, line 30 (`line:enter_window_1`)). -/
invariant [entered_zero]
  ∀ (i : node), entered i win_ord.zero

/-- Window 1's interval is the configuration's, at every validator
(Algorithm 7, lines 31–34 (`line:startup-foreach`–`line:startup-last`)). -/
invariant [bounds_genesis]
  ∀ (i : node) (f b l : slot),
    local_bounds i win_ord.zero f b l →
    f = slot_ord.zero ∧ b = genesis_boundary ∧ l = genesis_last

/-- A correct validator's interval of a later window is the one it computed
from its own decision: it has decided in that window's ACS, and the first
slot is `acs_first` of its decided set (Algorithm 7, line 48
(`line:median-compute`)). The decision is final, so the value stays what it
was when the interval was recorded. -/
invariant [bounds_decided]
  ∀ (i : node) (w : window) (f b l : slot),
    ¬ fm.byz i ∧ local_bounds i w f b l ∧ ¬ w = win_ord.zero →
    acs.has_decided (acs_state w) i ∧ f = acs_first (acs_state w) i

/-- A correct validator holds an interval only of a window it has
entered. -/
invariant [bounds_entered]
  ∀ (i : node) (w : window) (f b l : slot),
    ¬ fm.byz i ∧ local_bounds i w f b l → entered i w

/-- Interval shape: first ≤ boundary ≤ last. -/
invariant [bounds_shape]
  ∀ (i : node) (w : window) (f b l : slot),
    local_bounds i w f b l → slot_ord.le f b ∧ slot_ord.le b l

/-- Window width: every window's boundary and last slot are the shifts of
its first slot, so every window holds the `W` slots from its first, with
its boundary at the `(p + 1)`-th (Algorithm 7, lines 31–34
(`line:startup-foreach`–`line:startup-last`) and Algorithm 7, lines 49–52
(`line:open-foreach`–`line:last-update`)). -/
invariant [win_bounds_shift]
  ∀ (i : node) (w : window) (f b l : slot),
    local_bounds i w f b l → b = win_boundary f ∧ l = win_last f

/-- Transitive interval ordering (Proposition 8 (`prop:acs-fate-range`)'s "later windows
cover slots of strictly larger number", closed under the window order):
a correct validator's intervals of any two windows are strictly
separated. -/
invariant [win_bounds_ordered]
  ∀ (i : node) (w w' : window) (f b l f' b' l' : slot),
    ¬ fm.byz i ∧ win_ord.lt w w' ∧ local_bounds i w f b l ∧
    local_bounds i w' f' b' l' →
    slot_ord.lt l f'

/-! ## Invariants — ACS proposals -/

/-- An honest ACS proposal for window `w'` is strictly beyond the
predecessor window's interval, as every correct validator holds it
(Algorithm 7, line 40 (`line:sstar-guard`)/Algorithm 7, line 41
(`line:sstar-update`) persisted, with `[window_assignment_agreement]`;
feeds `[win_separation]` through `[acs_first_bracket]`'s lower pair). -/
invariant [acs_proposal_above_prev]
  ∀ (r j : node) (w' : window) (s : slot) (w0 : window) (f0 b0 l0 : slot),
    ¬ fm.byz r ∧ acs.proposed (acs_state w') r s ∧ win_ord.next w0 w' ∧
    ¬ fm.byz j ∧ local_bounds j w0 f0 b0 l0 →
    slot_ord.lt l0 s

/-- Two correct validators that have decided in the same ACS instance
compute the same first slot: the ACS's agreement gives them the same
decided set, and the first slot is a function of the set
(`[acs_first_local]`). Stated so that the cells that compare two
validators' intervals read it instead of re-deriving it. -/
invariant [first_agree]
  ∀ (i j : node) (w : window),
    ¬ fm.byz i ∧ ¬ fm.byz j ∧ acs.has_decided (acs_state w) i ∧
    acs.has_decided (acs_state w) j →
    acs_first (acs_state w) i = acs_first (acs_state w) j

/-- A correct decider's first slot of window `w'` lies beyond every correct
validator's interval of `w'`'s predecessor: `[acs_first_bracket]`'s lower
pair is a correct proposal, which `[acs_proposal_above_prev]` places there.
Stated once, at the ACS's decision, so that the entry step's cells read it
instead of re-deriving it. -/
invariant [first_above_prev]
  ∀ (i j : node) (w0 w' : window) (f0 b0 l0 : slot),
    ¬ fm.byz i ∧ acs.has_decided (acs_state w') i ∧ win_ord.next w0 w' ∧
    ¬ fm.byz j ∧ local_bounds j w0 f0 b0 l0 →
    slot_ord.lt l0 (acs_first (acs_state w') i)

/-- An honest proposal to `ACS[w']` presupposes having entered the
predecessor window (the Algorithm 7, line 37 (`line:ready`) activation context). -/
invariant [proposal_prev_entered]
  ∀ (r : node) (w' : window) (s : slot),
    ¬ fm.byz r ∧ acs.proposed (acs_state w') r s →
    ∃ w0, win_ord.next w0 w' ∧ entered r w0

/-- A correct validator holds an interval of every window it has entered:
window 1's from the configuration, a later window's from the entry step. -/
invariant [entered_has_bounds]
  ∀ (i : node) (w : window),
    ¬ fm.byz i ∧ entered i w → ∃ f b l, local_bounds i w f b l

/-! ## Invariants — openings -/

/-- Every opening is recorded with its window. -/
invariant [opened_backed]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i ∧ opened i s → ∃ w, aux_opened_win i s w

/-- The recorded window was entered. -/
invariant [opened_win_entered]
  ∀ (i : node) (s : slot) (w : window),
    ¬ fm.byz i ∧ aux_opened_win i s w → entered i w

/-- The opened slot lies in its recorded window's interval
(Proposition 8 (`prop:acs-fate-range`), interval form; a validator holds one
interval per window, so the ∀-formulation is exact). -/
invariant [opened_win_contained]
  ∀ (i : node) (s : slot) (w : window) (f b l : slot),
    ¬ fm.byz i ∧ aux_opened_win i s w ∧ local_bounds i w f b l →
    slot_ord.le f s ∧ slot_ord.le s l

/-- In-order openings (Proposition 10 (`prop:fate-order`) + Lemma 13 (`lemma:conductor-monotonicity`),
per-validator): below an opened slot, every scheduled slot is opened. -/
invariant [open_local_order]
  ∀ (i : node) (s s' : slot) (w0 : window) (f0 b0 l0 : slot),
    ¬ fm.byz i ∧ opened i s ∧
    entered i w0 ∧ local_bounds i w0 f0 b0 l0 ∧
    slot_ord.le f0 s' ∧ slot_ord.le s' l0 ∧ slot_ord.lt s' s →
    opened i s'

/-- Completions are of opened slots (Module 2 (`mod:orchestrator_2`) assumed
behaviour (i), enforced by the guard). -/
invariant [completed_opened]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i ∧ completed i s → opened i s

/-! ## Invariants — the ACS instances stay reachable

Everything the contract promises is promised at *reachable* states, so the
module tracks that every instance's abstract state is reachable: initially
by `[acs_init]`, then by the contract's closure axioms. -/

/-- Every ACS instance's abstract state is a reachable state of the
contract. -/
invariant [acs_reachable]
  ∀ (w : window), acs.reachable (acs_state w)

/-- **No premature abandonment** (Proposition 12
(`prop:acs-no-premature-abandonment`)): an honest validator abandons an ACS
instance only after deciding in it, since its one `abandon` is in the
handler of its own decision (`enter_window`). This is the second assumption
of Module 4 (`mod:acs`), in state form, as a fact of the model. -/
invariant [acs_abandoned_decided]
  ∀ (i : node) (w : window),
    ¬ fm.byz i ∧ acs.abandoned (acs_state w) i → acs.has_decided (acs_state w) i

/-! ## Liveness — totality, boundedness and recovery

Totality and `(2Wτ)`-recovery are temporal: the paper proves them only for
the Conductor run within Cadence, because they hinge on slots actually
completing (the introduction of Lemma 15 (`lemma:conductor-totality`)).
They are proven outside this model, in plain Lean over its timed runs, and
consume the invariants above as the state-level facts:

* **Totality**, Lemma 15 (`lemma:conductor-totality`), is
  `Conductor.totality` ([Conductor/Induction.lean](Conductor/Induction.lean)):
  the paper's per-window induction, Proposition 13
  (`prop:window-synchronization`), as `Conductor.window_synchronized`.
* **`(2W − p)`-Boundedness**, Lemma 14 (`lem:boundedness`), is
  `Conductor.boundedness` ([Conductor/Boundedness.lean](Conductor/Boundedness.lean)),
  from `safety [bounded_tail]` and the window widths.
* **`(2Wτ)`-Recovery**, Lemma 16 (`lemma:conductor-recovery`), is
  `Conductor.recovery` ([Conductor/Recovery.lean](Conductor/Recovery.lean)),
  through Propositions 14–19 (`Conductor.open_to_complete`,
  `Conductor.enters_every_window`, `Conductor.window_open_time`,
  `Conductor.window_progression`, `Conductor.smooth_windows`,
  `Conductor.first_post_gst_window_time`), and `Conductor.recovery_sharp`
  at `(W + p − 1)τ`. The four parameter assumptions of Algorithm 7,
  lines 7–10 (`line:assumption-one`–`line:assumption-four`), are fields of
  the schedule.

### The rows

The honest handlers — the ACS proposal (`acs_propose`), window entry
with its interval (`enter_window`), and the openings
(`open_slot`) — are held to their timing by the timed runs' rows
(`TimedRows`, `OpenPunctual`), the timed form of weak fairness. Their
guards are stable once true: they read positive observables and local
relations, and `ready_next` stays true because `completed` only grows and
the scheduled set grows only with entry, which preserves the readiness of
past windows (later windows' boundaries lie above, `[win_bounds_ordered]`).

The premises are stated in [Conductor/Schedule.lean](Conductor/Schedule.lean)
and listed, each with its role and its use, in
[Premises.md](../docs/Premises.md) §9: the timing model `Sync` (the rows,
punctual openings, one clock, each started window's ACS admissible for its
contract), the configuration, and the caller's
conditions (R-tot) and (R-term), which within Cadence are theorems about
Chorus (`Composed.caller_totality`, `Composed.caller_termination`). The
ACS's Termination and Δ-Totality are the assumed module's, the fields of
its `ACSTemporal` instance; this model meets that module's
no-premature-abandonment assumption as `[acs_abandoned_decided]`. The full
contract instance is `Conductor.conductorFull`
([Conductor/Temporal.lean](Conductor/Temporal.lean)). -/

/- The `Enumeration`/`FinEncodable` derivation over the action `Label`
sum must traverse every action's nested parameter sigma, which exceeds
the default instance-search budgets. The scaffolding cannot be disabled —
the `sat trace` queries below need the generated `ActionTag_EnumClass` — so
the budgets are raised instead. -/
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192

/- Proof reconstruction ON: the sweep and the persisted VC theorems below
carry no trusted-SMT step, which is what makes the theorems of
[Composition.lean](Composition.lean) (`Conductor ⊨ Orchestrator`, positional
MCP Safety) kernel-checked (axiom-pinned there).

One discharge attempt is expected to fail: `trust false` also flips
`embedBool`, changing the SMT query, and one attempt diverges under the
reconstruction encoding while the VC stays ✅ via its alternative form. -/
set_option veil.smt.trust false

/- Streaming theorem persistence (pairs with `trust false`): dischargers
retain their reconstructed witnesses and `#gen_theorems` persists them
incrementally. Captured at `#gen_spec`. -/
set_option veil.gen.streamTheorems true

/- VC registry ([Dependencies.md](../docs/Dependencies.md) §1): persist the
VC statements + metadata for the cross-file check/prove commands. -/
set_option veil.gen.vcRegistry true

/- Proof cache ([Dependencies.md](../docs/Dependencies.md) §2): store every
reconstructed proof this sweep produces in the content-addressed on-disk
cache (`.lake/build/veilcache/`) and consult it before every solve. The key
is the statement itself; every hit is re-checked against the live goal, and
the kernel still checks at every persistence point. File-level so the
dischargers capture it at `#gen_spec`. -/
set_option veil.cache.proofs true

/-! ## Step properties — two-state cells, checked per action

Stated for the contract's step-level fields: the two monotonicities (also
derivable from the update records) and the paper's Monotonicity, which
needs `[open_local_order]` at the pre-state together with `open_slot`'s
guard. -/

/-- `opened` is only ever set. -/
step_property [opened_mono] { opened I S → opened' I S }
/-- `completed` is only ever set. -/
step_property [completed_mono] { completed I S → completed' I S }
/-- The paper's Monotonicity (Lemma 13 (`lemma:conductor-monotonicity`)): a slot below
one an honest validator has opened, and not opened itself, is never opened
afterwards. -/
step_property [monotonicity] {
  ∀ (i : node) (s0 s1 : slot),
    ¬ fm.byz i ∧ opened i s1 ∧ slot_ord.le s0 s1 ∧ s0 ≠ s1 ∧ ¬ opened i s0 →
    ¬ opened' i s0 }

/- Solver budget for this module's in-file sweep: three times Veil's 60 s
default, for the same reason the proof files carry it
([ProofPrelude.lean](ProofPrelude.lean)) — the budget has to hold on the
slowest machine that runs cold, which is CI's 4-core runner. The sweep's
cell times are in [ConductorBounds.md](../docs/ConductorBounds.md) §10.
A cell that starts needing minutes is diverging, and wants the fact it
re-derives stated as an invariant instead (`[first_agree]`,
`[first_above_prev]`). File-level, before `#gen_spec`: solver options are
captured there ([CLAUDE.md](../CLAUDE.md), "Build"). -/
set_option veil.smt.timeout 180

#gen_spec

/- The sweep runs with the solver options set above. They are captured at
`#gen_spec`, so a `set_option … in` around this command is inert. -/
#check_invariants

/- Persist the discharged VCs as environment theorems for the
composition layer. With `veil.gen.streamTheorems` above, the retained
witnesses are persisted incrementally, with no re-elaboration. -/
#gen_theorems

/-! ## Reachability sanity checks

Against vacuous safety ([TODO.md](../docs/TODO.md) § "Soundness"): the ACS
pipeline is exercisable end-to-end — open and complete a slot of window 1,
become ready, propose, let the oracle decide, and enter window 2. -/

-- The steps are named: an `any 5 actions` trace's transition disjunction
-- exceeds the trace pipeline's simp budget.
sat trace {
  open_slot
  complete_slot
  acs_propose
  acs_step
  enter_window
  assert (∃ i w, ¬ w = win_ord.zero ∧ entered i w)
}

sat trace {
  any 2 actions
  assert (∃ i s, opened i s ∧ completed i s)
}

end Conductor
