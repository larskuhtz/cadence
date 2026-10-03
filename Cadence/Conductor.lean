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
validator has completed all scheduled slots up to the current window's
readiness boundary (its `p`-th slot — Algorithm 7, line 23 (`line:ready-check`)), it proposes a
first slot for the next window to that window's ACS instance
(Algorithm 7, line 42 (`line:acs-propose`)), choosing a slot strictly beyond the current window's
last (Algorithm 7, lines 40–41 (`line:sstar-guard`–`line:sstar-update`)). When ACS decides, the next
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
  `safety [window_assignment_agreement]` (structural: intervals are global
  oracle state, unique per window);
* opened-set structure (interval form of Proposition 8 (`prop:acs-fate-range`) /
  Proposition 11 (`prop:open-count-window`)) — `[opened_win_contained]`,
  `[open_local_order]`;
* open-prefix agreement — `safety [open_prefix_agreement]`, discharging
  the `OrchestratorSafety.open_prefix_agreement` contract field, which the
  `Cadence` glue module consumes through its `orch` class constraint;
* boundedness as interval inclusion (Lemma 14 (`lem:boundedness`), interval form) —
  `safety [bounded_tail]`: every scheduled-but-uncompleted slot lies
  strictly above the *previous* window's readiness boundary. The numeric
  `(2W − p)` bound is the one-line meta corollary: the region above
  `boundary(ω−1)` within scheduled intervals is the last `W − p` slots of
  window `ω−1` plus the `W` slots of window `ω`;
* integrity's clock half ("no open before the slot's starting time",
  Algorithm 7, line 27 (`line:conductor-wait-for-open`)) — `safety [opened_after_start]`, via the
  abstract monotone clock.

Meta (documented; genuinely temporal — see the Liveness section):
* totality (Lemma 15 (`lemma:conductor-totality`), `d_tot`-totality) and
  `(2Wτ)`-recovery — the paper's per-window induction;
* the four parameter assumptions (Algorithm 7, lines 7–10
  (`line:assumption-one`–`line:assumption-four`));
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
  "not before the starting time" (`open_slot`) expressible; all
  quantitative timing stays meta.

## Adversary

Conductor has **no Byzantine message surface beyond ACS**
([ConductorDesign.md](../docs/ConductorDesign.md) §3): its only inputs are
local `completed(s)` callbacks and ACS decisions. Byzantine influence enters
as (i) Byzantine validators' own ACS proposals — internal steps of the ACS
instance (`acs_step`), which the contract leaves unconstrained for Byzantine
validators — and (ii) up to `f` Byzantine pairs inside the decided core
set, captured by the median-range `require` of `acs_decide` (a *correct*
pair of the decided set bracketing the median from below, as an explicit
witness), justified from the contract by `Cadence.acs_median_bracket`
([AcsMedian.lean](AcsMedian.lean)). No quorum machinery and no `ByzNodeSet`
are needed; the fault pattern is the `FaultModel` the ACS contract is stated
against, otherwise unconstrained, and the resilience arithmetic (`≤ f`
Byzantine validators, one pair each in a core set of `2f + 1` validators)
lives in the ACS contract (`ACSSafety.decided_unique`,
`ACSTemporal.validity_quantitative`) and that lemma's fault-bound
hypothesis.

## Obligation discharge map (→ [Interfaces.lean](Interfaces.lean) `Orchestrator`)

The machine-checked half of this table is `Conductor.orchestratorSafety`
([Composition.lean](Composition.lean)); the rest is
`OrchestratorTemporal` there, the same rows as the fields of a class this
development supplies no instance of.

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
* **`B`-boundedness, `B = 2W − p`** — **unproven** — `safety [bounded_tail]`
  is the interval form; the count adds the widths (`[win_bounds_shift]`)
  at the instance at `slot := ℕ`
* **Totality / `R`-recovery, `R = 2Wτ`** — **unproven** — Liveness section
  below
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
/-- A window's readiness boundary, its `p`-th slot, as a function of its
first: the shift `+ (p − 1)`, the slot up to which Algorithm 7, line 23
(`line:ready-check`) asks for completion ("all but the last `W − p`"). Fixed
to `s + (p − 1)` at the instance at `slot := ℕ`, as `win_last`. -/
immutable function win_boundary : slot → slot
/-- Window 1's readiness boundary: the paper's slot `p` of window 1
(Algorithm 7, line 34 (`line:startup-last`)), `win_boundary` of slot 1
(`[genesis_window]`). Later windows' bounds are ACS-decided state. -/
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
/-- The decided window interval: first slot (the extracted median,
Algorithm 7, line 48 (`line:median-compute`)), readiness-boundary slot (the window's `p`-th
slot) and last slot (Algorithm 7, line 52 (`line:last-update`)). Computed from the decided set
(`acs_decide`), global because ACS agreement makes every correct
validator compute the same interval. Unique per window. -/
relation acs_decided (w : window) (first : slot) (boundary : slot) (last : slot)

/-! ### (L) Per-validator local state

The paper's `proposed_i` set (Algorithm 7, line 43 (`line:proposed-update`)) is the ACS state's own
record of `i`'s input — `acs.proposed (acs_state w) i s` — and needs no local
copy. -/

/-- `i` has entered window `w` (Algorithm 7, line 30 (`line:enter_window_1`), Algorithm 7, line 47 (`line:enter_window_omega`)). -/
relation entered (i : node) (w : window)
/-- The `open(s)` *output* has fired at `i` (Algorithm 7, line 28 (`line:trigger-open`)). -/
relation opened (i : node) (s : slot)
/-- The window `i` opened `s` under (proof bookkeeping). -/
relation opened_win (i : node) (s : slot) (w : window)
/-- `i` has received the `completed(s)` input (Algorithm 7, line 35 (`line:upon-completed`);
within Cadence: `i` finalized `S[s]`). -/
relation completed (i : node) (s : slot)

#gen_state

/-- The ACS instances start in initial states of their contract. -/
assumption [acs_init]
  ∀ (w : window), acs.init (acs_init_state w)
/-- A window's first slot, readiness boundary and last slot are in order:
`s ≤ s + (p − 1) ≤ s + (W − 1)`, which is `1 ≤ p ≤ W`. The main body allows
`p = 0` as well (Algorithm 7 (`algorithm:conductor`)'s `p ∈ {0, …, W − 1}`);
the model's boundary is a slot of the window, so it covers `p ≥ 1`
([ConductorBounds.md](../docs/ConductorBounds.md) §7, F25). -/
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
/-- Starting times are monotone in slot order (`τ`-spaced deadlines,
Appendix A.1 (`subsection:mcp-preliminaries`)). Not consumed by any invariant below —
recorded for model faithfulness (it constrains reachability traces). -/
assumption [start_time_mono]
  ∀ (s s' : slot), slot_ord.lt s s' →
    time_ord.le (start_time s) (start_time s')

/-! ## Derived state -/

/-- The bounds of window `w`: window 1's are immutable configuration,
later windows' are the ACS decision (`acs_decide` requires
`w ≠ zero`, so the disjuncts are exclusive). -/
ghost relation win_bounds (w : window) (f : slot) (b : slot) (l : slot) :=
  (w = win_ord.zero ∧ f = slot_ord.zero ∧ b = genesis_boundary ∧ l = genesis_last) ∨
  acs_decided w f b l

/-- The paper's eager `opened_i` variable (Algorithm 7, line 33 (`line:startup-opened-update`),
Algorithm 7, line 51 (`line:acs-opened-update`)): the union of the entered windows' intervals. -/
ghost relation slot_scheduled (i : node) (s : slot) :=
  ∃ w f b l, entered i w ∧ win_bounds w f b l ∧
    slot_ord.le f s ∧ slot_ord.le s l

/-- `i` is *in* window `w`: entered it, not yet entered its successor
(the `current_window_i` variable, Algorithm 7, line 14 (`line:current_window_init`) /
Algorithm 7, line 46 (`line:window-increment`); negative observation of own local state only). -/
ghost relation in_window (i : node) (w : window) :=
  entered i w ∧ ∀ w', win_ord.next w w' → ¬ entered i w'

/-- `ready_for_next_window()` (Algorithm 7, line 23 (`line:ready-check`)) while in window `w`:
every scheduled slot up to `w`'s readiness boundary is completed
(equivalently, per the paper: all but the last `W − p` of the eager
`opened_i` are complete). -/
ghost relation ready_next (i : node) (w : window) :=
  ∀ (f b l : slot), win_bounds w f b l →
    ∀ (s : slot) (w0 : window) (f0 b0 l0 : slot),
      entered i w0 → win_bounds w0 f0 b0 l0 →
      slot_ord.le f0 s → slot_ord.le s l0 → slot_ord.le s b →
      completed i s

/-- Every validator starts in window 1 (Algorithm 7, line 30 (`line:enter_window_1`)), with nothing
opened or completed and no window beyond 1 decided. -/
after_init {
  now := genesis_time
  -- Capitalized single letters are universal indices. `V` ranges over
  -- windows: `W` is the paper's window *width* throughout this file, and it
  -- also resolves to a Mathlib declaration, which Veil warns about.
  acs_state V := acs_init_state V
  acs_decided V F B L := false
  -- Every validator enters window 1 at startup (Algorithm 7, line 30 (`line:enter_window_1`)).
  entered I V := V == win_ord.zero
  opened I S := false
  opened_win I S V := false
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
the successor window `w'`, at most once. The `require` on `s_star` is the
state residue of Algorithm 7, lines 39–41 (`line:sstar-compute`–`line:sstar-update`): the proposed
slot lies strictly beyond the current window's last slot. (The other half
of the paper's computation — `s_star` is the *earliest* slot whose
starting time has not passed — is quantitative timing and feeds only the
recovery argument; meta.) -/
action acs_propose (i : node) (w : window) (w' : window) (s_star : slot)
    (acs_next : acsstate) {
  require ¬ fm.byz i
  require in_window i w
  require win_ord.next w w'
  -- At most once per window (`proposed_i`, Algorithm 7, line 43 (`line:proposed-update`)).
  require ∀ (s : slot), ¬ acs.proposed (acs_state w') i s
  require ready_next i w
  -- Algorithm 7, line 40 (`line:sstar-guard`)/Algorithm 7, line 41 (`line:sstar-update`): strictly beyond the current
  -- window (stated over `w'`'s predecessor's bounds — `w` is that
  -- predecessor; bounds are global and unique).
  require ∀ (w0 : window) (f0 b0 l0 : slot),
    win_ord.next w0 w' → win_bounds w0 f0 b0 l0 → slot_ord.lt l0 s_star
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

/-! ## ACS decision (oracle; Algorithm 7, lines 44–48 (`line:acs-decide`–`line:median-compute`) +
Algorithm 7, line 52 (`line:last-update`)) -/

/-- The handler of the output "`ACS[w]` decides": median extraction yields the
window interval `[first, last]` with readiness boundary `boundary`. The
`require`s are the handler's own guards plus the one bridge between the
contract and the median computation:

* *one interval per window* — all correct validators compute the same one
  (the contract's `agreement`: every correct decider holds the same set),
  so the interval is global state, like `mvba_decided_*` in Chorus;
* *the decision has happened* — some correct validator has decided
  (`acs.decided (acs_state w) i r1 s1` for the witness pair below implies
  `has_decided`);
* *median range validity, lower half* — the decided first slot is at
  least the slot of some correct pair in the decided set (`r1/s1`, passed
  as **explicit witnesses** — witnesses at the assembly action, not
  `∃`-ghosts in consumers). The model does not compute the median, and
  cardinality is outside the first-order fragment, so this is the **one
  stated bridge** between the contract and the model, a `require` and not
  a derivation. That it removes no behaviour of a correct ACS is a theorem
  from the contract: the median of a correct decider's set is bracketed by
  two of its correct pairs (`Cadence.acs_median_bracket`,
  [AcsMedian.lean](AcsMedian.lean), from `decided_unique`,
  `validity_quantitative` and the system's fault bound, through
  [Windows.lean](Windows.lean)'s `lowerMedian_between_correct`). That the
  witness *is* a genuine correct proposal is the contract's
  `validity_genuine`. The
  *upper* half of the bracket (`median ≤` some correct proposal — also
  provided by the median lemma) is deliberately not modelled: no safety
  property consumes it — it feeds only the recovery timing argument
  (Proposition 19 (`prop:first-post-gst-window-time`)), which is meta;
* *sequencing* — the predecessor window `w0` and its bounds are witnesses
  too: a decision presupposes correct proposals, whose proposers had
  entered `w0` (which therefore has bounds). This is what keeps window
  decisions sequential, and it gives the ordering invariants their ground
  terms;
* *interval width* — the recorded interval is the window's `W` slots from
  `first`, with the boundary at its `p`-th slot: `[first, win_last first]`
  and `win_boundary first`, the decided interval of Algorithm 7, lines
  49–52 (`line:open-foreach`–`line:last-update`). The widths are the shift
  functions' and are fixed at the instance at `slot := ℕ`; no safety
  property below depends on them. -/
action acs_decide (w0 : window) (w : window) (first : slot)
    (f0 : slot) (b0 : slot) (l0 : slot)
    (r1 : node) (s1 : slot) {
  -- Window 1 is never ACS-decided.
  require ¬ w = win_ord.zero
  -- One interval per window (from the contract's agreement).
  require ∀ f' b' l', ¬ acs_decided w f' b' l'
  -- Decision precedes entry: no honest validator has entered a window
  -- whose ACS has not decided. Derivable ([entered_has_bounds] + the
  -- uniqueness require + `w ≠ zero`) — stated explicitly because the
  -- SMT search for `bounded_tail` at this action diverges re-deriving
  -- it (witness materialisation, in require form).
  require ∀ (i : node), ¬ fm.byz i → ¬ entered i w
  -- Predecessor window and its (already fixed) bounds.
  require win_ord.next w0 w
  require win_bounds w0 f0 b0 l0
  -- Median range validity (lower half), with an explicit correct witness
  -- pair `(r1, s1)` from a correct decider's decided set.
  require ¬ fm.byz r1
  require ∃ (i : node), ¬ fm.byz i ∧ acs.decided (acs_state w) i r1 s1
  require slot_ord.le s1 first
  -- The window's `W` slots from `first`, boundary at the `p`-th
  -- (Algorithm 7, lines 49–52).
  acs_decided w first (win_boundary first) (win_last first) := true
}

/-! ## Window entry (Algorithm 7, line 44 (`line:acs-decide`) handler:
Algorithm 7, lines 45–47 (`line:acs-abandon`–`line:enter_window_omega`)) -/

/-- An honest validator in window `w` enters the successor `w'` once *its
own* `ACS[w']` has decided and the readiness condition holds (the two
activation conditions of Algorithm 7, line 44 (`line:acs-decide`), which
fires on `p_i`'s own `decide`). It abandons the instance in the same step
(Algorithm 7, line 45 (`line:acs-abandon`)), which is why abandonment never
precedes decision (`[acs_abandoned_decided]`). Entry *schedules* the
window's slots (the eager `opened_i` update — here the ghost
`slot_scheduled` grows by the decided interval, which `acs_decide` read off
the decided set); the `open` outputs fire later via `open_slot`. -/
action enter_window (i : node) (w : window) (w' : window)
    (f : slot) (b : slot) (l : slot) (acs_next : acsstate) {
  require ¬ fm.byz i
  require in_window i w
  require win_ord.next w w'
  require acs_decided w' f b l
  -- `i`'s own `ACS[w']` has decided.
  require acs.has_decided (acs_state w') i
  require ready_next i w
  -- `ACS[w'].abandon()`: an input transition of the instance's state.
  require acs.abandon (acs_state w') i acs_next
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
  require win_bounds w f b l
  require slot_ord.le f s
  require slot_ord.le s l
  require ¬ opened i s
  require time_ord.le (start_time s) now
  require ∀ (s' : slot) (w0 : window) (f0 b0 l0 : slot),
    entered i w0 → win_bounds w0 f0 b0 l0 →
    slot_ord.le f0 s' → slot_ord.le s' l0 → slot_ord.lt s' s →
    opened i s'
  opened i s := true
  opened_win i s w := true
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
Conductor-module "Safety"): the window intervals are agreed — one decided
interval per window. (The per-validator statement of the paper collapses
to this because the model globalizes the ACS decision, which its
agreement property licenses; any two validators placing a slot in a
window place it in the same interval.) -/
safety [window_assignment_agreement]
  ∀ (w : window) (f b l f' b' l' : slot),
    acs_decided w f b l ∧ acs_decided w f' b' l' →
    f = f' ∧ b = b' ∧ l = l'

/-- Cross-window slot monotonicity (Proposition 7 (`prop:acs-nonoverlap`)): a decided
window's interval lies strictly above its predecessor's (the paper's
`s.number ≥ s'.number + W`, in interval form). -/
safety [win_separation]
  ∀ (w0 w : window) (f0 b0 l0 f b l : slot),
    win_ord.next w0 w ∧ win_bounds w0 f0 b0 l0 ∧ acs_decided w f b l →
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
every scheduled slot up to the readiness boundary of `w'`'s predecessor
is completed. Contrapositive reading for the *current* window `ω`: every
scheduled-but-uncompleted slot lies strictly above `boundary(ω−1)` —
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
    entered i w' ∧ win_ord.next w w' ∧ win_bounds w f b l ∧
    -- s is scheduled (in entered window ws's interval), at or below b
    entered i ws ∧ win_bounds ws fs bs ls ∧
    slot_ord.le fs s ∧ slot_ord.le s ls ∧ slot_ord.le s b →
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

/-- Window 1 is never ACS-decided (its bounds are configuration). -/
invariant [decided_nonzero]
  ∀ (w : window) (f b l : slot),
    acs_decided w f b l → ¬ w = win_ord.zero

/-- Interval shape: first ≤ boundary ≤ last. -/
invariant [bounds_shape]
  ∀ (w : window) (f b l : slot),
    win_bounds w f b l → slot_ord.le f b ∧ slot_ord.le b l

/-- Window width: every window's boundary and last slot are the shifts of
its first slot, so every window holds the `W` slots from its first, with
its boundary at the `p`-th (Algorithm 7, lines 31–34
(`line:startup-foreach`–`line:startup-last`) and Algorithm 7, lines 49–52
(`line:open-foreach`–`line:last-update`)). -/
invariant [win_bounds_shift]
  ∀ (w : window) (f b l : slot),
    win_bounds w f b l → b = win_boundary f ∧ l = win_last f

/-- Decisions are sequential: every nonzero window below a decided window
is decided (the ACS instances are driven one window at a time —
Proposition 6 (`lemma:window-entry`) + the activation chain). -/
invariant [decided_downward_closed]
  ∀ (w w' : window) (f' b' l' : slot),
    acs_decided w' f' b' l' ∧ win_ord.lt w w' ∧ ¬ w = win_ord.zero →
    ∃ f b l, acs_decided w f b l

/-- Transitive interval ordering (Proposition 8 (`prop:acs-fate-range`)'s "later windows
cover slots of strictly larger number", closed under the window order):
the intervals of any two bounded windows are strictly separated. -/
invariant [win_bounds_ordered]
  ∀ (w w' : window) (f b l f' b' l' : slot),
    win_ord.lt w w' ∧ win_bounds w f b l ∧ win_bounds w' f' b' l' →
    slot_ord.lt l f'

/-! ## Invariants — ACS proposals -/

/-- An honest ACS proposal for window `w'` is strictly beyond the
predecessor window's interval (Algorithm 7, line 40 (`line:sstar-guard`)/Algorithm 7, line 41 (`line:sstar-update`)
persisted; feeds `[win_separation]` through the median witnesses). -/
invariant [acs_proposal_above_prev]
  ∀ (r : node) (w' : window) (s : slot) (w0 : window) (f0 b0 l0 : slot),
    ¬ fm.byz r ∧ acs.proposed (acs_state w') r s ∧ win_ord.next w0 w' ∧
    win_bounds w0 f0 b0 l0 →
    slot_ord.lt l0 s

/-- An honest proposal to `ACS[w']` presupposes having entered the
predecessor window (the Algorithm 7, line 37 (`line:ready`) activation context). -/
invariant [proposal_prev_entered]
  ∀ (r : node) (w' : window) (s : slot),
    ¬ fm.byz r ∧ acs.proposed (acs_state w') r s →
    ∃ w0, win_ord.next w0 w' ∧ entered r w0

/-- Entered windows have (fixed) bounds: window 1 by configuration, later
windows by the ACS decision that gated entry. -/
invariant [entered_has_bounds]
  ∀ (i : node) (w : window),
    ¬ fm.byz i ∧ entered i w → ∃ f b l, win_bounds w f b l

/-! ## Invariants — openings -/

/-- Every opening is recorded with its window. -/
invariant [opened_backed]
  ∀ (i : node) (s : slot),
    ¬ fm.byz i ∧ opened i s → ∃ w, opened_win i s w

/-- The recorded window was entered. -/
invariant [opened_win_entered]
  ∀ (i : node) (s : slot) (w : window),
    ¬ fm.byz i ∧ opened_win i s w → entered i w

/-- The opened slot lies in its recorded window's interval
(Proposition 8 (`prop:acs-fate-range`), interval form; bounds are unique, so the
∀-formulation is exact). -/
invariant [opened_win_contained]
  ∀ (i : node) (s : slot) (w : window) (f b l : slot),
    ¬ fm.byz i ∧ opened_win i s w ∧ win_bounds w f b l →
    slot_ord.le f s ∧ slot_ord.le s l

/-- In-order openings (Proposition 10 (`prop:fate-order`) + Lemma 13 (`lemma:conductor-monotonicity`),
per-validator): below an opened slot, every scheduled slot is opened. -/
invariant [open_local_order]
  ∀ (i : node) (s s' : slot) (w0 : window) (f0 b0 l0 : slot),
    ¬ fm.byz i ∧ opened i s ∧
    entered i w0 ∧ win_bounds w0 f0 b0 l0 ∧
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

/-! ## Liveness — meta-argument (totality & recovery)

Totality and `(2Wτ)`-recovery are genuinely temporal: the paper proves
them **only for Conductor run within Cadence** (they hinge on slots
actually completing — Lemma 15 (`lemma:conductor-totality`) intro), by an intricate
per-window induction. Following the Chorus doctrine
([ChorusDesign.md](../docs/ChorusDesign.md) §7), the temporal glue lives here
as named meta-axioms over the composed system, and the state-level content
they need is exactly the invariant set above.

### Meta-axioms

* **(F-justice)** — the honest actions `acs_propose`, `enter_window`,
  `open_slot`, `complete_slot`'s *upstream* (the glue's finalize chain),
  and `tick`, when continuously enabled, eventually fire. Enabledness is
  monotone for all of them (positive stable guards; `ready_next` is
  monotone because `completed` only grows and the scheduled set grows
  only with entry, which preserves readiness of *past* windows —
  boundaries of later windows lie above, `[win_bounds_ordered]`).
* **(A-acs-termination)** (Module 4 (`mod:acs`) ℓ-Termination) — once every honest
  validator has proposed to `ACS[w]`, the `acs_decide w` oracle
  eventually fires (with witnesses supplied by the median lemma,
  [Windows.lean](Windows.lean) `lowerMedian_between_correct`).
* **(A-acs-totality)** (Module 4 (`mod:acs`) Δ-Totality) — `enter_window`
  waits for the validator's *own* decision, so every correct validator
  needs its instance to decide; Δ-Totality bounds when that happens once
  one correct validator has decided. Its two assumptions are met by the
  model: no premature abandonment is `[acs_abandoned_decided]`, and
  Δ-synchronized proposals is a timing fact (Corollary 2
  (`cor:proposal-synchronization`)).
* **(A-sc-totality)**, **(A-sc-termination)** — completions propagate:
  within Cadence, `completed` is Chorus finalization, which is
  `d_tot`-total (Proposition 4 (`prop:chorus-totality`)) and `ℓ_chorus`-terminating.
  These enter through `complete_slot`'s occurrence, not its guard.

### The paper's induction, mirrored

Proposition 15 (`prop:enters-every-window`) (every correct validator enters every window):
induction over windows. In window `w`, either some correct validator
decides `ACS[w+1]` — global here, so all see it — or none does, in which
case every correct validator stays in `w`, eventually opens every slot of
its scheduled prefix (`open_slot` enabled once `tick` passes the starting
times — (F-justice) twice), completes them ((A-sc-termination) via the
glue), becomes ready, proposes ((F-justice) on `acs_propose`), and
(A-acs-termination) decides — then `enter_window` is enabled at every
correct validator and (F-justice) fires it.

`(2Wτ)`-recovery (Proposition 16 (`prop:window-open-time`) → Proposition 18 (`prop:smooth-windows`) →
Proposition 19 (`prop:first-post-gst-window-time`)) additionally tracks *when*: it needs
the four parameter assumptions (Algorithm 7, lines 7–10
(`line:assumption-one`–`line:assumption-four`))

1. `(p−1)τ + Φ_oc + ℓ ≤ Wτ`
2. `(p−1)τ + Φ_oc ≤ (W−1)τ`
3. `Δ < ℓ`
4. `d_tot + ℓ ≤ (p−1)τ`

with `Φ_oc = ℓ_chorus + d_tot` (Proposition 14 (`prop:conductor-open-to-complete`)).
These are arithmetic side conditions on real-time constants that do not
exist at this abstraction; they are recorded here as the assumptions the
meta-argument consumes. The quantitative conclusions (`d_tot`-totality of
openings, on-time opening from the second post-GST window) are theorems
*about the timed system*, out of scope for the untimed model by design. -/

/- The `Enumeration`/`FinEncodable` derivation over the action `Label`
sum must traverse `acs_decide`'s 12-nested parameter sigma, which exceeds
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
slowest machine that runs cold, which is CI's 4-core runner. At the last
measurement this module's slowest cell, `enter_window × bounded_tail`, ran
there at 95% of the 60 s budget. It is a *completed* solve, so the remedy is
the budget; a cell that starts needing minutes is diverging, and wants a
manual proof instead. File-level, before `#gen_spec`: solver options are
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
  acs_decide
  enter_window
  assert (∃ i w, ¬ w = win_ord.zero ∧ entered i w)
}

sat trace {
  any 2 actions
  assert (∃ i s, opened i s ∧ completed i s)
}

end Conductor
