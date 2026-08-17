import Veil
import Cadence.Interfaces
import Cadence.Windows
import Cadence.Tooling

/-! # Conductor — the window-based orchestrator (`algorithm:conductor`)

*Note: opening this file in a Lean-enabled editor re-runs its verification
sweep in the language server (~1 min, one SMT solve per VC). Prefer
`lake build Cadence.Conductor`; see `README.md` § "Before you
open these files in an editor".*

Veil model of the Conductor, the orchestrator instantiation of the Cadence
extreme-pipelining framework. Reference:
`papers/cadence/src/p2_conductor_proofs.tex` `§section:conductor-formal` — the
**ACS-based formal version** (windows over `mod:acs`), which is the one the
paper proves; the prose chapter `p2_conductor.tex` describes a not-yet-
reconciled deadline-MVBA variant (divergence flagged —
`docs/ConductorPlan.md` §1/§8). Plan: `docs/ConductorPlan.md`
§3; contracts: [`Interfaces.lean`](./Interfaces.lean) (`Orchestrator`,
`ACS`); support theory: [`Windows.lean`](./Windows.lean).

## Protocol summary (`algorithm:conductor`)

Slots are scheduled in *windows* of `W` consecutive slots. Every validator
starts in window 1 (slots `1..W`, opened at their starting times). Once a
validator has completed all scheduled slots up to the current window's
readiness boundary (its `p`-th slot — `line:ready-check`), it proposes a
first slot for the next window to that window's ACS instance
(`line:acs-propose`), choosing a slot strictly beyond the current window's
last (`line:sstar-guard`–`line:sstar-update`). When ACS decides, the next
window's first slot is the **median** of the decided proposals
(`line:median-compute`), and the validator enters the window and schedules
its `W` slots (`line:open-foreach`), each opening at its starting time
(`line:conductor-wait-for-open`).

## What is modelled vs. meta (per `docs/ConductorPlan.md` §3)

SMT-checked here (the safety-shaped content):
* window-entry order (`lemma:window-entry`) — `[entered_prefix]`;
* cross-window slot monotonicity (`prop:acs-nonoverlap`) —
  `safety [win_separation]` (+ the transitive `[win_bounds_ordered]`);
* window-assignment agreement (`prop:window-agreement`) —
  `safety [window_assignment_agreement]` (structural: intervals are global
  oracle state, unique per window);
* opened-set structure (interval form of `prop:acs-fate-range` /
  `prop:open-count-window`) — `[opened_win_contained]`,
  `[open_local_order]`;
* open-prefix agreement — `safety [open_prefix_agreement]`, discharging
  the `Orchestrator.open_prefix_agreement` contract field consumed by the
  `Cadence` glue module's `orch_open` oracle requires (a)/(b);
* boundedness as interval inclusion (`lem:boundedness`, interval form) —
  `safety [bounded_tail]`: every scheduled-but-uncompleted slot lies
  strictly above the *previous* window's readiness boundary. The numeric
  `(2W − p)` bound is the one-line meta corollary: the region above
  `boundary(ω−1)` within scheduled intervals is the last `W − p` slots of
  window `ω−1` plus the `W` slots of window `ω`;
* integrity's clock half ("no open before the slot's starting time",
  `line:conductor-wait-for-open`) — `safety [opened_after_start]`, via the
  abstract monotone clock.

Meta (documented; genuinely temporal — see the Liveness section):
* totality (`lemma:conductor-totality`, `d_tot`-totality) and
  `(2Wτ)`-recovery — the paper's per-window induction;
* the four parameter assumptions (`line:assumption-one..four`);
* `ℓ`-termination / `Δ`-totality of ACS — **(A-acs-termination)** /
  **(A-acs-totality)** (`Interfaces.lean` `ACS`);
* window width `= W` and every cardinality statement (interval
  formulations replace them, per plan §3).

## The eager `opened_i` variable vs. the `open(s)` output

`algorithm:conductor` adds all `W` slots to the *variable* `opened_i`
eagerly upon window entry (`line:acs-opened-update`), while the `open(s)`
*outputs* fire later, each at its slot's starting time
(`line:conductor-wait-for-open`). The model keeps the two apart:

* the eager variable is the **ghost** `slot_scheduled` — the union of the
  entered windows' intervals (no state, no bulk updates);
* the relation `opened` records the **outputs** (what `mod:orchestrator_2`
  and the glue's `orch_open` consume).

The readiness check (`line:ready-check`, "all but the last `W − p` of
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
  (`prop:fate-order`'s conclusion: with synchronized clocks and punctual
  triggers, openings occur in slot order). This converts the paper's
  timing argument into an explicit scheduling assumption of the model,
  documented here; it is the Conductor analogue of Chorus's `Phase`
  ordering.
* The clock (`now`, advanced by `tick`) exists only to make the guards
  "not before the starting time" (`open_slot`) expressible; all
  quantitative timing stays meta.

## Adversary

Conductor has **no Byzantine message surface beyond ACS**
(`docs/ConductorPlan.md` §3): its only inputs are local `completed(s)`
callbacks and ACS decisions. Byzantine influence enters as (i) Byzantine
validators' own ACS proposals — the free-input action `byz_acs_propose` —
and (ii) up to `f` Byzantine pairs inside the decided core set, captured
by the median-range `require` of `acs_decide` (two *correct* bracketing
proposals as explicit witnesses), justified by the quantitative half of
ACS validity through the median lemma
(`Windows.lean` `lowerMedian_between_correct`). No quorum machinery and no
`ByzNodeSet` are needed; `is_byz` is an unconstrained immutable predicate,
and the resilience arithmetic (`n = 3f + 1`, `≤ f` faulty pairs in a
`2f+1`-sized core set) lives in the ACS implementation's obligations and
the median lemma's hypotheses.

## Obligation discharge map (→ `Interfaces.lean` `Orchestrator`)

| Contract item | Discharged by |
|---|---|
| `open_prefix_agreement` (class field) | `safety [open_prefix_agreement]` |
| Integrity "at most once" | `¬ opened i s` require + monotone relation (an `open` output exists at most once per slot) |
| Integrity "not before starting time" | `safety [opened_after_start]` (+ synchronized-clocks assumption) |
| Monotonicity | `[open_local_order]` (in-order openings; per-validator) |
| `B`-boundedness, `B = 2W − p` | `safety [bounded_tail]` (interval form) + meta counting corollary |
| Totality / `R`-recovery, `R = 2Wτ` | meta — Liveness section below |
-/

veil module Conductor

/-! ## Types -/

-- Slot identifiers with a total order, a least slot (the paper's slot 1),
-- and a derived successor. No `+W` arithmetic (plan §3, ingredient 1).
type slot
-- Window indices (the paper's `ω ∈ ℕ≥1`): least window = window 1,
-- `next` = the `ω + 1` of `line:window-increment`.
type window
-- Abstract clock values.
type time
-- Validator identity.
type node

instantiate slot_ord : TotalOrderWithMinimum slot
instantiate win_ord : TotalOrderWithMinimum window
instantiate time_ord : TotalOrder time

/-! ## Immutable configuration -/

-- Byzantine validators (unconstrained — see "Adversary" above).
immutable relation is_byz (i : node)
-- The slot's starting time `s.deadline − Δ` (`line:conductor-wait-for-open`).
immutable function start_time : slot → time
-- Window 1's interval is `[slot 1, genesis_last]` with readiness boundary
-- `genesis_boundary` (the paper's slots `p` and `W` of window 1,
-- `line:startup-last`). Later windows' bounds are ACS-decided state.
immutable individual genesis_boundary : slot
immutable individual genesis_last : slot
-- Initial clock value.
immutable individual genesis_time : time

/-! ## Mutable state -/

-- The abstract global clock (synchronized clocks are a protocol
-- assumption — `algorithm:conductor` preamble "recall that validators'
-- clocks are synchronized").
individual now : time

-- (A) ACS oracle state, per window instance `ACS[w]` (`line:acs-instances`).
-- Proposals are *inputs* (honest via `acs_propose`, Byzantine free inputs
-- via `byz_acs_propose`); the decision is global — ACS agreement collapses
-- all correct validators' views into one relation, exactly like Chorus's
-- `mvba_decided_*`.
relation acs_proposed (w : window) (r : node) (s : slot)
-- The decided window interval: first slot (the extracted median,
-- `line:median-compute`), readiness-boundary slot (the window's `p`-th
-- slot) and last slot (`line:last-update`). Unique per window.
relation acs_decided (w : window) (first : slot) (boundary : slot) (last : slot)

-- (L) Per-validator local state.
-- `i` has proposed to `ACS[w]` (the `proposed_i` set, `line:proposed-update`).
relation acs_has_proposed (i : node) (w : window)
-- `i` has entered window `w` (`line:enter_window_1`, `line:enter_window_omega`).
relation entered (i : node) (w : window)
-- The `open(s)` *output* has fired at `i` (`line:trigger-open`).
relation opened (i : node) (s : slot)
-- ... recording the window it was scheduled under (proof bookkeeping).
relation opened_win (i : node) (s : slot) (w : window)
-- `i` has received the `completed(s)` input (`line:upon-completed`;
-- within Cadence: `i` finalized `S[s]`).
relation completed (i : node) (s : slot)

#gen_state

-- Window 1's interval is well-formed: `slot 1 ≤ boundary ≤ last`
-- (the `p`-th and `W`-th slots of `[1, W]`).
assumption [genesis_shape]
  slot_ord.le slot_ord.zero genesis_boundary ∧
  slot_ord.le genesis_boundary genesis_last
-- Starting times are monotone in slot order (`τ`-spaced deadlines,
-- `subsection:mcp-preliminaries`). Not consumed by any invariant below —
-- recorded for model faithfulness (it constrains reachability traces).
assumption [start_time_mono]
  ∀ (s s' : slot), slot_ord.lt s s' →
    time_ord.le (start_time s) (start_time s')

/-! ## Derived state -/

-- The bounds of window `w`: window 1's are immutable configuration,
-- later windows' are the ACS decision (`acs_decide` requires
-- `w ≠ zero`, so the disjuncts are exclusive).
ghost relation win_bounds (w : window) (f : slot) (b : slot) (l : slot) :=
  (w = win_ord.zero ∧ f = slot_ord.zero ∧ b = genesis_boundary ∧ l = genesis_last) ∨
  acs_decided w f b l

-- The paper's eager `opened_i` variable (`line:startup-opened-update`,
-- `line:acs-opened-update`): the union of the entered windows' intervals.
ghost relation slot_scheduled (i : node) (s : slot) :=
  ∃ w f b l, entered i w ∧ win_bounds w f b l ∧
    slot_ord.le f s ∧ slot_ord.le s l

-- `i` is *in* window `w`: entered it, not yet entered its successor
-- (the `current_window_i` variable, `line:current_window_init` /
-- `line:window-increment`; negative observation of own local state only).
ghost relation in_window (i : node) (w : window) :=
  entered i w ∧ ∀ w', win_ord.next w w' → ¬ entered i w'

-- `ready_for_next_window()` (`line:ready-check`) while in window `w`:
-- every scheduled slot up to `w`'s readiness boundary is completed
-- (equivalently, per the paper: all but the last `W − p` of the eager
-- `opened_i` are complete).
ghost relation ready_next (i : node) (w : window) :=
  ∀ (f b l : slot), win_bounds w f b l →
    ∀ (s : slot) (w0 : window) (f0 b0 l0 : slot),
      entered i w0 → win_bounds w0 f0 b0 l0 →
      slot_ord.le f0 s → slot_ord.le s l0 → slot_ord.le s b →
      completed i s

after_init {
  now := genesis_time
  acs_proposed W R S := false
  acs_decided W F B L := false
  acs_has_proposed I W := false
  -- Every validator enters window 1 at startup (`line:enter_window_1`).
  entered I W := W == win_ord.zero
  opened I S := false
  opened_win I S W := false
  completed I S := false
}

/-! ## Clock -/

/- The abstract clock advances monotonically and nondeterministically.
(Only the guard "not before the starting time" consumes it.) -/
action tick (t : time) {
  require time_ord.le now t
  now := t
}

/-! ## ACS proposal (`line:ready`–`line:proposed-update`)

An honest validator in window `w`, once ready, proposes a first slot for
the successor window `w'`, at most once. The `require` on `s_star` is the
state residue of `line:sstar-compute`–`line:sstar-update`: the proposed
slot lies strictly beyond the current window's last slot. (The other half
of the paper's computation — `s_star` is the *earliest* slot whose
starting time has not passed — is quantitative timing and feeds only the
recovery argument; meta.) -/
action acs_propose (i : node) (w : window) (w' : window) (s_star : slot) {
  require ¬ is_byz i
  require in_window i w
  require win_ord.next w w'
  require ¬ acs_has_proposed i w'
  require ready_next i w
  -- `line:sstar-guard`/`line:sstar-update`: strictly beyond the current
  -- window (stated over `w'`'s predecessor's bounds — `w` is that
  -- predecessor; bounds are global and unique).
  require ∀ (w0 : window) (f0 b0 l0 : slot),
    win_ord.next w0 w' → win_bounds w0 f0 b0 l0 → slot_ord.lt l0 s_star
  acs_proposed w' i s_star := true
  acs_has_proposed i w' := true
}

/- Byzantine ACS proposals are free oracle inputs (a Byzantine validator
may input anything, anytime, repeatedly). -/
action byz_acs_propose (r : node) (w : window) (s : slot) {
  require is_byz r
  acs_proposed w r s := true
}

/-! ## ACS decision (oracle; `line:acs-decide`–`line:median-compute` +
`line:last-update`)

The oracle event "`ACS[w]` decides, and median extraction yields the
window interval `[first, last]` with readiness boundary `boundary`". The
`require`s are the ACS contract (`mod:acs`, `Interfaces.lean` `ACS`)
plus the median extraction:

* *agreement* — at most one decision per window (all correct validators
  share it; global-state encoding, like `mvba_decided_*` in Chorus);
* *median range validity, lower half* — the decided first slot is at
  least some correct validator's proposal (`r1/s1`, passed as **explicit
  witnesses** — Build #10 lesson: witnesses at the assembly action, not
  `∃`-ghosts in consumers). Justified by the quantitative half of ACS
  validity (≥ `2f+1` pairs, ≤ `f` Byzantine) through `Windows.lean`
  `lowerMedian_between_correct`. This subsumes the qualitative validity
  (`ACS.validity_genuine` — the witness *is* a genuine correct proposal)
  and integrity (`ACS.integrity` — a correct proposal exists). The
  *upper* half of the bracket (`median ≤` some correct proposal — also
  provided by the median lemma) is deliberately not modelled: no safety
  property consumes it — it feeds only the recovery timing argument
  (`prop:first-post-gst-window-time`), which is meta;
* *sequencing* — the predecessor window `w0` and its bounds are witnesses
  too: a decision presupposes correct proposals, whose proposers had
  entered `w0` (which therefore has bounds). This is what keeps window
  decisions sequential, and it gives the ordering invariants their ground
  terms;
* *interval shape* — `first ≤ boundary ≤ last` (the boundary is the
  window's `p`-th slot, its last the `W`-th; widths stay meta).

The decided interval is deliberately *not* forced to be exactly `W` slots
wide — cardinalities are outside the relational layer (plan §3); every
safety property below is width-independent. -/
action acs_decide (w0 : window) (w : window)
    (first : slot) (boundary : slot) (last : slot)
    (f0 : slot) (b0 : slot) (l0 : slot)
    (r1 : node) (s1 : slot) {
  -- Window 1 is never ACS-decided.
  require ¬ w = win_ord.zero
  -- Agreement: one decision per window.
  require ∀ f' b' l', ¬ acs_decided w f' b' l'
  -- Decision precedes entry: no honest validator has entered a window
  -- whose ACS has not decided. Derivable ([entered_has_bounds] + the
  -- uniqueness require + `w ≠ zero`) — stated explicitly because the
  -- SMT search for `bounded_tail` at this action diverges re-deriving
  -- it (a Build #10-style witness materialisation, in require form).
  require ∀ (i : node), ¬ is_byz i → ¬ entered i w
  -- Predecessor window and its (already fixed) bounds.
  require win_ord.next w0 w
  require win_bounds w0 f0 b0 l0
  -- Median range validity (lower half), with an explicit correct witness.
  require ¬ is_byz r1
  require acs_proposed w r1 s1
  require slot_ord.le s1 first
  -- Interval shape.
  require slot_ord.le first boundary
  require slot_ord.le boundary last
  acs_decided w first boundary last := true
}

/-! ## Window entry (`line:acs-decide` handler:
`line:window-increment`–`line:enter_window_omega`)

An honest validator in window `w` enters the successor `w'` once `ACS[w']`
has decided and the readiness condition holds (the two activation
conditions of `line:acs-decide`). Entry *schedules* the window's slots
(the eager `opened_i` update — here the ghost `slot_scheduled` grows by
the decided interval); the `open` outputs fire later via `open_slot`. -/
action enter_window (i : node) (w : window) (w' : window)
    (f : slot) (b : slot) (l : slot) {
  require ¬ is_byz i
  require in_window i w
  require win_ord.next w w'
  require acs_decided w' f b l
  require ready_next i w
  entered i w' := true
}

/-! ## Opening a slot (`schedule_opening` trigger,
`line:conductor-wait-for-open`–`line:trigger-open`)

The `open(s)` output fires at honest validator `i` for a slot of an
entered window's interval, guarded by:

* integrity — not opened before, and not before the slot's starting time
  (the clock guard; `mod:orchestrator_2` Integrity, second half);
* in-order firing — every smaller scheduled slot has already been opened.
  This is the structural rendering of the paper's timing argument
  (`prop:fate-order` + `lemma:conductor-monotonicity`): with synchronized
  clocks, triggers fire at `max(entry, start)`, which is monotone in the
  slot number across entered windows. See "Timing relaxation" in the
  module header. -/
action open_slot (i : node) (s : slot) (w : window)
    (f : slot) (b : slot) (l : slot) {
  require ¬ is_byz i
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

/-! ## Completion input (`line:upon-completed`)

The `completed(s)` callback — within Cadence, `i`'s finalization of
`S[s]` (the glue module's `sc_finalize` sets its `completed` alongside).
Asynchronous and unforced; only opened slots complete (the assumed
behaviour verified structurally on the glue side,
`Cadence.[finalized_opened]`). -/
action complete_slot (i : node) (s : slot) {
  require ¬ is_byz i
  require opened i s
  require ¬ completed i s
  completed i s := true
}

/-! ## Safety properties -/

/- Window-assignment agreement (`prop:window-agreement`, and the
Conductor-module "Safety"): the window intervals are agreed — one decided
interval per window. (The per-validator statement of the paper collapses
to this because the model globalizes the ACS decision, which its
agreement property licenses; any two validators placing a slot in a
window place it in the same interval.) -/
safety [window_assignment_agreement]
  ∀ (w : window) (f b l f' b' l' : slot),
    acs_decided w f b l ∧ acs_decided w f' b' l' →
    f = f' ∧ b = b' ∧ l = l'

/- Cross-window slot monotonicity (`prop:acs-nonoverlap`): a decided
window's interval lies strictly above its predecessor's (the paper's
`s.number ≥ s'.number + W`, in interval form). -/
safety [win_separation]
  ∀ (w0 w : window) (f0 b0 l0 f b l : slot),
    win_ord.next w0 w ∧ win_bounds w0 f0 b0 l0 ∧ acs_decided w f b l →
    slot_ord.lt l0 f

/- Open-prefix agreement — the `Orchestrator.open_prefix_agreement`
contract field (`Interfaces.lean`), consumed by the Cadence glue module's
`orch_open` requires (a)/(b): if honest `j` has opened `s` and honest `i`
has opened a smaller `s'`, then `j` has opened `s'` too. -/
safety [open_prefix_agreement]
  ∀ (i j : node) (s s' : slot),
    ¬ is_byz i ∧ ¬ is_byz j ∧ opened i s' ∧ opened j s ∧ slot_ord.lt s' s →
    opened j s'

/- Integrity, clock half (`mod:orchestrator_2` Integrity; the
`line:conductor-wait-for-open` guard persisted): no slot is opened before
its starting time. -/
safety [opened_after_start]
  ∀ (i : node) (s : slot),
    ¬ is_byz i ∧ opened i s → time_ord.le (start_time s) now

/- Boundedness, interval form (`lem:boundedness`), stated as the
persisted readiness residue: once a validator has entered window `w'`,
every scheduled slot up to the readiness boundary of `w'`'s predecessor
is completed. Contrapositive reading for the *current* window `ω`: every
scheduled-but-uncompleted slot lies strictly above `boundary(ω−1)` —
within the scheduled intervals that region is the last `W − p` slots of
window `ω−1` plus the (at most `W`) slots of window `ω`, so at most
`2W − p` slots are open-but-uncompleted; the numeric bound is that
one-line meta corollary, per the plan's interval-formulation directive.
(For `ω` = window 1 the paper's `k ≤ W ≤ 2W − p` base case needs no
statement — window 1 has no predecessor.) -/
safety [bounded_tail]
  ∀ (i : node) (s : slot) (w' w ws : window) (f b l fs bs ls : slot),
    ¬ is_byz i ∧
    -- i has entered w', whose predecessor w has boundary b
    entered i w' ∧ win_ord.next w w' ∧ win_bounds w f b l ∧
    -- s is scheduled (in entered window ws's interval), at or below b
    entered i ws ∧ win_bounds ws fs bs ls ∧
    slot_ord.le fs s ∧ slot_ord.le s ls ∧ slot_ord.le s b →
    completed i s

/-! ## Invariants — window structure -/

/- Windows are entered in order, prefix-closed (`lemma:window-entry`):
whoever is in window `w` has entered every window below. ("At most once"
needs no statement — `entered` is a set.) -/
invariant [entered_prefix]
  ∀ (i : node) (w w' : window),
    ¬ is_byz i ∧ entered i w' ∧ win_ord.lt w w' → entered i w

/- Everyone starts in window 1 (`line:enter_window_1`). -/
invariant [entered_zero]
  ∀ (i : node), entered i win_ord.zero

/- Window 1 is never ACS-decided (its bounds are configuration). -/
invariant [decided_nonzero]
  ∀ (w : window) (f b l : slot),
    acs_decided w f b l → ¬ w = win_ord.zero

/- Interval shape: first ≤ boundary ≤ last. -/
invariant [bounds_shape]
  ∀ (w : window) (f b l : slot),
    win_bounds w f b l → slot_ord.le f b ∧ slot_ord.le b l

/- Decisions are sequential: every nonzero window below a decided window
is decided (the ACS instances are driven one window at a time —
`lemma:window-entry` + the activation chain). -/
invariant [decided_downward_closed]
  ∀ (w w' : window) (f' b' l' : slot),
    acs_decided w' f' b' l' ∧ win_ord.lt w w' ∧ ¬ w = win_ord.zero →
    ∃ f b l, acs_decided w f b l

/- Transitive interval ordering (`prop:acs-fate-range`'s "later windows
cover slots of strictly larger number", closed under the window order):
the intervals of any two bounded windows are strictly separated. -/
invariant [win_bounds_ordered]
  ∀ (w w' : window) (f b l f' b' l' : slot),
    win_ord.lt w w' ∧ win_bounds w f b l ∧ win_bounds w' f' b' l' →
    slot_ord.lt l f'

/-! ## Invariants — ACS proposals -/

/- An honest ACS proposal for window `w'` is strictly beyond the
predecessor window's interval (`line:sstar-guard`/`line:sstar-update`
persisted; feeds `[win_separation]` through the median witnesses). -/
invariant [acs_proposal_above_prev]
  ∀ (r : node) (w' : window) (s : slot) (w0 : window) (f0 b0 l0 : slot),
    ¬ is_byz r ∧ acs_proposed w' r s ∧ win_ord.next w0 w' ∧
    win_bounds w0 f0 b0 l0 →
    slot_ord.lt l0 s

/- An honest proposal to `ACS[w']` presupposes having entered the
predecessor window (the `line:ready` activation context). -/
invariant [proposal_prev_entered]
  ∀ (r : node) (w' : window) (s : slot),
    ¬ is_byz r ∧ acs_proposed w' r s →
    ∃ w0, win_ord.next w0 w' ∧ entered r w0

/- Entered windows have (fixed) bounds: window 1 by configuration, later
windows by the ACS decision that gated entry. -/
invariant [entered_has_bounds]
  ∀ (i : node) (w : window),
    ¬ is_byz i ∧ entered i w → ∃ f b l, win_bounds w f b l

/-! ## Invariants — openings -/

/- Every opening is recorded with its window. -/
invariant [opened_backed]
  ∀ (i : node) (s : slot),
    ¬ is_byz i ∧ opened i s → ∃ w, opened_win i s w

/- The recorded window was entered. -/
invariant [opened_win_entered]
  ∀ (i : node) (s : slot) (w : window),
    ¬ is_byz i ∧ opened_win i s w → entered i w

/- The opened slot lies in its recorded window's interval
(`prop:acs-fate-range`, interval form; bounds are unique, so the
∀-formulation is exact). -/
invariant [opened_win_contained]
  ∀ (i : node) (s : slot) (w : window) (f b l : slot),
    ¬ is_byz i ∧ opened_win i s w ∧ win_bounds w f b l →
    slot_ord.le f s ∧ slot_ord.le s l

/- In-order openings (`prop:fate-order` + `lemma:conductor-monotonicity`,
per-validator): below an opened slot, every scheduled slot is opened. -/
invariant [open_local_order]
  ∀ (i : node) (s s' : slot) (w0 : window) (f0 b0 l0 : slot),
    ¬ is_byz i ∧ opened i s ∧
    entered i w0 ∧ win_bounds w0 f0 b0 l0 ∧
    slot_ord.le f0 s' ∧ slot_ord.le s' l0 ∧ slot_ord.lt s' s →
    opened i s'

/- Completions are of opened slots (`mod:orchestrator_2` assumed
behaviour (i), enforced by the guard). -/
invariant [completed_opened]
  ∀ (i : node) (s : slot),
    ¬ is_byz i ∧ completed i s → opened i s

/-! ## Liveness — meta-argument (totality & recovery)

Totality and `(2Wτ)`-recovery are genuinely temporal: the paper proves
them **only for Conductor run within Cadence** (they hinge on slots
actually completing — `lemma:conductor-totality` intro), by an intricate
per-window induction. Following the Chorus doctrine (`docs/ChorusDesign.md` §7),
the temporal glue lives here as named meta-axioms over the composed
system, and the state-level content they need is exactly the invariant
set above.

### Meta-axioms

* **(F-justice)** — the honest actions `acs_propose`, `enter_window`,
  `open_slot`, `complete_slot`'s *upstream* (the glue's finalize chain),
  and `tick`, when continuously enabled, eventually fire. Enabledness is
  monotone for all of them (positive stable guards; `ready_next` is
  monotone because `completed` only grows and the scheduled set grows
  only with entry, which preserves readiness of *past* windows —
  boundaries of later windows lie above, `[win_bounds_ordered]`).
* **(A-acs-termination)** (`mod:acs` ℓ-Termination) — once every honest
  validator has proposed to `ACS[w]`, the `acs_decide w` oracle
  eventually fires (with witnesses supplied by the median lemma,
  `Windows.lean` `lowerMedian_between_correct`).
* **(A-acs-totality)** (`mod:acs` Δ-Totality) — the decision is global
  state here, so its propagation is immediate by encoding; the paper's
  `Δ` materialises in the timing bounds only.
* **(A-sc-totality)**, **(A-sc-termination)** — completions propagate:
  within Cadence, `completed` is Chorus finalization, which is
  `d_tot`-total (`prop:chorus-totality`) and `ℓ_chorus`-terminating.
  These enter through `complete_slot`'s occurrence, not its guard.

### The paper's induction, mirrored

`prop:enters-every-window` (every correct validator enters every window):
induction over windows. In window `w`, either some correct validator
decides `ACS[w+1]` — global here, so all see it — or none does, in which
case every correct validator stays in `w`, eventually opens every slot of
its scheduled prefix (`open_slot` enabled once `tick` passes the starting
times — (F-justice) twice), completes them ((A-sc-termination) via the
glue), becomes ready, proposes ((F-justice) on `acs_propose`), and
(A-acs-termination) decides — then `enter_window` is enabled at every
correct validator and (F-justice) fires it.

`(2Wτ)`-recovery (`prop:window-open-time` → `prop:smooth-windows` →
`prop:first-post-gst-window-time`) additionally tracks *when*: it needs
the four parameter assumptions (`line:assumption-one..four`)

1. `(p−1)τ + Φ_oc + ℓ ≤ Wτ`
2. `(p−1)τ + Φ_oc ≤ (W−1)τ`
3. `Δ < ℓ`
4. `d_tot + ℓ ≤ (p−1)τ`

with `Φ_oc = ℓ_chorus + d_tot` (`prop:conductor-open-to-complete`).
These are arithmetic side conditions on real-time constants that do not
exist at this abstraction; they are recorded here as the assumptions the
meta-argument consumes (plan §3). The quantitative conclusions
(`d_tot`-totality of openings, on-time opening from the second post-GST
window) are theorems *about the timed system*, out of scope for the
untimed model by design. -/

/- The `Enumeration`/`FinEncodable` derivation over the action `Label`
sum must traverse `acs_decide`'s 12-nested parameter sigma, which
exceeds the default instance-search budgets (the Chorus lesson struck
via action *count*; here via parameter *arity*). Disabling the
scaffolding entirely is not an option — the `sat trace` queries below
need the generated `ActionTag_EnumClass` — so raise the budgets
instead. -/
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192

/- Proof reconstruction ON (P8, 2026-07-10). History: tried 2026-07-07
and REVERTED for two reasons, both since resolved. (1) One attempt
diverges under the reconstruction encoding — `trust false` also flips
`embedBool`, changing the SMT query — timing out at both 60 s and 120 s
while the VC stays ✅ via its alternative form; that remains true and is
fine. (2) A Veil reporting issue then failed the otherwise-green build:
the tolerated attempt failure leaked an error-severity message
positioned at `#gen_spec`. Fixed 2026-07-10 — attempt-level diagnostics
in discharger snapshots are demoted to information severity (the VC's
effective status, reported by the results display, is the error channel).
With both resolved, the sweep and the
persisted VC theorems below carry no trusted-SMT step, which upgrades
`Composition.lean`'s theorems (`Conductor ⊨ Orchestrator`, positional
MCP Safety) to kernel-checked (axiom-pinned there). -/
set_option veil.smt.trust false

/- Streaming theorem persistence (pairs with `trust false`; cf. the same
note in `Cadence.lean`). Captured at `#gen_spec`. -/
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

/- The sweep runs at Veil's solver defaults — the `set_option ... in` pair
this command used to carry was inert (dischargers capture solver options
at `#gen_spec`); see the note in `Cadence.lean`. -/
#check_invariants

/- Persist the discharged VCs as environment theorems for the C4
composition layer. With `veil.gen.streamTheorems` above, the retained
witnesses are persisted incrementally — no re-elaboration, so the
solver-option headroom this command used to carry (for the serial
lazy-regen path) is no longer needed (cf. the same note in
`Cadence.lean`). -/
#gen_theorems

/-! ## Reachability sanity checks

Against vacuous safety (`docs/TODO.md` § "Soundness"): the ACS pipeline
is exercisable end-to-end — open and complete a slot of window 1, become
ready, propose, let the oracle decide, and enter window 2. (The steps are
named — an `any 5 actions` trace's transition disjunction exceeds the
trace pipeline's simp budget.) -/

sat trace {
  open_slot
  complete_slot
  acs_propose
  acs_decide
  enter_window
  assert (∃ i w, ¬ w = win_ord.zero ∧ entered i w)
}

sat trace {
  any 2 actions
  assert (∃ i s, opened i s ∧ completed i s)
}

end Conductor
