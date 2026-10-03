# Bounds — the paper's Δ-bounds and the model

*Design notes, not a description of what is proven. This document records
how the paper's concrete finite bounds relate to the model's theorems, why
the two are incomparable rather than ordered by strength, and the routes by
which bounds could be brought into the model — including tooling
constraints observed in practice. The proven liveness state of affairs is
[Liveness.md](Liveness.md); the open-items list is
[TODO.md](TODO.md).*

## 1. What the paper proves, and how the model relates

The paper proves concrete finite bounds end-to-end, parametric in exactly
two assumed primitive bounds:

* **Chorus**: `ℓ`-termination with `ℓ = 5Δ + ℓ_MVBA`
  (Lemma 11 (`lemma:chorus-termination`)), via a deterministic post-GST timeline
  (Proposition 5 (`prop:chorus-finalization-time`), Proposition 4 (`prop:chorus-totality`)), conditional
  on *Δ-synchronized participation*
  (Definition 5 (`def:delta-synchronized-participation`)).
* **Conductor**: totality with `d_tot = Δ` (Lemma 15 (`lemma:conductor-totality`)),
  boundedness `𝓑 = 2W − p` and recovery `𝓡 = 2Wτ`
  (Theorem 2 (`thm:conductor-correctness`)); the composition closes non-circularly
  (Corollary 4 (`cor:chorus-correctness-within-cadence`)).
* **The parametric holes**: `ℓ_MVBA` (Module 3 (`mod:mvba`)) and the ACS's `ℓ`
  (Module 4 (`mod:acs`)) are *assumed module properties*, stated as deterministic
  bounds — an idealisation, since the randomised constructions satisfy
  them only in expectation / with high probability. The first hole is
  closed in this development: the MVBA instantiation of the paper
  repository's internal supplement is modelled
  ([Cadence/Mvba.lean](../Cadence/Mvba.lean)), `ℓ_MVBA` is the field `ℓ`
  of `MVBATemporal` ([Cadence/Interfaces.lean](../Cadence/Interfaces.lean)),
  and the instance `Mvba.mvbaTemporal`
  ([Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)) proves the
  Termination it bounds — Supplement, Theorem 2 (`thm:termination`), `O(fΔ)` — over
  timed runs of the untimed model (§6.2).

The model relates to these in three distinct ways:

1. **Bound-free paper theorems** (agreement, slot safety, integrity, …)
   appear as the *same* theorems in the model.
2. **Timed-premise theorems** appear with the premise transported to its
   state-level consequence (proposal inclusion's `deadline − Δ ≥ GST`
   becomes the hypothesis `all_honest_recorded`; the liveness theorems'
   *saturation* hypotheses are the state consequences of what fairness
   delivers).
3. **The bounded statements themselves** are not model theorems at any
   abstraction level — they are fields of the full module contracts,
   stated over timed runs, and for the two implementations the fields of
   the `…Temporal` classes ((A-sc-termination), (A-acs-termination),
   (A-acs-totality), (A-orch-totality), (A-orch-boundedness),
   (A-orch-recovery); [Architecture.md](Architecture.md) §4 item 4,
   [Cadence/Interfaces.lean](../Cadence/Interfaces.lean),
   `OrchestratorTemporal`, `SlotConsensusTemporal`). What the
   model proves instead is the **bound-erased skeleton of their paper
   proofs**: each timeline milestone's state content is a theorem
   (saturation ⇒ dichotomy; buildability; certificate formation; the
   commit-round chain), and the Δ-arithmetic that orders the milestones
   in the paper is replaced by the named temporal assumptions that glue
   them in the model. Even inside the rows, the maximal state-shaped
   residue is extracted as a theorem (quiescence ↔ phase confinement;
   boundedness ↔ the interval-inclusion invariant, with the number
   `2W − p` a meta corollary).

## 2. Wording discipline: unbounded is not weaker

The model's liveness content and the paper's bounded theorems are
**incomparable, not ordered**:

* The paper's bounds assume *strong partial synchrony* — GST plus a known
  Δ, with every message (pre-GST sends included) delivered eventually — a
  strong assumption.
* The model's unbounded claims need only *eventual delivery and fair
  scheduling*: strictly weaker premises (they are implied by strong
  partial synchrony), for a weaker conclusion (eventually, not by a
  deadline).

Under strong partial synchrony the bounded claims imply the eventual
ones; under mere eventual delivery only the model's claims hold. Both
statements carry independent value, and prose comparing them should never
call the model's claims "weaker" without naming the premise trade.

There is also a meta-theoretic asymmetry worth recording: bounded
liveness in a Zeno-guarded explicit-time encoding is a **safety**
property, and its temporal residue — time diverges — is discharged by
fair scheduling of protocol and clock actions plus tick-enabledness, an
*inductive* argument. Genuine unbounded eventuallys are where the
coinductive reasoning over temporal fixpoints lives — the content the
liveness-to-safety reduction internalises. The two routes therefore serve
the two assumption regimes and complement rather than compete: an
explicit clock targets the strong-partial-synchrony claims, L2S the
assumption-minimal ones (and the (A-mvba)-style eventuallys for which no
deterministic bound exists at all).

## 3. Routes to bounds in the model

Three options, in ascending order of invasiveness; the first is the
preferred entry point, the last is taken only if the benefit is clear.

**(a) An add-on schedule theorem (no model change).** Mechanise
Lemma 11 (`lemma:chorus-termination`)'s *proof arithmetic* as a standalone plain-Lean
theorem over an abstract ordered time (an order plus an abstract
`+Δ`-successor; no `Real`, no Archimedean axiom — finite schedules need
neither): parameterise by one named per-seam bound assumption for each
temporal step of the chain ("this seam completes within Δ after GST",
"(A-mvba) within `ℓ_MVBA`"), take the chain's state theorems as the step
justifications, and conclude finalization by
`max(t, GST) + 5Δ + ℓ_MVBA`. This is the same treatment the unbounded
argument received — state content proven, temporal steps named — with the
schedule *composition* additionally kernel-checked. The gain is real if
modest: the paper's timeline arithmetic is exactly the kind of detail
that drifts (the `d_tot` bound changed `2Δ → Δ` between paper revisions),
and the theorem pins it. The per-seam `≤ Δ` facts remain assumptions —
they are the strong-partial-synchrony content itself.

**(b) A ghost clock in the model (Zeno-guard).** Add a monotone `now`
whose `tick` is guarded so that time cannot pass a deadline while an
obligated step is pending; bounded claims become sweep-shaped safety
invariants, and the temporal residue consolidates to fairness plus
non-Zenoness, whose state-level half (tick-enabledness in every reachable
state) is dischargeable like the existing enabledness content. Design
costs, all named: keep the time theory order-only (uninterpreted
monotone `laterΔ`, deadlines as ghost elements — mixed quantifiers with
arithmetic is where e-matching pain returns); route deadline bookkeeping
through ghost obligation relations so `tick`'s universal guard does not
read network relations negatively (the (M-frame) contract,
[ChorusDesign.md](ChorusDesign.md) §3.1.1); and guard vacuity — in
this encoding the bounded invariants are safe *by construction of the
guard*, so the theorems are the tick-enabledness results and the
non-vacuity witnesses that `now` exceeds the interesting thresholds.
Estimated bill at Chorus scale: a tick action, deadline ghosts on ~10
actions, 10–15 timing invariants — roughly +600–800 VCs, inside the
demonstrated envelope. If taken, stage it Conductor-first: Conductor
already carries an abstract monotone `now` with a clock-guarded `open`,
and the paper's own decomposition puts the timing in the orchestrator.

**(c) A full timed refactor or a timed overlay model.** A second, timed
model with a simulation to the untimed one re-raises the embedding cost
for little audit gain; a full refactor of Chorus is justified only if the
model would become *simpler* — which nothing currently suggests. Both
deferred absent a clear benefit.

## 4. Tooling constraints (recorded from practice)

Observed while building a Veil model of a different, inherently timed
protocol. They are recorded here so that they inform the decision above;
tool-side work belongs in the Veil fork, not in this repository.

* Veil has no support for `Real` time, although the SMT solvers and Lean
  itself would allow it. Workable substitute: time as an abstract ordered
  structure (there, an ordered Archimedean field; for the uses above, an
  order with an abstract `+Δ` suffices — Archimedean-ness is only ever
  needed for divergence, which stays meta regardless).
* Veil does not handle Mathlib's universe polymorphism, which blocks
  pulling in Mathlib's ordered-field theory directly. Upstream Veil work
  may address this; maturity and timeline unclear.
* A viable escape hatch exists: disable SMT and prove all VCs in plain
  Lean. For that (much simpler) protocol this was efficient — most VCs
  were one-liners. It is **not** an attractive route for Chorus, whose
  combinatorial/discrete core (quorum reasoning at the scale of
  [Architecture.md](Architecture.md) §2) is exactly where SMT earns its
  keep.

None of these constraints bites route (a): the add-on schedule theorem is
plain Lean over an abstract order, outside the Veil pipeline entirely.

## 5. Recorded decision

Beyond the MVBA's `ℓ_MVBA` (§6.2, proven), bounds are out of scope
([Architecture.md](Architecture.md) §4 item 4) until timing claims become a
priority; where they rank against the two items ahead of them in
[TODO.md](TODO.md) § Soundness is a call to make deliberately. When they do
go ahead: route (a) first — cheap, no model change, pins the schedule
arithmetic; route (b) Conductor-first if in-model timing is wanted, with
the three design costs above addressed up front; route (c) only against
demonstrated benefit. Ordering relative to the L2S extension (the fork's
`lars/liveness` branch) is decided then — the two are complementary, and
the ghost clock would incidentally hand L2S its simplest ω-target
(`infinitely_often tick`).

## 6. Route (a): the worked plan

Recorded so a future session can pick this up without re-deriving the
design. Priority context: this ranks *behind* primitive instantiation and
the (M-frame) checker ([TODO.md](TODO.md) § Soundness) on
auditor-confidence per effort, and *ahead* of L2S on near-term
value-per-effort — it is executable today, entirely in plain Lean, with
none of §4's tooling constraints in play.

**Depth decision.** Prove the theorem over **real timed runs of the
generated transition system**, not over abstract milestone propositions.
A run is `σ : ℕ → State` stepping through the actual Chorus transitions
with a monotone clock `c : ℕ → T`, where `T` carries a linear order plus
two abstract inflationary monotone shifts (`+Δ`, `+ℓ_MVBA`) — no `Real`,
no Archimedean axiom, `max` from the order. Every run point is reachable,
so the chain theorems of [Liveness.md](Liveness.md) §1 apply at every
milestone state. The abstract-propositions variant is the fallback only:
it checks arithmetic an auditor can check by eye.

**Hypotheses.** One named per-seam bound assumption per temporal step of
the chain ([ChorusDesign.md](ChorusDesign.md) §7): "this seam
completes within Δ after GST" for the (F-justice) seams, `ℓ_MVBA` for the
oracle seam. These hypotheses *are* the strong-partial-synchrony content;
the design rule is that they stay minimal and checkable against the
paper's premises — a hypothesis that smuggles a conclusion voids the
exercise. Workshop the exact statements in this section before writing
Lean.

**Target statement** (Chorus leg): for every timed run satisfying the
per-seam assumptions in which all correct validators participate by `t`,
every correct validator finalizes by `max(t, GST) + 5Δ + ℓ_MVBA` — the
statement shape of Lemma 11 (`lemma:chorus-termination`), with
Proposition 5 (`prop:chorus-finalization-time`)'s milestone table (`M+2Δ`, `M+3Δ`,
`T−Δ`, `T`) as the internal schedule.

**Staging** (reassess after step 2; each step is one focused session,
give or take):

1. Scaffolding: timed runs over the generated transition system, the
   time theory, the per-seam assumption vocabulary.
2. Milestones `M+2Δ` and `M+3Δ` — mostly plugging the proven theorems
   (saturation, `build_totality_of_reachable`, the definitional
   aggregation witness). This validates the scaffolding cheaply.
3. The MVBA tail, the commit round, and the two-case termination lemma;
   axiom pins at the standard trio; docs. Watch for per-validator
   "holds-by-time" content that may need one or two new invariants
   (a model change and cold re-solve — a known ~20-minute event).
4. Conductor: `d_tot = Δ` totality, the window induction, `2W − p`
   boundedness, `2Wτ` recovery.
5. The composition: Corollary 4 (`cor:chorus-correctness-within-cadence`) and the
   alternating-window non-circularity — the subtlest statement work and
   the highest-value single piece.

### 6.1 The MVBA leg

*Complete: §6.2 is the design as carried out, and §6.2.8 the record of each
step. This subsection is the plan it started from, kept for the argument.*

Step 3 above treats `ℓ_MVBA` as a **per-seam hypothesis** — "the oracle seam
completes within `ℓ_MVBA`". The MVBA's liveness theorem
(`Mvba.termination`, [Liveness.md](Liveness.md) §2.1) makes a second leg
available: *prove* `ℓ_MVBA` rather than assume it.

**Why it is tractable.** The untimed theorem was built so that this would be
the only remaining step. Every one of its five premises is a predicate on a
run, so a timed layer discharges them as ordinary Lean theorems over timed
runs of the same generated transition system — **no model change**, exactly
the depth decision of §6. Two of the five are immediate under any reasonable
timing model (the callers' premises are hypotheses either way), one is fair
scheduling, and the work is entirely in (A-viewsync)'s two clauses.

**What it needs that the Chorus leg does not.** The Chorus leg's time theory
is a linear order with two abstract inflationary shifts, because its schedule
is a fixed milestone table. The MVBA's is not fixed: the argument is that
*timeouts grow* until one view's budget exceeds the chain's latency, so the
time theory needs a **sequence** `Δ_v` unbounded relative to a fixed bound,
not two constants. That is the one genuinely new piece of arithmetic, and it
should be workshopped before any Lean, exactly as §6 says of the per-seam
statements. Do not assume this leg is cheaper than the Chorus leg because the
skeleton exists; it probably is not.

**What it buys, and why it may still rank first.** It is the only piece of
the bounds work that *removes an assumption* rather than attaching a bound to
one. (A-viewsync) is the strongest premise of the liveness result and the
only one not derivable in an untimed model ([MvbaPlan.md](MvbaPlan.md)
§3.7); with a clock both of its clauses become theorems — bounded post-GST
delivery gives the decision chain a finite latency, timeout growth makes some
view's budget exceed it, and (A-leader-rotation) supplies the honest leader.
That in turn is what `MVBATemporal.termination` needs, and it is the formal
version of the trust-base move [Liveness.md](Liveness.md) §2.1 describes informally.

**It does not subsume the premise witness.** [TODO.md](TODO.md) § Liveness
asks for a run witnessing that `Mvba.termination`'s five premises are jointly
satisfiable. `MVBATemporal.admissible_exists` is a run in which nobody
proposes (§6.2.7), so that item stays open.

This leg can run **in parallel with** the Chorus run-level liveness leg;
the rules that keep the two from colliding — and the one piece of design
they share, the projection from a composed run to an MVBA run — are
[Liveness.md](Liveness.md) §4.1.

**Staging**, in the shape of §6's:

1. Timed runs over `Mvba`'s generated transition system, and the time
   theory with a growing timeout schedule. Reuses §6 step 1's scaffolding if
   the Chorus leg went first.
2. The chain latency bound: the links of [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) from the
   leader's `Pre-Prepare` to the commit certificate, each with a Δ attached.
   Mostly plugging in proven theorems, and the cheap validation of the
   scaffolding.
3. The entry bound — every correct validator enters the good view within Δ
   of the first — which is the quantitative refinement of
   `eventually_entered_good`. The untimed argument's structure carries over
   (the climb, the common view, the overshoot bound); the bounds are new.
4. Discharge both (A-viewsync) clauses, then `MVBATemporal.termination`;
   axiom pins, docs, and the [Cadence.lean](../Cadence.lean) row moves from conditional to
   a discharged instance.


**Placement.** A sibling of the end-theorem files — e.g. a new
`Cadence/Chorus/Schedule.lean` at the `Compose`/`Pigeonhole`/`Counting`
layer: plain Lean, kernel-only, in-file `#guard_msgs` pins, a row and pin
at the audit root. On completion, the corresponding fields leave the
`…Temporal` classes (`SlotConsensusTemporal`,
`OrchestratorTemporal`) and are proven in the `…_of_temporal`
definitions — the contract fields in
[Cadence/Interfaces.lean](../Cadence/Interfaces.lean) themselves do not
change, which is the point of stating them there.

**Effort and risk.** Chorus-only (steps 1–3) ≈ 2–4 sessions; the full
bounded story ≈ 5–8. The dominant risk is statement-design churn, not
proof difficulty — the state-level content is already proven. Expected
finding class: a misstated or missing premise in one of the paper's
bounded lemmas (the timeline arithmetic has drifted once already,
`d_tot`: `2Δ → Δ`); protocol-level findings are unlikely, since the state
content is verified. The timed-run scaffolding is reusable by a later
L2S bring-up — nothing here is throwaway.

### 6.2 The MVBA leg, as designed and carried out

The per-seam statements §6 asked to be settled before any Lean. Everything
below is a *design*, not a result: what is proven is what
[Cadence/Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean) says is proven,
and its `#guard_msgs` pins, not this section. The section exists so that the
decisions and the two findings are not re-derived, and so that a reader can
check the premises against the supplement without reading Lean.

**Decisions in one place.**

* The clock belongs to the run: timed runs are labelled runs of the
  generated `Mvba` transition system with a clock sequence, and the
  contract is instantiated at `mvbaSafety th` itself (§6.2.1). No model change; nothing under `Mvba/Proofs/` re-solves.
* Time is a linearly ordered additive commutative monoid with `max`
  (§6.2.2). The theorem needs no Archimedean axiom; the non-vacuity
  witness `admissible_exists` needs an unbounded clock and gets it from
  Mathlib's `Archimedean` and `0 < Δ`.
* The timeout schedule is a function of the view, **bounded above** and
  **eventually above the chain latency** (§6.2.3). The paper's fixed known
  timeout is the special case; *unbounded* backoff is incompatible with the
  contract's fixed `ℓ`, which is the first finding.
* Fairness is bounded weak fairness after GST over plain enabledness,
  with the window measured from `max(now, gst)` so that a clock jump over a
  pending obligation's deadline is inadmissible (§6.2.4). A local step is
  held to `δ`. A step that consumes another party's message is held to what
  the supplement's network guarantees (since step 5b, 2026-09-29): `Δ` for
  messages sent at or after GST by correct validators and retained, `Δ + ρ`
  for the retransmitted classes (`ρ` is the supplement's retransmission
  interval `ρ_mvba`, the schedule's field `ρ`). While some fair labels stayed enabled
  after firing, plain enabledness made every admissible model
  unsatisfiable once a proposal existed. That was the second finding
  (§6.2.4), answered first in the premises (R3: fairness over
  state-changing steps) and since R4–R6 in the model: every fair action
  fires once, and the premises read plainly again (§6.4.7).
* (A-viewsync) is not assumed anywhere. Its two clauses are derived as a
  corollary of the timed premises; the bound itself is proven directly by
  a timed re-run of the chain and does **not** consume `Mvba.termination`
  (§6.2.7 says why it cannot).

#### 6.2.1 The clock belongs to the run

*Outcome first: `TimedRun` carries its own clock (route 2 below); the
product-state lift the section goes on to weigh no longer exists. The rest
of the section is the decision record, ending in the outcome.*

`MVBATemporal.clock : state → time`, and `TimedRun … clock` reads the clock
off each state; that is right for the Conductor, whose `now` is a state
field, and it was written that way for all three modules. `Mvba.State` has
no clock, and §6's "monotone clock `c : ℕ → T`" alongside the state is a
different object. Three ways to reconcile them were weighed:

1. **A ghost `now` in [Mvba.lean](../Cadence/Mvba.lean)** (§3(b)'s device with no guards). Changes
   every VC statement — a cold re-solve of the family — moves the audit pin,
   and adds a 26th label that the read-only label classification of
   [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) would silently file under `JusticeLabel`, so
   `FJustice` would demand weak fairness of `tick`. Out, on
   [Liveness.md](Liveness.md) §4.1's rules alone.
2. **Change `TimedRun` to carry its own clock sequence.** Arguably the right
   design for untimed models, but an edit to [Interfaces.lean](../Cadence/Interfaces.lean) — a joint
   decision under §4.1, and a Chorus-family rebuild.
3. **Pair the state with the clock.** `MVBASafety.timed S : MVBASafety … (state × time) byz`
   is a generic lift — every field is `S`'s on the first component, and a
   transition is an `S`-transition whose clock does not decrease — and
   `MVBATemporal` is instantiated at `(mvbaSafety th).timed time`. Nothing
   is restated: the lifted fragment *is* `mvbaSafety th` on the first
   component, definitionally.

Route 3 is taken. What it costs is a **seam**, stated so it is not
mistaken for a gap: the full `MVBA` instance this leg produces is at the
lifted fragment, while Chorus consumes `mvbaSafety th` at `Mvba.State`, so
`mvba_of_temporal` is not the join used and [System.lean](../Cadence/System.lean) does not
automatically inherit the timed instance. Closing it is one of two edits —
instantiate Chorus at the lifted fragment in [System.lean](../Cadence/System.lean) (the composed
system's MVBA sub-state then carries the clock the composition's own timing
needs anyway), or route 2 — and both are decisions to take with the Chorus
leg when its composition step (§6 step 5) is designed. The labelled timed
run `Cadence.TLRun` is the load-bearing object; the product is a thin
bridge, and if route 2 is taken later the bridge is deleted and the
premises are restated on `TLRun` unchanged.

The Chorus leg's projection from a composed run to an MVBA run
([Liveness.md](Liveness.md) §4.1) lifts to `TLRun` by carrying the
clock along the projected indices; `TLRun.toLRun` is the forgetful map, so
the projection is theirs to define and this leg's timed form is its
pullback, not a second definition.

**The seam, as a proposal to the Chorus leg** (step 4, 2026-09-28; the
decision is open). The instance now exists: `Mvba.mvbaTemporal` at
`(mvbaSafety th).timed time`, and the full `Mvba.mvbaTimed`. Chorus holds
the MVBA state as an abstract sort `mstate` and [System.lean](../Cadence/System.lean) fills it with
`Mvba.State`. There are two ways to hand the composed system the timed
instance:

* **(a) Plug the lifted fragment in at [System.lean](../Cadence/System.lean).** Fill `mstate` with
  `Mvba.State × time` and Chorus's constraint with `(mvbaSafety thM).timed
  time`. No class changes and nothing in Chorus re-solves: Chorus is generic
  in the class, and the lift is the same fragment on the first component, so
  `system_positional_log_safety` goes through unchanged. The cost is on the
  liveness side. The MVBA's clock is then a state component that only the
  MVBA's own steps advance (`mvba_step`, `mvba_propose` and the decision
  handlers choose it, subject only to monotonicity). A composed timed run
  would have to require, as a run predicate, that each such step stamps the
  composed run's current time, so that the MVBA's `TimedRun` reads the real
  clock. The projection would carry that requirement.
* **(b) Route 2: `TimedRun` carries its own clock sequence.** Drop
  `clock : state → time` from the temporal classes. The Conductor, whose
  state has `now`, then states `clk n = now (at' n)` inside its
  `Admissible`. `MVBATemporal` is instantiated at `mvbaSafety th` itself,
  the existing `mvba_of_temporal` gives the full `MVBA`, and [System.lean](../Cadence/System.lean)
  inherits it with no lift. The Chorus leg's projection takes the composed
  run's clock at the projected indices, with no ghost state and no stamping
  condition. On this leg's side, `MVBASafety.timed` and `TLRun.toTimedRun`
  are deleted and `Admissible` keeps its `TLRun` form, as said above. The
  cost is one [Interfaces.lean](../Cadence/Interfaces.lean) edit, which is a warm Chorus-family rebuild,
  and a joint decision.

**Recommendation: (b), bundled with the next [Interfaces.lean](../Cadence/Interfaces.lean) edit** (the
one that also carries `propose_valid`'s move to the rely form,
[CompositionContracts.md](CompositionContracts.md) §2), and taken when
the Chorus leg designs its composition step (§6 step 5). (a) works too, but
it puts a clock into the state that nothing but the MVBA steps maintain, and
that is the device route 1 was rejected for, moved one level up.

**Outcome (2026-09-29): (b), done before Chorus stage 4 started**, in one
[Interfaces.lean](../Cadence/Interfaces.lean) edit together with `propose_valid`'s move to the rely
form. `TimedRun` carries `clk : Nat → time`, the temporal classes have no
`clock` field, and `OrchestratorTemporal.clock_agrees` ties a Conductor run's
clock to its `now`. `Mvba.mvbaTemporal` is at `mvbaSafety th`, and the full
class is `Mvba.mvbaFull := mvba_of_temporal th (mvbaTemporal …)`, whose
fragment is by `rfl` the one [System.lean](../Cadence/System.lean) plugs into Chorus. The seam is
gone. `MVBASafety.timed` and the product state are deleted, and
`TLRun.toTimedRun` is the label-forgetting map. The witness run's clock is
`n • Δ`, since a run no longer has to start at a state's clock value, so the
negative-initial-clock remark of the step-4 reassessment no longer applies.

#### 6.2.2 The time theory

`time` is a **linearly ordered additive commutative monoid** — Mathlib's
`[LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]` — with a
bridge to Veil's `TotalOrder`, which is what `MVBATemporal` quantifies
over. `ℕ` and `ℝ≥0` are instances; nothing is a field, and no division
occurs. §3(a)'s "two abstract inflationary shifts" would not do: `ℓ` is a
sum of about ten terms with natural-number multiples (`n • C`) and a
`max`, and the bound's proof rearranges such sums, which an ordered monoid
does and two abstract successors do not. This is outside Veil's pipeline,
so §4's constraint on Mathlib's universe polymorphism does not apply.
The monoid must also be **cancellative** (`IsOrderedCancelAddMonoid`); step
2 found that, and the reassessment in §6.2.8 gives the `ℕ∞` counterexample.

Two remarks on what the theory does **not** assume. The **termination
bound needs no Archimedean axiom** — every quantity in it is a finite sum
of the constants. `admissible_exists` does: a `TimedRun` is unbounded by
definition (`clock_unbounded`), so exhibiting one needs an unbounded
monotone sequence in `time` from the initial clock `c`. `Archimedean time`
with `0 < Δ` gives `c`, then `max c ((n + 1) • Δ)`. It does not give
`n ↦ c + n • Δ`, which was the first plan: see §6.2.8's step-4
reassessment. That the witness, not the theorem, carries the
Archimedean assumption is worth keeping visible: it is the one place §3(a)'s
"finite schedules need neither" was too optimistic, and the cause is the
contract's non-Zeno field, not the schedule.

#### 6.2.3 The schedule, and the first finding

The supplement fixes the view timeout (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Views, leaders, and timing parameters"): *"The
view timeout is the fixed, known value `T := Δ_R + 4Δ + max{Δ, Δ_sync}`"*,
and the termination setting says the view timeout is the fixed `T`. The
model's schedule is the supplement's fixed `T` plus a harmless
generalisation: `τ` constant and `v_L = zero` is the paper's case, and
(S-cap)/(S-ramp) below also describe capped backoff should an
implementation want it.

The model's schedule is `τ : view → time`, with three hypotheses:

* **(S-cap)** `∀ v, τ v ≤ τ_max`;
* **(S-ramp)** `∃ v_L, ∀ v, v_L ≤ v → L_cert < τ v`, where `L_cert` is the
  chain's latency bound of §6.2.6;
* **(S-nonneg)** every constant is `≥ 0` and `0 < Δ`.

The paper's fixed known timeout is `v_L = zero` and `τ` constant. Backoff
*up to a cap* is a finite ramp: (S-ramp) holds from the first view whose
budget clears `L_cert`, and the views below it cost a constant that `ℓ`
absorbs.

**Finding 1 — unbounded backoff has no fixed `ℓ`.** `MVBATemporal.ℓ` is a
single element of `time`, and `termination` promises every decision by
`max(t, gst) + ℓ` in *every* admissible run. Under backoff without a cap,
consider runs whose proposals happen ever earlier before `gst`: pre-GST
asynchrony can burn arbitrarily many views, so the view current at `gst`
— and with it the budget `τ` of the next view to be burnt — is unbounded
across runs, and no `ℓ` covers them all. So an `O(fΔ)` theorem is a
fixed-timeout (or capped-backoff) result, and an implementation with
exponential backoff satisfies it only if the backoff is capped at `O(Δ)`.
§6.1's "a sequence `Δ_v` unbounded relative to a fixed bound" was
therefore the wrong requirement: the sequence must be *eventually above*
`L_cert` and *bounded*, which is what (S-ramp) and (S-cap) say. The
supplement's earlier backoff remark, which this finding concerned, and its
removal are in [History.md](History.md) § "Three notes moved out of the
living documents (R21)". One residue remains in the paper: the Supplement, Section
10.1 (`sec:timing-constants`) stub still lists "the MVBA view timeout and
its backoff policy" (P8, [PaperAlignment.md](PaperAlignment.md) §6).

#### 6.2.4 The per-seam statements: what an admissible run satisfies

`Admissible r` for a `TimedRun` over the lifted state says: **there is a
labelling of `r`** (a `TLRun` whose states and clocks are `r`'s) satisfying
the four clauses below. The existential is what a run's labels are — the
witness of how it was scheduled — and `TimedRun` has none.

Throughout, `ref N := max (clk N) gst` is the reference time of index `N`,
and "`P` within `D` of `N`" means `∃ n ≥ N, P n ∧ clk (n+1) ≤ ref N + D` —
the **post-state** of the firing step is inside the window. That choice is
the Zeno-guard: if a label is pending at `N` and the clock jumps past
`ref N + D` at the next step, no such `n` exists and the run is
inadmissible, which is exactly the paper's "nothing happens in `(a, b)`"
reading of a jump. Measuring from `max(clk N, gst)` rather than `clk N`
makes the clause bite across GST too — an obligation pending at `gst` is
due by `gst + D` — and it is what lets every milestone below be counted
from `max(t, gst)`.

| Clause | Names | Says | Paper |
|---|---|---|---|
| (F-byz) | — | nothing of `ByzLabel` | — |
| (Δ-justice) | `BoundedJustice` | six clauses, each of the form: if `l` is **enabled** at every index `n ≥ N` with `clk n ≤ ref N + D` (and the clause's side condition holds there), then `l` fires within `D` of `N`. A local step at `D = δ`; a network step at `D = Δ` when its messages were sent at or after GST by correct validators and retained, or at `D = Δ + ρ` when they are retransmitted (tables below) | the termination setting before Supplement, Lemma 13 (`lem:decision-propagation`) (delivery within `Δ` of messages sent at or after GST; retransmission every `ρ`), Supplement, Section 10.3 (`sec:reliable-delivery`) (one-view retention), Supplement, Lemma 14 (`lem:view-sync`), Supplement, Lemma 15 (`lem:convergence`), Supplement, Lemma 13 (`lem:decision-propagation`); local computation within `δ` (the paper: instantaneous, `δ = 0`) |
| (T-timer) | `TimerPunctual` | for honest `i`: (T1) `expire_timer i v` fires at `n` only if `clk m + τ v ≤ clk n` for some `m ≤ n` with `entered i v` at `m`; (T2) if `entered i v` at `m`, then `timer_expired i v` at some `n ≥ m` with `clk n ≤ clk m + τ v` | the local view timer, restarted on entry, expiring after exactly `τ v` |
| (Δ-avail) | `AvailWithin` | for honest `i`: `accepted i v e` at `m` ⇒ `avail_ready i e` within `Δ_sync` of `m` | Supplement, Lemma 5 (`lem:avail-progress`)'s `Δ_sync` |

`hop`, the per-label kind, is a classification of the fifteen
`JusticeLabel`s by what the guard consumes:

| network (reads another party's message or certificate) | `δ` (local) |
|---|---|
| `handle_preprepare_first`, `handle_preprepare` (the leader's `Pre-Prepare`) | `leader_propose_first`, `leader_repropose`, `leader_propose_fresh` (upon entering the view; `Recover` is the identity here) |
| `form_own_commitqc`, `form_own_tc_lock`, `form_own_tc_nolock` (a quorum of `Commit`s or timeouts the validator received itself; since R4, §6.4.7) | `send_commit`, `timeout_qc`, `timeout_noqc` (own state and a certificate already counted) |
| `adopt_prepqc` (a quorum of `Prepare`s the validator received itself; since R3, (N4) below) | |
| `sync_view`, `sync_view_adopt` (a timeout certificate) | |
| `decide` (a commit certificate; since step 5b, (N3) below) | |

With `δ = 0` the good view's latency is the paper's constant (§6.2.6),
which is the check that the classification is the paper's and not a
convenience.

**The network clauses** (step 5b, 2026-09-29; the finding C16 in
[History.md](History.md) § "The supplement at `eb1bb51`, reviewed against the pin `026dc8b`"). A network label's bound depends on its
messages' history, as the supplement's network at the paper target does. The
model's network relations hold from a message's first delivery to a
correct validator, so "sent at" is the first index at which the relation
holds.

| clause | owed within | when | the supplement |
|---|---|---|---|
| `first` | `Δ` | the messages are from correct senders (a correct leader; a quorum of correct validators), were first sent at or after GST (`SinceGst`, **N1**), and were retained by the receiver, which had reached the message's view or the one before (`RetainedBy`, **N2**); while every correct validator takes part. That the receiver has not moved past the view (**N2**, lower views discarded) is the receiving step's own `in_view` guard: since R4 every network label is one validator's step, so the clause names no separate receiver | delivery within `Δ` of messages sent at or after GST between correct validators; one-view retention; lower views discarded |
| `forwarded` | `Δ` | a timeout certificate forwarded, at or after GST, by the first correct validator to enter the view it justifies | Supplement, Algorithm 1, line 98 (`line:mvba:sv-forward`), Supplement, Lemma 14 (`lem:view-sync`)(b) |
| `timeouts` | `Δ + ρ` | a correct quorum's timeouts, whenever sent, while their senders are still in the view, formed into a certificate by a correct validator in the view | the `Timeout` retransmission, Supplement, Lemma 15 (`lem:convergence`) ("Reaching `V`") |
| `certificates` | `Δ + ρ` | a timeout certificate, whenever formed, while every correct validator takes part | Supplement, Algorithm 1, line 40 (`line:mvba:viewtc-retx`) |
| `decisions` | `Δ + ρ` | a commit certificate some correct validator has decided on (**N3**) | the composing layer's delivery, Supplement, Lemma 13 (`lem:decision-propagation`) |

*Since R8 (§6.4.2, C15) the last row is the caller's, not the MVBA's:
`decide` on a transferred certificate is the contract's input `accept`, so
the row left `BoundedJustice` for a clause of its own, `Mvba.Relayed`,
verbatim, and `decide` left the hop table and `Delivers`. Inside Cadence
Chorus's handoff row derives it (`Chorus.relayed_of_timedJustice`).*

Against the pin `026dc8b` the clause was one line: every network label
within `Δ` of `max(clk N, gst)`, regardless of its messages' history. That
held a correct validator to consuming within `Δ` a message sent before GST
(which the supplement may lose), a message two views ahead (which it may
discard), a certificate that has to travel (which costs `ρ` more), a
Byzantine leader's `Pre-Prepare` and Byzantine votes (which reach whom the
adversary chooses), and an assembly in a view everyone has left. A
supplement run of any of these kinds was not admissible, so the timed
claim said nothing about it. None was a misreading of the pinned text,
which did not yet state its network.

**Closed in R3: (N4), prepare certificates do not travel.** Until R3
`adopt_prepqc` was a local step once `msg_prepqc v e` held, a certificate
formed anywhere. In the supplement a validator holds a prepare certificate
only if it received a quorum of prepares itself; nobody forwards one. So a
supplement run in which one correct validator forms a view's prepare
certificate and another, which accepted the same proposal, never does
(Byzantine votes sent to some, or prepares lost before GST) was not
admissible: the timed claim held that second validator to adopting within
`δ`. Since R3 the model does what the supplement does
([Mvba.lean](../Cadence/Mvba.lean), `adopt_prepqc`, the supplement's
`TryFormPrepQC` at the paper target):

* the step takes the supermajority `q` of `Prepare`s as a parameter, as
  `form_prepqc v e q` does, and requires each member's `Prepare` on
  `(v, e)`, in place of `msg_prepqc v e`;
* it records the certificate it formed (`msg_prepqc v e`), since from then
  on the certificate exists and the validator's timeouts carry it;
* it is a network hop with a first-delivery clause — a correct quorum's
  `Prepare`s sent at or after GST and retained by the forming validator —
  and nothing is owed for a quorum with Byzantine members, whose votes
  reach whom the adversary chooses.

`form_prepqc` stays as the anonymous assembly, so the adversary's power is
unchanged. *(Superseded in R4, §6.4.7: the four anonymous assemblies carry
no fairness at all, `AssemblyLabel`; the rest of this paragraph is the R3
record.)* Its weak fairness assumes nothing of the supplement: a firing
move-enables no fair label by itself, since no honest guard reads
`msg_prepqc` and the one assembly that does, `form_tc_lock`, also needs a
timeout carrying the certificate, which the run has only if its sender
held it or, for the adversary, could form it from the broadcast prepares
anyway. The Mvba family was re-solved cold; the one new cell the solver
would have to search, `adopt_prepqc × prepqc_blocks_lower_commits`, is
manual, as its `form_prepqc` twin is. `#veil_status Mvba` is unchanged,
since no action or property was added. The good view is unaffected: there
every correct validator receives the whole correct quorum's prepares within
the same `Δ`, and the chain gets one milestone shorter (§6.2.6).

**Move-enabledness, and the second finding.** *(History, superseded by R6
(§6.4.7): the finding is resolved in the model, and every fairness premise
is stated over plain `Enabled` again. The two paragraphs below are the R3
record; "Resolved in the model" after them is the current state.)*
[Fairness.lean](../Cadence/Fairness.lean)'s `Enabled`
holds whenever *some* transition under the label exists — a stutter
included. Two of the model's assembly labels differ only in the quorum
parameter `q`, and the actions are idempotent: once `msg_prepqc v e` is
set, `form_prepqc v e q'` is still enabled for every other supermajority
`q'`, forever. Weak fairness per label then demands infinitely many
firings for one effect, and if `nodeset` has infinitely many
supermajorities no run satisfies it. In the *timed* form this is fatal
outright: infinitely many firings within `Δ`. So (Δ-justice) is stated for
`EnabledMove` — a transition under `l` to a **different** state, TLA+'s
`⟨A⟩_v` — under which one firing discharges every `q'` at once. *(Since R4,
§6.4.7, no fair label of this model has that property any more: the
anonymous assemblies are unfair, and each correct validator's step is
guarded on the record it sets, which `Mvba.enabledMove_of_enabled` checks.)* Veil's
actions are deterministic in their parameters, so a firing of a
move-enabled label is a move; the proofs pay one side condition per link
(the guard's negative flag becomes the effect's positive one, so the
states differ).

**Resolved in R3 for the untimed leg too.** The finding applied to the
untimed claims as well: `FJustice` was stated with `Enabled`, so the premise
sets of `Mvba.termination` and `Chorus.termination` were unsatisfiable at
any instance with infinitely many supermajorities. Since R3 every fairness
notion in [Fairness.lean](../Cadence/Fairness.lean) — `WeaklyFair`,
`WeaklyFairFamily`, `StronglyFair` — is stated over `EnabledMove`, which
moved there from [Timed.lean](../Cadence/Timed.lean) so that both sides use
one notion, and both `FJustice`s, Chorus's proposal family included, are
restated over it. In plain words: a correct validator's action is owed a
step only while it can take one that changes the state. The premise can
therefore hold at every quorum sort, not only at finite ones, and the
witness of §6.3 shows it holding without the finite-sort argument it used
to need. Each link of the untimed chains pays the side condition once,
with the effect it waits for (`EnabledMove.of_enabled_of_effect`, or
`eventually_of_weaklyFair`, which pays it inside).

**Resolved in the model (R4–R6, 2026-09-30).** The finding was about the
model, not the premise: it had fair labels that stay enabled after firing.
S1b (§6.4.7) removed them. Every fair action now has a "not already" guard
on a record its own step sets, as the paper's rules do, and each model
proves that no fair label is enabled without being able to change the
state, at every state: `Mvba.enabledMove_of_enabled` and
`Chorus.justice_enabledMove`. So the premises are stated with plain
enabledness again — an action enabled from some point on eventually fires
— with no qualifier: `WeaklyFair`, `WeaklyFairFamily`, `StronglyFair`,
`BoundedFair` and `BoundedFairWhile` are over `Enabled`, and so both
`FJustice`s and `BoundedJustice` are. For these models that is the same
premise as R3's: `Mvba.fJustice_iff_move`, `Chorus.fJustice_iff_move`,
`Mvba.boundedFair_iff_move` and `Mvba.boundedFairWhile_iff_move` state the
equivalence, from the acceptance lemmas. `EnabledMove` remains only as the
vocabulary of those four bridges, and the proofs lost the side condition
(`EnabledMove.of_enabled_of_effect` is gone).

**What is deliberately absent**, the checklist §6 asked for: no clause
mentions a good view, the leader rotation, or GST as a model event. Every
clause relates an environment event — a label firing, a clock reading — to
a guard or a local record. Since step 5b the network clauses' side
conditions also read the network's own facts, as the supplement's network
rules do: who sent a message (a correct validator or not), when it was
first sent against GST, which view its receiver had reached, and, for the
composing layer's delivery, whether a correct validator has decided on the
certificate. None of them is a protocol conclusion the argument needs;
each is a condition under which the supplement promises delivery.
(A-viewsync)'s shape was
forced because an untimed model could relate the timer only to protocol
*events*; with a clock the timer relates to *durations*, and the
certificate leaves the premise.

#### 6.2.5 Hypotheses of the instance, not of runs

`Admissible` is a predicate on runs and cannot constrain the theory `th` or
the sorts; what the argument needs of those is a hypothesis of the
*instance*, exactly as `ByzNodeSetEnum`, `ByzNodeSetHonestQuorum` and
`ViewOrderEnum` are hypotheses of `Mvba.termination`:

* **(A-leader-rotation-k)** — `∀ v, ∃ j < k, ` the leader of `succ^j v` is
  correct. The supplement's *"every `f+1` consecutive views contain a
  correct leader"* with `k = f+1`; the model's `leader_honest_cofinal` is
  its `k`-free shadow and is implied by it. The bound needs `k` because
  the number of Byzantine-led views burnt is what `O(fΔ)` counts.
* The three enumeration/quorum classes above, unchanged.
* The time theory of §6.2.2, and the schedule hypotheses of §6.2.3.

`MVBATemporal.ℓ` is then a closed term in `Δ, δ, Δ_sync, τ_max, k` and the
length of `ViewOrderEnum.below v_L`.

#### 6.2.6 The bound, milestone by milestone

Write `E₀` for the clock at the first index at which a correct validator
has entered the view in question, and `u := max(t, gst)`. Two lemmas carry
the schedule; the exact constants live in [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean), this table is
their derivation.

**A Byzantine-led (or ramp) view `v`, from `Synced v X`** — every correct
validator has entered some view `≥ v` by time `X ≥ gst`:

| milestone | by | why |
|---|---|---|
| every correct validator still in `v` has its timer expired | `X + τ v` | (T2) from its entry, which is `≤ X` |
| … and has timed out or left `v` | `+ 2δ` | `timeout_*` is enabled; at most one `adopt_prepqc` can intervene in `v` and change the highest held certificate, so one restart of the `δ` window |
| a timeout certificate for some view `≥ v` exists | `+ Δ` | either a correct validator is above `v`, which needs one, or the correct quorum's timeouts are all sent and a correct validator in `v` forms the certificate (`form_own_tc_*`, since R4); a first delivery, the timeouts retained by the first member to send one, which was in `v` then and forms it |
| `Synced (succ v)` | `+ Δ` | `sync_view` enabled for everyone at `≤ v`; a first delivery of a certificate formed after GST |

so `Synced (succ v) (X + C)` with **`C = τ_max + 2δ + 2Δ`** — the
supplement's `τ_{w+1} ≤ τ_w + 2Δ + T` (Supplement, Lemma 15 (`lem:convergence`)) at `δ = 0`.
Neither the leader nor the outcome of `v` enters: a view that happens to
decide is burnt like any other, which is what makes the lemma
unconditional. Both network rows are first deliveries only if `v` is
**fresh** — no correct validator reached a view `≥ v` before GST — so that
every timeout and certificate of such a view is sent after GST. For the
first view burnt after `u` that need not hold: its timeouts and its
certificate may predate GST and arrive by retransmission, at `Δ + ρ` each,
so that view costs **`C + 2ρ`** (`synced_succ_first`; the supplement's
"Reaching `V`").

**The good view `W`** — correct leader, `τ W > L_cert`, first correct entry
at `E₀ ≥ gst`:

| milestone | by | why |
|---|---|---|
| every correct validator is in `W` | `E₀ + Δ` | the first correct validator in `W` forwarded the certificate below it at `E₀ ≥ gst`; nobody is above `W` (below) |
| the leader's `Pre-Prepare` | `+ δ` | `leader_*` local |
| every correct validator accepted and sent `Prepare` | `+ Δ` | `handle_preprepare` |
| every correct validator holds its own `prepareQC_W` on `e` | `+ Δ` | `adopt_prepqc` on the correct quorum's prepares, all on one `e` (`accepted_unique`); a first delivery, since R3 ((N4) in §6.2.4) |
| … and has `avail_ready` | acceptance `+ Δ_sync` | (Δ-avail), in parallel |
| every correct `Commit` sent | `max` of the two `+ δ` | `send_commit` |
| `msg_commitqc W e`, and a correct validator decided | `+ Δ` | `form_own_commitqc` at the first correct validator in `W`, which forms the certificate from the correct quorum's `Commit`s and decides on it (`TryFormCommitQC` and `Decide`, since R4) |

so a correct validator has decided by `E₀ + L_cert` with
**`L_cert = 3Δ + max(Δ, Δ_sync) + 2δ`** — Supplement, Lemma 16 (`lem:good-view`)'s
`t*_w − τ_w` at `δ = 0`, `Δ_R = 0`. (Until R4 the certificate was the
anonymous assembly's at `E₀ + L_cert` and everyone decided on it by
`E₀ + L_cert + Δ`, a first delivery; since the validator that forms the
certificate now also decides, the good-view lemma concludes one decision,
and the others come by the transfer below, as they already did when a
decision preceded the chain.)
Every network row is a first delivery: each message is sent from inside `W`
after `E₀ ≥ gst`, by correct validators, and retained, because at `E₀`
every correct validator is already in `W − 1` or `W`. That last fact is the
**one-view retention** (`retained_before`, the model's twin of
Supplement, Lemma 15 (`lem:convergence`)'s retention clause). It holds when `W − 1` is fresh and
past the ramp: the first correct validator in `W − 1` forwarded its
certificate after GST, so everyone reaches `W − 1` within `Δ`, and nobody
can be above `W − 1` before its budget `τ(W − 1) > L_cert ≥ Δ` has run
out. Every step above needs no correct validator to have
timed out in `W` or entered a view above `W`: a `W`-timer of a correct
validator fires at `≥ E₀ + τ W > E₀ + L_cert` by (T1) and clock
monotonicity, a view above `W` needs a correct timeout in `W`
(`entered_le_of_no_timeout`, in its prefix form), and every guard the
chain needs is stable on that prefix. At `δ = 0` this is
`3Δ + max(Δ, Δ_sync)`, the supplement's constant with `Δ_R = 0` — `Recover`
is the identity in this model ([Mvba.lean](../Cadence/Mvba.lean), "The value type").

**The assembly.** Let `N₀` be the last index with `clk ≤ u` (the state at
time `u`; every proposal is at or before it), `M` the highest view any
correct validator has entered at `N₀` — a maximum over a finite list, since
each step enters at most one view — and `W` a correct-led view reached from
`M`: some `a` with `1 ≤ a ≤ |below v_L|` successors of `M` clear the ramp
(the successors below `v_L` are distinct members of the list `below v_L`),
and (A-leader-rotation-k) places a correct leader fewer than `k` views
further on, counted from the view *after* that one. The good view `W` is
thus at least `M + 2`, and its predecessor `W − 1` is fresh (above `M`) and
past the ramp, which is what the retention needs — the supplement's charge
of views `V` and `V + 1` as possibly unproductive (Supplement, Lemma 16 (`lem:good-view`) takes
`w ≥ V + 2`). Then: `Synced M (u + Δ + ρ)` by one retransmitted
`sync_view` hop, since the certificate below `M` exists at `N₀` but may
predate GST; `Synced (M + 1)` a further `C + 2ρ` on (the first burn);
`Synced W (u + Δ + ρ + 2ρ + n • C)` with `n ≤ |below v_L| + k` views burnt
in all; `W`'s first correct entry is after `N₀`, hence `E₀ ≥ u ≥ gst`; and
the second lemma has a correct validator decided by `E₀ + L_cert`. Whether
that decision is the good view's or came earlier, the composing layer
delivers its certificate to everyone within `Δ + ρ`
(Supplement, Lemma 13 (`lem:decision-propagation`)). Hence

  `ℓ = (Δ + ρ) + 2ρ + (|below v_L| + k) • C + L_cert + (Δ + ρ)`,

which is `O(kΔ)` when every constant is `O(Δ)` and the ramp is empty — the
supplement's `O(fΔ)` at `k = f + 1`.

**Against the supplement's own bound** (Supplement, Theorem 2 (`thm:termination`) at the paper target,
at `δ = Δ_R = 0`, the fixed `T`, `Δ_sync ≤ Δ`, an empty ramp, so
`|below v_L| = 1`, and `k = f + 1`): the supplement learns a certificate by
`t₀ + ρ + 4Δ + max{T, ρ} + T + f(2Δ + T) + T` and decides within a further
`ρ + Δ`. Both burn `f + 2` views, and at `T = 5Δ` (and `ρ ≤ T`) both bounds
come to `(7f + 20)Δ` plus retransmission terms: `2ρ` in the supplement's,
`4ρ` in the model's. The difference is the first view. There the
supplement pays one retransmission (its view-`V` timeouts, `max{T, ρ}`),
and each receiver forms the timeout certificate itself. The model forms
the certificate once and delivers it in a separate hop, and both of that
view's hops may be retransmissions. The caller's second premise enters
where `NoEarlyAbandon` did: no correct validator abandons at a clock
`≤ u + ℓ`, so `¬ abandoned` holds on every prefix the argument uses.

#### 6.2.7 What is proven where, and what (A-viewsync) becomes

`Mvba.termination` is **not consumed** by the bound and cannot be: it
yields `∃ n, decided`, and no timed premise turns an index into a clock
reading after the fact. The bound is a re-run of the chain with "within
`D`" in place of "eventually" — each of [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)'s links is
`enabled_<action>` (guards ⇒ enabledness) + one weak-fairness step +
`<action>_effect`; the timed twin keeps the first and third and replaces
the second by one (Δ-justice) step and a stability argument on the window.
`eventually_forall`'s twin is a maximum of indices — the clock is
monotone, so the latest of several bounded firings is still within the
bound. That is the sense in which §6.1's "mostly plugging in proven
theorems" is right, and the sense in which it is not: the temporal glue is
rewritten in full.

What *is* derived from the untimed file, as a corollary, is
**(A-viewsync)**: `AViewSync (tr.toLRun)` for every admissible `tr`. The
plan was to take `W` to be the good view above: the first clause from (T2)
plus `clock_unbounded`, the second from the good-view lemma's certificate
time against (T1). The proof (`Mvba.aViewSync_of_sync`) went differently
and needs less, and its statement needed a finite validator set. §6.2.8's
step-4 reassessment has both. That
theorem is the formal version of the trust-base move
[Liveness.md](Liveness.md) §2.1 describes, and it retires the only
premise of `Mvba.termination` that was not fair scheduling or a caller's
condition. `admissible_exists` is the run in which no one proposes and the
environment only marks availability, at every sort. `Admissible` holds of
it because no `JusticeLabel` is move-enabled at any of its states: sixteen
guard facts, and a member of each quorum for the assemblies. It does *not*
discharge [TODO.md](TODO.md) § Liveness's witness item, as this section once said:
nobody proposes in it, so it is no witness for `TerminationClaim`'s
`AllPropose`. That witness is §6.3's.

#### 6.2.8 Staging, revised

Reassess after step 2, as §6 says. No step touches the model, the proof
files, [Interfaces.lean](../Cadence/Interfaces.lean), [Fairness.lean](../Cadence/Fairness.lean) or [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean).

1. **This session.** [Cadence/Timed.lean](../Cadence/Timed.lean): `TLRun`,
   the `TotalOrder` bridge, move-enabledness, bounded fairness and its
   contrapositive, the bounded finite-conjunction lemma, `MVBASafety.timed`
   and `TLRun.toTimedRun`. [Cadence/Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean):
   `hop`, `Schedule` with its hypotheses, the four clauses, `Admissible`,
   (A-leader-rotation-k), `ℓ`, and the target as a `Prop`-valued
   definition **before** any proof — [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)'s discipline.
2. **Done (2026-09-28).** The good-view lemma: the eight timed links, the
   prefix form of `entered_le_of_no_timeout`, the stability arguments. The
   cheap validation of the scaffolding, and where a misclassified `hop`
   would show up. [Cadence/Mvba/Bound.lean](../Cadence/Mvba/Bound.lean),
   `Mvba.good_view_decides`; the reassessment is below.
3. **Done (2026-09-28).** The burn lemma, the finite starting point, the
   successor-chain count against `below v_L`, the assembly, and `ℓ`.
   [Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean),
   `Mvba.bounded_termination`; the reassessment is below step 2's.
4. **Done (2026-09-28).** `MVBATemporal` at the lifted fragment
   (`Mvba.mvbaTemporal`, with `Mvba.admissible_exists` and
   `Mvba.timed_termination`) and the full class (then `Mvba.mvbaTimed`, now
   `Mvba.mvbaFull`), in
   [Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean).
   (A-viewsync) as a corollary is `Mvba.aViewSync_of_sync`, and the
   assembly's first half is factored out as `Mvba.exists_good_view`, both in
   [Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean).
   The axiom pins, the [Cadence.lean](../Cadence.lean) rows and the verification-status text
   in [CLAUDE.md](../CLAUDE.md) and [Architecture.md](Architecture.md) §4 are updated, and the seam is put
   to the Chorus leg in §6.2.1. The reassessment is below step 3's.
5. **Done (2026-09-29).** Non-vacuity: the premise ledger (§6.3) and one
   model satisfying every premise of both termination theorems,
   [Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean). The
   reassessment is the last one below.

**Reassessment after step 2** (2026-09-28, as §6 asks). The good-view lemma
is `Mvba.good_view_decides` in
[Cadence/Mvba/Bound.lean](../Cadence/Mvba/Bound.lean), kernel-checked, axioms
at the standard trio. Its premises are the three clauses of `Sync` and the
two quorum classes; it builds in seconds and touched nothing under §4.1's
rules. The three questions the plan left open:

* **Which links cost more than one `BoundedFair` application.** None. Each
  of the eight links (`sync_view`, the leader's proposal, `handle_preprepare`,
  `form_prepqc`, `adopt_prepqc`, `send_commit`, `form_commitqc`, `decide`) is
  one application, through one generic lemma
  (`TLRun.withinFrom_of_boundedFair`) that also pays the move-enabledness
  side condition once for all of them. The leader link splits on the
  certificate below `W` (re-propose under a lock, fresh proposal without
  one), but that is a case split on the state with one application in each
  branch, exactly as in the untimed link. The quorum steps are one
  application per member plus `TLRun.withinFrom_forall`; availability is
  (Δ-avail) directly, joined to the adoption by taking the later of two
  indices (`TLRun.clk_max_le`). (Since R3 there are seven: each validator
  forms its own prepare certificate, so `form_prepqc` left the chain and
  `adopt_prepqc` is a network hop; §6.2.4, (N4).) The cost the plan did not foresee was on the
  *stability* side, not the fairness side. Three state facts
  [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) does not export had to be proven locally:
  `timer_set_label` (only `expire_timer i v` sets `timer_expired i v`, one
  case per action from M13's frame lemmas), the prefix form of
  `entered_le_of_no_timeout`, and the timeout certificate below `W` present
  *at* the first correct entry (`msg_tc_below_of_entered`). Each is a short
  plain-Lean proof.
* **Whether the hop table survived contact with the guards.** It did. Each
  link asks `hop` for its bound by `rfl`, so a disagreement between a link and
  the table fails to elaborate. No link needed a different class. Two δ-rows
  read a certificate built from other parties' messages, and both are right
  for the reason the table gives: `leader_*` reads `tc_lock`/`tc_nolock`,
  which `form_tc_*` sets in the same step as the `msg_tc` whose delivery
  `sync_view` has already paid for (`msg_tc_backed` at the entry index); and
  `adopt_prepqc`/`decide` read certificates whose delivery `Δ` sits on the
  assembly. The good view does not exercise the view-zero labels, the
  timeouts, `form_tc_*` or `sync_view_adopt`, so their rows are tested by
  step 3's burn lemma, not here.
* **Whether `Lcert`'s constant is still the one derived in §6.2.6.** It is,
  with no slack and no extra term. The proof names the eight milestone
  deadlines and closes `E₀ + Lcert = ` their sum by `abel`, so the table and
  the constant agree term for term.

Two findings, both about statements rather than about the protocol:

* **The time theory needs cancellation.** §6.2.2's linearly ordered monoid
  is not enough for the step "`L_cert < τ W`, hence `E₀ + L_cert < E₀ + τ W`".
  In `ℕ∞`, which satisfies §6.2.2's axioms, a clock at `⊤` makes both sides
  `⊤`. A correct `W`-timer may then fire inside the window, and a validator
  that times out in `W` stops the chain. The lemma therefore takes
  `[IsOrderedCancelAddMonoid time]`; `ℕ`, `ℚ≥0` and `ℝ≥0` are instances, so
  the intended models are unaffected. The claims in [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean) are
  stated over the weaker class and are unchanged. The theorem proving
  `BoundedTerminationClaim` (step 3's `bounded_termination`) carries the cancellative class as an explicit
  hypothesis. No run predicate can express it, because it constrains the
  sort, just like the instance hypotheses of §6.2.5.
* **Only the leader and the honest quorum move through the view.** §6.2.6's
  "every correct validator is in `W` / accepted" rows hold of every correct
  validator (the links are stated per validator), but the proof moves only
  `L` and `ByzNodeSetHonestQuorum`'s quorum through `W`. Decisions need no
  view (`decide` reads a certificate of any view), so the final row covers
  every correct validator regardless. The lemma's premises are therefore:
  every correct validator has proposed by the first entry `N₀`; none is
  abandoned by `E₀ + L_cert + δ`; `N₀` is the *first* correct entry, which
  step 3's assembly gets by `Nat.find`; and the clock at `N₀` is at or after
  GST.

The rest of the staging stands. Step 3 is where the burn lemma's `2δ` (one
adoption restarting the timeout's window) gets its first test, and it reuses
this file's link shape and prefix facts unchanged.

**Reassessment after step 3** (2026-09-28). The bound is
`Mvba.bounded_termination` in
[Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean):
`BoundedTerminationClaim`, kernel-checked, axioms at the standard trio,
from the two quorum classes and a cancellative time theory. The burn lemma
is `Mvba.synced_succ`, and its iteration is `Mvba.synced_iterate`. Nothing
under §4.1's rules was touched: no model change, no new invariant or step
property, nothing exported from [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean), and so the
`#veil_status Mvba` pin is unchanged. The questions the plan left open:

* **Whether the `2δ` timeout restart held.** It did, and it was the first
  thing tested. The claim needs one fact: *a certificate a validator
  acquires while it stays in `v` is a certificate of `v`*
  (`local_prepqc_new_in_view`). `adopt_prepqc` is guarded on `in_view` for
  the certificate's own view, and `sync_view_adopt` leaves the view. This
  is a two-state fact about labels, not an invariant. It is proven like
  step 2's `timer_set_label`, one case per action from M13's frame lemmas
  (`local_prepqc_set`), and then by induction along the run. From it,
  `within_timed_out` is three cases:
  * the goal already holds;
  * a certificate of `v` is held somewhere in the first `δ` window, after
    which the label is fixed for one more `δ`;
  * no certificate is acquired in the window, so the label chosen at its
    start stays enabled.

  The highest held certificate at the start is found over `below v`, as in
  the untimed link.
* **Whether the hop table survived the rows step 2 did not exercise.** It
  did. `timeout_qc`/`timeout_noqc` are `δ` steps, and `form_tc_lock`,
  `form_tc_nolock` and `sync_view` are `Δ` hops, each asked of `hop` by
  `rfl`. Three rows are still exercised by no proof. `sync_view_adopt` is
  never needed, because `tc_lock_implies_tc` lets a validator holding a
  higher certificate advance through `sync_view`. The two view-zero labels
  are never needed either, because `W` is strictly above a view already
  entered. Their fairness is a premise the bound does not use, which
  weakens nothing. Step 4's `admissible_exists` must still satisfy it,
  which it does vacuously where the labels are never move-enabled.
* **Whether `burn` and `ℓ` are still the constants in [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean).**
  `burn = τ_max + 2δ + 2Δ` is. The proof names the four deadlines and closes
  `X + burn =` their sum by `abel`. **`ℓ` moved**, from
  `Δ + (1 + |below v_L| + k) • C + L_cert + δ` to
  `Δ + (|below v_L| + k) • C + L_cert + δ`. The count is `a + j` burns:
  `1 ≤ a ≤ |below v_L|` successors of `M` clear the ramp
  (`exists_iterate_succ_ge`, a pigeonhole over `below v_L`), and `j < k`
  more reach a correct leader. The step out of `M` is the first of the `a`,
  so the `1 +` counted it twice. `Schedule.ℓ` is redefined to match, and
  §6.2.6 is updated. `a + j ≤ |below v_L| + k - 1` would be tighter still;
  it is not taken, because the natural-number subtraction buys one burn and
  costs readability.
* **How the finite starting point is proven.** As §6.2.6 said: a maximum
  over a finite list, since each step enters at most one view
  (`entered_set_view`, a label case split, then `entered_covered` by
  induction on the index). Neither the node sort nor the view sort is
  assumed finite, and `ViewOrderEnum` is not used for `M`. It is used for
  three other things: `succ`, the pigeonhole count, and the highest held
  certificate in the timeout step. `M` ranges over *correct* validators'
  views, which is all the argument needs.
* **Where cancellation goes.** On the theorem only.
  `bounded_termination` takes `[IsOrderedCancelAddMonoid time]`, and
  [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean)'s variables and both claims keep the weaker class. The
  burn lemma needs no cancellation. The assembly needs it twice: through
  `good_view_decides` (step 2's `ℕ∞` finding), and for `u < u + Δ`, which
  is how the last index at or before `u` is found by `Nat.find`. Keeping the
  claim at the supplement's theory means the extra class appears only where
  a proof uses it, and is not built into the definitions a reader checks
  against the paper.

Three facts are proven locally that neither [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) nor step 2
had: the certificate below a view with its predecessor produced
(`exists_tc_pred_of_entered`); that the first correct validator at or above
a view is *in* it (`entered_eq_of_first_above`, since skipping it needs a
correct timeout there); and the successor facts of `ViewOrderEnum`. Each is
a short plain-Lean proof.

**What step 4 now needs.** The protocol argument is complete. What remains
is plumbing between the claim and the contract, plus the corollary:

* `MVBATemporal.termination` at `(mvbaSafety th).timed time`, from
  `bounded_termination` through `Admissible`'s labelling. The observables
  are definitional (§6.2.8 step 1), so the work is `byGstBound`'s shape
  against `max t gst + ℓ`.
* `admissible_exists`, as §6.2.7 planned.
* `AViewSyncClaim`. Its second clause is the good view, and the assembly
  constructs that view (`W`, `N_W`) but does not export it. Step 4 should
  first factor the assembly's first half into a lemma that returns `W`
  with `good_view_decides`'s premises, then prove both
  `bounded_termination` and `AViewSyncClaim` from it. The first clause is
  (T2) plus `clk_unbounded`, as planned.
* The axiom pins, the [Cadence.lean](../Cadence.lean) row, and the text in [CLAUDE.md](../CLAUDE.md) and
  [Architecture.md](Architecture.md) §4 about the timed instance and its seam, as listed in
  the staging above.

**Reassessment after step 4** (2026-09-28; the names are those before the
§6.2.1 outcome: `mvbaTimed` is now `mvbaFull`, and the instance is at
`mvbaSafety th`). The instance is
`Mvba.mvbaTemporal : MVBATemporal … (S := (mvbaSafety th).timed time)` and
the full class is `Mvba.mvbaTimed`, in
[Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean). Both are
kernel-checked, with axioms at the standard trio, and
`Mvba.mvbaTimed_toSafety` hands back the lifted fragment by `rfl`. Nothing
under §4.1's rules was touched except one docstring sentence in
[Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) (`Terminates`, which said the timed form had no
instance). No model change, and the `#veil_status Mvba` pin is unchanged.
The **MVBA bounds leg is complete**; what it leaves open is the seam
proposal in §6.2.1. The questions the task set:

* **Whether the instance needed any hypothesis beyond the plan's.** No.
  The hypotheses are exactly §6.2.5's, with the time theory of §6.2.2 as
  step 2 amended it:
  * finitely many validators (`Fintype node`) in place of
    `ByzNodeSetEnum`, which it supplies (`ByzNodeSetEnum.ofFintype`; see the
    last point below);
  * `ByzNodeSetHonestQuorum` and `ViewOrderEnum`;
  * `LeaderRotation vfin sch.k th`;
  * `IsOrderedCancelAddMonoid time` for `termination`;
  * `Archimedean time` for `admissible_exists`. `0 < Δ` was already a
    field of `Schedule`.

  The hypotheses can be met. `Schedule.fixedNat` is the paper's fixed
  timeout at `time := ℕ`. An `example` in the same file instantiates
  `MVBATemporal` there, with the class's `TotalOrder ℕ` found by instance
  search (Veil's own), so the scoped bridge the instance was built with
  agrees with it. The contract's observables are the model's fields by
  `Iff.rfl` (`timed_decided_iff`, `timed_proposed_iff`,
  `timed_abandoned_iff`). The least upper bound in `byGstBound` and in the
  abandonment premise is `max` by one generic lemma, `Cadence.gstLub_iff`
  in [Timed.lean](../Cadence/Timed.lean), with `TimedRun.byGstBound_iff` built on it. So
  `timed_termination` is `bounded_termination` read through `Admissible`'s
  labelling and nothing else.
* **One correction to the plan, not a hypothesis.** The witness clock
  `c + n • Δ` of §6.2.7 is not unbounded in general. In an Archimedean
  linearly ordered cancellative monoid with negative elements, `c + n • Δ`
  can stay below `0` for all `n`. An example is
  `{(0, b)} ∪ {(a, b) : a < 0} ⊆ ℤ × ℤ` under the lexicographic order, with
  `c = (-1, 0)` and `Δ = (0, 1)`. That monoid is Archimedean because every
  positive element is `(0, b)` with `b > 0`, and every element is at most
  some `n • (0, b)`. The witness therefore uses `c`, then
  `max c ((n + 1) • Δ)`, which the Archimedean axiom bounds from below
  directly. The witness run fires `become_avail_ready` forever. It is
  admissible because every state is *quiet*: no input, entry, acceptance,
  or prepare/commit/timeout message. At a quiet state no hop-table label is
  move-enabled, which one case split over the transition bodies shows. The
  three labels no proof uses are covered by the same fact, vacuously.
* **Whether `AViewSyncClaim`'s statement survived.** Its premises did, and
  it gained one hypothesis: a finite validator set, `[Fintype node]`. The
  plan's premise `AllPropose` ("every correct validator proposes at some
  index") gives a common deadline only over finitely many validators, and
  without a deadline the bound has no starting point: nothing stops every
  correct-led view from being burnt before its leader has proposed. The
  first version of this step removed the need for finiteness by changing
  the premise to "proposed by some time `t`". Following review, the claim
  instead keeps `Mvba.termination`'s own caller premises (`AllPropose`,
  `NoEarlyAbandon`) and assumes finitely many validators (see the last
  point). The deadline form survives as the lemma behind it,
  `Mvba.aViewSync_of_proposedBy`, for any node sort. The claim does not
  need "no abandonment up to `u + ℓ`", because an abandoned correct
  validator has decided, and a decision is certificate-backed
  (`decided_backed`).
* **How it was proven: not through the good view, and why that matters.**
  The second clause of `AViewSync` only asks that a `W`-timer does not
  expire before *some* commit certificate exists. So **any** correct-led
  view above every view entered when a certificate first exists satisfies
  both clauses. The first clause follows from (T2), and the second from
  (T1), since the timer of such a view starts after the certificate
  (`Mvba.aViewSync_of_commitqc`). Neither step uses timing beyond the two
  timer clauses. The certificate itself comes from `bounded_termination`,
  or from an early abandonment. The factored good view (`GoodView`,
  `exists_good_view`) is what `bounded_termination` consumes, but this proof
  does not need it. **The finding** is about what kind of premise
  (A-viewsync) is, and [Liveness.md](Liveness.md) §2.1 now opens with
  the short account. It does not weaken `Mvba.termination`. It is the view
  timer stated as ordering constraints: the untimed model has the timer but
  no clock, so on its own a timer may fire at any moment, and the premise
  fixes the two orderings that matter. It holds in every run that
  terminates (`aViewSync_of_commitqc`), so the untimed theorem reads *given
  enough time, the protocol decides*, with the bound set aside and not the
  synchrony. The synchrony itself is the timed premises', in the
  supplement's terms, and `aViewSync_of_sync` derives the ordering
  constraints from them.

  **Both clauses are needed**, and the second does not imply the first
  through a least good view. Let a Byzantine leader of `V` never propose,
  and let `V`'s timer never fire, which is allowed because the marker is
  under no fairness obligation. Every correct validator stays in `V`. Every
  correct-led `W` above `V` is never entered, so it satisfies the second
  clause vacuously, and nobody decides. A least `W` would not help for two
  reasons. It constrains only correct-led candidates. And a candidate's
  failing the second clause means that *some* correct validator's timer
  fired early, not every one. The view order is also not assumed
  well-founded, except through `ViewOrderEnum`. In the timed model the two
  clauses are (T2), not late, and (T1) with `τ W > L_cert`, not early.
* **What the seam proposal says.** Two ways to hand the composed system the
  instance (§6.2.1). (a) plugs the lifted fragment in at [System.lean](../Cadence/System.lean): no
  class change, but the composed run must require each MVBA step to stamp
  the global time into the sub-state. (b) is route 2: `TimedRun` carries its
  own clock sequence, the instance moves to `mvbaSafety th` itself, and the
  existing `mvba_of_temporal` joins it. The recommendation is (b), bundled
  with the next [Interfaces.lean](../Cadence/Interfaces.lean) edit and decided with the Chorus leg's
  composition step. The decision is open.
* **The obligations list in [Interfaces.lean](../Cadence/Interfaces.lean)** was left naming
  `termination, ℓ` as unproven until the next edit of that file; it now
  names `Mvba.mvbaTemporal`.
* **Finiteness of the validator set, as a convention for claims.** It came
  up three times, spelled three ways: the class `ByzNodeSetEnum` (the
  MVBA's quorum enumeration), a complete list `nodes` with a proof that it
  contains every validator ([Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)), and the deadline
  form of this claim. None of them concerns the protocol. They are the
  point at which a liveness argument collapses finitely many per-validator
  eventualities into one index, which is sound only over a finite set. So
  the contract-level results of this leg (`mvbaTemporal`, `mvbaTimed`,
  `timed_termination`, `aViewSync_of_sync`) take `[Fintype node]`, and
  `ByzNodeSetEnum.ofFintype` ([ByzQuorum.lean](../Cadence/ByzQuorum.lean)) supplies the enumeration
  their proofs use. The building-block lemmas keep `ByzNodeSetEnum`, which
  is weaker: finite quorums over any node sort. `bounded_termination` keeps
  it too, as the general form.

  What finiteness does **not** do is simplify the proofs. Every step that
  consumes it is local and already existed. It also does not touch the two
  other finiteness questions of the leg: the abstract `nodeset` sort may
  still have infinitely many supermajorities (§6.2.4's caveat on
  `FJustice`, resolved in R3 by stating fairness over state-changing
  steps), and the view order is infinite by nature (`below vL`). It
  stays out of the Veil models and the safety theorems, which hold at any
  cardinality and whose solver could not use it anyway. **Proposal to the
  Chorus leg:** adopt the same convention. That means `[Fintype node]` in
  place of the `nodes`/`hnodes` argument in [Chorus/Termination.lean](../Cadence/Chorus/Termination.lean), and,
  when `Mvba.termination` is next touched, `[Fintype node]` in place of its
  `ByzNodeSetEnum` argument. At the concrete families `Fin n` both are
  instances already.

**Reassessment after the non-vacuity step** (2026-09-29). The results are
`Mvba.timedTermination_premises_satisfiable` and
`Mvba.termination_premises_satisfiable` in
[Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean), axioms at the
standard trio. Each is an existential over the whole premise set: the
sorts, the instances, the schedule, the theory and the run. No premise's
statement changed. **The model did change**, once, and that is the step's
main finding (§6.3.2): building the witness showed the model did not halt
a validator after it decides, as the supplement does, so the halt was added
([Cadence/Mvba.lean](../Cadence/Mvba.lean), "A decided validator halts").
The `#veil_status Mvba` count is unchanged, since only guards were added,
but every VC changed and the family was re-solved; the mutation test
[Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) mirrors the guard, still
finds its agreement violation, and its pinned trace moved (the two
decisions now come last). The questions the task set:

* **Whether any premise was harder to satisfy than the ledger expected.**
  One, and not the one flagged. The expected hard premise was `FJustice`
  with plain `Enabled` (§6.2.4). At the concrete family it cost one lemma:
  once the run is idle only two assembly labels are enabled, because a
  certificate has one quorum that can assemble it at `ByzNSet 4`
  (`Mvba.Witness.enabled_idle`), and the tail fired both forever. (Since
  R3 `FJustice` is stated over state-changing steps, the idle tail owes
  nothing, and that lemma is gone; §6.3.) The
  premise that mattered was the caller's `NoEarlyAbandon` together with the
  view timer. In the model as it was, a decision did not stop a validator,
  so a witness had either to change views forever or to have the caller
  abandon every validator after `max(t, GST) + ℓ`; the first version of the
  witness did the latter, through five views. That is what exposed the
  divergence from the supplement. With the halt, the witness is the run the
  plan asked for: everyone decides in view 0, then idles.
* **What the halt cost the proofs.** Every honest link now needs its
  validator *active*: neither abandoned nor decided (`Mvba.Active`, which
  replaced `¬ abandoned` in `SettledIn` and in the link hypotheses). The
  untimed proof already ran under "nobody has decided", so it needed only
  that substitution. The timed proof needed one new case split, in
  `bounded_termination`: either a correct validator decides by the
  certificate deadline `max(t, GST) + ℓ − δ`, and then everyone decides
  within `δ` of its certificate (`within_decided_ref`, the decide link
  measured from `ref N`), or nobody does, and the chain runs as before with
  every correct validator active up to that deadline. `ℓ` is unchanged.
* **Whether bounded weak fairness needed a real argument.** No. The run
  advances its clock only out of states at which no fair label is
  move-enabled (`Mvba.Witness.quiet`), so every window contains such a
  state on its own clock reading, and (Δ-justice) holds with its antecedent
  false. That is a property of this run, which is as eager as possible, and
  not of the premise.
* **Whether one run serves both claims.** It does. The untimed projection
  satisfies the five untimed premises; (A-viewsync) holds at `W = 1`,
  because the view-0 timers expire and nobody enters view 1. The file ends
  with both theorems applied to the witness.
* **What the proof costs.** Each state is a closed formula in its index,
  so the 25 prefix steps, the quiescence facts and the premises are linear
  arithmetic. The file elaborates in seconds and touches no VC.

### 6.3 The premises are jointly satisfiable

*The premises of the two MVBA liveness theorems — each one's role, why it
is plausible, whether it is obviously satisfiable, and where it is used —
are [Premises.md](Premises.md). This section is the detail behind their
joint satisfiability: the model (§6.3.1) and what building it found
(§6.3.2).*

A theorem whose premises can never hold at once proves nothing. For a
conditional liveness result the check is therefore that every premise can
be met in one model: the instance hypotheses, the class axioms, the model's
`assumption`s, and the fairness and timing premises. Because the premises
are hypotheses, **one model satisfying all of them suffices**. The model is
[Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean), and the two
theorems that say it satisfies them are:

* `Mvba.timedTermination_premises_satisfiable`: some instance, schedule
  and run meet every premise of `Mvba.timed_termination` (and so of
  `Mvba.mvbaTemporal`). The bounded claim is not vacuous: its runs are not
  all excluded by the timing model, and its caller conditions can be met in
  a run that is admissible.
* `Mvba.termination_premises_satisfiable`: some instance and run meet every
  premise of `Mvba.termination`. The untimed claim is not vacuous. In
  particular, its weak fairness does not contradict the rest.

Two premises are not obviously compatible with the others, and the model
is what shows they are. **Admissibility with the caller's conditions**:
every correct validator proposes and none abandons early, so the run must
stop on its own after deciding (§6.3.2). **Weak fairness at an idle tail**:
every fair action is one correct validator's step guarded on its own
record, so it disables itself by firing (`Mvba.enabledMove_of_enabled`,
§6.4.7), and a run that does all the work there is to do and then idles
owes nothing more. **Every premise is satisfiable, and none needed a
change to its statement.** Building the model did change the *model*: it
did not halt a validator after deciding, as the supplement does, and now it
does (§6.3.2).

#### 6.3.1 The model

* **Instance.** Validators `Fin 4` under `byzNodeSetFinGen 4 1`, with
  validator 3 Byzantine and silent. Quorums are sorted lists (`ByzNSet 4`),
  sixteen of them. Values are `Unit`, and every value is valid. Views are
  `ℕ` with `natViewOrder`, and validator 0 leads every view. Time is `ℕ`,
  the schedule is `Schedule.fixedNat ℕ 1` (`Δ = 1`, `δ = Δ_sync = 0`,
  timeout 5, retransmission interval `ρ = 1`), and GST and `t` are 0.
  `ℓ` then has the value `Mvba.Witness.ell` pins.
* **The run.** The three correct validators become available and propose
  at clock 0. They run the whole chain of view 0 and decide in it, each
  forming its own commit certificate and deciding on it (since R4). At clock
  5 their view-0 timers expire, which the timing model requires; having
  decided, they have halted, so none times out. From then on the run is
  idle: it repeats one step that changes nothing, and the clock advances
  by one per step. Nobody abandons, so both forms of the caller's
  abandonment premise hold vacuously.
* **Why the proofs are short.** Every state of the run is a closed formula
  in its index: a record is present at index `n` iff the step that sets it
  is before `n`, and that step is `c + i` for a constant `c` per record and
  validator `i`. Each transition, and each premise, is then linear
  arithmetic over the index.
* **Why the timed fairness premise is easy here.** The clock advances only
  out of states at which no fair label is enabled. So from every
  index there is a later one on the same clock reading at which a given
  fair label is disabled, and bounded weak fairness holds with its
  antecedent false. The run is fair because it never leaves an obligation
  pending while time passes. The untimed weak fairness holds for the same
  reason: at the idle state no fair label is enabled (`quiet`), so its
  antecedent fails from every index on.

#### 6.3.2 The finding: the model did not halt a validator after deciding

The plan (TODO's "Exhibit a run" item) was a run in which everyone decides
in the first view and the run then idles. The model as it stood had no such
run. Its `decide` recorded the decision and nothing else, and its
`timeout_qc` needed only the expired timer, the current view and
`¬ abandoned`. So a decided validator whose timer expired timed out, a
timeout certificate formed, and it entered the next view, whose chain ran
again. In the timed claim (T2) forces the timer of every view entered, so
the view changes never ended unless the caller abandoned — which the timed
claim allows only after `max(t, GST) + ℓ`, and `ℓ` exceeds a view's
timeout. The first witness therefore passed through five views.

**The supplement does stop.** Both its decision paths end in
`decide(…); abandon()` (the procedure `Decide` in Supplement, Algorithm 1 (`alg:mvba-cont3`), reached
from Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`), and the restart path), `abandon()` "halts all
MVBA sending and stops `W`", and the timeout fires only "upon `W` reaches
the view timeout and no decision in view `v`" (Supplement, Algorithm 1, line 36 (`line:mvba:timeout-send`)).
The paper target's termination proof relies on it
([History.md](History.md) § "The supplement at `eb1bb51`, reviewed against the pin `026dc8b`", C11).
The difference was not harmless for the timed claim: read as a model run, a
supplement run in which a validator decides and stops early abandons it
before `max(t, GST) + ℓ`, which the claim's caller condition excludes, so
the theorem said nothing about exactly the runs the supplement produces.

**The fix** ([Cadence/Mvba.lean](../Cadence/Mvba.lean), "A decided
validator halts"): every honest send also requires `∀ E, ¬ decided i E`.
After deciding, a validator sends nothing more, and in particular never
times out, which subsumes the "no decision in view `v`" guard. The halt is
kept apart from the caller's `abandoned`: the contract's Termination
premise is about the caller's `abandon()`, and a validator's own halt
must not count against it. Had `decide` set `abandoned`, every run deciding
before `max(t, GST) + ℓ` would violate that premise and the timed theorem
would be vacuous. The proofs' side is in the reassessment above.

### 6.4 The Chorus leg: the kick-off record

*Written 2026-09-29, after `Chorus.termination` (PR #43) and before any
Lean. S1, S1b, S2, S3, S4 and S5 are done since (§6.4.6, items 1–5, have their records): the leg is complete. It supersedes §6's staging for Chorus
(steps 1–3), which predates the MVBA leg. §6.2 and §6.3 are the template.
Decisions are recorded with their reasons. Those marked **open** are for
Lars to take: item 1 above all, and the two class changes it depends on.*

**In short, for an auditor.** The paper proves two timed properties of
Chorus:

* **ℓ-termination** (Lemma 11 (`lemma:chorus-termination`)): if every correct
  validator starts participating in the slot by time `t`, every correct
  validator finalizes by `max(t, GST) + 5Δ + ℓ_MVBA`;
* **d_tot-totality** (Proposition 4 (`prop:chorus-totality`)): if one correct validator
  finalizes at time `t`, every correct validator finalizes by
  `max(t, GST) + Δ`.

Both hold under *Δ-synchronized participation*
(Definition 5 (`def:delta-synchronized-participation`)): once one correct validator
starts, every correct validator starts within Δ. Both also hold "when run
within Cadence". The contract states the two properties as the fields
`bounded_termination` and `totality` of `SlotConsensusWithTotality`
([Interfaces.lean](../Cadence/Interfaces.lean)). Nothing instantiates
them yet.

The timed claims would assume what the MVBA's did (§6.2): messages arrive
within Δ after GST, local steps take at most δ (zero in the paper), and
the slot's three time landmarks (the deadline `D`, then `D + Δ` and
`D + 2Δ`) happen on time on synchronized clocks. They would further
assume that the MVBA's own timing premises hold of its steps inside the
run, and that the certificate bridge `ValidBridge` holds; the bridge is
unchanged from the untimed claim. The rest are the caller's conditions,
which the composition later discharges: everyone starts by `t`, starts are
Δ-synchronized, nobody starts before `D − Δ`, and nobody abandons before
finalizing.

**The main question is item 1.** The contract's fields speak about
`participate`, `abandon` and `propose`, and the Chorus model has none of
them. **Recommendation (open):** model the participation interface in
[Chorus.lean](../Cadence/Chorus.lean), exactly as the paper's standing
convention states it (option A, §6.4.1). Bundle it into the same
re-solve with one small [Interfaces.lean](../Cadence/Interfaces.lean) edit,
which adds the two "within Cadence" premises the paper's proofs use and
the class omits (finding F1). This is the only option under which the
timed claims are the paper's statements and the contract instances exist.

**Four findings, all about statements, none about the protocol.**

* **F1: the class's timed fields omit two premises the paper uses.**
  `bounded_termination` and `totality` lack "a correct validator abandons
  only after finalizing" (Algorithm 1 (`algorithm:cadence`), Algorithm 1, line 23 (`line:abandon`)). The
  untimed `SlotConsensusTemporal.termination` has that premise.
  `bounded_termination` also lacks "no correct validator starts before
  `D − Δ`", which is the Conductor's integrity
  (Lemma 12 (`lemma:conductor-integrity`)); the proof of
  Proposition 5 (`prop:chorus-finalization-time`) uses it in its first step. Without the
  first premise, a validator that abandons at once never finalizes.
  Without the second, a slot whose deadline lies far after `t` cannot
  finalize by `max(t, GST) + ℓ`. Either way the field is false for every
  faithful implementation, unless the implementation's own `Admissible`
  smuggles in the caller's conditions. The rely form of
  `MVBATemporal.termination` was adopted precisely to avoid that
  (§6.4.1, "The class change").
* **F2: the paper's message buffering needs a split hop.** "A message
  whose rule is blocked by this convention is not lost"
  (Appendix C.3 (`subsection:chorus-protocol-overview`)). A rule's network input is
  therefore due Δ after it was sent, and its local gate (a phase landmark,
  or participation) is due δ after it opened. Measuring a Δ-hop from the
  later of the two, as §6.2.4's `BoundedFair` does, costs one extra Δ at
  every step where a landmark opens last. The model's bound would then be
  `6Δ + ℓ_MVBA` or worse, not the paper's `5Δ`. §6.4.2 states the clause
  that keeps the paper's arithmetic.
* **F3: at δ > 0 the totality latency is `Δ + 2δ`, not Δ.** The
  Conductor's window induction closes *because* Chorus's totality
  latency equals the synchronization tolerance its condition grants.
  "Both equal `Δ = d_tot`", in the words of the paragraph before
  Definition 6 (`def:window-synchronized`). With local steps that take time the ratchet
  loses δ per window. This is the Conductor leg's question. §6.4.6 states
  what this leg provides so that it is not blocked.
* **F4: to be confirmed. The 5Δ bound looks loose by one Δ.**
  Lemma 11 (`lemma:chorus-termination`) splits at `T₀ = M + 4Δ + ℓ_MVBA` and adds Δ
  for totality (`M = max(t, GST)`). The inner split of
  Proposition 5 (`prop:chorus-finalization-time`) at `T₀ − Δ` already handles early
  finalizers, and the only use of that proposition's premise "no correct
  validator stops before `T`" is covered by "abandon only after
  finalizing". So a single split at `T₀ − Δ` should give `M + 4Δ + ℓ_MVBA`,
  which is the bound an earlier, commented-out draft next to the lemma
  states. §6.4.3 records how to handle it if the proof confirms it.
  **Confirmed by S4** (R18): `Chorus.timed_termination_tight` proves
  `M + 4Δ + ℓ_MVBA + 8δ`; the claim stays the paper's 5Δ
  (`Chorus.timed_termination`).

**Decisions in one place.**

* Participation interface: **option A (open)**. The model gains
  `participate` and `abandon`, and `propose` becomes the contract's input.
  Every sending rule is gated on active participation (§6.4.1).
* Class change C1/C2: **recommended (open)**, bundled with option A into
  one Chorus-family re-solve. C3 (the tolerance) goes to the Conductor leg.
* The clock is the run's (`TLRun`, `TimedRun.clk`), as in the MVBA leg.
  No clock goes into the model (§6.2.1).
* The time theory is §6.2.2's, including cancellation. The timing
  constants are the MVBA schedule's `Δ` and `δ`. Chorus adds only the
  deadline (§6.4.2).
* Fairness is bounded fairness over plain enabledness with a hop table.
  The hop is split into a network part and a local gate (F2). The phase
  markers leave the table and become punctual timers (§6.4.2).
* The MVBA is consumed **through the contract**: `T.Admissible` of the
  timed projection, `T.ℓ` and `T.termination`, for
  `T := Mvba.mvbaTemporal …` (§6.4.3). The upgrade step 5b can therefore
  refine the MVBA's timed premise without touching this leg.
* The proof re-runs the untimed chains with deadlines. It case-splits on
  an early finalization, as the paper does, and not on the progress
  dichotomy (§6.4.3).
* Non-vacuity comes from one witness, built after the model edit, that
  serves both the untimed and the timed claims (§6.4.5).

#### 6.4.1 The participation interface

**What the contract asks.** `SlotConsensusTemporal` has three inputs
(`participate`, `abandon`, `propose`) with their observables, effects,
frames and initial conditions. It has the admissible-run model, and
Termination and Quiescence stated over them. `SlotConsensusWithTotality`
takes an instance of it as a parameter. So the timed fields cannot even be
stated at Chorus until the participation interface exists at the
fragment. There is a second constraint: the class's frames say that
*internal* steps leave a correct validator's inputs unchanged.
`Chorus.slotConsensusSafety` currently sets `step := trans`, so any input
it had would also count as an internal step. Every option that
instantiates the class must therefore separate the input labels from
`step` in [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean).

**Option A: model the interface in [Chorus.lean](../Cadence/Chorus.lean).** Add
per-validator `participating i` and `abandoned i` as local state. Add two
input actions:

* `participate i`;
* `abandon i`, which forwards to the MVBA's `abandon` when the validator
  has invoked it, as Algorithm 5, line 48 (`line:fb-abandon`) does. Its successor-state parameter
  is harmless, since inputs carry no fairness.

The existing `propose j m` becomes the contract's `propose(P)`, with
`P ↦ m`, the class's `proposal := merkle_root` at
[Chorus/Compose.lean](../Cadence/Chorus/Compose.lean). Then gate every
rule that sends, with `participating i ∧ ¬ abandoned i`, and exempt the
rules that only process. That is the standing convention of
Appendix C.3 (`subsection:chorus-protocol-overview`), rule for rule:

* **Gated, because they send.** `propose` and `deliver_chunk_assigned`
  (at the proposer), `vote`, `commit_sign_*`, `cast_fast_commit`,
  `fb_sign_*`, `cast_fallback_vote`, `mvba_propose` (the convention names
  it explicitly), `cast_fb_commit`, and `commit_assign_*`/`finalize_commit`.
  The paper's finalization rules re-broadcast the proof
  (Algorithm 4, line 35 (`line:fast-rebroadcast-commitqc`), Algorithm 5, line 46 (`line:fb-commit-rebroadcast`)), and
  its totality proof relies on their being gated. The model's comment at
  "Commit decision" ("finalization on receipt has no active-participation
  precondition") then changes.
* **Exempt, because they process.** `record_chunk`, `aggregate_fastqc_*`,
  the decision handlers and `mvba_terminate`.
* **Anonymous capabilities.** `broadcast_commitqc_*` and
  `redisseminate_chunk` have no actor today. In the paper both are sends
  by a correct validator: the collector (Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)),
  and the fallback-entry caster (Algorithm 5, line 12 (`line:fb-redisseminate`)). The faithful
  form gives each a sender parameter, gated when the sender is correct and
  unconstrained when it is Byzantine. Without that, Quiescence cannot
  attribute those messages. **Recommended**, since the family re-solves
  anyway.

Quiescence is then provable in the paper's own two-part shape
(Lemma 6 (`lemma:chorus-quiescence`)):

* Chorus's own sends are gated;
* the MVBA's sends are the MVBA's `sent`, confined by its `quiescence` to
  the window between a gated `propose` and a forwarded `abandon`.

The message type is a sum of Chorus's attributed network relations and
`mmsg`, defined in [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) and
not in the model. The proof reads the transition bodies, like the MVBA's
`sent_new_tr`, so no `step_property` cell is needed.

*Cost.* Every VC statement changes (new state components), so the whole
Chorus family re-solves cold. The measured cold figures live in
[CLAUDE.md](../CLAUDE.md) and [Dependencies.md](Dependencies.md). Other
effects:

* **The audit pin.** The `#veil_status Chorus` pin in
  [Chorus/Certify.lean](../Cadence/Chorus/Certify.lean) grows by two
  actions' cells per property. The Chorus.lean edit adds no invariant: the
  new guards only strengthen hypotheses.
* **Manual cells.** They keep their statements' shape (`veil_inv_have` is
  by name), but their tactics must be re-run cold (CLAUDE.md,
  "The cache hides derivation drift").
* **The label classification.** [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)
  gains an `InputLabel` class (`participate`, `abandon`, `propose`). This
  is **a trap to avoid**: `JusticeLabel` is the complement of the other
  classes, so a new input would silently become weakly fair, and fairness
  of `abandon` would force every validator to abandon.
* **The component.** `MvbaStepLabel` and `mvbaComponent` gain the
  forwarding `abandon`.
* **The untimed claim.** `TerminationClaim` gains the caller's premises
  (every correct validator eventually participates; none abandons before
  finalizing), which are exactly `SlotConsensusTemporal.termination`'s.
  Its proof restructures, because a validator that finalizes on the fast
  path and then abandons also abandons the MVBA. So the MVBA's
  `NoEarlyAbandon` holds only on the branch where nobody has finalized.
  The re-proof therefore splits on an early finalization, which is the
  split the timed proof uses (§6.4.3). Each honest link gains the gate as
  a hypothesis, as the MVBA's links gained `Active` in PR #42.
* **The monitor.** Its label decoders learn the new actions.
* **Unaffected**: the FallbackReceipt and Mvba families, and the glue's
  safety theorem, which is generic in the fragment.

*Faithfulness.* This is the highest of the three options. The claims are
the paper's statements over the paper's interface. Both `…Temporal`
instances become possible, Quiescence stops being "out of scope" in
Chorus.lean's header, and `TerminationClaim` becomes the class's own
Termination.

**Option B: state the claims over what Chorus models.** Two variants.

* *B1, implicit participation.* Every validator participates from the
  run's start. The claim becomes: all correct validators participate from
  `D − Δ`, and all finalize by `max(D − Δ, GST) + ℓ`. That is a true and
  honest special case, and it is exactly the Conductor's steady state
  after recovery. It is not the paper's lemma, which quantifies over late
  and staggered starts. It cannot instantiate `SlotConsensusTemporal`,
  because `init_participating` and the input frames have nothing to bind
  to. Quiescence is false in it: an implicitly participating validator
  votes before any `open`. And it blocks the next leg:
  Proposition 14 (`prop:conductor-open-to-complete`) applies ℓ-termination at a start time
  `max(t, GST) + d_tot` set by the Conductor, not at `D − Δ`.
* *B2, a gated product in Lean.* Wrap the Chorus transition system with
  participation ghosts and gate its labels outside Veil. Safety transfers
  by simulation, and nothing re-solves. The wrapper cannot forward
  `abandon` to the MVBA (Algorithm 5, line 48 (`line:fb-abandon`)) without stepping `mvba_st`
  outside Chorus's transitions. That breaks the simulation to Chorus's
  reachable states, on which every invariant rests. Without forwarding,
  Quiescence is false for the MVBA's messages after a fast-path
  finalization. The wrapper would also be a second semantics of Chorus
  that an auditor has to read beside the model. Every run-level lemma of
  stages 3–4 would have to be transported through it.

**Option C: change the class.** For example, drop the inputs from the
Chorus-facing class, or state Termination over "participates from the
start". Either is unfaithful to Module 1 (`mod:slotconsensus`), whose interface
*is* the three inputs, and whose Quiescence is about them. **Not
recommended as the resolution.**

**The class change needed under every option (C1, C2; open, joint).**
Separate from the interface question, F1's two premises have to enter the
class. The proposed form, in the rely style of `MVBATemporal.termination`,
as antecedents rather than `Admissible` content:

* **C1**, in `bounded_termination` and `totality`:
  `∀ i, ¬ byz i → ∀ n, abandoned (r.at' n) i → ∃ V, finalized (r.at' n) i V`.
  This is the same antecedent `SlotConsensusTemporal.termination` already
  has.
* **C2**, in `bounded_termination`, with a datum
  `deadline : slot → time` beside `Δ`:
  `∀ n i, ¬ byz i → participating (r.at' n) i → deadline (S.tag (r.at' n)) ≤ r.clk n + Δ`.
  This is "no start before `D − Δ`", stated over the observable
  `participating`. It is equivalent to the paper's form at the start
  index, and it is implied at every later one. The composition
  discharges it from `OrchestratorSafety.integrity_timing` with
  `deadline s = start_time s + Δ`. The paper keeps this datum out of the
  module: its commented-out "assumed behaviour" block in
  Module 1 (`mod:slotconsensus`) lists it, and the lemmas carry it as "within
  Cadence". That is why it is an antecedent here and not a field of
  `SlotConsensusSafety`.

`ℓ` and `d_tot` stay data. The instance sets them to closed terms,
pinned by `rfl` lemmas in the style of `Lcert_paper`: at `δ = 0` they are
the paper's `5Δ + ℓ_MVBA` and `Δ`.

**Recommendation: A with C1/C2, in one edit of
[Chorus.lean](../Cadence/Chorus.lean) and [Interfaces.lean](../Cadence/Interfaces.lean) and
one re-solve.** Three things ride along in the same edit:

* the **(A-mvba) prose clean-up** that [TODO.md](TODO.md) § Liveness
  leaves for these files' next real edit: Chorus.lean's liveness section,
  and the SlotConsensus obligations row in Interfaces.lean;
* Chorus.lean's (F-justice) prose list, which should name
  `deliver_chunk_assigned` and `broadcast_commitqc_*`
  ([Liveness.md](Liveness.md) §4.3);
* PR #44's Module 3 (`mod:mvba`) Agreement prose edit in Interfaces.lean.

Chorus.lean's header paragraphs on Termination and Quiescence are
rewritten there too. [FallbackReceipt.lean](../Cadence/FallbackReceipt.lean)'s
(A-mvba) mention stays for its own next edit.

#### 6.4.2 The clock and the timing model

The clock belongs to the run, as settled for the MVBA (§6.2.1). A timed
Chorus run is a `TLRun` of the Chorus transition system at the `Mvba`
instance (`atMvba`, [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)).
The time theory is §6.2.2's, cancellative on the theorems, and the
constants are shared. The Chorus schedule is **the MVBA's `Schedule`
plus the deadline `D`**, so the run has one Δ and one δ, not two. The
phase landmarks use the same Δ, because the paper's arm times
`D + Δ` and `D + 2Δ` are stated in the network bound. What each premise
of `Chorus.termination` becomes:

**`FJustice` becomes buffered bounded fairness, with a hop table.** It
covers every justice label except the three phase markers (below) and the
inputs (§6.4.1). It is stated over plain enabledness, as §6.2.4's
`BoundedFair` and the untimed claim's `FJustice` are since R6: every fair
action of the model fires once (`Chorus.justice_enabledMove`), so the
§6.2.4 caveat about `Enabled` is answered in the model. The proposal
family becomes its timed twin, `BoundedFairFamily`: if some
`mvba_propose i v _` stays enabled over the window, one of them fires
within it. The clause,
generic in [Timed.lean](../Cadence/Timed.lean), with `gate l` the label's
local gate and `W = max (ref N + hop l) (ref N' + δ)`:

  **(Δδ-justice)** For `N ≤ N'`: suppose that at every index `n ≥ N` with
  `clk n ≤ W` at which `gate l` holds, `l` is enabled, and that
  `gate l` holds at every index `n ≥ N'` with `clk n ≤ W`. Then `l`
  fires with its post-state inside `W`.

With `N = N'` (and `δ ≤ Δ` for a Δ-row) it is §6.2.4's `BoundedFair`.
The gate is a state predicate
that may mention only the acting validator's local state and the phase:
its participation, and the landmark its rule waits for. That checklist
item keeps the clause from absorbing protocol progress. This is F2, and
it is what the paper's buffering sentence says: the message part is due
Δ after it was sent, and the rule fires δ after its gate opens.

The hop table, classified as §6.2.4's is, by what the guard consumes:

| `Δ` (another party's message or certificate) | `δ` (local, or carried by an input already received) |
|---|---|
| `deliver_chunk_assigned` (the proposer's chunk) | `record_chunk`, `vote` (gate: phase past the deadline) |
| `aggregate_fastqc_*` (others' vote signatures) | `commit_sign_*`, `cast_fast_commit` |
| `fb_sign_*` (others' votes and chunks; gate: the fallback arm) | `cast_fallback_vote` |
| `broadcast_commitqc_*` (others' commit votes) | `on_mvba_decide_*`, `mvba_terminate` (the certificates travel inside the decided value, whose `Valid` checks them) |
| `mvba_propose` family (others' fallback votes via `fbcert`; gate: the arm) | `cast_fb_commit` |
| `redisseminate_chunk` (the caster's chunk; removed by R19, F15) | `finalize_commit` |
| `commit_assign_*` (a certificate someone else broadcast) | |

The table has three consequences:

* **Participation.** Every row whose rule is gated (§6.4.1) adds
  participation to its gate.
* **`mvba_propose` is two rules** (corrected by S3, F9 below). This
  bullet first said that one Δ-row suffices, because "with the split hop
  that costs nothing". That holds for the case-(b) trigger, others' fallback
  votes, but not for case (a) (Algorithm 5, line 23 (`line:fb-mvba-propose-fast`)), whose trigger
  is the proposer's own complete fast meta-block: it exists only once the
  FastQCs have arrived, so a Δ-row on it costs a second Δ. The premise
  therefore has the paper's two rules, a Δ-family and a δ-family.
* **The check.** At δ = 0 the table reproduces the paper's timeline term
  for term (§6.4.3), as §6.2.4's did for the MVBA. The MVBA leg's own
  finding C16 (N3, PR #44) questions a δ-row that consumes another
  party's certificate: the MVBA's `decide`. The two δ-rows above that
  read certificates, the decision handlers, rest on a different argument:
  the certificates travel inside the decided value. If step 5b
  reclassifies `decide`, re-check these two rows against that argument.

**The table as built** (S2, 2026-09-30; `Chorus.hop`, `Chorus.gate` and
`Chorus.Owed` in [Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)).
Each row has a bound, a gate, and a condition under which it is owed at all.

| row | bound | gate | owed when |
|---|---|---|---|
| `deliver_chunk_assigned i j m` | `Δ` | none (since R19: the send was `propose`) | always (the proposer is correct by the guard) |
| `record_chunk` | `δ` | none | always |
| `vote i` | `δ` | `Active i`, phase past `D` | always |
| `aggregate_fastqc_* … q` | `Δ` | none | the quorum `q` is correct |
| `commit_sign_* i …`, `cast_fast_commit i` | `δ` | `Active i` | always |
| `broadcast_commitqc_* c … q` | `Δ` | `Active c` | the quorum `q` is correct |
| `fb_sign_pos i j m q qc` | `Δ` | `Active i`, the fallback arm | `q` and `qc` correct, and a correct supermajority has cast its votes |
| `fb_sign_neg i j qv` | `Δ` | `Active i`, the fallback arm | `qv` correct |
| `cast_fallback_vote i` | `δ` | `Active i`, the fallback arm | always |
| `mvba_propose i v _` on `FBCert` (`propose`, one family per `(i, v)`) | `Δ` | `Active i`, the MVBA arm | `FBCert` from a correct supermajority |
| `mvba_propose i v _` on the fast meta-block (`proposeFast`, one family per `(i, v)`, F9) | `δ` | `Active i`, the MVBA arm | `i`'s own complete fast meta-block |
| `on_mvba_decide_*`, `mvba_terminate` | `δ` | the MVBA arm | always (the guard reads `i`'s own decision) |
| `redisseminate_chunk k i j m` (removed by R19: inside `fb_sign_pos`, F15) | `Δ` | `Active k` | `k` signed a positive fallback entry for `(j, m)` (F8), or `k` has itself decided and `f+1` correct validators hold their chunk under `(j, m)` (F11) |
| `cast_fb_commit i v` (since R19: `TimedJustice.fbCommit`, split at its trigger) | `Δ` (was `δ`) | `fbCommitGate`: `Active i`, `i`'s own decision of `v` only, `mvba_complete` | (the gate; was: `i` has itself decided) |
| `mvba_avail_ready i v` (the family `avail`) | `Δ` (was `δ`, R19) | none | `i` holds `v` |
| `commit_assign_* i j …` | `Δ` | `Active i` | a correct validator finalized with that entry, or the fallback commit certificate from correct voters over the decided entry |
| `finalize_commit i` | `δ` | `Active i` | always |

The reconciliation with the labels since R5: the Byzantine splits
(`byz_broadcast_commitqc_*`, `byz_redisseminate_chunk`) are unfair and have
no row, and the honest collector and re-disseminator are rows at their
correct sender. `hop_isSome_iff` pins that the table covers exactly the fair
labels that are not phase markers. `mvba_propose`'s gate is the MVBA arm,
not the fallback arm, because the case-(a) trigger waits for it and §6.4.3's
timeline reaches the proposals only after it.

**The decision-handler re-check.** Step 5b made the MVBA's `decide` a
network hop ((N3), `Mvba.BoundedJustice.decisions`). The two δ-rows
**stand**. Each handler fires on the acting validator's *own* MVBA decision,
which is a local output, and the certificates its bridge check reads hold at
that decision by `ValidBridge`'s completeness. The transfer (N3) is about is
the transfer of a decision to a validator that did not decide first, which
is the MVBA's own `decide` step. Its cost, `Δ + ρ`, is inside `ℓ_MVBA`.

**Two findings against the table above, both built into the statement.**

* **F5: the paper owes delivery only between correct validators**
  (Proposition 5 (`prop:chorus-finalization-time`)'s proof: "every message between correct
  validators is delivered within Δ"). The model's network relations hold
  from a message's first delivery to anyone, a Byzantine sender's included.
  So a Δ-row that consumes a Byzantine validator's message would owe a
  delivery the paper does not promise, since a Byzantine voter may send to
  some validators only. That is the MVBA's C16 finding, on Chorus's side.
  Each Δ-row is therefore owed only when the messages it consumes came from
  correct senders (the last column). Both untimed `FJustice` definitions,
  Chorus's and the MVBA's, have the same shape, and the finding applies to
  both. **Closed in R8** (2026-09-30): both untimed `FJustice`s take the same
  owed-conditions (`Chorus.Owed`, `Mvba.Owed`), and re-proving
  `Chorus.termination` against them found F7 and F8 (below).
* **F6: `cast_fb_commit` reads a shared flag.** Its guard is
  `mvba_complete`, which the first validator to decide sets. The paper's
  rule fires on the voter's own decision (Algorithm 5, line 41 (`line:fb-commitvote`)). As a δ-row
  with no condition it would owe a vote from a validator whose MVBA has not
  decided. The row is owed once the voter itself has decided.

**The decision handoff (C15): the design** (R8, 2026-09-30, written before
the build). The supplement's paragraph "Decision output and handoff" (Supplement,
Section 1.2 (`subsec:mvba-protocol`)) says
four things: `decide(x, CommitQC)` outputs the certificate; Chorus broadcasts
it; a correct validator that receives a valid one re-broadcasts it and
finalizes; and the MVBA accepts a transferred `CommitQC` of any view
(Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)). Until R8 the MVBA's `decide` (its
transferred-certificate handler) was an *internal* MVBA step, taken by the
oracle `mvba_step`, so its timing was assumed inside `T.Admissible`
(`Mvba.BoundedJustice.decisions`). The design makes the transfer the
caller's, so that Chorus's own rows carry it.

* **(a) Where the relay lives.** A new Chorus action
  `accept_mvba_commitqc i c mvba_next` in [Chorus.lean](../Cadence/Chorus.lean),
  beside `mvba_propose`: a correct validator hands a valid certificate `c`
  to its MVBA through the contract's new input `mvba.accept mvba_st i c
  mvba_next`, and sets `mvba_st := mvba_next`. It reads no network relation
  at all. What stands for the certificate on the wire is the MVBA's own
  monotone record that it exists (`mvba.certifies`, read inside
  `mvba.accept`), so the monotone-network contract of
  [ChorusDesign.md](ChorusDesign.md) §3.1.1 is untouched: the only other
  guards are `¬ is_byz i` and the fired-once record below. **Chorus's
  broadcast is folded into the decision output.** A correct validator's
  decision counts as its broadcast of the certificate that commits it:
  that is the supplement's "upon receiving this output, Chorus broadcasts",
  with its instantaneous local computation. A separate broadcast rule,
  gated on participation, would let a validator decide, finalize on the
  fast path and abandon before it hands off, which the paper's
  instantaneous reaction rules out, and the MVBA would then wait for a
  certificate nobody sends. The re-broadcast needs no step either: once
  `i` has accepted, it has decided, so it is a sender in turn. The
  finalization the supplement attaches to the certificate is **not**
  modelled yet: the model has the main body's fallback commit round only. At
  the target the supplement adds the route, and R16 models it
  ([PaperAlignment.md](PaperAlignment.md) §5.7).
* **(b) The contract change** ([Interfaces.lean](../Cadence/Interfaces.lean),
  `MVBASafety`, additions only, first-order):
  * `certifies st c v`: `c` is a valid commitment proof for `v` at `st`;
  * `decided_certified`: a correct party's decision has a valid
    certificate — **decide exposes its certificate**;
  * the input `accept st p c st'`, with `accept_trans`;
  * `accept_effect`: accepting a valid certificate for `v` decides `v`,
    and `accept_enabled`: a correct party that has proposed, is not
    abandoned and has not decided can accept any valid certificate — **a
    transferred valid certificate is accepted**, in the rely form (the
    caller transfers; the MVBA accepts).

  `Mvba.mvbaSafety` proves them: `certifies (.commitqc w e) v` is
  `v = e ∧ msg_commitqc w e`, `accept` on `.commitqc w e` is the model's
  `decide p w e`, and `decided_certified` is the existing
  `reachable_decided_backed`. `Mvba.Msg` gains the constructor `commitqc`
  (sent by no MVBA party: `Sent` is `False` on it). **At the instance,
  `decide` becomes an input** (`Label.isInput`), so `mvbaSafety.step`, and
  with it Chorus's oracle `mvba_step`, no longer takes it: in the composed
  system an MVBA decides on a transferred certificate only when Chorus
  hands it over. `decided_certified`, `accept_effect` and `accept_enabled`
  are liveness facts and are withheld from the solver
  (`veil_smt_ignore`), so the Chorus cells see two new symbols and
  `accept_trans`. Nothing is weakened; `MVBATemporal` is unchanged. The
  MVBA's own claims change on the caller's side, since the transfer is now
  the caller's: the untimed claim gains the premise (F-relay)
  (`Mvba.FRelay`, a transfer is owed once a correct party has decided on
  the value), the timed `Sync` gains `Mvba.Relayed` (the old `decisions`
  clause, moved out of `BoundedJustice`, verbatim), and `decide` leaves
  the hop table and `Delivers`.
* **(c) The rows, and the derivation.** One row, a family per receiver:
  `accept_mvba_commitqc i _ _` is a `Δ`-row with no gate (it processes a
  message, like `aggregate_fastqc_*`), owed once **a correct validator has
  decided** (its certificate was sent at its decision). The derivation is
  the lemma `Chorus.relayed_of_timedJustice`: for `δ ≤ Δ + ρ` (the paper's
  `δ = 0` included), in every run satisfying `TimedJustice`, every
  projection's timed run satisfies `Mvba.Relayed`. In words: if `decide i
  v e` stayed enabled for `Δ + ρ` after a correct validator decided `e`,
  the relay row would have made `i` decide within `Δ`, which disables it.
  `Chorus.timedMvbaAdmissible_of_rows` is the form a witness uses: the
  MVBA's own three clauses on a projection, plus `TimedJustice`, give
  `TimedMvbaAdmissible` at the system's instance. The untimed twin is
  `Chorus.fRelay_of_fJustice`, which makes `MvbaAdmissible`'s premise set
  exactly the MVBA's own (`Mvba.FJustice ∧ AViewSync ∧ FAvail`) and
  derives the rest.
* **(d) The fired-once guard.** `local_mvba_qc_accepted i`, unset by the
  guard and set by the step, so the step always changes the state and
  `Chorus.justice_enabledMove` keeps holding with one more case. A validator
  that has accepted has decided, so the record never blocks a step that
  is owed.

**F5 closed, and what it needed besides.** Both untimed `FJustice`
definitions take the owed-conditions of the timed rows: Chorus's `Owed`
(moved to [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)), and the
MVBA's correct-sender part of `Delivers` (`Mvba.Owed`, a leader or a quorum
that is correct). Re-proving `Chorus.termination` against them showed
that R7's `Owed` was stricter than the paper's network in two rows, both
places where a correct validator forwards what it received:

* **F7: the fast meta-block travels.** `aggregate_fastqc_*` is also owed
  when a correct validator that cast its fast commit vote holds the FastQC:
  the same rule broadcasts its `FastBlock` (Algorithm 4, line 20 (`line:fast-metablock`)), and a
  correct validator that receives one adopts its FastQCs. The paper's
  finalization-time proof uses exactly this ("that validator held a fast
  meta-block and broadcast it"). Without it the case-(a) proposals would
  owe nothing whenever the FastQC's quorum had Byzantine voters.
* **F8: re-dissemination by the decoder.** `redisseminate_chunk k …` is
  also owed when its correct sender `k` signed a positive fallback entry
  for the root: it decoded the proposal to sign (Algorithm 5, line 12 (`line:fb-redisseminate`)
  sends every validator its chunk). A `FallbackQC`'s correct signer is the
  paper's source of the chunks (Proposition 5 (`prop:chorus-finalization-time`), "by
  `M + 3Δ`").

A third consequence is on the MVBA's untimed premise: (A-viewsync)'s second
clause now names a correct validator's **decision** rather than a commit
certificate, because a certificate the adversary assembled reaches only
whom the adversary chooses, so no transfer of it is owed. The timed model
implies the new clause as it implied the old one (`Mvba.aViewSync_of_sync`).
The proof of `Chorus.termination` no longer takes the commit route on the
late branch: saturation always yields a correct trigger for the MVBA (a
correct fast voter's meta-block, or a correct `FBCert`), and the MVBA arm
finalizes.

**Four findings from S3** (2026-10-01, R11, while proving the milestones;
each is built into the statement in the same PR; F12 was left for a
model session, R12, which closed it). Three are about premises, one about the model.

* **F9: the case-(a) proposal is a local step.** The table had one Δ-row for
  `mvba_propose`, owed on `CorrectFBCert ∨ i`'s own complete fast meta-block.
  In case (a) a correct validator cast its fast commit vote by
  `M + 2Δ + 2δ`, its FastQCs reach every correct validator through
  `aggregate_fastqc_*` (F7) by `M + 3Δ + 2δ`, and only then is the row owed,
  because the trigger is the receiver's local state. A Δ-row from there puts
  the proposals at `M + 4Δ + 2δ`, one Δ beyond the paper's `M + 3Δ`. The
  premise now has the paper's two rules (`TimedJustice.propose`,
  Algorithm 5, line 36 (`line:fb-mvba-propose`), a Δ-family owed on a correct `FBCert`; and
  `TimedJustice.proposeFast`, Algorithm 5, line 23 (`line:fb-mvba-propose-fast`), a δ-family owed
  on the own meta-block), and the proposals are by `M + 3Δ + 3δ`
  (`Chorus.within_all_input`). This raises `ℓ`'s δ-multiple from 8 to 9.
* **F10: a Δ-row costs `max(Δ, δ)`.** With its gate already open
  (`N = N'`), a buffered row's window is `ref N + max(Δ, δ)`; a row without a
  gate is always in this case. At `δ > Δ` every such hop costs `δ`, and
  `5Δ + ℓ_MVBA + 8δ` was then not reachable on the paper's route (a run may
  delay each step to the end of its window). The schedule now has the field
  `Chorus.Schedule.δ_le_Δ`: a local step is no slower than a network hop,
  true at the paper's `δ = 0`. It implies the `δ ≤ Δ + ρ` that
  `relayed_of_timedJustice` takes. `TotalityClaim` never needed it.
* **F11: re-dissemination was owed on the fast path** (found by R10, during
  the witness). `Owed (.redisseminate_chunk k …)` was
  `CorrectChunkQuorum j m ∨ msg_fb_pos_sig k j m`, with gate `Active k`, so
  every active correct validator owed every validator its chunk within Δ of
  a chunk quorum. The paper re-disseminates in two places only: inside the
  fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`), F8's disjunct) and after the
  validator's own MVBA decision (Algorithm 5, line 39 (`line:fb-commit-wait`)). R10's run: `Δ = 1`,
  `δ = 0`, `D = 1`, a fast-path finalization at clock 3, but the row for
  `k = 1` owed and open from clock 0 and due by 1. Both untimed and timed
  premises excluded such paper runs. The chunk-quorum disjunct is now owed
  only once `k` has itself decided. `Chorus.termination` is re-proven
  against it with no model change: `eventually_fbcommit_sig` used the
  disjunct only with `k := i`, the voter, which has decided.
* **F12: the model's fallback commit vote waited under more roots than the
  paper's** (found by R10). The paper waits only under FallbackQC entries:
  "**for each** FallbackQC in B′ with a positive entry ⟨s, j, root⟩: **wait
  until** p_i has received and validated its assigned chunk for root"
  (Algorithm 5, line 38 (`line:fb-commit-foreach`), Algorithm 5, line 39 (`line:fb-commit-wait`)). The model's
  `cast_fb_commit` required
  `∀ J M, is_proposer J → mvba_decided_pos J M → msg_chunk_received i J M`,
  under every decided positive root, FastQC-backed ones included. So the
  model had fewer runs than the paper: the safety claims did not cover a
  paper run in which the vote is cast without that wait, and the liveness
  bound had to pay for a chunk the paper does not wait for. **Closed in
  R12** (2026-10-01), see "F12 closed" below.

**F12 closed** (R12). The guard now reads like the paper line:

| | `cast_fb_commit`'s DA wait |
|---|---|
| paper | for each FallbackQC in B′ with a positive entry ⟨s, j, root⟩: wait until p_i has received and validated its assigned chunk for root |
| before | `∀ J M, is_proposer J → mvba_decided_pos J M → msg_chunk_received i J M` |
| after | `∀ J M, is_proposer J → mvba_decided_pos J M → vote_quorum_pos J M ∨ msg_chunk_received i J M` |

The decided entry vector does not record which certificate holds an
entry. The decision handlers check that one does
(`vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)`). So the model reads
"held by a FallbackQC" as "no positive FastQC for it exists". Both network
reads are positive, the antecedent is the frozen decided-vector read
already documented ([ChorusDesign.md](ChorusDesign.md) §3.1), and the
action keeps its one parameter, `i`. No invariant was needed:
none mentions the DA wait, and all 103 of the action's cells re-solved
cold. The `#veil_status Chorus` count was written down before the build as
unchanged, `101 + 46 × (101 + 1) + 47 = 4840`, and it is. `Chorus.termination`
is re-proven with a simpler argument (`eventually_fbcommit_sig`): under a
FastQC root there is nothing to wait for, and under a FallbackQC root one
of its `f+1` signers is correct and owes the re-dissemination (F8's
disjunct). Timeline, Totality and Witness needed no edit.

Two findings from the fix, both reported, neither acted on:

* **F13: where a root has both certificates, the model does not wait and
  the paper may.** If B′ carries a FallbackQC for `(j, m)` while a
  positive FastQC for `(j, m)` also exists (the MVBA proposer held only
  the former), the paper's validator waits for its chunk and the model's
  does not. For safety this only adds runs. For the timed claim it leaves
  a residual: in such a run the δ-row of `cast_fb_commit` is owed from the
  decision, while the paper's validator may wait for its chunk until the
  correct FallbackQC signer's re-dissemination arrives (a Δ-row). The run
  then violates the premise, and the claim says nothing about it. Closing
  this exactly needs the certificate kind in the MVBA's value (an entry
  vector that says FastQC or FallbackQC), which changes the value type
  `System.lean` instantiates. That is outside this session's scope.
  **Proposal:** carry the certificate kind in the entry vector in the
  composition leg, or accept the residual as stated here. *Re-scoped by
  R13:* F13 is an artefact of the hybrid target. At `48cac9a` each
  validator's own `B′` carries its certificates, and the realignment closes
  F13 exactly ([PaperAlignment.md](PaperAlignment.md) §5.5, §8 R15).
  **Closed in R15**, see "F13 closed" below.
* **F14: re-dissemination's "decided" owed-disjunct was used by no proof,
  and it was stronger than the paper.** `Owed (.redisseminate_chunk k i j
  m)` was `(CorrectChunkQuorum j m ∧ k has decided) ∨ msg_fb_pos_sig k j
  m`. The left disjunct was used only by the old `eventually_fbcommit_sig`,
  for FastQC roots, which no longer need a chunk. The paper's decided
  validator broadcasts only *its own* chunk, and only under FallbackQC
  entries (Algorithm 5, line 39 (`line:fb-commit-wait`)). It does not send other validators their
  chunks. So the disjunct owed steps that paper runs need not take.
  **Closed in R14**, see "F14 closed" below.

**F14 closed** (R14). The row now owes exactly what the paper sends:

| | `Owed (.redisseminate_chunk k i j m)` |
|---|---|
| paper | the fallback-entry rule re-encodes and sends each validator its assigned chunk (Algorithm 5, line 12 (`line:fb-redisseminate`)); a decided validator broadcasts only its own chunk (Algorithm 5, line 39 (`line:fb-commit-wait`)) |
| before | `(CorrectChunkQuorum j m ∧ ∃ v, mvba.decided k v) ∨ msg_fb_pos_sig k j m` |
| after | `msg_fb_pos_sig k j m` |

`FJustice` and `TimedJustice` are weaker (fewer obligations), and
`CorrectChunkQuorum`, which only the dropped disjunct used, is gone. No Veil
statement moved: `Owed` is a premise of the run-level theorems, not part of
the model. `eventually_fbcommit_sig` used only F8's disjunct, the FallbackQC
signer's own positive entry, and is unchanged up to the disjunction's
injection. `Chorus.termination`, the timeline milestones, `Chorus.totality`
and the three witness theorems re-checked in plain Lean, all at
`[propext, Classical.choice, Quot.sound]`.

**F13 closed** (R15). The MVBA's value is now the meta-block
representation, each validator decides its own, and the wait runs under
exactly the FallbackQC entries of the validator's own `B′`
([PaperAlignment.md](PaperAlignment.md) §8.1 (d)):

| | `cast_fb_commit`'s DA wait |
|---|---|
| paper | upon `MVBA[s].decide(B′)`: for each FallbackQC in B′ with a positive entry ⟨s, j, root⟩: wait until p_i has received and validated its assigned chunk for root (Algorithm 5, line 37 (`line:fb-mvba-decide`) to Algorithm 5, line 39 (`line:fb-commit-wait`)) |
| before | `∀ J M, is_proposer J → mvba_decided_pos J M → vote_quorum_pos J M ∨ msg_chunk_received i J M` |
| after | `cast_fb_commit i v`: `mvba.decided mvba_st i v` and `∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → msg_chunk_received i J M` |

A root that is FastQC-certified somewhere but FallbackQC-certified in the
validator's `B′` is now waited for, as in the paper, so the residual is
gone. `Owed (.cast_fb_commit i v)` is "`i` decided `v` and no other
representation" (P11 of [PaperAlignment.md](PaperAlignment.md) §6), and
the row stays a δ-row: its chunk is delivered by `redisseminate_chunk`'s
Δ-row from the correct FallbackQC signer, so the premise owes the vote δ
after the wait is over, when the paper's validator casts it.
`eventually_fbcommit_sig` reads the FallbackQC entries of the validator's
own decision; the fallback quorum is `ValidBridge`'s completeness, and the
correct signer's own signature gives the proposer's root and the decode
quorum. The `#veil_status Chorus` count is unchanged, `47 · 102 + 46 = 4840`.

**F15: re-dissemination is gated at delivery, so (Δ-avail) is not derivable**
(found by R18, 2026-10-02, while deriving the MVBA's (Δ-avail) from the
availability row; **closed in R19**, see "F15 closed" below). The paper sends a validator's chunk inside the fallback-entry
rule (Algorithm 5, line 12 (`line:fb-redisseminate`)), while the signer is
active, so the chunk is in flight from the signature on and is delivered
within `Δ` after GST whatever the signer does next. The model splits the send
off: `redisseminate_chunk k i j m` is a separate step, and for a correct `k`
it requires `participating k ∧ ¬ abandoned k` *at delivery*; its row's gate
is `Active k`. An abandonment between signing and delivery therefore drops a
message the paper has already sent. **Counterexample run.** The FallbackQC
for `(j, m)` has exactly one correct signer `k`, and `j` is Byzantine. `k`
signs at `D + Δ`, then receives another validator's fast commit certificate,
finalizes and abandons, all within `Δ` of signing (C1 permits it). A correct
`i` later accepts an MVBA value with that FallbackQC entry. Its chunk wait
can never be met, so `mvba_avail_ready` stays disabled and `Mvba.AvailWithin`
fails, while `TimedJustice` holds: `k`'s row lapsed when its gate closed. So
`timedMvbaAdmissible_of_rows` cannot drop (Δ-avail) for every run, and
`TimedMvbaAdmissible` still assumes it (P12's ledger line). It is our
divergence from the paper, not a finding about the paper. The timed
termination proof does not meet it: on its late branch nobody has abandoned
before the votes. Two designs for R19:

* **(a) a guard change**: the correct sender's `redisseminate_chunk` is
  guarded on its own `msg_fb_pos_sig k j m` (the send happened) instead of
  `Active k`. Small, but it lets a send fire *after* the abandonment, which
  conflicts with the Quiescence half of S5's `SlotConsensusTemporal`
  instance;
* **(b) one atomic step**: `fb_sign_pos` also delivers the chunk to every
  receiver (a bulk update), exactly as the paper's single rule does. This
  keeps Quiescence, and `redisseminate_chunk`'s correct-sender row becomes
  unnecessary.

The derivation needs one more fact, a property of the timing model: the
availability window covers a Chorus network hop and a local step,
`Δ + δ ≤ Δ_sync` (the chunk by `Δ` after the acceptance's reference time, the
report `δ` later). It belongs in the schedule, as a field like `δ_le_Δ`, not
as a lemma hypothesis. That is a statement change (`Chorus.Schedule` or
`Mvba.Schedule`), so it goes to R19 too, and with it the witness's schedule:
`Mvba.Schedule.fixedNat` has `Δ_sync = 0`.

**F15: the design** (R19, 2026-10-02, written before the build).

*(a) Where the paper re-disseminates.* At two points, both in Algorithm 5
(`alg:fallback`):

| paper | the model today | the model after R19 |
|---|---|---|
| Inside the fallback-entry rule. Its guard is "upon local time reaches `s.deadline + Δ`, at least `2f+1` valid Vote messages have been received, and `pathVote = none`" (Algorithm 5, line 7 (`line:fb-pathvote-guard`)). Then "for each proposer `p_j` … with `Ev(j) = ⊥`" (Algorithm 5, line 8 (`line:fb-cast-entry`)): "if collected `f+1` valid positive votes for `(p_j, ρ)` … and `isDecoded(ρ)`", it signs the positive entry (Algorithm 5, line 11 (`line:fb-positive-entry`)) and then "re-encode proposal; **send** each validator its assigned chunk for `ρ`" (Algorithm 5, line 12 (`line:fb-redisseminate`)). | Two steps. `fb_sign_pos i j m q qc` signs. `redisseminate_chunk k i j m` later delivers `i`'s chunk, once per receiver, while `k` is active (F15). | **One step.** `fb_sign_pos i j m q qc` signs *and* sends every validator its chunk, as the paper's rule does. |
| After the MVBA decision: "**wait until** `p_i` has received and validated its assigned chunk for `ρ`, then **broadcast** that chunk" (Algorithm 5, line 39 (`line:fb-commit-wait`)). | The wait is `cast_fb_commit`'s guard. The broadcast has no step, because it needs none. `msg_chunk_received i j m` says that `i`'s assigned chunk is on the network, and the decoding threshold `chunk_quorum` counts it from then on, wherever it travels next. Broadcasting it to the others changes no relation. Since F14 no row owes it either. | Unchanged. |

*(b) The fix: one atomic step*, the form R18 called (b). The rule gains
two bulk updates, each over a single-capital index:

```
action fb_sign_pos (i : node) (j : node) (m : merkle_root) (q qc : nodeset) {
  … the guards, unchanged …
  require ¬ local_fb_entry i j
  msg_fb_pos_sig i j m := true
  local_fb_entry i j := true
  -- Algorithm 5, line 12: re-encode, send each validator its assigned chunk.
  msg_chunk_received I j m := true
  local_chunk_sent i I j m := true
}
```

* **The parameter list stays at five.** The guards are unchanged, since the
  rule already requires `chunk_quorum j m` (`isDecoded`) and `well_encoded m`.
* **No VC is put at risk by the new writes.** No invariant reads
  `msg_chunk_received` or `local_chunk_sent` on its left-hand side. The
  three that mention `chunk_quorum` inside a negation
  (`progress_fallback_signing` and its kin) see no change in its truth
  value, because the rule's own guard already has `chunk_quorum j m`.
* **Quiescence is kept.** Every send of the rule happens inside the gated
  step (`participating i ∧ ¬ abandoned i`). `local_chunk_sent i I j m` is
  the per-sender send record, and S5's one-step Quiescence can read it as
  the `sent` observable for chunks, since `msg_chunk_received` has no
  sender index. After an abandonment, `i` sends nothing.
* **The fired-once guard is kept.** `fb_sign_pos` keeps `¬ local_fb_entry
  i j`, so its sends happen once. `Chorus.justice_enabledMove` loses a
  case and gains none.

*A consequence for the timed premise, which the design fixes.* After the
atomic step, `msg_chunk_received i j m` holds from the correct signer's
send. That is the convention every broadcast relation of the model already
follows: a relation holds from the send, and the *reader's* row is a
`Δ`-row that times the delivery. Two post-deadline rules read a validator's
own re-disseminated chunk. Today both are `δ`-rows, because until now the
chunk arrived through its own `Δ`-row:

* `cast_fb_commit i v`, the DA wait (Algorithm 5, line 39 (`line:fb-commit-wait`)), and
* `mvba_avail_ready i v`, the availability report.

Kept as `δ`-rows, they would owe their step `δ` after the decision or the
acceptance, even in a paper run whose chunk is still in flight. After GST
that is up to `Δ` after the send, and the MVBA can decide sooner than that
when every other message is fast. Such paper runs would then violate
`TimedJustice`, the F11 kind of gap. So both rows become `Δ`-rows, by
the hop table's own classification (they consume another party's
message):

* **`mvba_avail_ready`**: the `avail` family's bound goes from `δ` to `Δ`.
  Its owed-condition is unchanged (`i` holds `v`), and so is its gate (none).
* **`cast_fb_commit`**: a buffered `Δ`-row, split at its trigger. The
  message part is the chunks, due `Δ` after they were sent. The gate is
  the rule's trigger, "upon `MVBA[s].decide(B′)`" (Algorithm 5, line 37
  (`line:fb-mvba-decide`)): `Active i`, `i`'s own decision of `v` (the only
  one, P11), and the decision landmark `mvba_complete`, which is the model's
  shadow of the decided vector having arrived. The vote is then due by
  `max(chunks sent + Δ, trigger + δ)`, the paper's timing. The row moves out
  of the generic `rows` into its own `TimedJustice` field (`fbCommit`),
  because its owed-condition is now the gate. The untimed `Owed` is
  unchanged. **The gate checklist gains one item**: a rule's gate may name
  the acting validator's own MVBA output that the rule fires upon. That is
  local state, and the clause still says only "the rule fires `δ` after its
  trigger".

Both changes only remove or postpone obligations, so the premise gets
weaker. The bound does not move. On the late branch the chunks are sent by
saturation (`M + 2Δ + 2δ`, `fb_pos_sig_at_cast`), so they are due by
`M + 3Δ + 2δ`, which is before the decision. The vote stays at
`X_v = X_d + 3δ`, and `Lchorus` and `Ltight` are unchanged.

*The alternative, not taken.* The send could happen in the rule with
delivery as a separate step of the network: an in-flight relation written
by `fb_sign_pos`, and an ungated delivery step owed `Δ` after it. That
keeps the readers' rows as they are. But it needs a new relation, a
delivery record for the fired-once guard (`¬ msg_chunk_received` would be a
negative network read), and a kind of step the model does not have: one
taken by the network rather than by a validator. Its Quiescence argument
also rests on a convention, namely which record counts as `sent`. The
atomic step is the paper's rule as written, so the cost lands on two
premise rows instead.

*(c) `redisseminate_chunk` for correct senders is removed.* It stood for
line 12, which now lives inside `fb_sign_pos`. Line 39 needs no step,
by (a). Its `Owed` line, its hop row and its gate go with it, and so does
its untimed fairness row. `byz_redisseminate_chunk` stays: it is the
adversary's capability, which any holder of `f+1` chunks has, and it is
unfair. The proofs that consumed the row read the chunk at the signature
instead, through a first-flip fact proven in plain Lean as
`fb_pos_sig_flip` was: a correct `k` with `msg_fb_pos_sig k j m` has sent
every validator its chunk. No invariant is needed for it. This affects
`eventually_fbcommit_sig`, `within_fb_chunk` and `fAvail_of_fJustice`.
The last one also loses its `ActiveFrom` hypothesis, which existed only
for the signer's gate. That is the untimed face of F15.

*(d) The schedule constraint, and the witness.* The derivation of
(Δ-avail) needs exactly the following:

* A correct `i` accepts `v`. Then `v`'s FallbackQC entries are certified on
  the network (`ValidBridge` at a held value), each has a correct signer,
  and by (c) each signer has already sent `i` its chunk.
* So the `avail` row is owed and enabled from the acceptance on, and it
  fires within `max(Δ, δ) = Δ` (`δ_le_Δ`).

What is used is therefore **`Δ ≤ Δ_sync`**, not `Δ + δ ≤ Δ_sync`. The
`+ δ` belongs to a reading in which the chunk arrives through its own
`Δ`-row and the report then adds `δ`, which the atomic step retires.
**Decided at review:** the field

```
/-- **The MVBA's availability window covers one Chorus network hop**:
`Δ ≤ Δ_sync`. … -/
Δ_le_Δsync : mvba.Δ ≤ mvba.Δsync
```

beside `δ_le_Δ` in `Chorus.Schedule`
([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)). The Chorus
schedule composes the MVBA's, and the constraint relates the two layers, so
it belongs to the composing layer and not to `Mvba.Schedule`. R18's
`Δ + δ ≤ Δ_sync` implies it, and the two coincide at the paper's `δ = 0`.
The design review also extends the gate checklist by one item: a gate may
name the acting validator's own MVBA output that its rule fires upon.

The witness then needs `Δ_sync ≥ Δ = 1`. **Decided at review:** the
Chorus witness overrides `Δsync := 1` in its own schedule, and
`Mvba.Schedule.fixedNat` and the MVBA's witness stay untouched. So
`Mvba.Witness.ell = 24` cannot move. (At `Δ_sync = 1` the supplement's
timeout `T = 4Δ + max{Δ, Δ_sync}` is still `5`, and the ramp holds,
`Lcert 1 0 1 = 4 < 5`.)

`timedMvbaAdmissible_of_rows` then takes only the MVBA's own two clauses,
(Δ-justice) and (T-timer), and derives (Δ-avail) and the handoff from
`TimedJustice` and the schedule. The new lemma is
`Chorus.availWithin_of_timedJustice`, the twin of
`relayed_of_timedJustice`. No interim conditional derivation from R18
exists to remove.

*(e) The pin.* One action leaves, and no invariant or step property is
added: `A = 48`, `I = 100`, `S = 1`, so `#veil_status Chorus` is
`(A + 1)(I + S) + A = 49 · 101 + 48 = 4997` (from `5099`, one action's
`101 + 1` cells and its does-not-throw cell). Mvba `1507` and
FallbackReceipt `220` are unchanged. The Mvba model file does not change,
so NoLock needs no mirror.

*(f) The proposer's dissemination, the same shape* (added at the design
review: a gap of F15's shape is closed in the same re-solve, not parked).
`deliver_chunk_assigned i j m` required `participating j ∧ ¬ abandoned j`
at delivery. Algorithm 2 (`alg:proposer-dissemination`) sends every chunk in
the proposing step itself, in the `send` of its "for each validator `p_r`"
loop. So the model could not deliver a correct proposer's chunks once the
proposer had abandoned, while the paper's are in flight from the proposal
on. The safety claims therefore covered a different set of runs from the
paper's. The fix needs no new relation and no new kind of step:

| | `deliver_chunk_assigned i j m` |
|---|---|
| paper | upon `propose`: … for each validator `p_r`: send `p_r` its chunk (Algorithm 2 (`alg:proposer-dissemination`)) |
| before | `¬ is_byz j`, `participating j`, `¬ abandoned j`, `msg_proposer_signed j m`, `¬ local_chunk_sent j i j m` |
| after | `¬ is_byz j`, `msg_proposer_signed j m`, `¬ local_chunk_sent j i j m` |

* **The send is `propose`.** It is gated on participation and is the
  paper's proposing step. Its record is `msg_proposer_signed j m`, which
  for a correct `j` is written only there, so the guard that remains reads
  exactly that "the chunk was sent". The delivery stays a step, so
  `record_chunk`'s pre-deadline timing is unchanged.
* **Quiescence: a delivery of an earlier send is not a new send.** The
  proposer's `sent` record for its chunks is the proposal, which the gated
  `propose` writes. A later delivery writes the receiver's
  `msg_chunk_received` and the step's fired-once record, and sends
  nothing.
* **Its row.** It is still the `Δ`-row it was, owed always (the proposer is
  correct by the guard). Its gate `Active j` is dropped, so the delivery
  is due `Δ` after the send whatever the proposer does next. That
  *strengthens* the premise in one place, since the row is now owed after
  the proposer abandons. The paper's network promises exactly that: the
  message was sent between correct validators. No invariant reads the participation
  relations against chunk delivery, and the pin is unchanged by it.

**F15 closed** (R19, 2026-10-02). Built as designed, with the review's
decisions:

| | the fallback-entry rule's re-dissemination |
|---|---|
| paper | "re-encode proposal; send each validator its assigned chunk for `ρ`" inside the positive branch of the fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`)) |
| before | a separate step `redisseminate_chunk k i j m`, requiring `participating k ∧ ¬ abandoned k` at delivery |
| after | in `fb_sign_pos i j m q qc` itself: `msg_chunk_received I j m := true`, `local_chunk_sent i I j m := true` |

| | the proposer's dissemination |
|---|---|
| paper | upon `propose`: … for each validator `p_r`: send `p_r` its chunk (Algorithm 2 (`alg:proposer-dissemination`)) |
| before | `deliver_chunk_assigned i j m` required `participating j ∧ ¬ abandoned j` |
| after | the delivery reads the send (`msg_proposer_signed j m`) and nothing of the proposer's later state |

* **The model.** One action fewer; no invariant changed; no manual cell.
  `#veil_status Chorus` **5099 → 4997** (= 49 · 101 + 48), as predicted.
  The family re-solved cold, with an empty proof cache: lake exit 0, 4 978 ✅
  / 0 ❌ / 0 💥 / 0 ⏱, no cache hit, 505 s for the proof family after
  407 s for the model.
* **The premise.** `TimedJustice` has no re-dissemination row any more.
  `cast_fb_commit` and the `avail` family are `Δ`-rows, the first in its own
  field `fbCommit`, split at its trigger `fbCommitGate`. The gate
  checklist ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)'s
  header) admits the actor's own MVBA output. `deliver_chunk_assigned` has
  no gate. The untimed `FJustice` loses the re-dissemination row, and its
  `Owed` loses that line.
* **The schedule.** `Chorus.Schedule.Δ_le_Δsync : mvba.Δ ≤ mvba.Δsync`.
* **(Δ-avail), derived.** `Chorus.availWithin_of_timedJustice`: in every run
  satisfying `TimedJustice` and `ValidBridge`, at every schedule, every
  projection's timed run satisfies `Mvba.AvailWithin`.
  `timedMvbaAdmissible_of_rows` takes only (Δ-justice) and (T-timer) of the
  MVBA. `SyncAtMvba` and `TimedTerminationClaimAtMvba` state the timing
  model and the claim at the system's MVBA with only those two clauses
  assumed, and `Chorus.timed_termination_atMvba` and
  `…_tight_atMvba` are proven over them (`sync_of_syncAtMvba`). The timed
  claim at the system's MVBA therefore assumes no availability fact that
  Chorus provides.
* **The proofs.** The chunk is there from the correct signer's signature on
  (`fb_pos_sig_chunks`, by `record_backed` over `fb_pos_sig_chunks_flip`).
  `eventually_fbcommit_sig` and `fAvail_of_fJustice` read it directly, and
  the latter no longer takes `ActiveFrom`. `within_fb_chunk` is gone, and
  `within_finalized_late` meets the vote's split row with the chunks at
  saturation. The bound is unchanged: `T₀ = M + 4Δ + ℓ_MVBA + 7δ`,
  `Lchorus`, `Ltight`.
* **The witness.** `schC` overrides `Δsync := 1` (`Mvba.Schedule.fixedNat`
  and the MVBA's witness are untouched, and `Mvba.Witness.ell = 24`). Its
  clock-0 re-dissemination case is gone, and
  `timedTermination_premises_satisfiable` states `SyncAtMvba`.

**Expected pins, written before the build.** Chorus: one action and one
state relation, no property: `101 + 46 × (101 + 1) + 47 = 4840` (from
4737). Mvba: the model file does not change (`decide` becomes an input in
[Mvba/Compose.lean](../Cadence/Mvba/Compose.lean) only), so `1507` stays,
and NoLock, which copies the model, needs no mirror. FallbackReceipt:
`220`.

**The phase markers become punctual timers**, leaving the hop table as
the MVBA's `expire_timer` left it. **(P-phase)**, for each landmark
`L ∈ {D, D + Δ, D + 2Δ}` and its marker:

* **(P1) not early**: the marker fires only at a clock `≥ L`;
* **(P2) not late**: its post-phase holds at some index with clock `≤ L`.

Local clocks are synchronized throughout, so the clause holds before GST
too, as (T-timer) does. Termination uses only (P2). (P1) is kept because
it is part of the timing model, and it is what a timed proposal-inclusion
corollary would need: `phase = pre_deadline` up to `D`. The untimed claim
keeps the markers weakly fair (§2.1 of [Liveness.md](Liveness.md)). The
two classifications are separate functions over labels, so
[Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean) is not reshaped by
this.

**What `s.deadline − Δ ≥ GST` becomes.** Today it is
`all_honest_recorded`, the antecedent of proposal inclusion, and the
`on_time` of the contract. It stays exactly that: `on_time` is a state
fact in the fragment, and neither timed target needs it. A timed
corollary would derive it from "a correct proposer proposes at
`D − Δ ≥ GST`" with the deliver-Δ and record-δ rows, before the marker
fires at `D`. That meets a boundary. At δ > 0 a chunk that arrives exactly
at `D` is recorded too late. At δ = 0 it ties with the marker, which
leaves the chunk and the marker at the same instant. So the paper's
premise needs strict delivery or a tie-break. This is a finding for
whoever takes that corollary on, and it is not needed here.

**`MvbaAdmissible` becomes the MVBA's `Admissible`, through a timed
projection.** The untimed premise is "some projection's run satisfies
`Mvba.FJustice ∧ AViewSync ∧ FAvail`". The timed premise is "some
projection `p`, with the clock carried along, has `T.Admissible
p.timedRun`", where `T := Mvba.mvbaTemporal th hqe sch vfin hrot`. It is
stated with the contract's own field and restated nowhere, as
[Liveness.md](Liveness.md) §4.1 asked. The projection is stage 1's
`Component.Projection` plus a clock. Projected state `k` reads the clock
of the composed index at which the MVBA entered it. The projected step
`k → k+1` then carries the post-state clock of the composed step that
took it, which is exactly `FiresWithin`'s convention. The pieces:

* The clock is unbounded because the projection is `Scheduled`.
* `gst` is the composed run's.
* The only transfer the proof needs runs *back*: a decision at projected
  clock `≤ X` is a composed-run decision at clock `≤ X`, because the MVBA
  state is constant between its steps.
* A `boundedFair_iff` in the style of stage 1's `weaklyFair_iff` is
  optional, but recommended. It would let an auditor read the premise at
  either level.

At the `Mvba` instance `T.Admissible` unfolds to "a labelling satisfying
`Sync`". The projection supplies the labelling, so the premise is
`Sync sch p.run` definitionally.

**`ValidBridge` is not timing, and stays exactly as it is.**

**The caller's conditions** are the contract's antecedents (C1, C2, the
class's `SyncParticipation` and "every correct validator participates by
`t`"). Nothing about them goes into `Admissible`.

#### 6.4.3 The route to `ℓ = 5Δ + ℓ_MVBA`

**The case split is the paper's, not `Chorus.termination`'s.** The
untimed proof splits on the progress dichotomy: a commit route, or the
MVBA arm. The paper's timed proof splits on an early finalization instead,
and in the no-finalization branch it sends *every* correct validator
through the MVBA, fast path or not. That is the route to take, for two
reasons:

* The dichotomy's left disjunct would need a timed commit route whose
  bound fits inside the MVBA branch's. That holds only if
  `ℓ_MVBA ≥ Δ + O(δ)`, a fact about the MVBA's number, which the contract
  does not promise.
* The early-finalization split is also what the untimed re-proof needs
  after option A (§6.4.1). The two proofs then share their skeleton.

The dichotomy theorems stay in use as the source of the certified vector.
With `M = max(t, GST)`, the same notation as the paper:

| Paper milestone (Proposition 5 (`prop:chorus-finalization-time`)) | Model links, re-run with deadlines | Rows |
|---|---|---|
| `D ≤ t + Δ` | C2 at each correct start, with (P2) | — |
| by `M + Δ`: first-round votes | `eventually_voted`, then `eventually_quorum_cast` (`voted_implies_cast`) | `vote` δ |
| by `M + 2Δ`: second-round votes | `eventually_saturated` / `eventually_all_saturated` | aggregate Δ, sign/cast δ; `fb_sign_*` Δ, gate `D + Δ ≤ M + 2Δ`; `cast_fallback_vote` δ |
| by `M + 3Δ`: MVBA proposals, fallback chunks | `eventually_complete_fast_metablock`, `eventually_trigger`, `eventually_input`, `certifiedVector` (`ValidBridge` soundness); the chunks sent with each positive fallback signature (`fb_pos_sig_chunks`, F15) | the proposal family Δ, gate `D + 2Δ`; aggregate Δ; the chunks' hop Δ, timed at their reader (`fbCommit`) |
| by `T₀ − Δ = M + 3Δ + ℓ_MVBA`: decision | `T.termination` on the timed projection; `eventually_mvba_complete`, `eventually_fbcommit_sig` | `ℓ_MVBA`; handlers, terminate and cast δ |
| by `T₀`: certificates, finalization | `eventually_fbcommitqc` (a ghost, no hop), `eventually_committed_of_assignable` | `commit_assign_*` Δ, `finalize_commit` δ |

**What "re-run with deadlines" means here** is what it meant in §6.2.7:

* The existing `enabled_*` and `*_effect` lemmas are kept, with the gate
  added to the guards.
* Each `WeaklyFair` step becomes one (Δδ-justice) step, plus a stability
  argument on the window.
* `LRun.eventually_forall` becomes `TLRun.withinFrom_forall`.
* `Chorus.termination` is not consumed, for §6.2.7's reason: an index is
  not a clock reading.
* The stage-4 facts that make guards stable carry over unchanged: the DA
  wait's anti-monotonicity, `mvba_decided_pos_unique` /
  `mvba_decided_pos_neg_excl`, and `decided_persists`.

**Where `ℓ_MVBA` enters.** Only through `T.termination`, with `T` as in
§6.4.2, applied to the projected timed run. Its three antecedents come
from Chorus:

* **Proposals by `t_M = M + 3Δ + O(δ)`**: the proposal row, carried
  through the projection.
* **Validity**: `ValidBridge`'s soundness clause, used once for the one
  certified vector, as in stage 4.
* **No abandonment before `max(t_M, GST) + ℓ_MVBA`**: in the branch where
  nobody finalizes by `T₀ − Δ`, C1 means nobody has abandoned, so the
  forwarding `abandon` has not fired.

The MVBA's bound is then `T.ℓ`, which at the instance is
`Schedule.ℓ sch vfin` by `rfl`. The Chorus bound is stated with `T.ℓ` and
never with the MVBA's constants. The MVBA upgrade (5b, which may refine
`Mvba.BoundedJustice` and `Mvba.hop` after C16) therefore reaches this
leg only through `T`.

**The assembly, and F4.**

* *Case A*: some correct validator finalizes by `T₀ − Δ`. Totality
  (§6.4.4) finalizes everyone by `T₀`. Everyone already participates,
  since all start by `t`.
* *Case B*: nobody finalizes by `T₀ − Δ`. Then nobody has abandoned (C1),
  every gate a validator needs is open until it finalizes, and the table
  above finalizes everyone by `T₀`.

That is `M + 4Δ + ℓ_MVBA + c·δ`, one Δ inside the paper's claim.
**Decided (S4, R18): F4 is confirmed.** The claim is stated and proven at
the paper's `5Δ + ℓ_MVBA` plus the δ-terms (`Chorus.timed_termination`),
and the sharper bound is the named theorem it follows from
(`Chorus.timed_termination_tight`, `M + 4Δ + ℓ_MVBA + 8δ`). The split point
is the fallback commit votes' deadline `M + 3Δ + ℓ_MVBA + 6δ`, one `δ`
before `T₀ − Δ`: case B needs everyone active only until the votes, since
the last two links use the finalizing validator's own gate. No use of the
outer split turned up. The looseness is recorded for the authors as P5 of
[PaperAlignment.md](PaperAlignment.md) §6. "The MVBA tail and the round, as
proven" below has the milestones.

**The milestones as proven** (S3, 2026-10-01,
[Chorus/Timeline.lean](../Cadence/Chorus/Timeline.lean)). Up to the MVBA
proposals, each milestone is a lemma whose statement carries its deadline.
The premises are (Δδ-justice), (P-phase), C2 (for `D ≤ t + Δ`), and the
gate on the window (`ActiveUntil`, from C1 on S4's branch,
`activeUntil_of_not_finalized`). Neither the MVBA's timing nor the bridge
enters before the proposals, except that the proposed vector must be
certified and `Valid` (S4 supplies it from the evidence at saturation).

| milestone | lemma | by | `δ`s |
|---|---|---|---|
| every correct validator participating | `exists_start` | `t` | 0 |
| the deadline | `deadline_le_of_start` + (P2) | `D ≤ t + Δ` | 0 |
| first-round votes, all at one index | `within_voted`, `within_all_voted` | `M + Δ + δ` | 1 |
| a fallback signature per proposer | `within_fb_sig` | `M + 2Δ + δ` | 1 |
| the second-round vote, fast or fallback | `within_cast`, `within_all_saturated` | `M + 2Δ + 2δ` | 2 |
| the MVBA's trigger from correct senders | `correctTrigger_of_saturated` | (the same index) | 2 |
| a correct fast voter's FastQCs, everywhere (F7) | `within_complete_fast_metablock_by` | `M + 3Δ + 2δ` | 2 |
| the proposal on a correct `FBCert` | `within_input_of_fbcert` | `M + 3Δ + 2δ` | 2 |
| the proposal on the own meta-block (F9) | `within_input_of_fast` | `M + 3Δ + 3δ` | 3 |
| every correct validator's proposal | `within_all_input` | `t_M = M + 3Δ + 3δ` | 3 |
| a correct proposer's chunk, delivered and recorded | `within_proposal_recorded` | `max(X, GST) + Δ + δ`, if `< D` | 1 |

The last row is not on the termination path: it is the proposal-inclusion
corollary's first step, with the strict `< D` that §6.4.2's "What
`s.deadline − Δ ≥ GST` becomes" anticipated. The fallback chunks of the
paper's `M + 3Δ` milestone are left to S4, where the fallback commit round
needs them (§6.4.6, the reassessment).

**The MVBA tail and the round, as proven** (S4, 2026-10-02, R18,
[Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean)).
On the branch where no correct validator has finalized by the vote deadline
`X_v`, everyone is active until then (C1, `activeUntil_of_not_finalized`).
With `t_M = M + 3Δ + 3δ` and `X_d = t_M + ℓ_MVBA`:

| milestone | lemma | by | `δ`s |
|---|---|---|---|
| a FallbackQC signer's signature is there at its second-round vote | `fb_pos_sig_flip`, `fb_pos_sig_at_cast` | (saturation, `M + 2Δ + 2δ`) | 2 |
| its chunk sent to every validator with the signature (F8; F15, R19) | `fb_pos_sig_chunks` (was `within_fb_chunk`) | (saturation; the hop due by `M + 3Δ + 2δ`) | 2 |
| every correct validator decides in the MVBA | `within_all_decided` (`T.termination` on the projection) | `X_d` | 3 |
| a correct decision's entries recorded (the handlers) | `within_recorded` | `X_d + δ` | 4 |
| `mvba_complete` (`mvba_terminate`) | `within_complete` | `X_d + 2δ` | 5 |
| each fallback commit vote, under the validator's own `B′` | `within_fbcommit_sig` | `X_v = X_d + 3δ` | 6 |
| a correct fbCommitQC (the honest quorum's votes) | (collapsed in `within_finalized_late`) | `X_v` | 6 |
| every proposer's entry assigned | `within_assigned` | `X_v + Δ` | 6 |
| finalized | `within_finalized`, `within_finalized_late` | `T₀ = M + 4Δ + ℓ_MVBA + 7δ` | 7 |
| the split: early finalizers by totality | `within_finalized_tight` | `X_v + Δ + 2δ = M + 4Δ + ℓ_MVBA + 8δ` | 8 |

`T₀` is the reassessment's expectation, term for term. Five facts of the
proof, each in the file's header:

* **No common `B′`** (P2). Each validator waits and votes under its own
  decision. The handlers run on one correct decision, and the MVBA's
  agreement makes every correct decision's entries the recorded ones
  (`mvba_recorded_entry`, as in the untimed `eventually_mvba_complete`).
* **The chunks precede the decision.** A correct FallbackQC signer signed
  before its second-round vote (`fb_sign_pos`'s guards), so its signature is
  at the saturation index. This is the first-flip fact the reassessment
  asked for. Since R19 (F15) the same step sent every validator its chunk
  (`fb_pos_sig_chunks`), and the chunks' hop is timed at the vote's split
  row.
* **The MVBA tail is the contract's.** `T.termination` on `mvbaTimedRun p`,
  the proposals carried forward (`Projection.timed_forward`), their validity
  the MVBA's own `input_valid`, no abandonment before `t_M + ℓ_MVBA` (the
  branch, with `abandoned_of_mvba_abandoned`), the decision carried back
  (`Projection.timed_back`, `TimedRun.byGstBound_iff`).
* **`0 ≤ ℓ_MVBA`.** `TimedTerminationClaim` is generic in the MVBA contract
  `T`, and a time type may have negative elements. A contract with a negative
  latency would put the decision before the proposals' deadline, and the
  arithmetic of the round fails. The generic theorems take `0 ≤ T.ℓ`. It is
  a hypothesis on the contract instance, not on runs, and the system's MVBA
  has it (`mvbaSchedule_ℓ_nonneg`): `Chorus.timed_termination_atMvba` and
  `Chorus.timed_termination_tight_atMvba` take nothing beyond the MVBA
  instance's own hypotheses. `TimedTerminationClaim` is unchanged.
* **The δ-multiple.** The paper's route, the outer split at `T₀` with
  totality's `Δ + 2δ`, gives `5Δ + ℓ_MVBA + 9δ`, exactly `Lchorus`. So
  `Lchorus` stands as S3 restated it.

#### 6.4.4 `d_tot`-totality

**The route.** A correct validator finalizes at index `n` with clock `t`.
From that point, `local_committed_pos_backed` and
`local_committed_neg_backed` make every proposer's entry `Assignable` at
`n`, and the certificates are monotone. For another correct validator
`j`, `commit_assign_*` is a Δ-row whose network part holds from `n`. Its
gate (participation) opens by `max(t, GST) + Δ`. That comes from
Δ-synchronized participation, since the finalizer started at or before
`t`. Alternatively `j` has already abandoned, and then it has finalized
(C1). So (Δδ-justice) fires each assignment by `max(t, GST) + Δ + δ`, and
`finalize_commit` adds δ: `d_tot = Δ + 2δ`, which is Δ at δ = 0. The
per-proposer assignments run in parallel (`withinFrom_forall`). Their
stability is stage 3's no-invariant argument (§4.5 of
[Liveness.md](Liveness.md), correction 3).

**What it needs beyond termination.** Nothing new of the model. It uses
two things termination's case B does not:

* `SyncParticipation`. Termination's case A calls totality when everyone
  already participates, so the termination proof uses the gate-open form
  directly.
* The backing invariants.

It needs *less* than the paper's proof in one respect, and that is worth
stating plainly. The paper's totality proof spends most of its length on
recovery: chunks and decryption shares arriving in time for
`recoverProposals` (Algorithm 6, line 14 (`line:da-recover-slot`)). The model's `finalized`
is the committed entry vector (`pvector := slot × (node → Option
merkle_root)`, [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean)), and
payload recovery is not part of it. So that half of the paper's argument
has no model counterpart. That is the existing granularity of the
fragment, not something this leg introduces. The ledger should say it,
because an auditor comparing the proofs will notice the difference.

**The form to prove.** A generic lemma with the participation tolerance
as a parameter: under `d`-synchronized participation, the latency is
`max(Δ, d) + 2δ`. The class field is its instance at `d = Δ`. §6.4.6 says
why the parameter matters.

**Proven** (S3, 2026-10-01, [Chorus/Totality.lean](../Cadence/Chorus/Totality.lean)).
`Chorus.totality` is `TotalityClaim sch d` at every schedule and tolerance,
over finitely many validators, by exactly the route above: the assignments
by `max(c, GST) + max(Δ, d) + δ` (`within_assigned`), the finalization a
further `δ` (`within_finalized`). The latency is `Ltot` with no slack.
`Chorus.totality_paper` is the paper's `d_tot = Δ` at `δ = 0` and `d = Δ`.
The proof uses neither `δ ≤ Δ` nor the phase timers nor the MVBA nor the
bridge. One fact it needed that the model does not export is
`committed_participating`: a finalizer participates, since `finalize_commit`
is gated (the start of the finalizer's synchronized-participation window).

#### 6.4.5 The premises are jointly satisfiable

*The premises of the three Chorus liveness claims and of the contract
instance — each one's role, why it is plausible, its witness and where it
is used — are [Premises.md](Premises.md). This section is the detail
behind their joint satisfiability: the witness theorems, the devices that
make the premises that are not obviously compatible hold together, and
the model.*

The claims are `Chorus.termination` (untimed), `TotalityClaim` (proven as
`Chorus.totality`) and `TimedTerminationClaim` (proven as
`Chorus.timed_termination`, at the system's MVBA
`Chorus.timed_termination_atMvba`). One model satisfies every premise of
all three. It is [Cadence/Chorus/Witness.lean](../Cadence/Chorus/Witness.lean),
and the three theorems that say so, each pinned at the standard three
axioms, are:

* `Chorus.termination_premises_satisfiable`: some instance and run meet
  every premise of `Chorus.termination`. That is its hypotheses, the
  assumptions of the system's configuration `chorusTheory`, `FJustice`
  with its owed-conditions and its families, `MvbaAdmissible`,
  `ValidBridge`, and the caller's two.
* `Chorus.timedTermination_premises_satisfiable`: the same for the timed
  claim at the system's MVBA, `TimedTerminationClaimAtMvba`. That is
  `Mvba.mvbaTemporal`'s instance hypotheses, the schedule, `SyncAtMvba`
  (whose MVBA premise is the MVBA's own two clauses), `ValidBridge`, and the
  caller's four. The witness file also applies
  `Chorus.timed_termination_atMvba` to the run (an `example`), so the build
  checks that this premise set is the proven claim's.
* `Chorus.totality_premises_satisfiable`: the same for `TotalityClaim`, at
  the contract's tolerance `d = Δ`, together with the claim's antecedent: a
  correct validator finalizes.

Each states the premises only, never a conclusion. All three are stated at
the family `Chorus.termination` is proven at (`byzNodeSetFin n f`, every
`n = 3f + 1`) and at `chorusTheory`, so they speak about the instance the
proofs use. The contract instance proves more: `Chorus.admissible_exists`
gives an admissible run from every initial state of every configuration
meeting the instance's hypotheses — the run in which every proposer stays
silent, which needs the slot to have a proposer
([Premises.md](Premises.md) §2.10).

**The premises that need the model.** Four are obvious alone and not
obviously compatible with the rest.

* **`TimedJustice`.** The families quantify over every value, and the rows
  share one clock, so with `δ = 0` a `δ`-row enabled at `N` must fire
  before the clock moves. §6.3.1's device discharges it: the clock
  advances only where no row is enabled, and where one is, its gate closes
  inside its window.
* **`FJustice`**, for the timed row's reason. In the idle tail no fair
  label is enabled at all, since every fair action fires once
  (`Chorus.justice_enabledMove`, §6.4.7).
* **`MvbaAdmissible`, and the timed `MvbaOwnTiming`.** Chorus's own steps
  drive the MVBA's inputs (here `abandon`), and the projection needs the
  MVBA to be stepped infinitely often without any row becoming enabled.
  The run's MVBA is quiet: its projection is the abandonments plus the
  environment's availability marks, the quiet run of
  `Mvba.admissible_exists`.
* **`ValidBridge`.** It fixes the MVBA theory's `valid` against Chorus's
  network at every index, in both directions. With `valid := (· = v⋆)`,
  `v⋆` giving the proposer its root held by a FastQC and everyone else
  nothing, soundness holds because `v⋆` is the only representation that
  passes the certificate check at any index
  (`Chorus.Witness.certified_eq`). A non-proposer can have no entry. The
  proposer's entry cannot be negative, since no negative FastQC and no
  `FBCert` ever exist, and for the same reason it cannot be held by a
  FallbackQC. Completeness holds because nobody decides in the MVBA.

What an auditor comparing proofs should know besides: the model's
`finalized` is the committed entry vector, so the paper's payload recovery
(Algorithm 6, line 14 (`line:da-recover-slot`)) has no counterpart in any
of the claims (§6.4.4).

**The model** ([Chorus/Witness.lean](../Cadence/Chorus/Witness.lean)'s
header has the index table). The instance as above; the MVBA's values are
entry vectors over one root, `Unit`. One run serves all three claims, and
the untimed one forgets its clock:

* **Clock 0.** The three correct validators participate. The proposer
  proposes, its chunk reaches all four validators, and the three correct
  ones record it.
* **Clock 1 (`D`).** The deadline marker fires. Everyone votes, forms the
  FastQC, signs and casts its fast commit vote, broadcasts the commit
  certificate, commits the proposer's entry and finalizes, all on the fast
  path. Then everyone abandons, as C1 permits.
* **Clocks 2 and 3.** The fallback-arm and MVBA-arm markers fire on a run
  in which nobody is active any more. So nobody proposes to the MVBA, which
  stays quiet. Its projection is the abandonments plus the environment's
  availability marks, the quiet run of `Mvba.admissible_exists`
  ([Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean): `Mvba.Quiet`,
  `Mvba.not_enabled_of_quiet`, `Mvba.boundedJustice_of_quiet`).
* **The tail** repeats the MVBA's availability mark, a step that changes
  nothing, one clock unit per step.

Bounds are upper bounds, so this eager run is one the paper's protocol
produces. Nobody sends anything the paper's rules would not. The clock
advances only at four plateau ends, and at none of them is a row enabled
(the availability report aside, which nobody owes). Until R19 the first
one, the end of clock 0, had re-dissemination enabled, which needed an
argument of its own; since F15 re-dissemination happens only inside a
positive fallback signature, and nobody signs one. Every timed row
therefore holds with its antecedent false. Both proven claims also apply to the run
(`example`s in the file), which checks that it lives at their instance
regime.

**What the model found: F11, re-dissemination off the fallback path.**
The first version of the run had validators 1 and 2 re-disseminate the
proposer's chunk at clock 0. The model's `redisseminate_chunk` has no
fallback-path guard, and its row was owed whenever `f+1` correct validators
held the chunk (`CorrectChunkQuorum`), with only `Active k` as its gate. So
`TimedJustice` obliged every active correct validator to re-disseminate
within `Δ`, on the fast path too. The paper re-disseminates only on the
fallback path: inside the fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`)) and
in the fallback commit round's wait (Algorithm 5, line 39 (`line:fb-commit-wait`)). **Counterexample**
(`Δ = 1`, `δ = 0`, `D = 1`): a fast-path run whose messages take their full
`Δ` (FastQCs at 2, finalization and abandonment at 3) leaves the row for
validator 1 owed, enabled and gated open from clock 0 to clock 1. It must
fire by clock 1, and the paper's validator never sends it. Such paper runs
violated the premise, so both timed claims said nothing about them. A forced
re-delivery could even change outcomes: a chunk arriving before the
deadline turns a negative vote entry positive. The untimed `FJustice` had
the same gap for a validator that stays active. **Fixed in R11**
(`bd887c5`): the row is owed on the fallback signer's own positive entry
(F8), or once the sender has itself decided in the MVBA and the chunk is
decodable from correct holders. `Chorus.termination` was re-proven against
it. The witness needed no change, because its proof never used the
owed-condition; it only drops the forced re-dissemination steps.

**A second run, through the MVBA arm** (recommended, not required). This
run satisfies the proposal families, the handoff family and `ValidBridge`'s
completeness vacuously: nobody proposes to the MVBA and nobody decides.
That is enough for joint satisfiability, since one model suffices (§6.3).
A run that fires the case-(a) proposals, decides in the MVBA and finalizes
through the fallback commit round would show those three premises holding
non-vacuously, together with the rows that guard them. It would also be the
first witness in which `valid := (· = v⋆)` meets an actual decision. **Not done in R12:** it needs a hand-stepped MVBA decision (views,
votes and the commit certificate of `Mvba.Witness`'s run, driven from
Chorus's fallback or case-(a) proposals) and the fallback commit round, well
over the half day it was allowed. Consistency does not depend on it.

#### 6.4.6 Staging and sizing

One focused session each, give or take. Reassess after S3, as §6 asked
after its step 2.

1. **S1: the joint edit** (option A, C1/C2, and the ride-alongs of
   §6.4.1). It touches [Chorus.lean](../Cadence/Chorus.lean) and
   [Interfaces.lean](../Cadence/Interfaces.lean), and gives
   [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) its step/trans
   split.
   * It adds `InputLabel` to [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean).
   * It re-proves `Chorus.termination` against the extended
     `TerminationClaim`, with the early-finalization split.
   * It updates the monitor decoders.
   * It does the cold re-solve, updates the `#veil_status` pin, and
     re-states the axiom pins.
   Probably two sessions. **Must not overlap** the untimed non-vacuity
   work (which waits, §6.4.5), MVBA upgrade step 5b if it edits
   Interfaces.lean (bundle into S1 or serialize), or any other
   Interfaces.lean edit. One family re-solve at a time.

   **Done** (2026-09-29, one session, the "R1" PR). Option A with C1/C2 and
   the sender parameters, as decided. What an auditor should know:

   * **The model.** `participating`/`abandoned` per validator, written only
     by the inputs `participate i` and `abandon i mvba_next`. Every sending
     rule of §6.4.1's list is gated on `participating i ∧ ¬ abandoned i`,
     and the processing rules are exempt. `broadcast_commitqc_*` and
     `redisseminate_chunk` take a sender, gated when it is correct. The
     gates read only the acting validator's local state: no new network
     read, no fourth exception category. **No invariant was added.**
     `#veil_status Chorus` goes from 4222 to 4428: 101 init cells +
     42 actions × (101 + 1 step property) + 43 does-not-throw, as predicted
     before the build.
   * **The contract.** C1 in `bounded_termination` and `totality`; C2, with
     the datum `deadline : slot → time`, in `bounded_termination`. Both are
     antecedents in the rely form. The `…Safety` fragment is untouched, and
     no field was weakened.
   * **The claim.** `TerminationClaim` gains `AllParticipate` and
     `NoAbandonBeforeFinalizing`, the antecedents of
     `SlotConsensusTemporal.termination`. `Chorus.termination` is re-proven
     at the trio, split on an early finalization
     ([Liveness.md](Liveness.md) §4.7 has the record). `MvbaAdmissible` did
     **not** change shape: the MVBA's abandonment premise is derived on the
     branch that needs it.
   * **The composition.** `Chorus.slotConsensusSafety`'s `step` now
     excludes the inputs. The consequence §6.4.6 named holds: the composed
     system's Chorus is inert until the glue drives the inputs, and glue
     safety is unaffected ([CompositionContracts.md](CompositionContracts.md) §5).
     The glue drives the inputs since R25 ([ConductorBounds.md](ConductorBounds.md) §9, K1).

   Deviations from the plan, each small:

   * **`abandon` forwards every time**, not only "if mvbaInvoked"
     (Algorithm 5, line 48 (`line:fb-abandon`)). The difference is unobservable: the MVBA's own
     `abandon()` has no precondition, a party that has not proposed sends
     nothing in the MVBA, and after `abandon` Chorus never proposes to it.
     The conditional form would have needed a negative read of the MVBA's
     state, or a new local flag.
   * **`propose` loses its fairness.** It was weakly fair before; as the
     contract's `propose(P)` input it now carries none. No link of the
     proof fired it.
   * **Two run-level first-flip facts** (`committed_pos_assignable`,
     `committed_neg_assignable`) replace what an invariant would have given:
     `local_committed_*_backed` keeps the MVBA record but not the fallback
     commit certificate beside it, and the early-finalization branch needs
     both.
   * **FallbackReceipt.lean's header** was aligned too (§6.4.1 had left it
     for its own next edit). The receipt family replays warm.
   * **The monitor**: the silent MVBA stub has no `abandon`, so `abandon` is
     never enabled under the monitor, a coverage gap of the same kind as
     the decision handlers ([Monitor.md](Monitor.md) §8). The fixtures gained
     `participate` lines and the collector argument by hand.
   * **Quiescence** is not proven here. The gates make it provable in the
     paper's two-part shape; the one-step statement belongs to S5 with the
     rest of the `SlotConsensusTemporal` instance.

   **Then S1b: fired-once flags, and fairness over plain enabledness**
   (decided 2026-09-30, after R3; §6.4.7 is the plan). Both models change:
   every fair action that can stay enabled after it has fired gets the
   local "not already" guard the paper gives it. Then the fairness
   premises go back to plain enabledness. It comes **before S2 and before
   the witness (S6)**, since both are written against the final model and
   the final premises. **Three sessions:** R4 (the Mvba model) and R5 (the
   Chorus model), in parallel, with their cold re-solves serialized, then
   R6 (the flip to plain enabledness, plain Lean only), after both have
   merged. The flip waits for both because the fairness definitions are
   shared (§6.4.7, "Staging").
2. **S2: timed scaffolding, statements only.** In [Timed.lean](../Cadence/Timed.lean):
   * the (Δδ-justice) clause and `BoundedFairFamily`;
   * the timed projection (`Component.Projection` plus a clock), with its
     back-transfer lemma and, optionally, `boundedFair_iff`.

   A new `Cadence/Chorus/Schedule.lean`, holding:
   * the Chorus schedule (the MVBA's, plus `D`) and the hop table with its
     gates, with a `hop_isSome_iff` coverage pin;
   * (P-phase) and the timed `MvbaAdmissible`;
   * the two claims as `Prop` definitions **before any proof**, the
     discipline of [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean).

   **Done** (2026-09-30, the "R7" PR). Plain Lean only; no Veil file, no
   Interfaces.lean edit, nothing re-solved, and every `#veil_status` pin
   unchanged. What an auditor should know:

   * **Timed.lean.** (Δδ-justice) is `BufferedFair` (one label) and
     `BufferedFairFamily`. With `N = N'`, a trivial gate and `δ ≤ D` it is
     `BoundedFair` (`bufferedFair_iff_boundedFair`). `BoundedFairFamily` is
     the timed twin of `WeaklyFairFamily`. The timed projection is
     `Component.Projection.timed`, with the back-transfer (`timed_back`), a
     forward transfer (`timed_forward`) and `boundedFair_iff`, the timed
     twin of `weaklyFair_iff`.
   * **Chorus/Schedule.lean.** The schedule, `hop` (pinned by
     `hop_isSome_iff`), `gate`, `Owed`, `TimedJustice`, `PhasePunctual`,
     `TimedMvbaAdmissible`, the caller's conditions, and the two claims
     `TimedTerminationClaim` and `TotalityClaim`. The header states the
     gate checklist. §6.4.2 has the table as built and §6.4.5 the ledger
     draft.

   Changes to the plan, each small:

   * **An owed-condition per row** (F5, F6, §6.4.2). The generic clause
     takes a condition `C` beside the gate: what the environment must have
     supplied for the step to be owed. For Chorus that is correct senders,
     and, for `cast_fb_commit`, the voter's own decision. With `C` trivially
     true the clause is §6.4.2's verbatim.
   * **The claims are generic in the MVBA contract `T`.** Both consume only
     `T.Admissible` and `T.ℓ`, so the statement holds for any
     `T : MVBATemporal … (S := mvbaSafety thM)`, and the system's MVBA is
     the instance `T := Mvba.mvbaTemporal …` (`mvbaTemporal_ℓ`,
     `timedMvbaAdmissible_atMvba_iff`, by `rfl`).
   * **The `δ`-multiple of `ℓ` is fixed now**, at `8`
     (`Lchorus Δ δ ℓM = 5Δ + ℓM + 8δ`; restated as `9` by S3, F9). The docstring derives it milestone
     by milestone. S3–S4 confirm it, or restate it before the instance, as
     `Lcert` was.
   * **`TotalityClaim` takes fewer premises than the class field allows**:
     (Δδ-justice), participation synchronized within `d`, and C1. Neither
     the phase timers, nor the MVBA, nor the bridge is a premise. That makes
     the claim stronger, and it implies the field.
   * **`mvba_propose`'s gate is the MVBA arm** (§6.4.2), and the family is
     owed on a correct trigger only.

   Two findings were left open for R8, before the witness and S3:

   * **F5 on the untimed premises**: both `FJustice`s, Chorus's and the
     MVBA's, owed steps enabled by Byzantine senders' messages.
   * **C15**: the MVBA decision certificate's delivery is Chorus's protocol
     step (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"), which the
     model did not have.

   **Both closed in R8** (2026-09-30, §6.4.2 "The decision handoff (C15):
   the design" is the plan as written before the build). What an auditor
   should know:

   * **The premises.** Both untimed `FJustice`s owe a step only for
     messages from correct senders, with the timed rows' own
     owed-conditions: `Chorus.Owed` (now in
     [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean), shared with
     `TimedJustice`) and `Mvba.Owed` (a correct leader, a correct quorum:
     `Delivers`' sender part, `Mvba.owed_of_delivers`). Two amendments to
     R7's table came out of the re-proof, both the paper's forwarding rules:
     F7 (a correct fast voter's `FastBlock`) and F8 (the decoding fallback
     signer's re-dissemination), §6.4.2.
   * **The model.** One action, `accept_mvba_commitqc`, with its fired-once
     record; no invariant. `#veil_status Chorus` 4737 → **4840** = 101 +
     46 × (101 + 1) + 47, as predicted. The Chorus family re-solved cold,
     every file with 0 cache hits.
   * **The contract.** `MVBASafety` gains the supplement's strengthened
     interface, additions only (§6.4.2 (b)). At the instance `decide` is an
     input, so the MVBA's claims gain the caller's side: (F-relay) untimed,
     `Relayed` timed (the former `decisions` clause, verbatim), both derived
     inside Cadence. (A-viewsync)'s second clause names a correct decision.
   * **The proof.** `Chorus.termination`'s late branch always takes the
     MVBA arm (`eventually_mvba_route`); the commit route there rested on
     commit certificates that may include Byzantine votes. `Mvba.termination`,
     `Mvba.bounded_termination`, `Mvba.aViewSync_of_sync` and both MVBA
     witness theorems are re-proven; `Mvba.Witness.ell` is unchanged.
3. **S3: totality and the timeline to `M + 3Δ`.** Totality comes first,
   because it is small and validates the scaffolding. Then the links up to
   the MVBA proposals. The reassessment asks two things: did the hop table
   survive the guards, and does the split hop keep the paper's arithmetic.

   **Done** (2026-10-01, the "R11" PR). Totality (§6.4.4, "Proven") and the
   timeline to the proposals (§6.4.3, "The milestones as proven"), plain
   Lean in two new files, every theorem at the standard trio. Three
   statement fixes went in with it, under one commit before the proofs that
   need them: F9 (the proposal's two rules), F10 (`δ_le_Δ`) and F11
   (re-dissemination owed only where the paper sends), §6.4.2. F11 changed
   `Chorus.termination`'s premise, and its proof was re-run (one lemma). No
   model file, no Veil proof file, nothing re-solved, every `#veil_status`
   pin unchanged. F12 was left for a model session, and R12 closed it
   (§6.4.2, "F12 closed").

   **Reassessment after S3.**

   *(a) Did the hop table survive the guards?* Row by row, for the rows the
   proofs exercise:

   * `vote` (δ, gate: active, past `D`): yes, exactly. Its fired-once guard
     `¬ local_voted` lapses only by the vote.
   * `fb_sign_pos`/`fb_sign_neg` (Δ, gate: the fallback arm): yes, with one
     fact the untimed chain did not need. Whether the honest quorum's votes
     are positive evidence must be settled once, at the index where they
     have all voted; otherwise late evidence would disable `fb_sign_neg` and
     restart the window. It is: a correct vote is frozen once cast
     (`vote_pos_sig_frozen`, from three existing invariants). The lapses of
     `¬ msg_commit_cast`, `local_path ≠ fallback` and R5's fired-once
     `¬ local_fb_entry` are each the progress wanted.
   * `cast_fallback_vote` (δ): yes.
   * `aggregate_fastqc_*` (Δ, no gate): yes, through F7's disjunct only (a
     correct fast voter's meta-block), the quorum disjunct is not needed.
     Its fired-once `¬ local_fastqc` lapses by the goal.
   * `mvba_propose`: **no**, as one Δ-row (F9); as the paper's two rules,
     yes. Its "no input yet" guard lapses only by an input.
   * `commit_assign_*` (Δ, gate: active) and `finalize_commit` (δ):
     yes, in totality, with the owed-conditions verbatim the commitment
     proofs (`ProofPos`, `ProofNeg`).
   * `deliver_chunk_assigned` (Δ, gate: the proposer active) and
     `record_chunk` (δ): yes; R5's fired-once `local_chunk_sent` lapses only
     with the delivery. `record_chunk`'s phase guard *closes* at `D`, so its
     milestone needs the strict `< D` (the tie §6.4.2 recorded).
   * `redisseminate_chunk`: its owed-condition was wrong (F11); not on the
     path to the proposals.
   * R8's handoff row `accept_mvba_commitqc` is not on the path to the
     proposals; its derivation (`relayed_of_timedJustice`) is unchanged and
     its `δ ≤ Δ + ρ` now follows from `δ_le_Δ`.
   * Not exercised by S3: `commit_sign_*`/`cast_fast_commit` (the fast
     commit vote is never awaited, only counted when it happens),
     `broadcast_commitqc_*` (R8: the late branch takes the MVBA arm), the
     decision handlers, `mvba_terminate` and `cast_fb_commit` (S4).

   Every R5 fired-once guard met on the way lapsed only by the progress its
   link wanted, which `TLRun.withinFrom_of_bufferedFair` absorbs by widening
   the goal; none blocked an owed step. Across all rows, a Δ-row costs
   `max(Δ, δ)`, which is F10.

   *(b) Does the split hop keep the paper's arithmetic at δ = 0?* Yes, term
   for term, once F9 is in: first-round votes by `M + Δ`, the second-round
   vote by `M + 2Δ`, the FastQCs and the proposals by `M + 3Δ` — the
   paper's three milestones — and totality's `Δ`. The split is what keeps
   the fallback entry at `M + 2Δ`: its message part (the votes, by
   `M + Δ`) and its gate (the arm, by `D + Δ ≤ M + 2Δ`) are measured
   separately, where one hop from the later of the two would cost
   `M + 3Δ`. At δ > 0 the multiples are those of the table in §6.4.3,
   `t_M = M + 3Δ + 3δ`, so `ℓ = 5Δ + ℓ_MVBA + 9δ` (restated in
   `Chorus.Lchorus` from R7's 8; S4 confirms the rest).

   *(c) What S4 needs, and what F4 looks like now.*

   * **The MVBA tail.** `T.termination` on `mvbaTimedRun p` of a projection:
     proposals by `t_M` (`within_all_input`, carried to the projection by
     `Projection.timed_forward`); a `Valid` input (`certifiedVector` at the
     saturation index's evidence, `mvba_evidence_of_saturation`, and
     `ValidBridge`'s soundness); no abandonment before
     `max(t_M, GST) + ℓ_MVBA` (`activeUntil_of_not_finalized` on the branch
     where nobody finalizes before the inner split, then the MVBA's
     `abandoned` row through `abandoned_of_mvba_abandoned`). The decision
     comes back by `Projection.timed_back` and `TimedRun.byGstBound_iff`.
   * **The handoff** is already derived (`relayed_of_timedJustice`); S4
     consumes it only through `T.Admissible`.
   * **The fallback commit round**: the decision handlers and
     `mvba_terminate` (δ each, per proposer collapsed by
     `withinFrom_forall`), then `cast_fb_commit` (δ, owed on the own
     decision, F6), the fallback commit certificate (a ghost), the
     assignments and the finalization (`within_assigned`/`within_finalized`
     from Totality.lean, as they stand). **F12 bit here, and is fixed
     (R12).** Before the fix, the DA wait in `cast_fb_commit` covered
     FastQC-backed roots too, and after F11 the only owed source of a
     validator's own chunk under such a root was its own re-dissemination
     after its decision, so the commit vote was due `Δ + δ` after the
     decision. *Reassessed after R12:* a FastQC root now needs no chunk, so
     the vote's own hop is `δ` after the transported decision, as in the
     paper. A FallbackQC root's chunk comes from the correct signer (F8) by
     `M + 3Δ + 2δ`, before the decision at `t_M + ℓ_MVBA`; that needs the
     one first-flip fact recorded above (a correct validator signs
     fallback entries only before its second-round vote), which is S4's to
     prove. F13 is closed (R15): the vote's row is owed under the
     validator's own `B′`, so a root with both certificates is waited for
     as in the paper, and no run is outside the premise for it.
   * **The case split, and F4.** From the milestones: the decision by
     `t_M + ℓ_MVBA`, the fallback commit vote `3δ` later (the two decision
     handlers and `mvba_terminate`, then the vote, `δ` each with the
     handlers collapsed per proposer), the commitment `Δ`, the finalization
     `δ`, so `T₀ = t_M + ℓ_MVBA + Δ + 4δ = M + 4Δ + ℓ_MVBA + 7δ`, now that
     F12 is fixed (R12), and `M + 4Δ + ℓ_MVBA` at `δ = 0`. F4's single split at `T₀ − Δ` still looks right: a validator
     that finalizes before `T₀ − Δ` hands everyone totality's `Δ + 2δ`, and
     on the other branch nobody has abandoned by then, so the chain runs to
     `T₀`, giving `M + 4Δ + ℓ_MVBA + O(δ)`. Nothing in the milestones uses
     the outer split. F4 is decided in S4.
4. **S4: the MVBA tail and the assembly.** *Scheduled after the
   realignment to the paper target `48cac9a`
   ([PaperAlignment.md](PaperAlignment.md) §8), on the realigned model.*
   `T.termination` through the
   projection, the fallback commit round, and the case split, giving the
   bound. F4 is decided here.

   **Done** (2026-10-02, the "R18" PR). Plain Lean in one new file,
   [Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean),
   every theorem at the standard trio; no model file, no Veil proof file,
   nothing re-solved, every `#veil_status` pin unchanged. What an auditor
   should know:

   * **The claim.** `Chorus.timed_termination` is `TimedTerminationClaim`
     at the paper's bound `5Δ + ℓ_MVBA + 9δ` (`Lchorus`, unchanged), at
     the concrete family and the system's configurations, for every MVBA
     contract with `0 ≤ T.ℓ`; `Chorus.timed_termination_atMvba` at the
     system's MVBA, where that is a theorem. The R10 witness run
     instantiates it.
   * **F4, confirmed.** `Chorus.timed_termination_tight` proves
     `4Δ + ℓ_MVBA + 8δ` from the same premises, with one split at the
     fallback commit votes' deadline (§6.4.3, "The assembly, and F4").
   * **The milestones** are §6.4.3's "The MVBA tail and the round, as
     proven". `T₀ = M + 4Δ + ℓ_MVBA + 7δ`, as the reassessment expected.

   Changes to the plan, each small:

   * **`0 ≤ T.ℓ`**, a hypothesis of the two generic theorems on the MVBA
     contract (§6.4.3); the claim's statement is unchanged.
   * **The split point** is `T₀ − Δ − δ`, the vote deadline, rather than
     `T₀ − Δ`: the late branch needs everyone active only until the votes.
   * **(Δ-avail) is not derived** (task 1 of the session). The derivation
     met F15 (§6.4.2), a divergence of the model from the paper's
     re-dissemination, which needs a model change. It is R19's, with the
     schedule constraint `Δ + δ ≤ Δ_sync` the derivation needs.
     `timedMvbaAdmissible_of_rows` still takes the MVBA's three clauses.
   * **The comments of [Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)**
     were brought up to date (comment-only, approved in session).

   **Then R19: F15 closed** (2026-10-02, the "R19" PR; §6.4.2 "F15: the
   design" and "F15 closed"). A model session between S4 and S5. The
   fallback signer re-disseminates inside `fb_sign_pos`, the proposer's
   chunk delivery no longer requires the proposer to be active, and
   `redisseminate_chunk` is gone: `#veil_status Chorus` 5099 → 4997, the
   family re-solved cold. (Δ-avail) is derived
   (`availWithin_of_timedJustice`), and the claim at the system's MVBA
   (`TimedTerminationClaimAtMvba`) assumes only the MVBA's own two clauses.
   Changes to the plan:

   * **`Δ ≤ Δ_sync`, not `Δ + δ ≤ Δ_sync`.** Once the chunk is sent with the
     signature, the availability report is a `Δ`-row, which costs
     `max(Δ, δ) = Δ`. The `+ δ` belonged to a sequential reading that the
     atomic step retires.
   * **Two premise rows changed shape**, both weakenings. `cast_fb_commit`
     and `mvba_avail_ready` read a re-disseminated chunk, which now holds
     from its send, so they are `Δ`-rows (the first split at its trigger,
     `TimedJustice.fbCommit`). The gate checklist admits the actor's own
     MVBA output.
   * **The proposer's dissemination**, the same shape as F15, was closed in
     the same re-solve, at the design review's request, not parked.
   * **The witness overrides `Δ_sync`** in its own schedule.
     `Mvba.Schedule.fixedNat` and the MVBA's witness are untouched.
5. **S5: the contract instances. Done** (R20, 2026-10-02):
   [Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean). With it the
   Chorus bounds leg is complete. The plan was `SlotConsensusTemporal` at the new
   fragment, which includes:
   * Quiescence from the gates and the MVBA's `quiescence`. Since R19 every
     correct chunk send happens inside a gated step: the proposer's in
     `propose` (whose record is `msg_proposer_signed`) and a fallback
     signer's in `fb_sign_pos` (`local_chunk_sent i I j m`). A later
     `deliver_chunk_assigned` delivers an earlier send and is not a new
     send;
   * `admissible_exists` from an idle run;
   * Termination, as the unbounded corollary of the bounded one.

   Then `SlotConsensusWithTotality`, and the `…_of_temporal` join with its
   `rfl` lemma. After that:
   * the [Cadence.lean](../Cadence.lean) rows and pins, with the verification-status
     text in [CLAUDE.md](../CLAUDE.md), [Architecture.md](Architecture.md)
     §4 and [CompositionContracts.md](CompositionContracts.md) §5;
   * the (A-sc-termination) entry, which moves from assumed to discharged.

   **The record.** `Chorus.chorusTemporal` and `Chorus.chorusWithTotality`,
   at the system's configuration, every field proven, none weakened;
   `Chorus.slotConsensusFull` joins them with the fragment through
   `slotConsensus_of_temporal`, and `slotConsensusFull_toSafety` is `rfl`.
   `ℓ = Lchorus Δ δ ℓ_MVBA` and `d_tot = Ltot Δ δ Δ` are pinned by `rfl`,
   and are the paper's `5Δ + ℓ_MVBA` and `Δ` at `δ = 0`. Four changes to
   the plan:
   * **Termination is `Chorus.termination`, not the unbounded corollary of
     the bounded claim.** The untimed field's antecedents are participation
     and C1 only; the bounded claim also needs Δ-synchronized participation
     and C2, which the field does not give. `Admissible` carries both
     claims' premises, each by name.
   * **The contract's Quiescence was mis-stated, and is corrected** (approved
     by Lars): `SlotConsensusTemporal.quiescence` quantified over every
     transition, reachable or not, and its MVBA half needs two facts that
     hold only along a run, an MVBA proposal is made while participating
     (`participating_of_mvba_proposed`) and an abandonment is forwarded
     (`mvba_abandoned_of_abandoned`). The field now takes `S.reachable st`,
     as does `ACSTemporal.quiescence`, which had the same shape and no
     consumer ([CompositionContracts.md](CompositionContracts.md) §5).
   * **`admissible_exists` is a generic idle run, not the R10 witness**,
     which is one fixed instance: from any initial state of any
     configuration, nobody participates, the markers fire at the landmarks,
     and the caller abandons one validator at every other step. It needs a
     non-empty proposer set (§6.4.5; P14) and a view after the first with a
     correct leader, which `LeaderRotation` gives.
   * **The deadline is per slot** (`FamilySchedule`: one MVBA schedule and
     `D : slot → time`), since the class's `deadline` is a function of the
     slot; `ByzNodeSetHonestQuorum` is built for the family (`hqeFin`)
     rather than taken.
6. **S6: non-vacuity. Done** (R10, 2026-10-01): the final ledger and the
   one witness, [Chorus/Witness.lean](../Cadence/Chorus/Witness.lean)
   (§6.4.5). It touched no model file. It found F11 (re-dissemination owed
   off the fallback path), which R11 fixed in the statements.

Total: six to eight sessions. As in the MVBA leg, the dominant risk is
statement churn: F1–F4 are the churn this record tries to absorb up
front, before any Lean.

**What the Conductor's timed claims need from this leg.** The
Conductor's Totality, `B`-Boundedness and `R`-Recovery
(`OrchestratorTemporal`) consume Chorus's claims in
Proposition 13 (`prop:window-synchronization`) (totality), Proposition 14 (`prop:conductor-open-to-complete`)
(ℓ-termination), and the recovery chain through `Φ_oc = ℓ_chorus + d_tot`
and the parameter assumptions of Algorithm 7 (`algorithm:conductor`). For those proofs
to go through, this leg must hand over the following.

* **Premises the composition can discharge.** Each of Chorus's caller
  conditions has to be one a composed run proves:
  * participation by `t`: the glue invokes `participate` at `open`
    (Algorithm 1, line 17 (`line:participate`));
  * Δ-synchronized participation: the Conductor's own opening totality
    (Lemma 15 (`lemma:conductor-totality`));
  * C2: `integrity_timing`, with `deadline s = start_time s + Δ`;
  * C1: the glue abandons only after finalizing (Algorithm 1, line 23 (`line:abandon`)).

  C1/C2 are phrased with that in mind, as antecedents over the class's
  own observables.
* **`ℓ` and `d_tot` as data, with closed values.** They appear in
  assumptions (1)–(4) of Algorithm 7 (`algorithm:conductor`). They are fields already;
  the instance pins them.
* **Totality in the tolerance-parametric form of §6.4.4.** This is F3.
  The ratchet needs Chorus's latency not to exceed the tolerance the
  Conductor grants. At δ = 0 both are Δ, and the paper's induction goes
  through. At δ > 0 `max(Δ, d) + 2δ > d` for every `d`, so the Conductor
  leg has to choose. It can work at δ = 0, the paper's instantaneous
  local computation. It can find a δ-robust statement, for instance by
  re-synchronizing on the absolute start times, as
  Algorithm 7, line 27 (`line:conductor-wait-for-open`) does once the windows are ahead of the
  clock. Or it can record the degradation as a finding. **Proposal (C3,
  to the Conductor leg):** leave `syncParticipation_def`'s tolerance at Δ
  for now. The parametric lemma means this leg's statement does not
  pre-empt the choice.
* **One time theory and one Δ across the system.** Chorus, the MVBA, the
  Conductor and the ACS share the run's clock. So the Conductor leg
  should take the same schedule record rather than a second Δ.
* **Two edits outside this leg**, recorded so that neither comes as a
  surprise:
  * After S1, `Chorus.slotConsensusSafety`'s `step` excludes the inputs,
    so the glue's `sc_step` (which requires `sc.step`) can no longer
    participate. The composed system's Chorus is then inert until the
    composition leg gives the glue its `participate` / `propose` /
    `abandon` actions. The glue's safety theorem is unaffected: it is
    generic, and inertness only removes behaviours. Done in R25
    ([ConductorBounds.md](ConductorBounds.md) §9, K1).
  * Corollary 4 (`cor:chorus-correctness-within-cadence`) then closes the loop, which
    is §6 step 5.

#### 6.4.7 Fired-once flags: fairness over plain enabledness

*The plan for S1b (§6.4.6), decided 2026-09-30 after R3 (PR #48). **S1b is
done**: the Chorus half in R5 ("The Chorus half: done"), the Mvba half in R4
("R4 done: the Mvba half") and the flip in R6 ("R6 done: the flip"), the
records at the end of this section.*

**The decision.** Disabledness is modelled in the protocol, not resolved
in the proof. Every fair action that can stay enabled after it has fired
gets a local "not already" guard, as the paper describes the rule. Once
none is left, the fairness premises use **plain enabledness** again: an
action enabled from some point on eventually fires. The auditor's premise
then has no qualifier about state-changing steps. Today it has one, and
the reason for it takes §6.2.4 to explain. R3 made fairness count only
state-changing steps (TLA+'s `⟨A⟩_v`). That was sound, and weaker than
before, but it resolves scheduling non-determinism in the proof that an
implementation resolves in its protocol logic. The model moves closer to
the paper; the premises and the proofs get simpler.

**Where the non-determinism is.** Most honest per-validator actions
already disable themselves after firing: `vote` (`¬ local_voted`),
`send_commit` (`¬ commit_sent`), the timeouts (`¬ timed_out`), `decide`
(`∀ E, ¬ decided`), the leader's proposal (`¬ proposed_in`),
`commit_assign_*` (`¬ local_committed`), and since R3 `adopt_prepqc` (the
lock-view guard). Two sets do not; they are **the inventory to work
from**.

* **Mvba: the anonymous assemblies** `form_prepqc`, `form_commitqc`,
  `form_tc_lock` and `form_tc_nolock`. They have no validator, and a quorum
  parameter `q`, so once the certificate exists every `q`-variant stays
  enabled without effect. In the supplement (at the paper target) each is a step of
  one validator with a local condition:
  * `TryFormPrepQC`: pᵢ forms `prepareQC` if it "has not already formed a
    prepare certificate in the current view". This is `adopt_prepqc` since
    R3, and it is done;
  * the commit certificate: pᵢ forms `CommitQC` "provided that it has not
    already learned a decision certificate", and records it as
    `DecidedQC_i`;
  * the timeout certificate: "upon first collecting 2f+1 valid timeout
    messages", pᵢ forms `TC_{s,v}` and processes it through `SyncView`
    (Supplement, Algorithm 1, line 85 (`line:mvba:ht-advance`)).
* **Chorus:** `aggregate_fastqc_pos/neg i j …` (Algorithm 4, line 18 (`line:fast-formqc`)) and
  `broadcast_commitqc_pos/neg c j …` (Algorithm 4, line 31 (`line:fast-collect-commit`),
  Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)). Each has an actor and no fired-once
  guard. **An assumption to confirm:** the published paper writes these as
  `upon` handlers of an event-driven protocol, without "first time" (only
  the fast meta-block rule says it). The plan reads an `upon` handler as
  running once when its condition becomes true. That is the conventional
  reading, but the paper states no convention, so it is a question for the
  authors, recorded as paper-side finding P6 in
  [PaperAlignment.md](PaperAlignment.md) §6.

The inventory may not be complete. The acceptance criterion below is what
decides that, not this list. Candidates to check first:
`redisseminate_chunk` (re-delivery of a chunk already received),
`record_chunk`, the phase markers, and every assembly with a quorum
parameter.

**The shape.**

* A **per-validator** action with a quorum parameter (no `∃`-quorum ghost
  in a guard, as in `adopt_prepqc i v e q`). It sets a **local** record of
  what it formed, and a guard on that record's absence disables every
  `q`-variant at once. A negative read of the actor's *own local* state is
  what every existing honest guard does; no network relation is read
  negatively, so the monotone-network contract is untouched
  ([ChorusDesign.md](ChorusDesign.md) §3.1.1). It also sets the network
  certificate relation, as `adopt_prepqc` sets `msg_prepqc`, where the
  certificate is carried on (timeouts, broadcasts).
* The **anonymous forming stays**, but is **not fair**: it is the
  adversary's capability to aggregate signatures it saw, so safety's
  adversary is unchanged. It moves into an unfair label class (with the
  `byz_*` family, or its own class, with a `not_justice_of_*` pin), and
  the hop tables lose it. Where an honest per-validator action replaces it
  in a chain, the chain's link changes accordingly.
* Where the effect record itself is the natural flag (`aggregate_fastqc_*`
  sets `local_fastqc_*`), the guard is its absence, and no new relation is
  needed.
* At most 10 action parameters. An invariant only if the cleanest proof
  needs one (backing of the new local records is the likely one).

**The fairness side (R6).**

* [Fairness.lean](../Cadence/Fairness.lean): `WeaklyFair`,
  `WeaklyFairFamily` and `StronglyFair` over `Enabled` again.
  [Timed.lean](../Cadence/Timed.lean)'s `BoundedFair` over `Enabled` too.
  `EnabledMove` stays only as the vocabulary of the lemma below.
* Both `FJustice`s and `Mvba.BoundedJustice` are restated with plain
  enabledness, and their docstrings drop the state-changing qualifier. The
  proofs lose their side conditions (`EnabledMove.of_enabled_of_effect`,
  `eventually_of_weaklyFair`), unless keeping `eventually_of_weaklyFair`
  in plain form reads better.
* **The acceptance criterion, machine-checked, per model (R4 for Mvba,
  R5 for Chorus):** at every
  reachable state, every enabled fair label is move-enabled
  (`∀ l, JusticeLabel l → Enabled … st l → EnabledMove … st l`). It says
  the model has no fair action that stays enabled without effect, so the
  flag discipline is checked rather than read. For the audit surface it is
  the statement that, for this model, weak fairness over plain enabledness
  and over state-changing steps are the same premise. A label that fails
  it belongs in the inventory above. Proven per action from the guards and
  the generated frame lemmas, in plain Lean, not as a Veil cell. R6's
  docstrings cite both lemmas: they are what makes the plain premise the
  same premise as R3's.

**What it touches, and what it costs.**

* **R4:** [Mvba.lean](../Cadence/Mvba.lean), with
  [Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) mirroring it (the
  witness moves and is re-pinned, with `sequential := true`), and the
  whole Mvba liveness and timed stack: the hop table, `Delivers`, the
  chains, `Lcert` if a milestone moves, and the witness. Check
  [Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)'s step facts (the
  `mvba_tr` proofs) against the new per-validator actions. If the label
  change reaches Chorus's projection of the MVBA
  ([Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)'s
  `MvbaStepLabel` and `mvbaComponent`) or
  [Chorus/Termination.lean](../Cadence/Chorus/Termination.lean), R4 says so
  and coordinates with R5; it does not edit those files silently.
* **R5:** [Chorus.lean](../Cadence/Chorus.lean) and the Chorus liveness
  files, and the monitor, which R1 needed in full: both label decoders,
  `Cadence/Monitor/ChorusMonitorGen.lean` and the `traces/*.jsonl`
  fixtures, with all three monitor suites `ALL PASS` afterwards.
* **R6:** plain Lean only — Fairness.lean, Timed.lean, both `FJustice`s,
  `Mvba.BoundedJustice`, the chains' side conditions, and the ledgers.
* Interfaces.lean should not need to change; if a contract field turns out
  to need it, stop and report.
* Two cold family re-solves, one at a time. The `#veil_status` pins
  change with every added action: compute them before the build, update
  them where CLAUDE.md and [Architecture.md](Architecture.md) own them.
  Budget the manual cells: `adopt_prepqc`'s lock-persistence cell is the
  precedent for any per-validator action that creates a prepare
  certificate.
* Docs: R4 and R5 record their model changes (the inventory above, pins,
  History rows). R6 does the premise docs: §6.2.4 (the move-enabledness
  finding becomes history), the §6.3 and §6.4.5 ledgers,
  [Liveness.md](Liveness.md) §2, and a History row.

**Staging, and why the flip waits.** `WeaklyFair` and `WeaklyFairFamily`
in [Fairness.lean](../Cadence/Fairness.lean) are shared by both `FJustice`
definitions ([Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) and
[Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)). Flipping them to
plain enabledness in the Mvba session would put Chorus's premise back on
plain `Enabled` while `aggregate_fastqc_*` and `broadcast_commitqc_*` still
stay enabled without effect. Master would then carry a Chorus premise that
is unsatisfiable at infinite quorum sorts, and `Chorus.termination`'s proof
would break. So:

1. **R4 — Mvba S1b**: the model, NoLock, the Mvba liveness and timed stack
   and the witness, and the Mvba acceptance lemma. The premises stay in
   their current form (state-changing steps); the lemma shows that for
   this model it is equivalent to the plain one.
2. **R5 — Chorus S1b**: the model, the Chorus liveness chains, the
   monitor, and the Chorus acceptance lemma, with the premises again in
   their current form. It can run **in parallel with R4**: the two touch
   disjoint files, provided R4 keeps to the rule above about Chorus's
   projection of the MVBA. Their cold family re-solves run one at a time.
3. **R6 — the flip**, after R4 and R5 have both merged: plain Lean and
   docs, as listed above.

At no point does master carry a premise that is unsatisfiable at some
quorum sort.

**The Chorus half: done** (2026-09-30, session R5). The acceptance lemma is
**`Chorus.justice_enabledMove`**
([Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)): for every state,
reachable or not, and every label `l` with `JusticeLabel l`,
`Enabled (atMvba thM) thS st l → EnabledMove (atMvba thM) thS st l`. The
MVBA proposal is a justice label, so `Chorus.mvba_propose_enabledMove` is its
corollary for each member of the family. Both are pinned at
`[propext, Classical.choice, Quot.sound]`, the first also in
[Cadence.lean](../Cadence.lean). No reachability hypothesis is needed: each
fair action's firing sets a record its guard requires to be unset. The
proof is one lemma per action, read off the transition body.

*The inventory, as the lemma found it.* It was larger than the list above.
Every fair action that could stay enabled after firing now has a "not
already" guard on a record it sets itself. All the reads are negative reads
of the acting validator's own local state (category (L)). No network
relation is read negatively, and there is no new exception category
([ChorusDesign.md](ChorusDesign.md) §3.1.1).

| action | old guard, in words | new guard, in words |
|---|---|---|
| `aggregate_fastqc_pos/neg` | a supermajority signed | … and `i` does not hold this FastQC yet |
| `broadcast_commitqc_pos/neg` | a correct and active collector, or any Byzantine one; `2f+1` cast commit votes | a correct and active collector that has not broadcast a certificate for `j` yet (`local_commitqc_sent c j`); the Byzantine branch is now `byz_broadcast_commitqc_*` |
| `deliver_chunk_assigned` | an honest, active proposer that signed `m` | … that has not sent `i` this chunk yet (`local_chunk_sent j i j m`) |
| `redisseminate_chunk` | a correct and active sender, or any Byzantine one; the data is decodable | a correct and active sender that has not sent `i` this chunk yet (`local_chunk_sent k i j m`); the Byzantine branch is now `byz_redisseminate_chunk` |
| `commit_sign_pos/neg` | `i` holds the FastQC and has not cast | … and has not signed an entry for `j` yet (`local_commit_entry i j`) |
| `fb_sign_pos/neg` | the fallback-entry conditions | … and `i` has not signed its fallback entry for `j` yet (`local_fb_entry i j`) |
| `on_mvba_decide_pos/neg` | `i` decided `v`, the entry is certified | … and `i` has not recorded entry `j` of its decision yet (`local_mvba_recorded i j`) |
| `cast_fb_commit` | the DA wait holds | … and `i` has not cast its fallback commit vote yet (`local_fbcommit_voted i`) |
| `commit_assign_pos` | no *other* root committed for `j` | no root committed for `j` yet |
| `commit_assign_neg` | no positive entry committed for `j` | … and not the negative one either |

Where the plan was wrong or short:

* **`commit_assign_*` did not disable itself.** The list above credits it
  with `¬ local_committed`, but `finalize_commit` sets that, not
  `commit_assign_*`. The per-entry guards were the missing ones.
* **Six more families than listed** (the plan named two): the dissemination
  and re-dissemination of chunks, the commit and fallback entries, the
  decision handlers and the fallback commit vote. For those whose effect is
  a network tuple or a shared record (`mvba_decided_*`), the flag is a new
  local record. The six records are `local_chunk_sent`,
  `local_commit_entry`, `local_fb_entry`, `local_commitqc_sent`,
  `local_mvba_recorded` and `local_fbcommit_voted` (Chorus.lean,
  "Fired-once records"). Where the effect was already local
  (`aggregate_fastqc_*`, `commit_assign_*`), the guard is its absence.
* **The Byzantine branches of the two anonymous capabilities became their
  own unfair actions**, `byz_broadcast_commitqc_*` and
  `byz_redisseminate_chunk`. With the branch left inside the fair action and
  unconstrained, a label with a Byzantine sender would stay enabled after
  firing, which the lemma forbids. Guarding the Byzantine branch would
  constrain the adversary. This is the shape "The shape" gives the Mvba
  assemblies: the adversary's forming stays and is not fair. The honest
  actions now require a correct sender. The termination links already used
  the validator itself as collector and sender.
* **Flag granularity.** One record per actor and proposer, not per root or
  polarity: the paper's commit vote, fallback vote, commit certificate and
  decision each carry one entry per proposer.
* **No invariant.** What the links need of a record (that it comes with its
  effect) is plain Lean: a first-flip lemma per record and one induction
  (`Chorus.record_backed` in
  [Termination.lean](../Cadence/Chorus/Termination.lean)). The decision
  handler's link also uses the MVBA's agreement, to identify the recorded
  entry with the one it waits for.
* **The other candidates** needed nothing. `record_chunk` already requires
  that no positive entry is recorded, the phase markers move the phase, and
  the MVBA proposal's effect is the `Mvba` model's input record, whose
  absence its guard requires.

*Costs.* `#veil_status Chorus`: 4428 → **4737** = 101 initializer cells +
45 actions × (101 + 1 step property) + 46 does-not-throw, written down before
the build and matched (+309: three new actions × 103). Manual cells 12 → 15,
the three additions being the Byzantine assembly actions' copies of the
collector's cells. `TerminationClaim` did not change, and `Chorus.termination`
is re-proven at the trio. The premises keep their move form, and the flip is
R6.

**R4 done: the Mvba half** (2026-09-30, PR #51). What an auditor should
know:

* **The model.** The three rules the supplement gives a "not already"
  condition are one correct validator's step each, in its current view,
  with the quorum as a label parameter, as `adopt_prepqc i v e q` has been
  since R3:
  * `form_own_commitqc i v e q` — `TryFormCommitQC` and `Decide` in one
    handler segment: from `2f+1` `Commit`s of the current view, "provided
    that it has not already learned a decision certificate", form the
    `CommitQC`, record it as `DecidedQC_i` and decide. `DecidedQC_i` is set
    exactly when a validator decides (both decision paths set it), so the
    guard is `∀ E, ¬ decided i E` and no new relation was needed. The
    certificate is put on the network, where `decide` reads it.
  * `form_own_tc_lock i v q r₀ w e` and `form_own_tc_nolock i v q` —
    `HandleTimeout`, "upon first collecting `2f+1` valid timeout messages":
    the local record `tc_formed i v` is new, and its absence is the guard.
    The certificate goes on the network; `SyncView` is the next step
    (`sync_view`, `sync_view_adopt`), as the model has always split it.

  The four anonymous assemblies stay, as the adversary's capability, in a
  new unfair class `AssemblyLabel` (`not_justice_of_assembly`), and left
  the hop table. Only positive reads of `msg_*`; at most 6 parameters. One
  invariant, `tc_formed_backed` (the record is backed by `msg_tc v`), which
  the "not already formed" guard's lapse needs; `form_own_commitqc`'s
  record needs none, since its lapse is the goal.
* **The acceptance criterion**, `Mvba.enabledMove_of_enabled`:

  ```
  theorem enabledMove_of_enabled (l : Mvba.Label node nodeset value view)
      (hj : JusticeLabel l) (hen : Enabled … th st l) : EnabledMove … th st l
  ```

  It holds at **every** state, not only reachable ones: each fair action's
  guard, by itself, rules out that its update is a no-op. It is proven per
  action, in plain Lean, from the guards and the transition bodies, and
  pinned at the trio. **No label failed it**, so the inventory above was
  complete for the Mvba: the four assemblies were the only fair labels
  that could stay enabled after firing.
* **The pins.** `#veil_status Mvba` **1325 → 1507**: 50 properties (3
  safety + 47 invariants), 1 step property and 28 actions give
  50 + 28 × (50 + 1) + 29 = 1507, written down before the build and
  matched. Manual cells 3 → 5: `form_own_commitqc × commitqc_agree` (the
  `form_commitqc` cell's argument) and `form_own_commitqc × agreement` (the
  same argument at the decision the step makes, with `decided_backed`).
  R4 moves neither the Chorus pin (4737 since R5) nor FallbackReceipt's 220.
* **The liveness and timed stack**, re-proven with the premises in their
  current move form ([Fairness.lean](../Cadence/Fairness.lean) and
  [Timed.lean](../Cadence/Timed.lean) untouched):
  * the untimed chains go through a settled correct validator, which
    forms the commit certificate (`eventually_commitqc_of_settled`) and
    the view's timeout certificate (`eventually_tc_of_timed_out_quorum`);
    `Mvba.termination`'s statement is unchanged;
  * the timed premise: the new steps are network hops with first-delivery
    clauses; `Delivers` and `Receiving` lost their separate receiver,
    since every network label is now one validator's step and its
    `in_view` guard is the lower-view discard; the `timeouts` clause names
    the validator that forms the certificate;
  * `good_view_decides` now concludes that some correct validator has
    decided by `E₀ + Lcert`, since the step that forms the certificate
    decides; `bounded_termination`'s second case is therefore
    contradictory, and the transfer term already charged the others'
    decisions. `Lcert`, `Schedule.ℓ` and `Mvba.Witness.ell = 24` are
    unchanged;
  * both witness theorems stand: each correct validator forms its own
    commit certificate, and at the idle state no fair label is enabled at
    all.
* **NoLock** ([Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean)) mirrors
  the three steps. As a restriction, it drops the anonymous `form_prepqc`
  and `form_tc_*`, whose certificates the correct validators now form
  themselves. It keeps `form_commitqc`: the counterexample's view-1 commit
  certificate has to be the adversary's aggregation, since a correct
  validator that forms one decides on it and halts. The checker, still
  with `sequential := true`, finds agreement violated. The witness moved
  and is re-pinned at 25 transitions (was 26): the view-2 certificate is
  now formed and decided on in one step. The search takes 27 min on one
  core (was about 3½ min), because the per-validator steps and
  `tc_formed` multiply the states below that depth. *(Superseded in R6: a fixed
  environment schedule brings it to about a minute, with the same witness;
  "R6 done" below.)*
* **Chorus** is untouched: `MvbaStepLabel`, `mvbaComponent` and
  `Chorus.termination` re-elaborate against the new model without an edit.
  The one change a Chorus reader sees is in meaning, not text:
  `MvbaAdmissible`'s `Mvba.FJustice` of the projected run now ranges over
  the per-validator steps instead of the anonymous assemblies.

Deviations from the plan, each small:

* **No `DecidedQC_i` relation**: the decision is the record (above).
* **`Delivers` lost its receiver parameter**, which had been used only by
  the anonymous assemblies. With it went `NotPast` from `Receiving`; the
  guard's `in_view` says the same.
* **`decide`'s first-delivery clause is no longer used by the bound**: the
  good view's decision now comes with the certificate, and the others'
  come by transfer. The clause is kept, as the supplement's network
  rule; R6 may drop it.

**R6 done: the flip** (2026-09-30). What an auditor should know:

* **The premises read plainly.** [Fairness.lean](../Cadence/Fairness.lean)'s
  `WeaklyFair`, `WeaklyFairFamily`, `StronglyFair` and the projection's
  `WeaklyFairIn`, [Timed.lean](../Cadence/Timed.lean)'s `BoundedFair` and
  [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean)'s `BoundedFairWhile`
  are over `Enabled`: an action enabled from some point on eventually fires
  (within its window, for the timed ones). Both `FJustice`s and
  `Mvba.BoundedJustice` are stated with these notions. Their definitions'
  text did not change; their docstrings dropped the state-changing
  qualifier and cite the acceptance lemma.
* **The bridge, per model**, from the acceptance lemmas and pinned at the
  trio (also in [Cadence.lean](../Cadence.lean)):

  ```
  theorem Mvba.fJustice_iff_move (r : MvbaRun th) :
      FJustice r ↔ ∀ l, JusticeLabel l → WeaklyFairMove r l
  theorem Chorus.fJustice_iff_move (r : ChorusRun thS thM) :
      FJustice r ↔
        (∀ l, JusticeLabel l → ¬ ProposeLabel l → WeaklyFairMove r l) ∧
        ∀ i v, WeaklyFairFamilyMove r (fun l => ∃ mvba_next, l = .mvba_propose i v mvba_next)
  ```

  and, for every fair label, `Mvba.boundedFair_iff_move` and
  `Mvba.boundedFairWhile_iff_move` for (Δ-justice)'s clauses. The right-hand
  sides are R3's premises, TLA+'s `WF_v`. So the plain premise is not a new
  assumption: for these models it is the same one. `EnabledMove` and the
  move forms remain only as the vocabulary of those bridges.
* **The proofs lost their side conditions.** Every
  `EnabledMove.of_enabled_of_effect` is gone, the lemma with them.
  `eventually_of_weaklyFair` and `withinFrom_of_boundedFair(While)` kept
  their statements. The quiet-state lemmas now say what their proofs
  already showed, that no fair label is *enabled* (`Mvba.not_enabled_of_quiet`,
  `Mvba.Witness.quiet`), so both MVBA witnesses stand unchanged in
  statement. `Mvba.termination`, `Mvba.bounded_termination`,
  `Mvba.mvbaTemporal`, both witness theorems and `Chorus.termination` are
  re-proven at `[propext, Classical.choice, Quot.sound]`. No end theorem's
  statement changed.
* **Deviations from the plan.** The helper lemmas that name the vocabulary
  changed with it: `exists_disabled_of_never_fires` concludes `¬ Enabled`,
  `exists_not_moveEnabled_of_not_firesWithin` became
  `exists_not_enabled_of_not_firesWithin`, `not_moveEnabled_of_quiet`
  became `not_enabled_of_quiet`, `boundedJustice_of_quiet`'s hypothesis is
  plain disabledness, and the unused `enabledMove_of_fires_of_ne` is gone.
  `decide`'s first-delivery clause is kept, as the supplement's network
  rule.
* **CI headroom, alongside.** [Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean)'s
  search fixes the environment's schedule (its header, item 5) and drops
  three honest steps the scenario does not take (item 3). The check keeps
  `sequential := true`, and it reports the same pinned witness, in about a
  minute instead of 24 on one core. The Conductor's in-file sweep already
  had a 180 s budget; #51 read its two slowest cells against 60 s.

### 6.5 The Conductor leg: the kick-off record

*Written 2026-10-02 (R22), before any Lean.* The plan for the Conductor's
timed claims (`OrchestratorTemporal`: Totality, `𝓑`-Boundedness,
`𝓡`-Recovery) and for the composition that closes the Cadence loop
(Corollary 4 (`cor:chorus-correctness-within-cadence`)) is its own page,
[ConductorBounds.md](ConductorBounds.md). It takes up the hand-over list of
§6.4.6 ("What the Conductor's timed claims need from this leg"). It answers
F3 and C3 (its §5), and records the findings F16–F24 and the staging K0–K8.
