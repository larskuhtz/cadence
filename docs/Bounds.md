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
  (`lemma:chorus-termination`), via a deterministic post-GST timeline
  (`prop:chorus-finalization-time`, `prop:chorus-totality`), conditional
  on *Δ-synchronized participation*
  (`def:delta-synchronized-participation`).
* **Conductor**: totality with `d_tot = Δ` (`lemma:conductor-totality`),
  boundedness `𝓑 = 2W − p` and recovery `𝓡 = 2Wτ`
  (`thm:conductor-correctness`); the composition closes non-circularly
  (`cor:chorus-correctness-within-cadence`).
* **The parametric holes**: `ℓ_MVBA` (`mod:mvba`) and the ACS's `ℓ`
  (`mod:acs`) are *assumed module properties*, stated as deterministic
  bounds — an idealisation, since the randomised constructions satisfy
  them only in expectation / with high probability. The first hole is
  closed in this development: the MVBA instantiation of the paper
  repository's internal supplement is modelled
  ([Cadence/Mvba.lean](../Cadence/Mvba.lean)), `ℓ_MVBA` is the field `ℓ`
  of `MVBATemporal` ([Cadence/Interfaces.lean](../Cadence/Interfaces.lean)),
  and the instance `Mvba.mvbaTemporal`
  ([Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)) proves the
  Termination it bounds — the supplement's `thm:termination`, `O(fΔ)` — over
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
`lemma:chorus-termination`'s *proof arithmetic* as a standalone plain-Lean
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
statement shape of `lemma:chorus-termination`, with
`prop:chorus-finalization-time`'s milestone table (`M+2Δ`, `M+3Δ`,
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
5. The composition: `cor:chorus-correctness-within-cadence` and the
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
* Fairness is bounded weak fairness after GST on **state-changing** steps,
  with the window measured from `max(now, gst)` so that a clock jump over a
  pending obligation's deadline is inadmissible (§6.2.4). A local step is
  held to `δ`. A step that consumes another party's message is held to what
  the supplement's network guarantees (since step 5b, 2026-09-29): `Δ` for
  messages sent at or after GST by correct validators and retained, `Δ + ρ`
  for the retransmitted classes. Plain enabledness, as in [Fairness.lean](../Cadence/Fairness.lean), would
  make every admissible model unsatisfiable once a proposal exists; that is
  the second finding and it concerns the untimed leg too.
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

At the pin current when this leg was designed, `026dc8b`, the supplement
fixed the timer in one sentence (`subsec:mvba-protocol`): *"The view
timeout is chosen so that, after GST, it exceeds
`Δ_R + 3Δ + max{Δ, Δ_sync}`. If the implementation uses timeout backoff
rather than fixed known bounds, the timeout is eventually increased beyond
this value."* `thm:termination`'s proof then counted with a fixed timeout —
*"the view timeout is itself `O(Δ)`"* — to reach `O(fΔ)`.

At the current pin `eb1bb51` the sentence reads (`subsec:mvba-protocol`,
"Views, leaders, and timing parameters"): *"The view timeout is the fixed,
known value `T := Δ_R + 4Δ + max{Δ, Δ_sync}`"*, and the termination setting
says the view timeout is the fixed `T`. The backoff sentence is gone. The
model's schedule is then the supplement's fixed `T` plus a harmless
generalisation: `τ` constant and `v_L = zero` is the paper's case, and
(S-cap)/(S-ramp) below still describe capped backoff should an
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
across runs, and no `ℓ` covers them all. So the supplement's backoff remark
is compatible with *eventual* termination but not with its `O(fΔ)`
theorem as stated; the theorem is a fixed-timeout (or capped-backoff)
result, and a real implementation with exponential backoff satisfies it
only if the backoff is capped at `O(Δ)`. Recorded in
[PaperAlignment.md](PaperAlignment.md) §6. §6.1's "a sequence `Δ_v`
unbounded relative to a fixed bound" was therefore the wrong requirement:
the sequence must be *eventually above* `L_cert` and *bounded*, which is
what (S-ramp) and (S-cap) say.

*Resolved upstream at `eb1bb51`* ([MvbaPlan.md](MvbaPlan.md) §11.3, C13):
the timeout is now the fixed `T`, and the backoff remark is deleted. One
residue remains: the `sec:timing-constants` stub still lists "the MVBA view
timeout and its backoff policy".

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
| (Δ-justice) | `BoundedJustice` | six clauses, each of the form: if `l` is **move-enabled** at every index `n ≥ N` with `clk n ≤ ref N + D` (and the clause's side condition holds there), then `l` fires within `D` of `N`. A local step at `D = δ`; a network step at `D = Δ` when its messages were sent at or after GST by correct validators and retained, or at `D = Δ + ρ` when they are retransmitted (tables below) | the termination setting before `lem:decision-propagation` (delivery within `Δ` of messages sent at or after GST; retransmission every `ρ`), `sec:reliable-delivery` (one-view retention), `lem:view-sync`, `lem:convergence`, `lem:decision-propagation`; local computation within `δ` (the paper: instantaneous, `δ = 0`) |
| (T-timer) | `TimerPunctual` | for honest `i`: (T1) `expire_timer i v` fires at `n` only if `clk m + τ v ≤ clk n` for some `m ≤ n` with `entered i v` at `m`; (T2) if `entered i v` at `m`, then `timer_expired i v` at some `n ≥ m` with `clk n ≤ clk m + τ v` | the local view timer, restarted on entry, expiring after exactly `τ v` |
| (Δ-avail) | `AvailWithin` | for honest `i`: `accepted i v e` at `m` ⇒ `avail_ready i e` within `Δ_sync` of `m` | `lem:avail-progress`'s `Δ_sync` |

`hop`, the per-label kind, is a classification of the sixteen
`JusticeLabel`s by what the guard consumes:

| network (reads another party's message or certificate) | `δ` (local) |
|---|---|
| `handle_preprepare_first`, `handle_preprepare` (the leader's `Pre-Prepare`) | `leader_propose_first`, `leader_repropose`, `leader_propose_fresh` (upon entering the view; `Recover` is the identity here) |
| `form_prepqc`, `form_commitqc`, `form_tc_lock`, `form_tc_nolock` (a quorum of others' signatures — the model's separation of *delivery* from *assembly* puts the delivery on the assembly) | `adopt_prepqc`, `send_commit`, `timeout_qc`, `timeout_noqc` (own state and a certificate already counted) |
| `sync_view`, `sync_view_adopt` (a timeout certificate) | |
| `decide` (a commit certificate; since step 5b, (N3) below) | |

With `δ = 0` the good view's latency is the paper's constant (§6.2.6),
which is the check that the classification is the paper's and not a
convenience.

**The network clauses** (step 5b, 2026-09-29; [MvbaPlan.md](MvbaPlan.md)
§11.3 C16 and §11.5 stage 3). A network label's bound depends on its
messages' history, as the supplement's network at `eb1bb51` does. The
model's network relations hold from a message's first delivery to a
correct validator, so "sent at" is the first index at which the relation
holds.

| clause | owed within | when | the supplement |
|---|---|---|---|
| `first` | `Δ` | the messages are from correct senders (a correct leader; a quorum of correct validators), were first sent at or after GST (`SinceGst`, **N1**), and were retained by the receiver, which had reached the message's view or the one before (`RetainedBy`, **N2**); while every correct validator takes part and, for an assembly, the forming validator has not moved past the view (`NotPast`, **N2**) | delivery within `Δ` of messages sent at or after GST between correct validators; one-view retention; lower views discarded |
| `forwarded` | `Δ` | a timeout certificate forwarded, at or after GST, by the first correct validator to enter the view it justifies | `line:mvba:sv-forward`, `lem:view-sync`(b) |
| `timeouts` | `Δ + ρ` | a correct quorum's timeouts, whenever sent, while their senders are still in the view | the `Timeout` retransmission, `lem:convergence` ("Reaching `V`") |
| `certificates` | `Δ + ρ` | a timeout certificate, whenever formed, while every correct validator takes part | `line:mvba:viewtc-retx` |
| `decisions` | `Δ + ρ` | a commit certificate some correct validator has decided on (**N3**) | the composing layer's delivery, `lem:decision-propagation` |

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

**Open, closed in R3: (N4), prepare certificates do not travel.** `adopt_prepqc`
is a local step once `msg_prepqc v e` holds. In the supplement a validator
holds a prepare certificate only if it received a quorum of prepares
itself; nobody forwards one. So a supplement run in which one correct
validator forms a view's prepare certificate and another, which accepted
the same proposal, never does (Byzantine votes sent to some, or prepares
lost before GST) is not yet admissible. R3 closes it with a model change:
`adopt_prepqc` adopts from the prepares themselves, and the Mvba family is
re-solved, in one step together with the fairness clean-up
([TODO.md](TODO.md) § Liveness). The good view is
unaffected: there every correct validator receives the whole correct
quorum's prepares within the same `Δ`.

**Move-enabledness, and the second finding.** [Fairness.lean](../Cadence/Fairness.lean)'s `Enabled`
holds whenever *some* transition under the label exists — a stutter
included. Two of the model's assembly labels differ only in the quorum
parameter `q`, and the actions are idempotent: once `msg_prepqc v e` is
set, `form_prepqc v e q'` is still enabled for every other supermajority
`q'`, forever. Weak fairness per label then demands infinitely many
firings for one effect, and if `nodeset` has infinitely many
supermajorities no run satisfies it. In the *timed* form this is fatal
outright: infinitely many firings within `Δ`. So (Δ-justice) is stated for
`EnabledMove` — a transition under `l` to a **different** state, TLA+'s
`⟨A⟩_v` — under which one firing discharges every `q'` at once. Veil's
actions are deterministic in their parameters, so a firing of a
move-enabled label is a move; the proofs pay one side condition per link
(the guard's negative flag becomes the effect's positive one, so the
states differ). **This finding applies to the untimed leg**: `FJustice`
is stated with `Enabled`, so `TerminationClaim`'s premise set is
unsatisfiable at any instance with infinitely many supermajorities, and
[TODO.md](TODO.md) § Liveness's non-vacuity item should be read with
that in mind. It does not affect `Mvba.termination`'s truth — a stronger
premise — and the fix is the Chorus leg's to make in [Fairness.lean](../Cadence/Fairness.lean), so
it is reported there rather than made here.

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
| … and has timed out or left `v` | `+ 2δ` | `timeout_*` is move-enabled; at most one `adopt_prepqc` can intervene in `v` and change the highest held certificate, so one restart of the `δ` window |
| a timeout certificate for some view `≥ v` exists | `+ Δ` | either a correct validator is above `v`, which needs one, or the correct quorum's timeouts are all sent and `form_tc_*` is move-enabled; a first delivery, the timeouts retained by the first member to send one, which was in `v` then |
| `Synced (succ v)` | `+ Δ` | `sync_view` move-enabled for everyone at `≤ v`; a first delivery of a certificate formed after GST |

so `Synced (succ v) (X + C)` with **`C = τ_max + 2δ + 2Δ`** — the
supplement's `τ_{w+1} ≤ τ_w + 2Δ + T` (`lem:convergence`) at `δ = 0`.
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
| `msg_prepqc W e` | `+ Δ` | `form_prepqc` on the correct quorum's prepares, all on one `e` (`accepted_unique`) |
| every correct validator holds it | `+ δ` | `adopt_prepqc` |
| … and has `avail_ready` | acceptance `+ Δ_sync` | (Δ-avail), in parallel |
| every correct `Commit` sent | `max` of the two `+ δ` | `send_commit` |
| `msg_commitqc W e` | `+ Δ` | `form_commitqc` |
| every correct validator decided | `+ Δ` | `decide`, a network hop: the certificate was first obtained after GST, and reaches the others by broadcast — after the certificate, timers no longer matter |

so the certificate is at `E₀ + L_cert` with
**`L_cert = 3Δ + max(Δ + δ, Δ_sync) + 2δ`** — `lem:good-view`'s
`t*_w − τ_w` at `δ = 0`, `Δ_R = 0` — and the decisions at `E₀ + L_cert + Δ`.
Every network row is a first delivery: each message is sent from inside `W`
after `E₀ ≥ gst`, by correct validators, and retained, because at `E₀`
every correct validator is already in `W − 1` or `W`. That last fact is the
**one-view retention** (`retained_before`, the model's twin of
`lem:convergence`'s retention clause). It holds when `W − 1` is fresh and
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
of views `V` and `V + 1` as possibly unproductive (`lem:good-view` takes
`w ≥ V + 2`). Then: `Synced M (u + Δ + ρ)` by one retransmitted
`sync_view` hop, since the certificate below `M` exists at `N₀` but may
predate GST; `Synced (M + 1)` a further `C + 2ρ` on (the first burn);
`Synced W (u + Δ + ρ + 2ρ + n • C)` with `n ≤ |below v_L| + k` views burnt
in all; `W`'s first correct entry is after `N₀`, hence `E₀ ≥ u ≥ gst`; and
the second lemma decides everyone by `E₀ + L_cert + Δ`. If instead some
correct validator has decided before the chain completes, the composing
layer delivers its certificate to everyone within `Δ + ρ`
(`lem:decision-propagation`). Hence

  `ℓ = (Δ + ρ) + 2ρ + (|below v_L| + k) • C + L_cert + (Δ + ρ)`,

which is `O(kΔ)` when every constant is `O(Δ)` and the ramp is empty — the
supplement's `O(fΔ)` at `k = f + 1`.

**Against the supplement's own bound** (`thm:termination` at `eb1bb51`,
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
  indices (`TLRun.clk_max_le`). The cost the plan did not foresee was on the
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
  `FJustice`), and the view order is infinite by nature (`below vL`). It
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
  with plain `Enabled` (§6.2.4). At the concrete family it costs one lemma:
  once the run is idle only two assembly labels are enabled, because a
  certificate has one quorum that can assemble it at `ByzNSet 4`
  (`Mvba.Witness.enabled_idle`), and the tail fires both forever. The
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

*Auditor-first. The list says what each premise of the two MVBA liveness
theorems is and why it can hold. The model below the list shows that they
hold **together**. The detail is in §6.3.1–§6.3.3.*

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
  particular, weak fairness with plain enabledness does not contradict the
  rest at this instance.

**The ledger.** "Obvious" means an auditor can see by inspection that the
premise can hold. "Not obvious" means it needs the model.

Shared by both theorems (the instance):

* **Finitely many validators** (`Fintype node`): obvious, every real
  deployment has them. Model: `Fin 4`.
* **The quorum system** (`ByzNodeSet`, its axioms): obvious for
  `n ≥ 3f + 1`, and machine-checked for the whole family
  `byzNodeSetFinGen` ([ByzQuorum.lean](../Cadence/ByzQuorum.lean)). Model:
  `n = 4`, `f = 1`, validator 3 Byzantine.
* **A supermajority of correct validators** (`ByzNodeSetHonestQuorum`):
  obvious, since at most `f` validators are Byzantine. Model: `{0, 1, 2}`.
* **Views have successors, finitely many below each**
  (`ViewOrderEnum`): obvious for a view counter. Model: `ℕ`
  (`natViewOrderEnum`).
* **The model's assumptions** (`leader_functional`,
  `leader_honest_cofinal`): obvious, a leader schedule is a function and
  round-robin reaches every validator. Model: validator 0 leads every
  view.

The timed claim, `Mvba.timed_termination`:

* **The time theory** (a cancellative, Archimedean, linearly ordered
  monoid): obvious. Model: `ℕ`.
* **The schedule** (`Schedule`: `0 < Δ`, non-negative constants, a capped
  timeout that eventually exceeds the chain's latency): obvious. Model:
  `Schedule.fixedNat`, the paper's fixed timeout.
* **A correct leader in every `k` consecutive views** (`LeaderRotation`):
  obvious, round-robin gives `k = f + 1`. Model: `k = 1`.
* **The run is admissible** (`Sync`: bounded weak fairness after GST, a
  punctual view timer, availability within `Δ_sync`): **not obvious**
  together with the next three. `Mvba.admissible_exists` shows admissible
  runs exist, but its run has nobody proposing. Since step 5b the fairness
  clause is the supplement's network (§6.2.4, "The network clauses"): a
  network step is owed within `Δ` only for messages sent at or after GST
  by correct validators and retained, within `Δ + ρ` when they are
  retransmitted. Whenever `δ ≤ Δ` (the paper's `δ = 0`) that asks less of
  every label than before — a longer window only weakens a bounded-fairness
  clause, and every side condition does too — so admissibility is easier
  to meet, and the model below meets it for the same reason as
  before: its clock advances only where no fair label is move-enabled.
  The model sends nothing before GST, discards nothing, and every validator
  forms the certificates itself. So its run is admissible under either
  reading, and the change moves only the value of `ℓ`.
* **Every correct validator proposes by `t`**, **with a valid value**, and
  **none abandons before `max(t, GST) + ℓ`**: each obvious alone. Together
  with admissibility they need a run that stops on its own after deciding,
  since the caller may not stop it early; §6.3.2 says why that was not
  obvious.

The untimed claim, `Mvba.termination`:

* **(F-justice)**, weak fairness of every honest action with *plain*
  enabledness: **not obvious, and false at some instances.** At a
  `nodeset` sort with infinitely many supermajorities no run satisfies it
  once a prepare certificate exists (§6.2.4). At the finite quorum sorts of
  the concrete family it holds; the model shows that, since each quorum
  label that stays enabled forever also fires forever.
* **(A-viewsync)**, the view timer as ordering constraints: **not
  obvious** on its face, but it is a corollary of the timed premises
  (`Mvba.aViewSync_of_sync`), so it inherits their satisfiability. The
  model checks it directly.
* **(F-avail)**, the availability shares arrive: obvious.
* **`AllPropose`**, **`NoEarlyAbandon`**: obvious alone, and not
  obviously compatible with (F-justice) and the timer, for the same reason
  as in the timed claim.

**What the model found.** Every premise is satisfiable, and none needed
a change to its statement. Building the model did change the *model*: it
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
  at clock 0. They run the whole chain of view 0 and decide in it. At clock
  5 their view-0 timers expire, which the timing model requires; having
  decided, they have halted, so none times out. From then on the run is
  idle: it alternates the two quorum labels that are still enabled, the
  prepare and commit certificates of view 0, each a step that changes
  nothing, and the clock advances by one per step. Nobody abandons, so both
  forms of the caller's abandonment premise hold vacuously.
* **Why the proofs are short.** Every state of the run is a closed formula
  in its index: a record is present at index `n` iff the step that sets it
  is before `n`, and that step is `c + i` for a constant `c` per record and
  validator `i`. Each transition, and each premise, is then linear
  arithmetic over the index.
* **Why the timed fairness premise is easy here.** The clock advances only
  out of states at which no fair label is move-enabled. So from every
  index there is a later one on the same clock reading at which a given
  fair label is not move-enabled, and bounded weak fairness holds with its
  antecedent false. The run is fair because it never leaves an obligation
  pending while time passes.

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
`decide(…); abandon()` (the procedure `Decide` in `alg:mvba-cont3`, reached
from `line:mvba:qc-decide`, and the restart path), `abandon()` "halts all
MVBA sending and stops `W`", and the timeout fires only "upon `W` reaches
the view timeout and no decision in view `v`" (`line:mvba:timeout-send`).
That was so at the revision pinned then, `026dc8b`, and is so at the
current pin `eb1bb51`, whose termination proof now relies on it
([MvbaPlan.md](MvbaPlan.md) §11.3, C11).
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

#### 6.3.3 What the Chorus `TerminationClaim` will need

The same two things, after stage 5: a ledger of its premises in this form,
and one model satisfying all of them. The model can reuse this one for
the MVBA sub-state: its MVBA halts on its own after deciding, so Chorus,
which does not drive the MVBA's `abandon` in the single-slot model, needs
no abandonment for it. The premise that needs thought is **`ValidBridge`**,
the stated bridge between the MVBA's decision and the network's
certificates at Chorus's decision handlers. It relates two sub-states,
and a model must produce certificates that satisfy it, not merely an MVBA
run that decides. Plain-`Enabled` `FJustice` over Chorus's own quorum
labels is the second, with the same caveat as here and the same remedy at
finite sorts.

### 6.4 The Chorus leg: the kick-off record

*Written 2026-09-29, after `Chorus.termination` (PR #43) and before any
Lean. S1 is done since (§6.4.6, item 1, has its record); the rest is not. It supersedes §6's staging for Chorus
(steps 1–3), which predates the MVBA leg. §6.2 and §6.3 are the template.
Decisions are recorded with their reasons. Those marked **open** are for
Lars to take: item 1 above all, and the two class changes it depends on.*

**In short, for an auditor.** The paper proves two timed properties of
Chorus:

* **ℓ-termination** (`lemma:chorus-termination`): if every correct
  validator starts participating in the slot by time `t`, every correct
  validator finalizes by `max(t, GST) + 5Δ + ℓ_MVBA`;
* **d_tot-totality** (`prop:chorus-totality`): if one correct validator
  finalizes at time `t`, every correct validator finalizes by
  `max(t, GST) + Δ`.

Both hold under *Δ-synchronized participation*
(`def:delta-synchronized-participation`): once one correct validator
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
  only after finalizing" (`algorithm:cadence`, `line:abandon`). The
  untimed `SlotConsensusTemporal.termination` has that premise.
  `bounded_termination` also lacks "no correct validator starts before
  `D − Δ`", which is the Conductor's integrity
  (`lemma:conductor-integrity`); the proof of
  `prop:chorus-finalization-time` uses it in its first step. Without the
  first premise, a validator that abandons at once never finalizes.
  Without the second, a slot whose deadline lies far after `t` cannot
  finalize by `max(t, GST) + ℓ`. Either way the field is false for every
  faithful implementation, unless the implementation's own `Admissible`
  smuggles in the caller's conditions. The rely form of
  `MVBATemporal.termination` was adopted precisely to avoid that
  (§6.4.1, "The class change").
* **F2: the paper's message buffering needs a split hop.** "A message
  whose rule is blocked by this convention is not lost"
  (`subsection:chorus-protocol-overview`). A rule's network input is
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
  `def:window-synchronized`. With local steps that take time the ratchet
  loses δ per window. This is the Conductor leg's question. §6.4.6 states
  what this leg provides so that it is not blocked.
* **F4: to be confirmed. The 5Δ bound looks loose by one Δ.**
  `lemma:chorus-termination` splits at `T₀ = M + 4Δ + ℓ_MVBA` and adds Δ
  for totality (`M = max(t, GST)`). The inner split of
  `prop:chorus-finalization-time` at `T₀ − Δ` already handles early
  finalizers, and the only use of that proposition's premise "no correct
  validator stops before `T`" is covered by "abandon only after
  finalizing". So a single split at `T₀ − Δ` should give `M + 4Δ + ℓ_MVBA`,
  which is the bound an earlier, commented-out draft next to the lemma
  states. §6.4.3 records how to handle it if the proof confirms it.

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
* Fairness is bounded fairness on state-changing steps with a hop table.
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
  has invoked it, as `line:fb-abandon` does. Its successor-state parameter
  is harmless, since inputs carry no fairness.

The existing `propose j m` becomes the contract's `propose(P)`, with
`P ↦ m`, the class's `proposal := merkle_root` at
[Chorus/Compose.lean](../Cadence/Chorus/Compose.lean). Then gate every
rule that sends, with `participating i ∧ ¬ abandoned i`, and exempt the
rules that only process. That is the standing convention of
`subsection:chorus-protocol-overview`, rule for rule:

* **Gated, because they send.** `propose` and `deliver_chunk_assigned`
  (at the proposer), `vote`, `commit_sign_*`, `cast_fast_commit`,
  `fb_sign_*`, `cast_fallback_vote`, `mvba_propose` (the convention names
  it explicitly), `cast_fb_commit`, and `commit_assign_*`/`finalize_commit`.
  The paper's finalization rules re-broadcast the proof
  (`line:fast-rebroadcast-commitqc`, `line:fb-commit-rebroadcast`), and
  its totality proof relies on their being gated. The model's comment at
  "Commit decision" ("finalization on receipt has no active-participation
  precondition") then changes.
* **Exempt, because they process.** `record_chunk`, `aggregate_fastqc_*`,
  the decision handlers and `mvba_terminate`.
* **Anonymous capabilities.** `broadcast_commitqc_*` and
  `redisseminate_chunk` have no actor today. In the paper both are sends
  by a correct validator: the collector (`line:fast-broadcast-commitqc`),
  and the fallback-entry caster (`line:fb-redisseminate`). The faithful
  form gives each a sender parameter, gated when the sender is correct and
  unconstrained when it is Byzantine. Without that, Quiescence cannot
  attribute those messages. **Recommended**, since the family re-solves
  anyway.

Quiescence is then provable in the paper's own two-part shape
(`lemma:chorus-quiescence`):

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
  `prop:conductor-open-to-complete` applies ℓ-termination at a start time
  `max(t, GST) + d_tot` set by the Conductor, not at `D − Δ`.
* *B2, a gated product in Lean.* Wrap the Chorus transition system with
  participation ghosts and gate its labels outside Veil. Safety transfers
  by simulation, and nothing re-solves. The wrapper cannot forward
  `abandon` to the MVBA (`line:fb-abandon`) without stepping `mvba_st`
  outside Chorus's transitions. That breaks the simulation to Chorus's
  reachable states, on which every invariant rests. Without forwarding,
  Quiescence is false for the MVBA's messages after a fast-path
  finalization. The wrapper would also be a second semantics of Chorus
  that an auditor has to read beside the model. Every run-level lemma of
  stages 3–4 would have to be transported through it.

**Option C: change the class.** For example, drop the inputs from the
Chorus-facing class, or state Termination over "participates from the
start". Either is unfaithful to `mod:slotconsensus`, whose interface
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
  `mod:slotconsensus` lists it, and the lemmas carry it as "within
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
* PR #44's `mod:mvba` Agreement prose edit in Interfaces.lean.

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
inputs (§6.4.1). It is stated for `EnabledMove`, as in §6.2.4. The
§6.2.4 caveat about `Enabled` is thereby answered for the timed claim;
the untimed claim keeps plain enabledness. The proposal family becomes
its timed twin, `BoundedFairFamily`: if some `mvba_propose i v _` stays
move-enabled over the window, one of them fires within it. The clause,
generic in [Timed.lean](../Cadence/Timed.lean), with `gate l` the label's
local gate and `W = max (ref N + hop l) (ref N' + δ)`:

  **(Δδ-justice)** For `N ≤ N'`: suppose that at every index `n ≥ N` with
  `clk n ≤ W` at which `gate l` holds, `l` is move-enabled, and that
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
| `redisseminate_chunk` (the caster's chunk) | `finalize_commit` |
| `commit_assign_*` (a certificate someone else broadcast) | |

The table has three consequences:

* **Participation.** Every row whose rule is gated (§6.4.1) adds
  participation to its gate.
* **`mvba_propose` is conservative.** It is a Δ-row, although its
  case-(a) trigger (`line:fb-mvba-propose-fast`) reads only local
  FastQCs. With the split hop that costs nothing: the network part holds
  from `M + 2Δ + δ`, and the landmark gate opens at `D + 2Δ ≤ M + 3Δ`.
  So one row suffices, and splitting the action into the paper's two
  rules is optional.
* **The check.** At δ = 0 the table reproduces the paper's timeline term
  for term (§6.4.3), as §6.2.4's did for the MVBA. The MVBA leg's own
  finding C16 (N3, PR #44) questions a δ-row that consumes another
  party's certificate: the MVBA's `decide`. The two δ-rows above that
  read certificates, the decision handlers, rest on a different argument:
  the certificates travel inside the decided value. If step 5b
  reclassifies `decide`, re-check these two rows against that argument.

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

| Paper milestone (`prop:chorus-finalization-time`) | Model links, re-run with deadlines | Rows |
|---|---|---|
| `D ≤ t + Δ` | C2 at each correct start, with (P2) | — |
| by `M + Δ`: first-round votes | `eventually_voted`, then `eventually_quorum_cast` (`voted_implies_cast`) | `vote` δ |
| by `M + 2Δ`: second-round votes | `eventually_saturated` / `eventually_all_saturated` | aggregate Δ, sign/cast δ; `fb_sign_*` Δ, gate `D + Δ ≤ M + 2Δ`; `cast_fallback_vote` δ |
| by `M + 3Δ`: MVBA proposals, fallback chunks | `eventually_complete_fast_metablock`, `eventually_trigger`, `eventually_input`, `certifiedVector` (`ValidBridge` soundness); `redisseminate_chunk` | the proposal family Δ, gate `D + 2Δ`; aggregate Δ; redisseminate Δ |
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
**Decision (open, for S5 below):** state and instantiate the claim at the
paper's `5Δ + ℓ_MVBA` (plus the δ-terms), which is faithful and follows
by monotonicity. Prove the sharper bound as the named lemma it follows
from, and record the looseness in [PaperAlignment.md](PaperAlignment.md)
§6 as the MVBA leg recorded its `ℓ` correction. If the proof finds a use
of the outer split that this argument missed, the claim is unchanged and
F4 is withdrawn. The δ-multiple `c` is whatever the links count. It is
fixed by the proof, as `Lcert`'s was, and pinned by an `abel`-closed
equation.

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
`recoverProposals` (`line:da-recover-slot`). The model's `finalized`
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

#### 6.4.5 Premises and non-vacuity from the start

**The ledger, in draft.** "Obvious" and "not obvious" mean what they mean
in §6.3.

The instance, shared with the untimed claim:

* **Finitely many validators, `n = 3f + 1`, at most `f` Byzantine**
  (`Fin n`, `byzNodeSetFin`): obvious. `Fin 4` with one silent Byzantine
  validator.
* **An honest supermajority, `ViewOrderEnum`, `chorusTheory` and its
  assumptions**: obvious (§6.3).
* **The MVBA instance's hypotheses** (`LeaderRotation`, `Schedule`, a
  cancellative Archimedean time): obvious, `Schedule.fixedNat` over `ℕ`.
* **The deadline `D`**: any value.

The timing model:

* **(Δδ-justice) over Chorus's table, with the proposal family**: each row
  is obvious alone. Jointly they are **not obvious**, because the family
  quantifies over every value, including ones that never become
  proposable.
* **(P-phase)**: obvious. The markers fire at the clock readings `D`,
  `D + Δ`, `D + 2Δ`.
* **The MVBA's `Admissible` on the projection, with `Scheduled`**:
  obvious alone (`Mvba.admissible_exists`). Jointly **not obvious**,
  because Chorus's own fairness drives the MVBA's inputs.
* **`ValidBridge`**: **not obvious**. It fixes the MVBA theory's `valid`
  against Chorus's network at every index (§6.3.3).

The caller's conditions:

* **Everyone starts by `t`; starts are Δ-synchronized; nobody starts
  before `D − Δ`; nobody abandons before finalizing**: jointly obvious.
  Everyone starts at `D − Δ` and abandons (if at all) after finalizing.
  That is the Conductor's steady state.

The untimed claim after option A:

* **`FJustice` with plain `Enabled`**: not obvious, and false at
  infinite quorum sorts. It holds at `ByzNSet n`, provided the run's idle
  tail fires every stutter-enabled quorum label.
* **`MvbaAdmissible`, `ValidBridge`**: as above.
* **Eventual participation, and abandonment only after finalizing**:
  obvious.

**The model.** One model and one run, following §6.3.1, serve both
claims; the untimed projection forgets the clock. The run:

* `Fin 4` with validator 3 Byzantine and silent, one proposer, `ℕ` time,
  `Δ = 1`, `δ = 0`, `D = 1`, GST 0, and everyone participating at 0.
* The fast path. The proposal goes out at 0, votes at `D`, FastQCs and
  commit votes follow, and everyone finalizes. All of it happens at clock
  1, before the fallback arm opens at 2. Bounds are upper bounds, so an
  eager run may deliver at once.
* Then **everyone abandons**, as C1 permits. That disables the case-(a)
  proposals, so the MVBA receives no input. Its projection is the quiet
  run of `Mvba.admissible_exists`, which is trivially `Sync`, and
  `ValidBridge`'s completeness clause holds vacuously.
* The soundness clause holds with `valid := (· = v⋆)`. Here `v⋆` maps the
  proposer to its root and every other validator to `none`, which is the
  only certifiable vector in this run. With one proposer and no negative
  evidence, uniqueness is a short argument.
* The clock advances only at states where no row is move-enabled (the
  §6.3.1 device), and the untimed idle tail round-robins the
  stutter-enabled quorum labels.

A witness that runs the MVBA arm would be stronger evidence of the
proposal family and the completeness clause. It is not needed for joint
satisfiability, since one model suffices (§6.3). It can be added as a
second run if review asks for it.

**Order: after the model edit, and one witness for both.** On the current
model a witness cannot abandon. `advance_to_mvba_arm` is weakly fair, so
the case-(a) proposals are forced, and with them a full MVBA decision, the
handlers and the fallback commit round, all inside the run. That witness
would then be discarded when option A adds state and gates. So the untimed
non-vacuity item of [TODO.md](TODO.md) § Liveness should wait for S1
below and be built once, for both claims, as soon as the timed premises
are stated (S2). The witness depends on definitions only, so it can run
in parallel with the proofs. If option A is declined, the untimed witness
can go first on the current model, at the cost just described.

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

   Deviations from the plan, each small:

   * **`abandon` forwards every time**, not only "if mvbaInvoked"
     (`line:fb-abandon`). The difference is unobservable: the MVBA's own
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
     for its own next edit). The receipt family replays warm and
     `PreFix.lean` still finds its counterexample.
   * **The monitor**: the silent MVBA stub has no `abandon`, so `abandon` is
     never enabled under the monitor, a coverage gap of the same kind as
     the decision handlers ([Monitor.md](Monitor.md) §8). The fixtures gained
     `participate` lines and the collector argument by hand.
   * **Quiescence** is not proven here. The gates make it provable in the
     paper's two-part shape; the one-step statement belongs to S5 with the
     rest of the `SlotConsensusTemporal` instance.
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
3. **S3: totality and the timeline to `M + 3Δ`.** Totality comes first,
   because it is small and validates the scaffolding. Then the links up to
   the MVBA proposals. The reassessment asks two things: did the hop table
   survive the guards, and does the split hop keep the paper's arithmetic.
4. **S4: the MVBA tail and the assembly.** `T.termination` through the
   projection, the fallback commit round, and the case split, giving the
   bound. F4 is decided here.
5. **S5: the contract instances.** `SlotConsensusTemporal` at the new
   fragment, which includes:
   * Quiescence from the gates and the MVBA's `quiescence`;
   * `admissible_exists` from an idle run;
   * Termination, as the unbounded corollary of the bounded one.

   Then `SlotConsensusWithTotality`, and the `…_of_temporal` join with its
   `rfl` lemma. After that:
   * the [Cadence.lean](../Cadence.lean) rows and pins, with the verification-status
     text in [CLAUDE.md](../CLAUDE.md), [Architecture.md](Architecture.md)
     §4 and [CompositionContracts.md](CompositionContracts.md) §5;
   * the (A-sc-termination) entry, which moves from assumed to discharged.
6. **S6: non-vacuity.** The final ledger and the one witness (§6.4.5).
   It can start after S2 and run beside S3–S4. It touches no model file.

Total: six to eight sessions. As in the MVBA leg, the dominant risk is
statement churn: F1–F4 are the churn this record tries to absorb up
front, before any Lean.

**What the Conductor's timed claims need from this leg.** The
Conductor's Totality, `B`-Boundedness and `R`-Recovery
(`OrchestratorTemporal`) consume Chorus's claims in
`prop:window-synchronization` (totality), `prop:conductor-open-to-complete`
(ℓ-termination), and the recovery chain through `Φ_oc = ℓ_chorus + d_tot`
and the parameter assumptions of `algorithm:conductor`. For those proofs
to go through, this leg must hand over the following.

* **Premises the composition can discharge.** Each of Chorus's caller
  conditions has to be one a composed run proves:
  * participation by `t`: the glue invokes `participate` at `open`
    (`line:participate`);
  * Δ-synchronized participation: the Conductor's own opening totality
    (`lemma:conductor-totality`);
  * C2: `integrity_timing`, with `deadline s = start_time s + Δ`;
  * C1: the glue abandons only after finalizing (`line:abandon`).

  C1/C2 are phrased with that in mind, as antecedents over the class's
  own observables.
* **`ℓ` and `d_tot` as data, with closed values.** They appear in
  assumptions (1)–(4) of `algorithm:conductor`. They are fields already;
  the instance pins them.
* **Totality in the tolerance-parametric form of §6.4.4.** This is F3.
  The ratchet needs Chorus's latency not to exceed the tolerance the
  Conductor grants. At δ = 0 both are Δ, and the paper's induction goes
  through. At δ > 0 `max(Δ, d) + 2δ > d` for every `d`, so the Conductor
  leg has to choose. It can work at δ = 0, the paper's instantaneous
  local computation. It can find a δ-robust statement, for instance by
  re-synchronizing on the absolute start times, as
  `line:conductor-wait-for-open` does once the windows are ahead of the
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
    generic, and inertness only removes behaviours.
  * `cor:chorus-correctness-within-cadence` then closes the loop, which
    is §6 step 5.
