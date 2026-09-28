# Bounds — the paper's Δ-bounds and the model

*Design notes, not a description of what is proven. This document records
how the paper's concrete finite bounds relate to the model's theorems, why
the two are incomparable rather than ordered by strength, and the routes by
which bounds could be brought into the model — including tooling
constraints observed in practice. The proven liveness state of affairs is
[`Liveness.md`](./Liveness.md); the open-items list is
[`TODO.md`](./TODO.md).*

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
  them only in expectation / with high probability. The first hole has a
  referent in this development: the MVBA instantiation of the
  paper repository's internal supplement is modelled
  ([`Cadence/Mvba.lean`](../Cadence/Mvba.lean)), and `ℓ_MVBA` is the field
  `ℓ` of `MVBATemporal`
  ([`Cadence/Mvba/Compose.lean`](../Cadence/Mvba/Compose.lean)) — data, next
  to the Termination it bounds (the supplement's `thm:termination`,
  `O(fΔ)`); the model is untimed, so the bound stays a paper quantity.

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
   (A-orch-recovery); [`Architecture.md`](./Architecture.md) §4 item 4,
   [`Cadence/Interfaces.lean`](../Cadence/Interfaces.lean),
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
[`ChorusDesign.md`](./ChorusDesign.md) §3.1.1); and guard vacuity — in
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
  [`Architecture.md`](./Architecture.md) §2) is exactly where SMT earns its
  keep.

None of these constraints bites route (a): the add-on schedule theorem is
plain Lean over an abstract order, outside the Veil pipeline entirely.

## 5. Recorded decision

Bounds are currently out of scope ([`Architecture.md`](./Architecture.md)
§4 item 4) and stay so until timing claims become a priority. One input to
that decision changed after this was written: the MVBA now has an untimed
liveness theorem, so there is a leg of route (a) that **removes** an
assumption rather than attaching a bound to one (§6.1). Whether that
re-ranks bounds against the two items ahead of them in
[`TODO.md`](./TODO.md) § Soundness is a call to make deliberately, not a
consequence of the MVBA work. When they do go ahead: route (a) first — cheap, no model change, pins the schedule
arithmetic; route (b) Conductor-first if in-model timing is wanted, with
the three design costs above addressed up front; route (c) only against
demonstrated benefit. Ordering relative to the L2S extension (the fork's
`lars/liveness` branch) is decided then — the two are complementary, and
the ghost clock would incidentally hand L2S its simplest ω-target
(`infinitely_often tick`).

## 6. Route (a): the worked plan

Recorded so a future session can pick this up without re-deriving the
design. Priority context: this ranks *behind* primitive instantiation and
the (M-frame) checker ([`TODO.md`](./TODO.md) § Soundness) on
auditor-confidence per effort, and *ahead* of L2S on near-term
value-per-effort — it is executable today, entirely in plain Lean, with
none of §4's tooling constraints in play.

**Depth decision.** Prove the theorem over **real timed runs of the
generated transition system**, not over abstract milestone propositions.
A run is `σ : ℕ → State` stepping through the actual Chorus transitions
with a monotone clock `c : ℕ → T`, where `T` carries a linear order plus
two abstract inflationary monotone shifts (`+Δ`, `+ℓ_MVBA`) — no `Real`,
no Archimedean axiom, `max` from the order. Every run point is reachable,
so the chain theorems of [`Liveness.md`](./Liveness.md) §1 apply at every
milestone state. The abstract-propositions variant is the fallback only:
it checks arithmetic an auditor can check by eye.

**Hypotheses.** One named per-seam bound assumption per temporal step of
the chain ([`ChorusDesign.md`](./ChorusDesign.md) §7): "this seam
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

### 6.1 The MVBA leg, which did not exist when the plan above was written

Step 3 above treats `ℓ_MVBA` as a **per-seam hypothesis** — "the oracle seam
completes within `ℓ_MVBA`" — because when this plan was written the MVBA had
no liveness theorem to discharge it with. It has one now
(`Mvba.termination`, [`Liveness.md`](./Liveness.md) §2.1), so there is a
second leg available: *prove* `ℓ_MVBA` rather than assume it.

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
only one not derivable in an untimed model ([`MvbaPlan.md`](./MvbaPlan.md)
§3.7); with a clock both of its clauses become theorems — bounded post-GST
delivery gives the decision chain a finite latency, timeout growth makes some
view's budget exceed it, and (A-leader-rotation) supplies the honest leader.
That in turn is what `MVBATemporal.termination` needs, which `Cadence.lean`
calls "the smallest gap of the three implementations", and it is the formal
version of the trust-base move §2.1 describes informally.

**It also subsumes an open item.** [`TODO.md`](./TODO.md) § Liveness asks for
a run witnessing that `Mvba.termination`'s five premises are jointly
satisfiable. `MVBATemporal.admissible_exists` requires constructing admissible
timed runs anyway, so that witness falls out of this leg rather than needing
a session of its own. It is not worth doing separately.

This leg can run **in parallel with** the Chorus run-level liveness leg;
the rules that keep the two from colliding — and the one piece of design
they share, the projection from a composed run to an MVBA run — are
[`Liveness.md`](./Liveness.md) §4.1.

**Staging**, in the shape of §6's:

1. Timed runs over `Mvba`'s generated transition system, and the time
   theory with a growing timeout schedule. Reuses §6 step 1's scaffolding if
   the Chorus leg went first.
2. The chain latency bound: the links of `Mvba/Liveness.lean` from the
   leader's `Pre-Prepare` to the commit certificate, each with a Δ attached.
   Mostly plugging in proven theorems, and the cheap validation of the
   scaffolding.
3. The entry bound — every correct validator enters the good view within Δ
   of the first — which is the quantitative refinement of
   `eventually_entered_good`. The untimed argument's structure carries over
   (the climb, the common view, the overshoot bound); the bounds are new.
4. Discharge both (A-viewsync) clauses, then `MVBATemporal.termination`;
   axiom pins, docs, and the `Cadence.lean` row moves from conditional to
   a discharged instance.


**Placement.** A sibling of the end-theorem files — e.g.
`Cadence/Chorus/Schedule.lean` at the `Compose`/`Pigeonhole`/`Counting`
layer: plain Lean, kernel-only, in-file `#guard_msgs` pins, a row and pin
at the audit root. On completion, the corresponding fields leave the
`…Temporal` classes (`SlotConsensusTemporal`,
`OrchestratorTemporal`) and are proven in the `…_of_temporal`
definitions — the contract fields in
[`Cadence/Interfaces.lean`](../Cadence/Interfaces.lean) themselves do not
change, which is the point of stating them there.

**Effort and risk.** Chorus-only (steps 1–3) ≈ 2–4 sessions; the full
bounded story ≈ 5–8. The dominant risk is statement-design churn, not
proof difficulty — the state-level content is already proven. Expected
finding class: a misstated or missing premise in one of the paper's
bounded lemmas (the timeline arithmetic has drifted once already,
`d_tot`: `2Δ → Δ`); protocol-level findings are unlikely, since the state
content is verified. The timed-run scaffolding is reusable by a later
L2S bring-up — nothing here is throwaway.

### 6.2 The MVBA leg, workshopped (2026-09-16)

The per-seam statements §6 asked to be settled before any Lean, settled.
Everything below is a *design*, not a result: what is proven is what
[`Cadence/Mvba/Schedule.lean`](../Cadence/Mvba/Schedule.lean) says is proven,
and its `#guard_msgs` pins, not this section. The section exists so that the
decisions and the two findings are not re-derived, and so that a reader can
check the premises against the supplement without reading Lean.

**Decisions in one place.**

* The clock is a *product*: timed runs are labelled runs of the generated
  `Mvba` transition system paired with a clock sequence, and the contract
  is instantiated at the state type `Mvba.State × time`, through a generic
  lift of the safety fragment (§6.2.1). No model change; nothing under
  `Mvba/Proofs/` re-solves.
* Time is a linearly ordered additive commutative monoid with `max`
  (§6.2.2). The theorem needs no Archimedean axiom; the non-vacuity
  witness `admissible_exists` needs an unbounded clock and gets it from
  Mathlib's `Archimedean` and `0 < Δ`.
* The timeout schedule is a function of the view, **bounded above** and
  **eventually above the chain latency** (§6.2.3). The paper's fixed known
  timeout is the special case; *unbounded* backoff is incompatible with the
  contract's fixed `ℓ`, which is the first finding.
* Fairness is bounded weak fairness after GST on **state-changing** steps,
  with a per-label hop bound — `Δ` for a step that consumes another party's
  message, `δ` for a local step — and the window measured from
  `max(now, gst)` so that a clock jump over a pending obligation's deadline
  is inadmissible (§6.2.4). Plain enabledness, as in `Fairness.lean`, would
  make every admissible model unsatisfiable once a proposal exists; that is
  the second finding and it concerns the untimed leg too.
* (A-viewsync) is not assumed anywhere. Its two clauses are derived as a
  corollary of the timed premises; the bound itself is proven directly by
  a timed re-run of the chain and does **not** consume `Mvba.termination`
  (§6.2.7 says why it cannot).

#### 6.2.1 The clock is read off the state, and the state has none

`MVBATemporal.clock : state → time`, and `TimedRun … clock` reads the clock
off each state; that is right for the Conductor, whose `now` is a state
field, and it was written that way for all three modules. `Mvba.State` has
no clock, and §6's "monotone clock `c : ℕ → T`" alongside the state is a
different object. Three ways to reconcile them were weighed:

1. **A ghost `now` in `Mvba.lean`** (§3(b)'s device with no guards). Changes
   every VC statement — a cold re-solve of the family — moves the audit pin,
   and adds a 26th label that the read-only label classification of
   `Mvba/Liveness.lean` would silently file under `JusticeLabel`, so
   `FJustice` would demand weak fairness of `tick`. Out, on
   [`Liveness.md`](./Liveness.md) §4.1's rules alone.
2. **Change `TimedRun` to carry its own clock sequence.** Arguably the right
   design for untimed models, but an edit to `Interfaces.lean` — a joint
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
`mvba_of_temporal` is not the join used and `System.lean` does not
automatically inherit the timed instance. Closing it is one of two edits —
instantiate Chorus at the lifted fragment in `System.lean` (the composed
system's MVBA sub-state then carries the clock the composition's own timing
needs anyway), or route 2 — and both are decisions to take with the Chorus
leg when its composition step (§6 step 5) is designed. The labelled timed
run `Cadence.TLRun` is the load-bearing object; the product is a thin
bridge, and if route 2 is taken later the bridge is deleted and the
premises are restated on `TLRun` unchanged.

The Chorus leg's projection from a composed run to an MVBA run
([`Liveness.md`](./Liveness.md) §4.1) lifts to `TLRun` by carrying the
clock along the projected indices; `TLRun.toLRun` is the forgetful map, so
the projection is theirs to define and this leg's timed form is its
pullback, not a second definition.

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

Two remarks on what the theory does **not** assume. The **termination
bound needs no Archimedean axiom** — every quantity in it is a finite sum
of the constants. `admissible_exists` does: a `TimedRun` is unbounded by
definition (`clock_unbounded`), so exhibiting one needs an unbounded
monotone sequence in `time`, and `Archimedean time` with `0 < Δ` gives
`n ↦ c + n • Δ`. That the witness, not the theorem, carries the
Archimedean assumption is worth keeping visible: it is the one place §3(a)'s
"finite schedules need neither" was too optimistic, and the cause is the
contract's non-Zeno field, not the schedule.

#### 6.2.3 The schedule, and the first finding

The supplement fixes the timer in one sentence (`subsec:mvba-protocol`):
*"The view timeout is chosen so that, after GST, it exceeds
`Δ_R + 3Δ + max{Δ, Δ_sync}`. If the implementation uses timeout backoff
rather than fixed known bounds, the timeout is eventually increased beyond
this value."* `thm:termination`'s proof then counts with a fixed timeout —
*"the view timeout is itself `O(Δ)`"* — to reach `O(fΔ)`.

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
[`PaperAlignment.md`](./PaperAlignment.md) §6. §6.1's "a sequence `Δ_v`
unbounded relative to a fixed bound" was therefore the wrong requirement:
the sequence must be *eventually above* `L_cert` and *bounded*, which is
what (S-ramp) and (S-cap) say.

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
| (Δ-justice) | `BoundedJustice` | for every `JusticeLabel l`: if `l` is **move-enabled** at every index `n ≥ N` with `clk n ≤ ref N + hop l`, then `l` fires within `hop l` of `N`. `hop l = Δ` for a step that consumes another party's message, `δ` for a local step (table below) | post-GST delivery within `Δ`; local computation within `δ` (the paper: instantaneous, `δ = 0`) |
| (T-timer) | `TimerPunctual` | for honest `i`: (T1) `expire_timer i v` fires at `n` only if `clk m + τ v ≤ clk n` for some `m ≤ n` with `entered i v` at `m`; (T2) if `entered i v` at `m`, then `timer_expired i v` at some `n ≥ m` with `clk n ≤ clk m + τ v` | the local view timer, restarted on entry, expiring after exactly `τ v` |
| (Δ-avail) | `AvailWithin` | for honest `i`: `accepted i v e` at `m` ⇒ `avail_ready i e` within `Δ_sync` of `m` | `lem:avail-progress`'s `Δ_sync` |

`hop`, the per-label bound, is a classification of the sixteen
`JusticeLabel`s by what the guard consumes:

| `Δ` (reads another party's message or certificate) | `δ` (local) |
|---|---|
| `handle_preprepare_first`, `handle_preprepare` (the leader's `Pre-Prepare`) | `leader_propose_first`, `leader_repropose`, `leader_propose_fresh` (upon entering the view; `Recover` is the identity here) |
| `form_prepqc`, `form_commitqc`, `form_tc_lock`, `form_tc_nolock` (a quorum of others' signatures — the model's separation of *delivery* from *assembly* puts the delivery `Δ` on the assembly) | `adopt_prepqc`, `send_commit`, `decide`, `timeout_qc`, `timeout_noqc` (own state and a certificate already counted) |
| `sync_view`, `sync_view_adopt` (a timeout certificate) | |

With `δ = 0` the model's latency is the paper's constant (§6.2.6), which is
the check that the classification is the paper's and not a convenience.

**Move-enabledness, and the second finding.** `Fairness.lean`'s `Enabled`
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
[`TODO.md`](./TODO.md) § Liveness's non-vacuity item should be read with
that in mind. It does not affect `Mvba.termination`'s truth — a stronger
premise — and the fix is the Chorus leg's to make in `Fairness.lean`, so
it is reported there rather than made here.

**What is deliberately absent**, the checklist §6 asked for: no clause
mentions `decided`, `msg_commitqc`, a good view, a leader, or GST as a
model event. Every clause relates an environment event — a label firing,
a clock reading — to a guard or a local record. (A-viewsync)'s shape was
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
the schedule; the exact constants live in `Schedule.lean`, this table is
their derivation.

**A Byzantine-led (or ramp) view `v`, from `Synced v X`** — every correct
validator has entered some view `≥ v` by time `X ≥ gst`:

| milestone | by | why |
|---|---|---|
| every correct validator still in `v` has its timer expired | `X + τ v` | (T2) from its entry, which is `≤ X` |
| … and has timed out or left `v` | `+ 2δ` | `timeout_*` is move-enabled; at most one `adopt_prepqc` can intervene in `v` and change the highest held certificate, so one restart of the `δ` window |
| a timeout certificate for some view `≥ v` exists | `+ Δ` | either a correct validator is above `v`, which needs one, or the correct quorum's timeouts are all sent and `form_tc_*` is move-enabled |
| `Synced (succ v)` | `+ Δ` | `sync_view` move-enabled for everyone at `≤ v` |

so `Synced (succ v) (X + C)` with **`C = τ_max + 2δ + 2Δ`**. Neither the
leader nor the outcome of `v` enters: a view that happens to decide is
burnt like any other, which is what makes the lemma unconditional.

**The good view `W`** — correct leader, `τ W > L_cert`, first correct entry
at `E₀ ≥ gst`:

| milestone | by | why |
|---|---|---|
| every correct validator is in `W` | `E₀ + Δ` | the certificate below `W` exists at `E₀`; `sync_view` is a `Δ` hop; nobody is above `W` (below) |
| the leader's `Pre-Prepare` | `+ δ` | `leader_*` local |
| every correct validator accepted and sent `Prepare` | `+ Δ` | `handle_preprepare` |
| `msg_prepqc W e` | `+ Δ` | `form_prepqc` on the correct quorum's prepares, all on one `e` (`accepted_unique`) |
| every correct validator holds it | `+ δ` | `adopt_prepqc` |
| … and has `avail_ready` | acceptance `+ Δ_sync` | (Δ-avail), in parallel |
| every correct `Commit` sent | `max` of the two `+ δ` | `send_commit` |
| `msg_commitqc W e` | `+ Δ` | `form_commitqc` |
| every correct validator decided | `+ δ` | `decide` — after the certificate, timers no longer matter |

so the certificate is at `E₀ + L_cert` with
**`L_cert = 3Δ + max(Δ + δ, Δ_sync) + 2δ`** and the decisions at
`E₀ + L_cert + δ`. Every step above needs no correct validator to have
timed out in `W` or entered a view above `W`: a `W`-timer of a correct
validator fires at `≥ E₀ + τ W > E₀ + L_cert` by (T1) and clock
monotonicity, a view above `W` needs a correct timeout in `W`
(`entered_le_of_no_timeout`, in its prefix form), and every guard the
chain needs is stable on that prefix. At `δ = 0` this is
`3Δ + max(Δ, Δ_sync)`, the supplement's constant with `Δ_R = 0` — `Recover`
is the identity in this model (`Mvba.lean`, "The value type").

**The assembly.** Let `N₀` be the last index with `clk ≤ u` (the state at
time `u`; every proposal is at or before it), `M` the highest view any
validator has entered at `N₀` — a maximum over a finite list, since each
step enters at most one view — and `W` the first correct-led view at or
above `max(succ M, v_L)`, which (A-leader-rotation-k) places within `k`
views. Then: `Synced M (u + Δ)` by one `sync_view` hop, since the
certificate below `M` exists at `N₀`; `Synced W (u + Δ + n • C)` by at most
`n ≤ 1 + |below v_L| + k` applications of the first lemma; `W`'s first
correct entry is after `N₀`, hence `E₀ ≥ u ≥ gst`, and `E₀ ≤ u + Δ + n • C`;
and the second lemma decides everyone by `E₀ + L_cert + δ`. Hence

  `ℓ = Δ + (1 + |below v_L| + k) • C + L_cert + δ`,

which is `O(kΔ)` when every constant is `O(Δ)` and the ramp is empty — the
supplement's `O(fΔ)` at `k = f + 1`. The caller's second premise enters
where `NoEarlyAbandon` did: no correct validator abandons at a clock
`≤ u + ℓ`, so `¬ abandoned` holds on every prefix the argument uses.

#### 6.2.7 What is proven where, and what (A-viewsync) becomes

`Mvba.termination` is **not consumed** by the bound and cannot be: it
yields `∃ n, decided`, and no timed premise turns an index into a clock
reading after the fact. The bound is a re-run of the chain with "within
`D`" in place of "eventually" — each of `Liveness.lean`'s links is
`enabled_<action>` (guards ⇒ enabledness) + one weak-fairness step +
`<action>_effect`; the timed twin keeps the first and third and replaces
the second by one (Δ-justice) step and a stability argument on the window.
`eventually_forall`'s twin is a maximum of indices — the clock is
monotone, so the latest of several bounded firings is still within the
bound. That is the sense in which §6.1's "mostly plugging in proven
theorems" is right, and the sense in which it is not: the temporal glue is
rewritten in full.

What *is* derived from the untimed file, as a corollary, is
**(A-viewsync)**: `AViewSync (tr.toLRun)` for every admissible `tr`, with
`W` the good view above. Its first clause is (T2) plus `clock_unbounded`;
its second is the good-view lemma's certificate time against (T1). That
theorem is the formal version of the trust-base move
[`Liveness.md`](./Liveness.md) §2.1 describes, and it retires the only
premise of `Mvba.termination` that was not fair scheduling or a caller's
condition. `TODO.md` § Liveness's witness item is discharged by
`admissible_exists`: the run in which no one proposes and the environment
only marks availability, at every sort, with its clock `c + n • Δ`;
`Admissible` holds of it because no `JusticeLabel` is move-enabled at any
of its states (sixteen guard facts, each one line, and
`greater_than_third_nonempty` for the assemblies).

#### 6.2.8 Staging, revised

Reassess after step 2, as §6 says. No step touches the model, the proof
files, `Interfaces.lean`, `Fairness.lean` or `Mvba/Liveness.lean`.

1. **This session.** [`Cadence/Timed.lean`](../Cadence/Timed.lean): `TLRun`,
   the `TotalOrder` bridge, move-enabledness, bounded fairness and its
   contrapositive, the bounded finite-conjunction lemma, `MVBASafety.timed`
   and `TLRun.toTimedRun`. [`Cadence/Mvba/Schedule.lean`](../Cadence/Mvba/Schedule.lean):
   `hop`, `Schedule` with its hypotheses, the four clauses, `Admissible`,
   (A-leader-rotation-k), `ℓ`, and the target as a `Prop`-valued
   definition **before** any proof — `Liveness.lean`'s discipline.
2. The good-view lemma: the eight timed links, the prefix form of
   `entered_le_of_no_timeout`, the stability arguments. The cheap
   validation of the scaffolding, and where a misclassified `hop` would
   show up.
3. The burn lemma, `entered_finite`, the successor-chain count against
   `below v_L`, the assembly, and `ℓ`.
4. `MVBATemporal` at the lifted fragment: `admissible_exists` and
   `termination`; `AViewSync_of_admissible`; axiom pins; the `Cadence.lean`
   row moves from conditional to discharged; the "no full instance is
   fabricated" text in `CLAUDE.md` and `Architecture.md` §4 gains the
   timed instance and its seam; the joint decision of §6.2.1 is put to the
   Chorus leg.
