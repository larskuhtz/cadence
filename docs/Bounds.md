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
  them only in expectation / with high probability.

The model relates to these in three distinct ways:

1. **Bound-free paper theorems** (agreement, slot safety, integrity, …)
   appear as the *same* theorems in the model.
2. **Timed-premise theorems** appear with the premise transported to its
   state-level consequence (proposal inclusion's `deadline − Δ ≥ GST`
   becomes the hypothesis `all_honest_recorded`; the liveness theorems'
   *saturation* hypotheses are the state consequences of what fairness
   delivers).
3. **The bounded statements themselves** are not model theorems at any
   abstraction level — they are the named inventory rows
   ((A-sc-termination), (A-acs-termination), (A-acs-totality),
   (A-orch-totality), (A-orch-boundedness), (A-orch-recovery);
   [`Architecture.md`](./Architecture.md) §4 item 4,
   [`Cadence/Interfaces.lean`](../Cadence/Interfaces.lean)). What the
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
protocol (2026-08; recorded here so the constraints inform the decision,
not as Veil documentation — tool-side work belongs in the fork):

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
  combinatorial/discrete core (quorum reasoning over 98 properties ×
  39 actions) is exactly where SMT earns its keep.

None of these constraints bites route (a): the add-on schedule theorem is
plain Lean over an abstract order, outside the Veil pipeline entirely.

## 5. Recorded decision

Bounds are currently out of scope ([`Architecture.md`](./Architecture.md)
§4 item 4) and stay so until timing claims become a priority. When they
do: route (a) first — cheap, no model change, pins the schedule
arithmetic; route (b) Conductor-first if in-model timing is wanted, with
the three design costs above addressed up front; route (c) only against
demonstrated benefit. Ordering relative to the L2S extension (the fork's
`lars/liveness` branch) is decided then — the two are complementary, and
the ghost clock would incidentally hand L2S its simplest ω-target
(`infinitely_often tick`).
