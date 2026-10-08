# Bounds — the paper's Δ-bounds and the timed claims

*The timed claims of the MVBA and of Chorus: their timing models and
their findings. [The guide's chapter 6](https://larskuhtz.github.io/cadence/guide/components/) introduces the
claims.*

This document is the design behind the timed claims of the MVBA and of
Chorus: how the paper's bounded statements map onto theorems, the timing
model each claim assumes and why it has that shape, and the findings the
work produced (F1–F15). The claims themselves and their axiom pins are in
[Cadence.lean](../Cadence.lean); every premise is listed once, with its
role and its witness, in [Premises.md](Premises.md). The Conductor's timed
claims and the composed system's are [ConductorBounds.md](ConductorBounds.md).
How the work was planned and staged is in [History.md](History.md)
§ "From Bounds.md".

## 1. What the paper proves, and what is proven here

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
* **The primitive bounds**: `ℓ_MVBA` (Module 3 (`mod:mvba`)) and the ACS's `ℓ`
  (Module 4 (`mod:acs`)) are *assumed module properties*, stated as deterministic
  bounds — an idealisation, since the randomised constructions satisfy
  them only in expectation / with high probability.

Every one of these bounded statements is a theorem here, over timed runs of
the models' own transition systems:

* **`ℓ_MVBA` is proven, not assumed.** The MVBA of the paper repository's
  internal supplement is modelled ([Cadence/Mvba.lean](../Cadence/Mvba.lean)),
  and the instance `Mvba.mvbaTemporal`
  ([Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)) proves the
  Termination it bounds, Supplement, Theorem 2 (`thm:termination`),
  `O(fΔ)` (§6.2).
* **Chorus's `ℓ`-termination and `d_tot`-totality** are
  `Chorus.timed_termination` (with the sharper
  `Chorus.timed_termination_tight`) and `Chorus.totality`, and the contract
  instances `Chorus.chorusTemporal` and `Chorus.chorusWithTotality` (§6.4).
* **The Conductor's Totality, `(2W − p)`-Boundedness and `(2Wτ)`-Recovery**
  are `Conductor.totality`, `Conductor.boundedness` and `Conductor.recovery`,
  with the instances `Conductor.conductorTemporal` and
  `Conductor.conductorWithTotality`, for every ACS meeting its contract
  ([ConductorBounds.md](ConductorBounds.md)).
* **Corollary 4 and the composed system's claims** are `Composed.corollary4`,
  `Composed.boundedConcurrency`, `Composed.liveness` and
  `Composed.censorship` ([ConductorBounds.md](ConductorBounds.md)).

The ACS's `ℓ` stays an assumed module property: the ACS is an assumed
module, consumed through its contract.

The model relates to the paper's results in three ways:

1. **Bound-free paper theorems** (agreement, slot safety, integrity, …)
   appear as the *same* theorems in the model.
2. **Timed premises of safety-fragment theorems** keep their state-level
   form (proposal inclusion's `deadline − Δ ≥ GST` is the hypothesis
   `all_honest_recorded`).
3. **The bounded statements** are fields of the full module contracts,
   stated over timed runs ([Cadence/Interfaces.lean](../Cadence/Interfaces.lean):
   `MVBATemporal`, `SlotConsensusTemporal`, `SlotConsensusWithTotality`,
   `OrchestratorTemporal`, `OrchestratorWithTotality`), and each
   implementation's instance proves them from named premises
   ([Premises.md](Premises.md)). Each claim is stated as a `Prop`
   definition before its proof, in the leg's `Schedule.lean`
   ([Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean),
   [Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean),
   [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean),
   [Composed/Schedule.lean](../Cadence/Composed/Schedule.lean)), so the
   statement an auditor checks against the paper is separate from its
   proof. The untimed liveness claims (`Mvba.termination`,
   `Chorus.termination`) are their bound-erased forms
   ([Liveness.md](Liveness.md)).

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
assumption-minimal ones (and eventualities for which no deterministic
bound exists at all).

## 3. How time enters

**(a) No model carries a clock.** A timed claim is plain Lean over *timed
runs* of a model's own generated transition system: a run with a clock
sequence beside its states (`TimedRun`, and its labelled form `TLRun`,
[Timed.lean](../Cadence/Timed.lean)). Every run point is reachable, so every
state-level theorem applies at every milestone, and no Veil model or proof
family changes for a timed claim. The time theory is an ordered monoid, not
`Real` (§6.2.2).

**(b) The Zeno guard is a property of runs.** A deadline is met only if the
firing step's post-state is inside the window, so a run whose clock jumps
past a pending obligation's deadline satisfies no bounded-fairness clause
and is not admissible (§6.2.4). This takes the place of a ghost clock with
a guarded `tick` action inside a model. The alternatives weighed, and the
tooling constraints recorded at the time, are in [History.md](History.md)
§ "From Bounds.md"; so are the sections 4 and 5 that this document had
while the legs were planned, which is why the numbering continues at 6.

## 6. The timed legs

Each leg has the same shape: the claim stated as a `Prop` before any proof,
the timing model as named run premises, the proof as a re-run of the
untimed chain with deadlines, a contract instance, and a witness showing
that the premises hold together.

* **The MVBA** (§6.2, §6.3): `Mvba.bounded_termination`, the instance
  `Mvba.mvbaTemporal` joined into `Mvba.mvbaFull`, and the witness
  `Mvba.timedTermination_premises_satisfiable`.
* **Chorus** (§6.4): `Chorus.timed_termination`,
  `Chorus.timed_termination_tight` and `Chorus.totality`; the instances
  `Chorus.chorusTemporal` and `Chorus.chorusWithTotality`, joined into
  `Chorus.slotConsensusFull`; the witnesses in
  [Chorus/Witness.lean](../Cadence/Chorus/Witness.lean).
* **The Conductor and the composition** (§6.5):
  [ConductorBounds.md](ConductorBounds.md).

The premises stay minimal and checkable against the paper's: a premise
that smuggled in a conclusion would void the claim, and
[Premises.md](Premises.md) §7 checks that every premise is used.

### 6.1 The MVBA leg: why `ℓ_MVBA` is proven

The paper takes `ℓ_MVBA` as an assumed module bound. The development proves
it for the supplement's MVBA, and so removes an assumption rather than
attaching a bound to one: (A-viewsync), the one premise of the untimed
`Mvba.termination` that is neither fair scheduling nor a caller's
condition, is a theorem of the timed premises (`Mvba.aViewSync_of_sync`,
§6.2.7). The plan the leg started from is in [History.md](History.md)
§ "From Bounds.md".

### 6.2 The MVBA leg: the timing model

The timing model of the MVBA's bounded claim, and why it has its shape.
What is proven is what [Cadence/Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean)
states and its `#guard_msgs` pins confirm; this section lets a reader check
the premises against the supplement without reading Lean.

**Decisions in one place.**

* The clock belongs to the run: a timed run is a labelled run of the
  generated `Mvba` transition system with a clock sequence, and the
  contract is instantiated at `mvbaSafety th` itself (§6.2.1). No model
  change; nothing under `Mvba/Proofs/` re-solves.
* Time is a linearly ordered additive commutative monoid with `max`
  (§6.2.2); the bound's proof also needs it cancellative. The theorem needs
  no Archimedean axiom; the non-vacuity witness `admissible_exists` needs an
  unbounded clock and gets it from Mathlib's `Archimedean` and `0 < Δ`.
* The timeout schedule is a function of the view, **bounded above** and
  **eventually above the chain latency** (§6.2.3). The paper's fixed known
  timeout is the special case; *unbounded* backoff is incompatible with the
  contract's fixed `ℓ`, which is the first finding.
* Fairness is bounded weak fairness after GST over plain enabledness,
  with the window measured from `max(now, gst)` so that a clock jump over a
  pending obligation's deadline is inadmissible (§6.2.4). A local step is
  held to `δ`. A step that consumes another party's message is held to what
  the supplement's network guarantees: `Δ` for messages sent at or after
  GST by correct validators and retained, `Δ + ρ` for the retransmitted
  classes (`ρ` is the supplement's retransmission interval `ρ_mvba`, the
  schedule's field `ρ`). Plain enabledness is the right notion because
  every fair action of the model fires once (§6.4.7); a fair label that
  stays enabled after firing would make the premise unsatisfiable, which
  was the second finding (§6.2.4).
* (A-viewsync) is not assumed anywhere. Its two clauses are derived as a
  corollary of the timed premises; the bound itself is proven directly by
  a timed re-run of the chain and does **not** consume `Mvba.termination`
  (§6.2.7 says why it cannot).

#### 6.2.1 The clock belongs to the run

`TimedRun` carries its own clock sequence `clk : Nat → time`
([Interfaces.lean](../Cadence/Interfaces.lean)), and the temporal classes
have no clock field. A module whose state has a clock says so in its own
`Admissible`: `OrchestratorTemporal.clock_agrees` ties a Conductor run's
clock to its `now`. The MVBA and Chorus have no clock in their state.
`Mvba.mvbaTemporal` is instantiated at `mvbaSafety th`, and the full class
is `Mvba.mvbaFull := mvba_of_temporal th (mvbaTemporal …)`, whose fragment
is by `rfl` the one [System.lean](../Cadence/System.lean) plugs into Chorus.

The labelled timed run `Cadence.TLRun` is the load-bearing object: the
premises are stated on it, and `TLRun.toTimedRun` is the label-forgetting
map to the contract's `TimedRun`. The Chorus leg's projection from a
composed run to an MVBA run ([Liveness.md](Liveness.md) §4.1) carries the
composed run's clock along the projected indices, so the MVBA's timed run
reads the real clock with no ghost state.

Two other designs were weighed and rejected: a ghost `now` in
[Mvba.lean](../Cadence/Mvba.lean) (it changes every verification condition,
and a `tick` label would fall under weak fairness), and a lift of the
MVBA's state to `state × time`, which puts into the state a clock that only
the MVBA's own steps maintain. The decision record is in
[History.md](History.md) § "From Bounds.md".

#### 6.2.2 The time theory

`time` is a **linearly ordered additive commutative monoid** — Mathlib's
`[LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]` — with a
bridge to Veil's `TotalOrder`, which is what `MVBATemporal` quantifies
over. `ℕ` and `ℝ≥0` are instances; nothing is a field, and no division
occurs. Two abstract inflationary shifts, an order-only theory, would not do: `ℓ` is a
sum of about ten terms with natural-number multiples (`n • C`) and a
`max`, and the bound's proof rearranges such sums, which an ordered monoid
does and two abstract successors do not. This is plain Lean outside Veil's
pipeline, so Veil's restriction on Mathlib's universe-polymorphic classes
does not apply. The bound's proof also needs the monoid **cancellative**
(`IsOrderedCancelAddMonoid`); §6.2.8 gives the `ℕ∞` counterexample.

Two remarks on what the theory does **not** assume. The **termination
bound needs no Archimedean axiom** — every quantity in it is a finite sum
of the constants. `admissible_exists` does: a `TimedRun` is unbounded by
definition (`clock_unbounded`), so exhibiting one needs an unbounded
monotone sequence in `time`. `Archimedean time` with `0 < Δ` makes the
witness's clock `n ↦ n • Δ` unbounded. That the witness, not the theorem,
carries the Archimedean assumption is worth keeping visible: the cause is
the contract's non-Zeno field, not the schedule.

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
So the requirement is not a sequence `Δ_v` unbounded relative to a fixed
bound: the sequence must be *eventually above*
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

`hop`, the per-label kind, classifies the fourteen labels that carry a
timed obligation by what the guard consumes:

| network (reads another party's message or certificate) | `δ` (local) |
|---|---|
| `handle_preprepare_first`, `handle_preprepare` (the leader's `Pre-Prepare`) | `leader_propose_first`, `leader_repropose`, `leader_propose_fresh` (upon entering the view; `Recover` is the identity here) |
| `form_own_commitqc`, `form_own_tc_lock`, `form_own_tc_nolock` (a quorum of `Commit`s or timeouts the validator received itself; §6.4.7) | `send_commit`, `timeout_qc`, `timeout_noqc` (own state and a certificate already counted) |
| `adopt_prepqc` (a quorum of `Prepare`s the validator received itself; (N4) below) | |
| `sync_view`, `sync_view_adopt` (a timeout certificate) | |

With `δ = 0` the good view's latency is the paper's constant (§6.2.6),
which is the check that the classification is the paper's and not a
convenience.

**The network clauses.** A network label's bound depends on its
messages' history, as the supplement's network at the paper target does. The
model's network relations hold from a message's first delivery to a
correct validator, so "sent at" is the first index at which the relation
holds.

| clause | owed within | when | the supplement |
|---|---|---|---|
| `first` | `Δ` | the messages are from correct senders (a correct leader; a quorum of correct validators), were first sent at or after GST (`SinceGst`, **N1**), and were retained by the receiver, which had reached the message's view or the one before (`RetainedBy`, **N2**); while every correct validator takes part. That the receiver has not moved past the view (**N2**, lower views discarded) is the receiving step's own `in_view` guard: every network label is one validator's step, so the clause names no separate receiver | delivery within `Δ` of messages sent at or after GST between correct validators; one-view retention; lower views discarded |
| `forwarded` | `Δ` | a timeout certificate forwarded, at or after GST, by the first correct validator to enter the view it justifies | Supplement, Algorithm 1, line 98 (`line:mvba:sv-forward`), Supplement, Lemma 14 (`lem:view-sync`)(b) |
| `timeouts` | `Δ + ρ` | a correct quorum's timeouts, whenever sent, while their senders are still in the view, formed into a certificate by a correct validator in the view | the `Timeout` retransmission, Supplement, Lemma 15 (`lem:convergence`) ("Reaching `V`") |
| `certificates` | `Δ + ρ` | a timeout certificate, whenever formed, while every correct validator takes part | Supplement, Algorithm 1, line 40 (`line:mvba:viewtc-retx`) |
| `decisions` | `Δ + ρ` | a commit certificate some correct validator has decided on (**N3**), while that validator takes part: it has proposed and has not abandoned | the composing layer's delivery, Supplement, Lemma 13 (`lem:decision-propagation`), argued in the termination setting with the learner not abandoned |

*The last row is the caller's, not the MVBA's (C15, §6.4.2): `decide` on a
transferred certificate is the contract's input `accept`, so the row is a
clause of its own, `Mvba.Relayed`, outside `BoundedJustice`, and `decide`
is not in the hop table. Inside Cadence, Chorus's rows derive it
(`Chorus.relayedWhileActive_of_timedJustice`). It is owed only while the
decider takes part: a decider that has finalized may abandon before its
certificate's broadcast, and then nothing hands its decision on; the
MVBA's own proof needs it only inside its termination window, where nobody
correct has abandoned.*

Every side condition is one under which the supplement promises delivery.
A single clause holding every network label to `Δ` after GST, whatever its
messages' history, would hold a correct validator to consuming within `Δ`
a message sent before GST (which the supplement may lose), a message two
views ahead (which it may discard), a certificate that has to travel
(which costs `ρ` more), and Byzantine senders' messages (which reach whom
the adversary chooses); such supplement runs would not be admissible, and
the timed claim would say nothing about them. The review that replaced
the one-line clause is finding C16 in [History.md](History.md)
§ "The supplement at `eb1bb51`, reviewed against the pin `026dc8b`".

**(N4): prepare certificates do not travel.** In the supplement a
validator holds a prepare certificate only if it received a quorum of
prepares itself; nobody forwards one. The model does the same
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

A local adoption step on a certificate formed anywhere would hold a correct
validator to adopting a certificate it never received, and so exclude
supplement runs in which Byzantine votes reach only some validators.
`form_prepqc` stays as the anonymous assembly, the adversary's capability,
and carries no fairness (`AssemblyLabel`, §6.4.7). The good view is
unaffected: there every correct validator receives the whole correct
quorum's prepares within the same `Δ` (§6.2.6).

**Fairness over plain enabledness, and the second finding.**
[Fairness.lean](../Cadence/Fairness.lean)'s `Enabled` holds whenever
*some* transition under the label exists, a stutter included. If a fair
action stays enabled after it has fired — an idempotent assembly with a
quorum parameter, say — weak fairness per label demands infinitely many
firings for one effect; at a quorum sort with infinitely many
supermajorities no run satisfies it, and in the timed form it is fatal
outright (infinitely many firings within `Δ`). That is the second finding.
It is answered in the model: every fair action has a "not already" guard
on a record its own step sets, as the paper's rules do, and each model
proves, at every state, that no fair label is enabled without being able
to change the state (`Mvba.enabledMove_of_enabled`,
`Chorus.justice_enabledMove`; §6.4.7). So the premises use plain
enabledness — an action enabled from some point on eventually fires:
`WeaklyFair`, `WeaklyFairFamily`, `StronglyFair`, `BoundedFair` and
`BoundedFairWhile` are over `Enabled`, and so both `FJustice`s and
`BoundedJustice` are. For these models that is the same premise as weak
fairness over state-changing steps (TLA+'s `⟨A⟩_v`):
`Mvba.fJustice_iff_move`, `Chorus.fJustice_iff_move`,
`Mvba.boundedFair_iff_move` and `Mvba.boundedFairWhile_iff_move` state the
equivalence. How the premises were stated before the models were changed is
in [History.md](History.md) § "From Bounds.md".

**What is deliberately absent.** No clause
mentions a good view, the leader rotation, or GST as a model event. Every
clause relates an environment event — a label firing, a clock reading — to
a guard or a local record. The network clauses' side
conditions also read the network's own facts, as the supplement's network
rules do: who sent a message (a correct validator or not), when it was
first sent against GST, which view its receiver had reached, and, for the
composing layer's delivery, whether a correct validator that still takes
part has decided on the certificate. None of them is a protocol conclusion the argument needs;
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
  correct leader"* with `k = f+1`. The bound needs `k` because
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
| a timeout certificate for some view `≥ v` exists | `+ Δ` | either a correct validator is above `v`, which needs one, or the correct quorum's timeouts are all sent and a correct validator in `v` forms the certificate (`form_own_tc_*`); a first delivery, the timeouts retained by the first member to send one, which was in `v` then and forms it |
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
| every correct validator holds its own `prepareQC_W` on `e` | `+ Δ` | `adopt_prepqc` on the correct quorum's prepares, all on one `e` (`accepted_unique`); a first delivery ((N4) in §6.2.4) |
| … and has `avail_ready` | acceptance `+ Δ_sync` | (Δ-avail), in parallel |
| every correct `Commit` sent | `max` of the two `+ δ` | `send_commit` |
| `msg_commitqc W e`, and a correct validator decided | `+ Δ` | `form_own_commitqc` at the first correct validator in `W`, which forms the certificate from the correct quorum's `Commit`s and decides on it (`TryFormCommitQC` and `Decide`) |

so a correct validator has decided by `E₀ + L_cert` with
**`L_cert = 3Δ + max(Δ, Δ_sync) + 2δ`** — Supplement, Lemma 16 (`lem:good-view`)'s
`t*_w − τ_w` at `δ = 0`, `Δ_R = 0`. The validator that forms the
certificate decides on it; the others decide by the transfer in the
assembly below.
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
bound. So the state-level links are reused, and the temporal glue is
rewritten in full.

What *is* derived from the untimed file, as a corollary, is
**(A-viewsync)**: `AViewSync (tr.toLRun)` for every admissible `tr`. The
proof (`Mvba.aViewSync_of_sync`) does not go through the good view, and
the statement needs a finite validator set; §6.2.8 has both. That
theorem is the formal version of the trust-base move
[Liveness.md](Liveness.md) §2.1 describes, and it retires the only
premise of `Mvba.termination` that was not fair scheduling or a caller's
condition. `admissible_exists` is the run in which no one proposes and the
environment only marks availability, at every sort. `Admissible` holds of
it because no `JusticeLabel` is move-enabled at any of its states: sixteen
guard facts, and a member of each quorum for the assemblies. Nobody
proposes in it, so it is no witness for `TerminationClaim`'s `AllPropose`;
that witness is §6.3's.

#### 6.2.8 What the proofs needed

Facts the MVBA's timed proofs establish or require beyond §6.2.1–§6.2.7.
Each is about the claim or its premises, not about the protocol. The proofs
are [Mvba/Bound.lean](../Cadence/Mvba/Bound.lean) (the good view,
`Mvba.good_view_decides`),
[Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean)
(the burn lemma `Mvba.synced_succ`, the bound `Mvba.bounded_termination`,
`Mvba.aViewSync_of_sync`) and
[Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean) (the instance).

**The links.** Each link of the good view's chain is one bounded-fairness
application, through one generic lemma (`TLRun.withinFrom_of_boundedFair`).
The quorum steps are one application per member plus
`TLRun.withinFrom_forall`, and availability is (Δ-avail) directly, joined
to the adoption by taking the later of two indices (`TLRun.clk_max_le`).
Each link asks `hop` for its bound by `rfl`, so a disagreement between a
link and the hop table fails to elaborate. The cost is on the *stability*
side: three state facts [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)
does not export are proven locally — `timer_set_label` (only
`expire_timer i v` sets `timer_expired i v`, one case per action from M13's
frame lemmas), the prefix form of `entered_le_of_no_timeout`, and the
timeout certificate below `W` present *at* the first correct entry
(`msg_tc_below_of_entered`). Each constant (`Lcert`, `burn`) is closed
against its milestone deadlines by `abel`, so §6.2.6's tables and the
constants agree term for term. Three hop-table rows are exercised by no
proof: `sync_view_adopt` (a validator holding a higher certificate advances
through `sync_view`, by `tc_lock_implies_tc`) and the two view-zero labels
(the good view is strictly above a view already entered). Their fairness is
a premise the bound does not use, which weakens nothing.

**The time theory needs cancellation.** §6.2.2's linearly ordered monoid
is not enough for the step "`L_cert < τ W`, hence
`E₀ + L_cert < E₀ + τ W`". In `ℕ∞`, which satisfies §6.2.2's axioms, a
clock at `⊤` makes both sides `⊤`. A correct `W`-timer may then fire inside
the window, and a validator that times out in `W` stops the chain. So
`good_view_decides` and `bounded_termination` take
`[IsOrderedCancelAddMonoid time]`; `ℕ`, `ℚ≥0` and `ℝ≥0` are instances, so
the intended models are unaffected. The assembly also uses it for
`u < u + Δ`, which is how the last index at or before `u` is found by
`Nat.find`; the burn lemma needs no cancellation. The claims in
[Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean) are stated over the
weaker class, so the extra class appears only where a proof uses it, and
not in the definitions a reader checks against the paper. No run predicate
can express it, because it constrains the sort, just like the instance
hypotheses of §6.2.5.

**Only the leader and the honest quorum move through the good view.**
§6.2.6's "every correct validator is in `W` / accepted" rows hold of every
correct validator (the links are stated per validator), but the proof moves
only `L` and `ByzNodeSetHonestQuorum`'s quorum through `W`. Decisions need
no view (`decide` reads a certificate of any view), so the final row covers
every correct validator regardless. The good-view lemma's premises are
therefore: every correct validator has proposed by the first entry `N₀`;
none is inactive by `E₀ + L_cert + δ`; `N₀` is the *first* correct entry,
which the assembly gets by `Nat.find`; and the clock at `N₀` is at or after
GST.

**The timeout restart.** The burn lemma's `2δ` rests on one fact: *a
certificate a validator acquires while it stays in `v` is a certificate of
`v`* (`local_prepqc_new_in_view`). `adopt_prepqc` is guarded on `in_view`
for the certificate's own view, and `sync_view_adopt` leaves the view. This
is a two-state fact about labels, not an invariant; it is proven like
`timer_set_label`, one case per action from M13's frame lemmas
(`local_prepqc_set`), and then by induction along the run. From it,
`within_timed_out` has three cases: the goal already holds; a certificate
of `v` is acquired in the first `δ` window, after which the label is fixed
for one more `δ`; or none is, and the label chosen at the window's start
stays enabled.

**The count of burns.** It is `a + j`: `1 ≤ a ≤ |below v_L|` successors of
`M` clear the ramp (`exists_iterate_succ_ge`, a pigeonhole over
`below v_L`), and `j < k` more reach a correct leader. The step out of `M`
is the first of the `a`. `a + j ≤ |below v_L| + k − 1` would be one burn
tighter; it is not taken, because the natural-number subtraction costs
readability.

**The finite starting point.** `M`, the highest view a correct validator
has entered at `N₀`, is a maximum over a finite list, since each step
enters at most one view (`entered_set_view`, a label case split, then
`entered_covered` by induction on the index). Neither the node sort nor the
view sort is assumed finite for this, and `ViewOrderEnum` is not used for
`M`; it gives `succ`, the pigeonhole count, and the highest held
certificate in the timeout step. Three further facts are proven locally:
the certificate below a view with its predecessor produced
(`exists_tc_pred_of_entered`); that the first correct validator at or above
a view is *in* it (`entered_eq_of_first_above`, since skipping it needs a
correct timeout there); and the successor facts of `ViewOrderEnum`.

**The instance.** The hypotheses of `Mvba.mvbaTemporal` are §6.2.5's, with
the time theory of §6.2.2:

* finitely many validators (`Fintype node`), which supplies
  `ByzNodeSetEnum` (`ByzNodeSetEnum.ofFintype`);
* `ByzNodeSetHonestQuorum` and `ViewOrderEnum`;
* `LeaderRotation vfin sch.k th`;
* `IsOrderedCancelAddMonoid time` for termination;
* `Archimedean time` for `admissible_exists`, with `0 < Δ`, a field of
  `Schedule`; the witness run's clock is `n • Δ`, which the Archimedean
  axiom makes unbounded.

They can be met: `Schedule.fixedNat` is the paper's fixed timeout at
`time := ℕ`, and an `example` in the same file instantiates `MVBATemporal`
there. The contract's observables are the model's fields by `Iff.rfl`
(`timed_decided_iff`, `timed_proposed_iff`, `timed_abandoned_iff`), and the
least upper bound in `byGstBound` and in the abandonment premise is `max`
by one generic lemma, `Cadence.gstLub_iff` in
[Timed.lean](../Cadence/Timed.lean). So `timed_termination` is
`bounded_termination` read through `Admissible`'s labelling and nothing
else. `admissible_exists` is admissible because every state of its run is
*quiet* — no input, entry, acceptance, or prepare/commit/timeout message —
and at a quiet state no fair label is enabled.

**(A-viewsync), and what kind of premise it is.** `Mvba.aViewSync_of_sync`
keeps `Mvba.termination`'s own caller premises (`AllPropose`,
`NoEarlyAbandon`) and assumes finitely many validators. `AllPropose`
("every correct validator proposes at some index") gives a common deadline
only over finitely many validators, and without a deadline nothing stops
every correct-led view from being burnt before its leader has proposed.
The deadline form is the lemma behind it, `Mvba.aViewSync_of_proposedBy`,
for any node sort. The claim does not need "no abandonment up to
`u + ℓ`", because an abandoned correct validator has decided, and a
decision is certificate-backed (`decided_backed`).

The proof does not go through the good view. The second clause of
`AViewSync` only asks that a `W`-timer does not expire before some correct
validator has decided. So **any** correct-led view above every view entered
at a correct decision satisfies both clauses: the first follows from (T2),
and the second from (T1), since the timer of such a view starts after the
decision (`Mvba.aViewSync_of_commitqc`). Neither step uses timing beyond
the two timer clauses. The decision itself comes from
`bounded_termination`, or from an early abandonment. This says what kind
of premise (A-viewsync) is, and [Liveness.md](Liveness.md) §2.1 opens with
the short account: it is the view timer stated as ordering constraints.
The untimed model has the timer but no clock, so on its own a timer may
fire at any moment, and the premise fixes the two orderings that matter.
It holds in every run that terminates, so the untimed theorem reads *given
enough time, the protocol decides*, with the bound set aside and not the
synchrony.

**Both clauses are needed**, and the second does not imply the first
through a least good view. Let a Byzantine leader of `V` never propose,
and let `V`'s timer never fire, which is allowed because the marker is
under no fairness obligation. Every correct validator stays in `V`. Every
correct-led `W` above `V` is never entered, so it satisfies the second
clause vacuously, and nobody decides. A least `W` would not help: it
constrains only correct-led candidates, and a candidate's failing the
second clause means that *some* correct validator's timer fired early, not
every one. The view order is also not assumed well-founded, except through
`ViewOrderEnum`. In the timed model the two clauses are (T2), not late, and
(T1) with `τ W > L_cert`, not early.

**Finiteness of the validator set, as a convention for claims.** A
liveness argument collapses finitely many per-validator eventualities into
one index, which is sound only over a finite set. The contract-level
results take `[Fintype node]` (`mvbaTemporal`, `mvbaFull`,
`timed_termination`, `aViewSync_of_sync`, and `Mvba.termination`), and
`ByzNodeSetEnum.ofFintype` ([ByzQuorum.lean](../Cadence/ByzQuorum.lean))
supplies the enumeration their proofs use. The building-block lemmas keep
`ByzNodeSetEnum`, which is weaker (finite quorums over any node sort), and
`bounded_termination` keeps it as the general form. Chorus's claims follow
the same convention: `[Fintype node]` at the generic layers, `Fin n` at the
concrete family. Finiteness stays out of the Veil models and the safety
theorems, which hold at any cardinality. It does not touch the other two
finiteness questions: the abstract `nodeset` sort may have infinitely many
supermajorities (§6.2.4's second finding, answered in the model), and the
view order is infinite by nature (`below vL`).

**The halt, in the proofs.** A decided validator halts (§6.3.2), so every
honest link needs its validator *active*: neither abandoned nor decided
(`Mvba.Active`, in `SettledIn` and in the link hypotheses). The untimed
proof already ran under "nobody has decided". The timed proof splits in
`bounded_termination`: either a correct validator decides by the
certificate deadline and the others decide by the transfer, or nobody
does, and the chain runs as before with every correct validator active up
to that deadline. `ℓ` is unaffected.

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
  forming its own commit certificate and deciding on it. At clock
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

The witness wanted is a run in which everyone decides in the first view
and the run then idles. The model first had no such run. Its `decide` recorded the decision and nothing else, and its
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
would be vacuous. The proofs' side is in §6.2.8, "The halt, in the
proofs".

### 6.4 The Chorus leg

The paper proves two timed properties of Chorus:

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
([Interfaces.lean](../Cadence/Interfaces.lean)).

Both are proven. The claims are `TimedTerminationClaim` and
`TotalityClaim` in [Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean);
the theorems are `Chorus.timed_termination` (with the sharper
`Chorus.timed_termination_tight`, F4) and `Chorus.totality`; the contract
instances are `Chorus.chorusTemporal` and `Chorus.chorusWithTotality`,
joined with the fragment into `Chorus.slotConsensusFull`
([Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean)).

The timed claims assume what the MVBA's do (§6.2): messages between correct
validators arrive within Δ after GST, local steps take at most δ (zero in
the paper), and the slot's three time landmarks (the deadline `D`, then
`D + Δ` and `D + 2Δ`) happen on time on synchronized clocks. They further
assume that the MVBA contract's own timing premises hold of its steps
inside the run, and that the certificate bridge `ValidBridge` holds; the
bridge is unchanged from the untimed claim. The rest are the caller's
conditions, which the composition discharges
([ConductorBounds.md](ConductorBounds.md) §4): everyone starts by `t`,
starts are Δ-synchronized, nobody starts before `D − Δ`, and nobody
abandons before finalizing. [Premises.md](Premises.md) lists every premise
once.

**Four findings about the statements, none about the protocol.**

* **F1: the class's timed fields omitted two premises the paper uses.**
  `bounded_termination` and `totality` lacked "a correct validator abandons
  only after finalizing" (Algorithm 1 (`algorithm:cadence`), Algorithm 1, line 23 (`line:abandon`)). The
  untimed `SlotConsensusTemporal.termination` has that premise.
  `bounded_termination` also lacked "no correct validator starts before
  `D − Δ`", which is the Conductor's integrity
  (Lemma 12 (`lemma:conductor-integrity`)); the proof of
  Proposition 5 (`prop:chorus-finalization-time`) uses it in its first step. Without the
  first premise, a validator that abandons at once never finalizes.
  Without the second, a slot whose deadline lies far after `t` cannot
  finalize by `max(t, GST) + ℓ`. Either way the field is false for every
  faithful implementation, unless the implementation's own `Admissible`
  smuggles in the caller's conditions, which the rely form of
  `MVBATemporal.termination` avoids. **Closed:** the contract carries both
  as antecedents, C1 and C2 (§6.4.1); P13 of
  [PaperAlignment.md](PaperAlignment.md) §6 is the paper side.
* **F2: the paper's message buffering needs a split hop.** "A message
  whose rule is blocked by this convention is not lost"
  (Appendix C.3 (`subsection:chorus-protocol-overview`)). A rule's network input is
  therefore due Δ after it was sent, and its local gate (a phase landmark,
  or participation) is due δ after it opened. Measuring a Δ-hop from the
  later of the two, as §6.2.4's `BoundedFair` does, costs one extra Δ at
  every step where a landmark opens last, and the bound would be
  `6Δ + ℓ_MVBA` or worse, not the paper's `5Δ`. §6.4.2 states the clause
  that keeps the paper's arithmetic.
* **F3: at δ > 0 the totality latency is `Δ + 2δ`, not Δ.** The
  Conductor's window induction closes *because* Chorus's totality
  latency equals the synchronization tolerance its condition grants.
  "Both equal `Δ = d_tot`", in the words of the paragraph before
  Definition 6 (`def:window-synchronized`). With local steps that take time the ratchet
  loses δ per window. Totality is proven in the tolerance-parametric form
  (§6.4.4), and the Conductor leg works at the paper's δ = 0
  ([ConductorBounds.md](ConductorBounds.md) §5).
* **F4: the 5Δ bound is loose by one Δ.**
  Lemma 11 (`lemma:chorus-termination`) splits at `T₀ = M + 4Δ + ℓ_MVBA` and adds Δ
  for totality (`M = max(t, GST)`). The inner split of
  Proposition 5 (`prop:chorus-finalization-time`) at `T₀ − Δ` already handles early
  finalizers, and the only use of that proposition's premise "no correct
  validator stops before `T`" is covered by "abandon only after
  finalizing". So a single split gives `M + 4Δ + ℓ_MVBA`, which is the
  bound an earlier, commented-out draft next to the lemma states.
  **Confirmed:** `Chorus.timed_termination_tight` proves
  `M + 4Δ + ℓ_MVBA + 9δ`, the paper's `4Δ + ℓ_MVBA` at `δ = 0`; the claim
  stays the paper's 5Δ (`Chorus.timed_termination`), and the looseness is
  P5 of [PaperAlignment.md](PaperAlignment.md) §6.

**Decisions in one place.**

* Participation interface: the model has `participate` and `abandon`, and
  `propose` is the contract's input. Every sending rule is gated on active
  participation (§6.4.1).
* The class carries C1 and C2 as antecedents, in the rely form (§6.4.1).
  C3, the tolerance, is the Conductor leg's (F3).
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
  `T := Mvba.mvbaTemporal …` (§6.4.3). A change to the MVBA's timing model
  reaches this leg only through `T`.
* The proof re-runs the untimed chains with deadlines. It case-splits on
  an early finalization, as the paper does, and not on the progress
  dichotomy (§6.4.3).
* Non-vacuity comes from one witness that serves both the untimed and the
  timed claims (§6.4.5).

#### 6.4.1 The participation interface

**What the contract asks.** `SlotConsensusTemporal` has three inputs
(`participate`, `abandon`, `propose`) with their observables, effects,
frames and initial conditions. It has the admissible-run model, and
Termination and Quiescence stated over them. `SlotConsensusWithTotality`
takes an instance of it as a parameter. The class's frames say that
*internal* steps leave a correct validator's inputs unchanged, so
`Chorus.slotConsensusSafety`'s `step` excludes the input labels
([Chorus/Compose.lean](../Cadence/Chorus/Compose.lean)).

**The model** ([Chorus.lean](../Cadence/Chorus.lean)). Per-validator
`participating i` and `abandoned i` are local state, written only by two
input actions:

* `participate i`;
* `abandon i mvba_next`, which forwards to the MVBA's `abandon`, as
  Algorithm 5, line 48 (`line:fb-abandon`) does. It forwards every time,
  not only "if mvbaInvoked": the MVBA's own `abandon()` has no
  precondition, a party that has not proposed sends nothing in the MVBA,
  and after `abandon` Chorus never proposes to it. The conditional form
  would need a negative read of the MVBA's state, or a new local flag.

The action `propose j m` is the contract's `propose(P)`, with `P ↦ m`, the
class's `proposal := merkle_root` at
[Chorus/Compose.lean](../Cadence/Chorus/Compose.lean); as an input it
carries no fairness. Every rule that sends is gated on
`participating i ∧ ¬ abandoned i`, and the rules that only process are
exempt. That is the standing convention of
Appendix C.3 (`subsection:chorus-protocol-overview`), rule for rule:

* **Gated, because they send.** `propose` (at the proposer; it sends
  every validator its chunk in the same step), `vote`, `commit_sign_*`,
  `cast_fast_commit`, `broadcast_commitqc_*` and `broadcast_fbcommitqc`
  (at the collector), `fb_sign_*` (whose positive form also sends every
  validator its chunk, F15), `cast_fallback_vote`, `mvba_propose` (the
  convention names it explicitly), `send_mvba_cert` (the broadcast of the
  MVBA's commit certificate), `cast_fb_commit`, and the six
  `commit_assign_*` routes and `finalize_commit`. The paper's finalization
  rules re-broadcast the proof
  (Algorithm 4, line 35 (`line:fast-rebroadcast-commitqc`), Algorithm 5, line 46 (`line:fb-commit-rebroadcast`)), and
  its totality proof relies on their being gated.
* **Exempt, because they process.** `record_chunk`, the vote receipts
  `receive_vote_*`, `aggregate_fastqc_*`, the decision handlers and
  `mvba_terminate`, the certificate handoff `accept_mvba_commitqc`, and the
  availability report `mvba_avail_ready`. A message is on the network from
  its send on, so a chunk a proposer sent in its gated `propose` is due at
  its recipient whatever the proposer does next (F15).
* **Senders.** Every message names its sender. The collectors of
  `broadcast_commitqc_*` (Algorithm 4, line 33 (`line:fast-broadcast-commitqc`))
  and `broadcast_fbcommitqc` (Algorithm 5, line 44 (`line:fb-commit-broadcast`))
  are gated when correct; the Byzantine forms are the unfair
  `byz_broadcast_commitqc_*` and `byz_broadcast_fbcommitqc` (§6.4.7).
  Without the sender, Quiescence could not attribute those messages.

The gates read only the acting validator's local state: no network
relation is read negatively ([Locality.md](Locality.md) R1, R2).

Quiescence is then proven in the paper's own two-part shape
(Lemma 6 (`lemma:chorus-quiescence`)), in
[Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean):

* Chorus's own sends are gated;
* the MVBA's sends are the MVBA's `sent`, confined by its `quiescence` to
  the window between a gated `propose` and a forwarded `abandon`.

The message type is a sum of Chorus's attributed network relations and
`mmsg`, defined in [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) and
not in the model. The proof reads the transition bodies, like the MVBA's
`sent_new_tr`, so no `step_property` cell is needed.

**The label classification.** [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)
has an `InputLabel` class (`participate`, `abandon`, `propose`). It
matters: `JusticeLabel` is the complement of the other classes, so an input
outside `InputLabel` would silently become weakly fair, and fairness of
`abandon` would force every validator to abandon.

**The untimed claim.** `TerminationClaim` takes the caller's premises
(every correct validator eventually participates; none abandons before
finalizing), which are exactly `SlotConsensusTemporal.termination`'s. A
validator that finalizes on the fast path and then abandons also abandons
the MVBA, so the MVBA's `NoEarlyAbandon` holds only on the branch where
nobody has finalized. The proof therefore splits on an early finalization,
which is the split the timed proof uses (§6.4.3).

The alternatives that were weighed — claims over implicit participation, a
gated wrapper around the transition system outside Veil, or a changed
class — are in [History.md](History.md) § "From Bounds.md". They are
either not the paper's statements or unfaithful to Module 1
(`mod:slotconsensus`), whose interface *is* the three inputs.

**The class change: C1 and C2.** F1's two premises are in the class, in
the rely style of `MVBATemporal.termination`, as antecedents rather than
`Admissible` content:

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
`BoundedFair` and the untimed claim's `FJustice` are: every fair
action of the model fires once (`Chorus.justice_enabledMove`). The proposal
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

**The hop table**, classified as §6.2.4's is, by what the guard consumes,
with each row's gate and the condition under which it is owed at all, is
[Premises.md](Premises.md) §4.1 ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean):
`Chorus.hop`, `Chorus.gate`; `Chorus.Owed` in
[Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)). A step that
consumes a message is timed at its receiver: there is no delivery step, and
the receiver's row is owed when the message's sender is correct. A
certificate the actor sent itself is a local read, a `δ`-row (`rcvHop`).

`hop_isSome_iff` pins that the table covers exactly the fair labels that
are not phase markers. The Byzantine forms of the senders
(`byz_send_chunk`, `byz_redisseminate_chunk`, `byz_broadcast_commitqc_*`,
`byz_broadcast_fbcommitqc`, `byz_send_mvba_cert`) are unfair and have no
row (§6.4.7). `mvba_propose`'s gate is the MVBA arm, not the fallback arm,
because the case-(a) trigger waits for it and §6.4.3's timeline reaches
the proposals only after it. Six things about the table:

* **Participation.** Every row whose rule is gated (§6.4.1) has
  participation in its gate.
* **`mvba_propose` is two rules** (F9). Case (b)'s trigger, others'
  fallback votes, is a network input. Case (a)'s trigger (Algorithm 5, line 23 (`line:fb-mvba-propose-fast`))
  is the proposer's own complete fast meta-block, which exists only once
  the FastQCs have arrived, so a Δ-row on it would cost a second Δ; it is a
  δ-family.
* **The check.** At δ = 0 the table reproduces the paper's timeline term
  for term (§6.4.3), as §6.2.4's did for the MVBA.
* **The decision handlers are δ-rows** although they read certificates.
  Each fires on the acting validator's *own* MVBA decision, which is a
  local output, and the certificates its bridge check reads hold at that
  decision by `ValidBridge`'s completeness. So is `send_mvba_cert`, the
  broadcast of the decision's certificate. A decision's transfer to a
  validator that did not decide first is the handoff (C15, below).
* **A vote is received before it is used.** `receive_vote_*` is the
  receiver's `Δ`-row on a correct voter's vote, and the negative fallback
  entry `fb_sign_neg` reads the receiver's own receipts ("among the votes
  it received"), so it is a `δ`-row. The receipt costs the timeline one `δ`
  (§6.4.3).
* **Sending to oneself is a local step** (`rcvHop`). The commit routes
  `commit_assign_*` read a certificate with its sender. A certificate from
  another validator is a `Δ`-row; one the actor sent itself is a `δ`-row:
  the finalizer of the fallback commit round forms the fallback commit
  certificate and broadcasts it (Algorithm 5, lines 42–44
  (`line:fb-collect-commit`–`line:fb-commit-broadcast`)), and finalizes on
  its own broadcast (Algorithm 5, line 45 (`line:fb-recv-commit`)).

**Findings against the rows, each built into the statement.**

* **F5: the paper owes delivery only between correct validators**
  (Proposition 5 (`prop:chorus-finalization-time`)'s proof: "every message between correct
  validators is delivered within Δ"). Every message of the model names its
  sender and holds from its send on, a Byzantine sender's included. So a
  Δ-row that consumes a Byzantine validator's message would owe a
  delivery the paper does not promise, since a Byzantine voter may send to
  some validators only. That is the MVBA's C16 finding, on Chorus's side.
  Each Δ-row is therefore owed only when the messages it consumes came from
  correct senders (the owed column of [Premises.md](Premises.md) §4.1), and
  both untimed `FJustice`s,
  Chorus's and the MVBA's, take the same owed-conditions (`Chorus.Owed`,
  `Mvba.Owed`: a correct leader, a correct quorum). Re-proving
  `Chorus.termination` against them showed two rows stricter than the
  paper's network, both places where a correct validator forwards what it
  received:
  * **F7: the fast meta-block travels.** `aggregate_fastqc_*` is also owed
    when a correct validator that cast its fast commit vote holds the
    FastQC: the same rule broadcasts its `FastBlock` (Algorithm 4, line 20 (`line:fast-metablock`)), and a
    correct validator that receives one adopts its FastQCs. The paper's
    finalization-time proof uses exactly this ("that validator held a fast
    meta-block and broadcast it").
  * **F8: re-dissemination by the decoder.** A correct validator that
    signs a positive fallback entry has decoded the proposal, and sends
    every validator its chunk (Algorithm 5, line 12 (`line:fb-redisseminate`)). A
    `FallbackQC`'s correct signer is the paper's source of the chunks
    (Proposition 5 (`prop:chorus-finalization-time`), "by `M + 3Δ`"). Since
    F15 the send is part of the signing step.
* **F6: `cast_fb_commit` read a shared flag.** Its guard read a global
  `mvba_complete`, which the first validator to transport its decision set.
  The paper's rule fires on the voter's own decision (Algorithm 5, line 41
  (`line:fb-commitvote`)). **Closed:** the record is per validator,
  `local_mvba_complete i`, set by `i`'s own `mvba_terminate`, and both the
  guard and `fbCommitGate` read the voter's own row. The bound is
  unchanged: every correct validator has decided by `X_d`, so each
  transports its own decision by `X_d + 2δ`.
* **F9: the case-(a) proposal is a local step.** A correct validator's
  FastQCs reach every correct validator through `aggregate_fastqc_*` (F7)
  by `M + 3Δ + 3δ`, and only then is the case-(a) proposal owed, because
  its trigger is the receiver's local state. A Δ-row from there would put
  the proposals at `M + 4Δ + 3δ`, one Δ beyond the paper's `M + 3Δ`. The
  premise has the paper's two rules: `TimedJustice.propose`
  (Algorithm 5, line 36 (`line:fb-mvba-propose`)), a Δ-family owed on a correct `FBCert`; and
  `TimedJustice.proposeFast` (Algorithm 5, line 23 (`line:fb-mvba-propose-fast`)), a δ-family owed
  on the own meta-block. The proposals are by `M + 3Δ + 4δ`
  (`Chorus.within_all_input`).
* **F10: a Δ-row costs `max(Δ, δ)`.** With its gate already open
  (`N = N'`), a buffered row's window is `ref N + max(Δ, δ)`; a row without
  a gate is always in this case. At `δ > Δ` every such hop would cost `δ`,
  and the paper's route would not reach `5Δ + ℓ_MVBA + O(δ)` (a run may
  delay each step to the end of its window). The schedule has the field
  `Chorus.Schedule.δ_le_Δ`: a local step is no slower than a network hop,
  true at the paper's `δ = 0`. `TotalityClaim` does not need it. The
  handoff's first hop has a field of its own, `Chorus.Schedule.δ_le_ρ`
  (C15, below).
* **F11: re-dissemination was owed on the fast path** (found by the
  witness, §6.4.5). The row was owed whenever `f+1` correct validators held
  the chunk, so every active correct validator owed every validator its
  chunk within Δ, on the fast path too. The paper re-disseminates in two
  places only: inside the fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`)) and
  after the validator's own MVBA decision (Algorithm 5, line 39 (`line:fb-commit-wait`)). Such paper
  runs violated the premise. **Closed:** re-dissemination is owed only
  where the paper sends it, and since F15 it is part of `fb_sign_pos`.
* **F12: the fallback commit vote waited under more roots than the
  paper's.** The paper waits only under FallbackQC entries: "**for each**
  FallbackQC in B′ with a positive entry ⟨s, j, root⟩: **wait until** p_i
  has received and validated its assigned chunk for root"
  (Algorithm 5, line 38 (`line:fb-commit-foreach`), Algorithm 5, line 39 (`line:fb-commit-wait`)). The model's wait covered
  every decided positive root, FastQC-backed ones included, so it had
  fewer runs than the paper: the safety claims did not cover a paper run in
  which the vote is cast without that wait, and the bound paid for a chunk
  the paper does not wait for. **Closed** with F13.
* **F13: where a root has both certificates.** The model's first repair of
  F12 read "held by a FallbackQC" as "no positive FastQC exists for it",
  which differs from the paper for a root with both certificates where the
  validator's own `B′` carries the FallbackQC. It is an artefact of a model
  whose MVBA value was the bare entry vector
  ([PaperAlignment.md](PaperAlignment.md) §5.5). **Closed:** the MVBA's
  value is the meta-block representation, each validator decides its own,
  and the wait runs under exactly the FallbackQC entries of its own `B′`
  ([PaperAlignment.md](PaperAlignment.md) §8.1 (d)):

  | | `cast_fb_commit`'s DA wait |
  |---|---|
  | paper | upon `MVBA[s].decide(B′)`: for each FallbackQC in B′ with a positive entry ⟨s, j, root⟩: wait until p_i has received and validated its assigned chunk for root (Algorithm 5, line 37 (`line:fb-mvba-decide`) to Algorithm 5, line 39 (`line:fb-commit-wait`)) |
  | model | `cast_fb_commit i v`: `mvba.decided mvba_st i v` and `∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → chunk_received i J M`, where `chunk_received i J M` is "some sender sent `i` its chunk of `M`" (`∃ s, msg_chunk s i J M`) |

  `Owed (.cast_fb_commit i v)` is "`i` decided `v` and no other
  representation" (P11 of [PaperAlignment.md](PaperAlignment.md) §6).
* **F14: re-dissemination's "decided" owed-disjunct.** The row also owed
  chunks to other validators after a decision. The paper's decided
  validator broadcasts only *its own* chunk, and only under FallbackQC
  entries (Algorithm 5, line 39 (`line:fb-commit-wait`)), so the disjunct owed steps that paper runs
  need not take, and no proof used it. **Closed:** the disjunct is gone,
  and since F15 re-dissemination has no row at all.
* **F15: re-dissemination was gated at delivery.** The paper sends a
  validator's chunk inside the fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`)),
  while the signer is active, so the chunk is in flight from the signature
  on and is delivered within `Δ` after GST whatever the signer does next.
  The model had split the send off into a step gated on the signer's
  participation at delivery, so an abandonment between signing and delivery
  dropped a message the paper has already sent, and (Δ-avail) was not
  derivable from Chorus's rows. The proposer's dissemination had the same
  shape (Algorithm 2 (`alg:proposer-dissemination`)). **Closed:**

  | | the fallback-entry rule's re-dissemination |
  |---|---|
  | paper | "re-encode proposal; send each validator its assigned chunk for `ρ`" inside the positive branch of the fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`)) |
  | model | in `fb_sign_pos i j m q` itself: `msg_chunk i I j m := true` |

  | | the proposer's dissemination |
  |---|---|
  | paper | upon `propose`: … for each validator `p_r`: send `p_r` its chunk (Algorithm 2 (`alg:proposer-dissemination`)) |
  | model | in `propose j m` itself: `msg_chunk j I j m := true`; the recipient's `record_chunk` reads the chunk and nothing of the proposer's later state |

  What follows from it:
  * **Quiescence is kept.** Every send happens inside a gated step, and
    `msg_chunk s I j m` names its sender `s`. A later receipt of an
    earlier send is not a new send.
  * **Every reader of a chunk is a Δ-row.** `record_chunk`,
    `cast_fb_commit` and `mvba_avail_ready` read a chunk relation that
    holds from its send, so the reader's row times the delivery, as for
    every message of the model. The gate
    checklist ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)'s
    header) admits the actor's own MVBA output that its rule fires upon.
  * **(Δ-avail) is derived.** `Chorus.availWithin_of_timedJustice`: in every
    run satisfying `TimedJustice` and `ValidBridge`, at every schedule,
    every projection's timed run satisfies `Mvba.AvailWithin`. It uses one
    property of the composed timing model, `Chorus.Schedule.Δ_le_Δsync :
    mvba.Δ ≤ mvba.Δsync`: the MVBA's availability window covers one Chorus
    network hop. The field is in the Chorus schedule, which composes the
    MVBA's, because it relates the two layers. `SyncAtMvba` and
    `TimedTerminationClaimAtMvba` therefore assume of the MVBA only its own
    two clauses, (Δ-justice) and (T-timer).
  * **The bound does not move.** On the late branch the chunks are sent at
    saturation and are due before the decision.
  * The Chorus witness sets `Δsync := 1` in its own schedule;
    `Mvba.Schedule.fixedNat` and the MVBA's witness are untouched.

**The decision handoff (C15).** The supplement's "Decision output and
handoff" (Supplement, Section 1.2 (`subsec:mvba-protocol`)) says four
things: `decide(x, CommitQC)` outputs the certificate; Chorus broadcasts
it; a correct validator that receives a valid one re-broadcasts it and
finalizes; and the MVBA accepts a transferred `CommitQC` of any view
(Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)). The transfer is the caller's, so
Chorus's own rows carry it.

* **The broadcast.** `send_mvba_cert i c v`
  ([Chorus.lean](../Cadence/Chorus.lean)): a correct validator that has
  decided `v` sends, under its own name, a certificate `c` that certifies
  its decided entries (`msg_mvba_cert i c`); gated on its participation, a
  `δ`-row on its own decision.
* **The relay.** `accept_mvba_commitqc i s c mvba_next`: a correct
  validator that received `c` from `s` hands it to its MVBA through the
  contract's input `mvba.accept`, which checks it. The read of the message
  is positive ([Locality.md](Locality.md) R2). Finalization on
  the certificate is the `CommitQC` route, `commit_assign_*_mvba`
  ([PaperAlignment.md](PaperAlignment.md) §5.7), which re-broadcasts it.
* **The contract** (`MVBASafety`, first-order additions,
  [Interfaces.lean](../Cadence/Interfaces.lean)): `certifies`;
  `decided_certified`, **decide exposes its certificate**; the input
  `accept` with `accept_trans`; `accept_effect` and `accept_enabled`, **a
  transferred valid certificate is accepted**, in the rely form (the
  caller transfers; the MVBA accepts). `Mvba.mvbaSafety` proves them. At
  the instance `decide` is an input, so in the composed system an MVBA
  decides on a transferred certificate only when Chorus hands it over. The
  MVBA's own claims take the transfer as the caller's premise: (F-relay)
  untimed (`Mvba.FRelay`), `Mvba.Relayed` timed (§6.2.4).
* **The rows, and the derivation.** The relay row is a Δ-row with no gate
  (it processes a message, like `aggregate_fastqc_*`), owed once a correct
  validator has sent a certificate (`relayOwed`).
  `Chorus.relayedWhileActive_of_timedJustice`: in every run satisfying
  `TimedJustice`, every projection's timed run satisfies `Mvba.Relayed`.
  While the decider takes part, its `send_mvba_cert` row (gated on its
  participation, which its MVBA proposal gives, and on its not having
  abandoned) sends the certificate within `δ`, and the relay row hands it
  over `Δ` later; with the schedule's `Chorus.Schedule.δ_le_ρ`, the two hops
  fit in `Δ + ρ`. `Mvba.Relayed` is owed only while the decider takes part
  (§6.2.4), and that is what the rows give: a decider that finalized may
  abandon before its send fires. `Chorus.timedMvbaAdmissible_of_rows` is
  the form a witness uses, and the untimed twin is
  `Chorus.fRelay_of_fJustice`, on the branch where everyone is active.
* **The fired-once guards.** `local_mvba_cert_sent i` and
  `local_mvba_qc_accepted i`, unset by the guards and set by the steps, so
  each step always changes the state and `Chorus.justice_enabledMove`
  keeps holding.

One consequence is on the MVBA's untimed premise: (A-viewsync)'s second
clause names a correct validator's **decision** rather than a commit
certificate, because a certificate the adversary assembled reaches only
whom the adversary chooses, so no transfer of it is owed. The timed model
implies it (`Mvba.aViewSync_of_sync`). The late branch of
`Chorus.termination` always takes the MVBA arm: saturation yields a
correct trigger for the MVBA (a correct fast voter's meta-block, or a
correct `FBCert`), and the MVBA arm finalizes.

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

**What `s.deadline − Δ ≥ GST` becomes.** In the safety fragment it is
`all_honest_recorded`, the antecedent of proposal inclusion, and the
contract's `on_time`: a state fact that neither timed claim of this leg
needs. Its timed form is the first step of censorship resistance: a
correct proposer's chunk, sent with the proposal at `D − Δ ≥ GST`, is
recorded before the marker fires at `D` (`Chorus.within_proposal_recorded`,
which needs the recording strictly before `D`). At δ = 0 a chunk that
arrives exactly at `D` ties with the marker, and the paper states no
tie-break: P19 of [PaperAlignment.md](PaperAlignment.md) §6. The model
states the paper's inclusive reading as a premise, (P-incl)
`DeadlineInclusive` ([Premises.md](Premises.md) §4.8), and the composed
system's censorship resistance is proven under it (`Composed.censorship`;
[ConductorBounds.md](ConductorBounds.md), F31).

**`MvbaAdmissible` becomes the MVBA's `Admissible`, through a timed
projection.** The untimed premise is "some projection's run satisfies
`Mvba.FJustice ∧ AViewSync ∧ FAvail`". The timed premise is "some
projection `p`, with the clock carried along, has `T.Admissible
p.timedRun`", where `T` is the MVBA contract, at the system's MVBA
`Mvba.mvbaTemporal …`. It is stated with the contract's own field and
restated nowhere ([Liveness.md](Liveness.md) §4.1). The projection is
`Component.Projection.timed`, the untimed projection plus a clock. Projected state `k` reads the clock
of the composed index at which the MVBA entered it. The projected step
`k → k+1` then carries the post-state clock of the composed step that
took it, which is exactly `FiresWithin`'s convention. The pieces:

* The clock is unbounded because the projection is `Scheduled`.
* `gst` is the composed run's.
* The only transfer the proof needs runs *back*: a decision at projected
  clock `≤ X` is a composed-run decision at clock `≤ X`, because the MVBA
  state is constant between its steps.
* `boundedFair_iff`, the timed twin of `weaklyFair_iff`, lets an auditor
  read the premise at either level.

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
* The early-finalization split is also the untimed proof's (§6.4.1), so
  the two proofs share their skeleton.

The dichotomy theorems stay in use as the source of the certified vector.
With `M = max(t, GST)`, the same notation as the paper:

| Paper milestone (Proposition 5 (`prop:chorus-finalization-time`)) | Model links, re-run with deadlines | Rows |
|---|---|---|
| `D ≤ t + Δ` | C2 at each correct start, with (P2) | — |
| by `M + Δ`: first-round votes | `eventually_voted`, then `eventually_quorum_cast` (`voted_implies_cast`) | `vote` δ |
| by `M + 2Δ`: second-round votes | `eventually_received`, `eventually_saturated` / `eventually_all_saturated` | aggregate Δ, sign/cast δ; vote receipts Δ; `fb_sign_pos` Δ, `fb_sign_neg` δ on the receipts, gate `D + Δ ≤ M + 2Δ`; `cast_fallback_vote` δ |
| by `M + 3Δ`: MVBA proposals, fallback chunks | `eventually_complete_fast_metablock`, `eventually_trigger`, `eventually_input`, `certifiedVector` (`ValidBridge` soundness); the chunks sent with each positive fallback signature (`fb_pos_sig_chunks`, F15) | the proposal family Δ, gate `D + 2Δ`; aggregate Δ; the chunks' hop Δ, timed at their reader (`fbCommit`) |
| by `T₀ − Δ = M + 3Δ + ℓ_MVBA`: decision | `T.termination` on the timed projection; `eventually_mvba_complete`, `eventually_fbcommit_sig` | `ℓ_MVBA`; handlers, terminate and cast δ |
| by `T₀`: certificates, finalization | `eventually_fbcommitqc_sent`, `eventually_committed_of_assignable` | `broadcast_fbcommitqc` Δ, the assignments on the finalizer's own certificate δ (`rcvHop`), `finalize_commit` δ |

**What "re-run with deadlines" means here** is what it meant in §6.2.7:

* The existing `enabled_*` and `*_effect` lemmas are kept, with the gate
  added to the guards.
* Each `WeaklyFair` step becomes one (Δδ-justice) step, plus a stability
  argument on the window.
* `LRun.eventually_forall` becomes `TLRun.withinFrom_forall`.
* `Chorus.termination` is not consumed, for §6.2.7's reason: an index is
  not a clock reading.
* The untimed chains' facts that make guards stable carry over unchanged: the DA
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
  nobody finalizes by the vote deadline `X_v`, C1 means nobody has
  abandoned, so the forwarding `abandon` has not fired.

The MVBA's bound is then `T.ℓ`, which at the instance is
`Schedule.ℓ sch vfin` by `rfl`. The Chorus bound is stated with `T.ℓ` and
never with the MVBA's constants, so a change to the MVBA's timing model
reaches this leg only through `T`.

**The assembly, and F4.** One split, at the fallback commit votes'
deadline `X_v = M + 3Δ + ℓ_MVBA + 7δ`:

* *Case A*: some correct validator finalizes by `X_v`. Totality (§6.4.4)
  finalizes everyone by `X_v + Δ + 2δ`. Everyone already participates,
  since all start by `t`.
* *Case B*: nobody finalizes by `X_v`. Then nobody has abandoned by `X_v`
  (C1), every correct validator is active until then, and the tables below
  finalize everyone by `T₀ = X_v + Δ + 2δ`: the finalizer's own fallback
  commit certificate is a `Δ`-row on the votes, and the last two links use
  only the finalizing validator's own gate and its own certificate.

That is `M + 4Δ + ℓ_MVBA + 9δ` (`Ltight`), one Δ inside the paper's claim.
**F4 is confirmed.** The claim is stated and proven at the paper's
`5Δ + ℓ_MVBA` plus the δ-terms (`Chorus.timed_termination`), and the
sharper bound is the named theorem it follows from
(`Chorus.timed_termination_tight`, `Chorus.Ltight_le_Lchorus`). No step
uses the paper's outer split at `T₀`. The looseness is recorded for the
authors as P5 of [PaperAlignment.md](PaperAlignment.md) §6. "The MVBA tail
and the round" below has the milestones.

**The milestones to the MVBA proposals**
([Chorus/Timeline.lean](../Cadence/Chorus/Timeline.lean)). Up to the MVBA
proposals, each milestone is a lemma whose statement carries its deadline.
The premises are (Δδ-justice), (P-phase), C2 (for `D ≤ t + Δ`), and the
gate on the window (`ActiveUntil`, from C1 on the late branch,
`activeUntil_of_not_finalized`). Neither the MVBA's timing nor the bridge
enters before the proposals, except that the proposed vector must be
certified and `Valid` (from the evidence at saturation, below).

| milestone | lemma | by | `δ`s |
|---|---|---|---|
| every correct validator participating | `exists_start` | `t` | 0 |
| the deadline | `deadline_le_of_start` + (P2) | `D ≤ t + Δ` | 0 |
| first-round votes, all at one index | `within_voted`, `within_all_voted` | `M + Δ + δ` | 1 |
| every correct vote received by every correct validator | `within_received` | `M + 2Δ + δ` | 1 |
| a fallback signature per proposer | `within_fb_sig` | `M + 2Δ + 2δ` | 2 |
| the second-round vote, fast or fallback | `within_cast`, `within_all_saturated` | `M + 2Δ + 3δ` | 3 |
| the MVBA's trigger from correct senders | `correctTrigger_of_saturated` | (the same index) | 3 |
| a correct fast voter's FastQCs, everywhere (F7) | `within_complete_fast_metablock_by` | `M + 3Δ + 3δ` | 3 |
| the proposal on a correct `FBCert` | `within_input_of_fbcert` | `M + 3Δ + 3δ` | 3 |
| the proposal on the own meta-block (F9) | `within_input_of_fast` | `M + 3Δ + 4δ` | 4 |
| every correct validator's proposal | `within_all_input` | `t_M = M + 3Δ + 4δ` | 4 |
| a correct proposer's chunk, sent with its signature and recorded | `within_entry_recorded`, `within_proposal_recorded` | `max(X, GST) + Δ`, if `< D` | 0 |

The last row is not on the termination path: it is the proposal-inclusion
corollary's first step, with the strict `< D` of §6.4.2's "What
`s.deadline − Δ ≥ GST` becomes". The fallback chunks of the paper's
`M + 3Δ` milestone are in the next table, where the fallback commit round
needs them.

**The MVBA tail and the round**
([Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean)).
On the branch where no correct validator has finalized by the vote deadline
`X_v`, everyone is active until then (C1, `activeUntil_of_not_finalized`).
With `t_M = M + 3Δ + 4δ` and `X_d = t_M + ℓ_MVBA`:

| milestone | lemma | by | `δ`s |
|---|---|---|---|
| a FallbackQC signer's signature is there at its second-round vote | `fb_pos_sig_flip`, `fb_pos_sig_at_cast` | (saturation, `M + 2Δ + 3δ`) | 3 |
| its chunk sent to every validator with the signature (F8, F15) | `fb_pos_sig_chunks` | (saturation; the hop due by `M + 3Δ + 3δ`) | 3 |
| every correct validator decides in the MVBA | `within_all_decided` (`T.termination` on the projection) | `X_d` | 4 |
| a correct decision's entries recorded (the handlers) | `within_recorded` | `X_d + δ` | 5 |
| each correct validator's `local_mvba_complete` (its `mvba_terminate`) | `within_complete` | `X_d + 2δ` | 6 |
| each fallback commit vote, under the validator's own `B′` | `within_fbcommit_sig` | `X_v = X_d + 3δ` | 7 |
| the honest quorum's votes over the decided entries | (collapsed in `within_finalized_late`) | `X_v` | 7 |
| the finalizer's own fallback commit certificate | `within_fbcommitqc_sent` | `X_v + Δ` | 7 |
| every proposer's entry assigned, on that certificate (a local read) | `within_assigned_from` | `X_v + Δ + δ` | 8 |
| finalized | `within_finalized`, `within_finalized_late` | `T₀ = M + 4Δ + ℓ_MVBA + 9δ` | 9 |
| the split: early finalizers by totality | `within_finalized_split` | `X_v + Δ + 2δ = M + 4Δ + ℓ_MVBA + 9δ` | 9 |

Five facts of the proof, each in the file's header:

* **No common `B′`** (P2). Each validator waits and votes under its own
  decision. The handlers run on one correct decision, and the MVBA's
  agreement makes every correct decision's entries the recorded ones, so
  each validator's own `mvba_terminate` follows (as in the untimed
  `eventually_mvba_complete`).
* **The chunks precede the decision.** A correct FallbackQC signer signed
  before its second-round vote (`fb_sign_pos`'s guards), so its signature is
  at the saturation index (a first-flip fact). The same step sends every
  validator its chunk (F15, `fb_pos_sig_chunks`), and the chunks' hop is
  timed at the vote's split row.
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
  instance's own hypotheses, less its correct supermajority, which the
  family proves (`hqeFin`). `TimedTerminationClaim` is unchanged.
* **The δ-multiple.** The single split gives `4Δ + ℓ_MVBA + 9δ`
  (`Ltight`), and `Lchorus = 5Δ + ℓ_MVBA + 9δ` follows by adding a `Δ`.
  The `9δ` counts the model's vote-receipt step before the negative
  fallback entry; at `δ = 0` the bound is the paper's `4Δ + ℓ_MVBA`.

#### 6.4.4 `d_tot`-totality

**The route.** A correct validator finalizes at index `n` with clock `t`.
From that point, `local_committed_pos_backed` and
`local_committed_neg_backed` give every proposer's entry a commitment proof
the finalizer sent (`CertPos`, `CertNeg`: its re-broadcast fast commit
certificate, fallback commit certificate or MVBA commit certificate), and
the certificates are monotone. For another correct validator `j`, the
matching `commit_assign_*` route is at most a Δ-row (`rcvHop`: `δ` on `j`'s
own certificate) whose network part holds from `n`. Its
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
has no model counterpart. That is the granularity of the fragment, and it
is stated here because an auditor comparing the proofs will notice the
difference.

**The form to prove.** A generic lemma with the participation tolerance
as a parameter: under `d`-synchronized participation, the latency is
`max(Δ, d) + 2δ`. The class field is its instance at `d = Δ`. §6.4.6
("What the Conductor's timed claims take from this leg") says why the
parameter matters.

**The proof** ([Chorus/Totality.lean](../Cadence/Chorus/Totality.lean)).
`Chorus.totality` is `TotalityClaim sch d` at every schedule and tolerance,
over finitely many validators, by exactly the route above: the assignments
by `max(c, GST) + max(Δ, d) + δ` (`within_assigned`, from the per-sender
`within_assigned_from`), the finalization a
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
  proposes and sends all four validators their chunks, and the three
  correct ones record them.
* **Clock 1 (`D`).** The deadline marker fires. Everyone votes, receives
  the three correct votes, forms the FastQC, signs and casts its fast
  commit vote, broadcasts the commit certificate, commits the proposer's
  entry on validator 0's certificate and finalizes, all on the fast path.
  Then everyone abandons, as C1 permits.
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
(the availability report aside, which nobody owes). Re-dissemination
happens only inside a positive fallback signature, and nobody signs one.
Every timed row
therefore holds with its antecedent false. Both proven claims also apply to the run
(`example`s in the file), which checks that it lives at their instance
regime.

**What the model found: F11, re-dissemination off the fallback path.**
The first version of the run had validators 1 and 2 re-disseminate the
proposer's chunk at clock 0. The model's `redisseminate_chunk` then had no
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
the same gap for a validator that stays active. **Fixed** in the
statements: re-dissemination is owed only where the paper sends it (F8,
F14), and since F15 it is part of the fallback signer's own step.
`Chorus.termination` is proven against it. The witness needed no change, because its proof never used the
owed-condition; it only drops the forced re-dissemination steps.

**A second run, through the MVBA arm** (not required). This
run satisfies the proposal families, the handoff family and `ValidBridge`'s
completeness vacuously: nobody proposes to the MVBA and nobody decides.
That is enough for joint satisfiability, since one model suffices (§6.3).
A run that fires the case-(a) proposals, decides in the MVBA and finalizes
through the fallback commit round would show those three premises holding
non-vacuously, together with the rows that guard them. It would also be the
first witness in which `valid := (· = v⋆)` meets an actual decision. **Not
built:** it needs a hand-stepped MVBA decision (views,
votes and the commit certificate of `Mvba.Witness`'s run, driven from
Chorus's fallback or case-(a) proposals) and the fallback commit round.
Consistency does not depend on it.

#### 6.4.6 What the leg built, and what it hands the Conductor

The leg is complete. In the order it was built (the stages and their
records are in [History.md](History.md) § "From Bounds.md"):

1. **S1, the participation interface** (§6.4.1): `participate` and
   `abandon` in [Chorus.lean](../Cadence/Chorus.lean), the sending rules
   gated, C1 and C2 in [Interfaces.lean](../Cadence/Interfaces.lean),
   `InputLabel`, and `Chorus.termination` over the extended
   `TerminationClaim`, with the early-finalization split. Two run-level
   first-flip facts (`committed_pos_cert`, `committed_neg_cert`) give the
   early-finalization branch the commitment proof from a correct sender.
   **S1b, fired-once flags** (§6.4.7): every fair action of both models
   fires once, so fairness is over plain enabledness.
2. **S2, the statements** ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)):
   the schedule, the hop table with its gates and owed-conditions,
   `TimedJustice`, `PhasePunctual`, the timed `MvbaAdmissible`, the
   caller's conditions, and the two claims as `Prop` definitions before any
   proof. In [Timed.lean](../Cadence/Timed.lean): (Δδ-justice) as
   `BufferedFair` and `BufferedFairFamily` (with `N = N'`, a trivial gate
   and `δ ≤ D` it is `BoundedFair`, `bufferedFair_iff_boundedFair`), and
   the timed projection `Component.Projection.timed` with `timed_back`,
   `timed_forward` and `boundedFair_iff`. Both claims are generic in the
   MVBA contract `T`, and the system's MVBA is the instance
   `T := Mvba.mvbaTemporal …` (`mvbaTemporal_ℓ`,
   `timedMvbaAdmissible_atMvba_iff`, by `rfl`). `TotalityClaim` takes fewer
   premises than the class field allows — no phase timers, no MVBA, no
   bridge — so it is stronger than the field and implies it.
3. **S3, totality and the timeline to the MVBA proposals** (§6.4.4,
   §6.4.3): [Chorus/Totality.lean](../Cadence/Chorus/Totality.lean),
   [Chorus/Timeline.lean](../Cadence/Chorus/Timeline.lean).
4. **S4, the MVBA tail and the bound** (§6.4.3):
   [Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean),
   `Chorus.timed_termination` and `Chorus.timed_termination_tight` (F4).
5. **S5, the contract instances**
   ([Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean)):
   `Chorus.chorusTemporal` and `Chorus.chorusWithTotality`, at the
   system's configuration, every field proven and none weakened;
   `Chorus.slotConsensusFull` joins them with the fragment through
   `slotConsensus_of_temporal`, and `slotConsensusFull_toSafety` is `rfl`.
   `ℓ = Lchorus Δ δ ℓ_MVBA` and `d_tot = Ltot Δ δ Δ` are pinned by `rfl`,
   and are the paper's `5Δ + ℓ_MVBA` and `Δ` at `δ = 0`. Four facts of the
   instance:
   * **Termination is `Chorus.termination`**, not the unbounded corollary
     of the bounded claim. The untimed field's antecedents are
     participation and C1 only; the bounded claim also needs Δ-synchronized
     participation and C2, which the field does not give. `Admissible`
     carries both claims' premises, each by name.
   * **Quiescence is stated from a reachable state.** Its MVBA half needs
     two facts that hold only along a run: an MVBA proposal is made while
     participating (`participating_of_mvba_proposed`), and an abandonment
     is forwarded (`mvba_abandoned_of_abandoned`). So
     `SlotConsensusTemporal.quiescence` takes `S.reachable st`, as
     `ACSTemporal.quiescence` does
     ([CompositionContracts.md](CompositionContracts.md) §5).
   * **`admissible_exists` is a generic idle run**: from any initial state
     of any configuration, nobody participates, the markers fire at the
     landmarks, and the caller abandons one validator at every other step.
     It needs a non-empty proposer set (§6.4.5; P14) and a view after the
     first with a correct leader, which `LeaderRotation` gives.
   * **The deadline is per slot** (`FamilySchedule`: one MVBA schedule and
     `D : slot → time`), since the class's `deadline` is a function of the
     slot; `ByzNodeSetHonestQuorum` is built for the family (`hqeFin`)
     rather than taken.
6. **S6, non-vacuity** (§6.4.5): [Chorus/Witness.lean](../Cadence/Chorus/Witness.lean).

**What the Conductor's timed claims take from this leg.** The Conductor's
Totality, `B`-Boundedness and `R`-Recovery (`OrchestratorTemporal`) consume
Chorus's claims in Proposition 13 (`prop:window-synchronization`) (totality),
Proposition 14 (`prop:conductor-open-to-complete`) (ℓ-termination), and the
recovery chain through `Φ_oc = ℓ_chorus + d_tot` and the parameter
assumptions of Algorithm 7 (`algorithm:conductor`). This leg hands over:

* **Premises the composition discharges.** Each of Chorus's caller
  conditions is one a composed run proves (`Composed.corollary4`):
  * participation by `t`: the glue invokes `participate` at `open`
    (Algorithm 1, line 17 (`line:participate`));
  * Δ-synchronized participation: the Conductor's own opening totality
    (Lemma 15 (`lemma:conductor-totality`));
  * C2: `integrity_timing`, with `deadline s = start_time s + Δ`;
  * C1: the glue abandons only after finalizing (Algorithm 1, line 23 (`line:abandon`)).

  C1 and C2 are antecedents over the class's own observables for that
  reason.
* **`ℓ` and `d_tot` as data, with closed values.** They appear in
  assumptions (1)–(4) of Algorithm 7 (`algorithm:conductor`); the instance
  pins them.
* **Totality in the tolerance-parametric form of §6.4.4.** This is F3: the
  window induction needs Chorus's latency not to exceed the tolerance the
  Conductor grants. At δ = 0 both are Δ, and the paper's induction goes
  through; at δ > 0 `max(Δ, d) + 2δ > d` for every `d`. The Conductor
  leg works at δ = 0 (C3, [ConductorBounds.md](ConductorBounds.md) §5), and
  the parametric lemma leaves that choice to it.
* **One time theory and one Δ across the system.** Chorus, the MVBA, the
  Conductor and the ACS share the run's clock, and the Conductor's schedule
  extends Chorus's ([ConductorBounds.md](ConductorBounds.md) §6.2).
* **The inputs are the glue's.** `Chorus.slotConsensusSafety`'s `step`
  excludes the inputs, so the composed system's Chorus moves only when the
  glue drives `participate`, `propose` and `abandon`
  ([ConductorBounds.md](ConductorBounds.md) §9, K1); the glue's safety
  theorem is generic and unaffected. Corollary 4
  (`cor:chorus-correctness-within-cadence`) then closes the loop
  (`Composed.corollary4`).

#### 6.4.7 Fired-once flags: fairness over plain enabledness

**The decision.** Disabledness is modelled in the protocol, not resolved
in the proof. Every fair action that could stay enabled after it has fired
has a local "not already" guard, as the paper describes the rule, so the
fairness premises use **plain enabledness**: an action enabled from some
point on eventually fires, with no qualifier about state-changing steps.
Counting only state-changing steps (TLA+'s `⟨A⟩_v`) would also be sound,
but it resolves in the proof a scheduling non-determinism that an
implementation resolves in its protocol logic.

**Where the non-determinism was.** Most honest per-validator actions
disable themselves after firing: `vote` (`¬ local_voted`), `send_commit`
(`¬ commit_sent`), the timeouts (`¬ timed_out`), `decide`
(`∀ E, ¬ decided`), the leader's proposal (`¬ proposed_in`), and
`adopt_prepqc` (the lock-view guard). The others got the guard:

* **Mvba: the anonymous assemblies** `form_prepqc`, `form_commitqc`,
  `form_tc_lock` and `form_tc_nolock`. They have no validator, and a quorum
  parameter `q`, so once the certificate exists every `q`-variant stays
  enabled without effect. In the supplement (at the paper target) each is a
  step of one validator with a local condition:
  * `TryFormPrepQC`: pᵢ forms `prepareQC` if it "has not already formed a
    prepare certificate in the current view" (`adopt_prepqc`, §6.2.4);
  * the commit certificate: pᵢ forms `CommitQC` "provided that it has not
    already learned a decision certificate", and records it as
    `DecidedQC_i`;
  * the timeout certificate: "upon first collecting 2f+1 valid timeout
    messages", pᵢ forms `TC_{s,v}` and processes it through `SyncView`
    (Supplement, Algorithm 1, line 85 (`line:mvba:ht-advance`)).
* **Chorus:** `aggregate_fastqc_pos/neg i j …` (Algorithm 4, line 18 (`line:fast-formqc`)),
  `broadcast_commitqc_pos/neg c j …` (Algorithm 4, line 31 (`line:fast-collect-commit`),
  Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)), and six more families listed below.
  The paper writes the first two as `upon` handlers of an event-driven
  protocol, without "first time" (only the fast meta-block rule says it).
  The model reads an `upon` handler as running once when its condition
  becomes true. That is the conventional reading, but the paper states no
  convention: P6 of [PaperAlignment.md](PaperAlignment.md) §6.

**The shape.**

* A **per-validator** action with a quorum parameter (no `∃`-quorum ghost
  in a guard, as in `adopt_prepqc i v e q`). It sets a **local** record of
  what it formed, and a guard on that record's absence disables every
  `q`-variant at once. A negative read of the actor's *own local* state is
  what every existing honest guard does; no network relation is read
  negatively ([Locality.md](Locality.md) R1, R2). It also sets the network
  certificate relation, as `adopt_prepqc` sets `msg_prepqc`, where the
  certificate is carried on (timeouts, broadcasts).
* The **anonymous forming stays**, but is **not fair**: it is the
  adversary's capability to aggregate signatures it saw, so safety's
  adversary is unchanged. It moves into an unfair label class (with the
  `byz_*` family, or its own class, with a `not_justice_of_*` pin), and
  has no hop-table row. Where an honest per-validator action replaces it
  in a chain, the chain's link changes accordingly.
* Where the effect record itself is the natural flag (`aggregate_fastqc_*`
  sets `local_fastqc_*`), the guard is its absence, and no new relation is
  needed.

**The fairness side.**

* [Fairness.lean](../Cadence/Fairness.lean)'s `WeaklyFair`,
  `WeaklyFairFamily` and `StronglyFair`, and
  [Timed.lean](../Cadence/Timed.lean)'s `BoundedFair`, are over `Enabled`.
  `EnabledMove` remains only as the vocabulary of the bridges below.
* Both `FJustice`s and `Mvba.BoundedJustice` are stated with plain
  enabledness.
* **The acceptance criterion, machine-checked, per model:** at every
  state, every enabled fair label is move-enabled
  (`∀ l, JusticeLabel l → Enabled … st l → EnabledMove … st l`). It says
  the model has no fair action that stays enabled without effect, so the
  flag discipline is checked rather than read. For the audit surface it is
  the statement that, for this model, weak fairness over plain enabledness
  and over state-changing steps are the same premise. It is proven per
  action from the guards and the generated frame lemmas, in plain Lean, not
  as a Veil cell, and the premises' docstrings cite it.

**The Chorus half.** The acceptance lemma is
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

*The inventory, as the lemma found it.* Every fair action that could stay enabled after firing now has a "not
already" guard on a record it sets itself. All the reads are negative reads
of the acting validator's own local state ([Locality.md](Locality.md)
R1). No network relation is read negatively.

| action | old guard, in words | new guard, in words |
|---|---|---|
| `aggregate_fastqc_pos/neg` | a supermajority signed | … and `i` does not hold this FastQC yet |
| `broadcast_commitqc_pos/neg` | a correct and active collector, or any Byzantine one; `2f+1` cast commit votes | a correct and active collector that has not broadcast a certificate for `j` yet (`local_commitqc_sent c j`); the Byzantine branch is now `byz_broadcast_commitqc_*` |
| `commit_sign_pos/neg` | `i` holds the FastQC and has not cast | … and has not signed an entry for `j` yet (`local_commit_entry i j`) |
| `fb_sign_pos/neg` | the fallback-entry conditions | … and `i` has not signed its fallback entry for `j` yet (`local_fb_entry i j`) |
| `on_mvba_decide_pos/neg` | `i` decided `v`, the entry is certified | … and `i` has not recorded entry `j` of its decision yet (`local_mvba_recorded i j`) |
| `cast_fb_commit` | the DA wait holds | … and `i` has not cast its fallback commit vote yet (`local_fbcommit_voted i`) |
| `commit_assign_pos_*` | no *other* root committed for `j` | no root committed for `j` yet |
| `commit_assign_neg_*` | no positive entry committed for `j` | … and not the negative one either |

What the lemma required:

* **`commit_assign_*` needs per-entry guards.** `¬ local_committed` is set
  by `finalize_commit`, not by `commit_assign_*`.
* **The families besides the two named above**: the commit and fallback
  entries, the certificate broadcasts, the decision handlers, the
  handoff and the fallback commit vote. For those whose effect is a network
  tuple or a shared record (`aux_mvba_decided_*`), the flag is a local
  record: `local_commit_entry`, `local_fb_entry`, `local_commitqc_sent`,
  `local_fbcommitqc_sent`, `local_mvba_cert_sent`, `local_mvba_recorded`,
  `local_mvba_qc_accepted` and `local_fbcommit_voted` (Chorus.lean,
  "Fired-once records"). Where the effect is already local
  (`aggregate_fastqc_*`, the vote receipts `receive_vote_*`,
  `commit_assign_*`), the guard is its absence. The proposer's chunks are
  sent inside `propose`, an input, which carries no fairness.
* **The Byzantine branches of the two anonymous capabilities became their
  own unfair actions**, `byz_broadcast_commitqc_*` and
  `byz_redisseminate_chunk` (the re-dissemination is part of `fb_sign_pos`
  since F15; its Byzantine form remains, as any holder of `f+1` chunks can
  send). With the branch left inside the fair action and
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
* **The other candidates** need nothing. `record_chunk` already requires
  that no positive entry is recorded, the phase markers move the phase, and
  the MVBA proposal's effect is the `Mvba` model's input record, whose
  absence its guard requires.

**The Mvba half.**

* **The model.** The three rules the supplement gives a "not already"
  condition are one correct validator's step each, in its current view,
  with the quorum as a label parameter, as in `adopt_prepqc i v e q`:
  * `form_own_commitqc i v e q` — `TryFormCommitQC` and `Decide` in one
    handler segment: from `2f+1` `Commit`s of the current view, "provided
    that it has not already learned a decision certificate", form the
    `CommitQC`, record it as `DecidedQC_i` and decide. `DecidedQC_i` is set
    exactly when a validator decides (both decision paths set it), so the
    guard is `∀ E, ¬ decided i E`, with no relation of its own. The
    certificate is put on the network, where `decide` reads it.
  * `form_own_tc_lock i v q r₀ w e` and `form_own_tc_nolock i v q` —
    `HandleTimeout`, "upon first collecting `2f+1` valid timeout messages":
    the local record `tc_formed i v`, whose absence is the guard.
    The certificate goes on the network; `SyncView` is the next step
    (`sync_view`, `sync_view_adopt`).

  The four anonymous assemblies stay, as the adversary's capability, in
  the unfair class `AssemblyLabel` (`not_justice_of_assembly`), with no
  hop-table row. Only positive reads of `msg_*`; at most 6 parameters. One
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
  pinned at the trio. The four assemblies were the only fair labels of
  the Mvba that could stay enabled after firing.
* **Manual cells.** `form_own_commitqc × commitqc_agree` (the
  `form_commitqc` cell's argument) and `form_own_commitqc × agreement` (the
  same argument at the decision the step makes, with `decided_backed`). The
  number of manual cells is in [Architecture.md](Architecture.md); the cell
  count is the `#veil_status Mvba` pin in
  [Mvba/Certify.lean](../Cadence/Mvba/Certify.lean).
* **The liveness and timed stack:**
  * the untimed chains go through a settled correct validator, which
    forms the commit certificate (`eventually_commitqc_of_settled`) and
    the view's timeout certificate (`eventually_tc_of_timed_out_quorum`);
  * the timed premise: the three steps are network hops with
    first-delivery clauses; every network label is one validator's step,
    and its `in_view` guard is the lower-view discard; the `timeouts` clause names
    the validator that forms the certificate;
  * `good_view_decides` concludes that some correct validator has decided
    by `E₀ + Lcert`, since the step that forms the certificate decides,
    and the transfer term charges the others' decisions;
  * in both witnesses each correct validator forms its own commit
    certificate, and at the idle state no fair label is enabled at
    all.
* **NoLock** ([Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean)) mirrors
  the three steps. As a restriction, it drops the anonymous `form_prepqc`
  and `form_tc_*`, whose certificates the correct validators form
  themselves. It keeps `form_commitqc`: the counterexample's view-1 commit
  certificate has to be the adversary's aggregation, since a correct
  validator that forms one decides on it and halts. The checker, with
  `sequential := true`, finds agreement violated, and the file pins the
  witness.
* **Chorus:** `MvbaAdmissible`'s `Mvba.FJustice` of the projected run
  ranges over the per-validator steps, not the anonymous assemblies.

**The premises, and the bridges.**

* **The premises read plainly.** [Fairness.lean](../Cadence/Fairness.lean)'s
  `WeaklyFair`, `WeaklyFairFamily`, `StronglyFair` and the projection's
  `WeaklyFairIn`, [Timed.lean](../Cadence/Timed.lean)'s `BoundedFair` and
  [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean)'s `BoundedFairWhile`
  are over `Enabled`: an action enabled from some point on eventually fires
  (within its window, for the timed ones). Both `FJustice`s and
  `Mvba.BoundedJustice` are stated with these notions, and their
  docstrings cite the acceptance lemma.
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
  sides are weak fairness over state-changing steps, TLA+'s `WF_v`: for
  these models the plain premise is the same one. `EnabledMove` and the
  move forms remain only as the vocabulary of those bridges.

### 6.5 The Conductor leg

The Conductor's timed claims (`OrchestratorTemporal`: Totality,
`𝓑`-Boundedness, `𝓡`-Recovery) and the composition that closes the
Cadence loop (Corollary 4 (`cor:chorus-correctness-within-cadence`)) are
their own page, [ConductorBounds.md](ConductorBounds.md). It takes up the
hand-over list of §6.4.6 ("What the Conductor's timed claims take from
this leg"), answers F3 and C3 (its §5), and records the findings from F16
on.
