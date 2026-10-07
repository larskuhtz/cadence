# Conductor bounds — the timed claims of the Conductor and the composed system

*The timed claims of the Conductor and of the composed system: their
timing models and their findings. [The guide's chapter
6](https://larskuhtz.github.io/cadence/guide/components/) introduces the claims.*

This document explains how the development states and proves the paper's
timed claims about the Conductor (Algorithm 7 (`algorithm:conductor`)) and
about the composed system that runs it together with Chorus: what the paper
claims, how the module contract states it, what is assumed of the ACS, the
timing model, and the findings F16–F31 the formalization produced. Every
claim here is proven. The theorems with their axiom pins are indexed in
[Cadence.lean](../Cadence.lean); the premises, one line each, are
[Premises.md](Premises.md) §0 (the composed claims) and §9 (the Conductor's
own). [Bounds.md](Bounds.md) §6.2 and §6.4 have the timing machinery this
document reuses (the MVBA's and Chorus's). How the leg was planned and built,
session by session, is [History.md](History.md) § "Records moved out of the
living documents (R33)".

## 1. In short, for an auditor

**What the paper proves.** Theorem 2 (`thm:conductor-correctness`): "When
run within Cadence, Conductor is a correct implementation of the
orchestrator primitive, with `𝓑 = 2W − p` and `𝓡 = 2Wτ`." Three of
Module 2 (`mod:orchestrator_2`)'s properties are about time or need it:

* **Totality**, in the stronger form Lemma 15 (`lemma:conductor-totality`)
  proves: if a correct validator opens slot `s` at time `t`, every correct
  validator opens `s` by `max(t, GST) + d_tot`, where `d_tot = Δ` is
  Chorus's totality latency;
* **`𝓑`-Boundedness**, Lemma 14 (`lem:boundedness`): at most `2W − p`
  opened slots of a correct validator are not completed;
* **`𝓡`-Recovery**, Lemma 16 (`lemma:conductor-recovery`): every slot
  whose starting time is at least `GST + 2Wτ` is opened by every correct
  validator exactly at its starting time.

Boundedness holds for the Conductor alone. Totality and Recovery hold only
"when run within Cadence", because they need slots to complete, and slots
complete when Chorus finalizes them. The paper's proof is one induction over
the windows (Proposition 13 (`prop:window-synchronization`)), which
alternates between Chorus's conditional totality and the Conductor's
openings. Corollary 4 (`cor:chorus-correctness-within-cadence`) then closes
the loop the other way: within Cadence, Chorus's own condition,
Δ-synchronized participation, *is* the Conductor's totality.

**What those claims feed.** Within Cadence, Recovery gives `𝓡`-Liveness
(Definition 2 (`def:liveness`), Lemma 2 (`lemma:cadence-liveness`)) and
censorship resistance (Definition 3 (`def:censorship-resistance`)) for every
slot starting `2Wτ` after GST. Boundedness gives bounded concurrency (Lemma 5
(`lemma:cadence-bounded-concurrency`)). Corollary 4 makes Chorus's timed
claims (`ℓ = 5Δ + ℓ_MVBA`, `d_tot = Δ`; [Bounds.md](Bounds.md) §6.4) hold
with no caller premise left in the composed system.

**What is proven.**

* **The Conductor's three claims**, stated with their premises in
  [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean):
  Boundedness at the paper's `2W − p` (`Conductor.boundedness`), from the
  model's interval invariant `[bounded_tail]` and the window widths;
  `d_tot`-Totality by the window induction (`Conductor.totality`, with
  Proposition 13 and its three corollaries); Recovery at the paper's `2Wτ`
  through Propositions 14–19 (`Conductor.recovery`), and at the sharper
  `(W + p − 1)τ` (`Conductor.recovery_sharp`).
* **The full orchestrator contract**: `Conductor.conductorTemporal`,
  `Conductor.conductorWithTotality` and the join `Conductor.conductorFull`
  ([Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean)), for an
  arbitrary ACS meeting its contract.
* **The composed system's claims**
  ([Composed/](../Cadence/Composed/Corollary4.lean)): every condition each
  module takes from its caller is a theorem about the composed run;
  Corollary 4 (`Composed.corollary4`), Lemma 5 at `2W − p`
  (`Composed.boundedConcurrency`), `𝓡`-Liveness (`Composed.liveness`) and
  censorship resistance (`Composed.censorship`), each at `2Wτ` and at
  `(W + p − 1)τ`.
* **Non-vacuity**: one model of the composed system meets every premise of
  the four composed claims at once, and its orchestrator's part every
  premise of the Conductor's three (§8.2).

The safety half of the composition is
`Cadence.system_positional_log_safety` ([System.lean](../Cadence/System.lean)),
and the glue drives Chorus's `participate`, `propose` and `abandon` inputs
through the contract, so the composed system's Chorus is not inert (§4.1).

**What the timed claims assume.** The same timing model as the MVBA and
Chorus claims: one clock, one time theory and one Δ for the whole system.
Messages between correct validators arrive within Δ after GST, local steps
are instantaneous (δ = 0, §5), and timers fire on time. The ACS meets its
module (Module 4 (`mod:acs`)), since the target leaves the ACS unspecified
(§3), and the four parameter assumptions of Algorithm 7
(`algorithm:conductor`) hold. Every condition the Conductor needs from its
caller, and every condition Chorus needs from the Conductor, is discharged by
the composition. None is a premise of the composed claims.

**Three design decisions** (each Lars's, with its reason in the section
named):

1. **The ACS is an assumed module (§3).** The target has no concrete ACS, so
   the timed claims are relative to any instance of the ACS contract, and the
   ACS is named in the trust statement. A plain-Lean ideal ACS shows that the
   premises are consistent. P17 records the gap for the authors.
2. **"Within Cadence" enters the contract in rely form (§2.3).** The
   conditions the paper takes from Cadence are antecedents over the
   orchestrator's own observables (C5), and a Conductor-specific level
   states the `d_tot` form Corollary 4 consumes (C4).
3. **δ = 0 (§5).** The Conductor's and the composed claims are proven at the
   paper's instantaneous local computation, a plain schedule premise.
   Chorus's and the MVBA's theorems keep their δ-general forms, and F3
   records the degradation at δ > 0.

**The findings (§7, F16–F31; for the authors P15–P19,
[PaperAlignment.md](PaperAlignment.md) §6).** Every one is closed in the
development. Two reached the existing safety claims. **F18 / P16:** Module
4's Validity bounds the size of the decided set but not the number of pairs
per validator, and the median argument behind Proposition 7
(`prop:acs-nonoverlap`), and the model's stated bridge at `acs_decide`, need
at most `f` Byzantine-attributed pairs. The contract carries the
one-pair-per-validator field, which every natural ACS satisfies. **F25:** the
model now covers all of the paper's `p ∈ {0, …, W − 1}`. The other findings
concern the timed statements and the model's timing freedoms.

**The design in one place.**

* ACS: a contract (§3.3 (b)), with the ideal ACS (§3.3 (c1)) as the
  consistency witness.
* C4 (the `OrchestratorWithTotality` level) and C5 (rely antecedents for
  Totality and Recovery) (§2.3).
* C6 (one pair per validator in a decided ACS set), C7 (the ACS's `abandon`
  in `ACSSafety`) and C8 (Slot Consensus's inputs in `SlotConsensusSafety`),
  each with its cross-frames (§3.4, §4.1; F18–F20).
* δ = 0 for the Conductor's and the composed claims, a field of the schedule
  (§5).
* The clock is the run's. The Conductor's `now` equals it through
  `OrchestratorTemporal.clock_agrees`, so `tick` is the system's clock step
  (§6.1).
* One schedule record, `ConductorSchedule`, extends Chorus's
  `FamilySchedule` with the windows and the four parameter assumptions as
  fields (§6.3).
* A part of the composed run that stops stepping is projected by a stutter
  lift, and a part's premise applies once a correct validator has started
  the part (F24; [PartProjection.lean](../Cadence/PartProjection.lean)).

## 2. The claims, and what the contract says about them

### 2.1 The paper's chain

Every result below is from Appendix D.2 (`subsection:conductor-proof`). The
arrows are "is used by".

* **The ACS's two assumptions are met.** No premature abandonment is
  Proposition 12 (`prop:acs-no-premature-abandonment`): a correct validator
  abandons `ACS[ω]` only at Algorithm 7, line 45 (`line:acs-abandon`),
  inside the handler that fires on its own decision. Δ-synchronized
  proposals is Corollary 2 (`cor:proposal-synchronization`), the fourth
  condition of the window induction.
* **The window induction**, Proposition 13 (`prop:window-synchronization`),
  over Definition 6 (`def:window-synchronized`)'s four conditions: entry,
  openings, completions, and proposals to the next ACS. Each is "if one
  correct validator does it at `t`, all do it by `max(t, GST) + d_tot`".
  The step consumes the ACS's Δ-Totality (entry), Chorus's `d_tot`-Totality
  under Δ-synchronized participation (completions), and the Conductor's
  readiness rule. → Lemma 15 (openings), Corollary 1
  (`cor:entry-synchronization`) and Corollary 3
  (`cor:completion-totality`).
* **Open-to-complete**, Proposition 14 (`prop:conductor-open-to-complete`):
  a slot opened at `t` is completed by `max(t, GST) + d_tot + ℓ_chorus`. It
  consumes Lemma 15 and Chorus's `ℓ`-termination (Lemma 11
  (`lemma:chorus-termination`)). Its constant is `Φ_oc = ℓ_chorus + d_tot`.
* **Every window is entered**, Proposition 15 (`prop:enters-every-window`):
  from Proposition 14 and the ACS's Termination and Totality.
* **The recovery timeline:**
  * Proposition 16 (`prop:window-open-time`): entry by
    `max(T₁(ω), GST) + d_tot + ℓ`, using assumption (3) and the median's
    lower bracket;
  * Proposition 17 (`prop:window-progression`): a post-GST window entered
    by `T_p(ω)` is followed without a gap and on time, using assumptions
    (1)–(2) and the median's upper bracket;
  * Proposition 18 (`prop:smooth-windows`): from the second post-GST window
    on, using assumption (4);
  * Proposition 19 (`prop:first-post-gst-window-time`): the first post-GST
    window starts by `GST + Wτ`, using assumptions (2) and (4) and the upper
    bracket. → Lemma 16.
* **Boundedness**, Lemma 14, from Proposition 11
  (`prop:open-count-window`): `ωW` slots are opened in window `ω`, and the
  readiness rule leaves at most the last `W − p` of the earlier windows
  open.

The parameter assumptions, Algorithm 7, lines 7–10
(`line:assumption-one`–`line:assumption-four`), with
`Φ_oc = ℓ_chorus + d_tot` and `ℓ` the ACS's latency:

1. `(p − 1)τ + Φ_oc + ℓ ≤ Wτ`
2. `(p − 1)τ + Φ_oc ≤ (W − 1)τ`
3. `Δ < ℓ`
4. `d_tot + ℓ ≤ (p − 1)τ`

### 2.2 What the contract states

`OrchestratorTemporal` ([Interfaces.lean](../Cadence/Interfaces.lean)) has
`Admissible`, `admissible_exists`, `clock_agrees`, the caller's latencies
`caller_d_tot` and `caller_ℓ`, an eventual `totality`, `bound` with
`boundedness` (a state-level count), and `recovery_time` with `recovery`.
`OrchestratorWithTotality` adds `d_tot` and the bounded Totality. The
Conductor proves the fragment, `Conductor.orchestratorSafety`
([Composition.lean](../Cadence/Composition.lean)), and the temporal levels,
`Conductor.conductorTemporal` and `Conductor.conductorWithTotality`
([Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean)). Three
things the paper's chain needs are stated in the contract for that reason:

* the `d_tot` form of Totality, which Proposition 14 and Corollary 4 consume
  (F16, C4);
* "within Cadence", as antecedents (F17, C5, §2.3);
* the ACS's abandonment, and a one-pair-per-validator decided set, at the
  fragment the Conductor instantiates (F18, F19, §3.4).

### 2.3 How "within Cadence" enters: C4 and C5

The Conductor's Totality and Recovery are false for the Conductor alone. A
caller that never completes a slot leaves every correct validator in window
1 forever. The contract states them in **rely form (C5)**: Totality and
Recovery take, as antecedents over the orchestrator's own observables
(`opened`, `completed`), the two conditions the paper's proof takes from
Cadence. Both are conditional, exactly as Chorus's fields are:

* **(R-tot)** (`OrchestratorSafety.CallerTotality`): for every slot `s`, if
  the openings of `s` are synchronized within `d` (each opening at `t` is
  followed by every correct validator's by `max(t, GST) + d`), then so are
  its completions, at the caller's latency `caller_d_tot`;
* **(R-term)** (`OrchestratorSafety.CallerTermination`): for every slot
  `s`, if the openings of `s` are synchronized within `d` and every correct
  validator opens `s` by `t`, every correct validator completes `s` by
  `max(t, GST) + caller_ℓ`;
* and "a correct validator completes only slots it has opened", which the
  fragment gives through the glue's `[delivered_opened]`.

The tolerance is one constant: the paper's induction closes because
Chorus's totality latency equals the tolerance its condition grants ("both
equal `Δ = d_tot`", the paragraph before Definition 6
(`def:window-synchronized`)). Eventual Totality takes (R-tot) only, as the
paper's proof uses no termination for it. `Admissible` stays what it is for
the MVBA and Chorus: the scheduler, the network and the timers, nothing about
the caller. The composition discharges (R-tot) and (R-term) from
`Chorus.chorusWithTotality`'s `totality` and `bounded_termination` through
the glue (open ↦ participate, finalize ↦ complete;
`Composed.caller_totality`, `Composed.caller_termination`). Non-circularity
is visible in the types: each side is a conditional statement about one
slot, and the window induction lives inside the Conductor's proof.

The alternative, an `Admissible` that says "`r` is the orchestrator part of
an admissible composed run", is literally the paper's phrase. It is not
used: it puts the caller's behaviour into `Admissible`, which the rely form
avoids ([Bounds.md](Bounds.md) §6.4.1, "The class change"), and it would
make the Conductor's instance depend on Chorus's model.

**C4.** Module 2's Totality is eventual, so the `d_tot` field sits at a
Conductor-specific level, `OrchestratorWithTotality`, as
`SlotConsensusWithTotality` holds Chorus's. Its `d_tot` is pinned by `rfl`
(`Conductor.conductorWithTotality_d_tot`), and is the paper's `Δ` at
`δ = 0` (`Conductor.conductorWithTotality_d_tot_paper`). Corollary 4 and
Proposition 14 consume it. The paper side of C4 and C5 is P15.

## 3. The ACS question

### 3.1 What the Conductor's claims take from the ACS

| field of `ACSTemporal` / `ACSSafety` | timed? | used in |
|---|---|---|
| `agreement`, `validity_genuine`, `integrity` | no | safety, and Proposition 16's "a correct proposer proposed by `T₁(ω)`" |
| `validity_quantitative` with `fault_bound` | no (cardinality) | the median brackets: Propositions 7, 16, 17, 19 |
| `abandon`, `abandoned` and `NoPrematureAbandon` | no | the antecedent of both timed fields; Proposition 12 discharges it |
| `SyncProposals` (Δ-synchronized proposals) | yes | the antecedent of both timed fields; Corollary 2 discharges it |
| `termination` with `ℓ` | **yes** | Propositions 15, 16 and 17 (case 2) |
| `totality` with `Δ` | **yes** | Proposition 13 (entry), Propositions 15 and 17 (case 1) |
| `propose_enabled`, `abandon_enabled` | no | the Conductor's rows: its handlers give these inputs (F26) |
| `Admissible`, `admissible_exists` | defines the runs | every use of the two timed fields |
| `quiescence` | yes (run-level) | no Conductor claim |

So the Conductor needs both of the ACS's timed fields, and Algorithm 7's
"Uses" line, which names only "ACS (`ℓ`-termination)" (Algorithm 7, line 12
(`line:acs-instances`)), under-reports them (P17).

### 3.2 What the target says

The supplement's Section 2, "Concrete Instantiation of ACS", is empty at
`48cac9a`. It has a heading, no label, and two authors' margin notes: the
MVBA "seems like a good candidate", and a multi-shot consensus is an
alternative. The supplement's practical Conductor (Supplement, Section 3
(`sec:practical-conductor`)) uses an ACS "with candidate sets validated by"
a predicate, but that Conductor is outside the verified surface
([PaperAlignment.md](PaperAlignment.md) §5.8). **The ACS used by the
verified Conductor is therefore unspecified at the target** (P17).

### 3.3 The ACS is an assumed module

**(b) The ACS is a contract.** The timed claims are stated for an arbitrary
`[ACSTemporal …]` at the fragment the Conductor instantiates, with the
per-window projections as `T.Admissible` runs. The ACS is then **an assumed
module, named in the trust statement**, as the MVBA was before its
instantiation ([Bounds.md](Bounds.md) §6.2). This is what Algorithm 7 says ("Uses: ACS")
and what Theorem 2's proof does. The contract carries the repairs C6 and C7
(§3.4) and the input-enabledness of F26.

**(c1) The ideal ACS is the consistency witness.** A plain-Lean instance of
`ACSSafety` and `ACSTemporal`, `Cadence.IdealAcs.acsTemporal`
([Conductor/IdealAcs.lean](../Cadence/Conductor/IdealAcs.lean)): one global
decided set per window, fixed by the first correct decision; each correct
validator decides within `Δ`. It is the class's model, not a protocol, so it
is not "the ACS"; it shows that the premises can hold together, and it is the
ACS of the composed witness (§8.2).

**(a) A concrete ACS replaces the assumption once the paper specifies one.**
The standard reduction builds an ACS from the MVBA: each validator
broadcasts its signed proposal, proposes a set of `2f + 1` signed proposals
from distinct validators to an MVBA whose validity predicate checks the
signatures, and takes the MVBA's decision as the ACS's. The target specifies
none of these choices, so building it now would make a claim about *an* ACS
and not the paper's, which the single-target rule forbids
([PaperAlignment.md](PaperAlignment.md) §0). Once a target revision
specifies the ACS, the supplement's MVBA is the natural base, and its timed
instance `Mvba.mvbaTemporal` exists. A multi-shot consensus, the second
margin note, is not in the target either.

### 3.4 Two contract repairs

* **C6: one pair per validator (F18, P16).** `ACSSafety.decided_unique`: a
  correct decider's set holds at most one slot per validator, and
  `validity_quantitative` counts distinct validators. With the system's
  fault bound (at most `f` Byzantine validators), the median lemma's
  hypothesis (`IsMedian.between_correct`'s "at most `f`
  Byzantine-attributed entries", [Windows.lean](../Cadence/Windows.lean))
  follows from the contract: `Cadence.acs_median_bracket`
  ([AcsMedian.lean](../Cadence/AcsMedian.lean)) proves the link.
* **C7: the ACS's `abandon` in the fragment (F19).** `abandon`,
  `abandoned` and their frames are in `ACSSafety`, as `MVBASafety` has them,
  with the cross-frames: `propose` leaves `abandoned` unchanged, and
  `abandon` leaves `proposed` unchanged. The model's `enter_window` performs
  Algorithm 7, line 45 (`line:acs-abandon`), so Proposition 12 is a fact of
  the model, the invariant `[acs_abandoned_decided]`, and not a reading of
  the paper.

## 4. The glue: the composition

### 4.1 The glue drives Chorus's inputs

**[Interfaces.lean](../Cadence/Interfaces.lean) (C8, F20).** The glue
instantiates only `SlotConsensusSafety`, so Chorus's three inputs live
there: `participate`, `abandon` and `propose`, with their observables
(`participating`, `abandoned`, `proposed`), effects, step frames and
initial conditions, all first-order, together with

* the per-input cross-frames ("`participate` at `i` leaves `abandoned` and
  `proposed` unchanged", and so on, the `complete_frame` pattern);
* the per-validator frames ("an input at `i` leaves `j`'s records
  unchanged").

Without them, "the glue abandons only after finalizing" would not imply C1
at the contract level, since a `participate` could set `abandoned`.
`SlotConsensusTemporal` keeps `sent`, `Admissible`, Termination and
Quiescence.

**[Cadence.lean](../Cadence/Cadence.lean).** Three handlers drive the
contract's inputs, as `acs_propose` drives the ACS's:

* `on_open i s sc_next`, Algorithm 1, line 17 (`line:participate`): requires
  `orch.opened os i s` and `sc.participate (sc_state s) i sc_next`;
* `on_propose`, Algorithm 1, line 19 (`line:propose`): drives `sc.propose`,
  and requires `participating i s`, the order of Algorithm 1, lines 17–19
  (`line:participate`–`line:propose`);
* `on_finalize`, Algorithm 1, lines 20–23
  (`line:upon-finalize`–`line:abandon`): performs `sc.abandon` in the same
  step as `orch.complete`.

The glue keeps no copy of these calls: its `participating`, `abandoned` and
`proposed` are ghosts that read the instance's own records. Two first-order
invariants state C1 and C2 at the state level:

* `[abandoned_after_finalize]`: `sc.abandoned (sc_state s) i → ∃ v,
  sc.finalized (sc_state s) i v` (C1's state form);
* `[participating_opened]`: `sc.participating (sc_state s) i →
  orch.opened os i s` (with `integrity_timing`, C2's state form).

`[bounded_concurrency_interval]` states one direction, "an active instance
is opened and not completed", which is what Lemma 5's bound needs; the
separate handlers over-approximate the paper's atomic ones
([PaperAlignment.md](PaperAlignment.md) §5.10). The glue's safety claims are
unchanged: the inputs add behaviours only through contract-legal
transitions.

### 4.2 What the composition discharges

Each of Chorus's caller conditions ([Bounds.md](Bounds.md) §6.4.6, "What
the Conductor's timed claims take from this leg") is a theorem about the
composed run ([Composed/Corollary4.lean](../Cadence/Composed/Corollary4.lean)):

| Chorus's condition | discharged from | theorem |
|---|---|---|
| C1: abandon only after finalizing | Algorithm 1, line 23 (`line:abandon`): the glue's invariant `[abandoned_after_finalize]` | `Composed.c1_slot` |
| C2: no start before `D − Δ` | `OrchestratorSafety.integrity_timing`, with `D s = start_time s + Δ` (a schedule tie, §6.2) and `clock_agrees` | `Composed.c2_slot` |
| participation by `t` | the Conductor opens by `t` (Recovery, or Proposition 15), and the glue's `on_open` row | `Composed.participating_by` |
| Δ-synchronized participation | Lemma 15 plus the `on_open` row; at δ = 0 exactly `d_tot = Δ` | `Composed.sync_slot` |

The Conductor's caller conditions, (R-tot) and (R-term) of §2.3, come from
`Chorus.chorusWithTotality`'s two fields through the same table read
backwards (`Composed.caller_totality`, `Composed.caller_termination`).

### 4.3 Corollary 4 as a theorem

`Composed.corollary4` (`Corollary4Claim`): for every composed run meeting
its timing model and every started slot `s`, the run's slot-`s` Chorus part
satisfies Δ-synchronized participation, C1 and C2. So
`Chorus.chorusWithTotality`'s `bounded_termination` and `totality`, and
`Chorus.chorusTemporal`'s `termination`, hold for it with no caller premise
left (`Composed.corollary4_bounded_termination`, `…_totality`,
`…_termination`). It needs Lemma 15 within Cadence
(`Composed.openings_sync`), and so comes after the Conductor's claims, as in
the paper: "one finished result applied to another".

## 5. F3 and C3: the tolerance at δ > 0

At δ > 0, local steps take time in six places:

* Chorus's totality latency, `max(Δ, d) + 2δ` (`Chorus.totality`, F3);
* the glue's `on_open` (participation lags the opening by δ);
* the glue's `on_finalize` (the completion lags the finalization by δ);
* `enter_window` (δ after the decision and readiness);
* `acs_propose` (δ after readiness);
* `open_slot` (δ after `max(entry, start time)`).

In the window induction each of Definition 6's four tolerances is the
previous one plus a δ-multiple. So the tolerance grows linearly in the
window number. GST can be arbitrarily late, so arbitrarily many windows can
pass before it, and no fixed `d_tot` bounds them all. Once the tolerance
exceeds Δ, Chorus's `bounded_termination`, whose `SyncParticipation` is
fixed at Δ, no longer applies at all. The paper's induction closes exactly
because "both equal `Δ = d_tot`" (the paragraph before Definition 6
(`def:window-synchronized`)).

**The claims are stated at δ = 0**, the paper's model: "validators' clocks
are synchronized, so they share one global timeline", and local computation
is instantaneous throughout the main body. It is the field `δ_zero` of
`ConductorSchedule`, used by the Conductor's and the composed claims only.
Chorus's and the MVBA's theorems stay δ-general, and the composed theorem
instantiates them at δ = 0, where `Lchorus` and `Ltot` are the paper's values
by `rfl` (`chorusWithTotality_ℓ_paper`, `chorusWithTotality_d_tot_paper`).
The tolerance-parametric lemmas are kept wherever they cost nothing
(Chorus's are), so a δ-robust statement remains possible. It would need a
new argument: re-synchronizing on absolute time (Algorithm 7, line 27
(`line:conductor-wait-for-open`)) resets the tolerance only in the smooth
regime of Proposition 18, and Propositions 14–16 use `d_tot`-totality before
it. That is new mathematics, not a formalization of the paper's. F3 records
the degradation at δ > 0. It is a finding about the model, not about the
paper, whose model is δ = 0.

## 6. The timing model

### 6.1 The clock

The run's clock is the system's clock, as for the MVBA and Chorus
([Bounds.md](Bounds.md) §6.2.1). The Conductor holds a state clock, `now`,
advanced by `tick`, and only its `open_slot` guard reads it.
`OrchestratorTemporal.clock_agrees` requires `r.clk n = now (r.at' n)` in
every admissible run (`ClockAgrees`). In the composed run the orchestrator's
state is the glue's `os`, so the composed timing model takes the same
equation. Time advances exactly at the Conductor's `tick` steps, which are
the system's clock steps. Chorus's phase timers and the MVBA's timers read
`r.clk` at the projected indices, so all of them read one clock. **No clock
is added to any model.** `tick`'s guard does not block a clock advance that
the run's `clock_unbounded` demands: `tick t` is enabled for every
`t ≥ now`.

### 6.2 One time theory, one Δ

The time theory is §6.2.2's of [Bounds.md](Bounds.md): a linearly ordered,
cancellative, additive monoid with an ordered addition (F27), Archimedean for
the witness. The classes let each module carry its own Δ
(`SlotConsensusWithTotality.Δ`, `ACSTemporal.Δ`), and the Conductor model's
`start_time` is the slot's deadline minus a Δ the model never names. The
paper's proofs use one Δ for all three. Proposition 13's entry step, for
instance, needs the ACS's `max(t, GST) + Δ` to fall within
`max(t, GST) + d_tot`. So the schedule ties them (F23):

* `TA.Δ = Δ` and `TA.ℓ = ℓ` (the ACS's constants are the system's);
* `D_eq`: Chorus's per-slot deadline, `FamilySchedule.D`, is the
  Conductor's starting time plus Δ;
* `SlotConsensusWithTotality.deadline = fs.D` (`rfl` in
  `Chorus.chorusWithTotality`).

### 6.3 Windows, slots, and the parameter assumptions as fields

The timed claims are stated at an instance where slots are numbers. The
Veil model keeps `slot` an abstract order, and
[Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean) fixes:

* `slot := ℕ` (`natSlotOrder`), where `s : ℕ` is the paper's slot `s + 1`,
  so the model's least slot is the paper's slot 1 and no subtraction is
  truncated;
* starting times `start₀ + s • τ`, the τ-spaced starting times of Appendix
  A.1 (`subsection:mcp-preliminaries`), with `0 < τ` (`StartTimes`; the
  model itself states only that starting times strictly increase,
  `[start_time_strict]`, and `[genesis_window]` starts its clock at slot
  1's starting time);
* window widths and readiness boundaries from the model's shift functions
  (§7, F21): `win_last s = s + (W − 1)` and `win_boundary s = s + p`, the
  first slot that readiness does not ask to be complete (F25)
  (`WindowShifts`);
* some slot has always not yet started (`StartsUnbounded`, F28), and every
  window has a successor (`WindowsUnbounded`, F30).

The schedule record, `ConductorSchedule`, extends Chorus's `FamilySchedule`
with `W p : ℕ`, `τ`, the ACS's `ℓ`, `start₀`, and these fields, each named
after its paper line:

* `assm_one`: `(p − 1) • τ + Φ_oc + ℓ ≤ W • τ`
* `assm_two`: `(p − 1) • τ + Φ_oc ≤ (W − 1) • τ`
* `assm_three`: `Δ < ℓ`
* `assm_four`: `d_tot + ℓ ≤ (p − 1) • τ`
* `δ_zero`: `δ = 0` (§5)
* `p_lt_W`, `τ_pos` and `D_eq` (§6.2)

`Φ_oc` and `d_tot` are not new constants. They are
`Lchorus Δ δ ℓ_MVBA + Ltot Δ δ Δ` and `Ltot Δ δ Δ`, the Chorus instance's
own data (`Φ_oc_eq_chorus`), so the four assumptions speak about the values
the composed theorem uses.

Two remarks:

* With `ℓ > Δ ≥ 0`, assumption (4) forces `p ≥ 2`
  (`ConductorSchedule.two_le_p`). The main body's `p ∈ {0, …, W − 1}`
  therefore only matters for the safety properties (P9's note,
  [PaperAlignment.md](PaperAlignment.md) §6).
* Assumptions (1)–(2) could be instantiated with a smaller `Φ_oc` (§9, K5's
  slack, and P5's tight `ℓ_chorus`). The claims keep the paper's values, as
  the Chorus claims do.

### 6.4 The rows

The Conductor's and the glue's honest actions have rows in the style of
[Bounds.md](Bounds.md) §6.4.2. All of them are local: none consumes a
message, since the Conductor's only cross-validator channel is the ACS,
whose timing comes in through `TA.Admissible`. The Conductor's are
`TimedRows` and (P-open) `OpenPunctual`
([Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean)); the glue's
are `Composed.GlueRows` ([Composed/Schedule.lean](../Cadence/Composed/Schedule.lean)):

| row | kind | gate | owed when |
|---|---|---|---|
| `open_slot i s …` | punctual timer, like Chorus's phase markers | `i` scheduled `s`, `start_time s ≤ clk` | always |
| `acs_propose i …` | `δ` | `ready_next i w`, `i` in `w` | always |
| `enter_window i …` | `δ` | ready, and **`i`'s own** ACS decision (F22) | always |
| `acs_decide w …` | `δ` (records the decided interval) | some correct validator has decided | always |
| glue `on_open i s` | `δ` | `orch.opened os i s` | always |
| glue `on_propose i s` | `δ` | opened, and `i` a proposer of `s` | always |
| glue `on_finalize i s v` | `δ` | `i` finalized `v` for `s`, and opened `s` | always |
| glue `append`, `record_skip` | `δ` | their guards | always (for Lemma 2) |

The inputs `tick`, `acs_step` and `sc_step` carry no row: the clock is the
run's, and the sub-protocols' steps are timed by their own `Admissible`.

## 7. Findings at the statement level

F1–F15 are the MVBA and Chorus legs' ([Bounds.md](Bounds.md) §6.4). These
continue the numbering. "Faithful implementation" means one that meets the
paper's module. Every finding below is closed; where the paper side needs a
change, the P-number names the finding on the authors' page
([PaperAlignment.md](PaperAlignment.md) §6). The findings' original wording,
with their proposals and closing records, is in
[History.md](History.md) § "Records moved out of the living documents (R33)".

* **F16: the paper's consumers need Totality's `d_tot` form, and Module 2
  states it eventually.** `OrchestratorTemporal.totality` is Module 2's
  ("eventually opens"). Proposition 14 and Corollary 4 use Lemma 15's "more
  specifically" form, `max(t, GST) + d_tot`. **Closed** by C4, the level
  `OrchestratorWithTotality` (§2.3). Paper side: P15.
* **F17: Totality and Recovery are stated unconditionally, but the
  Conductor has them only within Cadence.** A caller that never completes a
  slot leaves the Conductor in window 1. So the fields as Module 2 states
  them are false of every faithful Conductor, unless `Admissible` encodes the
  caller's behaviour. That is P13's pattern, one module up. Module 2's
  commented-out "assumed behaviour" block, which lists "complete only after
  opening" and "complete within `Φ_oc` of opening", would not repair it
  either. The proofs use the *conditional* completion guarantees (R-tot) and
  (R-term). An unconditional `Φ_oc` bound is itself a consequence of the
  Conductor's totality (Proposition 14), so a module assumption stating it
  would assume the conclusion. **Closed** by C5, the rely form (§2.3).
  Paper side: P15.
* **F18: a decided ACS set may hold several pairs of one validator.**
  Module 4's Validity: "`|set| ≥ 2f + 1`, and for every validator-slot pair
  `(p_i, s_i) ∈ set` such that `p_i` is a correct validator, `p_i` proposed
  slot `s_i`". That counts `2f + 1` distinct *pairs*. The median argument
  ("the decided vector contains at least `f + 1` pairs contributed by
  correct validators", before Proposition 7) and the model's stated bridge
  at `acs_decide` (justified by `lowerMedian_between_correct`, whose
  hypothesis is "at most `f` Byzantine-attributed entries") need at most `f`
  Byzantine *pairs*. Under the module as stated, a single Byzantine
  validator's `2f + 1` pairs are a valid decision. The median is then the
  adversary's choice, the next window can overlap the previous one, and the
  proofs of Integrity (Lemma 12 (`lemma:conductor-integrity`)) and
  Monotonicity (Lemma 13 (`lemma:conductor-monotonicity`)) through
  Proposition 8 (`prop:acs-fate-range`) fail. **The model's safety theorems
  are unaffected as theorems:** the bridge is a `require`, and they hold of
  the model. What fails is the bridge's justification, that it removes no
  behaviour of a correct ACS. Any ACS that collects one signed proposal per
  validator meets the stronger property. **Closed** by C6 (§3.4): the
  bridge's justification is a theorem, `Cadence.acs_median_bracket`. The
  `require` itself stays a stated bridge: the model computes no median, and
  cardinality is outside the solver's fragment. Paper side: P16.
* **F19: the ACS's `abandon` was outside the fragment the Conductor
  instantiates, and nothing framed it against `propose`.** Algorithm 7,
  line 45 (`line:acs-abandon`) could not be modelled, and Proposition 12
  could not be derived even in the weak form "the Conductor never abandons".
  **Closed** by C7 (§3.4): `enter_window` abandons the instance, and
  Proposition 12 is the invariant `[acs_abandoned_decided]`.
* **F20: Slot Consensus's inputs were outside the fragment the glue
  instantiates, and the inputs had no cross-frames.** The same gap as F19
  for Chorus: the glue could not drive Algorithm 1, line 17
  (`line:participate`), Algorithm 1, line 19 (`line:propose`) or Algorithm
  1, line 23 (`line:abandon`), and even if it could, C1 would not follow at
  the contract level. **Closed** by C8 (§4.1): the glue drives the three
  inputs, and C1 and C2 hold in state form (`[abandoned_after_finalize]`,
  `[participating_opened]`).
* **F21: the Conductor model left free what the timed claims fix.** Each
  freedom was sound for safety and made a timed claim false of the model:
  the decided interval's width was unconstrained; `acs_propose` kept only
  the lower bound of the `s*` rule; `acs_decide` bracketed the first slot
  from below only; `start_time` was only monotone, and `genesis_time` was
  not tied to slot 1's starting time. **Closed** in
  [Conductor.lean](../Cadence/Conductor.lean), each by a constraint the
  paper's protocol satisfies, so the model loses only runs the paper does
  not have:
  * `win_last` and `win_boundary` (Algorithm 7, line 52
    (`line:last-update`); Algorithm 7, line 23 (`line:ready-check`)):
    `acs_decide` records `[first, win_last first]` with boundary
    `win_boundary first` (Algorithm 7, lines 49–52
    (`line:open-foreach`–`line:last-update`)), and `[genesis_window]` makes
    window 1 the shifts of slot 1 (Algorithm 7, lines 31–34
    (`line:startup-foreach`–`line:startup-last`)). The paper's window is
    exactly that interval. The invariant `[win_bounds_shift]` states the
    width for every window;
  * the `s*` rule (Algorithm 7, lines 38–41
    (`line:ready-time`–`line:sstar-update`)) as three `require`s over
    `now`: beyond the window's last slot `l0`, not yet started, and every
    slot strictly between `l0` and `s*` already started. The paper's `s*`
    is `max(earliest not passed, l0 + 1)`, which meets all three; with
    strictly increasing starting times nothing else does;
  * the upper bracket: a second correct witness pair `(r2, s2)` with
    `first ≤ s2`. The paper's median is between two correct estimates
    (the paragraph before Algorithm 7 (`algorithm:conductor`)), proven from
    the contract by `Cadence.acs_median_bracket`;
  * `[start_time_strict]` (Appendix A.1 (`subsection:mcp-preliminaries`):
    `τ > 0`), and `[genesis_window]` starts the clock at slot 1's starting
    time (the proof of Proposition 16 (`prop:window-open-time`): "every
    correct validator enters window 1 at time `0 = T₁(1)`"). The spacing
    itself, `+ (s − 1)τ`, is the instance's (§6.3).

  One freedom stays: `open_slot` may fire late ("Timing relaxation" in the
  model's header). It is an over-approximation (the paper's punctual
  openings are among the model's runs), and the row (P-open) closes it in
  the timed premise ([PaperAlignment.md](PaperAlignment.md) §5.10).
* **F22: `enter_window` read the first correct decision anywhere, not the
  validator's own.** Algorithm 7, line 44 (`line:acs-decide`) fires on
  `p_i`'s own `decide`. As a δ-row, `enter_window` would have owed an entry
  before `p_i`'s ACS had decided, which the paper's protocol cannot do; the
  ACS's Δ-Totality would then go unused, and the bound would come out
  tighter than the paper's for the wrong reason. **Closed:** `enter_window`
  requires `acs.has_decided (acs_state w') i` (the F6 pattern of
  [Bounds.md](Bounds.md) §6.4.2).
* **F23: the classes allow several Δs, and the paper uses one.** **Closed**
  by schedule ties, not class edits (§6.2).
* **F24: a part that stops stepping has no timed run.** A contract's
  `TimedRun` steps along `trans` forever, and no class gives a stutter
  step. In a composed run most per-slot Chorus instances and per-window ACS
  instances eventually stop. Whether the ACS has an always-enabled step is
  unknown, and `admissible_exists` gives *some* admissible run from each
  initial state, not one with the inputs a consumer gives (the "vacuity
  does not compose" point of
  [CompositionContracts.md](CompositionContracts.md) §7). **Closed** with
  no class change, `TransitionSystemSafety` included: a stutter lift at the
  projection, and a per-part premise that applies once a correct validator
  has started the part ([PartProjection.lean](../Cadence/PartProjection.lean)).

  **How a part that stops is projected.** The composed run is relabelled
  (`liftRun`): a composed step counts as a step of the part whenever it is
  a transition of the part's own contract. That covers a real step, and also
  a step in which the part stays where it is, provided the contract's `trans`
  allows that stutter. The relabelled run has the same states, clock and
  `gst`, so [Timed.lean](../Cadence/Timed.lean)'s
  `Component.Projection.timed` applies to it unchanged, over the contract
  read as a one-label transition system (`contractRTS`). The part's run,
  `partRun p`, is then a `TimedRun` of exactly the class's `init` and
  `trans`. A part stepped only finitely often is scheduled exactly when its
  final state can stutter (`lift_scheduled_of_finite`). A part already
  scheduled stays scheduled (`lift_scheduled_of_scheduled`). The consumer
  needs no stutter action: its own steps that leave the part alone (a
  `tick`, say) serve as the part's stutters. This is the paper's picture: a
  silent instance whose time goes on passing.

  The stutter is tested against `trans`, not `step`, and that matters.
  Chorus has no internal step that stays enabled once every correct
  validator has abandoned the slot: its honest actions fire once, and its
  phase markers end. What it has is the input `abandon`, re-issued to a
  validator that has already abandoned. Chorus's `abandon` only sets
  `abandoned i` and forwards to the MVBA's, which only sets the same flag,
  so the re-issue leaves the state unchanged. A finished slot can therefore
  stutter in `trans`, and in an all-correct run nothing else would keep its
  projection going.

  **Meaning is kept.** Every shape a contract field uses ("at every index",
  "eventually", "by time `t`", "by `max(t, GST) + d`", and "from index `n`,
  by `max(clk n, GST) + d`") reads the same on `partRun p` and on the
  composed run, with the part's state read off each composed state
  (`partRun_forall_iff`, `partRun_eventually_iff`, `partRun_byTime_iff`,
  `partRun_byGstBound_iff`, `partRun_byGst_at`, `composed_byGst_of_cover`).
  With these, `ACSTemporal.termination`, `ACSTemporal.totality` and
  `SlotConsensusTemporal.termination` are restated wholly in the composed
  run's vocabulary and proven from the fields (`acs_termination_in`,
  `acs_totality_in`, `sc_termination_in`).

  **The premise, and the ACS's idle admissibility.** The consumer's
  `Admissible` asks for a part's run only once a correct validator has
  started the part (`AcsAdmissible` for window `w`'s ACS: once a correct
  validator has proposed to it; the slot form over "a correct validator
  participates in slot `s`"). The guard loses nothing. Every use of an ACS
  field at window `w` has a correct proposal there: Termination's
  antecedent says so outright, and Totality's antecedent, a correct
  decision, implies one by `integrity`. Likewise every use of a slot field
  has a correct participant.

  The Conductor cannot build its admissible runs from
  `ACSTemporal.admissible_exists`, whatever inputs it gives: that run has
  its own clock and `gst`, while a part's run carries the composed ones; its
  steps may be inputs, or proposals, that the Conductor's guards do not
  give; and it is one run per instance, while the Conductor interleaves
  infinitely many instances on one clock. The guard makes that unnecessary.
  The Conductor's idle run moves the clock and opens window 1's slots at
  their starting times. No correct validator ever proposes, since readiness
  needs a completion and the idle run gives none. The premise therefore
  holds vacuously, by the fragment's `init_proposed` alone
  (`Conductor.admissible_exists`, `Conductor.idleRun_sync`). **No new ACS
  field is needed.** The ACS only has to be a module whose admissible runs
  exist (the class already says so) and whose finished instances can
  stutter. That second condition is part of the premise: a composed run in
  which a started instance deadlocks has no admissible part run, so it is
  not admissible. Module 4 (`mod:acs`) gives the ACS an `abandon()` input,
  as Module 1 gives Chorus one. In Chorus and the MVBA, re-issuing that
  input is the stutter, and the ideal ACS stutters by construction. Whether
  a deadlock is plausible is the auditor's judgement, on the premises page.

  **Why not something else.** A stutter-closed run in the contracts
  (`TimedRun` stepping by `trans` or equality, or a reflexivity field in
  `TransitionSystemSafety`) would re-prove the MVBA and Chorus temporal
  instances, or re-solve all four families and be false of every Veil model
  without a no-op action. A contract field for an always-enabled step is
  false of Chorus in an all-correct run. A finite-run `Admissible` changes
  all four temporal classes. A consumer action that re-issues `abandon` adds
  an action the paper does not have, for stutters the lift gets anyway.
* **F25: the model's readiness boundary was a slot it asked to be
  complete, so the model covered only `p ≥ 1`.** The main body allows
  `p ∈ {0, …, W − 1}` (Algorithm 7 (`algorithm:conductor`)). Its readiness
  check, Algorithm 7, line 23 (`line:ready-check`), "return `k − j ≤ W − p`"
  over the opened slots `s_1 < … < s_k` with `s_1, …, s_j` complete, asks
  in window `ω` for every slot of the earlier windows and the window's
  first `p`; at `p = 0` for the earlier windows only, and in window 1 for
  nothing. The paper is precise here. The model's boundary was the
  window's `p`-th slot with readiness asking for the slots *up to* it, which
  excluded `p = 0`. **Closed:** the boundary is the window's `(p + 1)`-th
  slot (`win_boundary s = s + p`), readiness asks for the scheduled slots
  *strictly below* it, and `[shift_shape]`'s
  `s ≤ win_boundary s ≤ win_last s` is exactly `0 ≤ p ≤ W − 1`.
  `[bounded_tail]` reads the boundary with `<`: at `p ≥ 1` it states what
  it stated before, at `p = 0` the paper's content. The timed claims need
  `p ≥ 2` anyway (§6.3, P9's note).
* **F26: the ACS contract did not say that its inputs are accepted.**
  `ACSSafety` states `propose`'s and `abandon`'s effects and frames, but
  not that a correct validator can give them: a contract whose `propose`
  relation is empty meets every field. The Conductor's handlers
  `acs_propose` and `enter_window` give these inputs, so their rows are
  owed only where the ACS accepts them, and with an ACS that refuses a
  correct validator's proposal no later window is ever entered: Recovery
  fails, and Totality can fail when it refuses some validators only.
  Module 4 (`mod:acs`) has the two inputs in its interface, and an input is
  the caller's to give, so every ACS meets it. **Closed:** two first-order
  fields in rely form, as `MVBASafety.accept_enabled` states the MVBA's
  caller-driven input: `ACSTemporal.propose_enabled` (a correct validator
  that has neither abandoned nor proposed can propose any slot) and
  `ACSTemporal.abandon_enabled` (a correct validator can abandon). They sit
  in the upper class, `ACSTemporal`, which no Veil module instantiates:
  placed in `ACSSafety` and withheld from the solver, they slowed a
  Conductor sweep cell past its budget, an observation for the Veil fork
  ([TODO.md](TODO.md)). Only a consumer's timed claims need them, and the
  ideal ACS proves both (`Cadence.IdealAcs.acsTemporal`). Not a paper
  issue: Module 4's inputs are invocations by the caller, and the module
  formalism has no refusal ([PaperAlignment.md](PaperAlignment.md) §6.1).
* **F27: the claims' time needs ordered addition.** Over a `time` with a
  linear order and an additive monoid but no axiom tying the two,
  `max(t, GST) + Δ` is not monotone in `t`, an opening at `t` need not be
  before `t + Δ`, and Totality is unprovable. **Closed:** `TotalityClaim`
  and `RecoveryClaim` take `[IsOrderedAddMonoid time]`, the time theory of
  §6.2, which Chorus's and the MVBA's timed claims assume too;
  `BoundednessClaim`, a state property, needs no time theory. Not a paper
  issue: the paper's time is the real line.
* **F28: Totality needs a slot whose starting time has not passed.**
  `acs_propose`'s `s*` is the first slot beyond the window whose starting
  time has not passed (Algorithm 7, lines 38–41
  (`line:ready-time`–`line:sstar-update`)). If the starting times were
  bounded, then once the clock passed them all no correct validator could
  propose to the next ACS, and the claim would be false in such runs. The
  paper's slots are infinitely many and τ-spaced on the real line (Appendix
  A.1 (`subsection:mcp-preliminaries`)), so its `s*` always exists.
  **Closed:** a plain premise of `TotalityClaim` and `RecoveryClaim`,
  `StartsUnbounded th` ("whatever the time, some slot has not started
  yet"), used to pick `s*` (`Conductor.sstar_exists`) and, in Recovery, to
  find a window of the chain that starts after GST
  (`Conductor.exists_post_gst`). `StartTimes` does not imply it, even with
  an Archimedean time: with `start₀ = (−1, 0)` and `τ = (0, 1)` in the
  lexicographic monoid `{(a, b) : a < 0, or a = 0 ∧ b ≥ 0}`, every starting
  time stays below `(0, 0)`. Over an Archimedean time with `0 ≤ start₀` it
  does (`Conductor.startsUnbounded_of_startTimes`). Not a paper issue.
* **F29: Totality's fault-bound premise was unused.** The window induction
  never needs the decided interval's row, for which the fault bound gives
  correct median witnesses: a validator enters a window only after a
  correct validator has, and by then the interval is recorded. **Closed:**
  the premise is not in `TotalityClaim`. The decided interval's row and the
  fault bound are premises of `RecoveryClaim`, where Propositions 15 and 16
  need the interval to be recorded.
* **F30: Recovery needs every window to have a successor.** The model's
  window order is abstract (`TotalOrderWithMinimum window`), and a
  validator leaves a window only for its successor: `acs_propose` and
  `enter_window` read `win_ord.next`. At `window := Fin 1` every validator
  stays in window 1 for good, every other premise holds, and no slot past
  window 1 is ever opened, so the claim would be false. The paper's windows
  are the numbers `ω ∈ ℕ≥1`, with one ACS instance for each `ω ≥ 2`
  (Algorithm 7, line 12 (`line:acs-instances`)), and Proposition 15
  (`prop:enters-every-window`) inducts over them. **Closed:** a plain
  configuration premise, `WindowsUnbounded` ("every window has a
  successor"), of `RecoveryClaim` only; Totality and Boundedness speak only
  of windows a correct validator has entered. The claim stays generic in
  the window type, and the premise holds at `window := ℕ`
  (`Conductor.windowsUnbounded_nat`, used by `Conductor.conductorFullNat`).
  Not a paper issue.
* **F31: censorship resistance's timed premise ties with the deadline.**
  The paper's proof that Algorithm 1 (`algorithm:cadence`) meets
  Definition 3 (`def:censorship-resistance`), in Appendix B.3
  (`subsection:correctness_cadence`), has a correct proposer open its slot
  and propose at its starting time `D − Δ ≥ GST`, and reads Chorus's
  proposal inclusion off Proposition 3 (`prop:honest-positive-entry`): every
  correct validator "receives and validates its assigned chunk under
  `root_P` by the deadline". In the model the chunk arrives by
  `max(D − Δ, GST) + Δ = D` and is recorded at `δ = 0` by `D`, while the
  deadline marker, punctual, also fires at `D`. Once it has fired,
  recording is closed, so `Chorus.within_proposal_recorded` needs the strict
  `< D`. That is the tie [Bounds.md](Bounds.md) §6.4.2 ("What
  `s.deadline − Δ ≥ GST` becomes") anticipated. No choice of `𝓡` removes
  it, since the proposal is always made exactly `Δ` before the deadline. The
  paper resolves the tie in the chunk's favour without saying so.
  **Closed** by a premise (Lars's decision): (P-incl) `DeadlineInclusive`,
  a standalone premise of Chorus's timing model
  ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)): a chunk a
  correct validator holds at a clock at or before `D` is recorded. It is not
  part of `SyncAtMvba`, so no other claim takes it; the Chorus witness meets
  it (`Chorus.Witness.deadlineInclusive`). The milestone is
  `Chorus.within_proposal_recorded_incl`
  ([Chorus/Inclusion.lean](../Cadence/Chorus/Inclusion.lean)), and
  censorship resistance is proven (`Composed.censorship`). The proposer tie
  is definitional: the claim's glue configuration takes Chorus's proposer
  set for every slot. What stays a premise is a well-encoded root for the
  proposer. Paper side: P19.

## 8. Premises and non-vacuity

### 8.1 The ledger

The premises have their one home on the premises page:
[Premises.md](Premises.md) §0 (the composed claims) and §9 (the
Conductor's own), each line with its role, use, plausibility and witness.

### 8.2 The witness

[Composed/Witness.lean](../Cadence/Composed/Witness.lean): one model of the
composed system meets every premise of the four composed claims at once,
and the orchestrator's part of it every premise of the Conductor's three
(`Composed.Witness.*_premises_satisfiable`; the run in plain words is
[Premises.md](Premises.md) §0.5). The model: `Fin 4` with validator 3
Byzantine and silent, one proposer, `Δ = τ = 1`, `δ = 0`, the MVBA
witness's schedule with the Chorus witness's `Δ_sync`, the ideal ACS,
`p = 4`, `W = p + Φ_oc + ℓ_ACS`, and a periodic run in which every slot
takes the fast path. The constants' values are the ones
[Composed/Witness.lean](../Cadence/Composed/Witness.lean) pins. The four
parameter assumptions hold by `decide`. How it is built:

* **The period is one clock reading.** The run is built from one block of
  steps, checked once for every clock reading `t` (`Composed.Witness.gstep`,
  through `Cadence.plateauRun`, the generic periodic extension): the block
  holds slot `t`'s start, slot `t − 1`'s fast path, slots `t − 2` and
  `t − 3`'s arm markers, and, once per window, the next window's ACS and
  entry. So every slot repeats the one before it shifted by `τ`, and every
  window repeats the first shifted by `Wτ` and `W` slots. A position whose
  slot or window does not exist yet is the Conductor's `tick` in place.
* **Every row holds at the end of a clock reading**
  (`Cadence.bufferedFairFamily_of_ends`): each handler fires in the
  reading its gate opens at, so no gate is open, or nothing it covers is
  enabled, when the clock moves. This is what makes `δ = 0` rows
  satisfiable.
* **A slot stutters by its `participate` re-issued until validator 0 has
  abandoned it, by its `abandon` after** (F24's re-issued `abandon` is the
  second half). Its initial state cannot stutter
  (`Composed.Witness.no_stutter_init`), so its part starts at its first
  step; every slot's part is then one labelled run with the clock shifted
  by the slot's number (`Composed.Witness.srun`). The orchestrator stutters
  by its `tick` in place, the ideal ACS by `trans_refl`, so both parts are
  stepped at every index.
* **Validator 3 sends nothing**, not even the Chorus witness's MVBA
  `Pre-Prepare`: the composed clock moves on the Conductor's `tick`, and the
  re-issued `abandon` keeps each slot's MVBA stepped.
* **One model at fixed types.** The theorems quantify over the claims'
  configuration and run, at `Fin 4` and `ℕ`, rather than over the types
  too; one model is all consistency asks.
* **The Conductor's own claims are covered too**
  (`Composed.Witness.conductor_premises_satisfiable`): their caller
  conditions, (R-tot) and (R-term), hold on the orchestrator's part as
  theorems of the composition (`Composed.caller_totality`,
  `Composed.caller_termination`).

## 9. What is proven where, by stage

The leg was built in stages K0–K8; source headers name the stage they
belong to. The plan, the per-stage records and the sizing are in
[History.md](History.md) § "Records moved out of the living documents
(R33)". Every theorem below is axiom-pinned at its own site and indexed in
[Cadence.lean](../Cadence.lean).

* **K0: the part projection (F24).**
  [PartProjection.lean](../Cadence/PartProjection.lean): `contractRTS`,
  `stutterSys`, `stutterComp`, `liftRun`, the two scheduling lemmas,
  `partRun` and its transfer lemmas.
* **K1: the composition, untimed.** C6, C7 and C8 in
  [Interfaces.lean](../Cadence/Interfaces.lean) with the cross-frames; the
  glue's three input handlers and two invariants
  ([Cadence.lean](../Cadence/Cadence.lean), §4.1); `enter_window` reading
  its own decision and abandoning the ACS
  ([Conductor.lean](../Cadence/Conductor.lean), F19, F22); the median
  bracket ([AcsMedian.lean](../Cadence/AcsMedian.lean), F18).
* **K2: the Conductor's timing completion (F21, F25).** The shift
  functions, the `s*` rule, the upper bracket and the starting-time facts
  in [Conductor.lean](../Cadence/Conductor.lean).
* **K3: the statements.** C4 and C5 in
  [Interfaces.lean](../Cadence/Interfaces.lean); the timing model,
  `ConductorSchedule`, the rows and the three claims in
  [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean); the ideal
  ACS in [Conductor/IdealAcs.lean](../Cadence/Conductor/IdealAcs.lean); the
  ACS's input-enabledness (F26).
* **K4: Boundedness and Totality.**
  [Conductor/Boundedness.lean](../Cadence/Conductor/Boundedness.lean) and
  [Conductor/Induction.lean](../Cadence/Conductor/Induction.lean), each item
  at the paper's deadline:

  | the paper | Lean | deadline |
  |---|---|---|
  | Proposition 11 (`prop:open-count-window`), interval form | `Conductor.opened_above` | — (a state fact) |
  | Lemma 14 (`lem:boundedness`) | `Conductor.boundedness` (`BoundednessClaim`) | `2W − p` opened, uncompleted slots, exactly |
  | Definition 6 (`def:window-synchronized`) | `EntrySync`, `OpenSync`, `CompSync`, `PropSync`, `WindowSynchronized` | — |
  | Proposition 12 (`prop:acs-no-premature-abandonment`) | the model's `[acs_abandoned_decided]`, consumed as the ACS's `NoPrematureAbandon` | — |
  | Proposition 13 (`prop:window-synchronization`) | `Conductor.window_synchronized` | `max(t, GST) + Δ`, all four conditions |
  | Corollary 1 (`cor:entry-synchronization`) | `Conductor.entry_sync` | `max(t, GST) + Δ` |
  | Corollary 2 (`cor:proposal-synchronization`) | `Conductor.prop_sync` | `max(t, GST) + Δ` |
  | Lemma 15 (`lemma:conductor-totality`) | `Conductor.open_sync`, and `Conductor.totality` (`TotalityClaim`) | `max(t, GST) + d_tot`, `d_tot = Δ` |
  | Corollary 3 (`cor:completion-totality`) | `Conductor.comp_sync` | `max(t, GST) + Δ` |

  How the proof goes:
  * **the induction runs over first slots, not windows**
    (`Conductor.window_induction`). The window order is abstract and not
    known to be well-founded. A window is named by its first slot, and the
    entry into a window depends only on smaller slots: its predecessor's
    entry, the completions below the predecessor's boundary, and the
    proposals to its ACS. The paper's four per-window steps are the lemmas
    `entry_step`, `open_step` and `prop_step`, with (R-tot) for the
    completions (`comp_of_open`);
  * **Boundedness needs no successor window in the order**: the one window
    above `s`'s that can hold an opened slot is found from that slot's own
    window, through its entered predecessor (`Conductor.entered_pred`, a
    plain-Lean reachability induction, since the model records the
    predecessor only in a guard);
  * the ACS is consumed through its contract only: Δ-Totality on the
    window's part of the run (`Cadence.acs_totality_in` under
    `AcsAdmissible`), `integrity`, `propose_enabled` and `abandon_enabled`.
    Chorus enters only through (R-tot);
  * the two rows are consumed in their diagonal form
    (`BufferedFairFamily.diag`), at `δ = 0`: a gate open from an index
    whose clock is within the deadline fires its row by that deadline.
* **K5: Recovery.**
  [Conductor/Recovery.lean](../Cadence/Conductor/Recovery.lean), each item
  at the paper's deadline (`d_tot = Δ` at `δ = 0`):

  | the paper | Lean | deadline |
  |---|---|---|
  | Proposition 14 (`prop:conductor-open-to-complete`) | `Conductor.open_to_complete` | `max(t, GST) + d_tot + ℓ_chorus`, for every correct validator |
  | Proposition 15 (`prop:enters-every-window`) | `Conductor.enters_every_window` (and `window_entered_by`, by some time) | eventually, for window 1 and each of its successors |
  | Proposition 16 (`prop:window-open-time`) | `Conductor.window_open_time` | `max(T₁(ω), GST) + d_tot + ℓ` |
  | Proposition 17 (`prop:window-progression`) | `Conductor.window_progression` | (1) the next window's first slot is `slot(ω, W) + 1`; (2) entered by `T₁(ω + 1)` |
  | Proposition 18 (`prop:smooth-windows`) | `Conductor.smooth_windows` | every slot of a later window opened by its starting time |
  | Proposition 19 (`prop:first-post-gst-window-time`) | `Conductor.first_post_gst_window_time` | `T₁(ω) ≤ GST + Wτ` |
  | Lemma 16 (`lemma:conductor-recovery`) | `Conductor.recovery` (`RecoveryClaim`) | `𝓡 = 2Wτ` |
  | (slack) | `Conductor.recovery_sharp` | `𝓡 = (W + p − 1)τ` |

  How the proof goes:
  * **one engine.** `succ_window`: once every correct validator has entered
    a window by `X`, every correct validator proposes to the next ACS by
    `max(X, T, GST) + ℓ_chorus`, where `T` bounds the starting times below
    the readiness boundary, and enters the next window `ℓ` later.
    Propositions 15–19 instantiate it. The paper's case splits on an early
    correct decision or entry, in Propositions 15, 16 and 17 point 2, are
    not needed: once every correct validator has proposed, the ACS's
    `ℓ`-termination applies whatever happened before;
  * **Proposition 16 needs neither Proposition 15 nor assumption (3).** It
    is stated for a window whose interval is recorded. The median's lower
    bracket, a correct proposal at or below the first slot, was made by
    `T₁(ω)`, since the `s*` rule never picks a slot that has started.
    Corollaries 1–3 then make every correct validator ready and proposing
    by `max(T₁(ω), GST) + Δ`;
  * **Proposition 15 and the windows' existence are one induction** along
    the chain of successors (`WinSucc`), which `WindowsUnbounded` makes
    infinite (F30). The smallest post-GST window is found on it
    (`exists_post_gst`): the chain's first slots grow (`chain_bounds`), and
    `StartsUnbounded` puts one past GST;
  * **window 1 is treated apart.** The paper's time starts at `0 = T₁(1)`
    with `GST ≥ 0`. A run here starts at slot 1's starting time, and GST is
    arbitrary, so window 1 may be post-GST with `T₁(1) > GST + Wτ`.
    `recovery` uses that window 1 is entered at its starting time, so its
    slots are opened at theirs, and Proposition 19 is stated for `ω > 1` (a
    predecessor that starts before GST). Not a paper issue: at
    `GST ≥ T₁(1)` the cases agree;
  * **the decided interval's row is fed one correct pair**, used as both
    median witnesses (`correct_pair`, from `validity_quantitative` and the
    fault bound). The model records any first slot between two correct
    pairs, and the timing argument reads only those brackets
    (`recorded_bracket`), so it holds at the median as well;
  * **the ACS through its contract only:** `TA.Admissible` of the window's
    part (`AcsAdmissible`), its ℓ-Termination
    (`Cadence.acs_termination_in`), Δ-Totality through Lemma 15's
    corollaries, Validity's two halves and its input-enabledness. Chorus
    enters only through (R-tot) and (R-term), at `d_tot` and `ℓ_chorus`.
    `0 ≤ ℓ_chorus` is derived from the MVBA schedule
    (`ConductorSchedule.ℓchorus_nonneg`).

  **The schedule arithmetic: slack (P18), no shortfall.** The proof needs:
  * `(p − 1)τ + ℓ_chorus + ℓ ≤ Wτ` (Proposition 17, both points), not (1)
    with `Φ_oc`;
  * `(p − 1)τ + ℓ_chorus ≤ (W − 1)τ` (Proposition 19 only), not (2) with
    `Φ_oc`;
  * `0 < ℓ`, not (3)'s `Δ < ℓ`;
  * (4) as stated (Propositions 18 and 19).

  Where every correct validator has already opened the slots, Chorus's
  termination applies directly, and Proposition 14's `d_tot` is not paid.
  Proposition 17 point 1 needs the proposals only by `T₁(ω + 1)`, which (1)
  implies. `𝓡 = (W + p − 1)τ ≤ 2Wτ` suffices, because the smallest post-GST
  window is itself entered by its `T_p` (`recovery_sharp`). With P5's tight
  `ℓ_chorus = 4Δ + ℓ_MVBA` (F4) as well, the `Φ_oc` of (1)–(2) could shrink
  from the paper's `6Δ + ℓ_MVBA` to `4Δ + ℓ_MVBA`. The claims keep the
  paper's values, as the Chorus claims do, and P18 reports the slack to the
  authors. Every premise is used ([Premises.md](Premises.md) §9, "Used
  in"); the one weakly used is assumption (3), for `0 < ℓ` only.
* **K6: the contract instances.**
  [Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean):

  | field | value | proven by |
  |---|---|---|
  | `Admissible` | `Conductor.Admissible`: `contractRun` of a labelled run meeting `Sync` | — (a definition: the claims' run premises by name) |
  | `admissible_exists` | | `Conductor.admissible_exists`, the idle run (`Conductor.idleRun_sync`) |
  | `clock_agrees` | | `ClockAgrees`, a conjunct of `Sync` |
  | `caller_d_tot`, `caller_ℓ` | `d_tot`, `ℓ_chorus` | `rfl` (`Conductor.conductorTemporal_caller`) |
  | `totality` | | `Conductor.totality` (Lemma 15) |
  | `bound`, `boundedness` | `2W − p` | `Conductor.boundedness` (Lemma 14); `rfl` (`Conductor.conductorTemporal_bound`) |
  | `recovery_time`, `recovery` | `2Wτ` | `Conductor.recovery` (Lemma 16); `rfl` (`Conductor.conductorTemporal_recovery_time`) |
  | `OrchestratorWithTotality.d_tot`, `.totality` | `d_tot`, the paper's `Δ` at `δ = 0` | `Conductor.totality`; `rfl` (`Conductor.conductorWithTotality_d_tot`), and `Conductor.conductorWithTotality_d_tot_paper` by rewriting |

  `Conductor.conductorFull` is the join, and
  `Conductor.conductorFull_toSafety` hands back
  `Conductor.orchestratorSafety th` by `rfl`. The class carries the paper's
  values; the sharper `Conductor.recovery_sharp` stays a separate theorem.
  * **the instance's hypotheses are the claims' configuration premises**,
    by name (`StartTimes`, `WindowShifts`, `StartsUnbounded`,
    `WindowsUnbounded`, the ACS's `Δ`, `ℓ` and fault bound); `Admissible`
    is the run premises only, so that `admissible_exists` needs no
    configuration it cannot build;
  * **the idle run opens window 1's slots**: (P-open) obliges every
    scheduled slot to open at its starting time, so the run proceeds in
    blocks, one per slot: a `tick` to the slot's starting time, then one
    step per validator, which opens the slot there if the validator is
    correct and the slot lies in window 1, and is a `tick` in place
    otherwise. Its clock is unbounded because the starting times are
    (`StartsUnbounded`);
  * **the rows stay shut because `p ≥ 2`**, which assumption (4) implies
    (`ConductorSchedule.two_le_p`). Window 1's first slot then lies below
    its readiness boundary (`Conductor.genesis_boundary_pos`) and is never
    completed, so no correct validator is ready;
  * **two configuration premises are discharged at the system's types**:
    `WindowsUnbounded` at `window := ℕ` (`Conductor.windowsUnbounded_nat`),
    and `StartsUnbounded` from `StartTimes` over an Archimedean time once
    `0 ≤ start₀` (`Conductor.startsUnbounded_of_startTimes`).
    `Conductor.conductorFullNat` is the full contract with both
    discharged;
  * **[System.lean](../Cadence/System.lean) keeps the fragments.** Its
    theorem is safety, generic in the slot order and the time; the full
    instance would narrow it to `slot := ℕ`, an ordered time, a schedule
    and an `ACSTemporal`, and add nothing safety needs.
* **K7: the composed timed claims.** [Composed/](../Cadence/Composed/Schedule.lean)
  and [Chorus/Inclusion.lean](../Cadence/Chorus/Inclusion.lean):

  | the paper | Lean | at |
  |---|---|---|
  | the composed timed run | `Composed.sysRTS`, `Composed.TSysRun`, `Composed.orchComponent`, `Composed.slotComponent`, `Composed.GlueRows`, `Composed.SysSync` | — (definitions: the claims' run premises by name) |
  | C1, C2, participation, Δ-synchronized participation (Chorus's caller conditions) | `Composed.c1_slot`, `Composed.c2_slot`, `Composed.participating_by`, `Composed.sync_slot` | `D = start + Δ`; `Δ` |
  | (R-tot), (R-term) (the Conductor's caller conditions) | `Composed.caller_totality`, `Composed.caller_termination` | `d_tot = Δ`, `ℓ_chorus` |
  | Lemma 15 (`lemma:conductor-totality`) within Cadence | `Composed.openings_sync` | `Δ` |
  | Corollary 4 (`cor:chorus-correctness-within-cadence`) | `Composed.corollary4` (`Corollary4Claim`); `Composed.corollary4_bounded_termination`, `…_totality`, `…_termination` | `5Δ + ℓ_MVBA`, `Δ` |
  | Lemma 5 (`lemma:cadence-bounded-concurrency`) | `Composed.boundedConcurrency` (`BoundedConcurrencyClaim`) | `𝓑 = 2W − p` |
  | Lemma 16 (`lemma:conductor-recovery`) within Cadence | `Composed.recovery_in`, `Composed.recovery_sharp_in` | `2Wτ`; `(W + p − 1)τ` |
  | `𝓡`-Liveness (Definition 2 (`def:liveness`), Lemma 2 (`lemma:cadence-liveness`)) | `Composed.liveness`, `Composed.liveness_sharp` (`LivenessClaim`) | `2Wτ`; `(W + p − 1)τ` |
  | Proposition 3 (`prop:honest-positive-entry`), timed | `Chorus.within_proposal_recorded_incl` | by the deadline, under (P-incl) |
  | `𝓡`-Censorship resistance (Definition 3 (`def:censorship-resistance`)) | `Composed.censorship`, `Composed.censorship_sharp` (`CensorshipClaim`) | `2Wτ`; `(W + p − 1)τ` |

  * **both parts are stutter-lifted**, the orchestrator's as well as each
    slot's, so both premises read "`T.Admissible (partRun p)`" with the
    instance's own `Admissible` (`Conductor.Admissible`,
    `Chorus.Admissible`), restated nowhere;
  * **one fault pattern, Chorus's** (`fmF`): the Conductor, the ACS and the
    glue are stated at it, so no transport like
    [System.lean](../Cadence/System.lean)'s `hbyz` is needed;
  * **the Conductor is consumed through its lemmas** (`Conductor.totality`,
    `Conductor.recovery`), not through the contract instance: the instance
    takes Recovery's configuration premises, and Corollary 4 needs only
    Totality's. Chorus is consumed through its contract instance
    (`Chorus.chorusWithTotality`, `Chorus.chorusTemporal`), whose fields
    are exactly the claims used;
  * **Corollary 4's Termination needs no Conductor premise**: its one
    caller condition, C1, is the glue's invariant;
  * **Liveness concludes `V.slot = s`** as Definition 2 asks, from the
    contract's `slot_safety` through the glue (`Composed.inv_appended_slot`);
  * **censorship resistance** needs (P-incl) (F31), that a proposer has not
    abandoned before proposing (`Chorus.committed_post_deadline`: a
    finalization postdates the deadline), and that a correct proposer's
    proposals are its own inputs (`Composed.run_proposed_of`, from the
    contract's frames), for the root's well-encodedness.

  The premises ([Premises.md](Premises.md) §0, each with its "Used in")
  are the union of the parts' environment premises (the glue's rows, the
  Conductor's `Sync` on its part, Chorus's `Admissible` on every started
  slot's part, the configuration, the assumed ACS), with every caller
  condition discharged; censorship resistance adds (P-incl) on every
  started slot and a well-encoded root.
* **K8: non-vacuity.** The composed witness (§8.2) and the premise ledger
  ([Premises.md](Premises.md) §0, §0.5, §9). A finished slot stutters by
  its re-issued `abandon`, the ideal ACS by construction, and each part's
  `Admissible` accepts the stutters.
