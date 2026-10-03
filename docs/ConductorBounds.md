# Conductor bounds — the kick-off record

*Written 2026-10-02 (session R22), before any Lean. Nothing here is proven
or modelled: it is the plan for the Conductor's timed claims and for the
composition that closes the Cadence loop. [Bounds.md](Bounds.md) §6.4 (the
Chorus leg) set the shape, and §6.2 (the MVBA leg) the timing machinery
this leg reuses. Decisions are recorded with their reasons. Those marked
**open** are for Lars to take.*

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
unconditionally in the composed system.

**What the development has today.** The contract states the three properties
as fields of `OrchestratorTemporal`
([Interfaces.lean](../Cadence/Interfaces.lean)), and nothing instantiates
them. The interval form of boundedness is proven (`safety [bounded_tail]` in
[Conductor.lean](../Cadence/Conductor.lean)). The safety half of the
composition is proven (`Cadence.system_positional_log_safety`,
[System.lean](../Cadence/System.lean)), but since S1 its Chorus is inert:
the glue cannot drive Chorus's `participate`, `propose` and `abandon` inputs
([CompositionContracts.md](CompositionContracts.md) §5).

**What the timed claims would assume.** The same timing model as the MVBA and
Chorus claims: one clock, one time theory and one Δ for the whole system.
Messages between correct validators arrive within Δ after GST, and local
steps are instantaneous (δ = 0, recommended in §5). Timers fire on time.
They would also assume that the ACS meets its module (Module 4 (`mod:acs`)),
since the target leaves the ACS unspecified (§3), and that the four parameter
assumptions of Algorithm 7 (`algorithm:conductor`) hold. Every condition the
Conductor needs from its caller, and every condition Chorus needs from the
Conductor, is discharged by the composition. None is left as a premise of
the composed claims.

**The three questions for Lars.**

1. **The ACS (§3).** The target has no concrete ACS: the supplement's
   section is empty. **Recommendation (open):** keep the ACS as a contract,
   so the timed claims are relative to an `ACSTemporal` instance and the ACS
   is a named assumed module, as the MVBA was before §6.2. Exhibit a
   plain-Lean ideal ACS only to show that the premises are jointly
   satisfiable.
2. **How "within Cadence" enters the contract (§2.3).** **Recommendation
   (open):** state the Conductor's Totality and Recovery in the rely form
   already used for Chorus and the MVBA. The conditions the paper takes from
   Cadence become antecedents over the orchestrator's own observables (C5),
   and a Conductor-specific level states the `d_tot` form that Corollary 4
   consumes (C4).
3. **δ (§5, C3 from the Chorus leg).** **Recommendation (open):** prove the
   Conductor's and the composed claims at δ = 0, the paper's instantaneous
   local computation, stated as a schedule field. Chorus's and the MVBA's
   theorems keep their δ-general forms.

**Nine findings about statements (§7, F16–F24) and three for the paper's
authors (P15–P17, [PaperAlignment.md](PaperAlignment.md) §6).** One of them
reaches the existing safety claims. **F18 / P16:** Module 4's Validity
bounds the size of the decided set but not the number of pairs per
validator. The median argument behind Proposition 7 (`prop:acs-nonoverlap`),
and the model's stated bridge at `acs_decide`, need at most `f`
Byzantine-attributed pairs. With the module as stated, a decided set could
consist entirely of one Byzantine validator's pairs. The fix is one
first-order field, and every natural ACS satisfies it. The other findings
concern the timed statements and the model's timing freedoms.

**Decisions in one place.**

* ACS: **(b), a contract (open)**, plus an ideal instance for non-vacuity
  (§3.4).
* C4 (an `OrchestratorWithTotality` level) and C5 (rely antecedents for
  Totality and Recovery): **recommended (open), jointly** (§2.3).
* C6 (one pair per validator in a decided ACS set): **recommended**, and
  independent of the timed leg, because it repairs the justification of a
  safety bridge (F18).
* C7 (the ACS's `abandon` moves into `ACSSafety`) and C8 (Slot Consensus's
  inputs move into `SlotConsensusSafety`), each with the cross-frames:
  **recommended**. They are the composition leg's prerequisites (§4, F19,
  F20).
* δ = 0 for the Conductor's and the composed claims: **recommended (open)**
  (§5).
* The clock is the run's. The Conductor's `now` equals it through
  `OrchestratorTemporal.clock_agrees`, so `tick` is the system's clock step
  (§6.1).
* One schedule record extends Chorus's `FamilySchedule` with the windows and
  the four parameter assumptions as fields, in the `δ_le_Δ` style (§6.3).
* Order: the glue's untimed composition edit first (K1), then the model's
  timing completion (K2), then the timed Conductor claims (K3–K6), then
  Corollary 4 and the composed claims (K7), then non-vacuity (K8) (§9).

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

### 2.2 The contract today

`OrchestratorTemporal` ([Interfaces.lean](../Cadence/Interfaces.lean)) has
`Admissible`, `admissible_exists`, `clock_agrees`, an *eventual*
`totality`, `bound` with `boundedness` (a state-level count), and
`recovery_time` with `recovery`. The Conductor proves the fragment,
`Conductor.orchestratorSafety`
([Composition.lean](../Cadence/Composition.lean)). The paper's chain needs
three things the contract does not have:

* the `d_tot` form of Totality, which Proposition 14 and Corollary 4 consume
  (F16);
* a way to say "within Cadence" (F17);
* the ACS's abandonment, and a one-pair-per-validator decided set, at the
  fragment the Conductor instantiates (F18, F19).

### 2.3 How "within Cadence" enters: C4 and C5

The Conductor's Totality and Recovery are false for the Conductor alone. A
caller that never completes a slot leaves every correct validator in window
1 forever. Two forms are faithful to "when run within Cadence":

* **(i) The rely form (C5).** Totality and Recovery take, as antecedents over
  the orchestrator's own observables (`opened`, `completed`), the two
  conditions the paper's proof takes from Cadence. Both are conditional,
  exactly as Chorus's fields are:
  * **(R-tot)** for every slot `s`: if the openings of `s` are
    `d`-synchronized (each opening at `t` is followed by every correct
    validator's by `max(t, GST) + d`), then the completions of `s` are
    `d_tot`-total;
  * **(R-term)** for every slot `s`: if the openings of `s` are
    `d`-synchronized and every correct validator opens `s` by `t`, every
    correct validator completes `s` by `max(t, GST) + ℓ_chorus`;
  * and "a correct validator completes only slots it has opened", which the
    fragment already gives through the glue's `[delivered_opened]`.

  `Admissible` then stays what it is for the MVBA and Chorus: the scheduler,
  the network and the timers, nothing about the caller. The composition
  discharges (R-tot) and (R-term) from `Chorus.chorusWithTotality`'s
  `totality` and `bounded_termination` through the glue (open ↦ participate,
  finalize ↦ complete). Non-circularity is then visible in the types: each
  side is a conditional statement about one slot, and the window induction
  lives inside the Conductor's proof.
* **(ii) A "within Cadence" `Admissible`.** `Admissible r` says that `r` is
  the orchestrator part of an admissible composed run. This is literally
  the paper's phrase. But it puts the caller's behaviour into `Admissible`,
  which the rely form was adopted to avoid ([Bounds.md](Bounds.md) §6.4.1,
  "The class change"). It also makes the Conductor's instance depend on
  Chorus's model.

**C4.** Module 2's Totality is eventual, so a `d_tot` field belongs at a
Conductor-specific level, as `SlotConsensusWithTotality` holds Chorus's.
`OrchestratorWithTotality` would have `Δ`, `d_tot` and the bounded
`totality` (in rely form under (i)). The instance pins `d_tot` by `rfl` to
the Chorus instance's `d_tot`. Corollary 4 and Proposition 14 consume it.

**Recommendation (open): (i) with C4**, in one
[Interfaces.lean](../Cadence/Interfaces.lean) edit. No Veil module
instantiates `OrchestratorTemporal`, so the edit is a warm rebuild of the
Chorus family and re-solves nothing. The paper side of this is P15.

## 3. The ACS question

### 3.1 What the Conductor's claims take from the ACS

| field of `ACSTemporal` / `ACSSafety` | timed? | used in |
|---|---|---|
| `agreement`, `validity_genuine`, `integrity` | no | safety (proven today), and Proposition 16's "a correct proposer proposed by `T₁(ω)`" |
| `validity_quantitative` with `fault_bound` | no (cardinality) | the median brackets: Propositions 7, 16, 17, 19 |
| `abandon`, `abandoned` and `NoPrematureAbandon` | no | the antecedent of both timed fields; Proposition 12 discharges it |
| `SyncProposals` (Δ-synchronized proposals) | yes | the antecedent of both timed fields; Corollary 2 discharges it |
| `termination` with `ℓ` | **yes** | Propositions 15, 16 and 17 (case 2) |
| `totality` with `Δ` | **yes** | Proposition 13 (entry), Propositions 15 and 17 (case 1) |
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

### 3.3 The options

**(a) Instantiate the ACS concretely, from the MVBA.** The standard
reduction: each validator broadcasts its signed proposal; once it holds
`2f + 1` signed proposals from distinct validators, it proposes that set to
an MVBA whose validity predicate checks the signatures; the MVBA's decision
is the ACS's. That would need:

* a fourth model or a plain-Lean wrapper over `Mvba`: the dissemination
  round, the candidate set as the MVBA's value, and the validity predicate;
* `ACSSafety` from the MVBA's agreement, external validity and integrity;
* Termination with `ℓ_ACS = Δ + ℓ_MVBA`;
* Δ-Totality, which `MVBATemporal` does not state. It would come from the
  decision handoff the supplement describes (a decided party's `CommitQC`,
  transferred and accepted; [Bounds.md](Bounds.md) §6.4.2, "The decision
  handoff (C15)"), now owed by the ACS layer instead of by Chorus.

The target specifies none of this. Every choice (the candidate-set
predicate, signatures, the one-proposal-per-validator rule, the transfer)
would be ours. The resulting claim would be about *an* ACS, not the paper's,
which is the hybrid the single-target rule forbids. **Not recommended at
this target.** It becomes the faithful option once the paper specifies the
ACS. The supplement's MVBA is then the natural base, and its timed instance
`Mvba.mvbaTemporal` already exists.

**(b) Keep the ACS as a contract.** The timed claims are stated for an
arbitrary `[ACSTemporal …]` at the fragment the Conductor instantiates, with
the per-window projections as `T.Admissible` runs. Exactly as the MVBA was
consumed before §6.2 closed it, the ACS is then **an assumed module, named
in the trust statement**. This is exactly what Algorithm 7 says ("Uses: ACS")
and what Theorem 2's proof does. The cost is the class edits C6 and C7, and
two consequences for non-vacuity (§8.2): an ideal instance has to exist, and
the Conductor's own `admissible_exists` needs the ACS to be able to stay
idle.

**(c) Other forms.**

* *(c1) An ideal ACS.* A plain-Lean instance of `ACSSafety` and
  `ACSTemporal`: one global decided set per window, fixed by the first
  correct decision; each correct validator decides within `Δ`. It is the
  class's model, not a protocol, so claiming it as "the ACS" would mislead.
  Its use is the **consistency witness** for (b).
* *(c2) A multi-shot consensus*, as the second margin note suggests: not in
  the target.

**Recommendation (open): (b), with (c1) as the non-vacuity witness.** P17
records the gap. Once a target revision specifies the ACS, (a) replaces the
assumption with a proof, along the path the MVBA took.

### 3.4 Two contract repairs needed under every option

* **C6: one pair per validator (F18, P16).** Add to `ACSSafety` the
  first-order field "a correct decider's set holds at most one slot per
  validator", and let `validity_quantitative` count distinct validators.
  With the system's fault bound (at most `f` Byzantine validators), the
  median lemma's hypothesis (`IsMedian.between_correct`'s "at most `f`
  Byzantine-attributed entries", [Windows.lean](../Cadence/Windows.lean))
  then follows from the contract. Today it does not.
* **C7: the ACS's `abandon` in the fragment (F19).** Move `abandon`,
  `abandoned` and their frames from `ACSTemporal` into `ACSSafety`, as
  `MVBASafety` has them. Add the cross-frames: `propose` leaves `abandoned`
  unchanged, and `abandon` leaves `proposed` unchanged. Then model Algorithm
  7, line 45 (`line:acs-abandon`) in `enter_window`, so that Proposition 12
  is a fact of the model and not a reading of the paper.

Both are [Interfaces.lean](../Cadence/Interfaces.lean) edits that change the
Conductor's VCs (one in-file sweep, about a minute cold) and nothing in the
Chorus or Mvba families.

## 4. The glue: the composition leg

### 4.1 What changes

**[Interfaces.lean](../Cadence/Interfaces.lean) (C8, F20).** The glue
instantiates only `SlotConsensusSafety`, and `participate`, `abandon` and
`propose` live in `SlotConsensusTemporal`. So the glue cannot even mention
them. Move the three inputs, their observables (`participating`,
`abandoned`, `proposed`), effects, step frames and initial conditions into
`SlotConsensusSafety`, all first-order, and add what is missing:

* the per-input cross-frames ("`participate` at `i` leaves `abandoned` and
  `proposed` unchanged", and so on, the `complete_frame` pattern);
* the per-validator frames ("an input at `i` leaves `j`'s records
  unchanged").

Without them, "the glue abandons only after finalizing" does not imply C1 at
the contract level, since a `participate` could set `abandoned`.
`SlotConsensusTemporal` keeps `sent`, `Admissible`, Termination and
Quiescence. Chorus does not instantiate `SlotConsensusSafety`, so its family
does not re-solve. The field proofs move from
[Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean) to
[Chorus/Compose.lean](../Cadence/Chorus/Compose.lean), where they are plain
Lean.

**[Cadence.lean](../Cadence/Cadence.lean).** Three handlers drive the
contract's inputs, as `acs_propose` drives the ACS's:

* `on_open i s sc_next`, Algorithm 1, line 17 (`line:participate`): requires
  `orch.opened os i s` and `sc.participate (sc_state s) i sc_next`. The
  ghost `sc_started` becomes the instance's own `participating`.
* `on_propose`, Algorithm 1, line 19 (`line:propose`): drives `sc.propose`
  instead of only recording `proposed`.
* `on_finalize`, Algorithm 1, lines 20–23
  (`line:upon-finalize`–`line:abandon`): performs `sc.abandon` in the same
  step as `orch.complete`, which is one more parameter. The glue's record
  `sc_abandoned` becomes the instance's `abandoned`.

The glue gains first-order invariants, each sweep-checked:

* `sc.abandoned (sc_state s) i → ∃ v, sc.finalized (sc_state s) i v`
  (C1's state form);
* `sc.participating (sc_state s) i → orch.opened os i s` (with
  `integrity_timing`, C2's state form).

Its own safety claims are unchanged: the edit adds behaviours only through
contract-legal input transitions.

**[System.lean](../Cadence/System.lean).** The end theorem is re-proven at
the moved fields. The composed system's Chorus is no longer inert, and
[CompositionContracts.md](CompositionContracts.md) §7's seam 2 ("the glue
does not drive Chorus's inputs") closes.

### 4.2 What the composition discharges

Each of Chorus's caller conditions ([Bounds.md](Bounds.md) §6.4.6, "What
the Conductor's timed claims need from this leg") becomes a theorem about
the composed run:

| Chorus's condition | discharged from | needs |
|---|---|---|
| C1: abandon only after finalizing | Algorithm 1, line 23 (`line:abandon`): the glue's invariant above | K1 only |
| C2: no start before `D − Δ` | `OrchestratorSafety.integrity_timing`, with `deadline s = start_time s + Δ` (a schedule tie, §6.2) and `clock_agrees` | K1, and the composed timed run (K7) |
| participation by `t` | the Conductor opens by `t` (Recovery, or Proposition 15), and the glue's `on_open` row | K5, K7 |
| Δ-synchronized participation | Lemma 15 plus the `on_open` row; at δ = 0 exactly `d_tot = Δ` | K4, K7 |

And the Conductor's caller conditions, (R-tot) and (R-term) of §2.3, come
from `Chorus.chorusWithTotality`'s two fields through the same table read
backwards.

### 4.3 Corollary 4 as a theorem

Yes. Its Lean form is: for every admissible composed run and every slot `s`,
the run's slot-`s` Chorus projection satisfies `SyncParticipation`, C1 and
C2. So `Chorus.chorusWithTotality`'s `bounded_termination` and `totality`,
and `Chorus.chorusTemporal`'s `termination`, hold for it with no caller
premise left. It is the last step of the leg (K7) because it needs Lemma 15
within Cadence. The paper orders it the same way: "one finished result
applied to another".

### 4.4 Order

The glue edit (K1) is untimed and depends on nothing in this leg. Doing it
first makes the composed system non-inert, the safety theorem keeps holding,
and every later session works on the final glue. Corollary 4 and the
composed timed claims (K7) come after the Conductor's timed claims (K4–K6),
which they consume.

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

**The choices.**

* **(α) δ = 0.** The paper's model: "validators' clocks are synchronized,
  so they share one global timeline", and local computation is
  instantaneous throughout the main body. It is a field `δ = 0` of the
  Conductor's schedule, used by the Conductor's and the composed claims
  only. Chorus's and the MVBA's theorems stay δ-general. The composed
  theorem instantiates them at δ = 0, where `Lchorus` and `Ltot` are the
  paper's values by `rfl` (`chorusWithTotality_ℓ_paper`,
  `chorusWithTotality_d_tot_paper`).
* **(β) A δ-robust statement.** Re-synchronize on absolute time: a window
  whose correct validators all enter before its first slot's starting time
  opens every slot at that starting time (Algorithm 7, line 27
  (`line:conductor-wait-for-open`)). Its openings are then synchronized by
  the clock, to within one δ, whatever the spread of the entries. That
  resets the ratchet in the smooth regime of Proposition 18. It does not
  cover the windows before it, and Propositions 14–16 use `d_tot`-totality
  there. A δ-robust Recovery would need a new argument for those windows,
  with a tolerance that stays inside Chorus's Δ. That is new mathematics,
  not a formalization of the paper's.
* **(γ) Record the degradation.** State the δ-general per-window lemma
  (tolerance `d_ω`, recurrence `d_{ω+1} = d_ω + cδ`), and the claims as
  holding while `d_ω ≤ Δ`. Faithful, but nothing downstream can use it.

**Recommendation (open): (α)**, with the tolerance-parametric lemmas kept
wherever they cost nothing (Chorus's already are), so that (β) stays open
for later. F3 stands as a finding about the model, not about the paper: the
paper's model is δ = 0.

## 6. The timing model

### 6.1 The clock

The run's clock is the system's clock, as for the MVBA and Chorus
([Bounds.md](Bounds.md) §6.2.1). The Conductor already holds a state clock,
`now`, advanced by `tick`, and only its `open_slot` guard reads it.
`OrchestratorTemporal.clock_agrees` requires `r.clk n = now (r.at' n)` in
every admissible run. In the composed run the orchestrator's state is the
glue's `os`, so the composed `Admissible` takes the same equation. Time
advances exactly at the Conductor's `tick` steps, which are the system's
clock steps. Chorus's phase timers and the MVBA's timers read `r.clk` at the
projected indices, so all of them read one clock. **No clock is added to any
model.** One proof obligation follows: `tick`'s guard must not block a
clock advance that the run's `clock_unbounded` demands. It does not:
`tick t` is enabled for every `t ≥ now`.

### 6.2 One time theory, one Δ

The time theory is §6.2.2's of [Bounds.md](Bounds.md): a linearly ordered,
cancellative, additive monoid, Archimedean for the witness. The classes let
each module carry its own Δ (`SlotConsensusWithTotality.Δ`,
`ACSTemporal.Δ`), and the Conductor model's `start_time` is the slot's
deadline minus a Δ the model never names. The paper's proofs use one Δ for
all three. Proposition 13's entry step, for instance, needs the ACS's
`max(t, GST) + Δ` to fall within `max(t, GST) + d_tot`. So the schedule ties
them (F23):

* `T_acs.Δ = Δ` and `T_acs.ℓ = ℓ` (the ACS's constants are the system's);
* `fs.D s = start_time s + Δ` (Chorus's per-slot deadline, `FamilySchedule.D`,
  is the Conductor's starting time plus Δ);
* `SlotConsensusWithTotality.deadline = fs.D` (already `rfl` in
  `Chorus.chorusWithTotality`).

### 6.3 Windows, slots, and the parameter assumptions as fields

The timed claims are stated at an instance where slots are numbers. The
Veil model keeps `slot` an abstract order, and the claims fix:

* `slot := ℕ`, slot 1 at the run's start: `start_time 1 = clk 0`, the
  paper's "every correct validator enters window 1 at time 0 = `T₁(1)`";
* `start_time s = start_time 1 + (s − 1) • τ`, the τ-spaced deadlines of
  Appendix A.1 (`subsection:mcp-preliminaries`), with `0 < τ`;
* window widths and readiness boundaries from the model's shift functions
  (§7, F21), at `W` and `p`.

The schedule record, `ConductorSchedule`, extends Chorus's `FamilySchedule`
with `W p : ℕ`, `τ`, the ACS's `ℓ`, and these fields, each named after its
paper line:

* `assm_one : (p − 1) • τ + Φ_oc + ℓ ≤ W • τ`
* `assm_two : (p − 1) • τ + Φ_oc ≤ (W − 1) • τ`
* `assm_three : Δ < ℓ`
* `assm_four : d_tot + ℓ ≤ (p − 1) • τ`
* `δ_zero : δ = 0` (§5)

`Φ_oc` and `d_tot` are not new constants. They are
`Lchorus Δ δ ℓ_MVBA + Ltot Δ δ Δ` and `Ltot Δ δ Δ`, the Chorus instance's
own data, so the four assumptions speak about the values the composed
theorem uses.

Two remarks:

* With `ℓ > Δ ≥ 0`, assumption (4) forces `p ≥ 2`. The main body's
  `p ∈ {0, …, W − 1}` therefore only matters for the safety properties
  (P9's note, [PaperAlignment.md](PaperAlignment.md) §6). Natural-number
  subtraction in `(p − 1) • τ` is then exact.
* Assumptions (1)–(2) could be instantiated with the sharper
  `Φ_oc = 5Δ + ℓ_MVBA` (the tight `4Δ + ℓ_MVBA` that F4/P5 confirmed, plus
  `d_tot = Δ`) instead of the paper's `6Δ + ℓ_MVBA`. The claim keeps the
  paper's values, as the Chorus leg did.

### 6.4 The rows

The Conductor's and the glue's honest actions get rows in the style of
[Bounds.md](Bounds.md) §6.4.2. All of them are local: none consumes a
message, since the Conductor's only cross-validator channel is the ACS,
whose timing comes in through `T_acs.Admissible`:

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
paper's module.

* **F16: the contract's Totality is eventual, and the paper's consumers need
  `d_tot`.** `OrchestratorTemporal.totality` is Module 2's ("eventually
  opens"). Proposition 14 and Corollary 4 use Lemma 15's "more specifically"
  form, `max(t, GST) + d_tot`, and no class states it. **Proposal:** C4
  (§2.3). Paper side: P15.
* **F17: Totality and Recovery are stated unconditionally, but the
  Conductor has them only within Cadence.** A caller that never completes a
  slot leaves the Conductor in window 1. So the fields as stated are false
  of every faithful Conductor, unless `Admissible` encodes the caller's
  behaviour. That is P13's pattern, one module up. Module 2's commented-out
  "assumed behaviour" block, which lists "complete only after opening" and
  "complete within `Φ_oc` of opening", would not repair it either. The
  proofs use the *conditional* completion guarantees (R-tot) and (R-term).
  An unconditional `Φ_oc` bound is itself a consequence of the Conductor's
  totality (Proposition 14), so a module assumption stating it would assume
  the conclusion. **Proposal:** C5 (§2.3). Paper side: P15.
* **F18: a decided ACS set may hold several pairs of one validator.**
  Module 4's Validity: "`|set| ≥ 2f + 1`, and for every validator-slot pair
  `(p_i, s_i) ∈ set` such that `p_i` is a correct validator, `p_i` proposed
  slot `s_i`". `ACSTemporal.validity_quantitative` says the same: `2f + 1`
  distinct *pairs*. The median argument ("the decided vector contains at
  least `f + 1` pairs contributed by correct validators", before
  Proposition 7) and the model's stated bridge at `acs_decide` (justified by
  `lowerMedian_between_correct`, whose hypothesis is "at most `f`
  Byzantine-attributed entries") need at most `f` Byzantine *pairs*. Under
  the module as stated, a single Byzantine validator's `2f + 1` pairs are a
  valid decision. The median is then the adversary's choice, the next
  window can overlap the previous one, and the proofs of Integrity (Lemma 12
  (`lemma:conductor-integrity`)) and Monotonicity (Lemma 13
  (`lemma:conductor-monotonicity`)) through Proposition 8
  (`prop:acs-fate-range`) fail. **The model's safety theorems are unaffected
  as theorems:** the bridge is a `require`, and they hold of the model. What
  fails is the bridge's justification, that it removes no behaviour of a
  correct ACS. Any ACS that collects one signed proposal per validator meets
  the stronger property. **Proposal:** C6 (§3.4). Paper side: P16.
* **F19: the ACS's `abandon` is outside the fragment the Conductor
  instantiates, and nothing frames it against `propose`.** Algorithm 7,
  line 45 (`line:acs-abandon`) is therefore not modelled, and Proposition 12
  cannot be derived even in the weak form "the Conductor never abandons",
  since no field says that a `propose` leaves `abandoned` unchanged.
  **Proposal:** C7 (§3.4).
* **F20: Slot Consensus's inputs are outside the fragment the glue
  instantiates, and the inputs have no cross-frames.** The same gap as F19
  for Chorus. The glue cannot drive Algorithm 1, line 17 (`line:participate`),
  Algorithm 1, line 19 (`line:propose`) or Algorithm 1, line 23
  (`line:abandon`), and even if it could, C1 would not follow at the contract level. **Proposal:** C8 (§4.1).
* **F21: the Conductor model leaves free what the timed claims fix.** Each
  freedom is sound for safety and makes a timed claim false of the model:
  * the decided interval's width is unconstrained (Conductor.lean,
    `acs_decide`: "deliberately *not* forced to be exactly `W` slots
    wide"), so boundedness's count `2W − p` and Proposition 17's "no gap"
    fail;
  * `acs_propose` keeps only the lower bound of Algorithm 7, lines 39–41
    (`line:sstar-compute`–`line:sstar-update`), "strictly beyond the current
    window", and not "the earliest slot whose starting time has not
    passed". Propositions 16 and 19 use the latter;
  * `acs_decide` brackets the first slot from below only. Propositions 17
    and 19 need the upper bracket (the median is at most some correct
    proposal), which [Windows.lean](../Cadence/Windows.lean) already
    proves;
  * `start_time` is only monotone, not τ-spaced, and `genesis_time` is not
    tied to slot 1's starting time;
  * `open_slot` may fire late ("Timing relaxation" in the model's header);
    its row (§6.4) closes that in the timed premise.

  **Proposal (K2):** immutable shift functions `win_last`, `win_boundary`
  (the `+ (W − 1)` and `+ (p − 1)` of a window's first slot), required by
  `acs_decide` and the genesis assumption; the full `s*` rule over `now` in
  `acs_propose`; the upper bracket as a second witness pair; and
  `start_time` strictly increasing. All are first-order, and the instance
  at `ℕ` fixes the arithmetic.
* **F22: `enter_window` reads the first correct decision anywhere, not the
  validator's own.** Its guard is the global `acs_decided`, which
  `acs_decide` sets on some correct validator's decision. Algorithm 7, line
  44 (`line:acs-decide`) fires on `p_i`'s own `decide`. As a δ-row,
  `enter_window` would owe an entry before `p_i`'s ACS has decided, which
  the paper's protocol cannot do; ACS's Δ-Totality would then go unused,
  and the bound would come out tighter than the paper's for the wrong
  reason. **Proposal (K1):** add `require acs.has_decided (acs_state w') i`
  (the F6 pattern of [Bounds.md](Bounds.md) §6.4.2).
* **F23: the classes allow several Δs, and the paper uses one.** See §6.2.
  **Proposal:** schedule ties, not class edits.
* **F24: a part that stops stepping has no timed run.** A contract's
  `TimedRun` steps along `trans` forever, and no class gives a stutter
  step. In a composed run most per-slot Chorus instances and per-window ACS
  instances eventually stop. The Chorus leg met the same question for the
  MVBA inside Chorus: `Component.Projection` asks that the part be stepped
  infinitely often (`scheduled`, [Liveness.md](Liveness.md) §4.2), and the
  idle run kept the MVBA stepping through repeated `abandon` inputs. At the
  contract level there are two further obstacles. Whether the ACS has an
  always-enabled step is unknown. And `admissible_exists` gives *some*
  admissible run from each initial state, not one with the inputs this
  consumer gives, so the Conductor cannot build its own admissible runs
  from it (the "vacuity does not compose" point of
  [CompositionContracts.md](CompositionContracts.md) §7). **Proposal:** a
  spike (K0) before the scaffolding. Two candidates:
  * a stutter-closed run for parts, which touches the run structure, not a
    class;
  * a named premise "the ACS can stay idle admissibly", met by the ideal
    ACS.

  A `TransitionSystemSafety` change would re-solve all four Veil families
  cold, and is the last resort.

## 8. Premises and non-vacuity from the start

### 8.1 The draft ledger

In the premise-ledger form of [Bounds.md](Bounds.md) §6.4.5, which R21 is
moving to a page of its own; this list moves there when K8 lands. Each line
gives the premise, why it is plausible, and the planned use. "Composed"
marks premises of the composed claims only.

*The instance:*

* **`n = 3f + 1`, at most `f` Byzantine, one fault pattern** (`hbyz`, the
  ACS's `byz` the same): obvious. *Used in:* the median brackets (with C6),
  and Chorus's claims.
* **The parameters `W ≥ 1` and `2 ≤ p ≤ W − 1`, and `0 < τ`**: obvious.
  *Used in:* every window lemma.

*The schedule* (`ConductorSchedule`, §6.3):

* **(1)–(4)**: arithmetic, satisfiable by choosing `W` large (§8.2). *Used
  in:* (1) Proposition 17 point 2; (2) Proposition 17 point 1 and
  Proposition 19; (3) Propositions 16 and 17; (4) Propositions 18 and 19.
* **`δ = 0`** (if (α) is taken): the paper's model. *Used in:* the window
  induction.
* **The Δ ties** (§6.2): definitional. *Used in:* Proposition 13 (entry),
  C2.
* **Slot 1 starts at the run's start; slots are τ-spaced**: the paper's
  setting. *Used in:* Propositions 16 and 19, and Lemma 16.

*The run* (`Admissible`):

* **The Conductor's and the glue's rows** (§6.4): the paper's
  instantaneous handlers and timers, as bounded fairness. *Used in:* every
  "fires by" step.
* **Each window's ACS projection is `T_acs`-admissible**: what "the ACS
  meets its module" means for one run. *Used in:* every use of the ACS's
  timed fields.
* **Each opened slot's Chorus projection is `Chorus.Admissible`**
  (composed): the Chorus leg's premises, per slot. *Used in:* (R-tot) and
  (R-term).
* **`clock_agrees`**: definitional (§6.1).

*The assumed module:*

* **An `ACSTemporal` instance at the fragment the Conductor instantiates**
  (option (b)): the paper's own "Uses: ACS". Not obvious that one exists:
  the ideal ACS (§3.3 (c1)) is the witness.

*Caller conditions:* none at the composed level. C1, C2, participation,
Δ-synchronized participation, (R-tot), (R-term), Δ-synchronized proposals
and no premature abandonment are all discharged (§4.2, Proposition 12,
Corollary 2).

### 8.2 The witness plan

One witness for the composed claims, in the style of
[Chorus/Witness.lean](../Cadence/Chorus/Witness.lean):

* `Fin 4`, validator 3 Byzantine and silent, one proposer per slot;
* `Δ = τ = 1`, `δ = 0`;
* the MVBA witness's `ℓ_MVBA`, `ℓ_ACS = 2`, `p = 4`,
  `W = p + Φ_oc + ℓ_ACS`. That gives (1) `3 + Φ_oc + 2 ≤ W` and
  (2) `3 + Φ_oc ≤ W − 1` with room to spare, (3) `1 < 2`, and
  (4) `1 + 2 ≤ 3`;
* the ideal ACS;
* a **periodic** run: every window repeats the first one, shifted by `Wτ`
  in time and by `W` in slot number. In each slot Chorus takes the fast
  path, as in the Chorus witness.

The run must be infinite and keep every row honest, so its construction is a
generic "periodic extension" lemma plus one period checked by hand. This is
the largest single piece of the leg, and the first non-vacuity witness of
the composed system: the per-module witnesses do not certify the composition
([CompositionContracts.md](CompositionContracts.md) §7, "Vacuity does not
compose").

## 9. Staging and sizing

Each stage is one R-session, numbered when it is scheduled. K0 can run in
parallel with K1. Everything else is in order.

* **K0: the projection spike (F24).** Settle how a part that stops stepping
  is projected, and the ACS's idle admissibility. A scratch file, no model
  or class edit. Output: a decision recorded here.
* **K1: the composition edit, untimed.**
  * [Interfaces.lean](../Cadence/Interfaces.lean): C6, C7, C8 with the
    cross-frames.
  * [Cadence.lean](../Cadence/Cadence.lean): `on_open`, the `propose` and
    `abandon` inputs, two invariants.
  * [Conductor.lean](../Cadence/Conductor.lean): `enter_window` reads its
    own decision and abandons the ACS (F19, F22).
  * [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) and
    [Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean): the moved
    field proofs. [Composition.lean](../Cadence/Composition.lean) and
    [System.lean](../Cadence/System.lean): re-proven.
  * A `sat trace` in the glue showing participation.
  * Re-solves: the Conductor's and the glue's sweeps cold (about a minute
    each). The Chorus, FallbackReceipt and Mvba families rebuild warm
    (Interfaces.lean is imported, and their VC statements do not change).
  * Pins: the end-theorem axiom pins re-stated. No `#veil_status` count
    changes. Closes [CompositionContracts.md](CompositionContracts.md) §7
    seam 2, and repairs F18's justification.
* **K2: the Conductor's timing completion (F21).** Conductor.lean only:
  shift functions, the `s*` rule, the upper bracket, τ-spacing. Re-solves the
  Conductor's sweep, plus
  [Composition.lean](../Cadence/Composition.lean). Can be bundled with K1's
  Conductor edit if K1 stays reviewable.
* **K3: scaffolding and statements.** C4 and C5 (one
  [Interfaces.lean](../Cadence/Interfaces.lean) edit, warm), timed Conductor
  runs, `ConductorSchedule`, the rows, the per-window ACS projection, the
  ideal ACS, and the claims stated in rely form. Plain Lean, no re-solve.
* **K4: the window induction.** Proposition 13, Lemma 15, Corollaries 1–3,
  and the count `2W − p` (Proposition 11, Lemma 14) from `[bounded_tail]`
  and the widths. Plain Lean.
* **K5: Recovery.** Propositions 14–19 and Lemma 16. Plain Lean; the
  schedule arithmetic is where F4-style slack would show.
* **K6: the contract instances.** `OrchestratorTemporal` and
  `OrchestratorWithTotality` at `Conductor.orchestratorSafety`, the join
  with its `…_toSafety` `rfl` lemma, then the
  [Cadence.lean](../Cadence.lean) rows and pins,
  [CLAUDE.md](../CLAUDE.md)'s status text,
  [Architecture.md](Architecture.md) §4 (after R21), and
  [CompositionContracts.md](CompositionContracts.md) §5.
* **K7: the composed timed claims.** The composed run, the per-slot Chorus
  projections, C1/C2/participation/synchronized participation discharged,
  (R-tot)/(R-term) from Chorus, **Corollary 4 as a theorem**, and the timed
  `𝓡`-Liveness and censorship resistance at `𝓡 = 2Wτ`. Plain Lean.
  Possibly two sessions.
* **K8: non-vacuity.** The periodic composed witness (§8.2), and the
  ledger moved to the premises page. Probably two sessions.

**Total:** nine to eleven sessions. **No stage re-solves the Chorus or Mvba
families cold**, unless K0 forces a `TransitionSystemSafety` change (F24).

**Constraints:**

* one [Interfaces.lean](../Cadence/Interfaces.lean) edit at a time, so K1
  and K3 are serialized with each other and with any other contract edit;
* K1 and K2 both edit [Conductor.lean](../Cadence/Conductor.lean);
* the premise-presentation pass (R21) owns the premises page and
  [Architecture.md](Architecture.md) §4 until it lands.

As in the Chorus leg, the dominant risk is statement churn. F16–F24 are the
churn this record tries to absorb before any Lean.
