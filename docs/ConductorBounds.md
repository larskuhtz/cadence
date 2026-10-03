# Conductor bounds — the kick-off record

*Written 2026-10-02 (session R22), before any Lean. Nothing here is proven
or modelled: it is the plan for the Conductor's timed claims and for the
composition that closes the Cadence loop. [Bounds.md](Bounds.md) §6.4 (the
Chorus leg) set the shape, and §6.2 (the MVBA leg) the timing machinery
this leg reuses. Decisions are recorded with their reasons. The three
questions put to Lars are **decided (2026-10-03)**, each as recommended.
K1, the untimed composition edit, is **done** (2026-10-03, R25; §9), and so
are K2, the model's timing completion (2026-10-03, R26; F21 closed), K3,
the contract edit and the claims stated (2026-10-03, R27; §9), and K4, the
window induction with Boundedness and Totality proven (2026-10-03, R28;
§9).*

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
as fields of `OrchestratorTemporal`, Totality and Recovery in rely form, with
the `d_tot` form on top in `OrchestratorWithTotality`
([Interfaces.lean](../Cadence/Interfaces.lean); C4, C5, since K3), and
nothing instantiates them. The three claims are stated, with their premises,
in [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean). Two are
proven (K4): Boundedness at the paper's `2W − p`, from the interval form
`safety [bounded_tail]` of [Conductor.lean](../Cadence/Conductor.lean) and
the window widths (`Conductor.boundedness`), and `d_tot`-Totality, by the
window induction (`Conductor.totality`, with Proposition 13 and its three
corollaries; [Conductor/Induction.lean](../Cadence/Conductor/Induction.lean)).
Recovery is K5's. The safety half of the
composition is proven (`Cadence.system_positional_log_safety`,
[System.lean](../Cadence/System.lean)), and since K1 the glue drives
Chorus's `participate`, `propose` and `abandon` inputs through the contract,
so the composed system's Chorus is not inert
([CompositionContracts.md](CompositionContracts.md) §3, §7 item 2).

**What the timed claims would assume.** The same timing model as the MVBA and
Chorus claims: one clock, one time theory and one Δ for the whole system.
Messages between correct validators arrive within Δ after GST, and local
steps are instantaneous (δ = 0, decided in §5). Timers fire on time.
They would also assume that the ACS meets its module (Module 4 (`mod:acs`)),
since the target leaves the ACS unspecified (§3), and that the four parameter
assumptions of Algorithm 7 (`algorithm:conductor`) hold. Every condition the
Conductor needs from its caller, and every condition Chorus needs from the
Conductor, is discharged by the composition. None is left as a premise of
the composed claims.

**The three questions, decided by Lars (2026-10-03).**

1. **The ACS (§3).** The target has no concrete ACS: the supplement's
   section is empty. **Decided:** keep the ACS as a contract,
   so the timed claims are relative to an `ACSTemporal` instance and the ACS
   is an assumed module named in the trust statement, as the MVBA was
   before §6.2. A plain-Lean ideal ACS is the consistency witness only.
   P17 records the gap, and (a) replaces the assumption once the paper
   specifies an ACS.
2. **How "within Cadence" enters the contract (§2.3).** **Decided:**
   state the Conductor's Totality and Recovery in the rely form
   already used for Chorus and the MVBA. The conditions the paper takes from
   Cadence become antecedents over the orchestrator's own observables (C5),
   and a Conductor-specific level states the `d_tot` form that Corollary 4
   consumes (C4).
3. **δ (§5, C3 from the Chorus leg).** **Decided:** prove the
   Conductor's and the composed claims at δ = 0, the paper's instantaneous
   local computation, stated as a plain schedule premise. Chorus's and the
   MVBA's theorems keep their δ-general forms, and F3 records the
   degradation at δ > 0.

**Fourteen findings about statements (§7, F16–F29) and three for the
paper's authors (P15–P17, [PaperAlignment.md](PaperAlignment.md) §6).** Two
of them
reach the existing safety claims. **F18 / P16:** Module 4's Validity
bounds the size of the decided set but not the number of pairs per
validator. The median argument behind Proposition 7 (`prop:acs-nonoverlap`),
and the model's stated bridge at `acs_decide`, need at most `f`
Byzantine-attributed pairs. With the module as stated, a decided set could
consist entirely of one Byzantine validator's pairs. The fix is one
first-order field, and every natural ACS satisfies it. **F25:** the model covered only `p ≥ 1` of the paper's `p ∈ {0, …, W − 1}`,
closed by R26. The other findings concern the timed statements and the
model's timing freedoms.

**Decisions in one place.**

* ACS: **(b), a contract, decided (2026-10-03)**, with (c1), the ideal
  ACS, as the consistency witness (§3.3).
* C4 (an `OrchestratorWithTotality` level) and C5 (rely antecedents for
  Totality and Recovery): **decided (2026-10-03), jointly** (§2.3).
* C6 (one pair per validator in a decided ACS set): **done (R25)**, and
  independent of the timed leg, because it repairs the justification of a
  safety bridge (F18).
* C7 (the ACS's `abandon` moves into `ACSSafety`) and C8 (Slot Consensus's
  inputs move into `SlotConsensusSafety`), each with the cross-frames:
  **done (R25)**. They are the composition leg's prerequisites (§4, F19,
  F20).
* δ = 0 for the Conductor's and the composed claims, as a plain schedule
  premise: **decided (2026-10-03)** (§5).
* The clock is the run's. The Conductor's `now` equals it through
  `OrchestratorTemporal.clock_agrees`, so `tick` is the system's clock step
  (§6.1).
* One schedule record extends Chorus's `FamilySchedule` with the windows and
  the four parameter assumptions as fields, in the `δ_le_Δ` style (§6.3).
* F24 (a part that stops stepping): **settled by K0 (R24, 2026-10-03)**. The
  composed run is relabelled so that a part's stutters, where its own
  `trans` allows them, count as its steps, and the per-part premise applies
  only once a correct validator has started the part. No class edit, no new
  field, and `TransitionSystemSafety` unchanged (§7 F24, §9 K0).
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

**Decided (Lars, 2026-10-03): (i) with C4**, in one
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

**Decided (Lars, 2026-10-03): (b), with (c1) as the consistency
witness.** The ACS is an assumed module, named in the trust statement. P17
records the gap. Once a target revision specifies the ACS, (a) replaces the
assumption with a proof, along the path the MVBA took.

### 3.4 Two contract repairs needed under every option

* **C6: one pair per validator (F18, P16).** Add to `ACSSafety` the
  first-order field "a correct decider's set holds at most one slot per
  validator", and let `validity_quantitative` count distinct validators.
  With the system's fault bound (at most `f` Byzantine validators), the
  median lemma's hypothesis (`IsMedian.between_correct`'s "at most `f`
  Byzantine-attributed entries", [Windows.lean](../Cadence/Windows.lean))
  then follows from the contract. **Done (R25):** `ACSSafety.decided_unique`,
  and `Cadence.acs_median_bracket` ([AcsMedian.lean](../Cadence/AcsMedian.lean))
  proves the link.
* **C7: the ACS's `abandon` in the fragment (F19).** Move `abandon`,
  `abandoned` and their frames from `ACSTemporal` into `ACSSafety`, as
  `MVBASafety` has them. Add the cross-frames: `propose` leaves `abandoned`
  unchanged, and `abandon` leaves `proposed` unchanged. Then model Algorithm
  7, line 45 (`line:acs-abandon`) in `enter_window`, so that Proposition 12
  is a fact of the model and not a reading of the paper. **Done (R25):** the
  model's invariant `[acs_abandoned_decided]`.

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

**Decided (Lars, 2026-10-03): (α)**, as a plain schedule premise of the
Conductor's and the composed timed claims. The Chorus and MVBA results stay
general in δ, and the tolerance-parametric lemmas are kept wherever they
cost nothing (Chorus's already are), so that (β) remains possible later. F3
records the degradation at δ > 0. It is a finding about the model, not about
the paper, whose model is δ = 0.

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
  paper's "every correct validator enters window 1 at time 0 = `T₁(1)`"
  (the model's `[genesis_window]` already ties its initial clock to slot
  1's starting time, so this is `clk 0 = now (r.at' 0)`, `clock_agrees`);
* `start_time s = start_time 1 + (s − 1) • τ`, the τ-spaced deadlines of
  Appendix A.1 (`subsection:mcp-preliminaries`), with `0 < τ` (the model
  states only that starting times strictly increase, `[start_time_strict]`);
* window widths and readiness boundaries from the model's shift functions
  (§7, F21): `win_last s = s + (W − 1)` and `win_boundary s = s + p`, the first slot
  that readiness does not ask to be complete (F25).

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
  **Closed (R25):** C6 is in the contract, and the bridge's justification
  is a theorem, `Cadence.acs_median_bracket`: with at most `f` Byzantine
  validators, the median of a correct decider's set lies between two of its
  correct pairs. The `require` itself stays, a stated bridge: the model
  computes no median, and cardinality is outside the solver's fragment.
* **F19: the ACS's `abandon` is outside the fragment the Conductor
  instantiates, and nothing frames it against `propose`.** Algorithm 7,
  line 45 (`line:acs-abandon`) is therefore not modelled, and Proposition 12
  cannot be derived even in the weak form "the Conductor never abandons",
  since no field says that a `propose` leaves `abandoned` unchanged.
  **Proposal:** C7 (§3.4). **Closed (R25):** `abandon`, `abandoned` and
  their frames are in `ACSSafety` with both cross-frames, `enter_window`
  abandons the instance, and Proposition 12 is the invariant
  `[acs_abandoned_decided]`.
* **F20: Slot Consensus's inputs are outside the fragment the glue
  instantiates, and the inputs have no cross-frames.** The same gap as F19
  for Chorus. The glue cannot drive Algorithm 1, line 17 (`line:participate`),
  Algorithm 1, line 19 (`line:propose`) or Algorithm 1, line 23
  (`line:abandon`), and even if it could, C1 would not follow at the contract level. **Proposal:** C8 (§4.1).
  **Closed (R25):** the three inputs are in `SlotConsensusSafety` with the
  per-input cross-frames and the per-validator frames; the glue's
  `on_open`, `on_propose` and `on_finalize` drive them, and C1 and C2 hold
  in state form (`[abandoned_after_finalize]`, `[participating_opened]`).
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
  (the `+ (W − 1)` and `+ (p − 1)` of a window's first slot; R26 made the
  boundary `+ p`, F25), required by
  `acs_decide` and the genesis assumption; the full `s*` rule over `now` in
  `acs_propose`; the upper bracket as a second witness pair; and
  `start_time` strictly increasing. All are first-order, and the instance
  at `ℕ` fixes the arithmetic.
  **Closed (R26):** in [Conductor.lean](../Cadence/Conductor.lean), each a
  constraint the paper's protocol satisfies, so the model loses only runs
  the paper does not have:
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
    the contract by `Cadence.acs_median_bracket` (R25);
  * `[start_time_strict]` (Appendix A.1 (`subsection:mcp-preliminaries`):
    `τ > 0`), and `[genesis_window]` starts the clock at slot 1's starting
    time (the proof of Proposition 16 (`prop:window-open-time`): "every
    correct validator enters window 1 at time `0 = T₁(1)`"). The spacing
    itself, `+ (s − 1)τ`, is K3's, at the instance.

  The `open_slot` freedom stays in the model, as planned: it is an
  over-approximation (the paper's punctual openings are among the model's
  runs), and the row closes it in the timed premise
  ([PaperAlignment.md](PaperAlignment.md) §5.10). Every safety property
  and `Conductor ⊨ OrchestratorSafety` re-proved unchanged.
* **F22: `enter_window` reads the first correct decision anywhere, not the
  validator's own.** Its guard is the global `acs_decided`, which
  `acs_decide` sets on some correct validator's decision. Algorithm 7, line
  44 (`line:acs-decide`) fires on `p_i`'s own `decide`. As a δ-row,
  `enter_window` would owe an entry before `p_i`'s ACS has decided, which
  the paper's protocol cannot do; ACS's Δ-Totality would then go unused,
  and the bound would come out tighter than the paper's for the wrong
  reason. **Proposal (K1):** add `require acs.has_decided (acs_state w') i`
  (the F6 pattern of [Bounds.md](Bounds.md) §6.4.2). **Closed (R25)**, as
  proposed.
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
  [CompositionContracts.md](CompositionContracts.md) §7). **Decided by the
  K0 spike (R24, 2026-10-03): a stutter lift at the projection, and a
  per-part premise that applies once a correct validator has started the
  part. No class changes, `TransitionSystemSafety` included.**
  [spikes/14_part_projection.lean](../spikes/14_part_projection.lean)
  builds it over the contracts as they are; §9 K0 has what K3 takes from
  it.

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
  started the part. For window `w`'s ACS, in the spike's form:

  ```lean
  ∀ w, (∃ n i s, ¬ byz i ∧ A.proposed ((r.at' n).acs w) i s) →
    ∃ p : (stutterComp (acsComp w)).Projection (liftRun (acsComp w) r).toLRun,
      TA.Admissible (partRun p)
  ```

  The slot form is the same, over "a correct validator participates in
  slot `s`". The guard loses nothing. Every use of an ACS field at window
  `w` has a correct proposal there: Termination's antecedent says so
  outright, and Totality's antecedent, a correct decision, implies one by
  `integrity`. Likewise every use of a slot field has a correct participant.

  The Conductor cannot build its admissible runs from
  `ACSTemporal.admissible_exists`, whatever inputs it gives, for three
  reasons:

  * the run that field provides has its own clock and `gst`, while a part's
    run carries the composed ones;
  * its steps may be inputs, or proposals, that the Conductor's guards do
    not give;
  * it is one run per instance, while the Conductor interleaves infinitely
    many instances on one clock.

  The guard makes that unnecessary. The Conductor's idle run moves only the
  clock (and fires `open_slot` at the starting times). No correct validator
  ever proposes, since readiness needs a completion and the idle run gives
  none. The premise therefore holds vacuously, by the fragment's
  `init_proposed` alone. `toy_admissible_exists` proves this for a consumer
  of the Conductor's shape, at every ACS, using no `ACSTemporal` field.
  **No new ACS field is needed.** The ACS then only has to be a module
  whose admissible runs exist (the class already says so) and whose
  finished instances can stutter. That second condition is part of the
  premise: a composed run in which a started instance deadlocks has no
  admissible part run, so it is not admissible. Module 4 (`mod:acs`) gives
  the ACS an `abandon()` input, as Module 1 gives Chorus one. In Chorus and
  the MVBA, re-issuing that input is the stutter, and the ideal ACS (§3.3
  (c1)) will have the same by construction. Whether a deadlock is
  plausible is the auditor's judgement, on the premises page.

  **The other candidates, and why not.**
  * *A stutter-closed run in the contracts* (`TimedRun` steps by `trans` or
    equality, or a reflexivity field in `TransitionSystemSafety`): the
    first would re-prove the MVBA and Chorus temporal instances, whose
    `Admissible` is over labelled runs. The second would re-solve all four
    families cold, and is false of every Veil model without a no-op action,
    Chorus's initial state included.
  * *A contract field for an always-enabled step*: needless for the
    consumer's claims, since the lift reads stutters off `trans`. As an
    internal step it is false of Chorus in an all-correct run, so it
    would also constrain (a).
  * *A finite-run `Admissible`*: changes all four temporal classes and
    their two proven instances.
  * *`scheduled` through repeated inputs* (the Chorus idle run's device),
    with a consumer action that re-issues `abandon`: the lift gets the same
    stutters without a model edit, and without an action the paper does
    not have.
* **F25: the model's readiness boundary was a slot it asked to be
  complete, so the model covered only `p ≥ 1`.** The main body allows
  `p ∈ {0, …, W − 1}` (Algorithm 7 (`algorithm:conductor`)). Its readiness
  check, Algorithm 7, line 23 (`line:ready-check`), "return `k − j ≤ W − p`"
  over the opened slots `s_1 < … < s_k` with `s_1, …, s_j` complete, asks
  in window `ω` for every slot of the earlier windows and the window's
  first `p`; at `p = 0` for the earlier windows only, and in window 1 for
  nothing. The paper is precise here. The model's boundary was the
  window's `p`-th slot with readiness asking for the slots *up to* it, so
  `first ≤ boundary` (from the first model on: `genesis_shape` and
  `acs_decide`'s interval shape) excluded `p = 0`, and the Conductor's
  safety theorems said nothing about that configuration. Found by R26.
  **Closed (R26)**, at the coordinator's request, in the same cold sweep:
  the boundary is the window's `(p + 1)`-th slot (`win_boundary s = s + p`),
  readiness asks for the scheduled slots *strictly below* it, and
  `[shift_shape]`'s `s ≤ win_boundary s ≤ win_last s` is then exactly
  `0 ≤ p ≤ W − 1`. `[bounded_tail]` reads the boundary with `<`: at
  `p ≥ 1` it states what it stated before, at `p = 0` the paper's content.
  No new state, every property kept, the sweep green. The timed claims
  need `p ≥ 2` anyway (§6.3, P9's note).

* **F26: the ACS contract does not say that its inputs are accepted.**
  Found by K3. `ACSSafety` states `propose`'s and `abandon`'s effects and
  frames, but not that a correct validator can give them: a contract whose
  `propose` relation is empty meets every field. The Conductor's handlers
  `acs_propose` and `enter_window` give these inputs, so their rows are
  owed only where the ACS accepts them, and with an ACS that refuses a
  correct validator's proposal no later window is ever entered: Recovery
  fails, and Totality can fail when it refuses some validators only.
  Module 4 (`mod:acs`) has the two inputs in its interface, and an input is
  the caller's to give, so every ACS meets it. The MVBA's contract states
  its one caller-driven input this way (`MVBASafety.accept_enabled`, rely
  form). **Closed (R27, decided by Lars 2026-10-03):** two first-order
  fields in that rely form, `propose_enabled` (a correct validator that has
  neither abandoned nor proposed can propose any slot) and
  `abandon_enabled` (a correct validator can abandon; window entry gives
  this input), in **`ACSTemporal`**. They were first placed in `ACSSafety`,
  withheld from the solver with `veil_smt_ignore`. The Conductor's in-file
  sweep then failed: `open_slot × open_prefix_agreement` went from about 5 s
  to over the 180 s budget on both attempts, reproducibly in isolation,
  with the fields in the middle of the class or at its end, and other
  cells slowed severalfold. Without the fields the sweep is green in 44 s.
  So withholding did not leave the solver's queries as they were (the
  cause is not diagnosed; a question for the Veil fork). Only a
  consumer's timed claims need the two fields, and no Veil module
  instantiates `ACSTemporal`, so no VC moves. The ideal ACS proves both
  (`Cadence.IdealAcs.acsTemporal`), and the claims lost the premise they
  carried in between. Not a paper issue: Module 4's inputs are
  invocations by the caller, and the module formalism has no refusal
  ([PaperAlignment.md](PaperAlignment.md) §6's table of facts used).

* **F27: the claims' time had no ordered addition.** Found by K4.
  [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean)'s claims
  were stated over a `time` with a linear order and an additive monoid, but
  no axiom tying the two. Then `max(t, GST) + Δ` is not monotone in `t`, an
  opening at `t` need not be before `t + Δ`, and Totality is unprovable as
  stated. The time theory of §6.2 is ordered, and Chorus's and the MVBA's
  timed claims assume it. **Closed (R28, decided by Lars 2026-10-03):**
  `TotalityClaim` and `RecoveryClaim` take `[IsOrderedAddMonoid time]`;
  `BoundednessClaim`, a state property, needs no time theory. Not a paper
  issue: the paper's time is the real line.
* **F28: Totality needs a slot whose starting time has not passed.** Found
  by K4. `acs_propose`'s `s*` is the first slot beyond the window whose
  starting time has not passed (Algorithm 7, lines 38–41
  (`line:ready-time`–`line:sstar-update`)), and `TotalityClaim` assumed
  nothing of the starting times beyond `[start_time_strict]`, so they could
  be bounded. Once the clock passes them all, no correct validator can
  propose to the next ACS. A validator that becomes ready only then never
  proposes, the ACS's synchronized-proposals assumption fails, and nothing
  makes it decide or enter a window that an earlier-ready correct validator
  entered: the claim is false in such runs. The paper's slots are
  infinitely many and τ-spaced on the real line (Appendix A.1
  (`subsection:mcp-preliminaries`)), so its `s*` always exists. **Closed
  (R28, decided by Lars 2026-10-03):** a plain premise,
  `StartsUnbounded th` ("whatever the time, some slot has not started
  yet"), used only to pick `s*` (`Conductor.sstar_exists`). `StartTimes`
  does not imply it, even with an Archimedean time: with
  `start₀ = (−1, 0)` and `τ = (0, 1)` in the lexicographic monoid
  `{(a, b) : a < 0, or a = 0 ∧ b ≥ 0}`, every starting time stays below
  `(0, 0)`. Deriving it would need `0 ≤ start₀` or a group. *For K5:*
  `RecoveryClaim` proposes too, so it needs `StartsUnbounded` as well, or
  `StartTimes` together with `[Archimedean time]` and `0 ≤ start₀`. Not a
  paper issue.
* **F29: Totality's fault-bound premise was unused.** Found by K4. K3 gave
  `TotalityClaim` the premise "at most the ACS's `fault_bound` validators
  are Byzantine", for the decided interval's row (its correct median
  witnesses). The window induction never needs that row: a validator
  enters a window only after a correct validator has, and by then the
  interval is recorded. **Closed (R28, decided by Lars 2026-10-03):** the
  premise is dropped from `TotalityClaim`. The decided interval's row and
  the fault bound remain premises of `RecoveryClaim`, where Propositions 15
  and 16 need the interval to be recorded.

## 8. Premises and non-vacuity from the start

### 8.1 The draft ledger

In the premise-ledger form of [Bounds.md](Bounds.md) §6.4.5. Superseded by
the draft K3 wrote on the premises page, [Premises.md](Premises.md) §9, over
the premises as stated in Lean; the list below is the plan it started from. Each line
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
* **`δ = 0`** (decided, §5): the paper's model. *Used in:* the window
  induction.
* **The Δ ties** (§6.2): definitional. *Used in:* Proposition 13 (entry),
  C2.
* **Slot 1 starts at the run's start; slots are τ-spaced**: the paper's
  setting. *Used in:* Propositions 16 and 19, and Lemma 16.

*The run* (`Admissible`):

* **The Conductor's and the glue's rows** (§6.4): the paper's
  instantaneous handlers and timers, as bounded fairness. *Used in:* every
  "fires by" step.
* **Each started window's ACS projection is `T_acs`-admissible**: what "the
  ACS meets its module" means for one run. The projection is F24's stutter
  lift, and the premise applies once a correct validator has proposed to
  the window. *Used in:* every use of the ACS's timed fields.
* **Each started slot's Chorus projection is `Chorus.Admissible`**
  (composed): the Chorus leg's premises, per slot, over the same lift, once
  a correct validator participates. *Used in:* (R-tot) and (R-term).
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

Every finished part must be able to stutter (F24): a finished slot does,
by `abandon` re-issued to a validator that has already abandoned, and the
ideal ACS does by construction.

The run must be infinite and keep every row honest, so its construction is a
generic "periodic extension" lemma plus one period checked by hand. This is
the largest single piece of the leg, and the first non-vacuity witness of
the composed system: the per-module witnesses do not certify the composition
([CompositionContracts.md](CompositionContracts.md) §7, "Vacuity does not
compose").

## 9. Staging and sizing

Each stage is one R-session, numbered when it is scheduled. K0 can run in
parallel with K1. Everything else is in order.

* **K0: the projection spike (F24). Done (R24, 2026-10-03).** Decision: the
  stutter lift plus the per-part premise guarded by a start (F24). No class
  or model edit, and no field implied. The evidence is
  [spikes/14_part_projection.lean](../spikes/14_part_projection.lean). What
  the later stages take from it:
  * **K3** moves the spike's generic half into the library, next to the
    timed projection in [Timed.lean](../Cadence/Timed.lean), with axiom
    pins: `contractRTS`, `stutterSys`, `stutterComp`, `liftRun`, the two
    scheduling lemmas, `partRun` and its transfer lemmas. It builds the
    Conductor's per-window component, `acsComponent w`, whose frame and
    step come from the generated frame lemmas of `acs_state`, as
    `Chorus.mvbaComponent`'s do. It also states the guarded ACS clause of
    the Conductor's `Admissible` in the form quoted in F24.
  * **K6** proves `admissible_exists` by the idle run, which moves only the
    clock and fires `open_slot`. It shows that the rows `acs_propose` and
    `enter_window` are disabled there (no completion, so no readiness), as
    `Chorus.not_enabled_of_idle` does for Chorus. The ACS clause then holds
    by `init_proposed`.
  * **K7** builds the glue's per-slot component, `scComponent s`, with the
    same guarded clause over a correct participant.
  * **K8** shows that the witness's finished parts can stutter: a finished
    slot by re-issuing `abandon` (Chorus's and the MVBA's `abandon` only set
    the flag), and the ideal ACS by construction. It also shows that the
    part's `Admissible` accepts the inserted stutters.
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
  * **Done (2026-10-03, R25).** As planned, with these differences:
    * the glue's record relations `sc_abandoned` and `proposed` are gone;
      `participating`, `abandoned` and `proposed` are ghosts reading the
      instance's own records, so no glue-side copy of a call remains;
    * `on_propose` also requires `participating i s`, the order of
      Algorithm 1, lines 17–19 (`line:participate`–`line:propose`);
    * `[bounded_concurrency_interval]` now states one direction, "an
      active instance is opened and not completed", which is what Lemma 5
      (`lemma:cadence-bounded-concurrency`)'s bound needs. The converse,
      which the paper's proof also states, holds only when `participate()`
      is atomic with `open(s)`; with `on_open` a separate handler, a
      validator that has opened `s` and not yet run it has one active
      instance fewer. Classified as an abstraction with its argument
      ([PaperAlignment.md](PaperAlignment.md) §5.10): the separate
      handlers over-approximate the paper's atomic ones, and the paper's
      runs are among the model's;
    * the Conductor gains the invariant `[acs_abandoned_decided]`
      (Proposition 12 (`prop:acs-no-premature-abandonment`) in state form),
      so the paper's reading is a fact of the model;
    * F18's link is the new [AcsMedian.lean](../Cadence/AcsMedian.lean)
      (`Cadence.acs_median_bracket`, both brackets, so K2's upper bracket
      has its justification already); the `require` stays a stated bridge;
    * sweeps, cold: the glue 182 → 216 cells, the Conductor 189 → 197, both
      green; the slowest cell, `enter_window × bounded_tail`, at 24 s of the
      180 s budget on this machine. K2 is not bundled.
* **K2: the Conductor's timing completion (F21).** Conductor.lean only:
  shift functions, the `s*` rule, the upper bracket, τ-spacing. Re-solves the
  Conductor's sweep, plus
  [Composition.lean](../Cadence/Composition.lean). Can be bundled with K1's
  Conductor edit if K1 stays reviewable.
  * **Done (2026-10-03, R26).** As planned (F21's record), with these
    differences:
    * `acs_decide` takes `first` only: `boundary` and `last` are the shifts
      of it, which keeps the action at 10 parameters with the second
      witness pair;
    * one new invariant, `[win_bounds_shift]` (every window's bounds are the
      shifts of its first slot), so K4 reads the widths off a reachable
      state instead of re-deriving them from the transitions;
    * `[genesis_window]` also ties `genesis_time` to slot 1's starting time
      (the fourth bullet of F21), and `[shift_shape]` replaces
      `genesis_shape`, which it implies at slot 1;
    * F25 found and closed: the boundary is the window's `(p + 1)`-th slot
      and readiness asks for the slots strictly below it, so the model
      covers the paper's `p = 0` (one further commit, re-solved cold);
    * two comments still say the model keeps the widths meta:
      [Interfaces.lean](../Cadence/Interfaces.lean)'s boundedness field
      (K3's file) and [Composition.lean](../Cadence/Composition.lean)'s
      boundedness note (a shared file). They are left for K3 and K4, which
      touch both;
    * the sweep, cold: the Conductor 197 → 205 cells, all green; the slowest
      cell at 19 s of the 180 s budget on this machine.
      [Composition.lean](../Cadence/Composition.lean) and
      [System.lean](../Cadence/System.lean) re-proved without an edit; no
      VC outside the Conductor changed.
* **K3: scaffolding and statements.** C4 and C5 (one
  [Interfaces.lean](../Cadence/Interfaces.lean) edit, warm), timed Conductor
  runs, `ConductorSchedule`, the rows, the per-window ACS projection, the
  ideal ACS, and the claims stated in rely form. Plain Lean, no re-solve.
  * **Done (2026-10-03, R27).** As planned, with these differences:
    * **C5's tolerance is one constant.** (R-tot) is "openings synchronized
      within `d` ⇒ completions synchronized within `d`", at the caller's
      latency `caller_d_tot`: the paper's induction closes because Chorus's
      totality latency equals the tolerance its condition grants ("both
      equal `Δ = d_tot`"). (R-term) takes the same tolerance and
      `caller_ℓ`. Both latencies are data of `OrchestratorTemporal`, since
      Recovery's `2Wτ` holds only at the instance's constants;
      `OrchestratorWithTotality` adds only `d_tot` and the bounded
      Totality. Eventual Totality takes (R-tot) only, as the paper's proof
      uses no termination for it;
    * the generic half of the K0 spike is a new file,
      [PartProjection.lean](../Cadence/PartProjection.lean), next to
      [Timed.lean](../Cadence/Timed.lean) rather than inside it (a shared
      file), with the two field lemmas updated for R25's moves
      (`abandoned` and `participating` are fragment fields now);
    * slots are `ℕ` from `0`: `s : ℕ` is the paper's slot `s + 1`, so
      starting times are `start₀ + s • τ` with no truncated subtraction;
    * the claims' conclusions are the contract's fields read at the
      Conductor's fragment (`orchestratorSafety th`), the caller's
      conditions likewise, through `contractRun`; K6 consumes them as
      stated;
    * the rows are the Conductor's three handlers and the punctual opening;
      the glue's rows of §6.4 time the caller's side and are K7's, over the
      glue's own runs;
    * Boundedness is a state property at bound `2W − p`, with
      `WindowShifts` its only premise; it is exactly what Lemma 5 needs
      (K7), so no separate Lemma-5 statement is made;
    * F26 found (§7) and closed in the same PR, by Lars's decision: the
      ACS contract states that its two inputs are accepted
      (`ACSTemporal.propose_enabled`, `abandon_enabled`, a second
      [Interfaces.lean](../Cadence/Interfaces.lean) edit, in the upper class
      because in `ACSSafety` they diverged a Conductor cell even when
      withheld from the solver, §7 F26). No VC moved;
    * the fault bound (at most `TA.fault_bound` Byzantine) is a premise of
      Totality too, not only of Recovery: the decided interval's row needs
      a correct pair in the decided set;
    * of the two stale "widths kept meta" comments R26 listed, the
      [Interfaces.lean](../Cadence/Interfaces.lean) one is fixed; the
      [Composition.lean](../Cadence/Composition.lean) one stays for K4
      (a shared file K3 does not edit).
* **K4: the window induction.** Proposition 13, Lemma 15, Corollaries 1–3,
  and the count `2W − p` (Proposition 11, Lemma 14) from `[bounded_tail]`
  and the widths. Plain Lean.
  * **Done (2026-10-03, R28).** Two new files, every theorem pinned at the
    standard trio, and the three claims' statements edited once (F27–F29,
    each decided by Lars in the session). What is proven, each item at the
    paper's deadline, with no slack:

    | the paper | Lean | deadline |
    |---|---|---|
    | Proposition 11 (`prop:open-count-window`), interval form | `Conductor.opened_above` | — (a state fact) |
    | Lemma 14 (`lem:boundedness`) | `Conductor.boundedness` (`BoundednessClaim`) | `2W − p` opened, uncompleted slots, exactly |
    | Definition 6 (`def:window-synchronized`) | `EntrySync`, `OpenSync`, `CompSync`, `PropSync`, `WindowSynchronized` | — |
    | Proposition 12 (`prop:acs-no-premature-abandonment`) | the model's `[acs_abandoned_decided]` (K1), consumed as the ACS's `NoPrematureAbandon` | — |
    | Proposition 13 (`prop:window-synchronization`) | `Conductor.window_synchronized` | `max(t, GST) + Δ`, all four conditions |
    | Corollary 1 (`cor:entry-synchronization`) | `Conductor.entry_sync` | `max(t, GST) + Δ` |
    | Corollary 2 (`cor:proposal-synchronization`) | `Conductor.prop_sync` | `max(t, GST) + Δ` |
    | Lemma 15 (`lemma:conductor-totality`) | `Conductor.open_sync`, and `Conductor.totality` (`TotalityClaim`) | `max(t, GST) + d_tot`, `d_tot = Δ` |
    | Corollary 3 (`cor:completion-totality`) | `Conductor.comp_sync` | `max(t, GST) + Δ` |

    Totality closes here, as planned, not in K5. Differences from the plan:
    * **the induction runs over first slots, not windows**
      (`Conductor.window_induction`). The window order is abstract and not
      known to be well-founded. A window is named by its first slot, and the
      entry into a window depends only on smaller slots: its predecessor's
      entry, the completions below the predecessor's boundary, and the
      proposals to its ACS. The paper's four per-window steps are the lemmas
      `entry_step`, `open_step` and `prop_step`, with (R-tot) for the
      completions (`comp_of_open`);
    * **Boundedness needs no successor window in the order**: the one
      window above `s`'s that can hold an opened slot is found from that
      slot's own window, through its entered predecessor. That is a new
      plain-Lean reachability induction, `Conductor.entered_pred`, since the
      model records the predecessor only in a guard. It lives with the
      other model facts in
      [Conductor/Boundedness.lean](../Cadence/Conductor/Boundedness.lean);
    * **three statement changes**, each found by the proof and decided by
      Lars (F27, F28, F29): an ordered time, unbounded starting times, and
      no fault bound for Totality. K3's note that the fault bound was "a
      premise of Totality too" is superseded by F29;
    * the ACS is consumed through its contract only: Δ-Totality on the
      window's part of the run (`Cadence.acs_totality_in` under
      `AcsAdmissible`), `integrity`, `propose_enabled` and
      `abandon_enabled`. Its termination, its fault bound and the median
      bracket are not used. Chorus enters only through (R-tot). The
      decided interval's row (`TimedRows.decide`) is not used by Totality;
      it is Recovery's;
    * the two rows are consumed in their diagonal form
      (`BufferedFairFamily.diag`), at `δ = 0`: a gate open from an index
      whose clock is within the deadline fires its row by that deadline;
    * [Composition.lean](../Cadence/Composition.lean)'s stale note about the
      widths is fixed (comment only). The model header of
      [Conductor.lean](../Cadence/Conductor.lean) still lists
      `B`-Boundedness as unproven in its discharge map. It is a model
      file, so editing it re-runs the sweep; it is left for K6, which
      rewrites the status text.
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
  Also **Lemma 5 (`lemma:cadence-bounded-concurrency`)'s bound** as a
  theorem: at most `𝓑` instances actively participated in, from the glue's
  `[bounded_concurrency_interval]` (an active instance is opened and not
  completed) and `OrchestratorTemporal.boundedness` at the instance K6
  provides (take the least of `𝓑 + 1` active slots: the other `𝓑` are
  opened above an opened, uncompleted slot). Possibly two sessions.
* **K8: non-vacuity.** The periodic composed witness (§8.2), and the
  ledger moved to the premises page. Probably two sessions.

**Total:** nine to eleven sessions. **No stage re-solves the Chorus or Mvba
families cold.** K0 settled F24 without a `TransitionSystemSafety` change.

**Constraints:**

* one [Interfaces.lean](../Cadence/Interfaces.lean) edit at a time, so K1
  and K3 are serialized with each other and with any other contract edit;
* K1 and K2 both edit [Conductor.lean](../Cadence/Conductor.lean);
* the premise-presentation pass (R21) owns the premises page and
  [Architecture.md](Architecture.md) §4 until it lands.

As in the Chorus leg, the dominant risk is statement churn. F16–F25 are the
churn this record tries to absorb before any Lean.
