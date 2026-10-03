# Open items

Everything *claimed* in this repository is proven and axiom-pinned — these
are places the development could go further, not gaps in what is asserted.
The authoritative, numbered list of Chorus-side open items is
[ChorusDesign.md](ChorusDesign.md) §9 (and §§10.1–10.3 for the bigger
lifts); this file collects the cross-cutting ones and the model-hygiene
wishlist.

## Contract composition — what the named seams still cost

The composition itself is in place and described in
[CompositionContracts.md](CompositionContracts.md). What remains, in the
order worth taking:

* **Chorus's participation interface.** Module 1 (`mod:slotconsensus`)'s
  `participate`/`abandon`/`propose` are absent from the model, so the whole
  of `SlotConsensus`'s upper level except Hiding's protocol half is unproven
  (the fields of `SlotConsensusTemporal`), and the glue's records of those
  calls (`sc_abandoned`, `proposed`) stay glue-local. Adding the inputs to
  the Chorus model would let the glue drive them and shrink what is owed to
  the temporal fields; it is a model change and pays the Chorus cold
  re-solve.
* **The ACS median bridge.** `acs_decide`'s `require` that a correct pair of
  the decided set brackets the first slot from below is the quantitative half
  of ACS validity (`ACS.validity_quantitative`, upper level) through
  [Windows.lean](../Cadence/Windows.lean)'s median lemma; cardinality is outside the first-order
  fragment. A Lean theorem deriving the `require` from the upper-level field
  plus the median lemma would turn that bridge into a proof.
* **The MVBA certificate bridge.** The completeness direction — that a
  decided entry's certificate is visible on Chorus's network — is what
  enables the decision handlers, and is what the liveness argument has to
  name ([CompositionContracts.md](CompositionContracts.md) §7 item 1).
* **The monitor's MVBA leg** is a coverage gap: the monitor instantiates
  Chorus's MVBA constraint with a stub that never decides, so no fallback-path
  trace can be checked ([Monitor.md](Monitor.md) §8).

Two smaller items fall out of the same work: **stating `Admissible`** (each
`…Temporal` class's admissible-execution model) for the Conductor and Chorus
in Lean — today it is an unsupplied class field whose intended content is the
(F-justice)/(A-acs-*) prose of the models' liveness sections; and a
**composed bounded-concurrency corollary** — from the glue's
`bounded_concurrency_interval` and `OrchestratorTemporal.boundedness`,
"at most `B` slots actively participated in", which needs a finite
minimum-extraction argument over slots that is not written yet.

## Soundness — guarding against vacuous claims

These are the items that would most change an auditor's confidence, so they
come first.

* **Instantiate the primitive class stack end-to-end.** The Byzantine-quorum
  interface is already discharged for the concrete `byzNodeSetFin` family
  (see [../Cadence/ByzQuorum.lean](../Cadence/ByzQuorum.lean)), which is why
  it is *not* on the assumption list in
  [Architecture.md](Architecture.md) §4, and `MVBA` has
  `Mvba.mvbaSafety` / `Mvba.mvba_of_temporal`
  ([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)). `ThresholdIBE` remains an axiomatic class
  with no model instance: producing one would demonstrate the axiom set is
  satisfiable rather than accidentally contradictory.
  [ChorusDesign.md](ChorusDesign.md) §9 item 1.
* **Non-vacuity of the safety claims.** [Cadence/Cadence.lean](../Cadence/Cadence.lean) and [Conductor.lean](../Cadence/Conductor.lean)
  carry in-build `sat trace` reachability witnesses so that the properties
  are not vacuously true (if finalization were unreachable, agreement would
  hold trivially). The receipt layer additionally has an exhaustive
  `#model_check` whose explored graph is checked to contain proposing runs.
  The MVBA instantiation has the strongest instrument of the three: a
  **mutation test** ([Cadence/Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) — the lock check removed,
  agreement refuted by the model checker and the counterexample pinned),
  which shows its invariants are load-bearing and not merely true.
  Extending the same discipline to every new property is a standing rule,
  not a one-off task.

  **Chorus is the exception**: it cannot carry an in-build `sat trace`
  today, for two reasons. (i) The
  trace pipeline needs the model-check scaffolding's label enumeration
  (`ActionTag_EnumClass` — see the Conductor's scaffolding note), which
  [Chorus.lean](../Cadence/Chorus.lean) deliberately disables (`veil.gen.modelCheckScaffolding
  false`): the derived `FinEncodableInjOnly` instances are O(n^k) in its
  number of actions and blow Lean's whnf heartbeat budget at Chorus's size. (ii) Every
  finalization trace passes through `vote`, whose bulk update uses
  `decide (∀ M, ¬ local_entry_pos …)` — `Classical.propDecidable`, which
  the trace pipeline cannot translate (the known failure mode behind the
  "no `decide` in update right-hand sides" rule; the glue's
  `record_skip` decomposition ([Cadence/Cadence.lean](../Cadence/Cadence.lean)) is the workaround pattern). Unblocking either
  is a model refactor, not a trace addition. The standing witness is
  instead the **monitor fixture run in CI** (`scripts/container.sh
  monitor`, run by [verify.yml](../.github/workflows/verify.yml) after the verification
  stage): the fast-path fixture reaches `finalize_commit` against the
  model's extracted actions, so an edit that made finalization unreachable
  turns CI red — [Monitor.md](Monitor.md) has the mechanism.
  Reachability-directed trace generation (§ Liveness below) would
  supersede this.
* **Syntactic audit of the monotone-network contract.** The (M-frame) half of
  the network abstraction — network relations consulted in positive position
  only — is checked by hand today and *not* enforced by the tool; a violation
  would not fail the build, it would silently void the asynchrony argument.
  A small Lean meta-program that walks each action's syntax and flags negative
  occurrences of a relation declared "network" would turn the top item of
  [Architecture.md](Architecture.md) §4 into a machine check. The other
  half already exists: Veil's generated step lemmas give the per-action frame
  and monotonicity facts as kernel-checked theorems rather than as a table
  maintained by hand. [ChorusDesign.md](ChorusDesign.md) §9 item 3.

  Two requirements come from the external audit, which found two relations
  mis-tabled in the hand audit's own record — exactly the failure mode a
  machine check removes. The check must *classify* every occurrence
  (positive / self-row / documented exception — the categories of
  [ChorusDesign.md](ChorusDesign.md) §3.1.1) rather than merely reject, so that sound negative
  reads are reported and acknowledged instead of slipping past a reject-only
  lint.

## Liveness

* **A non-vacuity instrument at the *composition* level.** The reason one is
  needed at all is that non-vacuity does not compose —
  [CompositionContracts.md](CompositionContracts.md) §7, "Vacuity does
  not compose", states why, and why the principled fix is liveness rather
  than a better contract. This item is the cheap standing check, not the
  answer. Every instrument of this kind in the repository is per-model: the
  `sat trace` blocks of `Cadence`, `Conductor` and `Mvba` and the
  `#model_check`s of the receipt layer and the MVBA mutation test. There is
  **none** for the composed system — [System.lean](../Cadence/System.lean), [Composition.lean](../Cadence/Composition.lean),
  [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) and
  [Mvba/Compose.lean](../Cadence/Mvba/Compose.lean) contain no reachability witness at all. So a
  guard that becomes unsatisfiable only *at the instantiation*, where one
  module's parameter meets another's state, would not fail a build: the
  invariants would hold vacuously and every pin would stay green.

  That is not hypothetical: because the MVBA checks validity on `propose`,
  Chorus's `mvba_propose` depends, at the composed instance, on a bridge between two
  notions of validity that nothing identifies
  ([CompositionContracts.md](CompositionContracts.md) §7 item 1). The
  composed safety theorem is unaffected, being parametric in the MVBA
  theory, but nothing reports whether that bridge is satisfiable.

  The instrument to build: instantiate the composed system at concrete
  finite sorts and either `#model_check` a run that reaches a decision, or
  pin a `sat trace` through `propose` → `mvba_propose` → a decision handler.
  Either turns "the seams admit a real execution" from an argument into a
  build-checked fact, and it is the only one of
  [MvbaPlan.md](MvbaPlan.md) §4's four instruments that does not already
  exist in some form.

* **Fired-once flags, then fairness over plain enabledness — done**
  (2026-09-30; the plan and its records are [Bounds.md](Bounds.md)
  §6.4.7). Every fair action that could stay enabled after firing has the
  local "not already" guard the paper gives it: the MVBA's anonymous
  assemblies became per-validator steps (R4, PR #51), and Chorus's
  certificate, chunk, entry and decision handlers got their fired-once
  records (R5, PR #50); the anonymous forming stays as an unfair adversary
  capability. The fairness premises are stated with plain enabledness again
  (R6): an action enabled from some point on eventually fires. Per model,
  every enabled fair label can change the state (`Mvba.enabledMove_of_enabled`,
  `Chorus.justice_enabledMove`), so the plain premise is the same as R3's
  state-changing one (`Mvba.fJustice_iff_move`, `Chorus.fJustice_iff_move`,
  and for the timed clauses `Mvba.boundedFair_iff_move` and
  `Mvba.boundedFairWhile_iff_move`).

* **Try the timer-priority route, which would remove the good view from
  the premises entirely.** (A-viewsync)'s second clause is indexed by the
  good view and has a commit certificate as its consequent; both are forced
  by the untimed abstraction, and [MvbaPlan.md](MvbaPlan.md) §3.7 gives
  the argument. The one clock-free alternative worth trying is a *priority*:
  the timer for a view fires only when no honest non-input action of that
  view is enabled. It is W-free and certificate-free, it would let the marker
  be weakly fair, and the good view would come from (A-leader-rotation)
  alone. §3.7 also lists the three obstacles — availability is not
  view-indexed, a label-to-view projection is needed, and widening a
  scheduling premise until the proof goes through is how one re-assumes the
  conclusion — and the reason it may not be worth it: the clock makes
  (A-viewsync) a theorem outright.

* **Exhibit a run satisfying the premises — done, for the MVBA and for
  Chorus.** Non-vacuity means that every premise of a theorem holds
  *jointly*. It is shown by a premise-by-premise ledger saying why each is
  satisfiable, plus one formal model and one run meeting all of them at
  once. Traces alone are illustrations.
  * **The MVBA:** `Mvba.timedTermination_premises_satisfiable` and
    `Mvba.termination_premises_satisfiable`
    ([Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean)), ledger in
    [Bounds.md](Bounds.md) §6.3. Building it found that the model did not
    halt a validator after deciding, as the supplement does (§6.3.2).
  * **Chorus:** `Chorus.termination_premises_satisfiable`,
    `Chorus.timedTermination_premises_satisfiable` and
    `Chorus.totality_premises_satisfiable`
    ([Cadence/Chorus/Witness.lean](../Cadence/Chorus/Witness.lean), R10),
    ledger in [Bounds.md](Bounds.md) §6.4.5. One run: everyone finalizes on
    the fast path, then abandons, and the MVBA stays quiet. `ValidBridge`
    holds with `valid := (· = v⋆)`, the one certifiable vector. Building
    it found F11: the re-dissemination row was owed off the fallback path,
    where the paper never re-disseminates, so the timed claims excluded
    ordinary fast-path runs. R11 fixed it in the statements.

  Every fair action of both models fires once, so both fairness premises
  hold at every quorum sort, and an idle tail owes nothing
  ([Bounds.md](Bounds.md) §6.2.4 and §6.4.7). **Left, optional:** a second
  Chorus run through the MVBA arm, which would satisfy the proposal and
  handoff families and `ValidBridge`'s completeness non-vacuously (§6.4.5).

* Full liveness-to-safety, so that liveness properties are stated and
  discharged inside the Veil models, like their safety properties. The
  fairness premises are already hypotheses of Lean theorems
  (`Chorus.termination`, `Mvba.termination`) and (A-mvba) is retired;
  what L2S would add is the models' own statement of those properties,
  checked per action by the existing pipeline.
* Actions are annotated with their fairness class in prose only; Veil has no
  surface syntax for it. The fork's liveness design doc sketches what that
  syntax should be ([Liveness.md](Liveness.md) §3 points to it).
* Reachability-directed trace generation, so that non-vacuity witnesses for
  the *progress* invariants can be produced mechanically rather than written
  by hand.
* The paper's Δ-bounds (`ℓ = 5Δ + ℓ_MVBA`, `d_tot = Δ`, …): the models
  are untimed, and the one latency bound proven is the MVBA's `ℓ_MVBA`
  ([Architecture.md](Architecture.md) §4 item 4). The routes to
  changing that and the recorded Veil tooling constraints are
  [Bounds.md](Bounds.md); the preferred route — a plain-Lean
  schedule theorem over timed runs of the generated transition system,
  no model change — has a **worked, staged plan ready to pick up** in
  [Bounds.md](Bounds.md) §6 (Chorus leg ≈ 2–4 sessions; ranked
  behind primitive instantiation and the (M-frame) checker, ahead of
  L2S on near-term value-per-effort). **The MVBA leg is complete**: its
  timing model is [Bounds.md](Bounds.md) §6.2 and
  [Cadence/Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean), and the good-view lemma
  ([Cadence/Mvba/Bound.lean](../Cadence/Mvba/Bound.lean)), the bounded
  claim (`Mvba.bounded_termination`,
  [Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean)),
  (A-viewsync) as a corollary (`Mvba.aViewSync_of_sync`) and the
  `MVBATemporal` instance (`Mvba.mvbaTemporal`,
  [Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)) are proven,
  at the fragment the composed system runs, and its premises are jointly
  satisfiable (`Mvba.timedTermination_premises_satisfiable`, below).
  Since step 5b its timing premise is the supplement's network
  ([Bounds.md](Bounds.md) §6.2.4, "The network clauses").

  **The Chorus leg: statements done (S2, 2026-09-30), totality and the
  timeline to the proposals proven (S3, 2026-10-01).** The timing model and
  both targets, `Chorus.TimedTerminationClaim` (`ℓ = 5Δ + ℓ_MVBA + 9δ`) and
  `Chorus.TotalityClaim` (tolerance-parametric), are `Prop` definitions in
  [Cadence/Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean). The
  premise findings F5 and C15 are closed (R8). `TotalityClaim` is proven
  (`Chorus.totality`, with the paper's `d_tot = Δ` as
  `Chorus.totality_paper`), and so is every milestone of
  Proposition 5 (`prop:chorus-finalization-time`) up to the MVBA proposals, by
  `M + 3Δ + 3δ` (`Chorus.within_all_input`,
  [Cadence/Chorus/Timeline.lean](../Cadence/Chorus/Timeline.lean)). S3's
  findings F9–F11 are fixed in the statements ([Bounds.md](Bounds.md)
  §6.4.2), and R12 fixed F12 in the model. **S4 done** (R18, 2026-10-02):
  `TimedTerminationClaim` is proven (`Chorus.timed_termination`, at the
  system's MVBA `Chorus.timed_termination_atMvba`), and F4 is confirmed
  (`Chorus.timed_termination_tight`, `4Δ + ℓ_MVBA + 8δ`;
  [Cadence/Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean)).
  **R19 done** (2026-10-02): F15 closed. The fallback signer
  re-disseminates inside the fallback-entry rule, and (Δ-avail) is derived
  (`Chorus.availWithin_of_timedJustice`; [Bounds.md](Bounds.md) §6.4.2,
  "F15 closed"). Next: S5, the contract instances
  ([Bounds.md](Bounds.md) §6.4.6).

  F13 is closed (R15, [Bounds.md](Bounds.md) §6.4.2, "F13 closed"): the
  fallback commit vote waits under the FallbackQC entries of the validator's
  own `B′`. F14 is closed (R14, "F14 closed").

## Model hygiene

* Retire remaining cryptic abbreviations in state and action names; keep the
  `msg_` prefix convention on every network relation (it is what makes the
  monotonicity audit above tractable by grep).
* Keep comments describing the model as it *is*. A comment that explains a
  superseded version reads as current to anyone who does not already know
  the history, which is the most expensive kind of documentation error here.
* Format the sources consistently against the Lean 4 style guide.

## Model structure — refactors explored and deferred

### Atomic-action candidates

The atomic-action pattern was applied successfully to `vote`. Four
analogous candidates were *not* applied:

| Candidate | Status | Reason |
|---|---|---|
| `cast_commit` = `commit_sign_pos` + `commit_sign_neg` + `cast_fast_commit` | Deferred | A/B `#check_vc cast_commit agreement_pos` ran in 1420 s wall / 245 s user CPU. Most likely the wall-time blowup was discharger-scheduler contention rather than genuine SMT cost (245 s of CPU against 1 420 s of wall). With the `commit_pos_sig_unique` / `commit_pos_sig_neg_excl` invariants stated explicitly, a re-test via `#check_action cast_commit` (bundles VCs under one awaiter — less contention surface) is the right next experiment. If that's clean, integrate. |
| `fb_vote` = `fb_sign_pos` + `fb_sign_neg` + `cast_fallback_vote` | Not attempted | Bulk update body is more complex than vote/cast_commit because each per-proposer fb-sign decision depends on an *existential* quorum witness (`∃ q : nodeset, …`). Plausibly tractable as an atomic action but the quantifier shape is genuinely different. Worth its own A/B. |
| `commit` = `commit_assign_pos` + `commit_assign_neg` + `finalize_commit` | Not attempted | Same shape as `cast_commit`; touches `agreement_pos` directly. If the `cast_commit` re-test goes well, this is the natural next candidate. |
| `mvba` = `on_mvba_decide_pos` + `on_mvba_decide_neg` + `mvba_terminate` | Deliberately *not* wanted | The decision handlers transport a correct validator's decision off the abstract MVBA state entry by entry, which keeps every update a monotone `:= true` and lets `#gen_proof_files` map proof files one for one. A bulk transport of the whole vector would be one action with a `∀ J`-quantified update over the two projections: possible, but it trades the monotone-update shape for one fewer action. |

The pattern for each is the same as `vote`/`cast_commit`: replace the
three actions with one atomic action whose body has universally-quantified
bulk updates on the per-proposer signature relations, with auxiliary
uniqueness/exclusion invariants stated explicitly so cvc5 has direct
hypotheses instead of multi-step chains.

### Measuring a candidate

Read the A/B numbers above with care: each `#check_vc` in them paid the
module's full DSL elaboration, and concurrent check commands contended for
one discharger scheduler, so fixed cost dominates them.

The recipe is to put `#prove_vc Chorus <action> <property> by …` cells in
a scratch file importing `Cadence.Chorus` — seconds per cell, since the model
elaborates once and the proof cache makes a statement-unchanged rebuild a
kernel replay. Prefer bundled measurement (`#check_action <action>`, many
invariants under one awaiter) over per-VC checks: it is closer to how the
action behaves in a full build.

### Other ideas not pursued

* **Payload-carrying pos/neg pairs** (`local_entry_*`, `committed_*`,
  `mvba_decided_*`, `fastqc_*`, `fallbackqc_*`, `msg_*_sig`): would need
  a Lean inductive (`inductive Outcome | none | pos (m : merkle_root) | neg`)
  as the codomain of a `function`, since Veil's `enum` can't hold the
  merkle_root payload. Plausibly correct but unclear whether the SMT
  cost stays manageable — the per-VC cost change measured for the
  payload-free `phase`/`path` enums was within noise, but those have a
  qualitatively different encoding signature from payload-carrying
  inductives. Not pursued.
* **`procedure` for inductive decomposition**: investigated, but Veil
  `procedure`s inline at WP elaboration — same transition relation as
  inlining. They don't help SMT.

## Scope extensions

* **Multi-slot Chorus.** The model fixes a single slot; cross-slot
  independence is argued, not modelled. The `slot` type is retained as a
  placeholder. [ChorusDesign.md](ChorusDesign.md) §3.4 and §9.
* **Epochs and proposer rotation**, and deriving `is_proposer` from a VRF
  rather than taking it as immutable configuration. [ChorusDesign.md](ChorusDesign.md) §9
  item 2.
* **Monitor coverage** — positive-path emission, per-message emission at the
  network boundary, multi-slot (Conductor) traces, Byzantine
  validate-vs-admit tagging. [Monitor.md](Monitor.md) §8.

## Paper alignment

The development corresponds to the paper target
([PaperAlignment.md](PaperAlignment.md) §0). The realignment items are
closed: sessions R14–R17 ([History.md](History.md)). The Chorus bounds leg
resumed with S4 (R18, done; P5 confirmed by proof) and R19 (F15, done); next is S5
(§ Liveness above, and [PaperAlignment.md](PaperAlignment.md) §8, "After the
realignment").

* **Send the findings page to the paper's authors**:
  [PaperAlignment.md](PaperAlignment.md) §6, P1–P13, all open on their
  side. Keep it current: a finding the authors resolve is marked so at the
  next re-check.
* **At the next paper commit**: re-run §1 of
  [PaperAlignment.md](PaperAlignment.md) against it and list it in §9; it
  becomes the target only when a session moves it.

The development verifies the main body's Algorithm 7 (`algorithm:conductor`). The
supplement's practical Conductor is outside the verified surface
([PaperAlignment.md](PaperAlignment.md) §9). Once it stabilises:

* **Check that the practical Conductor is compatible with the main-body
  Conductor at the interface level**, the `OrchestratorSafety` contract
  ([Interfaces.lean](../Cadence/Interfaces.lean)). If it is, the simpler
  main-body Conductor stays the verified one.

The `EquivCert` build guard is settled for the target: the main body's
Algorithm 5, line 29 (`line:fb-build-equiv`) is the protocol, and the supplement's witness-chunk
rule is an implementation variant
([PaperAlignment.md](PaperAlignment.md) §5.9; the supplement's
self-contradiction on it is finding P3).

## Verification-pipeline work

The tooling this project depends on is the public Veil fork (see
[Dependencies.md](Dependencies.md)); anything to be improved about it
belongs in that repository, and the requests this project has made are
tracked there. The one measurement worth carrying forward here is recorded in
[Architecture.md](Architecture.md) §7. What landed and when is
[History.md](History.md).

Two items remain open on this side:

* **The (M-frame) syntactic audit** above. Veil's generated step lemmas
  already supply the positive-position half of the contract as kernel-checked
  facts; what is missing is the classifier over action syntax.
* **One proof file opts out of the Bool-atom fold.**
  [Cadence/Chorus/Proofs/Vote.lean](../Cadence/Chorus/Proofs/Vote.lean) sets `veil.smt.foldBoolAtoms false`
  because its `fastqc_complete_implies_mvba_evidence` cell diverges under the
  folded query shape. That costs about 28 s of every warm re-validation (its
  batch runs 42 s against 13–15 s for the others) and leaves one ~30 MB
  olean. Worth revisiting if the cell can be made tractable in the folded
  shape, for instance as a manual cell.
