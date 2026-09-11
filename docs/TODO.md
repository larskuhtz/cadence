# Open items

Everything *claimed* in this repository is proven and axiom-pinned — these
are places the development could go further, not gaps in what is asserted.
The authoritative, numbered list of Chorus-side open items is
[`ChorusDesign.md`](./ChorusDesign.md) §9 (and §§10.1–10.3 for the bigger
lifts); this file collects the cross-cutting ones and the model-hygiene
wishlist.

## Contract composition — done 2026-09-04, the MVBA consumed 2026-09-10, two named seams left

**Implemented**: the module contracts are two-level type classes over an
explicit abstract state ([`CompositionContracts.md`](./CompositionContracts.md)),
the glue and the Conductor consume the state-level fragments as class
constraints (no restated `require`s), the Conductor and Chorus instances are
proven field for field, each implementation's unproven obligations are the
fields of an `…Temporal` class it supplies no instance of, and
`Cadence.system_positional_log_safety` composes MCP Safety at both instances
with no contract hypothesis left. What remains, in the order worth taking:

* ~~**Chorus's MVBA oracle as a class constraint.**~~ Done 2026-09-10
  ([`MvbaPlan.md`](./MvbaPlan.md) §6, step 6): Chorus `instantiate`s
  `MVBASafety` over an abstract state, advances it by an oracle step,
  drives `propose`, and two per-entry decision handlers transport a
  correct validator's decision into the existing records; the records'
  agreement is proven from the class, and `System.lean` plugs in
  `Mvba.mvbaSafety`. What is left of it is **one stated bridge** of the
  same kind as the ACS median bridge below — the handlers' certificate
  check against Chorus's network relations, the interpretation of the
  class's `Valid` in Chorus's vocabulary
  ([`CompositionContracts.md`](./CompositionContracts.md) §8 item 1) —
  and its completeness direction is what the liveness step (step 7) has
  to name. Follow-ups the step left: the monitor's MVBA leg is a
  coverage gap ([`Monitor.md`](./Monitor.md) §8), and `Chorus.lean` now
  imports `Interfaces.lean`, so a contract edit rebuilds the Chorus
  family (`Interfaces.lean`, "Why this file").
* **Chorus's participation interface.** `mod:slotconsensus`'s
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
  `Windows.lean`'s median lemma; cardinality is outside the first-order
  fragment. A Lean theorem deriving the `require` from the upper-level field
  plus the median lemma would turn the one stated bridge into a proof.

Two smaller items fall out of the same work: **stating `Admissible`** (each
`…Temporal` class's admissible-execution model) for the Conductor and Chorus
in Lean — today it is an unsupplied class field, and its intended content is
the
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
  (see [`../Cadence/ByzQuorum.lean`](../Cadence/ByzQuorum.lean)), which is why
  it is *not* on the assumption list in
  [`Architecture.md`](./Architecture.md) §4. `MVBA` has one since 2026-09-08
  (`Mvba.mvbaSafety` for the state-level fragment, `Mvba.mvba_of_temporal`
  for the full class given a temporal level — `Cadence/Mvba/Compose.lean`).
  `ThresholdIBE` is still an axiomatic class with no model instance:
  producing one would demonstrate the axiom set is satisfiable rather than
  accidentally contradictory. `ChorusDesign.md` §9 item 1.
* **Non-vacuity of the safety claims.** `Cadence.lean` and `Conductor.lean`
  carry in-build `sat trace` reachability witnesses so that the properties
  are not vacuously true (if finalization were unreachable, agreement would
  hold trivially). The receipt layer additionally has an exhaustive
  `#model_check` whose explored graph is checked to contain proposing runs.
  The MVBA instantiation has the strongest instrument of the three: a
  **mutation test** (`Cadence/Mvba/NoLock.lean` — the lock check removed,
  agreement refuted by the model checker and the counterexample pinned),
  which shows its invariants are load-bearing and not merely true.
  Extending the same discipline to every new property is a standing rule,
  not a one-off task.

  **Chorus is the exception** (2026-08 external audit, Finding 4): it cannot
  carry an in-build `sat trace` today, for two documented reasons. (i) The
  trace pipeline needs the model-check scaffolding's label enumeration
  (`ActionTag_EnumClass` — see the Conductor's scaffolding note), which
  `Chorus.lean` deliberately disables (`veil.gen.modelCheckScaffolding
  false`): the derived `FinEncodableInjOnly` instances are O(n^k) in its
  ~38 actions and blow Lean's whnf heartbeat budget. (ii) Every
  finalization trace passes through `vote`, whose bulk update uses
  `decide (∀ M, ¬ local_entry_pos …)` — `Classical.propDecidable`, which
  the trace pipeline cannot translate (the known failure mode behind the
  "no `decide` in update right-hand sides" rule; `Cadence.lean`'s
  `record_skip` decomposition is the workaround pattern). Unblocking either
  is a model refactor, not a trace addition. The standing witness is
  instead the **monitor fixture run in CI** (`scripts/container.sh
  monitor`, run by `.github/workflows/verify.yml` after the verification
  stage): the fast-path fixture reaches `finalize_commit` against the
  model's extracted actions, so an edit that made finalization unreachable
  turns CI red — [`Monitor.md`](./Monitor.md) has the mechanism.
  Reachability-directed trace generation (§ Liveness below) would
  supersede this.
* **Syntactic audit of the monotone-network contract.** The (M-frame) half of
  the network abstraction — network relations consulted in positive position
  only — is checked by hand today and *not* enforced by the tool; a violation
  would not fail the build, it would silently void the asynchrony argument.
  A small Lean meta-program that walks each action's syntax and flags negative
  occurrences of a relation declared "network" would turn the top item of
  [`Architecture.md`](./Architecture.md) §4 into a machine check. **Since
  2026-09-10 the other half exists**: M13 emits per-action frame and
  monotonicity lemmas, which is the positive-position content of the contract
  as kernel-checked facts rather than as a table maintained by hand.
  `ChorusDesign.md` §9 item 3. **Priority raised by the 2026-08 external
  audit** (its Finding 2): the hand audit's own record had mis-tabled two
  relations, which is exactly the failure mode a machine check removes. Design
  requirement from the same finding: the check must *classify* every
  occurrence (positive / self-row / documented exception — the categories of
  `ChorusDesign.md` §3.1.1) rather than merely reject, so sound negative reads
  are reported and acknowledged instead of slipping past a reject-only lint.

## Liveness

The fair-progress *safety content* is machine-checked, and the case split
is one theorem — `progress_dichotomy_of_saturation`,
`Cadence/Chorus/Progress.lean` — leaving exactly two temporal steps
outside Lean: (F-justice) delivers its saturation hypothesis, (A-mvba)
consumes its conclusion ([`ChorusDesign.md`](./ChorusDesign.md) §7 is what
the Chorus encoding does, [`Liveness.md`](./Liveness.md) the approach to
closing the rest). Remaining:

* Full liveness-to-safety, so that the (F-justice)/(F-byz)/(A-mvba)
  meta-axioms become premises of a Lean theorem rather than named
  assumptions. This is the single largest reduction of
  [`Architecture.md`](./Architecture.md) §4 available.
* Actions are annotated with their fairness class in prose only; Veil has no
  surface syntax for it. The fork's liveness design doc sketches what that
  syntax should be ([`Liveness.md`](./Liveness.md) §3 points to it).
* Reachability-directed trace generation, so that non-vacuity witnesses for
  the *progress* invariants can be produced mechanically rather than written
  by hand.
* The paper's Δ-bounds (`ℓ = 5Δ + ℓ_MVBA`, `d_tot = Δ`, …): the models
  are untimed and no artefact claims a latency bound
  ([`Architecture.md`](./Architecture.md) §4 item 4). The routes to
  changing that and the recorded Veil tooling constraints are
  [`Bounds.md`](./Bounds.md); the preferred route — a plain-Lean
  schedule theorem over timed runs of the generated transition system,
  no model change — has a **worked, staged plan ready to pick up** in
  [`Bounds.md`](./Bounds.md) §6 (Chorus leg ≈ 2–4 sessions; ranked
  behind primitive instantiation and the (M-frame) checker, ahead of
  L2S on near-term value-per-effort).

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
| `cast_commit` = `commit_sign_pos` + `commit_sign_neg` + `cast_fast_commit` | Deferred | A/B `#check_vc cast_commit agreement_pos` ran in 1420 s wall / 245 s user CPU. Most likely the wall-time blowup was discharger-scheduler contention rather than genuine SMT cost (245 s of CPU against 1 420 s of wall). With the two new `commit_pos_sig_unique` / `commit_pos_sig_neg_excl` lemmas now stated explicitly, a re-test via `#check_action cast_commit` (bundles VCs under one awaiter — less contention surface) is the right next experiment. If that's clean, integrate. |
| `fb_vote` = `fb_sign_pos` + `fb_sign_neg` + `cast_fallback_vote` | Not attempted | Bulk update body is more complex than vote/cast_commit because each per-proposer fb-sign decision depends on an *existential* quorum witness (`∃ q : nodeset, …`). Plausibly tractable as an atomic action but the quantifier shape is genuinely different. Worth its own A/B. |
| `commit` = `commit_assign_pos` + `commit_assign_neg` + `finalize_commit` | Not attempted | Same shape as `cast_commit`; touches `agreement_pos` directly. If the `cast_commit` re-test goes well after the lemma additions, this is the natural next candidate. |
| `mvba` = `on_mvba_decide_pos` + `on_mvba_decide_neg` + `mvba_terminate` | Not attempted — and since 2026-09-10 deliberately *not* wanted | The decision handlers transport a correct validator's decision off the abstract MVBA state entry by entry (`MvbaPlan.md` §6: per-entry handlers keep every update a monotone `:= true` and let `#gen_proof_files` map proof files one for one); a bulk transport of the whole vector would be one action with a `∀ J`-quantified update over the two projections. Possible, but it trades the monotone-update shape for one fewer action. |

The pattern for each is the same as `vote`/`cast_commit`: replace the
three actions with one atomic action whose body has universally-quantified
bulk updates on the per-proposer signature relations, with auxiliary
uniqueness/exclusion invariants stated explicitly so cvc5 has direct
hypotheses instead of multi-step chains.

### Measuring a candidate

Read the A/B numbers above with care: they were taken when every `#check_vc`
build still paid the module's full DSL elaboration, and concurrent check
commands contended for one discharger scheduler, so fixed cost dominates them.

The recipe now is to put `#prove_vc Chorus <action> <property> by …` cells in
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
  placeholder. `ChorusDesign.md` §3.4 and §9.
* **Epochs and proposer rotation**, and deriving `is_proposer` from a VRF
  rather than taking it as immutable configuration. `ChorusDesign.md` §9
  item 2.
* **Monitor coverage** — positive-path emission, per-message emission at the
  network boundary, multi-slot (Conductor) traces, Byzantine
  validate-vs-admit tagging. [`Monitor.md`](./Monitor.md) §8.

## Paper alignment

The verified surface is unchanged and mechanically re-checkable; the paper's
*implementation* track has moved a long way from it. Both, with the audit
that established them, are [`PaperAlignment.md`](./PaperAlignment.md). Three
items fall out of the 2026-09-03 audit, all documentary except the first:

* **Re-check the `EquivCert` build guard** once the paper side settles
  whether witness chunks are intended to supersede `line:fb-build-equiv`.
  `FallbackReceipt.lean`'s `equiv_available` mirrors the published guard; if
  the supplement's rule wins, the branch reassignment and the totality
  counting argument both need re-reading.
  [`PaperAlignment.md`](./PaperAlignment.md) §3.
* Cite `sec:domain-separation` where the network relations rely on
  message-type non-confusability — the paper now names an assumption the
  model has always made structurally (one relation per message type).
  Candidate homes: [`ChorusDesign.md`](./ChorusDesign.md) §3.5's relation
  table and [`Architecture.md`](./Architecture.md) §4 item 3.
* Record ChunkSync and `Δ_sync` alongside the (F-justice) justification for
  `redisseminate_chunk`: the implementation dropped
  `line:fb-redisseminate`, so the paper-side discharge of that fairness
  assumption now runs through a mechanism the supplement calls
  liveness-critical and has not specified.

## Verification-pipeline work

Mostly not tracked here. The tooling this project depends on is the public
Veil fork (see [`Dependencies.md`](./Dependencies.md)); anything to be
improved about it belongs in that repository. The one measurement worth
carrying forward is recorded in [`Architecture.md`](./Architecture.md) §7.

Two items are exceptions, because they are this project's to ask for.

**Asks from the contract-composition work (2026-09-08)** — recorded with
reproductions in the fork's roadmap (`VEIL-REVIEW.md` § "From the Cadence
contract-composition work", codes L9–L15 / M13–M14 / H6).

*The seven L-items landed in the fork on 2026-09-08 and were taken up here in
the 2026-09-09 Veil bump* ([`History.md`](./History.md),
[`Dependencies.md`](./Dependencies.md) §3 and §7): `#gen_theorems` now emits
the per-action preservation lemmas, so one `#gen_composition` per module
replaced the hand-assembled inductions and the explicit-instance macros of
`Cadence/Composition.lean` (L14); the `trSimp` simp set replaced the three
per-action lemma lists (L15); the abstract state's `Inhabited` instance is
derived rather than hand-written (L11); a non-first-order field of an
instantiated class is now an error naming class and field, with
`veil_smt_ignore` as the escape hatch (L10); the trace pipeline's binders are
hygienic, retiring the `st'` rule (L12); and an `assumption` over mutable
state gets a readable rejection (L13). What L9 (recursive destructuring of
instantiated classes before SMT) enables — the contracts sharing one
transition-system skeleton, and the temporal level as a class over the safety
instance instead of a residual structure — has landed in full. The skeleton
was briefly held back by fork bug L17 (`sat trace` mis-destructured an
instantiated class with an `extends` parent), which this work found and the
fork fixed on 2026-09-10. See [`History.md`](./History.md).

*M13 and M14 landed in the fork on 2026-09-10 and were taken up here the same
day* ([`History.md`](./History.md), [`Dependencies.md`](./Dependencies.md) §3):
generated step lemmas (`veil.gen.stepLemmas`) replaced most of the `StepFacts`
sections with one-line applications, and `step_property` turned the two facts
that need the guards or the invariants at the pre-state — the Conductor's
Monotonicity and Chorus's frozen entries — into SMT-checked cells. L17 (the
trace path with `extends` parents) landed with them, and the shared
transition-system skeleton went in on top.

Still open: **H6**, and the (M-frame) syntactic audit above — for which M13 is
now the missing half, since the contract is a set of frame facts about the
`msg_*` relations and those are exactly what it emits.


* ~~Re-include the Bool-atom fold.~~ **Done 2026-09-02** — ported forward in
  the fork, pinned, and validated cold; see
  [`History.md`](./History.md). The one residual is
  `Cadence/Chorus/Proofs/Vote.lean`, which still opts out because its
  `fastqc_complete_implies_mvba_evidence` cell diverges under the folded
  query shape. That costs ~28 s of every warm re-validation (its batch runs
  42 s against 13–15 s for the others) and leaves one ~30 MB olean. Worth
  revisiting if the cell can be made folded-shape-tractable, e.g. as a manual
  cell.
* ~~The ProofWidgets library gap.~~ **Fixed upstream in ProofWidgets
  v0.0.106**; this tree carries v0.0.105 because Mathlib v4.32.0 pins it, so
  it clears with the next Mathlib bump. Nothing to carry, and it only ever
  mattered to a consumer that precompiles — which on current evidence is not
  worth doing ([`Dependencies.md`](./Dependencies.md)).
