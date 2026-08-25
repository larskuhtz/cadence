# Open items

Everything *claimed* in this repository is proven and axiom-pinned — these
are places the development could go further, not gaps in what is asserted.
The authoritative, numbered list of Chorus-side open items is
[`ChorusDesign.md`](./ChorusDesign.md) §9 (and §§10.1–10.3 for the bigger
lifts); this file collects the cross-cutting ones and the model-hygiene
wishlist.

## Soundness — guarding against vacuous claims

These are the items that would most change an auditor's confidence, so they
come first.

* **Instantiate the primitive class stack end-to-end.** The Byzantine-quorum
  interface is already discharged for the concrete `byzNodeSetFin` family
  (see [`../Cadence/ByzQuorum.lean`](../Cadence/ByzQuorum.lean)), which is why
  it is *not* on the assumption list in
  [`Architecture.md`](./Architecture.md) §4. `MVBA` and `ThresholdIBE` are
  still axiomatic classes with no model instance: producing one would
  demonstrate the axiom set is satisfiable rather than accidentally
  contradictory. `ChorusDesign.md` §9 item 1.
* **Non-vacuity of the safety claims.** `Cadence.lean` and `Conductor.lean`
  carry in-build `sat trace` reachability witnesses so that the properties
  are not vacuously true (if finalization were unreachable, agreement would
  hold trivially). The receipt layer additionally has an exhaustive
  `#model_check` whose explored graph is checked to contain proposing runs.
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
  [`Architecture.md`](./Architecture.md) §4 into a machine check.
  `ChorusDesign.md` §9 item 3. **Priority raised by the 2026-08 external
  audit** (its Finding 2): the hand audit's own record had mis-tabled two
  relations, which is exactly the failure mode a machine check removes. Design
  requirement from the same finding: the check must *classify* every
  occurrence (positive / self-row / documented exception — the categories of
  `ChorusDesign.md` §3.1.1) rather than merely reject, so sound negative reads
  are reported and acknowledged instead of slipping past a reject-only lint.

## Liveness

The fair-progress *safety content* is machine-checked; the temporal glue is
not ([`ChorusDesign.md`](./ChorusDesign.md) §7 is what the Chorus encoding
does, [`Liveness.md`](./Liveness.md) the approach to closing the gap).
Remaining:

* Full liveness-to-safety, so that the (F-justice)/(F-byz)/(A-mvba)
  meta-axioms become premises of a Lean theorem rather than named
  assumptions. This is the single largest reduction of
  [`Architecture.md`](./Architecture.md) §4 available.
* Actions are annotated with their fairness class in prose only; Veil has no
  surface syntax for it. The fork's liveness design doc sketches what that
  syntax should be ([`Liveness.md`](./Liveness.md) §1 points to it).
* Reachability-directed trace generation, so that non-vacuity witnesses for
  the *progress* invariants can be produced mechanically rather than written
  by hand.
* Decompose (A-mvba). It currently collapses MVBA termination, partial
  synchrony and quorum availability into one black-box assumption; splitting
  it into a GST phase marker, per-action quorum-availability premises, and
  the probability-1 argument as a separate paper proof would make the
  model-to-reality gap legible item by item.

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
| `mvba` = `mvba_decide_pos` + `mvba_decide_neg` + `mvba_terminate` | Not attempted | The MVBA per-proposer decisions are gated by certificate-evidence preconditions (`vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)`, etc., post-Build-#10) — combining into one atomic action means the precondition becomes "every proposer has *some* evidence", which is the `mvba_terminate` precondition today. Should compose cleanly. |

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

## Verification-pipeline work

Not tracked here. The tooling this project depends on is the public Veil fork
(see [`Dependencies.md`](./Dependencies.md)); anything to be improved about it
belongs in that repository. The one measurement worth carrying forward is
recorded in [`Architecture.md`](./Architecture.md) §7.
