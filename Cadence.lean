-- Cadence — the audit root. The module documentation follows the imports,
-- which Lean requires to come first.

-- The per-slot consensus leg.
import Cadence.Chorus.Certify
import Cadence.Chorus.Compose
import Cadence.Chorus.Pigeonhole
import Cadence.Chorus.Counting
import Cadence.Chorus.Progress
import Cadence.Chorus.Termination
import Cadence.Chorus.Witness

-- The orchestration / pipelining leg, and the composed system.
import Cadence.Composition
import Cadence.System

-- The fallback receipt/propose leg: the shipped design, verified.
import Cadence.FallbackReceipt.Totality

-- The MVBA leg: the leader-based instantiation of the paper repository's
-- internal supplement, its contract (the safety fragment, the timed temporal
-- level, and the two joined), and the mutation test that refutes the
-- instantiation without its lock check, and the model showing the liveness
-- theorems' premises jointly satisfiable.
import Cadence.Mvba.Certify
import Cadence.Mvba.Compose
import Cadence.Mvba.Liveness
import Cadence.Mvba.Temporal
import Cadence.Mvba.Witness
import Cadence.Mvba.NoLock

/-!
# Cadence — the audit root

This module is the entry point for auditing the formal verification of the
**Cadence** BFT consensus protocol (<https://www.category.xyz/cadence>;
`arXiv:2607.02275v2`). It imports every finished result of the
development and, for each one, re-derives its **axiom footprint** as a
build-checked pin. If any end theorem ever came to depend on an extra axiom
— a `sorry` (`sorryAx`), a trusted solver verdict standing in as an axiom, a
hand-added assumption — this file would stop compiling.

Reading it top to bottom answers one question: *what exactly has been
proven, and what is it proven from?* [README.md](README.md) is the
orientation document; the verification architecture, the methods, and the
complete inventory of what is **not** in Lean are
[docs/Architecture.md](docs/Architecture.md).

## The end results

Each entry is the result, the file its statement lives in, and what it says.

* **`Chorus.invariants_of_reachable`** ([Chorus/Certify.lean](Cadence/Chorus/Certify.lean)) — every
  reachable state of the per-slot consensus satisfies all its declared safety
  properties and invariants (the count is pinned by `#veil_status Chorus` in
  that file)
* **`Chorus.slotConsensusSafety`** ([Chorus/Compose.lean](Cadence/Chorus/Compose.lean)) — Chorus ⊨
  `SlotConsensusSafety` — the state-level fragment of the paper's per-slot
  module contract (agreement, slot safety, proposal inclusion, and the
  monotonicity of finalization), for every slot's copy of the model and for
  every MVBA satisfying `MVBASafety` (Chorus's own class constraint); this is
  the object the glue consumes as its `sc` constraint
* **`Chorus.slotConsensus_of_temporal`** ([Chorus/Compose.lean](Cadence/Chorus/Compose.lean)) —
  given an instance of `SlotConsensusTemporal` **at the proven fragment** —
  the participation interface as contract fields (the model has it as
  actions and state), the admissible-run model, Termination and
  Quiescence — Chorus is a full `SlotConsensus`. This development has no such
  instance, and that is the statement of what is *not* proven about Chorus as
  a slot consensus: the class's own fields, over Chorus's own transition
  system, restated nowhere. Hiding's protocol half is first-order and is
  proven in the fragment
* **`Chorus.evidence_pigeonhole_of_reachable`**
  ([Chorus/Pigeonhole.lean](Cadence/Chorus/Pigeonhole.lean)) — `2f+1` honest fallback entries always
  yield certified per-proposer evidence, for **every** `n = 3f+1` (the
  counting step of the fallback liveness branch)
* **`Chorus.fbcert_of_honest_fallback_votes`,
  `Chorus.fbcommitqc_of_honest_commit_votes`**
  ([Chorus/Counting.lean](Cadence/Chorus/Counting.lean)) — certificate formation: once every honest
  validator has cast its fallback (resp. fallback commit) vote, `FBCert`
  (resp. `fbCommitQC`) exists — the honest population is itself the quorum,
  for **every** `n = 3f+1`
* **`Chorus.commitqc_of_honest_fast_dominant`**
  ([Chorus/Counting.lean](Cadence/Chorus/Counting.lean)) — a supermajority of honest fast commit
  votes yields, per proposer, a commitQC from honest votes alone (the counting
  step of the fast-dominant liveness branch), for **every** `n = 3f+1`
* **`Chorus.progress_dichotomy_of_saturation`**
  ([Chorus/Progress.lean](Cadence/Chorus/Progress.lean)) — the liveness case split as **one
  theorem**: in any reachable state where every honest validator has cast its
  path vote, either commitQCs exist for every proposer from honest votes
  alone, or the MVBA stands invoked with certified evidence for every proposer
  (verbatim the decision handlers' bridge `require` and `mvba_propose`'s
  validity guards), for **every** `n = 3f+1`
* **`Chorus.build_totality_of_reachable`** ([Chorus/Counting.lean](Cadence/Chorus/Counting.lean)) —
  any supermajority of per-proposer fallback entries — arbitrary
  honest/Byzantine mix, i.e. a validator's `2f+1` accepted receipts — yields a
  buildable meta-block entry (FallbackQC or EquivCert) for every proposer: the
  state-level half of "every correct validator can propose", for **every** `n
  = 3f+1`
* **`Chorus.termination`** ([Chorus/Termination.lean](Cadence/Chorus/Termination.lean)) — **Chorus
  terminates**: every correct validator finalizes the slot, in every run
  satisfying five premises, for **every** `n = 3f+1`, at the configuration
  the composed system runs (`Cadence.chorusTheory`, with the `Mvba` model
  as its MVBA). The untimed form of `lemma:chorus-termination`, with the
  `5Δ + ℓ_MVBA` bound erased. The premises, each a named definition in
  [Chorus/Liveness.lean](Cadence/Chorus/Liveness.lean) and none of them an axiom:
  * `FJustice`: correct validators' actions are scheduled fairly, for the
    messages of correct senders (nothing is asked of a Byzantine
    validator's messages);
  * `MvbaAdmissible`: the MVBA's steps inside the run are scheduled as
    `Mvba.termination` requires;
  * `ValidBridge`: the MVBA's validity check agrees with Chorus's
    certificates — the cryptographic seam between the two models, not a
    fairness assumption;
  * `AllParticipate`: every correct validator eventually invokes
    `participate()`;
  * `NoAbandonBeforeFinalizing`: no correct validator invokes `abandon()`
    before it has finalized.

  The last two are the caller's conditions, exactly the antecedents of the
  contract's `SlotConsensusTemporal.termination`; within Cadence the glue
  meets them. The MVBA's termination is not assumed: the proof applies
  `Mvba.termination` to the run's MVBA steps. Hypotheses: at most `f`
  Byzantine validators among `Fin n`, `ViewOrderEnum`.
  `FJustice` is weak fairness over plain enabledness: an action enabled
  from some point on, whose messages came from correct validators,
  eventually fires. Every fair action of the model fires
  once (`Chorus.justice_enabledMove`,
  [Chorus/Liveness.lean](Cadence/Chorus/Liveness.lean)), so this is the
  same premise as weak fairness over state-changing steps
  (`Chorus.fJustice_iff_move`).
  [Liveness.md](docs/Liveness.md) §2 explains each premise in short
* **`Chorus.termination_premises_satisfiable`,
  `Chorus.timedTermination_premises_satisfiable`,
  `Chorus.totality_premises_satisfiable`**
  ([Chorus/Witness.lean](Cadence/Chorus/Witness.lean)) — **the Chorus
  liveness claims are not vacuous**: one concrete model (four validators,
  one Byzantine and silent, one proposer, clock `ℕ`, `Δ = 1`, `δ = 0`) and
  one run, in which everyone finalizes on the fast path and then abandons,
  meet every premise of `Chorus.termination` at once, every premise of the
  timed `TimedTerminationClaim` at the system's MVBA, and every premise of
  `TotalityClaim` together with its antecedent. The timed claims are stated
  ([Chorus/Schedule.lean](Cadence/Chorus/Schedule.lean)) and not yet proven.
  [Bounds.md](docs/Bounds.md) §6.4.5 is the premise-by-premise ledger
* **`Conductor.orchestratorSafety`** ([Composition.lean](Cadence/Composition.lean)) — Conductor
  ⊨ `OrchestratorSafety` — the state-level fragment of the paper's
  slot-scheduling module contract (open-prefix agreement, Monotonicity,
  Integrity's at-most-once half, the observables' monotonicity and frames),
  every field proven from the Conductor's own transition system; the object
  the glue consumes as its `orch` constraint
* **`Conductor.orchestrator_of_temporal`** ([Composition.lean](Cadence/Composition.lean)) —
  given an instance of `OrchestratorTemporal` **at the proven fragment** —
  Totality, `B`-Boundedness, `R`-Recovery and the admissible-run model — the
  Conductor is a full `Orchestrator`. This development has no such instance,
  and that is the statement of what is *not* proven about the Conductor as an
  orchestrator. Integrity's timing half is first-order and is proven in the
  fragment
* **`Cadence.positional_log_safety`** ([Composition.lean](Cadence/Composition.lean)) — MCP
  Safety in the paper's positional form — two correct validators never
  disagree on the log entry at a given position — for the glue over *any*
  orchestrator and slot consensus satisfying the two `…Safety` contracts
* **`Cadence.system_positional_log_safety`** ([System.lean](Cadence/System.lean)) — the
  same, **for the composed system**: the glue running the Conductor's and
  Chorus's own transition systems, Chorus running the `Mvba` model's as its
  MVBA (`Mvba.mvbaSafety` fills Chorus's class constraint; its full
  contract is proven, `Mvba.mvbaFull` below). The one contract hypothesis
  left is `ACSSafety`, the ACS primitive the Conductor runs once per window;
  beyond it, what is assumed is the three modules' configurations and that
  the Conductor and Chorus agree on who is Byzantine
* **`FallbackReceipt.invariants_of_reachable`**
  ([FallbackReceipt/Certify.lean](Cadence/FallbackReceipt/Certify.lean)) — every reachable state of the
  fallback receipt/propose layer satisfies its declared invariants
* **`FallbackReceipt.build_totality_of_reachable`**
  ([FallbackReceipt/Totality.lean](Cadence/FallbackReceipt/Totality.lean)) — an honest validator can always
  build a *valid* fallback meta-block, for **every** `n = 3f+1`
* **`Mvba.invariants_of_reachable`** ([Mvba/Certify.lean](Cadence/Mvba/Certify.lean)) — every
  reachable state of the leader-based MVBA instantiation ([Mvba.lean](Cadence/Mvba.lean)
  — the protocol of the paper repository's *internal supplement*, pinned to a
  paper-repository commit in the model's header, not yet part of the published
  paper) satisfies all its declared safety properties and invariants
* **`Mvba.reachable_agreement`, `Mvba.reachable_integrity`,
  `Mvba.reachable_external_validity`** ([Mvba/Certify.lean](Cadence/Mvba/Certify.lean)) — the
  three safety properties of `mod:mvba` at every reachable state — the
  supplement's `thm:agreement` at the entries level, integrity (a correct
  validator decides at most once), `lem:external-validity`
* **`Mvba.mvbaFull`** ([Mvba/Temporal.lean](Cadence/Mvba/Temporal.lean)) — **Mvba ⊨ `MVBA`,
  the whole contract**, and the MVBA the composed system runs: its safety
  fragment is by `rfl` `Mvba.mvbaSafety`, the instance [System.lean](Cadence/System.lean)
  plugs into Chorus (`Mvba.mvbaFull_toSafety`). It joins the two rows
  below through `mvba_of_temporal`
* **`Mvba.mvbaSafety`** ([Mvba/Compose.lean](Cadence/Mvba/Compose.lean)) — Mvba ⊨ `MVBASafety` —
  the state-level fragment of the paper's MVBA module contract (agreement,
  integrity, external validity, the monotonicity of `decided`, the inputs,
  their observables and one-step Quiescence), every field proven from the
  model's own transition system ([MvbaPlan.md](docs/MvbaPlan.md) §6)
* **`Mvba.mvbaTemporal`** ([Mvba/Temporal.lean](Cadence/Mvba/Temporal.lean)) — **Mvba ⊨
  `MVBATemporal`**: `ℓ_MVBA`-Termination with an explicit `ℓ`, the
  supplement's `O(fΔ)` at `k = f + 1`. If every correct validator proposes a
  valid value by `t` and none abandons early, every correct validator
  decides by `max(t, GST) + ℓ`, in every admissible run. The admissible runs
  are those with a labelling satisfying the timing model of
  [Mvba/Schedule.lean](Cadence/Mvba/Schedule.lean): bounded weak fairness after GST under the
  supplement's network — a local step within `δ`, a message sent at or
  after GST by a correct validator and retained within `Δ`, a
  retransmitted one (timeouts, `ViewTC_i`, a decided `CommitQC`) within
  `Δ + ρ` — a punctual view timer, and availability within `Δ_sync`. Such runs exist (`Mvba.admissible_exists`). Termination is
  `Mvba.timed_termination`, from `Mvba.bounded_termination`
  ([Mvba/BoundedTermination.lean](Cadence/Mvba/BoundedTermination.lean)). No field is weakened. The
  hypotheses, none of them an axiom:
  * finitely many validators (`Fintype node`);
  * `ByzNodeSetHonestQuorum` (a supermajority of correct validators) and
    `ViewOrderEnum`;
  * (A-leader-rotation-k), `LeaderRotation`: a correct leader in every `k`
    consecutive views;
  * a schedule whose timeout is capped and eventually exceeds the chain's
    latency (`Schedule`);
  * a time theory that is a cancellative, Archimedean, linearly ordered
    monoid.
* **`Mvba.termination`** ([Mvba/Liveness.lean](Cadence/Mvba/Liveness.lean)) — **the same
  statement, untimed**: every correct validator eventually decides. Its
  premises are fair scheduling for correct senders, the supplement's caller
  conditions (all correct validators propose, none is abandoned before
  deciding, and a correct validator's decided certificate is handed on,
  (F-relay)), (F-avail), and (A-viewsync): the view timer stated as ordering
  constraints (timers do fire; the good view's timer waits for a correct
  validator's decision), so the theorem reads
  *given enough time, the protocol decides*. The timed premises imply
  (A-viewsync) (`Mvba.aViewSync_of_sync`). Hypotheses: finitely many
  validators, `ByzNodeSetHonestQuorum`, `ViewOrderEnum`. `FJustice` is
  weak fairness over plain enabledness. Every fair action of the model
  fires once (`Mvba.enabledMove_of_enabled`,
  [Mvba/Liveness.lean](Cadence/Mvba/Liveness.lean)), so this is the same
  premise as weak fairness over state-changing steps
  (`Mvba.fJustice_iff_move`; `Mvba.boundedFair_iff_move` and
  `Mvba.boundedFairWhile_iff_move` for the timed clauses). [Liveness.md](docs/Liveness.md)
  §2.1 explains the premise in short
* **`Mvba.timedTermination_premises_satisfiable`,
  `Mvba.termination_premises_satisfiable`** ([Mvba/Witness.lean](Cadence/Mvba/Witness.lean)) — **the
  two rows above are not vacuous**: one concrete model (four validators, one
  Byzantine, clock `ℕ`, the paper's fixed timeout) and one run meet every
  premise of `Mvba.timed_termination` at once, and the same run meets every
  premise of `Mvba.termination`. [Bounds.md](docs/Bounds.md) §6.3 is the
  premise-by-premise ledger

Two further build-checked claims are pinned where they are made, because
their form is not an axiom footprint:

* **Completeness of the per-VC evidence.** `#veil_status Chorus` (in
  [Chorus/Certify.lean](Cadence/Chorus/Certify.lean)), `#veil_status FallbackReceipt` (in
  [FallbackReceipt/Certify.lean](Cadence/FallbackReceipt/Certify.lean)) and `#veil_status Mvba` (in
  [Mvba/Certify.lean](Cadence/Mvba/Certify.lean)) walk each model's registry of
  verification conditions and report, per condition, whether a real,
  statement-matching, kernel-checked theorem is in scope. All three are
  pinned at every condition real, over the three standard axioms. That is the claim "nothing here is stubbed", as a command rather
  than as prose.
* **The MVBA's lock check is load-bearing.** [Mvba/NoLock.lean](Cadence/Mvba/NoLock.lean)
  pins the model checker's *counterexample* to the MVBA instantiation with
  the `Pre-Prepare` handler's lock check removed — two correct validators
  deciding different vectors — found on a restriction of that mutant every
  run of which is a run of the mutant. It is the mutation test of the
  instantiation's invariants: they are not merely true but needed. That
  file builds only if the violation is still found, verbatim.

## What this module does not import

The model-conformance monitor ([Cadence/Monitor](Cadence/Monitor)) is a separate concern — it
checks whether a real implementation trace is *simulated by* the model, which
is neither a proof nor part of any theorem's trust base. Its modules each
carry a `main` for `lean --run`, so they cannot share one import closure;
`lake build` still elaborates them. See [docs/Monitor.md](docs/Monitor.md).

## The trust base, re-derived

Each pin below is a `#guard_msgs` guard around Lean's own `#print axioms`:
the build fails unless the theorem depends on *exactly* `propext`,
`Classical.choice` and `Quot.sound` — the three standard axioms of Lean's
classical logic, and nothing else. In particular **no** `sorryAx` (which is
what an admitted or stubbed proof shows up as) and no project-specific axiom.

The same pins are made at each result's own site; repeating them here is
deliberate, so that an auditor can read the whole trust base off one page.
Anyone can re-derive them by hand: drop the `#guard_msgs in` line and run
`#print axioms <name>` in a scratch file importing this module.

Note what these pins do *and do not* say. They say: the theorem's proof term
is complete and kernel-checked from Lean's axioms. They do **not** say that
the *statement* is the right one — that the model faithfully formalises the
protocol, and that the assumptions the statements are conditioned on are
sound, is the part an auditor has to read, and it is inventoried in
[docs/Architecture.md](docs/Architecture.md) §4.
-/

/--
info: 'Chorus.invariants_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.invariants_of_reachable

/--
info: 'Chorus.slotConsensusSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensusSafety

/--
info: 'Chorus.slotConsensus_of_temporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensus_of_temporal

/--
info: 'Chorus.evidence_pigeonhole_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.evidence_pigeonhole_of_reachable

/--
info: 'Chorus.fbcert_of_honest_fallback_votes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fbcert_of_honest_fallback_votes

/--
info: 'Chorus.fbcommitqc_of_honest_commit_votes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fbcommitqc_of_honest_commit_votes

/--
info: 'Chorus.commitqc_of_honest_fast_dominant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.commitqc_of_honest_fast_dominant

/--
info: 'Chorus.progress_dichotomy_of_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.progress_dichotomy_of_saturation

/--
info: 'Chorus.build_totality_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.build_totality_of_reachable

/--
info: 'Chorus.termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.termination

/--
info: 'Chorus.justice_enabledMove' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.justice_enabledMove

/--
info: 'Chorus.fJustice_iff_move' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fJustice_iff_move

/--
info: 'Chorus.termination_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.termination_premises_satisfiable

/--
info: 'Chorus.timedTermination_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.timedTermination_premises_satisfiable

/--
info: 'Chorus.totality_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.totality_premises_satisfiable

/--
info: 'Conductor.orchestratorSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.orchestratorSafety

/--
info: 'Conductor.orchestrator_of_temporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.orchestrator_of_temporal

/--
info: 'Cadence.positional_log_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.positional_log_safety

/--
info: 'Cadence.system_positional_log_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.system_positional_log_safety

/--
info: 'FallbackReceipt.invariants_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FallbackReceipt.invariants_of_reachable

/--
info: 'FallbackReceipt.build_totality_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FallbackReceipt.build_totality_of_reachable

/--
info: 'Mvba.invariants_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.invariants_of_reachable

/--
info: 'Mvba.reachable_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.reachable_agreement

/--
info: 'Mvba.reachable_integrity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.reachable_integrity

/--
info: 'Mvba.reachable_external_validity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.reachable_external_validity

/--
info: 'Mvba.mvbaSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaSafety

/--
info: 'Mvba.mvba_of_temporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvba_of_temporal

/--
info: 'Mvba.termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.termination

/--
info: 'Mvba.enabledMove_of_enabled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.enabledMove_of_enabled

/--
info: 'Mvba.fJustice_iff_move' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.fJustice_iff_move

/--
info: 'Mvba.boundedFair_iff_move' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.boundedFair_iff_move

/--
info: 'Mvba.boundedFairWhile_iff_move' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.boundedFairWhile_iff_move

/--
info: 'Mvba.mvbaTemporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaTemporal

/--
info: 'Mvba.timed_termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.timed_termination

/--
info: 'Mvba.admissible_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.admissible_exists

/--
info: 'Mvba.bounded_termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.bounded_termination

/--
info: 'Mvba.aViewSync_of_sync' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.aViewSync_of_sync

/--
info: 'Mvba.mvbaFull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaFull

/--
info: 'Mvba.timedTermination_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.timedTermination_premises_satisfiable

/--
info: 'Mvba.termination_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.termination_premises_satisfiable
