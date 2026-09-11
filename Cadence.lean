/-
Cadence — the audit root.  (Plain comment, not a module docstring: Lean
requires `import` lines to come before any command.  The module
documentation follows the imports below.)
-/

-- The per-slot consensus leg.
import Cadence.Chorus.Certify
import Cadence.Chorus.Compose
import Cadence.Chorus.Pigeonhole
import Cadence.Chorus.Counting
import Cadence.Chorus.Progress

-- The orchestration / pipelining leg, and the composed system.
import Cadence.Composition
import Cadence.System

-- The fallback receipt/propose leg, both directions: the shipped design
-- verified, and the pre-fix design refuted.
import Cadence.FallbackReceipt.Totality
import Cadence.FallbackReceipt.PreFix

-- The MVBA leg: the leader-based instantiation of the paper repository's
-- internal supplement, its contract instance, and the mutation test that
-- refutes the instantiation without its lock check.
import Cadence.Mvba.Certify
import Cadence.Mvba.Compose
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
proven, and what is it proven from?* The prose story is in
[README.md](./README.md); the verification architecture, the methods, and the
complete inventory of what is **not** in Lean is
[docs/Architecture.md](./docs/Architecture.md).

## The end results

| Result | Statement lives in | Reads as |
|---|---|---|
| `Chorus.invariants_of_reachable` | `Cadence/Chorus/Certify.lean` | every reachable state of the per-slot consensus satisfies all its declared safety properties and invariants (the count is pinned by `#veil_status Chorus` in that file) |
| `Chorus.slotConsensusSafety` | `Cadence/Chorus/Compose.lean` | Chorus ⊨ `SlotConsensusSafety` — the state-level fragment of the paper's per-slot module contract (agreement, slot safety, proposal inclusion, and the monotonicity of finalization), for every slot's copy of the model and for every MVBA satisfying `MVBASafety` (Chorus's own class constraint); this is the object the glue consumes as its `sc` constraint |
| `Chorus.slotConsensus_of_temporal` | `Cadence/Chorus/Compose.lean` | given an instance of `SlotConsensusTemporal` **at the proven fragment** — the participation interface, the admissible-run model, Termination and Quiescence — Chorus is a full `SlotConsensus`. This development has no such instance, and that is the statement of what is *not* proven about Chorus as a slot consensus: the class's own fields, over Chorus's own transition system, restated nowhere. Hiding's protocol half is first-order and is proven in the fragment |
| `Chorus.evidence_pigeonhole_of_reachable` | `Cadence/Chorus/Pigeonhole.lean` | `2f+1` honest fallback entries always yield certified per-proposer evidence, for **every** `n = 3f+1` (the counting step of the fallback liveness branch) |
| `Chorus.fbcert_of_honest_fallback_votes`, `Chorus.fbcommitqc_of_honest_commit_votes` | `Cadence/Chorus/Counting.lean` | certificate formation: once every honest validator has cast its fallback (resp. fallback commit) vote, `FBCert` (resp. `fbCommitQC`) exists — the honest population is itself the quorum, for **every** `n = 3f+1` |
| `Chorus.commitqc_of_honest_fast_dominant` | `Cadence/Chorus/Counting.lean` | a supermajority of honest fast commit votes yields, per proposer, a commitQC from honest votes alone (the counting step of the fast-dominant liveness branch), for **every** `n = 3f+1` |
| `Chorus.progress_dichotomy_of_saturation` | `Cadence/Chorus/Progress.lean` | the liveness case split as **one theorem**: in any reachable state where every honest validator has cast its path vote, either commitQCs exist for every proposer from honest votes alone, or the MVBA stands invoked with certified evidence for every proposer (verbatim the decision handlers' bridge `require` and `mvba_propose`'s validity guards), for **every** `n = 3f+1` |
| `Chorus.build_totality_of_reachable` | `Cadence/Chorus/Counting.lean` | any supermajority of per-proposer fallback entries — arbitrary honest/Byzantine mix, i.e. a validator's `2f+1` accepted receipts — yields a buildable meta-block entry (FallbackQC or EquivCert) for every proposer: the state-level half of "every correct validator can propose", for **every** `n = 3f+1` |
| `Conductor.orchestratorSafety` | `Cadence/Composition.lean` | Conductor ⊨ `OrchestratorSafety` — the state-level fragment of the paper's slot-scheduling module contract (open-prefix agreement, Monotonicity, Integrity's at-most-once half, the observables' monotonicity and frames), every field proven from the Conductor's own transition system; the object the glue consumes as its `orch` constraint |
| `Conductor.orchestrator_of_temporal` | `Cadence/Composition.lean` | given an instance of `OrchestratorTemporal` **at the proven fragment** — Totality, `B`-Boundedness, `R`-Recovery and the admissible-run model — the Conductor is a full `Orchestrator`. This development has no such instance, and that is the statement of what is *not* proven about the Conductor as an orchestrator. Integrity's timing half is first-order and is proven in the fragment |
| `Cadence.positional_log_safety` | `Cadence/Composition.lean` | MCP Safety in the paper's positional form — two correct validators never disagree on the log entry at a given position — for the glue over *any* orchestrator and slot consensus satisfying the two `…Safety` contracts |
| `Cadence.system_positional_log_safety` | `Cadence/System.lean` | the same, **for the composed system**: the glue running the Conductor's and Chorus's own transition systems, Chorus running the `Mvba` model's as its MVBA (`Mvba.mvbaSafety` fills Chorus's class constraint). No contract hypothesis remains; what is assumed is the three modules' configurations and that the Conductor and Chorus agree on who is Byzantine |
| `FallbackReceipt.invariants_of_reachable` | `Cadence/FallbackReceipt/Certify.lean` | every reachable state of the fallback receipt/propose layer satisfies its declared invariants |
| `FallbackReceipt.build_totality_of_reachable` | `Cadence/FallbackReceipt/Totality.lean` | an honest validator can always build a *valid* fallback meta-block, for **every** `n = 3f+1` |
| `Mvba.invariants_of_reachable` | `Cadence/Mvba/Certify.lean` | every reachable state of the leader-based MVBA instantiation (`Cadence/Mvba.lean` — the protocol of the paper repository's *internal supplement*, pinned to a paper-repository commit in the model's header, not yet part of the published paper) satisfies all its declared safety properties and invariants |
| `Mvba.reachable_agreement`, `Mvba.reachable_integrity`, `Mvba.reachable_external_validity` | `Cadence/Mvba/Certify.lean` | the three safety properties of `mod:mvba` at every reachable state — the supplement's `thm:agreement` at the entries level, integrity (a correct validator decides at most once), `lem:external-validity` |
| `Mvba.mvbaSafety` | `Cadence/Mvba/Compose.lean` | Mvba ⊨ `MVBASafety` — the state-level fragment of the paper's MVBA module contract (agreement, integrity, external validity, the monotonicity of `decided`), every field proven from the model's own transition system. The object Chorus consumes as its `mvba` constraint, plugged in by `Cadence/System.lean` (`docs/MvbaPlan.md` §6) |
| `Mvba.mvba_of_temporal` | `Cadence/Mvba/Compose.lean` | given an instance of `MVBATemporal` **at the proven fragment** — the clock, the admissible-run model and `ℓ_MVBA`-Termination — Mvba is a full `MVBA`. This development has no such instance; those four fields are the whole of what is *not* proven about the instantiation, since the inputs (`propose`, `abandon`), their observables, effects and frames, and **Quiescence** in one-step form are all proven into the fragment. The smallest gap of the three implementations |

Two further build-checked claims are pinned where they are made, because
their form is not an axiom footprint:

* **Completeness of the per-VC evidence.** `#veil_status Chorus` (in
  `Cadence/Chorus/Certify.lean`), `#veil_status FallbackReceipt` (in
  `Cadence/FallbackReceipt/Certify.lean`) and `#veil_status Mvba` (in
  `Cadence/Mvba/Certify.lean`) walk each model's registry of
  verification conditions and report, per condition, whether a real,
  statement-matching, kernel-checked theorem is in scope. All three are
  pinned: `4222/4222 real`, `220/220 real` and `725/725 real`, three
  axioms. That is the claim "nothing here is stubbed", as a command rather
  than as prose.
* **The pre-fix receipt rules are broken.**
  `Cadence/FallbackReceipt/PreFix.lean` pins the model checker's
  *counterexample* to the receipt rules as published in `arXiv:2607.02275v1`.
  That file builds only if the bug is still found, verbatim.
* **The MVBA's lock check is load-bearing.** `Cadence/Mvba/NoLock.lean`
  pins the model checker's *counterexample* to the MVBA instantiation with
  the `Pre-Prepare` handler's lock check removed — two correct validators
  deciding different vectors — found on a restriction of that mutant every
  run of which is a run of the mutant. It is the mutation test of the
  instantiation's invariants: they are not merely true but needed. That
  file, too, builds only if the violation is still found, verbatim.

## What this module does not import

The model-conformance monitor (`Cadence/Monitor/`) is a separate concern — it
checks whether a real implementation trace is *simulated by* the model, which
is neither a proof nor part of any theorem's trust base. Its modules each
carry a `main` for `lean --run`, so they cannot share one import closure;
`lake build` still elaborates them. See [docs/Monitor.md](./docs/Monitor.md).

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
[docs/Architecture.md](./docs/Architecture.md) §4.
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
