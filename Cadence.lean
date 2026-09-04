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
| `Chorus.invariants_of_reachable` | `Cadence/Chorus/Certify.lean` | every reachable state of the per-slot consensus satisfies all 98 declared safety properties and invariants |
| `Chorus.slotConsensusSafety` | `Cadence/Chorus/Compose.lean` | Chorus ⊨ `SlotConsensusSafety` — the state-level fragment of the paper's per-slot module contract (agreement, slot safety, proposal inclusion, and the monotonicity of finalization), for every slot's copy of the model; this is the object the glue consumes as its `sc` constraint |
| `Chorus.slotConsensus_of_residual` | `Cadence/Chorus/Compose.lean` | given `Chorus.SlotConsensusResidual` — the participation interface, the admissible-run model, Termination and Quiescence, stated over Chorus's transition system — Chorus is a full `SlotConsensus`; Hiding's protocol half is discharged on the way. The residual's fields are the formal statement of what is *not* proven about Chorus as a slot consensus |
| `Chorus.evidence_pigeonhole_of_reachable` | `Cadence/Chorus/Pigeonhole.lean` | `2f+1` honest fallback entries always yield certified per-proposer evidence, for **every** `n = 3f+1` (the counting step of the fallback liveness branch) |
| `Chorus.fbcert_of_honest_fallback_votes`, `Chorus.fbcommitqc_of_honest_commit_votes` | `Cadence/Chorus/Counting.lean` | certificate formation: once every honest validator has cast its fallback (resp. fallback commit) vote, `FBCert` (resp. `fbCommitQC`) exists — the honest population is itself the quorum, for **every** `n = 3f+1` |
| `Chorus.commitqc_of_honest_fast_dominant` | `Cadence/Chorus/Counting.lean` | a supermajority of honest fast commit votes yields, per proposer, a commitQC from honest votes alone (the counting step of the fast-dominant liveness branch), for **every** `n = 3f+1` |
| `Chorus.progress_dichotomy_of_saturation` | `Cadence/Chorus/Progress.lean` | the liveness case split as **one theorem**: in any reachable state where every honest validator has cast its path vote, either commitQCs exist for every proposer from honest votes alone, or the MVBA stands invoked with decide-enabling evidence for every proposer (verbatim the `mvba_decide_*` guards), for **every** `n = 3f+1` |
| `Chorus.build_totality_of_reachable` | `Cadence/Chorus/Counting.lean` | any supermajority of per-proposer fallback entries — arbitrary honest/Byzantine mix, i.e. a validator's `2f+1` accepted receipts — yields a buildable meta-block entry (FallbackQC or EquivCert) for every proposer: the state-level half of "every correct validator can propose", for **every** `n = 3f+1` |
| `Conductor.orchestratorSafety` | `Cadence/Composition.lean` | Conductor ⊨ `OrchestratorSafety` — the state-level fragment of the paper's slot-scheduling module contract (open-prefix agreement, Monotonicity, Integrity's at-most-once half, the observables' monotonicity and frames), every field proven from the Conductor's own transition system; the object the glue consumes as its `orch` constraint |
| `Conductor.orchestrator_of_residual` | `Cadence/Composition.lean` | given `Conductor.OrchestratorResidual` — Totality, `B`-Boundedness, `R`-Recovery and the admissible-run model, stated over the Conductor's transition system — the Conductor is a full `Orchestrator`; Integrity's timing half is discharged on the way. The residual's fields are the formal statement of what is *not* proven about the Conductor as an orchestrator |
| `Cadence.positional_log_safety` | `Cadence/Composition.lean` | MCP Safety in the paper's positional form — two correct validators never disagree on the log entry at a given position — for the glue over *any* orchestrator and slot consensus satisfying the two `…Safety` contracts |
| `Cadence.system_positional_log_safety` | `Cadence/System.lean` | the same, **for the composed system**: the glue running the Conductor's and Chorus's own transition systems. No contract hypothesis remains; what is assumed is the two modules' configurations and that they agree on who is Byzantine |
| `FallbackReceipt.invariants_of_reachable` | `Cadence/FallbackReceipt/Certify.lean` | every reachable state of the fallback receipt/propose layer satisfies its declared invariants |
| `FallbackReceipt.build_totality_of_reachable` | `Cadence/FallbackReceipt/Totality.lean` | an honest validator can always build a *valid* fallback meta-block, for **every** `n = 3f+1` |

Two further build-checked claims are pinned where they are made, because
their form is not an axiom footprint:

* **Completeness of the per-VC evidence.** `#veil_status Chorus` (in
  `Cadence/Chorus/Certify.lean`) and `#veil_status FallbackReceipt` (in
  `Cadence/FallbackReceipt/Certify.lean`) walk each model's registry of
  verification conditions and report, per condition, whether a real,
  statement-matching, kernel-checked theorem is in scope. Both are pinned:
  `3861/3861 real` and `220/220 real`, three axioms. That is the claim
  "nothing here is stubbed", as a command rather than as prose.
* **The pre-fix receipt rules are broken.**
  `Cadence/FallbackReceipt/PreFix.lean` pins the model checker's
  *counterexample* to the receipt rules as published in `arXiv:2607.02275v1`.
  That file builds only if the bug is still found, verbatim.

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
info: 'Chorus.slotConsensus_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensus_of_residual

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
info: 'Conductor.orchestrator_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Conductor.orchestrator_of_residual

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
