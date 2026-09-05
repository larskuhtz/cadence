# Module contracts: the composition, mechanised

*Design record and status. It records a defect in how the module contracts
used to be stated, the design that replaced them, what is now machine-checked
about the composition, and — named, in one place — what is not. Implemented
2026-09-04 (branch `worktree-composition-contracts`); the code is
[`../Cadence/Interfaces.lean`](../Cadence/Interfaces.lean) (the contracts),
[`../Cadence/Cadence.lean`](../Cadence/Cadence.lean) and
[`../Cadence/Conductor.lean`](../Cadence/Conductor.lean) (the consumers),
[`../Cadence/Composition.lean`](../Cadence/Composition.lean) and
[`../Cadence/Chorus/Compose.lean`](../Cadence/Chorus/Compose.lean) (the
instances and residuals), and [`../Cadence/System.lean`](../Cadence/System.lean)
(the composed theorem).*

## 1. The defect that was fixed

The contracts were stated as *snapshots*. `Orchestrator.opened : validator →
slot → Prop` looked like a pure predicate on two declared types, but what a
validator has opened depends on how far the run has got: the index was real
and merely hidden — `orchestrator_instance` took a *state* and returned an
`Orchestrator`, so "the Orchestrator" was a family indexed by state and the
class type did not say so. Three consequences, one problem:

* **The class could not be consumed as a constraint.** A Veil module cannot
  `instantiate` a contract whose carrier is its own evolving state, so the
  glue *restated* each contract property as a `require` and an `invariant`,
  tied to the class only by a comment. Nothing checked the restatement — the
  seam the 2026-09 hand-off called *transcription fidelity*.
* **The temporal properties had nowhere to live.** Totality, Monotonicity,
  Integrity, boundedness, recovery, termination, quiescence are properties of
  *runs*; a snapshot contract cannot state them, so they were prose rows in
  obligation tables with named meta-axioms.
* **The contracts were nearly empty.** What survived into `Orchestrator` was
  one field, satisfiable by an orchestrator that never opens anything.

`ByzNodeSet` was the counterexample that made the diagnosis: it is consumed
exactly as a class constraint should be (`instantiate nset : ByzNodeSet node
nodeset`, discharged by `byzNodeSetFin`), because its operations genuinely are
functions of `node` and `nset`.

## 2. The design

**State the contract over an explicit state type.** Every observable becomes a
function of the abstract state, the module's transitions become relations on
it, and a consumer holds the state as a state component of its own and reads
it through the contract. The contract may carry a simpler state than the
implementation operates on; it carries enough for every property the paper
states.

**Two levels per module** — forced, not chosen (§7): Veil hands *every* axiom
of an instantiated class to the SMT solver, and a field that quantifies over
a run is not first-order, so it aborts every verification condition of the
consuming module. Hence, for each paper module `X`:

| Class | Content | Who uses it |
|---|---|---|
| `XSafety` | first-order: `init`, internal `step`, the input transitions the paper's *safety* properties mention, their union `trans`, `reachable` (abstract, closed under `init`/`trans`); the observables; monotonicity of every observable along `trans`; frames (internal steps do not fabricate a correct validator's inputs; an input records exactly itself); the paper's safety properties at `reachable st` | a Veil consumer `instantiate`s it; an implementation proves it |
| `X extends XSafety` | the module proper: the inputs only the temporal properties mention, with their observables; `clock`; `Admissible : TimedRun → Prop` (the execution model, implementation-defined, non-vacuous by `admissible_exists`); bounds as data; every temporal, quantitative and cryptographic-residue property, over `Run`/`TimedRun` | Lean-level only; an implementation *owes* it |

An implementation that proves the safety fragment but not the rest provides
the `XSafety` instance (kernel-checked) and a **residual** — a Lean
`structure` whose fields are exactly the upper-level obligations it does not
discharge, restated over its own transition system — plus `X_of_residual :
Residual → X`. Type-checking the latter is what guarantees the residual says
exactly what the class says; the residual *is* the module's remaining
assumption inventory, as a type.

**Conventions that make it uniform** (the header of `Interfaces.lean` is the
authoritative statement):

* *Correctness is one object.* Every class takes `byz : validator → Prop` as an
  explicit parameter; a Veil module instantiates `FaultModel` once and passes
  `fm.byz` to every contract it consumes, so all of them are stated against
  the same notion of "correct". Spike 05 established that a later
  `instantiate` can take an earlier instantiated parameter's projection.
* *Inputs are transitions, outputs are observables.* `complete : state →
  validator → slot → state → Prop` is driven by the consumer choosing a
  post-state; `opened : state → validator → slot → Prop` is read.
* *Time.* Timed properties take a `time` type with Veil's `TotalOrder` and an
  `Add`; `max(t, GST) + d` is `TimedRun.byGstBound` ("by `u + d` for the least
  `u` above both"), so no decidability of the order is needed.
* *Hiding.* `def:hiding` is simulation-based and not expressible here; the
  contract carries its protocol-level residue (`hiding_residue`: payloads
  become recoverable only after the deadline) and names the two steps that
  stay meta — `ThresholdIBE.decrypt_secret` and the paper's simulation.

## 3. The consumers: what changed in the models

**The glue** (`Cadence.lean`) now reads

```
instantiate fm   : FaultModel node
instantiate orch : OrchestratorSafety node slot ostate fm.byz
instantiate sc   : SlotConsensusSafety slot node proposal pvector scstate fm.byz
individual os : ostate
function sc_state (s : slot) : scstate
```

and every contract property it used to restate is gone from its guards and
invariants: `opened i s` is the ghost `orch.opened os i s`, `finalized i s v`
is `sc.finalized s (sc_state s) i v`, and the three invariants that carry
contract content (`finalized_agreement`, `finalized_inclusion`,
`opened_prefix_agreement`) are *proven* from the class axioms at the reachable
abstract state — kept as invariants only because downstream cells e-match on
them better. The old oracle actions became an oracle step per sub-protocol
(`orch_step`, `sc_step`: any internal transition the contract allows) plus
handlers that react to observables (`on_propose`, `on_finalize`, with
`record_skip` and `append` as before). `on_finalize` drives the orchestrator's
`complete` input, so the glue's `completed` *is* the orchestrator's record —
which is what lets `bounded_concurrency_interval` be stated over the object
`Orchestrator.boundedness` speaks about, with no bridge between two notions
of "completed". The `participate()` call is definitionally the opening; the
inputs the paper's safety properties never mention (`abandon`, `propose`) stay
glue-local records, as the paper's own local variables (§8).

The handler relaxation — the paper runs a handler atomically upon the output,
here it is a later action — admits strictly more behaviours, so every safety
property holds a fortiori; no safety property had to be weakened (the
biconditional in `bounded_concurrency_interval` survives because
`participate()` is the opening and `abandon()` shares its handler with
`complete(s)`). What it costs is an (F-justice) obligation on the handlers.

**The Conductor** (`Conductor.lean`) consumes `ACSSafety` the same way: one
abstract ACS state per window (`function acs_state (w : window) : acsstate`),
the honest `acs_propose` driving the instance's `propose` input, a new
`acs_step` oracle action for the instance's internal steps (Byzantine
proposals appearing, the decision itself — the contract constrains only
correct validators' proposals, so `byz_acs_propose` is subsumed), and
`acs_decide` reading `acs.decided` off the state. The Conductor's own fault
pattern is now the shared `FaultModel` too. One bridge remains a stated
`require` rather than a class property, deliberately: that the decided
first slot is bracketed from below by a *correct* pair of the decided set,
which is the quantitative half of ACS validity through the median lemma of
`Windows.lean` — cardinality is outside the first-order fragment (§8).

**Chorus is unchanged as a model.** Its MVBA oracle stays inlined for a
reason that is not the class's shape (§8).

Both consumers re-solved cold and green: the glue 177 conditions (7 actions ×
24 properties, plus the initializer and both reachability traces), the
Conductor 170 (7 × 20). Nothing was weakened; three glue invariants changed
name because the concept they track changed (`delivered` is the handler's
record of a finalization, `pending := delivered ∧ ¬ appended`).

## 4. The providers: what is proven, and how

* **`Conductor.orchestratorSafety th : OrchestratorSafety node slot
  (Conductor.State …) fm.byz`** (`Composition.lean`). Every field proven:
  `init`/`trans`/`reachable` are the Conductor's own relations, so the closure
  fields are the reachability constructors; `open_prefix_agreement` is
  `safety [open_prefix_agreement]` projected out of `invariants_of_reachable`
  (the strict order converted to `le ∧ ≠` by `TotalOrderWithMinimum.le_lt`);
  the paper's Monotonicity is `invariant [open_local_order]` plus the
  `open_slot` guard; and the **step-level** fields — `opened_mono`,
  `completed_mono`, `completed_step_frame`, `complete_effect`,
  `complete_frame`, `init_opened`, `init_completed` — are proven action by
  action from Veil's pre-computed transition bodies.
* **`Chorus.slotConsensusSafety th : SlotConsensusSafety slot node merkle_root
  (slot × (node → Option merkle_root)) (Chorus.State …) (fun i => nset.is_byz
  i = true)`** (`Chorus/Compose.lean`). The family runs one copy of the
  single-slot model per slot and tags each finalized vector with its slot,
  which is what makes `slot_safety` hold by construction; `agreement` and
  `proposal_inclusion` are the 2026-07 proofs over the named reachability
  projections; `on_time` is `all_honest_recorded`; and the step-level fields
  (`finalized_mono`, `on_time_mono`, `init_finalized`) rest on four uniform
  two-state lemmas over all 38 actions — including that a committed
  validator's entries are *frozen*, because `commit_assign_*` require
  `¬ local_committed i`.

**The step-level technique**, which the plan had not exercised and which was
the one open risk: a contract field such as "`opened` is monotone along
`trans`" is a relation between two consecutive states, and no
`#check_invariants` cell speaks about two states. Veil, however, pre-computes
each action's two-state transition as a `reducible` definition
`<action>.ext.tr` (a conjunction of the guards and `setIn {updated fields}
s₀ = s₁`) with a bridge `<action>.ext.derived_eq` from the derived transition
the reachability relation uses. So a step-level fact is proven by dispatching
the label, rewriting with `derived_eq`, unfolding `tr`, destructuring (the
`obtain` on the final equation substitutes the post-state), and evaluating
the field-representation `get`/`set` pair at the canonical functional
representation (`CanonicalField.set`, `FieldUpdateDescr.fieldUpdate`,
`IteratedArrow.curry`, …). One macro pair per model (`conductor_tr` /
`conductor_field_simp`, `chorus_tr` / `chorus_field_simp`) and one tactic
line per fact; the 38-action Chorus lemmas elaborate in seconds. The guards
are kept as inaccessible hypotheses, which is how the frozen-entries lemma
sees `¬ local_committed i`.

Trust base: every new declaration is pinned at `[propext, Classical.choice,
Quot.sound]` at its own site and in [`../Cadence.lean`](../Cadence.lean).

## 5. The residuals: exactly what is still assumed

`Conductor.OrchestratorResidual th` (`Composition.lean`) has fields
`Admissible`, `admissible_exists`, `totality`, `bound`, `boundedness`,
`recovery_time`, `recovery` — the paper's Totality (`lemma:conductor-totality`),
`B`-Boundedness (`lem:boundedness`; the interval form *is* proven as
`safety [bounded_tail]`, the count `2W − p` needs widths the model keeps meta)
and `R`-Recovery (`prop:smooth-windows`, `prop:first-post-gst-window-time`),
over timed runs of the Conductor with the admissible-execution model as data.
`orchestrator_of_residual` proves these are all that is missing, discharging
Integrity's timing half (`safety [opened_after_start]`) on the way.

`Chorus.SlotConsensusResidual th time message` (`Chorus/Compose.lean`) is
larger, honestly: Chorus models none of `mod:slotconsensus`'s participation
interface (`participate`/`abandon`/`propose` and their observables), no clock
and no message type, so the whole upper level except Hiding's protocol half
is residual — `slotConsensus_of_residual` discharges `hiding_residue` from
`safety [hiding_until_deadline]` and takes the rest as the hypothesis.

These two structures replace the rows of the old obligation tables that said
"documented, (A-…)". [`Architecture.md`](./Architecture.md) §4 item 4 now
points at them by name; the meta-axiom names (A-orch-totality),
(A-orch-boundedness), (A-orch-recovery), (A-sc-termination) are the fields'
docstrings.

## 6. The composed system

`Cadence.system_positional_log_safety` (`System.lean`) is the glue's
`positional_log_safety` instantiated at `Conductor.orchestratorSafety thC` and
`Chorus.slotConsensusSafety thS`: MCP Safety for the glue running the
Conductor's and Chorus's own transition systems, with **no contract
hypothesis left**. What remains are the two modules' configurations and one
hypothesis `hbyz` that the system's fault model and Chorus's
`ByzNodeSet.is_byz` agree — the transport that brings Chorus's instance to
the shared `byz` (`SlotConsensusSafety.castByz`, a rewrite along a
propositional equality of predicates). No temporal obligation enters: MCP
Safety is a safety property and needs only the two proven fragments.

## 7. Evidence

The runnable experiments are in [`../spikes/`](../spikes/README.md); 01–04
established the state-explicit shape, the negative control (removing the
class axiom makes the consumer's invariant fail with `❌`), the hazard (a
run-quantifying field in an instantiated class crashes all VCs with
`cvc5.Error.error "Symbol '->' not declared as a type"`) and the two-level
split; 05 the shared fault model, the inst-implicit order and the per-slot
`function` state. The step-level technique graduated straight into the code
(§4).

## 8. What this does not close — the remaining seams, named

1. **Chorus's MVBA oracle is inlined, not a class constraint.** `MVBASafety`
   exists and is the uniform shape, and Chorus's `mvba_decide_*` guards are
   the transcription of its fields, audited by reading:

   | `MVBASafety` field | Chorus guard (`mvba_decide_pos` / `mvba_decide_neg`) |
   |---|---|
   | `agreement`, `integrity` | `∀ m2, mvba_decided_pos j m2 → m = m2`, `¬ mvba_decided_neg j` / `∀ m, ¬ mvba_decided_pos j m`, plus `¬ mvba_complete` |
   | `external_validity` | `vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)` / `vote_quorum_neg j ∨ ((fb_quorum_neg j ∨ equiv_evidence j) ∧ fbcert)` |
   | `decided_mono`, `init_decided` | the relations are only ever set; `after_init` clears them |

   The obstacle is not the class's shape. The paper's `Valid B` is a
   function of the meta-block, which *carries* its certificates; Chorus
   checks a decided entry's certificate against its own network relations —
   a predicate on Chorus's **state**, which a class parameter declared before
   `#gen_state` cannot mention. Closing this means either carrying
   certificates in the value type or restating the evidence guards as the
   class's `Valid`; either changes every Chorus verification condition and is
   scheduled with the MVBA instantiation (`docs/MvbaPlan.md` on its branch),
   not here.
2. **Chorus has no participation interface**, so `SlotConsensusResidual`
   carries the whole of it; and the glue's records of the inputs it does not
   drive (`sc_abandoned`, `proposed`) are its own, as the paper's local
   variables are. That the glue's call *is* the instance's input is the
   trace-level refinement seam declared out of scope in `Composition.lean`'s
   header and `ChorusDesign.md` §10.1. Adding `participate`/`abandon` to the
   Chorus model would let the glue drive them and shrink the residual; it is
   a model change and pays the Chorus cold re-solve.
3. **The ACS median bridge.** `acs_decide`'s `require` that a correct pair of
   the decided set brackets the first slot from below is justified by
   `ACS.validity_quantitative` through `Windows.lean`'s median lemma, not
   derived from the class: cardinality is upper-level. It is one `require`,
   documented at the action.
4. **`Admissible` is implementation-defined data**, so a future full instance
   could be vacuous if it defined it as `False`; `admissible_exists` forbids
   that, and the definition is one line to audit.
5. **The two fault patterns** meet in `hbyz` (§6) — an honest hypothesis, not
   a proof.

## 9. What this supersedes

* **The shared-syntax route** (`openPrefixAgreement%`, on this branch until
  2026-09-04): it single-sourced the *statement* but left the hidden index in
  place and made the provider-state/consumer-observation conflation harder to
  see. Removed; do not reintroduce it for the other contracts.
* **The snapshot classes** `SlotConsensus`/`Orchestrator`/`ACS`/`MVBA` of the
  old `Interfaces.lean`, `Conductor.orchestrator_instance` and
  `Chorus.slotConsensus_instance` (per-state instances). The names
  `SlotConsensus`, `Orchestrator`, `ACS`, `MVBA` now denote the *full*
  contracts; the state-level fragments carry the `…Safety` suffix.
* `class MVBA` moved from `Primitives.lean` to `Interfaces.lean` — it is a
  module contract, and `Chorus.lean` imports `Primitives.lean`, so keeping it
  there made every contract edit a Chorus rebuild.

## 10. Veil facts that cost time to find

Recorded so they are not re-derived (all reproduced by the spikes or the code):

* Veil emits **every axiom of an instantiated class** to the solver. That is
  what makes the design work, and why a non-first-order field in the
  instantiated fragment aborts *all* the consumer's VCs (spike 03).
* `instantiate` must precede `#gen_state`, so a class cannot mention the
  module's own `State`; the design sidesteps this because the contract's
  state is a module *parameter* (`type ostate`). A later `instantiate` *can*
  refer to an earlier one's projection (`fm.byz`) and resolve inst-implicit
  class arguments from earlier instances (spike 05).
* A shared `def` over the carrier does **not** translate (the carrier
  arrives as a function argument; SMT-LIB is first-order); `@[invSimp]`
  unfolds it in hypotheses but not goals. Not needed any more.
* **Never name an action parameter `st'`**: Veil's trace pipeline uses that
  name for the post-state, and the `sat trace` fails with an application
  type mismatch naming `<action>.ext.tr … st' rd st st'`. (The sweep itself
  is unaffected, which is what makes the failure confusing.)
* `hiding` is a Lean keyword (`open … hiding`), unusable as a field name.
* Two-state facts about a generated transition: `<action>.ext.derived_eq`
  then the `reducible` `<action>.ext.tr`; `obtain ⟨_, h⟩ := h` on the final
  `setIn … = s₁` conjunct *substitutes* (so a following `subst` is a no-op
  the linter flags); the guards survive as inaccessible hypotheses. The
  `actSimp`/`nextSimp` simp sets unfold the action *bodies* and defeat the
  `derived_eq` rewrite — use the explicit lemma names.
* `all_honest_recorded j m` has four conjuncts since the 2026-08
  `well_encoded` refactor (`¬ is_byz j`, `is_proposer j`, the recorded
  entries, `well_encoded m`).
