# Module contracts: the composition, mechanised

*Design record and status. It records a defect in how the module contracts
used to be stated, the design that replaced them, what is now machine-checked
about the composition, and — named, in one place — what is not. Implemented
2026-09-04 (branch `worktree-composition-contracts`); the code is
[`../Cadence/Interfaces.lean`](../Cadence/Interfaces.lean) (the contracts),
[`../Cadence/Cadence.lean`](../Cadence/Cadence.lean),
[`../Cadence/Conductor.lean`](../Cadence/Conductor.lean) and, since
2026-09-10, [`../Cadence/Chorus.lean`](../Cadence/Chorus.lean) (the consumers),
[`../Cadence/Composition.lean`](../Cadence/Composition.lean) and
[`../Cadence/Chorus/Compose.lean`](../Cadence/Chorus/Compose.lean) (the
instances and the joins toward the full contracts), and [`../Cadence/System.lean`](../Cadence/System.lean)
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
| `TransitionSystemSafety state` | the seven things every contract has because it *is* a transition system: `init`, internal `step`, their union `trans`, an over-approximated `reachable`, and the three closure facts | extended by all four fragments, so the vocabulary is identical across them |
| `XSafety extends TransitionSystemSafety` | first-order: `init`, internal `step`, the input transitions the paper's *safety* properties mention, their union `trans`, `reachable` (abstract, closed under `init`/`trans`); the observables; monotonicity of every observable along `trans`; frames (internal steps do not fabricate a correct validator's inputs; an input records exactly itself); the paper's safety properties at `reachable st` | a Veil consumer `instantiate`s it; an implementation proves it |
| `XTemporal … [S : XSafety …]` | the rest of the module, stated **over the safety instance**: the inputs only the temporal properties mention, with their observables; `clock`; `Admissible : TimedRun → Prop` (the execution model, implementation-defined, non-vacuous by `admissible_exists`); bounds as data; every temporal and quantitative property, over `Run`/`TimedRun` | Lean-level only; an implementation *owes* it |
| `X extends XSafety, XTemporal` | the paper's module in one name; the second parent's instance argument *is* the first parent | the composition, where a full contract is needed |

An implementation that proves the safety fragment but not the rest provides
the `XSafety` instance (kernel-checked) and **no `XTemporal` instance at
it**. That absence is the whole statement of what is missing: every field of
`XTemporal` is already written over `S.init`, `S.trans`, `S.reachable` and
`S`'s observables, so there is nothing to restate at the implementation's
own types. `X_of_temporal h = { theSafetyInstance, h with }` joins the two
levels, and a companion `rfl` lemma pins that the join hands back exactly
the fragment that was proven.

Until 2026-09 each implementation instead carried a `…Residual` structure
whose fields restated those obligations at its own types, with an
`X_of_residual : Residual → X` whose type-checking was what guaranteed the
restatement matched the class. That mechanism cost one restatement per
obligation per implementation; the dependent-parent shape removes it
([`../spikes/06_dependent_temporal_parent.lean`](../spikes/06_dependent_temporal_parent.lean),
[`History.md`](./History.md)).

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

**Chorus** (`Chorus.lean`) consumes `MVBASafety` the same way since
2026-09-10 (`docs/MvbaPlan.md` §6): `instantiate mvba : MVBASafety node
mvalue mmsg mstate (fun i => nset.is_byz i = true)` after its `nset`, one
abstract state `individual mvba_st : mstate` seeded from an immutable
`mvba_init_state` with `assumption [mvba_init]` and carried as
`invariant [mvba_reachable]`, the oracle step `mvba_step`, the driven
input `mvba_propose` (the paper's `MVBA[s].propose(B_i)`, under the
proposer's own trigger and with `Valid B_i` as guards; `abandon` stays
undriven — the single-slot model never abandons the instance), and two
**per-entry decision handlers** `on_mvba_decide_pos` / `on_mvba_decide_neg`
that transport a correct validator's decision `mvba.decided mvba_st i v`
into the module's existing per-proposer records through the two immutable
projections `mval_pos v j m` / `mval_neg v j` of the opaque value sort
(the value is the entry vector; the projections carry two assumptions,
functional and exclusive, discharged by `System.lean` at `v j = some m` /
`v j = none`). The records' agreement, which the retired oracle actions
*enforced by guards*, is now *proven* from the class's `agreement` through
two tie invariants (every record is the projection of some correct
validator's decision). **One bridge** remains a stated `require`,
deliberately, and it is the MVBA counterpart of the ACS median bridge
(§8): each handler verifies the decided entry's certificate against
Chorus's network relations — `vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧
fbcert)`, resp. the negative form — which is what the class's `Valid`
*means* in a model whose signatures are network relations, and which a
class parameter fixed before the module's state exists cannot say.
`spikes/09_mvba_consumer_ok.lean` and `10_mvba_consumer_no_tie.lean` are
the shape experiment and its negative control. The cost was the full
Chorus cold re-solve, every verification condition having changed; what
it bought is recorded in §8.

All three consumers re-solved cold and green: the glue 177 conditions (7 actions ×
24 properties, plus the initializer and both reachability traces), the
Conductor 170 (7 × 20), Chorus at the count pinned by `#veil_status Chorus`
(`Cadence/Chorus/Certify.lean`). Nothing was weakened; three glue invariants changed
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
  two-state lemmas over all 40 actions — including that a committed
  validator's entries are *frozen*, because `commit_assign_*` require
  `¬ local_committed i`.
* **`Mvba.mvbaSafety th : MVBASafety node value (Mvba.State …) (fun i =>
  nset.is_byz i = true)`** (`Mvba/Compose.lean`, 2026-09-08; `docs/MvbaPlan.md`
  §5). The model is one instance of `mod:mvba`, so the contract is
  instantiated directly: `Valid` is the theory's immutable `valid` (the
  value is the entry vector), `decided` the relation of that name, `step`
  the transitions other than the two inputs; `agreement`, `integrity` and
  `external_validity` are the model's three `safety` declarations through
  the named reachability projections of `Mvba/Certify.lean`, and the
  step-level fields (`decided_mono`, `init_decided`) come from the 24
  actions' transition bodies by the same technique. Because the model has
  `propose` and `abandon` as actions and a per-sender row for each signed
  message kind, the instance file also proves — for the *upper* class,
  in the fragment itself — the inputs, their observables (`proposed :=
  input`, `abandoned`, `sent` by cases on `Mvba.Msg`), effects, frames,
  initial conditions and **Quiescence**, the last as the one-step fact
  `sent_new_tr` (every honest send requires `∃ E, input i E` and
  `¬ abandoned i`).

**The step-level fields**, which the plan had not exercised and which were
the one open risk: a contract field such as "`opened` is monotone along
`trans`" is a relation between two consecutive states, and no
`#check_invariants` cell speaks about two states. As of 2026-09-10 that is
no longer a gap in the tool, and the instance files reach for three things
in order.

1. **Generated lemmas** (`veil.gen.stepLemmas`). Everything the update
   records already determine is emitted and kernel-checked at `#gen_spec`:
   `<Module>.<f>.mono` over every label, `<Module>.<action>.frame_<f>`, and
   `<Module>.<f>.init`. `opened_mono_tr`, `completed_mono_tr`,
   `completed_frame_internal`, `init_not_opened`, `init_not_completed`
   (Conductor) and `committedAll_mono`, `committedPos_mono`,
   `recorded_mono`, `init_not_committed` (Chorus) are each a one-line
   application of one of these. They were 38-case `cases l` scripts before.
2. **A checked two-state cell** (`step_property`) where the fact needs the
   action guards or the invariants at the pre-state, which the update
   records do not carry. Two are stated: the Conductor's `monotonicity` —
   the paper's, which needs `[open_local_order]` at the pre-state together
   with `open_slot`'s guard — and Chorus's `committed_pos_frozen`, "a
   committed validator's positive entries do not change", which needs
   `commit_assign_pos`'s `¬ local_committed i`. Each is checked per action
   like an invariant and exported as `reachable_<name>_step`; the 30-line
   `monotonicity_tr` and the 38-case `committedPos_frozen` are gone.
3. **By hand from the transition bodies**, for what neither covers. Two
   remain, both about a *single* action rather than all of them:
   `complete_effect_tr` (the effect of `complete_slot`) and
   `complete_frame_other` (its pointwise frame). The technique is Veil's
   pre-computed `<action>.ext.tr` reached through `<action>.ext.derived_eq`
   — the `trSimp` simp set is exactly those two per action, so one
   `simp only [trSimp]` covers a module — then destructure and evaluate the
   field-representation `get`/`set` pair at the canonical representation
   (the `conductor_tr` / `conductor_field_simp` macro pairs, and their
   Chorus and Mvba twins). No macro names an action, so adding one to a
   model changes nothing here.

**The premise this costs.** A `step_property` cell's hypotheses are the
module's assumptions and invariants at the pre-state, so a contract field
discharged from one cannot be an all-states claim. The four monotonicity
fields — `OrchestratorSafety.opened_mono`/`completed_mono`,
`SlotConsensusSafety.finalized_mono`/`on_time_mono` — therefore take
`reachable st` before `trans`, as `monotonicity` always did. It costs the
consumers nothing: they already carry the sub-protocols' reachability as
invariants (`orch_reachable`, `sc_reachable`), and the glue re-solves with
the same 175 cells. The contracts' own convention has always promised
properties at reachable states (`Interfaces.lean`, "Conventions").

Trust base: every new declaration is pinned at `[propext, Classical.choice,
Quot.sound]` at its own site and in [`../Cadence.lean`](../Cadence.lean).

## 5. What is still assumed: the missing `XTemporal` instances

Each implementation proves its `XSafety` fragment. What it still owes is an
instance of the matching `XTemporal` class **at that fragment** — and this
development provides none of the three. Because those classes are stated
over the fragment's own `init` / `trans` / `reachable` / observables, the
list below is a list of *class fields*, not of restatements: there is no
second place where these obligations are written down.

**`OrchestratorTemporal … (S := Conductor.orchestratorSafety th)`** —
`Admissible`, `admissible_exists`, `totality`, `bound`, `boundedness`,
`recovery_time`, `recovery`: the paper's Totality
(`lemma:conductor-totality`), `B`-Boundedness (`lem:boundedness`; the
interval form *is* proven, as `safety [bounded_tail]` — the count `2W − p`
needs widths the model keeps meta) and `R`-Recovery
(`prop:smooth-windows`, `prop:first-post-gst-window-time`), over timed runs
of the Conductor with the admissible-execution model as data.
`Conductor.orchestrator_of_temporal` joins it to the fragment. Integrity's
timing half is **no longer here**: it is first-order and the Conductor
proves it, so it moved into `OrchestratorSafety` (`integrity_timing`, from
`safety [opened_after_start]`), which is why that fragment carries `time`.

**`SlotConsensusTemporal … (S := Chorus.slotConsensusSafety th)`** — the
largest of the three, honestly: Chorus models none of
`mod:slotconsensus`'s participation interface
(`participate`/`abandon`/`propose` and their observables), no clock and no
message type, so all of that is owed, together with Termination and
Quiescence. Hiding's protocol half is **no longer here** either: it is
first-order and Chorus proves it, so `deadline_passed`,
`payload_recoverable` and `hiding_residue` moved into
`SlotConsensusSafety`.

**`MVBATemporal … (S := Mvba.mvbaSafety th)`** — the smallest: `clock`,
`Admissible`, `admissible_exists`, `ℓ` and `termination`, the timed part of
`mod:mvba` alone (`ℓ_MVBA`-Termination, the supplement's `thm:termination`;
the model is untimed). Everything else — the two inputs, their observables,
effects, frames, initial conditions and **Quiescence** in one-step form —
is proven into the fragment from the transition bodies.

These classes replace the rows of the old obligation tables that said
"documented, (A-…)". [`Architecture.md`](./Architecture.md) §4 item 4 now
points at them by name; the meta-axiom names (A-orch-totality),
(A-orch-boundedness), (A-orch-recovery), (A-sc-termination) are the fields'
docstrings.

## 6. The composed system

`Cadence.system_positional_log_safety` (`System.lean`) is the glue's
`positional_log_safety` instantiated at `Conductor.orchestratorSafety thC` and
`Chorus.slotConsensusSafety thS` — the latter with Chorus's own MVBA
constraint filled by `Mvba.mvbaSafety thM` (`mstate` the `Mvba` model's
abstract state, `mvalue := node → Option merkle_root`, `mmsg := Mvba.Msg`):
MCP Safety for the glue running the Conductor's and Chorus's own transition
systems, Chorus running the `Mvba` model's, with **no contract hypothesis
left**. What remains are the three modules' configurations (`thC`, `thS`,
`thM`) and one hypothesis `hbyz` that the system's fault model and Chorus's
`ByzNodeSet.is_byz` agree — the transport that brings Chorus's instance to
the shared `byz` (`SlotConsensusSafety.castByz`, a rewrite along a
propositional equality of predicates). No transport is needed between
Chorus and the MVBA: both are stated against `nset.is_byz`. Chorus's three
`assumption`s enter as the `assumptions` conjunct of its instance's `init`;
at the entry-vector projections two of them are theorems, so the one
genuine hypothesis among them is that the abstract MVBA state Chorus starts
from is initial (`chorusTheory_assumptions`). No temporal obligation enters:
MCP Safety is a safety property and needs only the proven fragments.

## 7. Evidence

The runnable experiments are in [`../spikes/`](../spikes/README.md); 01–04
established the state-explicit shape, the negative control (removing the
class axiom makes the consumer's invariant fail with `❌`), the hazard (a
run-quantifying field in an instantiated class is fatal — originally `💥` on
every VC with `cvc5.Error.error "Symbol '->' not declared as a type"`, today
one error naming the class and the field) and the two-level split; 05 the
shared fault model, the inst-implicit order and the per-slot `function`
state. The step-level technique graduated straight into the code
(§4).

## 8. What this does not close — the remaining seams, named

1. **The MVBA bridge** (*closed as a seam 2026-09-10; what remains is a
   bridge of the same kind as item 3*). Until then Chorus consumed the MVBA
   as an oracle — three actions whose guards transcribed the class's
   fields, audited by reading:

   | `MVBASafety` field | the retired oracle's guard (`mvba_decide_pos` / `mvba_decide_neg`) |
   |---|---|
   | `agreement`, `integrity` | `∀ m2, mvba_decided_pos j m2 → m = m2`, `¬ mvba_decided_neg j` / `∀ m, ¬ mvba_decided_pos j m`, plus `¬ mvba_complete` |
   | `external_validity` | `vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)` / `vote_quorum_neg j ∨ ((fb_quorum_neg j ∨ equiv_evidence j) ∧ fbcert)` |
   | `decided_mono`, `init_decided` | the relations are only ever set; `after_init` clears them |

   Since `docs/MvbaPlan.md` §6 landed (§3 above), the first and third rows
   are gone: agreement and integrity are the class's axioms, used by the
   solver; monotonicity and the initial condition are the class's
   `decided_mono` / `init_decided` along the oracle step. The second row
   is what remains, and it remains **by design**: each decision handler
   `require`s the decided entry's certificate against Chorus's network
   relations. The paper's `Valid B` is a function of the meta-block, which
   *carries* its certificates; Chorus's certificate predicate is a fact
   about Chorus's **state**, which a class parameter declared before
   `#gen_state` cannot mention, so the guard is the interpretation of the
   class's `Valid` in Chorus's vocabulary — a bridge, not a restatement,
   documented at the handlers (`Chorus.lean`, "The MVBA instance") and in
   `ChorusDesign.md` §4, and stated in exactly three places: the two
   handlers, and as the caller's obligation in `mvba_propose`'s validity
   guards. It is sound in both directions that matter (it removes no
   behaviour of a correct MVBA, by `external_validity` and public
   verifiability; and it is safety-conservative if the MVBA were wrong).
   What the liveness step will have to name is its completeness direction
   — a decided entry's certificate is network-visible — which is what
   enables the handler (`MvbaPlan.md` §3). The instance behind the
   constraint is `Mvba.mvbaSafety` (§4), so the MVBA is no longer an
   assumed contract anywhere in the composed system.
2. **Chorus has no participation interface**, so `SlotConsensusTemporal`
   carries the whole of it; and the glue's records of the inputs it does not
   drive (`sc_abandoned`, `proposed`) are its own, as the paper's local
   variables are. That the glue's call *is* the instance's input is the
   trace-level refinement seam declared out of scope in `Composition.lean`'s
   header and `ChorusDesign.md` §10.1. Adding `participate`/`abandon` to the
   Chorus model would let the glue drive them and shrink what is owed; it is
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
  what makes the design work, and why a non-first-order field cannot sit in
  the instantiated fragment (spike 03). Since the 2026-09 fork bump the
  check commands *report* such a field by class and field name before any
  solver starts, instead of every VC of the consumer aborting with
  `Symbol '->' not declared as a type`; and `attribute [veil_smt_ignore]
  C.field` withholds a field from the solver while it stays a declared
  axiom of the class, with the withheld fields listed once per module. This
  development withholds nothing — the two-level split is what keeps the
  instantiated fragment first-order — but the attribute is the escape hatch
  if a field ever has to live in a class the models instantiate.
* `instantiate` must precede `#gen_state`, so a class cannot mention the
  module's own `State`; the design sidesteps this because the contract's
  state is a module *parameter* (`type ostate`). A later `instantiate` *can*
  refer to an earlier one's projection (`fm.byz`) and resolve inst-implicit
  class arguments from earlier instances (spike 05).
* A shared `def` over the carrier does **not** translate (the carrier
  arrives as a function argument; SMT-LIB is first-order); `@[invSimp]`
  unfolds it in hypotheses but not goals. Not needed any more.
* `hiding` is a Lean keyword (`open … hiding`), unusable as a field name.
* Two-state facts about a generated transition: prefer the generated step
  lemmas (`<f>.mono`, `<action>.frame_<f>`, `<f>.init`) and, when the guards
  or invariants are needed, a `step_property` cell — see §4. Only when
  neither applies, by hand: `simp only [trSimp]` (`<action>.ext.derived_eq`
  then the `reducible` `<action>.ext.tr`, for every action at once);
  `obtain ⟨_, h⟩ := h` on the final `setIn … = s₁` conjunct *substitutes*
  (so a following `subst` is a no-op the linter flags); the guards survive
  as inaccessible hypotheses. The `actSimp`/`nextSimp` simp sets unfold the
  action *bodies* and defeat the `derived_eq` rewrite — never use them for
  this.
* A `step_property` body elaborates over binders named `th`, `st`, `st'`, so
  a bound variable of a body must not use those names (the models use `s0`,
  `s1`). Capitals are quantified, as in an `invariant`. Step properties are
  conclusions only, and only mutable components have a primed form.
* `all_honest_recorded j m` has four conjuncts since the 2026-08
  `well_encoded` refactor (`¬ is_byz j`, `is_proposer j`, the recorded
  entries, `well_encoded m`).
