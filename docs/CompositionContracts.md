# Module contracts and the composition

*How the paper's module specifications are stated in Lean, how each Veil model
consumes the modules below it and proves the module it implements, and what
the composition does **not** establish. The code is
[Cadence/Interfaces.lean](../Cadence/Interfaces.lean) (the contracts),
[Cadence/Cadence.lean](../Cadence/Cadence.lean),
[Cadence/Conductor.lean](../Cadence/Conductor.lean) and
[Cadence/Chorus.lean](../Cadence/Chorus.lean) (the consumers),
[Cadence/Composition.lean](../Cadence/Composition.lean),
[Cadence/Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) and
[Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean) (the instances),
and [Cadence/System.lean](../Cadence/System.lean) (the composed theorem).
For what is proven overall, read [README.md](../README.md) and
[Architecture.md](Architecture.md).*

**§5 and §7 are the audit-relevant sections**: what each implementation proves
of its module contract and what stays assumed, and the seams the
composition does not close.

## 1. The problem

The paper decomposes Cadence into modules — Module 1 (`mod:slotconsensus`),
Module 2 (`mod:orchestrator_2`), Module 4 (`mod:acs`), Module 3 (`mod:mvba`) — and proves the top-level MCP
properties from their specifications. A mechanised composition has to
reproduce that structure without introducing a gap of its own. Two gaps are
easy to introduce and both are avoided here:

* **Transcription.** If a consumer restates a contract property as one of its
  own guards or invariants, nothing checks that the restatement says what the
  contract says. The correspondence becomes a comment.
* **Silent incompleteness.** If the obligations an implementation does *not*
  discharge are recorded in prose — an obligation list, a list of named
  meta-axioms — nothing checks that the list is complete, or that each entry
  still refers to the transition system the implementation actually proved
  things about.

The design below removes the first by making contracts **consumable as type
class constraints**, and the second by making the temporal obligations
**fields of a class**: an implementation discharges them by providing an
instance, and a class with no instance is an obligation left open, stated
once. Today that is only the ACS's, the assumed module.

## 2. The design: one skeleton, two levels

**Contracts are stated over an explicit state type.** Every observable is a
function of an abstract state; the module's transitions are relations on it;
a consumer holds that state as a component of its own and reads it through
the contract. The contract's state may be simpler than the implementation's;
it carries enough for every property the paper states.

**Each module is two classes** over a shared skeleton. The split is forced by
the tool: Veil hands *every* axiom of an instantiated class to the SMT
solver, and a field that quantifies over a run is not first-order, so it
would abort every verification condition of the consuming module.

| Class | Content | Who uses it |
|---|---|---|
| `TransitionSystemSafety state` | what every contract has because it *is* a transition system: `init`, the internal `step`, their union `trans`, an over-approximated `reachable`, and the three closure facts | extended by all four fragments, so the vocabulary is identical across them |
| `XSafety extends TransitionSystemSafety` | first-order only: the input transitions the paper's *safety* properties mention; the observables; monotonicity of every observable along `trans`; frames (an internal step does not fabricate a correct validator's input; an input records exactly itself); the paper's safety properties at `reachable st` | a Veil consumer `instantiate`s it; an implementation proves it |
| `XTemporal … [S : XSafety …]` | the rest of the module, stated **over the safety instance**: the inputs only the temporal properties mention, with their observables; `clock`; `Admissible : TimedRun → Prop` (the execution model, implementation-defined, non-vacuous by `admissible_exists`); bounds as data; every temporal and quantitative property, over `Run`/`TimedRun` | Lean level only; an implementation *owes* it |
| `X extends XSafety, XTemporal` | the paper's module under one name; the second parent's instance argument *is* the first parent | the composition, where a full contract is needed |

An implementation that proves the safety fragment but not the rest supplies
the `XSafety` instance and **no `XTemporal` instance at it**. That absence is
the whole statement of what is missing: every field of `XTemporal` is already
written over `S.init`, `S.trans`, `S.reachable` and `S`'s observables, so
there is nothing to restate at the implementation's own types.
`X_of_temporal h = { theSafetyInstance, h with }` joins the two levels when
one is supplied, and a companion `rfl` lemma pins that the join hands back
exactly the fragment that was proven.

**How to read a class as a contract.** The paper states each module as an
assume/guarantee pair — what the caller supplies, what the module returns —
and the classes carry both halves, in two encodings that are worth telling
apart because only one of them is visible as a field.

* *The guarantee side is the fields.* In the safety fragment every property
  is stated at `reachable st`, and `reachable` is closed under `trans` —
  every transition, the consumer's inputs at any time included — so a safety
  guarantee holds for **every** caller behaviour. The rely side of a safety
  fragment is therefore empty, and that is a statement rather than an
  omission: agreement does not depend on the caller behaving. At the
  temporal level the rely side is explicit: `termination` takes the caller's
  behaviour as antecedents (every correct party proposes by `t`, none
  abandons before `max(t, gst) + ℓ`) and the environment as `Admissible`.
* *A caller obligation the paper states as a precondition appears as
  partiality of the input relation.* The module's `propose` is a relation;
  an implementation's guard makes it empty where the precondition fails, and
  the caller has to prove the call is enabled before it can take it. The
  composition is blocking — a consumer `require`s the callee's relation — so
  this is a legitimate encoding of the rely side, but it lives in
  enabledness rather than in a named field. The contracts avoid it: the
  MVBA's validity precondition is an antecedent of
  `MVBATemporal.termination`, a named rely side. The implementation's guard
  (`Mvba.propose` checks `valid e`) is its own choice and still shows at the
  composed instance as enabledness; §7 item 1 has the history.

The practical difference is where an unmet obligation surfaces at the
composed instance: a guarantee that failed would break a proof, while a
caller obligation encoded as partiality makes a call *unenabled* — a
non-vacuity question, not a proof failure ("Vacuity does not compose",
§7).

**Conventions** (the header of [Interfaces.lean](../Cadence/Interfaces.lean) is authoritative):

* *Correctness is one object.* Every class takes `byz : validator → Prop` as
  an explicit parameter; a Veil module instantiates `FaultModel` once and
  passes `fm.byz` to every contract it consumes, so all of them are stated
  against the same notion of "correct".
* *Inputs are transitions, outputs are observables.*
  `complete : state → validator → slot → state → Prop` is driven by the
  consumer choosing a post-state; `opened : state → validator → slot → Prop`
  is read.
* *Time.* Timed properties take a `time` type with Veil's `TotalOrder` and an
  `Add`; the paper's `max(t, GST) + d` is `TimedRun.byGstBound` ("by `u + d`
  for the least `u` above both"), so no decidability of the order is needed.
* *Hiding.* Definition 4 (`def:hiding`) is simulation-based and not expressible here. The
  contract carries its protocol-level residue (`hiding_residue`: payloads
  become recoverable only after the deadline) and names the two steps that
  stay meta — `ThresholdIBE.decrypt_secret` and the paper's simulation.

## 3. The consumers

A consumer holds the sub-protocol's abstract state, `instantiate`s the
contract's safety fragment, advances the state only through the contract's
own transitions, and reads observables through the class. No contract
property appears as a `require` or an `invariant`.

### The glue ([Cadence.lean](../Cadence.lean))

```
instantiate fm   : FaultModel node
instantiate orch : OrchestratorSafety node slot ostate fm.byz
instantiate sc   : SlotConsensusSafety slot node proposal pvector scstate fm.byz
individual os : ostate
function sc_state (s : slot) : scstate
```

`opened i s` is the ghost `orch.opened os i s`; `finalized i s v` is
`sc.finalized s (sc_state s) i v`. The three invariants that carry contract
content (`finalized_agreement`, `finalized_inclusion`,
`opened_prefix_agreement`) are *proven* from the class axioms at the
reachable abstract state, and kept as invariants only because downstream
cells match on them more readily.

Each sub-protocol contributes an oracle step (`orch_step`, `sc_step`: any
internal transition the contract allows) plus handlers that react to
observables and drive the contracts' inputs, one per line of Algorithm 1
(`algorithm:cadence`) that gives an input:

| Handler | Paper | Input it drives |
|---|---|---|
| `on_open i s` | Algorithm 1, line 17 (`line:participate`) | `sc.participate` |
| `on_propose i s p` | Algorithm 1, line 19 (`line:propose`) | `sc.propose` |
| `on_finalize i s v` | Algorithm 1, lines 22–23 (`line:complete`–`line:abandon`) | `orch.complete` and `sc.abandon`, in one step |

So every record the glue reads of its own calls is the receiving instance's:
`completed` is the orchestrator's, which is what lets
`bounded_concurrency_interval` be stated over the object
`Orchestrator.boundedness` speaks about, and `participating`, `abandoned`
and `proposed` are the slot-consensus instance's. The contract's input
frames (an input records itself and nothing else) are what carry the glue's
invariants about them across every other step. Two of those invariants are
the caller conditions Chorus's termination claims take, in state form:
`[abandoned_after_finalize]` (C1) and `[participating_opened]` (C2, with the
orchestrator's `integrity_timing`).

The paper runs a handler atomically upon the output; here it is a later
action. That admits strictly more behaviours, so every safety property holds
a fortiori. One statement follows the relaxation:
`bounded_concurrency_interval` is "an active instance is opened and not
completed", the direction Lemma 5 (`lemma:cadence-bounded-concurrency`)
needs; the converse, which the paper's proof also states, fails while
`on_open` has not yet run. What the relaxation costs is an (F-justice)
obligation on the handlers.

### The Conductor ([Conductor.lean](../Cadence/Conductor.lean))

`ACSSafety` is consumed the same way: one abstract ACS state per window
(`function acs_state (w : window) : acsstate`), the honest `acs_propose`
driving the instance's `propose` input, an `acs_step` oracle action for the
instance's internal steps (Byzantine proposals appearing, the decision
itself — the contract constrains only correct validators' proposals), and
`acs_decide` reading `acs.decided` off the state, and `enter_window`
firing on the validator's *own* decision and driving the instance's
`abandon` input in the same step (Algorithm 7, lines 44–45
(`line:acs-decide`–`line:acs-abandon`)). The module's no-premature-abandonment
assumption is then the model's invariant `[acs_abandoned_decided]`
(Proposition 12 (`prop:acs-no-premature-abandonment`)).

One **stated bridge** remains a `require` rather than a class property: that
the decided first slot is bracketed from below by a *correct* pair of the
decided set. Cardinality is outside the first-order fragment, so the model
cannot derive it; that it removes no behaviour of a correct ACS is a Lean
theorem from the contract, `Cadence.acs_median_bracket` (§7 item 3).

### Chorus ([Chorus.lean](../Cadence/Chorus.lean))

`MVBASafety` is consumed the same way:
`instantiate mvba : MVBASafety node mvalue mentries mmsg mstate nodeset nset (fun i => nset.is_byz i = true)`
after `nset`, whose quorum family the contract's availability field counts
with, with one abstract state `individual mvba_st : mstate` seeded
from an immutable `mvba_init_state` (`assumption [mvba_init]`) and carried as
`invariant [mvba_reachable]`. The module supplies the oracle step
`mvba_step`; the driven input `mvba_propose` (the paper's
`MVBA[s].propose(B_i)`, under the proposer's own trigger and with `Valid B_i`
as guards); the forwarded `abandon`; the **decision handoff**
`accept_mvba_commitqc`, which hands a transferred valid commit
certificate to a validator's MVBA through the contract's input `accept`; the
**availability report** `mvba_avail_ready`, which drives the
contract's input `markAvail` once the validator holds its assigned chunk
under every positive FallbackQC entry of a representation; two
**per-entry decision handlers** `on_mvba_decide_pos` / `on_mvba_decide_neg`
that transport a correct validator's decision `mvba.decided mvba_st i v` into
the module's per-proposer records; and the two handlers of the **`CommitQC`
route** `on_mvba_commitqc_pos` / `on_mvba_commitqc_neg`, which
record the entries of a valid certificate `mvba.certifies mvba_st c
(mvba.entries v)` in the same records, so that a validator finalizes on the
MVBA's own commit certificate (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Decision output and handoff"). **The value is the meta-block representation** (an entry vector
and each positive entry's certificate kind,
[PaperAlignment.md](PaperAlignment.md) §8.1), and agreement is over its
entries: two correct validators may decide representations whose
certificates differ. Chorus reads a value's entry vector through the
contract's `mvba.entries` and two immutable projections
`mval_pos e j m` / `mval_neg e j`, and a positive entry's kind through the
immutable `mval_fb v j`. The projections carry two assumptions —
functional in the root, and exclusive — which [System.lean](../Cadence/System.lean) discharges at
`e j = some m` / `e j = none ∧ is_proposer j` (a non-proposer has no
entry). The fallback commit vote `cast_fb_commit i v` reads the
validator's own decision the same way and waits under exactly the
FallbackQC entries of `v`.

The records' agreement is *proven* from the class's `agreement`,
`certified_decided` and `certified_unique`, through two tie invariants
stating that every record is the projection of some correct validator's
decision or of a valid certificate.

**The decision handoff** is the supplement's strengthened Module 3 (`mod:mvba`)
interface (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"), and
nothing else: `certifies st c e` (a valid commitment proof for the entry
vector `e`, since the certificate is over entries), the field
`decided_certified` (**decide exposes its certificate**), the input `accept`
with `accept_trans`, and `accept_effect`/`accept_enabled` (**a transferred
valid certificate is accepted**, in the rely form, deciding a
representation of the certified entries). Beside them sit the
**certificate-level fields**: one certified entry vector
(`certified_unique`), the one every correct party decides
(`certified_decided`), with a valid representation (`certified_valid`) and
with the availability its correct signers established
(`certified_available`, over the observable `availReady`), and it stays
valid (`certified_mono`: the certificate is transferable). **The
availability input** is `markAvail` with `markAvail_trans`,
`markAvail_effect`, `availReady_markAvail_frame`, `init_availReady` and the
four frames saying that no other transition changes `availReady`. The
supplement makes `AvailReady` a predicate on the dissemination layer's
state, so the caller decides it ([PaperAlignment.md](PaperAlignment.md)
§6, P12). All are first-order. Five facts with an `∃` in their conclusion
that no safety cell of Chorus reads are withheld from the solver
(`veil_smt_ignore`: `decided_certified`, `accept_effect`, `accept_enabled`,
`certified_valid`, `certified_available`). `Mvba.mvbaSafety`
proves them, with `decide` as the instance's `accept`: the MVBA no longer
decides on a transferred certificate by an internal step, so the oracle
`mvba_step` cannot take it, and its timing is the caller's, derived from
Chorus's handoff row ([Bounds.md](Bounds.md) §6.4.2, C15). Nothing was
weakened and `MVBATemporal` is unchanged; `System.lean` needed no edit.

One **stated bridge** remains, deliberately, and it is the MVBA counterpart
of the ACS median bridge: each handler verifies the certificate the
representation names for the entry against Chorus's own network
relations — `vote_quorum_pos j m` for a FastQC, `fb_quorum_pos j m ∧
fbcert` for a FallbackQC, and the negative form. Its sites are the two
decision handlers, where the representation is the validator's decision,
and the two `CommitQC` route handlers, where it is the recovered one.
The paper's `Valid B` is a function of the meta-block, which *carries* its
certificates; Chorus's certificate predicate is a fact about Chorus's
**state**, which a class parameter declared before `#gen_state` cannot
mention. The guard is therefore the interpretation of the class's `Valid` in
Chorus's vocabulary (§7 item 1). For *liveness* the bridge is needed in both
directions and becomes a named run-level premise, `Chorus.ValidBridge` in
[Cadence/Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean): a
certified meta-block is `Valid` (what lets `mvba_propose` fire, since the
contract's `propose` requires `Valid`), and a correct validator's decided
or accepted meta-block is certified (what enables the handlers, and what
gives the availability report its chunks) — [Liveness.md](Liveness.md)
§4.3.

## 4. The providers: the proven instances

* **`Conductor.orchestratorSafety th : OrchestratorSafety node slot
  (Conductor.State …) fm.byz`** ([Composition.lean](../Cadence/Composition.lean)). Every field proven.
  `init`/`trans`/`reachable` are the Conductor's own relations, so the closure
  fields are the reachability constructors; `open_prefix_agreement` is
  `safety [open_prefix_agreement]` projected out of `invariants_of_reachable`;
  the paper's Monotonicity is `invariant [open_local_order]` together with the
  `open_slot` guard; the step-level fields (`opened_mono`, `completed_mono`,
  `completed_step_frame`, `complete_effect`, `complete_frame`, `init_opened`,
  `init_completed`) come from Veil's transition bodies as described below.
* **`Chorus.slotConsensusSafety th : SlotConsensusSafety slot node merkle_root
  (slot × (node → Option merkle_root)) (Chorus.State …) (fun i => nset.is_byz
  i = true)`** ([Chorus/Compose.lean](../Cadence/Chorus/Compose.lean)). The family runs one copy of the
  single-slot model per slot and tags each finalized vector with its slot,
  which is what makes `slot_safety` hold by construction; `agreement` and
  `proposal_inclusion` are the model's proofs through the named reachability
  projections; `on_time` is `all_honest_recorded`; the step-level fields
  (`finalized_mono`, `on_time_mono`, `init_finalized`) rest on four uniform
  two-state lemmas over all actions — including that a committed
  validator's entries are *frozen*, because `commit_assign_*` require
  `¬ local_committed i`.
* **`Mvba.mvbaSafety th : MVBASafety node value evec (Mvba.Msg …) (Mvba.State …)
  nodeset nset (fun i => nset.is_byz i = true)`** ([Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)). The model is one instance of
  Module 3 (`mod:mvba`), so the contract is instantiated directly: `Valid` is the
  theory's immutable `valid` and `entries` its `ent` (the value being the
  representation, `evec` the entry vector), `decided` the
  relation of that name, `step` the transitions other than the two inputs;
  `agreement`, `integrity` and `external_validity` are the model's three
  `safety` declarations through the named reachability projections; the
  step-level fields are `decided_mono` and `init_decided`. Because the model
  has `propose` and `abandon` as actions and a per-sender row for each signed
  message kind, the instance file additionally proves — for the *upper* class,
  in the fragment itself — the inputs, their observables (`proposed := input`,
  `abandoned`, `sent` by cases on `Mvba.Msg`), effects, frames, initial
  conditions and **Quiescence**, the last as the one-step fact `sent_new_tr`
  (every honest send requires `∃ E, input i E` and `¬ abandoned i`).

### Discharging the two-state fields

A contract field such as "`opened` is monotone along `trans`" relates two
consecutive states, which no invariant cell speaks about. The instance files
reach for three sources, in this order.

1. **Generated step lemmas** (`veil.gen.stepLemmas`), for everything the
   update records alone determine. `<Module>.<f>.mono` over every label,
   `<Module>.<action>.frame_<f>` and `<Module>.<f>.init` are emitted and
   kernel-checked at `#gen_spec`, and each contract field that follows from
   them is a one-line application.
2. **A checked two-state cell** (`step_property`) where the fact needs the
   action guards or the invariants at the pre-state, which the update records
   do not carry. Two are stated: the Conductor's `monotonicity` — the
   paper's, which needs `[open_local_order]` at the pre-state together with
   `open_slot`'s guard — and Chorus's `committed_pos_frozen`, "a committed
   validator's positive entries do not change", which needs
   `commit_assign_pos`'s `¬ local_committed i`. Each is checked per action
   like an invariant and exported as `reachable_<name>_step`.
3. **By hand from the transition bodies**, for what neither covers. Two
   remain, both about a *single* action rather than all of them:
   `complete_effect_tr` (the effect of `complete_slot`) and
   `complete_frame_other` (its pointwise frame). The technique is Veil's
   pre-computed `<action>.ext.tr` reached through `<action>.ext.derived_eq` —
   the `trSimp` simp set is exactly those two per action, so one
   `simp only [trSimp]` covers a module — then destructure and evaluate the
   field-representation `get`/`set` pair. No macro names an action, so adding
   one to a model changes nothing here.

**What source 2 costs.** A `step_property` cell's hypotheses are the module's
assumptions and invariants at the pre-state, so a contract field discharged
from one cannot be an all-states claim. The four monotonicity fields —
`OrchestratorSafety.opened_mono`/`completed_mono`,
`SlotConsensusSafety.finalized_mono`/`on_time_mono` — therefore take
`reachable st` before `trans`, as `monotonicity` does. It costs the consumers
nothing: they already carry the sub-protocols' reachability as invariants
(`orch_reachable`, `sc_reachable`), and the contracts' own convention has
always promised properties at reachable states ([Interfaces.lean](../Cadence/Interfaces.lean),
"Conventions").

Every declaration added by the composition is axiom-pinned at
`[propext, Classical.choice, Quot.sound]` at its own site and in
[Cadence.lean](../Cadence.lean).

## 5. The temporal levels: the `XTemporal` instances

Each implementation proves its `XSafety` fragment, and an instance of the
matching `XTemporal` class **at that fragment**. All three are proven: the
Conductor's, Chorus's and the MVBA's, each from named hypotheses. Because
those classes are stated over the fragment's own `init` / `trans` /
`reachable` / observables, the lists below are lists of *class fields*,
not of restatements: there is no second place where these obligations are
written down. What stays assumed is the ACS, which the Conductor consumes
as a module (both levels of `ACS`, an arbitrary instance). The composed
timed claims are proven from these instances (§6).

**`OrchestratorTemporal … (S := Conductor.orchestratorSafety th)` is
proven**, as `Conductor.conductorTemporal`
([Cadence/Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean)),
for an arbitrary ACS meeting `ACSSafety` and `ACSTemporal`, with
**`OrchestratorWithTotality`** on top (`Conductor.conductorWithTotality`:
`d_tot` and Totality's `d_tot` form, which Lemma 15
(`lemma:conductor-totality`) proves "more specifically" and Corollary 4
(`cor:chorus-correctness-within-cadence`) consumes; C4).
`Conductor.conductorFull` joins it with the fragment through
`orchestrator_of_temporal`, and `Conductor.conductorFull_toSafety` is
`rfl`. Every field is proven, none is weakened:

| field | proven by |
|---|---|
| `Admissible` | `Conductor.Admissible`: the run is `contractRun` of a labelled timed run meeting `Sync`, the claims' run premises by name |
| `admissible_exists` | `Conductor.admissible_exists`: the idle run, in which the caller completes nothing, no correct validator becomes ready, and only the clock and window 1's openings move |
| `clock_agrees` | `ClockAgrees`, a conjunct of `Sync` |
| `caller_d_tot`, `caller_ℓ` | Chorus's `d_tot` and `ℓ_chorus` |
| `totality` | `Conductor.totality` (Lemma 15) |
| `bound`, `boundedness` | `2W − p`, `Conductor.boundedness` (Lemma 14 (`lem:boundedness`)) |
| `recovery_time`, `recovery` | `2Wτ`, `Conductor.recovery` (Lemma 16 (`lemma:conductor-recovery`)) |
| `OrchestratorWithTotality.d_tot`, `.totality` | Chorus's `d_tot`, the paper's `Δ` at `δ = 0`; `Conductor.totality` |

The hypotheses are the claims' configuration premises by name
(`StartTimes`, `WindowShifts`, `StartsUnbounded`, `WindowsUnbounded`, the
ACS's `Δ`, `ℓ` and fault bound), finitely many validators and an ordered
time ([Premises.md](Premises.md) §9). `Conductor.conductorFullNat`
discharges `WindowsUnbounded` and `StartsUnbounded` at `window := ℕ` over
an Archimedean time whose slot 1 starts at or after `0`. `clock_agrees`
ties a run's clock to the Conductor's own `now`.

**Totality and Recovery are in rely form (C5, decided 2026-10-03).** They
hold of the Conductor only "when run within Cadence": a caller that never
completes a slot leaves every correct validator in window 1 (F17,
[ConductorBounds.md](ConductorBounds.md) §2.3). The two conditions the
paper's proofs take from the caller are the fields' antecedents, stated
over the fragment's own `opened` and `completed`, at the caller's latencies
`caller_d_tot` and `caller_ℓ`:

* **(R-tot)** `OrchestratorSafety.CallerTotality` — a slot whose openings
  are synchronized within `d` has its completions synchronized within `d`;
* **(R-term)** `OrchestratorSafety.CallerTermination` — a slot whose
  openings are synchronized within `d` and which every correct validator
  opens by `t` is completed by every correct validator by
  `max(t, GST) + ℓ`.

`Admissible` stays the scheduler, the network and the timers, as for the
MVBA and Chorus; nothing about the caller enters it. Within Cadence the
composition discharges both from `Chorus.chorusWithTotality`'s
`totality` and `bounded_termination` through the glue
(`Composed.caller_totality`, `Composed.caller_termination`, §6), and each
side is a conditional statement about one slot, so the composition is not
circular.
The statements the Conductor's proofs meet are
`Conductor.TotalityClaim`, `Conductor.BoundednessClaim` and
`Conductor.RecoveryClaim` ([Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean)),
whose conclusions are these fields at the Conductor's fragment, and the
instance consumes them as stated. `Conductor.boundedness` proves the count
`2W − p`, from the interval form `safety [bounded_tail]` and the window
widths (`[win_bounds_shift]`, over the model's shift functions) at the
instance at `slot := ℕ`; `Conductor.totality` proves `d_tot`-Totality by
the window induction; `Conductor.recovery` proves `(2Wτ)`-Recovery through
Propositions 14–19. Integrity's timing half is first-order and the Conductor proves
it, so it sits in `OrchestratorSafety` (`integrity_timing`, from `safety
[opened_after_start]`) — which is why that fragment carries `time`.

**`SlotConsensusTemporal … (S := Chorus.slotConsensusSafety th)` is
proven**, as `Chorus.chorusTemporal`
([Cadence/Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean)), at the
system's configuration, with `SlotConsensusWithTotality` on top
(`Chorus.chorusWithTotality`). `Chorus.slotConsensusFull` joins it with the
fragment through `slotConsensus_of_temporal`, and its `…_toSafety` lemma is
`rfl`. Every field is proven, none is weakened:

* the message type, `Chorus.Message` ([Compose.lean](../Cadence/Chorus/Compose.lean)):
  one constructor per network relation that records its sender, and the
  MVBA's messages;
* `Admissible`, the claims' premises by name (`FJustice`,
  `MvbaAdmissible`, `ValidBridge`, `SyncAtMvba`), and `admissible_exists`,
  a run in which every proposer stays silent;
* Termination, from `Chorus.termination`; `bounded_termination` and
  `totality`, from `Chorus.timed_termination_atMvba` and `Chorus.totality`;
* Quiescence, in Lemma 6 (`lemma:chorus-quiescence`)'s two parts: Chorus's own
  sending rules are gated on active participation, and the MVBA's sends are
  confined by the MVBA's own `quiescence` to the window between a gated
  `mvba_propose` and a forwarded `abandon`.

The instance's hypotheses are the MVBA instance's, and one about the
configuration: the slot's proposer set is non-empty ([Bounds.md](Bounds.md)
§6.4.5). Hiding's protocol half is first-order and Chorus proves it, so
`deadline_passed`, `payload_recoverable` and `hiding_residue` sit in
`SlotConsensusSafety`.

**Quiescence is stated from a reachable state.** The contract's
`quiescence` in `SlotConsensusTemporal` and in `ACSTemporal` quantified
over every transition, reachable or not. That was our mis-statement of the
paper's property, which is about executions: Chorus's MVBA half needs two
facts that hold along the run (an MVBA proposal is made only while
participating; an abandonment is forwarded), and at an unreachable state
neither holds. Both fields now take `S.reachable st`, as the fragments'
other run-level fields do. No consumer reads either. `MVBASafety`'s
`quiescence` keeps the stronger form: the `Mvba` model proves it, its
sending rules being gated on its own records, and Chorus's cells consume
it.

**The participation interface is in the fragment.** Module 1
(`mod:slotconsensus`)'s three inputs, their records, effects, frames and
initial conditions are fields of `SlotConsensusSafety`, proven by
`Chorus.slotConsensusSafety` from the three actions' bodies and Veil's
generated lemmas. The instance separates internal steps from inputs: its
`step` is every transition whose label is not an input
(`Chorus.Label.isInput`), which is what the frames ("internal steps do not
change a correct validator's inputs") need. The glue's oracle step
`sc_step` takes only `sc.step`, and its handlers give the inputs (§3), so
in the composed system ([System.lean](../Cadence/System.lean)) every Chorus transition is
either Chorus's own step or an input the glue gave.

**`MVBATemporal … (S := Mvba.mvbaSafety th)` is proven**, as
`Mvba.mvbaTemporal` ([Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)):
`Admissible`, `admissible_exists`, `ℓ` and `termination`, the timed part of
Module 3 (`mod:mvba`) (`ℓ_MVBA`-Termination). `mvba_of_temporal` joins it into the full
`MVBA`, `Mvba.mvbaFull`, whose fragment is by `rfl` the one
[System.lean](../Cadence/System.lean) plugs into Chorus. The instance's
hypotheses are the classes and the schedule of [Bounds.md](Bounds.md)
§6.2.5; none is a contract and none an axiom. Everything else — the two
inputs, their observables, effects, frames, initial conditions and
**Quiescence** in one-step form — is proven into the fragment from the
transition bodies. A run carries its own clock (`TimedRun.clk`), which is
what lets an untimed model's fragment carry a timed contract.

[Architecture.md](Architecture.md) §4 item 4 points at these field lists
by name; the meta-axiom names (A-orch-totality), (A-orch-boundedness),
(A-orch-recovery) are the fields' docstrings, discharged by
`Conductor.conductorTemporal` modulo the assumed ACS, and
(A-sc-termination) is discharged by `Chorus.chorusTemporal`.

## 6. The composed system

`Cadence.system_positional_log_safety` ([System.lean](../Cadence/System.lean)) is the glue's
`positional_log_safety` instantiated at `Conductor.orchestratorSafety thC` and
`Chorus.slotConsensusSafety thS` — the latter with Chorus's own MVBA
constraint filled by `Mvba.mvbaSafety thM` (`mstate` the `Mvba` model's
abstract state, `mvalue := MetaBlock node merkle_root`,
`mentries := node → Option merkle_root`, `mmsg := Mvba.Msg`).
The statement is MCP Safety for the glue running the Conductor's and Chorus's
own transition systems, Chorus running the `Mvba` model's. **One contract
hypothesis remains, by design: `ACSSafety`**, the agreement-on-a-common-subset
primitive the Conductor runs once per window, which this development consumes
as a class constraint and does not implement — the theorem holds for every
ACS meeting that contract.

Besides it, what remains are the three modules' configurations (`thC`, `thS`, `thM`) and
one hypothesis `hbyz` that the system's fault model and Chorus's
`ByzNodeSet.is_byz` agree — the transport that brings Chorus's instance to
the shared `byz` (`SlotConsensusSafety.castByz`, a rewrite along a
propositional equality of predicates). No transport is needed between Chorus
and the MVBA: both are stated against `nset.is_byz`.

Chorus's three `assumption`s enter as the `assumptions` conjunct of its
instance's `init`. Two of them — the entry-vector projections
`mval_pos_functional` and `mval_pos_neg_excl` — are theorems at the
instantiation (`chorusTheory_assumptions`); the one genuine hypothesis among
them is that the abstract MVBA state Chorus starts from is initial.

The MVBA's one `assumption` enters its own instance the same way, as the
`assumptions` conjunct of `mvbaSafety.init`: `leader_functional` (the leader
schedule is a function). A correct leader is a liveness premise of the
timed instance (`LeaderRotation`), not of the safety instance
([Premises.md](Premises.md) §2.5).

No temporal obligation enters: MCP Safety is a safety property and needs only
the proven fragments.

**The composed timed claims** ([Composed/](../Cadence/Composed/Schedule.lean))
consume the temporal levels. They are stated for the glue at the
Conductor and at Chorus's system configuration, on one clock, with one time
theory, one `Δ` and `δ = 0`, and **one fault pattern, Chorus's** (`fmF`), at
which the Conductor and the ACS are stated too, so no `hbyz` transport is
needed there. A composed run's premises (`Composed.SysSync`) are the glue's
five handler rows, the Conductor's instance's `Admissible` on the
orchestrator's part of the run, and Chorus's instance's `Admissible` on every
started slot's part (each part the stutter lift of
[PartProjection.lean](../Cadence/PartProjection.lean)). Every condition a
module takes from its caller is a theorem about the composed run:

* Chorus's C1, C2, participation and Δ-synchronized participation, from the
  glue's invariants, the Conductor's `integrity_timing` and clock, and
  Lemma 15 within Cadence (`Composed.openings_sync`);
* the Conductor's (R-tot) and (R-term), from Chorus's instance through the
  glue's `on_open` and `on_finalize`.

On that footing: Corollary 4 (`cor:chorus-correctness-within-cadence`)
(`Composed.corollary4`, with Chorus's three claims per slot and no caller
premise left), Lemma 5 (`lemma:cadence-bounded-concurrency`) at `2W − p`
(`Composed.boundedConcurrency`), Lemma 16 within Cadence
(`Composed.recovery_in`), `𝓡`-Liveness (Definition 2
(`def:liveness`)) and censorship resistance (Definition 3
(`def:censorship-resistance`)) at `2Wτ` and at `(W + p − 1)τ`
(`Composed.liveness`, `Composed.censorship`, and their `_sharp` forms). The premise list, each with its use, is
[Premises.md](Premises.md) §0. [System.lean](../Cadence/System.lean)'s
safety theorem is unchanged; it stays generic in the slot order, the time
and the fault-pattern transport, which the timed claims fix.

## 7. The remaining seams, named

1. **The MVBA certificate bridge.** Each decision handler `require`s the
   certificate the decided representation names for the entry against
   Chorus's network relations. This is a
   bridge, not a restatement: the paper's `Valid B` checks the certificates
   the meta-block *carries* — publicly verifiable objects any receiver can
   re-check — while a class parameter declared before `#gen_state` cannot
   mention Chorus's state. It is stated at the two decision handlers, at
   the two handlers of the `CommitQC` route, and as the caller's obligation
   in `mvba_propose`'s validity guards. It is sound in both directions that matter: it removes no
   behaviour of a correct MVBA (by `external_validity` plus public
   verifiability), and if the MVBA were wrong the handler would not fire,
   which is safety-conservative. The liveness argument names its
   *completeness* direction — that a decided entry's certificate is
   network-visible, which is what enables the handler — as the premise
   `Chorus.ValidBridge` of `Chorus.termination`.

   **The bridge is load-bearing for non-vacuity.** The MVBA *enforces*
   validity on `propose` (`require valid e` on `Mvba.propose`), so at the
   composed instance Chorus's `mvba_propose` can fire only when the MVBA's
   `Valid` holds of the vector — and Chorus establishes validity in *its
   own* vocabulary (entries certificate-backed, one per proposer), which is
   not identified with the class parameter. Nothing proven depends on that
   identification: the composed safety theorem is parametric in the MVBA
   theory. What depends on it is **non-vacuity**: if the two notions of
   validity did not coincide, the composed system could not propose at all,
   and no check would say so. That is the right direction for a mismatch to
   fail in — a wrong `Valid` stops the system rather than admitting invalid
   blocks — and it is why the bridge is written down here.

   **The caller's validity obligation is in the rely form.**
   `MVBATemporal.termination` takes "every correct party's input is `Valid`"
   as an antecedent next to the other two caller premises (§2, "How to read
   a class as a contract").
   The model's own `require valid e` keeps `Mvba.termination`'s premise list
   to fair scheduling and sentences of the supplement ([MvbaPlan.md](MvbaPlan.md)
   §3.5 step 4). The bridge is what makes Chorus's `mvba_propose` enabled at
   the composed instance — the Chorus liveness leg's `Chorus.ValidBridge`
   premise ([Cadence/Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)).
2. **The glue drives Chorus's inputs.** The three inputs are
   fields of `SlotConsensusSafety` and the glue's handlers give them (§3),
   so the records the glue reads are the instance's own and the composed
   system's Chorus is not inert. No glue-side copy of a call remains to
   coincide with the instance's input. What stays out of scope is the
   general statement of [System.lean](../Cadence/System.lean)'s header: that the modules' runs
   implement the glue's oracle steps (trace-level refinement).
3. **The ACS median bridge.** `acs_decide`'s `require` that a correct pair of
   the decided set brackets the first slot from below is not derived inside
   the model: the model does not compute the median, and cardinality is
   upper-level. It is one `require`, documented at the action. Its
   justification is a Lean theorem: `Cadence.acs_median_bracket`
   ([AcsMedian.lean](../Cadence/AcsMedian.lean)) proves, for every ACS meeting the contract and
   a system with at most `f` Byzantine validators, that the median of a
   correct decider's set lies between two of its correct pairs. It needs
   the contract's `decided_unique` (one slot per validator) and the
   distinct-validator count of `validity_quantitative`, which Module 4
   (`mod:acs`) does not state ([ConductorBounds.md](ConductorBounds.md)
   §3.4, F18, C6; P16).
4. **`Admissible` is implementation-defined data**, so a future full instance
   could be vacuous if it defined it as `False`; `admissible_exists` forbids
   that, and the definition is one line to audit.
5. **The two fault patterns** meet in `hbyz` (§6) — a hypothesis, not a proof.
   The composed timed claims avoid it by stating the Conductor and the ACS
   at Chorus's fault pattern.
6. **Censorship resistance rests on a timing convention** (F31,
   [ConductorBounds.md](ConductorBounds.md) §7; P19). A correct proposer's
   chunk, sent at the slot's starting time `D − Δ`, may arrive exactly at
   the deadline `D`, where Chorus's punctual deadline marker may fire
   first; the paper counts the chunk as on time without saying so. The
   model states that reading as a premise, (P-incl), and proves censorship
   resistance under it ([Premises.md](Premises.md) §4.8).
7. **The composed claims are non-vacuous**: one model of the whole
   composed system meets every premise of Corollary 4, Lemma 5,
   `𝓡`-Liveness and censorship resistance at once, and its orchestrator's
   part every premise of the Conductor's three
   (`Composed.Witness.*_premises_satisfiable`,
   [Premises.md](Premises.md) §0.5). What stays with the auditor is the
   premises' plausibility, which no witness settles.

### Vacuity does not compose

Safety is universally quantified over behaviours, so it composes: if a
provider is safe in all of its behaviours and the consumer only drives it
where the contract allows, the composition is safe. **Non-vacuity is
existential, and existentials do not compose.** A provider's witness — the
run in which it does something interesting — may rest on inputs the consumer
can never supply, and then the composition is vacuous although both parts
are not.

What the contracts here give is *for all implementations of the class, the
composed system is safe*, together with *there exists an implementation for
which it is non-vacuous*. What would be wanted is *for all safe and
non-vacuous implementations, the composed system is safe and non-vacuous*.
That is not available, and strengthening the class would not deliver it:
an implementation can be non-vacuous in isolation and still never reach
anything interesting under the input profile its consumer produces. To close
that, non-vacuity would have to be indexed by the admissible input profile —
and a property of the form "under every admissible input, something
eventually happens" is liveness. The strengthened-contract route collapses
into the liveness route rather than being an alternative to it.

Two consequences, both practical. **A per-model non-vacuity witness does not
certify the composition**, so the `sat trace` blocks in the module files are
evidence about the modules and nothing more; a witness has to be exhibited
for the composed system as well
([TODO.md](TODO.md) § Soundness). And **the principled fix is liveness**:
once a provider's own progress theorem is discharged and its consumer's
corresponding assumption with it, non-vacuity along that path stops being a
question about witnesses. [Mvba.termination](../Cadence/Mvba/Liveness.lean)
is that theorem for the MVBA, and `Chorus.termination` consumes it, which
retires Chorus's (A-mvba) ([Architecture.md](Architecture.md) §4 item 2).

Both are now done for the timed claims of the composed system. The
composition's premises are exhibited together in one model of the composed
system itself, not in the modules' own models
([Composed/Witness.lean](../Cadence/Composed/Witness.lean),
[Premises.md](Premises.md) §0.5). Every caller condition one module's claims
take from another is a theorem about the composed run (§0.4 there), so no
input profile is left to assume. In the witness's run every slot is opened,
proposed in, finalized and appended, and every window decided and entered:
the composed claims are not vacuous, and the run exercises what they speak
of.

## 8. Reproductions

The runnable experiments behind the design are in
[spikes/](../spikes/README.md): the state-explicit shape; the negative
control (removing a class axiom makes the consumer's invariant fail with
`❌`); the hazard that a run-quantifying field in an instantiated class is
fatal; the two-level split; the shared fault model and the per-slot
`function` state; and, for the MVBA consumer, the tie-invariant shape
([09_mvba_consumer_ok.lean](../spikes/09_mvba_consumer_ok.lean)) with its negative control
([10_mvba_consumer_no_tie.lean](../spikes/10_mvba_consumer_no_tie.lean)), which shows uniqueness failing at exactly
the handlers when the ties are removed.

Working rules for editing any of this — where a two-state fact comes from,
why a `…Safety` field must be first-order, the simp sets that do and do not
work on transition bodies — are in [CLAUDE.md](../CLAUDE.md).
