# Cadence verification — architecture

*Top-level design document for this formalisation. For orientation, build
instructions, and the evidence-auditing guide, start at
[README.md](../README.md); for the end theorems and their trust base on
one page, [`Cadence.lean`](../Cadence.lean). This file explains how the
formalisation is structured, what each part establishes and by what
method, and exactly where its trust boundaries and meta-theoretic seams
lie — **§4 is the audit checklist**: everything the machine does not
establish, in one place. The per-model design rationale lives one level
down: [ChorusDesign.md](./ChorusDesign.md) for the Chorus model, and
[ConductorDesign.md](./ConductorDesign.md) plus the module headers of
[Cadence/Cadence.lean](../Cadence/Cadence.lean) and
[Cadence/Conductor.lean](../Cadence/Conductor.lean) for the
composition-layer models.*

## 1. What is being verified

[Cadence](https://www.category.xyz/cadence) (`arXiv:2607.02275v2`; see the
root [README.md](../README.md) for the citation and how to resolve the label
names used here) is a BFT consensus design with three layers, and the
formalisation mirrors that decomposition one-to-one:

* **Chorus** (`p2_chorus.tex`, `alg_*.tex`) — the per-slot one-shot
  consensus: `k` concurrent proposers, a two-round fast path, and a
  fallback path (fallback voting → MVBA → a final commit round).
  Modelled in [Cadence/Chorus.lean](../Cadence/Chorus.lean).
* **Conductor** (`p2_conductor_proofs.tex`, the ACS version) — the
  window-based orchestrator that schedules slots. Modelled in
  [Cadence/Conductor.lean](../Cadence/Conductor.lean).
* **Cadence** (`p2_framework.tex`) — the extreme-pipelining glue that
  runs one slot-consensus instance per slot under the orchestrator and
  assembles the MCP log. Modelled in [Cadence/Cadence.lean](../Cadence/Cadence.lean).

Two auxiliary models cover the layer where the protocol's per-validator
reasoning is most intricate: the **fallback receipt/propose layer**
([Cadence/FallbackReceipt.lean](../Cadence/FallbackReceipt.lean) and companions), which
mechanises the per-validator layer where a real liveness bug was found
and fixed (see §5), and the *pre-fix* variant — the paper's receipt
rules as they stood **before** that bug fix, i.e. as published in
`arXiv:2607.02275v1` (§5; "pre-fix" is used in this sense throughout) —
kept as a machine-checked refutation.

A third model goes one level *below* the published paper: the **MVBA
instantiation** ([Cadence/Mvba.lean](../Cadence/Mvba.lean) and companions).
`mod:mvba` is an interface in the paper; the leader-based protocol that
implements it lives in the paper repository's *internal supplement*, which
is not yet part of the published paper and has neither tags nor versions,
so the model pins the paper-repository commit it was read against in its
header ([MvbaPlan.md](./MvbaPlan.md) §0). Its safety properties are the
three of `mod:mvba`, proven as for Chorus. It supplies the `MVBA` contract's
instance, which Chorus consumes as a class constraint and
[Cadence/System.lean](../Cadence/System.lean) fills in (§4 item 3).

### 1.1 How the layers correspond

Each paper module is a type class in
[Cadence/Interfaces.lean](../Cadence/Interfaces.lean); each layer of the
protocol is a Veil model that *implements* one contract and *consumes* the
contracts below it. The implication chain runs bottom-up, and every arrow is
a Lean instance rather than a correspondence argued in prose:

```
  Cadence.system_positional_log_safety                        System.lean
  MCP Safety for the composed system — no contract hypothesis left
                          ▲ instantiated at the instances below
  Cadence.positional_log_safety                          Composition.lean
  MCP Safety for the glue over ANY modules meeting the contracts
                          ▲
          ┌───────────────┴──────────────────┐
          │  Cadence — the pipelining glue   │            Cadence.lean
          │  instantiate orch : OrchestratorSafety
          │  instantiate sc   : SlotConsensusSafety
          └──────┬───────────────────────┬───┘
       filled by │                       │ filled by
  ┌──────────────┴────────────┐  ┌───────┴────────────────────────┐
  │ Conductor.orchestratorSafety│ │ Chorus.slotConsensusSafety     │
  │   Conductor.lean            │ │   Chorus.lean + Chorus/Proofs/ │
  │   instantiate acs : ACSSafety│ │  instantiate mvba : MVBASafety │
  └──────────────┬──────────────┘ └───────┬────────────────────────┘
                 │ no implementation      │ filled by
                 ▼ (standard primitive:   ▼
              ASSUMED   §4 item 3)     Mvba.mvbaSafety
                                        Mvba.lean + Mvba/Proofs/
```

| Paper module | Contract class | Implementation | Instance | Still owed |
|---|---|---|---|---|
| `mod:slotconsensus` | `SlotConsensusSafety` / `SlotConsensus` | `Cadence/Chorus.lean` | `Chorus.slotConsensusSafety` | `SlotConsensusTemporal` |
| `mod:orchestrator_2` | `OrchestratorSafety` / `Orchestrator` | `Cadence/Conductor.lean` | `Conductor.orchestratorSafety` | `OrchestratorTemporal` |
| `mod:mvba` | `MVBASafety` / `MVBA` | `Cadence/Mvba.lean` | `Mvba.mvbaSafety` | `MVBATemporal` |
| `mod:acs` | `ACSSafety` / `ACS` | — (out of scope) | — | the whole contract |

The fallback receipt/propose layer
([Cadence/FallbackReceipt.lean](../Cadence/FallbackReceipt.lean)) implements
no contract: it refines one step *inside* Chorus's fallback path (assembling
a valid meta-block from received receipts) at a finer per-validator grain
than the Chorus model uses, and is verified on its own terms (§5).

[CompositionContracts.md](./CompositionContracts.md) is the full account of
this layer: the two-level class design, what each instance proves, and the
seams that remain.

## 2. The methods

Four verification methods are combined — the numbering is a catalogue,
**not** a ranking of strength or soundness; every claim is checked by
at least one machine, and the trust base of each artefact is stated
(and, where possible, pinned in CI by `#guard_msgs`).

**Method 1 — inductive invariants, SMT-discharged** (labelled "sweep"
in the tables below). Each protocol model declares its safety
properties and helper invariants; Veil generates one verification
condition per (action × property) pair and discharges them with cvc5.

This table is the canonical home for these counts; other documents point
here rather than repeating them.

| Module | Actions | Declarations | VCs | Discharge |
|---|---|---|---|---|
| `Cadence/Chorus.lean` | 40 | 9 safety + 92 invariants + 1 step property | 4 222 | cvc5, **proof-reconstructed** (kernel-checked), + 11 manual Lean proofs for e-matching-divergent cells; the MVBA enters as a class constraint, so its axioms are hypotheses of every cell |
| `Cadence/Mvba.lean` | 24 | 3 safety + 25 invariants | 725 | cvc5, **proof-reconstructed** (kernel-checked), + 2 manual Lean proofs for the two argument-carrying cells (the lock-persistence step and cross-view certificate agreement) |
| `Cadence/FallbackReceipt.lean` | 9 | 1 safety + 20 invariants | 220 | cvc5, **proof-reconstructed** (kernel-checked, no trusted step) |
| `Cadence/Conductor.lean` | 7 | 5 safety + 15 invariants + 3 step properties | 189 | cvc5, **proof-reconstructed** (kernel-checked); the ACS enters as a class constraint |
| `Cadence/Cadence.lean` | 6 | 4 safety + 21 invariants | 182 | cvc5, **proof-reconstructed** (kernel-checked); the sub-protocols enter as class constraints, so the contract axioms are hypotheses of every cell |

The VC count is not arbitrary and can be recomputed from the model: one
condition per (label × safety-or-invariant), where the labels are the actions
plus the initializer; one per (action × step property); and one does-not-throw
condition per label. For the first three modules the total is pinned in the
build by `#veil_status` (§6); for the last two it is reported by the in-file
sweep.

**All five modules run with proof reconstruction** (`veil.smt.trust
false`): every ✅ is a proof re-checked by Lean's kernel, not a trusted
solver verdict. Where the VCs are discharged differs by module size:
`Cadence/Cadence.lean`/`Conductor.lean` run an in-file sweep
(`#check_invariants`); `Cadence/Chorus.lean`/`FallbackReceipt.lean`/`Mvba.lean`
only *state* their VCs (a persistent registry) and the per-action proof
files discharge them (§6). A per-cell fallback ladder (seed retries → the
alternative two-state encoding → manual Lean proofs) absorbs
reconstruction-resistant cells; no trusted islands are needed.

**Method 2 — exhaustive model checking (concrete instances).** Used
only where it is a *complete* method or strictly redundant — **no claim
about the final protocol rests on a bounded-instance check**:

* the **refutation** of the pre-fix receipt rules (§5) — exhibiting a
  reachable counterexample is complete evidence of a bug regardless of
  instance size; the found trace (`n = 3f+1`, `f = 1`) is pinned
  verbatim in the build;
* the **mutation test** of the MVBA instantiation
  ([Cadence/Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean)): with the
  `Pre-Prepare` handler's lock check removed, the checker exhibits two
  correct validators deciding differently — on a restriction of the mutant
  every run of which is a run of the mutant, so the evidence is complete
  in the same sense — which shows the proven invariants of
  `Cadence/Mvba.lean` are load-bearing and not merely true; the trace is
  pinned verbatim in the build;
* a **redundant regression check** over the receipt layer's structural
  invariants (23 975 states) — defense in depth alongside their
  unbounded SMT proofs, and a non-vacuity witness (the explored graph
  contains proposing runs).

**Method 3 — plain-Lean composition over reachable states.** Every
discharged VC is persisted as a named, kernel-checked theorem
(`#gen_theorems` in the small modules, `#prove_action` in the
proof-file families), and inductions over the generated `reachable`
relation assemble them into "every reachable state satisfies the
invariant clump" (`invariants_of_reachable`, plus one named
`reachable_<property>` projection per conjunct — emitted by
`#gen_composition` for all five verified modules: in the families'
`Certify.lean` files, and in `Cadence/Composition.lean` for the two small
ones), from which the paper's
*module contracts* ([Cadence/Interfaces.lean](../Cadence/Interfaces.lean)) are
instantiated. The contracts are type classes over an explicit abstract
state, in two levels — a first-order fragment the consuming Veil model
`instantiate`s as a class constraint (so the properties are the solver's
hypotheses, never restated), and the full class with every temporal and
quantitative obligation over explicit runs
([CompositionContracts.md](./CompositionContracts.md)):

* `Conductor ⊨ OrchestratorSafety` (`Conductor.orchestratorSafety`, every
  field proven — the two-state fields from Veil's transition bodies) and
  the paper's **positional MCP Safety** (`def:safety` over ordered logs) —
  [Cadence/Composition.lean](../Cadence/Composition.lean);
* `Chorus ⊨ SlotConsensusSafety` (`Chorus.slotConsensusSafety`) —
  [Cadence/Chorus/Compose.lean](../Cadence/Chorus/Compose.lean), over the composed
  certificate and named per-property projections of
  [Cadence/Chorus/Certify.lean](../Cadence/Chorus/Certify.lean);
* the **composed system** — the glue's MCP Safety instantiated at those two
  instances, with no contract hypothesis left
  (`Cadence.system_positional_log_safety`,
  [Cadence/System.lean](../Cadence/System.lean));
* what each implementation still owes of its *full* contract is a **missing
  class instance** — no `OrchestratorTemporal`, `SlotConsensusTemporal` or
  `MVBATemporal` at the fragment it proved — with a definition
  (`…_of_temporal`) that joins the two levels when one is supplied; these
  are §4 item 4 as types, restated nowhere;
* build totality of the receipt layer for **every** `n = 3f+1` —
  [Cadence/FallbackReceipt/Totality.lean](../Cadence/FallbackReceipt/Totality.lean),
  kernel-checked end-to-end;
* the **liveness argument's state-level content**, for every
  `n = 3f+1` — theorems rather than assumptions: the *progress
  dichotomy* (`Chorus.progress_dichotomy_of_saturation`,
  [Cadence/Chorus/Progress.lean](../Cadence/Chorus/Progress.lean) — in
  any reachable state where every honest validator has cast its path
  vote, per-proposer commitQCs from honest votes alone, or the MVBA
  invoked with evidence in the form of the decision handlers' bridge); its
  counting inputs — certificate formation and the fast-dominant
  commitQC ([Cadence/Chorus/Counting.lean](../Cadence/Chorus/Counting.lean)),
  the evidence pigeonhole
  ([Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean));
  and *network-level build totality*
  (`Chorus.build_totality_of_reachable`): a buildable meta-block entry
  from **any** accepted receipt supermajority, Byzantine members
  included. [Liveness.md](./Liveness.md) is the one-page summary.

**Method 4 — documented meta-theory.** What is deliberately *not*
inside Lean is stated as named assumptions and audited by hand (§4).
This is the one method that is weaker than the others — which is
exactly why §4 exists as its complete, auditable inventory.

## 3. Property coverage (what is proven, where)

The paper's headline properties and their formal counterparts:

| Paper claim | Formal artefact | Method |
|---|---|---|
| Chorus Agreement (`lemma:chorus-agreement`) | `safety [agreement_pos]`, `[agreement_pos_neg]`; instance field `agreement` in `Cadence/Chorus/Compose.lean` | sweep + composition |
| Chorus integrity | `safety [integrity_pos]`, `[integrity_pos_neg]` | sweep |
| Proposal inclusion / censorship resistance (`lemma:chorus-proposal-inclusion`) | `safety [proposal_inclusion]`, `[proposal_inclusion_no_neg]` (premise `all_honest_recorded`); instance field `proposal_inclusion` | sweep + composition |
| Hiding until the deadline (`lemma:chorus-hiding`) | protocol half: `safety [hiding_until_deadline]`; crypto half axiomatised (`ThresholdIBE`, [Cadence/Primitives.lean](../Cadence/Primitives.lean)) | sweep + axiom |
| Speculative-finality revertibility claim | `safety [speculative_agreement_pos]`, `[..._pos_neg]` (conditional on `no_equivocation` and `no_invalid_encoding`) | sweep |
| Chorus termination (`lemma:chorus-termination`) | fair-progress invariant layer + (F-\*)/(A-mvba) meta-axioms; untimed (no `ℓ` bound) | sweep + meta (§4) |
| "Fallback meta-block valid by construction" (`alg:fallback` build rule) | `certified_propose` (all `n`, SMT) + `build_totality_of_reachable` (all `n = 3f+1`, kernel-checked) | sweep + Lean |
| Evidence pigeonhole (per-proposer evidence always forms from `2f+1` honest fallback entries — the counting step of `lemma:chorus-termination`'s fallback branch) | `evidence_pigeonhole_of_reachable` ([Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean)), all `n = 3f+1` | sweep + Lean |
| Certificate formation (`FBCert`/`fbCommitQC` from all-honest participation; a per-proposer commitQC from any supermajority of honest fast commit votes — the counting steps of `lemma:chorus-termination`'s other branches) | `fbcert_of_honest_fallback_votes`, `fbcommitqc_of_honest_commit_votes`, `commitqc_of_honest_fast_dominant` ([Cadence/Chorus/Counting.lean](../Cadence/Chorus/Counting.lean)), all `n = 3f+1` | Lean (commitQC leg: sweep + Lean) |
| Progress dichotomy (`lemma:chorus-termination`'s case split as one statement: saturated reachable state ⇒ per-proposer commitQCs from honest votes alone, or MVBA invoked with per-proposer decide evidence) | `progress_dichotomy_of_saturation` ([Cadence/Chorus/Progress.lean](../Cadence/Chorus/Progress.lean)), all `n = 3f+1` | sweep + Lean |
| The pre-fix receipt rules are broken (the §7.2 finding) | pinned model-checker violation, [Cadence/FallbackReceipt/PreFix.lean](../Cadence/FallbackReceipt/PreFix.lean) | model check |
| The MVBA's lock check is load-bearing (`lem:lock-persistence`'s premise; the mutation test of `docs/MvbaPlan.md` §4): without it, two correct validators decide differently | pinned model-checker violation, [Cadence/Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) | model check |
| Conductor as the paper's orchestrator, state-level: open-prefix agreement, Monotonicity, Integrity (at most once), the observables' monotonicity and frames; boundedness in interval form | Conductor sweep + `Conductor.orchestratorSafety` (`Cadence/Composition.lean`) | sweep + composition |
| MCP Safety, positional form (`def:safety`) — for the glue over any contract instances, and for the composed system | `positional_log_safety` (`Cadence/Composition.lean`); `system_positional_log_safety` (`Cadence/System.lean`) | composition |
| Conductor/Cadence temporal claims (totality, ℓ-liveness, recovery, termination, quiescence) | fields of the `…Temporal` classes in `Cadence/Interfaces.lean`, stated over timed runs; the unproven subset per implementation is the field list of `OrchestratorTemporal` / `SlotConsensusTemporal`, of which this development supplies no instance | not proven — §4 item 4 |
| MVBA agreement, integrity, external validity (`mod:mvba`; the internal supplement's `thm:agreement` at the entries level and `lem:external-validity`, for its leader-based instantiation — `Cadence/Mvba.lean`'s header pins the referent) | `safety [agreement]`, `[integrity]`, `[external_validity]` in `Cadence/Mvba.lean`; instance fields of `Mvba.mvbaSafety` in `Cadence/Mvba/Compose.lean` | sweep + composition |
| MVBA Quiescence (`mod:mvba`), and the module's inputs and their observables | proven in `Mvba.mvbaSafety` (`Cadence/Mvba/Compose.lean`) from the transition bodies; only the timed fields are residual | composition |

## 4. The meta-assumption inventory

**This is the audit checklist.** Everything the Lean artefacts do *not*
establish, in one place; each item names where it is stated and why it is
believed sound. Nothing else in this repository requires a leap of faith —
the rest is re-derived by the machine on every build (see §6 and the pins
in [`Cadence.lean`](../Cadence.lean)).

The list is meant to be *checkable for completeness* rather than taken on
trust. Every assumption below has a **name**, and the named fairness and
oracle axioms — (F-justice), (F-byz), (A-mvba), (A-sc-termination),
(A-sc-totality) — appear verbatim in the Lean sources at the points where
they are consumed, so `grep -rn '(A-' Cadence/` enumerates the consumers
and would expose an axiom that had crept in without being listed here. The
network contract (item 1) is the exception and the reason item 1 comes
first: its names live in [ChorusDesign.md](./ChorusDesign.md) §3.1.1 rather
than in the code, and no tool checks it — the sources speak of "monotone"
relations, and it takes a human to confirm each use is positive.

1. **The monotone-network contract (M-update)+(M-frame)**
   ([ChorusDesign.md](./ChorusDesign.md) §3.1–§3.3): safety in the
   monotone model implies safety under asynchrony only if network
   relations are consulted positively. Veil does not enforce (M-frame);
   it is audited by hand, with three documented scoped exception
   categories (`fb_sign_neg`'s witnessed quorum; `cast_fb_commit`'s
   frozen decided-vector read; and seven *self-row* reads — a guard
   consulting a row of `msg_proposer_signed`/`msg_commit_cast`
   negatively, where the row is indexed by, and writable only by, the
   acting validator itself — enumerated in ChorusDesign.md §3.1).
2. **Fairness and oracle-termination axioms** ((F-justice), (F-byz),
   (A-mvba) — stated in the Chorus liveness section, composed in
   [ChorusDesign.md](./ChorusDesign.md) §7, summarised in
   [Liveness.md](./Liveness.md)). The liveness argument's state-level
   content is kernel-checked — the fair-progress invariants of the
   sweep, and the theorems of
   [Cadence/Chorus/Progress.lean](../Cadence/Chorus/Progress.lean),
   [Cadence/Chorus/Counting.lean](../Cadence/Chorus/Counting.lean) and
   [Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean) —
   so these assumptions contribute *temporal* content only, instances
   of "a continuously enabled fair action eventually fires":
   (F-justice) — weak fairness of honest actions (weak suffices:
   enabledness is monotone in this model); (F-byz) — Byzantine actions
   are unfair; (A-mvba) — the MVBA instance's own termination once every
   correct validator has proposed (probability-1, paper-level), whose
   protocol-side premises are theorem conclusions; the per-validator
   implementation refinement of the proposal build is the receipt
   layer (§5). Since Chorus consumes the MVBA as the class constraint
   `MVBASafety`, instantiated at the verified model
   ([Cadence/Mvba.lean](../Cadence/Mvba.lean); item 3), (A-mvba) is
   exactly the field `MVBATemporal.termination` **at `Mvba.mvbaSafety`**
   ([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean), item 4) —
   an obligation over the model's own transition system, of which the
   untimed model has no instance yet — together with (F-justice) on
   Chorus's `mvba_propose` (premise (i): every correct validator proposes)
   and on the decision handlers, whose enabledness has one leg the class
   does not give: the *completeness direction of the bridge* (a decided
   entry's certificate is on Chorus's network — what "publicly
   verifiable" means; `ChorusDesign.md` §7 item 4). Decomposing (A-mvba)
   into the MVBA instance's own fair-progress theorems is open work
   ([TODO.md](./TODO.md) § Liveness; the design constraints it must respect
   are [MvbaPlan.md](./MvbaPlan.md) §3).
3. **Primitive contracts as axioms**: `ThresholdIBE` (cryptographic
   hiding — genuinely an assumption, as for any crypto primitive;
   [Cadence/Primitives.lean](../Cadence/Primitives.lean)) and the `ACS`
   module contract ([Cadence/Interfaces.lean](../Cadence/Interfaces.lean))
   — a standard primitive whose implementation is out of scope, so no
   instance exists and every field is assumed. What *is* machine-checked
   is the consumption side for ACS: the Conductor takes `ACSSafety` as a
   class constraint, so it assumes exactly the class, with one stated
   bridge (the median-range `require` of `acs_decide`, justified by the
   class's quantitative validity through `Windows.lean`). The `MVBA`
   contract is **not** on this list, on either side: `Mvba.mvbaSafety`
   ([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)) instantiates
   its state-level fragment from the leader-based protocol of the paper
   repository's internal supplement ([Cadence/Mvba.lean](../Cadence/Mvba.lean);
   the referent is pinned in that header and is not yet part of the
   published paper), every field proven, and `Mvba.mvba_of_temporal` leaves
   only the timed fields (item 4); Chorus *consumes* the class as a
   constraint (`instantiate mvba : MVBASafety …`) with
   `Cadence/System.lean` filling it with that instance, so no MVBA
   property is assumed anywhere in the composed system. What that
   consumption leaves is **one stated bridge**, of the
   same kind as the ACS median bridge: Chorus's decision handlers
   `require` the decided entry's certificate against Chorus's own network
   relations (`vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)`, resp.
   the negative form), which is what the class's `Valid` — a parameter
   fixed before the module's state exists — *means* in a model whose
   signatures are network relations. It is documented at the handlers
   (`Cadence/Chorus.lean`), in `ChorusDesign.md` §4 and in
   [CompositionContracts.md](./CompositionContracts.md) §7 item 1; it
   removes no behaviour of a correct MVBA (public verifiability plus
   `external_validity`) and is safety-conservative if the MVBA were wrong.
   Chorus's two assumptions about the entry-vector projections
   (`mval_pos_functional`, `mval_pos_neg_excl`) are theorems at the
   instantiation (`Cadence/System.lean`, `chorusTheory_assumptions`); the
   one genuine hypothesis is that the abstract MVBA state Chorus starts
   from is initial. Note what is *not* on this list:
   the `ByzNodeSet` quorum/counting interface is **not** an assumption
   gap — its axioms are Lean-proven for the concrete `byzNodeSetFin`
   instance family, which covers every deployment size `n = 3f+1` with
   any Byzantine set of size `≤ f`. An end-to-end example instantiation
   of the remaining class stack (a `ThresholdIBE` model instance) is open
   work ([ChorusDesign.md](./ChorusDesign.md) §9).
4. **Temporal/quantitative module obligations**: totality, termination,
   `d_tot`-totality, Quiescence, boundedness, recovery — *fields* of the
   full contracts `Orchestrator`, `SlotConsensus`,
   `SlotConsensusWithTotality`, `ACS`, `MVBA` in
   [Cadence/Interfaces.lean](../Cadence/Interfaces.lean), stated over timed
   runs with an implementation-defined admissible-execution model. For the
   three implementations the exact unproven subset is the field list of a
   class that has **no instance** at the fragment they proved:
   `OrchestratorTemporal` ([Cadence/Composition.lean](../Cadence/Composition.lean);
   Totality, `B`-Boundedness, `R`-Recovery, the execution model),
   `SlotConsensusTemporal` ([Cadence/Chorus/Compose.lean](../Cadence/Chorus/Compose.lean);
   the participation interface, the clock, Termination, Quiescence — Chorus
   models no participation window) and `MVBATemporal`
   ([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean); the clock,
   the admissible-run model, `ℓ_MVBA` and Termination — the inputs, their
   observables and Quiescence are proven into the fragment, so nothing
   safety-shaped is left). The meta-axiom names
   ((A-orch-totality), (A-orch-boundedness), (A-orch-recovery),
   (A-sc-termination), (A-sc-totality), (A-acs-termination),
   (A-acs-totality)) are those fields' docstrings. The models are untimed;
   no formal artefact claims a latency bound.
5. **Scope**: single slot for Chorus (slot independence is argued, not
   modelled), no epochs/proposer rotation, chunk indices and
   erasure-code arithmetic abstracted
   ([ChorusDesign.md](./ChorusDesign.md) §3.4, §8), payload bytes not
   modelled.
6. **Composition seams**: (a) the glue's records of the slot-consensus
   inputs it does not drive into the contract (`sc_abandoned`, `proposed`)
   are its own, as the paper's local variables are — that its call *is*
   the instance's input is trace-level refinement, out of scope
   ([ChorusDesign.md](./ChorusDesign.md) §10.1); (b) the two fault patterns
   — the shared `FaultModel` and Chorus's `ByzNodeSet.is_byz` — meet in the
   hypothesis `hbyz` of `system_positional_log_safety`; (c) an
   implementation's `Admissible` execution model is data it defines
   (non-vacuity is a class axiom, the definition is one line to read).
   All three are named in [CompositionContracts.md](./CompositionContracts.md) §7.
7. **Trusted tooling**: Veil's VC generation and the concrete model
   checker are part of the trusted computing base everywhere (as is
   Lean's kernel). cvc5's `unsat` verdicts are *not* trusted — every
   sweep reconstructs its proofs kernel-checked (§6) — but its `sat`
   verdicts on the `sat trace` reachability sanity checks are (a wrong
   model there could only make a non-vacuity check vacuous, never a
   safety claim wrong). What sits inside that surface, and why an
   unrecognised action statement now fails the build rather than being
   silently mistranslated, is
   [Dependencies.md](./Dependencies.md) § "Trusted computing base".

## 5. The receipt layer: why the auxiliary models exist

The fallback receipt rules of `arXiv:2607.02275v1` contain a liveness bug: an
accepted EquivCert is never harvested, so a validator can propose an invalid
meta-block and never retry, which breaks the premise of the termination
proof. It was reported by a parallel formal-verification effort using Rocq,
confirmed against the paper sources here, and fixed in **v2** by a receipt
restriction plus an atomic build. The full record, including the
counterexample and which half of the fix is load-bearing, is
[ChorusDesign.md](./ChorusDesign.md) §7.2.

Because both versions are published, "pre-fix" and "fixed" name immutable
documents rather than an internal commit range. Two artefacts of this
development follow from the episode:

* the **fallback commit round** and the tightened wire format are modelled
  in `Cadence/Chorus.lean` rather than documented away; and
* the receipt/propose layer is mechanised **in both directions**: the v2
  design verified (including the counting argument, for every `n = 3f+1`,
  kernel-checked), and the v1 design refuted by exhaustive model checking,
  with the counterexample — the reported scenario — pinned in the build.

Keeping both directions in the build is what makes the refutation a standing
check rather than a one-off: a change that made the v1 rules verify, or the
v2 rules fail, breaks the build.

## 6. Trust base

The solver is not in it: every discharge is reconstructed as a Lean proof
term and re-checked by the kernel. The table below gives the axiom base per
artefact, each pinned by `#guard_msgs` where marked. Every pin is *also*
re-derived in the audit root [`Cadence.lean`](../Cadence.lean), so the whole
table can be read off one file:

| Artefact | Axioms | Pinned |
|---|---|---|
| `Cadence.positional_log_safety`, `Conductor.orchestratorSafety`, `Conductor.orchestrator_of_temporal` (`Cadence/Composition.lean`) | `propext, Classical.choice, Quot.sound` | ✓ |
| `Cadence.system_positional_log_safety` (`Cadence/System.lean`) | same | ✓ |
| `Chorus.invariants_of_reachable` + per-property projections (`Cadence/Chorus/Certify.lean`) | same | ✓ + `#veil_status`: 4222/4222 real |
| `FallbackReceipt.invariants_of_reachable` (`Cadence/FallbackReceipt/Certify.lean`) | same | ✓ + `#veil_status`: 220/220 real |
| `FallbackReceipt.build_totality_of_reachable` (`Cadence/FallbackReceipt/Totality.lean`) | same | ✓ |
| `Chorus.slotConsensusSafety`, `Chorus.slotConsensus_of_temporal` (`Cadence/Chorus/Compose.lean`) | same | ✓ |
| `Chorus.evidence_pigeonhole_of_reachable` (`Cadence/Chorus/Pigeonhole.lean`) | same | ✓ |
| `Mvba.invariants_of_reachable` + per-property projections (`Cadence/Mvba/Certify.lean`) | same | ✓ + `#veil_status`: 725/725 real |
| `Mvba.mvbaSafety`, `Mvba.mvba_of_temporal` (`Cadence/Mvba/Compose.lean`) | same | ✓ |
| the `FallbackReceiptPreFix` refutation (`Cadence/FallbackReceipt/PreFix.lean`) | expected model-checker violation (trace) | ✓ |
| the `MvbaNoLock` refutation (`Cadence/Mvba/NoLock.lean`) | expected model-checker violation (trace) | ✓ |

cvc5's `unsat` verdicts are trusted nowhere: every discharge runs with proof
reconstruction (`veil.smt.trust false`), so every proof is re-checked by
Lean's kernel. No composition consumes a stub: every pinned artefact rests on
persisted, kernel-checked proof terms.

The mechanism that makes this fit on a 32 GB machine is the
**verified-module file family**, sketched as a diagram in
[README.md](../README.md) § "How the files feed each other". A model file
(`Cadence/Chorus.lean`, `Cadence/FallbackReceipt.lean`, `Cadence/Mvba.lean`)
elaborates the transition system and persists
its VC *statements* in an olean-carried registry — it runs no solver
and persists no proofs. One proof file per action
(`<Model>/Proofs/<Action>.lean`) re-creates that action's VCs from the
registry — statements identical to what the model declares, by
construction — discharges them (cvc5 + reconstruction), persists every
proof as a kernel-checked theorem in its own small olean, and exports
one "this action preserves the invariants" lemma; keeping each action's
proofs in their own process/olean is what bounds memory (~5 GB per file
cold). The quorum-intersection cells that SMT cannot find are manual
`#prove_vc … by <tactic>` cells in their actions' proof files, consumed
after a statement check — the statement itself always comes from the
registry, and the tactics project invariant conjuncts by name
(`Cadence/ProofPrelude.lean`), so nothing in a proof file restates or
hand-indexes what the model declares. `<Model>/Certify.lean` composes the per-action lemmas
(`#gen_composition`) into `invariants_of_reachable` plus named
per-property projections, pins the axiom base, and re-audits the whole
set with a pinned `#veil_status` line — per VC, a real,
statement-matching, kernel-checked theorem must be in scope, or the
build fails.

What remains trusted is inventoried in §4 item 7 — Lean's kernel,
Veil's VC generation, the model checker where used, and the solver's
`sat` verdicts on non-load-bearing `sat trace` checks.

## 7. The verification pipeline this rests on

The tool itself is a fork of Veil, developed separately; its changes are
documented there, one branch per change. This repository records only *which*
capabilities it depends on and why — [Dependencies.md](./Dependencies.md).

Four of them explain the shape of the file tree:

* a **persistent registry of VC statements** plus cross-file proving
  commands, so one model's proofs can be spread over many small files (§6);
* a **kernel-replaying proof cache**, which makes re-validation cost minutes
  and be deterministic rather than solver-seed-dependent;
* **composition emission** and the **`#veil_status`** audit command, which
  make the reachability certificates and the "nothing is stubbed" claim
  machine-derived rather than narrated;
* scaling fixes without which a module at Chorus's VC scale does not
  elaborate at all.

One measurement bounds what a future scaling effort can win: reconstruction
proof terms of the same action share 65–92 % of their term mass. Most of a
single term is not about that action at all; it is the SMT pipeline
re-deriving the same embedding of the shared hypothesis context, once per
verification condition. Hoisting that shared processing into named,
once-checked lemmas is the next structural lever, and is worth roughly that
share.

## 8. History

Decision history and per-build records intentionally live outside this
document: [History.md](./History.md) (build history, per-module status) and
the git log. [ChorusDesign.md](./ChorusDesign.md) §7.2 carries the one
protocol bug found so far, because that record is a result rather than a
build log.
