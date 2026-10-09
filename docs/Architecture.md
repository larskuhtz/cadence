# Cadence verification — architecture

*The architecture of the verification: its structure, its methods and its
trust bases. [The guide's chapter 1](https://larskuhtz.github.io/cadence/guide/approach/) introduces the structure;
this page is the authority for the per-module counts (§2) and for the
assumption inventory (§4).*

This file explains how the formalisation is structured, what each part
establishes and by what method, and where its trust boundaries and
meta-theoretic seams lie. **§4 is the audit checklist**: everything the
machine does not establish, in one place; [the guide's chapter
4](https://larskuhtz.github.io/cadence/guide/modelling-idioms/) explains the modelling idioms it lists. The end
theorems and their trust base are on one page,
[Cadence.lean](../Cadence.lean). The per-model design rationale lives one
level down: [ChorusDesign.md](ChorusDesign.md) for the Chorus model, and
[ConductorDesign.md](ConductorDesign.md) plus the module headers of
[Cadence/Cadence.lean](../Cadence/Cadence.lean) and
[Cadence/Conductor.lean](../Cadence/Conductor.lean) for the
composition-layer models.

## 1. What is being verified

[Cadence](https://www.category.xyz/cadence) (`arXiv:2607.02275`; the
paper target is [PaperAlignment.md](PaperAlignment.md) §0, and the root
[README.md](../README.md) says how to resolve the label names used here) is a BFT consensus design with three layers, and the
formalisation mirrors that decomposition one-to-one:

* **Chorus** (Appendix C (`section:slot_agreement`)) — the per-slot one-shot
  consensus: `k` concurrent proposers, a two-round fast path, and a
  fallback path (fallback voting → MVBA → a final commit round).
  Modelled in [Cadence/Chorus.lean](../Cadence/Chorus.lean).
* **Conductor** (Appendix D (`section:conductor-formal`), the ACS version) — the
  window-based orchestrator that schedules slots. Modelled in
  [Cadence/Conductor.lean](../Cadence/Conductor.lean).
* **Cadence** (Appendix B (`section:framework`)) — the extreme-pipelining glue that
  runs one slot-consensus instance per slot under the orchestrator and
  assembles the MCP log. Modelled in [Cadence/Cadence.lean](../Cadence/Cadence.lean).

An auxiliary model covers the layer where the protocol's per-validator
reasoning is most intricate: the **fallback receipt/propose layer**
([Cadence/FallbackReceipt.lean](../Cadence/FallbackReceipt.lean) and companions), the
rules by which each validator turns the evidence it has received into a
valid proposal (§5).

A further model goes one level below the paper's main body: the **MVBA
instantiation** ([Cadence/Mvba.lean](../Cadence/Mvba.lean) and companions).
Module 3 (`mod:mvba`) is an interface in the main body; the leader-based
protocol that implements it is specified in the paper repository's
internal supplement, which is part of the paper target
([PaperAlignment.md](PaperAlignment.md) §0). Its safety properties are the
three of Module 3 (`mod:mvba`), proven as for Chorus. It supplies the `MVBA` contract's
instance, which Chorus consumes as a class constraint and
[Cadence/System.lean](../Cadence/System.lean) fills in (§4 item 3).

### 1.1 How the layers correspond

Each paper module is a type class in
[Cadence/Interfaces.lean](../Cadence/Interfaces.lean); each layer of the
protocol is a Veil model that *implements* one contract and *consumes* the
contracts below it. Each arrow reads "fills the contract constraint above
it", and each is a Lean instance rather than a correspondence argued in
prose. The dashed box is the ACS, an assumed module (§4 item 3).

![The modules and their contracts: the composed claims on top; the glue, which consumes the Orchestrator and SlotConsensus contracts; the Conductor, which meets Orchestrator and consumes the assumed ACS; Chorus, which meets SlotConsensus and consumes the MVBA contract, met by the MVBA model; the receipt layer beside Chorus.](diagrams/modules-contracts.svg)

| Paper module | Contract class | Implementation | Instances |
|---|---|---|---|
| Module 1 (`mod:slotconsensus`) | `SlotConsensusSafety` / `SlotConsensus` | [Cadence/Chorus.lean](../Cadence/Chorus.lean) | `Chorus.slotConsensusSafety`, `Chorus.chorusTemporal`, the full `Chorus.slotConsensusFull` |
| Module 2 (`mod:orchestrator_2`) | `OrchestratorSafety` / `Orchestrator` | [Cadence/Conductor.lean](../Cadence/Conductor.lean) | `Conductor.orchestratorSafety`, `Conductor.conductorTemporal`, the full `Conductor.conductorFull`, for every ACS meeting its contract |
| Module 3 (`mod:mvba`) | `MVBASafety` / `MVBA` | [Cadence/Mvba.lean](../Cadence/Mvba.lean) | `Mvba.mvbaSafety`, `Mvba.mvbaTemporal`, the full `Mvba.mvbaFull` |
| Module 4 (`mod:acs`) | `ACSSafety` / `ACS` | assumed module | the ideal model `Cadence.IdealAcs.acsSafety`, `Cadence.IdealAcs.acsTemporal` ([IdealAcs.lean](../Cadence/Conductor/IdealAcs.lean)), a consistency witness |

The fallback receipt/propose layer
([Cadence/FallbackReceipt.lean](../Cadence/FallbackReceipt.lean)) implements
no contract: it refines one step *inside* Chorus's fallback path (assembling
a valid meta-block from received receipts) at a finer per-validator grain
than the Chorus model uses, and is verified on its own terms (§5).

[CompositionContracts.md](CompositionContracts.md) is the full account of
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
| [Cadence/Chorus.lean](../Cadence/Chorus.lean) | 56 | 9 safety + 100 invariants + 1 step property | pinned: `#veil_status Chorus` in [Chorus/Certify.lean](../Cadence/Chorus/Certify.lean) | cvc5, **proof-reconstructed** (kernel-checked), + 59 manual Lean proofs for e-matching-divergent or near-budget cells (six of them the Byzantine assembly actions' copies of the collector's cells), and one cell that runs the automatic solver step with the Bool-atom fold off rather than a hand proof (`vote × fastqc_complete_implies_mvba_evidence`; [Dependencies.md](Dependencies.md) § "Native shared libraries"); the MVBA enters as a class constraint, so its axioms are hypotheses of every cell |
| [Cadence/Mvba.lean](../Cadence/Mvba.lean) | 29 | 3 safety + 50 invariants + 1 step property | pinned: `#veil_status Mvba` in [Mvba/Certify.lean](../Cadence/Mvba/Certify.lean) | cvc5, **proof-reconstructed** (kernel-checked), + 9 manual Lean proofs: 5 for the argument-carrying cells (the lock-persistence step, at both actions that create a prepare certificate; cross-view certificate agreement, at both actions that create a commit certificate; and agreement at the decision `form_own_commitqc` makes), and 4 frame cells at the two timeout actions that the solver found too slowly for a CI runner |
| [Cadence/FallbackReceipt.lean](../Cadence/FallbackReceipt.lean) | 9 | 1 safety + 20 invariants | pinned: `#veil_status FallbackReceipt` in [FallbackReceipt/Certify.lean](../Cadence/FallbackReceipt/Certify.lean) | cvc5, **proof-reconstructed** (kernel-checked, no trusted step) |
| [Cadence/Conductor.lean](../Cadence/Conductor.lean) | 6 | 5 safety + 19 invariants + 3 step properties | 193 | cvc5, **proof-reconstructed** (kernel-checked); the ACS enters as a class constraint |
| [Cadence/Cadence.lean](../Cadence/Cadence.lean) | 7 | 4 safety + 22 invariants | 216 | cvc5, **proof-reconstructed** (kernel-checked); the sub-protocols enter as class constraints, so the contract axioms are hypotheses of every cell |

The VC count is not arbitrary and can be recomputed from the model: one
condition per (label × safety-or-invariant), where the labels are the actions
plus the initializer; one per (action × step property); and one does-not-throw
condition per label. For the first three modules the total is pinned in the
build by `#veil_status` (§6); for the last two it is reported by the in-file
sweep.

**All five modules run with proof reconstruction** (`veil.smt.trust
false`): every ✅ is a proof re-checked by Lean's kernel, not a trusted
solver verdict. Where the VCs are discharged differs by module size:
[Cadence/Cadence.lean](../Cadence/Cadence.lean)/[Conductor.lean](../Cadence/Conductor.lean) run an in-file sweep
(`#check_invariants`); [Cadence/Chorus.lean](../Cadence/Chorus.lean)/[FallbackReceipt.lean](../Cadence/FallbackReceipt.lean)/[Mvba.lean](../Cadence/Mvba.lean)
only *state* their VCs (a persistent registry) and the per-action proof
files discharge them (§6). A per-cell fallback ladder (seed retries → the
alternative two-state encoding → manual Lean proofs) absorbs
reconstruction-resistant cells; no trusted islands are needed.

**Method 2 — exhaustive model checking (concrete instances).** Used
only where it is a *complete* method or strictly redundant — **no claim
about the final protocol rests on a bounded-instance check**:

* the **mutation test** of the MVBA instantiation
  ([Cadence/Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean)): with the
  `Pre-Prepare` handler's lock check removed, the checker exhibits two
  correct validators deciding differently — exhibiting a reachable
  counterexample is complete evidence regardless of instance size, and
  it is found on a restriction of the mutant every run of which is a run
  of the mutant — which shows the proven invariants of
  [Cadence/Mvba.lean](../Cadence/Mvba.lean) are load-bearing and not merely true; the trace is
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
`Certify.lean` files, and in [Cadence/Composition.lean](../Cadence/Composition.lean) for the two small
ones), from which the paper's
*module contracts* ([Cadence/Interfaces.lean](../Cadence/Interfaces.lean)) are
instantiated. The contracts are type classes over an explicit abstract
state, in two levels — a first-order fragment the consuming Veil model
`instantiate`s as a class constraint (so the properties are the solver's
hypotheses, never restated), and the full class with every temporal and
quantitative obligation over explicit runs
([CompositionContracts.md](CompositionContracts.md)):

* `Conductor ⊨ OrchestratorSafety` (`Conductor.orchestratorSafety`, every
  field proven — the two-state fields from Veil's transition bodies) and
  the paper's **positional MCP Safety** (Definition 1 (`def:safety`) over ordered logs) —
  [Cadence/Composition.lean](../Cadence/Composition.lean);
* `Chorus ⊨ SlotConsensusSafety` (`Chorus.slotConsensusSafety`) —
  [Cadence/Chorus/Compose.lean](../Cadence/Chorus/Compose.lean), over the composed
  certificate and named per-property projections of
  [Cadence/Chorus/Certify.lean](../Cadence/Chorus/Certify.lean);
* the **composed system** — the glue's MCP Safety instantiated at those two
  instances, conditional only on the Conductor's ACS contract `ACSSafety`
  (`Cadence.system_positional_log_safety`,
  [Cadence/System.lean](../Cadence/System.lean));
* the Conductor's and Chorus's temporal levels **are** instantiated:
  `Conductor.conductorTemporal` at `Conductor.orchestratorSafety`, for an
  arbitrary ACS meeting its contract
  ([Cadence/Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean)),
  and `Chorus.chorusTemporal` at `Chorus.slotConsensusSafety`
  ([Cadence/Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean)), each
  joined into its full contract by the definition (`…_of_temporal`) that
  hands the fragment back by `rfl`;
* the MVBA's temporal level **is** instantiated: `Mvba.mvbaTemporal`
  (`MVBATemporal` with `ℓ_MVBA`-Termination, the supplement's `O(fΔ)`) at
  `Mvba.mvbaSafety`, the fragment the composed system runs, joined into the
  full `MVBA` as `Mvba.mvbaFull`, from named hypotheses (§4 item 4) —
  [Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean);
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
  included. [Liveness.md](Liveness.md) is the one-page summary;
* **Chorus termination over runs**, for every `n = 3f+1`
  (`Chorus.termination`,
  [Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)): the temporal argument on
  top of that content, from the named premises of §4 item 2, consuming
  `Mvba.termination` for the MVBA arm. Untimed;
* **Chorus's timed claims over timed runs**: `d_tot`-totality
  (`Chorus.totality`, [Cadence/Chorus/Totality.lean](../Cadence/Chorus/Totality.lean))
  and ℓ-termination at the paper's `5Δ + ℓ_MVBA` (`Chorus.timed_termination`,
  [Cadence/Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean)),
  with the sharper `4Δ + ℓ_MVBA` (plus `9δ` local steps) from the same
  premises (`Chorus.timed_termination_tight`), under the timing model of
  [Cadence/Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean); they
  are the timing fields of `Chorus.chorusWithTotality`;
* **the Conductor's timed claims over timed runs**: `d_tot`-Totality
  (`Conductor.totality`), `(2W − p)`-Boundedness (`Conductor.boundedness`)
  and `(2Wτ)`-Recovery (`Conductor.recovery`), under the timing model of
  [Cadence/Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean),
  for an arbitrary ACS meeting its contract;
* **the composed system's timed claims**: Corollary 4, Lemma 5,
  `𝓡`-Liveness and censorship resistance (`Composed.corollary4`,
  `Composed.boundedConcurrency`, `Composed.liveness`, `Composed.censorship`,
  [Cadence/Composed/](../Cadence/Composed/Schedule.lean)), with every
  condition each module takes from its caller discharged as a theorem
  about the composed run;
* **non-vacuity of every liveness claim**: one model and run per leg
  meeting all of a claim's premises at once — the MVBA's
  ([Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean)), Chorus's
  ([Cadence/Chorus/Witness.lean](../Cadence/Chorus/Witness.lean)) and the
  composed system's, which covers the Conductor's claims too
  ([Cadence/Composed/Witness.lean](../Cadence/Composed/Witness.lean));
  [Premises.md](Premises.md) has the ledgers.

**Method 4 — documented meta-theory.** What is deliberately *not*
inside Lean is stated as named assumptions and audited by hand (§4).
This is the one method that is weaker than the others — which is
exactly why §4 exists as its complete, auditable inventory.

## 3. Property coverage (what is proven, where)

The paper's headline properties and their formal counterparts:

| Paper claim | Formal artefact | Method |
|---|---|---|
| Chorus Agreement (Lemma 9 (`lemma:chorus-agreement`)) | `safety [agreement_pos]`, `[agreement_pos_neg]`; instance field `agreement` in [Cadence/Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) | sweep + composition |
| Chorus integrity | `safety [integrity_pos]`, `[integrity_pos_neg]` | sweep |
| Proposal inclusion / censorship resistance (Lemma 10 (`lemma:chorus-proposal-inclusion`)) | `safety [proposal_inclusion]`, `[proposal_inclusion_no_neg]` (premise `all_honest_recorded`); instance field `proposal_inclusion` | sweep + composition |
| Hiding until the deadline (Lemma 7 (`lemma:chorus-hiding`)) | protocol half: `safety [hiding_until_deadline]`; crypto half axiomatised (`ThresholdIBE`, [Cadence/Primitives.lean](../Cadence/Primitives.lean)) | sweep + axiom |
| Speculative-finality revertibility claim | `safety [speculative_agreement_pos]`, `[..._pos_neg]` (conditional on `no_equivocation` and `no_invalid_encoding`) | sweep |
| Chorus termination (Lemma 11 (`lemma:chorus-termination`)), bound-erased: every correct validator finalizes the slot, at every `n = 3f+1` | `Chorus.termination` ([Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)), from the premises `FJustice`, `MvbaAdmissible`, `ValidBridge` of [Cadence/Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean) (§4 item 2); consumes `Mvba.termination`; untimed (no `5Δ + ℓ_MVBA` bound) | sweep + Lean over runs |
| Chorus ℓ-termination, timed (Lemma 11 (`lemma:chorus-termination`)): every correct validator finalizes by `max(t, GST) + 5Δ + ℓ_MVBA` (plus `9δ` local steps), at every `n = 3f+1`; and by `4Δ + ℓ_MVBA + 9δ` from the same premises (F4) | `Chorus.timed_termination`, `Chorus.timed_termination_tight` ([Cadence/Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean)), from the timing model of [Cadence/Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean), `ValidBridge` and the caller's four conditions; consumes the MVBA contract's `T.termination`; at the system's MVBA `Chorus.timed_termination_atMvba` and `Chorus.timed_termination_tight_atMvba`, whose MVBA caller clauses are derived from Chorus's rows (`Chorus.relayedWhileActive_of_timedJustice`, `Chorus.availWithin_of_timedJustice`) | Lean over timed runs |
| Chorus `d_tot`-totality (Proposition 4 (`prop:chorus-totality`)): `Δ + 2δ` after the first correct finalization, at a participation tolerance `d` in general | `Chorus.totality`, `Chorus.totality_paper` ([Cadence/Chorus/Totality.lean](../Cadence/Chorus/Totality.lean)) | Lean over timed runs |
| "Fallback meta-block valid by construction" (Algorithm 5 (`alg:fallback`) build rule) | `certified_propose` (all `n`, SMT) + `build_totality_of_reachable` (all `n = 3f+1`, kernel-checked) | sweep + Lean |
| Evidence pigeonhole (per-proposer evidence always forms from `2f+1` honest fallback entries — the counting step of Lemma 11 (`lemma:chorus-termination`)'s fallback branch) | `evidence_pigeonhole_of_reachable` ([Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean)), all `n = 3f+1` | sweep + Lean |
| Certificate formation (`FBCert`/`fbCommitQC` from all-honest participation; a per-proposer commitQC from any supermajority of honest fast commit votes — the counting steps of Lemma 11 (`lemma:chorus-termination`)'s other branches) | `fbcert_of_honest_fallback_votes`, `fbcommitqc_of_honest_commit_votes`, `commitqc_of_honest_fast_dominant` ([Cadence/Chorus/Counting.lean](../Cadence/Chorus/Counting.lean)), all `n = 3f+1` | Lean (commitQC leg: sweep + Lean) |
| Progress dichotomy (Lemma 11 (`lemma:chorus-termination`)'s case split as one statement: saturated reachable state ⇒ per-proposer commitQCs from honest votes alone, or MVBA invoked with per-proposer decide evidence) | `progress_dichotomy_of_saturation` ([Cadence/Chorus/Progress.lean](../Cadence/Chorus/Progress.lean)), all `n = 3f+1` | sweep + Lean |
| The MVBA's lock check is load-bearing (Supplement, Lemma 8 (`lem:lock-persistence`)'s premise; the mutation test of [docs/MvbaPlan.md](MvbaPlan.md) §4): without it, two correct validators decide differently | pinned model-checker violation, [Cadence/Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) | model check |
| Conductor as the paper's orchestrator, state-level: open-prefix agreement, Monotonicity, Integrity (at most once), the observables' monotonicity and frames; boundedness in interval form | Conductor sweep + `Conductor.orchestratorSafety` ([Cadence/Composition.lean](../Cadence/Composition.lean)) | sweep + composition |
| MCP Safety, positional form (Definition 1 (`def:safety`)) — for the glue over any contract instances, and for the composed system | `positional_log_safety` ([Cadence/Composition.lean](../Cadence/Composition.lean)); `system_positional_log_safety` ([Cadence/System.lean](../Cadence/System.lean)) | composition |
| Conductor temporal claims (Totality, `d_tot`-Totality, `(2W − p)`-Boundedness, `(2Wτ)`-Recovery; Lemmas 14–16) | `Conductor.totality`, `Conductor.boundedness`, `Conductor.recovery` ([Cadence/Conductor/Induction.lean](../Cadence/Conductor/Induction.lean), [Boundedness.lean](../Cadence/Conductor/Boundedness.lean), [Recovery.lean](../Cadence/Conductor/Recovery.lean)); the contract fields in `Conductor.conductorTemporal` and `Conductor.conductorWithTotality` ([Cadence/Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean)), for an arbitrary ACS meeting its contract, under the timing model of §4 item 4 | Lean over timed runs |
| The composed system's timed claims: Corollary 4 (`cor:chorus-correctness-within-cadence`), bounded concurrency (Lemma 5 (`lemma:cadence-bounded-concurrency`)), `𝓡`-Liveness (Lemma 2 (`lemma:cadence-liveness`)) and `𝓡`-censorship resistance (Definition 3 (`def:censorship-resistance`)) | `Composed.corollary4`, `Composed.boundedConcurrency`, `Composed.liveness`, `Composed.censorship` and the `_sharp` forms ([Cadence/Composed/](../Cadence/Composed/Schedule.lean)), under the premises of [Premises.md](Premises.md) §0 | Lean over timed runs |
| Non-vacuity: every premise of a liveness claim holds together with the others | `Mvba.*_premises_satisfiable`, `Chorus.*_premises_satisfiable`, `Composed.Witness.*_premises_satisfiable` ([Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean), [Cadence/Chorus/Witness.lean](../Cadence/Chorus/Witness.lean), [Cadence/Composed/Witness.lean](../Cadence/Composed/Witness.lean)) | Lean (one model and run each) |
| MVBA agreement, integrity, external validity (Module 3 (`mod:mvba`); the internal Supplement, Theorem 1 (`thm:agreement`) at the entries level and Supplement, Lemma 9 (`lem:external-validity`), for its leader-based instantiation — [Cadence/Mvba.lean](../Cadence/Mvba.lean)'s header pins the referent) | `safety [agreement]`, `[integrity]`, `[external_validity]` in [Cadence/Mvba.lean](../Cadence/Mvba.lean); instance fields of `Mvba.mvbaSafety` in [Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean) | sweep + composition |
| MVBA Quiescence (Module 3 (`mod:mvba`)), and the module's inputs and their observables | proven in `Mvba.mvbaSafety` ([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)) from the transition bodies | composition |
| MVBA `ℓ_MVBA`-Termination (Module 3 (`mod:mvba`); the internal Supplement, Theorem 2 (`thm:termination`), `O(fΔ)` at `k = f + 1`) | `Mvba.bounded_termination` ([Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean)); the contract field in `Mvba.mvbaTemporal` ([Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)), under the timing model and hypotheses of §4 item 4 | Lean over timed runs |

## 4. The meta-assumption inventory

**This is the audit checklist.** Everything the Lean artefacts do *not*
establish, in one place; each item names where it is stated and why it is
believed sound. Nothing else in this repository requires a leap of faith —
the rest is re-derived by the machine on every build (see §6 and the pins
in [Cadence.lean](../Cadence.lean)).

The list is meant to be *checkable for completeness* rather than taken on
trust. Every assumption below has a **name**. The premises of the liveness
theorems are named definitions, listed on one page (item 2), and the
assumption names — (A-viewsync), (A-leader-rotation-k), and the assumed
ACS's (A-acs-termination) and (A-acs-totality) — appear verbatim in the
Lean sources where they are consumed, so `grep -rn '(A-' Cadence/`
enumerates the consumers and would expose an assumption that had crept in
without being listed here. The
locality rules (item 1) are the exception and the reason item 1 comes
first: they live in [Locality.md](Locality.md) rather than in the code,
and no tool checks them yet — it takes a human, with the audit table, to
confirm each action follows them.

1. **The locality rules** ([Locality.md](Locality.md)): a model describes
   a distributed protocol, and safety in its monotone network implies
   safety under asynchrony ([ChorusDesign.md](ChorusDesign.md) §3.2), only
   if every action follows them — a correct validator reads its own state,
   messages positively (its own sends in either polarity), global time,
   configuration and its sub-protocol at its own index, and writes only its
   own state and messages under its own name; a Byzantine validator may do
   anything except forge a signature, write what it does not own, or change
   the sub-protocol other than through its contract (Locality.md §4.2,
   B1–B3); the environment touches only its own state; auxiliary records
   are read by no action. Veil does not
   enforce them. They are stated for pattern matching and checked by hand,
   action by action: the guide's audit table for Chorus
   ([guide/audit/Chorus.tsv](guide/audit/Chorus.tsv)), and Locality.md §7
   for the status of each model.
2. **Liveness premises** — the hypotheses of the liveness theorems, never
   axioms. **[Premises.md](Premises.md) is their one page**: for every
   headline claim, each premise with its role, why it is plausible, the
   witness theorem showing all of them hold together, and the proof step
   that uses it. The liveness argument's state-level content is
   kernel-checked — the fair-progress invariants of the sweep, and the
   theorems of [Cadence/Chorus/Progress.lean](../Cadence/Chorus/Progress.lean),
   [Cadence/Chorus/Counting.lean](../Cadence/Chorus/Counting.lean) and
   [Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean) —
   and so is the temporal argument over runs. What has to be believed is
   that the premises describe the executions that matter. The tagged names
   a `grep` finds are on that page: (F-justice), (A-viewsync), (F-avail),
   (F-relay) and their timed forms, and (A-leader-rotation-k). Two need
   a word here:
   * **(F-byz)** is the absence of a premise: no fairness is asked of the
     `byz_*` labels, so no progress relies on adversarial help.
   * **The MVBA's termination is a theorem, not a premise.** Chorus's
     claims apply `Mvba.termination` (and the MVBA contract's timed
     `termination`) to the run's MVBA steps, and derive that theorem's
     caller premises.
3. **Primitive contracts as axioms**: `ThresholdIBE` (cryptographic
   hiding — genuinely an assumption, as for any crypto primitive;
   [Cadence/Primitives.lean](../Cadence/Primitives.lean)) and the `ACS`
   module contract ([Cadence/Interfaces.lean](../Cadence/Interfaces.lean))
   — an assumed module: the target leaves the ACS unspecified (P17), so
   no protocol here implements it and every field is assumed. A plain-Lean
   ideal ACS (`Cadence.IdealAcs.acsSafety`, `acsTemporal`) shows the
   contract satisfiable; it is a model, not a protocol. What *is*
   machine-checked is the consumption side: the Conductor takes the ACS's
   two levels as class constraints and hypotheses, so it assumes exactly
   the class. The first slot each validator computes from its decided set
   is constrained by two model assumptions (`[acs_first_local]`,
   `[acs_first_bracket]`), which the paper's lower median meets under the
   fault bound (`Cadence.lowerMedian_first_assumptions`,
   [AcsMedian.lean](../Cadence/AcsMedian.lean)). The `MVBA`
   contract is **not** on this list, on either side: `Mvba.mvbaSafety`
   ([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)) instantiates
   its state-level fragment from the leader-based protocol of the paper
   repository's internal supplement ([Cadence/Mvba.lean](../Cadence/Mvba.lean);
   the referent is the paper target), every field proven, and `Mvba.mvba_of_temporal` leaves
   only the timed fields (item 4); Chorus *consumes* the class as a
   constraint (`instantiate mvba : MVBASafety …`) with
   [Cadence/System.lean](../Cadence/System.lean) filling it with that instance, so no MVBA
   property is assumed anywhere in the composed system. What that
   consumption leaves is **one stated bridge**, of the
   same kind as the ACS median bridge: Chorus's decision handlers and the
   handlers of the `CommitQC` route `require` the certificate the
   representation names for an entry against Chorus's own network
   relations (a vote quorum for a `FastQC` entry, a fallback quorum and the
   `FBCert` for a `FallbackQC` entry, resp. the negative form), which is
   what the class's `Valid` — a parameter
   fixed before the module's state exists — *means* in a model whose
   signatures are network relations. It is documented at the handlers
   ([Cadence/Chorus.lean](../Cadence/Chorus.lean)), in [ChorusDesign.md](ChorusDesign.md) §4 and in
   [CompositionContracts.md](CompositionContracts.md) §7 item 1; it
   removes no behaviour of a correct MVBA (public verifiability plus
   `external_validity`) and is safety-conservative if the MVBA were wrong.
   Chorus's two assumptions about the entry-vector projections
   (`mval_pos_functional`, `mval_pos_neg_excl`) are theorems at the
   instantiation ([Cadence/System.lean](../Cadence/System.lean), `chorusTheory_assumptions`); the
   one genuine hypothesis is that the abstract MVBA state Chorus starts
   from is initial. Note what is *not* on this list:
   the `ByzNodeSet` quorum interface and its counting extension
   `ByzNodeSetCounting` are **not** an assumption gap — their axioms are
   Lean-proven for the concrete `byzNodeSetFin` instance family, which
   covers every deployment size `n = 3f+1` with any Byzantine set of size
   `≤ f` (and `byzNodeSetFinGen`, every `n ≥ 3f+1`). The three liveness-side extensions are
   not gaps either, and are deliberately *outside* the interfaces the
   models instantiate, so that no safety theorem acquires them; each is
   discharged for a concrete witness, and a liveness theorem carries
   whichever it uses as a visible hypothesis. Two are in
   [Cadence/ByzQuorum.lean](../Cadence/ByzQuorum.lean) — `ByzNodeSetEnum`
   (a quorum's members as a list) and `ByzNodeSetHonestQuorum` (a
   supermajority of correct validators, which the intersection axioms do
   not give), both discharged for the same `n ≥ 3f+1` family. The third is
   [Cadence/ViewOrder.lean](../Cadence/ViewOrder.lean)'s `ViewOrderEnum`,
   the view dimension's counterpart, discharged for `Nat`: every view has
   an immediate successor, and the views at or below one are finitely many.
   The successor field is not a proof convenience — the `Mvba.sync_view_*`
   steps are guarded on `vord.next pv v`, so a view with nothing directly above it is
   a view no validator can leave, and no assumption about scheduling or the
   network would unstick it. An end-to-end example instantiation
   of the remaining class stack (a `ThresholdIBE` model instance) is open
   work ([ChorusDesign.md](ChorusDesign.md) §9). Signatures are not a
   class at all: each signed message type is its own network relation, so
   the models take for granted that a signature of one type cannot be
   presented as one of another. A deployment obtains that by the
   supplement's domain-separation rule, a tag unique to each message type
   at the start of the signed bytes (Supplement, Section 10.5 (`sec:domain-separation`);
   [ChorusDesign.md](ChorusDesign.md) §3.1).
4. **Temporal/quantitative module obligations**: totality, termination,
   `d_tot`-totality, Quiescence, boundedness, recovery — *fields* of the
   full contracts `Orchestrator`, `SlotConsensus`,
   `SlotConsensusWithTotality`, `ACS`, `MVBA` in
   [Cadence/Interfaces.lean](../Cadence/Interfaces.lean), stated over timed
   runs with an implementation-defined admissible-execution model.
   **The orchestrator's Totality, Boundedness and Recovery are proven,
   modulo the assumed ACS module.** `OrchestratorTemporal` and
   `OrchestratorWithTotality` have instances, `Conductor.conductorTemporal`
   and `Conductor.conductorWithTotality`
   ([Cadence/Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean)),
   at `Conductor.orchestratorSafety`, joined into the full `Orchestrator` as
   `Conductor.conductorFull`, for an arbitrary ACS meeting `ACSSafety` and
   `ACSTemporal`. Every field is proven: Totality and `d_tot`-Totality from
   `Conductor.totality`, `(2W − p)`-Boundedness from
   `Conductor.boundedness`, `(2Wτ)`-Recovery from `Conductor.recovery`, at
   the paper's values. Its `Admissible` is the claims' run premises by name
   (`Sync`, [Cadence/Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean)),
   and its admissible runs exist from every initial state (the idle run).
   The ACS stays assumed: (A-acs-termination) and (A-acs-totality) are the
   `ACS` contract's fields, which no protocol in this development
   implements (the target leaves the ACS unspecified, P17).
   **Chorus's Termination, ℓ-termination and `d_tot`-totality are
   proven.** `SlotConsensusTemporal` and `SlotConsensusWithTotality` have instances,
   `Chorus.chorusTemporal` and `Chorus.chorusWithTotality`
   ([Cadence/Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean)), at
   `Chorus.slotConsensusSafety` and the system's configuration, joined into
   the full `SlotConsensus` as `Chorus.slotConsensusFull`. Every field is
   proven: Termination from `Chorus.termination`, the timed fields from
   `Chorus.timed_termination_atMvba` and `Chorus.totality`, Quiescence in
   Lemma 6 (`lemma:chorus-quiescence`)'s two parts. Its `Admissible` is the
   claims' premises by name. **`MVBATemporal` has an instance**,
   `Mvba.mvbaTemporal`
   ([Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)), at
   `Mvba.mvbaSafety`, the fragment [Cadence/System.lean](../Cadence/System.lean) plugs into
   Chorus; its `Admissible` is the timing model of
   [Cadence/Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean). The three
   instances are proven from named hypotheses, none of them an axiom, and
   each proves that admissible runs exist from every initial state. The
   hypotheses and the run premises are [Premises.md](Premises.md) §1–§6
   and §9. The composed timed claims are proven from these instances
   ([Cadence/Composed/](../Cadence/Composed/Schedule.lean)):
   Corollary 4, Lemma 5 at `2W − p`, `𝓡`-Liveness and censorship
   resistance, with every caller condition discharged and their premises
   one list, [Premises.md](Premises.md) §0. That list holds together in one
   model of the composed system
   ([Cadence/Composed/Witness.lean](../Cadence/Composed/Witness.lean),
   [Premises.md](Premises.md) §0.5). The models are untimed; the
   latency bounds proven,
   `Mvba.bounded_termination`, `Chorus.totality`,
   `Chorus.timed_termination`, `Conductor.totality` and
   `Conductor.recovery`, are over timed runs, which carry the clock
   beside the models' untimed states.
5. **Scope**: single slot for Chorus (slot independence is argued, not
   modelled), no epochs/proposer rotation, chunk indices and
   erasure-code arithmetic abstracted
   ([ChorusDesign.md](ChorusDesign.md) §3.4, §8), payload bytes not
   modelled.
6. **Composition seams**: (a) that the modules' runs implement the glue's
   oracle steps is trace-level refinement, out of scope
   ([ChorusDesign.md](ChorusDesign.md) §10.1); the glue's own calls are
   the contracts' input transitions, so no glue-side record of a call
   remains; (b) the two fault patterns
   — the shared `FaultModel` and Chorus's `ByzNodeSet.is_byz` — meet in the
   hypothesis `hbyz` of `system_positional_log_safety`; (c) an
   implementation's `Admissible` execution model is data it defines
   (non-vacuity is a class axiom, the definition is one line to read).
   All three are named in [CompositionContracts.md](CompositionContracts.md) §7.
7. **Trusted tooling**: Veil's VC generation and the concrete model
   checker are part of the trusted computing base everywhere (as is
   Lean's kernel). cvc5's `unsat` verdicts are *not* trusted — every
   sweep reconstructs its proofs kernel-checked (§6) — but its `sat`
   verdicts on the `sat trace` reachability sanity checks are (a wrong
   model there could only make a non-vacuity check vacuous, never a
   safety claim wrong). What sits inside that surface, and why an
   unrecognised action statement fails the build rather than being
   silently mistranslated, is
   [Dependencies.md](Dependencies.md) § "Trusted computing base".

## 5. The receipt layer: why it has its own model

Chorus's monotone network abstracts away how a validator *observes*
certificates ([ChorusDesign.md](ChorusDesign.md) §8, "EquivCert is the pair
of proposer signatures"), but the MVBA's termination needs every correct
validator to propose a valid meta-block assembled from what it holds
locally. The fallback receipt rules (Algorithm 5 (`alg:fallback`)) are that per-validator
step: a receipt restriction plus an atomic build at propose time.
[ChorusDesign.md](ChorusDesign.md) §7.2 explains why the rules are shaped
this way and which half of them is load-bearing. The paper's v1 had a
liveness bug at exactly this step, fixed in v2; the model checker's
counterexample to the v1 rules is preserved at the git tag
`v1-receipt-refutation`.

Two artefacts of this development follow:

* the **fallback commit round** and the tightened wire format are modelled
  in [Cadence/Chorus.lean](../Cadence/Chorus.lean) rather than documented away; and
* the receipt/propose layer has its own per-validator model,
  [Cadence/FallbackReceipt.lean](../Cadence/FallbackReceipt.lean), which
  verifies the rules — "valid by construction" by SMT, and the counting
  argument for every `n = 3f+1`, kernel-checked.

## 6. Trust base

The solver is not in it: every discharge is reconstructed as a Lean proof
term and re-checked by the kernel. The table below gives the axiom base per
artefact, each pinned by `#guard_msgs` where marked. Every pin is *also*
re-derived in the audit root [Cadence.lean](../Cadence.lean), so the whole
table can be read off one file:

| Artefact | Axioms | Pinned |
|---|---|---|
| `Cadence.positional_log_safety`, `Conductor.orchestratorSafety`, `Conductor.orchestrator_of_temporal` ([Cadence/Composition.lean](../Cadence/Composition.lean)) | `propext, Classical.choice, Quot.sound` | ✓ |
| `Cadence.system_positional_log_safety` ([Cadence/System.lean](../Cadence/System.lean)) | same | ✓ |
| `Chorus.invariants_of_reachable` + per-property projections ([Cadence/Chorus/Certify.lean](../Cadence/Chorus/Certify.lean)) | same | ✓ + `#veil_status`: every cell real |
| `FallbackReceipt.invariants_of_reachable` ([Cadence/FallbackReceipt/Certify.lean](../Cadence/FallbackReceipt/Certify.lean)) | same | ✓ + `#veil_status`: every cell real |
| `FallbackReceipt.build_totality_of_reachable` ([Cadence/FallbackReceipt/Totality.lean](../Cadence/FallbackReceipt/Totality.lean)) | same | ✓ |
| `Chorus.slotConsensusSafety`, `Chorus.slotConsensus_of_temporal` ([Cadence/Chorus/Compose.lean](../Cadence/Chorus/Compose.lean)) | same | ✓ |
| `Chorus.evidence_pigeonhole_of_reachable` ([Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean)) | same | ✓ |
| `Mvba.invariants_of_reachable` + per-property projections ([Cadence/Mvba/Certify.lean](../Cadence/Mvba/Certify.lean)) | same | ✓ + `#veil_status`: every cell real |
| `Conductor.totality`, `Conductor.boundedness`, `Conductor.recovery` ([Cadence/Conductor/Induction.lean](../Cadence/Conductor/Induction.lean), [Boundedness.lean](../Cadence/Conductor/Boundedness.lean), [Recovery.lean](../Cadence/Conductor/Recovery.lean)); `Conductor.conductorTemporal`, `Conductor.conductorWithTotality`, `Conductor.conductorFull` ([Cadence/Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean)) | same | ✓ |
| `Mvba.mvbaSafety`, `Mvba.mvba_of_temporal` ([Cadence/Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)) | same | ✓ |
| `Mvba.bounded_termination`, `Mvba.aViewSync_of_sync` ([Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean)) | same | ✓ |
| `Mvba.mvbaTemporal`, `Mvba.timed_termination`, `Mvba.admissible_exists`, `Mvba.mvbaFull` ([Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)) | same | ✓ |
| `Mvba.timedTermination_premises_satisfiable`, `Mvba.termination_premises_satisfiable` ([Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean)) | same | ✓ |
| `Chorus.termination_premises_satisfiable`, `Chorus.timedTermination_premises_satisfiable`, `Chorus.totality_premises_satisfiable` ([Cadence/Chorus/Witness.lean](../Cadence/Chorus/Witness.lean)) | same | ✓ |
| `Chorus.totality`, `Chorus.totality_paper` ([Cadence/Chorus/Totality.lean](../Cadence/Chorus/Totality.lean)) | same | ✓ |
| `Chorus.timed_termination`, `Chorus.timed_termination_atMvba`, `Chorus.timed_termination_tight`, `Chorus.timed_termination_tight_atMvba` ([Cadence/Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean)) | same | ✓ |
| the `MvbaNoLock` refutation ([Cadence/Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean)) | expected model-checker violation (trace) | ✓ |

cvc5's `unsat` verdicts are trusted nowhere: every discharge runs with proof
reconstruction (`veil.smt.trust false`), so every proof is re-checked by
Lean's kernel. No composition consumes a stub: every pinned artefact rests on
persisted, kernel-checked proof terms.

The mechanism that makes this fit on a 32 GB machine is the
**verified-module file family**, drawn in
[model-to-theorem.svg](diagrams/model-to-theorem.svg) and explained in
[the guide's chapter 7](https://larskuhtz.github.io/cadence/guide/checking/). A model file
([Cadence/Chorus.lean](../Cadence/Chorus.lean), [Cadence/FallbackReceipt.lean](../Cadence/FallbackReceipt.lean), [Cadence/Mvba.lean](../Cadence/Mvba.lean))
elaborates the transition system and persists
its VC *statements* in an olean-carried registry — it runs no solver
and persists no proofs. One proof file per action
(`<Model>/Proofs/<Action>.lean`) re-creates that action's VCs from the
registry — statements identical to what the model declares, by
construction — discharges them (cvc5 + reconstruction), persists every
proof as a kernel-checked theorem in its own small olean, and exports
one "this action preserves the invariants" lemma; keeping each action's
proofs in their own process/olean is what bounds memory (a few GB per file
cold). The quorum-intersection cells that SMT cannot find are manual
`#prove_vc … by <tactic>` cells in their actions' proof files, consumed
after a statement check — the statement itself always comes from the
registry, and the tactics project invariant conjuncts by name
(Veil's `veil_inv_have`), so nothing in a proof file restates or
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
capabilities it depends on and why — [Dependencies.md](Dependencies.md).

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
document: [History.md](History.md) (build history, per-module status) and
the git log; a past state worth keeping whole is tagged (the v1 receipt
counterexample, §5).
