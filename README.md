# Cadence — machine-checked verification (Veil / Lean 4)

A formal verification of the [**Cadence**](https://www.category.xyz/cadence)
BFT consensus protocol (see [§ The protocol paper](#the-protocol-paper)): the
per-slot consensus **Chorus**, the window-based orchestrator **Conductor**, the
pipelining **Cadence** layer that composes them, and the fallback
receipt/propose layer.

Written in [Veil](https://github.com/larskuhtz/veil) on Lean 4. Veil is an
embedded DSL: a `.lean` file *is* the model, and elaborating the file *runs*
its verification. There is no separate proof script — `lake build` elaborates
the files, the verification commands fire during elaboration, and **if any of
them fails, the build fails**.

> **Status.** The SMT solver is not in the trust base: every discharge is
> reconstructed as a Lean proof term and re-checked by the kernel. Every end
> theorem is pinned to exactly `propext` / `Classical.choice` / `Quot.sound`
> — Lean's three standard axioms — with no `sorry` and no trusted solver
> verdict. Every timed claim of the composed system — Corollary 4, bounded
> concurrency, `𝓡`-liveness, censorship resistance — is proven from one
> list of premises ([docs/Premises.md](docs/Premises.md) §0), and that list
> is shown to hold together in one model of the composed system
> ([Cadence/Composed/Witness.lean](Cadence/Composed/Witness.lean)): the
> claims are not vacuous.

**Start here:** [Cadence.lean](Cadence.lean) — the audit root. It imports
every finished result and re-derives each axiom's footprint as a build-checked
pin, so the whole trust base can be read off one page.

---

## Map of the development

The paper decomposes Cadence into modules and proves the top-level properties
from their specifications. The formalisation mirrors that decomposition: each
paper module is a type class in
[Cadence/Interfaces.lean](Cadence/Interfaces.lean), and each layer is a
Veil model that **implements** one contract and **consumes** the contracts
below it.

```mermaid
flowchart BT
    MVBA["Mvba ⊨ MVBASafety<br/>Cadence/Mvba.lean"]
    ACS["ACS — assumed<br/>a standard primitive,<br/>no implementation here"]
    CHOR["Chorus ⊨ SlotConsensusSafety<br/>Cadence/Chorus.lean<br/>consumes MVBASafety"]
    COND["Conductor ⊨ OrchestratorSafety<br/>Cadence/Conductor.lean<br/>consumes ACSSafety"]
    GLUE["Cadence — extreme-pipelining glue<br/>Cadence/Cadence.lean<br/>consumes OrchestratorSafety,<br/>SlotConsensusSafety"]
    POS["MCP Safety for the glue over any<br/>modules meeting the contracts<br/>Cadence/Composition.lean"]
    SYS["MCP Safety for the composed system<br/>conditional only on ACSSafety<br/>Cadence/System.lean"]

    MVBA --> CHOR
    ACS -.-> COND
    CHOR --> GLUE
    COND --> GLUE
    GLUE --> POS
    POS --> SYS

    classDef assumed stroke-dasharray:4 3
    class ACS assumed
```

| Layer | Paper | Model | Proves | Consumes |
|---|---|---|---|---|
| Pipelining glue | Algorithm 1 (`algorithm:cadence`) | [Cadence/Cadence.lean](Cadence/Cadence.lean) | MCP Safety (positional) | Orchestrator, SlotConsensus |
| Slot scheduling | Module 2 (`mod:orchestrator_2`) | [Cadence/Conductor.lean](Cadence/Conductor.lean) | `Conductor.orchestratorSafety` | ACS |
| Per-slot consensus | Module 1 (`mod:slotconsensus`) | [Cadence/Chorus.lean](Cadence/Chorus.lean) | `Chorus.slotConsensusSafety` | MVBA |
| Byzantine agreement | Module 3 (`mod:mvba`) | [Cadence/Mvba.lean](Cadence/Mvba.lean) | `Mvba.mvbaSafety` | — |
| Fallback receipts | Algorithm 5 (`alg:fallback`) | [Cadence/FallbackReceipt.lean](Cadence/FallbackReceipt.lean) | meta-block validity by construction | — |

The receipt layer implements no contract: it refines one step *inside*
Chorus's fallback path — assembling a valid meta-block from received receipts
— at a finer per-validator grain than the Chorus model uses.

Each arrow reads "fills the contract constraint above it", and each is a Lean
instance rather than a correspondence argued in prose — except the dashed
one, which marks the single contract nothing here implements. Every
implemented contract is proven whole, from named hypotheses: a full `MVBA`
(`Mvba.mvbaFull`), a full `SlotConsensus` with the timing strengthenings
(`Chorus.slotConsensusFull`, `Chorus.chorusWithTotality`) at the system's
configuration, and a full `Orchestrator` with `d_tot`-Totality
(`Conductor.conductorFull`, `Conductor.conductorWithTotality`) for an
arbitrary ACS meeting its contract; see
[docs/CompositionContracts.md](docs/CompositionContracts.md) §5. What stays
assumed is the ACS, and the glue's composed timed claims are not yet
stated.

---

## Audit Guide

### A. Machine-checked

You do not need to trust this project's authors, for any of the
following claims. They are re-derived by the machine on every build, and a violation
is a build failure.

| What is guaranteed | How it is enforced |
|---|---|
| Every stated theorem has a **complete proof**, checked by Lean's kernel | the build; plus the axiom pins in [Cadence.lean](Cadence.lean) — a `sorry` anywhere shows up as the axiom `sorryAx` and fails the pin |
| The trust base has not drifted (no extra axiom crept in) | `#guard_msgs in #print axioms <thm>` for every end theorem, in [Cadence.lean](Cadence.lean) and at each result's own site |
| **cvc5's verdicts are not believed.** Every solver discharge is reconstructed as a Lean proof term and re-checked by the kernel | all models elaborate with `veil.smt.trust false`; if a proof cannot be reconstructed, the cell fails |
| **Nothing is stubbed.** Every Chorus verification condition (one per action × property, plus a does-not-throw check per action), and every one of the receipt layer's and of the MVBA instantiation's, has a real, statement-matching, kernel-checked theorem in scope | the pinned `#veil_status` lines in [Cadence/Chorus/Certify.lean](Cadence/Chorus/Certify.lean), [Cadence/FallbackReceipt/Certify.lean](Cadence/FallbackReceipt/Certify.lean) and [Cadence/Mvba/Certify.lean](Cadence/Mvba/Certify.lean), each asserting *all* cells real with the axiom union over all of them |
| The verification conditions are the ones the model states — they are not re-typed by hand anywhere | the proof files read their statements out of the model's own persisted registry; identity is by construction |
| **The composition is not a transcription.** The glue, the Conductor and Chorus consume the sub-protocol contracts as *class constraints* over abstract states (`instantiate orch : OrchestratorSafety …`, `instantiate sc : SlotConsensusSafety …`, `instantiate acs : ACSSafety …`, `instantiate mvba : MVBASafety …`), so no contract property is restated as a guard or invariant; the implementations' instances (`Conductor.orchestratorSafety`, `Chorus.slotConsensusSafety`, `Mvba.mvbaSafety`) are checked against the same classes. Two stated *bridges* remain — the ACS median range and the MVBA decision's certificate check — each the interpretation of a class parameter in the consumer's vocabulary rather than a restatement (docs/CompositionContracts.md §7) | the `instantiate` lines in [Cadence/Cadence.lean](Cadence/Cadence.lean), [Cadence/Conductor.lean](Cadence/Conductor.lean) and [Cadence/Chorus.lean](Cadence/Chorus.lean); the instance definitions' types; [Cadence/System.lean](Cadence/System.lean), which instantiates the glue's end theorem at the instances, with `Mvba.mvbaSafety` filling Chorus's constraint, and leaves one contract hypothesis, the Conductor's `ACSSafety` |
| **What each implementation owes of its contract is a type, not prose.** The temporal obligations are the fields of a class stated over the very transition system the implementation proved, so they are written down once and nowhere else. The proven temporal levels, the MVBA's, Chorus's and the Conductor's, are instances of those classes, with their hypotheses in their types | `OrchestratorTemporal` is instantiated, `Conductor.conductorTemporal`, and joined by `orchestrator_of_temporal` into `Conductor.conductorFull` ([Cadence/Conductor/Temporal.lean](Cadence/Conductor/Temporal.lean)); `MVBATemporal` is instantiated, `Mvba.mvbaTemporal`, and joined by `mvba_of_temporal` into `Mvba.mvbaFull` ([Cadence/Mvba/Temporal.lean](Cadence/Mvba/Temporal.lean)); `SlotConsensusTemporal` is instantiated, `Chorus.chorusTemporal`, and joined by `slotConsensus_of_temporal` into `Chorus.slotConsensusFull` ([Cadence/Chorus/Temporal.lean](Cadence/Chorus/Temporal.lean)) — each join paired with a `rfl` lemma that it hands back exactly the proven fragment |
| The MVBA instantiation's invariants are **load-bearing**, not merely true: remove the lock check and agreement fails | [Cadence/Mvba/NoLock.lean](Cadence/Mvba/NoLock.lean) pins the model checker's counterexample to the mutant; the file builds only if the violation is still found, verbatim |

In short: `lake build` succeeding is the claim. You can re-derive any pin
yourself — drop a `#guard_msgs in` line, or run `#print axioms <name>` in a
scratch file (see [Working on the models](#working-on-the-models) below).

The script `scripts/container.sh check` re-runs **Lean's kernel over every
declaration in the development** — every reconstructed Chorus proof
included — in **4 minutes**, with no SMT solver, no tactic execution and no
elaboration. Forcing the elaborator to redo the whole project from source on
top of that is a further 9 minutes; re-solving every verification condition
with cvc5 from scratch, about 90 minutes. What each of those does and does not
establish — and how both differ from simply *importing* prebuilt `.olean`
files, which are trusted rather than re-checked — is the audit ladder in
[docs/Container.md](docs/Container.md) §3–§4.

### B. To be checked by an auditor

Machine checking establishes that the proofs are complete. It cannot
establish that the *statements* are the right ones. Three questions remain
for a human reader:

1. **Does the model faithfully describe the protocol?** The models are the
   `.lean` files listed under [What is where](#what-is-where); each carries a
   long header explaining its modelling choices, and
   [docs/ChorusDesign.md](docs/ChorusDesign.md) is the full design-rationale
   document for the big one. The abstractions deliberately taken (chunk
   indices, erasure coding, payload bytes, single slot for Chorus) are listed
   in [docs/Architecture.md](docs/Architecture.md) §4 item 5 and
   [docs/ChorusDesign.md](docs/ChorusDesign.md) §3.4 and §8.
2. **Are the top-level properties the right properties?** The end
   theorems, in the paper's own vocabulary, are tabulated in
   [Cadence.lean](Cadence.lean) and in [What is proven](#what-is-proven)
   below. The paper's *module contracts* — the interfaces the layers are
   proven against, stated in full as type classes (every property of each
   paper module, safety and liveness alike) and consumed by the models as
   class constraints — are [Cadence/Interfaces.lean](Cadence/Interfaces.lean);
   [docs/CompositionContracts.md](docs/CompositionContracts.md) explains the
   encoding and names the seams that remain.
3. **Are the meta-theoretic assumptions sound?** **Start with
   [docs/Premises.md](docs/Premises.md)**: every liveness claim is
   conditional, and that page lists each of its premises once — its role,
   why it is plausible, the witness showing all of a claim's premises hold
   together, and the proof step that uses it. Everything else deliberately
   kept outside Lean — the network abstraction's soundness contract, the
   cryptographic primitives, the timing/quantitative module obligations —
   is a **named, complete inventory**:
   [docs/Architecture.md](docs/Architecture.md) §4. That inventory is the
   audit checklist. It is short on purpose.

Item 3 lists assumptions *by name*, and the fairness and oracle axioms appear
verbatim in the Lean sources where they are consumed — `grep -rn '(A-'
Cadence/` enumerates them — so the inventory's completeness is checkable. The
one assumption without that property is the network contract, which is why it
is item 1 of the inventory and a standing rule in [CLAUDE.md](CLAUDE.md): a
violation of it would not fail the build.

*The file [docs/AuditReport.md](docs/AuditReport.md) contains an audit report
that was created by [Aristotle (Harmonic)](https://aristotle.harmonic.fun) for
the revision bfeee8c of this project against the version 2 of the Cadence
paper published on arxiv.*

---

## What is proven

Three methods appear in the table; [docs/Architecture.md](docs/Architecture.md)
§2 defines them and gives the per-module counts.

* **sweep** — one inductive-invariant verification condition per action ×
  property, discharged by cvc5 with **proof reconstruction**, so every
  discharge is a Lean proof term the kernel re-checks. For the three large
  models the proofs live in per-action files and the per-VC evidence is
  pinned by `#veil_status`.
* **composition** — plain Lean over the persisted VC theorems: an induction
  over reachable states, then the module contract's instance.
* **model check** — exhaustive exploration of a concrete instance
  (`n = 4`, `f = 1`), used only where it is complete evidence.

Every row below is axiom-pinned at `[propext, Classical.choice, Quot.sound]`
in [Cadence.lean](Cadence.lean).

| Claim | Where | Method |
|---|---|---|
| **Agreement** — correct validators never finalize conflicting proposal vectors | [Cadence/Chorus.lean](Cadence/Chorus.lean) (`agreement_pos`, `agreement_pos_neg`) → `Chorus.slotConsensusSafety` | sweep + composition |
| **Proposal inclusion** (censorship resistance, under the paper's synchrony premise) | [Cadence/Chorus.lean](Cadence/Chorus.lean) → instance field | sweep + composition |
| **Hiding until the deadline** (protocol half) | [Cadence/Chorus.lean](Cadence/Chorus.lean) (`hiding_until_deadline`) | sweep; the cryptographic half is axiomatised ([Cadence/Primitives.lean](Cadence/Primitives.lean)) |
| **Speculative-finality revertibility** ("reverted only if the proposer is the culprit") | [Cadence/Chorus.lean](Cadence/Chorus.lean) (`speculative_agreement_*`) | sweep, conditional on `no_equivocation` + `no_invalid_encoding` — the paper's full culprit set: equivocation, or committing to an invalidly encoded root |
| **Fair-progress liveness content** (no livelock of fair actions — strictly stronger than deadlock-freedom) | [Cadence/Chorus.lean](Cadence/Chorus.lean), liveness section | sweep + the named temporal assumptions ([docs/Liveness.md](docs/Liveness.md)) |
| **Progress dichotomy** — the liveness case split as one theorem: in any reachable state where every honest validator has cast its path vote, either commitQCs exist for every proposer from honest votes alone, or the MVBA stands invoked with decide-enabling evidence for every proposer, for **every** `n = 3f+1` | [Cadence/Chorus/Progress.lean](Cadence/Chorus/Progress.lean) (`progress_dichotomy_of_saturation`); its counting inputs — the evidence pigeonhole and certificate formation — are separately stated and pinned in [Cadence/Chorus/Pigeonhole.lean](Cadence/Chorus/Pigeonhole.lean) and [Cadence/Chorus/Counting.lean](Cadence/Chorus/Counting.lean) | plain Lean over reachable states |
| **MVBA termination, bound-erased** — every correct validator eventually decides, from six named premises (weak fairness of the honest actions for correct senders, the timeout discipline, availability, and the caller's three: everyone proposes, nobody is abandoned before deciding, decided certificates are handed on) and three hypothesis classes. The timing premise, (A-viewsync), states the view timer as ordering constraints (timers do fire; the good view's timer waits for a correct validator's decision), so the theorem reads *given enough time, the protocol decides*. It is a theorem of the timing model below (`Mvba.aViewSync_of_sync`); [docs/Liveness.md](docs/Liveness.md) §2.1 explains it in short. This is the untimed shadow of `MVBATemporal.termination`, not that field | [Cadence/Mvba/Liveness.lean](Cadence/Mvba/Liveness.lean) (`Mvba.termination`) | plain Lean over runs of the generated transition system; premises are hypotheses, never axioms ([docs/Liveness.md](docs/Liveness.md) §2.1) |
| **Chorus termination, bound-erased** — every correct validator finalizes the slot, for **every** `n = 3f+1`, at the configuration the composed system runs, from five named premises: correct validators' actions are scheduled fairly, for the messages of correct senders (`FJustice`); the MVBA's steps are scheduled as the MVBA's own termination theorem requires (`MvbaAdmissible`); the MVBA's validity check agrees with Chorus's certificates (`ValidBridge`, the cryptographic seam between the two models, not a fairness assumption); and the caller's two conditions, that every correct validator eventually participates (`AllParticipate`) and none abandons before finalizing (`NoAbandonBeforeFinalizing`). The MVBA's termination is not assumed: the proof applies `Mvba.termination` to the run's MVBA steps. The untimed form of Lemma 11 (`lemma:chorus-termination`); the bound is the next row | [Cadence/Chorus/Termination.lean](Cadence/Chorus/Termination.lean) (`Chorus.termination`), premises in [Cadence/Chorus/Liveness.lean](Cadence/Chorus/Liveness.lean) | plain Lean over runs of the generated transition system; premises are hypotheses, never axioms ([docs/Liveness.md](docs/Liveness.md) §2) |
| **Network-level build totality** — any supermajority of accepted receipts (Byzantine members included) yields a buildable fallback meta-block entry per proposer: the state-level half of "every correct validator can propose", for **every** `n = 3f+1` | [Cadence/Chorus/Counting.lean](Cadence/Chorus/Counting.lean) (`build_totality_of_reachable`) | plain Lean over reachable states |
| **MCP Safety, positional form** — for the glue over *any* orchestrator and slot consensus satisfying the contracts, and **for the composed system** (the glue running the Conductor's and Chorus's own transition systems, Chorus running the `Mvba` model's as its MVBA; conditional only on the ACS contract `ACSSafety`) | [Cadence/Composition.lean](Cadence/Composition.lean) (`positional_log_safety`), [Cadence/System.lean](Cadence/System.lean) (`system_positional_log_safety`) | sweep (against the contracts as class constraints) + composition |
| **`Conductor ⊨ OrchestratorSafety`**, **`Chorus ⊨ SlotConsensusSafety`** — the state-level fragments of the paper's module contracts, every field proven (including the two-state fields: monotonicity of the observables, frames, the paper's Monotonicity) | [Cadence/Composition.lean](Cadence/Composition.lean) (`Conductor.orchestratorSafety`), [Cadence/Chorus/Compose.lean](Cadence/Chorus/Compose.lean) (`Chorus.slotConsensusSafety`) | composition, over persisted VC theorems and Veil's transition bodies |
| **Chorus's full contract, at the system's configuration** — `SlotConsensusTemporal` and `SlotConsensusWithTotality` instantiated, every field proven: Termination; `ℓ`-termination with `ℓ = 5Δ + ℓ_MVBA` at `δ = 0` (Lemma 11 (`lemma:chorus-termination`)); `d_tot`-totality with `d_tot = Δ` at `δ = 0` (Proposition 4 (`prop:chorus-totality`)); Quiescence (Lemma 6 (`lemma:chorus-quiescence`)); the participation interface. `Admissible` is the premises above by name, and a run in which every proposer stays silent shows it is not vacuous. Hypotheses: the MVBA instance's, and a non-empty proposer set. Joined with the fragment into the full `SlotConsensus`, which hands the fragment back by `rfl` | [Cadence/Chorus/Temporal.lean](Cadence/Chorus/Temporal.lean) (`Chorus.chorusTemporal`, `Chorus.chorusWithTotality`, `Chorus.slotConsensusFull`) | plain Lean over runs; premises are hypotheses, never axioms |
| **The Conductor's full contract, for an arbitrary ACS meeting its contract** — `OrchestratorTemporal` and `OrchestratorWithTotality` instantiated, every field proven: Totality and `d_tot`-Totality with `d_tot = Δ` at `δ = 0` (Lemma 15 (`lemma:conductor-totality`)); `(2W − p)`-Boundedness (Lemma 14 (`lem:boundedness`)); `(2Wτ)`-Recovery (Lemma 16 (`lemma:conductor-recovery`)), all in rely form on the caller's totality and termination. `Admissible` is the claims' run premises by name, and a run in which the caller completes nothing shows it is not vacuous. Hypotheses: the configuration premises (τ-spaced, unbounded starting times; windows of `W` slots, each with a successor; the ACS's constants and fault bound); two of them hold at `window := ℕ` over an Archimedean time (`Conductor.conductorFullNat`). The ACS is an assumed module. Joined with the fragment into the full `Orchestrator`, which hands the fragment back by `rfl`. Integrity's timing half is first-order and sits in the fragment | [Cadence/Conductor/Temporal.lean](Cadence/Conductor/Temporal.lean) (`Conductor.conductorTemporal`, `Conductor.conductorWithTotality`, `Conductor.conductorFull`), from `Conductor.totality`, `Conductor.boundedness`, `Conductor.recovery` | plain Lean over timed runs; premises are hypotheses, never axioms |
| **The composed system's timed claims, the loop closed** — the glue running the Conductor and Chorus on one clock, with one `Δ` and `δ = 0`. Every condition each module's claims take from its caller is a theorem about the composed run: Chorus's (no abandonment before finalizing, no start before `D − Δ`, Δ-synchronized participation) and the Conductor's (its caller's totality and termination, from Chorus). On that footing: **Corollary 4 (`cor:chorus-correctness-within-cadence`)**, Chorus's `ℓ`-termination, `d_tot`-totality and termination for every slot with no caller premise left; **Lemma 5 (`lemma:cadence-bounded-concurrency`)**, at most `2W − p` instances actively participated in; and **`𝓡`-Liveness** (Definition 2 (`def:liveness`), Lemma 2 (`lemma:cadence-liveness`)) at the paper's `2Wτ` and at the sharper `(W + p − 1)τ`: every slot starting `𝓡` after GST ends up in every correct validator's log; and **`𝓡`-censorship resistance** (Definition 3 (`def:censorship-resistance`)) at the same values: a correct proposer's proposal is in that slot's vector in every correct validator's log, under the paper's "by the deadline" read inclusively (a stated premise, F31). The premises are one list ([docs/Premises.md](docs/Premises.md) §0): the glue's handler rows, each module's timing model on its part of the run, the configuration, and the assumed ACS. **They hold together**: one model of the composed system (four validators, one Byzantine and silent, the ideal ACS, a periodic run in which every slot takes the fast path) meets all of them at once, and its orchestrator's part every premise of the Conductor's own claims ([Cadence/Composed/Witness.lean](Cadence/Composed/Witness.lean), `Composed.Witness.*_premises_satisfiable`) | [Cadence/Composed/](Cadence/Composed/Schedule.lean) (`Composed.corollary4`, `Composed.boundedConcurrency`, `Composed.liveness`, `Composed.censorship`, and the `_sharp` forms) | plain Lean over timed runs of the composed system; premises are hypotheses, never axioms |
| **Fallback meta-block "valid by construction"**, including the counting argument, for **every** `n = 3f+1` | [Cadence/FallbackReceipt.lean](Cadence/FallbackReceipt.lean) + [Cadence/FallbackReceipt/Totality.lean](Cadence/FallbackReceipt/Totality.lean) | sweep + composition |
| **MVBA agreement, integrity and external validity** — the three safety properties of Module 3 (`mod:mvba`), for the leader-based instantiation of the paper repository's *internal supplement* (views, timeouts, timeout certificates, the lock; the supplement is part of the paper target) | [Cadence/Mvba.lean](Cadence/Mvba.lean) (`agreement`, `integrity`, `external_validity`) → `Mvba.mvbaSafety` | sweep + composition |
| **`Mvba ⊨ MVBASafety`** — the state-level fragment of the paper's MVBA contract, every field proven, including the two inputs, their observables and **Quiescence**; given an `MVBATemporal` instance (the clock, the admissible-run model, `ℓ_MVBA`-Termination — four fields, nothing safety-shaped) the instantiation is a full `MVBA`. Chorus consumes the class as a constraint and [Cadence/System.lean](Cadence/System.lean) fills it with this instance | [Cadence/Mvba/Compose.lean](Cadence/Mvba/Compose.lean) (`Mvba.mvbaSafety`, `mvba_of_temporal`) | composition, over persisted VC theorems and Veil's transition bodies |
| **`Mvba ⊨ MVBATemporal`, and so a full `MVBA`**, the one the composed system runs: **`ℓ_MVBA`-Termination with an explicit `ℓ`**, the supplement's `O(fΔ)` at `k = f + 1`. Every correct validator decides by `max(t, GST) + ℓ` once all have proposed valid values by `t` and none abandons early, in every admissible run. Admissible means bounded fairness after GST under the supplement's network (a message sent at or after GST by a correct validator and retained is consumed within `Δ`, a retransmitted one within `Δ + ρ`, a local step within `δ`), a punctual view timer, and availability within `Δ_sync`, and such runs exist. The hypotheses are finitely many validators, the honest-quorum and view-order classes, a correct leader in every `k` consecutive views, a capped timeout that eventually exceeds the chain's latency, and a cancellative, Archimedean time monoid. | [Cadence/Mvba/Temporal.lean](Cadence/Mvba/Temporal.lean) (`Mvba.mvbaTemporal`, `Mvba.mvbaFull`), from [Cadence/Mvba/BoundedTermination.lean](Cadence/Mvba/BoundedTermination.lean) (`Mvba.bounded_termination`) | plain Lean over timed runs of the generated transition system; premises are hypotheses, never axioms ([docs/Bounds.md](docs/Bounds.md) §6.2) |
| **The MVBA's lock check is load-bearing** — with the `Pre-Prepare` handler's lock check removed, two correct validators decide different vectors: the mutation test showing the instantiation's invariants are needed, not merely true | [Cadence/Mvba/NoLock.lean](Cadence/Mvba/NoLock.lean) | exhaustive model check of a restriction of the mutant (every run of which is a run of the mutant); the counterexample trace is pinned in the build |

What is *not* proven in Lean is, first, the premises of the liveness
theorems — one page, [docs/Premises.md](docs/Premises.md); the theorems
themselves, and the liveness argument's entire state-level content,
**are** machine-checked ([docs/Liveness.md](docs/Liveness.md)) — and then
the cryptographic primitives, the monotone-network soundness contract and
the rest of the named assumption inventory in
[docs/Architecture.md](docs/Architecture.md) §4. The temporal part of that
inventory is also a *type*: the `…Temporal` classes list, field by field,
what each implementation owes of its paper contract, and each is
instantiated from named hypotheses. The ACS's is not: the ACS is an
assumed module, consumed through its contract.

---

## Checking the proofs

The quickest check needs no build at all. Prebuilt images — this project
already built and verified inside the image — are published for `linux/arm64`
and `linux/amd64`. [scripts/container.sh](scripts/container.sh) pulls what
it needs on first use (~4 GiB, once):

```bash
RUNTIME=podman scripts/container.sh check    # kernel-re-check every proof — 4 min, no solver
RUNTIME=podman scripts/container.sh verify   # re-verify against the checkout's sources
```

`RUNTIME` selects `podman`, `docker`, or Apple's `container`. The two commands
are tiers 1 and 2 of an audit ladder that ends at "re-solve every verification
condition from scratch". What each tier does and does not establish — in
particular, what a prebuilt `.olean` proves — is
[docs/Container.md](docs/Container.md) §3–§4. Every tier, including the
last, also runs natively on Linux and macOS ([below](#building-natively));
the container just fixes the environment.

## Working on the models

The `dev` image is the same environment with the sources mounted. Open the
folder in VS Code with the **Dev Containers** extension —
[.devcontainer/](.devcontainer) uses the published image — or work from a
terminal:

```bash
RUNTIME=podman scripts/container.sh shell    # interactive shell in the workspace
RUNTIME=podman scripts/container.sh verify   # staged re-verification, after an edit
```

Opening a file costs what it elaborates: [Cadence/Chorus.lean](Cadence/Chorus.lean) runs no
invariant sweep but elaborates the model plus its background does-not-throw
checks (a couple of minutes); a [Cadence/Chorus/Proofs/](Cadence/Chorus/Proofs) file re-proves one
action's cells (seconds with a warm cache, minutes cold); the consumer files
load prebuilt `.olean`s in seconds. To suppress solving entirely while
editing, set `VEIL_NO_VERIFY=1` in the *editor's* environment — the
devcontainer already does; never set it in a shell profile, since `lake build`
must still verify. Every skipped command reports a visible
`⏭ skipped (veil.noVerify)` warning, so "no errors" in this mode never means
"verified".

The development workflow and the model-specific rules are in
[CLAUDE.md](CLAUDE.md). Building the images yourself — needed only when the
dependency tree changes — is [docs/Images.md](docs/Images.md).

### Building natively

Requires [elan](https://github.com/leanprover/elan); the pinned toolchain and
the dependency tree are fetched automatically on the first build. Building also
needs a system `clang` with a version-matched `libc++` development package
(providing the compiler's resource-dir headers): that is a transitive native
dependency of the cvc5 binding used for proof reconstruction, whose build
compiles an FFI shim with a hardcoded `clang -std=c++17 -stdlib=libc++`
invocation. elan's bundled toolchain `clang` does not ship those headers and
cannot substitute.

```bash
LEAN_NUM_THREADS=4 lake build   # everything: models, every proof file
                                # (one per action), composition
                                # certificates, end theorems, the audit
                                # root's axiom pins, and the monitor
```

Bound the parallelism on the **first** build, as above. `lean-smt` and
`lean-auto` compile their own native plugins, and if that build is OOM-killed
mid-link the half-written libraries are left in place and considered
up-to-date, so every later build fails in milliseconds while loading them.
Recovery is `rm -rf .lake/packages/{auto,smt}/.lake/build`. Lake has no `-j`
flag; `LEAN_NUM_THREADS` is the only control.

**Memory.** `lake build` runs as many `lean` processes at once as
`LEAN_NUM_THREADS` allows, which defaults to the core count. A *cold* proof
file peaks at 2–4 GB of resident memory (one reaches 9 GB), so on most
machines the core count is too many. The script sets the cap from the
memory available:

```bash
scripts/revalidate.sh          # one lake build, cap derived from memory
JOBS=4 scripts/revalidate.sh   # ... with an explicit cap
BATCH=1 scripts/revalidate.sh  # staged build, one proof file at a time
scripts/revalidate.sh /tmp     # ... and write the RSS sample log there
```

`JOBS` is the number of concurrent `lean` processes, at roughly 4 GB each.
The default is 8 on a 14-core / 36 GB machine, which ran the whole suite in
about 7 min warm and 11 min cold. Past that, more slots do not help, because
the build is bound by its longest dependency chain. On few cores keep `JOBS`
low (CI's 4-core runner uses `JOBS=2`), since concurrent solvers slow each
other enough to push a near-budget cell over its timeout. The staged `BATCH`
mode is what the image build uses.
The script's header has the measurements.

Individual pieces, for iteration:

```bash
lake build Cadence.Chorus                    # the per-slot consensus MODEL (no sweep) — ~2 min
lake build Cadence.Chorus.Proofs.Vote        # one Chorus action's ~100 proof cells
lake build Cadence.Chorus.Certify            # composition certificate + the #veil_status audit pin
lake build Cadence.Mvba Cadence.Mvba.Certify # the MVBA model and its certificate
lake build Cadence.Cadence Cadence.Conductor # the two small models, sweeps included
lake build Cadence.FallbackReceipt           # receipt model + its n=4 exhaustive model check
lake build Cadence                           # the audit root: every axiom pin, re-derived
```

**Reading the output.** Verification results are marked `✅` proven, `❌`
counterexample, `💥` solver crash, `⏱` timeout, and `♻` proof-cache replay
(kernel-checked). Count **all four** of the first group: grepping only for
`❌` hides timeouts and crashes. A healthy build has only `✅` and `♻`.

**Two timing regimes.** Most verification conditions are frame obligations
(the action writes nothing the property reads), which Veil closes without
calling the solver at all; the rest are solved by cvc5, and those
reconstructed proofs are cached on disk under `.lake/build/veilcache/` and
replayed, kernel-checked, on later builds. A first build therefore solves
every solver-touched condition cold, and a re-validation replays them — both
in minutes rather than hours on a workstation, run through
[scripts/revalidate.sh](scripts/revalidate.sh);
[docs/Container.md](docs/Container.md) §4 has measured times per audit tier.
The cache is a build artefact, not shipped, and safe to delete at any time:
it only ever skips proof *search*, never checking.

Do not run other heavy jobs concurrently with a *cold* proof-file build: some
verification conditions sit close to the solver time budget, and stolen cores
turn them into spurious timeouts.

A native build works on macOS and Linux alike, from any checkout path. The
container path is for a *fixed, published* environment rather than to work
around a platform limitation — see [docs/Container.md](docs/Container.md).

---

## How the proof fits together

### The commands that do the work

| Command | What it does |
|---|---|
| `veil module …` / `#gen_spec` (in the model files) | turns the declared state, actions and invariants into a transition system, and prepares one *verification condition* (VC) per action × property — "if the invariants hold and this action fires, this property still holds" — plus a does-not-throw VC per action |
| `#prove_action <Module> <action>` (one per file under `<Model>/Proofs/`) | re-creates every VC of one action from the module's persisted registry, discharges it with cvc5, **reconstructs** each `unsat` verdict as a Lean proof term that the kernel re-checks — the solver's word is never taken — persists the theorems, and emits the action's preservation lemma. Cells SMT cannot find carry a hand-written *tactic* in the same file (`#prove_vc … by <tactic>`) — the statement still comes from the registry — and are consumed after a statement check |
| `#gen_composition <Module>` (in `<Model>/Certify.lean`) | composes the per-action preservation lemmas into `<Module>.invariants_of_reachable` — every reachable state satisfies every invariant — plus one named `reachable_<property>` projection per property; kernel-checked at every step |
| `#veil_status <Module>` (pinned in `<Model>/Certify.lean`) | the audit command: walks the module's VC registry against the environment and reports, per VC, whether a real, statement-matching, kernel-checked theorem is in scope, and the axiom union over all of them. `#veil_status <Module> table` prints the full per-VC table |
| `#model_check` (receipt layer; the mutation test) | exhaustively explores a small concrete instance (`n = 4`, `f = 1`) — an independent, solver-free check over the same properties; and, in [Mvba/NoLock.lean](Cadence/Mvba/NoLock.lean), the mechanical refutation whose pinned counterexample a green build requires |
| `#gen_theorems` (the small models [Cadence/Cadence.lean](Cadence/Cadence.lean), [Cadence/Conductor.lean](Cadence/Conductor.lean)) | after an in-file `#check_invariants` sweep, persists each proven VC as a named theorem in the module's `.olean` |
| `#guard_msgs in #print axioms <thm>` | the trust-base pin: the build fails unless the theorem depends on *exactly* the expected axioms |

### How the files feed each other

The Chorus leg; the other legs are smaller instances of the same shape.

```
Cadence/Chorus.lean          the MODEL: state, actions, invariants. Elaborating it
   │                         persists every VC statement (the "VC registry") — it
   │                         runs no invariant sweep and persists no proofs
   ▼ imported by
Cadence/Chorus/Proofs/*.lean one file per action (41): #prove_action re-proves every
   │                         registered VC statement of that action → real
   │                         kernel-checked proofs, plus one exported preservation
   │                         lemma ("this action preserves all invariants"). The
   │                         manual quorum-intersection proofs live here too
   ▼ imported by
Cadence/Chorus/Certify.lean  #gen_composition: induction over all reachable states —
   │                         one case per action, applying its preservation lemma —
   │                         plus a named projection per property; ends in its
   │                         #guard_msgs axiom pin and the #veil_status audit pin
   ▼ imported by
Cadence/Chorus/Compose.lean      hand-written end theorems: Chorus ⊨ SlotConsensusSafety,
Cadence/Chorus/Pigeonhole.lean   and the evidence pigeonhole — each ending in its
                                 own #guard_msgs axiom pin
```

The per-action file layer exists for one reason: a module's proofs would
otherwise all have to sit in a single process's environment to be persisted,
which exceeds a 32 GB machine. One small file per action keeps every process
small, and the composition needs only one lemma per action. Those files are
ordinary hand-owned Lean files, scaffolded once by `#gen_proof_files`.

[Cadence/Cadence.lean](Cadence/Cadence.lean) and [Cadence/Conductor.lean](Cadence/Conductor.lean) are small enough to
persist their real proofs directly, and [Cadence/Composition.lean](Cadence/Composition.lean) consumes
them the same way. The receipt layer uses the same family shape and doubles
as the architecture's fast regression leg.

### What depends on what

The import graph is worth reading separately from the logical composition,
because the two run in opposite directions. A model that *consumes* a
contract does not import the module that implements it — it imports only
[Interfaces.lean](Cadence/Interfaces.lean). The instances are joined up afterwards, and exactly one
file imports all three legs:

```mermaid
flowchart TD
    IF["Interfaces.lean<br/>the module contracts"]

    IF --> GLUE["Cadence.lean<br/>the glue"]
    IF --> COND["Conductor.lean"]
    IF --> CHOR["Chorus.lean"]
    IF --> CCOMP["Chorus/Compose.lean<br/>Chorus ⊨ SlotConsensusSafety"]
    IF --> MCOMP["Mvba/Compose.lean<br/>Mvba ⊨ MVBASafety"]

    GLUE --> COMP["Composition.lean<br/>Conductor ⊨ OrchestratorSafety<br/>positional MCP Safety"]
    COND --> COMP

    CHOR --> CPROOFS["Chorus/Proofs/"] --> CCERT["Chorus/Certify.lean"] --> CCOMP

    MVBA["Mvba.lean"] --> MPROOFS["Mvba/Proofs/"] --> MCERT["Mvba/Certify.lean"] --> MCOMP

    COMP --> SYS["System.lean<br/>the glue's MCP Safety<br/>at all three instances"]
    CCOMP --> SYS
    MCOMP --> SYS
```

Two consequences worth noting. [Cadence.lean](Cadence.lean) and [Conductor.lean](Cadence/Conductor.lean) import no
proof of any other module — their theorems are statements about *any* modules
meeting the contracts — so editing them never re-runs the Chorus family,
whereas editing a contract does. And [System.lean](Cadence/System.lean) is the single file where
the three legs meet; it is the only one that imports all of them.

The receipt layer imports none of this and is verified on its own terms.

---

## What is where

```
Cadence.lean                       AUDIT ROOT: every end theorem, every axiom pin
Cadence/
  Chorus.lean                      per-slot consensus MODEL — no sweep; consumes the
                                    MVBA as a class constraint (instantiate mvba);
                                    persists the VC registry (both proof encodings of
                                    each obligation); the audited cell count is the
                                    #veil_status pin in Chorus/Certify.lean
  Chorus/Proofs/                    one proof file per action (41): #prove_action —
                                    persisted real proofs + one preservation lemma each;
                                    the manual cells live here
  Chorus/Certify.lean               #gen_composition: reachability induction + named
                                    per-property projections (axiom- and audit-pinned)
  Chorus/Compose.lean               Chorus ⊨ SlotConsensusSafety + the join toward the
                                    full SlotConsensus  (axiom-pinned)
  Chorus/Pigeonhole.lean            evidence pigeonhole for every n = 3f+1  (axiom-pinned)
  Chorus/Counting.lean              the certificate-formation counting steps for every
                                    n = 3f+1  (axiom-pinned)
  Chorus/Progress.lean              the fair-progress case split as one theorem  (axiom-pinned)
  Chorus/Liveness.lean              the run-level termination claim for Chorus and every
                                    premise it takes
  Chorus/Termination.lean           the proof of that claim, Chorus.termination  (axiom-pinned)
  Chorus/Temporal.lean              Chorus ⊨ SlotConsensus in full: the temporal and timing
                                    instances, the join  (axiom-pinned)
  Conductor.lean                   window-based orchestrator MODEL (+ sweep, traces, theorems)
  Cadence.lean                     extreme-pipelining MODEL (+ sweep, traces, theorems)
  Conductor/Schedule.lean           the Conductor's timing model and its three timed claims,
                                    stated
  Conductor/Induction.lean, Conductor/Boundedness.lean, Conductor/Recovery.lean
                                   Totality, (2W − p)-Boundedness, (2Wτ)-Recovery
                                    (axiom-pinned)
  Conductor/Temporal.lean           Conductor ⊨ Orchestrator in full: the temporal and
                                    totality instances, the join  (axiom-pinned)
  Composed/                        the composed system's timed run, its premises and its
                                    four claims: Corollary 4, Lemma 5, Liveness,
                                    censorship resistance  (axiom-pinned)
  Composed/Witness.lean, Composed/Witness/
                                   one model meeting every premise of the composed
                                    claims at once (non-vacuity)
  Composition.lean                 Cadence + Conductor reachability inductions,
                                    Conductor ⊨ OrchestratorSafety + the join toward the
                                    full Orchestrator, positional MCP Safety
  System.lean                      the composed system: the glue's MCP Safety at the
                                    Conductor, Chorus and Mvba instances — the only
                                    file importing all three legs (axiom-pinned)
  FallbackReceipt.lean             fallback receipt/propose MODEL, the post-v1 receipt rules
                                    (+ the n=4 exhaustive model check)
  FallbackReceipt/Proofs/, FallbackReceipt/Certify.lean
                                   the receipt layer's proof-file family (axiom-pinned)
  FallbackReceipt/Totality.lean    build totality for every n = 3f+1 (axiom-pinned)
  Mvba.lean                        leader-based MVBA MODEL — the internal supplement's
                                    instantiation (the supplement at the paper target); no sweep,
                                    VC registry, three sat trace witnesses
  Mvba/Proofs/, Mvba/Certify.lean  the MVBA family's proof files (26; manual cells counted in docs/Architecture.md) and
                                    certificate (axiom- and audit-pinned)
  Mvba/Compose.lean                Mvba ⊨ MVBASafety + the join toward the full MVBA
                                    (axiom-pinned)
  Mvba/NoLock.lean                 the lock check removed, mechanically refuted (pinned
                                    counterexample — the mutation test)
  Mvba/Progress.lean, Mvba/Rank.lean
                                   disabling implies progress; the lexicographic ranking
  Mvba/Liveness.lean               the MVBA's termination claim, its premises, its proof
  Mvba/Schedule.lean               the timing model and the bounded claim, stated
  Mvba/Bound.lean, Mvba/BoundedTermination.lean
                                   the good-view lemma; the burn lemma and the bound
  Mvba/Temporal.lean               the timed MVBATemporal instance and the full MVBA
  Mvba/Witness.lean                one model meeting every premise of both termination
                                    theorems (non-vacuity)
  Interfaces.lean                  the module contracts — SlotConsensus / Orchestrator / ACS /
                                    MVBA as two-level type classes over explicit state
                                    (the …Safety fragments the models consume; the full
                                    classes with every temporal obligation)
  Primitives.lean                  cryptographic primitive classes (ThresholdIBE, …)
  QuorumCounting.lean              the quorum counting facts beyond intersection
                                    (ByzNodeSetCounting)
  ByzQuorum.lean                   Byzantine-quorum instances, non-vacuity witnesses
  Windows.lean                     the ACS median lemma (plain Lean)
  ViewOrder.lean                   what a view counter needs beyond a total order
  Fairness.lean, Timed.lean        runs, enabledness and fairness; timed runs and bounded
                                    fairness after GST (plain Lean)
  ProofPrelude.lean                shared option blocks of the proof files
  Tooling.lean                     targeted #check_vc / #check_invariant commands
  Monitor/
    Alphabet.lean                  reflects Chorus.Label → published alphabet (JSON) + Rust stub
    ChorusMonitor.lean             model-conformance monitor (hand-written oracle) + CLI
    ChorusMonitorGen.lean          same monitor, instantiation generated by #gen_monitor
    MvbaStub.lean                  the monitor's stand-in for Chorus's MVBA constraint
    TraceMutate.lean               corrupt a valid trace, to model implementation bugs
Containerfile                      multi-stage OCI image: toolchain / deps / dev /
                                    build / verified / verified-cache
.devcontainer/                     opens the dev image in VS Code
.github/workflows/                 CI: re-verify every commit; publish the images
scripts/                           staged build, container dispatch, monitor suites
traces/                            JSONL trace fixtures for the monitor
docs/                              see the reading guide below
```

---

## Model-conformance monitor

The proofs above establish Chorus's safety invariants over *all* reachable
states of the model. A separate, complementary question is whether a real
execution of the Rust implementation refines the model. The monitor answers
it by replaying a projected implementation trace against the model and
reporting whether the model *accepts* (simulates) it — it runs the model's own
action bodies, one trace label at a time, and a failed guard means the
implementation diverged. It is **not** model checking and not a re-proof.

```bash
scripts/run-chorus-monitor.sh < traces/fast_path_negative.jsonl
#   → ACCEPTED — 18 step(s) simulated by the model ✓   (exit 0)

scripts/test-chorus-monitor.sh        # acceptance regression (both monitors must agree)
scripts/test-monitor-divergence.sh    # negative regression: every mutated trace must be REJECTED
scripts/test-single-node-monitor.sh   # per-node projection mode
```

Design, scope, the emitter contract and the full flag reference:
[docs/Monitor.md](docs/Monitor.md).

---

## Reading guide

The documentation is layered, so that a reader can stop at the level of
detail they need. Nothing below assumes familiarity with Lean or with formal
verification; the deeper layers assume progressively more.

### Level 1 — what is claimed (about an hour)

| | |
|---|---|
| The end theorems and the trust base on one page | [Cadence.lean](Cadence.lean) |
| **The premises of every liveness claim** — one line each: role, plausibility, witness, use | [docs/Premises.md](docs/Premises.md) |
| The verification architecture: how the layers correspond, the four methods, the trust bases | [docs/Architecture.md](docs/Architecture.md) §1–§3 |
| **The audit checklist** — everything the machine does *not* establish, by name | [docs/Architecture.md](docs/Architecture.md) §4 |

### Level 2 — is it the right claim?

| | |
|---|---|
| The module contracts — every property of each paper module, as type classes | [Cadence/Interfaces.lean](Cadence/Interfaces.lean) |
| How the modules are composed, what the composition proves, and the seams that remain | [docs/CompositionContracts.md](docs/CompositionContracts.md) |
| The liveness claim: what is machine-checked, what stays temporal, and why | [docs/Liveness.md](docs/Liveness.md) |
| The paper's Δ-bounds against the untimed models | [docs/Bounds.md](docs/Bounds.md) |
| Whether the models still match the paper, and how to re-check that mechanically | [docs/PaperAlignment.md](docs/PaperAlignment.md) |
| The paper itself, and how it is cited | [§ The protocol paper](#the-protocol-paper) |

### Level 3 — one layer at a time

Each model can be read on its own; the contracts are the only interface
between them.

| Layer | Design rationale | Source |
|---|---|---|
| **Chorus** (per-slot consensus) | [docs/ChorusDesign.md](docs/ChorusDesign.md) — the network abstraction and its soundness contract (§3), the state-locality contract with a paper analogue per relation (§3.5), the invariant map (§6), the liveness argument (§7), abstractions to review (§8) | [Cadence/Chorus.lean](Cadence/Chorus.lean) |
| **MVBA** | the model header of [Cadence/Mvba.lean](Cadence/Mvba.lean) — the specification it is read against, the state, the abstractions, and the safety argument; [docs/MvbaPlan.md](docs/MvbaPlan.md) for the decisions behind it | [Cadence/Mvba.lean](Cadence/Mvba.lean) |
| **Conductor** and the **glue** | [docs/ConductorDesign.md](docs/ConductorDesign.md) | [Cadence/Conductor.lean](Cadence/Conductor.lean), [Cadence/Cadence.lean](Cadence/Cadence.lean) |
| **Fallback receipts** | [docs/ChorusDesign.md](docs/ChorusDesign.md) §7.2 (why the receipt rules are shaped as they are) | [Cadence/FallbackReceipt.lean](Cadence/FallbackReceipt.lean) |

Every model file carries a header that states its scope, its abstractions and
its property coverage; those headers are authoritative where they and a
design document disagree.

### Level 4 — reproducing and extending

| | |
|---|---|
| The rendered documentation site: what is on it, what it costs, and what it is worth as evidence | [docs/Documentation.md](docs/Documentation.md) |
| Verso's gaps that the site works around, and which workaround to delete when each is fixed | [docs/VersoIssues.md](docs/VersoIssues.md) |
| Using the published images; **what a prebuilt `.olean` proves**, and the audit ladder | [docs/Container.md](docs/Container.md) |
| What the forked Veil provides beyond upstream, and why | [docs/Dependencies.md](docs/Dependencies.md) |
| The model-conformance monitor (implementation traces against the model) | [docs/Monitor.md](docs/Monitor.md) |
| Building and publishing the images (maintainers) | [docs/Images.md](docs/Images.md) |
| How to *work on* the models: workflow, build commands, model-specific traps | [CLAUDE.md](CLAUDE.md) |

### Records

These are dated documents kept as evidence, not as descriptions of the
current state.

| | |
|---|---|
| Open items and deferred work | [docs/TODO.md](docs/TODO.md), [docs/ChorusDesign.md](docs/ChorusDesign.md) §9 |
| The external audit of this artefact | [docs/AuditReport.md](docs/AuditReport.md) — frozen at the revision it audited (`bfeee8c`); inline notes mark what has since been closed |
| How the verification reached this state | [docs/History.md](docs/History.md) |
| The workflow this repository is arranged for | [docs/Scenario.md](docs/Scenario.md) |

## The protocol paper

> Kushal Babel, Fatima Elsheimy, Lioba Heimbach, Mohammad Mussadiq Jalalzai,
> Tobias Klenze, Jovan Komatovic, Jason Milionis, Mike Setrin, Victor Shoup.
> **Cadence: Extreme Pipelining with Multiple Concurrent Proposers.**
> arXiv:[2607.02275](https://arxiv.org/abs/2607.02275) \[cs.DC].

**The target.** The development **corresponds to paper revision
`48cac9a` (main body plus internal supplement)**: one revision of the paper
repository, whose main body has its public versions on arXiv and whose
internal supplement's Part I specifies the leader-based MVBA that
[Cadence/Mvba.lean](Cadence/Mvba.lean) models. Claims are about that
revision, and a protocol bug found here is a bug in it. The target's one
home, with its full hash, the mechanical re-check and the review behind
"corresponds", is [docs/PaperAlignment.md](docs/PaperAlignment.md) §0; its
§6 is the page of findings for the paper's authors. The commit from which
the development corresponds is tagged `paper-target/48cac9a`; the previous
target is tagged `paper-target/arxiv-v2`, and how the development moved
between targets is [docs/History.md](docs/History.md) § "Paper alignment
before the single target".

**Access to the target.** Auditors are assumed to have, or to be able to
obtain, the paper sources at the target, the internal supplement included.
All of it is to be made public, and the supplement's MVBA is a standard
leader-based BFT primitive.

**The Conductor.** The development verifies the main body's
Algorithm 7 (`algorithm:conductor`). The supplement's practical Conductor is outside the
verified surface ([docs/PaperAlignment.md](docs/PaperAlignment.md) §9).

**The receipt layer and v1.** arXiv v1 had a liveness bug in the fallback
receipt rules: a validator could propose an entry that was not valid
fallback evidence, once and for good. v2 fixed the rules, and they are
unchanged in substance at the target.
[Cadence/FallbackReceipt.lean](Cadence/FallbackReceipt.lean) models them,
and is kept as a separate model for that reason. The model checker's
counterexample to the v1 rules is at the tag
[`v1-receipt-refutation`](https://github.com/larskuhtz/cadence/tree/v1-receipt-refutation).

### Resolving a citation

The sources and documentation cite the paper as a reader sees it in the
target's rendered PDF, with the LaTeX label in parentheses as the
secondary key: Lemma 9 (`lemma:chorus-agreement`), Algorithm 5, line 7
(`line:fb-pathvote-guard`), Module 1 (`mod:slotconsensus`). The main body
and the supplement are separate documents, so a supplement citation says
so: Supplement, Section 1 (`sec:mvba-instantiation`), Supplement,
Algorithm 1, line 31 (`line:mvba:qc-decide`). Every citation is to the
target revision.

The authority for every such reference is the label map
[docs/paper-labels.tsv](docs/paper-labels.tsv): each label of the two
documents at the target, with its rendered reference and its page,
generated by machine from a build of the target. To look a label up, grep
the map. To regenerate it, for instance at a new target, run
`scripts/paper-labels.sh` (it reads the paper checkout with `git archive`
and builds both documents with `tectonic`); `scripts/paper-cites.sh` then
checks every citation in the repository against it. The labels are not
hyperlinks: the PDF is compiled with `hypertexnames=false` and carries no
label-named destinations, and arXiv's HTML substitutes its own ids.

The compiled PDFs of arXiv v1 and v2 are checked in under [paper/](paper).
