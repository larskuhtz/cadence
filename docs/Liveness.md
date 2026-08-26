# Liveness — what is proven, what is assumed

*The audit summary for the liveness claim. The model-level narrative — how
the theorems and assumptions compose against Chorus's actions and
invariants — is [`ChorusDesign.md`](./ChorusDesign.md) §7; the assumption
inventory is [`Architecture.md`](./Architecture.md) §4 items 2 and 4.*

## 1. The shape of the claim

The liveness claim — under the named assumptions below, every honest
validator eventually commits — factors into state-level facts and temporal
steps. **Every state-level fact is a kernel-checked, axiom-pinned theorem**
over reachable states, for every `n = 3f+1`:

| Theorem | Says |
|---|---|
| `progress_dichotomy_of_saturation` ([`Cadence/Chorus/Progress.lean`](../Cadence/Chorus/Progress.lean)) | in any reachable state where every honest validator has cast its path vote, commitQCs exist for every proposer from honest votes alone, **or** the MVBA is invoked with per-proposer evidence in exactly the `mvba_decide_*` guard form |
| `evidence_pigeonhole_of_reachable` ([`Cadence/Chorus/Pigeonhole.lean`](../Cadence/Chorus/Pigeonhole.lean)) | `2f+1` honest per-proposer fallback entries always yield a FallbackQC or an EquivCert |
| `fbcert_of_honest_fallback_votes`, `fbcommitqc_of_honest_commit_votes`, `commitqc_of_honest_fast_dominant` ([`Cadence/Chorus/Counting.lean`](../Cadence/Chorus/Counting.lean)) | certificate formation: the honest population is itself the quorum; a supermajority of honest fast commit votes is a per-proposer commitQC |
| `build_totality_of_reachable` (same file) | **any** supermajority of accepted receipts, Byzantine members included, yields a buildable fallback meta-block entry per proposer — "every correct validator can propose", at the state level |

plus the fair-progress and enabledness invariants of the sweep (the
"Liveness" section of [`Cadence/Chorus.lean`](../Cadence/Chorus.lean)).

**Every temporal step is an instance of one rule** — *a continuously
enabled fair action eventually fires* — applied at named seams:
(F-justice) drives every honest validator to the dichotomy's saturation
hypothesis and fires the certificate-to-commit actions after it, and
(A-mvba) consumes the dichotomy's conclusion. Nothing else is assumed: no
counting, no case analysis, no certificate or quorum reasoning lives
outside Lean.

## 2. The assumptions, exactly

* **(F-justice)** — honest actions are weakly fair. Weak (not strong)
  fairness suffices because the model is monotone: enabledness is itself
  monotone, so the enable/disable toggle that strong fairness exists for
  cannot occur. ((F-compassion) is reserved vocabulary for the
  non-monotone implementation and never invoked.)
* **(F-byz)** — Byzantine actions (the `byz_*` family) are unfair:
  progress never relies on adversarial help, which makes the discharged
  content strictly stronger than deadlock freedom.
* **(A-mvba)** — the MVBA primitive's own liveness: invoked with
  per-proposer evidence, it eventually decides every proposer and
  terminates. The randomised primitive terminates with probability 1,
  which no deductive framework expresses — the probability argument stays
  on paper, exactly as for any cryptographic primitive contract.
* Scheduling is distinct from **network delivery**. The monotone network
  makes broadcast signatures globally visible, so delivery surfaces only
  as fairness on the observation actions (`record_chunk`,
  `redisseminate_chunk`, `aggregate_fastqc_*`); the network abstraction's
  own soundness contract is [`Architecture.md`](./Architecture.md) §4
  item 1.

The well-founded ranking that makes the chain terminate is structural:
per-slot state is finite and all relations are monotone, so every fair
firing strictly shrinks the residual of unset tuples. It rests on the same
monotonicity audit as the network contract.

## 3. What would close the rest

Veil has no fairness annotations and no quantification over runs, so the
rule "continuously enabled ⇒ eventually fires" is not expressible today.
The designed extension — fairness classes on actions,
ω-acceptance/response properties, discharged by the POPL'18
**liveness-to-safety** reduction on the existing safety-VC pipeline — is
Veil work and lives in the fork: **`docs/Liveness.md` on the
`lars/liveness` branch of `larskuhtz/veil`**. With it, (F-justice) becomes
the premise of a Lean theorem and the deterministic liveness properties
("honest fast-path commit eventually", "slot eventually decides") become
provable in-system. (A-mvba)'s probability-1 core, and real-time bounds
(GST, latency — the models are untimed), stay out of scope regardless.

The paper's concrete Δ-bounds are a separate, *incomparable* layer — they
assume strong partial synchrony, where the model's claims above need only
eventual delivery. How the two relate, and the routes by which bounds
could be brought into the model, is [`Bounds.md`](./Bounds.md).
