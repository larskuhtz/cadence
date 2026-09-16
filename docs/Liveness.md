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
| `progress_dichotomy_of_saturation` ([`Cadence/Chorus/Progress.lean`](../Cadence/Chorus/Progress.lean)) | in any reachable state where every honest validator has cast its path vote, commitQCs exist for every proposer from honest votes alone, **or** the MVBA is invoked with per-proposer evidence in exactly the certificate form of the decision handlers' bridge and of `mvba_propose`'s validity guards |
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
  non-monotone implementation and never invoked.) **This justification is
  specific to Chorus and does not generalise**: it holds because a slot is
  one-shot and its state purely accumulating. `Mvba` runs views, so nine of
  its honest actions are guarded by the current view and eleven can be
  disabled outright; what replaces the argument there, and why the answer
  is still weak fairness but for a different reason, is
  [`MvbaPlan.md`](./MvbaPlan.md) §3.1 and §3.2, with the disabling facts
  proven in [`Cadence/Mvba/Progress.lean`](../Cadence/Mvba/Progress.lean)
  and the measure they are progress in — a lexicographic rank that no
  transition can raise — in
  [`Cadence/Mvba/Rank.lean`](../Cadence/Mvba/Rank.lean). **`Mvba`'s
  bound-erased termination is now proven** from named premises:
  `Mvba.termination` in
  [`Cadence/Mvba/Liveness.lean`](../Cadence/Mvba/Liveness.lean), over the
  run vocabulary of [`Cadence/Fairness.lean`](../Cadence/Fairness.lean). It
  is the first liveness result in this development that is a *theorem*
  rather than a state-level fragment with the temporal step left to a named
  axiom — the scheduling assumptions are hypotheses of the statement, which
  is the discipline §2 of this document asks for. `Mvba` also needs a
  *third* scheduling class that Chorus does not, and the reason is the
  timeout: if a timeout action's guard says nothing about time, weak
  fairness forces it to fire out of every view, including the one the
  protocol is supposed to succeed in. The model therefore carries the view
  timer as an **abstract phase marker** — `expire_timer`, a clock with
  exactly one tick — and both timeout actions are guarded on it. With that
  the timeouts are weakly fair like every other honest action, and the
  third class contains the marker alone, governed by (A-viewsync): finite
  in every view below the good one, and in the good one not before a commit
  certificate exists. A *fifth* class holds `become_avail_ready`, the
  availability layer's action, governed by (F-avail): it is unguarded, so
  leaving it under weak fairness would have proven (F-avail) and hidden the
  MVBA's dependence on that layer behind "the scheduler is fair".
  Why (A-viewsync) has the shape it does, why the marker cannot be weakly
  fair, and why a GST marker alone would not change either, are
  [`MvbaPlan.md`](./MvbaPlan.md) §3.7. Those two clauses are the untimed skeleton of the
  supplement's timeout discipline, and they are the *whole* of what
  `Mvba.termination` assumes about timing —
  [`MvbaPlan.md`](./MvbaPlan.md) §3.2's correction, with the classification
  machine-checked in
  [`Cadence/Mvba/Liveness.lean`](../Cadence/Mvba/Liveness.lean).
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
monotonicity audit as the network contract. Finiteness is what makes it
work, so this ranking is also Chorus-specific: `Mvba`'s view type is
unbounded and needs the different, lexicographic ranking of
[`MvbaPlan.md`](./MvbaPlan.md) §3.3.

## 2.1 Why `Mvba` assumes more than `Chorus`, and where that ends

`Chorus`'s liveness rests on fairness plus the sub-protocol's own
termination, and nothing that names a view or a deadline. `Mvba`'s rests on
those plus (A-viewsync). The difference looks like a weakness of the MVBA
proof and is not: it is the whole stack's one unavoidable assumption becoming
visible at the layer that has to carry it.

**The two models use the same timing device.** `Chorus.lean` has an abstract
`Phase` — `pre_deadline → post_deadline → post_fb_arm → post_mvba_arm`,
advanced by three non-deterministic actions — and `Mvba.lean` has
`timer_expired`, the same device with one tick instead of three. Both replace
wall-clock time by a monotone marker, and both gate real actions on it
(`record_chunk` needs `pre_deadline`; the two `timeout_*` need
`timer_expired`). So the shapes are the same.

**Chorus's markers are weakly fair and `Mvba`'s is not**, and the reason is
what each advance *does*. Chorus's phases move the protocol from one arm to
the next: fast path, then fallback, then the MVBA arm. Advancing early
forfeits the faster arm and nothing else — there is always somewhere to fall
— and termination is then delegated to **(A-mvba)**, the sub-protocol's own.
`Mvba`'s view *is* that last arm. A timer firing early forfeits the view, and
the only thing to fall onto is another view; if every view's timer fires
early, nothing terminates at all. There is no sub-protocol left to delegate
to, so the assumption that *some* view survives its timeout has to be made
here.

That is FLP, paid where it must be. The paper pays it twice over, in the two
MVBA options: the randomised primitive pays with probability-1 termination
(no deductive framework here expresses that), and the supplement's
leader-based protocol — the one modelled — pays with partial synchrony.
(A-viewsync) is the untimed shadow of the second payment.

**Chorus does have an (A-viewsync)-shaped premise; it is just somewhere
else.** `all_honest_recorded` — "every honest validator recorded the positive
entry", in the model's own words the protocol-level shadow of
`s.deadline − Δ ≥ GST` — is exactly "the work finished before the marker
advanced". It is carried as an **antecedent of the properties** (proposal
inclusion, and the fair-progress invariants that rest on it) rather than as a
run-level premise, and it buys *proposal inclusion* rather than termination,
which is why it does not appear in a fairness list. The accounting differs;
the assumption is of the same kind.

**Where it ends.** What this work does to the stack's trust base is replace
an unconditional consensus-termination assumption by a synchroniser interface
plus a proof: (A-mvba) says "the MVBA terminates", `Mvba.termination` says
"it terminates given (A-viewsync), (F-justice), (F-avail) and the callers'
two premises", and half of (A-viewsync) — the entry — is itself derived.
The replacement is not yet formal: `Mvba.termination` is the **bound-erased
shadow** of `MVBATemporal.termination`, not that field, which is stated over
timed runs with `gst` and `ℓ`. Connecting them is the bounded phase, and the
untimed theorem is already in the right shape for it — every premise is a
predicate on a run, so a timed layer discharges them as ordinary Lean
theorems without touching the model, which is the pattern
[`Bounds.md`](./Bounds.md) §6 sets out for Chorus. In that phase (A-viewsync)
stops being an assumption: with a clock, bounded post-GST delivery gives the
decision chain a finite latency, timeout growth makes some view's budget
exceed it, and both of its clauses become theorems.
[`MvbaPlan.md`](./MvbaPlan.md) §3.7 has the detail, including why no
intermediate step — a GST marker without a clock, say — gets there earlier.

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
