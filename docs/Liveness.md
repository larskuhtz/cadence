# Liveness — what is proven, what is assumed, what would close the gap

*What **is** proven about liveness today: the fair-progress invariants —
the safety content of the liveness argument — are machine-checked like
every other invariant, and the temporal glue (fair scheduling ⇒ eventual
firing) is a named meta-assumption. See [`Architecture.md`](./Architecture.md)
§4 items 2 and 4 for exactly which assumptions that leaves, and
[`ChorusDesign.md`](./ChorusDesign.md) §7 for what the Chorus encoding does.
This document records the assumption structure on the Cadence side and what
a tool extension would reduce it to; the extension's design itself is tool
work and lives in the Veil fork (see §1).*

## 1. The tool extension (design lives in the fork)

Closing the temporal gap would be the largest single reduction of
[`Architecture.md`](./Architecture.md) §4 available: (F-justice), (F-byz)
and (A-mvba) would become *premises of a Lean theorem* rather than named
assumptions beside one. The proposed mechanism, in one sentence: annotate
actions with fairness classes and state ω-acceptance / response
(`p ↝ q`) properties directly, then discharge them by the POPL'18
**liveness-to-safety (L2S)** reduction — a snapshot-augmented state space
on which the negated ω-property is an ordinary inductive-invariant
problem, so Veil's whole existing safety-VC pipeline applies verbatim.

That design — surface syntax, the L2S construction, ranking functions as a
second-tier option, and the bring-up plan — is Veil work, and per this
repository's documentation rules it lives in the fork:
**`docs/Liveness.md` on the `lars/liveness` branch of `larskuhtz/veil`**.

## 2. The fairness assumptions the extension would internalise

The assumptions are stated and consumed in the models' own liveness
sections ([`ChorusDesign.md`](./ChorusDesign.md) §7 narrates them); what
matters structurally:

* They are **scheduling** assumptions about *honest* actions only — the
  Byzantine-adversary actions (the `byz_*` family in
  [`Cadence/Chorus.lean`](../Cadence/Chorus.lean)) carry no fairness and
  can never satisfy a progress obligation ((F-byz)).
* Weak fairness suffices in the monotone model: enabledness is itself
  monotone, so the enable/disable toggle that strong fairness exists for
  cannot occur ((F-compassion) is reserved vocabulary for the non-monotone
  implementation and never invoked).
* Scheduling is **distinct from** network-level eventual delivery. A full
  liveness proof needs both: fairness on the validators' local actions,
  and a delivery assumption — under the extension, a compassion
  annotation on a synthetic delivery action (or on the delivery action of
  the explicit-network refactor sketched in
  [`ChorusDesign.md`](./ChorusDesign.md) §10.1).

## 3. Cadence's obligations, mapped to the extension

Even with the extension in place, Cadence's liveness properties split by
what they need:

* **"Honest fast-path commit eventually"** — *in scope*: a
  network-delivery compassion annotation plus fairness on the validator's
  local aggregation actions. Worth attempting as soon as the extension
  exists; the fair-progress invariants it would build on are already
  proven.
* **"MVBA eventually terminates"** — *out of scope permanently*: the
  randomised primitive terminates with probability 1, and no deductive
  FOL framework handles probabilities. It stays an axiomatic black box
  with a deterministic termination guarantee under a fair-scheduling
  precondition — exactly the current (A-mvba) treatment — and the
  probability-1 argument stays on paper.
* **"Slot eventually decides"** — follows once the above two are in hand:
  every honest validator either fast-commits or falls back to the MVBA,
  both of which terminate.

Real-time bounds (GST-style bounded delivery, latency) stay out of scope
either way: the models are untimed, and no formal artefact here claims a
latency bound ([`Architecture.md`](./Architecture.md) §4 item 4).

So the useful intermediate target is unchanged: prove the *deterministic*
liveness properties modulo the standard assumptions. That target becomes
reachable once the L2S extension exists — and until then, the split above
is the honest statement of where the machine stops and the assumptions
begin.
