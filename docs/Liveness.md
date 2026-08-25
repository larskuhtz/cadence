# Liveness — the approach, and the tool extension it would need

*This document is a **proposal**, not a description of what is proven. What
*is* proven about liveness today: the fair-progress invariants — the safety
content of the liveness argument — are machine-checked like every other
invariant, and the temporal glue (fair scheduling ⇒ eventual firing) is a
named meta-assumption. See [`Architecture.md`](./Architecture.md) §4 items 2
and 4 for exactly which assumptions that leaves, and
[`ChorusDesign.md`](./ChorusDesign.md) §7 for what the Chorus encoding does.
Closing that gap would be the largest single reduction of §4 available; this
document sketches how.*

The proposal is a path to extending Veil with deductive liveness reasoning,
accompanying [`ChorusDesign.md`](./ChorusDesign.md) §10.3. It is deliberately
narrower than full LTL: most distributed-systems liveness obligations are naturally
expressible as ω-acceptance conditions on a labelled transition system
(LTS), and can be discharged by a **liveness-to-safety (L2S)**
reduction that reuses the existing safety-VC machinery.

## 1. Why Veil's structure already does most of the work

A `veil module` already produces a **labelled guarded transition
system**: every action has a distinct name (the label), an explicit
guard (`require` clauses) and an explicit update. No control-flow
analysis is needed to recover an LTS — it is already first-class.

That is the structural prerequisite for everything below.

## 2. Surface syntax — ω-acceptance, not LTL

Rather than introducing an LTL parser, the proposed extension exposes
ω-conditions directly. Two cases cover the vast majority of practical
properties:

* **Buchi-style "infinitely often"** — assert that some action label
  fires infinitely often, or that some state predicate holds
  infinitely often.
* **Response / leads-to** — `p ↝ q` (`p` eventually implies `q`),
  i.e. `□ (p → ◇ q)`. This is the most common shape in distributed-
  systems work and subsumes "eventually `q`" via `p ≡ true`.

A strawman surface syntax:

```
fairness justice    send_vote                -- weak-fair action
fairness compassion deliver                  -- strong-fair action

acceptance [block_progresses]
  infinitely_often  finalize_commit          -- Buchi acceptance

response [eventual_commit]
  ¬ is_byz i ∧ voted i s    ↝    committed i s
```

LTL operators beyond `□`, `◇`, `↝`, and `infinitely_often` are
deferred. They are convenient but not load-bearing for the kinds of
properties Cadence-style protocols generate. Even a *block-counter
monotonically advances* property is naturally captured as "the action
that increments the counter fires infinitely often, and each occurrence
strictly changes the counter".

## 3. Discharge via liveness-to-safety (L2S)

The proposed reduction is the one developed for first-order
transition systems by Padon, Hoenicke, Losa, Podelski, Sagiv, Shoham
(*Reducing Liveness to Safety in First-Order Logic*, POPL'18). The
construction in two sentences:

> Augment the state with (a) a *witness snapshot* `σ̂` of a candidate
> "lasso head" state and (b) a flag per fairness obligation tracking
> whether that obligation was discharged since the snapshot. The
> negation of the ω-property becomes a *safety* property of the
> augmented system: it is unsafe ever to return to `σ̂` with the
> property still false and all fairness obligations satisfied (i.e.
> with a fair lasso closed).

The crucial property for Veil: the resulting verification obligation
is a **standard inductive-invariant problem on an augmented state
space**. Every piece of existing Veil machinery (`#gen_state`,
`#gen_spec`, the per-action induction VCs, the SMT discharge
pipeline, the auxiliary-invariant patterns documented for Veil's own
`Examples/Ivy/ReliableBroadcast.lean` and for `Cadence/Chorus.lean`) applies
verbatim. No new
SMT theory for well-founded orders is required; no new tactic family
is required. The user authors *auxiliary invariants for the
augmented system* — a skill they already exercise for safety.

## 4. Meta-theoretic assumptions

The L2S reduction is sound *modulo* the fair-scheduling assumption:
every action declared `justice` (resp. `compassion`) is assumed to
fire whenever continuously (resp. infinitely-often) enabled. These
assumptions belong in the framework's meta-theory and should be
documented prominently:

* They are **scheduling** assumptions about *honest* actions — the
  Byzantine-adversary actions (the `byz_*` family in `Cadence/Chorus.lean`)
  are *not* subject to fairness.
* They are **distinct from** network-level eventual-delivery
  assumptions. Cadence-style liveness needs *both* a fair-scheduling
  assumption on the validator's local actions *and* a network-level
  delivery assumption. The latter is most naturally expressed as a
  separate compassion annotation on a synthetic `network_deliver`
  action, or — in the explicit-network refactor sketched in
  [`ChorusDesign.md`](./ChorusDesign.md) §10.1 — as compassion on the
  `eventually_deliver` action.

## 5. Ranking functions — keep as an option, not a requirement

The STeP / verification-diagrams style (annotate response properties
with a ranking function into a well-founded order) is more *readable*
than L2S in cases where the ranking is obvious — "the queue size
strictly decreases", "the round number strictly increases". For these
cases the SMT obligations are simple (linear arithmetic on `ℕ`),
which Z3 handles cleanly.

It would be a worthwhile *second-tier* feature: a `ranking λ st => …`
annotation on `response` properties, generating a per-helpful-action
VC that the rank strictly decreases (or `q` is established directly).
But it is not the recommended primary path because:

* It introduces a new VC shape (well-founded decrease) that the
  user must reason about separately from inductive invariants.
* L2S already handles the same set of properties.
* For complex properties where the ranking is non-trivial
  (e.g. lexicographic over multiple counters), L2S auxiliary
  invariants are usually no harder to author.

A reasonable rollout order: L2S first (covers everything), ranking
mode later (ergonomics for the common easy cases).

## 6. What stays out of scope

* **Real-time / time-bounded liveness.** Bounded-delivery, eventual
  synchrony with a *finite* GST, deadlock detection under
  partial-synchrony — all require a notion of clock and reasoning
  about elapsed steps. Encodable in the framework (clocks are just
  monotone variables) but requires user discipline; the verifier
  itself does not need new theory.
* **Probabilistic liveness.** Asynchronous Byzantine agreement of
  the Ben-Or / common-coin / MVBA family terminates with probability
  1, not deterministically. No deductive FOL framework — STeP-style
  or L2S — handles probabilities. The standard move is to model the
  randomised primitive as an *axiomatic black box* with a
  deterministic termination guarantee assumed under a fair-scheduling
  precondition; the probability-1 argument lives on paper.
* **Full LTL** (next-step `X`, until `U` other than the response
  shape, past-time operators). Useful for some hardware-verification
  properties; rarely needed in distributed-systems work; can be
  added later via a Buchi-product translator on top of L2S.

## 7. Concrete bring-up plan

Sketching what a first implementation might look like:

1. **Action labels are already there** (`procedure_definition` /
   `action_definition` carries a name). Expose them in the model
   metadata so future syntax can refer to them.
2. **Add fairness annotations**: `fairness justice <name>`,
   `fairness compassion <name>`. Store as part of the module's
   metadata; surface them in the L2S construction below.
3. **Add `response p ↝ q`** as a top-level declaration that desugars
   to:
   a. Synthesised auxiliary state: `witness_p : state`,
      `witness_active : Bool`, and per-fair-action `fired_since_snap`
      flags.
   b. Generated transition relation that, on entering a `p ∧ ¬q`
      state, may non-deterministically snapshot.
   c. Generated safety property: it is unsafe to be back at
      `witness_p` with `witness_active`, every `fired_since_snap`
      true, and `q` still false.
   d. Hand off to the standard `#check_invariants` pipeline.
4. **Add `acceptance infinitely_often <action>`** as a degenerate
   case of (3): `p = true`, `q` defined by the action's firing flag,
   reduces to "the firing flag is set infinitely often".
5. **Document the fair-scheduling assumption** as a load-bearing
   meta-theoretic claim of the framework (analogous to the
   (M-update)+(M-frame) contract documented in `ChorusDesign.md` §3.1.1).
6. **Optionally** layer a ranking-function shorthand for
   easy-ranking response properties on top of (3).

Steps 1–5 are SMT-discharge-only and reuse the existing pipeline;
step 6 is an ergonomic extension.

## 8. Relationship to Cadence's liveness obligations

Even with this extension in place, Cadence's specific liveness
properties remain hard for the reasons in §6:

* "Honest fast-path commit eventually" — *reachable* in scope: needs
  a network-delivery compassion annotation plus the validator's local
  aggregation compassion. Worth attempting once the extension is
  ready.
* "MVBA eventually terminates" — *out of scope*. Model the MVBA
  termination as a separate axiomatic assumption (analogous to its
  agreement / external-validity assumptions).
* "Slot eventually decides" — follows once the above two are in
  hand: every honest validator either fast-commits or falls back to
  the MVBA, both of which terminate.

So while a complete liveness proof of Cadence is still gated on
modelling decisions that have nothing to do with the verifier (the
probabilistic MVBA argument, the GST/synchrony layer), there is a
useful intermediate target: prove the *deterministic* liveness
properties of the protocol modulo the standard assumptions. That
target becomes reachable once the L2S extension exists.
