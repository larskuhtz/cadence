# Module contracts: making the state explicit

*Design note. It records a defect in how the module contracts are stated, the
fix, and the experiment showing the fix works in Veil. Nothing here is
implemented yet beyond the Orchestrator's property being single-sourced; the
migration is [`TODO.md`](./TODO.md) § "Contract composition".*

## 1. The defect

[`Interfaces.lean`](../Cadence/Interfaces.lean)'s contracts are stated as
*snapshots*. `Orchestrator.opened : validator → slot → Prop` looks like a pure
predicate on two declared types, but it is not a function of those types: what
a validator has opened depends on how far the run has got. The index is real
and merely hidden — `Composition.lean`'s `orchestrator_instance` takes a state
`st` and a proof that it is reachable, and returns an `Orchestrator`. So "the
Orchestrator" is a *family indexed by state*, and the class type does not say
so. Veil is honest about this where the contract is not: it generates every
named invariant as `Conductor.open_prefix_agreement th st`, explicitly indexed.

Three consequences follow, and they are one problem rather than three.

* **The class cannot be consumed as a constraint.** This is the visible
  symptom: a consumer cannot `instantiate` a contract whose carrier is really
  its own evolving state, so it restates the property instead, tied to the
  class only by a comment. Nothing checks the restatement.
* **The temporal properties have nowhere to live.** Totality, Monotonicity,
  Integrity, `B`-boundedness and `R`-recovery are all properties of *runs*. A
  snapshot contract cannot state them, so they became prose rows in an
  obligation table with named meta-axioms, discharged by argument rather than
  by the machine.
* **The contract is nearly empty.** What survives into `Orchestrator` is one
  field, `open_prefix_agreement`, which an orchestrator that never opens
  anything satisfies vacuously. Everything that makes an orchestrator
  *orchestrate* sits outside the formal claim.

Note what is *not* the problem: `ByzNodeSet` is consumed exactly as a class
constraint should be (`instantiate nset : ByzNodeSet node nodeset`, discharged
by `byzNodeSetFin`), because its operations genuinely are functions of `node`
and `nset`. The contrast is the diagnosis, not a Veil limitation.

## 2. The fix

State the contract over an explicit state type, so every field is a pure
function of declared types and the consuming module can take it as an ordinary
class constraint. The consumer holds the orchestrator's state as a state
component of its own and reads it through the contract's accessors.

The contract may carry a *simpler* state than the implementation operates on —
the Conductor's windows, clock and ACS need not appear — provided it carries
enough to support the safety content the consumer needs. Stating more than the
consumer uses is a feature, not waste: it puts each assumption where it
*originates* rather than only where it is consumed, which is what makes a claim
traceable through the stack.

## 3. The experiment

Both halves were checked against the real pipeline, with a negative control.

```lean
class MiniOrch (validator slot state : Type) where
  init      : state
  step      : state → state → Prop
  reachable : state → Prop
  opened    : state → validator → slot → Prop
  byz       : validator → Prop
  lt        : slot → slot → Prop
  reachable_init  : reachable init
  reachable_step  : ∀ st st', reachable st → step st st' → reachable st'
  opened_monotone : ∀ st st' i s, step st st' → opened st i s → opened st' i s
  open_prefix_agreement : ∀ st, reachable st →
    ∀ i j s s', ¬ byz i → ¬ byz j →
      opened st i s' → opened st j s → lt s' s → opened st j s'

veil module Mini
type node ; type slot ; type ostate
instantiate orch : MiniOrch node slot ostate
individual os : ostate
relation appended (i : node) (s : slot)
#gen_state
after_init { os := orch.init ; appended I S := false }
action orch_step (os' : ostate) { require orch.step os os' ; os := os' }
action append (i : node) (s : slot) {
  require ¬ orch.byz i
  require orch.opened os i s
  appended i s := true }
invariant [os_reachable]    orch.reachable os
invariant [appended_opened] ∀ i s, appended i s → orch.opened os i s
invariant [prefix_agreement_usable]
  ∀ i j s s', ¬ orch.byz i → ¬ orch.byz j →
    orch.opened os i s' → orch.opened os j s → orch.lt s' s → orch.opened os j s'
#gen_spec
#check_invariants
```

**All invariants discharge.** Three findings:

1. **A Veil module can consume a state-explicit contract as a class
   constraint.** `instantiate` accepts it, because the state type is a module
   *parameter* (`type ostate`) rather than the module's generated `State` — the
   ordering constraint that blocks the snapshot form does not arise.
2. **Veil feeds the instantiated class's axioms to the solver.** This is what
   makes the approach work at all, and it is the same mechanism `ByzNodeSet`
   already relies on. `prefix_agreement_usable` is discharged from
   `open_prefix_agreement` and `os_reachable`; the consumer *uses* the contract
   rather than restating it.
3. **Negative control: the axiom is load-bearing.** Removing
   `open_prefix_agreement` from the class and changing nothing else makes
   `prefix_agreement_usable` fail with a counterexample (`❌`) while every other
   invariant still passes. So the discharge above is not vacuous.

A fourth point falls out unasked: `appended_opened` is maintainable *only*
because `opened_monotone` is a formal field. Making the state explicit forces
Monotonicity — today a prose row in the obligation table — to become a stated
axiom that does real work. That is the provenance benefit, demonstrated rather
than argued.

## 4. What this supersedes

An earlier attempt single-sourced the property as shared *syntax*
(`openPrefixAgreement%`), so that the consumer's invariant and the class field
expand from one definition. That closes the drift between two statements, and
it removed a real shape mismatch — the class demanded `le ∧ ≠` where the models
prove `lt`, so the instance carried a hand conversion, now deleted. But it
leaves the hidden index in place, and by making the two statements textually
identical it makes the conflation between the provider's state and the
consumer's observation *harder* to see. It should be treated as scaffolding and
removed when the contracts are restated, not extended to the other contracts.

For the record of why a shared *definition* was not used instead: a `def` over
the carrier does not survive SMT translation, because the carrier arrives as a
function argument and SMT-LIB is first-order. That constraint disappears in the
design above, where the carrier is an uninterpreted state sort and the
accessors are uninterpreted predicates applied to it — all first-order.

## 5. What this does not fix

The consumer's `opened` and the implementation's `opened` remain different
objects, related by an observation map. Making the index explicit turns that
from something hidden into something nameable, but it does not discharge it —
trace-level refinement stays out of scope
([`Composition.lean`](../Cadence/Composition.lean)'s header,
[`ChorusDesign.md`](./ChorusDesign.md) §10.1).

Nor does it make the temporal rows *provable*: Veil has no fairness or
run quantification today ([`Liveness.md`](./Liveness.md)). It makes them
*stateable*, which converts "trust this prose row" into "assume this named
formal hypothesis" — a declared gap rather than an unchecked one.
