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

## 5. Stating liveness and the concrete bounds at the interface

An interface is part of the model's *specification*, not a detail of the
proof: its fields are the proof obligations the sub-protocol owes, and the
composed protocol consumes them as assumptions. So an obligation belongs in
the class whether or not this project can discharge it mechanically today, and
whether or not anything consumes it yet. Omitting the temporal rows because
Veil cannot prove them, or the bounds because nothing reads them, loses the
provenance of the claim — the assumption ends up recorded where it is
consumed instead of where it originates.

There is one hazard, and it is sharp. **Veil emits every axiom of an
instantiated class to the solver.** That is the mechanism §3 depends on, but
it means a field that is not first-order poisons the whole module: adding a
`totality` field quantifying over a run (`run : Nat → state`) to the
instantiated class made **all nine** VCs of the consuming module crash with

    cvc5.Error.error "Symbol '->' not declared as a type"

— cvc5 has no function sorts, and the arrow reached the encoder verbatim.

The fix is a two-level contract, checked and working:

```lean
class OrchSafety (validator slot state : Type) where
  init … step … reachable … opened … completed … byz … lt …
  reachable_init … reachable_step …
  opened_monotone        -- Monotonicity
  open_prefix_agreement  -- the safety residue

/-- A run: the execution the temporal obligations speak about. -/
structure OrchRun (state : Type) [O : OrchSafety validator slot state] where
  at' : Nat → state
  starts : at' 0 = O.init
  steps  : ∀ n, O.step (at' n) (at' (n + 1))

class Orch (validator slot state : Type)
    extends OrchSafety validator slot state where
  totality    : …    -- (A-orch-totality), over an OrchRun
  bound       : Nat  -- the deployment's B = 2W − p, carried as data
  boundedness : …    -- (A-orch-boundedness), over an OrchRun
```

The consuming Veil module writes `instantiate orch : OrchSafety node slot
ostate` — the first-order fragment only — and its VCs all discharge. `Orch`
extends it, so `F.toOrchSafety` hands the composition exactly what it assumes:
an implementation owes the full contract and nothing is omitted from the
interface. What differs between the two levels is only *which* fields cross
into the SMT layer, not which are specified.

Two further consequences worth taking deliberately.

* **The obligation table becomes the class.** The rows in
  [`Interfaces.lean`](../Cadence/Interfaces.lean)'s Orchestrator table are
  exactly these fields; once they are fields, the table is a rendering of the
  contract rather than a substitute for it.
* **An unmet obligation becomes type-visible.** Conductor can supply an
  `OrchSafety` instance — those fields are proven — but not an `Orch`
  instance, because totality and boundedness are not mechanically provable
  here yet. That is the honest state, and stating it this way is *stronger*
  than a prose row: the absence of an `Orch` instance is checkable, whereas a
  table entry is not. If something later needs to consume a temporal field
  before Veil can prove it, it should enter as a named `axiom` in a file
  carrying its own `#print axioms` pin, so the extra assumption shows up in
  the trust base instead of in prose — never by weakening the pins on the end
  theorems, which stay at `[propext, Classical.choice, Quot.sound]`.

## 6. The inventory: does every contract follow the pattern?

Ten contract classes, in two groups. The split is not stylistic: it is whether
the carrier is *data* or a *run*.

### Algebraic primitives — already in the right shape

Every field is a function of the declared types and every property is a pure
statement about those functions, so each is consumable as an `instantiate`
constraint exactly as `ByzNodeSet` is. These are the positive control for the
pattern, and they need no restatement.

| Class (`Primitives.lean`) | Operations | Laws |
|---|---|---|
| `HashFunction` | `hash` | `collision_resistant` |
| `SignatureScheme` | `Sign`, `Verify`, `signer` | `sound`, `unforgeable`, `sound_signer`, `unforgeable_signer` |
| `ErasureCoding` | `Encode`, `Decode` | `decode_sound`, `encode_inj` |
| `MerkleTree` | `MerkleRoot`, `MerkleProof`, `VerifyMerkle` | `sound`, `binding` |
| `ThresholdIBE` | `Enc`, `KeyShare`, `VerifyShare`, `Dec`, `mpk`, `msk` | `decrypt_sound`, `decrypt_secret` |

Two caveats that are about content rather than shape. `ThresholdIBE`'s
`decrypt_secret` is a *structural* surrogate — "if `Dec` succeeded then a
verified `≥ t` share set existed" — not computational hiding, which is not
expressible in this style at all and stays a named meta-assumption
([`Architecture.md`](./Architecture.md) §4 item 3). And **none of these five is
consumed via `instantiate` by any model**: the only `instantiate` of a
contract anywhere is `ByzNodeSet`. They are correctly shaped but unwired,
which is the mirror image of the sub-protocol problem and a separate item.

### Sub-protocol interfaces — all carry the same defect

Each has a carrier that is really a run, with the index hidden, so each needs
the two-level treatment of §5.

| Class | Hidden-state carrier | Currently prose | Also needs |
|---|---|---|---|
| `Orchestrator` | `opened`, `completed` | Totality, Integrity ×2, Monotonicity, `B`-boundedness, `R`-recovery | — (design settled, §5) |
| `SlotConsensus` | `finalized`; `on_time_proposal` is documented as "per-instance data fixed by the execution" | Hiding, ℓ-Termination (A-sc-termination), Quiescence | resolving per-instance vs the glue's slot-indexed family |
| `SlotConsensusWithTotality` | inherits | `d_tot`-Totality (A-sc-totality) | it is an **empty** `extends SlotConsensus` — see below |
| `ACS` | `proposed`, `decided`, `has_decided` | ℓ-Termination (A-acs-termination), Δ-Totality (A-acs-totality), quantitative validity | not consumed as a class at all (Conductor models a window interval) |
| `MVBA` | `input`, `output` — whose docstring says "eventually populated", so time is hidden too | ℓ_MVBA-Termination, Quiescence | not consumed as a class at all (Chorus inlines the oracle) |

Three observations worth acting on.

* **The codebase already anticipated the two-level shape.**
  `SlotConsensusWithTotality extends SlotConsensus` has an *empty body*, with
  a docstring explaining that the property is temporal so "this class adds no
  formal fields — it is a marker carrying the documented obligation". That is
  precisely the upper level of §5, left unpopulated. Filling it in is the
  smallest possible first instance of the pattern.
* **The upper level takes three kinds of field, not one.** Beyond temporal
  properties, the ACS table marks its quantitative validity half documented
  because cardinality is "outside the first-order language", and
  `B`-boundedness is the same kind of statement. Liveness, bounds and
  cardinality all belong at the non-first-order level; only the first-order
  residue goes in the fragment a Veil module instantiates.
* **`ByzNodeSet` is the only contract in the development that is both
  correctly shaped and discharged by a proven instance.** `Orchestrator` and
  `SlotConsensus` have constructed instances (`orchestrator_instance`,
  `Chorus.slotConsensus_instance`) but the wrong shape; the five primitives
  have the right shape and no instance and no consumer; `ACS` and `MVBA` have
  neither.

### The uniform target

For each sub-protocol interface `X`:

* `XSafety` — first-order: the carrier accessors over an explicit state,
  `init`/`step`/`reachable`, and the state-predicate properties. This is what
  a consuming Veil module `instantiate`s.
* `XRun` — the execution its temporal obligations quantify over.
* `X extends XSafety` — the specification proper: every remaining row of the
  obligation table as a field, including bounds carried as data.

An implementation owes `X`; a Veil consumer assumes `XSafety`; `toXSafety`
connects them. Obligations this project cannot yet discharge stay stated and
uninstantiated, which makes the gap type-visible rather than prose.

## 7. What this does not fix

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
