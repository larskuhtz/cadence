import Veil
import Cadence.Interfaces

/-! Spike: an Orchestrator contract with its state EXPLICIT in the type, so
every field is a pure function of declared types, consumed by a Veil module
as an ordinary class constraint (the `ByzNodeSet` pattern).

The question this answers: does Veil hand an instantiated class's axioms to
the solver, so the consumer can *use* the contract rather than restate it? -/

class MiniOrch (validator slot state : Type) where
  -- the orchestrator's own state, abstract to the consumer
  init      : state
  step      : state → state → Prop
  reachable : state → Prop
  -- observations: pure predicates on that state
  opened    : state → validator → slot → Prop
  byz       : validator → Prop
  lt        : slot → slot → Prop
  -- structure
  reachable_init : reachable init
  reachable_step : ∀ st st', reachable st → step st st' → reachable st'
  -- Monotonicity: today a documented obligation, here a formal field
  opened_monotone : ∀ st st' i s, step st st' → opened st i s → opened st' i s
  -- NEGATIVE CONTROL: the safety axiom is deliberately absent

veil module Mini

type node
type slot
type ostate

instantiate orch : MiniOrch node slot ostate

-- the orchestrator's state, held explicitly by the consuming protocol
individual os : ostate
relation appended (i : node) (s : slot)

#gen_state

after_init {
  os := orch.init
  appended I S := false
}

-- the orchestrator advances; the consumer only knows it took a legal step
action orch_step (os' : ostate) {
  require orch.step os os'
  os := os'
}

action append (i : node) (s : slot) {
  require ¬ orch.byz i
  require orch.opened os i s
  appended i s := true
}

-- (1) the consumer tracks reachability of the orchestrator's state
invariant [os_reachable]
  orch.reachable os

-- (2) maintained only because the contract promises monotonicity
invariant [appended_opened]
  ∀ i s, appended i s → orch.opened os i s

-- (3) THE test: can the solver *use* the class axiom, or must it be restated?
invariant [prefix_agreement_usable]
  ∀ i j s s', ¬ orch.byz i → ¬ orch.byz j →
    orch.opened os i s' → orch.opened os j s → orch.lt s' s → orch.opened os j s'

#gen_spec
#check_invariants

end Mini
