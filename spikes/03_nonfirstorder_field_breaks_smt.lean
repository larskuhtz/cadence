import Veil
import Cadence.Interfaces

/-! Spike: does adding a NON-first-order field (a liveness property that
quantifies over runs) to a class the Veil module instantiates break SMT
translation of the module's VCs?

If it does, the contract must be split: a first-order part the module
instantiates, extended by the full contract used only at the Lean level. -/

class MiniOrchLive (validator slot state : Type) where
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
  -- Totality: quantifies over a RUN, i.e. over a function `Nat → state`.
  -- Deliberately not first-order.
  totality : ∀ (run : Nat → state), run 0 = init → (∀ n, step (run n) (run (n + 1))) →
    ∀ i j s, ¬ byz i → ¬ byz j → (∃ n, opened (run n) i s) → ∃ m, opened (run m) j s

veil module MiniLive

type node
type slot
type ostate

instantiate orch : MiniOrchLive node slot ostate

individual os : ostate
relation appended (i : node) (s : slot)

#gen_state

after_init {
  os := orch.init
  appended I S := false
}

action orch_step (os' : ostate) {
  require orch.step os os'
  os := os'
}

action append (i : node) (s : slot) {
  require ¬ orch.byz i
  require orch.opened os i s
  appended i s := true
}

invariant [os_reachable]
  orch.reachable os

invariant [appended_opened]
  ∀ i s, appended i s → orch.opened os i s

invariant [prefix_agreement_usable]
  ∀ i j s s', ¬ orch.byz i → ¬ orch.byz j →
    orch.opened os i s' → orch.opened os j s → orch.lt s' s → orch.opened os j s'

#gen_spec
#check_invariants

end MiniLive
