import Veil
import Cadence.Interfaces

/-! Spike: state the WHOLE contract at the interface, including liveness and
bounds, while keeping the part a Veil module instantiates first-order.

`OrchSafety` is the first-order fragment the consuming module instantiates.
`Orch` is the full contract — the specification proper — extending it with the
temporal and quantitative obligations. An implementation owes `Orch`; the Veil
composition consumes `OrchSafety`; nothing is omitted from the interface. -/

class OrchSafety (validator slot state : Type) where
  init      : state
  step      : state → state → Prop
  reachable : state → Prop
  opened    : state → validator → slot → Prop
  completed : state → validator → slot → Prop
  byz       : validator → Prop
  lt        : slot → slot → Prop
  reachable_init  : reachable init
  reachable_step  : ∀ st st', reachable st → step st st' → reachable st'
  /-- Monotonicity (`mod:orchestrator_2`). -/
  opened_monotone : ∀ st st' i s, step st st' → opened st i s → opened st' i s
  /-- Open-prefix agreement: the safety residue of Totality + Monotonicity. -/
  open_prefix_agreement : ∀ st, reachable st →
    ∀ i j s s', ¬ byz i → ¬ byz j →
      opened st i s' → opened st j s → lt s' s → opened st j s'

/-- A run of the orchestrator: the execution its temporal obligations speak
about. -/
structure OrchRun (state : Type) [O : OrchSafety validator slot state] where
  at' : Nat → state
  starts : at' 0 = O.init
  steps  : ∀ n, O.step (at' n) (at' (n + 1))

class Orch (validator slot : Type) (state : Type)
    extends OrchSafety validator slot state where
  /-- **Totality** (A-orch-totality), eventual form: what one correct
      validator opens, every correct validator opens. -/
  totality : ∀ (r : @OrchRun validator slot state toOrchSafety) (i j : validator) (s : slot),
    ¬ byz i → ¬ byz j → (∃ n, opened (r.at' n) i s) → ∃ m, opened (r.at' m) j s
  /-- **`B`-Boundedness** (A-orch-boundedness): at most `B` opened-but-
      uncompleted slots at any point, for the deployment's `B = 2W − p`. -/
  bound : Nat
  boundedness : ∀ (r : @OrchRun validator slot state toOrchSafety) (n : Nat) (i : validator)
      (f : Fin (bound + 1) → slot),
    ¬ byz i → (∀ k, opened (r.at' n) i (f k) ∧ ¬ completed (r.at' n) i (f k)) →
    ¬ Function.Injective f

veil module MiniSplit

type node
type slot
type ostate

-- the module instantiates only the first-order fragment
instantiate orch : OrchSafety node slot ostate

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

end MiniSplit

-- The full contract still reaches the safety fragment the module consumed,
-- so an implementation owing `Orch` discharges what the composition assumes.
example (validator slot state : Type) [F : Orch validator slot state] :
    OrchSafety validator slot state := F.toOrchSafety
