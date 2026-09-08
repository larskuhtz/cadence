import Veil

/-! Spike 05 (2026-09-04): the three mechanics questions the final design
rests on, beyond what 01–04 established.

1. Can a later `instantiate` refer to an *earlier* instantiated parameter —
   a shared fault model whose `byz` is passed as an explicit class argument
   (so that every contract a module consumes is stated against one notion
   of "correct"), and a `TotalOrder` instance resolved as an inst-implicit
   class argument?
2. Does a per-slot abstract state — `function sc_state (s : slot) : scstate`
   — with class-field applications `sc.finalized s (sc_state s) i v` in
   guards and invariants translate to SMT?
3. Does the solver then discharge the consumer's agreement and prefix
   invariants from the class axioms *at the reachable abstract state*?

Expected: `exit 0`, all `✅`. This is the shape `Cadence/Cadence.lean` now
has (with the real contracts of `Cadence/Interfaces.lean`).

Two Veil facts this file also records, because its first version tripped over
both (and was committed with them, 2026-09-04): an `assumption` may mention
immutable components only — a mutable `os` in one is rejected with
`Unbound uncapitalized variable` — so the initial abstract states are
immutable parameters constrained by assumptions; and an action parameter must
not be named `st'`, which the trace pipeline uses for the post-state. -/

class FaultModel (validator : Type) where
  byz : validator → Prop

class OrchS (validator slot state : Type) [ord : TotalOrder slot] (byz : validator → Prop) where
  init : state → Prop
  step : state → state → Prop
  reachable : state → Prop
  opened : state → validator → slot → Prop
  reachable_init : ∀ st, init st → reachable st
  reachable_step : ∀ st st', reachable st → step st st' → reachable st'
  opened_monotone : ∀ st st' i s, step st st' → opened st i s → opened st' i s
  open_prefix_agreement : ∀ st, reachable st →
    ∀ i j s s', ¬ byz i → ¬ byz j →
      opened st i s' → opened st j s → ord.le s' s → s' ≠ s → opened st j s'

class ScS (slot validator pvector state : Type) (byz : validator → Prop) where
  init : slot → state → Prop
  step : slot → state → state → Prop
  reachable : slot → state → Prop
  finalized : slot → state → validator → pvector → Prop
  reachable_init : ∀ s st, init s st → reachable s st
  reachable_step : ∀ s st st', reachable s st → step s st st' → reachable s st'
  finalized_monotone : ∀ s st st' i V, step s st st' → finalized s st i V → finalized s st' i V
  agreement : ∀ s st, reachable s st → ∀ i j V V', ¬ byz i → ¬ byz j →
    finalized s st i V → finalized s st j V' → V = V'

veil module SpkA

type node
type slot
type ostate
type scstate
type pvector

instantiate slot_ord : TotalOrder slot
instantiate fm : FaultModel node
instantiate orch : OrchS node slot ostate fm.byz
instantiate sc : ScS slot node pvector scstate fm.byz

-- the sub-protocols' initial states: per-execution data, constrained below
immutable individual os0 : ostate
immutable function sc_init_state : slot → scstate
-- the orchestrator's state and one slot-consensus state per slot, held
-- explicitly by the consuming protocol
individual os : ostate
function sc_state (s : slot) : scstate
relation appended (i : node) (s : slot) (v : pvector)

#gen_state

assumption [os_init] orch.init os0
assumption [sc_init] ∀ s, sc.init s (sc_init_state s)

after_init {
  os := os0
  sc_state S := sc_init_state S
  appended I S V := false
}

action orch_step (os_next : ostate) {
  require orch.step os os_next
  os := os_next
}

action sc_step (s : slot) (sc_next : scstate) {
  require sc.step s (sc_state s) sc_next
  sc_state s := sc_next
}

action append (i : node) (s : slot) (v : pvector) {
  require ¬ fm.byz i
  require orch.opened os i s
  require sc.finalized s (sc_state s) i v
  appended i s v := true
}

invariant [os_reachable] orch.reachable os
invariant [sc_reachable] ∀ s, sc.reachable s (sc_state s)
invariant [appended_opened] ∀ i s v, appended i s v → orch.opened os i s
invariant [appended_finalized] ∀ i s v, appended i s v → sc.finalized s (sc_state s) i v
invariant [log_agreement] ∀ i j s v v', ¬ fm.byz i → ¬ fm.byz j →
  appended i s v → appended j s v' → v = v'
invariant [prefix_usable] ∀ i j s s', ¬ fm.byz i → ¬ fm.byz j →
  orch.opened os i s' → orch.opened os j s → slot_ord.le s' s → s' ≠ s → orch.opened os j s'

#gen_spec
#check_invariants

end SpkA
