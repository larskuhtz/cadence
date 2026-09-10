import Veil

/-! Spike: the **negative control** for the slot-tag encoding of
`07_sc_state_tag_ok.lean`.

That spike replaces `SlotConsensusSafety`'s slot index by a state observable
`tag : state → slot`, preserved by every transition (`tag_frame`), and shows
that the consumer can still prove "slot `s`'s state is tagged `s`"
(`[sc_tagged]`) and, from it, that an appended vector carries its slot
(`[appended_slot]`).

This file is that module with **`tag_frame` deleted from the class** and
nothing else changed. If `[sc_tagged]` still passed, the encoding would be
proving itself for some other reason and the spike above would be vacuous —
so the expected result is a counterexample, at exactly the action that moves
a slot-consensus state.

**Expected: `exit 1`, and exactly one `❌` — `sc_tagged` under `sc_step`.**
Every other cell still passes, including `appended_slot`, which *reads*
`sc_tagged`: each cell assumes the whole invariant clump at the pre-state, so
a broken conjunct only fails its own cell. That is the shape of an inductive
counterexample, and it is why the one ❌ is the right amount of evidence.
Read the exit code from `scratch.sh` itself.

The counterexample also prints `orch.toTSS.init`, which is worth noting: the
skeleton parent is destructured into the solver's hypotheses, so a contract
that `extends` one is consumed exactly like a flat one. -/

set_option linter.unusedVariables false

class FaultModel (validator : Type) where
  byz : validator → Prop

/-- The shared skeleton: what every module contract has because it is a
transition system, stated once. -/
class TSS (state : Type) where
  init : state → Prop
  step : state → state → Prop
  trans : state → state → Prop
  reachable : state → Prop
  step_trans : ∀ st st', step st st' → trans st st'
  reachable_init : ∀ st, init st → reachable st
  reachable_trans : ∀ st st', reachable st → trans st st' → reachable st'

/-- The orchestrator fragment — unindexed already, extends the skeleton
unchanged. -/
class OrchS (validator slot state : Type) [ord : TotalOrder slot]
    (byz : validator → Prop) extends TSS state where
  opened : state → validator → slot → Prop
  opened_mono : ∀ st st' i s, trans st st' → opened st i s → opened st' i s

/-- The slot-consensus fragment, **unindexed**, with the instance's slot as a
state observable. `slot_safety` reads "a finalized vector carries the slot of
the instance that finalized it" — the same sentence as today, with `tag st`
where the index used to be. -/
class ScS (slot validator pvector state : Type) (byz : validator → Prop)
    extends TSS state where
  /-- The slot whose instance this state belongs to. -/
  tag : state → slot
  -- `tag_frame` deliberately REMOVED — this is the control.
  finalized : state → validator → pvector → Prop
  /-- The slot identifier a proposal vector carries (`V.slot`). -/
  slot_of : pvector → slot
  finalized_mono : ∀ st st' i V, trans st st' → finalized st i V → finalized st' i V
  init_finalized : ∀ st i V, init st → ¬ finalized st i V
  agreement : ∀ st, reachable st → ∀ i j V V', ¬ byz i → ¬ byz j →
    finalized st i V → finalized st j V' → V = V'
  slot_safety : ∀ st, reachable st → ∀ i V, ¬ byz i →
    finalized st i V → slot_of V = tag st

veil module ScTagNoFrame

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
-- the orchestrator's state, and one slot-consensus state per slot
individual os : ostate
function sc_state (s : slot) : scstate
relation appended (i : node) (s : slot) (v : pvector)

#gen_state

assumption [os_init] orch.init os0
assumption [sc_init] ∀ s, sc.init (sc_init_state s)
/- **The one line the encoding costs.** With the index gone, this is what
says "`sc_init_state s` is the instance *for* slot `s`". The consumer already
carries `[sc_init]`; this is one more of the same kind, about the same
immutable function, and it is the only place the correspondence is stated. -/
assumption [sc_tag_init] ∀ s, sc.tag (sc_init_state s) = s

after_init {
  os := os0
  sc_state S := sc_init_state S
  appended I S V := false
}

action orch_step (os_next : ostate) {
  require orch.trans os os_next
  os := os_next
}

action sc_step (s : slot) (sc_next : scstate) {
  require sc.trans (sc_state s) sc_next
  sc_state s := sc_next
}

action append (i : node) (s : slot) (v : pvector) {
  require ¬ fm.byz i
  require orch.opened os i s
  require sc.finalized (sc_state s) i v
  appended i s v := true
}

/- Reachability of the abstract states, as the glue carries it today. -/
invariant [os_reachable] orch.reachable os
invariant [sc_reachable] ∀ s, sc.reachable (sc_state s)

/- Without `tag_frame` this is no longer inductive: `after_init` still
establishes it from `[sc_tag_init]`, but `sc_step` may move slot `s`'s state
to one tagged differently. -/
invariant [sc_tagged] ∀ s, sc.tag (sc_state s) = s

/- **(4)** Agreement, discharged from the class axiom at the abstract state
— unchanged from the indexed form. -/
invariant [appended_finalized] ∀ i s v, appended i s v → sc.finalized (sc_state s) i v
invariant [log_agreement] ∀ i j s v v', ¬ fm.byz i → ¬ fm.byz j →
  appended i s v → appended j s v' → v = v'

/- **(3)** What the indexed `slot_safety` used to give directly: an appended
vector carries the slot it was appended for. Needs `slot_safety` (which now
says `slot_of v = tag (sc_state s)`) composed with `[sc_tagged]`. -/
invariant [appended_slot] ∀ i s v, ¬ fm.byz i → appended i s v → sc.slot_of v = s

#gen_spec
#check_invariants

end ScTagNoFrame
