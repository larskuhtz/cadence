import Veil

/-! Spike: can `SlotConsensusSafety` drop its **slot index** and carry the
instance's slot in the state instead, so that all four module contracts
extend one unindexed transition-system skeleton?

`SlotConsensusSafety` is the only family-indexed contract: its `init`,
`step`, `trans`, `reachable` and `finalized` all take a slot, because the
paper runs one Chorus instance per slot. The other three contracts are
unindexed. A shared skeleton must therefore either be indexed (and used at
`Unit` by three of the four — awkward, and it degrades every contract an
auditor reads), or the index has to become something else.

This spike takes the second road: the index becomes an **observable of the
state**, `tag : state → slot`, preserved by every transition
(`tag_frame`). What was `init s st` is then `init st ∧ tag st = s`, and the
consumer — which holds one abstract state per slot — pins the correspondence
once, in an assumption about its *initial* states, and carries
`tag (sc_state s) = s` as an ordinary inductive invariant.

What must hold for the encoding to be usable, and is checked below:

1. the unindexed contract with `tag`/`tag_frame` translates and is
   `instantiate`-able alongside a second contract over a different state
   type (both extending the same skeleton — the fork validates the skeleton
   parent itself in `VeilTest/DestructParentClass.lean`);
2. `[sc_tagged]` — "slot `s`'s state is tagged `s`" — is **inductive** from
   the initial assumption and `tag_frame` alone;
3. the consumer can still get what the indexed `slot_safety` gave it: a
   vector finalized in slot `s`'s instance carries slot `s`
   (`[appended_slot]`, which needs `slot_safety` *and* `[sc_tagged]`);
4. agreement still discharges from the class axioms at the abstract state
   (`[log_agreement]`), as it does today.

Expected: `exit 0`, all `✅`. The cost the spike is measuring is the one
extra assumption in the consumer, `[sc_tag_init]`. -/

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
  /-- Transitions stay inside their instance. -/
  tag_frame : ∀ st st', trans st st' → tag st' = tag st
  finalized : state → validator → pvector → Prop
  /-- The slot identifier a proposal vector carries (`V.slot`). -/
  slot_of : pvector → slot
  finalized_mono : ∀ st st' i V, trans st st' → finalized st i V → finalized st' i V
  init_finalized : ∀ st i V, init st → ¬ finalized st i V
  agreement : ∀ st, reachable st → ∀ i j V V', ¬ byz i → ¬ byz j →
    finalized st i V → finalized st j V' → V = V'
  slot_safety : ∀ st, reachable st → ∀ i V, ¬ byz i →
    finalized st i V → slot_of V = tag st

veil module ScTag

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

/- **(2)** The index, as an inductive invariant. `after_init` gives it from
`[sc_tag_init]`; `sc_step` preserves it by `tag_frame`; no other action
touches `sc_state`. -/
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

end ScTag
