import Cadence.Mvba.Certify
import Cadence.Interfaces

/-! # MvbaCompose — `Mvba ⊨ MVBASafety`, and the join toward `MVBA`

The provider step of the MVBA instantiation (`docs/MvbaPlan.md` §5): the
`Mvba` transition system ([`Mvba.lean`](../Mvba.lean)), packaged as the
state-level MVBA contract of [`Interfaces.lean`](../Interfaces.lean) —
the class Chorus consumes as its `mvba` constraint (plan step 6, landed
2026-09-10; [`System.lean`](../System.lean) plugs this instance in) —
together with the join toward the full `MVBA` class. This is the only file of the `Mvba` family that imports
`Cadence.Interfaces`, on the pattern of
[`Chorus/Compose.lean`](../Chorus/Compose.lean).

**The instance.** `mod:mvba` is one instance per Chorus slot, and the model
is one instance, so the contract is instantiated directly: `init`, `step`,
`trans`, `reachable` are the model's own relations, the state is the
model's state, `Valid` is the theory's immutable `valid` (the entry vector
is the value, `docs/MvbaPlan.md` §1.2), `decided` is the relation of that
name read at the canonical field representation, and `byz` is the
Byzantine predicate of the module's `ByzNodeSet` instance.

| `MVBASafety` field | discharged by |
|---|---|
| `agreement`, `integrity`, `external_validity` | `safety [agreement]`, `[integrity]`, `[external_validity]`, through the named reachability projections of [`Mvba/Certify.lean`](./Certify.lean) |
| `decided_mono`, `init_decided` | the transition bodies of all 24 actions, uniformly (`decided_mono_tr`, `init_not_decided` below): `decided` is only ever set, and `after_init` clears it |
| `step_trans`, `reachable_init`, `reachable_trans` | the reachability constructors |

**What is left unproven is smaller than for the other two.** The model has the module's
two inputs as actions (`propose`, `abandon`) and a per-party message row
for each of the five signed message kinds, so the upper level's inputs,
their observables (`proposed := input`, `abandoned`, `sent` by cases on
`Mvba.Msg`), effects, frames, initial conditions **and Quiescence** are
proven here — Quiescence is the one-step fact `sent_new_tr`: a correct
party's new message row comes from an honest send, and every honest send
requires `∃ E, input i E` and `¬ abandoned i`. What remains is the timed
part alone — `clock`, the admissible-run model, `ℓ` and
`ℓ_MVBA`-Termination — the four fields of `MVBATemporal`, of which this
development has no instance: the smallest gap of the three implementations,
since the inputs, their observables, the frames and one-step Quiescence are
all proven into the fragment. `mvba_of_temporal` joins the two levels.
-/

-- NOTE: no `open Veil` here, as in `Chorus/Compose.lean` — Veil names are
-- used fully qualified, which keeps the file in the generated transition
-- system's instance regime (`Composition.lean`'s header).

namespace Mvba

/-- The signed messages of the protocol, per sender: the contract's
`message` type. The certificate rows (`msg_prepqc`, `msg_commitqc`,
`msg_tc`, `tc_lock`, `tc_nolock`) have no sender — they are assembled
from `2f+1` signatures — so they are not messages a party *sends*. -/
inductive Msg (view value : Type) where
  | preprepare (v : view) (e : value)
  | prepare (v : view) (e : value)
  | commit (v : view) (e : value)
  | timeout_qc (v w : view) (e : value)
  | timeout_noqc (v : view)

/-- A consumer that holds the message sort as an opaque parameter needs it
inhabited (Chorus's `[Inhabited mmsg]`); a view suffices for a witness. -/
instance {view value : Type} [Inhabited view] : Inhabited (Msg view value) :=
  ⟨.timeout_noqc default⟩

open Classical

section Instance

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]

/- The abstract field representation of the Mvba state at the canonical
`Classical` instances (cf. `Composition.lean`'s `afr%`). -/
local macro "afr%" f:ident : term =>
  `(@Mvba.instAbstractFieldRepresentation node nodeset value view
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    $f)

/-- `i` has decided `e`: the contract's `decide(v)` output. -/
noncomputable abbrev Decided
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) (i : node) (e : value) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.decided) st.decided i e = true

/-- `i` has proposed `e` (`input`): the record of the `propose(v)` input. -/
noncomputable abbrev Proposed
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) (i : node) (e : value) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.input) st.input i e = true

/-- `i` has abandoned: the record of the `abandon()` input. -/
noncomputable abbrev Abandoned
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) (i : node) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.abandoned) st.abandoned i = true

/-- `p` has sent `m`: the message's network row with `p` as its sender. -/
noncomputable def Sent
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) (p : node) :
    Msg view value → Prop
  | .preprepare v e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_preprepare) st.msg_preprepare p v e = true
  | .prepare v e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_prepare) st.msg_prepare p v e = true
  | .commit v e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_commit) st.msg_commit p v e = true
  | .timeout_qc v w e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_timeout_qc) st.msg_timeout_qc p v w e = true
  | .timeout_noqc v =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_timeout_noqc) st.msg_timeout_noqc p v = true

/-- The labels of the module's two inputs, `propose(v)` and `abandon()`;
every other label is an internal step of the protocol. -/
def Label.isInput : Mvba.Label node nodeset value view → Prop
  | .propose _ _ => True
  | .abandon _ => True
  | _ => False

variable (th : Mvba.Theory node nodeset value view)

/-! ### Step-level facts, uniformly over all 24 actions

Each is proven by exposing every action's pre-computed transition body
(`<action>.ext.derived_eq`, then the `reducible` `<action>.ext.tr` — Veil's
`trSimp` set is exactly those two per action, so one `simp only` covers all
of them),
substituting the post-state and evaluating the field-representation
`get`/`set` pair at the canonical representation
(`docs/CompositionContracts.md` §4). -/

/-- Expose one action's transition body in `h`. -/
local macro "mvba_tr" h:ident : tactic =>
  `(tactic| (simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation, everywhere. -/
local macro "mvba_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [Decided, Proposed, Abandoned, Sent,
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id] at *)

section StepFacts
variable {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}
  {l : Mvba.Label node nodeset value view}

set_option maxHeartbeats 4000000 in
/-- `decided` stands across every action. -/
theorem decided_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (i : node) (e : value) (h : Decided st i e) : Decided st' i e := by
  cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 4000000 in
/-- `input` stands across every action. -/
theorem proposed_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (i : node) (e : value) (h : Proposed st i e) : Proposed st' i e := by
  cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 4000000 in
/-- `abandoned` stands across every action. -/
theorem abandoned_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (i : node) (h : Abandoned st i) : Abandoned st' i := by
  cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 8000000 in
/-- Every message row stands across every action (the network is monotone). -/
theorem sent_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (p : node) (m : Msg view value) (h : Sent st p m) : Sent st' p m := by
  cases m <;> cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 4000000 in
/-- Internal steps leave `input` untouched: only `propose` sets it. -/
theorem proposed_frame_internal (hl : ¬ Label.isInput l)
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (i : node) (e : value) : Proposed st' i e ↔ Proposed st i e := by
  cases l <;> simp [Label.isInput] at hl <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp

set_option maxHeartbeats 4000000 in
/-- Internal steps leave `abandoned` untouched: only `abandon` sets it. -/
theorem abandoned_frame_internal (hl : ¬ Label.isInput l)
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (i : node) : Abandoned st' i ↔ Abandoned st i := by
  cases l <;> simp [Label.isInput] at hl <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp

/-- `propose(e)` at `i` records `input i e`. -/
theorem propose_effect_tr {i : node} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st (.propose i e) st') :
    Proposed st' i e := by
  mvba_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); mvba_field_simp

/-- `abandon()` at `i` records `abandoned i`. -/
theorem abandon_effect_tr {i : node}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st (.abandon i) st') :
    Abandoned st' i := by
  mvba_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); mvba_field_simp

set_option maxHeartbeats 8000000 in
/-- **Quiescence, one step.** A correct party's *new* message row comes from
one of its honest sends, each of which requires the party to have proposed
(`∃ E, input i E`) and not to have abandoned; a Byzantine signer's row is
its own. So the sender has proposed at the post-state and had not
abandoned at the pre-state. -/
theorem sent_new_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (p : node) (m : Msg view value) (hp : ¬ nset.is_byz p = true)
    (hnew : Sent st' p m) (hold : ¬ Sent st p m) :
    (∃ v, Proposed st' p v) ∧ ¬ Abandoned st p := by
  cases m <;> cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> simp_all <;> exact ⟨_, by assumption⟩

/-- Initially nobody has decided. -/
theorem init_not_decided
    (hinit : (Mvba.relationalTransitionSystem node nodeset value view).init th st)
    (i : node) (e : value) : ¬ Decided st i e := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init] at hinit
  simp only [Mvba.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); mvba_field_simp

/-- Initially nobody has proposed. -/
theorem init_not_proposed
    (hinit : (Mvba.relationalTransitionSystem node nodeset value view).init th st)
    (i : node) (e : value) : ¬ Proposed st i e := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init] at hinit
  simp only [Mvba.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); mvba_field_simp

/-- Initially nobody has abandoned. -/
theorem init_not_abandoned
    (hinit : (Mvba.relationalTransitionSystem node nodeset value view).init th st)
    (i : node) : ¬ Abandoned st i := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init] at hinit
  simp only [Mvba.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); mvba_field_simp

end StepFacts

set_option maxHeartbeats 1000000 in
/-- **`Mvba ⊨ MVBASafety`** — for every Mvba theory `th` (the validity
predicate and the leader schedule), the Mvba transition system is an
instance of the state-level MVBA contract, with `byz` the Byzantine
predicate of the module's `ByzNodeSet` instance. `init` is the model's
initial-state relation together with its theory assumption
(`leader_functional`), `step` its transitions other than the two inputs,
`trans` any transition, `reachable` its reachable set; `Valid` is the
theory's `valid`, `decided` the relation of that name. -/
@[implicit_reducible]
noncomputable def mvbaSafety :
    MVBASafety node value (Msg view value) (Mvba.State (Mvba.FieldAbstractType node nodeset value view))
      (fun i => nset.is_byz i = true) where
  Valid e := th.valid e = true
  init st := (Mvba.relationalTransitionSystem node nodeset value view).assumptions th ∧
    (Mvba.relationalTransitionSystem node nodeset value view).init th st
  step st st' := ∃ l, ¬ Label.isInput l ∧
    (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st'
  trans st st' := (Mvba.relationalTransitionSystem node nodeset value view).next th st st'
  reachable st := (Mvba.relationalTransitionSystem node nodeset value view).reachable th st
  step_trans _ _ h := ⟨h.choose, h.choose_spec.2⟩
  reachable_init st h := Veil.RelationalTransitionSystem.reachable.init st h.1 h.2
  reachable_trans st st' hr hn := Veil.RelationalTransitionSystem.reachable.step st st' hr hn
  -- The two inputs are the model's own actions, so the interface, its
  -- observables, their frames and one-step Quiescence are all first-order
  -- facts this model proves — which is why they sit in the fragment rather
  -- than at the temporal level (`Interfaces.lean`, the placement rule).
  propose st p v st' := (Mvba.relationalTransitionSystem node nodeset value view).tr th st (.propose p v) st'
  abandon st p st' := (Mvba.relationalTransitionSystem node nodeset value view).tr th st (.abandon p) st'
  propose_trans _ _ _ _ h := ⟨_, h⟩
  abandon_trans _ _ _ h := ⟨_, h⟩
  decided := Decided
  proposed := Proposed
  abandoned := Abandoned
  sent := Sent
  decided_mono _ _ i e hn h := decided_mono_tr th hn.choose_spec i e h
  proposed_mono _ _ p v hn h := proposed_mono_tr th hn.choose_spec p v h
  abandoned_mono _ _ p hn h := abandoned_mono_tr th hn.choose_spec p h
  sent_mono _ _ p m hn h := sent_mono_tr th hn.choose_spec p m h
  propose_effect _ _ _ _ h := propose_effect_tr th h
  abandon_effect _ _ _ h := abandon_effect_tr th h
  proposed_step_frame _ _ p v h _ := proposed_frame_internal th h.choose_spec.1 h.choose_spec.2 p v
  abandoned_step_frame _ _ p h _ := abandoned_frame_internal th h.choose_spec.1 h.choose_spec.2 p
  init_decided _ i e h := init_not_decided th h.2 i e
  init_proposed _ p v h := init_not_proposed th h.2 p v
  init_abandoned _ p h := init_not_abandoned th h.2 p
  agreement _ hr i j e e' hi hj hdi hdj := reachable_agreement hr i j e e' hi hj hdi hdj
  integrity _ hr i e e' hi hdi hdi' := reachable_integrity hr i e e' hi hdi hdi'
  external_validity _ hr i e hi hd := reachable_external_validity hr i e hi hd
  -- **Quiescence**, in the one-step form the contract now states: a new
  -- message row of a correct party at a transition comes with the input and
  -- with the party not having abandoned. `sent_new_tr` is exactly that, over
  -- all 5 message kinds × 24 actions.
  quiescence _ _ p m hn hp hnew hold := sent_new_tr th hn.choose_spec p m hp hnew hold

/-! ### What the full `MVBA` still owes

With the inputs, their observables, the frames and one-step Quiescence all
proven above, what stands between the fragment and the full `MVBA` is an
instance of **`MVBATemporal … (S := mvbaSafety th)`** — and there is none.
Its fields are exactly four: the clock, the admissible-run model, `ℓ` and
`ℓ_MVBA`-Termination (the supplement's `thm:termination`, `O(fΔ)`), which
the untimed model cannot state (`docs/MvbaPlan.md` §3).

This is the smallest gap of the three implementations, and it is stated
without restating anything: every field of `MVBATemporal` is already over
`(mvbaSafety th)`'s own `init`, `trans` and observables. -/

/-- Given a temporal level **at this fragment**, `Mvba` is a full `MVBA`.
Nothing is restated to join them, and the fragment comes back out by
`rfl`. -/
@[implicit_reducible]
noncomputable def mvba_of_temporal {time : Type} [TotalOrder time] [Add time]
    (h : MVBATemporal node value (Msg view value) (Mvba.State (Mvba.FieldAbstractType node nodeset value view)) time
      (fun i => nset.is_byz i = true) (S := mvbaSafety th)) :
    MVBA node value (Msg view value) (Mvba.State (Mvba.FieldAbstractType node nodeset value view)) time
      (fun i => nset.is_byz i = true) :=
  { mvbaSafety th, h with }

/-- The fragment the composition consumes is exactly the one that was
proven. -/
theorem mvba_of_temporal_toSafety {time : Type} [TotalOrder time] [Add time]
    (h : MVBATemporal node value (Msg view value) (Mvba.State (Mvba.FieldAbstractType node nodeset value view)) time
      (fun i => nset.is_byz i = true) (S := mvbaSafety th)) :
    (mvba_of_temporal th h).toMVBASafety = mvbaSafety th := rfl

end Instance
end Mvba

/-! ## The pinned trust base

The instance rests on the standard Lean trio and nothing else — no
`sorryAx`, no trusted-SMT step. The composition consumes the proof-file
family (`Mvba/Proofs/`, via `Mvba/Certify.lean`'s `#gen_composition`):
every VC statement re-created from the persistent registry, solved as a
fresh kernel-checked reconstruction, assembled per action into a
preservation lemma, and composed. The temporal-conditioned full instance
is pinned too: what is unproven enters as a *hypothesis* — the missing
`MVBATemporal` instance — never as an axiom. -/

/--
info: 'Mvba.mvbaSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaSafety

/--
info: 'Mvba.mvba_of_temporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvba_of_temporal
