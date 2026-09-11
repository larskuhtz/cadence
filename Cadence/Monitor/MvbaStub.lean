/-
The monitor's stand-in for Chorus's MVBA constraint.

Chorus consumes the MVBA as the class constraint
`instantiate mvba : MVBASafety node mvalue mmsg mstate …` over three abstract
sorts. A concrete monitor instance has to fix them,
and no implementation event corresponds to any of them: the MVBA's internal
state and messages are not observable at the Chorus trace boundary, and the
implementation's decision handler is not emitted yet (`docs/Monitor.md` §8).
So the monitor instantiates

* `mstate := Unit`, `mmsg := Unit` — the oracle step `mvba_step` is a silent
  step that changes nothing;
* `mvalue := MV` below — the entry vector at `n = 4`, two roots, as a finite
  record, with the two projections Chorus's `Theory` needs
  (`mvalPos`/`mvalNeg`);
* the class instance `silentMvba` — an MVBA that never decides. Every field
  is trivially inhabited (`decided := False` makes agreement, integrity and
  external validity vacuous), so the instance is a *consistent* model of the
  class, and every guard that reads it is decidable (the instances at the
  end). Its consequence for coverage is documented in `docs/Monitor.md` §8:
  the decision handlers and `mvba_terminate` can never fire under it, so the
  MVBA leg of the fallback path is outside what the current monitor can
  accept. The fixtures under `traces/` are fast-path only and never reach it.

Shared by the hand-written monitor and the `#gen_monitor`-generated one.
Not part of any theorem's trust base.
-/
import Cadence.Interfaces
open Lean (ToJson FromJson Json)

namespace ChorusMonitor

/-- The entry vector `node → Option merkle_root` at the monitor's instance
(`n = 4`, roots `Fin 2`), as a record so the action `Label` keeps its derived
`DecidableEq`/`Repr`/`ToJson`/`Hashable`. Entry `k` is proposer `k`'s entry:
`some m` a positive entry on root `m`, `none` a negative one. -/
structure MV where
  e0 : Option (Fin 2)
  e1 : Option (Fin 2)
  e2 : Option (Fin 2)
  e3 : Option (Fin 2)
deriving DecidableEq, Repr, Hashable, Inhabited

instance : ToJson MV where
  toJson v := Json.arr #[ToJson.toJson v.e0, ToJson.toJson v.e1, ToJson.toJson v.e2, ToJson.toJson v.e3]

/-- The vector as a function on nodes. -/
def MV.entry (v : MV) : Fin 4 → Option (Fin 2)
  | 0 => v.e0
  | 1 => v.e1
  | 2 => v.e2
  | 3 => v.e3

/-- `mval_pos v j m` at the instance: `v j = some m`. -/
def mvalPos (v : MV) (j : Fin 4) (m : Fin 2) : Bool := v.entry j == some m
/-- `mval_neg v j` at the instance: `v j = none`. -/
def mvalNeg (v : MV) (j : Fin 4) : Bool := v.entry j == none

/-- Decode an entry vector from a JSON array of four entries, each `null`
(negative) or a root index (positive). -/
def decodeMV (j : Json) : Except String MV := do
  let arr ← j.getArr?
  unless arr.size == 4 do throw s!"mvalue needs 4 entries (one per node), got {arr.size}"
  let ent (e : Json) : Except String (Option (Fin 2)) :=
    match e with
    | .null => pure none
    | _ => do
      let k ← e.getNat?
      if h : k < 2 then pure (some ⟨k, h⟩) else throw s!"root index {k} out of range (≥ 2)"
  pure ⟨← ent arr[0]!, ← ent arr[1]!, ← ent arr[2]!, ← ent arr[3]!⟩

/-- Decode the (unobservable) abstract MVBA state: `null` only. -/
def decodeMState (j : Json) : Except String Unit :=
  match j with
  | .null => pure ()
  | _ => throw "mstate is not observable; write null"

/-- An MVBA that never decides, at state `Unit` and message `Unit`: a
consistent model of `MVBASafety` under which every guard reading it is
decidable. Generic in the party type (nothing here depends on it, and the
monitor spells its node sort `Fin (3 * 1 + 1)`); reducible so that instance
synthesis sees through its fields. -/
@[reducible] def silentMvba {α : Type} (byz : α → Prop) : MVBASafety α MV Unit Unit byz where
  init _ := True
  step _ _ := True
  trans _ _ := True
  reachable _ := True
  step_trans _ _ _ := trivial
  reachable_init _ _ := trivial
  reachable_trans _ _ _ _ := trivial
  Valid _ := True
  propose _ _ _ _ := False
  abandon _ _ _ := False
  propose_trans _ _ _ _ h := h.elim
  abandon_trans _ _ _ h := h.elim
  decided _ _ _ := False
  proposed _ _ _ := False
  abandoned _ _ := False
  sent _ _ _ := False
  decided_mono _ _ _ _ _ h := h
  proposed_mono _ _ _ _ _ h := h
  abandoned_mono _ _ _ _ h := h
  sent_mono _ _ _ _ _ h := h
  propose_effect _ _ _ _ h := h.elim
  abandon_effect _ _ _ h := h.elim
  proposed_step_frame _ _ _ _ _ _ := Iff.rfl
  abandoned_step_frame _ _ _ _ _ := Iff.rfl
  init_decided _ _ _ _ h := h
  init_proposed _ _ _ _ h := h
  init_abandoned _ _ _ h := h
  quiescence _ _ _ _ _ _ h _ := h.elim
  agreement _ _ _ _ _ _ _ _ h _ := h.elim
  integrity _ _ _ _ _ _ h _ := h.elim
  external_validity _ _ _ _ _ _ := trivial

/-! The guards of the MVBA actions, decidable at the silent instance. The
extracted executor asks for these as instance arguments (Veil cannot decide
a class-valued proposition generically). -/

instance silentMvba.decDecided {α : Type} (byz : α → Prop) (st : Unit) (i : α) (v : MV) :
    Decidable ((silentMvba byz).decided st i v) := isFalse id
instance silentMvba.decStep {α : Type} (byz : α → Prop) (st st' : Unit) :
    Decidable ((silentMvba byz).step st st') := isTrue trivial
instance silentMvba.decPropose {α : Type} (byz : α → Prop) (st : Unit) (i : α) (v : MV) (st' : Unit) :
    Decidable ((silentMvba byz).propose st i v st') := isFalse id

end ChorusMonitor
