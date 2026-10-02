/-
The monitor's stand-in for Chorus's MVBA constraint.

Chorus consumes the MVBA as the class constraint
`instantiate mvba : MVBASafety node mvalue mentries mmsg mstate …` over four
abstract sorts. A concrete monitor instance has to fix them,
and no implementation event corresponds to any of them: the MVBA's internal
state and messages are not observable at the Chorus trace boundary, and the
implementation's decision handler is not emitted yet ([Monitor.md](../../docs/Monitor.md) §8).
So the monitor instantiates

* `mstate := Unit`, `mmsg := Unit` — the oracle step `mvba_step` is a silent
  step that changes nothing;
* `mentries := ME` below — the entry vector at `n = 4`, two roots, as a
  finite record, with the two projections Chorus's `Theory` needs
  (`mvalPos`/`mvalNeg`);
* `mvalue := MV` below — a meta-block representation: an entry vector and,
  per entry, whether a positive entry is certified by a `FallbackQC`
  (`mvalFb`);
* the class instance `silentMvba` — an MVBA that never decides. Every field
  is trivially inhabited (`decided := False` makes agreement, integrity and
  external validity vacuous), so the instance is a *consistent* model of the
  class, and every guard that reads it is decidable (the instances at the
  end). Its consequence for coverage is documented in [Monitor.md](../../docs/Monitor.md) §8:
  the decision handlers, `mvba_terminate` and the handoff
  `accept_mvba_commitqc` can never fire under it, so the
  MVBA leg of the fallback path is outside what the current monitor can
  accept. The fixtures under `traces/` are fast-path only and never reach it.

Shared by the hand-written monitor and the `#gen_monitor`-generated one.
Not part of any theorem's trust base.
-/
import Cadence.Interfaces
open Lean (ToJson FromJson Json)

namespace ChorusMonitor

/-- The entry vector `node → Option merkle_root` at the monitor's instance
(`n = 4`, roots `Fin 2`), as a record. Entry `k` is proposer `k`'s entry:
`some m` a positive entry on root `m`, `none` a negative one. -/
structure ME where
  e0 : Option (Fin 2)
  e1 : Option (Fin 2)
  e2 : Option (Fin 2)
  e3 : Option (Fin 2)
deriving DecidableEq, Repr, Hashable, Inhabited

/-- The vector as a function on nodes. -/
def ME.entry (v : ME) : Fin 4 → Option (Fin 2)
  | 0 => v.e0
  | 1 => v.e1
  | 2 => v.e2
  | 3 => v.e3

/-- A meta-block representation at the monitor's instance: the entry vector,
and per entry whether a positive entry is certified by a `FallbackQC`
(otherwise by a `FastQC`; ignored for a negative entry). A record so the
action `Label` keeps its derived `DecidableEq`/`Repr`/`ToJson`/`Hashable`. -/
structure MV where
  entries : ME
  fb0 : Bool
  fb1 : Bool
  fb2 : Bool
  fb3 : Bool
deriving DecidableEq, Repr, Hashable, Inhabited

/-- The `FallbackQC` flags as a function on nodes. -/
def MV.fb (v : MV) : Fin 4 → Bool
  | 0 => v.fb0
  | 1 => v.fb1
  | 2 => v.fb2
  | 3 => v.fb3

/-- One entry on the wire: `null` (negative), a root index (positive, held by
a `FastQC`), or `{"fallback": k}` (positive on root `k`, held by a
`FallbackQC`). -/
def entryJson (e : Option (Fin 2)) (fb : Bool) : Json :=
  match e, fb with
  | none, _ => .null
  | some m, false => ToJson.toJson m
  | some m, true => Json.mkObj [("fallback", ToJson.toJson m)]

instance : ToJson MV where
  toJson v := Json.arr #[entryJson v.entries.e0 v.fb0, entryJson v.entries.e1 v.fb1,
    entryJson v.entries.e2 v.fb2, entryJson v.entries.e3 v.fb3]

/-- `mval_pos e j m` at the instance: `e j = some m`. -/
def mvalPos (v : ME) (j : Fin 4) (m : Fin 2) : Bool := v.entry j == some m
/-- `mval_neg e j` at the instance: `e j = none`. -/
def mvalNeg (v : ME) (j : Fin 4) : Bool := v.entry j == none
/-- `mval_fb v j` at the instance: the representation's `FallbackQC` flag. -/
def mvalFb (v : MV) (j : Fin 4) : Bool := v.fb j

/-- Decode a meta-block representation from a JSON array of four entries,
each `null`, a root index, or `{"fallback": k}` (`entryJson`). -/
def decodeMV (j : Json) : Except String MV := do
  let arr ← j.getArr?
  unless arr.size == 4 do throw s!"mvalue needs 4 entries (one per node), got {arr.size}"
  let root (k : Nat) : Except String (Fin 2) :=
    if h : k < 2 then pure ⟨k, h⟩ else throw s!"root index {k} out of range (≥ 2)"
  let ent (e : Json) : Except String (Option (Fin 2) × Bool) :=
    match e with
    | .null => pure (none, false)
    | .obj _ => do
      let k ← (← e.getObjVal? "fallback").getNat?
      pure (some (← root k), true)
    | _ => do
      let k ← e.getNat?
      pure (some (← root k), false)
  let (a0, f0) ← ent arr[0]!
  let (a1, f1) ← ent arr[1]!
  let (a2, f2) ← ent arr[2]!
  let (a3, f3) ← ent arr[3]!
  pure ⟨⟨a0, a1, a2, a3⟩, f0, f1, f2, f3⟩

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
@[reducible] def silentMvba {α pset : Type} {B : ByzNodeSet α pset} (byz : α → Prop) :
    MVBASafety α MV ME Unit Unit pset B byz where
  init _ := True
  step _ _ := True
  trans _ _ := True
  reachable _ := True
  step_trans _ _ _ := trivial
  reachable_init _ _ := trivial
  reachable_trans _ _ _ _ := trivial
  Valid _ := True
  entries v := v.entries
  propose _ _ _ _ := False
  abandon _ _ _ := False
  propose_trans _ _ _ _ h := h.elim
  -- Vacuous: this stub has no `propose` transition at all.
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
  availReady _ _ _ := False
  -- The decision handoff: nothing is ever certified, so nothing is accepted.
  certifies _ _ _ := False
  decided_certified _ _ _ _ _ h := h.elim
  accept _ _ _ _ := False
  accept_trans _ _ _ _ h := h.elim
  accept_effect _ _ _ _ _ h _ := h.elim
  accept_enabled _ _ _ _ _ _ h := h.elim
  certified_unique _ _ _ _ _ _ h _ := h.elim
  certified_decided _ _ _ _ _ _ h _ _ := h.elim
  certified_valid _ _ _ _ h := h.elim
  certified_available _ _ _ _ h := h.elim

/-! The guards of the MVBA actions, decidable at the silent instance. The
extracted executor asks for these as instance arguments (Veil cannot decide
a class-valued proposition generically). -/

instance silentMvba.decDecided {α pset : Type} {B : ByzNodeSet α pset} (byz : α → Prop)
    (st : Unit) (i : α) (v : MV) :
    Decidable ((silentMvba (B := B) byz).decided st i v) := isFalse id
instance silentMvba.decStep {α pset : Type} {B : ByzNodeSet α pset} (byz : α → Prop)
    (st st' : Unit) :
    Decidable ((silentMvba (B := B) byz).step st st') := isTrue trivial
instance silentMvba.decPropose {α pset : Type} {B : ByzNodeSet α pset} (byz : α → Prop)
    (st : Unit) (i : α) (v : MV) (st' : Unit) :
    Decidable ((silentMvba (B := B) byz).propose st i v st') := isFalse id
/-- The stub has no `abandon` transition (its state `Unit` cannot record
`abandoned`), so Chorus's `abandon` input, which forwards to it, is never
enabled under this monitor ([Monitor.md](../../docs/Monitor.md) §8). -/
instance silentMvba.decAbandon {α pset : Type} {B : ByzNodeSet α pset} (byz : α → Prop)
    (st : Unit) (i : α) (st' : Unit) :
    Decidable ((silentMvba (B := B) byz).abandon st i st') := isFalse id
/-- Nothing is certified under the stub, so the handoff input is never
enabled either. -/
instance silentMvba.decAccept {α pset : Type} {B : ByzNodeSet α pset} (byz : α → Prop)
    (st : Unit) (i : α) (c : Unit) (st' : Unit) :
    Decidable ((silentMvba (B := B) byz).accept st i c st') := isFalse id

end ChorusMonitor
