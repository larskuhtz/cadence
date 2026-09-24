import Veil

/-! # ViewOrder — what a view counter has to be, beyond a total order

Veil's `TotalOrderWithMinimum` is what the MVBA model's views are typed by,
and it is deliberately weak: a least element, a total order, and `next` as a
*relation* saying "immediate successor". Safety needs no more. Liveness needs
two things it does not say, and this file is where they are named rather than
assumed in passing.

* **Every view has a successor.** `Mvba.sync_view` is guarded on
  `vord.next pv v`, so a view with nothing directly above it is a view no
  validator can leave. This is not a proof convenience: without it the model
  is genuinely stuck, and no assumption about scheduling or the network would
  unstick it. A total order need not have successors — ℚ does not — so it has
  to be said.
* **The views at or below a given one are finitely many.** The liveness proof
  climbs the view order toward a target view and has to know the climb ends;
  that is a counting argument, and counting needs a finite list. This is the
  view dimension's analogue of
  [`ByzQuorum.lean`](./ByzQuorum.lean)'s `ByzNodeSetEnum` for the node
  dimension, and it is introduced for the same reason and on the same terms:
  as a **hypothesis of the theorems that need it**, never as an axiom of the
  model and never as part of any claim's statement.

Both hold of every view counter a real implementation uses, and the `Nat`
witness at the bottom is the machine-checked record that they are jointly
satisfiable.
-/

namespace Cadence

open Veil

/-- **What liveness needs of the view order.** Two fields, discharged for
`Nat` below and hypotheses of `Mvba.termination`. -/
class ViewOrderEnum (view : Type) (vord : TotalOrderWithMinimum view) where
  /-- The immediate successor of a view … -/
  succ : view → view
  /-- … and the proof that it is one. -/
  next_succ : ∀ V : view, vord.next V (succ V)
  /-- The views at or below `W`, as a finite list. -/
  below : view → List view
  /-- `below W` covers them; it may contain more. -/
  mem_below : ∀ (W V : view), vord.le V W → V ∈ below W

/-! ## The witness

`Nat` with its usual order, which is what a view counter is. Kept a `def`
rather than an `instance`: this development never *runs* at a concrete view
type, and a global instance on `Nat` would join instance search everywhere
for no benefit. -/

/-- `Nat` as a view order. -/
@[implicit_reducible]
def natViewOrder : TotalOrderWithMinimum Nat where
  le := (· ≤ ·)
  le_refl := Nat.le_refl
  le_trans := fun _ _ _ => Nat.le_trans
  le_antisymm := fun _ _ => Nat.le_antisymm
  le_total := Nat.le_total
  lt := (· < ·)
  le_lt := by intro x y; omega
  next := fun x y => x + 1 = y
  next_def := by
    intro x y
    constructor
    · rintro rfl
      exact ⟨by omega, fun z hz => by omega⟩
    · rintro ⟨h1, h2⟩
      have h3 := h2 (x + 1) (by omega)
      omega
  zero := 0
  zero_lt := Nat.zero_le

/-- Both fields hold of it. -/
@[implicit_reducible]
def natViewOrderEnum : ViewOrderEnum Nat natViewOrder where
  succ := (· + 1)
  next_succ := fun _ => rfl
  below := fun W => List.range (W + 1)
  mem_below := by
    intro W V h
    have hle : V ≤ W := h
    simp only [List.mem_range]
    omega

end Cadence
