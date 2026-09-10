import Veil
import Cadence.Interfaces

/-! Spike: can the *temporal* level of a module contract be a class over the
**safety instance**, so that the full contract is the two levels joined and
nothing is restated?

The shape Part B wants (`docs/CompositionContracts.md` §2, the interface
redesign):

* `XSafety state` — the first-order fragment a Veil module `instantiate`s;
* `XTemporal state [S : XSafety state]` — every temporal obligation, stated
  over `S.init` / `S.trans`, so it cannot drift from the fragment;
* `X` — the paper's module in one name, carrying both.

The open question is only about the third: Lean 4's `extends` with a
**dependent parent**, whose instance argument is the first parent. If that is
rejected, the fallback is a plain field (`toTemporal : XTemporal … (S :=
toXSafety)`), which gives the same two projections. Either way nothing here
reaches SMT: no Veil module instantiates `X`.

Expected: `exit 0`, no `sorry`, and the `#check`s below print the two
projections. -/

set_option linter.unusedVariables false

namespace Spike06

/-! ## The safety fragment — first-order, as a Veil module would take it -/

class OrchS (validator slot state : Type) [ord : TotalOrder slot]
    (byz : validator → Prop) where
  init : state → Prop
  step : state → state → Prop
  trans : state → state → Prop
  reachable : state → Prop
  step_trans : ∀ st st', step st st' → trans st st'
  reachable_init : ∀ st, init st → reachable st
  reachable_trans : ∀ st st', reachable st → trans st st' → reachable st'
  opened : state → validator → slot → Prop
  opened_mono : ∀ st st' i s, trans st st' → opened st i s → opened st' i s
  init_opened : ∀ st i s, init st → ¬ opened st i s

/-! ## The temporal level, over the safety **instance**

Every field mentions `S.init` / `S.trans` / `S.opened`, so a temporal
obligation is stated at exactly the transition system the fragment fixes.
This is what the residual structures used to do, by restating those
relations at the implementation's own types. -/

class OrchT (validator slot state : Type) [ord : TotalOrder slot]
    (byz : validator → Prop) [S : OrchS validator slot state byz] where
  /-- Totality, over a run of the *safety instance's* transition relation. -/
  totality : ∀ run : Nat → state, S.init (run 0) → (∀ n, S.trans (run n) (run (n + 1))) →
    ∀ i j s, ¬ byz i → ¬ byz j →
      (∃ n, S.opened (run n) i s) → ∃ m, S.opened (run m) j s
  /-- A bound carried as data, as `B`-Boundedness does. -/
  bound : Nat
  boundedness : ∀ st, S.reachable st → ∀ i s, ¬ byz i → S.opened st i s →
    ¬ ∃ f : Fin bound → slot, Function.Injective f ∧ ∀ k, S.opened st i (f k)

/-! ## Form A — the dependent parent

`OrchT`'s instance argument must resolve to the first parent. This is the
form the redesign wants; if Lean takes it, `X` reads as the paper's module in
one name and both levels are ordinary projections. -/

class Orch (validator slot state : Type) [ord : TotalOrder slot]
    (byz : validator → Prop) extends
    OrchS validator slot state byz,
    OrchT validator slot state byz

-- The two projections the composition needs.
#check @Orch.toOrchS
#check @Orch.toOrchT

/- **The load-bearing check.** `OrchT`'s instance argument must have resolved
to *this* class's own `OrchS` parent — if `extends` had instead left it as a
fresh instance-implicit binder, the two levels could be about different
transition systems and the whole point would be lost. Printed explicitly, the
`S` argument of `Orch.toOrchT`'s result must be `Orch.toOrchS self`. -/
set_option pp.explicit true in
#check @Orch.toOrchT

/-! ## Form B — the fallback, a plain field

Kept in the spike whether or not Form A elaborates, because it is the shape
to fall back to and it must be known to work. -/

class Orch' (validator slot state : Type) [ord : TotalOrder slot]
    (byz : validator → Prop) extends OrchS validator slot state byz where
  toTemporal : OrchT validator slot state byz (S := toOrchS)

#check @Orch'.toOrchS
#check @Orch'.toTemporal

/-! ## The point of the exercise: a provider with a proven fragment and an
assumed temporal level, joined with **nothing restated**.

`impl` stands for an implementation (`Conductor.orchestratorSafety`): the
fragment is proven. Given a temporal instance *at that fragment*, the full
contract is `mk` applied to the two — which is what replaces
`orchestrator_of_residual` and its restated `OrchestratorResidual` fields
(retired 2026-09-09; `docs/History.md`). -/

section Provider
variable {validator slot state : Type} [TotalOrder slot] {byz : validator → Prop}

/-- A proven safety fragment (any one; here the trivial witness). -/
@[implicit_reducible]
def impl : OrchS validator slot state byz where
  init _ := True
  step _ _ := True
  trans _ _ := True
  reachable _ := True
  step_trans _ _ _ := trivial
  reachable_init _ _ := trivial
  reachable_trans _ _ _ _ := trivial
  opened _ _ _ := False
  opened_mono _ _ _ _ _ h := h
  init_opened _ _ _ _ := id

/-- **Form A joins the two levels with no restatement.** The gap an
implementation still owes is literally "no `OrchT` instance at this
`OrchS` instance" — a missing instance, not a structure whose fields repeat
the class's. -/
@[implicit_reducible]
def orch_of_temporal (h : OrchT validator slot state byz (S := impl)) :
    Orch validator slot state byz :=
  { impl, h with }

/-- The same for Form B. -/
@[implicit_reducible]
def orch'_of_temporal (h : OrchT validator slot state byz (S := impl)) :
    Orch' validator slot state byz :=
  { toOrchS := impl, toTemporal := h }

/-- And the fragment comes back out unchanged — the composition consumes
exactly what the implementation proved. -/
example (h : OrchT validator slot state byz (S := impl)) :
    (orch_of_temporal h).toOrchS = impl := rfl

example (h : OrchT validator slot state byz (S := impl)) :
    (orch'_of_temporal h).toOrchS = impl := rfl

end Provider

/-! ## Negative control: the temporal level is *not* silently droppable

If `OrchT`'s fields did not mention `S`, a temporal instance at one safety
instance would satisfy the class at another. They do mention `S`, so this
`example` only type-checks at the matching instance — which is the property
that makes "no instance" an honest statement of the gap. -/

section Control
variable {validator slot state : Type} [TotalOrder slot] {byz : validator → Prop}

example (h : OrchT validator slot state byz (S := impl)) :
    OrchT validator slot state byz (S := impl) := h

end Control

end Spike06
