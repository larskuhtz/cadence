import Cadence.Fairness
import Mathlib.Order.MinMax

/-! # Timed — labelled timed runs, and bounded fairness after GST

The timed vocabulary of the bounds work ([Bounds.md](../docs/Bounds.md)
§6.2), one level below the module contracts and one level above
[Fairness.lean](Fairness.lean): a labelled run **with a clock**, what it
means for a step to change the state, and weak fairness with a *deadline*
instead of an *eventually*. Nothing here is Cadence-specific and nothing
here is assumed — these are definitions, and the lemmas about them are the
shapes every bounded-liveness proof uses.

## Why a second run type

[Interfaces.lean](Interfaces.lean)'s `TimedRun` is what the contracts
quantify over: states and a clock sequence, but no labels. Fairness is about
labels, so the load-bearing object here is `TLRun`: an `LRun`, labels
included, together with the same clock sequence (monotone, unbounded) and
the run's `gst`. `TLRun.toTimedRun` forgets the labels, and a contract's
`Admissible` is stated as "the run has a labelling that satisfies ...".

## The two decisions the definitions encode

**Deadlines are on the post-state.** `FiresWithin N D l` says `l` fires at
some `n ≥ N` with `clk (n + 1) ≤ ref N + D`: the step's *effect* is inside
the window, not merely its start. A run whose clock jumps past `ref N + D`
while `l` is pending therefore satisfies no `FiresWithin`, and `BoundedFair`
rejects it — the Zeno-guard of [Bounds.md](../docs/Bounds.md) §3(b), stated as a property
of runs rather than as a guard in the model. `ref N := max (clk N) gst`
makes the same clause bite across GST: an obligation pending when GST
arrives is due `D` after GST.

**Fairness is about steps that change the state.** [Fairness.lean](Fairness.lean)'s
`Enabled` holds when *some* transition exists under the label, a stutter
included; `EnabledMove` asks for a transition to a *different* state — TLA+'s
`⟨A⟩_v`. The reason is recorded in [Bounds.md](../docs/Bounds.md) §6.2.4: assembly actions are
idempotent, so under plain enabledness every one of the (possibly
infinitely many) quorum-indexed labels with the same effect stays enabled
forever and must fire, and no run is fair. Under `EnabledMove` one firing
discharges them all. -/

namespace Cadence

open Veil

/-! ## Veil's total order, from Mathlib's linear order

The contracts quantify over Veil's `TotalOrder`; the arithmetic of a
schedule wants Mathlib's ordered algebra. This is the bridge, reducible so
that `TotalOrder.le a b` *is* `a ≤ b` wherever the instance is this one. -/

/-- A `TotalOrder` from a `LinearOrder`, definitionally `(· ≤ ·)`. -/
@[reducible]
def totalOrderOfLinearOrder (α : Type) [LinearOrder α] : TotalOrder α where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total := le_total

namespace Timed

/-- The same bridge as a **scoped** instance (`open scoped Cadence.Timed`),
so that a `TimedRun` over a linearly ordered clock elaborates without
naming the instance — the structure-instance elaborator synthesises the
constructor's instance argument by search, not from the expected type.
Low priority, so Veil's own instances (`total_order_nat`, …) win where both
apply; either way the order is `(· ≤ ·)`. -/
scoped instance (priority := low) instTotalOrderOfLinearOrder {α : Type} [LinearOrder α] :
    TotalOrder α :=
  totalOrderOfLinearOrder α

end Timed

section

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {time : Type} [LinearOrder time]

/-- A **labelled timed run**: a labelled run of `sys` together with a clock
reading at every index — monotone, unbounded (no Zeno runs) — and the
run's global stabilisation time.

The clock belongs to the run, as in the contracts' `TimedRun`, so a model
whose state has no clock is timed without adding one. Dot-notation reaches the `LRun` API (`r.reachable`,
`r.mono`, `r.steps`, …) through the parent projection. -/
structure TLRun (sys : RelationalTransitionSystem ρ σ lbl) (th : ρ)
    (time : Type) [LinearOrder time] extends LRun sys th where
  /-- The clock reading at each index. -/
  clk : Nat → time
  /-- Time does not run backwards. -/
  clk_mono : ∀ n, clk n ≤ clk (n + 1)
  /-- Time diverges: no Zeno runs. -/
  clk_unbounded : ∀ t, ∃ n, t ≤ clk n
  /-- The global stabilisation time. Nothing is assumed of the run before
  it, and every deadline below is measured from at least it. -/
  gst : time

namespace TLRun

variable (r : TLRun sys th time)

/-- Monotonicity of the clock along the index order. -/
theorem clk_le_of_le {m n : Nat} (h : m ≤ n) : r.clk m ≤ r.clk n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (r.clk_mono n)

/-- **Deadlines order indices.** If the clock is at most `x` at `m` and
above `x` at `n`, then `m` is before `n` — the step that turns a clock
bound into an index bound, used every time a monotone fact established
"by time `x`" has to hold at a later index. -/
theorem lt_of_clk_le_of_lt {m n : Nat} {x : time}
    (hm : r.clk m ≤ x) (hn : x < r.clk n) : m < n := by
  by_contra h
  exact absurd (lt_of_lt_of_le hn (r.clk_le_of_le (Nat.le_of_not_lt h))) (not_lt.mpr hm)

/-- The **reference time** of an index: its clock, or `gst` if that is
later. Every deadline is measured from a reference time, so that an
obligation pending when GST arrives is due at `gst + D`. -/
def ref (N : Nat) : time := max (r.clk N) r.gst

theorem clk_le_ref (N : Nat) : r.clk N ≤ r.ref N := le_max_left _ _
theorem gst_le_ref (N : Nat) : r.gst ≤ r.ref N := le_max_right _ _
theorem ref_le {N : Nat} {x : time} (h₁ : r.clk N ≤ x) (h₂ : r.gst ≤ x) : r.ref N ≤ x :=
  max_le h₁ h₂
theorem ref_eq_of_gst_le {N : Nat} (h : r.gst ≤ r.clk N) : r.ref N = r.clk N :=
  max_eq_left h

/-- `P` holds at some index at or after `N` whose clock reads at most `t`:
the "by time `t`" of the contracts (`TimedRun.byTime`), with the index
lower bound a proof needs to chain milestones. -/
def WithinFrom (N : Nat) (t : time) (P : σ → Prop) : Prop :=
  ∃ n, N ≤ n ∧ r.clk n ≤ t ∧ P (r.at' n)

/-- `l` fires at some index at or after `N`, and the **post-state** of that
step is inside the window `ref N + D`. -/
def FiresWithin [Add time] (N : Nat) (D : time) (l : lbl) : Prop :=
  ∃ n, N ≤ n ∧ r.lbl n = l ∧ r.clk (n + 1) ≤ r.ref N + D

/-- A firing within the window, read through its effect: if every firing of
`l` leaves `P` true, then `P` holds within the window. -/
theorem withinFrom_of_firesWithin [Add time] {N : Nat} {D : time} {l : lbl}
    {P : σ → Prop} (h : r.FiresWithin N D l)
    (heff : ∀ n, r.lbl n = l → P (r.at' (n + 1))) :
    r.WithinFrom N (r.ref N + D) P :=
  let ⟨n, hn, hl, hclk⟩ := h
  ⟨n + 1, Nat.le_succ_of_le hn, hclk, heff n hl⟩

/-- **A monotone fact established by a deadline holds after it.** If `P` is
monotone along the run and holds at some index with clock at most `t`, then
it holds at every index whose clock is past `t`. This is how a milestone
"by time `t`" is consumed at the state where the next one is argued:
`LRun.mono` through `lt_of_clk_le_of_lt`. -/
theorem holds_of_deadline_lt {N : Nat} {t : time} {P : σ → Prop}
    (hstep : ∀ n, P (r.at' n) → P (r.at' (n + 1)))
    (h : r.WithinFrom N t P) {n : Nat} (hn : t < r.clk n) : P (r.at' n) :=
  let ⟨_, _, hclk, hP⟩ := h
  r.toLRun.mono (P := P) hstep hP n (Nat.le_of_lt (r.lt_of_clk_le_of_lt hclk hn))

/-- **A finite family of bounded eventualities is one bounded eventuality.**
If each entry of a finite list satisfies a monotone predicate at some index
at or after `N` with clock at most `t`, then at one index — the latest of
them — they all do, and its clock is still at most `t`. This is
`LRun.eventually_forall` with the deadline carried through: the clock is
monotone, so the maximum index has the clock of one of the witnesses.

`hN` is needed for the empty list, whose single witness is `N` itself. -/
theorem withinFrom_forall {α : Type v} (P : α → σ → Prop)
    (hmono : ∀ a n, P a (r.at' n) → P a (r.at' (n + 1))) (N : Nat) (t : time)
    (hN : r.clk N ≤ t) :
    ∀ (xs : List α), (∀ a ∈ xs, ∃ n, N ≤ n ∧ r.clk n ≤ t ∧ P a (r.at' n)) →
      ∃ n, N ≤ n ∧ r.clk n ≤ t ∧ ∀ a ∈ xs, P a (r.at' n)
  | [], _ => ⟨N, le_rfl, hN, by simp⟩
  | a :: xs, h => by
    obtain ⟨na, hna, hca, hPa⟩ := h a (by simp)
    obtain ⟨nx, hnx, hcx, hPx⟩ :=
      withinFrom_forall P hmono N t hN xs (fun b hb => h b (by simp [hb]))
    refine ⟨max na nx, le_trans hna (le_max_left _ _), ?_, fun b hb => ?_⟩
    · rcases le_total na nx with hle | hle
      · rw [max_eq_right hle]; exact hcx
      · rw [max_eq_left hle]; exact hca
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact r.toLRun.mono (P := P b) (fun m hm => hmono b m hm) hPa _ (le_max_left _ _)
      · exact r.toLRun.mono (P := P b) (fun m hm => hmono b m hm) (hPx b hb') _
          (le_max_right _ _)

end TLRun

/-! ## Move-enabledness, and bounded weak fairness -/

/-- A label is **move-enabled** at a state when the system has a transition
out of that state under it **to a different state** — TLA+'s `⟨A⟩_v`. For a
Veil action this is its `require` clauses satisfiable *and* its update not a
no-op, which for the monotone models means some relation it sets is still
unset. -/
def EnabledMove (sys : RelationalTransitionSystem ρ σ lbl) (th : ρ) (st : σ) (l : lbl) : Prop :=
  ∃ st', sys.tr th st l st' ∧ st' ≠ st

theorem Enabled.of_move {st : σ} {l : lbl} (h : EnabledMove sys th st l) :
    Enabled sys th st l :=
  let ⟨st', htr, _⟩ := h
  ⟨st', htr⟩

/-- **Bounded weak fairness** of `l` with hop bound `D`: from any index `N`,
if `l` is move-enabled at every index at or after `N` whose clock is inside
the window `ref N + D`, then `l` fires with its post-state inside that
window. The timed form of `WeaklyFair`; the paper's "after GST, every step a
correct validator can take is taken within `D`". -/
def BoundedFair [Add time] (r : TLRun sys th time) (D : time) (l : lbl) : Prop :=
  ∀ N, (∀ n, N ≤ n → r.clk n ≤ r.ref N + D → EnabledMove sys th (r.at' n) l) →
    r.FiresWithin N D l

/-- **The form a proof uses.** If a bounded-fair label does not fire within
its window from `N`, it is not move-enabled at some index inside that
window — so a proof that it *stays* move-enabled across the window has
produced a contradiction, and a proof that it can only be disabled by
progress has produced progress by the deadline. The contrapositive of
`BoundedFair`, and the timed twin of `exists_disabled_of_never_fires`. -/
theorem exists_not_moveEnabled_of_not_firesWithin [Add time]
    {r : TLRun sys th time} {D : time} {l : lbl} (hbf : BoundedFair r D l)
    {N : Nat} (hnever : ¬ r.FiresWithin N D l) :
    ∃ n, N ≤ n ∧ r.clk n ≤ r.ref N + D ∧ ¬ EnabledMove sys th (r.at' n) l := by
  by_contra hc
  push Not at hc
  exact hnever (hbf N (fun n hn hclk => hc n hn hclk))

/-- If a label fires at `n`, it was enabled at `n` — and if the step changed
the state, move-enabled. -/
theorem enabledMove_of_fires_of_ne (r : TLRun sys th time) (n : Nat)
    (hne : r.at' (n + 1) ≠ r.at' n) : EnabledMove sys th (r.at' n) (r.lbl n) :=
  ⟨r.at' (n + 1), r.steps n, hne⟩

end

/-! ## Forgetting the labels, and the contracts' least upper bound -/

section Contract

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {time : Type} [LinearOrder time]

open scoped Timed in
/-- A labelled timed run as a contract `TimedRun`: the states and the clock,
the labels forgotten. `hinit` and `hsteps` say that `sys`'s runs are the
contract's; for a fragment whose `init` and `trans` are the model's own
(`Mvba.mvbaSafety`) both are the definitions. The `TotalOrder` on `time` is
the scoped bridge above. -/
def TLRun.toTimedRun (r : TLRun sys th time) (init : σ → Prop) (trans : σ → σ → Prop)
    (hinit : init (r.at' 0)) (hsteps : ∀ n, trans (r.at' n) (r.at' (n + 1))) :
    TimedRun σ time init trans where
  at' := r.at'
  starts := hinit
  steps := hsteps
  clk := r.clk
  clock_mono := r.clk_mono
  clock_unbounded := r.clk_unbounded
  gst := r.gst

open scoped Timed in
/-- **The contracts' least upper bound is `max`.** `TimedRun.byGstBound`
and `MVBATemporal.termination`'s abandonment premise write "`max(t, gst)`"
as "the least `u` above both", since Veil's `TotalOrder` has no `max`. At a
linear order that `u` is `max t g`, and this is the conversion, once. -/
theorem gstLub_iff {t g u : time} :
    (TotalOrder.le t u ∧ TotalOrder.le g u ∧
      ∀ u', TotalOrder.le t u' → TotalOrder.le g u' → TotalOrder.le u u') ↔ u = max t g := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact le_antisymm (h₃ _ (le_max_left t g) (le_max_right t g)) (max_le h₁ h₂)
  · rintro rfl
    exact ⟨le_max_left t g, le_max_right t g, fun _ h₁ h₂ => max_le h₁ h₂⟩

open scoped Timed in
/-- `byGstBound t d P` is "`P` by `max t gst + d`". -/
theorem _root_.TimedRun.byGstBound_iff [Add time] {state : Type} {init : state → Prop}
    {trans : state → state → Prop}
    (r : TimedRun state time init trans) (t d : time) (P : state → Prop) :
    r.byGstBound t d P ↔ r.byTime (max t r.gst + d) P := by
  constructor
  · rintro ⟨u, h₁, h₂, h₃, hb⟩
    rwa [gstLub_iff.mp ⟨h₁, h₂, h₃⟩] at hb
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := gstLub_iff.mpr (rfl : max t r.gst = max t r.gst)
    exact ⟨_, h₁, h₂, h₃, h⟩

end Contract

end Cadence

/-! ## The pinned trust base

Definitions and a handful of lemmas about them; the standard trio and
nothing else, and nothing about any particular protocol. -/

/--
info: 'Cadence.exists_not_moveEnabled_of_not_firesWithin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.exists_not_moveEnabled_of_not_firesWithin

/-- info: 'Cadence.TLRun.withinFrom_forall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cadence.TLRun.withinFrom_forall

/-- info: 'Cadence.gstLub_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cadence.gstLub_iff

/-- info: 'TimedRun.byGstBound_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TimedRun.byGstBound_iff
