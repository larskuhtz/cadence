import Cadence.Fairness
import Mathlib.Order.MinMax

/-! # Timed — labelled timed runs, and bounded fairness after GST

The timed vocabulary of the bounds work ([`docs/Bounds.md`](../docs/Bounds.md)
§6.2), one level below the module contracts and one level above
[`Fairness.lean`](./Fairness.lean): a labelled run **with a clock**, what it
means for a step to change the state, and weak fairness with a *deadline*
instead of an *eventually*. Nothing here is Cadence-specific and nothing
here is assumed — these are definitions, and the two lemmas about them are
the two shapes every bounded-liveness proof uses.

## Why a second run type, and why the clock is not in the state

[`Interfaces.lean`](./Interfaces.lean)'s `TimedRun` reads the clock **off
the state** (`clock : state → time`), which is right for the Conductor,
whose `now` is a state field. The untimed models have no such field, and
a model change for the sake of a contract's signature is the wrong trade
(`Bounds.md` §6.2.1). So the load-bearing object is `TLRun`: an `LRun` —
labels included, since fairness is about labels — together with a clock
*sequence*, monotone and unbounded, and the run's `gst`. The bridge to the
contract vocabulary is `MVBASafety.timed`, the lift of a safety fragment to
the product state `state × time`, and `TLRun.toTimedRun`, which pairs each
state with its clock. The fragment is untouched by the lift: every field is
the original's on the first component.

## The two decisions the definitions encode

**Deadlines are on the post-state.** `FiresWithin N D l` says `l` fires at
some `n ≥ N` with `clk (n + 1) ≤ ref N + D`: the step's *effect* is inside
the window, not merely its start. A run whose clock jumps past `ref N + D`
while `l` is pending therefore satisfies no `FiresWithin`, and `BoundedFair`
rejects it — the Zeno-guard of `docs/Bounds.md` §3(b), stated as a property
of runs rather than as a guard in the model. `ref N := max (clk N) gst`
makes the same clause bite across GST: an obligation pending when GST
arrives is due `D` after GST.

**Fairness is about steps that change the state.** `Fairness.lean`'s
`Enabled` holds when *some* transition exists under the label, a stutter
included; `EnabledMove` asks for a transition to a *different* state — TLA+'s
`⟨A⟩_v`. The reason is recorded in `Bounds.md` §6.2.4: assembly actions are
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

The clock is a separate sequence and not a state field on purpose; the
header says why. Dot-notation reaches the `LRun` API (`r.reachable`,
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

/-! ## The clock-carrying lift of a safety fragment

`MVBATemporal` is a class **over** a safety instance `S` at a state type
`state`, and its `TimedRun` reads the clock off `state`. To instantiate it
for a model whose state has no clock, the fragment is lifted to
`state × time`: every observable is `S`'s on the first component, and a
transition is an `S`-transition along which the clock does not decrease.
Nothing about the protocol is restated; the lift is generic in `S`. -/

section Lift

variable {party value message state : Type} {byz : party → Prop}

/-- The lift of a safety fragment to the product with a clock. -/
@[implicit_reducible]
def _root_.MVBASafety.timed (S : MVBASafety party value message state byz)
    (time : Type) [LinearOrder time] :
    MVBASafety party value message (state × time) byz where
  init p := S.init p.1
  step p p' := S.step p.1 p'.1 ∧ p.2 ≤ p'.2
  trans p p' := S.trans p.1 p'.1 ∧ p.2 ≤ p'.2
  reachable p := S.reachable p.1
  step_trans _ _ h := ⟨S.step_trans _ _ h.1, h.2⟩
  reachable_init _ h := S.reachable_init _ h
  reachable_trans _ _ hr h := S.reachable_trans _ _ hr h.1
  Valid := S.Valid
  propose p q v p' := S.propose p.1 q v p'.1 ∧ p.2 ≤ p'.2
  abandon p q p' := S.abandon p.1 q p'.1 ∧ p.2 ≤ p'.2
  propose_trans _ _ _ _ h := ⟨S.propose_trans _ _ _ _ h.1, h.2⟩
  abandon_trans _ _ _ h := ⟨S.abandon_trans _ _ _ h.1, h.2⟩
  decided p := S.decided p.1
  proposed p := S.proposed p.1
  abandoned p := S.abandoned p.1
  sent p := S.sent p.1
  decided_mono _ _ q v h := S.decided_mono _ _ q v h.1
  proposed_mono _ _ q v h := S.proposed_mono _ _ q v h.1
  abandoned_mono _ _ q h := S.abandoned_mono _ _ q h.1
  sent_mono _ _ q m h := S.sent_mono _ _ q m h.1
  propose_effect _ _ _ _ h := S.propose_effect _ _ _ _ h.1
  propose_valid _ _ _ _ h := S.propose_valid _ _ _ _ h.1
  abandon_effect _ _ _ h := S.abandon_effect _ _ _ h.1
  proposed_step_frame _ _ q v h hq := S.proposed_step_frame _ _ q v h.1 hq
  abandoned_step_frame _ _ q h hq := S.abandoned_step_frame _ _ q h.1 hq
  init_decided _ q v h := S.init_decided _ q v h
  init_proposed _ q v h := S.init_proposed _ q v h
  init_abandoned _ q h := S.init_abandoned _ q h
  quiescence _ _ q m h hq hnew hold := S.quiescence _ _ q m h.1 hq hnew hold
  agreement _ hr := S.agreement _ hr
  integrity _ hr := S.integrity _ hr
  external_validity _ hr := S.external_validity _ hr

/-- The lifted fragment is the original on the first component — by
definition, which is the point: nothing was restated. -/
theorem _root_.MVBASafety.timed_decided (S : MVBASafety party value message state byz)
    (time : Type) [LinearOrder time] (p : state × time) (q : party) (v : value) :
    (S.timed time).decided p q v ↔ S.decided p.1 q v := Iff.rfl

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {time : Type} [LinearOrder time]

open scoped Timed in
/-- A labelled timed run of `sys`, as a `TimedRun` of the lifted fragment:
each state paired with its clock, the labels forgotten. `hinit` and `hsteps`
say that `sys`'s runs are `S`'s — for `Mvba.mvbaSafety th` both are the
definitions, since its `init` and `trans` are the model's own. The
`TotalOrder` on `time` is the scoped bridge above. -/
def TLRun.toTimedRun (r : TLRun sys th time) (S : MVBASafety party value message σ byz)
    (hinit : S.init (r.at' 0)) (hsteps : ∀ n, S.trans (r.at' n) (r.at' (n + 1))) :
    TimedRun (σ × time) time (S.timed time).init (S.timed time).trans Prod.snd where
  at' n := (r.at' n, r.clk n)
  starts := hinit
  steps n := ⟨hsteps n, r.clk_mono n⟩
  clock_mono n := r.clk_mono n
  clock_unbounded := r.clk_unbounded
  gst := r.gst

open scoped Timed in
theorem TLRun.toTimedRun_at' (r : TLRun sys th time) (S : MVBASafety party value message σ byz)
    (hinit : S.init (r.at' 0)) (hsteps : ∀ n, S.trans (r.at' n) (r.at' (n + 1))) (n : Nat) :
    (r.toTimedRun S hinit hsteps).at' n = (r.at' n, r.clk n) := rfl

end Lift

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

/-- info: 'MVBASafety.timed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MVBASafety.timed
