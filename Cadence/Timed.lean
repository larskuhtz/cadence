import Cadence.Fairness
import Mathlib.Order.MinMax

/-! # Timed — labelled timed runs, and bounded fairness after GST

The timed vocabulary of the bounds work ([Bounds.md](../docs/Bounds.md)
§6.2), one level below the module contracts and one level above
[Fairness.lean](Fairness.lean): a labelled run **with a clock**, and weak
fairness with a *deadline* instead of an *eventually*. Nothing here is Cadence-specific and nothing
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

**Fairness is about enabled actions.** Bounded fairness is stated over
[Fairness.lean](Fairness.lean)'s `Enabled`, as the untimed fairness notions
there are: a label enabled throughout its window fires within it. For the
MVBA, the one model timed here, that is the same premise as bounded fairness
over state-changing steps (`BoundedFairMove`), because every fair label is
move-enabled wherever it is enabled (`Mvba.enabledMove_of_enabled`); the
bridge is `Mvba.boundedFair_iff_move`, from `boundedFair_iff_move` below, and
Fairness.lean's section "Enabledness and the two fairness classes" says why
the distinction was ever drawn.

## Two more pieces, for the Chorus leg

**The buffered hop** (`BufferedFair`, `BufferedFairFamily`): the paper's
buffering sentence as a fairness clause, with a step's bound split into a
message part and a local gate ([Bounds.md](../docs/Bounds.md) §6.4.2, F2).
When the gate opens with the message part it is `BoundedFair` again
(`bufferedFair_iff_boundedFair`).

**The timed projection** (`Component.Projection.timed`): a component's run
inside a composed run, with the clock carried along, so that a part's timing
model can be stated on the part's own run and its conclusions brought back
(`timed_back`, `timed_forward`, `boundedFair_iff`). -/

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

/-! ## Bounded weak fairness

Over [Fairness.lean](Fairness.lean)'s `Enabled`, as the untimed fairness
notions are. -/

/-- **Bounded weak fairness** of `l` with hop bound `D`: from any index `N`,
if `l` is enabled at every index at or after `N` whose clock is inside
the window `ref N + D`, then `l` fires with its post-state inside that
window. The timed form of `WeaklyFair`; the paper's "after GST, every step a
correct validator can take is taken within `D`". -/
def BoundedFair [Add time] (r : TLRun sys th time) (D : time) (l : lbl) : Prop :=
  ∀ N, (∀ n, N ≤ n → r.clk n ≤ r.ref N + D → Enabled sys th (r.at' n) l) →
    r.FiresWithin N D l

/-- **The form a proof uses.** If a bounded-fair label does not fire within
its window from `N`, it is disabled at some index inside that window — so a
proof that it *stays* enabled across the window has produced a
contradiction, and a proof that it can only be disabled by progress has
produced progress by the deadline. The contrapositive of `BoundedFair`, and
the timed twin of `exists_disabled_of_never_fires`. -/
theorem exists_not_enabled_of_not_firesWithin [Add time]
    {r : TLRun sys th time} {D : time} {l : lbl} (hbf : BoundedFair r D l)
    {N : Nat} (hnever : ¬ r.FiresWithin N D l) :
    ∃ n, N ≤ n ∧ r.clk n ≤ r.ref N + D ∧ ¬ Enabled sys th (r.at' n) l := by
  by_contra hc
  push Not at hc
  exact hnever (hbf N (fun n hn hclk => hc n hn hclk))

/-! ### The state-changing form, and the bridge

As in [Fairness.lean](Fairness.lean): `BoundedFairMove` is only the
right-hand side of a model's bridge, and no premise is stated with it. -/

/-- `BoundedFair` over state-changing steps (`EnabledMove`). -/
def BoundedFairMove [Add time] (r : TLRun sys th time) (D : time) (l : lbl) : Prop :=
  ∀ N, (∀ n, N ≤ n → r.clk n ≤ r.ref N + D → EnabledMove sys th (r.at' n) l) →
    r.FiresWithin N D l

/-- **The bridge, per label.** For a label that is move-enabled wherever it is
enabled along the run, bounded fairness over plain enabledness and over
state-changing steps are the same premise. -/
theorem boundedFair_iff_move [Add time] {r : TLRun sys th time} {D : time} {l : lbl}
    (hacc : ∀ n, Enabled sys th (r.at' n) l → EnabledMove sys th (r.at' n) l) :
    BoundedFair r D l ↔ BoundedFairMove r D l :=
  ⟨fun h N hen => h N fun n hn hc => Enabled.of_move (hen n hn hc),
   fun h N hen => h N fun n hn hc => hacc n (hen n hn hc)⟩

/-! ## Families, and the buffered hop

Two generalisations of `BoundedFair`, both for the Chorus leg
([Bounds.md](../docs/Bounds.md) §6.4.2). A **family** is fair as a whole,
the timed twin of `WeaklyFairFamily`: one of an action's parameters is a
result rather than a choice. A **buffered hop** splits a step's bound in
two, as the paper's message buffering does: "a message whose rule is
blocked by this convention is not lost" (`subsection:chorus-protocol-overview`).
The message part is due `D` after it was sent, and the rule fires `δ` after
its local gate opened. Measuring one hop from the later of the two, as
`BoundedFair` would, costs an extra `D` wherever the gate opens last. -/

/-- A label of the family `S` fires at some index at or after `N`, with the
post-state of that step at clock at most `t`. `FiresWithin N D l` is the
case `t = ref N + D` and `S = (· = l)` (`firesWithin_iff`). -/
def TLRun.FiresBy (r : TLRun sys th time) (N : Nat) (t : time) (S : lbl → Prop) : Prop :=
  ∃ n, N ≤ n ∧ S (r.lbl n) ∧ r.clk (n + 1) ≤ t

theorem TLRun.firesWithin_iff [Add time] (r : TLRun sys th time) (N : Nat) (D : time) (l : lbl) :
    r.FiresWithin N D l ↔ r.FiresBy N (r.ref N + D) (· = l) :=
  Iff.rfl

/-- **Bounded weak fairness of a family** `S`: from any index `N`, if at every
index at or after `N` whose clock is inside `ref N + D` some label of `S`
is enabled, then some label of `S` fires with its post-state inside that
window. The label that is enabled may change from index to index. For a
singleton family it is `BoundedFair` (`boundedFairFamily_eq_iff`). -/
def BoundedFairFamily [Add time] (r : TLRun sys th time) (D : time) (S : lbl → Prop) : Prop :=
  ∀ N, (∀ n, N ≤ n → r.clk n ≤ r.ref N + D → ∃ l, S l ∧ Enabled sys th (r.at' n) l) →
    r.FiresBy N (r.ref N + D) S

/-- A one-label family is bounded-fair exactly when its label is. -/
theorem boundedFairFamily_eq_iff [Add time] {r : TLRun sys th time} {D : time} {l : lbl} :
    BoundedFairFamily r D (· = l) ↔ BoundedFair r D l :=
  ⟨fun h N hen => h N fun n hn hc => ⟨l, rfl, hen n hn hc⟩,
   fun h N hen => h N fun n hn hc => by
     obtain ⟨l', rfl, hl'⟩ := hen n hn hc
     exact hl'⟩

/-- The **window of a buffered hop** from `N` (the message part is due) and
`N' ≥ N` (the local gate is open): the later of `ref N + D` and
`ref N' + δ`. -/
def TLRun.bufWindow [Add time] (r : TLRun sys th time) (N N' : Nat) (D δ : time) : time :=
  max (r.ref N + D) (r.ref N' + δ)

/-- **(Δδ-justice), for a family**: bounded weak fairness with the hop split
into a message part `D` and a local part `δ`, [Bounds.md](../docs/Bounds.md)
§6.4.2. Read with `W := bufWindow N N' D δ`, for `N ≤ N'`:

* **the message part** — at every index `n ≥ N` with `clk n ≤ W`, `C` holds
  and, wherever the gate is open, some label of `S` is enabled;
* **the local gate** — `gate` holds at every index `n ≥ N'` with
  `clk n ≤ W`.

Then some label of `S` fires, with its post-state inside `W`.

`gate` is a state predicate that, at each use, mentions only the acting
validator's own local state and the phase (Chorus/Schedule.lean states that
checklist). `C` says what the environment must have supplied for the step
to be owed at all, for instance that the messages it consumes came from
correct senders; with `C` and `gate` trivially true and `δ ≤ D` the clause
is `BoundedFairFamily` (`bufferedFairFamily_iff`). -/
def BufferedFairFamily [Add time] (r : TLRun sys th time) (D δ : time) (C gate : σ → Prop)
    (S : lbl → Prop) : Prop :=
  ∀ N N', N ≤ N' →
    (∀ n, N ≤ n → r.clk n ≤ r.bufWindow N N' D δ →
      C (r.at' n) ∧ (gate (r.at' n) → ∃ l, S l ∧ Enabled sys th (r.at' n) l)) →
    (∀ n, N' ≤ n → r.clk n ≤ r.bufWindow N N' D δ → gate (r.at' n)) →
    r.FiresBy N (r.bufWindow N N' D δ) S

/-- **(Δδ-justice)** for one label: `BufferedFairFamily` of the family
`(· = l)`, written out (`bufferedFair_iff_family`). This is the clause a
row of a hop table asserts. -/
def BufferedFair [Add time] (r : TLRun sys th time) (D δ : time) (C gate : σ → Prop)
    (l : lbl) : Prop :=
  ∀ N N', N ≤ N' →
    (∀ n, N ≤ n → r.clk n ≤ r.bufWindow N N' D δ →
      C (r.at' n) ∧ (gate (r.at' n) → Enabled sys th (r.at' n) l)) →
    (∀ n, N' ≤ n → r.clk n ≤ r.bufWindow N N' D δ → gate (r.at' n)) →
    ∃ n, N ≤ n ∧ r.lbl n = l ∧ r.clk (n + 1) ≤ r.bufWindow N N' D δ

theorem bufferedFair_iff_family [Add time] {r : TLRun sys th time} {D δ : time}
    {C gate : σ → Prop} {l : lbl} :
    BufferedFair r D δ C gate l ↔ BufferedFairFamily r D δ C gate (· = l) := by
  constructor
  · intro h N N' hNN' hmsg hgate
    exact h N N' hNN' (fun n hn hc => ⟨(hmsg n hn hc).1, fun hg => by
      obtain ⟨l', rfl, hl'⟩ := (hmsg n hn hc).2 hg
      exact hl'⟩) hgate
  · intro h N N' hNN' hmsg hgate
    exact h N N' hNN' (fun n hn hc =>
      ⟨(hmsg n hn hc).1, fun hg => ⟨l, rfl, (hmsg n hn hc).2 hg⟩⟩) hgate

section Reduction

variable [AddCommMonoid time] [IsOrderedAddMonoid time]

/-- With the gate opening together with the message part (`N = N'`) and
`δ ≤ D`, the window is `ref N + D`, `BoundedFair`'s. -/
theorem TLRun.bufWindow_diag (r : TLRun sys th time) (N : Nat) {D δ : time} (hδ : δ ≤ D) :
    r.bufWindow N N D δ = r.ref N + D :=
  max_eq_left (add_le_add_right hδ _)

/-- **At `N = N'` the buffered hop is `BoundedFair`'s clause.** A label that is
owed (`C`), gated open and enabled throughout the window `ref N + D` fires
within `D` of `N`, when `δ ≤ D`: the diagonal of (Δδ-justice), which is
§6.2.4's `BoundedFair` with the gate and `C` added to the window's
antecedent. -/
theorem BufferedFairFamily.diag {r : TLRun sys th time} {D δ : time} {C gate : σ → Prop}
    {S : lbl → Prop} (h : BufferedFairFamily r D δ C gate S) (hδ : δ ≤ D) (N : Nat)
    (hen : ∀ n, N ≤ n → r.clk n ≤ r.ref N + D →
      C (r.at' n) ∧ gate (r.at' n) ∧ ∃ l, S l ∧ Enabled sys th (r.at' n) l) :
    r.FiresBy N (r.ref N + D) S := by
  have hw := r.bufWindow_diag N hδ
  have := h N N le_rfl (fun n hn hc => by
      rw [hw] at hc
      exact ⟨(hen n hn hc).1, fun _ => (hen n hn hc).2.2⟩)
    (fun n hn hc => by rw [hw] at hc; exact (hen n hn hc).2.1)
  rwa [hw] at this

/-- **The reduction, for a family.** With nothing owed beyond enabledness
(`C` and `gate` hold everywhere) and `δ ≤ D`, (Δδ-justice) is
`BoundedFairFamily`: the diagonal `N = N'` gives one direction, and a
window that only grows gives the other. -/
theorem bufferedFairFamily_iff {r : TLRun sys th time} {D δ : time} {C gate : σ → Prop}
    {S : lbl → Prop} (hC : ∀ s, C s) (hg : ∀ s, gate s) (hδ : δ ≤ D) :
    BufferedFairFamily r D δ C gate S ↔ BoundedFairFamily r D S := by
  constructor
  · intro h N hen
    exact h.diag hδ N fun n hn hc => ⟨hC _, hg _, hen n hn hc⟩
  · intro h N N' _ hmsg _
    have hle : r.ref N + D ≤ r.bufWindow N N' D δ := le_max_left _ _
    obtain ⟨n, hn, hS, hc⟩ :=
      h N fun n hn hc => (hmsg n hn (le_trans hc hle)).2 (hg _)
    exact ⟨n, hn, hS, le_trans hc hle⟩

/-- **The reduction, for one label** — the lemma the Chorus leg's plan asks
for: with `N = N'`, a trivial gate and nothing further owed, the buffered
hop *is* §6.2.4's `BoundedFair` (`δ ≤ D`, as for every `Δ`-row). -/
theorem bufferedFair_iff_boundedFair {r : TLRun sys th time} {D δ : time} {C gate : σ → Prop}
    {l : lbl} (hC : ∀ s, C s) (hg : ∀ s, gate s) (hδ : δ ≤ D) :
    BufferedFair r D δ C gate l ↔ BoundedFair r D l := by
  rw [bufferedFair_iff_family, bufferedFairFamily_iff hC hg hδ, boundedFairFamily_eq_iff]

end Reduction

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

/-! ## The timed projection

[Fairness.lean](Fairness.lean)'s `Component.Projection` turns a run of the
whole into a run of a part, at the part's steps. Here it is lifted to
labelled *timed* runs by carrying the clock along ([Bounds.md](../docs/Bounds.md)
§6.4.2): projected state `k` reads the clock of the composed index at which
the part **entered** it, `entry k` — index `0` for the initial state, and the
post-state of the part's `k`-th step otherwise. The projected step `k → k+1`
then carries the post-state clock of the composed step that took it, which is
`FiresWithin`'s convention, and the projected run's `gst` is the composed
run's.

Three facts make the projection a faithful view of time, and each is a
theorem below:

* **back-transfer** (`timed_back`): a fact of the part at projected clock
  `≤ X` holds of the composed run at clock `≤ X`, since the part's state is
  constant between its steps — the direction a proof uses to bring the
  part's decision back;
* **forward transfer** (`timed_forward`): a fact of the part at a composed
  index with clock `≤ X` holds of the projected run at clock `≤ X`;
* **fairness transfer** (`boundedFair_iff`): bounded weak fairness of a
  label of the part means the same read on the projected run or on the
  composed one, as `weaklyFair_iff` does untimed. -/

namespace Component

section Timed

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {ρ' σ' lbl' : Type} {sub : RelationalTransitionSystem ρ' σ' lbl'} {th' : ρ'}
variable {time : Type} [LinearOrder time]
variable {C : Component sys th sub th'} {r : TLRun sys th time}

namespace Projection

variable (p : C.Projection r.toLRun)

/-- The composed index at which the part entered its projected state `k`:
`0` for the initial state, one past its `k`-th step's index otherwise. -/
noncomputable def entry (_ : C.Projection r.toLRun) : Nat → Nat
  | 0 => 0
  | k + 1 => C.idx r.toLRun k + 1

theorem entry_le_idx : ∀ k, p.entry k ≤ C.idx r.toLRun k
  | 0 => Nat.zero_le _
  | k + 1 => p.scheduled.idx_lt_idx_succ k

/-- Between entering a projected state and leaving it, the part's state is
that projected state. -/
theorem proj_eq_run_of_between {k m : Nat} (h₁ : p.entry k ≤ m)
    (h₂ : m ≤ C.idx r.toLRun k) : C.proj (r.at' m) = p.run.at' k := by
  classical
  rw [p.proj_eq_run_cover m]
  congr 1
  apply le_antisymm
  · have := Scheduled.cover_mono (C := C) (r := r.toLRun) h₂
    rwa [p.scheduled.cover_idx] at this
  · cases k with
    | zero => exact Nat.zero_le _
    | succ k =>
      have hmono := Scheduled.cover_mono (C := C) (r := r.toLRun) h₁
      refine le_trans ?_ hmono
      show k + 1 ≤ Nat.count _ (C.idx r.toLRun k + 1)
      rw [Nat.count_succ, if_pos (p.scheduled.isSub_idx k)]
      exact Nat.succ_le_succ (le_of_eq (p.scheduled.cover_idx k).symm)

/-- A composed index at or after the entry of projected state `k` is covered
by `k` or a later projected state. -/
theorem le_cover_of_entry_le {k n : Nat} (h : p.entry k ≤ n) : k ≤ C.cover r.toLRun n := by
  classical
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    have hmono := Scheduled.cover_mono (C := C) (r := r.toLRun) h
    refine le_trans ?_ hmono
    show k + 1 ≤ Nat.count _ (C.idx r.toLRun k + 1)
    rw [Nat.count_succ, if_pos (p.scheduled.isSub_idx k)]
    exact Nat.succ_le_succ (le_of_eq (p.scheduled.cover_idx k).symm)

/-- The projected run's `k`-th state is the part's state at its entry index. -/
theorem run_at'_entry (k : Nat) : p.run.at' k = C.proj (r.at' (p.entry k)) :=
  (p.proj_eq_run_of_between le_rfl (p.entry_le_idx k)).symm

/-- The projected state covering index `n` was entered at or before `n`. -/
theorem entry_cover_le (n : Nat) : p.entry (C.cover r.toLRun n) ≤ n := by
  classical
  unfold Component.cover
  cases h : Nat.count (fun m => C.isSub (r.toLRun.lbl m)) n with
  | zero => exact Nat.zero_le _
  | succ k =>
    exact Nat.nth_lt_of_lt_count (p := fun m => C.isSub (r.toLRun.lbl m)) (by omega)

/-- **The timed projection**: the projected run, with the clock of each
projected state's entry index, and the composed run's `gst`. -/
noncomputable def timed : TLRun sub th' time where
  toLRun := p.run
  clk k := r.clk (p.entry k)
  clk_mono k := r.clk_le_of_le (by
    cases k with
    | zero => exact Nat.zero_le _
    | succ k => exact Nat.succ_le_succ (p.scheduled.idx_lt_idx_succ k).le)
  clk_unbounded t := by
    obtain ⟨n, hn⟩ := r.clk_unbounded t
    exact ⟨n + 1, le_trans hn (r.clk_le_of_le (Nat.le_succ_of_le (p.scheduled.le_idx n)))⟩
  gst := r.gst

@[simp] theorem timed_toLRun : p.timed.toLRun = p.run := rfl
@[simp] theorem timed_clk (k : Nat) : p.timed.clk k = r.clk (p.entry k) := rfl
@[simp] theorem timed_gst : p.timed.gst = r.gst := rfl

/-- The projected reference time is the composed one at the entry index. -/
theorem timed_ref (k : Nat) : p.timed.ref k = r.ref (p.entry k) := rfl

/-- **Back-transfer.** A fact of the part that holds at a projected state
whose clock is at most `X` holds of the composed run at an index whose clock
is at most `X`: the index at which the part entered that state. So the
part's decision "by `X`" in the projection is a decision by `X` in the
composed run. -/
theorem timed_back {P : σ' → Prop} {k : Nat} {X : time} (hc : p.timed.clk k ≤ X)
    (hP : P (p.timed.at' k)) : ∃ n, r.clk n ≤ X ∧ P (C.proj (r.at' n)) :=
  ⟨p.entry k, hc, p.run_at'_entry k ▸ hP⟩

/-- **Forward transfer.** A fact of the part at a composed index whose clock
is at most `X` holds of the projected run at a projected index whose clock is
at most `X`: the projected state covering that index was entered no later. -/
theorem timed_forward {P : σ' → Prop} {n : Nat} {X : time} (hc : r.clk n ≤ X)
    (hP : P (C.proj (r.at' n))) : ∃ k, p.timed.clk k ≤ X ∧ P (p.timed.at' k) :=
  ⟨C.cover r.toLRun n, le_trans (r.clk_le_of_le (p.entry_cover_le n)) hc,
    by rw [p.proj_eq_run_cover n] at hP; exact hP⟩

/-- **Bounded weak fairness of a label of the part, read in the composed
run**: if the label is enabled — at the part's state — at every composed
index from `N` on whose clock is inside `ref N + D`, then the whole takes a
step of the part, labelled with it by the projection, whose post-state is
inside the window. The composed-run form of `BoundedFair p.timed D l'`;
`boundedFair_iff` says the two are the same. -/
def BoundedFairIn [Add time] (D : time) (l' : lbl') : Prop :=
  ∀ N, (∀ n, N ≤ n → r.clk n ≤ r.ref N + D → Enabled sub th' (C.proj (r.at' n)) l') →
    ∃ n, N ≤ n ∧ C.isSub (r.lbl n) ∧ p.lbl n = l' ∧ r.clk (n + 1) ≤ r.ref N + D

/-- **Bounded weak fairness survives the timed projection, in both
directions** (for a non-negative bound). A premise on the projected run —
the form the part's own timing model states — therefore means the same as
the premise read at the composed run, so the re-indexing smuggles nothing
in. The timed twin of `weaklyFair_iff`: between the part's steps its state
does not change, and the projected clock is the entry clock, which is never
later than a composed index it covers. -/
theorem boundedFair_iff [AddCommMonoid time] [IsOrderedAddMonoid time] {D : time}
    (hD : 0 ≤ D) (l' : lbl') : BoundedFair p.timed D l' ↔ p.BoundedFairIn D l' := by
  classical
  have href : ∀ {a b : Nat}, a ≤ b → r.ref a ≤ r.ref b := fun h =>
    max_le_max (r.clk_le_of_le h) le_rfl
  constructor
  · intro h N hen
    set K := C.cover r.toLRun N
    have hKN : p.entry K ≤ N := p.entry_cover_le N
    have hwin : p.timed.ref K + D ≤ r.ref N + D := add_le_add_left (href hKN) _
    obtain ⟨k, hk, hl, hc⟩ := h K fun k hk hck => by
      have hNk : N ≤ C.idx r.toLRun k :=
        le_trans (p.scheduled.le_idx_cover N) (p.scheduled.idx_strictMono.monotone hk)
      have hstate := p.proj_eq_run_of_between (k := k) (m := max N (p.entry k))
        (le_max_right _ _) (max_le hNk (p.entry_le_idx k))
      show Enabled sub th' (p.run.at' k) l'
      rw [← hstate]
      refine hen _ (le_max_left _ _) ?_
      rcases le_total N (p.entry k) with hle | hle
      · rw [max_eq_right hle]; exact le_trans hck hwin
      · rw [max_eq_left hle]
        exact le_trans (r.clk_le_ref N) (le_add_of_nonneg_right hD)
    refine ⟨C.idx r.toLRun k,
      le_trans (p.scheduled.le_idx_cover N) (p.scheduled.idx_strictMono.monotone hk),
      p.scheduled.isSub_idx k, hl, le_trans hc hwin⟩
  · intro h K hen
    have hcov : C.cover r.toLRun (p.entry K) = K := by
      have := p.proj_eq_run_of_between (k := K) le_rfl (p.entry_le_idx K)
      apply le_antisymm
      · have hm := Scheduled.cover_mono (C := C) (r := r.toLRun) (p.entry_le_idx K)
        rwa [p.scheduled.cover_idx] at hm
      · cases K with
        | zero => exact Nat.zero_le _
        | succ k =>
          show k + 1 ≤ Nat.count _ (C.idx r.toLRun k + 1)
          rw [Nat.count_succ, if_pos (p.scheduled.isSub_idx k)]
          exact Nat.succ_le_succ (le_of_eq (p.scheduled.cover_idx k).symm)
    obtain ⟨n, hn, hsub, hl, hc⟩ := h (p.entry K) fun n hn hcn => by
      rw [p.proj_eq_run_cover n]
      have hK : K ≤ C.cover r.toLRun n := hcov ▸ Scheduled.cover_mono (C := C) (r := r.toLRun) hn
      exact hen _ hK (le_trans (r.clk_le_of_le (p.entry_cover_le n)) hcn)
    have hidx : C.idx r.toLRun (C.cover r.toLRun n) = n := Scheduled.idx_cover_of_isSub hsub
    refine ⟨C.cover r.toLRun n, hcov ▸ Scheduled.cover_mono (C := C) (r := r.toLRun) hn, ?_, ?_⟩
    · show p.lbl (C.idx r.toLRun (C.cover r.toLRun n)) = l'
      rw [hidx, hl]
    · show r.clk (C.idx r.toLRun (C.cover r.toLRun n) + 1) ≤ r.ref (p.entry K) + D
      rw [hidx]; exact hc

end Projection

end Timed

end Component

end Cadence

/-! ## The pinned trust base

Definitions and a handful of lemmas about them; the standard trio and
nothing else, and nothing about any particular protocol. -/

/--
info: 'Cadence.exists_not_enabled_of_not_firesWithin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.exists_not_enabled_of_not_firesWithin

/-- info: 'Cadence.boundedFair_iff_move' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cadence.boundedFair_iff_move

/-- info: 'Cadence.TLRun.withinFrom_forall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cadence.TLRun.withinFrom_forall

/-- info: 'Cadence.gstLub_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cadence.gstLub_iff

/-- info: 'TimedRun.byGstBound_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TimedRun.byGstBound_iff

/-! The buffered hop and its reduction to `BoundedFair`, and the timed
projection with its three transfers. The projection rests on Mathlib's
`Nat.nth`/`Nat.count`, as the untimed one does. -/

/-- info: 'Cadence.bufferedFair_iff_boundedFair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cadence.bufferedFair_iff_boundedFair

/-- info: 'Cadence.bufferedFairFamily_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cadence.bufferedFairFamily_iff

/-- info: 'Cadence.BufferedFairFamily.diag' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cadence.BufferedFairFamily.diag

/-- info: 'Cadence.boundedFairFamily_eq_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cadence.boundedFairFamily_eq_iff

/--
info: 'Cadence.Component.Projection.timed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.Component.Projection.timed

/--
info: 'Cadence.Component.Projection.timed_back' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.Component.Projection.timed_back

/--
info: 'Cadence.Component.Projection.timed_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.Component.Projection.timed_forward

/--
info: 'Cadence.Component.Projection.boundedFair_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.Component.Projection.boundedFair_iff
