import Cadence.PartProjection

/-! # Composed.Witness.Periodic — runs built one plateau at a time

[ConductorBounds.md](../../../docs/ConductorBounds.md) §8.2, stage K8. The
generic half of the composed witness: three facts about labelled timed runs
that hold of any system, used by
[Witness.lean](../Witness.lean) for the composed one.

* **The periodic extension** (`plateauRun`): a run whose clock reads `t` on
  the `t`-th block of `L` consecutive indices (a *plateau*), built from one
  block of steps checked once, for every `t`. An infinite run is then a
  proof about one period, with the clock and the shift as data.
* **Quiet plateau ends** (`bufferedFairFamily_of_ends`,
  `weaklyFairWhen_of_tail`, …): a fairness row of the
  `BufferedFairFamily` shape holds of a run in which, at some index of every
  clock reading, the row's gate is closed, or nothing it covers is enabled,
  or nothing is owed. Every handler of the composed witness fires inside the
  plateau its gate opens in, so every row holds this way, with nothing left
  pending when the clock moves. The untimed rows hold the same way at a
  tail where nothing is enabled.
* **Aligned parts** (`idx_of_always`, `idx_of_from`): in the stutter lift
  of [PartProjection.lean](../../PartProjection.lean), a part that can
  stutter at every index is stepped at every index, and one that can from
  its first step on is stepped at every index from there; its projected run
  is then the composed run, read from that index. -/

namespace Cadence

open Veil
open scoped Cadence.Timed

/-! ## The periodic extension -/

section Periodic

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}

/-- The plateau of index `n` is `n / L`, its position `n % L`: every index
is one position of one plateau. -/
theorem plateau_decomp (L n : Nat) : n = n / L * L + n % L := by
  rw [Nat.div_add_mod' n L]

/-- **One period checked gives every step.** If the step at position `j`
of plateau `t` is a transition for every `t` and every `j < L`, every step
is. -/
theorem steps_of_plateaus {L : Nat} (hL : 0 < L) {st : Nat → σ} {l : Nat → lbl}
    (h : ∀ t j, j < L → sys.tr th (st (t * L + j)) (l (t * L + j)) (st (t * L + j + 1))) (n : Nat) :
    sys.tr th (st n) (l n) (st (n + 1)) := by
  have := h (n / L) (n % L) (Nat.mod_lt n hL)
  rwa [← plateau_decomp] at this

/-- **The periodic extension**: the labelled timed run over `ℕ` whose clock
reads `t` on plateau `t`, from the states and labels of one checked period,
with global stabilisation at time `0`. -/
def plateauRun (L : Nat) (hL : 0 < L) (st : Nat → σ) (l : Nat → lbl)
    (holds : sys.assumptions th) (starts : sys.init th (st 0))
    (h : ∀ t j, j < L → sys.tr th (st (t * L + j)) (l (t * L + j)) (st (t * L + j + 1))) :
    TLRun sys th ℕ where
  at' := st
  lbl := l
  holds := holds
  starts := starts
  steps := steps_of_plateaus hL h
  clk n := n / L
  clk_mono n := Nat.div_le_div_right (Nat.le_succ n)
  clk_unbounded t := ⟨t * L, by rw [Nat.mul_div_cancel _ hL]⟩
  gst := 0

/-- Every index is followed by the last index of its plateau, at the same
clock reading. -/
theorem plateau_end (L : Nat) (hL : 0 < L) (n : Nat) :
    n ≤ n / L * L + (L - 1) ∧ (n / L * L + (L - 1)) / L = n / L := by
  have hd := plateau_decomp L n
  have hm := Nat.mod_lt n hL
  refine ⟨by omega, ?_⟩
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt (by omega), Nat.zero_add]

end Periodic

/-! ## Quiet plateau ends -/

section Quiet

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]

/-- **A buffered family holds when every clock reading has a quiet index**:
from every index `N` some later index `P` on the same clock reading has the
row's owed-condition false, its gate closed, or no label of the family
enabled. With `0 ≤ δ`, `P` lies inside every window measured from an index
at or before it, so the clause's antecedent fails at `P`. -/
theorem bufferedFairFamily_of_ends {r : TLRun sys th time} {D δ : time} (hδ : 0 ≤ δ)
    {C gate : σ → Prop} {S : lbl → Prop}
    (hend : ∀ N, ∃ P, N ≤ P ∧ r.clk P = r.clk N ∧
      ¬ (C (r.at' P) ∧ gate (r.at' P) ∧ ∃ l, S l ∧ Enabled sys th (r.at' P) l)) :
    BufferedFairFamily r D δ C gate S := by
  intro N N' hNN' h1 h2
  obtain ⟨P, hP, hclk, hq⟩ := hend N'
  have hW : r.clk P ≤ r.bufWindow N N' D δ := by
    rw [hclk]
    exact le_trans (r.clk_le_ref N') (le_trans (le_add_of_nonneg_right hδ) (le_max_right _ _))
  have hg := h2 P hP hW
  obtain ⟨hC, hen⟩ := h1 P (le_trans hNN' hP) hW
  exact absurd ⟨hC, hg, hen hg⟩ hq

/-- The one-label form of `bufferedFairFamily_of_ends`. -/
theorem bufferedFair_of_ends {r : TLRun sys th time} {D δ : time} (hδ : 0 ≤ δ)
    {C gate : σ → Prop} {l : lbl}
    (hend : ∀ N, ∃ P, N ≤ P ∧ r.clk P = r.clk N ∧
      ¬ (C (r.at' P) ∧ gate (r.at' P) ∧ Enabled sys th (r.at' P) l)) :
    BufferedFair r D δ C gate l :=
  bufferedFair_iff_family.mpr (bufferedFairFamily_of_ends hδ fun N => by
    obtain ⟨P, h1, h2, h3⟩ := hend N
    exact ⟨P, h1, h2, fun ⟨hC, hg, l', hl', hen⟩ => h3 ⟨hC, hg, hl' ▸ hen⟩⟩)

/-- **An untimed fairness row holds at a quiet tail**: from every index some
later index has the owed-condition false or the label disabled. -/
theorem weaklyFairWhen_of_tail {r : LRun sys th} {C : σ → Prop} {l : lbl}
    (htail : ∀ N, ∃ P, N ≤ P ∧ ¬ (C (r.at' P) ∧ Enabled sys th (r.at' P) l)) :
    WeaklyFairWhen r C l := by
  intro N hen
  obtain ⟨P, hP, hq⟩ := htail N
  exact absurd (hen P hP) hq

/-- The family form of `weaklyFairWhen_of_tail`. -/
theorem weaklyFairFamilyWhen_of_tail {r : LRun sys th} {C : σ → Prop} {S : lbl → Prop}
    (htail : ∀ N, ∃ P, N ≤ P ∧ ¬ (C (r.at' P) ∧ ∃ l, S l ∧ Enabled sys th (r.at' P) l)) :
    WeaklyFairFamilyWhen r C S := by
  intro N hen
  obtain ⟨P, hP, hq⟩ := htail N
  exact absurd (hen P hP) hq

end Quiet

/-! ## Aligned parts -/

section Aligned

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {ρ' σ' lbl' : Type} {sub : RelationalTransitionSystem ρ' σ' lbl'} {th' : ρ'}

/-- The `k`-th index of a predicate that holds exactly from `n0` on is
`n0 + k`. -/
theorem nth_of_from {p : Nat → Prop} [DecidablePred p] {n0 : Nat} (h : ∀ n, p n ↔ n0 ≤ n) (k : Nat) :
    Nat.nth p k = n0 + k := by
  have hc : Nat.count p (n0 + k) = k := by
    induction k with
    | zero =>
      rw [Nat.add_zero, Nat.count_eq_card_filter_range, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro x hx hpx
      have := (h x).1 hpx
      simp at hx
      omega
    | succ k ih =>
      rw [← Nat.add_assoc, Nat.count_succ, ih, if_pos ((h _).2 (by omega))]
  have := Nat.nth_count ((h (n0 + k)).2 (Nat.le_add_right n0 k))
  rwa [hc] at this

open Classical in
/-- **A part stepped at every index**: its `k`-th step is the `k`-th index. -/
theorem idx_of_always (C : Component sys th sub th') (r : LRun sys th) (h : ∀ n, C.isSub (r.lbl n))
    (k : Nat) : C.idx r k = k := by
  unfold Component.idx
  have := nth_of_from (p := fun n => C.isSub (r.lbl n)) (n0 := 0) (fun n => ⟨fun _ => Nat.zero_le n, fun _ => h n⟩) k
  rw [Nat.zero_add] at this
  convert this

open Classical in
/-- **A part stepped at every index from `n0` on**: its `k`-th step is
index `n0 + k`. -/
theorem idx_of_from (C : Component sys th sub th') (r : LRun sys th) {n0 : Nat}
    (h : ∀ n, C.isSub (r.lbl n) ↔ n0 ≤ n) (k : Nat) : C.idx r k = n0 + k := by
  unfold Component.idx
  convert nth_of_from (p := fun n => C.isSub (r.lbl n)) h k

end Aligned

/-! ### Aligned part runs

The stutter lift of [PartProjection.lean](../../PartProjection.lean),
read at a part whose contract relates its state at every index to its state
at the next (`hall`), or does so from index `n0` on and not before
(`hfrom`). The projection is then any labelling, and the part's run is
the composed run read off at the part, from `n0`. -/

section AlignedRuns

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {σ' : Type} {T : TransitionSystemSafety σ'}
variable {time : Type} [LinearOrder time]
variable {C : Component sys th (contractRTS T) ()} {r : TLRun sys th time}

/-- Two timed runs with the same states, clocks and GST are equal. -/
theorem timedRun_ext {state : Type} {init : state → Prop} {trans : state → state → Prop}
    {r₁ r₂ : TimedRun state time init trans} (h₁ : ∀ k, r₁.at' k = r₂.at' k)
    (h₂ : ∀ k, r₁.clk k = r₂.clk k) (h₃ : r₁.gst = r₂.gst) : r₁ = r₂ := by
  obtain ⟨⟨a₁, _, _⟩, c₁, _, _, g₁⟩ := r₁
  obtain ⟨⟨a₂, _, _⟩, c₂, _, _, g₂⟩ := r₂
  have ha : a₁ = a₂ := funext h₁
  have hc : c₁ = c₂ := funext h₂
  simp only at h₃
  subst ha hc h₃
  rfl

/-- A part related to itself across every step is stepped at every index
of the lift. -/
theorem lift_isSub_of_all (hall : ∀ n, T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1)))) (n : Nat) :
    (stutterComp C).isSub ((liftRun C r).lbl n) :=
  (lift_isSub_iff C r n).2 (hall n)

/-- Its projection: any labelling (`Projection.ofScheduled`). -/
noncomputable def projOfAll (hall : ∀ n, T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1)))) :
    (stutterComp C).Projection (liftRun C r).toLRun :=
  Component.Projection.ofScheduled _ _ fun N => ⟨N, le_rfl, lift_isSub_of_all hall N⟩

theorem entry_of_all (hall : ∀ n, T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1))))
    (p : (stutterComp C).Projection (liftRun C r).toLRun) (k : Nat) : p.entry k = k := by
  cases k with
  | zero => rfl
  | succ k =>
    show (stutterComp C).idx (liftRun C r).toLRun k + 1 = k + 1
    rw [idx_of_always _ _ (lift_isSub_of_all hall)]

/-- **The part's run is the composed run, read off at the part.** -/
theorem partRun_at'_of_all (hall : ∀ n, T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1))))
    (p : (stutterComp C).Projection (liftRun C r).toLRun) (k : Nat) :
    (partRun p).at' k = C.proj (r.at' k) := by
  rw [partRun_at', entry_of_all hall]

theorem partRun_clk_of_all (hall : ∀ n, T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1))))
    (p : (stutterComp C).Projection (liftRun C r).toLRun) (k : Nat) :
    (partRun p).clk k = r.clk k := by
  rw [partRun_clk, entry_of_all hall]

/-- A part stepped exactly from `n0` on is stepped at index `n0 + k` of the
lift, its `k`-th step. -/
theorem entry_of_from {n0 : Nat}
    (hfrom : ∀ n, T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1))) ↔ n0 ≤ n)
    (p : (stutterComp C).Projection (liftRun C r).toLRun) (k : Nat) :
    p.entry (k + 1) = n0 + k + 1 := by
  show (stutterComp C).idx (liftRun C r).toLRun k + 1 = n0 + k + 1
  rw [idx_of_from _ _ (fun n => (lift_isSub_iff C r n).trans (hfrom n))]

/-- Its projection: any labelling. -/
noncomputable def projOfFrom {n0 : Nat}
    (hfrom : ∀ n, T.trans (C.proj (r.at' n)) (C.proj (r.at' (n + 1))) ↔ n0 ≤ n) :
    (stutterComp C).Projection (liftRun C r).toLRun :=
  Component.Projection.ofScheduled _ _ fun N =>
    ⟨max N n0, le_max_left _ _, (lift_isSub_iff C r _).2 ((hfrom _).2 (le_max_right _ _))⟩

end AlignedRuns

end Cadence
