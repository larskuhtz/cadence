import Veil.Frontend.Std

/-! # Cadence-local Byzantine quorum instance for `n ≥ 3f+1`

Veil's `byzNodeSetFin` (`Veil/Frontend/Std.lean`) pins the quorum threshold to
the *tight* case `n = 3f+1` (`supermajority q := 2f+1 ≤ |q|`, `hf : n = 3f+1`).
That is a genuine limitation: a BFT protocol must tolerate `f` Byzantine for
**any** `n ≥ 3f+1`, and with the threshold fixed at `2f+1` the intersection
statement is false for `n > 3f+1` (two `2f+1`-quorums can be disjoint).

Rather than touch the shared Veil instance (used by other examples), this is a
Cadence-local copy with the **`n`-scaled** supermajority threshold
`n − f ≤ |q|` (written `n ≤ |q| + f` to keep Nat subtraction out of `omega`;
it collapses to `2f+1` when `n = 3f+1`), and `hf` relaxed to `3f+1 ≤ n`. The
eight `ByzNodeSet` axioms then hold for the whole family `n ≥ 3f+1`
(`2(n−f) − n = n − 2f ≥ f+1`). `greater_than_third := f+1 ≤ |q|` is unchanged
(it never depended on `n`). The proofs are Veil's, with the arithmetic relaxed.
-/

namespace Cadence

section

variable (n f : Nat) (hf : 3 * f + 1 ≤ n)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)

include hbyz

/-- Within any nodup list `s` over `Fin n`, the number of Byzantine elements
    is at most the global Byzantine count `f`. (Copied from Veil.) -/
private theorem byz_in_list_le (s : List (Fin n)) (hnodup : s.Nodup) :
    (s.filter (fun a => decide (is_byz a))).length ≤ f := by
  calc (s.filter (fun a => decide (is_byz a))).length
      = (s.filter (fun a => decide (is_byz a))).toFinset.card := by
        rw [List.toFinset_card_of_nodup (List.Nodup.filter _ hnodup)]
      _ ≤ ((List.ofFn (n := n) id).filter (fun i => decide (is_byz i))).toFinset.card := by
        apply Finset.card_le_card
        intro a ha ; simp at ha ⊢ ; exact ha.2
      _ ≤ ((List.ofFn (n := n) id).filter (fun i => decide (is_byz i))).length :=
        List.toFinset_card_le _
      _ ≤ f := hbyz

/-- ByzNodeSet instance for `Fin n` with at most `f` Byzantine nodes, valid for
    **any** `n ≥ 3f+1` (not only the tight `n = 3f+1`). The supermajority
    threshold scales with `n`. -/
def byzNodeSetFinGen : ByzNodeSet (Fin n) (ByzNSet n) where
  is_byz := is_byz
  member a s := a ∈ s.val
  is_empty s := s.val = []
  supermajority s := n ≤ s.val.length + f          -- `n − f ≤ |s|`, the n-scaled quorum
  greater_than_third s := f + 1 ≤ s.val.length
  supermajorities_intersect_in_honest := by
    intro ⟨s1, hs1_sorted⟩ ⟨s2, hs2_sorted⟩ hsup1 hsup2
    simp only at hsup1 hsup2
    have hnodup1 := List.Pairwise.nodup hs1_sorted
    have hnodup2 := List.Pairwise.nodup hs2_sorted
    have hcard1 : s1.toFinset.card = s1.length := List.toFinset_card_of_nodup hnodup1
    have hcard2 : s2.toFinset.card = s2.length := List.toFinset_card_of_nodup hnodup2
    have hinter := Finset.card_inter (s1.toFinset) (s2.toFinset)
    have hunion := Finset.card_le_univ (s1.toFinset ∪ s2.toFinset) ; simp at hunion
    have hinter_size : f + 1 ≤ (s1.toFinset ∩ s2.toFinset).card := by omega
    by_contra h ; push_neg at h
    have hall_byz : ∀ a ∈ s1.toFinset ∩ s2.toFinset, is_byz a := by
      intro a ha ; simp at h ha
      have := h a ha.1 ha.2 ; tauto
    have hbyz_count : (s1.toFinset ∩ s2.toFinset).card ≤ f := by
      calc (s1.toFinset ∩ s2.toFinset).card
          ≤ ((List.ofFn (n := n) id).filter (fun i => decide (is_byz i))).toFinset.card := by
            apply Finset.card_le_card
            intro a ha ; simp at ha ⊢ ; exact hall_byz a (by simp [ha])
          _ ≤ (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length := by
            apply List.toFinset_card_le
          _ ≤ f := hbyz
    omega
  greater_than_third_one_honest := by
    intro ⟨s, hs_sorted⟩ hgt
    simp only at hgt
    by_contra h ; push_neg at h
    have hall_byz : ∀ a ∈ s, is_byz a := by
      intro a ha ; simp at h ; have := h a ha ; tauto
    have hnodup := List.Pairwise.nodup hs_sorted
    have hbyz_count : s.length ≤ f := by
      calc s.length
          = s.toFinset.card := by simp [List.toFinset_card_of_nodup hnodup]
          _ ≤ ((List.ofFn (n := n) id).filter (fun i => decide (is_byz i))).toFinset.card := by
            apply Finset.card_le_card
            intro a ha ; simp at ha ⊢ ; exact hall_byz a ha
          _ ≤ (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length := by
            apply List.toFinset_card_le
          _ ≤ f := hbyz
    omega
  supermajority_greater_than_third := by
    intro _ hs ; omega
  greater_than_third_nonempty := by
    intro s hs heq ; simp_all
  supermajority_contains_honest_greater_than_third := by
    intro ⟨s, hs_sorted⟩ hsup
    simp only at hsup
    refine ⟨⟨s.filter (fun a => !decide (is_byz a)), List.Pairwise.filter _ hs_sorted⟩, ?_, ?_⟩
    · show f + 1 ≤ _
      have hsplit := List.length_eq_length_filter_add (l := s) (fun a => decide (is_byz a))
      have hb := byz_in_list_le n f is_byz hbyz s (List.Pairwise.nodup hs_sorted)
      simp only ; omega
    · intro a ha ; simp only [List.mem_filter] at ha ; simp_all
  supermajority_greater_than_third_intersect := by
    intro ⟨s1, hs1_sorted⟩ ⟨s2, hs2_sorted⟩ hsup1 hgtt2
    simp only at hsup1 hgtt2
    have hnodup1 := List.Pairwise.nodup hs1_sorted
    have hnodup2 := List.Pairwise.nodup hs2_sorted
    have hcard1 : s1.toFinset.card = s1.length := List.toFinset_card_of_nodup hnodup1
    have hcard2 : s2.toFinset.card = s2.length := List.toFinset_card_of_nodup hnodup2
    have hinter := Finset.card_inter_add_card_union s1.toFinset s2.toFinset
    have hunion : (s1.toFinset ∪ s2.toFinset).card ≤ n := by
      have := Finset.card_le_univ (s1.toFinset ∪ s2.toFinset) ; simpa using this
    have hne : 0 < (s1.toFinset ∩ s2.toFinset).card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hne
    rw [Finset.mem_inter, List.mem_toFinset, List.mem_toFinset] at ha
    exact ⟨a, by simp [ha.1], by simp [ha.2]⟩
  supermajorities_intersect_in_greater_than_third := by
    intro ⟨s1, hs1_sorted⟩ ⟨s2, hs2_sorted⟩ hsup1 hsup2
    simp only at hsup1 hsup2
    refine ⟨⟨s1.filter (fun a => decide (a ∈ s2)), List.Pairwise.filter _ hs1_sorted⟩, ?_, ?_⟩
    · show f + 1 ≤ _
      have hnodup1 := List.Pairwise.nodup hs1_sorted
      have hnodup2 := List.Pairwise.nodup hs2_sorted
      have hcard1 : s1.toFinset.card = s1.length := List.toFinset_card_of_nodup hnodup1
      have hcard2 : s2.toFinset.card = s2.length := List.toFinset_card_of_nodup hnodup2
      have hinter := Finset.card_inter_add_card_union s1.toFinset s2.toFinset
      have hunion : (s1.toFinset ∪ s2.toFinset).card ≤ n := by
        have := Finset.card_le_univ (s1.toFinset ∪ s2.toFinset) ; simpa using this
      have hfilt : (s1.filter (fun a => decide (a ∈ s2))).length
          = (s1.toFinset ∩ s2.toFinset).card := by
        rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ hnodup1)]
        congr 1
        ext a ; simp
      simp only ; omega
    · intro a ha ; simp only [List.mem_filter] at ha ; simp_all

-- Decidability of the guard-facing data fields (copied from Veil, for the
-- new instance). The theorem fields are erased; only these are evaluated.
instance byzNodeSetFinGen_is_byz_dec :
  ∀ a, Decidable (ByzNodeSet.is_byz (self := byzNodeSetFinGen n f hf is_byz hbyz) a) := by
  dsimp [byzNodeSetFinGen] ; intros ; infer_instance

instance byzNodeSetFinGen_member_dec :
  ∀ a b, Decidable (ByzNodeSet.member (self := byzNodeSetFinGen n f hf is_byz hbyz) a b) := by
  dsimp [byzNodeSetFinGen] ; intros ; infer_instance

instance byzNodeSetFinGen_supermajority_dec :
  ∀ a, Decidable (ByzNodeSet.supermajority _ (self := byzNodeSetFinGen n f hf is_byz hbyz) a) := by
  dsimp [byzNodeSetFinGen] ; intros ; infer_instance

instance byzNodeSetFinGen_greater_than_third_dec :
  ∀ a, Decidable (ByzNodeSet.greater_than_third _ (self := byzNodeSetFinGen n f hf is_byz hbyz) a) := by
  dsimp [byzNodeSetFinGen] ; intros ; infer_instance

end

/-! ## Instantiation sanity checks

The whole point: a valid `ByzNodeSet` at a **non-tight** committee size
`n > 3f+1` — impossible with Veil's `byzNodeSetFin` (`n = 3f+1` exactly). -/

-- n = 5 > 3f+1 = 4 (f = 1): the case the tight Veil instance cannot express.
example : ByzNodeSet (Fin 5) (ByzNSet 5) :=
  byzNodeSetFinGen 5 1 (by decide) (fun i => i.val = 0) (by decide)

-- n = 6 (f = 1) — another non-tight size.
example : ByzNodeSet (Fin 6) (ByzNSet 6) :=
  byzNodeSetFinGen 6 1 (by decide) (fun i => i.val = 0) (by decide)

-- n = 4 = 3f+1 (f = 1): the tight case, equivalent to Veil's instance
-- (threshold `n − f = 3 = 2f+1`) — the monitor's current instantiation.
example : ByzNodeSet (Fin 4) (ByzNSet 4) :=
  byzNodeSetFinGen 4 1 (by decide) (fun _ => False) (by decide)

end Cadence
