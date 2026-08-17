import Veil

/-! # Slot/window theory and the ACS median lemma (plan phase C2)

Support theory for the Conductor orchestrator model
([`Conductor.lean`](./Conductor.lean)): the ordered slot/window structure
and the order-statistics lemma justifying the median-range `require` of the
Conductor's ACS-decide oracle action. Reference:
`docs/ConductorPlan.md` §3 (new modelling ingredients 1–2)
and `papers/cadence/src/p2_conductor_proofs.tex` (`algorithm:conductor`,
`line:median-compute`; median range validity is used in
`prop:acs-nonoverlap` and `prop:window-open-time`).

## How the plan's "ordered slot/window theory" resolved

`docs/ConductorPlan.md` §3 proposed static uninterpreted functions
(`win_of : slot → window`, `win_first/win_last : window → slot`) with Horn
axioms. Working the design out against `algorithm:conductor` showed the
window→interval assignment **cannot be static theory**: a window's first
slot is decided *at runtime* by `ACS[ω]` (`line:median-compute`), so the
assignment is execution-dependent state. The design therefore splits:

* **Static** — only the *index* structures:
  - `slot` gets `TotalOrderWithMinimum` (Veil `Frontend/Std.lean`): a total
    order with strict variant, a least element (the paper's slot 1 — window
    1's first slot), and a derived successor `next` (needed for the
    `line:sstar-update` guard residue "strictly above the current window's
    last slot"). No `+W` arithmetic enters the SMT layer.
  - `window` gets `TotalOrderWithMinimum` likewise (least element = window
    1; `next` = the `ω + 1` stepping of `line:window-increment`).
  Both classes come with proven `Fin (n+1)` instances in
  `Veil/Frontend/Std.lean`, so the axiom sets are demonstrably satisfiable
  — the instance discipline established for `ByzNodeSet` — and **no new
  axioms are introduced by C2 at all**.
* **Dynamic** — the window *intervals* `[first(ω), last(ω)]` (and the
  readiness boundary, the paper's "first `p` slots of the window") are
  *oracle state* in `Conductor.lean`: relations populated by the ACS-decide
  oracle action, unique per window by its `require`s (= ACS agreement).
  Cardinality facts ("exactly `W` slots wide", `prop:open-count-window`)
  stay meta, per the plan's interval-formulation directive.

This also disposes of the plan's flagged technical risk ("SMT behavior of
the ordered-type theory"): the only background theory the Conductor's VCs
carry is two `TotalOrderWithMinimum` instances and one `TotalOrder` (for
the abstract clock), each a small Horn axiom set of the shape Veil's
existing examples (NOPaxos `seq_t`) already exercise.

## The median lemma

`algorithm:conductor` opens window `ω` at the **median** of the slot
numbers in the decided ACS set (`line:median-compute`). The paper's
argument (stated after `lemma:window-entry`): the decided set contains at
least `2f + 1` pairs of which at most `f` are Byzantine, so the median
lies between two *correct* proposals. The Conductor model imports exactly
this consequence as a `require` on its ACS-decide oracle action, with the
two correct bracketing proposals as explicit action parameters (witnesses,
per the Build #10 certificate-materialisation lesson). This file proves
the justifying lemma, in two layers:

1. `IsMedian` — the abstract order-statistics property ("at least half the
   values are ≤ m, at least half are ≥ m") — and the bracketing lemma
   `IsMedian.between_correct`: any such `m` over ≥ `2f+1` values of which
   ≤ `f` are Byzantine-attributed is bracketed by two correct values.
   Stated over an abstract correctness predicate, *not* over cardinality
   of node sets — per the stake-weighting design rule of
   `docs/ConductorPlan.md` §7 (a weighted instance re-proves `IsMedian`
   membership for its weighted median and inherits the bracketing).
2. `lowerMedian` — the deterministic sorted-middle median an
   implementation computes — and `lowerMedian_isMedian`, the instance
   proof that it satisfies `IsMedian`. (Any other conventional pick of the
   middle order statistic — upper median, min/max of the two — satisfies
   `IsMedian` the same way; the Conductor model depends only on the
   abstract property.)

`lowerMedian_between_correct` packages the two for citation from
`Conductor.lean`.
-/

namespace Cadence

/-! ## The abstract median property -/

/-- `m` is a (weak) median of the multiset of values `vals`: at least half
the elements are `≤ m` and at least half are `≥ m`. Every conventional
median satisfies this (see `lowerMedian_isMedian` below). -/
def IsMedian {α : Type} [LinearOrder α] (m : α) (vals : List α) : Prop :=
  vals.length ≤ 2 * vals.countP (fun x => decide (x ≤ m)) ∧
  vals.length ≤ 2 * vals.countP (fun x => decide (m ≤ x))

/-- **Median range validity** (the paper's argument at
`line:median-compute` / `prop:acs-nonoverlap`): if `m` is a median of the
values of a list of (validator, value) pairs with at least `2f + 1`
entries of which at most `f` are Byzantine-attributed, then some correct
entry has value `≤ m` and some correct entry has value `≥ m`.

The pigeonhole: at least `⌈(2f+1)/2⌉ = f + 1` entries have value `≤ m`
(resp. `≥ m`); at most `f` entries are Byzantine; so a correct entry
remains on each side. -/
theorem IsMedian.between_correct {node α : Type} [LinearOrder α]
    (is_byz : node → Bool) {l : List (node × α)} {m : α} {f : Nat}
    (hmed : IsMedian m (l.map Prod.snd))
    (hlen : 2 * f + 1 ≤ l.length)
    (hbyz : l.countP (fun p => is_byz p.1) ≤ f) :
    (∃ p ∈ l, is_byz p.1 = false ∧ p.2 ≤ m) ∧
    (∃ p ∈ l, is_byz p.1 = false ∧ m ≤ p.2) := by
  obtain ⟨hlow, hhigh⟩ := hmed
  rw [List.length_map] at hlow hhigh
  rw [List.countP_map] at hlow hhigh
  constructor
  · -- Lower side: ≥ f + 1 entries with value ≤ m, ≤ f Byzantine.
    by_contra hno
    push_neg at hno
    have hmono : l.countP ((fun x => decide (x ≤ m)) ∘ Prod.snd) ≤
        l.countP (fun p => is_byz p.1) := by
      apply List.countP_mono_left
      intro p hp hple
      simp only [Function.comp_apply, decide_eq_true_eq] at hple
      have := hno p hp
      cases hbp : is_byz p.1 with
      | true => rfl
      | false => exact absurd hple (by simpa [hbp] using this)
    omega
  · -- Upper side: symmetric.
    by_contra hno
    push_neg at hno
    have hmono : l.countP ((fun x => decide (m ≤ x)) ∘ Prod.snd) ≤
        l.countP (fun p => is_byz p.1) := by
      apply List.countP_mono_left
      intro p hp hple
      simp only [Function.comp_apply, decide_eq_true_eq] at hple
      have := hno p hp
      cases hbp : is_byz p.1 with
      | true => rfl
      | false => exact absurd hple (by simpa [hbp] using this)
    omega

/-! ## The concrete sorted-middle median -/

/-- The lower median: the element at (0-based) position `⌊(n−1)/2⌋` of the
sorted list — the value `median(·)` of `line:median-compute` computes for
an odd-sized set, and the smaller of the two middle order statistics for
an even-sized one. -/
def lowerMedian {α : Type} [LinearOrder α] (vals : List α) (h : vals ≠ []) : α :=
  (vals.mergeSort (fun a b => decide (a ≤ b)))[(vals.length - 1) / 2]'(by
    have hlen := List.length_mergeSort (le := fun a b : α => decide (a ≤ b)) (l := vals)
    have : 0 < vals.length := List.length_pos_iff.mpr h
    omega)

/-- The sorted-middle median satisfies the abstract median property. -/
theorem lowerMedian_isMedian {α : Type} [LinearOrder α]
    (vals : List α) (h : vals ≠ []) : IsMedian (lowerMedian vals h) vals := by
  classical
  set le := fun a b : α => decide (a ≤ b) with hle
  set s := vals.mergeSort le with hs
  have hperm : s.Perm vals := List.mergeSort_perm vals le
  have hlen : s.length = vals.length := hperm.length_eq
  have hpos : 0 < vals.length := List.length_pos_iff.mpr h
  set n := vals.length with hn
  set k := (n - 1) / 2 with hk
  have hkn : k < n := by omega
  -- Sortedness of `s`, in getElem form.
  have hpair : List.Pairwise (fun a b => le a b = true) s :=
    List.pairwise_mergeSort
      (fun a b c hab hbc => by
        simp only [hle, decide_eq_true_eq] at *; exact le_trans hab hbc)
      (fun a b => by simp only [hle]; simpa using le_total a b)
      vals
  have hmono : ∀ (i j : Nat) (hi : i < s.length) (hj : j < s.length),
      i ≤ j → s[i] ≤ s[j] := by
    intro i j hi hj hij
    rcases Nat.lt_or_ge i j with hlt | hge
    · have := (List.pairwise_iff_getElem.mp hpair) i j hi hj hlt
      simpa [hle, decide_eq_true_eq] using this
    · have : i = j := by omega
      subst this; exact le_refl _
  have hm : lowerMedian vals h = s[k]'(by omega) := rfl
  -- Count on the sorted list, then transfer through the permutation.
  have hcount_le : k + 1 ≤ s.countP (fun x => decide (x ≤ lowerMedian vals h)) := by
    -- The first k+1 elements are ≤ s[k].
    have hsplit := List.countP_append
      (p := fun x => decide (x ≤ lowerMedian vals h))
      (l₁ := s.take (k + 1)) (l₂ := s.drop (k + 1))
    rw [List.take_append_drop] at hsplit
    have htake_all : (s.take (k + 1)).countP
        (fun x => decide (x ≤ lowerMedian vals h)) = (s.take (k + 1)).length := by
      rw [List.countP_eq_length]
      intro a ha
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp ha
      have hilen : i < s.length := by
        have := hi; simp only [List.length_take] at this; omega
      have : (s.take (k + 1))[i]'hi = s[i]'hilen := List.getElem_take
      rw [this] at hgi
      subst hgi
      have hik : i ≤ k := by
        have := hi; simp only [List.length_take] at this; omega
      simp only [decide_eq_true_eq, hm]
      exact hmono i k hilen (by omega) hik
    have htake_len : (s.take (k + 1)).length = k + 1 := by
      simp only [List.length_take]; omega
    omega
  have hcount_ge : n - k ≤ s.countP (fun x => decide (lowerMedian vals h ≤ x)) := by
    -- The elements from position k on are ≥ s[k].
    have hsplit := List.countP_append
      (p := fun x => decide (lowerMedian vals h ≤ x))
      (l₁ := s.take k) (l₂ := s.drop k)
    rw [List.take_append_drop] at hsplit
    have hdrop_all : (s.drop k).countP
        (fun x => decide (lowerMedian vals h ≤ x)) = (s.drop k).length := by
      rw [List.countP_eq_length]
      intro a ha
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp ha
      have hilen : k + i < s.length := by
        have := hi; simp only [List.length_drop] at this; omega
      have : (s.drop k)[i]'hi = s[k + i]'hilen := List.getElem_drop
      rw [this] at hgi
      subst hgi
      simp only [decide_eq_true_eq, hm]
      exact hmono k (k + i) (by omega) hilen (by omega)
    have hdrop_len : (s.drop k).length = n - k := by
      simp only [List.length_drop]; omega
    omega
  -- Transfer counts from `s` to `vals` and close with arithmetic.
  constructor
  · have := hperm.countP_eq (fun x => decide (x ≤ lowerMedian vals h))
    omega
  · have := hperm.countP_eq (fun x => decide (lowerMedian vals h ≤ x))
    omega

/-- **The packaged median lemma** cited by the ACS-decide oracle action of
[`Conductor.lean`](./Conductor.lean): the sorted-middle median of the
values of a decided ACS set (≥ `2f+1` pairs, ≤ `f` Byzantine-attributed —
the quantitative half of ACS validity, `mod:acs`) is bracketed by two
correct entries' values. -/
theorem lowerMedian_between_correct {node α : Type} [LinearOrder α]
    (is_byz : node → Bool) {l : List (node × α)} {f : Nat}
    (h : l.map Prod.snd ≠ [])
    (hlen : 2 * f + 1 ≤ l.length)
    (hbyz : l.countP (fun p => is_byz p.1) ≤ f) :
    (∃ p ∈ l, is_byz p.1 = false ∧ p.2 ≤ lowerMedian (l.map Prod.snd) h) ∧
    (∃ p ∈ l, is_byz p.1 = false ∧ lowerMedian (l.map Prod.snd) h ≤ p.2) :=
  IsMedian.between_correct is_byz (lowerMedian_isMedian _ h) hlen hbyz

end Cadence
