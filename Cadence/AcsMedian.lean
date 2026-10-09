import Cadence.Interfaces
import Cadence.Windows
import Mathlib.Data.Fintype.Card

/-! # The ACS median bracket, from the contract

The Conductor reads a window's first slot off its ACS decision as the
**median** of the decided slots (Algorithm 7, line 48
(`line:median-compute`)), and every safety property that separates windows
rests on one consequence: the median lies above some *correct* validator's
proposal. The paper argues it in one sentence, "since at most `f` of the
`2f + 1` decided values are faulty, the median lies between the smallest and
largest honest estimate" (the paragraph before Algorithm 7
(`algorithm:conductor`)).

The Conductor model does not compute the median, and cardinality is outside
the first-order fragment its solver sees. So the model leaves the first slot
a validator computes abstract, `acs_first st i`, and takes the consequence
as an assumption on it, `[acs_first_bracket]`: two correct validators'
pairs of a correct decider's set, one at or below the first slot and one at
or above it ([Conductor.lean](Conductor.lean)). This file proves that the
paper's median meets it:

> **`acs_median_bracket`** — for every ACS meeting the contract
> ([Interfaces.lean](Interfaces.lean) `ACSSafety`, `ACSTemporal`), and a
> system with at most `f` Byzantine validators, the median of a correct
> decider's set is bracketed from below and from above by pairs of correct
> validators in that set.

With the median of a decided set as a function of the set alone
(`medianOf`), the model's two assumptions on its first slot are theorems
(`lowerMedian_first_assumptions`).

**What it needs from the contract.** Module 4 (`mod:acs`)'s Validity bounds
the size of a decided set, `|set| ≥ 2f + 1`, but not the number of pairs one
validator contributes. Under that Validity alone the lemma is false: `2f + 1`
pairs of one Byzantine validator are a valid decision, and their median is
the adversary's choice. The contract therefore carries the per-validator
bound as `ACSSafety.decided_unique`, and `ACSTemporal.validity_quantitative`
counts distinct validators (P16, [PaperAlignment.md](../docs/PaperAlignment.md)
§6; F18, [ConductorBounds.md](../docs/ConductorBounds.md) §7). With both,
the decided set's validators are distinct, so at most `f` of its pairs are
Byzantine, which is the hypothesis of [Windows.lean](Windows.lean)'s median
lemma.

**The fault bound** is the system's: at most `f` Byzantine validators, with
`f` the contract's `fault_bound` (`hfault`). It is a premise about the
execution, as `hbyz` is for Chorus's quorum family, and no class states it.

**The order.** The lemma is stated over a `LinearOrder` on slots, the order
[Windows.lean](Windows.lean) computes medians in. The Conductor's slot order
is a total order, so it is one. -/

namespace Cadence

section MedianBracket

variable {validator slot state time message : Type} [LinearOrder slot]
  [TotalOrder time] [Add time] {byz : validator → Prop}
  [S : ACSSafety validator slot state byz]
  [T : ACSTemporal validator slot state time message byz]

omit [LinearOrder slot] in
/-- In a correct decider's set, no validator appears twice: by
`decided_unique` a validator's pair is determined by the validator. -/
theorem acs_decided_validators_nodup {st : state} (hr : S.reachable st)
    {i : validator} (hi : ¬ byz i)
    {l : List (validator × slot)} (hnd : l.Nodup)
    (hl : ∀ p s, (p, s) ∈ l ↔ S.decided st i p s) :
    (l.map Prod.fst).Nodup := by
  refine List.Nodup.map_on ?_ hnd
  rintro ⟨p, s⟩ hx ⟨p', s'⟩ hy (hpp : p = p')
  subst hpp
  have := S.decided_unique st hr i p s s' hi ((hl p s).mp hx) ((hl p s').mp hy)
  rw [this]

/-- **The median bracket.** At a reachable state, let `l` enumerate a
correct validator's decided set without repetition. If at most
`fault_bound` validators are Byzantine, the set is non-empty and its lower
median lies between the slots of two pairs of correct validators in it:
one at or below, one at or above.

The two halves are what `[acs_first_bracket]` asks of the first slot
when it is the median (`medianOf_bracket`). -/
theorem acs_median_bracket [Fintype validator] [DecidablePred byz]
    (hfault : (Finset.univ.filter byz).card ≤ T.fault_bound)
    {st : state} (hr : S.reachable st) {i : validator} (hi : ¬ byz i)
    (hd : S.has_decided st i)
    {l : List (validator × slot)} (hnd : l.Nodup)
    (hl : ∀ p s, (p, s) ∈ l ↔ S.decided st i p s) :
    ∃ h : l.map Prod.snd ≠ [],
      (∃ r s, ¬ byz r ∧ S.decided st i r s ∧ s ≤ lowerMedian (l.map Prod.snd) h) ∧
      (∃ r s, ¬ byz r ∧ S.decided st i r s ∧ lowerMedian (l.map Prod.snd) h ≤ s) := by
  classical
  have hkeys := acs_decided_validators_nodup hr hi hnd hl
  -- At least `2f + 1` entries: the distinct validators of `validity_quantitative`.
  have hlen : 2 * T.fault_bound + 1 ≤ l.length := by
    obtain ⟨g, hinj, hg⟩ := T.validity_quantitative st hr i hi hd
    have hsub : Finset.univ.image g ⊆ (l.map Prod.fst).toFinset := by
      intro v hv
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨s, hs⟩ := hg k
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(g k, s), (hl _ _).mpr hs, rfl⟩)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
      List.toFinset_card_of_nodup hkeys, List.length_map] at hcard
    exact hcard
  -- At most `f` Byzantine entries: their validators are distinct and Byzantine.
  have hbyz : l.countP (fun p => decide (byz p.1)) ≤ T.fault_bound := by
    have hc : l.countP (fun p => decide (byz p.1)) =
        ((l.map Prod.fst).filter (fun v => decide (byz v))).length := by
      rw [← List.countP_eq_length_filter, List.countP_map]
      rfl
    rw [hc]
    have hfnd : ((l.map Prod.fst).filter (fun v => decide (byz v))).Nodup := hkeys.filter _
    have hsub : ((l.map Prod.fst).filter (fun v => decide (byz v))).toFinset ⊆
        Finset.univ.filter byz := by
      intro v hv
      have := List.mem_toFinset.mp hv
      simp only [List.mem_filter, decide_eq_true_eq] at this
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, this.2⟩
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hfnd] at this
    omega
  have hne : l.map Prod.snd ≠ [] := by
    intro h
    have : l = [] := List.map_eq_nil_iff.mp h
    rw [this] at hlen
    simp at hlen
  obtain ⟨⟨p, hp, hpc, hple⟩, ⟨q, hq, hqc, hqle⟩⟩ :=
    lowerMedian_between_correct (fun v => decide (byz v)) hne hlen hbyz
  refine ⟨hne, ⟨p.1, p.2, ?_, (hl _ _).mp hp, hple⟩, ⟨q.1, q.2, ?_, (hl _ _).mp hq, hqle⟩⟩
  · simpa using hpc
  · simpa using hqc

end MedianBracket

/-! ## The first slot the Conductor computes: the lower median

The Conductor model leaves the first slot abstract, `acs_first st i`, and
assumes two things of it ([Conductor.lean](Conductor.lean)): it is a
function of the decided set alone (`[acs_first_local]`), and two correct
pairs of the decider's set bracket it (`[acs_first_bracket]`). Here the
first slot is the paper's, the lower median of the decided slots (Algorithm
7, line 48 (`line:median-compute`)), and both assumptions are theorems. -/

section MedianFirst

open Classical

variable {validator slot state time message : Type} [LinearOrder slot] [Inhabited slot]
  [Fintype validator]

/-- The decided set, as a list of pairs: for each validator in a fixed
enumeration, its pair, if it has one. A function of the relation alone. -/
noncomputable def decidedPairs (D : validator → slot → Prop) : List (validator × slot) :=
  (Finset.univ : Finset validator).toList.filterMap fun p =>
    if h : ∃ s, D p s then some (p, h.choose) else none

/-- **The lower median of a decided set** (Algorithm 7, line 48
(`line:median-compute`)), a function of the set alone. An empty set has no
median; its value there is never read. -/
noncomputable def medianOf (D : validator → slot → Prop) : slot :=
  if h : (decidedPairs D).map Prod.snd ≠ [] then lowerMedian _ h else default

omit [LinearOrder slot] [Inhabited slot] in
theorem decidedPairs_nodup (D : validator → slot → Prop) : (decidedPairs D).Nodup := by
  refine List.Nodup.filterMap ?_ (Finset.nodup_toList _)
  intro a a' b ha ha'
  by_cases h : ∃ s, D a s <;> by_cases h' : ∃ s, D a' s <;> simp_all [eq_comm]

omit [LinearOrder slot] [Inhabited slot] in
theorem mem_decidedPairs {D : validator → slot → Prop}
    (huniq : ∀ p s s', D p s → D p s' → s = s') (p : validator) (s : slot) :
    (p, s) ∈ decidedPairs D ↔ D p s := by
  simp only [decidedPairs, List.mem_filterMap, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    by_cases h : ∃ s, D q s
    · simp only [h, dite_true, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      exact h.choose_spec
    · simp [h] at hq
  · intro hs
    have h : ∃ s, D p s := ⟨s, hs⟩
    exact ⟨p, by simp [h, huniq p _ _ h.choose_spec hs]⟩

omit [Inhabited slot] in
/-- The lower median is one of the values. -/
theorem lowerMedian_mem (vals : List slot) (h : vals ≠ []) : lowerMedian vals h ∈ vals :=
  (List.mergeSort_perm vals _).subset (List.getElem_mem _)

/-- **A set whose slots are all `c` has median `c`**: the median of a
non-empty set is one of its slots. -/
theorem medianOf_eq_of_const {D : validator → slot → Prop} {c : slot}
    (hc : ∀ p s, D p s → s = c) (hne : ∃ p s, D p s) : medianOf D = c := by
  obtain ⟨p, s, hps⟩ := hne
  have hmem : ∀ x ∈ (decidedPairs D).map Prod.snd, x = c := by
    intro x hx
    obtain ⟨⟨q, y⟩, hq, rfl⟩ := List.mem_map.1 hx
    simp only [decidedPairs, List.mem_filterMap] at hq
    obtain ⟨q', -, hq'⟩ := hq
    by_cases h : ∃ s, D q' s
    · simp only [h, dite_true, Option.some.injEq, Prod.mk.injEq] at hq'
      obtain ⟨rfl, rfl⟩ := hq'
      exact hc _ _ h.choose_spec
    · simp [h] at hq'
  have hne : (decidedPairs D).map Prod.snd ≠ [] := by
    have h : ∃ s, D p s := ⟨s, hps⟩
    have : (p, h.choose) ∈ decidedPairs D := by
      simp only [decidedPairs, List.mem_filterMap, Finset.mem_toList, Finset.mem_univ, true_and]
      exact ⟨p, by simp [h]⟩
    exact List.ne_nil_of_mem (List.mem_map_of_mem (f := Prod.snd) this)
  simp only [medianOf, dif_pos hne]
  exact hmem _ (lowerMedian_mem _ hne)

variable [TotalOrder time] [Add time] {byz : validator → Prop}
  [S : ACSSafety validator slot state byz]

/-- `[acs_first_local]` at the lower median: two decided sets with the same
pairs have the same median, whoever holds them. -/
theorem medianOf_local {st st' : state} {i j : validator}
    (h : ∀ p s, S.decided st i p s ↔ S.decided st' j p s) :
    medianOf (S.decided st i) = medianOf (S.decided st' j) := by
  have : S.decided st i = S.decided st' j := funext fun p => funext fun s => propext (h p s)
  rw [this]

/-- `[acs_first_bracket]` at the lower median: at a reachable state, two
correct pairs of a correct decider's set bracket the median of its set, if
at most `fault_bound` validators are Byzantine. `acs_median_bracket` at
the set's enumeration. -/
theorem medianOf_bracket [T : ACSTemporal validator slot state time message byz]
    [DecidablePred byz] (hfault : (Finset.univ.filter byz).card ≤ T.fault_bound)
    {st : state} (hr : S.reachable st) {i : validator} (hi : ¬ byz i)
    (hd : S.has_decided st i) :
    (∃ r1 s1, ¬ byz r1 ∧ S.decided st i r1 s1 ∧ s1 ≤ medianOf (S.decided st i)) ∧
    (∃ r2 s2, ¬ byz r2 ∧ S.decided st i r2 s2 ∧ medianOf (S.decided st i) ≤ s2) := by
  have hl := mem_decidedPairs (D := S.decided st i)
    (fun p s s' h h' => S.decided_unique st hr i p s s' hi h h')
  obtain ⟨hne, hlo, hhi⟩ := acs_median_bracket (T := T) hfault hr hi hd
    (decidedPairs_nodup _) hl
  simp only [medianOf, dif_pos hne]
  exact ⟨hlo, hhi⟩

/-- **The lower median meets the Conductor's two assumptions on its first
slot**: it is a function of the decided set alone (`[acs_first_local]`),
and, under the fault bound, two correct pairs of a correct decider's set
bracket it (`[acs_first_bracket]`). So the paper's median (Algorithm 7,
line 48 (`line:median-compute`)) is a first-slot rule the Conductor's
theorems cover. -/
theorem lowerMedian_first_assumptions [T : ACSTemporal validator slot state time message byz]
    [DecidablePred byz] (hfault : (Finset.univ.filter byz).card ≤ T.fault_bound) :
    (∀ (st st' : state) (i j : validator),
      (∀ p s, S.decided st i p s ↔ S.decided st' j p s) →
      medianOf (S.decided st i) = medianOf (S.decided st' j)) ∧
    (∀ (st : state) (i : validator), S.reachable st ∧ ¬ byz i ∧ S.has_decided st i →
      (∃ r1 s1, ¬ byz r1 ∧ S.decided st i r1 s1 ∧ s1 ≤ medianOf (S.decided st i)) ∧
      (∃ r2 s2, ¬ byz r2 ∧ S.decided st i r2 s2 ∧ medianOf (S.decided st i) ≤ s2)) :=
  ⟨fun _ _ _ _ h => medianOf_local h,
    fun _ _ ⟨hr, hi, hd⟩ => medianOf_bracket hfault hr hi hd⟩

end MedianFirst

end Cadence

/-! ## The pinned trust base -/

/--
info: 'Cadence.acs_median_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.acs_median_bracket

/--
info: 'Cadence.lowerMedian_first_assumptions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.lowerMedian_first_assumptions
