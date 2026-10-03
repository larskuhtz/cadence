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
the first-order fragment its solver sees. So `acs_decide` takes the
consequence as a `require` with an explicit witness pair `(r1, s1)`, a
correct validator's pair of a correct decider's set at or below the decided
first slot ([Conductor.lean](Conductor.lean)). That `require` is a **stated
bridge**: it is not derived inside the model. This file proves the other
half of a bridge, that it removes no behaviour of a correct ACS:

> **`acs_median_bracket`** — for every ACS meeting the contract
> ([Interfaces.lean](Interfaces.lean) `ACSSafety`, `ACSTemporal`), and a
> system with at most `f` Byzantine validators, the median of a correct
> decider's set is bracketed from below and from above by pairs of correct
> validators in that set.

So whenever the handler's first slot *is* the median, witnesses meeting the
`require` exist.

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

The lower half is what `acs_decide`'s `require` asks of its witnesses
`(r1, s1)` when the decided first slot is the median. -/
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

end Cadence

/-! ## The pinned trust base -/

/--
info: 'Cadence.acs_median_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.acs_median_bracket
