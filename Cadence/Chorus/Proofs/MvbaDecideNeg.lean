import Cadence.Chorus

/-! # `Chorus` proofs — action `mvba_decide_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `mvba_decide_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus mvba_decide_neg <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path). -/

open Veil Chorus

set_option veil.smt.trust false
-- Mirror Chorus.lean's elaboration budgets (the 97-conjunct clump needs them).
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
-- Proof cache: consume entries earlier solves stored (kernel-replayed on
-- hit, `veil.cache.kernelReplay`); store fresh solves for the next rebuild.
set_option veil.cache.proofs true
-- A kernel-replay hit consumes a manual `#prove_vc … by <tac>` cell at the
-- command level and never elaborates the `by` suffix; the unreachable-/
-- unused-tactic linters would flag that (by design here).
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Chorus.Proofs


theorem mvba_decide_neg_commitqc_pos_mvba_neg_excl (ρ : Type) (σ : Type) (slot : Type)
    [slot_dec_eq : DecidableEq.{1} slot] [slot_inhabited : Inhabited.{1} slot] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (nodeset : Type)
    [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset] (merkle_root : Type)
    [merkle_root_dec_eq : DecidableEq.{1} merkle_root] [merkle_root_inhabited : Inhabited.{1} merkle_root]
    [nset : ByzNodeSet node nodeset] (Phase : Type) [Phase_dec_eq : DecidableEq.{1} Phase]
    [Phase_inhabited : Inhabited.{1} Phase] [Phase_Enum : @Phase_EnumClass Phase] (PathChoice : Type)
    [PathChoice_dec_eq : DecidableEq.{1} PathChoice] [PathChoice_inhabited : Inhabited.{1} PathChoice]
    [PathChoice_Enum : @PathChoice_EnumClass PathChoice] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain slot node nodeset merkle_root Phase PathChoice __veil_f)
          (State.Label.toCodomain slot node nodeset merkle_root Phase PathChoice __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain slot node nodeset merkle_root Phase PathChoice __veil_f)
          (State.Label.toCodomain slot node nodeset merkle_root Phase PathChoice __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory slot node nodeset merkle_root Phase PathChoice) ρ]
    [mvba_decide_neg_dec_0 :
      delta% @Chorus.mvba_decide_neg._veil_dec_type_0 χ slot node nodeset merkle_root Phase PathChoice nset χ_rep]
    [mvba_decide_neg_dec_1 :
      delta% @Chorus.mvba_decide_neg._veil_dec_type_1 node χ nodeset nset slot merkle_root Phase PathChoice χ_rep]
    [mvba_decide_neg_dec_2 :
      delta% @Chorus.mvba_decide_neg._veil_dec_type_2 node χ merkle_root slot nodeset Phase PathChoice χ_rep] :
    ∀ (j : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@mvba_decide_neg.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub
          mvba_decide_neg_dec_0 mvba_decide_neg_dec_1 mvba_decide_neg_dec_2 j)
        (@Assumptions ρ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum ρ_sub)
        (@Invariants ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@commitqc_pos_mvba_neg_excl ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hphase hcompl hprop hinvoked hev hnodec J M hqc
  refine ⟨?_, ?_⟩
  · intro hjJ
    subst hjJ
    rcases hev with ⟨Qn, hQn_sup, hQn⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
    · obtain ⟨Qm, hQm_sup, hQm⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j M hqc
      obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qm Qn hQm_sup hQn_sup
      have hb_hon' : ByzNodeSet.is_byz b = false := by simpa using hb_hon
      have hx := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b j M hb_hon' (hQm b (by simpa using hb1))
      have hy := hQn b (by simpa using hb2)
      rw [hx] at hy; simp at hy
    · obtain ⟨Qc, hQc_sup, hQc⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j M hqc
      obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
      have hc_hon' : ByzNodeSet.is_byz c = false := by simpa using hc_hon
      have hcf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c hc_hon' (hQc c (by simpa using hc1)).2
      have hy := hqf c (by simpa using hc2)
      rw [hcf] at hy; simp at hy
  · exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 J M hqc


theorem mvba_decide_neg_inclusion_no_mvba_neg (ρ : Type) (σ : Type) (slot : Type) [slot_dec_eq : DecidableEq.{1} slot]
    [slot_inhabited : Inhabited.{1} slot] (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset]
    [nodeset_inhabited : Inhabited.{1} nodeset] (merkle_root : Type) [merkle_root_dec_eq : DecidableEq.{1} merkle_root]
    [merkle_root_inhabited : Inhabited.{1} merkle_root] [nset : ByzNodeSet node nodeset] (Phase : Type)
    [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase] [Phase_Enum : @Phase_EnumClass Phase]
    (PathChoice : Type) [PathChoice_dec_eq : DecidableEq.{1} PathChoice]
    [PathChoice_inhabited : Inhabited.{1} PathChoice] [PathChoice_Enum : @PathChoice_EnumClass PathChoice]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain slot node nodeset merkle_root Phase PathChoice __veil_f)
          (State.Label.toCodomain slot node nodeset merkle_root Phase PathChoice __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain slot node nodeset merkle_root Phase PathChoice __veil_f)
          (State.Label.toCodomain slot node nodeset merkle_root Phase PathChoice __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory slot node nodeset merkle_root Phase PathChoice) ρ]
    [mvba_decide_neg_dec_0 :
      delta% @Chorus.mvba_decide_neg._veil_dec_type_0 χ slot node nodeset merkle_root Phase PathChoice nset χ_rep]
    [mvba_decide_neg_dec_1 :
      delta% @Chorus.mvba_decide_neg._veil_dec_type_1 node χ nodeset nset slot merkle_root Phase PathChoice χ_rep]
    [mvba_decide_neg_dec_2 :
      delta% @Chorus.mvba_decide_neg._veil_dec_type_2 node χ merkle_root slot nodeset Phase PathChoice χ_rep] :
    ∀ (j : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@mvba_decide_neg.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub
          mvba_decide_neg_dec_0 mvba_decide_neg_dec_1 mvba_decide_neg_dec_2 j)
        (@Assumptions ρ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum ρ_sub)
        (@Invariants ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@inclusion_no_mvba_neg ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hphase hcompl hprop hinvoked hev hnodec J M hbyzJ hpropJ hall hwe
  refine ⟨?_, ?_⟩
  · intro hjJ
    subst hjJ
    rcases hev with ⟨Qn, hQn_sup, hQn⟩ | ⟨harm, -⟩
    · have hQn_gtt := nset.supermajority_greater_than_third Qn hQn_sup
      obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest Qn hQn_gtt
      have ha_hon' : ByzNodeSet.is_byz a = false := by simpa using ha_hon
      have hx := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j a M hbyzJ hpropJ hall hwe ha_hon'
      have hy := hQn a (by simpa using ha_mem)
      rw [hx] at hy; simp at hy
    · rcases harm with ⟨qn, hqn_gtt, hqn⟩ | ⟨m1, m2, hm12, hp1, hp2⟩
      · obtain ⟨a, ha_mem, ha_hon⟩ := nset.greater_than_third_one_honest qn hqn_gtt
        have ha_hon' : ByzNodeSet.is_byz a = false := by simpa using ha_hon
        have hx := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j a M hbyzJ hpropJ hall hwe ha_hon'
        have hy := hqn a (by simpa using ha_mem)
        rw [hx] at hy; simp at hy
      · exact hm12 (hinv.2.2.2.2.2.2.2.2.2.1 j m1 m2 hbyzJ hp1 hp2)
  · exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 J M hbyzJ hpropJ hall hwe

#prove_action Chorus mvba_decide_neg

end Chorus.Proofs
