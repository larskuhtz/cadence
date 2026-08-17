import Cadence.Chorus

/-! # `Chorus` proofs — action `mvba_decide_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `mvba_decide_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus mvba_decide_pos <property> by <tac>` lines
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


theorem mvba_decide_pos_commitqc_pos_mvba_consistent (ρ : Type) (σ : Type) (slot : Type)
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
    [mvba_decide_pos_dec_0 :
      delta% @Chorus.mvba_decide_pos._veil_dec_type_0 χ slot node nodeset merkle_root Phase PathChoice nset χ_rep]
    [mvba_decide_pos_dec_1 :
      delta% @Chorus.mvba_decide_pos._veil_dec_type_1 node merkle_root χ nodeset nset slot Phase PathChoice χ_rep]
    [mvba_decide_pos_dec_2 :
      delta% @Chorus.mvba_decide_pos._veil_dec_type_2 node merkle_root χ slot nodeset Phase PathChoice χ_rep] :
    ∀ (j : node) (m : merkle_root),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@mvba_decide_pos.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub
          mvba_decide_pos_dec_0 mvba_decide_pos_dec_1 mvba_decide_pos_dec_2 j m)
        (@Assumptions ρ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum ρ_sub)
        (@Invariants ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@commitqc_pos_mvba_consistent ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hphase hcompl hprop hinvoked hev hagree hnneg J M1 M2 hqc hmv
  by_cases hnew : j = J ∧ m = M2
  · obtain ⟨rfl, rfl⟩ := hnew
    rcases hev with ⟨Q2, hQ2_sup, hQ2⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
    · obtain ⟨Qm, hQm_sup, hQm⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j M1 hqc
      obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Qm Q2 hQm_sup hQ2_sup
      have hb_hon' : ByzNodeSet.is_byz b = false := by simpa using hb_hon
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b j M1 m hb_hon' (hQm b (by simpa using hb1)) (hQ2 b (by simpa using hb2))
    · exfalso
      obtain ⟨Qc, hQc_sup, hQc⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j M1 hqc
      obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
      have hc_hon' : ByzNodeSet.is_byz c = false := by simpa using hc_hon
      have hcf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c hc_hon' (hQc c (by simpa using hc1)).2
      have hy := hqf c (by simpa using hc2)
      rw [hcf] at hy; simp at hy
  · have hmv' : st.mvba_decided_pos J M2 = true := hmv (fun h1 h2 => hnew ⟨h1, h2⟩)
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 J M1 M2 hqc hmv'


theorem mvba_decide_pos_commitqc_neg_mvba_pos_excl (ρ : Type) (σ : Type) (slot : Type)
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
    [mvba_decide_pos_dec_0 :
      delta% @Chorus.mvba_decide_pos._veil_dec_type_0 χ slot node nodeset merkle_root Phase PathChoice nset χ_rep]
    [mvba_decide_pos_dec_1 :
      delta% @Chorus.mvba_decide_pos._veil_dec_type_1 node merkle_root χ nodeset nset slot Phase PathChoice χ_rep]
    [mvba_decide_pos_dec_2 :
      delta% @Chorus.mvba_decide_pos._veil_dec_type_2 node merkle_root χ slot nodeset Phase PathChoice χ_rep] :
    ∀ (j : node) (m : merkle_root),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@mvba_decide_pos.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub
          mvba_decide_pos_dec_0 mvba_decide_pos_dec_1 mvba_decide_pos_dec_2 j m)
        (@Assumptions ρ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum ρ_sub)
        (@Invariants ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@commitqc_neg_mvba_pos_excl ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hphase hcompl hprop hinvoked hev hagree hnneg J M hqc
  refine ⟨?_, ?_⟩
  · intro hjJ hmM
    subst hjJ; subst hmM
    rcases hev with ⟨Q2, hQ2_sup, hQ2⟩ | ⟨-, ⟨qf, hqf_sup, hqf⟩⟩
    · obtain ⟨Qn, hQn_sup, hQn⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hqc
      obtain ⟨b, hb1, hb2, hb_hon⟩ := nset.supermajorities_intersect_in_honest Q2 Qn hQ2_sup hQn_sup
      have hb_hon' : ByzNodeSet.is_byz b = false := by simpa using hb_hon
      have hx := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b j m hb_hon' (hQ2 b (by simpa using hb1))
      have hy := hQn b (by simpa using hb2)
      rw [hx] at hy; simp at hy
    · obtain ⟨Qc, hQc_sup, hQc⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hqc
      obtain ⟨c, hc1, hc2, hc_hon⟩ := nset.supermajorities_intersect_in_honest Qc qf hQc_sup hqf_sup
      have hc_hon' : ByzNodeSet.is_byz c = false := by simpa using hc_hon
      have hcf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c hc_hon' (hQc c (by simpa using hc1)).2
      have hy := hqf c (by simpa using hc2)
      rw [hcf] at hy; simp at hy
  · exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 J M hqc

#prove_action Chorus mvba_decide_pos

end Chorus.Proofs
