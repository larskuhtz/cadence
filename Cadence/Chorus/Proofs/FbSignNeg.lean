import Cadence.Chorus

/-! # `Chorus` proofs — action `fb_sign_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `fb_sign_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus fb_sign_neg <property> by <tac>` lines
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


theorem fb_sign_neg_inclusion_no_honest_fb_neg (ρ : Type) (σ : Type) (slot : Type) [slot_dec_eq : DecidableEq.{1} slot]
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
    [fb_sign_neg_dec_0 : delta% @Chorus.fb_sign_neg._veil_dec_type_0 nodeset node nset]
    [fb_sign_neg_dec_1 :
      delta% @Chorus.fb_sign_neg._veil_dec_type_1 nodeset χ node nset slot merkle_root Phase PathChoice χ_rep]
    [fb_sign_neg_dec_2 :
      delta% @Chorus.fb_sign_neg._veil_dec_type_2 node nodeset χ merkle_root nset slot Phase PathChoice χ_rep] :
    ∀ (i : node) (j : node) (qv : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@fb_sign_neg.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub
          fb_sign_neg_dec_0 fb_sign_neg_dec_1 fb_sign_neg_dec_2 i j qv)
        (@Assumptions ρ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum ρ_sub)
        (@Invariants ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@inclusion_no_honest_fb_neg ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hbyz_i hphase hvoted hcast hpath hprop_j hsup_qv hqv_cast hguard J R M hbyzJ hpropJ hall hbyzR
  refine ⟨?_, ?_⟩
  · intro h1 h2
    subst h1; subst h2
    obtain ⟨t, ht_gtt, ht⟩ := nset.supermajority_contains_honest_greater_than_third qv hsup_qv
    have hsigs : ∀ a, ByzNodeSet.member a t = true →
        ByzNodeSet.member a qv = true ∧ st.msg_vote_pos_sig a j M = true := by
      intro a ha
      obtain ⟨ha_qv, ha_hon⟩ := ht a (by simpa using ha)
      have ha_qv' : ByzNodeSet.member a qv = true := by simpa using ha_qv
      have ha_hon' : ByzNodeSet.is_byz a = false := by simpa using ha_hon
      have ha_voted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a ha_hon' (hqv_cast a ha_qv')
      exact ⟨ha_qv', hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a j M ha_hon' hprop_j ha_voted (hall a ha_hon')⟩
    obtain ⟨xx, hxx_t, hxx_chunk⟩ := hguard M t t ht_gtt hsigs ht_gtt
    obtain ⟨-, hxx_hon⟩ := ht xx (by simpa using hxx_t)
    have hxx_hon' : ByzNodeSet.is_byz xx = false := by simpa using hxx_hon
    have hch := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 xx j M hxx_hon' (hall xx hxx_hon')
    rw [hxx_chunk] at hch; simp at hch
  · exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 J R M hbyzJ hpropJ hall hbyzR


theorem fb_sign_neg_fb_neg_qv_no_pos_quorum (ρ : Type) (σ : Type) (slot : Type) [slot_dec_eq : DecidableEq.{1} slot]
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
    [fb_sign_neg_dec_0 : delta% @Chorus.fb_sign_neg._veil_dec_type_0 nodeset node nset]
    [fb_sign_neg_dec_1 :
      delta% @Chorus.fb_sign_neg._veil_dec_type_1 nodeset χ node nset slot merkle_root Phase PathChoice χ_rep]
    [fb_sign_neg_dec_2 :
      delta% @Chorus.fb_sign_neg._veil_dec_type_2 node nodeset χ merkle_root nset slot Phase PathChoice χ_rep] :
    ∀ (i : node) (j : node) (qv : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@fb_sign_neg.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub
          fb_sign_neg_dec_0 fb_sign_neg_dec_1 fb_sign_neg_dec_2 i j qv)
        (@Assumptions ρ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum ρ_sub)
        (@Invariants ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@fb_neg_qv_no_pos_quorum ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hbyz_i hphase hvoted hcast hpath hprop_j hsup_qv hqv_cast hguard hne1 hne2 hne3
  intro R J QV q M hbyzR hqvmem hgtt_q
  by_cases hnew : i = R ∧ j = J ∧ qv = QV
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    by_cases hex : ∃ a, ByzNodeSet.member a q = true ∧
        (ByzNodeSet.member a qv = true → st.msg_vote_pos_sig a j M = false)
    · obtain ⟨a, h1, h2⟩ := hex
      exact ⟨a, h1, h2⟩
    · exfalso
      push_neg at hex
      have hq_all : ∀ a, ByzNodeSet.member a q = true →
          ByzNodeSet.member a qv = true ∧ st.msg_vote_pos_sig a j M = true := by
        intro a ha
        have h := hex a ha
        refine ⟨h.1, ?_⟩
        cases hs : st.msg_vote_pos_sig a j M with
        | true => rfl
        | false => exact absurd hs h.2
      obtain ⟨xx, hxx_q, hxx_chunk⟩ := hguard M q q hgtt_q hq_all hgtt_q
      have hch := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 xx j M (hq_all xx hxx_q).2
      rw [hxx_chunk] at hch; simp at hch
  · have hold : st.local_fb_neg_qv R J QV = true := hqvmem (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩)
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hne1 hne2 hne3 R J QV q M hbyzR hold hgtt_q


theorem fb_sign_neg_fb_neg_no_pos_quorum (ρ : Type) (σ : Type) (slot : Type) [slot_dec_eq : DecidableEq.{1} slot]
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
    [fb_sign_neg_dec_0 : delta% @Chorus.fb_sign_neg._veil_dec_type_0 nodeset node nset]
    [fb_sign_neg_dec_1 :
      delta% @Chorus.fb_sign_neg._veil_dec_type_1 nodeset χ node nset slot merkle_root Phase PathChoice χ_rep]
    [fb_sign_neg_dec_2 :
      delta% @Chorus.fb_sign_neg._veil_dec_type_2 node nodeset χ merkle_root nset slot Phase PathChoice χ_rep] :
    ∀ (i : node) (j : node) (qv : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@fb_sign_neg.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub
          fb_sign_neg_dec_0 fb_sign_neg_dec_1 fb_sign_neg_dec_2 i j qv)
        (@Assumptions ρ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum ρ_sub)
        (@Invariants ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@fb_neg_no_pos_quorum ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hbyz_i hphase hvoted hcast hpath hprop_j hsup_qv hqv_cast hguard hne1 hne2 hne3
  intro R J M hbyzR hfb x hsup_x
  by_cases hnew : i = R ∧ j = J
  · obtain ⟨rfl, rfl⟩ := hnew
    obtain ⟨t, ht_gtt, ht⟩ :=
      nset.supermajorities_intersect_in_greater_than_third qv x hsup_qv hsup_x
    by_cases hex : ∃ a, ByzNodeSet.member a t = true ∧ st.msg_vote_pos_sig a j M = false
    · obtain ⟨a, ha_t, ha_sig⟩ := hex
      obtain ⟨-, ha_x⟩ := ht a (by simpa using ha_t)
      exact ⟨a, by simpa using ha_x, ha_sig⟩
    · exfalso
      push_neg at hex
      have ht_all : ∀ a, ByzNodeSet.member a t = true →
          ByzNodeSet.member a qv = true ∧ st.msg_vote_pos_sig a j M = true := by
        intro a ha
        obtain ⟨ha_qv, -⟩ := ht a (by simpa using ha)
        refine ⟨by simpa using ha_qv, ?_⟩
        cases hs : st.msg_vote_pos_sig a j M with
        | true => rfl
        | false => exact absurd hs (hex a ha)
      obtain ⟨xx, hxx_t, hxx_chunk⟩ := hguard M t t ht_gtt ht_all ht_gtt
      have hch := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 xx j M (ht_all xx hxx_t).2
      rw [hxx_chunk] at hch; simp at hch
  · have hold : st.msg_fb_neg_sig R J = true := hfb (fun h1 h2 => hnew ⟨h1, h2⟩)
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hne1 hne2 hne3 R J M hbyzR hold x hsup_x

#prove_action Chorus fb_sign_neg

end Chorus.Proofs
