import Cadence.Chorus

/-! # `Chorus` proofs — action `byz_sign_vote_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `byz_sign_vote_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus byz_sign_vote_pos <property> by <tac>` lines
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


theorem byz_sign_vote_pos_fb_neg_no_pos_quorum (ρ : Type) (σ : Type) (slot : Type) [slot_dec_eq : DecidableEq.{1} slot]
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
    [ρ_sub : IsSubReaderOf (@Theory slot node nodeset merkle_root Phase PathChoice) ρ] :
    ∀ (r : node) (j : node) (m : merkle_root),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@byz_sign_vote_pos.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub r j m)
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
  intro hbyz_r hchunk hne1 hne2 hne3 R J M hbyzR hfb x hsup_x
  -- Pre-state no-equivocation from the post-state hypotheses (pre-state
  -- signatures persist into the post state).
  have hne1' : ∀ a b c1 c2, st.msg_vote_pos_sig a b c1 = true →
      st.msg_vote_pos_sig a b c2 = true → c1 = c2 := by
    intro a b c1 c2 h1 h2
    exact hne1 a b c1 c2 (fun _ => h1) (fun _ => h2)
  have hne2' : ∀ a b c, st.msg_vote_pos_sig a b c = true →
      st.msg_vote_neg_sig a b = false := by
    intro a b c h1
    exact hne2 a b c (fun _ => h1)
  obtain ⟨qv, hqv⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 R J hbyzR hfb
  obtain ⟨hqv_sup, hqv_cast⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 R J qv hbyzR hqv
  have hpropJ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 R J qv hbyzR hqv
  obtain ⟨t, ht_gtt, ht⟩ :=
    nset.supermajorities_intersect_in_greater_than_third qv x hqv_sup hsup_x
  obtain ⟨b, hb_t, hb_nosig⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hne1' hne2' hne3 R J qv t M hbyzR hqv ht_gtt
  obtain ⟨hb_qv, hb_x⟩ := ht b (by simpa using hb_t)
  have hb_qv' : ByzNodeSet.member b qv = true := by simpa using hb_qv
  have hb_sig_false : st.msg_vote_pos_sig b J M = false := hb_nosig hb_qv'
  refine ⟨b, by simpa using hb_x, ?_, hb_sig_false⟩
  -- b is not the newly signed tuple: if it were, b (= r) had already cast a
  -- complete vote, so under no-equivocation its pre-state entry for J is
  -- exactly (pos, m) — contradicting the absent pre-state signature — or a
  -- negative entry — contradicting the new positive signature.
  intro hrb hjJ hmM
  subst hrb; subst hjJ; subst hmM
  have hcast_r := hqv_cast r hb_qv'
  rcases hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r j hcast_r hpropJ with ⟨M0, hM0⟩ | hneg
  · have hM0m : M0 = m := hne1 r j M0 m (fun _ => hM0) (fun h => absurd rfl (h rfl rfl))
    subst hM0m
    rw [hb_sig_false] at hM0; simp at hM0
  · have hx2 := hne2 r j m (fun h => absurd rfl (h rfl rfl))
    rw [hx2] at hneg; simp at hneg


#prove_action Chorus byz_sign_vote_pos

end Chorus.Proofs
