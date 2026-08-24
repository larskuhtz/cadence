import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `byz_sign_vote_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `byz_sign_vote_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus byz_sign_vote_pos <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared blocks from
`Cadence/ProofPrelude.lean` record what each of the other options is
for. -/

open Veil Chorus Veil.InvProjection

-- The no-trusted-solver rule (README.md) stays written out per proof file so
-- it remains greppable; the shared blocks below are defined and documented
-- in `Cadence/ProofPrelude.lean`.
set_option veil.smt.trust false
veil_proof_options
veil_large_clump_budgets

namespace Chorus.Proofs


#prove_vc Chorus byz_sign_vote_pos fb_neg_no_pos_quorum by
  unveil_local
  inv_have h_fb_neg_sig_has_witness := fb_neg_sig_has_witness
  inv_have h_fb_neg_qv_backed := fb_neg_qv_backed
  inv_have h_fb_neg_qv_is_proposer := fb_neg_qv_is_proposer
  inv_have h_fb_neg_qv_no_pos_quorum := fb_neg_qv_no_pos_quorum
  inv_have h_vote_cast_entries := vote_cast_entries
  intro _hbyz_r _hchunk hne1 hne2 hne3 hnie R J M hbyzR hfb x hsup_x
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
  obtain ⟨qv, hqv⟩ := h_fb_neg_sig_has_witness R J hbyzR hfb
  obtain ⟨hqv_sup, hqv_cast⟩ := h_fb_neg_qv_backed R J qv hbyzR hqv
  have hpropJ := h_fb_neg_qv_is_proposer R J qv hbyzR hqv
  obtain ⟨t, ht_gtt, ht⟩ :=
    nset.supermajorities_intersect_in_greater_than_third qv x hqv_sup hsup_x
  -- `no_invalid_encoding` passes through unadapted: this action leaves the
  -- proposer-signature relation untouched.
  obtain ⟨b, hb_t, hb_nosig⟩ :=
    h_fb_neg_qv_no_pos_quorum hne1' hne2' hne3 hnie R J qv t M hbyzR hqv ht_gtt
  obtain ⟨hb_qv, hb_x⟩ := ht b hb_t
  have hb_sig_false : st.msg_vote_pos_sig b J M = false := hb_nosig hb_qv
  refine ⟨b, hb_x, ?_, hb_sig_false⟩
  -- b is not the newly signed tuple: if it were, b (= r) had already cast a
  -- complete vote, so under no-equivocation its pre-state entry for J is
  -- exactly (pos, m) — contradicting the absent pre-state signature — or a
  -- negative entry — contradicting the new positive signature.
  rintro rfl rfl rfl
  have hcast_r := hqv_cast r hb_qv
  rcases h_vote_cast_entries r j hcast_r hpropJ with ⟨M0, hM0⟩ | hneg
  · have hM0m : M0 = m := hne1 r j M0 m (fun _ => hM0) (fun h => absurd rfl (h rfl rfl))
    subst hM0m
    rw [hb_sig_false] at hM0; simp at hM0
  · have hx2 := hne2 r j m (fun h => absurd rfl (h rfl rfl))
    rw [hx2] at hneg; simp at hneg

#prove_action Chorus byz_sign_vote_pos

end Chorus.Proofs
