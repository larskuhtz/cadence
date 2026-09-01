import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `vote`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `vote` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus vote <property> by <tac>` lines
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

/- Manual discharge of the one VC the SMT pipeline cannot solve
automatically: `vote` preserves `fb_neg_no_pos_quorum`. The proof applies
`supermajorities_intersect_in_greater_than_third` once — to the recorded
witness quorum (`local_fb_neg_qv`) and the claimed post-state vote
supermajority — and closes with `fb_neg_qv_no_pos_quorum`; against `vote`'s
bulk signature update, cvc5's e-matching diverges instead of finding this
single instantiation. The `#prove_action` below consumes this cell as-is
after a statement check. -/
#prove_vc Chorus vote fb_neg_no_pos_quorum by
  unveil_local
  intro hbyz_i _hphase hvoted hne1 hne2 hne3 hnie R J M hbyz_R hfbneg x hsup
  inv_have hsig_voted := vote_sig_pos_implies_voted
  inv_have hcast_voted := vote_cast_implies_voted
  inv_have hwitness := fb_neg_sig_has_witness
  inv_have hqv_backed := fb_neg_qv_backed
  inv_have hqv_no_pos := fb_neg_qv_no_pos_quorum
  clear hinv
  -- The voter `i` has no pre-state vote signatures: it has not voted yet.
  have hno_sig_i : ∀ j m, st.msg_vote_pos_sig i j m = false := by
    intro j m
    cases hb : st.msg_vote_pos_sig i j m with
    | false => rfl
    | true =>
      have hv := hsig_voted i j m hbyz_i hb
      rw [hvoted] at hv
      simp at hv
  -- Pre-state no-equivocation, from the post-state hypotheses: pre-state
  -- signatures belong to validators other than `i`, whose rows the update
  -- leaves unchanged.
  have hne1' : ∀ r j m1 m2, st.msg_vote_pos_sig r j m1 = true →
      st.msg_vote_pos_sig r j m2 = true → m1 = m2 := by
    intro r j m1 m2 h1 h2
    have hir : ¬ (i = r) := by
      rintro rfl
      rw [hno_sig_i] at h1
      simp at h1
    exact hne1 r j m1 m2 (by rw [if_neg hir]; exact h1) (by rw [if_neg hir]; exact h2)
  have hne2' : ∀ r j m, st.msg_vote_pos_sig r j m = true →
      st.msg_vote_neg_sig r j = false := by
    intro r j m h1
    have hir : ¬ (i = r) := by
      rintro rfl
      rw [hno_sig_i] at h1
      simp at h1
    have hn := hne2 r j m (by rw [if_neg hir]; exact h1)
    rw [if_neg hir] at hn
    simpa using hn
  -- The recorded witness quorum of R's negative fallback entry.
  obtain ⟨qv, hqv⟩ := hwitness R J hbyz_R hfbneg
  obtain ⟨hqv_sup, hqv_cast⟩ := hqv_backed R J qv hbyz_R hqv
  -- `i` is not in `qv`: its members had broadcast votes, `i` has not voted.
  have hi_not_qv : ByzNodeSet.member i qv = false := by
    cases hb : ByzNodeSet.member i qv with
    | false => rfl
    | true =>
      have hv := hcast_voted i hbyz_i (hqv_cast i hb)
      rw [hvoted] at hv
      simp at hv
  -- Intersect `qv` with the claimed post-state supermajority `x`.
  obtain ⟨t, ht_gtt, ht_mem⟩ :=
    nset.supermajorities_intersect_in_greater_than_third qv x hqv_sup hsup
  -- The witness invariant yields a member of `t` with no pre-state signature.
  -- `no_invalid_encoding` passes through unadapted: `vote` leaves the
  -- proposer-signature relation untouched, so the post-state hypothesis is
  -- already the pre-state fact.
  obtain ⟨a, ha_t, ha_nosig⟩ := hqv_no_pos hne1' hne2' hne3 hnie R J qv t M hbyz_R hqv ht_gtt
  obtain ⟨ha_qv, ha_x⟩ := ht_mem a ha_t
  have ha_sig_false : st.msg_vote_pos_sig a J M = false := ha_nosig ha_qv
  -- `a ≠ i` (it is in `qv`), so its post-state row equals its pre-state row.
  have hai : ¬ (i = a) := by
    rintro rfl
    rw [hi_not_qv] at ha_qv
    simp at ha_qv
  refine ⟨a, ha_x, ?_⟩
  rw [if_neg hai]
  simp [ha_sig_false]

#prove_action Chorus vote

end Chorus.Proofs
