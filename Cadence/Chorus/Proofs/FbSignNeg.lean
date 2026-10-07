import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `fb_sign_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `fb_sign_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus fb_sign_neg <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared blocks from
[ProofPrelude.lean](../../ProofPrelude.lean) record what each of the other options is
for. -/

open Veil Chorus

-- The no-trusted-solver rule ([README.md](../../../README.md)) stays written out per proof file so
-- it remains greppable; the shared blocks below are defined and documented
-- in [ProofPrelude.lean](../../ProofPrelude.lean).
set_option veil.smt.trust false
veil_proof_options
veil_large_clump_budgets

namespace Chorus.Proofs

/- `fb_neg_qv_no_pos_quorum` and `fb_neg_no_pos_quorum` are manual cells: the
guard reads the validator's own vote receipts, and the step from "every
member of `q` signed positive" to "`i` received that entry from every member"
needs no-equivocation per member, an instantiation cvc5 finds only at the
edge of its budget, or not at all (for the first it reports a spurious
counterexample with an empty model). `inclusion_no_honest_fb_neg` is solved
directly: the `no_invalid_encoding` invariant supplies the
signed-root-is-well-encoded bridge as an explicit premise. -/

#prove_vc Chorus fb_sign_neg fb_neg_qv_no_pos_quorum by
  unveil_local
  veil_inv_have h_old := fb_neg_qv_no_pos_quorum
  veil_inv_have h_rcv_pos := vote_rcv_pos_backed
  veil_inv_have h_rcv_neg := vote_rcv_neg_backed
  veil_inv_have h_from_local := vote_pos_from_local
  veil_inv_have h_signed := local_entry_pos_signed
  intro hbyz _hpart _hab _hph _hvoted _hcast _hpath _hprop _hsup hrcv hguard _hfresh
    hne1 hne2 hne3 hnie R J QV q M hR haux hq
  by_cases hnew : i = R ∧ j = J ∧ qv = QV
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    -- Every member of `q` in `qv` signed positive for `M`: then `i` received
    -- exactly that entry from each, which the guard forbids for a root that
    -- re-encodes, and `M` does re-encode — `q` has a correct member.
    by_contra hall
    have hall' : ∀ x, ByzNodeSet.member x q = true →
        ByzNodeSet.member x qv = true ∧ st.msg_vote_pos_sig x j M = true := by
      intro x hx
      by_contra hc
      apply hall
      refine ⟨x, hx, fun hxqv => ?_⟩
      cases h : st.msg_vote_pos_sig x j M
      · rfl
      · exact absurd ⟨hxqv, h⟩ hc
    have hrcvM : ∀ x, ByzNodeSet.member x q = true →
        ByzNodeSet.member x qv = true ∧ st.local_vote_rcv_pos i x j M = true := by
      intro x hx
      obtain ⟨hxqv, hxsig⟩ := hall' x hx
      refine ⟨hxqv, ?_⟩
      rcases hrcv x hxqv with ⟨M', hM'⟩ | hneg
      · obtain ⟨-, hsig'⟩ := h_rcv_pos i x j M' hbyz hM'
        have := hne1 x j M' M hsig' hxsig
        subst this
        exact hM'
      · obtain ⟨-, hnsig⟩ := h_rcv_neg i x j hbyz hneg
        have := hne2 x j M hxsig
        rw [this] at hnsig; simp at hnsig
    have hwe := hguard M q hq hrcvM
    obtain ⟨b, hbq, hb⟩ := nset.greater_than_third_one_honest q hq
    have hbsig := (hall' b hbq).2
    have hloc := h_from_local b j M (by simpa using hb) hbsig
    have hps := h_signed b j M (by simpa using hb) hloc
    have := hnie j M hps
    rw [this] at hwe; simp at hwe
  · have haux' : st.aux_fb_neg_qv R J QV = true := by
      apply haux
      intro h1 h2 h3
      exact hnew ⟨h1, h2, h3⟩
    exact h_old hne1 hne2 hne3 hnie R J QV q M hR haux' hq

#prove_vc Chorus fb_sign_neg fb_neg_no_pos_quorum by
  unveil_local
  veil_inv_have h_old := fb_neg_no_pos_quorum
  veil_inv_have h_rcv_pos := vote_rcv_pos_backed
  veil_inv_have h_rcv_neg := vote_rcv_neg_backed
  veil_inv_have h_from_local := vote_pos_from_local
  veil_inv_have h_signed := local_entry_pos_signed
  intro hbyz _hpart _hab _hph _hvoted _hcast _hpath _hprop hsup hrcv hguard _hfresh
    hne1 hne2 hne3 hnie R J M hR hfb x hx
  by_cases hnew : i = R ∧ j = J
  · obtain ⟨rfl, rfl⟩ := hnew
    -- Intersect the received quorum with the vote supermajority: an `f+1`
    -- set `t` inside both. If every member of `x` signed positive for `M`,
    -- `i` received that entry from every member of `t`, which the guard
    -- forbids for a root that re-encodes, and `M` does: `t` has a correct
    -- member, whose entry pins the proposer's signature.
    obtain ⟨t, ht_gtt, ht⟩ := cnt.supermajorities_share_third qv x hsup hx
    by_contra hall
    have hsig : ∀ a, ByzNodeSet.member a t = true → st.msg_vote_pos_sig a j M = true := by
      intro a ha
      cases h : st.msg_vote_pos_sig a j M
      · exact absurd ⟨a, (ht a ha).2, h⟩ hall
      · rfl
    have hrcvM : ∀ a, ByzNodeSet.member a t = true →
        ByzNodeSet.member a qv = true ∧ st.local_vote_rcv_pos i a j M = true := by
      intro a ha
      have haqv := (ht a ha).1
      refine ⟨haqv, ?_⟩
      rcases hrcv a haqv with ⟨M', hM'⟩ | hneg
      · obtain ⟨-, hsig'⟩ := h_rcv_pos i a j M' hbyz hM'
        have := hne1 a j M' M hsig' (hsig a ha)
        subst this
        exact hM'
      · obtain ⟨-, hnsig⟩ := h_rcv_neg i a j hbyz hneg
        have := hne2 a j M (hsig a ha)
        rw [this] at hnsig; simp at hnsig
    have hwe := hguard M t ht_gtt hrcvM
    obtain ⟨b, hbt, hb⟩ := nset.greater_than_third_one_honest t ht_gtt
    have hloc := h_from_local b j M (by simpa using hb) (hsig b hbt)
    have hps := h_signed b j M (by simpa using hb) hloc
    have := hnie j M hps
    rw [this] at hwe; simp at hwe
  · have hfb' : st.msg_fb_neg_sig R J = true := hfb (fun h1 h2 => hnew ⟨h1, h2⟩)
    exact h_old hne1 hne2 hne3 hnie R J M hR hfb' x hx

#prove_action Chorus fb_sign_neg

end Chorus.Proofs
