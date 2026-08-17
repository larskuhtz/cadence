import Cadence.Chorus

/-! # `Chorus` proofs — action `vote`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `vote` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus vote <property> by <tac>` lines
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
-- `fastqc_complete_implies_mvba_evidence` diverges under the K5(a2')
-- Bool-atom fold's query shape (2026-07-14, the fold-era cache refresh):
-- the one cell of 3 822 where cvc5's e-matching runs to ANY budget
-- (measured: the whole WP/TR retry ladder at 60 s, then again at 120 s)
-- on the folded query, where the pre-fold shape solves in <37 s. The fold
-- is tactic-side only — VC statements and cache keys are unchanged — so
-- with the option off here, the 96 fold-era cached cells still hit and
-- only this cell re-solves (pre-fold shape, one fat witness). Revisit if
-- lean-smt/cvc5 changes the e-matching behavior (`docs/Dependencies.md` §2).
set_option veil.smt.foldBoolAtoms false

namespace Chorus.Proofs

/- Manual discharge of the one VC the SMT pipeline cannot solve
automatically: `vote` preserves `fb_neg_no_pos_quorum`. The proof applies
`supermajorities_intersect_in_greater_than_third` once — to the recorded
witness quorum (`local_fb_neg_qv`) and the claimed post-state vote
supermajority — and closes with `fb_neg_qv_no_pos_quorum`; against `vote`'s
bulk signature update, cvc5's e-matching diverges instead of finding this
single instantiation. Stated verbatim as the canonical VC statement (originally a stub from
Veil's "insert theorem stubs" suggestion; pre-M6 an `@[veil]` interactive
discharger for the in-file sweep — now a preproven cell the
`#prove_action` below consumes as-is after a statement check). The conjunct indices (14/17/78/80/81) in the `hinv.2.…` projections follow the
declaration order of the safety properties and invariants in this file —
adjust them when adding or reordering declarations before this point. -/
theorem vote_fb_neg_no_pos_quorum (ρ : Type) (σ : Type) (slot : Type) [slot_dec_eq : DecidableEq.{1} slot]
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
    [vote_dec_0 : delta% @Chorus.vote._veil_dec_type_0 node χ merkle_root slot nodeset Phase PathChoice χ_rep]
    [vote_dec_1 : delta% @Chorus.vote._veil_dec_type_1 node χ merkle_root slot nodeset Phase PathChoice χ_rep] :
    ∀ (i : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@vote.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub
          vote_dec_0 vote_dec_1 i)
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
  intro hbyz_i hphase hvoted hne1 hne2 hne3 R J M hbyz_R hfbneg x hsup
  have h14 := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h17 := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h71 := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h73 := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h74 := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  -- The voter `i` has no pre-state vote signatures: it has not voted yet.
  have hno_sig_i : ∀ j m, st.msg_vote_pos_sig i j m = false := by
    intro j m
    cases hb : st.msg_vote_pos_sig i j m with
    | false => rfl
    | true =>
      have hv := h14 i j m hbyz_i hb
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
  obtain ⟨qv, hqv⟩ := h71 R J hbyz_R hfbneg
  obtain ⟨hqv_sup, hqv_cast⟩ := h73 R J qv hbyz_R hqv
  -- `i` is not in `qv`: its members had broadcast votes, `i` has not voted.
  have hi_not_qv : ByzNodeSet.member i qv = false := by
    cases hb : ByzNodeSet.member i qv with
    | false => rfl
    | true =>
      have hv := h17 i hbyz_i (hqv_cast i hb)
      rw [hvoted] at hv
      simp at hv
  -- Intersect `qv` with the claimed post-state supermajority `x`.
  obtain ⟨t, ht_gtt, ht_mem⟩ :=
    nset.supermajorities_intersect_in_greater_than_third qv x hqv_sup hsup
  -- The witness invariant yields a member of `t` with no pre-state signature.
  obtain ⟨a, ha_t, ha_nosig⟩ := h74 hne1' hne2' hne3 R J qv t M hbyz_R hqv ht_gtt
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
