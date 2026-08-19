import Cadence.Chorus

/-! # `Chorus` proofs — action `aggregate_fastqc_pos`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `aggregate_fastqc_pos` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus aggregate_fastqc_pos <property> by <tac>` lines
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

/- Manual discharges for the remaining verification conditions whose
quorum-intersection chains cvc5's e-matching cannot find automatically
(each is the same shape: one or two applications of the `ByzNodeSet`
counting axioms against explicitly witnessed quorums, closed by a
recorded backing invariant). They are stated verbatim as the canonical VC
statements, so the `#prove_action` below consumes them as-is after a
statement check. The `hinv.2.…`
projections index the conjuncts of the assembled `Invariants` in
declaration order — adjust when adding or reordering declarations. -/
theorem aggregate_fastqc_pos_spec_fastqc_pos_mvba_pos_unique (ρ : Type) (σ : Type) (slot : Type)
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
    [aggregate_fastqc_pos_dec_0 : delta% @Chorus.aggregate_fastqc_pos._veil_dec_type_0 nodeset node nset]
    [aggregate_fastqc_pos_dec_1 :
      delta%
        @Chorus.aggregate_fastqc_pos._veil_dec_type_1 node merkle_root nodeset χ nset slot Phase PathChoice χ_rep] :
    ∀ (i : node) (j : node) (m : merkle_root) (q : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@aggregate_fastqc_pos.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub aggregate_fastqc_pos_dec_0 aggregate_fastqc_pos_dec_1 i j m q)
        (@Assumptions ρ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum ρ_sub)
        (@Invariants ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@spec_fastqc_pos_mvba_pos_unique ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hbyz_i hsup_q hq_sigs hne1 hne2 hne3 I J M M' hbyz_I hfq hmv
  by_cases hnew : i = I ∧ j = J ∧ m = M
  · obtain ⟨rfl, rfl, rfl⟩ := hnew
    rcases hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j M' hmv with ⟨Q2, hQ2_sup, hQ2⟩ | ⟨⟨qf, hqf_gtt, hqf⟩, -⟩
    · obtain ⟨a, ha1, ha2, ha_hon⟩ := nset.supermajorities_intersect_in_honest q Q2 hsup_q hQ2_sup
      exact hne1 a j m M' (hq_sigs a (by simpa using ha1)) (hQ2 a (by simpa using ha2))
    · obtain ⟨rf, hrf_mem, hrf_hon⟩ := nset.greater_than_third_one_honest qf hqf_gtt
      have hrf_hon' : ByzNodeSet.is_byz rf = false := by simpa using hrf_hon
      obtain ⟨qv2, hqv2_gtt, hqv2⟩ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rf j M' hrf_hon' (hqf rf (by simpa using hrf_mem))
      obtain ⟨b, hb1, hb2⟩ := nset.supermajority_greater_than_third_intersect q qv2 hsup_q hqv2_gtt
      exact hne1 b j m M' (hq_sigs b (by simpa using hb1)) (hqv2 b (by simpa using hb2))
  · have hold : st.local_fastqc_pos I J M = true := hfq (fun h1 h2 h3 => hnew ⟨h1, h2, h3⟩)
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hne1 hne2 hne3 I J M M' hbyz_I hold hmv

#prove_action Chorus aggregate_fastqc_pos

end Chorus.Proofs
