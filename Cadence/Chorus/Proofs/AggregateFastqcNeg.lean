import Cadence.Chorus

/-! # `Chorus` proofs — action `aggregate_fastqc_neg`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `aggregate_fastqc_neg` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus aggregate_fastqc_neg <property> by <tac>` lines
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

/-! ### Manual discharges

Three VCs that SMT cannot solve at this clump size: they fall into
e-matching divergence, and run-to-run different subsets of the three time
out at any budget (300 s, 400 s and 900 s all observed), so no budget
fixes them. Each proof is short and mirrors an existing template above:

* `broadcast_commitqc_pos × progress_fallback_signing` — pure frame: the
  action touches only `msg_commitqc_pos`, which the invariant never
  mentions; the proof is the pre-state projection.
* `aggregate_fastqc_neg × fastqc_complete_implies_mvba_evidence` — the
  new `local_fastqc_neg i j` entry can complete `i`'s fast meta-block;
  per proposer the evidence comes from `local_fastqc_pos_backed` /
  `local_fastqc_neg_backed`, and for the new `(i, j)` entry from the
  action's own witnessed vote quorum.
* `mvba_decide_pos × commitqc_neg_mvba_pos_excl` — mirror of
  `mvba_decide_neg_commitqc_pos_mvba_neg_excl` with the polarities
  swapped: the neg-commitQC's vote backing (`msg_commitqc_neg_votes`)
  meets the decision's positive vote-quorum evidence in an honest
  double-voter (`vote_unique_pos_neg`), and its cast backing
  (`msg_commitqc_neg_backed`) meets `fbcert` in an honest validator
  violating the `pathVote` exclusion (`commit_cast_fallback_sig_excl`).
-/
theorem aggregate_fastqc_neg_fastqc_complete_implies_mvba_evidence (ρ : Type) (σ : Type) (slot : Type)
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
    [aggregate_fastqc_neg_dec_0 : delta% @Chorus.aggregate_fastqc_neg._veil_dec_type_0 nodeset node nset]
    [aggregate_fastqc_neg_dec_1 :
      delta%
        @Chorus.aggregate_fastqc_neg._veil_dec_type_1 node nodeset χ nset slot merkle_root Phase PathChoice χ_rep] :
    ∀ (i : node) (j : node) (q : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@aggregate_fastqc_neg.ext ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset
          nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq
          Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep
          χ_rep_lawful σ_sub ρ_sub aggregate_fastqc_neg_dec_0 aggregate_fastqc_neg_dec_1 i j q)
        (@Assumptions ρ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum ρ_sub)
        (@Invariants ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited nodeset nodeset_dec_eq
          nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase Phase_dec_eq Phase_inhabited
          Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@fastqc_complete_implies_mvba_evidence ρ σ slot slot_dec_eq slot_inhabited node node_dec_eq node_inhabited
          nodeset nodeset_dec_eq nodeset_inhabited merkle_root merkle_root_dec_eq merkle_root_inhabited nset Phase
          Phase_dec_eq Phase_inhabited Phase_Enum PathChoice PathChoice_dec_eq PathChoice_inhabited PathChoice_Enum χ
          χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hbyz_i hsup_q hq I hbyz_I hmeta J hprop_J
  rcases hmeta J hprop_J with ⟨M, hpos⟩ | hneg
  · exact Or.inl ⟨M, hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 I J M hbyz_I hpos⟩
  · by_cases hnew : i = I ∧ j = J
    · obtain ⟨rfl, rfl⟩ := hnew
      exact Or.inr ⟨q, hsup_q, hq⟩
    · have hpre : st.local_fastqc_neg I J = true := hneg (fun h1 h2 => hnew ⟨h1, h2⟩)
      exact Or.inr (hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 I J hbyz_I hpre)

#prove_action Chorus aggregate_fastqc_neg

end Chorus.Proofs
