import Cadence.Chorus.Counting
import Cadence.Chorus.Pigeonhole

/-! # Chorus/Progress — the fair-progress case split, as one theorem

The composition of the counting theorems ([`Counting.lean`](./Counting.lean))
and the evidence pigeonhole ([`Pigeonhole.lean`](./Pigeonhole.lean)): the
**entire state-level content of the liveness case split**
(`docs/ChorusDesign.md` §7) as a single statement over reachable states, for
the concrete instance family at every `n = 3f+1`.

> **(Progress dichotomy.)** In any reachable *saturated* state — every
> honest validator has cast its path vote, fast or fallback, carrying the
> per-proposer entries that cast required — either
>
> * a commit certificate exists for **every** proposer, formed from honest
>   votes alone (the fast-dominant route, no MVBA involved), or
> * the MVBA stands **invoked** (one of the paper's two triggers holds) with
>   decide-enabling evidence for **every** proposer — the conclusion's
>   evidence disjunction is, verbatim, the external-validity `require` of
>   `mvba_decide_pos` / `mvba_decide_neg` in the model.

This is what turns the meta-argument's case analysis into a lookup: the
temporal glue that remains is only *"(F-justice) drives every honest
validator to the saturation hypothesis"* and *"(A-mvba) consumes the right
disjunct"* — no reasoning about populations, paths or certificates is left
outside Lean. The branch structure inside the proof is exactly the doc's:
all-fast ⇒ `commitqc_of_honest_fast_dominant` per proposer; some honest
fast-caster ⇒ its commit signatures back a complete fast meta-block
(case-(a) trigger) and network-visible vote quorums
(`fast_path_implies_vote_quorums`); no fast-caster ⇒ every honest validator
fell back, so `FBCert` forms (`fbcert_of_honest_fallback_votes`) and the
evidence pigeonhole supplies each proposer's certificate.

Trust base: `[propext, Classical.choice, Quot.sound]`, pinned below — the
reachability projections consume the proof-file family's kernel-checked VC
theorems through [`Certify.lean`](./Certify.lean); the counting inputs are
the pinned theorems of `Counting.lean` and `Pigeonhole.lean`. -/

namespace Chorus
open Classical ByzNodeSet

section Progress

variable {slot merkle_root Phase PathChoice : Type}
  [Inhabited slot] [Inhabited merkle_root]
  [Inhabited Phase] [Inhabited PathChoice]
  [Phase_Enum : Chorus.Phase_EnumClass Phase]
  [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
  [node_inhabited : Inhabited (Fin n)]

/- Apply a generated `Chorus` declaration at the canonical `Classical`
instantiation, at the concrete quorum instance family (cf. the identical
local macros of `Pigeonhole.lean` and `Counting.lean`). -/
local macro "cpv%" t:ident args:term:max* : term =>
  `(@$t
    (Chorus.Theory slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice)
    (Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice))
    slot (fun a b => Classical.propDecidable (a = b)) inferInstance
    (Fin n) (fun a b => Classical.propDecidable (a = b)) inferInstance
    (ByzNSet n) (fun a b => Classical.propDecidable (a = b)) inferInstance
    merkle_root (fun a b => Classical.propDecidable (a = b)) inferInstance
    (byzNodeSetFin n f hf is_byz hbyz)
    Phase (fun a b => Classical.propDecidable (a = b)) inferInstance inferInstance
    PathChoice (fun a b => Classical.propDecidable (a = b)) inferInstance inferInstance
    (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice)
    (fun ff => @Chorus.instAbstractFieldRepresentation slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) ff)
    (fun ff => @Chorus.instLawfulAbstractFieldRepresentation slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) ff)
    instIsSubStateOfRefl instIsSubReaderOfRefl
    $args*)

/- The abstract field representation at the canonical instances. -/
local macro "pafr%" fld:ident : term =>
  `(@Chorus.instAbstractFieldRepresentation slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    $fld)

variable (st : Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice))

/-- `r` has cast (broadcast) its fast commit vote (`msg_commit_cast`). -/
private abbrev pCast (r : Fin n) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.msg_commit_cast)
    st.msg_commit_cast r = true

/-- `r` holds a positive fast commit signature for `(j, m)`. -/
private abbrev pPos (r j : Fin n) (m : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.msg_commit_pos_sig)
    st.msg_commit_pos_sig r j m = true

/-- `r` holds a negative fast commit signature for `j`. -/
private abbrev pNeg (r j : Fin n) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.msg_commit_neg_sig)
    st.msg_commit_neg_sig r j = true

/-- `r` has cast its fallback vote (`msg_fallback_sig`). -/
private abbrev pFbVote (r : Fin n) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.msg_fallback_sig)
    st.msg_fallback_sig r = true

/-- `r` has a positive fallback signed entry `⟨j, m⟩`. -/
private abbrev pFbPos (r j : Fin n) (m : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.msg_fb_pos_sig)
    st.msg_fb_pos_sig r j m = true

/-- `r` has a negative fallback signed entry for `j`. -/
private abbrev pFbNeg (r j : Fin n) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.msg_fb_neg_sig)
    st.msg_fb_neg_sig r j = true

set_option maxHeartbeats 1600000 in
/-- **The progress dichotomy** — the liveness case split of
`docs/ChorusDesign.md` §7 as one theorem. In any reachable state in which
every honest validator has cast its path vote with the per-proposer entries
that cast required (*saturation* — what (F-justice) eventually delivers),
either a commitQC exists for every proposer from honest votes alone, or
`mvba_invoked` holds together with, for every proposer, evidence in exactly
the external-validity form of `mvba_decide_pos` / `mvba_decide_neg`. -/
theorem progress_dichotomy_of_saturation
    {th : Chorus.Theory slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice}
    {st : Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice)}
    (hreach : (Chorus.relationalTransitionSystem slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice
      (nset := byzNodeSetFin n f hf is_byz hbyz)).reachable th st)
    (hsat : ∀ r : Fin n, ¬ is_byz r →
      (pCast n st r ∧ ∀ j : Fin n, th.is_proposer j = true →
        ((∃ m, pPos n st r j m) ∨ pNeg n st r j)) ∨
      (pFbVote n st r ∧ ∀ j : Fin n, th.is_proposer j = true →
        ((∃ m, pFbPos n st r j m) ∨ pFbNeg n st r j))) :
    (∀ j : Fin n, th.is_proposer j = true →
      ((∃ m, cpv% Chorus.commitqc_pos j m th st) ∨ (cpv% Chorus.commitqc_neg j th st))) ∨
    ((cpv% Chorus.mvba_invoked th st) ∧
      ∀ j : Fin n, th.is_proposer j = true →
        ((∃ m, (cpv% Chorus.vote_quorum_pos j m th st) ∨
               ((cpv% Chorus.fb_quorum_pos j m th st) ∧ (cpv% Chorus.fbcert th st))) ∨
         ((cpv% Chorus.vote_quorum_neg j th st) ∨
          (((cpv% Chorus.fb_quorum_neg j th st) ∨ (cpv% Chorus.equiv_evidence j th st)) ∧
           (cpv% Chorus.fbcert th st))))) := by
  classical
  -- Honesty in the instance's vocabulary.
  have honest : ∀ r : Fin n, ¬ is_byz r →
      ¬ (ByzNodeSet.is_byz (self := byzNodeSetFin n f hf is_byz hbyz) r = true) := by
    intro r hr hb
    exact hr (by simpa [byzNodeSetFin] using hb)
  by_cases hallfast : ∀ r : Fin n, ¬ is_byz r →
      pCast n st r ∧ ∀ j : Fin n, th.is_proposer j = true →
        ((∃ m, pPos n st r j m) ∨ pNeg n st r j)
  · -- Every honest validator cast fast: a commitQC per proposer, from the
    -- honest population alone (`x ≥ 2f+1`).
    obtain ⟨H, hH_card, hH_honest⟩ := honest_supermajority n f hf is_byz hbyz
    refine Or.inl (fun j hj => ?_)
    exact commitqc_of_honest_fast_dominant n f hf is_byz hbyz hreach j H hH_card
      (fun r hr => by
        have hhr := hH_honest r hr
        obtain ⟨hcast, hentries⟩ := hallfast r hhr
        exact ⟨hhr, hcast, hentries j hj⟩)
  · by_cases hexfast : ∃ r : Fin n, ¬ is_byz r ∧
        pCast n st r ∧ ∀ j : Fin n, th.is_proposer j = true →
          ((∃ m, pPos n st r j m) ∨ pNeg n st r j)
    · -- Mixed (`1 ≤ x`): a fast-caster's commit signatures back a complete
      -- fast meta-block — the case-(a) trigger — and network-visible vote
      -- quorums for every proposer.
      obtain ⟨r0, hbz0, hcast0, hentries0⟩ := hexfast
      -- Its per-proposer FastQCs (the case-(a) meta-block).
      have hfastqcs : ∀ j : Fin n, th.is_proposer j = true →
          ((∃ m, @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.local_fastqc_pos)
              st.local_fastqc_pos r0 j m = true) ∨
           @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.local_fastqc_neg)
              st.local_fastqc_neg r0 j = true) := by
        intro j hj
        rcases hentries0 j hj with ⟨m, hp⟩ | hn
        · exact Or.inl ⟨m, Chorus.reachable_commit_pos_sig_from_local_fastqc
            (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r0 j m ⟨honest r0 hbz0, hp⟩⟩
        · exact Or.inr (Chorus.reachable_commit_neg_sig_from_local_fastqc
            (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r0 j ⟨honest r0 hbz0, hn⟩)
      refine Or.inr ⟨?_, ?_⟩
      · -- `mvba_invoked` via the case-(a) trigger.
        unfold Chorus.mvba_invoked Chorus.complete_fast_metablock
        dsimp only
        exact Or.inr ⟨r0, honest r0 hbz0, hfastqcs⟩
      · -- Per-proposer evidence: the fast-caster's path is fast, so the
        -- backing vote supermajorities are on the network.
        have hpath := Chorus.reachable_commit_cast_path_fast
          (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r0 ⟨honest r0 hbz0, hcast0⟩
        intro j hj
        rcases Chorus.reachable_fast_path_implies_vote_quorums
            (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r0 ⟨honest r0 hbz0, hpath⟩ j hj
          with ⟨m, hvq⟩ | hvq
        · exact Or.inl ⟨m, Or.inl hvq⟩
        · exact Or.inr (Or.inl hvq)
    · -- Fallback (`x = 0`): every honest validator fell back, so `FBCert`
      -- forms and the pigeonhole yields each proposer's evidence.
      have hallfb : ∀ r : Fin n, ¬ is_byz r →
          pFbVote n st r ∧ ∀ j : Fin n, th.is_proposer j = true →
            ((∃ m, pFbPos n st r j m) ∨ pFbNeg n st r j) := by
        intro r hr
        rcases hsat r hr with hfast | hfb
        · exact absurd ⟨r, hr, hfast⟩ hexfast
        · exact hfb
      have hfbcert : cpv% Chorus.fbcert th st :=
        fbcert_of_honest_fallback_votes n f hf is_byz hbyz
          (fun r hr => (hallfb r hr).1)
      obtain ⟨H, hH_card, hH_honest⟩ := honest_supermajority n f hf is_byz hbyz
      refine Or.inr ⟨?_, ?_⟩
      · -- `mvba_invoked` via the fallback trigger.
        unfold Chorus.mvba_invoked
        dsimp only
        exact Or.inl hfbcert
      · intro j hj
        rcases Chorus.evidence_pigeonhole_of_reachable n f hf is_byz hbyz hreach j H hH_card
            (fun r hr => ⟨hH_honest r hr, ((hallfb r (hH_honest r hr)).2 j hj)⟩)
          with ⟨m, hq⟩ | hq | hq
        · exact Or.inl ⟨m, Or.inr ⟨hq, hfbcert⟩⟩
        · exact Or.inr (Or.inr ⟨Or.inl hq, hfbcert⟩)
        · exact Or.inr (Or.inr ⟨Or.inr hq, hfbcert⟩)

end Progress
end Chorus

/-! ## The pinned trust base

The standard Lean trio and nothing else — no `sorryAx`: the whole chain
(the proof-file family's kernel-checked VC theorems through
`Certify.lean`'s reachability projections; the counting theorems of
`Counting.lean` and the pigeonhole of `Pigeonhole.lean`) is real proofs
end-to-end. A regression anywhere in that chain fails this guard. -/

/--
info: 'Chorus.progress_dichotomy_of_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.progress_dichotomy_of_saturation
