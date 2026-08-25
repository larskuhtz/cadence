import Cadence.Chorus.Certify

/-! # Chorus/Counting — the certificate-formation counting steps, mechanised

Companion to [`Pigeonhole.lean`](./Pigeonhole.lean) (read its header first):
the remaining *counting* steps of the fair-progress argument
(`docs/ChorusDesign.md` §7), as Lean theorems over the concrete instance
family `byzNodeSetFin n f` — **every** `n = 3f+1`, every Byzantine set of
size `≤ f`. With these, the counting content of all three branches of the
case split is mechanised, and what remains meta in the liveness argument is
*purely* the temporal glue ((F-justice)/(F-byz)/(A-mvba);
`docs/Architecture.md` §4 item 2).

1. `honest_supermajority` — the honest population itself is a
   supermajority-sized node set: `n = 3f+1` minus `≤ f` Byzantine leaves
   `≥ 2f+1`. Pure counting; the witness every formation step below uses.
2. `fbcert_of_honest_fallback_votes` / `fbcommitqc_of_honest_commit_votes`
   — once every honest validator has cast its fallback vote
   (resp. fallback commit vote), the certificate exists: the honest
   population is the quorum. These discharge the "`FBCert` forms" step of
   the `x = 0` branch and the "`2f+1` honest commit votes form
   `fbCommitQC`" step of the commit-round epilogue — previously the two
   places `docs/ChorusDesign.md` §7 called a meta-level counting step.
   State-level and reachability-free: the certificates are existential
   statements the honest quorum witnesses directly.
3. `commitqc_of_honest_fast_dominant` — the `x ≥ 2f+1` branch: any
   supermajority of honest validators that have cast fast commit votes
   yields, per proposer, a commitQC from honest votes alone. The
   polarity/root agreement comes from the invariant chain
   `commit_*_sig_from_local_fastqc` → `local_fastqc_pos_cross_unique` /
   `local_fastqc_pos_neg_excl` over the named reachability projections of
   [`Certify.lean`](./Certify.lean).

The hypotheses are exactly what the (F-justice) temporal layer delivers —
"every honest validator (of the given population) has signed/cast" — so the
theorems slot into the meta-argument at the stated seam. Stated for the
concrete instance family because "the honest population is a set the
quorum language can quantify over" is not expressible over the abstract
`ByzNodeSet` axioms (cf. the header of `FallbackReceipt/Totality.lean`).

Trust base: `[propext, Classical.choice, Quot.sound]`, pinned below.
`commitqc_of_honest_fast_dominant` consumes the proof-file family's
kernel-checked VC theorems through `Certify.lean`'s reachability
projections; the other theorems are kernel-checked counting outright. -/

namespace Chorus
open Classical ByzNodeSet

section Counting

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
instantiation, at the concrete quorum instance family (the generated
composition's regime with `node := Fin n`,
`nset := byzNodeSetFin n f hf is_byz hbyz`); cf. `Pigeonhole.lean`. -/
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

/- The abstract field representation at the canonical instances
(cf. `Pigeonhole.lean`'s `pafr%`). -/
local macro "cafr%" fld:ident : term =>
  `(@Chorus.instAbstractFieldRepresentation slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    $fld)

section HonestPopulation
include hf hbyz

omit node_inhabited in
/-- **The honest population is a supermajority** — `n = 3f+1` nodes minus
`≤ f` Byzantine leaves a sorted node set of `≥ 2f+1` honest members. The
witness set every certificate-formation step below quantifies over. -/
theorem honest_supermajority :
    ∃ H : ByzNSet n, 2 * f + 1 ≤ H.val.length ∧ ∀ r, r ∈ H.val → ¬ is_byz r := by
  classical
  refine ⟨⟨(List.ofFn (n := n) id).filter (fun a => !decide (is_byz a)),
    List.Pairwise.filter _ (by simp)⟩, ?_, ?_⟩
  · have hsplit := List.length_eq_length_filter_add
      (l := List.ofFn (n := n) id) (fun a => decide (is_byz a))
    have hlen : (List.ofFn (n := n) id).length = n := by simp
    simp only
    omega
  · intro r hr
    have hmem := List.mem_filter.mp hr
    simpa using hmem.2

end HonestPopulation

variable (st : Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice))

/-- `r` has cast its fallback vote (`msg_fallback_sig`). -/
private abbrev fbVote (r : Fin n) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (cafr% Chorus.State.Label.msg_fallback_sig)
    st.msg_fallback_sig r = true

/-- `r` has cast its fallback commit vote (`msg_fbcommit_sig`). -/
private abbrev fbcVote (r : Fin n) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (cafr% Chorus.State.Label.msg_fbcommit_sig)
    st.msg_fbcommit_sig r = true

/-- `r` holds a positive fast commit signature for `(j, m)`. -/
private abbrev cmPos (r j : Fin n) (m : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (cafr% Chorus.State.Label.msg_commit_pos_sig)
    st.msg_commit_pos_sig r j m = true

/-- `r` holds a negative fast commit signature for `j`. -/
private abbrev cmNeg (r j : Fin n) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (cafr% Chorus.State.Label.msg_commit_neg_sig)
    st.msg_commit_neg_sig r j = true

/-- `r` has cast (broadcast) its fast commit vote (`msg_commit_cast`). -/
private abbrev cmCast (r : Fin n) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (cafr% Chorus.State.Label.msg_commit_cast)
    st.msg_commit_cast r = true

/-- **`FBCert` formation** (`x = 0` branch, `docs/ChorusDesign.md` §7): once
every honest validator has cast its fallback vote, `fbcert` holds — the
honest population is itself the certifying quorum. Reachability-free. -/
theorem fbcert_of_honest_fallback_votes
    {th : Chorus.Theory slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice}
    {st : Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice)}
    (h : ∀ r : Fin n, ¬ is_byz r → fbVote n st r) :
    cpv% Chorus.fbcert th st := by
  classical
  obtain ⟨H, hlen, hH⟩ := honest_supermajority n f hf is_byz hbyz
  unfold Chorus.fbcert
  dsimp only
  simp only [byzNodeSetFin, decide_eq_true_eq]
  exact ⟨H, hlen, fun r hr => h r (hH r hr)⟩

/-- **`fbCommitQC` formation** (the commit-round epilogue,
`line:fb-collect-commit` / `line:fb-formcommitqc`): once every honest
validator has cast its fallback commit vote, `fbcommitqc` holds — the same
honest-population quorum. Reachability-free. -/
theorem fbcommitqc_of_honest_commit_votes
    {th : Chorus.Theory slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice}
    {st : Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice)}
    (h : ∀ r : Fin n, ¬ is_byz r → fbcVote n st r) :
    cpv% Chorus.fbcommitqc th st := by
  classical
  obtain ⟨H, hlen, hH⟩ := honest_supermajority n f hf is_byz hbyz
  unfold Chorus.fbcommitqc
  dsimp only
  simp only [byzNodeSetFin, decide_eq_true_eq]
  exact ⟨H, hlen, fun r hr => h r (hH r hr)⟩

set_option maxHeartbeats 1000000 in
/-- **CommitQC formation in the fast-dominant branch** (`x ≥ 2f+1`,
`docs/ChorusDesign.md` §7): in any reachable state, a supermajority `H` of
honest validators that have cast fast commit votes — each carrying its
per-proposer entry for `j`, as `cast_fast_commit` requires — yields a
commitQC for `j` from honest votes alone. Agreement across `H` is the
invariant chain `commit_*_sig_from_local_fastqc` →
`local_fastqc_pos_cross_unique` / `local_fastqc_pos_neg_excl`. -/
theorem commitqc_of_honest_fast_dominant
    {th : Chorus.Theory slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice}
    {st : Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice)}
    (hreach : (Chorus.relationalTransitionSystem slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice
      (nset := byzNodeSetFin n f hf is_byz hbyz)).reachable th st)
    (j : Fin n) (H : ByzNSet n)
    (hH_card : 2 * f + 1 ≤ H.val.length)
    (hH : ∀ r, r ∈ H.val → ¬ is_byz r ∧ cmCast n st r ∧
      ((∃ m, cmPos n st r j m) ∨ cmNeg n st r j)) :
    (∃ m, cpv% Chorus.commitqc_pos j m th st) ∨
    (cpv% Chorus.commitqc_neg j th st) := by
  classical
  -- Honesty in the instance's vocabulary.
  have honest : ∀ r : Fin n, ¬ is_byz r →
      ¬ (ByzNodeSet.is_byz (self := byzNodeSetFin n f hf is_byz hbyz) r = true) := by
    intro r hr hb
    exact hr (by simpa [byzNodeSetFin] using hb)
  -- A representative member fixes the polarity (and, if positive, the root).
  have hne : H.val ≠ [] := by
    intro hnil
    rw [hnil] at hH_card
    simp at hH_card
  obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hbz0, hcast0, hentry0⟩ := hH r0 hr0
  rcases hentry0 with ⟨m0, hp0⟩ | hn0
  · -- Positive representative: every member is positive on the same root.
    have hfq0 := Chorus.reachable_commit_pos_sig_from_local_fastqc
      (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r0 j m0 ⟨honest r0 hbz0, hp0⟩
    refine Or.inl ⟨m0, ?_⟩
    unfold Chorus.commitqc_pos
    dsimp only
    simp only [byzNodeSetFin, decide_eq_true_eq]
    refine ⟨H, hH_card, ?_⟩
    intro r hr
    obtain ⟨hbz, hcast, hentry⟩ := hH r hr
    rcases hentry with ⟨m, hp⟩ | hn
    · have hfq := Chorus.reachable_commit_pos_sig_from_local_fastqc
        (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r j m ⟨honest r hbz, hp⟩
      have hm : m = m0 := Chorus.reachable_local_fastqc_pos_cross_unique
        (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r r0 j m m0
        ⟨honest r hbz, honest r0 hbz0, hfq, hfq0⟩
      exact ⟨hm ▸ hp, hcast⟩
    · have hfqn := Chorus.reachable_commit_neg_sig_from_local_fastqc
        (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r j ⟨honest r hbz, hn⟩
      exact absurd ⟨hfq0, hfqn⟩ (Chorus.reachable_local_fastqc_pos_neg_excl
        (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r0 r j m0
        ⟨honest r0 hbz0, honest r hbz⟩)
  · -- Negative representative: every member is negative.
    have hfqn0 := Chorus.reachable_commit_neg_sig_from_local_fastqc
      (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r0 j ⟨honest r0 hbz0, hn0⟩
    refine Or.inr ?_
    unfold Chorus.commitqc_neg
    dsimp only
    simp only [byzNodeSetFin, decide_eq_true_eq]
    refine ⟨H, hH_card, ?_⟩
    intro r hr
    obtain ⟨hbz, hcast, hentry⟩ := hH r hr
    rcases hentry with ⟨m, hp⟩ | hn
    · have hfq := Chorus.reachable_commit_pos_sig_from_local_fastqc
        (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r j m ⟨honest r hbz, hp⟩
      exact absurd ⟨hfq, hfqn0⟩ (Chorus.reachable_local_fastqc_pos_neg_excl
        (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r r0 j m
        ⟨honest r hbz, honest r0 hbz0⟩)
    · exact ⟨hn, hcast⟩

end Counting
end Chorus

/-! ## The pinned trust base

The standard Lean trio and nothing else — no `sorryAx`.
`commitqc_of_honest_fast_dominant` consumes the proof-file family's
re-proved, kernel-checked VC theorems through `Certify.lean`'s
reachability projections; the certificate-formation theorems are
kernel-checked counting outright. A regression anywhere in that chain
fails these guards. -/

/--
info: 'Chorus.fbcert_of_honest_fallback_votes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fbcert_of_honest_fallback_votes

/--
info: 'Chorus.fbcommitqc_of_honest_commit_votes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fbcommitqc_of_honest_commit_votes

/--
info: 'Chorus.commitqc_of_honest_fast_dominant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.commitqc_of_honest_fast_dominant
