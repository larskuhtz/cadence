import Cadence.Chorus.Certify
import Cadence.FallbackReceipt.Totality

/-! # ChorusPigeonhole — the evidence pigeonhole, mechanised

The evidence-formation counting step of Chorus's fair-progress argument
(`docs/ChorusDesign.md` §7, the `x = 0`
branch): in any reachable Chorus state, if a
supermajority of *honest* validators each hold a fallback signed entry
for a proposer `j`, then certified per-proposer evidence exists —

> a positive FallbackQC (`fb_quorum_pos`), a negative FallbackQC
> (`fb_quorum_neg`), or an EquivCert (`equiv_evidence`)

— which is exactly the per-proposer evidence premise of the (A-mvba)
meta-axiom's decide actions (`mvba_decide_pos`/`mvba_decide_neg`
external validity).

The counting content is the same two-class pigeonhole as the receipt
layer's build totality (`ByzNSet.two_cover`,
`FallbackReceipt/Totality.lean`):
split the supermajority by "holds a *positive* entry for `j`"; an `f+1`
all-negative class is a negative FallbackQC; an `f+1` all-positive
class either agrees on one root (a positive FallbackQC) or exhibits two
distinct roots — and each honest positive fallback entry pins a
*proposer-signed* root via the invariant chain

> `msg_fb_pos_sig_backed` (an `f+1` vote quorum backs the entry) →
> `greater_than_third_one_honest` (it contains an honest voter) →
> `vote_pos_from_local` → `local_entry_pos_signed`
> (the honest voter's entry pins `msg_proposer_signed`),

so two distinct roots yield `equiv_evidence`. All reachable-state facts
come from the named projections of
[`Chorus/Certify.lean`](./Certify.lean) (`#gen_composition`); like
`FallbackReceipt/Totality.lean`, the
theorem is stated over the concrete instance family
`byzNodeSetFin n f` — **every** `n = 3f+1`, every Byzantine set of size
`≤ f`, arbitrary `slot`/`merkle_root`/`Phase`/`PathChoice` types —
because the two-class counting is not expressible over the abstract
`ByzNodeSet` axioms.

What this discharges: the "Evidence pigeonhole" step of the liveness
argument — see `docs/ChorusDesign.md` §7 for how it composes with the
other theorems and where the named temporal assumptions
((F-justice)/(F-byz)/(A-mvba); `docs/Architecture.md` §4) enter. Trust base:
`[propext, Classical.choice, Quot.sound]` (pinned below) — the reachability
projections consume the proof-file family's re-proved VC theorems
(`Chorus/Proofs/`, via `Chorus/Certify.lean`), and the counting is
kernel-checked outright. -/

namespace Chorus
open Classical ByzNodeSet

section Pigeonhole

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
`nset := byzNodeSetFin n f hf is_byz hbyz`). -/
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
(cf. `Chorus/Compose.lean`'s `afr%`). -/
local macro "pafr%" fld:ident : term =>
  `(@Chorus.instAbstractFieldRepresentation slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    $fld)

variable (st : Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice))

/-- `r` has cast a positive fallback signed entry `⟨j, m⟩`. -/
private abbrev fbPos (r j : Fin n) (m : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.msg_fb_pos_sig)
    st.msg_fb_pos_sig r j m = true

/-- `r` has cast a negative fallback signed entry for `j`. -/
private abbrev fbNeg (r j : Fin n) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.msg_fb_neg_sig)
    st.msg_fb_neg_sig r j = true

/-- The proposer `j` has signed root `m` (`msg_proposer_signed`). -/
private abbrev propSigned (j : Fin n) (m : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (pafr% Chorus.State.Label.msg_proposer_signed)
    st.msg_proposer_signed j m = true

set_option maxHeartbeats 1000000 in
/-- **The evidence pigeonhole** (`docs/ChorusDesign.md` §7, `x = 0` branch):
in any reachable state, a supermajority of honest validators holding
fallback signed entries for `j` yields certified per-proposer evidence
— a FallbackQC (positive or negative) or an EquivCert. Stated for every
`n = 3f+1` and any Byzantine set of size `≤ f`. -/
theorem evidence_pigeonhole_of_reachable
    {th : Chorus.Theory slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice}
    {st : Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice)}
    (hreach : (Chorus.relationalTransitionSystem slot (Fin n) (ByzNSet n) merkle_root Phase PathChoice
      (nset := byzNodeSetFin n f hf is_byz hbyz)).reachable th st)
    (j : Fin n) (H : ByzNSet n)
    (hH_card : 2 * f + 1 ≤ H.val.length)
    (hH : ∀ r, r ∈ H.val → ¬ is_byz r ∧
      ((∃ m, fbPos n st r j m) ∨ fbNeg n st r j)) :
    (∃ m, cpv% Chorus.fb_quorum_pos j m th st) ∨
    (cpv% Chorus.fb_quorum_neg j th st) ∨
    (cpv% Chorus.equiv_evidence j th st) := by
  classical
  -- Case 1: an EquivCert already exists.
  by_cases heqv : (cpv% Chorus.equiv_evidence j th st)
  · exact Or.inr (Or.inr heqv)
  -- Honesty in the instance's vocabulary.
  have honest : ∀ r : Fin n, ¬ is_byz r →
      ¬ (ByzNodeSet.is_byz (self := byzNodeSetFin n f hf is_byz hbyz) r = true) := by
    intro r hr hb
    exact hr (by simpa [byzNodeSetFin] using hb)
  -- The signature chain: an honest positive fallback entry pins a
  -- proposer-signed root.
  have hsig : ∀ (r : Fin n) (m : merkle_root), ¬ is_byz r →
      fbPos n st r j m →
      propSigned n st j m := by
    intro r m hr hp
    have hbacked := Chorus.reachable_msg_fb_pos_sig_backed
      (nset := byzNodeSetFin n f hf is_byz hbyz) hreach r j m ⟨honest r hr, hp⟩
    obtain ⟨q, hq_gtt, hq⟩ := hbacked
    obtain ⟨v, hv_mem, hv_honest⟩ :=
      ByzNodeSet.greater_than_third_one_honest (self := byzNodeSetFin n f hf is_byz hbyz)
        q hq_gtt
    have hlocal := Chorus.reachable_vote_pos_from_local
      (nset := byzNodeSetFin n f hf is_byz hbyz) hreach v j m ⟨hv_honest, hq v hv_mem⟩
    exact Chorus.reachable_local_entry_pos_signed
      (nset := byzNodeSetFin n f hf is_byz hbyz) hreach v j m ⟨hv_honest, hlocal⟩
  -- No EquivCert: any two proposer-signed roots agree.
  have huniq : ∀ (m1 m2 : merkle_root),
      propSigned n st j m1 → propSigned n st j m2 → m1 = m2 := by
    intro m1 m2 h1 h2
    by_contra hne
    refine heqv ?_
    unfold Chorus.equiv_evidence
    dsimp only
    exact ⟨m1, m2, hne, h1, h2⟩
  -- The two-class pigeonhole over the honest supermajority.
  rcases ByzNSet.two_cover H hH_card
      (fun r => ∃ m, fbPos n st r j m)
    with ⟨t, ht_len, ht_mem⟩ | ⟨t, ht_len, ht_mem⟩
  · -- All-positive class: the roots agree (no EquivCert), so `t`
    -- witnesses a positive FallbackQC.
    have ht_ne : t.val ≠ [] := by
      intro hnil
      rw [hnil] at ht_len
      simp at ht_len
    obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ ht_ne
    obtain ⟨hr0H, m0, hr0p⟩ := ht_mem r0 hr0
    refine Or.inl ⟨m0, ?_⟩
    unfold Chorus.fb_quorum_pos
    dsimp only
    simp only [byzNodeSetFin, decide_eq_true_eq]
    refine ⟨t, ht_len, ?_⟩
    intro r hr
    obtain ⟨hrH, m, hrp⟩ := ht_mem r hr
    have hm : m = m0 :=
      huniq m m0
        (hsig r m (hH r hrH).1 hrp)
        (hsig r0 m0 (hH r0 hr0H).1 hr0p)
    exact hm ▸ hrp
  · -- All-negative class: entry completeness (the hypothesis) leaves
    -- the negative entry, so `t` witnesses a negative FallbackQC.
    refine Or.inr (Or.inl ?_)
    unfold Chorus.fb_quorum_neg
    dsimp only
    simp only [byzNodeSetFin, decide_eq_true_eq]
    refine ⟨t, ht_len, ?_⟩
    intro r hr
    obtain ⟨hrH, hrnp⟩ := ht_mem r hr
    rcases (hH r hrH).2 with hpos | hneg
    · exact absurd hpos hrnp
    · exact hneg

end Pigeonhole
end Chorus

/-! ## The pinned trust base

The standard Lean trio and nothing else — no `sorryAx`: the whole chain
(the proof-file family's re-proved, kernel-checked VC theorems consumed
through `Chorus/Certify.lean`'s reachability projections; the `two_cover`
counting, kernel-checked outright) is real proofs end-to-end. See the
pinned-trust-base note in `Chorus/Compose.lean` for the full reading of
the file-family architecture. A regression anywhere in that chain fails
this guard. -/

/--
info: 'Chorus.evidence_pigeonhole_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.evidence_pigeonhole_of_reachable
