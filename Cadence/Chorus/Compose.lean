import Cadence.Chorus.Certify
import Cadence.Interfaces

/-! # ChorusCompose — `Chorus ⊨ SlotConsensusSafety`

The final leg of the composition layer (`docs/ConductorDesign.md` §5.2,
`docs/CompositionContracts.md`): the Chorus transition system, packaged as
the state-level slot-consensus contract that the `Cadence` glue module
consumes as its `sc` constraint ([`Interfaces.lean`](../Interfaces.lean)).

**The family.** `mod:slotconsensus` is one instance per slot, and the
contract is stated as the family over slots. Chorus is a single-slot model,
so the instance runs one independent copy of it per slot: every slot's
`init`, `step`, `reachable` are Chorus's own, and a validator's finalized
proposal vector is its decision vector *tagged with the slot* —
`pvector := slot × (node → Option merkle_root)`. That tag is what makes the
contract's `slot_safety` hold by construction: the glue's "slot safety is
absorbed by indexing" and the paper's `V.slot = s` are the same fact here.

**The proposal-vector construction** (the "granularity note" of the
contract): a committed validator's vector maps each proposer `J` to its
committed positive root (`some M` iff `local_committed_pos i J M`), and
every non-proposer to `none`. The `is_proposer` gate is load-bearing: the
module's invariant clump does not record "committed entries exist only for
proposers" (it is a guard of `commit_assign_*`), so agreement at
non-proposer indices holds by construction rather than by invariant.
`finalized s st i V` requires `local_committed i` — the paper's
`finalize(V)` output — and pins `V` to the tagged vector; `on_time` is the
module's `all_honest_recorded` synchrony-premise ghost, exactly as the
contract's docstring says.

| `SlotConsensusSafety` field | discharged by |
|---|---|
| `agreement` | `safety [agreement_pos]` + `[agreement_pos_neg]` + `invariant [local_committed_complete]` |
| `slot_safety` | by construction (the slot tag) |
| `proposal_inclusion` | `safety [proposal_inclusion]` + `[proposal_inclusion_no_neg]` + `invariant [local_committed_complete]` |
| `finalized_mono`, `on_time_mono`, `init_finalized` | the transition bodies of all 38 actions, uniformly (`committedAll_mono`, `committedPos_frozen`, `recorded_mono`, `init_not_committed` below); the vector is frozen once committed because `commit_assign_*` require `¬ local_committed i` |
| `step_trans`, `reachable_init`, `reachable_trans` | the reachability constructors |

all consumed through the named reachability projections of
[`Chorus/Certify.lean`](./Certify.lean) (emitted by `#gen_composition` from
the proof-file family's preservation lemmas).

**What stays residual.** Chorus models neither the participation interface
of `mod:slotconsensus` (`participate`/`abandon`/`propose` are absent — the
model is single-slot and its participation window is Cadence-driven) nor
time, and it has no message type at the interface. So the upper level's
inputs, their observables, the clock, the admissible-run model, Termination
and Quiescence are the residual `SlotConsensusResidual` below —
`slotConsensus_of_residual` proves that, given them, Chorus is a full
`SlotConsensus`, discharging on the way the one upper-level field Chorus
*does* prove: the protocol half of Hiding (`safety [hiding_until_deadline]`,
the contract's `hiding_residue`). The residual is the formal statement of
`docs/Architecture.md` §4 item 4 for this module.

Trust base: `[propext, Classical.choice, Quot.sound]` — the standard Lean
trio, nothing else — pinned by the `#guard_msgs` axiom checks at the end of
this file. The composition consumes the proof-file family
(`Chorus/Proofs/`, via `Chorus/Certify.lean`'s `#gen_composition`):
every VC statement re-created from the persistent registry, solved as a
fresh kernel-checked reconstruction, assembled per action into a
preservation lemma, and composed — kernel-checked at every `addDecl` —
inside Veil. -/

-- NOTE: deliberately NO `open Veil` here — it activates the Veil DSL's
-- scoped keywords, one of which (`includes`) collides with the
-- `SlotConsensusSafety` field name in the `where` block below. Veil names
-- are used fully qualified instead.

namespace Chorus
open Classical ByzNodeSet

section Instance

variable {slot node nodeset merkle_root Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase]
  [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

/- The abstract field representation of the Chorus state at the canonical
`Classical` instances (cf. `Composition.lean`'s `afr%`). -/
local macro "afr%" f:ident : term =>
  `(@Chorus.instAbstractFieldRepresentation slot node nodeset merkle_root Phase PathChoice
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    $f)

/-- `i` has committed a positive entry `⟨J, M⟩` (state read at the canonical
representation). -/
noncomputable abbrev CommittedPos
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    (i J : node) (M : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_committed_pos)
    st.local_committed_pos i J M = true

/-- `i` has finalized (`local_committed`). -/
noncomputable abbrev CommittedAll
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    (i : node) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_committed) st.local_committed i = true

/-- `r` has recorded proposer `j`'s entry `m` (`local_entry_pos`) — the
per-validator half of `all_honest_recorded`. -/
noncomputable abbrev Recorded
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    (r j : node) (m : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_entry_pos) st.local_entry_pos r j m = true

/-- The slot is past its deadline: the phase is no longer `pre_deadline`. -/
noncomputable abbrev DeadlinePassed
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)) : Prop :=
  ¬ (@Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.phase) st.phase = Phase_Enum.pre_deadline)

/-- The Chorus state is inhabited. Veil derives this instance as part of the
model-check scaffolding, which `Chorus.lean` disables (its label enumeration
is `O(nᵏ)` in the action count); the composed system needs it because the
glue's `scstate` sort must be inhabited, so it is provided here. -/
noncomputable instance instInhabitedChorusState :
    Inhabited (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)) :=
  ⟨by constructor <;> exact default⟩

variable (th : Chorus.Theory slot node nodeset merkle_root Phase PathChoice)

/-- The proposal vector a committed validator holds: each proposer maps to
its committed positive root (if any), every non-proposer to `none`. -/
noncomputable def decisionVector
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    (i : node) : node → Option merkle_root :=
  fun J =>
    if th.is_proposer J = true then
      if hpos : ∃ M, CommittedPos st i J M then some hpos.choose else none
    else none

/-! ### Step-level facts, uniformly over all 38 actions

Each is proven by exposing every action's pre-computed transition body
(`<action>.ext.derived_eq`, then the `reducible` `<action>.ext.tr`),
substituting the post-state and evaluating the field-representation
`get`/`set` pair at the canonical representation. The commit relations are
only ever set to `true`, and `commit_assign_pos`/`commit_assign_neg` are
guarded by `¬ local_committed i`, so a committed validator's entries are
frozen. -/

/-- Expose one action's transition body in `h`. -/
local macro "chorus_tr" h:ident : tactic =>
  `(tactic| (simp only [Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct] at $h:ident
             simp only [
               Chorus.advance_to_deadline.ext.derived_eq, Chorus.advance_to_fb_arm.ext.derived_eq,
               Chorus.advance_to_mvba_arm.ext.derived_eq, Chorus.propose.ext.derived_eq,
               Chorus.deliver_chunk_assigned.ext.derived_eq, Chorus.record_chunk.ext.derived_eq,
               Chorus.vote.ext.derived_eq, Chorus.aggregate_fastqc_pos.ext.derived_eq,
               Chorus.aggregate_fastqc_neg.ext.derived_eq, Chorus.commit_sign_pos.ext.derived_eq,
               Chorus.commit_sign_neg.ext.derived_eq, Chorus.cast_fast_commit.ext.derived_eq,
               Chorus.broadcast_commitqc_pos.ext.derived_eq,
               Chorus.broadcast_commitqc_neg.ext.derived_eq, Chorus.fb_sign_pos.ext.derived_eq,
               Chorus.fb_sign_neg.ext.derived_eq, Chorus.cast_fallback_vote.ext.derived_eq,
               Chorus.mvba_decide_pos.ext.derived_eq, Chorus.mvba_decide_neg.ext.derived_eq,
               Chorus.mvba_terminate.ext.derived_eq, Chorus.redisseminate_chunk.ext.derived_eq,
               Chorus.cast_fb_commit.ext.derived_eq, Chorus.commit_assign_pos.ext.derived_eq,
               Chorus.commit_assign_neg.ext.derived_eq, Chorus.finalize_commit.ext.derived_eq,
               Chorus.byz_sign_proposer.ext.derived_eq, Chorus.byz_deliver_chunk.ext.derived_eq,
               Chorus.byz_sign_vote_pos.ext.derived_eq, Chorus.byz_sign_vote_neg.ext.derived_eq,
               Chorus.byz_cast_vote.ext.derived_eq, Chorus.byz_sign_fb_pos.ext.derived_eq,
               Chorus.byz_sign_fb_neg.ext.derived_eq, Chorus.byz_sign_fallback.ext.derived_eq,
               Chorus.byz_sign_commit_pos.ext.derived_eq,
               Chorus.byz_sign_commit_neg.ext.derived_eq, Chorus.byz_cast_commit.ext.derived_eq,
               Chorus.byz_sign_fbcommit.ext.derived_eq,
               Chorus.byz_release_msg_decrypt_share.ext.derived_eq] at $h:ident
             simp only [
               Chorus.advance_to_deadline.ext.tr, Chorus.advance_to_fb_arm.ext.tr,
               Chorus.advance_to_mvba_arm.ext.tr, Chorus.propose.ext.tr,
               Chorus.deliver_chunk_assigned.ext.tr, Chorus.record_chunk.ext.tr,
               Chorus.vote.ext.tr, Chorus.aggregate_fastqc_pos.ext.tr,
               Chorus.aggregate_fastqc_neg.ext.tr, Chorus.commit_sign_pos.ext.tr,
               Chorus.commit_sign_neg.ext.tr, Chorus.cast_fast_commit.ext.tr,
               Chorus.broadcast_commitqc_pos.ext.tr, Chorus.broadcast_commitqc_neg.ext.tr,
               Chorus.fb_sign_pos.ext.tr, Chorus.fb_sign_neg.ext.tr,
               Chorus.cast_fallback_vote.ext.tr, Chorus.mvba_decide_pos.ext.tr,
               Chorus.mvba_decide_neg.ext.tr, Chorus.mvba_terminate.ext.tr,
               Chorus.redisseminate_chunk.ext.tr, Chorus.cast_fb_commit.ext.tr,
               Chorus.commit_assign_pos.ext.tr, Chorus.commit_assign_neg.ext.tr,
               Chorus.finalize_commit.ext.tr, Chorus.byz_sign_proposer.ext.tr,
               Chorus.byz_deliver_chunk.ext.tr, Chorus.byz_sign_vote_pos.ext.tr,
               Chorus.byz_sign_vote_neg.ext.tr, Chorus.byz_cast_vote.ext.tr,
               Chorus.byz_sign_fb_pos.ext.tr, Chorus.byz_sign_fb_neg.ext.tr,
               Chorus.byz_sign_fallback.ext.tr, Chorus.byz_sign_commit_pos.ext.tr,
               Chorus.byz_sign_commit_neg.ext.tr, Chorus.byz_cast_commit.ext.tr,
               Chorus.byz_sign_fbcommit.ext.tr, Chorus.byz_release_msg_decrypt_share.ext.tr] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation, everywhere. -/
local macro "chorus_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [CommittedPos, CommittedAll, Recorded, DeadlinePassed,
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id] at *)

section StepFacts
variable {st st' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)}

set_option maxHeartbeats 4000000 in
/-- `local_committed` stands across every action. -/
theorem committedAll_mono
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (i : node) (h : CommittedAll st i) : CommittedAll st' i := by
  obtain ⟨l, htr⟩ := hn
  cases l <;> chorus_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    chorus_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 4000000 in
/-- `local_committed_pos` stands across every action. -/
theorem committedPos_mono
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (i J : node) (M : merkle_root) (h : CommittedPos st i J M) : CommittedPos st' i J M := by
  obtain ⟨l, htr⟩ := hn
  cases l <;> chorus_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    chorus_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 4000000 in
/-- A committed validator's positive entries are frozen: `commit_assign_pos`
requires `¬ local_committed i`. -/
theorem committedPos_frozen
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (i : node) (hc : CommittedAll st i) (J : node) (M : merkle_root)
    (h : CommittedPos st' i J M) : CommittedPos st i J M := by
  obtain ⟨l, htr⟩ := hn
  cases l <;> chorus_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    chorus_field_simp <;> first | exact h | (rcases h with ⟨rfl, rfl, rfl⟩ | h <;> simp_all)

set_option maxHeartbeats 4000000 in
/-- `local_entry_pos` stands across every action. -/
theorem recorded_mono
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (r j : node) (m : merkle_root) (h : Recorded st r j m) : Recorded st' r j m := by
  obtain ⟨l, htr⟩ := hn
  cases l <;> chorus_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    chorus_field_simp <;> first | exact h | (right; exact h)

/-- Initially nobody has committed. -/
theorem init_not_committed
    (hinit : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).init th st)
    (i : node) : ¬ CommittedAll st i := by
  simp only [Chorus.relationalTransitionSystem, Chorus.Init] at hinit
  simp only [Chorus.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); chorus_field_simp

/-- A committed validator's decision vector does not change. -/
theorem decisionVector_stable
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (i : node) (hc : CommittedAll st i) : decisionVector th st' i = decisionVector th st i := by
  have hiff : ∀ J M, CommittedPos st' i J M ↔ CommittedPos st i J M :=
    fun J M => ⟨committedPos_frozen th hn i hc J M, committedPos_mono th hn i J M⟩
  funext J
  unfold decisionVector
  by_cases hp : th.is_proposer J = true
  · rw [if_pos hp, if_pos hp]
    -- The two branches differ only in the predicate under the `∃`, and the
    -- predicates are equal.
    have hpred : (fun M => CommittedPos st' i J M) = (fun M => CommittedPos st i J M) :=
      funext fun M => propext (hiff J M)
    exact congrArg
      (fun P : merkle_root → Prop => (if hpos : ∃ M, P M then some hpos.choose else none : Option merkle_root))
      hpred
  · rw [if_neg hp, if_neg hp]

end StepFacts

set_option maxHeartbeats 1000000 in
/-- **`Chorus ⊨ SlotConsensusSafety`** — for every Chorus theory `th`, the
family of slot-indexed copies of the Chorus transition system is an instance
of the state-level slot-consensus contract, with `byz` the Byzantine
predicate of the module's `ByzNodeSet` instance. -/
@[implicit_reducible]
noncomputable def slotConsensusSafety :
    SlotConsensusSafety slot node merkle_root (slot × (node → Option merkle_root))
      (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
      (fun i => nset.is_byz i = true) where
  init _ st := (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).assumptions th ∧
    (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).init th st
  step _ st st' := (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st'
  trans _ st st' := (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st'
  reachable _ st := (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).reachable th st
  step_trans _ _ _ h := h
  reachable_init _ st h := Veil.RelationalTransitionSystem.reachable.init st h.1 h.2
  reachable_trans _ st st' hr hn := Veil.RelationalTransitionSystem.reachable.step st st' hr hn
  finalized s st i V := CommittedAll st i ∧ V = (s, decisionVector th st i)
  slot_of V := V.1
  includes V j P := V.2 j = some P
  on_time _ st j P := Chorus.all_honest_recorded (nset := nset)
    (χ := Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) j P th st
  finalized_mono _ st st' i V hn h :=
    ⟨committedAll_mono th hn i h.1, by rw [h.2, decisionVector_stable th hn i h.1]⟩
  on_time_mono _ st st' j P hn h :=
    ⟨h.1, h.2.1, fun r hr => recorded_mono th hn r j P (h.2.2.1 r hr), h.2.2.2⟩
  init_finalized _ _ i V h hf := init_not_committed th h.2 i hf.1
  agreement _ st hr i j V V' hci hcj hfi hfj := by
    obtain ⟨hci_com, hVi⟩ := hfi
    obtain ⟨hcj_com, hVj⟩ := hfj
    subst hVi; subst hVj
    refine Prod.ext rfl ?_
    show decisionVector th st i = decisionVector th st j
    funext J
    unfold decisionVector
    by_cases hp : th.is_proposer J = true
    · rw [if_pos hp, if_pos hp]
      by_cases hi : ∃ M, CommittedPos st i J M
      · -- `i` decided positively: so does `j` (completeness + pos/neg
        -- exclusion), and the roots agree.
        have hj' : ∃ M, CommittedPos st j J M := by
          rcases reachable_local_committed_complete hr j ⟨hcj, hcj_com⟩ J hp with hpos | hneg
          · exact hpos
          · obtain ⟨Mi, hMi⟩ := hi
            exact absurd hneg
              (reachable_agreement_pos_neg hr i j J Mi ⟨hci, hcj, hci_com, hcj_com, hMi⟩)
        rw [dif_pos hi, dif_pos hj']
        congr 1
        exact reachable_agreement_pos hr i j J hi.choose hj'.choose
          ⟨hci, hcj, hci_com, hcj_com, hi.choose_spec, hj'.choose_spec⟩
      · -- `i` decided negatively (completeness): so must `j`.
        have hj' : ¬ ∃ M, CommittedPos st j J M := by
          rintro ⟨M, hM⟩
          rcases reachable_local_committed_complete hr i ⟨hci, hci_com⟩ J hp with hpos | hneg
          · exact hi hpos
          · exact (reachable_agreement_pos_neg hr j i J M ⟨hcj, hci, hcj_com, hci_com, hM⟩) hneg
        rw [dif_neg hi, dif_neg hj']
    · rw [if_neg hp, if_neg hp]
  -- By construction: the family's instance for slot `s` tags its vectors
  -- with `s`.
  slot_safety _ _ _ _ _ _ hf := by rw [hf.2]
  proposal_inclusion _ st hr i j V P hci hfi hot := by
    obtain ⟨hcom, hV⟩ := hfi
    subst hV
    show decisionVector th st i j = some P
    have hp : th.is_proposer j = true := hot.2.1
    unfold decisionVector
    rw [if_pos hp]
    have hex : ∃ M, CommittedPos st i j M := by
      rcases reachable_local_committed_complete hr i ⟨hci, hcom⟩ j hp with hpos | hneg
      · exact hpos
      · exact absurd hneg (reachable_proposal_inclusion_no_neg hr j i P ⟨hot, hci⟩)
    rw [dif_pos hex]
    congr 1
    exact reachable_proposal_inclusion hr j i P hex.choose ⟨hot, hci, hex.choose_spec⟩

/-! ### The residual: what the full `SlotConsensus` still owes

Chorus has no participation interface, no clock and no message type at the
contract's level of abstraction, so the whole upper level except Hiding's
protocol half is residual. The structure below restates those fields over
the Chorus transition system; `slotConsensus_of_residual` proves they are
all that is missing and discharges `hiding_residue` from
`safety [hiding_until_deadline]`. `docs/Architecture.md` §4 item 4 lists the
temporal rows by their meta-axiom names ((A-sc-termination) is
`termination` here); this structure is that list as a type, together with
the interface Chorus does not model. -/
structure SlotConsensusResidual (time message : Type) [TotalOrder time] [Add time] where
  participate : slot → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) →
    node → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) → Prop
  abandon : slot → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) →
    node → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) → Prop
  propose : slot → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) →
    node → merkle_root → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) → Prop
  participate_trans : ∀ s st i st', participate s st i st' → (slotConsensusSafety th).trans s st st'
  abandon_trans : ∀ s st i st', abandon s st i st' → (slotConsensusSafety th).trans s st st'
  propose_trans : ∀ s st i P st', propose s st i P st' → (slotConsensusSafety th).trans s st st'
  participating : slot → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) → node → Prop
  abandoned : slot → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) → node → Prop
  proposed : slot → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) → node → merkle_root → Prop
  sent : slot → Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) → node → message → Prop
  participating_mono : ∀ s st st' i, (slotConsensusSafety th).trans s st st' → participating s st i → participating s st' i
  abandoned_mono : ∀ s st st' i, (slotConsensusSafety th).trans s st st' → abandoned s st i → abandoned s st' i
  proposed_mono : ∀ s st st' i P, (slotConsensusSafety th).trans s st st' → proposed s st i P → proposed s st' i P
  sent_mono : ∀ s st st' i m, (slotConsensusSafety th).trans s st st' → sent s st i m → sent s st' i m
  participate_effect : ∀ s st i st', participate s st i st' → participating s st' i
  abandon_effect : ∀ s st i st', abandon s st i st' → abandoned s st' i
  propose_effect : ∀ s st i P st', propose s st i P st' → proposed s st' i P
  participating_step_frame : ∀ s st st' i, (slotConsensusSafety th).step s st st' → ¬ nset.is_byz i = true →
    (participating s st' i ↔ participating s st i)
  abandoned_step_frame : ∀ s st st' i, (slotConsensusSafety th).step s st st' → ¬ nset.is_byz i = true →
    (abandoned s st' i ↔ abandoned s st i)
  proposed_step_frame : ∀ s st st' i P, (slotConsensusSafety th).step s st st' → ¬ nset.is_byz i = true →
    (proposed s st' i P ↔ proposed s st i P)
  init_participating : ∀ s st i, (slotConsensusSafety th).init s st → ¬ participating s st i
  init_abandoned : ∀ s st i, (slotConsensusSafety th).init s st → ¬ abandoned s st i
  init_proposed : ∀ s st i P, (slotConsensusSafety th).init s st → ¬ proposed s st i P
  clock : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) → time
  Admissible : ∀ s, TimedRun (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)) time
    ((slotConsensusSafety th).init s) ((slotConsensusSafety th).trans s) clock → Prop
  admissible_exists : ∀ s st, (slotConsensusSafety th).init s st →
    ∃ r : TimedRun (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)) time
      ((slotConsensusSafety th).init s) ((slotConsensusSafety th).trans s) clock, Admissible s r ∧ r.at' 0 = st
  /-- **(A-sc-termination)**, eventual form. -/
  termination : ∀ s (r : TimedRun (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)) time
      ((slotConsensusSafety th).init s) ((slotConsensusSafety th).trans s) clock), Admissible s r →
    (∀ i, ¬ nset.is_byz i = true → r.eventually (fun st => participating s st i)) →
    (∀ i, ¬ nset.is_byz i = true → ∀ n, abandoned s (r.at' n) i →
      ∃ V, (slotConsensusSafety th).finalized s (r.at' n) i V) →
    ∀ j, ¬ nset.is_byz j = true → r.eventually (fun st => ∃ V, (slotConsensusSafety th).finalized s st j V)
  /-- Quiescence: Chorus's in-model shadow is phase confinement; the
      participation-window statement needs the interface it lacks. -/
  quiescence : ∀ s (r : TimedRun (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)) time
      ((slotConsensusSafety th).init s) ((slotConsensusSafety th).trans s) clock), Admissible s r →
    ∀ n i m, ¬ nset.is_byz i = true → sent s (r.at' (n + 1)) i m → ¬ sent s (r.at' n) i m →
      participating s (r.at' (n + 1)) i ∧ ¬ abandoned s (r.at' n) i

/-- Given the residual, Chorus is a full `SlotConsensus`. The one upper-level
field Chorus proves — Hiding's protocol half — is discharged here:
`payload_recoverable` is the module's `slot_key_released` (the decryption
threshold has been reached), `deadline_passed` its phase leaving
`pre_deadline`, and `safety [hiding_until_deadline]` is exactly the
implication. -/
@[implicit_reducible]
noncomputable def slotConsensus_of_residual {time message : Type} [TotalOrder time] [Add time]
    (h : SlotConsensusResidual th time message) :
    SlotConsensus slot node merkle_root (slot × (node → Option merkle_root))
      (Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
      time message (fun i => nset.is_byz i = true) where
  toSlotConsensusSafety := slotConsensusSafety th
  participate := h.participate
  abandon := h.abandon
  propose := h.propose
  participate_trans := h.participate_trans
  abandon_trans := h.abandon_trans
  propose_trans := h.propose_trans
  participating := h.participating
  abandoned := h.abandoned
  proposed := h.proposed
  sent := h.sent
  participating_mono := h.participating_mono
  abandoned_mono := h.abandoned_mono
  proposed_mono := h.proposed_mono
  sent_mono := h.sent_mono
  participate_effect := h.participate_effect
  abandon_effect := h.abandon_effect
  propose_effect := h.propose_effect
  participating_step_frame := h.participating_step_frame
  abandoned_step_frame := h.abandoned_step_frame
  proposed_step_frame := h.proposed_step_frame
  init_participating := h.init_participating
  init_abandoned := h.init_abandoned
  init_proposed := h.init_proposed
  clock := h.clock
  Admissible := h.Admissible
  admissible_exists := h.admissible_exists
  termination := h.termination
  deadline_passed _ st := DeadlinePassed st
  payload_recoverable _ st := Chorus.slot_key_released (nset := nset)
    (χ := Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) th st
  hiding_residue _ _ hr hk := reachable_hiding_until_deadline hr hk
  quiescence := h.quiescence

end Instance
end Chorus

/-! ## The pinned trust base

The instance rests on the standard Lean trio and nothing else — in
particular, **no `sorryAx`**: no trusted-SMT step and no statement stub
anywhere in the chain. The Chorus model persists no per-VC theorems (its
VC *statements* are carried claim-free by the persistent VC registry);
the composition consumes the **proof-file family** (`Chorus/Proofs/`):
one file per action, each re-proving its action's
registered VC statements from scratch as fresh kernel-checked
reconstructions (`veil.smt.trust false`), persisted as real proofs in
small per-file oleans and assembled into one preservation lemma. A
regression anywhere in that chain — a proof silently degrading to a
stub, trusted SMT reappearing — fails this guard. The residual-conditioned
full instance is pinned too: its assumptions enter as a *hypothesis*, never
as an axiom. -/

/--
info: 'Chorus.slotConsensusSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensusSafety

/--
info: 'Chorus.slotConsensus_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensus_of_residual
