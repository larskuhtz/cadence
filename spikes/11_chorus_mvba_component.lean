import Cadence.Chorus
import Cadence.Mvba.Compose
import Cadence.Fairness

/-! Spike 11 (2026-09-16): **the MVBA is a `Component` of Chorus** at the
system's instantiation — the reassessment evidence behind
`docs/Liveness.md` §4.2, run before stage 2 of the Chorus run-level liveness
leg is written for real.

Stage 1 of that leg added the generic `Cadence.Component` /
`Component.Projection` to `Cadence/Fairness.lean`: a part held inside a whole,
the projection of a composed run onto the part's steps, and weak fairness
transferred across the re-indexing. The question this spike answers is
whether the generic shape fits the *generated* Chorus artefacts at
`mvba := Mvba.mvbaSafety thM` (the instantiation `Cadence/System.lean` uses)
without a model change, a new cell, or a hand-written case analysis that has
to be maintained. It does, and each of the five fields comes from where the
file says:

* `isSub` — a two-constructor match on `Chorus.Label`;
* `frame` — M13's generated `Chorus.<action>.frame_mvba_st`, one per other
  action, dispatched by `cases l` with a named `case` each. Two mechanics
  worth knowing, both recorded in §4.2: the `MVBASafety` instance is a term
  at this instantiation and has to be brought into scope with `letI` before
  the generated lemmas apply, and a `first | …` over the forty lemmas instead
  of named cases times out in `whnf`;
* `step` — the two oracle actions' guards, read off their transition bodies
  with the `chorus_tr` / field-simp pattern of `Cadence/Composition.lean`:
  `mvba_step` requires `mvba.step`, which at this instance *is* "some
  non-input `Mvba` label's transition", and `mvba_propose` requires
  `mvba.propose`, the `propose` label's;
* `init` — the one hand proof. `mvba_st` is seeded from the theory's
  `mvba_init_state`, not a literal, so M13 emits no `mvba_st.init`; the value
  is read off the initializer's transition by exposing it and evaluating the
  field representation (a single leaf, nothing to destructure). At this
  instance Chorus's `[mvba_init]` assumption is exactly
  `sub.assumptions ∧ sub.init`.

Expected: `exit 0`, the three `#print axioms` at
`[propext, Classical.choice, Quot.sound]`. Nothing here is imported by the
build; stage 2 lands the same content as a real module with the label
classes and the premises around it. -/

open Veil
open Classical

namespace Chorus

section
variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

variable {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice}
variable {thM : Mvba.Theory node nodeset (node → Option merkle_root) view}
variable {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)}

/-- The labels of Chorus that are the MVBA's own steps. -/
def IsMvbaLabel : Chorus.Label slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice → Prop
  | .mvba_step _ => True
  | .mvba_propose .. => True
  | _ => False

/-- Expose an action's transition body (`Cadence/Composition.lean`'s
`conductor_tr`, for Chorus). -/
local macro "chorus_tr" h:ident : tactic =>
  `(tactic| (simp only [Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation, in every hypothesis and the goal. -/
local macro "chorus_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id] at *)

set_option maxHeartbeats 1000000 in
/-- Every action other than the two oracle actions leaves `mvba_st` alone:
the generated per-action frame lemmas, one `case` each. -/
theorem mvba_st_frame_of_not_mvba
    (l : Chorus.Label slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root
        (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
        (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice
        (mvba := Mvba.mvbaSafety thM)).tr thS s l s')
    (hl : ¬ IsMvbaLabel l) : s'.mvba_st = s.mvba_st := by
  letI : MVBASafety node (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (fun i => nset.is_byz i = true) := Mvba.mvbaSafety thM
  cases l
  case mvba_step => exact absurd trivial hl
  case mvba_propose => exact absurd trivial hl
  case advance_to_deadline => exact Chorus.advance_to_deadline.frame_mvba_st htr
  case advance_to_fb_arm => exact Chorus.advance_to_fb_arm.frame_mvba_st htr
  case advance_to_mvba_arm => exact Chorus.advance_to_mvba_arm.frame_mvba_st htr
  case propose => exact Chorus.propose.frame_mvba_st htr
  case deliver_chunk_assigned => exact Chorus.deliver_chunk_assigned.frame_mvba_st htr
  case record_chunk => exact Chorus.record_chunk.frame_mvba_st htr
  case vote => exact Chorus.vote.frame_mvba_st htr
  case aggregate_fastqc_pos => exact Chorus.aggregate_fastqc_pos.frame_mvba_st htr
  case aggregate_fastqc_neg => exact Chorus.aggregate_fastqc_neg.frame_mvba_st htr
  case commit_sign_pos => exact Chorus.commit_sign_pos.frame_mvba_st htr
  case commit_sign_neg => exact Chorus.commit_sign_neg.frame_mvba_st htr
  case cast_fast_commit => exact Chorus.cast_fast_commit.frame_mvba_st htr
  case broadcast_commitqc_pos => exact Chorus.broadcast_commitqc_pos.frame_mvba_st htr
  case broadcast_commitqc_neg => exact Chorus.broadcast_commitqc_neg.frame_mvba_st htr
  case fb_sign_pos => exact Chorus.fb_sign_pos.frame_mvba_st htr
  case fb_sign_neg => exact Chorus.fb_sign_neg.frame_mvba_st htr
  case cast_fallback_vote => exact Chorus.cast_fallback_vote.frame_mvba_st htr
  case on_mvba_decide_pos => exact Chorus.on_mvba_decide_pos.frame_mvba_st htr
  case on_mvba_decide_neg => exact Chorus.on_mvba_decide_neg.frame_mvba_st htr
  case mvba_terminate => exact Chorus.mvba_terminate.frame_mvba_st htr
  case redisseminate_chunk => exact Chorus.redisseminate_chunk.frame_mvba_st htr
  case cast_fb_commit => exact Chorus.cast_fb_commit.frame_mvba_st htr
  case commit_assign_pos => exact Chorus.commit_assign_pos.frame_mvba_st htr
  case commit_assign_neg => exact Chorus.commit_assign_neg.frame_mvba_st htr
  case finalize_commit => exact Chorus.finalize_commit.frame_mvba_st htr
  case byz_sign_proposer => exact Chorus.byz_sign_proposer.frame_mvba_st htr
  case byz_deliver_chunk => exact Chorus.byz_deliver_chunk.frame_mvba_st htr
  case byz_sign_vote_pos => exact Chorus.byz_sign_vote_pos.frame_mvba_st htr
  case byz_sign_vote_neg => exact Chorus.byz_sign_vote_neg.frame_mvba_st htr
  case byz_cast_vote => exact Chorus.byz_cast_vote.frame_mvba_st htr
  case byz_sign_fb_pos => exact Chorus.byz_sign_fb_pos.frame_mvba_st htr
  case byz_sign_fb_neg => exact Chorus.byz_sign_fb_neg.frame_mvba_st htr
  case byz_sign_fallback => exact Chorus.byz_sign_fallback.frame_mvba_st htr
  case byz_sign_commit_pos => exact Chorus.byz_sign_commit_pos.frame_mvba_st htr
  case byz_sign_commit_neg => exact Chorus.byz_sign_commit_neg.frame_mvba_st htr
  case byz_cast_commit => exact Chorus.byz_cast_commit.frame_mvba_st htr
  case byz_sign_fbcommit => exact Chorus.byz_sign_fbcommit.frame_mvba_st htr
  case byz_release_msg_decrypt_share => exact Chorus.byz_release_msg_decrypt_share.frame_mvba_st htr

set_option maxHeartbeats 1000000 in
/-- `mvba_step`'s guard is `mvba.step`, which at the `Mvba` instance is some
non-input label's transition. -/
theorem mvba_step_tr {mvba_next}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root
        (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
        (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice
        (mvba := Mvba.mvbaSafety thM)).tr thS s (.mvba_step mvba_next) s') :
    ∃ l', (Mvba.relationalTransitionSystem node nodeset (node → Option merkle_root) view).tr thM
      s.mvba_st l' s'.mvba_st := by
  chorus_tr htr
  obtain ⟨hstep, htr⟩ := htr
  chorus_field_simp
  obtain ⟨l', -, hl'⟩ := hstep
  subst htr
  exact ⟨l', hl'⟩

set_option maxHeartbeats 1000000 in
/-- `mvba_propose`'s last guard is `mvba.propose`, the `propose` label's
transition. -/
theorem mvba_propose_tr {i v mvba_next}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root
        (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
        (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice
        (mvba := Mvba.mvbaSafety thM)).tr thS s (.mvba_propose i v mvba_next) s') :
    (Mvba.relationalTransitionSystem node nodeset (node → Option merkle_root) view).tr thM
      s.mvba_st (.propose i v) s'.mvba_st := by
  chorus_tr htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨hprop, htr⟩ := htr
  chorus_field_simp
  subst htr
  exact hprop

set_option maxHeartbeats 1000000 in
/-- The initial value of `mvba_st`, read off the initializer's transition
(no generated `mvba_st.init`: the seed is the theory's, not a literal). -/
theorem mvba_st_init
    (hi : (Chorus.relationalTransitionSystem slot node nodeset merkle_root
        (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
        (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice
        (mvba := Mvba.mvbaSafety thM)).init thS s) : s.mvba_st = thS.mvba_init_state := by
  simp only [Chorus.relationalTransitionSystem, Chorus.Init, Chorus.initializer.ext.tr] at hi
  subst_vars
  chorus_field_simp

/-- **The MVBA is a component of Chorus**, at the instantiation
`Cadence/System.lean` uses. -/
noncomputable def mvbaComponent
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view) :
    Cadence.Component
      (Chorus.relationalTransitionSystem slot node nodeset merkle_root
        (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
        (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice
        (mvba := Mvba.mvbaSafety thM)) thS
      (Mvba.relationalTransitionSystem node nodeset (node → Option merkle_root) view) thM where
  proj st := st.mvba_st
  isSub := IsMvbaLabel
  init s ha hi := by
    obtain ⟨hinit, -, -⟩ := ha
    rw [mvba_st_init hi]
    exact hinit
  frame _ l _ htr hl := mvba_st_frame_of_not_mvba l htr hl
  step _ l _ htr hl := by
    cases l with
    | mvba_step mvba_next => exact mvba_step_tr htr
    | mvba_propose i v mvba_next => exact ⟨.propose i v, mvba_propose_tr htr⟩
    | _ => exact absurd hl id

end
end Chorus

#print axioms Chorus.mvba_st_frame_of_not_mvba
#print axioms Chorus.mvba_st_init
#print axioms Chorus.mvbaComponent
