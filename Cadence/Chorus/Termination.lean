import Cadence.Chorus.Liveness
import Cadence.Chorus.Progress

namespace Chorus

open Cadence

section PhaseOrder

variable {Phase : Type} [Phase_Enum : Chorus.Phase_EnumClass Phase]

/-- The four phases are distinct (the enum's `distinct` field, unpacked). -/
theorem phase_distinct :
    (Phase_EnumClass.pre_deadline : Phase) ≠ Phase_EnumClass.post_deadline ∧
    (Phase_EnumClass.pre_deadline : Phase) ≠ Phase_EnumClass.post_fb_arm ∧
    (Phase_EnumClass.pre_deadline : Phase) ≠ Phase_EnumClass.post_mvba_arm ∧
    (Phase_EnumClass.post_deadline : Phase) ≠ Phase_EnumClass.post_fb_arm ∧
    (Phase_EnumClass.post_deadline : Phase) ≠ Phase_EnumClass.post_mvba_arm ∧
    (Phase_EnumClass.post_fb_arm : Phase) ≠ Phase_EnumClass.post_mvba_arm := by
  have hd := Phase_Enum.distinct
  simp [distinctN, distinctPairs, andN] at hd
  tauto

end PhaseOrder

section Steps

open Classical

variable {slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited mstate] [Inhabited mvalue] [Inhabited mmsg]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [mvba : MVBASafety node mvalue mmsg mstate (fun i => nset.is_byz i = true)]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice}
  {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)}

/-- Expose an action's transition body. -/
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

open Lean in
/-- One `case <action> => have <h> := Chorus.<action>.frame_<field> <htr>; <tac>`
line per listed action. -/
local macro "frame_cases " htr:ident fld:ident hfr:ident "[" acts:ident,* "]" "=>" tac:tactic : tactic => do
  let mut acc ← `(tactic| skip)
  for a in acts.getElems do
    let lem := mkIdent (`Chorus ++ a.getId ++ Name.mkSimple ("frame_" ++ fld.getId.toString))
    acc ← `(tactic| ($acc; case $a:ident => (have $hfr := $lem:ident $htr; $tac)))
  return acc

set_option maxHeartbeats 1000000 in
theorem phase_step {l}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s l s') :
    s'.phase = s.phase ∨
    (s.phase = Phase_EnumClass.pre_deadline ∧ s'.phase = Phase_EnumClass.post_deadline) ∨
    (s.phase = Phase_EnumClass.post_deadline ∧ s'.phase = Phase_EnumClass.post_fb_arm) ∨
    (s.phase = Phase_EnumClass.post_fb_arm ∧ s'.phase = Phase_EnumClass.post_mvba_arm) := by
  cases l
  case advance_to_deadline | advance_to_fb_arm | advance_to_mvba_arm =>
    chorus_tr htr
    obtain ⟨h, rfl⟩ := htr
    chorus_field_simp
    simp [h]
  frame_cases htr phase hfr
    [propose, deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos,
     aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit,
     broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg,
     cast_fallback_vote, mvba_step, mvba_propose, on_mvba_decide_pos, on_mvba_decide_neg,
     mvba_terminate, redisseminate_chunk, cast_fb_commit, commit_assign_pos, commit_assign_neg,
     finalize_commit, byz_sign_proposer, byz_deliver_chunk, byz_sign_vote_pos,
     byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback,
     byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_sign_fbcommit,
     byz_release_msg_decrypt_share] => exact Or.inl hfr

set_option maxHeartbeats 1000000 in
theorem commit_cast_flip {l} {i : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true)
    (h0 : ¬ s.msg_commit_cast i = true) (h1 : s'.msg_commit_cast i = true) :
    ∀ J, th.is_proposer J = true →
      (∃ M, s.msg_commit_pos_sig i J M = true) ∨ s.msg_commit_neg_sig i J = true := by
  cases l
  case cast_fast_commit i' =>
    chorus_tr htr
    obtain ⟨-, -, -, hsig, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hne
    · exact hsig
    · simp_all
  case byz_cast_commit r =>
    chorus_tr htr
    obtain ⟨hr, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne r i with rfl | hne
    · simp_all
    · simp_all
  frame_cases htr msg_commit_cast hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, broadcast_commitqc_pos, broadcast_commitqc_neg,
     fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, on_mvba_decide_pos,
     on_mvba_decide_neg, mvba_terminate, redisseminate_chunk, cast_fb_commit,
     commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos,
     byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg,
     byz_sign_fbcommit, byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
theorem fallback_sig_flip {l} {i : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true)
    (h0 : ¬ s.msg_fallback_sig i = true) (h1 : s'.msg_fallback_sig i = true) :
    ∀ J, th.is_proposer J = true →
      (∃ M, s.msg_fb_pos_sig i J M = true) ∨ s.msg_fb_neg_sig i J = true := by
  cases l
  case cast_fallback_vote i' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, hsig, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hne
    · exact hsig
    · simp_all
  case byz_sign_fallback r =>
    chorus_tr htr
    obtain ⟨hr, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne r i with rfl | hne
    · simp_all
    · simp_all
  frame_cases htr msg_fallback_sig hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, mvba_step, mvba_propose,
     on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk,
     cast_fb_commit, commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos,
     byz_sign_fb_neg, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_sign_fbcommit, byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
theorem path_fallback_flip {l} {i : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s l s')
    (h0 : ¬ s.local_path i = PathChoice_EnumClass.fallback) (h1 : s'.local_path i = PathChoice_EnumClass.fallback) :
    s'.msg_fallback_sig i = true := by
  cases l
  case cast_fast_commit i' =>
    have hff : (PathChoice_EnumClass.fast : PathChoice) ≠ PathChoice_EnumClass.fallback := by
      have hd := PathChoice_Enum.distinct
      simp [distinctN, distinctPairs, andN] at hd
      tauto
    chorus_tr htr
    obtain ⟨-, -, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hne
    · exact absurd (by simpa using h1) hff
    · simp_all
  case cast_fallback_vote i' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hne
    · simp
    · simp_all
  frame_cases htr local_path hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, broadcast_commitqc_pos, broadcast_commitqc_neg,
     fb_sign_pos, fb_sign_neg, mvba_step, mvba_propose, on_mvba_decide_pos, on_mvba_decide_neg,
     mvba_terminate, redisseminate_chunk, cast_fb_commit, commit_assign_pos, commit_assign_neg,
     finalize_commit, byz_sign_proposer, byz_deliver_chunk, byz_sign_vote_pos,
     byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback,
     byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_sign_fbcommit,
     byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0

/-- Turn an enabledness goal into the action's guards. -/
local macro "chorus_enabled" : tactic =>
  `(tactic| simp only [Enabled, Chorus.relationalTransitionSystem, Chorus.Next,
      Chorus.NextAct, trSimp])

/-! ### Enabledness and effect, per action the chains fire -/

theorem enabled_advance_to_deadline (h : s.phase = Phase_EnumClass.pre_deadline) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s .advance_to_deadline := by
  chorus_enabled
  exact ⟨_, h, rfl⟩

theorem advance_to_deadline_effect (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s .advance_to_deadline s') :
    s'.phase = Phase_EnumClass.post_deadline := by
  chorus_tr htr
  obtain ⟨-, rfl⟩ := htr
  chorus_field_simp

theorem enabled_advance_to_fb_arm (h : s.phase = Phase_EnumClass.post_deadline) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s .advance_to_fb_arm := by
  chorus_enabled
  exact ⟨_, h, rfl⟩

theorem advance_to_fb_arm_effect (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s .advance_to_fb_arm s') :
    s'.phase = Phase_EnumClass.post_fb_arm := by
  chorus_tr htr
  obtain ⟨-, rfl⟩ := htr
  chorus_field_simp

theorem enabled_vote {i : node} (hi : ¬ nset.is_byz i = true)
    (hph : s.phase ≠ Phase_EnumClass.pre_deadline) (hnv : ¬ s.local_voted i = true) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s (.vote i) := by
  chorus_enabled
  exact ⟨_, hi, hph, hnv, rfl⟩

theorem vote_effect {i : node} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s (.vote i) s') :
    s'.local_voted i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_fb_sign_pos {i j : node} {m : merkle_root} {q qc qv : nodeset}
    (hi : ¬ nset.is_byz i = true)
    (hph : s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
    (hv : s.local_voted i = true) (hnc : ¬ s.msg_commit_cast i = true)
    (hpath : ¬ s.local_path i = PathChoice_EnumClass.fallback) (hj : th.is_proposer j = true)
    (hqv : nset.supermajority qv) (hqvc : ∀ r, nset.member r qv = true → s.msg_vote_cast r = true)
    (hq : nset.greater_than_third q) (hqs : ∀ r, nset.member r q = true → s.msg_vote_pos_sig r j m = true)
    (hqc : nset.greater_than_third qc) (hqcs : ∀ r, nset.member r qc = true → s.msg_chunk_received r j m = true)
    (hwe : th.well_encoded m = true) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s (.fb_sign_pos i j m q qc) := by
  chorus_enabled
  exact ⟨_, hi, hph, hv, hnc, hpath, hj, ⟨qv, hqv, hqvc⟩, hq, hqs, hqc, hqcs, hwe, rfl⟩

theorem fb_sign_pos_effect {i j : node} {m : merkle_root} {q qc : nodeset}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s (.fb_sign_pos i j m q qc) s') :
    s'.msg_fb_pos_sig i j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_fb_sign_neg {i j : node} {qv : nodeset}
    (hi : ¬ nset.is_byz i = true)
    (hph : s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
    (hv : s.local_voted i = true) (hnc : ¬ s.msg_commit_cast i = true)
    (hpath : ¬ s.local_path i = PathChoice_EnumClass.fallback) (hj : th.is_proposer j = true)
    (hqv : nset.supermajority qv) (hqvc : ∀ r, nset.member r qv = true → s.msg_vote_cast r = true)
    (hnone : ∀ M q qc, ¬ (nset.greater_than_third q ∧
      (∀ r, nset.member r q = true → nset.member r qv = true ∧ s.msg_vote_pos_sig r j M = true) ∧
      nset.greater_than_third qc ∧
      (∀ r, nset.member r qc = true → s.msg_chunk_received r j M = true) ∧
      th.well_encoded M = true)) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s (.fb_sign_neg i j qv) := by
  chorus_enabled
  exact ⟨_, hi, hph, hv, hnc, hpath, hj, hqv, hqvc,
    fun M q qc h1 h2 h3 h4 h5 => hnone M q qc ⟨h1, h2, h3, h4, h5⟩, rfl⟩

theorem fb_sign_neg_effect {i j : node} {qv : nodeset}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s (.fb_sign_neg i j qv) s') :
    s'.msg_fb_neg_sig i j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_cast_fallback_vote {i : node}
    (hi : ¬ nset.is_byz i = true)
    (hph : s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
    (hv : s.local_voted i = true) (hnc : ¬ s.msg_commit_cast i = true)
    (hpath : ¬ s.local_path i = PathChoice_EnumClass.fallback)
    (hall : ∀ J, th.is_proposer J = true →
      (∃ M, s.msg_fb_pos_sig i J M = true) ∨ s.msg_fb_neg_sig i J = true) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s (.cast_fallback_vote i) := by
  chorus_enabled
  exact ⟨_, hi, hph, hv, hnc, hpath, hall, rfl⟩

theorem cast_fallback_vote_effect {i : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s (.cast_fallback_vote i) s') :
    s'.msg_fallback_sig i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_broadcast_commitqc_pos {j : node} {m : merkle_root} {q : nodeset}
    (hq : nset.supermajority q)
    (hall : ∀ r, nset.member r q = true →
      s.msg_commit_pos_sig r j m = true ∧ s.msg_commit_cast r = true) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s (.broadcast_commitqc_pos j m q) := by
  chorus_enabled
  exact ⟨_, hq, hall, rfl⟩

theorem broadcast_commitqc_pos_effect {j : node} {m : merkle_root} {q : nodeset}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s (.broadcast_commitqc_pos j m q) s') :
    s'.msg_commitqc_pos j m = true := by
  chorus_tr htr
  obtain ⟨-, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_broadcast_commitqc_neg {j : node} {q : nodeset}
    (hq : nset.supermajority q)
    (hall : ∀ r, nset.member r q = true →
      s.msg_commit_neg_sig r j = true ∧ s.msg_commit_cast r = true) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s (.broadcast_commitqc_neg j q) := by
  chorus_enabled
  exact ⟨_, hq, hall, rfl⟩

theorem broadcast_commitqc_neg_effect {j : node} {q : nodeset}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s (.broadcast_commitqc_neg j q) s') :
    s'.msg_commitqc_neg j = true := by
  chorus_tr htr
  obtain ⟨-, -, rfl⟩ := htr
  chorus_field_simp

/-- `commit_assign_pos`, enabled for a validator that has assigned nothing
for `j` yet: its two consistency guards then hold vacuously. -/
theorem enabled_commit_assign_pos {i j : node} {m : merkle_root}
    (hi : ¬ nset.is_byz i = true) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true) (hqc : s.msg_commitqc_pos j m = true)
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) (hnn : ¬ s.local_committed_neg i j = true) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s (.commit_assign_pos i j m) := by
  chorus_enabled
  exact ⟨_, hi, hnc, hj, Or.inl hqc, fun m' h => absurd h (hnp m'), hnn, rfl⟩

theorem commit_assign_pos_effect {i j : node} {m : merkle_root}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s (.commit_assign_pos i j m) s') :
    s'.local_committed_pos i j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_commit_assign_neg {i j : node}
    (hi : ¬ nset.is_byz i = true) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true) (hqc : s.msg_commitqc_neg j = true)
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s (.commit_assign_neg i j) := by
  chorus_enabled
  exact ⟨_, hi, hnc, hj, Or.inl hqc, hnp, rfl⟩

theorem commit_assign_neg_effect {i j : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s (.commit_assign_neg i j) s') :
    s'.local_committed_neg i j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_finalize_commit {i : node}
    (hi : ¬ nset.is_byz i = true) (hnc : ¬ s.local_committed i = true)
    (hall : ∀ J, th.is_proposer J = true →
      (∃ M, s.local_committed_pos i J M = true) ∨ s.local_committed_neg i J = true) :
    Enabled (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) th s (.finalize_commit i) := by
  chorus_enabled
  exact ⟨_, hi, hnc, hall, rfl⟩

theorem finalize_commit_effect {i : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s (.finalize_commit i) s') :
    s'.local_committed i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, rfl⟩ := htr
  chorus_field_simp

end Steps

/-! ## Run-level facts -/

section RunFacts

open Classical

variable {slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited mstate] [Inhabited mvalue] [Inhabited mmsg]
  [Inhabited Phase] [Inhabited PathChoice]
  {nset : ByzNodeSet node nodeset}
  {cnt : Cadence.ByzNodeSetCounting node nodeset nset}
  {mvba : MVBASafety node mvalue mmsg mstate (fun i => nset.is_byz i = true)}
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice}

/-- A labelled run of Chorus at any MVBA instance. -/
local notation "CRun" => LRun (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)

/-- **Saturation** of one validator — the `hsat` shape of
`progress_dichotomy_of_saturation`: it has cast its fast commit vote with a
commit signature for every proposer, or its fallback vote with a fallback
signature for every proposer. -/
def Saturated (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice))
    (i : node) : Prop :=
  (st.msg_commit_cast i = true ∧ ∀ j, th.is_proposer j = true →
    (∃ m, st.msg_commit_pos_sig i j m = true) ∨ st.msg_commit_neg_sig i j = true) ∨
  (st.msg_fallback_sig i = true ∧ ∀ j, th.is_proposer j = true →
    (∃ m, st.msg_fb_pos_sig i j m = true) ∨ st.msg_fb_neg_sig i j = true)

/-- Saturation is monotone along every step: every relation in it is. -/
theorem Saturated.step
    {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)}
    {l} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s l s')
    {i : node} (h : Saturated th s i) : Saturated th s' i := by
  rcases h with ⟨hc, hs⟩ | ⟨hc, hs⟩
  · refine Or.inl ⟨Chorus.msg_commit_cast.mono htr i hc, fun j hj => ?_⟩
    rcases hs j hj with ⟨m, hm⟩ | hm
    · exact Or.inl ⟨m, Chorus.msg_commit_pos_sig.mono htr i j m hm⟩
    · exact Or.inr (Chorus.msg_commit_neg_sig.mono htr i j hm)
  · refine Or.inr ⟨Chorus.msg_fallback_sig.mono htr i hc, fun j hj => ?_⟩
    rcases hs j hj with ⟨m, hm⟩ | hm
    · exact Or.inl ⟨m, Chorus.msg_fb_pos_sig.mono htr i j m hm⟩
    · exact Or.inr (Chorus.msg_fb_neg_sig.mono htr i j hm)

/-- **A correct validator's fast commit vote carries a commit signature per
proposer, at every point of every run.** Not an invariant of the model: the
first index at which `msg_commit_cast i` holds is a `cast_fast_commit i`
step (`commit_cast_flip`), whose guard is the signatures, and signatures are
monotone. -/
theorem commit_cast_sigs (r : CRun th) {i : node} (hi : ¬ nset.is_byz i = true) :
    ∀ n, (r.at' n).msg_commit_cast i = true → ∀ j, th.is_proposer j = true →
      (∃ m, (r.at' n).msg_commit_pos_sig i j m = true) ∨ (r.at' n).msg_commit_neg_sig i j = true
  | 0, h => by simp [Chorus.msg_commit_cast.init r.starts i] at h
  | n + 1, h => by
    have carry : ∀ j, th.is_proposer j = true →
        ((∃ m, (r.at' n).msg_commit_pos_sig i j m = true) ∨ (r.at' n).msg_commit_neg_sig i j = true) →
        (∃ m, (r.at' (n + 1)).msg_commit_pos_sig i j m = true) ∨
          (r.at' (n + 1)).msg_commit_neg_sig i j = true := by
      intro j _ hj
      rcases hj with ⟨m, hm⟩ | hm
      · exact Or.inl ⟨m, Chorus.msg_commit_pos_sig.mono (r.steps n) i j m hm⟩
      · exact Or.inr (Chorus.msg_commit_neg_sig.mono (r.steps n) i j hm)
    by_cases h0 : (r.at' n).msg_commit_cast i = true
    · exact fun j hj => carry j hj (commit_cast_sigs r hi n h0 j hj)
    · exact fun j hj => carry j hj (commit_cast_flip (r.steps n) hi h0 h j hj)

/-- **A correct validator's fallback vote carries a fallback signature per
proposer**, by the same first-flip argument (`fallback_sig_flip`). -/
theorem fallback_sig_sigs (r : CRun th) {i : node} (hi : ¬ nset.is_byz i = true) :
    ∀ n, (r.at' n).msg_fallback_sig i = true → ∀ j, th.is_proposer j = true →
      (∃ m, (r.at' n).msg_fb_pos_sig i j m = true) ∨ (r.at' n).msg_fb_neg_sig i j = true
  | 0, h => by simp [Chorus.msg_fallback_sig.init r.starts i] at h
  | n + 1, h => by
    have carry : ∀ j, th.is_proposer j = true →
        ((∃ m, (r.at' n).msg_fb_pos_sig i j m = true) ∨ (r.at' n).msg_fb_neg_sig i j = true) →
        (∃ m, (r.at' (n + 1)).msg_fb_pos_sig i j m = true) ∨
          (r.at' (n + 1)).msg_fb_neg_sig i j = true := by
      intro j _ hj
      rcases hj with ⟨m, hm⟩ | hm
      · exact Or.inl ⟨m, Chorus.msg_fb_pos_sig.mono (r.steps n) i j m hm⟩
      · exact Or.inr (Chorus.msg_fb_neg_sig.mono (r.steps n) i j hm)
    by_cases h0 : (r.at' n).msg_fallback_sig i = true
    · exact fun j hj => carry j hj (fallback_sig_sigs r hi n h0 j hj)
    · exact fun j hj => carry j hj (fallback_sig_flip (r.steps n) hi h0 h j hj)

/-- A validator on the fallback path has cast its fallback vote
(`path_fallback_flip`, first-flip again; `local_path` starts at `none`). -/
theorem path_fallback_sig (r : CRun th) {i : node} :
    ∀ n, (r.at' n).local_path i = PathChoice_EnumClass.fallback → (r.at' n).msg_fallback_sig i = true
  | 0, h => by
    have hnf : (PathChoice_EnumClass.none : PathChoice) ≠ PathChoice_EnumClass.fallback := by
      have hd := PathChoice_Enum.distinct
      simp [distinctN, distinctPairs, andN] at hd
      tauto
    exact absurd ((Chorus.local_path.init r.starts i).symm.trans h) hnf
  | n + 1, h => by
    by_cases h0 : (r.at' n).local_path i = PathChoice_EnumClass.fallback
    · exact Chorus.msg_fallback_sig.mono (r.steps n) i (path_fallback_sig r n h0)
    · exact path_fallback_flip (r.steps n) h0 h

/-- The phase is at one of the two arms — where the fallback path runs. -/
def AtArm (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)) :
    Prop :=
  st.phase = Phase_EnumClass.post_fb_arm ∨ st.phase = Phase_EnumClass.post_mvba_arm

omit [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited mstate] [Inhabited mvalue] [Inhabited mmsg] [Inhabited Phase] [Inhabited PathChoice]
  PathChoice_Enum in
theorem AtArm.ne_pre
    {st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)}
    (h : AtArm st) : st.phase ≠ Phase_EnumClass.pre_deadline := by
  obtain ⟨-, d2, d3, -, -, -⟩ := phase_distinct (Phase := Phase)
  rcases h with h | h <;> rw [h]
  · exact d2.symm
  · exact d3.symm

/-- Past the deadline stays past the deadline. -/
theorem phase_ne_pre_step
    {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)}
    {l} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s l s')
    (h : s.phase ≠ Phase_EnumClass.pre_deadline) : s'.phase ≠ Phase_EnumClass.pre_deadline := by
  obtain ⟨-, d2, d3, -, -, -⟩ := phase_distinct (Phase := Phase)
  rcases phase_step htr with h' | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
  · rw [h']; exact h
  · exact absurd h1 h
  · rw [h2]; exact d2.symm
  · rw [h2]; exact d3.symm

/-- At an arm stays at an arm. -/
theorem AtArm.step
    {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)}
    {l} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice).tr th s l s')
    (h : AtArm s) : AtArm s' := by
  obtain ⟨-, d2, d3, d4, d5, -⟩ := phase_distinct (Phase := Phase)
  rcases phase_step htr with h' | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
  · unfold AtArm; rw [h']; exact h
  · rcases h with h | h <;> simp_all
  · rcases h with h | h <;> simp_all
  · exact Or.inr h2

/-- **The phase reaches an arm and stays there.** `advance_to_deadline`
and `advance_to_fb_arm` are weakly fair and each is enabled at exactly its
phase; the phase only moves forward (`phase_step`). -/
theorem eventually_atArm (r : CRun th) (hfj : ∀ l, JusticeLabel l → WeaklyFair r l) :
    ∃ N, ∀ n, N ≤ n → AtArm (r.at' n) := by
  obtain ⟨d1, -, -, -, -, -⟩ := phase_distinct (Phase := Phase)
  have hpast : ∃ N, (r.at' N).phase ≠ Phase_EnumClass.pre_deadline := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n, -, hfire⟩ := hfj .advance_to_deadline ⟨fun h => h, fun h => h⟩ 0
      (fun n _ => enabled_advance_to_deadline (hcon n))
    exact d1 ((hcon (n + 1)).symm.trans (advance_to_deadline_effect (hfire ▸ r.steps n)))
  obtain ⟨N1, hN1⟩ := hpast
  have hpast' : ∀ n, N1 ≤ n → (r.at' n).phase ≠ Phase_EnumClass.pre_deadline :=
    r.mono (P := fun st => st.phase ≠ Phase_EnumClass.pre_deadline)
      (fun m hm => phase_ne_pre_step (r.steps m) hm) hN1
  have harm : ∃ N, AtArm (r.at' N) := by
    by_contra hcon
    have hpd : ∀ n, N1 ≤ n → (r.at' n).phase = Phase_EnumClass.post_deadline := by
      intro n hn
      rcases Phase_Enum.complete (r.at' n).phase with h | h | h | h
      · exact absurd h (hpast' n hn)
      · exact h
      · exact absurd ⟨n, Or.inl h⟩ hcon
      · exact absurd ⟨n, Or.inr h⟩ hcon
    obtain ⟨n, hn, hfire⟩ := hfj .advance_to_fb_arm ⟨fun h => h, fun h => h⟩ N1
      (fun n hn => enabled_advance_to_fb_arm (hpd n hn))
    exact hcon ⟨n + 1, Or.inl (advance_to_fb_arm_effect (hfire ▸ r.steps n))⟩
  obtain ⟨N2, hN2⟩ := harm
  exact ⟨N2, r.mono (P := AtArm) (fun m hm => AtArm.step (r.steps m) hm) hN2⟩

/-- **Every correct validator votes**: `vote i` needs only the phase past the
deadline and `¬ local_voted i`. -/
theorem eventually_voted (r : CRun th) (hfj : ∀ l, JusticeLabel l → WeaklyFair r l)
    {i : node} (hi : ¬ nset.is_byz i = true) : ∃ N, (r.at' N).local_voted i = true := by
  obtain ⟨N, hN⟩ := eventually_atArm r hfj
  by_contra hcon
  push Not at hcon
  obtain ⟨n, -, hfire⟩ := hfj (.vote i) ⟨fun h => h, fun h => h⟩ N
    (fun n hn => enabled_vote hi (hN n hn).ne_pre (hcon n))
  exact hcon (n + 1) (vote_effect (hfire ▸ r.steps n))

/-- **An honest quorum's votes are all on the network at one index**, and
stay there. `nodes` is a complete list of validators — the finiteness that
collapses the family of eventualities (`LRun.eventually_forall`). -/
theorem eventually_quorum_cast (r : CRun th) (hfj : ∀ l, JusticeLabel l → WeaklyFair r l)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes)
    {qv : nodeset} (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true) :
    ∃ N, ∀ n, N ≤ n → ∀ a, nset.member a qv = true → (r.at' n).msg_vote_cast a = true := by
  obtain ⟨N, -, hN⟩ := r.eventually_forall
    (fun a st => nset.member a qv = true → st.msg_vote_cast a = true)
    (fun a n h hm => Chorus.msg_vote_cast.mono (r.steps n) a (h hm)) 0 nodes
    (fun a _ => by
      by_cases hm : nset.member a qv = true
      · obtain ⟨n, hn⟩ := eventually_voted r hfj (hqvh a hm)
        exact ⟨n, Nat.zero_le _, fun _ =>
          Chorus.reachable_voted_implies_cast (r.reachable n) a ⟨hqvh a hm, hn⟩⟩
      · exact ⟨0, Nat.le_refl 0, fun h => absurd h hm⟩)
  exact ⟨N, fun n hn a ha =>
    r.mono (P := fun st => st.msg_vote_cast a = true)
      (fun m hm => Chorus.msg_vote_cast.mono (r.steps m) a hm) (hN a (hnodes a) ha) n hn⟩

end RunFacts

end Chorus

