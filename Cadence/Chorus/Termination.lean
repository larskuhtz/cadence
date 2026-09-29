import Cadence.Chorus.Liveness
import Cadence.Chorus.Progress

/-! # Chorus/Termination — the run-level proof of Chorus's termination claim

[Liveness.md](../../docs/Liveness.md) §4, stages 3–5, against the
claim and premises stated in [Liveness.lean](Liveness.lean). This file
holds the proof, so far through stage 3; that one holds the statement, and
nothing here adds a premise to it.

## Stage 3: the fast route, from (F-justice) alone

Two theorems, both taking `FJustice` and nothing else of the three premises:

* **Saturation** — `saturation_fin`: from some index on, every correct
  validator has cast its path vote, fast or fallback, carrying a signature
  for every proposer. That is the `hsat` hypothesis of
  `progress_dichotomy_of_saturation`, so `eventually_progress_dichotomy`
  follows: in every run satisfying (F-justice), the progress dichotomy holds
  at some index.
* **The commit route** — `commit_route_fin`: from an index at which a commit
  certificate exists for every proposer (the dichotomy's left disjunct),
  every correct validator finalizes; `terminates_of_commit_route` is the
  same fact as `Terminates`, the claim's target.

What remains for stages 4–5 is the dichotomy's right disjunct: the MVBA arm,
where `MvbaAdmissible` and `ValidBridge` enter.

## How it is built

Three layers, the last two in the shape of [Mvba/Liveness.lean](../Mvba/Liveness.lean)'s first
link:

1. **Step facts** (section `Steps`) — per-action enabledness (the guards)
   and effect (the post-state), and two-state facts read off the transition
   bodies by label dispatch: the phase only moves forward; the first step
   at which `msg_commit_cast i` / `msg_fallback_sig i` / `local_path i =
   fallback` holds is the correct validator's own honest action; and
   `msg_vote_pos_sig`, `msg_vote_neg_sig`, `local_entry_neg` are monotone —
   the `<f>.mono` statements Veil generates for every other network
   relation, proven here because the generator recognises only
   literal-`true` writes and `vote` writes these as disjunctions with their
   old values. Each dispatch
   is one `case` per action — the generated `frame_<field>` lemmas plus the
   actions that write the field — so a forgotten action is an unsolved
   goal.
2. **Run-level chains** (section `RunFacts`) — generic in the quorum
   instance and the MVBA, with the finiteness they consume made explicit: a
   complete list of validators and an honest supermajority. Each link is
   `Cadence.WeaklyFair` used in the only way [Fairness.lean](../Fairness.lean) allows: a label
   that stays enabled fires, so a proof shows the label stays enabled unless
   the disabling event is the progress wanted.
3. **The concrete family** (section `Concrete`) — `Fin n`, `byzNodeSetFin`
   at every `n = 3f+1`, the MVBA constraint filled by `Mvba.mvbaSafety
   thM`: the runs of [Liveness.lean](Liveness.lean)'s claim. The node list is `List.ofFn
   id` and the honest quorum is `honest_supermajority`'s.

## What it uses from the sweep, and what it does not

One invariant: `voted_implies_cast`, to put a correct voter's vote on the
network. The two facts [Liveness.md](../../docs/Liveness.md) §4.4 flags as outside the sweep —
a correct validator's fast commit vote, resp. fallback vote, carries a
signature per proposer — are **derived** here at run level from the
first-flip step (`commit_cast_sigs`, `fallback_sig_sigs`), not added to
the model. The commit route needs no invariant at all (see
`eventually_committed_of_commitqcs`). No cell is added for any of this; the
model's one accommodation is that `vote` writes its updates as monotone
disjunctions ([Liveness.md](../../docs/Liveness.md) §4.5). -/

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

/-! ## Step facts

Everything a single transition says that the chains below need, generic in
the sorts, the quorum instance and the MVBA. -/

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

/-- The generic Chorus transition system (any quorum instance, any MVBA). -/
local notation "RTS" => Chorus.relationalTransitionSystem slot node nodeset merkle_root
  mstate mvalue mmsg Phase PathChoice

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
/-- **The phase only moves forward**, one marker at a time: every action but
the three `advance_to_*` frames it (Veil's generated `frame_phase`), and each of those
is enabled at exactly its own phase. -/
theorem phase_step {l}
    (htr : (RTS).tr th s l s') :
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
/-- **The first fast commit vote is the validator's own `cast_fast_commit`.**
If `msg_commit_cast i` flips on a step and `i` is correct, the step was
`cast_fast_commit i` — `byz_cast_commit` requires a Byzantine signer, and
every other action frames the relation — so its guard, a commit signature
per proposer, held at the pre-state. -/
theorem commit_cast_flip {l} {i : node}
    (htr : (RTS).tr th s l s')
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
/-- **The first fallback vote is the validator's own `cast_fallback_vote`**,
by the same dispatch: its guard is a fallback signature per proposer. -/
theorem fallback_sig_flip {l} {i : node}
    (htr : (RTS).tr th s l s')
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
/-- **The fallback path is entered only by casting the fallback vote**:
`local_path i` becomes `fallback` only at `cast_fallback_vote i`, which sets
`msg_fallback_sig i` in the same step (`cast_fast_commit` writes `fast`). -/
theorem path_fallback_flip {l} {i : node}
    (htr : (RTS).tr th s l s')
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

set_option maxHeartbeats 1000000 in
/-- **`msg_vote_pos_sig` is monotone**, over every label and at every state
— the statement Veil generates as `<f>.mono`, proven by the same dispatch: `vote`
writes it as a disjunction with its old value, `byz_sign_vote_pos` writes
`true`, every other action frames it. Veil does not generate it because it
recognises only literal-`true` writes, and `vote`'s disjunct is computed. -/
theorem msg_vote_pos_sig_mono {l} (htr : (RTS).tr th s l s') :
    ∀ (r j : node) (m : merkle_root), s.msg_vote_pos_sig r j m = true → s'.msg_vote_pos_sig r j m = true := by
  intro r j m h
  cases l
  case vote i' =>
    chorus_tr htr
    obtain ⟨-, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  case byz_sign_vote_pos =>
    chorus_tr htr
    obtain ⟨-, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr msg_vote_pos_sig hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, propose,
     deliver_chunk_assigned, record_chunk, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step,
     mvba_propose, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk,
     cast_fb_commit, commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg,
     byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_sign_fbcommit, byz_release_msg_decrypt_share] => exact hfr ▸ h

set_option maxHeartbeats 1000000 in
/-- **`msg_vote_neg_sig` is monotone** — as `msg_vote_pos_sig_mono`. -/
theorem msg_vote_neg_sig_mono {l} (htr : (RTS).tr th s l s') :
    ∀ (r j : node), s.msg_vote_neg_sig r j = true → s'.msg_vote_neg_sig r j = true := by
  intro r j h
  cases l
  case vote i' =>
    chorus_tr htr
    obtain ⟨-, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  case byz_sign_vote_neg =>
    chorus_tr htr
    obtain ⟨-, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr msg_vote_neg_sig hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, propose,
     deliver_chunk_assigned, record_chunk, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step,
     mvba_propose, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk,
     cast_fb_commit, commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_pos, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg,
     byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_sign_fbcommit, byz_release_msg_decrypt_share] => exact hfr ▸ h

set_option maxHeartbeats 1000000 in
/-- **`local_entry_neg` is monotone** — `vote` is its only writer, a
disjunction with the old value. -/
theorem local_entry_neg_mono {l} (htr : (RTS).tr th s l s') :
    ∀ (r j : node), s.local_entry_neg r j = true → s'.local_entry_neg r j = true := by
  intro r j h
  cases l
  case vote i' =>
    chorus_tr htr
    obtain ⟨-, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr local_entry_neg hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, propose,
     deliver_chunk_assigned, record_chunk, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step,
     mvba_propose, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk,
     cast_fb_commit, commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos,
     byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg,
     byz_cast_commit, byz_sign_fbcommit, byz_release_msg_decrypt_share] => exact hfr ▸ h

/-- Turn an enabledness goal into the action's guards. -/
local macro "chorus_enabled" : tactic =>
  `(tactic| simp only [Enabled, Chorus.relationalTransitionSystem, Chorus.Next,
      Chorus.NextAct, trSimp])

/-! ### Enabledness and effect, per action the chains fire -/

theorem enabled_advance_to_deadline (h : s.phase = Phase_EnumClass.pre_deadline) :
    Enabled RTS th s .advance_to_deadline := by
  chorus_enabled
  exact ⟨_, h, rfl⟩

theorem advance_to_deadline_effect (htr : (RTS).tr th s .advance_to_deadline s') :
    s'.phase = Phase_EnumClass.post_deadline := by
  chorus_tr htr
  obtain ⟨-, rfl⟩ := htr
  chorus_field_simp

theorem enabled_advance_to_fb_arm (h : s.phase = Phase_EnumClass.post_deadline) :
    Enabled RTS th s .advance_to_fb_arm := by
  chorus_enabled
  exact ⟨_, h, rfl⟩

theorem advance_to_fb_arm_effect (htr : (RTS).tr th s .advance_to_fb_arm s') :
    s'.phase = Phase_EnumClass.post_fb_arm := by
  chorus_tr htr
  obtain ⟨-, rfl⟩ := htr
  chorus_field_simp

theorem enabled_vote {i : node} (hi : ¬ nset.is_byz i = true)
    (hph : s.phase ≠ Phase_EnumClass.pre_deadline) (hnv : ¬ s.local_voted i = true) :
    Enabled RTS th s (.vote i) := by
  chorus_enabled
  exact ⟨_, hi, hph, hnv, rfl⟩

theorem vote_effect {i : node} (htr : (RTS).tr th s (.vote i) s') :
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
    Enabled RTS th s (.fb_sign_pos i j m q qc) := by
  chorus_enabled
  exact ⟨_, hi, hph, hv, hnc, hpath, hj, ⟨qv, hqv, hqvc⟩, hq, hqs, hqc, hqcs, hwe, rfl⟩

theorem fb_sign_pos_effect {i j : node} {m : merkle_root} {q qc : nodeset}
    (htr : (RTS).tr th s (.fb_sign_pos i j m q qc) s') :
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
    Enabled RTS th s (.fb_sign_neg i j qv) := by
  chorus_enabled
  exact ⟨_, hi, hph, hv, hnc, hpath, hj, hqv, hqvc,
    fun M q qc h1 h2 h3 h4 h5 => hnone M q qc ⟨h1, h2, h3, h4, h5⟩, rfl⟩

theorem fb_sign_neg_effect {i j : node} {qv : nodeset}
    (htr : (RTS).tr th s (.fb_sign_neg i j qv) s') :
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
    Enabled RTS th s (.cast_fallback_vote i) := by
  chorus_enabled
  exact ⟨_, hi, hph, hv, hnc, hpath, hall, rfl⟩

theorem cast_fallback_vote_effect {i : node}
    (htr : (RTS).tr th s (.cast_fallback_vote i) s') :
    s'.msg_fallback_sig i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_broadcast_commitqc_pos {j : node} {m : merkle_root} {q : nodeset}
    (hq : nset.supermajority q)
    (hall : ∀ r, nset.member r q = true →
      s.msg_commit_pos_sig r j m = true ∧ s.msg_commit_cast r = true) :
    Enabled RTS th s (.broadcast_commitqc_pos j m q) := by
  chorus_enabled
  exact ⟨_, hq, hall, rfl⟩

theorem broadcast_commitqc_pos_effect {j : node} {m : merkle_root} {q : nodeset}
    (htr : (RTS).tr th s (.broadcast_commitqc_pos j m q) s') :
    s'.msg_commitqc_pos j m = true := by
  chorus_tr htr
  obtain ⟨-, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_broadcast_commitqc_neg {j : node} {q : nodeset}
    (hq : nset.supermajority q)
    (hall : ∀ r, nset.member r q = true →
      s.msg_commit_neg_sig r j = true ∧ s.msg_commit_cast r = true) :
    Enabled RTS th s (.broadcast_commitqc_neg j q) := by
  chorus_enabled
  exact ⟨_, hq, hall, rfl⟩

theorem broadcast_commitqc_neg_effect {j : node} {q : nodeset}
    (htr : (RTS).tr th s (.broadcast_commitqc_neg j q) s') :
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
    Enabled RTS th s (.commit_assign_pos i j m) := by
  chorus_enabled
  exact ⟨_, hi, hnc, hj, Or.inl hqc, fun m' h => absurd h (hnp m'), hnn, rfl⟩

theorem commit_assign_pos_effect {i j : node} {m : merkle_root}
    (htr : (RTS).tr th s (.commit_assign_pos i j m) s') :
    s'.local_committed_pos i j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_commit_assign_neg {i j : node}
    (hi : ¬ nset.is_byz i = true) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true) (hqc : s.msg_commitqc_neg j = true)
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) :
    Enabled RTS th s (.commit_assign_neg i j) := by
  chorus_enabled
  exact ⟨_, hi, hnc, hj, Or.inl hqc, hnp, rfl⟩

theorem commit_assign_neg_effect {i j : node}
    (htr : (RTS).tr th s (.commit_assign_neg i j) s') :
    s'.local_committed_neg i j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_finalize_commit {i : node}
    (hi : ¬ nset.is_byz i = true) (hnc : ¬ s.local_committed i = true)
    (hall : ∀ J, th.is_proposer J = true →
      (∃ M, s.local_committed_pos i J M = true) ∨ s.local_committed_neg i J = true) :
    Enabled RTS th s (.finalize_commit i) := by
  chorus_enabled
  exact ⟨_, hi, hnc, hall, rfl⟩

theorem finalize_commit_effect {i : node}
    (htr : (RTS).tr th s (.finalize_commit i) s') :
    s'.local_committed i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, rfl⟩ := htr
  chorus_field_simp

end Steps

/-! ## Run-level facts

The two chains of [Liveness.md](../../docs/Liveness.md) §4.4, over any labelled Chorus run.
The fairness hypothesis is `FJustice`'s body, `∀ l, JusticeLabel l →
WeaklyFair r l`, so the concrete theorems below pass `FJustice r` through
unchanged. The quorum instance and the MVBA are implicit arguments here
(read off the run's type), so these lemmas instantiate at the concrete
family without any instance search at `byzNodeSetFin`. -/

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

/-- The generic Chorus transition system (any quorum instance, any MVBA). -/
local notation "RTS" => Chorus.relationalTransitionSystem slot node nodeset merkle_root
  mstate mvalue mmsg Phase PathChoice

/-- A labelled run of Chorus at any MVBA instance. -/
local notation "CRun" => LRun RTS

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
    {l} (htr : (RTS).tr th s l s')
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
    {l} (htr : (RTS).tr th s l s')
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
    {l} (htr : (RTS).tr th s l s')
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

/-- **Every correct validator is eventually saturated.** The chain of
[Liveness.md](../../docs/Liveness.md) §4.4: the phase reaches an arm, `i` votes, an honest
quorum's votes are on the network; then, unless `i` saturates, each
proposer gets a fallback signature from `i` — `fb_sign_pos` once positive
evidence appears (it is monotone, so the label stays enabled), `fb_sign_neg`
against the honest quorum if it never does (the absence of that evidence
*is* its guard) — and `cast_fallback_vote i` fires. Every step either fires
or is disabled by `i` casting a path vote, which saturates it by the
first-flip facts. -/
theorem eventually_saturated (r : CRun th) (hfj : ∀ l, JusticeLabel l → WeaklyFair r l)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes)
    {qv : nodeset} (hqv : nset.supermajority qv)
    (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true)
    {i : node} (hi : ¬ nset.is_byz i = true) : ∃ n, Saturated th (r.at' n) i := by
  obtain ⟨Na, hNa⟩ := eventually_atArm r hfj
  obtain ⟨Nv, hNv⟩ := eventually_voted r hfj hi
  obtain ⟨Nq, hNq⟩ := eventually_quorum_cast r hfj nodes hnodes hqvh
  by_contra hcon
  -- `i` never casts a path vote: either would saturate it.
  have hnc : ∀ n, ¬ (r.at' n).msg_commit_cast i = true :=
    fun n h => hcon ⟨n, Or.inl ⟨h, commit_cast_sigs r hi n h⟩⟩
  have hnf : ∀ n, ¬ (r.at' n).msg_fallback_sig i = true :=
    fun n h => hcon ⟨n, Or.inr ⟨h, fallback_sig_sigs r hi n h⟩⟩
  have hnp : ∀ n, ¬ (r.at' n).local_path i = PathChoice_EnumClass.fallback :=
    fun n h => hnf n (path_fallback_sig r n h)
  -- From `N` on: at an arm, `i` has voted, the honest quorum's votes are cast.
  have harm : ∀ n, max Na (max Nv Nq) ≤ n → AtArm (r.at' n) :=
    fun n hn => hNa n (by omega)
  have hv : ∀ n, max Na (max Nv Nq) ≤ n → (r.at' n).local_voted i = true :=
    fun n hn => r.mono (P := fun st => st.local_voted i = true)
      (fun m hm => Chorus.local_voted.mono (r.steps m) i hm) hNv n (by omega)
  have hq : ∀ n, max Na (max Nv Nq) ≤ n →
      ∀ a, nset.member a qv = true → (r.at' n).msg_vote_cast a = true :=
    fun n hn => hNq n (by omega)
  -- Each proposer eventually carries a fallback signature from `i`.
  have hsign : ∀ j, th.is_proposer j = true → ∃ n, max Na (max Nv Nq) ≤ n ∧
      ((∃ m, (r.at' n).msg_fb_pos_sig i j m = true) ∨ (r.at' n).msg_fb_neg_sig i j = true) := by
    intro j hj
    by_contra hns
    by_cases hpos : ∃ n, max Na (max Nv Nq) ≤ n ∧ ∃ M q qc, nset.greater_than_third q ∧
        (∀ a, nset.member a q = true → nset.member a qv = true ∧ (r.at' n).msg_vote_pos_sig a j M = true) ∧
        nset.greater_than_third qc ∧
        (∀ a, nset.member a qc = true → (r.at' n).msg_chunk_received a j M = true) ∧
        th.well_encoded M = true
    · -- Positive evidence appeared: it persists, so `fb_sign_pos` stays enabled.
      obtain ⟨n0, hn0, M, q, qc, hq1, hq2, hqc1, hqc2, hwe⟩ := hpos
      have hq2' : ∀ n, n0 ≤ n → ∀ a, nset.member a q = true → (r.at' n).msg_vote_pos_sig a j M = true :=
        fun n hn a ha => r.mono (P := fun st => st.msg_vote_pos_sig a j M = true)
          (fun m hm => msg_vote_pos_sig_mono (r.steps m) a j M hm) (hq2 a ha).2 n hn
      have hqc2' : ∀ n, n0 ≤ n → ∀ a, nset.member a qc = true → (r.at' n).msg_chunk_received a j M = true :=
        fun n hn a ha => r.mono (P := fun st => st.msg_chunk_received a j M = true)
          (fun m hm => Chorus.msg_chunk_received.mono (r.steps m) a j M hm) (hqc2 a ha) n hn
      obtain ⟨n, hn, hfire⟩ := hfj (.fb_sign_pos i j M q qc) ⟨fun h => h, fun h => h⟩ n0
        (fun n hn => enabled_fb_sign_pos hi (harm n (by omega)) (hv n (by omega)) (hnc n) (hnp n) hj
          hqv (hq n (by omega)) hq1 (hq2' n hn) hqc1 (hqc2' n hn) hwe)
      exact hns ⟨n + 1, by omega, Or.inl ⟨M, fb_sign_pos_effect (hfire ▸ r.steps n)⟩⟩
    · -- It never appears: that absence is `fb_sign_neg`'s guard against `qv`.
      obtain ⟨n, hn, hfire⟩ := hfj (.fb_sign_neg i j qv) ⟨fun h => h, fun h => h⟩ (max Na (max Nv Nq))
        (fun n hn => enabled_fb_sign_neg hi (harm n hn) (hv n hn) (hnc n) (hnp n) hj
          hqv (hq n hn) (fun M q qc hh => hpos ⟨n, hn, M, q, qc, hh⟩))
      exact hns ⟨n + 1, by omega, Or.inr (fb_sign_neg_effect (hfire ▸ r.steps n))⟩
  -- All proposers at one index, and ever after.
  obtain ⟨Ns, hNs, hall⟩ := r.eventually_forall
    (fun j st => th.is_proposer j = true →
      (∃ m, st.msg_fb_pos_sig i j m = true) ∨ st.msg_fb_neg_sig i j = true)
    (fun j n h hj => by
      rcases h hj with ⟨m, hm⟩ | hm
      · exact Or.inl ⟨m, Chorus.msg_fb_pos_sig.mono (r.steps n) i j m hm⟩
      · exact Or.inr (Chorus.msg_fb_neg_sig.mono (r.steps n) i j hm))
    (max Na (max Nv Nq)) nodes
    (fun j _ => by
      by_cases hj : th.is_proposer j = true
      · obtain ⟨n, hn, h⟩ := hsign j hj
        exact ⟨n, hn, fun _ => h⟩
      · exact ⟨max Na (max Nv Nq), Nat.le_refl _, fun h => absurd h hj⟩)
  have hall' : ∀ n, Ns ≤ n → ∀ j, th.is_proposer j = true →
      (∃ m, (r.at' n).msg_fb_pos_sig i j m = true) ∨ (r.at' n).msg_fb_neg_sig i j = true :=
    r.mono (P := fun st => ∀ j, th.is_proposer j = true →
        (∃ m, st.msg_fb_pos_sig i j m = true) ∨ st.msg_fb_neg_sig i j = true)
      (fun m h j hj => by
        rcases h j hj with ⟨k, hk⟩ | hk
        · exact Or.inl ⟨k, Chorus.msg_fb_pos_sig.mono (r.steps m) i j k hk⟩
        · exact Or.inr (Chorus.msg_fb_neg_sig.mono (r.steps m) i j hk))
      (fun j hj => hall j (hnodes j) hj)
  -- So `cast_fallback_vote i` stays enabled, and fires.
  obtain ⟨n, -, hfire⟩ := hfj (.cast_fallback_vote i) ⟨fun h => h, fun h => h⟩ Ns
    (fun n hn => enabled_cast_fallback_vote hi (harm n (by omega)) (hv n (by omega)) (hnc n) (hnp n)
      (hall' n hn))
  exact hnf (n + 1) (cast_fallback_vote_effect (hfire ▸ r.steps n))

/-- **Saturation of the whole correct population at one index** — the `hsat`
hypothesis of `progress_dichotomy_of_saturation`, and it persists. -/
theorem eventually_all_saturated (r : CRun th) (hfj : ∀ l, JusticeLabel l → WeaklyFair r l)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes)
    {qv : nodeset} (hqv : nset.supermajority qv)
    (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true) :
    ∃ N, ∀ n, N ≤ n → ∀ i, ¬ nset.is_byz i = true → Saturated th (r.at' n) i := by
  obtain ⟨N, -, hN⟩ := r.eventually_forall
    (fun i st => ¬ nset.is_byz i = true → Saturated th st i)
    (fun i n h hi => (h hi).step (r.steps n)) 0 nodes
    (fun i _ => by
      by_cases hi : nset.is_byz i = true
      · exact ⟨0, Nat.le_refl 0, fun h => absurd hi h⟩
      · obtain ⟨n, hn⟩ := eventually_saturated r hfj nodes hnodes hqv hqvh hi
        exact ⟨n, Nat.zero_le _, fun _ => hn⟩)
  exact ⟨N, fun n hn i hi =>
    r.mono (P := fun st => Saturated th st i) (fun m h => h.step (r.steps m))
      (hN i (hnodes i) hi) n hn⟩

/-- **A commit certificate becomes a broadcast one**: from the certificate's
own quorum, `broadcast_commitqc_*` stays enabled until it fires (its guards
are monotone). -/
theorem eventually_msg_commitqc (r : CRun th) (hfj : ∀ l, JusticeLabel l → WeaklyFair r l)
    {N : Nat} {j : node}
    (hqc : (∃ m, Chorus.commitqc_pos (nset := nset) (mvba := mvba) j m th (r.at' N)) ∨
      Chorus.commitqc_neg (nset := nset) (mvba := mvba) j th (r.at' N)) :
    ∃ n, N ≤ n ∧
      ((∃ m, (r.at' n).msg_commitqc_pos j m = true) ∨ (r.at' n).msg_commitqc_neg j = true) := by
  by_contra hcon
  rcases hqc with ⟨m, hqc⟩ | hqc
  · unfold Chorus.commitqc_pos at hqc
    obtain ⟨q, hq, hall⟩ := hqc
    have hall' : ∀ n, N ≤ n → ∀ a, nset.member a q = true →
        (r.at' n).msg_commit_pos_sig a j m = true ∧ (r.at' n).msg_commit_cast a = true :=
      fun n hn a ha =>
        ⟨r.mono (P := fun st => st.msg_commit_pos_sig a j m = true)
          (fun k hk => Chorus.msg_commit_pos_sig.mono (r.steps k) a j m hk) (hall a ha).1 n hn,
         r.mono (P := fun st => st.msg_commit_cast a = true)
          (fun k hk => Chorus.msg_commit_cast.mono (r.steps k) a hk) (hall a ha).2 n hn⟩
    obtain ⟨n, hn, hfire⟩ := hfj (.broadcast_commitqc_pos j m q) ⟨fun h => h, fun h => h⟩ N
      (fun n hn => enabled_broadcast_commitqc_pos hq (hall' n hn))
    exact hcon ⟨n + 1, by omega, Or.inl ⟨m, broadcast_commitqc_pos_effect (hfire ▸ r.steps n)⟩⟩
  · unfold Chorus.commitqc_neg at hqc
    obtain ⟨q, hq, hall⟩ := hqc
    have hall' : ∀ n, N ≤ n → ∀ a, nset.member a q = true →
        (r.at' n).msg_commit_neg_sig a j = true ∧ (r.at' n).msg_commit_cast a = true :=
      fun n hn a ha =>
        ⟨r.mono (P := fun st => st.msg_commit_neg_sig a j = true)
          (fun k hk => Chorus.msg_commit_neg_sig.mono (r.steps k) a j hk) (hall a ha).1 n hn,
         r.mono (P := fun st => st.msg_commit_cast a = true)
          (fun k hk => Chorus.msg_commit_cast.mono (r.steps k) a hk) (hall a ha).2 n hn⟩
    obtain ⟨n, hn, hfire⟩ := hfj (.broadcast_commitqc_neg j q) ⟨fun h => h, fun h => h⟩ N
      (fun n hn => enabled_broadcast_commitqc_neg hq (hall' n hn))
    exact hcon ⟨n + 1, by omega, Or.inr (broadcast_commitqc_neg_effect (hfire ▸ r.steps n))⟩

/-- **The commit route finalizes.** From an index at which a commit
certificate exists for every proposer, every correct validator eventually
has `local_committed`: each certificate is broadcast, the validator assigns
every proposer's entry from it, and `finalize_commit` fires.

No invariant is used. `commit_assign_*`'s two consistency guards are
anti-monotone, but they concern only the validator's *own* earlier
assignments for that proposer — and the argument is by contradiction on the
validator never assigning one, in which case both hold vacuously. -/
theorem eventually_committed_of_commitqcs (r : CRun th) (hfj : ∀ l, JusticeLabel l → WeaklyFair r l)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) {N : Nat}
    (hqc : ∀ j, th.is_proposer j = true →
      (∃ m, Chorus.commitqc_pos (nset := nset) (mvba := mvba) j m th (r.at' N)) ∨
        Chorus.commitqc_neg (nset := nset) (mvba := mvba) j th (r.at' N))
    {i : node} (hi : ¬ nset.is_byz i = true) :
    ∃ n, N ≤ n ∧ (r.at' n).local_committed i = true := by
  -- Every proposer's certificate is broadcast, at one index and ever after.
  have hQ : ∀ j st, ((∃ m, (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
        mstate mvalue mmsg Phase PathChoice)).msg_commitqc_pos j m = true) ∨ st.msg_commitqc_neg j = true) →
      ∀ {l st'}, (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase
        PathChoice).tr th st l st' →
      (∃ m, st'.msg_commitqc_pos j m = true) ∨ st'.msg_commitqc_neg j = true := by
    intro j st h l st' htr
    rcases h with ⟨m, hm⟩ | hm
    · exact Or.inl ⟨m, Chorus.msg_commitqc_pos.mono htr j m hm⟩
    · exact Or.inr (Chorus.msg_commitqc_neg.mono htr j hm)
  obtain ⟨N1, hN1, hall⟩ := r.eventually_forall
    (fun j st => th.is_proposer j = true →
      (∃ m, st.msg_commitqc_pos j m = true) ∨ st.msg_commitqc_neg j = true)
    (fun j n h hj => hQ j _ (h hj) (r.steps n)) N nodes
    (fun j _ => by
      by_cases hj : th.is_proposer j = true
      · obtain ⟨n, hn, h⟩ := eventually_msg_commitqc r hfj (hqc j hj)
        exact ⟨n, hn, fun _ => h⟩
      · exact ⟨N, Nat.le_refl _, fun h => absurd h hj⟩)
  have hbc : ∀ n, N1 ≤ n → ∀ j, th.is_proposer j = true →
      (∃ m, (r.at' n).msg_commitqc_pos j m = true) ∨ (r.at' n).msg_commitqc_neg j = true :=
    r.mono (P := fun st => ∀ j, th.is_proposer j = true →
        (∃ m, st.msg_commitqc_pos j m = true) ∨ st.msg_commitqc_neg j = true)
      (fun k h j hj => hQ j _ (h j hj) (r.steps k)) (fun j hj => hall j (hnodes j) hj)
  by_contra hcon
  have hnc : ∀ n, ¬ (r.at' n).local_committed i = true := by
    intro n hn
    by_cases hle : N ≤ n
    · exact hcon ⟨n, hle, hn⟩
    · exact hcon ⟨N, Nat.le_refl _, r.mono (P := fun st => st.local_committed i = true)
        (fun k hk => Chorus.local_committed.mono (r.steps k) i hk) hn N (by omega)⟩
  -- The entry for `j` is assigned by `i`, positive or negative.
  have hE : ∀ j st, ((∃ m, (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
        mstate mvalue mmsg Phase PathChoice)).local_committed_pos i j m = true) ∨
        st.local_committed_neg i j = true) →
      ∀ {l st'}, (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mmsg Phase
        PathChoice).tr th st l st' →
      (∃ m, st'.local_committed_pos i j m = true) ∨ st'.local_committed_neg i j = true := by
    intro j st h l st' htr
    rcases h with ⟨m, hm⟩ | hm
    · exact Or.inl ⟨m, Chorus.local_committed_pos.mono htr i j m hm⟩
    · exact Or.inr (Chorus.local_committed_neg.mono htr i j hm)
  have hassign : ∀ j, th.is_proposer j = true → ∃ n, N1 ≤ n ∧
      ((∃ m, (r.at' n).local_committed_pos i j m = true) ∨ (r.at' n).local_committed_neg i j = true) := by
    intro j hj
    by_contra hna
    have hnp : ∀ n, N1 ≤ n → ∀ m', ¬ (r.at' n).local_committed_pos i j m' = true :=
      fun n hn m' h => hna ⟨n, hn, Or.inl ⟨m', h⟩⟩
    have hnn : ∀ n, N1 ≤ n → ¬ (r.at' n).local_committed_neg i j = true :=
      fun n hn h => hna ⟨n, hn, Or.inr h⟩
    rcases hbc N1 (Nat.le_refl _) j hj with ⟨m, hm⟩ | hm
    · have hm' : ∀ n, N1 ≤ n → (r.at' n).msg_commitqc_pos j m = true :=
        r.mono (P := fun st => st.msg_commitqc_pos j m = true)
          (fun k hk => Chorus.msg_commitqc_pos.mono (r.steps k) j m hk) hm
      obtain ⟨n, hn, hfire⟩ := hfj (.commit_assign_pos i j m) ⟨fun h => h, fun h => h⟩ N1
        (fun n hn => enabled_commit_assign_pos hi (hnc n) hj (hm' n hn) (hnp n hn) (hnn n hn))
      exact hna ⟨n + 1, by omega, Or.inl ⟨m, commit_assign_pos_effect (hfire ▸ r.steps n)⟩⟩
    · have hm' : ∀ n, N1 ≤ n → (r.at' n).msg_commitqc_neg j = true :=
        r.mono (P := fun st => st.msg_commitqc_neg j = true)
          (fun k hk => Chorus.msg_commitqc_neg.mono (r.steps k) j hk) hm
      obtain ⟨n, hn, hfire⟩ := hfj (.commit_assign_neg i j) ⟨fun h => h, fun h => h⟩ N1
        (fun n hn => enabled_commit_assign_neg hi (hnc n) hj (hm' n hn) (hnp n hn))
      exact hna ⟨n + 1, by omega, Or.inr (commit_assign_neg_effect (hfire ▸ r.steps n))⟩
  -- Every proposer assigned at one index and ever after, so `finalize_commit` fires.
  obtain ⟨N2, -, hall2⟩ := r.eventually_forall
    (fun j st => th.is_proposer j = true →
      (∃ m, st.local_committed_pos i j m = true) ∨ st.local_committed_neg i j = true)
    (fun j n h hj => hE j _ (h hj) (r.steps n)) N1 nodes
    (fun j _ => by
      by_cases hj : th.is_proposer j = true
      · obtain ⟨n, hn, h⟩ := hassign j hj
        exact ⟨n, hn, fun _ => h⟩
      · exact ⟨N1, Nat.le_refl _, fun h => absurd h hj⟩)
  have hall2' : ∀ n, N2 ≤ n → ∀ j, th.is_proposer j = true →
      (∃ m, (r.at' n).local_committed_pos i j m = true) ∨ (r.at' n).local_committed_neg i j = true :=
    r.mono (P := fun st => ∀ j, th.is_proposer j = true →
        (∃ m, st.local_committed_pos i j m = true) ∨ st.local_committed_neg i j = true)
      (fun k h j hj => hE j _ (h j hj) (r.steps k)) (fun j hj => hall2 j (hnodes j) hj)
  obtain ⟨n, -, hfire⟩ := hfj (.finalize_commit i) ⟨fun h => h, fun h => h⟩ N2
    (fun n hn => enabled_finalize_commit hi (hnc n) (hall2' n hn))
  exact hnc (n + 1) (finalize_commit_effect (hfire ▸ r.steps n))

end RunFacts

/-! ## At the concrete quorum family, at the system's MVBA

The runs of [Liveness.lean](Liveness.lean)'s claim, at the family the counting theorems are
stated over: `Fin n` with `byzNodeSetFin` at every `n = 3f+1`. -/

section Concrete

open Classical ByzNodeSet

variable {slot merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [vord : TotalOrderWithMinimum view]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
  [node_inhabited : Inhabited (Fin n)]
  -- The quorum counting facts Chorus consumes (its `cnt` class constraint).
  [cnt : Cadence.ByzNodeSetCounting (Fin n) (ByzNSet n) (byzNodeSetFin n f hf is_byz hbyz)]
  {thS : Chorus.Theory slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (Fin n → Option merkle_root) view))
      (Fin n → Option merkle_root) (Mvba.Msg view (Fin n → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory (Fin n) (ByzNSet n) (Fin n → Option merkle_root) view}

/-- Apply a generated `Chorus` declaration at the canonical `Classical`
instantiation — [Progress.lean](Progress.lean)'s `cpv%`, at the `Mvba` model's types and
with the MVBA constraint filled by `Mvba.mvbaSafety thM`. -/
local macro "cpvm%" t:ident args:term:max* : term =>
  `(@$t
    (Chorus.Theory slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (Fin n → Option merkle_root) view)) (Fin n → Option merkle_root) (Mvba.Msg view (Fin n → Option merkle_root)) Phase PathChoice)
    (Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (Fin n → Option merkle_root) view)) (Fin n → Option merkle_root) (Mvba.Msg view (Fin n → Option merkle_root)) Phase PathChoice))
    slot (fun a b => Classical.propDecidable (a = b)) inferInstance
    (Fin n) (fun a b => Classical.propDecidable (a = b)) inferInstance
    (ByzNSet n) (fun a b => Classical.propDecidable (a = b)) inferInstance
    merkle_root (fun a b => Classical.propDecidable (a = b)) inferInstance
    (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (Fin n → Option merkle_root) view))
      (fun a b => Classical.propDecidable (a = b)) inferInstance
    (Fin n → Option merkle_root) (fun a b => Classical.propDecidable (a = b)) inferInstance
    (Mvba.Msg view (Fin n → Option merkle_root)) (fun a b => Classical.propDecidable (a = b)) inferInstance
    (byzNodeSetFin n f hf is_byz hbyz) (Cadence.byzNodeSetFin_counting n f hf is_byz hbyz)
    (Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM)
    Phase (fun a b => Classical.propDecidable (a = b)) inferInstance inferInstance
    PathChoice (fun a b => Classical.propDecidable (a = b)) inferInstance inferInstance
    (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (Fin n → Option merkle_root) view)) (Fin n → Option merkle_root) (Mvba.Msg view (Fin n → Option merkle_root)) Phase PathChoice)
    (fun ff => @Chorus.instAbstractFieldRepresentation slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (Fin n → Option merkle_root) view)) (Fin n → Option merkle_root) (Mvba.Msg view (Fin n → Option merkle_root)) Phase PathChoice
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) ff)
    (fun ff => @Chorus.instLawfulAbstractFieldRepresentation slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (Fin n → Option merkle_root) view)) (Fin n → Option merkle_root) (Mvba.Msg view (Fin n → Option merkle_root)) Phase PathChoice
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) ff)
    instIsSubStateOfRefl instIsSubReaderOfRefl
    $args*)

omit node_inhabited cnt in
/-- The honest population, in the instance's vocabulary: a supermajority
whose every member is correct. -/
theorem honest_quorum_fin :
    ∃ H : ByzNSet n, (byzNodeSetFin n f hf is_byz hbyz).supermajority H ∧
      ∀ a, (byzNodeSetFin n f hf is_byz hbyz).member a H = true →
        ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz a = true := by
  classical
  obtain ⟨H, hlen, hhon⟩ := honest_supermajority n f hf is_byz hbyz
  refine ⟨H, by simpa +instances [byzNodeSetFin] using hlen, fun a ha hb => ?_⟩
  exact hhon a (by simpa +instances [byzNodeSetFin] using ha) (by simpa +instances [byzNodeSetFin] using hb)

/-- **Stage 3, first theorem: every correct validator is eventually
saturated, and stays so** — from (F-justice) alone. The conclusion is, per
index, `progress_dichotomy_of_saturation`'s `hsat` hypothesis. -/
theorem saturation_fin (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thS thM)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r) :
    ∃ N, ∀ k, N ≤ k → ∀ i : Fin n, ¬ is_byz i → Saturated thS (r.at' k) i := by
  obtain ⟨H, hH, hHh⟩ := honest_quorum_fin n f hf is_byz hbyz
  obtain ⟨N, hN⟩ := eventually_all_saturated r hfj (List.ofFn (n := n) id) (by simp) hH hHh
  exact ⟨N, fun k hk i hi => hN k hk i (by simpa +instances [byzNodeSetFin] using hi)⟩

set_option maxHeartbeats 1600000 in
/-- **The progress dichotomy holds in every run satisfying (F-justice)**: the
saturation theorem discharges `progress_dichotomy_of_saturation`'s `hsat` at
a reachable index. Its left disjunct is `commit_route_fin`'s hypothesis;
its right disjunct is the MVBA arm (stage 4). -/
theorem eventually_progress_dichotomy (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thS thM)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r) :
    ∃ N,
    (∀ j : Fin n, thS.is_proposer j = true →
      ((∃ m, cpvm% Chorus.commitqc_pos j m thS (r.at' N)) ∨ (cpvm% Chorus.commitqc_neg j thS (r.at' N)))) ∨
    ((cpvm% Chorus.mvba_invoked thS (r.at' N)) ∧
      ∀ j : Fin n, thS.is_proposer j = true →
        ((∃ m, (cpvm% Chorus.vote_quorum_pos j m thS (r.at' N)) ∨
               ((cpvm% Chorus.fb_quorum_pos j m thS (r.at' N)) ∧ (cpvm% Chorus.fbcert thS (r.at' N)))) ∨
         ((cpvm% Chorus.vote_quorum_neg j thS (r.at' N)) ∨
          (((cpvm% Chorus.fb_quorum_neg j thS (r.at' N)) ∨ (cpvm% Chorus.equiv_evidence j thS (r.at' N))) ∧
           (cpvm% Chorus.fbcert thS (r.at' N)))))) := by
  obtain ⟨N, hN⟩ := saturation_fin n f hf is_byz hbyz r hfj
  exact ⟨N, progress_dichotomy_of_saturation
    (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM) n f hf is_byz hbyz
    (r.reachable N) (fun i hi => hN N (Nat.le_refl N) i hi)⟩

set_option maxHeartbeats 1600000 in
/-- **Stage 3, second theorem: the commit route finalizes** — from an index at
which every proposer has a commit certificate (the progress dichotomy's left
disjunct, verbatim), every correct validator eventually has
`local_committed`. From (F-justice) alone. -/
theorem commit_route_fin (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thS thM)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r) {N : Nat}
    (hqc : ∀ j : Fin n, thS.is_proposer j = true →
      ((∃ m, cpvm% Chorus.commitqc_pos j m thS (r.at' N)) ∨ (cpvm% Chorus.commitqc_neg j thS (r.at' N)))) :
    ∀ i : Fin n, ¬ is_byz i → ∃ k, N ≤ k ∧ (r.at' k).local_committed i = true :=
  fun i hi => eventually_committed_of_commitqcs r hfj (List.ofFn (n := n) id) (by simp) hqc
    (by simpa +instances [byzNodeSetFin] using hi)

set_option maxHeartbeats 1600000 in
/-- The commit route in the claim's own vocabulary: if the dichotomy's left
disjunct ever holds, the run `Terminates`. -/
theorem terminates_of_commit_route (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thS thM)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r) {N : Nat}
    (hqc : ∀ j : Fin n, thS.is_proposer j = true →
      ((∃ m, cpvm% Chorus.commitqc_pos j m thS (r.at' N)) ∨ (cpvm% Chorus.commitqc_neg j thS (r.at' N)))) :
    Terminates (nset := byzNodeSetFin n f hf is_byz hbyz) r := by
  intro i hi
  obtain ⟨k, -, hk⟩ := commit_route_fin n f hf is_byz hbyz r hfj hqc i
    (fun hb => hi (by simpa +instances [byzNodeSetFin] using hb))
  exact ⟨k, hk⟩

end Concrete

end Chorus

/-! ## The pinned trust base

The standard Lean trio and nothing else — no `sorryAx`. The stage-3 theorems
at the concrete family, their generic cores, the three hand-proven
monotonicity lemmas, and the two run-level facts derived in place of new
invariants. The reachability they use comes from the
proof-file family through [Certify.lean](Certify.lean), and the dichotomy from
[Progress.lean](Progress.lean), each pinned there. -/

/--
info: 'Chorus.msg_vote_pos_sig_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.msg_vote_pos_sig_mono

/--
info: 'Chorus.msg_vote_neg_sig_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.msg_vote_neg_sig_mono

/--
info: 'Chorus.local_entry_neg_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.local_entry_neg_mono

/--
info: 'Chorus.saturation_fin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.saturation_fin

/--
info: 'Chorus.eventually_progress_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_progress_dichotomy

/--
info: 'Chorus.commit_route_fin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.commit_route_fin

/--
info: 'Chorus.terminates_of_commit_route' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.terminates_of_commit_route

/--
info: 'Chorus.eventually_all_saturated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_all_saturated

/--
info: 'Chorus.eventually_committed_of_commitqcs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_committed_of_commitqcs

/--
info: 'Chorus.commit_cast_sigs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.commit_cast_sigs

/--
info: 'Chorus.fallback_sig_sigs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fallback_sig_sigs
