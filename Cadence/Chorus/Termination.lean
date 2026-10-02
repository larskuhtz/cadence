import Cadence.Chorus.Liveness
import Cadence.Chorus.Progress
import Cadence.System

/-! # Chorus/Termination — the run-level proof of Chorus's termination claim

[Liveness.md](../../docs/Liveness.md) §4, stages 3–5, against the
claim and premises stated in [Liveness.lean](Liveness.lean). This file
holds the proof; that one holds the statement, and nothing here adds a
premise to it.

## The result

**`Chorus.termination`** — `TerminationClaim`, proven at every `n = 3f+1`
with at most `f` Byzantine validators and at the system's configuration
`Cadence.chorusTheory`: every run satisfying `FJustice`, `MvbaAdmissible`,
`ValidBridge`, `AllParticipate` and `NoAbandonBeforeFinalizing` terminates,
i.e. every correct validator finalizes the slot. The one further hypothesis
is the view order's enumeration, which `Mvba.termination` takes.

The proof splits on an early finalization, as the paper's does. If some
correct validator finalizes, the others finalize from its commitment proof
(`eventually_committed_of_finalized`, the untimed totality). If none ever
does, none ever abandons, so every correct validator is actively
participating from some index on (`activeFrom_of_never_finalized`, the gate
every sending rule requires), and the MVBA arm finalizes everyone (stage 4).
Each honest link takes the gate as a hypothesis (`ActiveFrom`), as the
MVBA's links take `Active`.

Every fairness link is owed only for messages from correct senders
(`Owed`, [Liveness.lean](Liveness.lean)), so every link names the correct
senders it relies on: the honest quorum's votes, a correct fast voter's
`FastBlock`, a correct fallback signer's re-dissemination, a correct
validator's decision for the handoff, the correct voters' fallback commit
certificate, a correct finalizer's commitment proof.

## Stage 3: saturation, from (F-justice) and the gate

* **Saturation** — `saturation_fin`: from some index on, every correct
  validator has cast its path vote, fast or fallback, carrying a signature
  for every proposer. That is the `hsat` hypothesis of the progress
  analysis ([Progress.lean](Progress.lean)). `eventually_progress_dichotomy`
  still states the full dichotomy; the proof uses its evidence half
  (`mvba_evidence_of_saturation`).
* **The MVBA route** — `eventually_mvba_route`: at saturation the MVBA's
  trigger holds from correct senders (`CorrectTrigger`: a correct fast
  voter's complete meta-block, or else the correct population's `FBCert`),
  with a certificate for every proposer.

Until R8 the late branch split on the dichotomy and took a commit route on
its left disjunct. That disjunct's commit certificates may rest on
Byzantine commit votes nobody correct is owed, while the MVBA route is open
at every saturated state, so the split is gone.

## Stage 4: the MVBA arm, from the run premises and the gate

* **The MVBA arm** — `mvba_arm_fin`: from an index at which the MVBA route
  is open, every correct validator finalizes; `terminates_of_mvba_arm` is
  the same fact as `Terminates`. It is stated at the system's configuration
  `Cadence.chorusTheory` and takes `FJustice`, `MvbaAdmissible` and
  `ValidBridge`, plus the view order's enumeration that `Mvba.termination`
  takes.

The chain (`eventually_committed_of_mvba_arm`): every correct validator
proposes one certified vector built from the evidence (`certifiedVector`,
`Valid` by the bridge's soundness clause); the MVBA's own `Mvba.termination`
is applied to the composed run's MVBA projection, its three caller premises
derived (every correct validator proposes; nobody is abandoned in the MVBA,
because on this branch nobody invokes Chorus's `abandon`, and the MVBA's
`abandoned` row moves only with it — `abandoned_of_mvba_abandoned`; and
decided certificates are handed on, `fRelay_of_fJustice`, from the handoff
`accept_mvba_commitqc`); one decision is transported into Chorus by the
decision handlers (the bridge's completeness clause) and completed by
`mvba_terminate`; every correct validator's own chunks arrive and it casts
its fallback commit vote; and the correct voters' fallback commit
certificate is a commitment proof for every proposer's entry, the commit
route's hypothesis (`eventually_committed_of_assignable`). Stage 5 is the
case split above: `Chorus.termination`.

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
   that stays enabled fires, so a proof shows the label stays enabled
   unless the disabling event is the progress wanted (directly, or through
   `eventually_of_weaklyFair`). The MVBA arm's chain
   (sections `CertifiedVector`, `MvbaArm`) is the same layer at the
   system's MVBA, still generic in the quorum instance, with finiteness as
   `[Fintype node]` and the honest quorum as `ByzNodeSetHonestQuorum` —
   the two hypotheses `Mvba.termination` takes. It reaches the MVBA's
   state through [Liveness.lean](Liveness.lean)'s projection `mvbaComponent`; the one
   (F-justice) clause it uses beyond the per-label one is the proposal
   family's.
3. **The concrete family** (section `Concrete`) — `Fin n`, `byzNodeSetFin`
   at every `n = 3f+1`, the MVBA constraint filled by `Mvba.mvbaSafety
   thM`: the runs of [Liveness.lean](Liveness.lean)'s claim. The node list is `List.ofFn
   id` and the honest quorum is `honest_supermajority`'s
   (`byzNodeSetFin_honest`, for the MVBA arm).

## What it uses from the sweep, and what it does not

Stage 3 uses one invariant: `voted_implies_cast`, to put a correct voter's
vote on the network. The two facts [Liveness.md](../../docs/Liveness.md) §4.4 flags as outside the sweep —
a correct validator's fast commit vote, resp. fallback vote, carries a
signature per proposer — are **derived** here at run level from the
first-flip step (`commit_cast_sigs`, `fallback_sig_sigs`), not added to
the model. So is the fact the early-finalization branch needs, that a
committed entry is assignable (`committed_pos_assignable`,
`committed_neg_assignable`): the invariant `local_committed_*_backed` keeps
the MVBA record but not the fallback commit certificate beside it. The commit route needs no invariant at all (see
`eventually_committed_of_assignable`). Stage 4 reads existing invariants at
reachable states: the FastQC backing (`local_fastqc_*_backed`, for a
complete fast meta-block to spread), the decision records' backing,
uniqueness and decodability (`mvba_decided_pos_backed`,
`mvba_decided_pos_unique`, `mvba_decided_pos_neg_excl`,
`mvba_decided_pos_chunks_decodable`), and the signature chain that makes a
decided root proposer-signed (`proposer_signed_of_decided_pos`). No cell is
added for any of this; the model's one accommodation is that `vote` writes
its updates as monotone disjunctions ([Liveness.md](../../docs/Liveness.md) §4.5). -/

namespace Chorus

open Cadence

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
    [participate, abandon, propose, deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos,
     aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit,
     broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg,
     cast_fallback_vote, mvba_step, mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos, on_mvba_decide_neg,
     mvba_terminate, redisseminate_chunk, cast_fb_commit, commit_assign_pos, commit_assign_neg,
     finalize_commit, byz_sign_proposer, byz_deliver_chunk, byz_sign_vote_pos,
     byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback,
     byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_sign_fbcommit, byz_redisseminate_chunk, byz_broadcast_commitqc_pos,
     byz_broadcast_commitqc_neg,
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
    obtain ⟨-, -, -, -, -, hsig, rfl⟩ := htr
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
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, broadcast_commitqc_pos, broadcast_commitqc_neg,
     fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos,
     on_mvba_decide_neg, mvba_terminate, redisseminate_chunk, cast_fb_commit,
     commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos,
     byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg,
     byz_sign_fbcommit, byz_redisseminate_chunk, byz_broadcast_commitqc_pos,
     byz_broadcast_commitqc_neg, byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0

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
    obtain ⟨-, -, -, -, -, -, -, hsig, rfl⟩ := htr
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
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, mvba_step, mvba_propose, accept_mvba_commitqc,
     on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk,
     cast_fb_commit, commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos,
     byz_sign_fb_neg, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_sign_fbcommit, byz_redisseminate_chunk, byz_broadcast_commitqc_pos,
     byz_broadcast_commitqc_neg, byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0

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
    obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hne
    · exact absurd (by simpa using h1) hff
    · simp_all
  case cast_fallback_vote i' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hne
    · simp
    · simp_all
  frame_cases htr local_path hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, broadcast_commitqc_pos, broadcast_commitqc_neg,
     fb_sign_pos, fb_sign_neg, mvba_step, mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos, on_mvba_decide_neg,
     mvba_terminate, redisseminate_chunk, cast_fb_commit, commit_assign_pos, commit_assign_neg,
     finalize_commit, byz_sign_proposer, byz_deliver_chunk, byz_sign_vote_pos,
     byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback,
     byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_sign_fbcommit, byz_redisseminate_chunk, byz_broadcast_commitqc_pos,
     byz_broadcast_commitqc_neg,
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
    obtain ⟨-, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  case byz_sign_vote_pos =>
    chorus_tr htr
    obtain ⟨-, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr msg_vote_pos_sig hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step,
     mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk,
     cast_fb_commit, commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg,
     byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_sign_fbcommit, byz_redisseminate_chunk, byz_broadcast_commitqc_pos,
     byz_broadcast_commitqc_neg, byz_release_msg_decrypt_share] => exact hfr ▸ h

set_option maxHeartbeats 1000000 in
/-- **`msg_vote_neg_sig` is monotone** — as `msg_vote_pos_sig_mono`. -/
theorem msg_vote_neg_sig_mono {l} (htr : (RTS).tr th s l s') :
    ∀ (r j : node), s.msg_vote_neg_sig r j = true → s'.msg_vote_neg_sig r j = true := by
  intro r j h
  cases l
  case vote i' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  case byz_sign_vote_neg =>
    chorus_tr htr
    obtain ⟨-, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr msg_vote_neg_sig hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step,
     mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk,
     cast_fb_commit, commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_pos, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg,
     byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_sign_fbcommit, byz_redisseminate_chunk, byz_broadcast_commitqc_pos,
     byz_broadcast_commitqc_neg, byz_release_msg_decrypt_share] => exact hfr ▸ h

set_option maxHeartbeats 1000000 in
/-- **`local_entry_neg` is monotone** — `vote` is its only writer, a
disjunction with the old value. -/
theorem local_entry_neg_mono {l} (htr : (RTS).tr th s l s') :
    ∀ (r j : node), s.local_entry_neg r j = true → s'.local_entry_neg r j = true := by
  intro r j h
  cases l
  case vote i' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr local_entry_neg hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step,
     mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk,
     cast_fb_commit, commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer,
     byz_deliver_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos,
     byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg,
     byz_cast_commit, byz_sign_fbcommit, byz_redisseminate_chunk, byz_broadcast_commitqc_pos,
     byz_broadcast_commitqc_neg, byz_release_msg_decrypt_share] => exact hfr ▸ h

set_option maxHeartbeats 1000000 in
/-- **A committed positive entry was assignable when it was committed.** If
`local_committed_pos i j m` flips on a step, the step was
`commit_assign_pos i j m` — its only writer — whose certificate guard held
at the pre-state. The invariant `local_committed_pos_backed` keeps only the
MVBA record, not the fallback commit certificate beside it; this first-flip
fact keeps both, which is what the early-finalization branch needs. -/
theorem committed_pos_flip {l} {i j : node} {m : merkle_root}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_committed_pos i j m = true) (h1 : s'.local_committed_pos i j m = true) :
    s.msg_commitqc_pos j m = true ∨ (Chorus.fbcommitqc th s ∧ s.mvba_decided_pos j m = true) := by
  cases l
  case commit_assign_pos i' j' m' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, hqc, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hi
    · rcases eq_or_ne j' j with rfl | hj
      · rcases eq_or_ne m' m with rfl | hm
        · exact hqc
        · simp_all
      · simp_all
    · simp_all
  frame_cases htr local_committed_pos hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon,
     propose, deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos,
     aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit,
     broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg,
     cast_fallback_vote, mvba_step, mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos, on_mvba_decide_neg,
     mvba_terminate, redisseminate_chunk, cast_fb_commit, commit_assign_neg, finalize_commit,
     byz_sign_proposer, byz_deliver_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote,
     byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos,
     byz_sign_commit_neg, byz_cast_commit, byz_sign_fbcommit, byz_redisseminate_chunk, byz_broadcast_commitqc_pos,
     byz_broadcast_commitqc_neg, byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **A committed negative entry was assignable when it was committed**, by
the same dispatch (`commit_assign_neg` is its only writer). -/
theorem committed_neg_flip {l} {i j : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_committed_neg i j = true) (h1 : s'.local_committed_neg i j = true) :
    s.msg_commitqc_neg j = true ∨ (Chorus.fbcommitqc th s ∧ s.mvba_decided_neg j = true) := by
  cases l
  case commit_assign_neg i' j' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, hqc, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hi
    · rcases eq_or_ne j' j with rfl | hj
      · exact hqc
      · simp_all
    · simp_all
  frame_cases htr local_committed_neg hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon,
     propose, deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos,
     aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit,
     broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg,
     cast_fallback_vote, mvba_step, mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos, on_mvba_decide_neg,
     mvba_terminate, redisseminate_chunk, cast_fb_commit, commit_assign_pos, finalize_commit,
     byz_sign_proposer, byz_deliver_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote,
     byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos,
     byz_sign_commit_neg, byz_cast_commit, byz_sign_fbcommit, byz_redisseminate_chunk, byz_broadcast_commitqc_pos,
     byz_broadcast_commitqc_neg, byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **A fallback-entry record comes with the entry.** `local_fb_entry i j`
is written only by `fb_sign_pos` / `fb_sign_neg` at `i` and `j`, each of which
sets `i`'s fallback signature for `j` in the same step. -/
theorem fb_entry_flip {l} {i j : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_fb_entry i j = true) (h1 : s'.local_fb_entry i j = true) :
    (∃ m, s'.msg_fb_pos_sig i j m = true) ∨ s'.msg_fb_neg_sig i j = true := by
  cases l
  case fb_sign_pos =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  case fb_sign_neg =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr local_fb_entry hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, cast_fallback_vote, mvba_step, mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos,
     on_mvba_decide_neg, mvba_terminate, redisseminate_chunk, cast_fb_commit, commit_assign_pos,
     commit_assign_neg, finalize_commit, byz_sign_proposer, byz_deliver_chunk,
     byz_redisseminate_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos,
     byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit,
     byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0


set_option maxHeartbeats 1000000 in
/-- **A collector's record comes with the certificate it broadcast**
(`broadcast_commitqc_*` is the only writer of `local_commitqc_sent`). -/
theorem commitqc_sent_flip {l} {c j : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_commitqc_sent c j = true) (h1 : s'.local_commitqc_sent c j = true) :
    (∃ m, s'.msg_commitqc_pos j m = true) ∨ s'.msg_commitqc_neg j = true := by
  cases l
  case broadcast_commitqc_pos =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  case broadcast_commitqc_neg =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr local_commitqc_sent hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, fb_sign_pos, fb_sign_neg,
     cast_fallback_vote, mvba_step, mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos, on_mvba_decide_neg,
     mvba_terminate, redisseminate_chunk, cast_fb_commit, commit_assign_pos, commit_assign_neg,
     finalize_commit, byz_sign_proposer, byz_deliver_chunk, byz_redisseminate_chunk,
     byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg,
     byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit,
     byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0


set_option maxHeartbeats 1000000 in
/-- **A sent-chunk record comes with the delivery** (`deliver_chunk_assigned`
and `redisseminate_chunk` are its only writers). -/
theorem chunk_sent_flip {l} {k i j : node} {m : merkle_root}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_chunk_sent k i j m = true) (h1 : s'.local_chunk_sent k i j m = true) :
    s'.msg_chunk_received i j m = true := by
  cases l
  case deliver_chunk_assigned =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all; obtain ⟨rfl, rfl, rfl, rfl⟩ := h1; simp
  case redisseminate_chunk =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr local_chunk_sent hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos,
     commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg,
     fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, accept_mvba_commitqc, on_mvba_decide_pos,
     on_mvba_decide_neg, mvba_terminate, cast_fb_commit, commit_assign_pos, commit_assign_neg,
     finalize_commit, byz_sign_proposer, byz_deliver_chunk, byz_redisseminate_chunk,
     byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg,
     byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit,
     byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0


set_option maxHeartbeats 1000000 in
/-- **The fallback-commit record comes with the vote** (`cast_fb_commit`). -/
theorem fbcommit_voted_flip {l} {i : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_fbcommit_voted i = true) (h1 : s'.local_fbcommit_voted i = true) :
    s'.msg_fbcommit_sig i = true := by
  cases l
  case cast_fb_commit =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_cases htr local_fbcommit_voted hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, accept_mvba_commitqc,
     on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk,
     commit_assign_pos, commit_assign_neg, finalize_commit, byz_sign_proposer, byz_deliver_chunk,
     byz_redisseminate_chunk, byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos,
     byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit,
     byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0


set_option maxHeartbeats 1000000 in
/-- **A decision record comes with the entry it recorded**: the handler that
writes `local_mvba_recorded i j` read a decision `v` of `i` and recorded
entry `j` of `v`. -/
theorem mvba_recorded_flip {l} {i j : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_mvba_recorded i j = true) (h1 : s'.local_mvba_recorded i j = true) :
    ∃ v, mvba.decided s.mvba_st i v ∧ ((∃ M, th.mval_pos v j M = true ∧ s'.mvba_decided_pos j M = true) ∨
      (th.mval_neg v j = true ∧ s'.mvba_decided_neg j = true)) := by
  cases l
  case on_mvba_decide_pos i' j' m' v' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, hd, hv, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hi
    · rcases eq_or_ne j' j with rfl | hj
      · exact ⟨_, hd, Or.inl ⟨_, hv, by simp⟩⟩
      · simp_all
    · simp_all
  case on_mvba_decide_neg i' j' v' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, hd, hv, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hi
    · rcases eq_or_ne j' j with rfl | hj
      · exact ⟨_, hd, Or.inr ⟨hv, by simp⟩⟩
      · simp_all
    · simp_all
  frame_cases htr local_mvba_recorded hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, accept_mvba_commitqc,
     mvba_terminate, redisseminate_chunk, cast_fb_commit, commit_assign_pos, commit_assign_neg,
     finalize_commit, byz_sign_proposer, byz_deliver_chunk, byz_redisseminate_chunk,
     byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg,
     byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit,
     byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0


set_option maxHeartbeats 1000000 in
/-- **A handoff record comes with its input**: the step that writes
`local_mvba_qc_accepted i` handed a certificate to `i`'s MVBA, whose
post-state is the new MVBA state. -/
theorem qc_accepted_flip {l} {i : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_mvba_qc_accepted i = true) (h1 : s'.local_mvba_qc_accepted i = true) :
    ∃ c, mvba.accept s.mvba_st i c s'.mvba_st := by
  cases l
  case accept_mvba_commitqc i' c n =>
    chorus_tr htr
    obtain ⟨-, -, hacc, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hi
    · exact ⟨c, hacc⟩
    · simp_all
  frame_cases htr local_mvba_qc_accepted hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose,
     on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, redisseminate_chunk, cast_fb_commit,
     commit_assign_pos, commit_assign_neg,
     finalize_commit, byz_sign_proposer, byz_deliver_chunk, byz_redisseminate_chunk,
     byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg,
     byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit,
     byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0

/-- `abandon i` records `abandoned i`. -/
theorem abandon_effect {i : node} {n : mstate} (htr : (RTS).tr th s (.abandon i n) s') :
    s'.abandoned i = true := by
  chorus_tr htr
  obtain ⟨-, rfl⟩ := htr
  chorus_field_simp

/-- Turn an enabledness goal into the action's guards. -/
local macro "chorus_enabled" : tactic =>
  `(tactic| simp only [Enabled, Chorus.relationalTransitionSystem, Chorus.Next,
      Chorus.NextAct, trSimp])

/-- `i` is **actively participating** at `st`: it has invoked
`participate()` and not `abandon()`. This is the gate every sending rule of
the model requires of its sender ([Chorus.lean](../Chorus.lean), "Participation
inputs"), so it is a hypothesis of every sending rule's enabledness below. -/
def Active (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice))
    (i : node) : Prop :=
  st.participating i = true ∧ ¬ st.abandoned i = true

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

theorem enabled_vote {i : node} (hi : ¬ nset.is_byz i = true) (ha : Active s i)
    (hph : s.phase ≠ Phase_EnumClass.pre_deadline) (hnv : ¬ s.local_voted i = true) :
    Enabled RTS th s (.vote i) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hph, hnv, rfl⟩

theorem vote_effect {i : node} (htr : (RTS).tr th s (.vote i) s') :
    s'.local_voted i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_fb_sign_pos {i j : node} {m : merkle_root} {q qc qv : nodeset}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i)
    (hph : s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
    (hv : s.local_voted i = true) (hnc : ¬ s.msg_commit_cast i = true)
    (hpath : ¬ s.local_path i = PathChoice_EnumClass.fallback) (hj : th.is_proposer j = true)
    (hqv : nset.supermajority qv) (hqvc : ∀ r, nset.member r qv = true → s.msg_vote_cast r = true)
    (hq : nset.greater_than_third q) (hqs : ∀ r, nset.member r q = true → s.msg_vote_pos_sig r j m = true)
    (hqc : nset.greater_than_third qc) (hqcs : ∀ r, nset.member r qc = true → s.msg_chunk_received r j m = true)
    (hwe : th.well_encoded m = true) (hfr : ¬ s.local_fb_entry i j = true) :
    Enabled RTS th s (.fb_sign_pos i j m q qc) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hph, hv, hnc, hpath, hj, ⟨qv, hqv, hqvc⟩, hq, hqs, hqc, hqcs, hwe, hfr, rfl⟩

theorem fb_sign_pos_effect {i j : node} {m : merkle_root} {q qc : nodeset}
    (htr : (RTS).tr th s (.fb_sign_pos i j m q qc) s') :
    s'.msg_fb_pos_sig i j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_fb_sign_neg {i j : node} {qv : nodeset}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i)
    (hph : s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
    (hv : s.local_voted i = true) (hnc : ¬ s.msg_commit_cast i = true)
    (hpath : ¬ s.local_path i = PathChoice_EnumClass.fallback) (hj : th.is_proposer j = true)
    (hqv : nset.supermajority qv) (hqvc : ∀ r, nset.member r qv = true → s.msg_vote_cast r = true)
    (hnone : ∀ M q qc, ¬ (nset.greater_than_third q ∧
      (∀ r, nset.member r q = true → nset.member r qv = true ∧ s.msg_vote_pos_sig r j M = true) ∧
      nset.greater_than_third qc ∧
      (∀ r, nset.member r qc = true → s.msg_chunk_received r j M = true) ∧
      th.well_encoded M = true))
    (hfr : ¬ s.local_fb_entry i j = true) :
    Enabled RTS th s (.fb_sign_neg i j qv) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hph, hv, hnc, hpath, hj, hqv, hqvc,
    fun M q qc h1 h2 h3 h4 h5 => hnone M q qc ⟨h1, h2, h3, h4, h5⟩, hfr, rfl⟩

theorem fb_sign_neg_effect {i j : node} {qv : nodeset}
    (htr : (RTS).tr th s (.fb_sign_neg i j qv) s') :
    s'.msg_fb_neg_sig i j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_cast_fallback_vote {i : node}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i)
    (hph : s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
    (hv : s.local_voted i = true) (hnc : ¬ s.msg_commit_cast i = true)
    (hpath : ¬ s.local_path i = PathChoice_EnumClass.fallback)
    (hall : ∀ J, th.is_proposer J = true →
      (∃ M, s.msg_fb_pos_sig i J M = true) ∨ s.msg_fb_neg_sig i J = true) :
    Enabled RTS th s (.cast_fallback_vote i) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hph, hv, hnc, hpath, hall, rfl⟩

theorem cast_fallback_vote_effect {i : node}
    (htr : (RTS).tr th s (.cast_fallback_vote i) s') :
    s'.msg_fallback_sig i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_broadcast_commitqc_pos {c j : node} {m : merkle_root} {q : nodeset}
    (hc : ¬ nset.is_byz c = true) (ha : Active s c) (hq : nset.supermajority q)
    (hall : ∀ r, nset.member r q = true →
      s.msg_commit_pos_sig r j m = true ∧ s.msg_commit_cast r = true)
    (hfr : ¬ s.local_commitqc_sent c j = true) :
    Enabled RTS th s (.broadcast_commitqc_pos c j m q) := by
  chorus_enabled
  exact ⟨_, hc, ha.1, ha.2, hq, hall, hfr, rfl⟩

theorem broadcast_commitqc_pos_effect {c j : node} {m : merkle_root} {q : nodeset}
    (htr : (RTS).tr th s (.broadcast_commitqc_pos c j m q) s') :
    s'.msg_commitqc_pos j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_broadcast_commitqc_neg {c j : node} {q : nodeset}
    (hc : ¬ nset.is_byz c = true) (ha : Active s c) (hq : nset.supermajority q)
    (hall : ∀ r, nset.member r q = true →
      s.msg_commit_neg_sig r j = true ∧ s.msg_commit_cast r = true)
    (hfr : ¬ s.local_commitqc_sent c j = true) :
    Enabled RTS th s (.broadcast_commitqc_neg c j q) := by
  chorus_enabled
  exact ⟨_, hc, ha.1, ha.2, hq, hall, hfr, rfl⟩

theorem broadcast_commitqc_neg_effect {c j : node} {q : nodeset}
    (htr : (RTS).tr th s (.broadcast_commitqc_neg c j q) s') :
    s'.msg_commitqc_neg j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

/-- `commit_assign_pos`, enabled for a validator that has assigned nothing
for `j` yet, from either certificate. -/
theorem enabled_commit_assign_pos {i j : node} {m : merkle_root}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true)
    (hqc : s.msg_commitqc_pos j m = true ∨ (Chorus.fbcommitqc th s ∧ s.mvba_decided_pos j m = true))
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) (hnn : ¬ s.local_committed_neg i j = true) :
    Enabled RTS th s (.commit_assign_pos i j m) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hnc, hj, hqc, hnp, hnn, rfl⟩

theorem commit_assign_pos_effect {i j : node} {m : merkle_root}
    (htr : (RTS).tr th s (.commit_assign_pos i j m) s') :
    s'.local_committed_pos i j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_commit_assign_neg {i j : node}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true)
    (hqc : s.msg_commitqc_neg j = true ∨ (Chorus.fbcommitqc th s ∧ s.mvba_decided_neg j = true))
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) (hnn : ¬ s.local_committed_neg i j = true) :
    Enabled RTS th s (.commit_assign_neg i j) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hnc, hj, hqc, hnp, hnn, rfl⟩

theorem commit_assign_neg_effect {i j : node}
    (htr : (RTS).tr th s (.commit_assign_neg i j) s') :
    s'.local_committed_neg i j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_finalize_commit {i : node}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hnc : ¬ s.local_committed i = true)
    (hall : ∀ J, th.is_proposer J = true →
      (∃ M, s.local_committed_pos i J M = true) ∨ s.local_committed_neg i J = true) :
    Enabled RTS th s (.finalize_commit i) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hnc, hall, rfl⟩

theorem finalize_commit_effect {i : node}
    (htr : (RTS).tr th s (.finalize_commit i) s') :
    s'.local_committed i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

/-! ### Enabledness and effect, per action the MVBA arm fires -/

theorem enabled_advance_to_mvba_arm (h : s.phase = Phase_EnumClass.post_fb_arm) :
    Enabled RTS th s .advance_to_mvba_arm := by
  chorus_enabled
  exact ⟨_, h, rfl⟩

theorem advance_to_mvba_arm_effect (htr : (RTS).tr th s .advance_to_mvba_arm s') :
    s'.phase = Phase_EnumClass.post_mvba_arm := by
  chorus_tr htr
  obtain ⟨-, rfl⟩ := htr
  chorus_field_simp

theorem enabled_aggregate_fastqc_pos {i j : node} {m : merkle_root} {q : nodeset}
    (hi : ¬ nset.is_byz i = true) (hq : nset.supermajority q)
    (hall : ∀ r, nset.member r q = true → s.msg_vote_pos_sig r j m = true)
    (hnf : ¬ s.local_fastqc_pos i j m = true) :
    Enabled RTS th s (.aggregate_fastqc_pos i j m q) := by
  chorus_enabled
  exact ⟨_, hi, hq, hall, hnf, rfl⟩

theorem aggregate_fastqc_pos_effect {i j : node} {m : merkle_root} {q : nodeset}
    (htr : (RTS).tr th s (.aggregate_fastqc_pos i j m q) s') :
    s'.local_fastqc_pos i j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_aggregate_fastqc_neg {i j : node} {q : nodeset}
    (hi : ¬ nset.is_byz i = true) (hq : nset.supermajority q)
    (hall : ∀ r, nset.member r q = true → s.msg_vote_neg_sig r j = true)
    (hnf : ¬ s.local_fastqc_neg i j = true) :
    Enabled RTS th s (.aggregate_fastqc_neg i j q) := by
  chorus_enabled
  exact ⟨_, hi, hq, hall, hnf, rfl⟩

theorem aggregate_fastqc_neg_effect {i j : node} {q : nodeset}
    (htr : (RTS).tr th s (.aggregate_fastqc_neg i j q) s') :
    s'.local_fastqc_neg i j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_mvba_propose {i : node} {v : mvalue} {n : mstate}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i)
    (htrig : (Chorus.fbcert th s ∧
        (s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)) ∨
      (Chorus.complete_fast_metablock i th s ∧ s.phase = Phase_EnumClass.post_mvba_arm))
    (hpos : ∀ J M, th.mval_pos v J M = true → th.is_proposer J = true ∧
      (Chorus.vote_quorum_pos J M th s ∨ (Chorus.fb_quorum_pos J M th s ∧ Chorus.fbcert th s)))
    (hneg : ∀ J, th.mval_neg v J = true → th.is_proposer J = true ∧
      (Chorus.vote_quorum_neg J th s ∨
        ((Chorus.fb_quorum_neg J th s ∨ Chorus.equiv_evidence J th s) ∧ Chorus.fbcert th s)))
    (hall : ∀ J, th.is_proposer J = true → (∃ M, th.mval_pos v J M = true) ∨ th.mval_neg v J = true)
    (hprop : mvba.propose s.mvba_st i v n) :
    Enabled RTS th s (.mvba_propose i v n) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, htrig, hpos, hneg, hall, hprop, rfl⟩

theorem enabled_accept_mvba_commitqc {i : node} {c : mmsg} {n : mstate}
    (hi : ¬ nset.is_byz i = true) (hfr : ¬ s.local_mvba_qc_accepted i = true)
    (hacc : mvba.accept s.mvba_st i c n) :
    Enabled RTS th s (.accept_mvba_commitqc i c n) := by
  chorus_enabled
  exact ⟨_, hi, hfr, hacc, rfl⟩

theorem enabled_on_mvba_decide_pos {i j : node} {m : merkle_root} {v : mvalue}
    (hi : ¬ nset.is_byz i = true) (hph : s.phase = Phase_EnumClass.post_mvba_arm)
    (hj : th.is_proposer j = true) (hinv : Chorus.mvba_invoked th s)
    (hd : mvba.decided s.mvba_st i v) (hv : th.mval_pos v j m = true)
    (hc : Chorus.vote_quorum_pos j m th s ∨ (Chorus.fb_quorum_pos j m th s ∧ Chorus.fbcert th s))
    (hfr : ¬ s.local_mvba_recorded i j = true) :
    Enabled RTS th s (.on_mvba_decide_pos i j m v) := by
  chorus_enabled
  exact ⟨_, hi, hph, hj, hinv, hd, hv, hc, hfr, rfl⟩

theorem on_mvba_decide_pos_effect {i j : node} {m : merkle_root} {v : mvalue}
    (htr : (RTS).tr th s (.on_mvba_decide_pos i j m v) s') :
    s'.mvba_decided_pos j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_on_mvba_decide_neg {i j : node} {v : mvalue}
    (hi : ¬ nset.is_byz i = true) (hph : s.phase = Phase_EnumClass.post_mvba_arm)
    (hj : th.is_proposer j = true) (hinv : Chorus.mvba_invoked th s)
    (hd : mvba.decided s.mvba_st i v) (hv : th.mval_neg v j = true)
    (hc : Chorus.vote_quorum_neg j th s ∨
      ((Chorus.fb_quorum_neg j th s ∨ Chorus.equiv_evidence j th s) ∧ Chorus.fbcert th s))
    (hfr : ¬ s.local_mvba_recorded i j = true) :
    Enabled RTS th s (.on_mvba_decide_neg i j v) := by
  chorus_enabled
  exact ⟨_, hi, hph, hj, hinv, hd, hv, hc, hfr, rfl⟩

theorem on_mvba_decide_neg_effect {i j : node} {v : mvalue}
    (htr : (RTS).tr th s (.on_mvba_decide_neg i j v) s') :
    s'.mvba_decided_neg j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_mvba_terminate {i : node} {v : mvalue}
    (hi : ¬ nset.is_byz i = true) (hph : s.phase = Phase_EnumClass.post_mvba_arm)
    (hnc : ¬ s.mvba_complete = true) (hinv : Chorus.mvba_invoked th s)
    (hd : mvba.decided s.mvba_st i v)
    (hall : ∀ J, th.is_proposer J = true →
      ((∃ M, th.mval_pos v J M = true ∧ s.mvba_decided_pos J M = true) ∨
        (th.mval_neg v J = true ∧ s.mvba_decided_neg J = true))) :
    Enabled RTS th s (.mvba_terminate i v) := by
  chorus_enabled
  exact ⟨_, hi, hph, hnc, hinv, hd, hall, rfl⟩

theorem mvba_terminate_effect {i : node} {v : mvalue}
    (htr : (RTS).tr th s (.mvba_terminate i v) s') :
    s'.mvba_complete = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_redisseminate_chunk {k i j : node} {m : merkle_root}
    (hk : ¬ nset.is_byz k = true) (ha : Active s k) (hj : th.is_proposer j = true)
    (hs : s.msg_proposer_signed j m = true) (hq : Chorus.chunk_quorum j m th s)
    (hfr : ¬ s.local_chunk_sent k i j m = true) :
    Enabled RTS th s (.redisseminate_chunk k i j m) := by
  chorus_enabled
  exact ⟨_, hk, ha.1, ha.2, hj, hs, hq, hfr, rfl⟩

theorem redisseminate_chunk_effect {k i j : node} {m : merkle_root}
    (htr : (RTS).tr th s (.redisseminate_chunk k i j m) s') :
    s'.msg_chunk_received i j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_cast_fb_commit {i : node}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hph : s.phase = Phase_EnumClass.post_mvba_arm)
    (hc : s.mvba_complete = true)
    (hda : ∀ J M, th.is_proposer J = true → s.mvba_decided_pos J M = true →
      Chorus.vote_quorum_pos J M th s ∨ s.msg_chunk_received i J M = true)
    (hfr : ¬ s.local_fbcommit_voted i = true) :
    Enabled RTS th s (.cast_fb_commit i) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hph, hc, hda, hfr, rfl⟩

theorem cast_fb_commit_effect {i : node}
    (htr : (RTS).tr th s (.cast_fb_commit i) s') :
    s'.msg_fbcommit_sig i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

/-! ### The certificates are monotone -/

theorem vote_quorum_pos_step {l} (htr : (RTS).tr th s l s') {j : node} {m : merkle_root}
    (h : Chorus.vote_quorum_pos j m th s) : Chorus.vote_quorum_pos j m th s' := by
  unfold Chorus.vote_quorum_pos at h ⊢
  obtain ⟨q, hq, hall⟩ := h
  exact ⟨q, hq, fun a ha => msg_vote_pos_sig_mono htr a j m (hall a ha)⟩

theorem vote_quorum_neg_step {l} (htr : (RTS).tr th s l s') {j : node}
    (h : Chorus.vote_quorum_neg j th s) : Chorus.vote_quorum_neg j th s' := by
  unfold Chorus.vote_quorum_neg at h ⊢
  obtain ⟨q, hq, hall⟩ := h
  exact ⟨q, hq, fun a ha => msg_vote_neg_sig_mono htr a j (hall a ha)⟩

theorem fb_quorum_pos_step {l} (htr : (RTS).tr th s l s') {j : node} {m : merkle_root}
    (h : Chorus.fb_quorum_pos j m th s) : Chorus.fb_quorum_pos j m th s' := by
  unfold Chorus.fb_quorum_pos at h ⊢
  obtain ⟨q, hq, hall⟩ := h
  exact ⟨q, hq, fun a ha => Chorus.msg_fb_pos_sig.mono htr a j m (hall a ha)⟩

theorem fb_quorum_neg_step {l} (htr : (RTS).tr th s l s') {j : node}
    (h : Chorus.fb_quorum_neg j th s) : Chorus.fb_quorum_neg j th s' := by
  unfold Chorus.fb_quorum_neg at h ⊢
  obtain ⟨q, hq, hall⟩ := h
  exact ⟨q, hq, fun a ha => Chorus.msg_fb_neg_sig.mono htr a j (hall a ha)⟩

theorem equiv_evidence_step {l} (htr : (RTS).tr th s l s') {j : node}
    (h : Chorus.equiv_evidence j th s) : Chorus.equiv_evidence j th s' := by
  unfold Chorus.equiv_evidence at h ⊢
  obtain ⟨m1, m2, hne, h1, h2⟩ := h
  exact ⟨m1, m2, hne, Chorus.msg_proposer_signed.mono htr j m1 h1,
    Chorus.msg_proposer_signed.mono htr j m2 h2⟩

theorem fbcert_step {l} (htr : (RTS).tr th s l s')
    (h : Chorus.fbcert th s) : Chorus.fbcert th s' := by
  unfold Chorus.fbcert at h ⊢
  obtain ⟨q, hq, hall⟩ := h
  exact ⟨q, hq, fun a ha => Chorus.msg_fallback_sig.mono htr a (hall a ha)⟩

theorem complete_fast_metablock_step {l} (htr : (RTS).tr th s l s') {i : node}
    (h : Chorus.complete_fast_metablock i th s) : Chorus.complete_fast_metablock i th s' := by
  unfold Chorus.complete_fast_metablock at h ⊢
  intro j hj
  rcases h j hj with ⟨m, hm⟩ | hm
  · exact Or.inl ⟨m, Chorus.local_fastqc_pos.mono htr i j m hm⟩
  · exact Or.inr (Chorus.local_fastqc_neg.mono htr i j hm)

theorem mvba_invoked_step {l} (htr : (RTS).tr th s l s')
    (h : Chorus.mvba_invoked th s) : Chorus.mvba_invoked th s' := by
  unfold Chorus.mvba_invoked at h ⊢
  rcases h with h | ⟨i, hi, h⟩
  · exact Or.inl (fbcert_step htr h)
  · exact Or.inr ⟨i, hi, complete_fast_metablock_step htr h⟩

theorem chunk_quorum_step {l} (htr : (RTS).tr th s l s') {j : node} {m : merkle_root}
    (h : Chorus.chunk_quorum j m th s) : Chorus.chunk_quorum j m th s' := by
  unfold Chorus.chunk_quorum at h ⊢
  obtain ⟨q, hq, hall⟩ := h
  exact ⟨q, hq, fun a ha => Chorus.msg_chunk_received.mono htr a j m (hall a ha)⟩

theorem fbcommitqc_step {l} (htr : (RTS).tr th s l s')
    (h : Chorus.fbcommitqc th s) : Chorus.fbcommitqc th s' := by
  unfold Chorus.fbcommitqc at h ⊢
  obtain ⟨q, hq, hall⟩ := h
  exact ⟨q, hq, fun a ha => Chorus.msg_fbcommit_sig.mono htr a (hall a ha)⟩

/-- **A decided root is proposer-signed**, at every reachable state: the
decision is backed by a FastQC or a FallbackQC (`mvba_decided_pos_backed`),
either of which has an honest member whose signature pins the proposer's. -/
theorem proposer_signed_of_decided_pos (hr : (RTS).reachable th s) {j : node} {m : merkle_root}
    (h : s.mvba_decided_pos j m = true) : s.msg_proposer_signed j m = true := by
  rcases Chorus.reachable_mvba_decided_pos_backed hr j m h with hv | ⟨hf, -⟩
  · unfold Chorus.vote_quorum_pos at hv
    obtain ⟨q, hq, hall⟩ := hv
    obtain ⟨a, ha, hab⟩ :=
      ByzNodeSet.greater_than_third_one_honest q (ByzNodeSet.supermajority_greater_than_third q hq)
    exact Chorus.reachable_local_entry_pos_signed hr a j m
      ⟨hab, Chorus.reachable_vote_pos_from_local hr a j m ⟨hab, hall a ha⟩⟩
  · unfold Chorus.fb_quorum_pos at hf
    obtain ⟨q, hq, hall⟩ := hf
    obtain ⟨a, ha, -⟩ := ByzNodeSet.greater_than_third_one_honest q hq
    exact Chorus.reachable_fb_pos_sig_proposer_signed hr a j m (hall a ha)

/-! ### The two guards the MVBA arm is stated with -/

/-- `i`'s **proposal trigger** (Algorithm 5 (`alg:fallback`)), `mvba_propose`'s second
guard: the fallback trigger (`fbcert`) from the fallback arm on, or the
case-(a) trigger — a complete fast meta-block of its own — at the MVBA
arm. -/
def ProposeTrigger (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice))
    (i : node) : Prop :=
  (Chorus.fbcert th st ∧
    (st.phase = Phase_EnumClass.post_fb_arm ∨ st.phase = Phase_EnumClass.post_mvba_arm)) ∨
  (Chorus.complete_fast_metablock i th st ∧ st.phase = Phase_EnumClass.post_mvba_arm)

/-- **An assignable entry for proposer `j`** — `commit_assign_*`'s
certificate guard: a broadcast fast commit certificate, or the fallback
commit certificate together with the MVBA's decision for `j`. -/
def Assignable (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice))
    (j : node) : Prop :=
  (∃ m, st.msg_commitqc_pos j m = true ∨ (Chorus.fbcommitqc th st ∧ st.mvba_decided_pos j m = true)) ∨
  (st.msg_commitqc_neg j = true ∨ (Chorus.fbcommitqc th st ∧ st.mvba_decided_neg j = true))

theorem assignable_pos_step {l} (htr : (RTS).tr th s l s') {j : node} {m : merkle_root}
    (h : s.msg_commitqc_pos j m = true ∨ (Chorus.fbcommitqc th s ∧ s.mvba_decided_pos j m = true)) :
    s'.msg_commitqc_pos j m = true ∨ (Chorus.fbcommitqc th s' ∧ s'.mvba_decided_pos j m = true) :=
  h.imp (Chorus.msg_commitqc_pos.mono htr j m)
    fun ⟨hq, hd⟩ => ⟨fbcommitqc_step htr hq, Chorus.mvba_decided_pos.mono htr j m hd⟩

theorem assignable_neg_step {l} (htr : (RTS).tr th s l s') {j : node}
    (h : s.msg_commitqc_neg j = true ∨ (Chorus.fbcommitqc th s ∧ s.mvba_decided_neg j = true)) :
    s'.msg_commitqc_neg j = true ∨ (Chorus.fbcommitqc th s' ∧ s'.mvba_decided_neg j = true) :=
  h.imp (Chorus.msg_commitqc_neg.mono htr j)
    fun ⟨hq, hd⟩ => ⟨fbcommitqc_step htr hq, Chorus.mvba_decided_neg.mono htr j hd⟩

/-- **The MVBA's trigger, from correct senders**: a correct `FBCert`, or a
correct validator that cast its fast commit vote with a complete fast
meta-block (whose `FastBlock` it broadcast). The form of `mvba_invoked` that
makes the proposals owed. -/
def CorrectTrigger (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)) :
    Prop :=
  CorrectFBCert st ∨ ∃ i0, ¬ nset.is_byz i0 = true ∧ st.msg_commit_cast i0 = true ∧
    Chorus.complete_fast_metablock (nset := nset) (mvba := mvba) i0 th st

theorem correctFBCert_step {l} (htr : (RTS).tr th s l s') (h : CorrectFBCert s) :
    CorrectFBCert s' :=
  let ⟨q, hq, hc, hall⟩ := h
  ⟨q, hq, hc, fun a ha => Chorus.msg_fallback_sig.mono htr a (hall a ha)⟩

theorem correctFbCommitQC_step {l} (htr : (RTS).tr th s l s') (h : CorrectFbCommitQC s) :
    CorrectFbCommitQC s' :=
  let ⟨q, hq, hc, hall⟩ := h
  ⟨q, hq, hc, fun a ha => Chorus.msg_fbcommit_sig.mono htr a (hall a ha)⟩

theorem fbcert_of_correct (h : CorrectFBCert s) : Chorus.fbcert (nset := nset) (mvba := mvba) th s :=
  let ⟨q, hq, _, hall⟩ := h
  ⟨q, hq, hall⟩

theorem fbcommitqc_of_correct (h : CorrectFbCommitQC s) :
    Chorus.fbcommitqc (nset := nset) (mvba := mvba) th s :=
  let ⟨q, hq, _, hall⟩ := h
  ⟨q, hq, hall⟩

/-- **A commitment proof for `j`'s positive entry `m` from correct senders**:
a correct validator finalized with that entry (its finalization
re-broadcast its proof), or the fallback commit certificate from correct
voters with the MVBA's decision. It is `commit_assign_pos`'s owed-condition
(`Owed`), verbatim. -/
def ProofPos (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice))
    (j : node) (m : merkle_root) : Prop :=
  (∃ k, ¬ nset.is_byz k = true ∧ st.local_committed k = true ∧ st.local_committed_pos k j m = true) ∨
    (CorrectFbCommitQC st ∧ st.mvba_decided_pos j m = true)

/-- The same for `j`'s negative entry. -/
def ProofNeg (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice))
    (j : node) : Prop :=
  (∃ k, ¬ nset.is_byz k = true ∧ st.local_committed k = true ∧ st.local_committed_neg k j = true) ∨
    (CorrectFbCommitQC st ∧ st.mvba_decided_neg j = true)

theorem proofPos_step {l} (htr : (RTS).tr th s l s') {j : node} {m : merkle_root}
    (h : ProofPos (nset := nset) s j m) : ProofPos (nset := nset) s' j m :=
  h.imp (fun ⟨k, hk, hc, hp⟩ => ⟨k, hk, Chorus.local_committed.mono htr k hc,
      Chorus.local_committed_pos.mono htr k j m hp⟩)
    fun ⟨hq, hd⟩ => ⟨correctFbCommitQC_step htr hq, Chorus.mvba_decided_pos.mono htr j m hd⟩

theorem proofNeg_step {l} (htr : (RTS).tr th s l s') {j : node}
    (h : ProofNeg (nset := nset) s j) : ProofNeg (nset := nset) s' j :=
  h.imp (fun ⟨k, hk, hc, hp⟩ => ⟨k, hk, Chorus.local_committed.mono htr k hc,
      Chorus.local_committed_neg.mono htr k j hp⟩)
    fun ⟨hq, hd⟩ => ⟨correctFbCommitQC_step htr hq, Chorus.mvba_decided_neg.mono htr j hd⟩

theorem mvba_invoked_of_correct (h : CorrectTrigger (nset := nset) (mvba := mvba) th s) :
    Chorus.mvba_invoked (nset := nset) (mvba := mvba) th s := by
  unfold Chorus.mvba_invoked
  rcases h with hfb | ⟨i0, hi0, -, hc⟩
  · exact Or.inl (fbcert_of_correct hfb)
  · exact Or.inr ⟨i0, hi0, hc⟩

end Steps

/-! ## Run-level facts

The two chains of [Liveness.md](../../docs/Liveness.md) §4.4, over any labelled Chorus run.
The fairness hypothesis is `FJustice`'s per-label clause, `∀ l,
JusticeLabel l → ¬ FamilyLabel l → WeaklyFair r l`, so the concrete
theorems below pass its first component through unchanged; none of the
stage-3 chains fires `mvba_propose`. The quorum instance and the MVBA are implicit arguments here
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

/-- **From index `A` on, every correct validator is actively
participating** (`Active`). This is the gate hypothesis the honest links
below take. The claim's two caller premises give it on the branch of the
proof where no correct validator ever finalizes (`termination`): everybody
eventually participates, and nobody abandons before finalizing. -/
def ActiveFrom (r : CRun th) (A : Nat) : Prop :=
  ∀ n, A ≤ n → ∀ i, ¬ nset.is_byz i = true → Active (r.at' n) i

/-- **`FJustice`'s per-label clause, at any MVBA**: every fair label outside
the two families is weakly fair while it is owed (`Owed`, correct senders).
The chains below take it in this form, and the claim's `FJustice` gives it
as its first component. -/
abbrev PerLabel (r : CRun th) : Prop :=
  ∀ l, JusticeLabel l → ¬ FamilyLabel l →
    WeaklyFairWhen r (Owed (nset := nset) (mvba := mvba) th l) l

/-- **A fired-once record holds only together with its effect**, at every
point of every run: the record is initially unset, the step at which it is
first set establishes `Q` (the first-flip lemmas above), and `Q` persists.
This is what lets a link read "`Q` has not happened yet" as "the action has
not fired yet", which is the action's fired-once guard. -/
theorem record_backed (r : CRun th)
    {F Q : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) → Prop}
    (h0 : ¬ F (r.at' 0))
    (hflip : ∀ n, ¬ F (r.at' n) → F (r.at' (n + 1)) → Q (r.at' (n + 1)))
    (hQ : ∀ n, Q (r.at' n) → Q (r.at' (n + 1))) :
    ∀ n, F (r.at' n) → Q (r.at' n)
  | 0, h => absurd h h0
  | n + 1, h => by
    by_cases hn : F (r.at' n)
    · exact hQ n (record_backed r h0 hflip hQ n hn)
    · exact hflip n hn h

/-- A correct validator's fallback-entry record comes with its fallback
signature for that proposer. -/
theorem fb_entry_sigs (r : CRun th) {i j : node} :
    ∀ n, (r.at' n).local_fb_entry i j = true →
      (∃ m, (r.at' n).msg_fb_pos_sig i j m = true) ∨ (r.at' n).msg_fb_neg_sig i j = true :=
  record_backed r (F := fun st => st.local_fb_entry i j = true)
    (Q := fun st => (∃ m, st.msg_fb_pos_sig i j m = true) ∨ st.msg_fb_neg_sig i j = true)
    (by simp [Chorus.local_fb_entry.init r.starts i j])
    (fun n h0 h1 => fb_entry_flip (r.steps n) h0 h1)
    (fun n h => h.imp (fun ⟨m, hm⟩ => ⟨m, Chorus.msg_fb_pos_sig.mono (r.steps n) i j m hm⟩)
      (Chorus.msg_fb_neg_sig.mono (r.steps n) i j))

/-- A collector's record comes with a broadcast certificate for that
proposer. -/
theorem commitqc_sent_msg (r : CRun th) {c j : node} :
    ∀ n, (r.at' n).local_commitqc_sent c j = true →
      (∃ m, (r.at' n).msg_commitqc_pos j m = true) ∨ (r.at' n).msg_commitqc_neg j = true :=
  record_backed r (F := fun st => st.local_commitqc_sent c j = true)
    (Q := fun st => (∃ m, st.msg_commitqc_pos j m = true) ∨ st.msg_commitqc_neg j = true)
    (by simp [Chorus.local_commitqc_sent.init r.starts c j])
    (fun n h0 h1 => commitqc_sent_flip (r.steps n) h0 h1)
    (fun n h => h.imp (fun ⟨m, hm⟩ => ⟨m, Chorus.msg_commitqc_pos.mono (r.steps n) j m hm⟩)
      (Chorus.msg_commitqc_neg.mono (r.steps n) j))

/-- A sent-chunk record comes with the chunk's delivery. -/
theorem chunk_sent_received (r : CRun th) {k i j : node} {m : merkle_root} :
    ∀ n, (r.at' n).local_chunk_sent k i j m = true → (r.at' n).msg_chunk_received i j m = true :=
  record_backed r (F := fun st => st.local_chunk_sent k i j m = true)
    (Q := fun st => st.msg_chunk_received i j m = true)
    (by simp [Chorus.local_chunk_sent.init r.starts k i j m])
    (fun n h0 h1 => chunk_sent_flip (r.steps n) h0 h1)
    (fun n h => Chorus.msg_chunk_received.mono (r.steps n) i j m h)

/-- The fallback-commit record comes with the fallback commit vote. -/
theorem fbcommit_voted_sig (r : CRun th) {i : node} :
    ∀ n, (r.at' n).local_fbcommit_voted i = true → (r.at' n).msg_fbcommit_sig i = true :=
  record_backed r (F := fun st => st.local_fbcommit_voted i = true)
    (Q := fun st => st.msg_fbcommit_sig i = true)
    (by simp [Chorus.local_fbcommit_voted.init r.starts i])
    (fun n h0 h1 => fbcommit_voted_flip (r.steps n) h0 h1)
    (fun n h => Chorus.msg_fbcommit_sig.mono (r.steps n) i h)

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
theorem eventually_atArm (r : CRun th) (hfj : PerLabel r) :
    ∃ N, ∀ n, N ≤ n → AtArm (r.at' n) := by
  obtain ⟨d1, -, -, -, -, -⟩ := phase_distinct (Phase := Phase)
  have hpast : ∃ N, (r.at' N).phase ≠ Phase_EnumClass.pre_deadline := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n, -, hfire⟩ := (hfj .advance_to_deadline ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial) 0
      (fun n _ => (enabled_advance_to_deadline (hcon n)))
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
    obtain ⟨n, hn, hfire⟩ := (hfj .advance_to_fb_arm ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial) N1
      (fun n hn => (enabled_advance_to_fb_arm (hpd n hn)))
    exact hcon ⟨n + 1, Or.inl (advance_to_fb_arm_effect (hfire ▸ r.steps n))⟩
  obtain ⟨N2, hN2⟩ := harm
  exact ⟨N2, r.mono (P := AtArm) (fun m hm => AtArm.step (r.steps m) hm) hN2⟩

/-- **Every correct validator votes**: `vote i` needs only the phase past the
deadline and `¬ local_voted i`. -/
theorem eventually_voted (r : CRun th) (hfj : PerLabel r)
    {A : Nat} (hact : ActiveFrom r A)
    {i : node} (hi : ¬ nset.is_byz i = true) : ∃ N, (r.at' N).local_voted i = true := by
  obtain ⟨N, hN⟩ := eventually_atArm r hfj
  by_contra hcon
  push Not at hcon
  obtain ⟨n, -, hfire⟩ := (hfj (.vote i) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial) (max N A)
    (fun n hn => (enabled_vote hi (hact n (by omega) i hi) (hN n (by omega)).ne_pre (hcon n)))
  exact hcon (n + 1) (vote_effect (hfire ▸ r.steps n))

/-- **An honest quorum's votes are all on the network at one index**, and
stay there. `nodes` is a complete list of validators — the finiteness that
collapses the family of eventualities (`LRun.eventually_forall`). -/
theorem eventually_quorum_cast (r : CRun th) (hfj : PerLabel r)
    {A : Nat} (hact : ActiveFrom r A) (nodes : List node) (hnodes : ∀ a, a ∈ nodes)
    {qv : nodeset} (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true) :
    ∃ N, ∀ n, N ≤ n → ∀ a, nset.member a qv = true → (r.at' n).msg_vote_cast a = true := by
  obtain ⟨N, -, hN⟩ := r.eventually_forall
    (fun a st => nset.member a qv = true → st.msg_vote_cast a = true)
    (fun a n h hm => Chorus.msg_vote_cast.mono (r.steps n) a (h hm)) 0 nodes
    (fun a _ => by
      by_cases hm : nset.member a qv = true
      · obtain ⟨n, hn⟩ := eventually_voted r hfj hact (hqvh a hm)
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
*is* its guard) — and `cast_fallback_vote i` fires. While `i` has no
signature for a proposer it has not signed an entry for it either
(`fb_entry_sigs`), so the fired-once guard holds throughout. Every step either fires
or is disabled by `i` casting a path vote, which saturates it by the
first-flip facts. -/
theorem eventually_saturated (r : CRun th) (hfj : PerLabel r)
    {A : Nat} (hact : ActiveFrom r A) (nodes : List node) (hnodes : ∀ a, a ∈ nodes)
    {qv : nodeset} (hqv : nset.supermajority qv)
    (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true)
    {i : node} (hi : ¬ nset.is_byz i = true) : ∃ n, Saturated th (r.at' n) i := by
  obtain ⟨Na, hNa⟩ := eventually_atArm r hfj
  obtain ⟨Nv, hNv⟩ := eventually_voted r hfj hact hi
  obtain ⟨Nq, hNq⟩ := eventually_quorum_cast r hfj hact nodes hnodes hqvh
  by_contra hcon
  -- `i` never casts a path vote: either would saturate it.
  have hnc : ∀ n, ¬ (r.at' n).msg_commit_cast i = true :=
    fun n h => hcon ⟨n, Or.inl ⟨h, commit_cast_sigs r hi n h⟩⟩
  have hnf : ∀ n, ¬ (r.at' n).msg_fallback_sig i = true :=
    fun n h => hcon ⟨n, Or.inr ⟨h, fallback_sig_sigs r hi n h⟩⟩
  have hnp : ∀ n, ¬ (r.at' n).local_path i = PathChoice_EnumClass.fallback :=
    fun n h => hnf n (path_fallback_sig r n h)
  -- From `N` on: at an arm, `i` has voted, the honest quorum's votes are cast.
  have harm : ∀ n, max A (max Na (max Nv Nq)) ≤ n → AtArm (r.at' n) :=
    fun n hn => hNa n (by omega)
  have hv : ∀ n, max A (max Na (max Nv Nq)) ≤ n → (r.at' n).local_voted i = true :=
    fun n hn => r.mono (P := fun st => st.local_voted i = true)
      (fun m hm => Chorus.local_voted.mono (r.steps m) i hm) hNv n (by omega)
  have hq : ∀ n, max A (max Na (max Nv Nq)) ≤ n →
      ∀ a, nset.member a qv = true → (r.at' n).msg_vote_cast a = true :=
    fun n hn => hNq n (by omega)
  -- Each proposer eventually carries a fallback signature from `i`.
  have hsign : ∀ j, th.is_proposer j = true → ∃ n, max A (max Na (max Nv Nq)) ≤ n ∧
      ((∃ m, (r.at' n).msg_fb_pos_sig i j m = true) ∨ (r.at' n).msg_fb_neg_sig i j = true) := by
    intro j hj
    by_contra hns
    by_cases hpos : ∃ n, max A (max Na (max Nv Nq)) ≤ n ∧ ∃ M q qc, nset.greater_than_third q ∧
        (∀ a, nset.member a q = true → nset.member a qv = true ∧ (r.at' n).msg_vote_pos_sig a j M = true) ∧
        nset.greater_than_third qc ∧
        (∀ a, nset.member a qc = true → (r.at' n).msg_chunk_received a j M = true) ∧
        th.well_encoded M = true
    · -- Positive evidence appeared: it persists, so `fb_sign_pos` stays enabled.
      -- The votes are the honest quorum's, so they are owed; and a positive
      -- vote carries its chunk (`vote_pos_sig_chunk`), so the voters are also
      -- the chunk holders the step decodes from, correct ones.
      obtain ⟨n0, hn0, M, q, -, hq1, hq2, -, -, hwe⟩ := hpos
      have hQ : Mvba.CorrectQuorum (node := node) q := fun a ha => hqvh a (hq2 a ha).1
      have hq2' : ∀ n, n0 ≤ n → ∀ a, nset.member a q = true → (r.at' n).msg_vote_pos_sig a j M = true :=
        fun n hn a ha => r.mono (P := fun st => st.msg_vote_pos_sig a j M = true)
          (fun m hm => msg_vote_pos_sig_mono (r.steps m) a j M hm) (hq2 a ha).2 n hn
      have hqc2' : ∀ n, n0 ≤ n → ∀ a, nset.member a q = true → (r.at' n).msg_chunk_received a j M = true :=
        fun n hn a ha => Chorus.reachable_vote_pos_sig_chunk (r.reachable n) a j M (hq2' n hn a ha)
      obtain ⟨n, hn, hfire⟩ := (hfj (.fb_sign_pos i j M q q) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).fires n0
        (fun n hn => ⟨hQ, hQ, qv, hqv, hqvh, hq n (by omega)⟩)
        (fun n hn => (enabled_fb_sign_pos hi (hact n (by omega) i hi) (harm n (by omega)) (hv n (by omega)) (hnc n) (hnp n) hj
          hqv (hq n (by omega)) hq1 (hq2' n hn) hq1 (hqc2' n hn) hwe
          fun h => hns ⟨n, by omega, fb_entry_sigs r n h⟩))
      exact hns ⟨n + 1, by omega, Or.inl ⟨M, fb_sign_pos_effect (hfire ▸ r.steps n)⟩⟩
    · -- It never appears: that absence is `fb_sign_neg`'s guard against `qv`,
      -- a correct quorum.
      obtain ⟨n, hn, hfire⟩ := (hfj (.fb_sign_neg i j qv) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).fires
        (max A (max Na (max Nv Nq))) (fun _ _ => hqvh)
        (fun n hn => (enabled_fb_sign_neg hi (hact n (by omega) i hi) (harm n hn) (hv n hn) (hnc n) (hnp n) hj
          hqv (hq n hn) (fun M q qc hh => hpos ⟨n, hn, M, q, qc, hh⟩)
          fun h => hns ⟨n, hn, fb_entry_sigs r n h⟩))
      exact hns ⟨n + 1, by omega, Or.inr (fb_sign_neg_effect (hfire ▸ r.steps n))⟩
  -- All proposers at one index, and ever after.
  obtain ⟨Ns, hNs, hall⟩ := r.eventually_forall
    (fun j st => th.is_proposer j = true →
      (∃ m, st.msg_fb_pos_sig i j m = true) ∨ st.msg_fb_neg_sig i j = true)
    (fun j n h hj => by
      rcases h hj with ⟨m, hm⟩ | hm
      · exact Or.inl ⟨m, Chorus.msg_fb_pos_sig.mono (r.steps n) i j m hm⟩
      · exact Or.inr (Chorus.msg_fb_neg_sig.mono (r.steps n) i j hm))
    (max A (max Na (max Nv Nq))) nodes
    (fun j _ => by
      by_cases hj : th.is_proposer j = true
      · obtain ⟨n, hn, h⟩ := hsign j hj
        exact ⟨n, hn, fun _ => h⟩
      · exact ⟨max A (max Na (max Nv Nq)), Nat.le_refl _, fun h => absurd h hj⟩)
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
  obtain ⟨n, -, hfire⟩ := (hfj (.cast_fallback_vote i) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial) Ns
    (fun n hn => (enabled_cast_fallback_vote hi (hact n (by omega) i hi) (harm n (by omega)) (hv n (by omega)) (hnc n) (hnp n)
      (hall' n hn)))
  exact hnf (n + 1) (cast_fallback_vote_effect (hfire ▸ r.steps n))

/-- **Saturation of the whole correct population at one index** — the `hsat`
hypothesis of `progress_dichotomy_of_saturation`, and it persists. -/
theorem eventually_all_saturated (r : CRun th) (hfj : PerLabel r)
    {A : Nat} (hact : ActiveFrom r A) (nodes : List node) (hnodes : ∀ a, a ∈ nodes)
    {qv : nodeset} (hqv : nset.supermajority qv)
    (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true) :
    ∃ N, ∀ n, N ≤ n → ∀ i, ¬ nset.is_byz i = true → Saturated th (r.at' n) i := by
  obtain ⟨N, -, hN⟩ := r.eventually_forall
    (fun i st => ¬ nset.is_byz i = true → Saturated th st i)
    (fun i n h hi => (h hi).step (r.steps n)) 0 nodes
    (fun i _ => by
      by_cases hi : nset.is_byz i = true
      · exact ⟨0, Nat.le_refl 0, fun h => absurd hi h⟩
      · obtain ⟨n, hn⟩ := eventually_saturated r hfj hact nodes hnodes hqv hqvh hi
        exact ⟨n, Nat.zero_le _, fun _ => hn⟩)
  exact ⟨N, fun n hn i hi =>
    r.mono (P := fun st => Saturated th st i) (fun m h => h.step (r.steps m))
      (hN i (hnodes i) hi) n hn⟩

/-- **The phase reaches the MVBA arm and stays there**: from an arm,
`advance_to_mvba_arm` is weakly fair and enabled at the fallback arm. -/
theorem eventually_mvbaArm (r : CRun th) (hfj : PerLabel r) :
    ∃ N, ∀ n, N ≤ n → (r.at' n).phase = Phase_EnumClass.post_mvba_arm := by
  obtain ⟨-, -, d3, -, d5, d6⟩ := phase_distinct (Phase := Phase)
  obtain ⟨Na, hNa⟩ := eventually_atArm r hfj
  have hstay : ∀ m, (r.at' m).phase = Phase_EnumClass.post_mvba_arm →
      (r.at' (m + 1)).phase = Phase_EnumClass.post_mvba_arm := by
    intro m hm
    rcases phase_step (r.steps m) with h' | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h']; exact hm
    · exact absurd (h1.symm.trans hm) d3
    · exact absurd (h1.symm.trans hm) d5
    · exact absurd (h1.symm.trans hm) d6
  have hex : ∃ N, (r.at' N).phase = Phase_EnumClass.post_mvba_arm := by
    by_contra hcon
    have hfb : ∀ n, Na ≤ n → (r.at' n).phase = Phase_EnumClass.post_fb_arm :=
      fun n hn => (hNa n hn).resolve_right fun h => hcon ⟨n, h⟩
    obtain ⟨n, -, hfire⟩ := (hfj .advance_to_mvba_arm ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial) Na
      (fun n hn => (enabled_advance_to_mvba_arm (hfb n hn)))
    exact hcon ⟨n + 1, advance_to_mvba_arm_effect (hfire ▸ r.steps n)⟩
  obtain ⟨N, hN⟩ := hex
  exact ⟨N, r.mono (P := fun st => st.phase = Phase_EnumClass.post_mvba_arm) hstay hN⟩

/-- **A complete fast meta-block spreads.** If a correct validator that has
cast its fast commit vote holds a FastQC for every proposer, every correct
validator eventually does: the rule that cast the vote also broadcast the
`FastBlock` (Algorithm 4, line 20 (`line:fast-metablock`)), so adopting each FastQC is owed, and
each is backed by a vote quorum on the network (`local_fastqc_*_backed`),
which keeps `aggregate_fastqc_*` enabled. -/
theorem eventually_complete_fast_metablock (r : CRun th)
    (hfj : PerLabel r)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) {N : Nat} {i0 : node} (hi0 : ¬ nset.is_byz i0 = true)
    (hcast0 : (r.at' N).msg_commit_cast i0 = true)
    (h0 : Chorus.complete_fast_metablock (nset := nset) (mvba := mvba) i0 th (r.at' N))
    {i : node} (hi : ¬ nset.is_byz i = true) :
    ∃ M, N ≤ M ∧ Chorus.complete_fast_metablock (nset := nset) (mvba := mvba) i th (r.at' M) := by
  unfold Chorus.complete_fast_metablock at h0
  obtain ⟨M, hM, hall⟩ := r.eventually_forall
    (fun j st => th.is_proposer j = true →
      (∃ m, st.local_fastqc_pos i j m = true) ∨ st.local_fastqc_neg i j = true)
    (fun j n h hj => by
      rcases h hj with ⟨m, hm⟩ | hm
      · exact Or.inl ⟨m, Chorus.local_fastqc_pos.mono (r.steps n) i j m hm⟩
      · exact Or.inr (Chorus.local_fastqc_neg.mono (r.steps n) i j hm))
    N nodes
    (fun j _ => by
      by_cases hj : th.is_proposer j = true
      · rcases h0 j hj with ⟨m, hm⟩ | hm
        · obtain ⟨q, hq, hqs⟩ := Chorus.reachable_local_fastqc_pos_backed (r.reachable N) i0 j m ⟨hi0, hm⟩
          obtain ⟨k, hk, h⟩ := eventually_of_weaklyFairWhen
            (hfj (.aggregate_fastqc_pos i j m q) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h))
            (P := fun st => st.local_fastqc_pos i j m = true) (N := N)
            (fun n hn => Or.inr ⟨i0, hi0,
              r.mono (P := fun st => st.msg_commit_cast i0 = true)
                (fun k hk => Chorus.msg_commit_cast.mono (r.steps k) i0 hk) hcast0 n hn,
              r.mono (P := fun st => st.local_fastqc_pos i0 j m = true)
                (fun k hk => Chorus.local_fastqc_pos.mono (r.steps k) i0 j m hk) hm n hn⟩)
            (fun _ _ h => aggregate_fastqc_pos_effect h)
            (fun n hn hnot => enabled_aggregate_fastqc_pos hi hq (fun a ha =>
              r.mono (P := fun st => st.msg_vote_pos_sig a j m = true)
                (fun k hk => msg_vote_pos_sig_mono (r.steps k) a j m hk) (hqs a ha) n hn) hnot)
          exact ⟨k, hk, fun _ => Or.inl ⟨m, h⟩⟩
        · obtain ⟨q, hq, hqs⟩ := Chorus.reachable_local_fastqc_neg_backed (r.reachable N) i0 j ⟨hi0, hm⟩
          obtain ⟨k, hk, h⟩ := eventually_of_weaklyFairWhen
            (hfj (.aggregate_fastqc_neg i j q) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h))
            (P := fun st => st.local_fastqc_neg i j = true) (N := N)
            (fun n hn => Or.inr ⟨i0, hi0,
              r.mono (P := fun st => st.msg_commit_cast i0 = true)
                (fun k hk => Chorus.msg_commit_cast.mono (r.steps k) i0 hk) hcast0 n hn,
              r.mono (P := fun st => st.local_fastqc_neg i0 j = true)
                (fun k hk => Chorus.local_fastqc_neg.mono (r.steps k) i0 j hk) hm n hn⟩)
            (fun _ _ h => aggregate_fastqc_neg_effect h)
            (fun n hn hnot => enabled_aggregate_fastqc_neg hi hq (fun a ha =>
              r.mono (P := fun st => st.msg_vote_neg_sig a j = true)
                (fun k hk => msg_vote_neg_sig_mono (r.steps k) a j hk) (hqs a ha) n hn) hnot)
          exact ⟨k, hk, fun _ => Or.inr h⟩
      · exact ⟨N, Nat.le_refl _, fun h => absurd h hj⟩)
  refine ⟨M, hM, ?_⟩
  unfold Chorus.complete_fast_metablock
  exact fun j hj => hall j (hnodes j) hj

/-- **Every correct validator's proposal trigger eventually holds for
good, and is owed**, from an index at which the MVBA's trigger holds from
correct senders: a correct `FBCert` persists, and a correct fast voter's
meta-block spreads (`eventually_complete_fast_metablock`). -/
theorem eventually_trigger (r : CRun th)
    (hfj : PerLabel r)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) {N : Nat}
    (htrig : CorrectTrigger (nset := nset) (mvba := mvba) th (r.at' N))
    {i : node} (hi : ¬ nset.is_byz i = true) :
    ∃ M, ∀ n, M ≤ n → ProposeTrigger (nset := nset) (mvba := mvba) th (r.at' n) i ∧
      proposeOwed (nset := nset) (mvba := mvba) th i (r.at' n) := by
  obtain ⟨Nm, hNm⟩ := eventually_mvbaArm r hfj
  obtain ⟨Na, hNa⟩ := eventually_atArm r hfj
  rcases htrig with hfb | ⟨i0, hi0, hcast0, h0⟩
  · have hfb' := r.mono (P := fun st => CorrectFBCert st)
      (fun k hk => correctFBCert_step (r.steps k) hk) hfb
    exact ⟨max N Na, fun n hn => ⟨Or.inl
      ⟨fbcert_of_correct (hfb' n (by omega)), hNa n (by omega)⟩, Or.inl (hfb' n (by omega))⟩⟩
  · obtain ⟨M, -, hc⟩ := eventually_complete_fast_metablock r hfj nodes hnodes hi0 hcast0 h0 hi
    have hc' := r.mono (P := fun st => Chorus.complete_fast_metablock (nset := nset) (mvba := mvba) i th st)
      (fun k hk => complete_fast_metablock_step (r.steps k) hk) hc
    exact ⟨max M Nm, fun n hn => ⟨Or.inr ⟨hc' n (by omega), hNm n (by omega)⟩, Or.inr (hc' n (by omega))⟩⟩

/-- **A committed positive entry is assignable, at every point of every
run**: the first-flip step was `commit_assign_pos` (`committed_pos_flip`),
whose certificate guard is monotone (`assignable_pos_step`). -/
theorem committed_pos_assignable (r : CRun th) {i j : node} {m : merkle_root} :
    ∀ n, (r.at' n).local_committed_pos i j m = true →
      (r.at' n).msg_commitqc_pos j m = true ∨
        (Chorus.fbcommitqc th (r.at' n) ∧ (r.at' n).mvba_decided_pos j m = true)
  | 0, h => by simp [Chorus.local_committed_pos.init r.starts i j m] at h
  | n + 1, h => by
    by_cases h0 : (r.at' n).local_committed_pos i j m = true
    · exact assignable_pos_step (r.steps n) (committed_pos_assignable r n h0)
    · exact assignable_pos_step (r.steps n) (committed_pos_flip (r.steps n) h0 h)

/-- **A committed negative entry is assignable**, likewise. -/
theorem committed_neg_assignable (r : CRun th) {i j : node} :
    ∀ n, (r.at' n).local_committed_neg i j = true →
      (r.at' n).msg_commitqc_neg j = true ∨
        (Chorus.fbcommitqc th (r.at' n) ∧ (r.at' n).mvba_decided_neg j = true)
  | 0, h => by simp [Chorus.local_committed_neg.init r.starts i j] at h
  | n + 1, h => by
    by_cases h0 : (r.at' n).local_committed_neg i j = true
    · exact assignable_neg_step (r.steps n) (committed_neg_assignable r n h0)
    · exact assignable_neg_step (r.steps n) (committed_neg_flip (r.steps n) h0 h)

/-- **A commitment proof from correct senders makes the entry assignable**:
a correct validator's committed entry is (`committed_pos_assignable`), and a
correct fallback commit certificate is a fallback commit certificate. -/
theorem assignable_pos_of_proof (r : CRun th) (n : Nat) {j : node} {m : merkle_root}
    (h : ProofPos (nset := nset) (r.at' n) j m) :
    (r.at' n).msg_commitqc_pos j m = true ∨
      (Chorus.fbcommitqc (nset := nset) (mvba := mvba) th (r.at' n) ∧ (r.at' n).mvba_decided_pos j m = true) := by
  rcases h with ⟨k, -, -, hp⟩ | ⟨hq, hd⟩
  · exact committed_pos_assignable r n hp
  · exact Or.inr ⟨fbcommitqc_of_correct hq, hd⟩

theorem assignable_neg_of_proof (r : CRun th) (n : Nat) {j : node}
    (h : ProofNeg (nset := nset) (r.at' n) j) :
    (r.at' n).msg_commitqc_neg j = true ∨
      (Chorus.fbcommitqc (nset := nset) (mvba := mvba) th (r.at' n) ∧ (r.at' n).mvba_decided_neg j = true) := by
  rcases h with ⟨k, -, -, hp⟩ | ⟨hq, hd⟩
  · exact committed_neg_assignable r n hp
  · exact Or.inr ⟨fbcommitqc_of_correct hq, hd⟩

/-- **The commit route, from commitment proofs.** From an index at which
every proposer's entry has a commitment proof from correct senders
(`ProofPos`/`ProofNeg`: a correct validator's finalization, or the
fallback commit certificate from correct voters with the MVBA's decision),
every correct validator eventually has `local_committed`. Such a proof makes
the entry assignable, and assigning it is owed. No invariant, because
`commit_assign_*`'s consistency and fired-once guards hold for a validator
that has assigned nothing for the proposer.

The two premises about `i` are the claim's caller premises, read at `i`:
it participates at some point (`hpart`), and it has abandoned only once it
has finalized (`hab`). So as long as `i` has not finalized, it is actively
participating from its participation on, which is the gate
`commit_assign_*` and `finalize_commit` require. Nothing is assumed about
the other validators: this is what lets the early-finalization branch of
`termination` use it. -/
theorem eventually_committed_of_assignable (r : CRun th)
    (hfj : PerLabel r)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) {N : Nat}
    (hA : ∀ j, th.is_proposer j = true →
      (∃ m, ProofPos (nset := nset) (r.at' N) j m) ∨ ProofNeg (nset := nset) (r.at' N) j)
    {i : node} (hi : ¬ nset.is_byz i = true)
    (hpart : ∃ P, (r.at' P).participating i = true)
    (hab : ∀ n, (r.at' n).abandoned i = true → (r.at' n).local_committed i = true) :
    ∃ n, N ≤ n ∧ (r.at' n).local_committed i = true := by
  by_contra hcon
  have hnc : ∀ n, ¬ (r.at' n).local_committed i = true := by
    intro n hn
    by_cases hle : N ≤ n
    · exact hcon ⟨n, hle, hn⟩
    · exact hcon ⟨N, Nat.le_refl _, r.mono (P := fun st => st.local_committed i = true)
        (fun k hk => Chorus.local_committed.mono (r.steps k) i hk) hn N (by omega)⟩
  -- `i` never finalizes, so it never abandons: from its participation on it is active.
  obtain ⟨P, hP⟩ := hpart
  have hact : ∀ n, P ≤ n → Active (r.at' n) i := fun n hn =>
    ⟨r.mono (P := fun st => st.participating i = true)
        (fun k hk => Chorus.participating.mono (r.steps k) i hk) hP n hn,
     fun h => hnc n (hab n h)⟩
  -- The entry for `j` is assigned by `i`, positive or negative.
  have hE : ∀ j n, ((∃ m, (r.at' n).local_committed_pos i j m = true) ∨
        (r.at' n).local_committed_neg i j = true) →
      (∃ m, (r.at' (n + 1)).local_committed_pos i j m = true) ∨
        (r.at' (n + 1)).local_committed_neg i j = true := by
    intro j n h
    rcases h with ⟨m, hm⟩ | hm
    · exact Or.inl ⟨m, Chorus.local_committed_pos.mono (r.steps n) i j m hm⟩
    · exact Or.inr (Chorus.local_committed_neg.mono (r.steps n) i j hm)
  have hassign : ∀ j, th.is_proposer j = true → ∃ n, N ≤ n ∧
      ((∃ m, (r.at' n).local_committed_pos i j m = true) ∨ (r.at' n).local_committed_neg i j = true) := by
    intro j hj
    by_contra hna
    have hnp : ∀ n, N ≤ n → ∀ m', ¬ (r.at' n).local_committed_pos i j m' = true :=
      fun n hn m' h => hna ⟨n, hn, Or.inl ⟨m', h⟩⟩
    have hnn : ∀ n, N ≤ n → ¬ (r.at' n).local_committed_neg i j = true :=
      fun n hn h => hna ⟨n, hn, Or.inr h⟩
    rcases hA j hj with ⟨m, hm⟩ | hm
    · -- The positive entry's proof persists; it is owed, and it makes the
      -- entry assignable, so `commit_assign_pos` stays enabled.
      have hm' := r.mono (P := fun st => ProofPos (nset := nset) st j m)
        (fun k h => proofPos_step (r.steps k) h) hm
      obtain ⟨n, hn, hfire⟩ := (hfj (.commit_assign_pos i j m) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).fires
        (max N P) (fun n hn => hm' n (by omega))
        (fun n hn => (enabled_commit_assign_pos hi (hact n (by omega)) (hnc n) hj
          (assignable_pos_of_proof r n (hm' n (by omega)))
          (hnp n (by omega)) (hnn n (by omega))))
      exact hna ⟨n + 1, by omega, Or.inl ⟨m, commit_assign_pos_effect (hfire ▸ r.steps n)⟩⟩
    · have hm' := r.mono (P := fun st => ProofNeg (nset := nset) st j)
        (fun k h => proofNeg_step (r.steps k) h) hm
      obtain ⟨n, hn, hfire⟩ := (hfj (.commit_assign_neg i j) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).fires
        (max N P) (fun n hn => hm' n (by omega))
        (fun n hn => (enabled_commit_assign_neg hi (hact n (by omega)) (hnc n) hj
          (assignable_neg_of_proof r n (hm' n (by omega)))
          (hnp n (by omega)) (hnn n (by omega))))
      exact hna ⟨n + 1, by omega, Or.inr (commit_assign_neg_effect (hfire ▸ r.steps n))⟩
  -- Every proposer assigned at one index and ever after, so `finalize_commit` fires.
  obtain ⟨N2, -, hall2⟩ := r.eventually_forall
    (fun j st => th.is_proposer j = true →
      (∃ m, st.local_committed_pos i j m = true) ∨ st.local_committed_neg i j = true)
    (fun j n h hj => hE j n (h hj)) N nodes
    (fun j _ => by
      by_cases hj : th.is_proposer j = true
      · obtain ⟨n, hn, h⟩ := hassign j hj
        exact ⟨n, hn, fun _ => h⟩
      · exact ⟨N, Nat.le_refl _, fun h => absurd h hj⟩)
  have hall2' : ∀ n, N2 ≤ n → ∀ j, th.is_proposer j = true →
      (∃ m, (r.at' n).local_committed_pos i j m = true) ∨ (r.at' n).local_committed_neg i j = true :=
    r.mono (P := fun st => ∀ j, th.is_proposer j = true →
        (∃ m, st.local_committed_pos i j m = true) ∨ st.local_committed_neg i j = true)
      (fun k h j hj => hE j k (h j hj)) (fun j hj => hall2 j (hnodes j) hj)
  obtain ⟨n, -, hfire⟩ := (hfj (.finalize_commit i) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial) (max N2 P)
    (fun n hn => (enabled_finalize_commit hi (hact n (by omega)) (hnc n) (hall2' n (by omega))))
  exact hnc (n + 1) (finalize_commit_effect (hfire ▸ r.steps n))

/-- **Once a correct validator has finalized, every proposer's entry has a
commitment proof from a correct sender**: it committed an entry for every
proposer (`local_committed_complete`), and its finalization re-broadcast its
proof. -/
theorem proofs_of_finalized (r : CRun th) {n : Nat} {i0 : node}
    (hi0 : ¬ nset.is_byz i0 = true) (hc : (r.at' n).local_committed i0 = true) :
    ∀ j, th.is_proposer j = true →
      (∃ m, ProofPos (nset := nset) (r.at' n) j m) ∨ ProofNeg (nset := nset) (r.at' n) j := by
  intro j hj
  rcases Chorus.reachable_local_committed_complete (r.reachable n) i0 ⟨hi0, hc⟩ j hj with ⟨m, hm⟩ | hm
  · exact Or.inl ⟨m, Or.inl ⟨i0, hi0, hc, hm⟩⟩
  · exact Or.inr (Or.inl ⟨i0, hi0, hc, hm⟩)

/-- **Untimed totality: once one correct validator finalizes, every correct
validator does** — given only the two caller premises at the latter. Its
proofs are on the network (`proofs_of_finalized`), so the commit
route applies (`eventually_committed_of_assignable`). This is the
early-finalization branch of `termination`, and it needs none of the MVBA
premises. -/
theorem eventually_committed_of_finalized (r : CRun th)
    (hfj : PerLabel r)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) {n0 : Nat} {i0 : node}
    (hi0 : ¬ nset.is_byz i0 = true) (hc0 : (r.at' n0).local_committed i0 = true)
    {i : node} (hi : ¬ nset.is_byz i = true)
    (hpart : ∃ P, (r.at' P).participating i = true)
    (hab : ∀ n, (r.at' n).abandoned i = true → (r.at' n).local_committed i = true) :
    ∃ n, n0 ≤ n ∧ (r.at' n).local_committed i = true :=
  eventually_committed_of_assignable r hfj nodes hnodes (proofs_of_finalized r hi0 hc0) hi hpart hab

/-- **The gate from the caller premises, on the late branch.** If no correct
validator ever finalizes, none ever abandons (`hab`), and since every one
eventually participates (`hpart`), there is one index from which all are
active. `nodes` is the complete list that collapses the eventualities. -/
theorem activeFrom_of_never_finalized (r : CRun th)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes)
    (hpart : ∀ i, ¬ nset.is_byz i = true → ∃ P, (r.at' P).participating i = true)
    (hab : ∀ i, ¬ nset.is_byz i = true → ∀ n,
      (r.at' n).abandoned i = true → (r.at' n).local_committed i = true)
    (hnever : ∀ n i, ¬ nset.is_byz i = true → ¬ (r.at' n).local_committed i = true) :
    ∃ A, ActiveFrom r A := by
  obtain ⟨A, -, hA⟩ := r.eventually_forall
    (fun i st => ¬ nset.is_byz i = true → st.participating i = true)
    (fun i n h hi => Chorus.participating.mono (r.steps n) i (h hi)) 0 nodes
    (fun i _ => by
      by_cases hi : nset.is_byz i = true
      · exact ⟨0, Nat.le_refl 0, fun h => absurd hi h⟩
      · obtain ⟨P, hP⟩ := hpart i hi
        exact ⟨P, Nat.zero_le _, fun _ => hP⟩)
  exact ⟨A, fun n hn i hi =>
    ⟨r.mono (P := fun st => st.participating i = true)
        (fun k hk => Chorus.participating.mono (r.steps k) i hk) (hA i (hnodes i) hi) n hn,
     fun h => hnever n i hi (hab i hi n h)⟩⟩

end RunFacts

/-! ## The MVBA arm, at the system's MVBA

The dichotomy's right disjunct, over any run of Chorus at the `Mvba`
instance, generic in the quorum instance: [Liveness.md](../../docs/Liveness.md) §4.6's chain,
steps 2–5. The composed run's MVBA state is read through the projection of
[Liveness.lean](Liveness.lean) (`mvbaComponent`), and the MVBA's own termination theorem
is consumed as it stands. -/

section CertifiedVector

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

/-- **The meta-block the dichotomy's evidence certifies**: for each proposer
the root of a positive certificate on the network at `st`, where one exists,
and `⊥` otherwise. -/
noncomputable def certifiedVector
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)) :
    node → Option merkle_root := fun j =>
  if h : thS.is_proposer j = true ∧ ∃ m,
      Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS st ∨
      (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS st ∧
        Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS st)
  then some h.2.choose else none

end CertifiedVector

section MvbaArm

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  {nset : ByzNodeSet node nodeset} [vord : TotalOrderWithMinimum view]
  {cnt : Cadence.ByzNodeSetCounting node nodeset nset}
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (node → Option merkle_root) view}
  {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)}

/-- The `MVBASafety` instance the composed system runs, as a local instance
for the generic step lemmas. -/
local macro "mvba_inst" : tactic =>
  `(tactic| letI : MVBASafety node (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (fun i => nset.is_byz i = true) := Mvba.mvbaSafety thM)

set_option maxHeartbeats 1000000 in
/-- `mvba_step`'s guard, with both halves kept: the MVBA takes a transition
under a label that is not one of its two inputs. -/
theorem mvba_step_internal {mvba_next}
    (htr : (atMvba (nset := nset) thM).tr thS s (.mvba_step mvba_next) s') :
    ∃ l', ¬ Mvba.Label.isInput l' ∧
      (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
        s.mvba_st l' s'.mvba_st := by
  chorus_tr htr
  obtain ⟨hstep, htr⟩ := htr
  chorus_field_simp
  obtain ⟨l', hl, hl'⟩ := hstep
  subst htr
  exact ⟨l', hl, hl'⟩

/-- A predicate on MVBA states that every MVBA transition preserves is
preserved by every step of the composed run: the MVBA's state moves only by
its own transitions (`mvbaComponent`). -/
theorem mvba_st_step (r : ChorusRun (nset := nset) thS thM)
    (P : Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view) → Prop)
    (hP : ∀ st l st', (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root)
      (view := view)).tr thM st l st' → P st → P st')
    (n : Nat) (h : P (r.at' n).mvba_st) : P (r.at' (n + 1)).mvba_st := by
  by_cases hs : MvbaStepLabel (r.lbl n)
  · obtain ⟨l', hl'⟩ := (mvbaComponent thS thM).step _ _ _ (r.steps n) hs
    exact hP _ _ _ hl' h
  · have hf : (r.at' (n + 1)).mvba_st = (r.at' n).mvba_st :=
      (mvbaComponent thS thM).frame _ _ _ (r.steps n) hs
    exact hf ▸ h

omit [Inhabited merkle_root] in
set_option maxHeartbeats 1000000 in
/-- The MVBA's `abandon()` at `j` leaves every other party's `abandoned`
row alone. -/
theorem mvba_abandon_frame_other
    {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view)}
    {j i : node}
    (htr : (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      st (.abandon j) st')
    (hne : j ≠ i) : st'.abandoned i = st.abandoned i := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp] at htr
  subst htr
  chorus_field_simp
  all_goals simp [hne]

/-- **The MVBA's `abandoned` row moves only with Chorus's `abandon`**: a
party the composed run's MVBA has abandoned has invoked Chorus's
`abandon()`. The MVBA starts with nobody abandoned, `mvba_step` takes only
non-input transitions, `mvba_propose`'s input frames `abandoned`, and
Chorus's `abandon i` forwards to the MVBA's `abandon()` at `i` and nobody
else. This is how the caller's premise about Chorus's `abandon` becomes the
MVBA's `NoEarlyAbandon`. -/
theorem abandoned_of_mvba_abandoned (r : ChorusRun (nset := nset) thS thM) (i : node) :
    ∀ n, (r.at' n).mvba_st.abandoned i = true → (r.at' n).abandoned i = true
  | 0 => by
    obtain ⟨-, hinit⟩ := (mvbaComponent thS thM).init _ r.holds r.starts
    have h0 : (r.at' 0).mvba_st.abandoned i = false := Mvba.abandoned.init hinit i
    simp [h0]
  | n + 1 => by
    mvba_inst
    intro h
    by_cases hprev : (r.at' n).mvba_st.abandoned i = true
    · exact Chorus.abandoned.mono (r.steps n) i (abandoned_of_mvba_abandoned r i n hprev)
    by_cases hs : MvbaStepLabel (r.lbl n)
    · rcases (mvbaStepLabel_iff _).1 hs with ⟨m, hm⟩ | ⟨j, v, m, hm⟩ | ⟨j, m, hm⟩ | ⟨j, c, m, hm⟩
      · obtain ⟨l', hl', htr⟩ := mvba_step_internal (hm ▸ r.steps n)
        exact absurd ((Mvba.abandoned_frame_internal thM hl' htr i).1 h) hprev
      · have := Mvba.propose.frame_abandoned (mvba_propose_tr (hm ▸ r.steps n))
        rw [this] at h
        exact absurd h hprev
      · have htr := hm ▸ r.steps n
        by_cases hji : j = i
        · subst hji
          exact abandon_effect htr
        · rw [mvba_abandon_frame_other (abandon_tr htr) hji] at h
          exact absurd h hprev
      · obtain ⟨w, e, -, htr⟩ := accept_mvba_commitqc_tr (hm ▸ r.steps n)
        have := Mvba.decide.frame_abandoned htr
        rw [this] at h
        exact absurd h hprev
    · have hf : (r.at' (n + 1)).mvba_st = (r.at' n).mvba_st :=
        (mvbaComponent thS thM).frame _ _ _ (r.steps n) hs
      rw [hf] at h
      exact absurd h hprev

omit [Inhabited merkle_root] in
/-- The MVBA's `propose` input is enabled for a validator with no input yet,
not abandoned, proposing a valid value. -/
theorem enabled_propose_mvba
    {st : Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view)}
    {i : node} {v : node → Option merkle_root}
    (hin : ∀ E, ¬ st.input i E = true) (hab : ¬ st.abandoned i = true) (hv : thM.valid v = true) :
    ∃ st', (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      st (.propose i v) st' := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
  exact ⟨_, hin, hab, hv, rfl⟩

/-- A decision of the MVBA stands in the composed run. -/
theorem decided_persists (r : ChorusRun (nset := nset) thS thM) {i : node}
    {v : node → Option merkle_root} {k : Nat}
    (hd : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k).mvba_st i v) :
    ∀ n, k ≤ n → (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st i v :=
  r.mono (P := fun st => (Mvba.mvbaSafety (nset := nset) thM).decided st.mvba_st i v)
    (fun n h => mvba_st_step r _ (fun _ _ _ htr h => Mvba.decided_mono_tr thM htr i v h) n h) hd

/-- **A validator that has handed over a certificate has decided**, at every
point of the composed run: the step that set `local_mvba_qc_accepted i` was
its handoff, whose MVBA transition is `decide` (`qc_accepted_flip`), and
the decision persists. -/
theorem qc_accepted_decided (r : ChorusRun (nset := nset) thS thM) {i : node} :
    ∀ n, (r.at' n).local_mvba_qc_accepted i = true →
      ∃ v, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st i v
  | 0, h => by
    mvba_inst
    simp [Chorus.local_mvba_qc_accepted.init r.starts i] at h
  | n + 1, h => by
    mvba_inst
    by_cases h0 : (r.at' n).local_mvba_qc_accepted i = true
    · obtain ⟨v, hv⟩ := qc_accepted_decided r n h0
      exact ⟨v, decided_persists r hv (n + 1) (Nat.le_succ n)⟩
    · obtain ⟨c, hc⟩ := qc_accepted_flip (r.steps n) h0 h
      cases c
      all_goals first
        | exact (hc : False).elim
        | exact ⟨_, Mvba.decide_effect hc⟩

omit [Inhabited merkle_root] in
/-- `decide`'s guards, read off an enabled `decide`: a correct validator that
has not decided. -/
theorem decide_enabled_guards
    {st : Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view)}
    {i : node} {v : view} {e : node → Option merkle_root}
    (h : Enabled (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)) thM
      st (.decide i v e)) :
    ¬ nset.is_byz i = true ∧ ∀ E, ¬ st.decided i E = true := by
  obtain ⟨st', htr⟩ := h
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp] at htr
  obtain ⟨h1, -, -, -, h5, -⟩ := htr
  exact ⟨h1, h5⟩

/-- **(F-relay) is derived, not assumed**: on every projection of a run
satisfying `FJustice`, the MVBA's caller hands decided certificates on. If
`decide i v e` stayed enabled in the projected run while a correct
validator had decided `e`, the handoff would be owed to `i` from the
corresponding composed index on and enabled there (with the certificate on
`(v, e)`), so `FJustice`'s handoff family would fire, `i` would decide, and
`decide i v e` would be disabled after all. So the premise holds with its
antecedent false. -/
theorem fRelay_of_fJustice (r : ChorusRun (nset := nset) thS thM) (hfj : FJustice r)
    (p : (mvbaComponent thS thM).Projection r) : Mvba.FRelay p.run := by
  mvba_inst
  intro i v e K hen
  exfalso
  have hi := (decide_enabled_guards (hen K le_rfl).2).1
  -- Read the antecedent at the composed indices from `idx K` on.
  have htrans : ∀ n, (mvbaComponent thS thM).idx r K ≤ n →
      (∃ j, ¬ nset.is_byz j = true ∧ (r.at' n).mvba_st.decided j e = true) ∧
      Enabled (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)) thM
        (r.at' n).mvba_st (.decide i v e) := fun n hn => by
    have hk := hen ((mvbaComponent thS thM).cover r n) (p.scheduled.le_cover_of_idx_le hn)
    rw [← p.proj_eq_run_cover n] at hk
    exact hk
  obtain ⟨m, hm, c, mn, hl⟩ := (hfj.2.2 i).fires ((mvbaComponent thS thM).idx r K)
    (fun n hn => let ⟨j, hj, hd⟩ := (htrans n hn).1; ⟨j, e, hj, hd⟩)
    (fun n hn => by
      obtain ⟨st', htr'⟩ := (htrans n hn).2
      refine ⟨_, ⟨.commitqc v e, st', rfl⟩, enabled_accept_mvba_commitqc hi (fun hf => ?_) htr'⟩
      obtain ⟨w, hw⟩ := qc_accepted_decided r n hf
      exact (decide_enabled_guards (htrans n hn).2).2 w hw)
  obtain ⟨w, e', -, htr⟩ := accept_mvba_commitqc_tr (hl ▸ r.steps m)
  exact (decide_enabled_guards (htrans (m + 1) (by omega)).2).2 e' (Mvba.decide_effect htr)

/-- **The MVBA terminates inside the composed run**: `Mvba.termination`
applied to the run's MVBA projection. `MvbaAdmissible` supplies the
projection and its three scheduling premises; the caller's three premises are
given or derived: every correct validator proposes (`hall`); none has
invoked Chorus's `abandon()` (`hnab`), so none is abandoned in the MVBA
(`abandoned_of_mvba_abandoned`); and decided certificates are handed on
(`fRelay_of_fJustice`). -/
theorem all_decided_of_all_input [Fintype node] (hqe : Cadence.ByzNodeSetHonestQuorum node nodeset nset)
    (vfin : Cadence.ViewOrderEnum view vord)
    (r : ChorusRun (nset := nset) thS thM) (hcj : FJustice r) (hadm : MvbaAdmissible r)
    (hall : ∀ i, ¬ nset.is_byz i = true → ∃ n E, (r.at' n).mvba_st.input i E = true)
    (hnab : ∀ i, ¬ nset.is_byz i = true → ∀ n, ¬ (r.at' n).abandoned i = true) :
    ∀ i, ¬ nset.is_byz i = true → ∃ n v, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st i v := by
  obtain ⟨p, hfj, hav, hfa⟩ := hadm
  have hap : Mvba.AllPropose p.run := fun i hi => by
    obtain ⟨n, E, h⟩ := hall i hi
    refine ⟨(mvbaComponent thS thM).cover r n, E, ?_⟩
    rw [← p.proj_eq_run_cover n]
    exact h
  have hna : Mvba.NoEarlyAbandon p.run := fun i k hi h =>
    absurd (abandoned_of_mvba_abandoned r i _ h) (hnab i hi _)
  intro i hi
  obtain ⟨k, E, hk⟩ := Mvba.termination hqe vfin p.run hfj hav hfa hap hna
    (fRelay_of_fJustice r hcj p) i hi
  exact ⟨_, E, hk⟩

/-- The certified vector is `Certified` where the evidence is: every
proposer has a positive or a negative certificate. -/
theorem certified_certifiedVector
    (hmp : ∀ v j m, thS.mval_pos v j m = true ↔ v j = some m)
    (hmn : ∀ v j, thS.mval_neg v j = true ↔ v j = none ∧ thS.is_proposer j = true)
    (hev : ∀ j, thS.is_proposer j = true →
      (∃ m, Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS s ∨
        (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS s ∧
          Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s)) ∨
      (Chorus.vote_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS s ∨
        ((Chorus.fb_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS s ∨
          Chorus.equiv_evidence (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS s) ∧
          Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s))) :
    Certified (thS := thS) (thM := thM) s (certifiedVector thS thM s) := by
  refine ⟨fun J M hJ => ?_, fun J hJ => ?_, fun J hJ => ?_⟩
  · rw [hmp] at hJ
    unfold certifiedVector at hJ
    split at hJ
    · rename_i h
      cases Option.some.inj hJ
      exact ⟨h.1, h.2.choose_spec⟩
    · cases hJ
  · rw [hmn] at hJ
    obtain ⟨hnone, hpr⟩ := hJ
    unfold certifiedVector at hnone
    split at hnone
    · cases hnone
    · rename_i h
      refine ⟨hpr, ?_⟩
      rcases hev J hpr with hp | hn
      · exact absurd ⟨hpr, hp⟩ h
      · exact hn
  · by_cases h : ∃ m,
        Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∨
        (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∧
          Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s)
    · refine Or.inl ⟨h.choose, (hmp _ _ _).2 ?_⟩
      unfold certifiedVector
      rw [dif_pos ⟨hJ, h⟩]
    · refine Or.inr ((hmn _ _).2 ⟨?_, hJ⟩)
      unfold certifiedVector
      rw [dif_neg fun h' => h h'.2]

/-- Certification is monotone: every certificate in it is. -/
theorem Certified.step {l}
    (htr : (atMvba (nset := nset) (slot := slot) (Phase := Phase) (PathChoice := PathChoice) thM).tr thS s l s')
    {v : node → Option merkle_root}
    (h : Certified (thS := thS) (thM := thM) s v) : Certified (thS := thS) (thM := thM) s' v := by
  mvba_inst
  obtain ⟨hp, hn, ha⟩ := h
  refine ⟨fun J M hJ => ?_, fun J hJ => ?_, ha⟩
  · obtain ⟨hpr, hc⟩ := hp J M hJ
    exact ⟨hpr, hc.imp (vote_quorum_pos_step htr)
      fun ⟨a, b⟩ => ⟨fb_quorum_pos_step htr a, fbcert_step htr b⟩⟩
  · obtain ⟨hpr, hc⟩ := hn J hJ
    exact ⟨hpr, hc.imp (vote_quorum_neg_step htr)
      fun ⟨a, b⟩ => ⟨a.imp (fb_quorum_neg_step htr) (equiv_evidence_step htr), fbcert_step htr b⟩⟩

/-- **A correct validator whose trigger holds from correct senders and whose
vector is certified and `Valid` from some index on proposes**: `mvba_propose
i v` is then owed and enabled for some successor state until `i` has an
input, so the family fires (`FJustice`'s proposal clause). -/
theorem eventually_input (r : ChorusRun (nset := nset) thS thM)
    (hfam : ∀ i v, WeaklyFairFamilyWhen r (proposeOwed (nset := nset) (mvba := Mvba.mvbaSafety thM) thS i)
      (fun l => ∃ mvba_next, l = .mvba_propose i v mvba_next))
    {A : Nat} (hact : ActiveFrom r A)
    {i : node} (hi : ¬ nset.is_byz i = true) {v : node → Option merkle_root} {N : Nat}
    (htrig : ∀ n, N ≤ n → ProposeTrigger (nset := nset) (mvba := Mvba.mvbaSafety thM) thS (r.at' n) i ∧
      proposeOwed (nset := nset) (mvba := Mvba.mvbaSafety thM) thS i (r.at' n))
    (hcert : ∀ n, N ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) v)
    (hvalid : (Mvba.mvbaSafety (nset := nset) thM).Valid v) :
    ∃ n E, (r.at' n).mvba_st.input i E = true := by
  mvba_inst
  by_contra hcon
  have hno : ∀ n E, ¬ (r.at' n).mvba_st.input i E = true := fun n E h => hcon ⟨n, E, h⟩
  obtain ⟨k, -, m, hm⟩ := (hfam i v).fires (max N A) (fun n hn => (htrig n (by omega)).2) fun n hn => by
    have ha := hact n (by omega) i hi
    obtain ⟨st', hst'⟩ := enabled_propose_mvba (hno n)
      (fun h => ha.2 (abandoned_of_mvba_abandoned r i n h)) hvalid
    obtain ⟨h1, h2, h3⟩ := hcert n (by omega)
    exact ⟨_, ⟨st', rfl⟩, (enabled_mvba_propose hi ha (htrig n (by omega)).1 h1 h2 h3 hst')⟩
  exact hno (k + 1) v (Mvba.propose_effect_tr thM (mvba_propose_tr (hm ▸ r.steps k)))

/-- **A correct validator's decision record comes with its decision's
entry**, at every point of the composed run: the handler that set
`local_mvba_recorded i j` read a decision `v` of `i` and recorded entry `j`
of `v` (`mvba_recorded_flip`), and both persist. -/
theorem mvba_recorded_entry (r : ChorusRun (nset := nset) thS thM) {i j : node} :
    ∀ n, (r.at' n).local_mvba_recorded i j = true →
      ∃ v, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st i v ∧
        ((∃ M, thS.mval_pos v j M = true ∧ (r.at' n).mvba_decided_pos j M = true) ∨
          (thS.mval_neg v j = true ∧ (r.at' n).mvba_decided_neg j = true)) := by
  mvba_inst
  refine record_backed r (F := fun st => st.local_mvba_recorded i j = true)
    (Q := fun st => ∃ v, (Mvba.mvbaSafety (nset := nset) thM).decided st.mvba_st i v ∧
      ((∃ M, thS.mval_pos v j M = true ∧ st.mvba_decided_pos j M = true) ∨
        (thS.mval_neg v j = true ∧ st.mvba_decided_neg j = true)))
    (by simp [Chorus.local_mvba_recorded.init r.starts i j]) ?_ ?_
  · intro n h0 h1
    obtain ⟨v, hd, he⟩ := mvba_recorded_flip (r.steps n) h0 h1
    exact ⟨v, decided_persists r hd (n + 1) (Nat.le_succ n), he⟩
  · rintro n ⟨v, hd, he⟩
    refine ⟨v, decided_persists r hd (n + 1) (Nat.le_succ n), ?_⟩
    rcases he with ⟨M, hM, h⟩ | ⟨hM, h⟩
    · exact Or.inl ⟨M, hM, Chorus.mvba_decided_pos.mono (r.steps n) j M h⟩
    · exact Or.inr ⟨hM, Chorus.mvba_decided_neg.mono (r.steps n) j h⟩

set_option maxHeartbeats 1000000 in
/-- **The decision is transported.** From a correct validator's MVBA decision
`v`: every proposer's entry of `v` is recorded (`on_mvba_decide_pos/neg`,
whose bridge `require` is `ValidBridge`'s completeness clause), and then
`mvba_terminate` sets `mvba_complete`. From some index on both hold. A
handler's fired-once record can stand in the way only if `i` has already
recorded that entry of its decision, which by the MVBA's agreement is the
entry of `v` (`mvba_recorded_entry`). -/
theorem eventually_mvba_complete (r : ChorusRun (nset := nset) thS thM)
    (hfj : PerLabel r) (hbr : ValidBridge r)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) {N : Nat}
    (hinv : Chorus.mvba_invoked (nset := nset) (mvba := Mvba.mvbaSafety thM) thS (r.at' N))
    {i : node} (hi : ¬ nset.is_byz i = true) {k : Nat} {v : node → Option merkle_root}
    (hd : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k).mvba_st i v) :
    ∃ T, N ≤ T ∧ ∀ n, T ≤ n → (r.at' n).mvba_complete = true ∧ ∀ J, thS.is_proposer J = true →
      ((∃ M, thS.mval_pos v J M = true ∧ (r.at' n).mvba_decided_pos J M = true) ∨
        (thS.mval_neg v J = true ∧ (r.at' n).mvba_decided_neg J = true)) := by
  mvba_inst
  obtain ⟨Nm, hNm⟩ := eventually_mvbaArm r hfj
  have hdec := decided_persists r hd
  have hcert : ∀ n, k ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) v :=
    r.mono (P := fun st => Certified (thS := thS) (thM := thM) st v)
      (fun n h => h.step (r.steps n)) (hbr.2 k i v hi hd)
  have hinv' : ∀ n, N ≤ n → Chorus.mvba_invoked thS (r.at' n) :=
    r.mono (P := fun st => Chorus.mvba_invoked thS st) (fun n h => mvba_invoked_step (r.steps n) h) hinv
  -- Every proposer's entry of `v` is recorded, at one index and ever after.
  have hrec_step : ∀ J n, (thS.is_proposer J = true →
      ((∃ M, thS.mval_pos v J M = true ∧ (r.at' n).mvba_decided_pos J M = true) ∨
        (thS.mval_neg v J = true ∧ (r.at' n).mvba_decided_neg J = true))) →
      (thS.is_proposer J = true →
      ((∃ M, thS.mval_pos v J M = true ∧ (r.at' (n + 1)).mvba_decided_pos J M = true) ∨
        (thS.mval_neg v J = true ∧ (r.at' (n + 1)).mvba_decided_neg J = true))) := by
    intro J n h hJ
    rcases h hJ with ⟨M, hM, hd⟩ | ⟨hM, hd⟩
    · exact Or.inl ⟨M, hM, Chorus.mvba_decided_pos.mono (r.steps n) J M hd⟩
    · exact Or.inr ⟨hM, Chorus.mvba_decided_neg.mono (r.steps n) J hd⟩
  obtain ⟨Tr, hTr, hall⟩ := r.eventually_forall
    (fun J st => thS.is_proposer J = true →
      ((∃ M, thS.mval_pos v J M = true ∧ st.mvba_decided_pos J M = true) ∨
        (thS.mval_neg v J = true ∧ st.mvba_decided_neg J = true)))
    hrec_step (max k (max N Nm)) nodes
    (fun J _ => by
      by_cases hJ : thS.is_proposer J = true
      · obtain ⟨-, -, hent⟩ := hcert k (Nat.le_refl _)
        -- While entry `J` of `v` is unrecorded, `i` has recorded nothing for `J`.
        have hfresh : ∀ n, k ≤ n →
            ¬ ((∃ M, thS.mval_pos v J M = true ∧ (r.at' n).mvba_decided_pos J M = true) ∨
              (thS.mval_neg v J = true ∧ (r.at' n).mvba_decided_neg J = true)) →
            ¬ (r.at' n).local_mvba_recorded i J = true := by
          intro n hn hnr hf
          obtain ⟨v', hd', he'⟩ := mvba_recorded_entry r n hf
          obtain rfl : v' = v := (Mvba.mvbaSafety (nset := nset) thM).agreement _
            (Chorus.reachable_mvba_reachable (r.reachable n)) i i v' v hi hi hd' (hdec n hn)
          exact hnr he'
        rcases hent J hJ with ⟨M, hM⟩ | hM
        · obtain ⟨n, hn, h⟩ := eventually_of_weaklyFair
            ((hfj (.on_mvba_decide_pos i J M v) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial))
            (P := fun st => (∃ M, thS.mval_pos v J M = true ∧ st.mvba_decided_pos J M = true) ∨
              (thS.mval_neg v J = true ∧ st.mvba_decided_neg J = true)) (N := max k (max N Nm))
            (fun _ _ h => Or.inl ⟨M, hM, on_mvba_decide_pos_effect h⟩) (fun n hn hnr => by
              obtain ⟨hp, -, -⟩ := hcert n (by omega)
              exact enabled_on_mvba_decide_pos hi (hNm n (by omega)) hJ (hinv' n (by omega))
                (hdec n (by omega)) hM (hp J M hM).2 (hfresh n (by omega) hnr))
          exact ⟨n, hn, fun _ => h⟩
        · obtain ⟨n, hn, h⟩ := eventually_of_weaklyFair
            ((hfj (.on_mvba_decide_neg i J v) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial))
            (P := fun st => (∃ M, thS.mval_pos v J M = true ∧ st.mvba_decided_pos J M = true) ∨
              (thS.mval_neg v J = true ∧ st.mvba_decided_neg J = true)) (N := max k (max N Nm))
            (fun _ _ h => Or.inr ⟨hM, on_mvba_decide_neg_effect h⟩) (fun n hn hnr => by
              obtain ⟨-, hng, -⟩ := hcert n (by omega)
              exact enabled_on_mvba_decide_neg hi (hNm n (by omega)) hJ (hinv' n (by omega))
                (hdec n (by omega)) hM (hng J hM).2 (hfresh n (by omega) hnr))
          exact ⟨n, hn, fun _ => h⟩
      · exact ⟨max k (max N Nm), Nat.le_refl _, fun h => absurd h hJ⟩)
  have hrec : ∀ n, Tr ≤ n → ∀ J, thS.is_proposer J = true →
      ((∃ M, thS.mval_pos v J M = true ∧ (r.at' n).mvba_decided_pos J M = true) ∨
        (thS.mval_neg v J = true ∧ (r.at' n).mvba_decided_neg J = true)) :=
    r.mono (P := fun st => ∀ J, thS.is_proposer J = true →
        ((∃ M, thS.mval_pos v J M = true ∧ st.mvba_decided_pos J M = true) ∨
          (thS.mval_neg v J = true ∧ st.mvba_decided_neg J = true)))
      (fun n h J => hrec_step J n (h J)) (fun J hJ => hall J (hnodes J) hJ)
  -- So `mvba_terminate i v` stays enabled until `mvba_complete` holds.
  have hc : ∃ n, Tr ≤ n ∧ (r.at' n).mvba_complete = true := by
    by_contra hcon
    obtain ⟨n, hn, hfire⟩ := (hfj (.mvba_terminate i v) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial) Tr
      (fun n hn => (enabled_mvba_terminate hi (hNm n (by omega)) (fun h => hcon ⟨n, hn, h⟩)
        (hinv' n (by omega)) (hdec n (by omega)) (hrec n hn)))
    exact hcon ⟨n + 1, by omega, mvba_terminate_effect (hfire ▸ r.steps n)⟩
  obtain ⟨Tc, hTc, hc⟩ := hc
  exact ⟨Tc, by omega, fun n hn =>
    ⟨r.mono (P := fun st => st.mvba_complete = true)
      (fun m h => Chorus.mvba_complete.mono (r.steps m) h) hc n hn, hrec n (by omega)⟩⟩

set_option maxHeartbeats 1000000 in
/-- **Every correct validator casts its fallback commit vote**, once the
decision is transported and it has decided itself: its DA wait is met under
every decided-positive root, and no new decided root appears (the records
are unique per proposer), so `cast_fb_commit` stays enabled, and it is owed.

The wait is the paper's (Algorithm 5, line 38 (`line:fb-commit-foreach`)): a root is certificate-
backed (`mvba_decided_pos_backed`). Under a FastQC there is nothing to wait
for. Under a FallbackQC one of its `f+1` signers is correct and decoded the
proposal to sign, so it re-disseminates `i`'s chunk (Algorithm 5, line 12 (`line:fb-redisseminate`),
F8's disjunct of the owed-condition). -/
theorem eventually_fbcommit_sig (r : ChorusRun (nset := nset) thS thM)
    (hfj : PerLabel r)
    {A : Nat} (hact : ActiveFrom r A)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) {T : Nat} {v : node → Option merkle_root}
    (hT : ∀ n, T ≤ n → (r.at' n).mvba_complete = true ∧ ∀ J, thS.is_proposer J = true →
      ((∃ M, thS.mval_pos v J M = true ∧ (r.at' n).mvba_decided_pos J M = true) ∨
        (thS.mval_neg v J = true ∧ (r.at' n).mvba_decided_neg J = true)))
    {i : node} (hi : ¬ nset.is_byz i = true)
    (hdi : ∃ k w, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k).mvba_st i w) :
    ∃ n, (r.at' n).msg_fbcommit_sig i = true := by
  mvba_inst
  obtain ⟨Nm, hNm⟩ := eventually_mvbaArm r hfj
  have hreach := r.reachable T
  obtain ⟨kd, w, hdw⟩ := hdi
  -- The wait under every root decided positive at `T`: a FastQC, or `i`'s chunk.
  have hwait_step : ∀ J M n, Chorus.vote_quorum_pos J M thS (r.at' n) ∨
      (r.at' n).msg_chunk_received i J M = true →
      Chorus.vote_quorum_pos J M thS (r.at' (n + 1)) ∨
        (r.at' (n + 1)).msg_chunk_received i J M = true := fun J M n h =>
    h.imp (vote_quorum_pos_step (r.steps n)) (Chorus.msg_chunk_received.mono (r.steps n) i J M)
  obtain ⟨Nd, hNd, hall⟩ := r.eventually_forall
    (fun J st => thS.is_proposer J = true →
      ∀ M, (r.at' T).mvba_decided_pos J M = true →
        Chorus.vote_quorum_pos J M thS st ∨ st.msg_chunk_received i J M = true)
    (fun J n h hJ M hM => hwait_step J M n (h hJ M hM)) T nodes
    (fun J _ => by
      by_cases hJ : thS.is_proposer J = true
      · rcases (hT T (Nat.le_refl _)).2 J hJ with ⟨M0, -, hM0⟩ | ⟨-, hneg⟩
        · rcases Chorus.reachable_mvba_decided_pos_backed hreach J M0 hM0 with
            ⟨q, hq, hallq⟩ | ⟨⟨q, hq, hallq⟩, -⟩
          · -- A FastQC: no wait.
            refine ⟨T, Nat.le_refl _, fun _ M hM => ?_⟩
            obtain rfl := Chorus.reachable_mvba_decided_pos_unique hreach J M M0 ⟨hM, hM0⟩
            exact Or.inl ⟨q, hq, hallq⟩
          · -- A FallbackQC: its correct signer re-disseminates `i`'s chunk.
            obtain ⟨k, hkq, hk⟩ := ByzNodeSet.greater_than_third_one_honest q hq
            have hown : ∀ n, T ≤ n → (r.at' n).msg_fb_pos_sig k J M0 = true := fun n hn =>
              r.mono (P := fun st => st.msg_fb_pos_sig k J M0 = true)
                (fun m h => Chorus.msg_fb_pos_sig.mono (r.steps m) k J M0 h) (hallq k hkq) n hn
            obtain ⟨n, hn, h⟩ := eventually_of_weaklyFairWhen
              (hfj (.redisseminate_chunk k i J M0) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h))
              (P := fun st => st.msg_chunk_received i J M0 = true) (N := max T A)
              (fun n hn => hown n (by omega))
              (fun _ _ h => redisseminate_chunk_effect h)
              (fun n hn hnr => enabled_redisseminate_chunk hk (hact n (by omega) k hk) hJ
                (r.mono (P := fun st => st.msg_proposer_signed J M0 = true)
                  (fun m h => Chorus.msg_proposer_signed.mono (r.steps m) J M0 h)
                  (proposer_signed_of_decided_pos hreach hM0) n (by omega))
                (r.mono (P := fun st => Chorus.chunk_quorum J M0 thS st)
                  (fun m h => chunk_quorum_step (r.steps m) h)
                  (Chorus.reachable_mvba_decided_pos_chunks_decodable hreach J M0 hM0) n (by omega))
                fun hf => hnr (chunk_sent_received r n hf))
            refine ⟨n, by omega, fun _ M hM => ?_⟩
            obtain rfl := Chorus.reachable_mvba_decided_pos_unique hreach J M M0 ⟨hM, hM0⟩
            exact Or.inr h
        · exact ⟨T, Nat.le_refl _, fun _ M hM =>
            absurd ⟨hM, hneg⟩ (Chorus.reachable_mvba_decided_pos_neg_excl hreach J M)⟩
      · exact ⟨T, Nat.le_refl _, fun h => absurd h hJ⟩)
  -- The DA wait holds from then on: every root decided later was decided at `T`.
  have hda : ∀ n, max Nd Nm ≤ n → ∀ J M, thS.is_proposer J = true →
      (r.at' n).mvba_decided_pos J M = true →
        Chorus.vote_quorum_pos J M thS (r.at' n) ∨ (r.at' n).msg_chunk_received i J M = true := by
    intro n hn J M hJ hM
    rcases (hT T (Nat.le_refl _)).2 J hJ with ⟨M0, -, hM0⟩ | ⟨-, hneg⟩
    · have hM0n := r.mono (P := fun st => st.mvba_decided_pos J M0 = true)
        (fun m h => Chorus.mvba_decided_pos.mono (r.steps m) J M0 h) hM0 n (by omega)
      obtain rfl := Chorus.reachable_mvba_decided_pos_unique (r.reachable n) J M M0 ⟨hM, hM0n⟩
      exact r.mono (P := fun st => Chorus.vote_quorum_pos J M thS st ∨
          st.msg_chunk_received i J M = true)
        (fun m h => hwait_step J M m h) (hall J (hnodes J) hJ M hM0) n (by omega)
    · have hnegn := r.mono (P := fun st => st.mvba_decided_neg J = true)
        (fun m h => Chorus.mvba_decided_neg.mono (r.steps m) J h) hneg n (by omega)
      exact absurd ⟨hM, hnegn⟩ (Chorus.reachable_mvba_decided_pos_neg_excl (r.reachable n) J M)
  obtain ⟨n, -, h⟩ := eventually_of_weaklyFairWhen
    (hfj (.cast_fb_commit i) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h))
    (P := fun st => st.msg_fbcommit_sig i = true) (N := max (max A kd) (max Nd Nm))
    (fun n hn => ⟨w, decided_persists r hdw n (by omega)⟩)
    (fun _ _ h => cast_fb_commit_effect h)
    (fun n hn hnv => enabled_cast_fb_commit hi (hact n (by omega) i hi) (hNm n (by omega)) (hT n (by omega)).1
      (hda n (by omega)) fun hf => hnv (fbcommit_voted_sig r n hf))
  exact ⟨n, h⟩

/-- **The fallback commit certificate forms, from correct voters**: an honest
quorum's fallback commit votes are all on the network at one index. -/
theorem eventually_fbcommitqc (r : ChorusRun (nset := nset) thS thM)
    (hfj : PerLabel r)
    {A : Nat} (hact : ActiveFrom r A)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) {T : Nat} {v : node → Option merkle_root}
    (hT : ∀ n, T ≤ n → (r.at' n).mvba_complete = true ∧ ∀ J, thS.is_proposer J = true →
      ((∃ M, thS.mval_pos v J M = true ∧ (r.at' n).mvba_decided_pos J M = true) ∨
        (thS.mval_neg v J = true ∧ (r.at' n).mvba_decided_neg J = true)))
    {qv : nodeset} (hqv : nset.supermajority qv)
    (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true)
    (hdec : ∀ a, ¬ nset.is_byz a = true →
      ∃ k w, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k).mvba_st a w) :
    ∃ n, T ≤ n ∧ CorrectFbCommitQC (r.at' n) := by
  mvba_inst
  obtain ⟨F, hF, hall⟩ := r.eventually_forall
    (fun a st => nset.member a qv = true → st.msg_fbcommit_sig a = true)
    (fun a n h hm => Chorus.msg_fbcommit_sig.mono (r.steps n) a (h hm)) T nodes
    (fun a _ => by
      by_cases hm : nset.member a qv = true
      · obtain ⟨n, hn⟩ := eventually_fbcommit_sig r hfj hact nodes hnodes hT (hqvh a hm)
          (hdec a (hqvh a hm))
        exact ⟨max T n, by omega, fun _ => r.mono (P := fun st => st.msg_fbcommit_sig a = true)
          (fun m h => Chorus.msg_fbcommit_sig.mono (r.steps m) a h) hn _ (by omega)⟩
      · exact ⟨T, Nat.le_refl _, fun h => absurd h hm⟩)
  exact ⟨F, hF, qv, hqv, hqvh, fun a ha => hall a (hnodes a) ha⟩

set_option maxHeartbeats 1000000 in
/-- **The MVBA arm finalizes** — generic in the quorum instance, at the
system's MVBA. From an index at which the MVBA's trigger holds from correct
senders (`CorrectTrigger`) and every proposer has a positive or a negative
certificate, every correct validator eventually has `local_committed`.

`hmp`/`hmn` say that the theory reads a vector entrywise, `some m` or a
proposer's `none`, which is what `Cadence.chorusTheory` does. -/
theorem eventually_committed_of_mvba_arm [Fintype node]
    (hqe : Cadence.ByzNodeSetHonestQuorum node nodeset nset) (vfin : Cadence.ViewOrderEnum view vord)
    (hmp : ∀ v j m, thS.mval_pos v j m = true ↔ v j = some m)
    (hmn : ∀ v j, thS.mval_neg v j = true ↔ v j = none ∧ thS.is_proposer j = true)
    (r : ChorusRun (nset := nset) thS thM)
    (hfj : FJustice r) (hadm : MvbaAdmissible r) (hbr : ValidBridge r)
    {A : Nat} (hact : ActiveFrom r A)
    (hab : ∀ i, ¬ nset.is_byz i = true → ∀ n,
      (r.at' n).abandoned i = true → (r.at' n).local_committed i = true)
    (hnab : ∀ i, ¬ nset.is_byz i = true → ∀ n, ¬ (r.at' n).abandoned i = true) {N : Nat}
    (htrig : CorrectTrigger (nset := nset) (mvba := Mvba.mvbaSafety thM) thS (r.at' N))
    (hev : ∀ j, thS.is_proposer j = true →
      (∃ m, Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS (r.at' N) ∨
        (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS (r.at' N) ∧
          Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS (r.at' N))) ∨
      (Chorus.vote_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS (r.at' N) ∨
        ((Chorus.fb_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS (r.at' N) ∨
          Chorus.equiv_evidence (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS (r.at' N)) ∧
          Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS (r.at' N))))
    {i : node} (hi : ¬ nset.is_byz i = true) :
    ∃ n, N ≤ n ∧ (r.at' n).local_committed i = true := by
  have hnodes : ∀ a, a ∈ (Finset.univ : Finset node).toList := fun a => by simp
  -- One certified vector for everybody, from the evidence at `N`; `Valid` by the bridge.
  have hcert : ∀ n, N ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) (certifiedVector thS thM (r.at' N)) :=
    r.mono (P := fun st => Certified (thS := thS) (thM := thM) st (certifiedVector thS thM (r.at' N)))
      (fun n h => h.step (r.steps n)) (certified_certifiedVector hmp hmn hev)
  have hvalid := hbr.1 N _ (hcert N (Nat.le_refl _))
  -- Every correct validator proposes it (or something else first).
  have hall : ∀ i, ¬ nset.is_byz i = true → ∃ n E, (r.at' n).mvba_st.input i E = true := by
    intro i hi
    obtain ⟨M, hM⟩ := eventually_trigger r hfj.1 _ hnodes htrig hi
    exact eventually_input r hfj.2.1 hact hi (N := max M N) (fun n hn => hM n (by omega))
      (fun n hn => hcert n (by omega)) hvalid
  -- So the MVBA terminates: every correct validator decides.
  have hdec := all_decided_of_all_input hqe vfin r hfj hadm hall hnab
  obtain ⟨i0, -, hi0⟩ := ByzNodeSet.greater_than_third_one_honest hqe.honestQuorum
    (ByzNodeSet.supermajority_greater_than_third _ hqe.honestQuorum_supermajority)
  obtain ⟨k0, v0, hd0⟩ := hdec i0 hi0
  -- The decision is transported, the fallback commit certificate forms, and the entries are assignable.
  obtain ⟨T, hNT, hT⟩ := eventually_mvba_complete r hfj.1 hbr _ hnodes
    (by mvba_inst; exact mvba_invoked_of_correct htrig) hi0 hd0
  obtain ⟨F, hTF, hq⟩ := eventually_fbcommitqc r hfj.1 hact _ hnodes hT hqe.honestQuorum_supermajority
    hqe.honestQuorum_correct hdec
  obtain ⟨n, hn, h⟩ := eventually_committed_of_assignable r hfj.1 _ hnodes (N := F)
    (fun j hj => by
      rcases (hT F hTF).2 j hj with ⟨M, -, hM⟩ | ⟨-, hM⟩
      · exact Or.inl ⟨M, Or.inr ⟨hq, hM⟩⟩
      · exact Or.inr (Or.inr ⟨hq, hM⟩)) hi ⟨A, (hact A (Nat.le_refl _) i hi).1⟩ (hab i hi)
  exact ⟨n, by omega, h⟩

end MvbaArm

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
saturated, and stays so** — from (F-justice) and the gate: every correct
validator actively participating from some index on. The conclusion is, per
index, `progress_dichotomy_of_saturation`'s `hsat` hypothesis. -/
theorem saturation_fin (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thS thM)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    {A : Nat} (hact : ActiveFrom r A) :
    ∃ N, ∀ k, N ≤ k → ∀ i : Fin n, ¬ is_byz i → Saturated thS (r.at' k) i := by
  obtain ⟨H, hH, hHh⟩ := honest_quorum_fin n f hf is_byz hbyz
  obtain ⟨N, hN⟩ := eventually_all_saturated r hfj.1 hact (List.ofFn (n := n) id) (by simp) hH hHh
  exact ⟨N, fun k hk i hi => hN k hk i (by simpa +instances [byzNodeSetFin] using hi)⟩

set_option maxHeartbeats 1600000 in
/-- **The progress dichotomy holds in every run satisfying (F-justice) in
which every correct validator is active from some index on**: the
saturation theorem discharges `progress_dichotomy_of_saturation`'s `hsat` at
a reachable index. The late branch of `termination` no longer splits on it:
`eventually_mvba_route` below always reaches the MVBA arm, from correct
senders. -/
theorem eventually_progress_dichotomy (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thS thM)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    {A : Nat} (hact : ActiveFrom r A) :
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
  obtain ⟨N, hN⟩ := saturation_fin n f hf is_byz hbyz r hfj hact
  exact ⟨N, progress_dichotomy_of_saturation
    (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM) n f hf is_byz hbyz
    (r.reachable N) (fun i hi => hN N (Nat.le_refl N) i hi)⟩

omit node_inhabited cnt in
/-- The honest population as the instance `Mvba.termination` consumes: the
quorum of `honest_quorum_fin`, at `byzNodeSetFin`. -/
@[implicit_reducible]
noncomputable def byzNodeSetFin_honest :
    Cadence.ByzNodeSetHonestQuorum (Fin n) (ByzNSet n) (byzNodeSetFin n f hf is_byz hbyz) where
  honestQuorum := (honest_quorum_fin n f hf is_byz hbyz).choose
  honestQuorum_supermajority := (honest_quorum_fin n f hf is_byz hbyz).choose_spec.1
  honestQuorum_correct := (honest_quorum_fin n f hf is_byz hbyz).choose_spec.2

variable {is_proposer : Fin n → Bool} {well_encoded : merkle_root → Bool}
  {mvba_init_state : Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (Fin n → Option merkle_root) view)}

/-- The Chorus configuration at the system's instantiation. -/
local notation "thC" => Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
  is_proposer well_encoded mvba_init_state

set_option maxHeartbeats 1600000 in
/-- **The MVBA route is always open, from correct senders.** In every run
satisfying (F-justice) in which every correct validator is active from some
index on, there is an index at which the MVBA's trigger holds from correct
senders and every proposer has a certificate in the proposals' form. At
saturation either some correct validator cast its fast commit vote — then
it holds a complete fast meta-block (its commit signatures come from its
FastQCs) and broadcast it — or none did, and every correct validator cast
its fallback vote, so the correct population is an `FBCert`. The evidence is
`mvba_evidence_of_saturation`. -/
theorem eventually_mvba_route (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thS thM)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    {A : Nat} (hact : ActiveFrom r A) :
    ∃ N,
    CorrectTrigger (nset := byzNodeSetFin n f hf is_byz hbyz)
      (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM) thS (r.at' N) ∧
      ∀ j : Fin n, thS.is_proposer j = true →
        ((∃ m, (cpvm% Chorus.vote_quorum_pos j m thS (r.at' N)) ∨
               ((cpvm% Chorus.fb_quorum_pos j m thS (r.at' N)) ∧ (cpvm% Chorus.fbcert thS (r.at' N)))) ∨
         ((cpvm% Chorus.vote_quorum_neg j thS (r.at' N)) ∨
          (((cpvm% Chorus.fb_quorum_neg j thS (r.at' N)) ∨ (cpvm% Chorus.equiv_evidence j thS (r.at' N))) ∧
           (cpvm% Chorus.fbcert thS (r.at' N))))) := by
  obtain ⟨N, hN⟩ := saturation_fin n f hf is_byz hbyz r hfj hact
  refine ⟨N, ?_, mvba_evidence_of_saturation
    (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM) n f hf is_byz hbyz
    (r.reachable N) (fun i hi => hN N (Nat.le_refl N) i hi)⟩
  by_cases hexfast : ∃ i0, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i0 = true ∧
      (r.at' N).msg_commit_cast i0 = true
  · obtain ⟨i0, hi0, hcast⟩ := hexfast
    refine Or.inr ⟨i0, hi0, hcast, ?_⟩
    unfold Chorus.complete_fast_metablock
    intro j hj
    rcases commit_cast_sigs r hi0 N hcast j hj with ⟨m, hp⟩ | hn
    · exact Or.inl ⟨m, Chorus.reachable_commit_pos_sig_from_local_fastqc
        (nset := byzNodeSetFin n f hf is_byz hbyz)
        (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM)
        (r.reachable N) i0 j m ⟨hi0, hp⟩⟩
    · exact Or.inr (Chorus.reachable_commit_neg_sig_from_local_fastqc
        (nset := byzNodeSetFin n f hf is_byz hbyz)
        (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM)
        (r.reachable N) i0 j ⟨hi0, hn⟩)
  · push Not at hexfast
    obtain ⟨H, hH, hHh⟩ := honest_quorum_fin n f hf is_byz hbyz
    refine Or.inl ⟨H, hH, hHh, fun a ha => ?_⟩
    have ha' : ¬ is_byz a := fun hb => hHh a ha (by simpa +instances [byzNodeSetFin] using hb)
    rcases hN N (Nat.le_refl N) a ha' with ⟨hc, -⟩ | ⟨hfb, -⟩
    · exact absurd hc (hexfast a (hHh a ha))
    · exact hfb

set_option maxHeartbeats 1600000 in
/-- **Stage 4: the MVBA arm finalizes.** From an index at which the MVBA's
trigger holds from correct senders and every proposer has a positive or a
negative certificate (`eventually_mvba_route`), every correct
validator eventually has `local_committed` — at the system's configuration
`Cadence.chorusTheory`, from the three premises of `TerminationClaim` about
scheduling and the MVBA seam, the gate, and the fact that no correct
validator ever abandons (which holds on the branch this is used on).

`vfin` is the view order's enumeration, which `Mvba.termination` takes;
the finiteness of the validators is `Fin n`'s. -/
theorem mvba_arm_fin (vfin : Cadence.ViewOrderEnum view vord)
    (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thC thM)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hadm : MvbaAdmissible (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hbr : ValidBridge (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    {A : Nat} (hact : ActiveFrom r A)
    (hab : NoAbandonBeforeFinalizing (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hnab : ∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true → ∀ k,
      ¬ (r.at' k).abandoned i = true) {N : Nat}
    (hright : CorrectTrigger (nset := byzNodeSetFin n f hf is_byz hbyz)
      (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM) thC (r.at' N) ∧
      ∀ j : Fin n, (thC).is_proposer j = true →
        ((∃ m, (cpvm% Chorus.vote_quorum_pos j m thC (r.at' N)) ∨
               ((cpvm% Chorus.fb_quorum_pos j m thC (r.at' N)) ∧ (cpvm% Chorus.fbcert thC (r.at' N)))) ∨
         ((cpvm% Chorus.vote_quorum_neg j thC (r.at' N)) ∨
          (((cpvm% Chorus.fb_quorum_neg j thC (r.at' N)) ∨ (cpvm% Chorus.equiv_evidence j thC (r.at' N))) ∧
           (cpvm% Chorus.fbcert thC (r.at' N)))))) :
    ∀ i : Fin n, ¬ is_byz i → ∃ k, N ≤ k ∧ (r.at' k).local_committed i = true :=
  fun _ hi => eventually_committed_of_mvba_arm (byzNodeSetFin_honest n f hf is_byz hbyz) vfin
    (fun _ _ _ => decide_eq_true_iff) (fun _ _ => decide_eq_true_iff) r hfj hadm hbr hact hab hnab
    hright.1 hright.2
    (by simpa +instances [byzNodeSetFin] using hi)

set_option maxHeartbeats 1600000 in
/-- The MVBA arm in the claim's own vocabulary: if the MVBA route is open
from correct senders, the run `Terminates`. -/
theorem terminates_of_mvba_arm (vfin : Cadence.ViewOrderEnum view vord)
    (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thC thM)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hadm : MvbaAdmissible (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hbr : ValidBridge (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    {A : Nat} (hact : ActiveFrom r A)
    (hab : NoAbandonBeforeFinalizing (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hnab : ∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true → ∀ k,
      ¬ (r.at' k).abandoned i = true) {N : Nat}
    (hright : CorrectTrigger (nset := byzNodeSetFin n f hf is_byz hbyz)
      (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM) thC (r.at' N) ∧
      ∀ j : Fin n, (thC).is_proposer j = true →
        ((∃ m, (cpvm% Chorus.vote_quorum_pos j m thC (r.at' N)) ∨
               ((cpvm% Chorus.fb_quorum_pos j m thC (r.at' N)) ∧ (cpvm% Chorus.fbcert thC (r.at' N)))) ∨
         ((cpvm% Chorus.vote_quorum_neg j thC (r.at' N)) ∨
          (((cpvm% Chorus.fb_quorum_neg j thC (r.at' N)) ∨ (cpvm% Chorus.equiv_evidence j thC (r.at' N))) ∧
           (cpvm% Chorus.fbcert thC (r.at' N)))))) :
    Terminates (nset := byzNodeSetFin n f hf is_byz hbyz) r := by
  intro i hi
  obtain ⟨k, -, hk⟩ := mvba_arm_fin n f hf is_byz hbyz vfin r hfj hadm hbr hact hab hnab hright i
    (fun hb => hi (by simpa +instances [byzNodeSetFin] using hb))
  exact ⟨k, hk⟩

omit cnt in
set_option maxHeartbeats 1600000 in
/-- **Stage 5: Chorus terminates.** [Liveness.lean](Liveness.lean)'s `TerminationClaim`, proven:
at every `n = 3f+1` with at most `f` Byzantine validators, at the system's
configuration `Cadence.chorusTheory`, every run satisfying `FJustice`,
`MvbaAdmissible`, `ValidBridge`, `AllParticipate` and
`NoAbandonBeforeFinalizing` `Terminates` — every correct validator
finalizes the slot.

The proof splits on an early finalization, as the paper's does
(Lemma 11 (`lemma:chorus-termination`)):

* **some correct validator finalizes.** Its certificates are on the
  network, so every other correct validator finalizes through the commit
  route (`eventually_committed_of_finalized`), needing only the two caller
  premises at itself. This branch is the untimed totality.
* **no correct validator ever finalizes.** Then none ever abandons
  (`NoAbandonBeforeFinalizing`), so from some index every correct validator
  is actively participating (`activeFrom_of_never_finalized`), and the MVBA
  route is open from correct senders (`eventually_mvba_route`): the MVBA
  arm finalizes everyone. The MVBA's premise that nobody is abandoned before
  deciding holds because nobody abandons at all. (Until R8 this branch
  split on the progress dichotomy and took the commit route on its left
  disjunct, whose commit certificates may rest on Byzantine votes that
  nobody correct is owed; the MVBA arm needs no such split.)

The split on the dichotomy alone no longer suffices, because a validator
that finalizes on the fast path may then abandon, which also abandons the
MVBA. `vfin`, the view order's enumeration, is the one further hypothesis,
and like `Mvba.termination`'s it belongs to the proof, not to the claim.
The quorum counting facts are the concrete family's own instance
(`Cadence.byzNodeSetFin_counting`), not a hypothesis. -/
theorem termination (vfin : Cadence.ViewOrderEnum view vord) :
    TerminationClaim (nset := byzNodeSetFin n f hf is_byz hbyz)
      (cnt := Cadence.byzNodeSetFin_counting n f hf is_byz hbyz) (thC) thM := by
  intro r hfj hadm hbr hpart hab
  have hnodes : ∀ a, a ∈ List.ofFn (n := n) id := by simp
  by_cases hearly : ∃ k i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true ∧
      (r.at' k).local_committed i = true
  · obtain ⟨k0, i0, hi0, hc0⟩ := hearly
    intro i hi
    obtain ⟨k, -, hk⟩ := eventually_committed_of_finalized r hfj.1 _ hnodes hi0 hc0 hi
      (hpart i hi) (hab i hi)
    exact ⟨k, hk⟩
  · have hnever : ∀ k i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true →
        ¬ (r.at' k).local_committed i = true := fun k i hi hc => hearly ⟨k, i, hi, hc⟩
    have hnab : ∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true → ∀ k,
        ¬ (r.at' k).abandoned i = true := fun i hi k h => hnever k i hi (hab i hi k h)
    obtain ⟨A, hact⟩ := activeFrom_of_never_finalized r _ hnodes hpart hab hnever
    obtain ⟨N, hright⟩ := eventually_mvba_route n f hf is_byz hbyz r hfj hact
    exact terminates_of_mvba_arm n f hf is_byz hbyz vfin r hfj hadm hbr hact hab hnab hright

end Concrete

end Chorus

/-! ## The pinned trust base

The standard Lean trio and nothing else — no `sorryAx`. The claim itself
(`Chorus.termination`), the stage-3 and stage-4 theorems at the concrete
family, their generic cores, the three
hand-proven monotonicity lemmas, and the run-level facts derived in place of
new invariants. The reachability they use comes from the proof-file family
through [Certify.lean](Certify.lean), the dichotomy from [Progress.lean](Progress.lean),
and the MVBA's termination from [Mvba/Liveness.lean](../Mvba/Liveness.lean), each pinned there. -/

/--
info: 'Chorus.termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.termination

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
info: 'Chorus.eventually_all_saturated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_all_saturated

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

/--
info: 'Chorus.eventually_mvba_route' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_mvba_route

/--
info: 'Chorus.fRelay_of_fJustice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fRelay_of_fJustice

/--
info: 'Chorus.mvba_arm_fin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.mvba_arm_fin

/--
info: 'Chorus.terminates_of_mvba_arm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.terminates_of_mvba_arm

/--
info: 'Chorus.eventually_committed_of_mvba_arm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_committed_of_mvba_arm

/--
info: 'Chorus.eventually_committed_of_assignable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_committed_of_assignable

/--
info: 'Chorus.eventually_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_input

/--
info: 'Chorus.eventually_mvba_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_mvba_complete

/--
info: 'Chorus.eventually_fbcommit_sig' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_fbcommit_sig

/--
info: 'Chorus.certified_certifiedVector' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.certified_certifiedVector

/--
info: 'Chorus.abandoned_of_mvba_abandoned' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.abandoned_of_mvba_abandoned

/--
info: 'Chorus.eventually_committed_of_finalized' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.eventually_committed_of_finalized

/--
info: 'Chorus.activeFrom_of_never_finalized' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.activeFrom_of_never_finalized

/--
info: 'Chorus.committed_pos_assignable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.committed_pos_assignable

/--
info: 'Chorus.committed_neg_assignable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.committed_neg_assignable

/--
info: 'Chorus.proposer_signed_of_decided_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.proposer_signed_of_decided_pos

/--
info: 'Chorus.byzNodeSetFin_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.byzNodeSetFin_honest
