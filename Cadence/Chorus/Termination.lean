import Cadence.Chorus.Liveness
import Cadence.Chorus.Progress
import Cadence.System

/-! # Chorus/Termination — the run-level proof of Chorus's termination claim

[Liveness.md](../../docs/Liveness.md) §4.4–§4.7, against the
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
decider's commit certificate for the handoff, a correct collector's fallback
commit certificate, a correct finalizer's re-broadcast commitment proof.

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

The late branch does not split on the dichotomy. Its left disjunct's commit
certificates may rest on Byzantine commit votes that nobody correct is
owed, while the MVBA route is open at every saturated state.

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
decided certificates are handed on, `fRelay_of_fJustice`: a correct
decider sends its certificate, `send_mvba_cert`, and the receiver takes it,
`accept_mvba_commitqc`); every correct validator's decision is handled by
its decision handlers (the bridge's completeness clause) and completed by
its own `mvba_terminate`; every correct validator's own chunks have been
sent and it casts its fallback commit vote over its decided entries, which
agree; a correct collector sends the fallback commit certificate over them
(`broadcast_fbcommitqc`); and that certificate, from a correct sender, is a
commitment proof for every proposer's entry, the commit route's hypothesis
(`eventually_committed_of_assignable`). Stage 5 is the case split above:
`Chorus.termination`.

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
   old values. Each dispatch handles the actions that write the field by
   hand and closes every other one with its generated `frame_<field>` lemma
   (`frame_rest`), which exists only for an action that does not write the
   field, so a forgotten writer is an error.
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

Stage 3 uses these invariants: `voted_implies_cast`, to put a correct
voter's vote on the network, `vote_cast_valid`, for the vote to pass the
receiver's check and carry an entry for every proposer, `vote_pos_sig_chunk`,
`vote_pos_from_local` and `local_entry_pos_signed`, for a correct positive
entry to carry its chunk under a signed root, and `vote_rcv_pos_backed`, for a received
positive entry to be the sender's signature. The two facts [Liveness.md](../../docs/Liveness.md) §4.4 flags as outside the sweep —
a correct validator's fast commit vote, resp. fallback vote, carries a
signature per proposer — are **derived** here at run level from the
first-flip step (`commit_cast_sigs`, `fallback_sig_sigs`), not added to
the model. So is the fact the early-finalization branch needs, that a
correct validator's committed entry comes with the commitment proof it
re-broadcast under its own name (`committed_pos_cert`,
`committed_neg_cert`). The commit route needs no invariant at all (see
`eventually_committed_of_assignable`). Stage 4 reads existing invariants at
reachable states: the FastQC backing (`local_fastqc_*_backed`, for a
complete fast meta-block to spread), a correct validator's complete
commitment (`local_committed_complete`), and the validity of a broadcast
fallback commit certificate (`msg_fbcommitqc_backed`), whose correct signer
pins its entries to the decided ones (`fbcommit_sig_decided`). No cell is
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

open Lean Elab Tactic in
/-- Close every goal a `cases` on a Chorus label has left with that action's
generated frame lemma for the field `fld`, `Chorus.<action>.frame_<fld>`,
introduced as `hfr`, then `tac`. Veil generates a frame lemma exactly for
the actions that do not write the field, so a writer left to this tactic is
an unknown-identifier error, never a silent gap. -/
elab "frame_rest " htr:ident fld:ident hfr:ident " => " tac:tactic : tactic => do
  let mut rest : List MVarId := []
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let act := (← g.getTag).eraseMacroScopes.components.getLast!
    let lem := mkIdent (`Chorus ++ act ++ Name.mkSimple ("frame_" ++ fld.getId.toString))
    setGoals [g]
    evalTactic (← `(tactic| (have $hfr := $lem:ident $htr; $tac)))
    rest := rest ++ (← getGoals)
  setGoals rest

/-! ## Step facts

Everything a single transition says that the chains below need, generic in
the sorts, the quorum instance and the MVBA. -/

section Steps

open Classical

variable {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited mstate] [Inhabited mvalue] [Inhabited mentries] [Inhabited mmsg]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [mvba : MVBASafety node mvalue mentries mmsg mstate nodeset nset (fun i => nset.is_byz i = true)]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice}
  {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}

/-- The generic Chorus transition system (any quorum instance, any MVBA). -/
local notation "RTS" => Chorus.relationalTransitionSystem slot node nodeset merkle_root
  mstate mvalue mentries mmsg Phase PathChoice
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
  frame_rest htr phase hfr => exact Or.inl hfr

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
  frame_rest htr msg_commit_cast hfr => exact absurd (hfr ▸ h1) h0

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
  frame_rest htr msg_fallback_sig hfr => exact absurd (hfr ▸ h1) h0

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
  frame_rest htr local_path hfr => exact absurd (hfr ▸ h1) h0

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
    obtain ⟨-, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_rest htr msg_vote_pos_sig hfr => exact hfr ▸ h

set_option maxHeartbeats 1000000 in
/-- **`msg_vote_chunk` is monotone** — as `msg_vote_pos_sig_mono`: `vote`
writes it as a disjunction with its old value, `byz_carry_vote_chunk`
writes `true`. -/
theorem msg_vote_chunk_mono {l} (htr : (RTS).tr th s l s') :
    ∀ (r j : node) (m : merkle_root), s.msg_vote_chunk r j m = true → s'.msg_vote_chunk r j m = true := by
  intro r j m h
  cases l
  case vote i' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    simp_all
  case byz_carry_vote_chunk =>
    chorus_tr htr
    obtain ⟨-, rfl⟩ := htr
    chorus_field_simp
    simp_all
  frame_rest htr msg_vote_chunk hfr => exact hfr ▸ h

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
  frame_rest htr msg_vote_neg_sig hfr => exact hfr ▸ h

/-- **A vote that passes the receiver's check keeps passing it**: every
row `vote_valid` reads is a monotone network row. -/
theorem vote_valid_mono {l} (htr : (RTS).tr th s l s') {r : node}
    (h : Chorus.vote_valid r th s) : Chorus.vote_valid r th s' := by
  unfold Chorus.vote_valid Chorus.vote_entry_valid at *
  obtain ⟨hc, hsh, hall⟩ := h
  refine ⟨Chorus.msg_vote_cast.mono htr r hc, Chorus.msg_decrypt_share.mono htr r hsh,
    fun j hj => ?_⟩
  rcases hall j hj with ⟨m, hs, hch, hps⟩ | hn
  · exact Or.inl ⟨m, msg_vote_pos_sig_mono htr r j m hs, msg_vote_chunk_mono htr r j m hch,
      Chorus.msg_proposer_signed.mono htr j m hps⟩
  · exact Or.inr (msg_vote_neg_sig_mono htr r j hn)

/-- A valid vote's entry for a proposer: positive with its chunk under a
signed root, or negative. -/
theorem vote_valid_entry {r j : node} (h : Chorus.vote_valid r th s)
    (hj : th.is_proposer j = true) :
    (∃ m, s.msg_vote_pos_sig r j m = true ∧ s.msg_vote_chunk r j m = true ∧
      s.msg_proposer_signed j m = true) ∨ s.msg_vote_neg_sig r j = true := by
  unfold Chorus.vote_valid Chorus.vote_entry_valid at h
  exact h.2.2 j hj

/-- A correct validator's cast vote passes every receiver's check
(`vote_cast_valid`). -/
theorem correct_vote_valid
    (hr : (RTS).reachable th s) {a : node} (ha : ¬ nset.is_byz a = true)
    (hc : s.msg_vote_cast a = true) : Chorus.vote_valid a th s :=
  Chorus.reachable_vote_cast_valid hr a ⟨ha, hc⟩

/-- A correct validator's positive vote entry carries its chunk under a
proposer-signed root (`vote_pos_sig_chunk`, `vote_pos_from_local`,
`local_entry_pos_signed`). -/
theorem correct_vote_pos
    (hr : (RTS).reachable th s) {a j : node} {m : merkle_root} (ha : ¬ nset.is_byz a = true)
    (h : s.msg_vote_pos_sig a j m = true) :
    s.msg_vote_chunk a j m = true ∧ s.msg_proposer_signed j m = true :=
  ⟨(Chorus.reachable_vote_pos_sig_chunk hr a j m ha).mpr h,
    Chorus.reachable_local_entry_pos_signed hr a j m
      ⟨ha, Chorus.reachable_vote_pos_from_local hr a j m ⟨ha, h⟩⟩⟩

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
  frame_rest htr local_entry_neg hfr => exact hfr ▸ h

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
    repeat (obtain ⟨_, htr⟩ := htr)
    chorus_field_simp
    simp_all
  case fb_sign_neg =>
    chorus_tr htr
    repeat (obtain ⟨_, htr⟩ := htr)
    chorus_field_simp
    simp_all
  frame_rest htr local_fb_entry hfr => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **A collector's record comes with the certificate it broadcast**
(`broadcast_commitqc_*` is the only writer of `local_commitqc_sent`). -/
theorem commitqc_sent_flip {l} {c j : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_commitqc_sent c j = true) (h1 : s'.local_commitqc_sent c j = true) :
    (∃ m, s'.msg_commitqc_pos c j m = true) ∨ s'.msg_commitqc_neg c j = true := by
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
  frame_rest htr local_commitqc_sent hfr => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **A correct positive fallback signer has sent every validator its chunk**
(Algorithm 5, line 12 (`line:fb-redisseminate`)): the step that sets
`msg_fb_pos_sig k j m` for a correct `k` is `k`'s own `fb_sign_pos`, which
sends every validator its chunk under `(j, m)` in the same step. -/
theorem fb_pos_sig_chunks_flip {l} {k j : node} {m : merkle_root}
    (htr : (RTS).tr th s l s') (hk : ¬ nset.is_byz k = true)
    (h0 : ¬ s.msg_fb_pos_sig k j m = true) (h1 : s'.msg_fb_pos_sig k j m = true) :
    ∀ i, s'.msg_chunk k i j m = true := by
  cases l
  case fb_sign_pos i' j' m' q =>
    chorus_tr htr
    repeat (obtain ⟨_, htr⟩ := htr)
    chorus_field_simp
    intro i
    by_cases hjm : i' = k ∧ j = j' ∧ m = m'
    · obtain ⟨rfl, rfl, rfl⟩ := hjm
      simp
    · simp_all
  case byz_sign_fb_pos r' j' m' =>
    chorus_tr htr
    obtain ⟨hb, -, rfl⟩ := htr
    chorus_field_simp
    by_cases hrk : r' = k
    · subst hrk
      simp_all
    · simp_all
  frame_rest htr msg_fb_pos_sig hfr => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **The fallback-commit record comes with the vote** (`cast_fb_commit`). -/
theorem fbcommit_voted_flip {l} {i : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_fbcommit_voted i = true) (h1 : s'.local_fbcommit_voted i = true) :
    ∃ e, s'.msg_fbcommit_sig i e = true := by
  cases l
  case cast_fb_commit i' v' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hne
    · exact ⟨mvba.entries v', by simp⟩
    · simp_all
  frame_rest htr local_fbcommit_voted hfr => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **A correct validator's fallback commit vote signs its own decision**
(Algorithm 5, line 41 (`line:fb-commitvote`)): the step that sets
`msg_fbcommit_sig r e` for a correct `r` is `r`'s `cast_fb_commit r v`,
whose guard is `r`'s decision `v`, and it signs `entries(v)`. -/
theorem fbcommit_sig_flip {l} {r : node} {e : mentries}
    (htr : (RTS).tr th s l s') (hr : ¬ nset.is_byz r = true)
    (h0 : ¬ s.msg_fbcommit_sig r e = true) (h1 : s'.msg_fbcommit_sig r e = true) :
    ∃ v, mvba.decided s.mvba_st r v ∧ mvba.entries v = e := by
  cases l
  case cast_fb_commit i' v' =>
    chorus_tr htr
    obtain ⟨-, -, -, hd, -, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' r with rfl | hne
    · by_cases he : mvba.entries v' = e
      · exact ⟨v', hd, he⟩
      · simp_all
    · simp_all
  case byz_sign_fbcommit r' e' =>
    chorus_tr htr
    obtain ⟨hb, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne r' r with rfl | hne
    · simp_all
    · simp_all
  frame_rest htr msg_fbcommit_sig hfr => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **An availability record comes with the report**: the step that writes
`local_avail_marked i v` took the MVBA's availability input for `i` and
`v`, so `i` is `AvailReady` for `v` in the post-state. -/
theorem avail_marked_flip {l} {i : node} {v : mvalue}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_avail_marked i v = true) (h1 : s'.local_avail_marked i v = true) :
    mvba.availReady s'.mvba_st i v := by
  cases l
  case mvba_avail_ready i' v' n' =>
    chorus_tr htr
    obtain ⟨-, -, -, hav, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hi
    · rcases eq_or_ne v' v with rfl | hv
      · exact mvba.markAvail_effect _ _ _ _ hav
      · simp_all
    · simp_all
  frame_rest htr local_avail_marked hfr => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **A handoff record comes with its input**: the step that writes
`local_mvba_qc_accepted i` handed a certificate to `i`'s MVBA, whose
post-state is the new MVBA state. -/
theorem qc_accepted_flip {l} {i : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_mvba_qc_accepted i = true) (h1 : s'.local_mvba_qc_accepted i = true) :
    ∃ c, mvba.accept s.mvba_st i c s'.mvba_st := by
  cases l
  case accept_mvba_commitqc i' r c n =>
    chorus_tr htr
    obtain ⟨-, -, -, hacc, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hi
    · exact ⟨c, hacc⟩
    · simp_all
  frame_rest htr local_mvba_qc_accepted hfr => exact absurd (hfr ▸ h1) h0

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
def Active (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
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

/-- `receive_vote_pos`, enabled for a receiver that holds no entry of `r`'s
vote for `j` yet, once `r`'s vote passes the receiver's check and its entry
for `j` is positive on `m` with its chunk under a signed root. -/
theorem enabled_receive_vote_pos {i r j : node} {m : merkle_root}
    (hi : ¬ nset.is_byz i = true) (hj : th.is_proposer j = true)
    (hv : Chorus.vote_valid r th s) (hs : s.msg_vote_pos_sig r j m = true)
    (hch : s.msg_vote_chunk r j m = true) (hps : s.msg_proposer_signed j m = true)
    (hnp : ∀ m2, ¬ s.local_vote_rcv_pos i r j m2 = true) (hnn : ¬ s.local_vote_rcv_neg i r j = true) :
    Enabled RTS th s (.receive_vote_pos i r j m) := by
  unfold Chorus.vote_valid at hv
  obtain ⟨hc, hsh, hall⟩ := hv
  chorus_enabled
  exact ⟨_, hi, hj, hc, hsh, hall, hs, hch, hps, hnp, hnn, rfl⟩

theorem receive_vote_pos_effect {i r j : node} {m : merkle_root}
    (htr : (RTS).tr th s (.receive_vote_pos i r j m) s') :
    s'.local_vote_rcv_pos i r j m = true := by
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  chorus_field_simp

theorem enabled_receive_vote_neg {i r j : node}
    (hi : ¬ nset.is_byz i = true) (hj : th.is_proposer j = true)
    (hv : Chorus.vote_valid r th s) (hs : s.msg_vote_neg_sig r j = true)
    (hnp : ∀ m2, ¬ s.local_vote_rcv_pos i r j m2 = true) (hnn : ¬ s.local_vote_rcv_neg i r j = true) :
    Enabled RTS th s (.receive_vote_neg i r j) := by
  unfold Chorus.vote_valid at hv
  obtain ⟨hc, hsh, hall⟩ := hv
  chorus_enabled
  exact ⟨_, hi, hj, hc, hsh, hall, hs, hnp, hnn, rfl⟩

theorem receive_vote_neg_effect {i r j : node}
    (htr : (RTS).tr th s (.receive_vote_neg i r j) s') :
    s'.local_vote_rcv_neg i r j = true := by
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  chorus_field_simp

theorem enabled_fb_sign_pos {i j : node} {m : merkle_root} {q qv : nodeset}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i)
    (hph : s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
    (hv : s.local_voted i = true) (hnc : ¬ s.msg_commit_cast i = true)
    (hpath : ¬ s.local_path i = PathChoice_EnumClass.fallback) (hj : th.is_proposer j = true)
    (hqv : nset.supermajority qv) (hqvc : ∀ r, nset.member r qv = true → Chorus.vote_valid r th s)
    (hq : nset.greater_than_third q) (hps : s.msg_proposer_signed j m = true)
    (hqs : ∀ r, nset.member r q = true →
      s.msg_vote_pos_sig r j m = true ∧ s.msg_vote_chunk r j m = true ∧ Chorus.vote_valid r th s)
    (hwe : th.well_encoded m = true) (hfr : ¬ s.local_fb_entry i j = true) :
    Enabled RTS th s (.fb_sign_pos i j m q) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hph, hv, hnc, hpath, hj, ⟨qv, hqv, hqvc⟩, hq, hps, hqs, hwe, hfr, rfl⟩

theorem fb_sign_pos_effect {i j : node} {m : merkle_root} {q : nodeset}
    (htr : (RTS).tr th s (.fb_sign_pos i j m q) s') :
    s'.msg_fb_pos_sig i j m = true := by
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  chorus_field_simp

/-- `fb_sign_neg` against the votes of `qv` that `i` holds: an entry of every
sender's vote, and no root with `f+1` positive entries among them that
re-encodes to it. -/
theorem enabled_fb_sign_neg {i j : node} {qv : nodeset}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i)
    (hph : s.phase = Phase_EnumClass.post_fb_arm ∨ s.phase = Phase_EnumClass.post_mvba_arm)
    (hv : s.local_voted i = true) (hnc : ¬ s.msg_commit_cast i = true)
    (hpath : ¬ s.local_path i = PathChoice_EnumClass.fallback) (hj : th.is_proposer j = true)
    (hqv : nset.supermajority qv)
    (hrcv : ∀ r, nset.member r qv = true →
      (∃ m2, s.local_vote_rcv_pos i r j m2 = true) ∨ s.local_vote_rcv_neg i r j = true)
    (hnone : ∀ M q, ¬ (nset.greater_than_third q ∧
      (∀ r, nset.member r q = true → nset.member r qv = true ∧ s.local_vote_rcv_pos i r j M = true) ∧
      th.well_encoded M = true))
    (hfr : ¬ s.local_fb_entry i j = true) :
    Enabled RTS th s (.fb_sign_neg i j qv) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hph, hv, hnc, hpath, hj, hqv, hrcv,
    fun M q h1 h2 h3 => hnone M q ⟨h1, h2, h3⟩, hfr, rfl⟩

theorem fb_sign_neg_effect {i j : node} {qv : nodeset}
    (htr : (RTS).tr th s (.fb_sign_neg i j qv) s') :
    s'.msg_fb_neg_sig i j = true := by
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
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
    s'.msg_commitqc_pos c j m = true := by
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
    s'.msg_commitqc_neg c j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

/-! The three finalization routes per entry sign. Each is enabled for a
validator that has assigned nothing for `j` yet and has received the
certificate the route reads, and re-broadcasts that certificate under its
own name. -/

theorem enabled_commit_assign_pos_fast {i j c : node} {m : merkle_root}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true) (hqc : s.msg_commitqc_pos c j m = true)
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) (hnn : ¬ s.local_committed_neg i j = true) :
    Enabled RTS th s (.commit_assign_pos_fast i j m c) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hnc, hj, hqc, hnp, hnn, rfl⟩

theorem commit_assign_pos_fast_effect {i j c : node} {m : merkle_root}
    (htr : (RTS).tr th s (.commit_assign_pos_fast i j m c) s') :
    s'.local_committed_pos i j m = true ∧ s'.msg_commitqc_pos i j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_commit_assign_pos_fb {i j c : node} {m : merkle_root} {e : mentries}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true) (hqc : s.msg_fbcommitqc c e = true) (he : th.mval_pos e j m = true)
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) (hnn : ¬ s.local_committed_neg i j = true) :
    Enabled RTS th s (.commit_assign_pos_fb i j m c e) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hnc, hj, hqc, he, hnp, hnn, rfl⟩

theorem commit_assign_pos_fb_effect {i j c : node} {m : merkle_root} {e : mentries}
    (htr : (RTS).tr th s (.commit_assign_pos_fb i j m c e) s') :
    s'.local_committed_pos i j m = true ∧ s'.msg_fbcommitqc i e = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem commit_assign_pos_fb_guard {i j c : node} {m : merkle_root} {e : mentries}
    (htr : (RTS).tr th s (.commit_assign_pos_fb i j m c e) s') :
    th.mval_pos e j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, he, -, -, -⟩ := htr
  exact he

theorem enabled_commit_assign_pos_mvba {i j r : node} {m : merkle_root} {c : mmsg} {v : mvalue}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true) (hmsg : s.msg_mvba_cert r c = true)
    (hc : mvba.certifies s.mvba_st c (mvba.entries v)) (hv : th.mval_pos (mvba.entries v) j m = true)
    (hb : (¬ th.mval_fb v j = true ∧ Chorus.vote_quorum_pos j m th s) ∨
      (th.mval_fb v j = true ∧ Chorus.fb_quorum_pos j m th s ∧ Chorus.fbcert th s))
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) (hnn : ¬ s.local_committed_neg i j = true) :
    Enabled RTS th s (.commit_assign_pos_mvba i j m r c v) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hnc, hj, hmsg, hc, hv, hb, hnp, hnn, rfl⟩

theorem commit_assign_pos_mvba_effect {i j r : node} {m : merkle_root} {c : mmsg} {v : mvalue}
    (htr : (RTS).tr th s (.commit_assign_pos_mvba i j m r c v) s') :
    s'.local_committed_pos i j m = true ∧ s'.msg_mvba_cert i c = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem commit_assign_pos_mvba_guard {i j r : node} {m : merkle_root} {c : mmsg} {v : mvalue}
    (htr : (RTS).tr th s (.commit_assign_pos_mvba i j m r c v) s') :
    mvba.certifies s.mvba_st c (mvba.entries v) ∧ th.mval_pos (mvba.entries v) j m = true ∧
      ((¬ th.mval_fb v j = true ∧ Chorus.vote_quorum_pos j m th s) ∨
        (th.mval_fb v j = true ∧ Chorus.fb_quorum_pos j m th s ∧ Chorus.fbcert th s)) := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, hc, hv, hb, -, -, -⟩ := htr
  exact ⟨hc, hv, hb⟩

theorem enabled_commit_assign_neg_fast {i j c : node}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true) (hqc : s.msg_commitqc_neg c j = true)
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) (hnn : ¬ s.local_committed_neg i j = true) :
    Enabled RTS th s (.commit_assign_neg_fast i j c) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hnc, hj, hqc, hnp, hnn, rfl⟩

theorem commit_assign_neg_fast_effect {i j c : node}
    (htr : (RTS).tr th s (.commit_assign_neg_fast i j c) s') :
    s'.local_committed_neg i j = true ∧ s'.msg_commitqc_neg i j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_commit_assign_neg_fb {i j c : node} {e : mentries}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true) (hqc : s.msg_fbcommitqc c e = true) (he : th.mval_neg e j = true)
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) (hnn : ¬ s.local_committed_neg i j = true) :
    Enabled RTS th s (.commit_assign_neg_fb i j c e) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hnc, hj, hqc, he, hnp, hnn, rfl⟩

theorem commit_assign_neg_fb_effect {i j c : node} {e : mentries}
    (htr : (RTS).tr th s (.commit_assign_neg_fb i j c e) s') :
    s'.local_committed_neg i j = true ∧ s'.msg_fbcommitqc i e = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem commit_assign_neg_fb_guard {i j c : node} {e : mentries}
    (htr : (RTS).tr th s (.commit_assign_neg_fb i j c e) s') :
    th.mval_neg e j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, he, -, -, -⟩ := htr
  exact he

theorem enabled_commit_assign_neg_mvba {i j r : node} {c : mmsg} {v : mvalue}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i) (hnc : ¬ s.local_committed i = true)
    (hj : th.is_proposer j = true) (hmsg : s.msg_mvba_cert r c = true)
    (hc : mvba.certifies s.mvba_st c (mvba.entries v)) (hv : th.mval_neg (mvba.entries v) j = true)
    (hb : Chorus.vote_quorum_neg j th s ∨
      ((Chorus.fb_quorum_neg j th s ∨ Chorus.equiv_evidence j th s) ∧ Chorus.fbcert th s))
    (hnp : ∀ m', ¬ s.local_committed_pos i j m' = true) (hnn : ¬ s.local_committed_neg i j = true) :
    Enabled RTS th s (.commit_assign_neg_mvba i j r c v) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hnc, hj, hmsg, hc, hv, hb, hnp, hnn, rfl⟩

theorem commit_assign_neg_mvba_effect {i j r : node} {c : mmsg} {v : mvalue}
    (htr : (RTS).tr th s (.commit_assign_neg_mvba i j r c v) s') :
    s'.local_committed_neg i j = true ∧ s'.msg_mvba_cert i c = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem commit_assign_neg_mvba_guard {i j r : node} {c : mmsg} {v : mvalue}
    (htr : (RTS).tr th s (.commit_assign_neg_mvba i j r c v) s') :
    mvba.certifies s.mvba_st c (mvba.entries v) ∧ th.mval_neg (mvba.entries v) j = true ∧
      (Chorus.vote_quorum_neg j th s ∨
        ((Chorus.fb_quorum_neg j th s ∨ Chorus.equiv_evidence j th s) ∧ Chorus.fbcert th s)) := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, hc, hv, hb, -, -, -⟩ := htr
  exact ⟨hc, hv, hb⟩

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
    (hpos : ∀ J M, th.mval_pos (mvba.entries v) J M = true → th.is_proposer J = true ∧
      ((¬ th.mval_fb v J = true ∧ Chorus.vote_quorum_pos J M th s) ∨
        (th.mval_fb v J = true ∧ Chorus.fb_quorum_pos J M th s ∧ Chorus.fbcert th s)))
    (hneg : ∀ J, th.mval_neg (mvba.entries v) J = true → th.is_proposer J = true ∧
      (Chorus.vote_quorum_neg J th s ∨
        ((Chorus.fb_quorum_neg J th s ∨ Chorus.equiv_evidence J th s) ∧ Chorus.fbcert th s)))
    (hall : ∀ J, th.is_proposer J = true → (∃ M, th.mval_pos (mvba.entries v) J M = true) ∨ th.mval_neg (mvba.entries v) J = true)
    (hprop : mvba.propose s.mvba_st i v n) :
    Enabled RTS th s (.mvba_propose i v n) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, htrig, hpos, hneg, hall, hprop, rfl⟩

/-- `send_mvba_cert`, enabled for a correct, active validator whose MVBA
decision has output the certificate `c` and that has not yet sent one. -/
theorem enabled_send_mvba_cert {i : node} {c : mmsg}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i)
    (hd : mvba.decidedCert s.mvba_st i c)
    (hfr : ¬ s.local_mvba_cert_sent i = true) :
    Enabled RTS th s (.send_mvba_cert i c) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hd, hfr, rfl⟩

theorem send_mvba_cert_effect {i : node} {c : mmsg}
    (htr : (RTS).tr th s (.send_mvba_cert i c) s') :
    s'.msg_mvba_cert i c = true ∧ s'.local_mvba_cert_sent i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

/-- What `send_mvba_cert` reads: a correct sender, and the certificate its
own decision output. -/
theorem send_mvba_cert_guard {i : node} {c : mmsg}
    (htr : (RTS).tr th s (.send_mvba_cert i c) s') :
    ¬ nset.is_byz i = true ∧ mvba.decidedCert s.mvba_st i c := by
  chorus_tr htr
  obtain ⟨hi, -, -, hd, -, -⟩ := htr
  exact ⟨hi, hd⟩

/-- **The certificate `send_mvba_cert` sends is valid**, at a reachable MVBA
state: the decision's output certificate certifies the decided entries
(`decidedCert_certifies`). -/
theorem send_mvba_cert_certifies {i : node} {c : mmsg}
    (hr : mvba.reachable s.mvba_st)
    (htr : (RTS).tr th s (.send_mvba_cert i c) s') :
    ∃ e, mvba.certifies s'.mvba_st c e := by
  obtain ⟨hi, hd⟩ := send_mvba_cert_guard htr
  obtain ⟨v, -, hc⟩ := mvba.decidedCert_certifies _ hr i c hi hd
  refine ⟨mvba.entries v, ?_⟩
  rw [Chorus.send_mvba_cert.frame_mvba_st htr]
  exact hc

theorem enabled_accept_mvba_commitqc {i r : node} {c : mmsg} {n : mstate}
    (hi : ¬ nset.is_byz i = true) (hfr : ¬ s.local_mvba_qc_accepted i = true)
    (hmsg : s.msg_mvba_cert r c = true) (hacc : mvba.accept s.mvba_st i c n) :
    Enabled RTS th s (.accept_mvba_commitqc i r c n) := by
  chorus_enabled
  exact ⟨_, hi, hfr, hmsg, hacc, rfl⟩

theorem enabled_mvba_avail_ready {i : node} {v : mvalue} {n : mstate}
    (hi : ¬ nset.is_byz i = true)
    (hda : ∀ J M, th.mval_pos (mvba.entries v) J M = true → th.mval_fb v J = true →
      Chorus.chunk_received i J M th s)
    (hfr : ¬ s.local_avail_marked i v = true) (hav : mvba.markAvail s.mvba_st i v n) :
    Enabled RTS th s (.mvba_avail_ready i v n) := by
  chorus_enabled
  exact ⟨_, hi, hda, hfr, hav, rfl⟩

theorem enabled_on_mvba_decide_pos {i j : node} {m : merkle_root} {v : mvalue}
    (hi : ¬ nset.is_byz i = true)
    (hj : th.is_proposer j = true)
    (hd : mvba.decided s.mvba_st i v) (hv : th.mval_pos (mvba.entries v) j m = true)
    (hc : (¬ th.mval_fb v j = true ∧ Chorus.vote_quorum_pos j m th s) ∨
      (th.mval_fb v j = true ∧ Chorus.fb_quorum_pos j m th s ∧ Chorus.fbcert th s))
    (hfr : ¬ s.local_mvba_recorded i j = true) :
    Enabled RTS th s (.on_mvba_decide_pos i j m v) := by
  chorus_enabled
  exact ⟨_, hi, hj, hd, hv, hc, hfr, rfl⟩

theorem on_mvba_decide_pos_effect {i j : node} {m : merkle_root} {v : mvalue}
    (htr : (RTS).tr th s (.on_mvba_decide_pos i j m v) s') :
    s'.aux_mvba_decided_pos j m = true ∧ s'.local_mvba_recorded i j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_on_mvba_decide_neg {i j : node} {v : mvalue}
    (hi : ¬ nset.is_byz i = true)
    (hj : th.is_proposer j = true)
    (hd : mvba.decided s.mvba_st i v) (hv : th.mval_neg (mvba.entries v) j = true)
    (hc : Chorus.vote_quorum_neg j th s ∨
      ((Chorus.fb_quorum_neg j th s ∨ Chorus.equiv_evidence j th s) ∧ Chorus.fbcert th s))
    (hfr : ¬ s.local_mvba_recorded i j = true) :
    Enabled RTS th s (.on_mvba_decide_neg i j v) := by
  chorus_enabled
  exact ⟨_, hi, hj, hd, hv, hc, hfr, rfl⟩

theorem on_mvba_decide_neg_effect {i j : node} {v : mvalue}
    (htr : (RTS).tr th s (.on_mvba_decide_neg i j v) s') :
    s'.aux_mvba_decided_neg j = true ∧ s'.local_mvba_recorded i j = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_mvba_terminate {i : node} {v : mvalue}
    (hi : ¬ nset.is_byz i = true)
    (hnc : ¬ s.local_mvba_complete i = true)
    (hd : mvba.decided s.mvba_st i v)
    (hall : ∀ J, th.is_proposer J = true → s.local_mvba_recorded i J = true) :
    Enabled RTS th s (.mvba_terminate i v) := by
  chorus_enabled
  exact ⟨_, hi, hnc, hd, hall, rfl⟩

theorem mvba_terminate_effect {i : node} {v : mvalue}
    (htr : (RTS).tr th s (.mvba_terminate i v) s') :
    s'.local_mvba_complete i = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, rfl⟩ := htr
  chorus_field_simp

theorem enabled_cast_fb_commit {i : node} {v : mvalue}
    (hi : ¬ nset.is_byz i = true) (ha : Active s i)
    (hd : mvba.decided s.mvba_st i v)
    (hc : s.local_mvba_complete i = true)
    (hda : ∀ J M, th.mval_pos (mvba.entries v) J M = true → th.mval_fb v J = true →
      Chorus.chunk_received i J M th s)
    (hfr : ¬ s.local_fbcommit_voted i = true) :
    Enabled RTS th s (.cast_fb_commit i v) := by
  chorus_enabled
  exact ⟨_, hi, ha.1, ha.2, hd, hc, hda, hfr, rfl⟩

theorem cast_fb_commit_effect {i : node} {v : mvalue}
    (htr : (RTS).tr th s (.cast_fb_commit i v) s') :
    s'.msg_fbcommit_sig i (mvba.entries v) = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

/-- `broadcast_fbcommitqc`, enabled for a correct, active collector that has
not sent one yet and holds `2f+1` fallback commit votes over `e`. -/
theorem enabled_broadcast_fbcommitqc {c : node} {e : mentries} {q : nodeset}
    (hc : ¬ nset.is_byz c = true) (ha : Active s c) (hq : nset.supermajority q)
    (hall : ∀ r, nset.member r q = true → s.msg_fbcommit_sig r e = true)
    (hfr : ¬ s.local_fbcommitqc_sent c = true) :
    Enabled RTS th s (.broadcast_fbcommitqc c e q) := by
  chorus_enabled
  exact ⟨_, hc, ha.1, ha.2, hq, hall, hfr, rfl⟩

theorem broadcast_fbcommitqc_effect {c : node} {e : mentries} {q : nodeset}
    (htr : (RTS).tr th s (.broadcast_fbcommitqc c e q) s') :
    s'.msg_fbcommitqc c e = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

set_option maxHeartbeats 1000000 in
/-- **A certificate-sent record comes with the certificate**: the step that
sets `local_mvba_cert_sent i` is `i`'s `send_mvba_cert`, which sends a valid
MVBA commit certificate. -/
theorem mvba_cert_sent_flip {l} {i : node}
    (hr : mvba.reachable s.mvba_st) (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_mvba_cert_sent i = true) (h1 : s'.local_mvba_cert_sent i = true) :
    ∃ c e, mvba.certifies s'.mvba_st c e ∧ s'.msg_mvba_cert i c = true := by
  cases l
  case send_mvba_cert i' c =>
    obtain rfl : i' = i := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    obtain ⟨e, he⟩ := send_mvba_cert_certifies hr htr
    exact ⟨c, e, he, (send_mvba_cert_effect htr).1⟩
  frame_rest htr local_mvba_cert_sent hfr => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **A correct validator sends only valid MVBA commit certificates**: the
step that sets `msg_mvba_cert i c` for a correct `i` is its
`send_mvba_cert` or the re-broadcast of a finalization on `c`
(`commit_assign_*_mvba`), each of which checks `c` (`mvba.certifies`). -/
theorem mvba_cert_flip {l} {i : node} {c : mmsg}
    (hr : mvba.reachable s.mvba_st)
    (htr : (RTS).tr th s l s') (hi : ¬ nset.is_byz i = true)
    (h0 : ¬ s.msg_mvba_cert i c = true) (h1 : s'.msg_mvba_cert i c = true) :
    ∃ e, mvba.certifies s'.mvba_st c e := by
  cases l
  case send_mvba_cert i' c' =>
    obtain ⟨rfl, rfl⟩ : i' = i ∧ c' = c := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    exact send_mvba_cert_certifies hr htr
  case commit_assign_pos_mvba i' j' m' r' c' v =>
    obtain ⟨rfl, rfl⟩ : i' = i ∧ c' = c := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    refine ⟨mvba.entries v, ?_⟩
    rw [Chorus.commit_assign_pos_mvba.frame_mvba_st htr]
    exact (commit_assign_pos_mvba_guard htr).1
  case commit_assign_neg_mvba i' j' r' c' v =>
    obtain ⟨rfl, rfl⟩ : i' = i ∧ c' = c := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    refine ⟨mvba.entries v, ?_⟩
    rw [Chorus.commit_assign_neg_mvba.frame_mvba_st htr]
    exact (commit_assign_neg_mvba_guard htr).1
  case byz_send_mvba_cert r' c' =>
    chorus_tr htr
    obtain ⟨hb, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne r' i with rfl | hne
    · simp_all
    · simp_all
  frame_rest htr msg_mvba_cert hfr => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **A collector's fallback record comes with the certificate it sent**
(`broadcast_fbcommitqc` is the only writer of `local_fbcommitqc_sent`). -/
theorem fbcommitqc_sent_flip {l} {c : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_fbcommitqc_sent c = true) (h1 : s'.local_fbcommitqc_sent c = true) :
    ∃ e, s'.msg_fbcommitqc c e = true := by
  cases l
  case broadcast_fbcommitqc c' e q =>
    obtain rfl : c' = c := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    exact ⟨e, broadcast_fbcommitqc_effect htr⟩
  frame_rest htr local_fbcommitqc_sent hfr => exact absurd (hfr ▸ h1) h0

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

theorem chunk_received_step {l} (htr : (RTS).tr th s l s') {i j : node} {m : merkle_root}
    (h : Chorus.chunk_received i j m th s) : Chorus.chunk_received i j m th s' := by
  unfold Chorus.chunk_received at h ⊢
  obtain ⟨k, hk⟩ := h
  exact ⟨k, Chorus.msg_chunk.mono htr k i j m hk⟩

theorem chunk_quorum_step {l} (htr : (RTS).tr th s l s') {j : node} {m : merkle_root}
    (h : Chorus.chunk_quorum j m th s) : Chorus.chunk_quorum j m th s' := by
  unfold Chorus.chunk_quorum at h ⊢
  obtain ⟨q, hq, hall⟩ := h
  exact ⟨q, hq, fun a ha => msg_vote_chunk_mono htr a j m (hall a ha)⟩

theorem fbcommitqc_step {l} (htr : (RTS).tr th s l s') {e : mentries}
    (h : Chorus.fbcommitqc e th s) : Chorus.fbcommitqc e th s' := by
  unfold Chorus.fbcommitqc at h ⊢
  obtain ⟨q, hq, hall⟩ := h
  exact ⟨q, hq, fun a ha => Chorus.msg_fbcommit_sig.mono htr a e (hall a ha)⟩

/-- The bridge check on a positive entry's certificate is monotone. -/
theorem bridge_pos_step {l} (htr : (RTS).tr th s l s') {v : mvalue} {j : node} {m : merkle_root}
    (h : (¬ th.mval_fb v j = true ∧ Chorus.vote_quorum_pos j m th s) ∨
      (th.mval_fb v j = true ∧ Chorus.fb_quorum_pos j m th s ∧ Chorus.fbcert th s)) :
    (¬ th.mval_fb v j = true ∧ Chorus.vote_quorum_pos j m th s') ∨
      (th.mval_fb v j = true ∧ Chorus.fb_quorum_pos j m th s' ∧ Chorus.fbcert th s') :=
  h.imp (fun ⟨a, b⟩ => ⟨a, vote_quorum_pos_step htr b⟩)
    fun ⟨a, b, d⟩ => ⟨a, fb_quorum_pos_step htr b, fbcert_step htr d⟩

/-- The bridge check on a negative entry's certificate is monotone. -/
theorem bridge_neg_step {l} (htr : (RTS).tr th s l s') {j : node}
    (h : Chorus.vote_quorum_neg j th s ∨
      ((Chorus.fb_quorum_neg j th s ∨ Chorus.equiv_evidence j th s) ∧ Chorus.fbcert th s)) :
    Chorus.vote_quorum_neg j th s' ∨
      ((Chorus.fb_quorum_neg j th s' ∨ Chorus.equiv_evidence j th s') ∧ Chorus.fbcert th s') :=
  h.imp (vote_quorum_neg_step htr)
    fun ⟨a, b⟩ => ⟨a.imp (fb_quorum_neg_step htr) (equiv_evidence_step htr), fbcert_step htr b⟩

/-- **A decided root is proposer-signed**, at every reachable state: the
decision is backed by a FastQC or a FallbackQC (`mvba_decided_pos_backed`),
either of which has an honest member whose signature pins the proposer's. -/
theorem proposer_signed_of_decided_pos (hr : (RTS).reachable th s) {j : node} {m : merkle_root}
    (h : s.aux_mvba_decided_pos j m = true) : s.msg_proposer_signed j m = true := by
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
def ProposeTrigger (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (i : node) : Prop :=
  (Chorus.fbcert th st ∧
    (st.phase = Phase_EnumClass.post_fb_arm ∨ st.phase = Phase_EnumClass.post_mvba_arm)) ∨
  (Chorus.complete_fast_metablock i th st ∧ st.phase = Phase_EnumClass.post_mvba_arm)

set_option maxHeartbeats 1000000 in
/-- **A valid MVBA certificate stays valid** across every step: an MVBA
transition keeps it (`certified_mono`), and every other action frames the
MVBA's state. -/
theorem certifies_step {l} (htr : (RTS).tr th s l s') {c : mmsg} {e : mentries}
    (hc : mvba.certifies s.mvba_st c e) : mvba.certifies s'.mvba_st c e := by
  cases l
  case mvba_step =>
    chorus_tr htr
    obtain ⟨hst, rfl⟩ := htr
    chorus_field_simp
    exact mvba.certified_mono _ _ c e (mvba.step_trans _ _ hst) hc
  case mvba_propose =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, -, hp, rfl⟩ := htr
    chorus_field_simp
    exact mvba.certified_mono _ _ c e (mvba.propose_trans _ _ _ _ hp) hc
  case accept_mvba_commitqc =>
    chorus_tr htr
    obtain ⟨-, -, -, hacc, rfl⟩ := htr
    chorus_field_simp
    exact mvba.certified_mono _ _ c e (mvba.accept_trans _ _ _ _ hacc) hc
  case mvba_avail_ready =>
    chorus_tr htr
    obtain ⟨-, -, -, hav, rfl⟩ := htr
    chorus_field_simp
    exact mvba.certified_mono _ _ c e (mvba.markAvail_trans _ _ _ _ hav) hc
  case abandon =>
    chorus_tr htr
    obtain ⟨hab, rfl⟩ := htr
    chorus_field_simp
    exact mvba.certified_mono _ _ c e (mvba.abandon_trans _ _ _ hab) hc
  frame_rest htr mvba_st hfr => exact hfr ▸ hc

/-! ### Commitment proofs, with their senders

A validator finalizes an entry on a commitment proof it received, and
re-broadcasts the proof under its own name (Algorithm 4, line 35
(`line:fast-rebroadcast-commitqc`), Algorithm 5, line 46
(`line:fb-commit-rebroadcast`), and the supplement's "re-broadcasts it").
`CertPos st c j m` is that a proof for `j`'s positive entry `m` is on the
network **from sender `c`**, in one of the three forms the routes
`commit_assign_pos_*` read, with what the route checks of it; the step to a
receiver is owed when `c` is correct (`Owed`). -/

/-- A commitment proof for `j`'s positive entry `m`, sent by `c`: a fast
commit certificate, a fallback commit certificate whose entry vector has the
entry, or a valid MVBA commit certificate whose entries a representation `v`
with the entry and its bridge certificate on the network names. -/
def CertPos (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (c j : node) (m : merkle_root) : Prop :=
  st.msg_commitqc_pos c j m = true ∨
  (∃ e, st.msg_fbcommitqc c e = true ∧ th.mval_pos e j m = true) ∨
  (∃ cc v, st.msg_mvba_cert c cc = true ∧ mvba.certifies st.mvba_st cc (mvba.entries v) ∧
    th.mval_pos (mvba.entries v) j m = true ∧
    ((¬ th.mval_fb v j = true ∧ Chorus.vote_quorum_pos j m th st) ∨
      (th.mval_fb v j = true ∧ Chorus.fb_quorum_pos j m th st ∧ Chorus.fbcert th st)))

/-- The same for `j`'s negative entry. -/
def CertNeg (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (c j : node) : Prop :=
  st.msg_commitqc_neg c j = true ∨
  (∃ e, st.msg_fbcommitqc c e = true ∧ th.mval_neg e j = true) ∨
  (∃ cc v, st.msg_mvba_cert c cc = true ∧ mvba.certifies st.mvba_st cc (mvba.entries v) ∧
    th.mval_neg (mvba.entries v) j = true ∧
    (Chorus.vote_quorum_neg j th st ∨
      ((Chorus.fb_quorum_neg j th st ∨ Chorus.equiv_evidence j th st) ∧ Chorus.fbcert th st)))

theorem certPos_step {l} (htr : (RTS).tr th s l s') {c j : node} {m : merkle_root}
    (h : CertPos (mvba := mvba) th s c j m) : CertPos (mvba := mvba) th s' c j m := by
  rcases h with h | ⟨e, he, hm⟩ | ⟨cc, v, hmsg, hc, hv, hb⟩
  · exact Or.inl (Chorus.msg_commitqc_pos.mono htr c j m h)
  · exact Or.inr (Or.inl ⟨e, Chorus.msg_fbcommitqc.mono htr c e he, hm⟩)
  · refine Or.inr (Or.inr ⟨cc, v, Chorus.msg_mvba_cert.mono htr c cc hmsg, certifies_step htr hc, hv, ?_⟩)
    exact bridge_pos_step htr hb

theorem certNeg_step {l} (htr : (RTS).tr th s l s') {c j : node}
    (h : CertNeg (mvba := mvba) th s c j) : CertNeg (mvba := mvba) th s' c j := by
  rcases h with h | ⟨e, he, hm⟩ | ⟨cc, v, hmsg, hc, hv, hb⟩
  · exact Or.inl (Chorus.msg_commitqc_neg.mono htr c j h)
  · exact Or.inr (Or.inl ⟨e, Chorus.msg_fbcommitqc.mono htr c e he, hm⟩)
  · refine Or.inr (Or.inr ⟨cc, v, Chorus.msg_mvba_cert.mono htr c cc hmsg, certifies_step htr hc, hv, ?_⟩)
    exact bridge_neg_step htr hb

set_option maxHeartbeats 1000000 in
/-- **A committed positive entry comes with the proof it re-broadcast.** If
`local_committed_pos i j m` flips on a step, the step was one of `i`'s three
routes `commit_assign_pos_*`, its only writers, which sent the proof it read
under `i`'s own name: so `i` is the sender of a commitment proof for the
entry at the post-state. -/
theorem committed_pos_flip {l} {i j : node} {m : merkle_root}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_committed_pos i j m = true) (h1 : s'.local_committed_pos i j m = true) :
    CertPos (mvba := mvba) th s' i j m := by
  cases l
  case commit_assign_pos_fast i' j' m' c' =>
    obtain ⟨rfl, rfl, rfl⟩ : i' = i ∧ j' = j ∧ m' = m := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    exact Or.inl (commit_assign_pos_fast_effect htr).2
  case commit_assign_pos_fb i' j' m' c' e =>
    obtain ⟨rfl, rfl, rfl⟩ : i' = i ∧ j' = j ∧ m' = m := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    exact Or.inr (Or.inl ⟨e, (commit_assign_pos_fb_effect htr).2, commit_assign_pos_fb_guard htr⟩)
  case commit_assign_pos_mvba i' j' m' r' c v =>
    obtain ⟨rfl, rfl, rfl⟩ : i' = i ∧ j' = j ∧ m' = m := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    obtain ⟨hc, hv, hb⟩ := commit_assign_pos_mvba_guard htr
    refine Or.inr (Or.inr ⟨c, v, (commit_assign_pos_mvba_effect htr).2, ?_, hv, ?_⟩)
    · rw [Chorus.commit_assign_pos_mvba.frame_mvba_st htr]
      exact hc
    · exact bridge_pos_step htr hb
  frame_rest htr local_committed_pos hfr => exact absurd (hfr ▸ h1) h0

set_option maxHeartbeats 1000000 in
/-- **A committed negative entry comes with the proof it re-broadcast**, by
the same dispatch over `commit_assign_neg_*`. -/
theorem committed_neg_flip {l} {i j : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_committed_neg i j = true) (h1 : s'.local_committed_neg i j = true) :
    CertNeg (mvba := mvba) th s' i j := by
  cases l
  case commit_assign_neg_fast i' j' c' =>
    obtain ⟨rfl, rfl⟩ : i' = i ∧ j' = j := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    exact Or.inl (commit_assign_neg_fast_effect htr).2
  case commit_assign_neg_fb i' j' c' e =>
    obtain ⟨rfl, rfl⟩ : i' = i ∧ j' = j := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    exact Or.inr (Or.inl ⟨e, (commit_assign_neg_fb_effect htr).2, commit_assign_neg_fb_guard htr⟩)
  case commit_assign_neg_mvba i' j' r' c v =>
    obtain ⟨rfl, rfl⟩ : i' = i ∧ j' = j := by
      have h := htr
      chorus_tr h
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := h
      chorus_field_simp
      by_contra hne
      simp_all
    obtain ⟨hc, hv, hb⟩ := commit_assign_neg_mvba_guard htr
    refine Or.inr (Or.inr ⟨c, v, (commit_assign_neg_mvba_effect htr).2, ?_, hv, ?_⟩)
    · rw [Chorus.commit_assign_neg_mvba.frame_mvba_st htr]
      exact hc
    · exact bridge_neg_step htr hb
  frame_rest htr local_committed_neg hfr => exact absurd (hfr ▸ h1) h0

/-- **The MVBA's trigger, from correct senders**: a correct `FBCert`, or a
correct validator that cast its fast commit vote with a complete fast
meta-block (whose `FastBlock` it broadcast). The form of `mvba_invoked` that
makes the proposals owed. -/
def CorrectTrigger (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) :
    Prop :=
  CorrectFBCert st ∨ ∃ i0, ¬ nset.is_byz i0 = true ∧ st.msg_commit_cast i0 = true ∧
    Chorus.complete_fast_metablock (nset := nset) (mvba := mvba) i0 th st

theorem correctFBCert_step {l} (htr : (RTS).tr th s l s') (h : CorrectFBCert s) :
    CorrectFBCert s' :=
  let ⟨q, hq, hc, hall⟩ := h
  ⟨q, hq, hc, fun a ha => Chorus.msg_fallback_sig.mono htr a (hall a ha)⟩

theorem correctFbCommitQC_step {l} (htr : (RTS).tr th s l s') {e : mentries}
    (h : CorrectFbCommitQC e s) : CorrectFbCommitQC e s' :=
  let ⟨q, hq, hc, hall⟩ := h
  ⟨q, hq, hc, fun a ha => Chorus.msg_fbcommit_sig.mono htr a e (hall a ha)⟩

theorem fbcert_of_correct (h : CorrectFBCert s) : Chorus.fbcert (nset := nset) (mvba := mvba) th s :=
  let ⟨q, hq, _, hall⟩ := h
  ⟨q, hq, hall⟩

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

variable {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited mstate] [Inhabited mvalue] [Inhabited mentries] [Inhabited mmsg]
  [Inhabited Phase] [Inhabited PathChoice]
  {nset : ByzNodeSet node nodeset}
  {cnt : Cadence.ByzNodeSetCounting node nodeset nset}
  {mvba : MVBASafety node mvalue mentries mmsg mstate nodeset nset (fun i => nset.is_byz i = true)}
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice}

/-- The generic Chorus transition system (any quorum instance, any MVBA). -/
local notation "RTS" => Chorus.relationalTransitionSystem slot node nodeset merkle_root
  mstate mvalue mentries mmsg Phase PathChoice

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
    {F Q : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) → Prop}
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

/-- A collector's record comes with a certificate for that proposer that it
broadcast. -/
theorem commitqc_sent_msg (r : CRun th) {c j : node} :
    ∀ n, (r.at' n).local_commitqc_sent c j = true →
      (∃ m, (r.at' n).msg_commitqc_pos c j m = true) ∨ (r.at' n).msg_commitqc_neg c j = true :=
  record_backed r (F := fun st => st.local_commitqc_sent c j = true)
    (Q := fun st => (∃ m, st.msg_commitqc_pos c j m = true) ∨ st.msg_commitqc_neg c j = true)
    (by simp [Chorus.local_commitqc_sent.init r.starts c j])
    (fun n h0 h1 => commitqc_sent_flip (r.steps n) h0 h1)
    (fun n h => h.imp (fun ⟨m, hm⟩ => ⟨m, Chorus.msg_commitqc_pos.mono (r.steps n) c j m hm⟩)
      (Chorus.msg_commitqc_neg.mono (r.steps n) c j))

/-- **A correct positive fallback signer has sent every validator its
chunk**: at every point of the run at which a correct `k` holds a positive
fallback signature for `(j, m)`, it has sent every validator its chunk under
`m`. The re-dissemination happens inside the signing step
(`fb_pos_sig_chunks_flip`). -/
theorem fb_pos_sig_chunks (r : CRun th) {k j : node} {m : merkle_root}
    (hk : ¬ nset.is_byz k = true) :
    ∀ n, (r.at' n).msg_fb_pos_sig k j m = true → ∀ i, (r.at' n).msg_chunk k i j m = true :=
  record_backed r (F := fun st => st.msg_fb_pos_sig k j m = true)
    (Q := fun st => ∀ i, st.msg_chunk k i j m = true)
    (by simp [Chorus.msg_fb_pos_sig.init r.starts k j m])
    (fun n h0 h1 => fb_pos_sig_chunks_flip (r.steps n) hk h0 h1)
    (fun n h i => Chorus.msg_chunk.mono (r.steps n) k i j m (h i))

/-- The fallback-commit record comes with a fallback commit vote. -/
theorem fbcommit_voted_sig (r : CRun th) {i : node} :
    ∀ n, (r.at' n).local_fbcommit_voted i = true → ∃ e, (r.at' n).msg_fbcommit_sig i e = true :=
  record_backed r (F := fun st => st.local_fbcommit_voted i = true)
    (Q := fun st => ∃ e, st.msg_fbcommit_sig i e = true)
    (by simp [Chorus.local_fbcommit_voted.init r.starts i])
    (fun n h0 h1 => fbcommit_voted_flip (r.steps n) h0 h1)
    (fun n ⟨e, h⟩ => ⟨e, Chorus.msg_fbcommit_sig.mono (r.steps n) i e h⟩)

/-- A certificate-sent record comes with a valid MVBA commit certificate the
validator sent. -/
theorem mvba_cert_sent_msg (r : CRun th) {i : node} :
    ∀ n, (r.at' n).local_mvba_cert_sent i = true →
      ∃ c e, mvba.certifies (r.at' n).mvba_st c e ∧ (r.at' n).msg_mvba_cert i c = true :=
  record_backed r (F := fun st => st.local_mvba_cert_sent i = true)
    (Q := fun st => ∃ c e, mvba.certifies st.mvba_st c e ∧ st.msg_mvba_cert i c = true)
    (by simp [Chorus.local_mvba_cert_sent.init r.starts i])
    (fun n h0 h1 => mvba_cert_sent_flip (Chorus.reachable_mvba_reachable (r.reachable n))
      (r.steps n) h0 h1)
    (fun n ⟨c, e, hc, h⟩ => ⟨c, e, certifies_step (r.steps n) hc,
      Chorus.msg_mvba_cert.mono (r.steps n) i c h⟩)

/-- **A correct validator's MVBA commit certificate is valid**, at every point
of the run (`mvba_cert_flip`; a valid certificate stays valid). -/
theorem mvba_cert_valid (r : CRun th) {i : node} {c : mmsg} (hi : ¬ nset.is_byz i = true) :
    ∀ n, (r.at' n).msg_mvba_cert i c = true → ∃ e, mvba.certifies (r.at' n).mvba_st c e :=
  record_backed r (F := fun st => st.msg_mvba_cert i c = true)
    (Q := fun st => ∃ e, mvba.certifies st.mvba_st c e)
    (by simp [Chorus.msg_mvba_cert.init r.starts i c])
    (fun n h0 h1 => mvba_cert_flip (Chorus.reachable_mvba_reachable (r.reachable n))
      (r.steps n) hi h0 h1)
    (fun n ⟨e, h⟩ => ⟨e, certifies_step (r.steps n) h⟩)

/-- A collector's fallback record comes with a fallback commit certificate
it sent. -/
theorem fbcommitqc_sent_msg (r : CRun th) {c : node} :
    ∀ n, (r.at' n).local_fbcommitqc_sent c = true → ∃ e, (r.at' n).msg_fbcommitqc c e = true :=
  record_backed r (F := fun st => st.local_fbcommitqc_sent c = true)
    (Q := fun st => ∃ e, st.msg_fbcommitqc c e = true)
    (by simp [Chorus.local_fbcommitqc_sent.init r.starts c])
    (fun n h0 h1 => fbcommitqc_sent_flip (r.steps n) h0 h1)
    (fun n ⟨e, h⟩ => ⟨e, Chorus.msg_fbcommitqc.mono (r.steps n) c e h⟩)

/-- **Saturation** of one validator — the `hsat` shape of
`progress_dichotomy_of_saturation`: it has cast its fast commit vote with a
commit signature for every proposer, or its fallback vote with a fallback
signature for every proposer. -/
def Saturated (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (i : node) : Prop :=
  (st.msg_commit_cast i = true ∧ ∀ j, th.is_proposer j = true →
    (∃ m, st.msg_commit_pos_sig i j m = true) ∨ st.msg_commit_neg_sig i j = true) ∨
  (st.msg_fallback_sig i = true ∧ ∀ j, th.is_proposer j = true →
    (∃ m, st.msg_fb_pos_sig i j m = true) ∨ st.msg_fb_neg_sig i j = true)

/-- Saturation is monotone along every step: every relation in it is. -/
theorem Saturated.step
    {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}
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
def AtArm (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) :
    Prop :=
  st.phase = Phase_EnumClass.post_fb_arm ∨ st.phase = Phase_EnumClass.post_mvba_arm

omit [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited mstate] [Inhabited mvalue] [Inhabited mentries] [Inhabited mmsg] [Inhabited Phase] [Inhabited PathChoice]
  PathChoice_Enum in
theorem AtArm.ne_pre
    {st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}
    (h : AtArm st) : st.phase ≠ Phase_EnumClass.pre_deadline := by
  obtain ⟨-, d2, d3, -, -, -⟩ := phase_distinct (Phase := Phase)
  rcases h with h | h <;> rw [h]
  · exact d2.symm
  · exact d3.symm

/-- Past the deadline stays past the deadline. -/
theorem phase_ne_pre_step
    {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}
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
    {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}
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

/-- `i` holds an entry of `a`'s vote for `j`: a vote receipt. -/
def Received (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (i a j : node) : Prop :=
  (∃ m, st.local_vote_rcv_pos i a j m = true) ∨ st.local_vote_rcv_neg i a j = true

theorem Received.step
    {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}
    {l} (htr : (RTS).tr th s l s') {i a j : node} (h : Received s i a j) : Received s' i a j :=
  h.imp (fun ⟨m, hm⟩ => ⟨m, Chorus.local_vote_rcv_pos.mono htr i a j m hm⟩)
    (Chorus.local_vote_rcv_neg.mono htr i a j)

/-- **A correct validator receives every correct voter's vote.** Once a
correct `a` has cast its vote, the vote passes the receiver's check and
carries an entry for every proposer (`vote_cast_valid`), and taking it is
owed (its sender is correct) and enabled at `i` until `i` holds an entry
of `a`'s vote for `j`. -/
theorem eventually_received (r : CRun th) (hfj : PerLabel r)
    {A : Nat} (hact : ActiveFrom r A)
    {i a j : node} (hi : ¬ nset.is_byz i = true) (ha : ¬ nset.is_byz a = true)
    (hj : th.is_proposer j = true) : ∃ N, Received (r.at' N) i a j := by
  obtain ⟨Nv, hNv⟩ := eventually_voted r hfj hact ha
  have hcast : ∀ n, Nv ≤ n → (r.at' n).msg_vote_cast a = true := fun n hn =>
    r.mono (P := fun st => st.msg_vote_cast a = true)
      (fun m hm => Chorus.msg_vote_cast.mono (r.steps m) a hm)
      (Chorus.reachable_voted_implies_cast (r.reachable Nv) a ⟨ha, hNv⟩) n hn
  by_contra hcon
  have hnp : ∀ n m2, ¬ (r.at' n).local_vote_rcv_pos i a j m2 = true :=
    fun n m2 h => hcon ⟨n, Or.inl ⟨m2, h⟩⟩
  have hnn : ∀ n, ¬ (r.at' n).local_vote_rcv_neg i a j = true :=
    fun n h => hcon ⟨n, Or.inr h⟩
  have hval : ∀ n, Nv ≤ n → Chorus.vote_valid a th (r.at' n) := fun n hn =>
    correct_vote_valid (r.reachable n) ha (hcast n hn)
  rcases vote_valid_entry (hval Nv le_rfl) hj with ⟨m, hm, hch, hps⟩ | hm
  · obtain ⟨n, -, hfire⟩ := (hfj (.receive_vote_pos i a j m) ⟨fun h => h, fun h => h, fun h => h⟩
        (fun h => h)).fires Nv (fun _ _ => ha)
      (fun n hn => enabled_receive_vote_pos hi hj (hval n hn)
        (r.mono (P := fun st => st.msg_vote_pos_sig a j m = true)
          (fun k hk => msg_vote_pos_sig_mono (r.steps k) a j m hk) hm n hn)
        (r.mono (P := fun st => st.msg_vote_chunk a j m = true)
          (fun k hk => msg_vote_chunk_mono (r.steps k) a j m hk) hch n hn)
        (r.mono (P := fun st => st.msg_proposer_signed j m = true)
          (fun k hk => Chorus.msg_proposer_signed.mono (r.steps k) j m hk) hps n hn)
        (hnp n) (hnn n))
    exact hnp (n + 1) m (receive_vote_pos_effect (hfire ▸ r.steps n))
  · obtain ⟨n, -, hfire⟩ := (hfj (.receive_vote_neg i a j) ⟨fun h => h, fun h => h, fun h => h⟩
        (fun h => h)).fires Nv (fun _ _ => ha)
      (fun n hn => enabled_receive_vote_neg hi hj (hval n hn)
        (r.mono (P := fun st => st.msg_vote_neg_sig a j = true)
          (fun k hk => msg_vote_neg_sig_mono (r.steps k) a j hk) hm n hn)
        (hnp n) (hnn n))
    exact hnn (n + 1) (receive_vote_neg_effect (hfire ▸ r.steps n))

/-- **Every correct validator is eventually saturated.** The chain of
[Liveness.md](../../docs/Liveness.md) §4.4: the phase reaches an arm, `i` votes, an honest
quorum's votes are on the network and `i` receives each of them
(`eventually_received`); then, unless `i` saturates, each proposer gets a
fallback signature from `i` — `fb_sign_pos` once positive evidence appears
among the votes `i` received (receipts are monotone, so the label stays
enabled), `fb_sign_neg` against the honest quorum if it never does (the
absence of that evidence *is* its guard) — and `cast_fallback_vote i` fires.
While `i` has no signature for a proposer it has not signed an entry for it
either (`fb_entry_sigs`), so the fired-once guard holds throughout. Every
step either fires or is disabled by `i` casting a path vote, which saturates
it by the first-flip facts. -/
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
  -- From `N0` on: at an arm, `i` has voted, the honest quorum's votes are cast.
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
    -- `i` holds an entry of every vote of `qv` for `j`, at one index and ever after.
    obtain ⟨Nr, hNr, hrall⟩ := r.eventually_forall
      (fun a st => nset.member a qv = true → Received st i a j)
      (fun a n h hm => (h hm).step (r.steps n)) (max A (max Na (max Nv Nq))) nodes
      (fun a _ => by
        by_cases hm : nset.member a qv = true
        · obtain ⟨n, hn⟩ := eventually_received r hfj hact hi (hqvh a hm) hj
          exact ⟨max (max A (max Na (max Nv Nq))) n, by omega, fun _ =>
            r.mono (P := fun st => Received st i a j) (fun k h => h.step (r.steps k)) hn _ (by omega)⟩
        · exact ⟨max A (max Na (max Nv Nq)), Nat.le_refl _, fun h => absurd h hm⟩)
    have hrcv : ∀ n, Nr ≤ n → ∀ a, nset.member a qv = true → Received (r.at' n) i a j :=
      fun n hn a ha => r.mono (P := fun st => Received st i a j)
        (fun k h => h.step (r.steps k)) (hrall a (hnodes a) ha) n hn
    by_contra hns
    by_cases hpos : ∃ n, Nr ≤ n ∧ ∃ M q, nset.greater_than_third q ∧
        (∀ a, nset.member a q = true → nset.member a qv = true ∧ (r.at' n).local_vote_rcv_pos i a j M = true) ∧
        th.well_encoded M = true
    · -- Positive evidence among the received votes: it persists, and the
      -- receipts are backed by the senders' signatures, so `fb_sign_pos` stays
      -- enabled. Its voters are the honest quorum's, so it is owed.
      obtain ⟨n0, hn0, M, q, hq1, hq2, hwe⟩ := hpos
      have hQ : Mvba.CorrectQuorum (node := node) q := fun a ha => hqvh a (hq2 a ha).1
      have hsig : ∀ n, n0 ≤ n → ∀ a, nset.member a q = true → (r.at' n).msg_vote_pos_sig a j M = true :=
        fun n hn a ha => r.mono (P := fun st => st.msg_vote_pos_sig a j M = true)
          (fun m hm => msg_vote_pos_sig_mono (r.steps m) a j M hm)
          (Chorus.reachable_vote_rcv_pos_backed (r.reachable n0) i a j M ⟨hi, (hq2 a ha).2⟩).2 n hn
      obtain ⟨n, hn, hfire⟩ := (hfj (.fb_sign_pos i j M q) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).fires n0
        (fun n hn => ⟨hQ, qv, hqv, hqvh, hq n (by omega)⟩)
        (fun n hn => (enabled_fb_sign_pos hi (hact n (by omega) i hi) (harm n (by omega)) (hv n (by omega)) (hnc n) (hnp n) hj
          hqv (fun a ha => correct_vote_valid (r.reachable n) (hqvh a ha) (hq n (by omega) a ha)) hq1
          (let ⟨a0, ha0, _⟩ := nset.greater_than_third_one_honest q hq1
           (correct_vote_pos (r.reachable n) (hqvh a0 (hq2 a0 ha0).1) (hsig n hn a0 ha0)).2)
          (fun a ha => ⟨hsig n hn a ha,
            (correct_vote_pos (r.reachable n) (hqvh a (hq2 a ha).1) (hsig n hn a ha)).1,
            correct_vote_valid (r.reachable n) (hqvh a (hq2 a ha).1) (hq n (by omega) a (hq2 a ha).1)⟩)
          hwe fun h => hns ⟨n, by omega, fb_entry_sigs r n h⟩))
      exact hns ⟨n + 1, by omega, Or.inl ⟨M, fb_sign_pos_effect (hfire ▸ r.steps n)⟩⟩
    · -- It never appears: that absence, over the votes of `qv` that `i`
      -- holds, is `fb_sign_neg`'s guard against `qv`, a correct quorum.
      obtain ⟨n, hn, hfire⟩ := (hfj (.fb_sign_neg i j qv) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).fires
        Nr (fun _ _ => hqvh)
        (fun n hn => (enabled_fb_sign_neg hi (hact n (by omega) i hi) (harm n (by omega)) (hv n (by omega)) (hnc n) (hnp n) hj
          hqv (hrcv n hn) (fun M q hh => hpos ⟨n, hn, M, q, hh⟩)
          fun h => hns ⟨n, by omega, fb_entry_sigs r n h⟩))
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

/-- **A correct validator's committed positive entry comes with the proof it
re-broadcast, at every point of every run**: the first-flip step was one of
its routes `commit_assign_pos_*` (`committed_pos_flip`), and the proof
persists (`certPos_step`). -/
theorem committed_pos_cert (r : CRun th) {i j : node} {m : merkle_root} :
    ∀ n, (r.at' n).local_committed_pos i j m = true → CertPos (mvba := mvba) th (r.at' n) i j m :=
  record_backed r (F := fun st => st.local_committed_pos i j m = true)
    (Q := fun st => CertPos (mvba := mvba) th st i j m)
    (by simp [Chorus.local_committed_pos.init r.starts i j m])
    (fun n h0 h1 => committed_pos_flip (r.steps n) h0 h1)
    (fun n h => certPos_step (r.steps n) h)

/-- **A committed negative entry comes with the proof it re-broadcast**,
likewise. -/
theorem committed_neg_cert (r : CRun th) {i j : node} :
    ∀ n, (r.at' n).local_committed_neg i j = true → CertNeg (mvba := mvba) th (r.at' n) i j :=
  record_backed r (F := fun st => st.local_committed_neg i j = true)
    (Q := fun st => CertNeg (mvba := mvba) th st i j)
    (by simp [Chorus.local_committed_neg.init r.starts i j])
    (fun n h0 h1 => committed_neg_flip (r.steps n) h0 h1)
    (fun n h => certNeg_step (r.steps n) h)

/-- **The commit route, from commitment proofs.** From an index at which
every proposer's entry has a commitment proof from a correct sender
(`CertPos`/`CertNeg` at a correct `c`), every correct validator eventually
has `local_committed`. Taking the proof is owed (its sender is correct) and
enabled: the route that reads the proof's form requires nothing else of a
validator that has assigned nothing for the proposer. No invariant is used.

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
      (∃ m c, ¬ nset.is_byz c = true ∧ CertPos (mvba := mvba) th (r.at' N) c j m) ∨
      (∃ c, ¬ nset.is_byz c = true ∧ CertNeg (mvba := mvba) th (r.at' N) c j))
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
    -- The proof's form persists, and the route that reads it stays enabled.
    rcases hA j hj with ⟨m, c, hc, hq | ⟨e, he, hme⟩ | ⟨cc, v, hmsg, hcert, hv, hb⟩⟩ |
        ⟨c, hc, hq | ⟨e, he, hme⟩ | ⟨cc, v, hmsg, hcert, hv, hb⟩⟩
    · have hq' := r.mono (P := fun st => st.msg_commitqc_pos c j m = true)
        (fun k h => Chorus.msg_commitqc_pos.mono (r.steps k) c j m h) hq
      obtain ⟨n, hn, hfire⟩ := (hfj (.commit_assign_pos_fast i j m c) ⟨fun h => h, fun h => h, fun h => h⟩
          (fun h => h)).fires (max N P) (fun _ _ => hc)
        (fun n hn => enabled_commit_assign_pos_fast hi (hact n (by omega)) (hnc n) hj
          (hq' n (by omega)) (hnp n (by omega)) (hnn n (by omega)))
      exact hna ⟨n + 1, by omega, Or.inl ⟨m, (commit_assign_pos_fast_effect (hfire ▸ r.steps n)).1⟩⟩
    · have he' := r.mono (P := fun st => st.msg_fbcommitqc c e = true)
        (fun k h => Chorus.msg_fbcommitqc.mono (r.steps k) c e h) he
      obtain ⟨n, hn, hfire⟩ := (hfj (.commit_assign_pos_fb i j m c e) ⟨fun h => h, fun h => h, fun h => h⟩
          (fun h => h)).fires (max N P) (fun _ _ => hc)
        (fun n hn => enabled_commit_assign_pos_fb hi (hact n (by omega)) (hnc n) hj
          (he' n (by omega)) hme (hnp n (by omega)) (hnn n (by omega)))
      exact hna ⟨n + 1, by omega, Or.inl ⟨m, (commit_assign_pos_fb_effect (hfire ▸ r.steps n)).1⟩⟩
    · have hall := r.mono (P := fun st => st.msg_mvba_cert c cc = true ∧
          mvba.certifies st.mvba_st cc (mvba.entries v) ∧
          ((¬ th.mval_fb v j = true ∧ Chorus.vote_quorum_pos j m th st) ∨
            (th.mval_fb v j = true ∧ Chorus.fb_quorum_pos j m th st ∧ Chorus.fbcert th st)))
        (fun k ⟨h1, h2, h3⟩ => ⟨Chorus.msg_mvba_cert.mono (r.steps k) c cc h1,
          certifies_step (r.steps k) h2, bridge_pos_step (r.steps k) h3⟩) ⟨hmsg, hcert, hb⟩
      obtain ⟨n, hn, hfire⟩ := (hfj (.commit_assign_pos_mvba i j m c cc v) ⟨fun h => h, fun h => h, fun h => h⟩
          (fun h => h)).fires (max N P) (fun _ _ => hc)
        (fun n hn => enabled_commit_assign_pos_mvba hi (hact n (by omega)) (hnc n) hj
          (hall n (by omega)).1 (hall n (by omega)).2.1 hv (hall n (by omega)).2.2
          (hnp n (by omega)) (hnn n (by omega)))
      exact hna ⟨n + 1, by omega, Or.inl ⟨m, (commit_assign_pos_mvba_effect (hfire ▸ r.steps n)).1⟩⟩
    · have hq' := r.mono (P := fun st => st.msg_commitqc_neg c j = true)
        (fun k h => Chorus.msg_commitqc_neg.mono (r.steps k) c j h) hq
      obtain ⟨n, hn, hfire⟩ := (hfj (.commit_assign_neg_fast i j c) ⟨fun h => h, fun h => h, fun h => h⟩
          (fun h => h)).fires (max N P) (fun _ _ => hc)
        (fun n hn => enabled_commit_assign_neg_fast hi (hact n (by omega)) (hnc n) hj
          (hq' n (by omega)) (hnp n (by omega)) (hnn n (by omega)))
      exact hna ⟨n + 1, by omega, Or.inr (commit_assign_neg_fast_effect (hfire ▸ r.steps n)).1⟩
    · have he' := r.mono (P := fun st => st.msg_fbcommitqc c e = true)
        (fun k h => Chorus.msg_fbcommitqc.mono (r.steps k) c e h) he
      obtain ⟨n, hn, hfire⟩ := (hfj (.commit_assign_neg_fb i j c e) ⟨fun h => h, fun h => h, fun h => h⟩
          (fun h => h)).fires (max N P) (fun _ _ => hc)
        (fun n hn => enabled_commit_assign_neg_fb hi (hact n (by omega)) (hnc n) hj
          (he' n (by omega)) hme (hnp n (by omega)) (hnn n (by omega)))
      exact hna ⟨n + 1, by omega, Or.inr (commit_assign_neg_fb_effect (hfire ▸ r.steps n)).1⟩
    · have hall := r.mono (P := fun st => st.msg_mvba_cert c cc = true ∧
          mvba.certifies st.mvba_st cc (mvba.entries v) ∧
          (Chorus.vote_quorum_neg j th st ∨
            ((Chorus.fb_quorum_neg j th st ∨ Chorus.equiv_evidence j th st) ∧ Chorus.fbcert th st)))
        (fun k ⟨h1, h2, h3⟩ => ⟨Chorus.msg_mvba_cert.mono (r.steps k) c cc h1,
          certifies_step (r.steps k) h2, bridge_neg_step (r.steps k) h3⟩) ⟨hmsg, hcert, hb⟩
      obtain ⟨n, hn, hfire⟩ := (hfj (.commit_assign_neg_mvba i j c cc v) ⟨fun h => h, fun h => h, fun h => h⟩
          (fun h => h)).fires (max N P) (fun _ _ => hc)
        (fun n hn => enabled_commit_assign_neg_mvba hi (hact n (by omega)) (hnc n) hj
          (hall n (by omega)).1 (hall n (by omega)).2.1 hv (hall n (by omega)).2.2
          (hnp n (by omega)) (hnn n (by omega)))
      exact hna ⟨n + 1, by omega, Or.inr (commit_assign_neg_mvba_effect (hfire ▸ r.steps n)).1⟩
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
proposer (`local_committed_complete`), and each commitment re-broadcast its
proof under its own name (`committed_pos_cert`, `committed_neg_cert`). -/
theorem proofs_of_finalized (r : CRun th) {n : Nat} {i0 : node}
    (hi0 : ¬ nset.is_byz i0 = true) (hc : (r.at' n).local_committed i0 = true) :
    ∀ j, th.is_proposer j = true →
      (∃ m c, ¬ nset.is_byz c = true ∧ CertPos (mvba := mvba) th (r.at' n) c j m) ∨
      (∃ c, ¬ nset.is_byz c = true ∧ CertNeg (mvba := mvba) th (r.at' n) c j) := by
  intro j hj
  rcases Chorus.reachable_local_committed_complete (r.reachable n) i0 ⟨hi0, hc⟩ j hj with ⟨m, hm⟩ | hm
  · exact Or.inl ⟨m, i0, hi0, committed_pos_cert r n hm⟩
  · exact Or.inr ⟨i0, hi0, committed_neg_cert r n hm⟩

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
held by a `FastQC` if its vote quorum is there and by a `FallbackQC`
otherwise, and `⊥` where none exists. -/
noncomputable def certifiedVector
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)) :
    MetaBlock node merkle_root := fun j =>
  if h : thS.is_proposer j = true ∧ ∃ m,
      Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS st ∨
      (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS st ∧
        Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS st)
  then some (h.2.choose,
    if Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j h.2.choose thS st then CertKind.fastQC else CertKind.fallbackQC)
  else none

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
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
  {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)}

/-- The `MVBASafety` instance the composed system runs, as a local instance
for the generic step lemmas. -/
local macro "mvba_inst" : tactic =>
  `(tactic| letI : MVBASafety node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset nset (fun i => nset.is_byz i = true) := Mvba.mvbaSafety thM)

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
    (P : Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view) → Prop)
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
    {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)}
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
    · rcases (mvbaStepLabel_iff _).1 hs with ⟨m, hm⟩ | ⟨j, v, m, hm⟩ | ⟨j, m, hm⟩ | ⟨j, r₀, c, m, hm⟩ |
          ⟨j, v, m, hm⟩
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
      · obtain ⟨w, e, x, _, -, -, htr⟩ := accept_mvba_commitqc_tr (hm ▸ r.steps n)
        have := Mvba.decide.frame_abandoned htr
        rw [this] at h
        exact absurd h hprev
      · have := Mvba.become_avail_ready.frame_abandoned (mvba_avail_ready_tr (hm ▸ r.steps n))
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
    {st : Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)}
    {i : node} {v : MetaBlock node merkle_root}
    (hin : ∀ E, ¬ st.input i E = true) (hab : ¬ st.abandoned i = true) (hv : thM.valid v = true) :
    ∃ st', (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      st (.propose i v) st' := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
  exact ⟨_, hin, hab, hv, rfl⟩

/-- A decision of the MVBA stands in the composed run. -/
theorem decided_persists (r : ChorusRun (nset := nset) thS thM) {i : node}
    {v : MetaBlock node merkle_root} {k : Nat}
    (hd : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k).mvba_st i v) :
    ∀ n, k ≤ n → (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st i v :=
  r.mono (P := fun st => (Mvba.mvbaSafety (nset := nset) thM).decided st.mvba_st i v)
    (fun n h => mvba_st_step r _ (fun _ _ _ htr h => Mvba.decided_mono_tr thM htr i v h) n h) hd

/-- A decision's output certificate stands along the run. -/
theorem decidedCert_persists (r : ChorusRun (nset := nset) thS thM)
    {k : Nat} {j : node} {c : Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)}
    (hc : (Mvba.mvbaSafety (nset := nset) thM).decidedCert (r.at' k).mvba_st j c) :
    ∀ n, k ≤ n → (Mvba.mvbaSafety (nset := nset) thM).decidedCert (r.at' n).mvba_st j c :=
  r.mono (P := fun st => (Mvba.mvbaSafety (nset := nset) thM).decidedCert st.mvba_st j c)
    (fun n h => mvba_st_step r _ (fun _ _ _ htr h => Mvba.decidedCert_mono_tr thM htr j c h) n h) hc

/-- A valid MVBA certificate stands in the composed run. -/
theorem certifies_persists (r : ChorusRun (nset := nset) thS thM)
    {c : Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)}
    {e : node → Option merkle_root} {k : Nat}
    (hc : (Mvba.mvbaSafety (nset := nset) thM).certifies (r.at' k).mvba_st c e) :
    ∀ n, k ≤ n → (Mvba.mvbaSafety (nset := nset) thM).certifies (r.at' n).mvba_st c e :=
  r.mono (P := fun st => (Mvba.mvbaSafety (nset := nset) thM).certifies st.mvba_st c e)
    (fun n h => mvba_st_step r _ (fun _ _ _ htr h => Mvba.certifies_mono_tr thM htr c e h) n h) hc

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
      case commitqc w e =>
        have h' : Mvba.Accept thM (r.at' n).mvba_st i (.commitqc w e) (r.at' (n + 1)).mvba_st := hc
        obtain ⟨_, x, -, h''⟩ := h'
        exact ⟨x, Mvba.decide_effect h''⟩
      all_goals exact (hc : False).elim

omit [Inhabited merkle_root] in
/-- `decide`'s guards, read off an enabled `decide`: a correct validator that
has not decided. -/
theorem decide_enabled_guards
    {st : Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)}
    {i s₀ : node} {v : view} {e : MetaBlock node merkle_root}
    (h : Enabled (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)) thM
      st (.decide i s₀ v e)) :
    ¬ nset.is_byz i = true ∧ ∀ E, ¬ st.decided i E = true := by
  obtain ⟨st', htr⟩ := h
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp] at htr
  obtain ⟨h1, -, -, -, -, h6, -⟩ := htr
  exact ⟨h1, h6⟩

omit [Inhabited merkle_root] in
/-- `decide`'s other two guards: the validator has proposed and has not
abandoned. -/
theorem decide_enabled_live
    {st : Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)}
    {i s₀ : node} {v : view} {e : MetaBlock node merkle_root}
    (h : Enabled (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)) thM
      st (.decide i s₀ v e)) :
    (∃ E, Mvba.Proposed st i E) ∧ ¬ Mvba.Abandoned st i := by
  obtain ⟨st', htr⟩ := h
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp] at htr
  obtain ⟨-, h2, h3, -, -, -, -⟩ := htr
  exact ⟨h2, h3⟩

/-- **A correct, active decider sends its commit certificate** (the
supplement's "Decision output and handoff"): `send_mvba_cert` is enabled
with the certificate its decision outputs (`decided_certified`, a
`decidedCert` at its own index, which stands) until it has
sent one, and it is owed unconditionally, as a rule on the validator's own
decision. -/
theorem eventually_cert_sent (r : ChorusRun (nset := nset) thS thM) (hfj : PerLabel r)
    {A : Nat} (hact : ActiveFrom r A) {j : node} (hj : ¬ nset.is_byz j = true)
    {k : Nat} {v : MetaBlock node merkle_root}
    (hd : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k).mvba_st j v) :
    ∃ n c e, (Mvba.mvbaSafety (nset := nset) thM).certifies (r.at' n).mvba_st c e ∧
      (r.at' n).msg_mvba_cert j c = true := by
  mvba_inst
  have hdec := decided_persists r hd
  obtain ⟨c, hc⟩ := (Mvba.mvbaSafety (nset := nset) thM).decided_certified _
    (Chorus.reachable_mvba_reachable (r.reachable k)) j v hj hd
  have hc' := decidedCert_persists r hc
  have _ := hdec
  by_contra hcon
  have hns : ∀ n, ¬ (r.at' n).local_mvba_cert_sent j = true :=
    fun n h => hcon (let ⟨c, e, h1, h2⟩ := mvba_cert_sent_msg r n h; ⟨n, c, e, h1, h2⟩)
  obtain ⟨n, -, hfire⟩ := (hfj (.send_mvba_cert j c) ⟨fun h => h, fun h => h, fun h => h⟩
      (fun h => h)).of_forall (fun _ => trivial) (max k A)
    (fun n hn => enabled_send_mvba_cert hj (hact n (by omega) j hj) (hc' n (by omega)) (hns n))
  exact hns (n + 1) (send_mvba_cert_effect (hfire ▸ r.steps n)).2

/-- **(F-relay) is derived, not assumed**: on every projection of a run
satisfying `FJustice` in which every correct validator is active from some
index on, the MVBA's caller hands decided certificates on. If `decide i v e`
stayed enabled in the projected run while a correct validator `j` had
decided `e`, then `j` would send its commit certificate
(`eventually_cert_sent`), the handoff from a correct sender would be owed to
`i` and enabled (`accept_enabled`: `i` has proposed, is not abandoned and
has not decided), so `FJustice`'s handoff family would fire, `i` would
decide, and `decide i v e` would be disabled after all. So the premise holds
with its antecedent false. -/
theorem fRelay_of_fJustice (r : ChorusRun (nset := nset) thS thM) (hfj : FJustice r)
    {A : Nat} (hact : ActiveFrom r A)
    (p : (mvbaComponent thS thM).Projection r) : Mvba.FRelay p.run := by
  mvba_inst
  intro i j₀ v e K hen
  exfalso
  have hi := (decide_enabled_guards (hen K le_rfl).2).1
  -- Read the antecedent at the composed indices from `idx K` on.
  have htrans : ∀ n, (mvbaComponent thS thM).idx r K ≤ n →
      (¬ nset.is_byz j₀ = true ∧ (r.at' n).mvba_st.decided j₀ e = true) ∧
      Enabled (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)) thM
        (r.at' n).mvba_st (.decide i j₀ v e) := fun n hn => by
    have hk := hen ((mvbaComponent thS thM).cover r n) (p.scheduled.le_cover_of_idx_le hn)
    rw [← p.proj_eq_run_cover n] at hk
    exact hk
  -- The decider sends a certificate, which stays valid and on the network.
  obtain ⟨hj, hdj⟩ := (htrans _ le_rfl).1
  set j := j₀
  obtain ⟨n1, c, e1, hc1, hm1⟩ := eventually_cert_sent r hfj.1 hact hj (v := e) hdj
  have hc : ∀ n, n1 ≤ n → (Mvba.mvbaSafety (nset := nset) thM).certifies (r.at' n).mvba_st c e1 :=
    certifies_persists r hc1
  have hm : ∀ n, n1 ≤ n → (r.at' n).msg_mvba_cert j c = true :=
    r.mono (P := fun st => st.msg_mvba_cert j c = true)
      (fun k h => Chorus.msg_mvba_cert.mono (r.steps k) j c h) hm1
  obtain ⟨m, hm', r', c', mn, hl⟩ := (hfj.2.2.1 i).fires (max ((mvbaComponent thS thM).idx r K) n1)
    (fun n hn => ⟨j, c, hj, hm n (by omega)⟩)
    (fun n hn => by
      have hen' := (htrans n (by omega)).2
      obtain ⟨hin, hab⟩ := decide_enabled_live hen'
      obtain ⟨st', hacc⟩ := Mvba.accept_enabled_tr thM
        (Chorus.reachable_mvba_reachable (r.reachable n)) hi (hc n (by omega)) hin hab
        (fun v' h => (decide_enabled_guards hen').2 v' h)
      refine ⟨_, ⟨j, c, st', rfl⟩, enabled_accept_mvba_commitqc hi (fun hf => ?_) (hm n (by omega)) hacc⟩
      obtain ⟨w, hw⟩ := qc_accepted_decided r n hf
      exact (decide_enabled_guards hen').2 w hw)
  obtain ⟨w, e', x, s', -, -, htr⟩ := accept_mvba_commitqc_tr (hl ▸ r.steps m)
  exact (decide_enabled_guards (htrans (m + 1) (by omega)).2).2 x (Mvba.decide_effect htr)

/-- Certification is monotone: every certificate in it is. -/
theorem Certified.step {l}
    (htr : (atMvba (nset := nset) (slot := slot) (Phase := Phase) (PathChoice := PathChoice) thM).tr thS s l s')
    {v : MetaBlock node merkle_root}
    (h : Certified (thS := thS) (thM := thM) s v) : Certified (thS := thS) (thM := thM) s' v := by
  mvba_inst
  obtain ⟨hp, hn, ha⟩ := h
  refine ⟨fun J M hJ => ?_, fun J hJ => ?_, ha⟩
  · obtain ⟨hpr, hc⟩ := hp J M hJ
    exact ⟨hpr, hc.imp (fun ⟨a, b⟩ => ⟨a, vote_quorum_pos_step htr b⟩)
      fun ⟨a, b, c⟩ => ⟨a, fb_quorum_pos_step htr b, fbcert_step htr c⟩⟩
  · obtain ⟨hpr, hc⟩ := hn J hJ
    exact ⟨hpr, hc.imp (vote_quorum_neg_step htr)
      fun ⟨a, b⟩ => ⟨a.imp (fb_quorum_neg_step htr) (equiv_evidence_step htr), fbcert_step htr b⟩⟩

/-- **A validator's availability record comes with its `AvailReady`**, at
every point of the composed run. -/
theorem avail_marked_ready (r : ChorusRun (nset := nset) thS thM) {i : node} {v : MetaBlock node merkle_root} :
    ∀ n, (r.at' n).local_avail_marked i v = true → (r.at' n).mvba_st.avail_ready i v = true := by
  mvba_inst
  refine record_backed r (F := fun st => st.local_avail_marked i v = true)
    (Q := fun st => st.mvba_st.avail_ready i v = true)
    (by simp [Chorus.local_avail_marked.init r.starts i v]) (fun n h0 h1 => avail_marked_flip (r.steps n) h0 h1) ?_
  intro n h
  exact mvba_st_step r (fun st => st.avail_ready i v = true)
    (fun _ _ _ htr h => Mvba.avail_ready.mono htr i v h) n h

set_option maxHeartbeats 1000000 in
/-- **(F-avail), derived**: the MVBA's availability premise holds of the
projection of every composed run satisfying (F-justice) and the bridge,
once every correct validator is active. It is the caller's premise, and
the caller is Chorus: `AvailReady_i(x)` is the dissemination layer's
predicate (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Commit
availability condition"), which Chorus reports by `mvba_avail_ready`.

A correct validator `i` that accepted `x` waits for its assigned chunk under
every positive `FallbackQC` entry of `x`. Those certificates are on the
network (`ValidBridge`'s completeness at an accepted value), so each has a
correct signer, which decoded the proposal and, in the same step, sent `i`
its chunk (Algorithm 5, line 12 (`line:fb-redisseminate`)). So the wait is
met from the acceptance on, the report is enabled until `i` is `AvailReady`
for `x`, and it is owed, so it fires. No validator needs to be active: the
signer's send happened when it signed. -/
theorem fAvail_of_fJustice (r : ChorusRun (nset := nset) thS thM) (hfj : FJustice r)
    (hbr : ValidBridge r) (p : (mvbaComponent thS thM).Projection r) : Mvba.FAvail p.run := by
  mvba_inst
  intro i k V w hi hacc
  -- The acceptance, at the composed run's index.
  have hacc' : (r.at' ((mvbaComponent thS thM).idx r k)).mvba_st.accepted i V w = true := hacc
  set kd := (mvbaComponent thS thM).idx r k
  -- `x`'s certificates are on the network (the bridge's completeness).
  have hcert : ∀ n, kd ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) w :=
    r.mono (P := fun st => Certified (thS := thS) (thM := thM) st w)
      (fun n h => Certified.step (r.steps n) h) (hbr.2.2 kd i V w hi hacc')
  -- `i` still holds `w` later: acceptance persists.
  have haccp : ∀ n, kd ≤ n → (r.at' n).mvba_st.accepted i V w = true :=
    r.mono (P := fun st => st.mvba_st.accepted i V w = true)
      (fun n h => mvba_st_step r (fun st => st.accepted i V w = true)
        (fun _ _ _ htr h => Mvba.accepted.mono htr i V w h) n h) hacc'
  -- The wait under each FallbackQC entry of `w` is met from the acceptance
  -- on: the entry's FallbackQC has a correct signer, which sent every
  -- validator its chunk when it signed (`fb_pos_sig_chunks`).
  have hda : ∀ n, kd ≤ n → ∀ J M, thS.mval_pos (thM.ent w) J M = true → thS.mval_fb w J = true →
      Chorus.chunk_received (nset := nset) (mvba := Mvba.mvbaSafety thM) i J M thS (r.at' n) :=
      fun n hn J M hM hfb => by
    obtain ⟨-, hkind⟩ := (hcert n hn).1 J M hM
    obtain ⟨q, hq, hallq⟩ := (hkind.resolve_left fun h => h.1 hfb).2.1
    obtain ⟨k, hkq, hkh⟩ := ByzNodeSet.greater_than_third_one_honest q hq
    exact ⟨k, fb_pos_sig_chunks r hkh n (hallq k hkq) i⟩
  -- Read the conclusion back at the projection.
  suffices h : ∃ n, (r.at' n).mvba_st.avail_ready i w = true by
    obtain ⟨n, hn⟩ := h
    refine ⟨(mvbaComponent thS thM).cover r n, ?_⟩
    rw [← p.proj_eq_run_cover n]
    exact hn
  by_contra hcon
  have hno : ∀ n, ¬ (r.at' n).mvba_st.avail_ready i w = true := fun n h => hcon ⟨n, h⟩
  obtain ⟨m, -, mn, hl⟩ := (hfj.2.2.2 i w).fires kd
      (fun n hn => ⟨V, haccp n (by omega)⟩) fun n hn => by
    -- The `Mvba` model's availability input is unguarded.
    obtain ⟨st', hst'⟩ : ∃ st', (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root)
        (view := view)).tr thM (r.at' n).mvba_st (.become_avail_ready i w) st' := by
      simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
      exact ⟨_, rfl⟩
    exact ⟨_, ⟨st', rfl⟩, enabled_mvba_avail_ready hi (hda n (by omega))
      (fun hf => hno n (avail_marked_ready r n hf)) hst'⟩
  exact hno (m + 1) (Mvba.avail_effect_tr thM (mvba_avail_ready_tr (hl ▸ r.steps m)))

/-- **The MVBA terminates inside the composed run**: `Mvba.termination`
applied to the run's MVBA projection. `MvbaAdmissible` supplies the
projection and its two scheduling premises; the caller's four premises are
given or derived: every correct validator proposes (`hall`); none has
invoked Chorus's `abandon()` (`hnab`), so none is abandoned in the MVBA
(`abandoned_of_mvba_abandoned`); decided certificates are handed on by
their deciders, active from `A` on (`fRelay_of_fJustice`); and the
availability shares arrive (`fAvail_of_fJustice`). -/
theorem all_decided_of_all_input [Fintype node] (hqe : Cadence.ByzNodeSetHonestQuorum node nodeset nset)
    (vfin : Cadence.ViewOrderEnum view vord)
    (r : ChorusRun (nset := nset) thS thM) (hcj : FJustice r) (hadm : MvbaAdmissible r)
    (hbr : ValidBridge r) {A : Nat} (hact : ActiveFrom r A)
    (hall : ∀ i, ¬ nset.is_byz i = true → ∃ n E, (r.at' n).mvba_st.input i E = true)
    (hnab : ∀ i, ¬ nset.is_byz i = true → ∀ n, ¬ (r.at' n).abandoned i = true) :
    ∀ i, ¬ nset.is_byz i = true → ∃ n v, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st i v := by
  obtain ⟨p, hfj, hav⟩ := hadm
  have hfa := fAvail_of_fJustice r hcj hbr p
  have hap : Mvba.AllPropose p.run := fun i hi => by
    obtain ⟨n, E, h⟩ := hall i hi
    refine ⟨(mvbaComponent thS thM).cover r n, E, ?_⟩
    rw [← p.proj_eq_run_cover n]
    exact h
  have hna : Mvba.NoEarlyAbandon p.run := fun i k hi h =>
    absurd (abandoned_of_mvba_abandoned r i _ h) (hnab i hi _)
  intro i hi
  obtain ⟨k, E, hk⟩ := Mvba.termination hqe vfin p.run hfj hav hfa hap hna
    (fRelay_of_fJustice r hcj hact p) i hi
  exact ⟨_, E, hk⟩

/-- The certified vector is `Certified` where the evidence is: every
proposer has a positive or a negative certificate. The configuration links
are the system's: `mval_pos`/`mval_neg` read an entry vector, `ent` drops a
representation's certificates, and `mval_fb` reads a positive entry's
kind. -/
theorem certified_certifiedVector
    (hmp : ∀ (e : node → Option merkle_root) j m, thS.mval_pos e j m = true ↔ e j = some m)
    (hmn : ∀ (e : node → Option merkle_root) j,
      thS.mval_neg e j = true ↔ e j = none ∧ thS.is_proposer j = true)
    (hent : ∀ v, thM.ent v = MetaBlock.entries v)
    (hmf : ∀ v j, thS.mval_fb v j = true ↔ (v j).map Prod.snd = some CertKind.fallbackQC)
    (hev : ∀ j, thS.is_proposer j = true →
      (∃ m, Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS s ∨
        (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS s ∧
          Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s)) ∨
      (Chorus.vote_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS s ∨
        ((Chorus.fb_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS s ∨
          Chorus.equiv_evidence (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS s) ∧
          Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s))) :
    Certified (thS := thS) (thM := thM) s (certifiedVector thS thM s) := by
  -- The vector's entry, on either branch of its definition.
  have hpos : ∀ J (h : thS.is_proposer J = true ∧ ∃ m,
      Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∨ (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∧ Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s)),
      certifiedVector thS thM s J = some (h.2.choose,
        if Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J h.2.choose thS s then CertKind.fastQC else CertKind.fallbackQC) := by
    intro J h
    unfold certifiedVector
    rw [dif_pos h]
  have hnil : ∀ J, ¬ (thS.is_proposer J = true ∧ ∃ m,
      Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∨ (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∧ Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s)) →
      certifiedVector thS thM s J = none := by
    intro J h
    unfold certifiedVector
    rw [dif_neg h]
  refine ⟨fun J M hJ => ?_, fun J hJ => ?_, fun J hJ => ?_⟩
  · rw [hent, hmp] at hJ
    by_cases h : thS.is_proposer J = true ∧ ∃ m,
        Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∨ (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∧ Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s)
    · rw [MetaBlock.entries, hpos J h] at hJ
      simp only [Option.map_some, Option.some.injEq] at hJ
      subst hJ
      refine ⟨h.1, ?_⟩
      by_cases hv : Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J h.2.choose thS s
      · exact Or.inl ⟨by rw [hmf, hpos J h]; simp [hv], hv⟩
      · exact Or.inr ⟨by rw [hmf, hpos J h]; simp [hv], h.2.choose_spec.resolve_left hv⟩
    · rw [MetaBlock.entries, hnil J h] at hJ
      simp at hJ
  · rw [hent, hmn] at hJ
    obtain ⟨hnone, hpr⟩ := hJ
    by_cases h : thS.is_proposer J = true ∧ ∃ m,
        Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∨ (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∧ Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s)
    · rw [MetaBlock.entries, hpos J h] at hnone
      simp at hnone
    · refine ⟨hpr, ?_⟩
      rcases hev J hpr with hp | hn
      · exact absurd ⟨hpr, hp⟩ h
      · exact hn
  · simp only [hent]
    by_cases h : thS.is_proposer J = true ∧ ∃ m,
        Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∨ (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J m thS s ∧ Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS s)
    · refine Or.inl ⟨h.2.choose, (hmp _ _ _).2 ?_⟩
      rw [MetaBlock.entries, hpos J h]
      rfl
    · refine Or.inr ((hmn _ _).2 ⟨?_, hJ⟩)
      rw [MetaBlock.entries, hnil J h]
      rfl

/-- **A correct validator whose trigger holds from correct senders and whose
vector is certified and `Valid` from some index on proposes**: `mvba_propose
i v` is then owed and enabled for some successor state until `i` has an
input, so the family fires (`FJustice`'s proposal clause). -/
theorem eventually_input (r : ChorusRun (nset := nset) thS thM)
    (hfam : ∀ i v, WeaklyFairFamilyWhen r (proposeOwed (nset := nset) (mvba := Mvba.mvbaSafety thM) thS i)
      (fun l => ∃ mvba_next, l = .mvba_propose i v mvba_next))
    {A : Nat} (hact : ActiveFrom r A)
    {i : node} (hi : ¬ nset.is_byz i = true) {v : MetaBlock node merkle_root} {N : Nat}
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

set_option maxHeartbeats 1000000 in
/-- **The decision is transported.** From a correct validator's MVBA decision
`v`: every proposer's entry of `v` is handled (`on_mvba_decide_pos/neg`,
whose bridge `require` is `ValidBridge`'s completeness clause, each enabled
until `i` has handled that entry), and then `i`'s own `mvba_terminate` sets
`local_mvba_complete i`. From some index at or after `N` on, it holds. -/
theorem eventually_mvba_complete (r : ChorusRun (nset := nset) thS thM)
    (hfj : PerLabel r) (hbr : ValidBridge r)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) (N : Nat)
    {i : node} (hi : ¬ nset.is_byz i = true) {k : Nat} {v : MetaBlock node merkle_root}
    (hd : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k).mvba_st i v) :
    ∃ T, N ≤ T ∧ ∀ n, T ≤ n → (r.at' n).local_mvba_complete i = true := by
  mvba_inst
  have hdec := decided_persists r hd
  have hcert : ∀ n, k ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) v :=
    r.mono (P := fun st => Certified (thS := thS) (thM := thM) st v)
      (fun n h => h.step (r.steps n)) (hbr.2.1 k i v hi hd)
  -- Every proposer's entry of `v` is handled, at one index and ever after.
  obtain ⟨Tr, hTr, hall⟩ := r.eventually_forall
    (fun J st => thS.is_proposer J = true → st.local_mvba_recorded i J = true)
    (fun J n h hJ => Chorus.local_mvba_recorded.mono (r.steps n) i J (h hJ)) (max k N) nodes
    (fun J _ => by
      by_cases hJ : thS.is_proposer J = true
      · obtain ⟨-, -, hent⟩ := hcert k (Nat.le_refl _)
        rcases hent J hJ with ⟨M, hM⟩ | hM
        · obtain ⟨n, hn, h⟩ := eventually_of_weaklyFair
            ((hfj (.on_mvba_decide_pos i J M v) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial))
            (P := fun st => st.local_mvba_recorded i J = true) (N := max k N)
            (fun _ _ h => (on_mvba_decide_pos_effect h).2) (fun n hn hnr => by
              obtain ⟨hp, -, -⟩ := hcert n (by omega)
              exact enabled_on_mvba_decide_pos hi hJ (hdec n (by omega)) hM (hp J M hM).2 hnr)
          exact ⟨n, hn, fun _ => h⟩
        · obtain ⟨n, hn, h⟩ := eventually_of_weaklyFair
            ((hfj (.on_mvba_decide_neg i J v) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial))
            (P := fun st => st.local_mvba_recorded i J = true) (N := max k N)
            (fun _ _ h => (on_mvba_decide_neg_effect h).2) (fun n hn hnr => by
              obtain ⟨-, hng, -⟩ := hcert n (by omega)
              exact enabled_on_mvba_decide_neg hi hJ (hdec n (by omega)) hM (hng J hM).2 hnr)
          exact ⟨n, hn, fun _ => h⟩
      · exact ⟨max k N, Nat.le_refl _, fun h => absurd h hJ⟩)
  have hrec : ∀ n, Tr ≤ n → ∀ J, thS.is_proposer J = true → (r.at' n).local_mvba_recorded i J = true :=
    fun n hn J hJ => r.mono (P := fun st => st.local_mvba_recorded i J = true)
      (fun m h => Chorus.local_mvba_recorded.mono (r.steps m) i J h) (hall J (hnodes J) hJ) n hn
  -- So `mvba_terminate i v` stays enabled until `local_mvba_complete i` holds.
  have hc : ∃ n, Tr ≤ n ∧ (r.at' n).local_mvba_complete i = true := by
    by_contra hcon
    obtain ⟨n, hn, hfire⟩ := (hfj (.mvba_terminate i v) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h)).of_forall (fun _ => trivial) Tr
      (fun n hn => (enabled_mvba_terminate hi (fun h => hcon ⟨n, hn, h⟩)
        (hdec n (by omega)) (hrec n hn)))
    exact hcon ⟨n + 1, by omega, mvba_terminate_effect (hfire ▸ r.steps n)⟩
  obtain ⟨Tc, hTc, hc⟩ := hc
  exact ⟨Tc, by omega, fun n hn =>
    r.mono (P := fun st => st.local_mvba_complete i = true)
      (fun m h => Chorus.local_mvba_complete.mono (r.steps m) i h) hc n hn⟩

/-- **A correct validator's fallback commit vote signs a decision of its
own**, at every point of the composed run: the vote's first step is its
`cast_fb_commit` (`fbcommit_sig_flip`), and the decision persists. -/
theorem fbcommit_sig_decided (r : ChorusRun (nset := nset) thS thM) {a : node}
    (ha : ¬ nset.is_byz a = true) {e : node → Option merkle_root} :
    ∀ n, (r.at' n).msg_fbcommit_sig a e = true →
      ∃ v, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st a v ∧ thM.ent v = e := by
  mvba_inst
  exact record_backed r (F := fun st => st.msg_fbcommit_sig a e = true)
    (Q := fun st => ∃ v, (Mvba.mvbaSafety (nset := nset) thM).decided st.mvba_st a v ∧ thM.ent v = e)
    (by simp [Chorus.msg_fbcommit_sig.init r.starts a e])
    (fun n h0 h1 => let ⟨v, hd, he⟩ := fbcommit_sig_flip (r.steps n) ha h0 h1
      ⟨v, decided_persists r hd (n + 1) (Nat.le_succ n), he⟩)
    (fun n ⟨v, hd, he⟩ => ⟨v, decided_persists r hd (n + 1) (Nat.le_succ n), he⟩)

set_option maxHeartbeats 1000000 in
/-- **Every correct validator casts its fallback commit vote**, once it has
decided `w`, and the vote signs `entries(w)`. Its decision is transported
(`eventually_mvba_complete`) and is the `B′` it waits under, and the only
one it has (the `Mvba` model decides once per validator), so `cast_fb_commit
i w` is owed; its DA wait is met under every `FallbackQC` entry of `w`, so
the vote stays enabled.

The wait is the paper's (Algorithm 5, line 38 (`line:fb-commit-foreach`)): the certificate `w`
names for an entry is on the network (`ValidBridge`'s completeness). Under a
`FastQC` entry there is nothing to wait for. Under a `FallbackQC` entry one
of its `f+1` signers is correct and decoded the proposal to sign, and in the
same step sent `i` its chunk (Algorithm 5, line 12 (`line:fb-redisseminate`),
`fb_pos_sig_chunks`). -/
theorem eventually_fbcommit_sig (r : ChorusRun (nset := nset) thS thM)
    (hfj : PerLabel r) (hbr : ValidBridge r)
    {A : Nat} (hact : ActiveFrom r A)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes)
    {i : node} (hi : ¬ nset.is_byz i = true) {kd : Nat} {w : MetaBlock node merkle_root}
    (hdw : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' kd).mvba_st i w) :
    ∃ n, (r.at' n).msg_fbcommit_sig i (thM.ent w) = true := by
  mvba_inst
  have hdec := decided_persists r hdw
  -- `i` transports its own decision.
  obtain ⟨T, -, hT⟩ := eventually_mvba_complete r hfj hbr nodes hnodes 0 hi hdw
  -- `w` is `i`'s one decision: the `Mvba` model decides once per validator.
  have huniq : ∀ n w', (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st i w' → w' = w :=
    fun n w' h => Mvba.reachable_integrity
      (Chorus.reachable_mvba_reachable (r.reachable (max n kd))) i w' w hi
      (decided_persists r h _ (Nat.le_max_left _ _)) (hdec _ (Nat.le_max_right _ _))
  -- The certificates `w` names are on the network (the bridge's completeness).
  have hcert : ∀ n, kd ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) w :=
    r.mono (P := fun st => Certified (thS := thS) (thM := thM) st w)
      (fun n h => h.step (r.steps n)) (hbr.2.1 kd i w hi hdw)
  -- The wait under each FallbackQC entry of `w` is met from the decision
  -- on: the entry's correct signer sent `i` its chunk when it signed.
  have hda : ∀ n, kd ≤ n → ∀ J M, thS.mval_pos (thM.ent w) J M = true → thS.mval_fb w J = true →
      Chorus.chunk_received (nset := nset) (mvba := Mvba.mvbaSafety thM) i J M thS (r.at' n) :=
      fun n hn J M hM hfb => by
    obtain ⟨-, hkind⟩ := (hcert n hn).1 J M hM
    obtain ⟨q, hq, hallq⟩ := (hkind.resolve_left fun h => h.1 hfb).2.1
    obtain ⟨k, hkq, hkh⟩ := ByzNodeSet.greater_than_third_one_honest q hq
    exact ⟨k, fb_pos_sig_chunks r hkh n (hallq k hkq) i⟩
  obtain ⟨n, -, e, he⟩ := eventually_of_weaklyFairWhen
    (hfj (.cast_fb_commit i w) ⟨fun h => h, fun h => h, fun h => h⟩ (fun h => h))
    (P := fun st => ∃ e, st.msg_fbcommit_sig i e = true) (N := max (max A kd) T)
    (fun n hn => ⟨hdec n (by omega), huniq n⟩)
    (fun _ _ h => ⟨_, cast_fb_commit_effect h⟩)
    (fun n hn hnv => enabled_cast_fb_commit hi (hact n (by omega) i hi)
      (hdec n (by omega)) (hT n (by omega)) (hda n (by omega))
      fun hf => hnv (fbcommit_voted_sig r n hf))
  -- The vote signs a decision of `i`'s, which is `w`.
  obtain ⟨v', hd', rfl⟩ := fbcommit_sig_decided r hi n he
  exact ⟨n, huniq n v' hd' ▸ he⟩

/-- **A correct quorum's fallback commit votes over the decided entries are
all on the network at one index**: every member votes over its own decision
(`eventually_fbcommit_sig`), whose entries are `v0`'s by the MVBA's
agreement. -/
theorem eventually_fbcommitqc (r : ChorusRun (nset := nset) thS thM)
    (hfj : PerLabel r) (hbr : ValidBridge r)
    {A : Nat} (hact : ActiveFrom r A)
    (nodes : List node) (hnodes : ∀ a, a ∈ nodes) (T : Nat)
    {qv : nodeset} (hqv : nset.supermajority qv)
    (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true)
    {i0 : node} (hi0 : ¬ nset.is_byz i0 = true) {k0 : Nat} {v0 : MetaBlock node merkle_root}
    (hd0 : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k0).mvba_st i0 v0)
    (hdec : ∀ a, ¬ nset.is_byz a = true →
      ∃ k w, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k).mvba_st a w) :
    ∃ n, T ≤ n ∧ CorrectFbCommitQC (thM.ent v0) (r.at' n) := by
  mvba_inst
  obtain ⟨F, hF, hall⟩ := r.eventually_forall
    (fun a st => nset.member a qv = true → st.msg_fbcommit_sig a (thM.ent v0) = true)
    (fun a n h hm => Chorus.msg_fbcommit_sig.mono (r.steps n) a _ (h hm)) T nodes
    (fun a _ => by
      by_cases hm : nset.member a qv = true
      · obtain ⟨k, w, hw⟩ := hdec a (hqvh a hm)
        obtain ⟨n, hn⟩ := eventually_fbcommit_sig r hfj hbr hact nodes hnodes (hqvh a hm) hw
        -- `w`'s entries are `v0`'s: the MVBA's agreement.
        have heq : thM.ent w = thM.ent v0 :=
          (Mvba.mvbaSafety (nset := nset) thM).agreement _
            (Chorus.reachable_mvba_reachable (r.reachable (max k k0))) a i0 w v0 (hqvh a hm) hi0
            (decided_persists r hw _ (Nat.le_max_left _ _)) (decided_persists r hd0 _ (Nat.le_max_right _ _))
        rw [heq] at hn
        exact ⟨max T n, by omega, fun _ => r.mono (P := fun st => st.msg_fbcommit_sig a (thM.ent v0) = true)
          (fun m h => Chorus.msg_fbcommit_sig.mono (r.steps m) a _ h) hn _ (by omega)⟩
      · exact ⟨T, Nat.le_refl _, fun h => absurd h hm⟩)
  exact ⟨F, hF, qv, hqv, hqvh, fun a ha => hall a (hnodes a) ha⟩

/-- **Every fallback commit certificate is over the decided entries**: its
`2f+1` votes (`msg_fbcommitqc_backed`) have a correct signer, whose vote
signs a decision of its own (`fbcommit_sig_decided`), which agrees with every
correct decision (the MVBA's agreement). -/
theorem fbcommitqc_decided (r : ChorusRun (nset := nset) thS thM)
    {i0 : node} (hi0 : ¬ nset.is_byz i0 = true) {k0 : Nat} {v0 : MetaBlock node merkle_root}
    (hd0 : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k0).mvba_st i0 v0)
    {n : Nat} {c : node} {e : node → Option merkle_root}
    (h : (r.at' n).msg_fbcommitqc c e = true) : e = thM.ent v0 := by
  mvba_inst
  have hb := Chorus.reachable_msg_fbcommitqc_backed (r.reachable n) c e h
  unfold Chorus.fbcommitqc at hb
  obtain ⟨q, hq', hall⟩ := hb
  obtain ⟨a, ha, hab⟩ :=
    ByzNodeSet.greater_than_third_one_honest q (ByzNodeSet.supermajority_greater_than_third q hq')
  obtain ⟨w, hw, rfl⟩ := fbcommit_sig_decided r hab n (hall a ha)
  exact (Mvba.mvbaSafety (nset := nset) thM).agreement _
    (Chorus.reachable_mvba_reachable (r.reachable (max n k0))) a i0 w v0 hab hi0
    (decided_persists r hw _ (Nat.le_max_left _ _)) (decided_persists r hd0 _ (Nat.le_max_right _ _))

set_option maxHeartbeats 1000000 in
/-- **A correct collector sends the fallback commit certificate over the
decided entries** (Algorithm 5, line 44 (`line:fb-commit-broadcast`)). Once
a correct quorum's votes over `entries(v0)` are on the network,
`broadcast_fbcommitqc` at a correct, active `c` is owed and enabled until
`c` has sent one. And every fallback commit certificate is over the decided
entries: its `2f+1` votes have a correct signer, whose vote signs its own
decision (`fbcommit_sig_decided`), which agrees with `v0`. -/
theorem eventually_fbcommitqc_sent (r : ChorusRun (nset := nset) thS thM)
    (hfj : PerLabel r) {A : Nat} (hact : ActiveFrom r A)
    {c : node} (hc : ¬ nset.is_byz c = true)
    {i0 : node} (hi0 : ¬ nset.is_byz i0 = true) {k0 : Nat} {v0 : MetaBlock node merkle_root}
    (hd0 : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' k0).mvba_st i0 v0)
    {F : Nat} (hq : CorrectFbCommitQC (thM.ent v0) (r.at' F)) :
    ∃ n, F ≤ n ∧ (r.at' n).msg_fbcommitqc c (thM.ent v0) = true := by
  mvba_inst
  -- Any fallback commit certificate is over `entries(v0)`.
  have hent : ∀ n e, (r.at' n).msg_fbcommitqc c e = true → e = thM.ent v0 :=
    fun n e h => fbcommitqc_decided r hi0 hd0 h
  obtain ⟨q, hqs, hqc, hall⟩ := hq
  have hall' : ∀ n, F ≤ n → ∀ a, nset.member a q = true → (r.at' n).msg_fbcommit_sig a (thM.ent v0) = true :=
    fun n hn a ha => r.mono (P := fun st => st.msg_fbcommit_sig a (thM.ent v0) = true)
      (fun m h => Chorus.msg_fbcommit_sig.mono (r.steps m) a _ h) (hall a ha) n hn
  by_contra hcon
  have hns : ∀ n, F ≤ n → ¬ (r.at' n).local_fbcommitqc_sent c = true := fun n hn h => by
    obtain ⟨e, he⟩ := fbcommitqc_sent_msg r n h
    exact hcon ⟨n, hn, hent n e he ▸ he⟩
  obtain ⟨n, hn, hfire⟩ := (hfj (.broadcast_fbcommitqc c (thM.ent v0) q) ⟨fun h => h, fun h => h, fun h => h⟩
      (fun h => h)).fires (max F A) (fun _ _ => hqc)
    (fun n hn => enabled_broadcast_fbcommitqc hc (hact n (by omega) c hc) hqs (hall' n (by omega))
      (hns n (by omega)))
  exact hcon ⟨n + 1, by omega, broadcast_fbcommitqc_effect (hfire ▸ r.steps n)⟩

set_option maxHeartbeats 1000000 in
/-- **The MVBA arm finalizes** — generic in the quorum instance, at the
system's MVBA. From an index at which the MVBA's trigger holds from correct
senders (`CorrectTrigger`) and every proposer has a positive or a negative
certificate, every correct validator eventually has `local_committed`.

The chain: every correct validator proposes, so every one decides
(`all_decided_of_all_input`); a correct quorum casts its fallback commit
votes over the decided entries (`eventually_fbcommitqc`); a correct
collector sends the fallback commit certificate (`eventually_fbcommitqc_sent`);
it carries an entry for every proposer (the decided vector is certified,
`ValidBridge`), and every correct validator finalizes on it through
`commit_assign_*_fb` (`eventually_committed_of_assignable`).

`hmp`/`hmn` say that the theory reads an entry vector entrywise, `some m`
or a proposer's `none`, and `hmf` that it reads a representation's
certificate kind, which is what `Cadence.chorusTheory` does; `hent` that the
MVBA's `ent` drops a representation's certificates, which is what
`Cadence.mvbaTheory` does. -/
theorem eventually_committed_of_mvba_arm [Fintype node]
    (hqe : Cadence.ByzNodeSetHonestQuorum node nodeset nset) (vfin : Cadence.ViewOrderEnum view vord)
    (hmp : ∀ (e : node → Option merkle_root) j m, thS.mval_pos e j m = true ↔ e j = some m)
    (hmn : ∀ (e : node → Option merkle_root) j,
      thS.mval_neg e j = true ↔ e j = none ∧ thS.is_proposer j = true)
    (hent : ∀ v, thM.ent v = MetaBlock.entries v)
    (hmf : ∀ v j, thS.mval_fb v j = true ↔ (v j).map Prod.snd = some CertKind.fallbackQC)
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
      (fun n h => h.step (r.steps n)) (certified_certifiedVector hmp hmn hent hmf hev)
  have hvalid := hbr.1 N _ (hcert N (Nat.le_refl _))
  -- Every correct validator proposes it (or something else first).
  have hall : ∀ i, ¬ nset.is_byz i = true → ∃ n E, (r.at' n).mvba_st.input i E = true := by
    intro i hi
    obtain ⟨M, hM⟩ := eventually_trigger r hfj.1 _ hnodes htrig hi
    exact eventually_input r hfj.2.1 hact hi (N := max M N) (fun n hn => hM n (by omega))
      (fun n hn => hcert n (by omega)) hvalid
  -- So the MVBA terminates: every correct validator decides.
  have hdec := all_decided_of_all_input hqe vfin r hfj hadm hbr hact hall hnab
  obtain ⟨i0, -, hi0⟩ := ByzNodeSet.greater_than_third_one_honest hqe.honestQuorum
    (ByzNodeSet.supermajority_greater_than_third _ hqe.honestQuorum_supermajority)
  obtain ⟨k0, v0, hd0⟩ := hdec i0 hi0
  -- The correct quorum's fallback commit votes, and a correct collector's certificate.
  obtain ⟨F, hNF, hq⟩ := eventually_fbcommitqc r hfj.1 hbr hact _ hnodes N hqe.honestQuorum_supermajority
    hqe.honestQuorum_correct hi0 hd0 hdec
  obtain ⟨G, hFG, hG⟩ := eventually_fbcommitqc_sent r hfj.1 hact hi0 hi0 hd0 hq
  -- It carries an entry for every proposer: the decided vector is certified.
  obtain ⟨-, -, htot⟩ := hbr.2.1 k0 i0 v0 hi0 hd0
  obtain ⟨n, hn, h⟩ := eventually_committed_of_assignable r hfj.1 _ hnodes (N := G)
    (fun j hj => by
      rcases htot j hj with ⟨M, hM⟩ | hM
      · exact Or.inl ⟨M, i0, hi0, Or.inr (Or.inl ⟨_, hG, hM⟩)⟩
      · exact Or.inr ⟨i0, hi0, Or.inr (Or.inl ⟨_, hG, hM⟩)⟩) hi ⟨A, (hact A (Nat.le_refl _) i hi).1⟩ (hab i hi)
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
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view))
      (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view}

/-- Apply a generated `Chorus` declaration at the canonical `Classical`
instantiation — [Progress.lean](Progress.lean)'s `cpv%`, at the `Mvba` model's types and
with the MVBA constraint filled by `Mvba.mvbaSafety thM`. -/
local macro "cpvm%" t:ident args:term:max* : term =>
  `(@$t
    (Chorus.Theory slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)) Phase PathChoice)
    (Chorus.State (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)) Phase PathChoice))
    slot (fun a b => Classical.propDecidable (a = b)) inferInstance
    (Fin n) (fun a b => Classical.propDecidable (a = b)) inferInstance
    (ByzNSet n) (fun a b => Classical.propDecidable (a = b)) inferInstance
    merkle_root (fun a b => Classical.propDecidable (a = b)) inferInstance
    (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view))
      (fun a b => Classical.propDecidable (a = b)) inferInstance
    (MetaBlock (Fin n) merkle_root) (fun a b => Classical.propDecidable (a = b)) inferInstance
    (Fin n → Option merkle_root) (fun a b => Classical.propDecidable (a = b)) inferInstance
    (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)) (fun a b => Classical.propDecidable (a = b)) inferInstance
    (byzNodeSetFin n f hf is_byz hbyz) (Cadence.byzNodeSetFin_counting n f hf is_byz hbyz)
    (Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thM)
    Phase (fun a b => Classical.propDecidable (a = b)) inferInstance inferInstance
    PathChoice (fun a b => Classical.propDecidable (a = b)) inferInstance inferInstance
    (Chorus.FieldAbstractType slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)) Phase PathChoice)
    (fun ff => @Chorus.instAbstractFieldRepresentation slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)) Phase PathChoice
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) ff)
    (fun ff => @Chorus.instLawfulAbstractFieldRepresentation slot (Fin n) (ByzNSet n) merkle_root
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)) Phase PathChoice
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) ff)
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
  {mvba_init_state : Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)}

/-- The Chorus configuration at the system's instantiation. -/
local notation "thC" => Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
  is_proposer well_encoded mvba_init_state

variable {mvalid : MetaBlock (Fin n) merkle_root → Bool} {mleader : view → Fin n → Bool}

/-- The MVBA configuration at the system's instantiation: `ent` drops a
representation's certificates. -/
local notation "thMC" => Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader

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
    (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thC thMC)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hadm : MvbaAdmissible (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hbr : ValidBridge (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    {A : Nat} (hact : ActiveFrom r A)
    (hab : NoAbandonBeforeFinalizing (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hnab : ∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true → ∀ k,
      ¬ (r.at' k).abandoned i = true) {N : Nat}
    (hright : CorrectTrigger (nset := byzNodeSetFin n f hf is_byz hbyz)
      (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thMC) thC (r.at' N) ∧
      ∀ j : Fin n, (thC).is_proposer j = true →
        ((∃ m, (cpvm% Chorus.vote_quorum_pos j m thC (r.at' N)) ∨
               ((cpvm% Chorus.fb_quorum_pos j m thC (r.at' N)) ∧ (cpvm% Chorus.fbcert thC (r.at' N)))) ∨
         ((cpvm% Chorus.vote_quorum_neg j thC (r.at' N)) ∨
          (((cpvm% Chorus.fb_quorum_neg j thC (r.at' N)) ∨ (cpvm% Chorus.equiv_evidence j thC (r.at' N))) ∧
           (cpvm% Chorus.fbcert thC (r.at' N)))))) :
    ∀ i : Fin n, ¬ is_byz i → ∃ k, N ≤ k ∧ (r.at' k).local_committed i = true :=
  fun _ hi => eventually_committed_of_mvba_arm (byzNodeSetFin_honest n f hf is_byz hbyz) vfin
    (fun _ _ _ => decide_eq_true_iff) (fun _ _ => decide_eq_true_iff) (fun _ => rfl)
    (fun _ _ => decide_eq_true_iff) r hfj hadm hbr hact hab hnab
    hright.1 hright.2
    (by simpa +instances [byzNodeSetFin] using hi)

set_option maxHeartbeats 1600000 in
/-- The MVBA arm in the claim's own vocabulary: if the MVBA route is open
from correct senders, the run `Terminates`. -/
theorem terminates_of_mvba_arm (vfin : Cadence.ViewOrderEnum view vord)
    (r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz) thC thMC)
    (hfj : FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hadm : MvbaAdmissible (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hbr : ValidBridge (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    {A : Nat} (hact : ActiveFrom r A)
    (hab : NoAbandonBeforeFinalizing (nset := byzNodeSetFin n f hf is_byz hbyz) r)
    (hnab : ∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true → ∀ k,
      ¬ (r.at' k).abandoned i = true) {N : Nat}
    (hright : CorrectTrigger (nset := byzNodeSetFin n f hf is_byz hbyz)
      (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thMC) thC (r.at' N) ∧
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
configurations `Cadence.chorusTheory` and `Cadence.mvbaTheory`, every run
satisfying `FJustice`, `MvbaAdmissible`, `ValidBridge`, `AllParticipate`
and `NoAbandonBeforeFinalizing` `Terminates` — every correct validator
finalizes the slot.

**Why the MVBA's configuration is fixed.** At `Cadence.mvbaTheory` a
meta-block's entry vector is its own entries with the certificates dropped
(`ent := MetaBlock.entries`), as the paper defines `entries(B)`; the
validity predicate and the leader schedule stay arbitrary. Termination
needs it because a validator must be able to propose a certified
meta-block: under an arbitrary `ent` no representation need have the
entries the network certifies. It fixes the configuration the composed
system runs, as `Cadence.chorusTheory` does for Chorus's projections; it is
not a premise.

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
  deciding holds because nobody abandons at all. This branch does not
  split on the progress dichotomy: the commit certificates of its left
  disjunct may rest on Byzantine votes that nobody correct is owed, and
  the MVBA arm needs no such split.

The split on the dichotomy alone no longer suffices, because a validator
that finalizes on the fast path may then abandon, which also abandons the
MVBA. `vfin`, the view order's enumeration, is the one further hypothesis,
and like `Mvba.termination`'s it belongs to the proof, not to the claim.
The quorum counting facts are the concrete family's own instance
(`Cadence.byzNodeSetFin_counting`), not a hypothesis. -/
theorem termination (vfin : Cadence.ViewOrderEnum view vord) :
    TerminationClaim (nset := byzNodeSetFin n f hf is_byz hbyz)
      (cnt := Cadence.byzNodeSetFin_counting n f hf is_byz hbyz) (thC) thMC := by
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
info: 'Chorus.committed_pos_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.committed_pos_cert

/--
info: 'Chorus.committed_neg_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.committed_neg_cert

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

/--
info: 'Chorus.fb_pos_sig_chunks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fb_pos_sig_chunks
