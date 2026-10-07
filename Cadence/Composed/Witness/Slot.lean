import Cadence.Chorus.Witness

/-! # Composed.Witness.Slot — one slot's Chorus, as the composed witness runs it

[ConductorBounds.md](../../../docs/ConductorBounds.md) §8.2, stage K8. The
composed witness runs every slot's Chorus instance the way
[Chorus/Witness.lean](../../Chorus/Witness.lean) runs its one slot: the fast
path, with validator 3 Byzantine and silent. This file is that trajectory at
the system's slot type `ℕ`, as a sequence of **local states** `cst m`, one per
step the slot takes, and the facts about them that the composed proofs read:

* every local step is a Chorus transition (`cstep`), and every local state
  from `1` on has a **stutter** (`stut`): a re-issued `participate` while
  validator 0 has not abandoned, a re-issued `abandon` after (F24);
* the initial local state has **no** stutter (`no_stutter_init`), so a slot's
  part starts moving exactly at its first step;
* at the five **quiet** local states (`0`, `11`, `36`, `37`, `38`), where the
  composed run's clock may advance, no row of Chorus's hop table is enabled,
  the availability report aside (`quiet`), and at the final one no fair label
  at all (`justice_final`);
* the only certifiable meta-block is `v⋆` (`certified_eq`), the MVBA stays
  quiet, and nobody decides in it.

The instance (`Fin 4`, validator 3 Byzantine, validator 0 the one proposer,
the MVBA theory with `valid := (· = v⋆)` and validator 0 leading every view)
is the Chorus witness's, reused by name. The local trajectory is the Chorus
witness's run without its oracle ticks: the composed run's clock moves on the
Conductor's `tick`, so no Byzantine `Pre-Prepare` is needed to advance time,
and validator 3 sends nothing at all.

The step that sets each record (with `x < 3` a correct validator):

* `participating x`: `x`; the proposer's root: `3`; the chunk to validator
  `y` (any of the four): `4 + y`; `local_entry_pos x`: `8 + x`;
* the deadline marker at `11`;
* the vote of `x`: `12 + x`; its FastQC: `15 + x`; its commit signature:
  `18 + x`; its fast commit vote: `21 + x`; its commit certificate:
  `24 + x`; its committed entry: `27 + x`; its finalization: `30 + x`; its
  abandonment (Chorus's and the MVBA's): `33 + x`;
* the fallback-arm marker at `36`, the MVBA-arm marker at `37`; from `38` on
  the state no longer changes. -/

namespace Composed.Witness

open Cadence Chorus
open scoped Cadence.Timed

attribute [local instance] Chorus.Witness.nsetC Chorus.Witness.cntC natViewOrder

/-- The MVBA's values and entry vectors, the Chorus witness's. -/
abbrev V := Chorus.Witness.V
abbrev E := Chorus.Witness.E
abbrev MS := Chorus.Witness.MS
abbrev Ph := Chorus.Witness.Ph
abbrev PC := Chorus.Witness.PC
/-- A slot instance's Chorus state, at the system's slot type `ℕ`. -/
abbrev CS := StateAtMvba ℕ (Fin 4) (ByzNSet 4) Unit ℕ Ph PC
/-- A slot instance's Chorus label. -/
abbrev CL := LabelAtMvba ℕ (Fin 4) (ByzNSet 4) Unit ℕ Ph PC

/-- The MVBA theory, the Chorus witness's. -/
abbrev thM : Mvba.Theory (Fin 4) (ByzNSet 4) V E ℕ := Chorus.Witness.thM

/-- The MVBA's state at local index `m`: quiet, and abandoned by the three
correct validators (`33 + x`). -/
def mst (m : Nat) : MS where
  msg_preprepare _ _ _ := false
  msg_prepare _ _ _ := false
  msg_commit _ _ _ := false
  msg_timeout_qc _ _ _ _ := false
  msg_timeout_noqc _ _ := false
  msg_prepqc _ _ := false
  msg_commitqc _ _ := false
  msg_tc _ := false
  tc_lock _ _ _ := false
  tc_nolock _ := false
  input _ _ := false
  entered _ _ := false
  voted _ _ := false
  accepted _ _ _ := false
  local_prepqc _ _ _ := false
  timed_out _ _ := false
  commit_sent _ _ := false
  proposed_in _ _ := false
  decided _ _ := false
  abandoned i := decide (i.val < 3 ∧ 33 + i.val < m)
  avail_ready _ _ := false
  timer_expired _ _ := false
  tc_formed _ _ := false

/-- The system's Chorus configuration at slot type `ℕ`: validator 0 the one
proposer, every root well-encoded, the MVBA starting from `mst 0`. -/
noncomputable def thS : Chorus.Theory ℕ (Fin 4) (ByzNSet 4) Unit MS V E (Mvba.Msg ℕ V E) Ph PC :=
  Cadence.chorusTheory (slot := ℕ) (Phase := Ph) (PathChoice := PC)
    (fun j => decide (j.val = 0)) (fun _ => true) (mst 0)

/-- Chorus at the `Mvba` instance, at slot type `ℕ`. -/
noncomputable abbrev sys := atMvba (slot := ℕ) (Phase := Ph) (PathChoice := PC) thM

open Phase_IndT PathChoice_IndT in
/-- A slot's Chorus state at local index `m`. -/
def cst (m : Nat) : CS where
  phase := if m ≤ 11 then pre_deadline else if m ≤ 36 then post_deadline
    else if m ≤ 37 then post_fb_arm else post_mvba_arm
  msg_proposer_signed j _ := decide (j.val = 0 ∧ 3 < m)
  msg_chunk_received i j _ := decide (j.val = 0 ∧ 4 + i.val < m)
  msg_vote_pos_sig r j _ := decide (j.val = 0 ∧ r.val < 3 ∧ 12 + r.val < m)
  msg_vote_neg_sig _ _ := false
  msg_vote_cast r := decide (r.val < 3 ∧ 12 + r.val < m)
  msg_fb_pos_sig _ _ _ := false
  msg_fb_neg_sig _ _ := false
  msg_fallback_sig _ := false
  msg_commit_pos_sig r j _ := decide (j.val = 0 ∧ r.val < 3 ∧ 18 + r.val < m)
  msg_commit_neg_sig _ _ := false
  msg_commit_cast r := decide (r.val < 3 ∧ 21 + r.val < m)
  msg_commitqc_pos j _ := decide (j.val = 0 ∧ 24 < m)
  msg_commitqc_neg _ := false
  msg_decrypt_share r := decide (r.val < 3 ∧ 12 + r.val < m)
  msg_fbcommit_sig _ := false
  local_fastqc_pos i j _ := decide (j.val = 0 ∧ i.val < 3 ∧ 15 + i.val < m)
  local_fastqc_neg _ _ := false
  mvba_st := mst m
  aux_mvba_decided_pos _ _ := false
  aux_mvba_decided_neg _ := false
  local_mvba_complete _ := false
  local_entry_pos i j _ := decide (j.val = 0 ∧ i.val < 3 ∧ 8 + i.val < m)
  local_entry_neg _ _ := false
  local_voted i := decide (i.val < 3 ∧ 12 + i.val < m)
  local_path i := if i.val < 3 ∧ 21 + i.val < m then fast else none
  local_committed i := decide (i.val < 3 ∧ 30 + i.val < m)
  local_committed_pos i j _ := decide (j.val = 0 ∧ i.val < 3 ∧ 27 + i.val < m)
  local_committed_neg _ _ := false
  aux_fb_neg_qv _ _ _ := false
  local_chunk_sent k i j _ := decide (j.val = 0 ∧ k.val = 0 ∧ 4 + i.val < m)
  local_commit_entry i j := decide (j.val = 0 ∧ i.val < 3 ∧ 18 + i.val < m)
  local_fb_entry _ _ := false
  local_commitqc_sent c j := decide (j.val = 0 ∧ c.val < 3 ∧ 24 + c.val < m)
  local_mvba_recorded _ _ := false
  local_mvba_qc_accepted _ := false
  local_fbcommit_voted _ := false
  local_avail_marked _ _ := false
  participating i := decide (i.val < 3 ∧ i.val < m)
  abandoned i := decide (i.val < 3 ∧ 33 + i.val < m)

/-- The quorum of the three correct validators, the Chorus witness's. -/
abbrev Q : ByzNSet 4 := Chorus.Witness.Q

/-- The label of the local step out of local index `m < 38`. -/
def lab : Nat → CL
  | 0 => .participate 0
  | 1 => .participate 1
  | 2 => .participate 2
  | 3 => .propose 0 ()
  | 4 => .deliver_chunk_assigned 0 0 ()
  | 5 => .deliver_chunk_assigned 1 0 ()
  | 6 => .deliver_chunk_assigned 2 0 ()
  | 7 => .deliver_chunk_assigned 3 0 ()
  | 8 => .record_chunk 0 0 ()
  | 9 => .record_chunk 1 0 ()
  | 10 => .record_chunk 2 0 ()
  | 11 => .advance_to_deadline
  | 12 => .vote 0
  | 13 => .vote 1
  | 14 => .vote 2
  | 15 => .aggregate_fastqc_pos 0 0 () Q
  | 16 => .aggregate_fastqc_pos 1 0 () Q
  | 17 => .aggregate_fastqc_pos 2 0 () Q
  | 18 => .commit_sign_pos 0 0 ()
  | 19 => .commit_sign_pos 1 0 ()
  | 20 => .commit_sign_pos 2 0 ()
  | 21 => .cast_fast_commit 0
  | 22 => .cast_fast_commit 1
  | 23 => .cast_fast_commit 2
  | 24 => .broadcast_commitqc_pos 0 0 () Q
  | 25 => .broadcast_commitqc_pos 1 0 () Q
  | 26 => .broadcast_commitqc_pos 2 0 () Q
  | 27 => .commit_assign_pos 0 0 ()
  | 28 => .commit_assign_pos 1 0 ()
  | 29 => .commit_assign_pos 2 0 ()
  | 30 => .finalize_commit 0
  | 31 => .finalize_commit 1
  | 32 => .finalize_commit 2
  | 33 => .abandon 0 (mst 34)
  | 34 => .abandon 1 (mst 35)
  | 35 => .abandon 2 (mst 36)
  | 36 => .advance_to_fb_arm
  | _ => .advance_to_mvba_arm

/-- **The stutter at local index `m ≥ 1`**: validator 0's `participate`
re-issued before it abandons, its `abandon` re-issued after (F24). -/
def stut (m : Nat) : CL := if m < 34 then .participate 0 else .abandon 0 (mst m)

/-! The enum classes' constants are the generated inductive's constructors. -/

@[simp] theorem ph_pre : (Phase_EnumClass.pre_deadline : Ph) = .pre_deadline := rfl
@[simp] theorem ph_post : (Phase_EnumClass.post_deadline : Ph) = .post_deadline := rfl
@[simp] theorem ph_fb : (Phase_EnumClass.post_fb_arm : Ph) = .post_fb_arm := rfl
@[simp] theorem ph_mvba : (Phase_EnumClass.post_mvba_arm : Ph) = .post_mvba_arm := rfl
@[simp] theorem pc_none : (PathChoice_EnumClass.none : PC) = .none := rfl
@[simp] theorem pc_fast : (PathChoice_EnumClass.fast : PC) = .fast := rfl
@[simp] theorem pc_fb : (PathChoice_EnumClass.fallback : PC) = .fallback := rfl

/-! ## Proof tactics, the Chorus witness's -/

-- A step's unfolding is one `simp` over all 38 state components.
set_option maxHeartbeats 4000000

-- One simp-lemma list serves every step, so a given step leaves some unused.
set_option linter.unusedSimpArgs false

-- The case splits over every label close each case by the first tactic of a
-- `first` that applies, so some alternatives are unreachable in some cases.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Normalise `decide`d facts over this instance to linear arithmetic. -/
local macro "wnorm" : tactic =>
  `(tactic| (
    try dsimp +instances only [Chorus.Witness.nsetC, byzNodeSetFin, natViewOrder] at *
    try simp only [← Bool.decide_and, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      Bool.not_eq_true, decide_eq_false_iff_not, Fin.ext_iff, List.mem_cons, List.mem_nil_iff,
      List.length_cons, List.length_nil, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.val_zero,
      exists_eq_left, exists_const, and_true, true_and, or_false] at *))

/-- Split a goal into its conjuncts and close each. -/
local macro "wclose" : tactic =>
  `(tactic| (and_intros <;> intros <;> first | trivial | omega | (split_ifs <;> first | rfl | omega | (simp only [decide_eq_decide] at * <;> omega) | (simp_all <;> omega)) | (refine ⟨Q, ?_, ?_⟩ <;> simp [Q, Chorus.Witness.Q] <;> omega)))

/-- Evaluate the field-representation `get`/`set` pair, and `cst`, `mst`. -/
local macro "wfields" : tactic =>
  `(tactic| (
    try simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id,
      Veil.FieldRepresentation.get, cst, mst, thS, Cadence.chorusTheory, Q, Chorus.Witness.Q,
      Chorus.chunk_quorum, Chorus.State.mk.injEq, Mvba.State.mk.injEq, funext_iff]))

/-- Expose a transition's guards and update, evaluated at `cst`. -/
local macro "wexpose" : tactic =>
  `(tactic| (simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp]; wfields))

/-- One ordinary step. -/
local macro "wstep" : tactic => `(tactic| (wexpose <;> wnorm <;> wclose))

/-- Expose an MVBA transition's guards and update, evaluated at `mst`. -/
local macro "mexpose" : tactic =>
  `(tactic| (
    simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
    try simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id,
      Veil.FieldRepresentation.get, mst, Mvba.State.mk.injEq]))

/-! ## The MVBA's steps -/

/-- Chorus's `abandon i` forwards to the MVBA's `abandon()`: at `33 + i` it
records it, after that it is a stutter. -/
theorem abandon_tr (i : Fin 4) (m : Nat) (hi : i.val < 3) (hm : 33 + i.val ≤ m) :
    (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).tr thM (mst m)
      (.abandon i) (mst (max m (34 + i.val))) := by
  mexpose
  intro a
  simp only [← Bool.decide_and, ← Bool.decide_or, decide_eq_decide, Fin.ext_iff]
  omega

/-- From local index 36 on the MVBA's state no longer changes. -/
theorem mst_stable {m : Nat} (h : 36 ≤ m) : mst m = mst 36 := by
  simp only [mst, Mvba.State.mk.injEq, funext_iff, decide_eq_decide]
  and_intros <;> intros <;> first | trivial | omega

/-- The MVBA is quiet at every local index: nobody has proposed to it. -/
theorem mquiet (m : Nat) : Mvba.Quiet (mst m) := by
  simp [Mvba.Quiet, mst]

/-- Nobody decides in the MVBA. -/
theorem not_decided (m : Nat) (i : Fin 4) (v : V) : ¬ (Mvba.mvbaSafety thM).decided (mst m) i v :=
  fun h => Bool.false_ne_true h

/-- Nobody ever holds a valid MVBA commit certificate: none is formed. -/
theorem not_certified (m : Nat) (c : Mvba.Msg ℕ V E) (e : E) :
    ¬ (Mvba.mvbaSafety thM).certifies (mst m) c e := by
  show ¬ Mvba.Certifies (mst m) c e
  cases c <;> simp [Mvba.Certifies, Veil.FieldRepresentation.get, mst]

/-- Nobody ever holds a meta-block in the MVBA. -/
theorem not_accepted (m : Nat) (i : Fin 4) (w : ℕ) (v : V) : ¬ (mst m).accepted i w v = true := by
  simp [mst]

/-- An MVBA step of Chorus (`abandon`'s forwarding): its MVBA guard first,
then the fields. -/
local macro "wmvba" h:term : tactic =>
  `(tactic| (
    simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp]
    refine ⟨$h, ?_⟩
    wfields <;> wnorm <;> wclose))

/-! ## The trajectory is a run of the model -/

/-- The MVBA model's assumption at `thM`. -/
theorem mholds : (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).assumptions thM :=
  Chorus.Witness.mholds

theorem mstarts : (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).init thM (mst 0) := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init, trSimp]
  simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      Veil.FieldRepresentation.get, mst, Mvba.State.mk.injEq, funext_iff]

/-- Chorus's assumptions at `chorusTheory`. -/
theorem holds : sys.assumptions thS :=
  (Cadence.chorusTheory_assumptions thM _ _ (mst 0)).mpr ⟨mholds, mstarts⟩

theorem starts : sys.init thS (cst 0) := by
  simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Init, trSimp]
  simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id,
      Veil.FieldRepresentation.get, cst, thS, Cadence.chorusTheory, Chorus.State.mk.injEq, funext_iff]

theorem steps_0 (m : Nat) (h : m < 33) : sys.tr thS (cst m) (lab m) (cst (m + 1)) := by
  interval_cases m <;> simp only [lab] <;> wstep

theorem step_33 : sys.tr thS (cst 33) (lab 33) (cst 34) := by
  simp only [lab]; wmvba abandon_tr 0 33 (by decide) (by decide)
theorem step_34 : sys.tr thS (cst 34) (lab 34) (cst 35) := by
  simp only [lab]; wmvba abandon_tr 1 34 (by decide) (by decide)
theorem step_35 : sys.tr thS (cst 35) (lab 35) (cst 36) := by
  simp only [lab]; wmvba abandon_tr 2 35 (by decide) (by decide)
theorem step_36 : sys.tr thS (cst 36) (lab 36) (cst 37) := by simp only [lab]; wstep
theorem step_37 : sys.tr thS (cst 37) (lab 37) (cst 38) := by simp only [lab]; wstep

/-- **Every local step is a transition.** -/
theorem cstep (m : Nat) (h : m < 38) : sys.tr thS (cst m) (lab m) (cst (m + 1)) := by
  by_cases h33 : m < 33
  · exact steps_0 m h33
  have : m = 33 ∨ m = 34 ∨ m = 35 ∨ m = 36 ∨ m = 37 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact step_33
  · exact step_34
  · exact step_35
  · exact step_36
  · exact step_37

/-- From local index 38 on the state no longer changes. -/
theorem cst_stable {m : Nat} (h : 38 ≤ m) : cst m = cst 38 := by
  simp only [cst, Chorus.State.mk.injEq, mst_stable (show 36 ≤ m by omega),
    mst_stable (show 36 ≤ 38 by omega), if_neg (show ¬ m ≤ 11 by omega),
    if_neg (show ¬ m ≤ 36 by omega), if_neg (show ¬ m ≤ 37 by omega), funext_iff, decide_eq_decide]
  and_intros <;> intros <;> first | trivial | rfl | omega | (split_ifs <;> first | rfl | omega)

/-- **Every local state from 1 on can stutter**: validator 0 already
participates, so its `participate` changes nothing, and once it has
abandoned, neither does its `abandon`. -/
theorem stut_tr (m : Nat) (h : 1 ≤ m) : sys.tr thS (cst m) (stut m) (cst m) := by
  by_cases h34 : m < 34
  · simp only [stut, if_pos h34]
    wstep
  · simp only [stut, if_neg h34]
    have := abandon_tr 0 m (by decide) (by simp; omega)
    rw [show max m (34 + (0 : Fin 4).val) = m by simp; omega] at this
    wmvba this

/-! ## The initial local state has no stutter

A slot's part of the composed run starts moving exactly at its first step
only if its initial state cannot stutter: every label either fails its
guard there or changes the state. The MVBA's first. -/

/-- Expose an MVBA transition in a hypothesis, evaluated at `mst`. -/
local macro "mexposeh" h:ident : tactic =>
  `(tactic| (
    simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp] at $h:ident
    try simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id,
      Veil.FieldRepresentation.get, mst, Mvba.State.mk.injEq, funext_iff] at $h:ident))

/-- No MVBA label is a stutter at the MVBA's initial state. -/
theorem mno_stutter (l : Mvba.Label (Fin 4) (ByzNSet 4) V E ℕ) :
    ¬ (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).tr thM (mst 0) l (mst 0) := by
  intro htr
  cases l
  all_goals mexposeh htr
  all_goals (repeat (obtain ⟨_, htr⟩ := htr))
  all_goals first | (simp_all; done) | (obtain ⟨_, h⟩ := htr _ _ rfl; exact h rfl) | (obtain ⟨_, h⟩ := htr _ _ _ rfl rfl; exact h rfl)

theorem mno_stutter_step : ¬ (Mvba.mvbaSafety thM).step (mst 0) (mst 0) :=
  fun ⟨l, _, h⟩ => mno_stutter l h

/-- Expose a transition in a hypothesis, evaluated at `cst`, its update
split field by field. -/
local macro "wunfoldeq" h:ident : tactic =>
  `(tactic| (
    simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at $h:ident
    try simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id,
      Veil.FieldRepresentation.get, cst, mst, thS, Cadence.chorusTheory, Q, Chorus.Witness.Q,
      Mvba.mvbaSafety, Chorus.State.mk.injEq, funext_iff] at $h:ident))

/-- **The initial local state has no stutter.** -/
theorem no_stutter_init (l : CL) : ¬ sys.tr thS (cst 0) l (cst 0) := by
  intro htr
  cases l
  all_goals wunfoldeq htr
  all_goals (repeat (obtain ⟨_, htr⟩ := htr))
  case mvba_step =>
    rename_i h; exact mno_stutter_step (by simpa [mst] using h)
  all_goals first | (simp_all; done) | (obtain ⟨_, h⟩ := htr _ _ rfl; exact h rfl) | (obtain ⟨_, h⟩ := htr _ _ _ rfl rfl; exact h rfl)

/-! ## No row is enabled at a quiet local state

At `11` (the end of the slot's first clock), `36`, `37` and from `38` on
(the ends of the next three), and at the initial state, no row of the hop
table is enabled, the availability report aside, which nobody owes since
nobody holds a meta-block. -/

/-- A guard over a supermajority's members, refuted by the five
supermajorities. -/
local macro "wquorum" : tactic =>
  `(tactic| (rcases Chorus.Witness.supermajority_cases ‹ByzNSet 4› ‹_› with h | h | h | h | h <;>
    simp only [h, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at * <;> omega))

/-- A guard asking a supermajority to have no member at all. -/
local macro "wmember" : tactic =>
  `(tactic| (obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos (by omega : 0 < (‹ByzNSet 4›).val.length); simp_all))

/-- Expose a transition's guards in a hypothesis, evaluated at `cst`. -/
local macro "wunfold" h:ident : tactic =>
  `(tactic| (
    simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at $h:ident
    try simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id,
      Veil.FieldRepresentation.get, cst, mst, thS, Cadence.chorusTheory, Q, Chorus.Witness.Q,
      Mvba.mvbaSafety] at $h:ident))

-- Refute a row's enabledness at a concrete local state: dismiss the labels
-- off the hop table, take the decision-reading labels to the quiet MVBA, and
-- read every other row's guards at the state.
set_option hygiene false in
local macro "wquiet" : tactic =>
  `(tactic| (
    rintro ⟨s', htr⟩
    cases l
    all_goals first | (simp [hop] at hh; done) | skip
    all_goals first | exact absurd ⟨_, _, _, rfl⟩ ha | skip
    case accept_mvba_commitqc i c mn =>
      obtain ⟨w, e, x, -, -, h⟩ := accept_mvba_commitqc_tr htr
      exact Mvba.not_enabled_decide_of_quiet (mquiet _) ⟨_, h⟩
    case on_mvba_decide_pos =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, hdec, -⟩ := htr
      exact not_decided _ _ _ hdec
    case on_mvba_decide_neg =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, hdec, -⟩ := htr
      exact not_decided _ _ _ hdec
    case on_mvba_commitqc_pos i j m c v =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, hc, -⟩ := htr
      exact not_certified _ _ _ hc
    case on_mvba_commitqc_neg i j c v =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, hc, -⟩ := htr
      exact not_certified _ _ _ hc
    case mvba_terminate =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, hdec, -⟩ := htr
      exact not_decided _ _ _ hdec
    case cast_fb_commit =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, -, hdec, -⟩ := htr
      exact not_decided _ _ _ hdec
    all_goals wunfold htr
    all_goals (repeat (obtain ⟨_, htr⟩ := htr))
    all_goals wnorm
    all_goals first | omega | wquorum | wmember))

/-- The availability report, enabled throughout for a representation with
no `FallbackQC` entry, and owed nowhere, since nobody holds a meta-block. -/
def IsAvail (l : CL) : Prop := ∃ i v n, l = .mvba_avail_ready i v n

theorem quiet0 {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (cst 0) l := by wquiet
theorem quiet11 {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (cst 11) l := by wquiet
theorem quiet36 {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (cst 36) l := by wquiet
theorem quiet37 {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (cst 37) l := by wquiet
theorem quiet38 {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (cst 38) l := by wquiet

/-- At the final local state no fair label is enabled, the availability
report aside: the rows by `quiet38`, and the three phase markers because the
phase is past the last landmark. -/
theorem justice38 (l : CL) (hj : JusticeLabel l) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (cst 38) l := by
  by_cases hm : MarkerLabel l
  · obtain ⟨L, rfl⟩ := (markerLabel_iff l).mp hm
    rintro ⟨s', htr⟩
    cases L <;> simp only [Landmark.marker] at htr <;> wunfold htr
  · obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp ((hop_isSome_iff l).mpr ⟨hj, hm⟩)
    exact quiet38 hh ha

/-! ## The bridge -/

/-- A ghost certificate over a supermajority whose members' signatures never
appear, refuted by the quorum's having a member: nobody signs a negative vote
entry or casts a fallback vote. -/
local macro "wnocert" h:ident : tactic =>
  `(tactic| (
    simp only [Chorus.vote_quorum_neg, Chorus.fbcert] at $h:ident
    obtain ⟨q, hq, hall⟩ := $h:ident
    dsimp +instances only [Chorus.Witness.nsetC, byzNodeSetFin] at hq hall
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos (by omega : 0 < q.val.length)
    have := hall r (by simpa using hr)
    simp +unfoldPartialApp [Veil.FieldRepresentation.get, instIsSubStateOfRefl.getFrom_id, cst] at this))

/-- **The only certifiable representation is `v⋆`**, at every local index:
a non-proposer has no entry, and the proposer's entry is its one root held by
a FastQC, since no negative FastQC and no `FBCert` ever exist. -/
theorem certified_eq (m : Nat) (v : V) (hc : Certified (thS := thS) (thM := thM) (cst m) v) :
    v = Chorus.Witness.vstar := by
  obtain ⟨hpos, hneg, hall⟩ := hc
  funext j
  simp only [thS, Cadence.chorusTheory, thM, Chorus.Witness.thM, MetaBlock.entries,
    decide_eq_true_eq] at hpos hneg hall
  by_cases hj : j.val = 0
  · have hj0 : j = 0 := Fin.ext hj
    subst hj0
    rcases hall 0 (by decide) with ⟨M, hM⟩ | hM
    · cases hv : v 0 with
      | none => simp [hv] at hM
      | some p =>
        obtain ⟨u, k⟩ := p
        rcases (hpos 0 u (by simp [hv])).2 with ⟨hnf, -⟩ | ⟨-, -, h⟩
        · cases k
          · simp [Chorus.Witness.vstar]
          · simp [hv] at hnf
        · wnocert h
    · rcases (hneg 0 hM).2 with h | ⟨-, h⟩
      · wnocert h
      · wnocert h
  · cases hv : v j with
    | none => simp [Chorus.Witness.vstar, hj]
    | some p => exact absurd (hpos j p.1 (by simp [hv])).1 hj

end Composed.Witness

/-! ## The pinned trust base -/

/--
info: 'Composed.Witness.cstep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.cstep

/--
info: 'Composed.Witness.stut_tr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.stut_tr

/--
info: 'Composed.Witness.no_stutter_init' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.no_stutter_init

/--
info: 'Composed.Witness.certified_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.certified_eq
