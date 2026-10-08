import Cadence.Chorus.TimedTermination
import Mathlib.Tactic.IntervalCases

/-! # Chorus.Witness — the premises of the Chorus liveness claims are jointly satisfiable

[Bounds.md](../../docs/Bounds.md) §6.4.5. A conditional theorem whose
premises can never hold together proves nothing. This file exhibits **one
model** — an instance, a schedule and a labelled timed run — that satisfies
every premise of the three Chorus liveness claims at once:

* `Chorus.termination_premises_satisfiable`: every premise of
  `Chorus.termination` (its hypotheses, `chorusTheory`'s assumptions,
  `FJustice`, `MvbaAdmissible`, `ValidBridge` and the two caller premises),
  on the run with its clock forgotten;
* `Chorus.timedTermination_premises_satisfiable`: every premise of
  `TimedTerminationClaim` at the system's MVBA, `T := Mvba.mvbaTemporal …`
  (the timing model `SyncAtMvba`, `ValidBridge` and the caller's four
  conditions);
* `Chorus.totality_premises_satisfiable`: every premise of `TotalityClaim`,
  together with its antecedent (a correct validator finalizes).

Each proves the premises only, never a conclusion. Because the premises are
hypotheses, one model suffices. [Premises.md](../../docs/Premises.md) lists
the premises one by one, and [Bounds.md](../../docs/Bounds.md) §6.4.5 has
the detail of their joint satisfiability; this header describes the
model.
Its template is [Mvba/Witness.lean](../Mvba/Witness.lean).

## The instance

* Four validators, `Fin 4`, under Veil's tight family `byzNodeSetFin 4 1`
  (the family `Chorus.termination` is stated at): `f = 1`, validator 3
  Byzantine and silent. A quorum is a sorted list with at least three
  members.
* Validator 0 is the one proposer; roots are `Unit`, every root is
  well-encoded. The configuration is the system's `chorusTheory`, so a
  vector's entry is a root or a proposer's explicit absence.
* The MVBA's values are meta-block representations, `ent` drops their
  certificates (the system's `mvbaTheory`), and `valid := (· = v⋆)`, where
  `v⋆` gives the proposer its root held by a FastQC and every other
  validator nothing: the one representation a certificate check can pass
  in this run (`certified_eq`).
  Validator 0 leads every MVBA view.
* Views and time are `ℕ`; the schedule is the MVBA's fixed timeout
  (`Δ = 1`, `δ = 0`, `ρ = 1`) and the deadline `D = 1`. GST is 0.

## The run

At clock 0 the three correct validators participate, the proposer proposes
and sends all four validators their chunks, and the three correct ones
record them. At clock 1 the deadline marker fires; everyone votes, takes
the three correct votes, forms the FastQC, signs and casts the fast commit
vote, broadcasts the commit certificate, commits the proposer's entry on
validator 0's certificate and finalizes, all on the fast path, before the
fallback arm opens at 2. Then everyone abandons, as C1 permits: the
Cadence glue abandons a slot once it has finalized it. The fallback arm
(clock 2) and the MVBA arm (clock 3) open on a run in which nobody is active
any more, so nobody proposes to the MVBA, which stays quiet. The run then
idles on the MVBA's environment marking availability, one clock unit per
step. Bounds are upper bounds, so the eager run is a run the paper's
protocol produces; nobody sends anything the paper's rules would not.

## Why the proofs are short

Every state is a **closed formula in its index** (`st`, `mst`): a record is
present at index `n` exactly when the step that sets it comes before `n`. A
transition is then linear arithmetic over the index.

The clock advances only out of four **plateau ends** (indices 7, 42, 44
and the idle tail). At none of them is a row of the hop table enabled, the
availability report aside, which nobody owes since nobody holds a
meta-block. (Re-dissemination happens only inside a positive fallback
signature since F15, and nobody signs one here; building this witness found
F11, [Bounds.md](../../docs/Bounds.md) §6.4.5.) So every row of
`TimedJustice` holds with its antecedent false: the
run never leaves an obligation pending while time passes. The untimed
fairness holds for the same reason: in the idle tail no fair label is
enabled at all. -/

namespace Chorus

open Cadence
open scoped Cadence.Timed

namespace Witness

/-! ## The instance -/

/-- Validator 3 is the Byzantine one. -/
abbrev isByz : Fin 4 → Prop := fun i => i.val = 3

theorem hbyz : (List.ofFn (n := 4) id |>.filter (fun i => decide (isByz i))).length ≤ 1 := by
  decide

/-- Four validators, one Byzantine: Veil's tight family at `n = 4`, `f = 1`. -/
@[implicit_reducible]
def nsetC : ByzNodeSet (Fin 4) (ByzNSet 4) := byzNodeSetFin 4 1 rfl isByz hbyz

/-- The family's counting facts (`Cadence.byzNodeSetFin_counting`). -/
theorem cntC : ByzNodeSetCounting (Fin 4) (ByzNSet 4) nsetC := byzNodeSetFin_counting 4 1 rfl isByz hbyz

attribute [local instance] nsetC cntC natViewOrder

/-- The MVBA's values: meta-block representations over one root type `Unit`,
and their entry vectors. -/
abbrev V := MetaBlock (Fin 4) Unit
abbrev E := Fin 4 → Option Unit
abbrev MS := Mvba.State (Mvba.FieldAbstractType (Fin 4) (ByzNSet 4) V E ℕ)
abbrev Ph := Chorus.Phase_IndT
abbrev PC := Chorus.PathChoice_IndT
abbrev CS := StateAtMvba Unit (Fin 4) (ByzNSet 4) Unit ℕ Ph PC
abbrev CL := LabelAtMvba Unit (Fin 4) (ByzNSet 4) Unit ℕ Ph PC

/-- `v⋆`: the proposer's root, held by a `FastQC`, and nothing for every
other validator. -/
def vstar : V := fun j => if j.val = 0 then some ((), CertKind.fastQC) else none

/-- The MVBA theory: `ent` the representation's entries (the system's
configuration, `Cadence.mvbaTheory`), `valid := (· = v⋆)`; validator 0
leads every view. -/
def thM : Mvba.Theory (Fin 4) (ByzNSet 4) V E ℕ where
  ent := MetaBlock.entries
  valid v := decide (v = vstar)
  leader _ l := decide (l = 0)

/-! ## The states

`mst n` is the MVBA's state and `st n` Chorus's at index `n`. With `x` a
correct validator (`x < 3`), the step that sets each record is:

* `participating x`: `x`; the proposer's root, with its chunk to every
  validator: `3`; `local_entry_pos x`: `4 + x`;
* the oracle tick at 7 (validator 3's `Pre-Prepare`), the deadline marker
  at 8;
* the vote of `x`: `9 + x`; `x`'s receipt of `y`'s vote (`y < 3`):
  `12 + 3x + y`; its FastQC: `21 + x`; its commit signature: `24 + x`; its
  fast commit vote: `27 + x`; its commit certificate broadcast: `30 + x`;
  its committed entry, on validator 0's certificate, which it re-broadcasts:
  `33 + x`; its finalization: `36 + x`; its abandonment (Chorus's and the
  MVBA's): `39 + x`;
* a tick at 42, the fallback-arm marker at 43, a tick at 44, the MVBA-arm
  marker at 45, and ticks from 46 on, where the state no longer changes.

Nothing else is ever set: no negative entry, no fallback signature, no MVBA
input or decision, and validator 3 sends nothing. -/

/-- The MVBA's state at index `n`: quiet, abandoned by the three correct
validators (`39 + x`), and, from the first tick (7) on, one `Pre-Prepare`
from the Byzantine validator 3, which no correct validator acts on. -/
def mst (n : Nat) : MS where
  msg_preprepare l v x := decide (l.val = 3 ∧ v = 0 ∧ x = default ∧ 7 < n)
  msg_prepare _ _ _ := false
  msg_commit _ _ _ := false
  msg_timeout_qc _ _ _ _ := false
  msg_timeout_noqc _ _ := false
  msg_prepqc _ _ _ := false
  msg_commitqc _ _ _ := false
  msg_tc _ _ := false
  msg_tc_lock _ _ _ _ := false
  msg_tc_nolock _ _ := false
  input _ _ := false
  entered _ _ := false
  voted _ _ := false
  accepted _ _ _ := false
  local_prepqc _ _ _ := false
  timed_out _ _ := false
  commit_sent _ _ := false
  proposed_in _ _ := false
  decided _ _ := false
  abandoned i := decide (i.val < 3 ∧ 39 + i.val < n)
  avail_ready _ _ := false
  timer_expired _ _ := false
  tc_formed _ _ := false
  decided_qc _ _ _ := false

/-- The system's configuration: validator 0 the one proposer, every root
well-encoded, and the MVBA starting from `mst 0`. -/
noncomputable def thS : Chorus.Theory Unit (Fin 4) (ByzNSet 4) Unit MS V E (Mvba.Msg ℕ V E) Ph PC :=
  Cadence.chorusTheory (slot := Unit) (Phase := Ph) (PathChoice := PC)
    (fun j => decide (j.val = 0)) (fun _ => true) (mst 0)

/-- Chorus at the `Mvba` instance, at this configuration. -/
noncomputable abbrev sys := atMvba (slot := Unit) (Phase := Ph) (PathChoice := PC) thM

open Phase_IndT PathChoice_IndT in
/-- Chorus's state at index `n`. -/
def st (n : Nat) : CS where
  phase := if n ≤ 8 then pre_deadline else if n ≤ 43 then post_deadline
    else if n ≤ 45 then post_fb_arm else post_mvba_arm
  msg_proposer_signed j _ := decide (j.val = 0 ∧ 3 < n)
  msg_chunk k _ j _ := decide (k.val = 0 ∧ j.val = 0 ∧ 3 < n)
  msg_vote_pos_sig r j _ := decide (j.val = 0 ∧ r.val < 3 ∧ 9 + r.val < n)
  msg_vote_neg_sig _ _ := false
  msg_vote_cast r := decide (r.val < 3 ∧ 9 + r.val < n)
  msg_fb_pos_sig _ _ _ := false
  msg_fb_neg_sig _ _ := false
  msg_fallback_sig _ := false
  msg_commit_pos_sig r j _ := decide (j.val = 0 ∧ r.val < 3 ∧ 24 + r.val < n)
  msg_commit_neg_sig _ _ := false
  msg_commit_cast r := decide (r.val < 3 ∧ 27 + r.val < n)
  msg_commitqc_pos c j _ := decide (j.val = 0 ∧ c.val < 3 ∧ 30 + c.val < n)
  msg_commitqc_neg _ _ := false
  msg_decrypt_share r := decide (r.val < 3 ∧ 9 + r.val < n)
  msg_fbcommit_sig _ _ := false
  msg_fbcommitqc _ _ := false
  msg_mvba_cert _ _ := false
  local_fastqc_pos i j _ := decide (j.val = 0 ∧ i.val < 3 ∧ 21 + i.val < n)
  local_fastqc_neg _ _ := false
  mvba_st := mst n
  aux_mvba_decided_pos _ _ := false
  aux_mvba_decided_neg _ := false
  local_mvba_complete _ := false
  local_entry_pos i j _ := decide (j.val = 0 ∧ i.val < 3 ∧ 4 + i.val < n)
  local_entry_neg _ _ := false
  local_voted i := decide (i.val < 3 ∧ 9 + i.val < n)
  local_path i := if i.val < 3 ∧ 27 + i.val < n then fast else none
  local_committed i := decide (i.val < 3 ∧ 36 + i.val < n)
  local_committed_pos i j _ := decide (j.val = 0 ∧ i.val < 3 ∧ 33 + i.val < n)
  local_committed_neg _ _ := false
  aux_fb_neg_qv _ _ _ := false
  local_vote_rcv_pos i r j _ :=
    decide (j.val = 0 ∧ i.val < 3 ∧ r.val < 3 ∧ 12 + 3 * i.val + r.val < n)
  local_vote_rcv_neg _ _ _ := false
  local_commit_entry i j := decide (j.val = 0 ∧ i.val < 3 ∧ 24 + i.val < n)
  local_fb_entry _ _ := false
  local_commitqc_sent c j := decide (j.val = 0 ∧ c.val < 3 ∧ 30 + c.val < n)
  local_fbcommitqc_sent _ := false
  local_mvba_cert_sent _ := false
  local_mvba_recorded _ _ := false
  local_mvba_qc_accepted _ := false
  local_fbcommit_voted _ := false
  local_avail_marked _ _ := false
  participating i := decide (i.val < 3 ∧ i.val < n)
  abandoned i := decide (i.val < 3 ∧ 39 + i.val < n)

/-! The enum classes' constants are the generated inductive's constructors. -/

@[simp] theorem ph_pre : (Phase_EnumClass.pre_deadline : Ph) = .pre_deadline := rfl
@[simp] theorem ph_post : (Phase_EnumClass.post_deadline : Ph) = .post_deadline := rfl
@[simp] theorem ph_fb : (Phase_EnumClass.post_fb_arm : Ph) = .post_fb_arm := rfl
@[simp] theorem ph_mvba : (Phase_EnumClass.post_mvba_arm : Ph) = .post_mvba_arm := rfl
@[simp] theorem pc_none : (PathChoice_EnumClass.none : PC) = .none := rfl
@[simp] theorem pc_fast : (PathChoice_EnumClass.fast : PC) = .fast := rfl
@[simp] theorem pc_fb : (PathChoice_EnumClass.fallback : PC) = .fallback := rfl

/-! ## The labels -/

/-- The correct validators, the run's one quorum. -/
def Q : ByzNSet 4 := ⟨[0, 1, 2], by decide⟩

/-- The oracle tick: the Byzantine validator 3 sends a `Pre-Prepare` (an
internal MVBA step, unfair, and the same message at every tick). The clock
moves on it. -/
def tick (n : Nat) : CL := .mvba_step (mst (n + 1))

/-- The label of each step of the active prefix. -/
def prefixLabel : Nat → CL
  | 0 => .participate 0
  | 1 => .participate 1
  | 2 => .participate 2
  | 3 => .propose 0 ()
  | 4 => .record_chunk 0 0 ()
  | 5 => .record_chunk 1 0 ()
  | 6 => .record_chunk 2 0 ()
  | 7 => tick 7
  | 8 => .advance_to_deadline
  | 9 => .vote 0
  | 10 => .vote 1
  | 11 => .vote 2
  | 12 => .receive_vote_pos 0 0 0 ()
  | 13 => .receive_vote_pos 0 1 0 ()
  | 14 => .receive_vote_pos 0 2 0 ()
  | 15 => .receive_vote_pos 1 0 0 ()
  | 16 => .receive_vote_pos 1 1 0 ()
  | 17 => .receive_vote_pos 1 2 0 ()
  | 18 => .receive_vote_pos 2 0 0 ()
  | 19 => .receive_vote_pos 2 1 0 ()
  | 20 => .receive_vote_pos 2 2 0 ()
  | 21 => .aggregate_fastqc_pos 0 0 () Q
  | 22 => .aggregate_fastqc_pos 1 0 () Q
  | 23 => .aggregate_fastqc_pos 2 0 () Q
  | 24 => .commit_sign_pos 0 0 ()
  | 25 => .commit_sign_pos 1 0 ()
  | 26 => .commit_sign_pos 2 0 ()
  | 27 => .cast_fast_commit 0
  | 28 => .cast_fast_commit 1
  | 29 => .cast_fast_commit 2
  | 30 => .broadcast_commitqc_pos 0 0 () Q
  | 31 => .broadcast_commitqc_pos 1 0 () Q
  | 32 => .broadcast_commitqc_pos 2 0 () Q
  | 33 => .commit_assign_pos_fast 0 0 () 0
  | 34 => .commit_assign_pos_fast 1 0 () 0
  | 35 => .commit_assign_pos_fast 2 0 () 0
  | 36 => .finalize_commit 0
  | 37 => .finalize_commit 1
  | 38 => .finalize_commit 2
  | 39 => .abandon 0 (mst 40)
  | 40 => .abandon 1 (mst 41)
  | 41 => .abandon 2 (mst 42)
  | 42 => tick 42
  | 43 => .advance_to_fb_arm
  | 44 => tick 44
  | _ => .advance_to_mvba_arm

/-- The idle step: the oracle tick at the idle state. -/
def idle : CL := .mvba_step (mst 46)

/-- The label of the step out of index `n`: the active prefix, then the idle
step for ever. -/
def lbl (n : Nat) : CL := if n < 46 then prefixLabel n else idle

/-! ## Proof tactics

A transition of `sys` unfolds to its guards and an equation between the
updated state and the post-state. At `st` both sides are structure literals
of `decide`d linear facts, so the equation splits field by field and every
remaining goal is linear arithmetic over the index; a guard over a quorum
is met by `Q`. -/

-- A step's unfolding is one `simp` over all 38 state components, and the
-- default heartbeat budget does not cover the largest (the bulk-update
-- `vote`).
set_option maxHeartbeats 4000000

-- One simp-lemma list serves every step of the run, so a given step leaves
-- some of its entries unused.
set_option linter.unusedSimpArgs false

/-- Normalise `decide`d facts over this instance to linear arithmetic. -/
local macro "wnorm" : tactic =>
  `(tactic| (
    try dsimp +instances only [nsetC, byzNodeSetFin, natViewOrder] at *
    try simp only [← Bool.decide_and, ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq,
      Bool.not_eq_true, decide_eq_false_iff_not, Fin.ext_iff, List.mem_cons, List.mem_nil_iff,
      List.length_cons, List.length_nil, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.val_zero,
      exists_eq_left, exists_const, and_true, true_and, or_false] at *))

/-- Split a goal into its conjuncts and close each: by arithmetic, by
splitting a path choice, or, for a guard over a quorum, with `Q`. -/
local macro "wclose" : tactic =>
  `(tactic| (and_intros <;> intros <;> first | trivial | omega | (split_ifs <;> first | rfl | omega | (simp only [decide_eq_decide] at * <;> omega) | (simp_all <;> omega)) | (refine ⟨Q, ?_, ?_⟩ <;> simp [Q] <;> omega)))

/-- Evaluate the field-representation `get`/`set` pair, and `st`, `mst`. -/
local macro "wfields" : tactic =>
  `(tactic| (
    try simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id,
      Veil.FieldRepresentation.get, st, mst, thS, Cadence.chorusTheory, Q, Chorus.chunk_quorum,
      Chorus.State.mk.injEq, Mvba.State.mk.injEq, funext_iff]))

/-- Expose a transition's guards and update, evaluated at `st`. -/
local macro "wexpose" : tactic =>
  `(tactic| (simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp]; wfields))

/-- Evaluate `lbl` at a literal index to the label it names. -/
local macro "wlabel" : tactic =>
  `(tactic| simp only [lbl, prefixLabel, tick, Nat.reduceLT, Nat.reduceAdd, ↓reduceIte])

/-- One ordinary step of the run. -/
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

/-- Close an equation between two `mst` literals, field by field: the
`Pre-Prepare` record by a split on whether the representation is the sent
one, and the abandonment record by arithmetic. -/
local macro "mclose" : tactic =>
  `(tactic| (
    refine ⟨fun a v e => ?_, fun a => ?_⟩
    · have hc : (∀ x, (default : Option (Unit × CertKind)) = e x) ↔ (∀ x, e x = default) :=
        ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩
      simp only [hc, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide, Fin.ext_iff,
        Fin.val_zero]
      by_cases hP : ∀ x, e x = default <;>
        simp only [hP, implies_true, true_and, and_true, false_and, and_false, or_false] <;> omega
    · simp only [← Bool.decide_and, ← Bool.decide_or, decide_eq_decide, Fin.ext_iff,
        Fin.lt_def, Fin.le_def]
      omega))

/-! ## The MVBA's steps -/

/-- The Byzantine `Pre-Prepare` is an internal MVBA step, not one of its
inputs. -/
theorem tickLabel_not_input : ¬ Mvba.Label.isInput (.byz_preprepare (3 : Fin 4) 0 (default : V) :
    Mvba.Label (Fin 4) (ByzNSet 4) V E ℕ) := fun h => by
  rcases Mvba.Label.isInput_cases h with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;> cases h

/-- The MVBA's step at a tick: validator 3's `Pre-Prepare`, sent at 7 and
unchanged after. -/
theorem tick_tr (n : Nat) (h : n = 7 ∨ 42 ≤ n) :
    (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).tr thM (mst n)
      (.byz_preprepare 3 0 default) (mst (n + 1)) := by
  mexpose
  refine ⟨by dsimp +instances only [nsetC, byzNodeSetFin]; decide, ?_⟩
  mclose

theorem tick_step (n : Nat) (h : n = 7 ∨ 42 ≤ n) :
    (Mvba.mvbaSafety thM).step (mst n) (mst (n + 1)) :=
  ⟨_, tickLabel_not_input, tick_tr n h⟩

/-- Chorus's `abandon i` forwards to the MVBA's `abandon()`, at `39 + i`. -/
theorem abandon_tr (i : Fin 4) (hi : i.val < 3) :
    (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).tr thM (mst (39 + i.val))
      (.abandon i) (mst (39 + i.val + 1)) := by
  mexpose
  mclose

/-- From index 42 on the MVBA's state no longer changes. -/
theorem mst_stable {n : Nat} (h : 42 ≤ n) : mst n = mst 42 := by
  simp only [mst, Mvba.State.mk.injEq, funext_iff, decide_eq_decide]
  and_intros <;> intros <;> first | trivial | omega |
    exact ⟨fun ⟨a, b, c, _⟩ => ⟨a, b, c, by omega⟩, fun ⟨a, b, c, _⟩ => ⟨a, b, c, by omega⟩⟩

/-- The MVBA is quiet at every index: nobody has proposed to it. -/
theorem mquiet (n : Nat) : Mvba.Quiet (mst n) := by
  simp [Mvba.Quiet, mst]

/-- Nobody decides in the MVBA. -/
theorem not_decided (n : Nat) (i : Fin 4) (v : V) : ¬ (Mvba.mvbaSafety thM).decided (mst n) i v :=
  fun h => Bool.false_ne_true h

/-- Nobody ever holds a valid MVBA commit certificate: none is formed. -/
theorem not_certified (n : Nat) (c : Mvba.Msg ℕ V E) (e : E) :
    ¬ (Mvba.mvbaSafety thM).certifies (mst n) c e := by
  show ¬ Mvba.Certifies (mst n) c e
  cases c <;> simp [Mvba.Certifies, Veil.FieldRepresentation.get, mst]

/-- No MVBA decision ever outputs a certificate: nobody decides. -/
theorem not_decidedCert (n : Nat) (i : Fin 4) (c : Mvba.Msg ℕ V E) :
    ¬ (Mvba.mvbaSafety thM).decidedCert (mst n) i c := by
  show ¬ Mvba.DecidedCert (mst n) i c
  cases c <;> simp [Mvba.DecidedCert, Veil.FieldRepresentation.get, mst]

/-- Nobody ever holds a meta-block in the MVBA. -/
theorem not_accepted (n : Nat) (i : Fin 4) (w : ℕ) (v : V) : ¬ (mst n).accepted i w v = true := by
  simp [mst]

/-- An MVBA step of Chorus (the oracle tick, or `abandon`'s forwarding): its
MVBA guard first, from the lemmas about `mst`, then the fields. -/
local macro "wmvba" h:term : tactic =>
  `(tactic| (
    simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp]
    refine ⟨$h, ?_⟩
    wfields <;> wnorm <;> wclose))

/-! ## The run is a run of the model

The theory meets the model's assumptions, index 0 is initial, and every
step is a transition: the 46 steps of the active prefix, then the idle tail,
whose state no longer changes. -/

/-- The MVBA model's assumption at `thM`: one leader, validator 0, for every view. -/
theorem mholds : (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).assumptions thM := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Assumptions, Mvba.leader_functional,
    thM, instIsSubReaderOfRefl.readFrom_id]
  intro _ L L' h h'
  simp only [decide_eq_true_eq] at h h'
  rw [h, h']

theorem mstarts : (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).init thM (mst 0) := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init, trSimp]
  simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      Veil.FieldRepresentation.get, mst, Mvba.State.mk.injEq, funext_iff]

/-- Chorus's assumptions at `chorusTheory`: the MVBA starts initial
(`Cadence.chorusTheory_assumptions`). -/
theorem holds : sys.assumptions thS :=
  (Cadence.chorusTheory_assumptions thM _ _ (mst 0)).mpr ⟨mholds, mstarts⟩

theorem starts : sys.init thS (st 0) := by
  simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Init, trSimp]
  simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id,
      Veil.FieldRepresentation.get, st, thS, Cadence.chorusTheory, Chorus.State.mk.injEq, funext_iff]

theorem steps_0 (n : Nat) (h : n < 7) : sys.tr thS (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem steps_1 (n : Nat) (h₁ : 8 ≤ n) (h : n < 39) : sys.tr thS (st n) (lbl n) (st (n + 1)) := by
  interval_cases n <;> wlabel <;> wstep

theorem step_7 : sys.tr thS (st 7) (lbl 7) (st 8) := by wlabel; wmvba tick_step 7 (by omega)
theorem step_39 : sys.tr thS (st 39) (lbl 39) (st 40) := by wlabel; wmvba abandon_tr 0 (by decide)
theorem step_40 : sys.tr thS (st 40) (lbl 40) (st 41) := by wlabel; wmvba abandon_tr 1 (by decide)
theorem step_41 : sys.tr thS (st 41) (lbl 41) (st 42) := by wlabel; wmvba abandon_tr 2 (by decide)
theorem step_42 : sys.tr thS (st 42) (lbl 42) (st 43) := by wlabel; wmvba tick_step 42 (by omega)
theorem step_43 : sys.tr thS (st 43) (lbl 43) (st 44) := by wlabel; wstep
theorem step_44 : sys.tr thS (st 44) (lbl 44) (st 45) := by wlabel; wmvba tick_step 44 (by omega)
theorem step_45 : sys.tr thS (st 45) (lbl 45) (st 46) := by wlabel; wstep

/-- From index 46 on the state no longer changes. -/
theorem st_stable {n : Nat} (h : 46 ≤ n) : st n = st 46 := by
  simp only [st, Chorus.State.mk.injEq, mst_stable (show 42 ≤ n by omega),
    mst_stable (show 42 ≤ 46 by omega), if_neg (show ¬ n ≤ 8 by omega),
    if_neg (show ¬ n ≤ 43 by omega), if_neg (show ¬ n ≤ 45 by omega), funext_iff, decide_eq_decide]
  and_intros <;> intros <;> first | trivial | rfl | omega | (split_ifs <;> first | rfl | omega)

/-- The idle step is a transition from the idle state to itself. -/
theorem tail_step : sys.tr thS (st 46) idle (st 46) := by
  have h := tick_step 46 (Or.inr (by omega))
  rw [mst_stable (n := 47) (by omega), ← mst_stable (n := 46) (by omega)] at h
  simp only [idle]
  wmvba h

theorem steps (n : Nat) : sys.tr thS (st n) (lbl n) (st (n + 1)) := by
  by_cases h46 : 46 ≤ n
  · rw [st_stable h46, st_stable (n := n + 1) (by omega)]
    have : lbl n = idle := by simp only [lbl, if_neg (show ¬ n < 46 by omega)]
    rw [this]
    exact tail_step
  by_cases h7 : n < 7
  · exact steps_0 n h7
  by_cases h39 : 8 ≤ n ∧ n < 39
  · exact steps_1 n h39.1 h39.2
  have : n = 7 ∨ n = 39 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step_7
  · exact step_39
  · exact step_40
  · exact step_41
  · exact step_42
  · exact step_43
  · exact step_44
  · exact step_45

/-- The clock: 0 up to the first plateau end, then 1, 2 and 3 at the three
landmarks, and one unit per step once the run is idle. -/
def clk (n : Nat) : ℕ :=
  if n ≤ 7 then 0 else if n ≤ 42 then 1 else if n ≤ 44 then 2 else if n ≤ 46 then 3 else n - 43

/-- **The labelled timed run.** GST is 0. -/
noncomputable def run : TChorusRun thS thM ℕ where
  at' := st
  lbl := lbl
  holds := holds
  starts := starts
  steps := steps
  clk := clk
  clk_mono n := by simp only [clk]; split_ifs <;> omega
  clk_unbounded t := ⟨t + 47, by simp only [clk]; split_ifs <;> omega⟩
  gst := 0

/-- A correct validator is one of the first three. -/
theorem correct_lt {p : Fin 4} (h : ¬ nsetC.is_byz p = true) : p.val < 3 := by
  dsimp +instances only [nsetC, byzNodeSetFin] at h
  simp only [decide_eq_true_eq] at h
  omega

/-! ## No row is enabled at a plateau's end

At 42, 44 and in the idle tail every correct validator has abandoned, so
every gated row is disabled; the processing rows have fired, the vote
receipts among them; the MVBA is quiet and nobody has decided. At 7, before
the deadline, every chunk is recorded and nothing else is due. -/

/-- The five supermajorities of four validators. -/
theorem supermajority_cases (q : ByzNSet 4) (h : 2 * 1 + 1 ≤ q.val.length) :
    q.val = [0, 1, 2] ∨ q.val = [0, 1, 3] ∨ q.val = [0, 2, 3] ∨ q.val = [1, 2, 3] ∨
      q.val = [0, 1, 2, 3] := by
  have hall : ∀ q ∈ allByzNSets 4, 2 * 1 + 1 ≤ q.val.length →
      (q.val = [0, 1, 2] ∨ q.val = [0, 1, 3] ∨ q.val = [0, 2, 3] ∨ q.val = [1, 2, 3] ∨
        q.val = [0, 1, 2, 3]) := by decide
  exact hall q (allByzNSets_complete q) h

/-- Expose a transition's guards in a hypothesis, evaluated at `st`. -/
local macro "wunfold" h:ident : tactic =>
  `(tactic| (
    simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at $h:ident
    try simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id,
      Veil.FieldRepresentation.get, st, mst, thS, Cadence.chorusTheory, Q, Mvba.mvbaSafety] at $h:ident))

/-- A guard over a supermajority's members, refuted by the five
supermajorities. -/
local macro "wquorum" : tactic =>
  `(tactic| (rcases supermajority_cases ‹ByzNSet 4› ‹_› with h | h | h | h | h <;>
    simp only [h, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at * <;> omega))

/-- A guard asking a supermajority to have no member at all. -/
local macro "wmember" : tactic =>
  `(tactic| (obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos (by omega : 0 < (‹ByzNSet 4›).val.length); simp_all))

-- Refute a row's enabledness at a concrete state of the run: dismiss the
-- labels off the hop table, take the handoff to the MVBA's own quiet lemma,
-- the decision-reading labels to `not_decided`, the MVBA certificate's
-- finalization routes to `not_certified`, and read every other row's guards
-- at the state.
set_option hygiene false in
local macro "wquiet" : tactic =>
  `(tactic| (
    rintro ⟨s', htr⟩
    cases l
    all_goals first | (simp [hop] at hh; done) | skip
    all_goals first | exact absurd ⟨_, _, _, rfl⟩ ha | skip
    case accept_mvba_commitqc i r c mn =>
      obtain ⟨w, e, x, _, -, -, h⟩ := accept_mvba_commitqc_tr htr
      exact Mvba.not_enabled_decide_of_quiet (mquiet _) ⟨_, h⟩
    case on_mvba_decide_pos =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, hdec, -⟩ := htr
      exact not_decided _ _ _ hdec
    case on_mvba_decide_neg =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, hdec, -⟩ := htr
      exact not_decided _ _ _ hdec
    case commit_assign_pos_mvba =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, -, -, -, -, hc, -⟩ := htr
      exact not_certified _ _ _ hc
    case commit_assign_neg_mvba =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, -, -, -, -, hc, -⟩ := htr
      exact not_certified _ _ _ hc
    case send_mvba_cert =>
      simp only [sys, atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
      obtain ⟨-, -, -, hdc, -⟩ := htr
      exact not_decidedCert _ _ _ hdc
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

/-- At 7, the end of clock 0, no row other than the availability report is
enabled. -/
theorem quiet7 {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd)
    (ha : ¬ IsAvail l) : ¬ Enabled sys thS (st 7) l := by
  wquiet

theorem quiet42 {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (st 42) l := by
  wquiet
theorem quiet44 {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (st 44) l := by
  wquiet
theorem quiet46 {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (st 46) l := by
  wquiet

/-- The indices out of which the clock advances. -/
def PlateauEnd (n : Nat) : Prop := n = 7 ∨ n = 42 ∨ n = 44 ∨ 46 ≤ n

/-- No row is enabled at a plateau end, the availability report aside. -/
theorem quiet {n : Nat} (hn : PlateauEnd n) {l : CL} {hd : Mvba.Hop} (hh : hop l = some hd)
    (ha : ¬ IsAvail l) : ¬ Enabled sys thS (st n) l := by
  rcases hn with rfl | rfl | rfl | hn
  · exact quiet7 hh ha
  · exact quiet42 hh ha
  · exact quiet44 hh ha
  · rw [st_stable hn]; exact quiet46 hh ha

/-- Every index is followed, on the same clock reading, by a plateau end. -/
theorem plateau_after (N : Nat) : ∃ P, PlateauEnd P ∧ N ≤ P ∧ clk P = clk N := by
  by_cases h1 : N ≤ 7
  · exact ⟨7, Or.inl rfl, h1, by simp only [clk]; split_ifs <;> omega⟩
  by_cases h2 : N ≤ 42
  · exact ⟨42, Or.inr (Or.inl rfl), h2, by simp only [clk]; split_ifs <;> omega⟩
  by_cases h3 : N ≤ 44
  · exact ⟨44, Or.inr (Or.inr (Or.inl rfl)), h3, by simp only [clk]; split_ifs <;> omega⟩
  · exact ⟨max N 46, Or.inr (Or.inr (Or.inr (le_max_right _ _))), le_max_left _ _,
      by simp only [clk]; split_ifs <;> omega⟩

/-- At 42 nobody is active: the three correct validators have abandoned, and
validator 3 never participates. -/
theorem inactive42 (k : Fin 4) : ¬ Active (st 42) k := by
  simp only [Active, st]
  simp only [decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not]
  omega

/-- **A buffered family holds with its antecedent false** on this run, at any
bounds, if no member is the availability report: its window reaches a plateau end
after the gate's index `N'` on the same clock reading, where no member is
enabled. -/
theorem bufferedFairFamily_of_quiet {D δ : ℕ} {C gate : CS → Prop} {S : CL → Prop}
    (hS : ∀ l, S l → (∃ h, hop l = some h) ∧ ¬ IsAvail l) :
    BufferedFairFamily run D δ C gate S := by
  intro N N' hNN' h1 h2
  obtain ⟨P, hP, hle, hclk⟩ := plateau_after N'
  have hW : run.clk P ≤ run.bufWindow N N' D δ := by
    show clk P ≤ _
    rw [hclk]
    exact le_trans (run.clk_le_ref N') (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  obtain ⟨-, hen⟩ := h1 P (le_trans hNN' hle) hW
  obtain ⟨l, hl, hen⟩ := hen (h2 P hle hW)
  obtain ⟨⟨h, hh⟩, ha⟩ := hS l hl
  exact absurd hen (quiet hP hh ha)

theorem bufferedFair_of_quiet {D δ : ℕ} {C gate : CS → Prop} {l : CL} {h : Mvba.Hop}
    (hh : hop l = some h) (ha : ¬ IsAvail l) : BufferedFair run D δ C gate l :=
  bufferedFair_iff_family.mpr (bufferedFairFamily_of_quiet fun _ hl => ⟨⟨h, hl ▸ hh⟩, hl ▸ ha⟩)

/-- **A buffered family holds with its owed-condition false** throughout: the
window's first index is in it. -/
theorem bufferedFairFamily_of_not_owed {D δ : ℕ} {C gate : CS → Prop} {S : CL → Prop}
    (hC : ∀ n, ¬ C (st n)) : BufferedFairFamily run D δ C gate S := by
  intro N N' hNN' h1 _
  exact (hC N' (h1 N' hNN' (le_trans (run.clk_le_ref N')
    (le_trans (Nat.le_add_right _ _) (le_max_right _ _)))).1).elim

/-! ## The schedule, and the instance's hypotheses -/

/-- The MVBA's fixed-timeout schedule (`Δ = 1`, `δ = 0`, `ρ = 1`) with the
availability bound of the composed system, `Δ_sync = Δ = 1`, and the
deadline `D = 1`. A local step is no slower than a hop or a retransmission,
`0 ≤ 1`, and the availability window covers a hop, `1 ≤ 1`. The MVBA's own fixed schedule
(`Mvba.Schedule.fixedNat`, `Δ_sync = 0`) is left as it is; the timeout `5`
still clears the chain's latency, `Lcert 1 0 1 = 4`. -/
def schC : Chorus.Schedule ℕ ℕ where
  mvba := { Mvba.Schedule.fixedNat ℕ 1 with
    Δsync := 1
    Δsync_nonneg := Nat.zero_le _
    τ_ramp := fun _ _ => by simp [Mvba.Lcert, Mvba.Schedule.fixedNat] }
  D := 1
  δ_le_Δ := Nat.zero_le _
  δ_le_ρ := Nat.zero_le _
  Δ_le_Δsync := le_rfl

/-- `ByzNodeSetHonestQuorum` at this instance: the three correct validators. -/
@[implicit_reducible]
def hqeC : ByzNodeSetHonestQuorum (Fin 4) (ByzNSet 4) nsetC where
  honestQuorum := Q
  honestQuorum_supermajority := by
    dsimp +instances [nsetC, byzNodeSetFin, Q]
    decide
  honestQuorum_correct := by
    dsimp +instances [nsetC, byzNodeSetFin, Q]
    decide

/-- **(A-leader-rotation-k)** at `k = 1`: validator 0 leads every view. -/
theorem rotation : Mvba.LeaderRotation natViewOrderEnum schC.mvba.k thM := by
  intro v
  refine ⟨0, Nat.one_pos, 0, rfl, ?_⟩
  dsimp +instances only [nsetC, byzNodeSetFin]
  decide

/-! ## (a) The timed premises -/

/-- **(Δδ-justice)**: every row, the four families (the proposal on its two
triggers, the handoff and the availability report) and the fallback commit
vote, with their antecedents false. Nobody decides in the MVBA, so the vote's
gate, its own decision, never opens. -/
theorem timedJustice : TimedJustice schC run := by
  refine ⟨fun l h hh hfam => ?_, fun _ _ => bufferedFairFamily_of_quiet fun _ ⟨_, hl⟩ =>
      ⟨⟨.net, by rw [hl]; rfl⟩, fun ⟨_, _, _, h⟩ => (by rw [hl] at h; cases h)⟩,
    fun _ _ => bufferedFairFamily_of_quiet fun _ ⟨_, hl⟩ =>
      ⟨⟨.net, by rw [hl]; rfl⟩, fun ⟨_, _, _, h⟩ => (by rw [hl] at h; cases h)⟩,
    fun _ => bufferedFairFamily_of_quiet fun _ ⟨_, _, _, hl⟩ =>
      ⟨⟨.net, by rw [hl]; rfl⟩, fun ⟨_, _, _, h⟩ => (by rw [hl] at h; cases h)⟩,
    fun i v => bufferedFairFamily_of_not_owed fun n ⟨w, hw⟩ => not_accepted n i w v hw,
    fun i v N N' _ _ h2 => ?_⟩
  · exact bufferedFair_of_quiet hh fun ⟨_, _, _, h⟩ => hfam (h ▸ trivial)
  · obtain ⟨-, hd, -⟩ := h2 N' le_rfl (le_trans (run.clk_le_ref N')
      (le_trans (Nat.le_add_right _ _) (le_max_right _ _)))
    exact (not_decided N' i v hd).elim

theorem lbl_deadline {n : Nat} (h : lbl n = .advance_to_deadline) : n = 8 := by
  by_cases hn : n < 46
  · revert h; interval_cases n <;> simp [lbl, prefixLabel, tick]
  · simp [lbl, if_neg hn, idle] at h

theorem lbl_fbArm {n : Nat} (h : lbl n = .advance_to_fb_arm) : n = 43 := by
  by_cases hn : n < 46
  · revert h; interval_cases n <;> simp [lbl, prefixLabel, tick]
  · simp [lbl, if_neg hn, idle] at h

theorem lbl_mvbaArm {n : Nat} (h : lbl n = .advance_to_mvba_arm) : n = 45 := by
  by_cases hn : n < 46
  · revert h; interval_cases n <;> simp [lbl, prefixLabel, tick]
  · simp [lbl, if_neg hn, idle] at h

/-- **(P-phase)**: each marker fires at its landmark's clock reading (`D = 1`,
`D + Δ = 2`, `D + 2Δ = 3`), and the phase reaches the landmark there. -/
theorem phasePunctual : PhasePunctual schC run := by
  intro L
  cases L
  · refine ⟨fun n hn => ?_, 9, ?_, ?_⟩
    · rw [lbl_deadline hn]; decide
    · simp [Landmark.Reached, run, st]
    · decide
  · refine ⟨fun n hn => ?_, 44, ?_, ?_⟩
    · rw [lbl_fbArm hn]; decide
    · simp [Landmark.Reached, run, st]
    · decide
  · refine ⟨fun n hn => ?_, 46, ?_, ?_⟩
    · rw [lbl_mvbaArm hn]; decide
    · simp [Landmark.Reached, run, st]
    · decide

/-- **(P-incl)**: every chunk the correct proposer sent is recorded. The
proposer sends every validator its chunk at clock 0, the three correct ones
record it at once, and the deadline marker fires only after them, at
clock 1. The tie-break premise of censorship resistance holds of the
witness, at its schedule and at any other. -/
theorem deadlineInclusive (sch : Chorus.Schedule ℕ ℕ) : DeadlineInclusive sch run := by
  intro n i j m hi _ _ hc _
  have hi3 := correct_lt hi
  refine ⟨7, (), ?_⟩
  simp only [run, st, decide_eq_true_eq] at hc ⊢
  omega

/-! ## The MVBA's projection: quiet, abandoned by the caller -/

/-- The MVBA's label at each index: the three abandonments, and validator
3's `Pre-Prepare` at every tick. -/
def mlbl (n : Nat) : Mvba.Label (Fin 4) (ByzNSet 4) V E ℕ :=
  if n = 39 then .abandon 0 else if n = 40 then .abandon 1 else if n = 41 then .abandon 2
  else .byz_preprepare 3 0 default

/-- The MVBA moves at the ticks and at the three abandonments, and nowhere
else. -/
theorem mvbaStep_cases {n : Nat} (h : MvbaStepLabel (lbl n)) :
    n = 7 ∨ n = 39 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 44 ∨ 46 ≤ n := by
  by_cases hn : n < 46
  · revert h; interval_cases n <;> simp [lbl, prefixLabel, tick, MvbaStepLabel]
  · omega

theorem realizes (n : Nat) (h : MvbaStepLabel (lbl n)) :
    (Mvba.relationalTransitionSystem (Fin 4) (ByzNSet 4) V E ℕ).tr thM (mst n) (mlbl n) (mst (n + 1)) := by
  rcases mvbaStep_cases h with rfl | rfl | rfl | rfl | rfl | rfl | h46
  · exact tick_tr 7 (Or.inl rfl)
  · exact abandon_tr 0 (by decide)
  · exact abandon_tr 1 (by decide)
  · exact abandon_tr 2 (by decide)
  · exact tick_tr 42 (Or.inr le_rfl)
  · exact tick_tr 44 (Or.inr (by omega))
  · have ht := tick_tr 42 (Or.inr le_rfl)
    rw [mst_stable (n := 43) (by omega)] at ht
    rw [mst_stable (n := n) (by omega), mst_stable (n := n + 1) (by omega)]
    have hl : mlbl n = .byz_preprepare 3 0 default := by
      simp only [mlbl, if_neg (show n ≠ 39 by omega), if_neg (show n ≠ 40 by omega),
        if_neg (show n ≠ 41 by omega)]
    rw [hl]
    exact ht

/-- **The MVBA's projection.** Its steps are the run's ticks and the
forwarded abandonments, labelled by the MVBA's own `byz_preprepare` and
`abandon`. The idle tail ticks for ever, so the MVBA is stepped infinitely
often. -/
noncomputable def proj : (mvbaComponent thS thM).Projection run.toLRun where
  lbl := mlbl
  realizes n h := realizes n h
  scheduled N := ⟨max N 46, le_max_left _ _, by
    show MvbaStepLabel (lbl (max N 46))
    simp only [lbl, if_neg (show ¬ max N 46 < 46 by omega), idle, MvbaStepLabel]⟩

/-- Every state of the projection is one of the MVBA states `mst`. -/
theorem proj_at (k : Nat) : proj.run.at' k = mst ((mvbaComponent thS thM).idx run.toLRun k) := rfl

/-- The projection never expires a timer. -/
theorem mlbl_ne_expire (n : Nat) (i : Fin 4) (v : ℕ) : mlbl n ≠ .expire_timer i v := by
  simp only [mlbl]; split_ifs <;> simp

/-- **The MVBA's own two timed clauses**, on the timed projection:
(Δ-justice) with its antecedent false, since no fair MVBA label is enabled
at a quiet state; (T-timer), since no timer fires and nobody enters a view. -/
theorem mvbaOwn : Mvba.BoundedJustice schC.mvba proj.timed ∧
    Mvba.TimerPunctual schC.mvba proj.timed := by
  refine ⟨Mvba.boundedJustice_of_quiet fun N D _ => ⟨N, le_rfl,
      le_trans (proj.timed.clk_le_ref N) (Nat.le_add_right _ _),
      fun _ _ hh => by
        show ¬ Enabled _ _ (proj.run.at' N) _
        rw [proj_at]
        exact Mvba.not_enabled_of_quiet (mquiet _) hh⟩,
    ⟨fun n i v _ hl => absurd hl (mlbl_ne_expire _ i v), fun m i v _ hent => ?_⟩⟩
  change (proj.run.at' m).entered i v = true at hent
  rw [proj_at] at hent
  simp [mst] at hent

/-- **The timing model at the system's MVBA**: (Δδ-justice), (P-phase), and
the MVBA's own two clauses on the projection. The
MVBA's clauses on its caller, the handoff and (Δ-avail), are derived
(`sync_of_syncAtMvba`, below, with the bridge). -/
theorem syncAtMvba : SyncAtMvba schC run :=
  ⟨timedJustice, phasePunctual, ⟨proj, mvbaOwn⟩⟩

/-! ## (b) The untimed premises, on the same run -/

/-- At the idle state no fair label is enabled: the rows by `quiet46`, and the
three phase markers because the phase is past the last landmark. -/
theorem justice46 (l : CL) (hj : JusticeLabel l) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (st 46) l := by
  by_cases hm : MarkerLabel l
  · obtain ⟨L, rfl⟩ := (markerLabel_iff l).mp hm
    rintro ⟨s', htr⟩
    cases L <;> simp only [Landmark.marker] at htr <;> wunfold htr
  · obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp ((hop_isSome_iff l).mpr ⟨hj, hm⟩)
    exact quiet46 hh ha

theorem justice_tail {n : Nat} (hn : 46 ≤ n) (l : CL) (hj : JusticeLabel l) (ha : ¬ IsAvail l) :
    ¬ Enabled sys thS (run.at' n) l := by
  show ¬ Enabled sys thS (st n) l
  rw [st_stable hn]
  exact justice46 l hj ha

/-- **(F-justice)**, every clause with its antecedent false: from any `N` on
the idle state is reached, and there no fair label is enabled. -/
theorem fJustice : FJustice run.toLRun :=
  ⟨fun l hj hfam N hen => absurd (hen (max N 46) (le_max_left _ _)).2
      (justice_tail (le_max_right _ _) l hj fun ⟨_, _, _, h⟩ => hfam (h ▸ trivial)),
    fun _ _ N hen => by
      obtain ⟨-, l, ⟨_, rfl⟩, hl⟩ := hen (max N 46) (le_max_left _ _)
      exact absurd hl (justice_tail (le_max_right _ _) _ ⟨fun h => h, fun h => h, fun h => h⟩
        fun ⟨_, _, _, h⟩ => by cases h),
    fun _ N hen => by
      obtain ⟨-, l, ⟨_, _, _, rfl⟩, hl⟩ := hen (max N 46) (le_max_left _ _)
      exact absurd hl (justice_tail (le_max_right _ _) _ ⟨fun h => h, fun h => h, fun h => h⟩
        fun ⟨_, _, _, h⟩ => by cases h),
    fun i v N hen => by
      obtain ⟨⟨w, hw⟩, -⟩ := hen N le_rfl
      exact (not_accepted N i w v hw).elim⟩

/-- **The MVBA's scheduling premise** on the untimed projection: (F-justice)
with its antecedent false, and (A-viewsync) with `W = 1` vacuously (nobody
enters a view or expires a timer). -/
theorem mvbaAdmissible : MvbaAdmissible run.toLRun := by
  refine ⟨proj, fun l hj _ N hen => ?_, ⟨1, 0, 0, rfl, rfl, ?_, fun i V _ _ ⟨n, hn⟩ => ?_,
    fun i n _ hexp => ?_⟩⟩
  · obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp ((Mvba.hop_isSome_iff l).mpr hj)
    have := hen N le_rfl
    rw [proj_at] at this
    exact absurd this (Mvba.not_enabled_of_quiet (mquiet _) hh)
  · dsimp +instances only [nsetC, byzNodeSetFin]
    decide
  · rw [proj_at] at hn; simp [mst] at hn
  · rw [proj_at] at hexp; simp [mst] at hexp

/-! ## The bridge -/

/-- A ghost certificate over a supermajority whose members' signatures never
appear, refuted by the quorum's having a member: nobody signs a negative vote
entry or casts a fallback vote in this run. -/
local macro "wnocert" h:ident : tactic =>
  `(tactic| (
    simp only [Chorus.vote_quorum_neg, Chorus.fbcert] at $h:ident
    obtain ⟨q, hq, hall⟩ := $h:ident
    dsimp +instances only [nsetC, byzNodeSetFin] at hq hall
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos (by omega : 0 < q.val.length)
    have := hall r (by simpa using hr)
    simp +unfoldPartialApp [Veil.FieldRepresentation.get, instIsSubStateOfRefl.getFrom_id, st] at this))

/-- **The only certifiable representation is `v⋆`**, at every index. A
non-proposer has no entry: a negative entry is a proposer's explicit
absence, and a positive one a proposer's. The proposer's entry cannot be
negative, since no negative FastQC and no `FBCert` ever exist, so it is its
one root; and that root is held by a FastQC, since a FallbackQC entry needs
the `FBCert` too. -/
theorem certified_eq (n : Nat) (v : V) (hc : Certified (thS := thS) (thM := thM) (st n) v) :
    v = vstar := by
  obtain ⟨hpos, hneg, hall⟩ := hc
  funext j
  simp only [thS, Cadence.chorusTheory, thM, MetaBlock.entries, decide_eq_true_eq] at hpos hneg hall
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
          · simp [vstar]
          · simp [hv] at hnf
        · wnocert h
    · rcases (hneg 0 hM).2 with h | ⟨-, h⟩
      · wnocert h
      · wnocert h
  · cases hv : v j with
    | none => simp [vstar, hj]
    | some p => exact absurd (hpos j p.1 (by simp [hv])).1 hj

/-- **`ValidBridge`**, with `valid := (· = v⋆)`, in both directions at every
index. Soundness: a certified vector is `v⋆` (`certified_eq`), hence valid.
Completeness: nobody decides or holds a meta-block in the MVBA, so it asks
nothing. -/
theorem validBridge : ValidBridge run.toLRun :=
  ⟨fun n v hc => by
      show decide (v = vstar) = true
      exact decide_eq_true (certified_eq n v hc),
    fun n i v _ hd => absurd hd (not_decided n i v),
    fun n i w v _ hacc => absurd hacc (not_accepted n i w v)⟩

/-- `Sync` at the system's MVBA, its two caller clauses derived
(`sync_of_syncAtMvba`): the handoff from the handoff row, (Δ-avail) from the
availability row and `Δ ≤ Δ_sync`. -/
theorem sync : Sync schC (Mvba.mvbaTemporal thM hqeC schC.mvba natViewOrderEnum rotation) run :=
  sync_of_syncAtMvba hqeC schC natViewOrderEnum rotation syncAtMvba validBridge

/-! ## The caller's premises -/

theorem allParticipate : AllParticipate run.toLRun := by
  intro i hi
  refine ⟨3, ?_⟩
  have := correct_lt hi
  show (st 3).participating i = true
  simp [st]
  omega

/-- **C1**: each correct validator abandons only after it has finalized
(`finalize_commit` at `36 + i`, `abandon` at `39 + i`). -/
theorem noAbandonBeforeFinalizing : NoAbandonBeforeFinalizing run.toLRun := by
  intro i _ n hab
  change (st n).abandoned i = true at hab
  show (st n).local_committed i = true
  simp [st] at hab ⊢
  omega

/-- Everyone participates by clock 0. -/
theorem allParticipateBy : AllParticipateBy 0 run := by
  intro i hi
  refine ⟨3, by decide, ?_⟩
  have := correct_lt hi
  show (st 3).participating i = true
  simp [st]
  omega

/-- Participation is synchronized within any tolerance: everyone has started
at clock 0. -/
theorem syncParticipationWithin (d : ℕ) : SyncParticipationWithin d run := by
  intro _ _ _ _ j hj
  refine ⟨3, Nat.zero_le _, ?_⟩
  have := correct_lt hj
  show (st 3).participating j = true
  simp [st]
  omega

/-- **C2**: nobody starts before `D − Δ = 0`. -/
theorem noEarlyStart : NoEarlyStart schC run := fun _ _ _ _ => Nat.le_add_left _ _

/-- Validator 0 has finalized by index 37 (clock 1): the antecedent of the
totality claim is met. -/
theorem finalizes : (run.at' 37).local_committed 0 = true := by
  show (st 37).local_committed 0 = true
  simp [st]

/-! ## The proven claims apply

Not needed for non-vacuity: these check that the run is an instance of what
`Chorus.termination`, `Chorus.totality` and `Chorus.timed_termination_atMvba`
quantify over, at their own instance regime, with nothing re-bundled. The
last one is the check that the witness's premise set is the proven timed
claim's: `syncAtMvba`, `validBridge` and the caller's four, at the system's
MVBA, and nothing else. -/

example : Terminates run.toLRun :=
  termination 4 1 rfl isByz hbyz natViewOrderEnum run.toLRun fJustice mvbaAdmissible validBridge
    allParticipate noAbandonBeforeFinalizing

example (j : Fin 4) (hj : ¬ nsetC.is_byz j = true) :
    ∃ m, run.clk m ≤ max (run.clk 37) run.gst + schC.dtot schC.Δ ∧
      (run.at' m).local_committed j = true :=
  totality schC schC.Δ run timedJustice (syncParticipationWithin _) noAbandonBeforeFinalizing
    37 0 (by decide) finalizes j hj

example (j : Fin 4) (hj : ¬ nsetC.is_byz j = true) :
    ∃ n, run.clk n ≤ max 0 run.gst + schC.ℓ (schC.mvba.ℓ natViewOrderEnum) ∧
      (run.at' n).local_committed j = true :=
  timed_termination_atMvba 4 1 rfl isByz hbyz schC natViewOrderEnum rotation run syncAtMvba validBridge
    (syncParticipationWithin _) noAbandonBeforeFinalizing noEarlyStart 0 allParticipateBy j hj

end Witness

/-! ## The three results -/

open Witness in
/-- **The premises of `Chorus.termination` are jointly satisfiable.** Some
instance and run meet all of them at once: the theorem's hypotheses (the
concrete family at some `n = 3f + 1` with at most `f` Byzantine validators,
the view order's enumeration), the assumptions of the system's configuration
`chorusTheory`, and the claim's five premises — (F-justice) with its
correct-sender owed-conditions and its two families, the MVBA's scheduling
`MvbaAdmissible` (whose handoff premise is derived), the bridge
`ValidBridge` in both directions, and the caller's two.

It rules out that the untimed termination claim is vacuous, and in
particular that its fairness or its bridge contradicts the rest. -/
theorem termination_premises_satisfiable :
    ∃ (n f : Nat) (hf : n = 3 * f + 1) (is_byz : Fin n → Prop) (_ : DecidablePred is_byz)
      (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
      (slot merkle_root view Phase PathChoice : Type) (_ : Inhabited slot) (_ : Inhabited merkle_root)
      (_ : Inhabited view) (_ : Inhabited Phase) (_ : Inhabited PathChoice)
      (vord : TotalOrderWithMinimum view) (_ : Chorus.Phase_EnumClass Phase)
      (_ : Chorus.PathChoice_EnumClass PathChoice) (_ : Inhabited (Fin n))
      (_ : Cadence.ViewOrderEnum view vord)
      (is_proposer : Fin n → Bool) (well_encoded : merkle_root → Bool)
      (mvba_init_state :
        Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view))
      (thM : Mvba.Theory (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view),
      (atMvba (nset := byzNodeSetFin n f hf is_byz hbyz) (slot := slot) (Phase := Phase)
        (PathChoice := PathChoice) thM).assumptions
        (Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
          is_proposer well_encoded mvba_init_state) ∧
      ∃ r : ChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz)
          (Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
            is_proposer well_encoded mvba_init_state) thM,
        FJustice (nset := byzNodeSetFin n f hf is_byz hbyz) r ∧
        MvbaAdmissible (nset := byzNodeSetFin n f hf is_byz hbyz) r ∧
        ValidBridge (nset := byzNodeSetFin n f hf is_byz hbyz) r ∧
        AllParticipate (nset := byzNodeSetFin n f hf is_byz hbyz) r ∧
        NoAbandonBeforeFinalizing (nset := byzNodeSetFin n f hf is_byz hbyz) r :=
  ⟨4, 1, rfl, isByz, inferInstance, hbyz, Unit, Unit, ℕ, Ph, PC, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, natViewOrder, inferInstance, inferInstance,
    inferInstance, natViewOrderEnum, _, _, mst 0, thM, holds, run.toLRun, fJustice, mvbaAdmissible,
    validBridge, allParticipate, noAbandonBeforeFinalizing⟩

open Witness in
/-- **The premises of the timed termination claim at the system's MVBA are
jointly satisfiable** (`TimedTerminationClaimAtMvba`, proven as
`timed_termination_atMvba`). Some instance, schedule and timed run meet all
of them at once: the instance hypotheses of `Mvba.mvbaTemporal` (finitely
many validators, a correct supermajority, the view order, a correct leader
in every `k` views, a cancellative Archimedean time), the assumptions of
`chorusTheory`, the schedule (with `δ ≤ Δ`, `δ ≤ ρ` and `Δ ≤ Δ_sync`), the
timing model `SyncAtMvba` — (Δδ-justice), (P-phase), the MVBA's own two
clauses on the timed projection — the bridge, and
the caller's conditions:
participation synchronized within `Δ`, C1, C2, and everyone participating
by `t`. The MVBA's clauses on its caller are derived, so they are not
premises.

It rules out that the bounded termination claim holds only because no run
can meet its premises: there is a run admissible under the timing model in
which the caller behaves. -/
theorem timedTermination_premises_satisfiable :
    ∃ (n f : Nat) (hf : n = 3 * f + 1) (is_byz : Fin n → Prop) (_ : DecidablePred is_byz)
      (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
      (slot merkle_root view Phase PathChoice : Type) (_ : Inhabited slot) (_ : Inhabited merkle_root)
      (_ : Inhabited view) (_ : Inhabited Phase) (_ : Inhabited PathChoice)
      (vord : TotalOrderWithMinimum view) (_ : Chorus.Phase_EnumClass Phase)
      (_ : Chorus.PathChoice_EnumClass PathChoice) (_ : Inhabited (Fin n))
      (vfin : Cadence.ViewOrderEnum view vord)
      (time : Type) (_ : LinearOrder time) (_ : AddCommMonoid time)
      (_ : IsOrderedCancelAddMonoid time) (_ : Archimedean time)
      (_ : ByzNodeSetHonestQuorum (Fin n) (ByzNSet n) (byzNodeSetFin n f hf is_byz hbyz))
      (is_proposer : Fin n → Bool) (well_encoded : merkle_root → Bool)
      (mvba_init_state :
        Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view))
      (thM : Mvba.Theory (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)
      (sch : Chorus.Schedule view time)
      (_ : Mvba.LeaderRotation (nset := byzNodeSetFin n f hf is_byz hbyz) vfin sch.mvba.k thM),
      (atMvba (nset := byzNodeSetFin n f hf is_byz hbyz) (slot := slot) (Phase := Phase)
        (PathChoice := PathChoice) thM).assumptions
        (Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
          is_proposer well_encoded mvba_init_state) ∧
      ∃ (r : TChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz)
          (Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
            is_proposer well_encoded mvba_init_state) thM time) (t : time),
        SyncAtMvba (nset := byzNodeSetFin n f hf is_byz hbyz) sch r ∧
        ValidBridge (nset := byzNodeSetFin n f hf is_byz hbyz) r.toLRun ∧
        SyncParticipationWithin (nset := byzNodeSetFin n f hf is_byz hbyz) sch.Δ r ∧
        NoAbandonBeforeFinalizing (nset := byzNodeSetFin n f hf is_byz hbyz) r.toLRun ∧
        NoEarlyStart (nset := byzNodeSetFin n f hf is_byz hbyz) sch r ∧
        AllParticipateBy (nset := byzNodeSetFin n f hf is_byz hbyz) t r :=
  ⟨4, 1, rfl, isByz, inferInstance, hbyz, Unit, Unit, ℕ, Ph, PC, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, natViewOrder, inferInstance, inferInstance,
    inferInstance, natViewOrderEnum, ℕ, inferInstance, inferInstance, inferInstance, inferInstance,
    hqeC, _, _, mst 0, thM, schC, rotation, holds, run, 0, syncAtMvba, validBridge,
    syncParticipationWithin _, noAbandonBeforeFinalizing, noEarlyStart, allParticipateBy⟩

open Witness in
/-- **The premises of `TotalityClaim` are jointly satisfiable**, at the
contract's tolerance `d = Δ`, together with the claim's antecedent. Some
instance, schedule and timed run meet (Δδ-justice), participation
synchronized within `Δ` and C1, and in it a correct validator finalizes: the
totality claim's conclusion is a real constraint on a run. -/
theorem totality_premises_satisfiable :
    ∃ (n f : Nat) (hf : n = 3 * f + 1) (is_byz : Fin n → Prop) (_ : DecidablePred is_byz)
      (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
      (slot merkle_root view Phase PathChoice : Type) (_ : Inhabited slot) (_ : Inhabited merkle_root)
      (_ : Inhabited view) (_ : Inhabited Phase) (_ : Inhabited PathChoice)
      (_ : TotalOrderWithMinimum view) (_ : Chorus.Phase_EnumClass Phase)
      (_ : Chorus.PathChoice_EnumClass PathChoice) (_ : Inhabited (Fin n))
      (time : Type) (_ : LinearOrder time) (_ : AddCommMonoid time)
      (is_proposer : Fin n → Bool) (well_encoded : merkle_root → Bool)
      (mvba_init_state :
        Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view))
      (thM : Mvba.Theory (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)
      (sch : Chorus.Schedule view time),
      (atMvba (nset := byzNodeSetFin n f hf is_byz hbyz) (slot := slot) (Phase := Phase)
        (PathChoice := PathChoice) thM).assumptions
        (Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
          is_proposer well_encoded mvba_init_state) ∧
      ∃ r : TChorusRun (nset := byzNodeSetFin n f hf is_byz hbyz)
          (Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
            is_proposer well_encoded mvba_init_state) thM time,
        TimedJustice (nset := byzNodeSetFin n f hf is_byz hbyz) sch r ∧
        SyncParticipationWithin (nset := byzNodeSetFin n f hf is_byz hbyz) sch.Δ r ∧
        NoAbandonBeforeFinalizing (nset := byzNodeSetFin n f hf is_byz hbyz) r.toLRun ∧
        ∃ k i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true ∧
          (r.at' k).local_committed i = true :=
  ⟨4, 1, rfl, isByz, inferInstance, hbyz, Unit, Unit, ℕ, Ph, PC, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, natViewOrder, inferInstance, inferInstance,
    inferInstance, ℕ, inferInstance, inferInstance, _, _, mst 0, thM, schC, holds, run, timedJustice,
    syncParticipationWithin _, noAbandonBeforeFinalizing, 37, 0, by decide, finalizes⟩

end Chorus

/-! ## The pinned trust base -/

/--
info: 'Chorus.termination_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.termination_premises_satisfiable

/--
info: 'Chorus.timedTermination_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.timedTermination_premises_satisfiable

/--
info: 'Chorus.totality_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.totality_premises_satisfiable

/--
info: 'Chorus.Witness.deadlineInclusive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.Witness.deadlineInclusive
