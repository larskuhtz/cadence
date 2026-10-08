import Cadence.Chorus.TimedTermination

/-! # Chorus.Temporal — the timed `SlotConsensusTemporal` instance, and the full `SlotConsensus`

[Bounds.md](../../docs/Bounds.md) §6.4.6, stage S5. The temporal level of
Module 1 (`mod:slotconsensus`), instantiated at the system's configuration
(`Cadence.chorusTheory`, `Cadence.mvbaTheory`, the quorum family
`n = 3f + 1`) over the fragment Chorus proves, `slotConsensusSafety`, and
joined with it into the full contract. [Mvba/Temporal.lean](../Mvba/Temporal.lean)
is the template.

Each class field and what proves it:

* **`Admissible`** is `Chorus.Admissible`: the run has a labelling that
  satisfies the claims' premises, each by its own name: `FJustice`,
  `MvbaAdmissible` and `ValidBridge` ([Liveness.lean](Liveness.lean)) for the
  untimed field, `SyncAtMvba` ([Schedule.lean](Schedule.lean)) at the run's
  slot's schedule for the timed ones;
* **`admissible_exists`** is the idle run (`admissible_exists`): nobody
  participates, so every proposer stays silent, the phase markers fire at
  their landmarks, and the caller abandons one validator at every other
  step, which steps the MVBA;
* **`termination`** is `Chorus.termination`, read through the labelling;
* **`quiescence`** is `sent_new`, in Lemma 6 (`lemma:chorus-quiescence`)'s two
  parts: Chorus's own sends are gated on active participation
  (`own_sent_new`, [Compose.lean](Compose.lean)), and the MVBA's are confined
  by its own `quiescence` to the window between a gated `mvba_propose` and a
  forwarded `abandon` (`mvba_sent_new`, through the two invariants
  `participating_of_mvba_proposed` and `mvba_abandoned_of_abandoned`);
* **`sent`** is `Chorus.Sent` ([Compose.lean](Compose.lean)), monotone
  along every step (`sent_mono`). The three inputs, their records and
  their frames are fields of the fragment, proven with it
  (`Chorus.slotConsensusSafety`, [Compose.lean](Compose.lean));
* **`SlotConsensusWithTotality`**: `bounded_termination` is
  `Chorus.timed_termination_atMvba` at `ℓ = 5Δ + ℓ_MVBA + 9δ`, and `totality`
  is `Chorus.totality` at `d_tot = Δ + 2δ`; at `δ = 0` these are the paper's
  `5Δ + ℓ_MVBA` and `Δ` (`chorusWithTotality_ℓ_paper`,
  `chorusWithTotality_d_tot_paper`).

`slotConsensusFull` joins the fragment and the temporal level through
[Compose.lean](Compose.lean)'s `slotConsensus_of_temporal`, and
`slotConsensusFull_toSafety` checks by `rfl` that the join hands back
exactly `slotConsensusSafety`.

## What the instance is proven from

Nothing is assumed of the protocol, and every hypothesis is about the
configuration or the time theory:

* **the slot's proposer set is non-empty** (`hprop`). A proposer need not
  propose: the idle run is the case in which every proposer stays silent.
  The hypothesis is what makes that run admissible: with no proposer at all,
  the empty meta-block is certified at every state and the bridge would make
  admissibility depend on the MVBA's validity predicate accepting it;
* the view order's enumeration (`vfin`) and (A-leader-rotation-k) (`hrot`),
  the MVBA's own instance hypotheses;
* the time theory: a linearly ordered, cancellative, Archimedean additive
  monoid, as for the MVBA's instance.

A supermajority of correct validators, the MVBA's third instance
hypothesis, holds of the family (`hqeFin`). -/

namespace Chorus

open Cadence
open scoped Cadence.Timed

/-! ## The idle run

The run `admissible_exists` exhibits from every initial state. -/

section Idle

open Classical

local macro "chorus_tr" h:ident : tactic =>
  `(tactic| (simp only [Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

local macro "chorus_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id] at *)

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}

/-- **An idle state**: nobody participates, so no gated rule can fire; no
proposer has signed a root, no chunk has been sent, and nobody has signed
a vote or a fallback vote; the MVBA is quiet, nobody has decided in it, and
it holds no commit certificate. Every rule of the hop table reads one of
these records. -/
structure Idle (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) : Prop where
  part : ∀ i, s.participating i = false
  signed : ∀ j m, s.msg_proposer_signed j m = false
  chunk : ∀ k i j m, s.msg_chunk k i j m = false
  vpos : ∀ r j m, s.msg_vote_pos_sig r j m = false
  vneg : ∀ r j, s.msg_vote_neg_sig r j = false
  fallback : ∀ r, s.msg_fallback_sig r = false
  quiet : Mvba.Quiet s.mvba_st
  decided : ∀ i v, s.mvba_st.decided i v = false
  commitqc : ∀ c v e, s.mvba_st.msg_commitqc c v e = false
  decidedqc : ∀ i v e, s.mvba_st.decided_qc i v e = false
  timer : ∀ i v, s.mvba_st.timer_expired i v = false

omit [Inhabited node] [Inhabited nodeset] cnt in
/-- A supermajority has a member. -/
theorem supermajority_member {q : nodeset} (h : nset.supermajority q) : ∃ r, nset.member r q = true :=
  let ⟨a, ha, _, _⟩ := nset.supermajorities_intersect_in_honest q q h h
  ⟨a, ha⟩

omit [Inhabited slot] [Inhabited merkle_root] [Inhabited Phase] [Inhabited PathChoice] cnt Phase_Enum PathChoice_Enum in
/-- Nobody has decided in the MVBA at an idle state. -/
theorem Idle.not_decided {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hI : Idle s) (i : node) (v : MetaBlock node merkle_root) :
    ¬ (Mvba.mvbaSafety thM).decided s.mvba_st i v := by
  show ¬ (s.mvba_st.decided i v = true)
  simp [hI.decided i v]

omit [Inhabited slot] [Inhabited merkle_root] [Inhabited Phase] [Inhabited PathChoice] cnt Phase_Enum PathChoice_Enum in
/-- Nobody holds a valid MVBA commit certificate at an idle state. -/
theorem Idle.not_certified {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hI : Idle s) (c : Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
    (e : node → Option merkle_root) :
    ¬ (Mvba.mvbaSafety thM).certifies s.mvba_st c e := by
  show ¬ Mvba.Certifies s.mvba_st c e
  cases c <;> simp [Mvba.Certifies, Veil.FieldRepresentation.get, hI.commitqc]

omit [Inhabited slot] [Inhabited merkle_root] [Inhabited Phase] [Inhabited PathChoice] cnt Phase_Enum PathChoice_Enum in
/-- No decision has output a certificate at an idle state. -/
theorem Idle.not_decidedCert {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hI : Idle s) (i : node) (c : Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) :
    ¬ (Mvba.mvbaSafety thM).decidedCert s.mvba_st i c := by
  show ¬ Mvba.DecidedCert s.mvba_st i c
  cases c <;> simp [Mvba.DecidedCert, Veil.FieldRepresentation.get, hI.decidedqc]

/-- The availability report, owed for a meta-block its validator holds. -/
def IsAvail (l : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice) : Prop :=
  ∃ i v n, l = .mvba_avail_ready i v n

set_option maxHeartbeats 4000000 in
/-- **At an idle state no row of the hop table is enabled**, the
availability report aside. -/
theorem not_enabled_of_idle {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hI : Idle s) {l : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice}
    {hd : Mvba.Hop} (hh : hop l = some hd) (ha : ¬ IsAvail l) :
    ¬ Enabled (atMvba thM) thS s l := by
  rintro ⟨s', htr⟩
  cases l
  all_goals first | (simp [hop] at hh; done) | skip
  all_goals first | exact absurd ⟨_, _, _, rfl⟩ ha | skip
  case accept_mvba_commitqc i r c mn =>
    obtain ⟨w, e, x, s₀, -, -, h⟩ := accept_mvba_commitqc_tr htr
    exact Mvba.not_enabled_decide_of_quiet (th := thM) hI.quiet ⟨_, h⟩
  case send_mvba_cert =>
    chorus_tr htr
    obtain ⟨-, -, -, hdc, -⟩ := htr
    exact hI.not_decidedCert _ _ hdc
  case on_mvba_decide_pos =>
    chorus_tr htr
    obtain ⟨-, -, hdec, -⟩ := htr
    exact hI.not_decided _ _ hdec
  case on_mvba_decide_neg =>
    chorus_tr htr
    obtain ⟨-, -, hdec, -⟩ := htr
    exact hI.not_decided _ _ hdec
  case mvba_terminate =>
    chorus_tr htr
    obtain ⟨-, -, hdec, -⟩ := htr
    exact hI.not_decided _ _ hdec
  case aggregate_fastqc_pos =>
    chorus_tr htr
    obtain ⟨-, hq, hall, -⟩ := htr
    obtain ⟨r, hr⟩ := supermajority_member hq
    have := hall r hr
    chorus_field_simp
    simp_all [Idle.vpos hI]
  case aggregate_fastqc_neg =>
    chorus_tr htr
    obtain ⟨-, hq, hall, -⟩ := htr
    obtain ⟨r, hr⟩ := supermajority_member hq
    have := hall r hr
    chorus_field_simp
    simp_all [Idle.vneg hI]
  all_goals chorus_tr htr
  all_goals (repeat (obtain ⟨_, htr⟩ := htr))
  all_goals chorus_field_simp
  all_goals simp_all [Idle.part hI, Idle.signed hI, Idle.vpos hI, Idle.vneg hI,
    Chorus.chunk_received]

local macro "mvba_inst" : tactic =>
  `(tactic| letI : MVBASafety node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset nset (fun i => nset.is_byz i = true) := Mvba.mvbaSafety thM)

/-- Every initial state is idle. -/
theorem idle_init {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (ha : (atMvba thM).assumptions thS) (hi : (atMvba thM).init thS s) : Idle s := by
  mvba_inst
  have hm := ((mvbaComponent thS thM).init s ha hi).2
  have hst : s.mvba_st = _ := mvba_st_init hi
  exact ⟨Chorus.participating.init hi, Chorus.msg_proposer_signed.init hi,
    Chorus.msg_chunk.init hi, Chorus.msg_vote_pos_sig.init hi,
    Chorus.msg_vote_neg_sig.init hi, Chorus.msg_fallback_sig.init hi,
    Mvba.quiet_init hm, Mvba.decided.init hm, Mvba.msg_commitqc.init hm,
    Mvba.decided_qc.init hm, Mvba.timer_expired.init hm⟩

omit [Inhabited merkle_root] cnt in
/-- An MVBA `abandon()` keeps the MVBA quiet, undecided and certificate-free. -/
theorem idle_mvba_abandon {ms ms' : Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)}
    {i : node}
    (htr : (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      ms (.abandon i) ms')
    (hq : Mvba.Quiet ms) (hd : ∀ i v, ms.decided i v = false)
    (hc : ∀ c v e, ms.msg_commitqc c v e = false) (hdq : ∀ i v e, ms.decided_qc i v e = false)
    (ht : ∀ i v, ms.timer_expired i v = false) :
    Mvba.Quiet ms' ∧ (∀ i v, ms'.decided i v = false) ∧ (∀ c v e, ms'.msg_commitqc c v e = false) ∧
      (∀ i v e, ms'.decided_qc i v e = false) ∧ (∀ i v, ms'.timer_expired i v = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Mvba.Quiet, Mvba.abandon.frame_input htr, Mvba.abandon.frame_entered htr,
      Mvba.abandon.frame_accepted htr, Mvba.abandon.frame_msg_prepare htr,
      Mvba.abandon.frame_msg_commit htr, Mvba.abandon.frame_msg_timeout_qc htr,
      Mvba.abandon.frame_msg_timeout_noqc htr]
    exact hq
  · rw [Mvba.abandon.frame_decided htr]; exact hd
  · rw [Mvba.abandon.frame_msg_commitqc htr]; exact hc
  · rw [Mvba.abandon.frame_decided_qc htr]; exact hdq
  · rw [Mvba.abandon.frame_timer_expired htr]; exact ht

/-- `abandon` keeps a state idle. -/
theorem idle_abandon {s s' : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    {i : node} {mn}
    (htr : (atMvba thM).tr thS s (.abandon i mn) s') (hI : Idle s) : Idle s' := by
  mvba_inst
  obtain ⟨hq, hd, hc, hdq, ht⟩ :=
    idle_mvba_abandon (abandon_tr htr) hI.quiet hI.decided hI.commitqc hI.decidedqc hI.timer
  exact ⟨by rw [Chorus.abandon.frame_participating htr]; exact hI.part,
    by rw [Chorus.abandon.frame_msg_proposer_signed htr]; exact hI.signed,
    by rw [Chorus.abandon.frame_msg_chunk htr]; exact hI.chunk,
    by rw [Chorus.abandon.frame_msg_vote_pos_sig htr]; exact hI.vpos,
    by rw [Chorus.abandon.frame_msg_vote_neg_sig htr]; exact hI.vneg,
    by rw [Chorus.abandon.frame_msg_fallback_sig htr]; exact hI.fallback, hq, hd, hc, hdq, ht⟩

set_option hygiene false in
/-- Every label but `abandon` and the three MVBA steps leaves the MVBA's
state and these Chorus records alone, when it frames them. -/
local macro "idle_frame" act:ident : tactic => do
  let f (s : String) := Lean.mkIdent (`Chorus ++ act.getId ++ Lean.Name.mkSimple ("frame_" ++ s))
  `(tactic| exact ⟨by rw [$(f "participating") htr]; exact hI.part,
      by rw [$(f "msg_proposer_signed") htr]; exact hI.signed,
      by rw [$(f "msg_chunk") htr]; exact hI.chunk,
      by rw [$(f "msg_vote_pos_sig") htr]; exact hI.vpos,
      by rw [$(f "msg_vote_neg_sig") htr]; exact hI.vneg,
      by rw [$(f "msg_fallback_sig") htr]; exact hI.fallback,
      by rw [$(f "mvba_st") htr]; exact hI.quiet,
      by rw [$(f "mvba_st") htr]; exact hI.decided,
      by rw [$(f "mvba_st") htr]; exact hI.commitqc,
      by rw [$(f "mvba_st") htr]; exact hI.decidedqc,
      by rw [$(f "mvba_st") htr]; exact hI.timer⟩)

/-- A phase marker keeps a state idle. -/
theorem idle_marker {s s' : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (L : Landmark) (htr : (atMvba thM).tr thS s L.marker s') (hI : Idle s) : Idle s' := by
  mvba_inst
  cases L <;> simp only [Landmark.marker] at htr
  · idle_frame advance_to_deadline
  · idle_frame advance_to_fb_arm
  · idle_frame advance_to_mvba_arm

/-! ### The idle run's steps -/

omit [Inhabited merkle_root] cnt in
/-- The MVBA's `abandon()` has no guard. -/
theorem mvba_abandon_exists
    (ms : Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
    (i : node) :
    ∃ ms', (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      ms (.abandon i) ms' := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
  exact ⟨_, rfl⟩

/-- The MVBA's state after `default`'s `abandon()`. -/
noncomputable def mvbaAb (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)
    (ms : Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)) :
    Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view) :=
  Classical.choose (mvba_abandon_exists (thM := thM) ms default)

set_option maxHeartbeats 1000000 in
/-- `abandon` is enabled whenever the MVBA's `abandon()` is. -/
theorem abandon_exists {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice} {i : node} {mn}
    (h : (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      s.mvba_st (.abandon i) mn) :
    ∃ s', (atMvba thM).tr thS s (.abandon i mn) s' := by
  simp only [atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp]
  exact ⟨_, h, rfl⟩

set_option maxHeartbeats 1000000 in
/-- Each marker is enabled at the phase before its landmark. -/
theorem marker_exists {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice} (L : Landmark)
    (h : s.phase = (match L with
      | .deadline => Phase_EnumClass.pre_deadline
      | .fbArm => Phase_EnumClass.post_deadline
      | .mvbaArm => Phase_EnumClass.post_fb_arm)) :
    ∃ s', (atMvba thM).tr thS s L.marker s' := by
  cases L <;> simp only [Landmark.marker, atMvba, Chorus.relationalTransitionSystem, Chorus.Next,
    Chorus.NextAct, trSimp] <;> exact ⟨_, h, rfl⟩

set_option maxHeartbeats 1000000 in
/-- Each marker sets the phase to its landmark's. -/
theorem marker_phase {s s' : StateAtMvba slot node nodeset merkle_root view Phase PathChoice} (L : Landmark)
    (htr : (atMvba thM).tr thS s L.marker s') :
    s'.phase = (match L with
      | .deadline => Phase_EnumClass.post_deadline
      | .fbArm => Phase_EnumClass.post_fb_arm
      | .mvbaArm => Phase_EnumClass.post_mvba_arm) := by
  cases L <;> simp only [Landmark.marker] at htr <;> chorus_tr htr <;> obtain ⟨-, rfl⟩ := htr <;>
    chorus_field_simp

/-- The idle run's label at index `n` from state `s`: the three phase markers
at 0, 2 and 4, and `default`'s `abandon()` everywhere else. -/
noncomputable def idleLabel
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)
    (n : Nat) (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) :
    LabelAtMvba slot node nodeset merkle_root view Phase PathChoice :=
  if n = 0 then .advance_to_deadline else if n = 2 then .advance_to_fb_arm
  else if n = 4 then .advance_to_mvba_arm else .abandon default (mvbaAb thM s.mvba_st)

/-- The idle run's successor state. -/
noncomputable def idleNext
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)
    (n : Nat) (s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) :
    StateAtMvba slot node nodeset merkle_root view Phase PathChoice :=
  if h : ∃ s', (atMvba thM).tr thS s (idleLabel thM n s) s' then h.choose else s

/-- The idle run's states from `st`. -/
noncomputable def idleSt
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)
    (st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) :
    Nat → StateAtMvba slot node nodeset merkle_root view Phase PathChoice
  | 0 => st
  | n + 1 => idleNext thS thM n (idleSt thS thM st n)

/-- The phase at index `n` of the idle run. -/
def phaseAt (n : Nat) : Phase :=
  if n = 0 then Phase_EnumClass.pre_deadline else if n ≤ 2 then Phase_EnumClass.post_deadline
  else if n ≤ 4 then Phase_EnumClass.post_fb_arm else Phase_EnumClass.post_mvba_arm

/-- At the phase `phaseAt n`, the idle run's label at `n` is enabled. -/
theorem idle_exists {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice} {n : Nat}
    (hph : s.phase = phaseAt (Phase := Phase) n) :
    ∃ s', (atMvba thM).tr thS s (idleLabel thM n s) s' := by
  unfold idleLabel
  split_ifs with h0 h2 h4
  · exact marker_exists .deadline (by simp [hph, phaseAt, h0])
  · exact marker_exists .fbArm (by simp [hph, phaseAt, h2])
  · exact marker_exists .mvbaArm (by simp [hph, phaseAt, h4])
  · exact abandon_exists (Classical.choose_spec (mvba_abandon_exists (thM := thM) s.mvba_st default))

/-- The successor is a step, when there is one. -/
theorem idleNext_tr {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice} {n : Nat}
    (h : ∃ s', (atMvba thM).tr thS s (idleLabel thM n s) s') :
    (atMvba thM).tr thS s (idleLabel thM n s) (idleNext thS thM n s) := by
  unfold idleNext
  rw [dif_pos h]
  exact h.choose_spec

/-- The idle run's step at `n` moves the phase from `phaseAt n` to
`phaseAt (n + 1)`. -/
theorem idle_phase_next {s s' : StateAtMvba slot node nodeset merkle_root view Phase PathChoice} {n : Nat}
    (htr : (atMvba thM).tr thS s (idleLabel thM n s) s') (hph : s.phase = phaseAt (Phase := Phase) n) :
    s'.phase = phaseAt (Phase := Phase) (n + 1) := by
  unfold idleLabel at htr
  split_ifs at htr with h0 h2 h4
  · rw [marker_phase .deadline htr]; simp [phaseAt, h0]
  · rw [marker_phase .fbArm htr]; simp [phaseAt, h2]
  · rw [marker_phase .mvbaArm htr]; simp [phaseAt, h4]
  · rw [Chorus.abandon.frame_phase (mvba := Mvba.mvbaSafety thM) htr, hph]
    simp only [phaseAt]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **The idle run is a run**: from an initial state, each index is at
`phaseAt n` and steps by its label. -/
theorem idleSt_step {st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hi : (atMvba thM).init thS st) (n : Nat) :
    (idleSt thS thM st n).phase = phaseAt n ∧
      (atMvba thM).tr thS (idleSt thS thM st n) (idleLabel thM n (idleSt thS thM st n))
        (idleSt thS thM st (n + 1)) := by
  induction n with
  | zero =>
    have hph : (idleSt thS thM st 0).phase = phaseAt (Phase := Phase) 0 := by
      simp [idleSt, phaseAt, Chorus.phase.init (mvba := Mvba.mvbaSafety thM) hi]
    exact ⟨hph, idleNext_tr (idle_exists hph)⟩
  | succ n ih =>
    have hph := idle_phase_next ih.2 ih.1
    exact ⟨hph, idleNext_tr (idle_exists hph)⟩

/-- Every state of the idle run is idle. -/
theorem idleSt_idle {st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (ha : (atMvba thM).assumptions thS) (hi : (atMvba thM).init thS st) (n : Nat) :
    Idle (idleSt thS thM st n) := by
  induction n with
  | zero => exact idle_init ha hi
  | succ n ih =>
    have htr := (idleSt_step hi n).2
    unfold idleLabel at htr
    split_ifs at htr
    · exact idle_marker .deadline htr ih
    · exact idle_marker .fbArm htr ih
    · exact idle_marker .mvbaArm htr ih
    · exact idle_abandon htr ih

omit [Inhabited slot] [Inhabited merkle_root] [Inhabited Phase] [Inhabited PathChoice] cnt Phase_Enum PathChoice_Enum in
/-- The idle run's label at `n` is a marker only at 0, 2 and 4, each its
landmark's. -/
theorem idleLabel_marker {n : Nat} {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    {L : Landmark} (h : idleLabel thM n s = L.marker) :
    n = (match L with | .deadline => 0 | .fbArm => 2 | .mvbaArm => 4) := by
  unfold idleLabel at h
  cases L <;> split_ifs at h <;> simp_all [Landmark.marker]

/-- Past index 4 the phase is past the last landmark, so no marker is
enabled. -/
theorem marker_not_enabled {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hph : s.phase = Phase_EnumClass.post_mvba_arm) (L : Landmark) :
    ¬ Enabled (atMvba thM) thS s L.marker := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := phase_distinct (Phase := Phase)
  rintro ⟨s', htr⟩
  cases L <;> simp only [Landmark.marker] at htr <;> chorus_tr htr <;> obtain ⟨hg, -⟩ := htr <;>
    chorus_field_simp <;> simp_all

end Idle

/-! ### The idle run, timed -/

section IdleRun

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time] [Archimedean time]

/-- The idle run's clock: the deadline `D` at the first two indices, then
`D + Δ`, then `D + 2Δ` (each landmark read at its marker and the index after
it), then on by `Δ` per step, but never below `(n − 5)Δ`, which makes it
unbounded however far below `0` the deadline is. -/
def idleClk (D Δ : time) (n : Nat) : time :=
  if n ≤ 5 then D + (n / 2) • Δ else max (D + 2 • Δ) ((n - 5) • Δ)

omit [Archimedean time] in
theorem idleClk_mono {D Δ : time} (hΔ : 0 < Δ) (n : Nat) : idleClk D Δ n ≤ idleClk D Δ (n + 1) := by
  unfold idleClk
  by_cases h5 : n + 1 ≤ 5
  · rw [if_pos (by omega), if_pos h5]
    exact add_le_add_right (nsmul_le_nsmul_left hΔ.le (Nat.div_le_div_right (Nat.le_succ n))) _
  by_cases h5' : n ≤ 5
  · rw [if_pos h5', if_neg h5]
    have : n / 2 = 2 := by omega
    rw [this]
    exact le_max_left _ _
  · rw [if_neg h5', if_neg h5]
    exact max_le_max le_rfl (nsmul_le_nsmul_left hΔ.le (by omega))

theorem idleClk_unbounded {D Δ : time} (hΔ : 0 < Δ) (t : time) : ∃ n, t ≤ idleClk D Δ n := by
  obtain ⟨k, hk⟩ := Archimedean.arch t hΔ
  refine ⟨k + 6, ?_⟩
  unfold idleClk
  rw [if_neg (by omega)]
  exact le_trans hk (le_trans (nsmul_le_nsmul_left hΔ.le (by omega)) (le_max_right _ _))

/-- **The idle run** from an initial state: the phase markers at the
slot's three landmarks, `default`'s `abandon()` at every other step, and
nothing else. Nobody participates and so nobody proposes: the slot's
proposers all stay silent. GST is the deadline. -/
noncomputable def idleRun (ha : (atMvba thM).assumptions thS)
    {st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hi : (atMvba thM).init thS st) (D Δ : time) (hΔ : 0 < Δ) : TChorusRun thS thM time where
  at' := idleSt thS thM st
  lbl n := idleLabel thM n (idleSt thS thM st n)
  holds := ha
  starts := hi
  steps n := (idleSt_step hi n).2
  clk := idleClk D Δ
  clk_mono := idleClk_mono hΔ
  clk_unbounded := idleClk_unbounded hΔ
  gst := D

variable (ha : (atMvba thM).assumptions thS)
  {st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
  (hi : (atMvba thM).init thS st) {D Δ : time} (hΔ : 0 < Δ)

include ha hi in
theorem idleRun_idle (n : Nat) : Idle ((idleRun ha hi D Δ hΔ).at' n) := idleSt_idle ha hi n

include hi in
theorem idleRun_phase (n : Nat) : ((idleRun ha hi D Δ hΔ).at' n).phase = phaseAt n :=
  (idleSt_step hi n).1

include ha hi in
/-- From index 5 on no fair label is enabled, the availability report aside:
the markers because the phase is past the last landmark, every other fair
label because the state is idle. -/
theorem idleRun_tail {n : Nat} (hn : 5 ≤ n)
    {l : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hj : JusticeLabel l) (hav : ¬ IsAvail l) :
    ¬ Enabled (atMvba thM) thS ((idleRun ha hi D Δ hΔ).at' n) l := by
  by_cases hm : MarkerLabel l
  · obtain ⟨L, rfl⟩ := (markerLabel_iff l).mp hm
    refine marker_not_enabled ?_ L
    rw [idleRun_phase]
    simp only [phaseAt]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp ((hop_isSome_iff l).mpr ⟨hj, hm⟩)
    exact not_enabled_of_idle (idleRun_idle ha hi hΔ n) hh hav

include ha hi in
/-- **(F-justice)** on the idle run, every clause with its antecedent
false. -/
theorem idleRun_fJustice : FJustice (idleRun ha hi D Δ hΔ).toLRun := by
  refine ⟨fun l hj hfam N hen => ?_, fun i v N hen => ?_, fun i N hen => ?_, fun i v N hen => ?_⟩
  · exact absurd (hen (max N 5) (le_max_left _ _)).2
      (idleRun_tail ha hi hΔ (le_max_right _ _) hj fun ⟨_, _, _, h⟩ => hfam (h ▸ trivial))
  · obtain ⟨-, l, ⟨_, rfl⟩, hl⟩ := hen N le_rfl
    exact (not_enabled_of_idle (idleRun_idle ha hi hΔ N) (hd := .net) rfl
      (fun ⟨_, _, _, h⟩ => by cases h) hl).elim
  · obtain ⟨-, l, ⟨_, _, _, rfl⟩, hl⟩ := hen N le_rfl
    exact (not_enabled_of_idle (idleRun_idle ha hi hΔ N) (hd := .net) rfl
      (fun ⟨_, _, _, h⟩ => by cases h) hl).elim
  · obtain ⟨⟨w, hw⟩, -⟩ := hen N le_rfl
    have := (idleRun_idle ha hi (D := D) hΔ N).quiet.2.2.1 i w v
    simp_all

include hi in
/-- The idle run's MVBA steps are `default`'s `abandon()`, at every index
but the three markers'. -/
theorem idleRun_mvba_step (n : Nat) (h : MvbaStepLabel ((idleRun ha hi D Δ hΔ).lbl n)) :
    (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      ((idleRun ha hi D Δ hΔ).at' n).mvba_st (.abandon default)
      ((idleRun ha hi D Δ hΔ).at' (n + 1)).mvba_st := by
  have htr := (idleRun ha hi D Δ hΔ).steps n
  change (atMvba thM).tr thS _ (idleLabel thM n _) _ at htr
  change MvbaStepLabel (idleLabel thM n _) at h
  unfold idleLabel at htr h
  split_ifs at htr h
  · exact absurd h id
  · exact absurd h id
  · exact absurd h id
  · exact abandon_tr htr

include hi in
theorem idleRun_mvba_scheduled (N : Nat) :
    ∃ n, N ≤ n ∧ MvbaStepLabel ((idleRun ha hi D Δ hΔ).lbl n) := by
  refine ⟨max N 5, le_max_left _ _, ?_⟩
  change MvbaStepLabel (idleLabel thM _ _)
  unfold idleLabel
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  trivial

/-- **The idle run's MVBA projection**, labelled by the MVBA's own
`abandon()` at `default`. -/
noncomputable def idleProj : (mvbaComponent thS thM).Projection (idleRun ha hi D Δ hΔ).toLRun where
  lbl _ := .abandon default
  realizes n h := idleRun_mvba_step ha hi hΔ n h
  scheduled := idleRun_mvba_scheduled ha hi hΔ

include ha hi in
/-- Every state of the projection is idle's MVBA state. -/
theorem idleProj_quiet (k : Nat) :
    ∃ n, (idleProj ha hi hΔ (D := D)).run.at' k = ((idleRun ha hi D Δ hΔ).at' n).mvba_st :=
  ⟨_, rfl⟩

include ha hi in
/-- **The MVBA's scheduling premise** on the idle run: (F-justice) with its
antecedent false, as nothing fair is enabled at a quiet MVBA state; and
(A-viewsync) at any view with a correct leader and a predecessor, vacuously,
since nobody enters a view or expires a timer. -/
theorem idleRun_mvbaAdmissible
    (hgood : ∃ (W PV : view) (L : node), vord.next PV W ∧ thM.leader W L = true ∧ ¬ nset.is_byz L = true) :
    MvbaAdmissible (idleRun ha hi D Δ hΔ).toLRun := by
  obtain ⟨W, PV, L, hn, hl, hL⟩ := hgood
  refine ⟨idleProj ha hi hΔ, fun l hj _ N hen => ?_, ⟨W, PV, L, hn, hl, hL, fun i V _ _ ⟨n, hen'⟩ => ?_,
    fun i n _ hexp => ?_⟩⟩
  · obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp ((Mvba.hop_isSome_iff l).mpr hj)
    obtain ⟨m, hm⟩ := idleProj_quiet ha hi hΔ (D := D) N
    have := hen N le_rfl
    rw [hm] at this
    exact absurd this (Mvba.not_enabled_of_quiet (idleRun_idle ha hi hΔ m).quiet hh)
  · obtain ⟨m, hm⟩ := idleProj_quiet ha hi hΔ (D := D) n
    rw [hm, (idleRun_idle ha hi hΔ m).quiet.2.1] at hen'
    cases hen'
  · obtain ⟨m, hm⟩ := idleProj_quiet ha hi hΔ (D := D) n
    rw [hm, (idleRun_idle ha hi hΔ m).timer] at hexp
    cases hexp

end IdleRun

section Bridge

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}

/-- A ghost certificate over a supermajority none of whose members has
signed, refuted by the quorum's having a member. -/
local macro "nocert" h:ident hI:ident : tactic =>
  `(tactic| (
    simp only [Chorus.vote_quorum_pos, Chorus.vote_quorum_neg, Chorus.fbcert] at $h:ident
    obtain ⟨q, hq, hall⟩ := $h:ident
    obtain ⟨r, hr⟩ := supermajority_member hq
    have := hall r hr
    simp +unfoldPartialApp [Veil.FieldRepresentation.get, instIsSubStateOfRefl.getFrom_id,
      ($hI).vpos, ($hI).vneg, ($hI).fallback] at this))

/-- **Nothing is certified at an idle state of a slot with a proposer.** The
proposer must have an entry, a positive one needs a FastQC or the `FBCert`,
a negative one a negative FastQC or the `FBCert`, and none of those
certificates has a signature behind it. -/
theorem not_certified_of_idle {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hI : Idle s) {J₀ : node} (hJ₀ : thS.is_proposer J₀ = true) (v : MetaBlock node merkle_root) :
    ¬ Certified (thS := thS) (thM := thM) s v := by
  rintro ⟨hpos, hneg, hall⟩
  rcases hall J₀ hJ₀ with ⟨M, hM⟩ | hM
  · rcases (hpos J₀ M hM).2 with ⟨-, h⟩ | ⟨-, -, h⟩
    · nocert h hI
    · nocert h hI
  · rcases (hneg J₀ hM).2 with h | ⟨-, h⟩
    · nocert h hI
    · nocert h hI

end Bridge

section IdleTimed

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time] [Archimedean time]
  (ha : (atMvba thM).assumptions thS)
  {st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
  (hi : (atMvba thM).init thS st) (sch : Schedule view time)

/-- The idle run at a schedule: its landmarks are the schedule's. -/
noncomputable abbrev idleRunAt : TChorusRun thS thM time :=
  idleRun ha hi sch.D sch.Δ sch.mvba.Δ_pos

include ha hi in
/-- **A buffered family over the hop table holds with its antecedent
false**: at the window's gate index `N'`, which lies in the window, the gate
is open, so a member would be enabled, and none is. -/
theorem idleRun_bff {D δ : time} (hδ : 0 ≤ δ) {C gate : StateAtMvba slot node nodeset merkle_root view Phase PathChoice → Prop}
    {S : LabelAtMvba slot node nodeset merkle_root view Phase PathChoice → Prop}
    (hS : ∀ l, S l → (∃ h, hop l = some h) ∧ ¬ IsAvail l) :
    BufferedFairFamily (idleRunAt ha hi sch) D δ C gate S := by
  intro N N' _ h1 h2
  have hW : (idleRunAt ha hi sch).clk N' ≤ (idleRunAt ha hi sch).bufWindow N N' D δ :=
    le_trans ((idleRunAt ha hi sch).clk_le_ref N')
      (le_trans (le_add_of_nonneg_right hδ) (le_max_right _ _))
  obtain ⟨-, hen⟩ := h1 N' ‹_› hW
  obtain ⟨l, hl, hen⟩ := hen (h2 N' le_rfl hW)
  obtain ⟨⟨h, hh⟩, hav⟩ := hS l hl
  exact absurd hen (not_enabled_of_idle (idleRun_idle ha hi (D := sch.D) sch.mvba.Δ_pos N') hh hav)

include ha hi in
/-- **(Δδ-justice)** on the idle run. -/
theorem idleRun_timedJustice : TimedJustice sch (idleRunAt ha hi sch) := by
  have hδ := sch.mvba.δ_nonneg
  refine ⟨fun l h hh hown => ?_, fun i v => ?_, fun i v => ?_, fun i => ?_, fun i v => ?_, fun i v => ?_⟩
  · refine bufferedFair_iff_family.mpr (idleRun_bff ha hi sch hδ fun l' hl' => ?_)
    subst hl'
    exact ⟨⟨h, hh⟩, fun ⟨_, _, _, he⟩ => hown (he ▸ trivial)⟩
  · exact idleRun_bff ha hi sch hδ fun l ⟨_, hl⟩ => ⟨⟨.net, hl ▸ rfl⟩, fun ⟨_, _, _, he⟩ => by
      rw [hl] at he; cases he⟩
  · exact idleRun_bff ha hi sch hδ fun l ⟨_, hl⟩ => ⟨⟨.net, hl ▸ rfl⟩, fun ⟨_, _, _, he⟩ => by
      rw [hl] at he; cases he⟩
  · exact idleRun_bff ha hi sch hδ fun l ⟨_, _, _, hl⟩ => ⟨⟨.net, hl ▸ rfl⟩, fun ⟨_, _, _, he⟩ => by
      rw [hl] at he; cases he⟩
  · intro N N' _ h1 _
    have hW : (idleRunAt ha hi sch).clk N' ≤ (idleRunAt ha hi sch).bufWindow N N' sch.Δ sch.δ :=
      le_trans ((idleRunAt ha hi sch).clk_le_ref N')
        (le_trans (le_add_of_nonneg_right hδ) (le_max_right _ _))
    obtain ⟨⟨w, hw⟩, -⟩ := h1 N' ‹_› hW
    have := (idleRun_idle ha hi (D := sch.D) sch.mvba.Δ_pos N').quiet.2.2.1 i w v
    simp_all
  · exact bufferedFair_iff_family.mpr (idleRun_bff ha hi sch hδ fun l hl => by
      subst hl; exact ⟨⟨.net, rfl⟩, fun ⟨_, _, _, he⟩ => by cases he⟩)

include hi in
/-- **(P-phase)** on the idle run: each marker fires at its landmark's clock
reading, at index 0, 2 or 4, and the phase is past it at the next index, on
the same reading. -/
theorem idleRun_phasePunctual : PhasePunctual sch (idleRunAt ha hi sch) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := phase_distinct (Phase := Phase)
  have hph := fun n => idleRun_phase ha hi (D := sch.D) sch.mvba.Δ_pos n
  intro L
  refine ⟨fun n hn => ?_, ?_⟩
  · have := idleLabel_marker hn
    cases L <;> simp only at this <;> subst this <;>
      simp [idleRunAt, idleRun, idleClk, Landmark.time, one_nsmul]
  · cases L
    · refine ⟨1, ?_, by simp [idleRunAt, idleRun, idleClk, Landmark.time]⟩
      simp [Landmark.Reached, hph, phaseAt, Ne.symm h01]
    · refine ⟨3, ?_, by simp [idleRunAt, idleRun, idleClk, Landmark.time, one_nsmul]⟩
      simp [Landmark.Reached, hph, phaseAt]
    · refine ⟨5, ?_, by simp [idleRunAt, idleRun, idleClk, Landmark.time]⟩
      simp [Landmark.Reached, hph, phaseAt]

include ha hi in
/-- **The MVBA's own scheduling** on the idle run's projection: (Δ-justice)
with its antecedent false at a quiet state, and (T-timer) since nobody
enters a view and no timer is expired. -/
theorem idleRun_mvbaOwnTiming : MvbaOwnTiming sch (idleRunAt ha hi sch) := by
  refine ⟨idleProj ha hi sch.mvba.Δ_pos, Mvba.boundedJustice_of_quiet fun N D' hD' => ⟨N, le_rfl,
      le_trans ((idleProj ha hi sch.mvba.Δ_pos (D := sch.D)).timed.clk_le_ref N) (le_add_of_nonneg_right hD'),
      fun l h hh => ?_⟩, fun n i v _ hl => ?_, fun m i v _ hent => ?_⟩
  · obtain ⟨m, hm⟩ := idleProj_quiet ha hi sch.mvba.Δ_pos (D := sch.D) N
    show ¬ Enabled _ _ ((idleProj ha hi sch.mvba.Δ_pos (D := sch.D)).run.at' N) l
    rw [hm]
    exact Mvba.not_enabled_of_quiet (idleRun_idle ha hi (D := sch.D) sch.mvba.Δ_pos m).quiet hh
  · cases hl
  · obtain ⟨k, hk⟩ := idleProj_quiet ha hi sch.mvba.Δ_pos (D := sch.D) m
    change ((idleProj ha hi sch.mvba.Δ_pos (D := sch.D)).run.at' m).entered i v = true at hent
    rw [hk, (idleRun_idle ha hi (D := sch.D) sch.mvba.Δ_pos k).quiet.2.1] at hent
    cases hent

end IdleTimed


/-! ## Quiescence, the MVBA's half, and the whole

The MVBA's own `quiescence` (the contract's field, proven by `Mvba` from its
sending rules) confines a correct validator's MVBA messages to the window
between its MVBA proposal and its MVBA abandonment. Chorus makes the first
only while participating (I1) and forwards the second from its own
`abandon` (I2), so the window lies inside Chorus's participation window. -/

section Quiescence

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
  {s s' : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}

/-- **Quiescence, the MVBA's half**: a correct validator's new MVBA message,
sent across a step out of a reachable state, finds it participating after
the step and not abandoned before it. -/
theorem mvba_sent_new {l} {i : node} {c : Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)}
    (hr : (atMvba (slot := slot) (Phase := Phase) (PathChoice := PathChoice) thM).reachable thS s)
    (htr : (atMvba thM).tr thS s l s') (hi : ¬ nset.is_byz i = true)
    (hnew : (Mvba.mvbaSafety thM).sent s'.mvba_st i c) (hold : ¬ (Mvba.mvbaSafety thM).sent s.mvba_st i c) :
    s'.participating i = true ∧ ¬ s.abandoned i = true := by
  rcases mvba_st_tr_or_eq htr with heq | ⟨l', h'⟩
  · rw [heq] at hnew
    exact absurd hnew hold
  · obtain ⟨⟨v, hv⟩, hab⟩ := Mvba.sent_new_tr thM h' i c hi hnew hold
    exact ⟨participating_of_mvba_proposed (Veil.RelationalTransitionSystem.reachable.step _ _ hr ⟨l, htr⟩) hv,
      fun ha => hab (mvba_abandoned_of_abandoned hr ha)⟩

/-- **Quiescence** (Lemma 6 (`lemma:chorus-quiescence`)), one step: a
correct validator's new message of the slot's instance, its own or its
MVBA's, sent across a step out of a reachable state, finds it participating
after the step and not abandoned before it. -/
theorem sent_new {l} {i : node} {msg : Message node merkle_root (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))}
    (hr : (atMvba (slot := slot) (Phase := Phase) (PathChoice := PathChoice) thM).reachable thS s)
    (htr : (atMvba thM).tr thS s l s') (hi : ¬ nset.is_byz i = true)
    (hnew : Sent (mvba := Mvba.mvbaSafety thM) s' i msg) (hold : ¬ Sent (mvba := Mvba.mvbaSafety thM) s i msg) :
    s'.participating i = true ∧ ¬ s.abandoned i = true := by
  by_cases hm : ∃ c, msg = .mvba c
  · obtain ⟨c, rfl⟩ := hm
    exact mvba_sent_new hr htr hi hnew hold
  · obtain ⟨hp, ha⟩ := own_sent_new (mvba := Mvba.mvbaSafety thM) (fun c h => hm ⟨c, h⟩) htr hi hnew hold
    exact ⟨Chorus.participating.mono (mvba := Mvba.mvbaSafety thM) htr i hp, by simp [ha]⟩

end Quiescence

/-! ## The run model, and the instance's fields over any quorum family -/

section Fields

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

/-- A state of one slot's instance: the slot and Chorus's state at the
`Mvba` instance, as `slotConsensusSafety` pairs them. -/
abbrev SlotState (slot node nodeset merkle_root view Phase PathChoice : Type) :=
  slot × StateAtMvba slot node nodeset merkle_root view Phase PathChoice

/-- The fragment at the `Mvba` instance. -/
noncomputable abbrev scSafety
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view) :
    SlotConsensusSafety slot node merkle_root (slot × (node → Option merkle_root))
      (SlotState slot node nodeset merkle_root view Phase PathChoice) (fun i => nset.is_byz i = true) :=
  slotConsensusSafety (mvba := Mvba.mvbaSafety thM) thS

/-- **The schedule of the slot family**: one MVBA schedule, whose `Δ` and
`δ` every slot shares, and a deadline per slot (`s.deadline`), with the two
properties of the timing model that `Schedule` carries. -/
structure FamilySchedule (slot view time : Type) [vord : TotalOrderWithMinimum view]
    [LinearOrder time] [AddCommMonoid time] where
  /-- The MVBA's schedule. -/
  mvba : Mvba.Schedule view time
  /-- Each slot's deadline. -/
  D : slot → time
  /-- A local step is no slower than a network hop (`Schedule.δ_le_Δ`). -/
  δ_le_Δ : mvba.δ ≤ mvba.Δ
  /-- A local step is no slower than the MVBA's retransmission period
  (`Schedule.δ_le_ρ`). -/
  δ_le_ρ : mvba.δ ≤ mvba.ρ
  /-- The MVBA's availability window covers one Chorus hop
  (`Schedule.Δ_le_Δsync`). -/
  Δ_le_Δsync : mvba.Δ ≤ mvba.Δsync

/-- Slot `s`'s schedule. -/
def FamilySchedule.at {time : Type} [LinearOrder time] [AddCommMonoid time]
    (fs : FamilySchedule slot view time) (s : slot) : Schedule view time :=
  ⟨fs.mvba, fs.D s, fs.δ_le_Δ, fs.δ_le_ρ, fs.Δ_le_Δsync⟩

variable {time : Type} [LinearOrder time] [AddCommMonoid time]

/-- **`SlotConsensusTemporal.Admissible`**, as this instance defines it: the
run has a labelling, a `TChorusRun` with its states, clocks and GST, that
satisfies the premises of the two claims, each by its own name and restated
nowhere. The untimed claim's three: (F-justice) on Chorus's own honest
actions, the MVBA's scheduling on the run's MVBA projection, and the
certificate bridge (`FJustice`, `MvbaAdmissible`, `ValidBridge`,
[Liveness.lean](Liveness.lean)). The timed claims' timing model at the
system's MVBA, at the run's slot's schedule (`SyncAtMvba`,
[Schedule.lean](Schedule.lean)), with the same bridge. The labels are the
witness of how the run was scheduled, which a `TimedRun` does not carry. -/
def Admissible
    {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
    {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
    (fs : FamilySchedule slot view time)
    (r : TimedRun (SlotState slot node nodeset merkle_root view Phase PathChoice) time
      (scSafety thS thM).init (scSafety thS thM).trans) : Prop :=
  ∃ r' : TChorusRun thS thM time,
    (∀ k, r'.at' k = (r.at' k).2) ∧ (∀ k, r'.clk k = r.clk k) ∧ r'.gst = r.gst ∧
    FJustice r'.toLRun ∧ MvbaAdmissible r'.toLRun ∧ ValidBridge r'.toLRun ∧
    SyncAtMvba (fs.at (r.at' 0).1) r'

end Fields

/-! ## Admissibility is not vacuous -/

section Exists

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time] [Archimedean time]

/-- **`admissible_exists`** — every initial state starts an admissible run:
the idle run at the state's slot's schedule, in which every proposer stays
silent. Two facts about the configuration make it admissible. The slot has
a proposer (`hprop`), so no meta-block is certified at an idle state and the
bridge holds with nothing to say; with no proposer at all, the empty
meta-block would be certified everywhere, and the bridge would make the
run's admissibility depend on the MVBA's validity predicate accepting it.
And some view after the first has a correct leader (`hgood`), the view at
which the MVBA's (A-viewsync) is stated; it holds vacuously, as nobody enters
a view. -/
theorem admissible_exists (fs : FamilySchedule slot view time)
    (hprop : ∃ J, thS.is_proposer J = true)
    (hgood : ∃ (W PV : view) (L : node), vord.next PV W ∧ thM.leader W L = true ∧ ¬ nset.is_byz L = true) :
    ∀ p, (scSafety thS thM).init p →
      ∃ r : TimedRun (SlotState slot node nodeset merkle_root view Phase PathChoice) time
        (scSafety thS thM).init (scSafety thS thM).trans, Admissible fs r ∧ r.at' 0 = p := by
  rintro ⟨s₀, st⟩ ⟨ha, hi⟩
  obtain ⟨J₀, hJ₀⟩ := hprop
  let r' := idleRunAt ha hi (fs.at s₀)
  refine ⟨⟨⟨fun k => (s₀, r'.at' k), ⟨ha, hi⟩, fun k => ⟨rfl, _, r'.steps k⟩⟩,
      r'.clk, r'.clk_mono, r'.clk_unbounded, r'.gst⟩,
    ⟨r', fun _ => rfl, fun _ => rfl, rfl, idleRun_fJustice ha hi _, idleRun_mvbaAdmissible ha hi _ hgood,
      ⟨fun k v hc => absurd hc (not_certified_of_idle (idleRun_idle ha hi _ k) hJ₀ v),
        fun k i v _ hd => absurd hd ((idleRun_idle ha hi _ k).not_decided i v),
        fun k i w v _ hacc => (Bool.false_ne_true
          (((idleRun_idle ha hi (D := (fs.at s₀).D) (fs.at s₀).mvba.Δ_pos k).quiet.2.2.1 i w v).symm.trans
            hacc)).elim⟩,
      ⟨idleRun_timedJustice ha hi _, idleRun_phasePunctual ha hi _, idleRun_mvbaOwnTiming ha hi _⟩⟩,
    rfl⟩

end Exists

/-! ## Sent messages stay sent -/

section SentMono

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
  {s s' : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}

/-- A message once sent stays sent: Chorus's network rows are monotone,
and the MVBA's state moves only by its own transitions, whose rows are. -/
theorem sent_mono {l} (htr : (atMvba thM).tr thS s l s') (i : node)
    (msg : Message node merkle_root (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)))
    (h : Sent (mvba := Mvba.mvbaSafety thM) s i msg) : Sent (mvba := Mvba.mvbaSafety thM) s' i msg := by
  letI := Mvba.mvbaSafety (nset := nset) thM
  cases msg with
  | proposal m => exact Chorus.msg_proposer_signed.mono htr i m h
  | votePos j m => exact Chorus.msg_vote_pos_sig_mono htr i j m h
  | voteNeg j => exact Chorus.msg_vote_neg_sig_mono htr i j h
  | voteCast => exact Chorus.msg_vote_cast.mono htr i h
  | fbPos j m => exact Chorus.msg_fb_pos_sig.mono htr i j m h
  | fbNeg j => exact Chorus.msg_fb_neg_sig.mono htr i j h
  | fallback => exact Chorus.msg_fallback_sig.mono htr i h
  | commitPos j m => exact Chorus.msg_commit_pos_sig.mono htr i j m h
  | commitNeg j => exact Chorus.msg_commit_neg_sig.mono htr i j h
  | commitCast => exact Chorus.msg_commit_cast.mono htr i h
  | decryptShare => exact Chorus.msg_decrypt_share.mono htr i h
  | fbCommit e => exact Chorus.msg_fbcommit_sig.mono htr i e h
  | chunk r j m => exact Chorus.msg_chunk.mono htr i r j m h
  | commitqcPos j m => exact Chorus.msg_commitqc_pos.mono htr i j m h
  | commitqcNeg j => exact Chorus.msg_commitqc_neg.mono htr i j h
  | fbCommitQC e => exact Chorus.msg_fbcommitqc.mono htr i e h
  | mvbaCert c => exact Chorus.msg_mvba_cert.mono htr i c h
  | mvba c =>
    rcases mvba_st_tr_or_eq htr with heq | ⟨l', h'⟩
    · show (Mvba.mvbaSafety thM).sent s'.mvba_st i c
      rw [heq]; exact h
    · exact Mvba.sent_mono_tr thM h' i c h

end SentMono

/-! ## The instance, at the system's configuration -/

section Instance

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
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time]
  [Archimedean time]
  {is_proposer : Fin n → Bool} {well_encoded : merkle_root → Bool}
  {mvba_init_state : Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)}
  {mvalid : MetaBlock (Fin n) merkle_root → Bool} {mleader : view → Fin n → Bool}

/-- The Chorus configuration at the system's instantiation. -/
local notation "thC" => Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
  is_proposer well_encoded mvba_init_state

/-- The MVBA configuration at the system's instantiation. -/
local notation "thMC" => Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader

/-- The quorum family, `n = 3f + 1` with at most `f` Byzantine validators. -/
local notation "nsetF" => byzNodeSetFin n f hf is_byz hbyz

/-- The family's quorum counting facts. -/
local notation "cntF" => Cadence.byzNodeSetFin_counting n f hf is_byz hbyz

omit [Inhabited merkle_root] [Inhabited view] node_inhabited in
/-- **A view with a correct leader and a predecessor**, from
(A-leader-rotation-k): among the `k` views after the first, one has a
correct leader. This is what the MVBA's (A-viewsync) names, and the idle
run meets it at that view. -/
theorem goodView_of_rotation (vfin : ViewOrderEnum view vord) {k : Nat}
    (hrot : Mvba.LeaderRotation (nset := nsetF) vfin k thMC) :
    ∃ (W PV : view) (L : Fin n), vord.next PV W ∧ (thMC).leader W L = true ∧
      ¬ (nsetF).is_byz L = true := by
  obtain ⟨j, -, L, hL, hc⟩ := hrot (vfin.succ vord.zero)
  refine ⟨vfin.succ^[j] (vfin.succ vord.zero), vfin.succ^[j] vord.zero, L, ?_, hL, hc⟩
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  exact vfin.next_succ _

/-- The fragment at the system's configuration. -/
local notation "SC" => scSafety (nset := nsetF) (cnt := cntF) thC thMC

omit [AddCommMonoid time] [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- The slot's tag is constant along a run. -/
theorem tag_run
    (r : TimedRun (SlotState slot (Fin n) (ByzNSet n) merkle_root view Phase PathChoice) time
      (SC).init (SC).trans) : ∀ k, (r.at' k).1 = (r.at' 0).1
  | 0 => rfl
  | k + 1 => ((r.steps k).1).symm.trans (tag_run r k)

omit [AddCommMonoid time] [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- From an admissible run's labelling: no correct validator abandons
before finalizing, read at the labelling. -/
theorem noAbandon_of {r : TimedRun (SlotState slot (Fin n) (ByzNSet n) merkle_root view Phase PathChoice) time
      (SC).init (SC).trans}
    {r' : TChorusRun (nset := nsetF) thC thMC time} (hat : ∀ k, r'.at' k = (r.at' k).2)
    (hab : ∀ i, ¬ (nsetF).is_byz i = true → ∀ k, (r.at' k).2.abandoned i = true →
      ∃ V, (SC).finalized (r.at' k) i V) :
    NoAbandonBeforeFinalizing (nset := nsetF) r'.toLRun := fun i hi k hk => by
  obtain ⟨V, hc, -⟩ := hab i hi k (by rw [← hat]; exact hk)
  rw [hat]; exact hc

/-- **`Chorus ⊨ SlotConsensusTemporal`** at the system's configuration.
Every field is proven, none is weakened:

* `sent` is `Chorus.Sent`, monotone (`sent_mono`);
* `Admissible` is `Chorus.Admissible`, the claims' premises by name;
* `admissible_exists` from the idle run, in which every proposer stays
  silent;
* `termination` from `Chorus.termination`;
* `quiescence` from `sent_new`, in Lemma 6 (`lemma:chorus-quiescence`)'s
  two parts.

Proven from named hypotheses only: the slot's proposer set is non-empty
(`hprop`), the view order's enumeration (`vfin`), (A-leader-rotation-k)
(`hrot`), and a cancellative, Archimedean time theory. -/
@[implicit_reducible]
noncomputable def chorusTemporal (fs : FamilySchedule slot view time)
    (hprop : ∃ J, is_proposer J = true)
    (vfin : ViewOrderEnum view vord) (hrot : Mvba.LeaderRotation (nset := nsetF) vfin fs.mvba.k thMC) :
    SlotConsensusTemporal slot (Fin n) merkle_root (slot × (Fin n → Option merkle_root))
      (SlotState slot (Fin n) (ByzNSet n) merkle_root view Phase PathChoice) time
      (Message (Fin n) merkle_root (Fin n → Option merkle_root) (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)))
      (fun i => (nsetF).is_byz i = true) (S := SC) :=
  letI : ByzNodeSet (Fin n) (ByzNSet n) := nsetF
  SlotConsensusTemporal.mk (S := SC)
    (sent := fun p i msg => Sent (mvba := Mvba.mvbaSafety thMC) p.2 i msg)
    (sent_mono := fun _ _ i msg h hs => sent_mono h.2.choose_spec i msg hs)
    (Admissible := Admissible fs)
    (admissible_exists := admissible_exists fs hprop (goodView_of_rotation n f hf is_byz hbyz vfin hrot))
    (termination := fun r hadm hpart hab j hj => by
      obtain ⟨r', hat, -, -, hfj, hma, hbr, -⟩ := hadm
      obtain ⟨k, hk⟩ := Chorus.termination n f hf is_byz hbyz vfin r'.toLRun hfj hma hbr
        (fun i hi => by
          obtain ⟨k, hk⟩ := hpart i hi
          exact ⟨k, by rw [hat]; exact hk⟩)
        (noAbandon_of n f hf is_byz hbyz hat hab) j hj
      exact ⟨k, _, by rw [← hat]; exact hk, rfl⟩)
    (quiescence := fun _ _ i msg hr h hi hnew hold => by
      obtain ⟨-, l, htr⟩ := h
      exact sent_new hr htr hi hnew hold)

end Instance

/-! ## `SlotConsensusWithTotality`, and the full `SlotConsensus` -/

section WithTotality

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
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedCancelAddMonoid time]
  [Archimedean time]
  {is_proposer : Fin n → Bool} {well_encoded : merkle_root → Bool}
  {mvba_init_state : Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)}
  {mvalid : MetaBlock (Fin n) merkle_root → Bool} {mleader : view → Fin n → Bool}

local notation "thC" => Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
  is_proposer well_encoded mvba_init_state
local notation "thMC" => Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader
local notation "nsetF" => byzNodeSetFin n f hf is_byz hbyz
local notation "cntF" => Cadence.byzNodeSetFin_counting n f hf is_byz hbyz
local notation "SC" => scSafety (nset := nsetF) (cnt := cntF) thC thMC

omit [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- The caller's participation, synchronized within `Δ`, read off an
admissible run's labelling. -/
theorem syncWithin_of {fs : FamilySchedule slot view time}
    {r : TimedRun (SlotState slot (Fin n) (ByzNSet n) merkle_root view Phase PathChoice) time
      (SC).init (SC).trans}
    {r' : TChorusRun (nset := nsetF) thC thMC time} (hat : ∀ k, r'.at' k = (r.at' k).2)
    (hclk : ∀ k, r'.clk k = r.clk k) (hgst : r'.gst = r.gst)
    (hsync : ∀ k i, ¬ (nsetF).is_byz i = true → (r.at' k).2.participating i = true →
      ∀ j, ¬ (nsetF).is_byz j = true →
        r.byGstBound (r.clk k) fs.mvba.Δ (fun st => st.2.participating j = true)) :
    SyncParticipationWithin (nset := nsetF) (fs.at (r.at' 0).1).Δ r' := fun k i hi hp j hj => by
  obtain ⟨m, hm, hpm⟩ := (TimedRun.byGstBound_iff _ _ _ _).mp (hsync k i hi (by rw [← hat]; exact hp) j hj)
  exact ⟨m, by rw [hclk, hclk, hgst]; exact hm, by rw [hat]; exact hpm⟩

/-- **`Chorus ⊨ SlotConsensusWithTotality`** at the system's configuration:
the two timing strengthenings, proven over the same `Admissible`.

* `ℓ` is `Lchorus Δ δ ℓ_MVBA = 5Δ + ℓ_MVBA + 9δ`, the paper's
  `5Δ + ℓ_MVBA` at `δ = 0` (`chorusWithTotality_ℓ_paper`), with `ℓ_MVBA`
  the system's MVBA's `ℓ`; `bounded_termination` is
  `Chorus.timed_termination_atMvba`; the class carries the paper's
  latency.
* `d_tot` is `Ltot Δ δ Δ = Δ + 2δ`, the paper's `Δ` at `δ = 0`
  (`chorusWithTotality_d_tot_paper`); `totality` is `Chorus.totality` at
  tolerance `Δ`.
* `deadline` is the family schedule's per-slot deadline.

The two caller antecedents, no abandonment before finalizing (C1) and no
start before `D − Δ` (C2), are the fields' own. -/
@[implicit_reducible]
noncomputable def chorusWithTotality (fs : FamilySchedule slot view time)
    (hprop : ∃ J, is_proposer J = true)
    (vfin : ViewOrderEnum view vord) (hrot : Mvba.LeaderRotation (nset := nsetF) vfin fs.mvba.k thMC) :
    SlotConsensusWithTotality slot (Fin n) merkle_root (slot × (Fin n → Option merkle_root))
      (SlotState slot (Fin n) (ByzNSet n) merkle_root view Phase PathChoice) time
      (Message (Fin n) merkle_root (Fin n → Option merkle_root) (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)))
      (fun i => (nsetF).is_byz i = true) (S := SC)
      (T := chorusTemporal n f hf is_byz hbyz fs hprop vfin hrot) :=
  letI : ByzNodeSet (Fin n) (ByzNSet n) := nsetF
  SlotConsensusWithTotality.mk (S := SC) (T := chorusTemporal n f hf is_byz hbyz fs hprop vfin hrot)
    (Δ := fs.mvba.Δ)
    (ℓ := Lchorus fs.mvba.Δ fs.mvba.δ (fs.mvba.ℓ vfin))
    (d_tot := Ltot fs.mvba.Δ fs.mvba.δ fs.mvba.Δ)
    (deadline := fs.D)
    (SyncParticipation := fun r => ∀ k i, ¬ (nsetF).is_byz i = true → (r.at' k).2.participating i = true →
      ∀ j, ¬ (nsetF).is_byz j = true →
        r.byGstBound (r.clk k) fs.mvba.Δ (fun st => st.2.participating j = true))
    (syncParticipation_def := fun _ => Iff.rfl)
    (bounded_termination := fun r hadm hsync hab hC2 t hall j hj => by
      obtain ⟨r', hat, hclk, hgst, -, -, hbr, hsa⟩ := hadm
      obtain ⟨m, hm, hc⟩ := timed_termination_atMvba n f hf is_byz hbyz (fs.at (r.at' 0).1)
        vfin hrot r' hsa hbr
        (syncWithin_of n f hf is_byz hbyz hat hclk hgst hsync)
        (noAbandon_of n f hf is_byz hbyz hat hab)
        (fun k i hi hp => by
          have h := hC2 k i hi (by show (r.at' k).2.participating i = true; rw [← hat]; exact hp)
          rw [show (SC).tag (r.at' k) = (r.at' 0).1 from tag_run n f hf is_byz hbyz r k] at h
          rw [hclk]; exact h)
        t (fun i hi => by
          obtain ⟨k, hk, hp⟩ := hall i hi
          exact ⟨k, by rw [hclk]; exact hk, by rw [hat]; exact hp⟩) j hj
      rw [TimedRun.byGstBound_iff]
      exact ⟨m, by rw [← hclk, ← hgst]; exact hm, _, by rw [← hat]; exact hc, rfl⟩)
    (totality := fun r hadm hsync hab k i V hi hfin j hj => by
      obtain ⟨r', hat, hclk, hgst, -, -, -, hTJ, -, -⟩ := hadm
      obtain ⟨m, hm, hc⟩ := Chorus.totality (nset := nsetF) (cnt := cntF) (fs.at (r.at' 0).1)
        (fs.at (r.at' 0).1).Δ r' hTJ (syncWithin_of n f hf is_byz hbyz hat hclk hgst hsync)
        (noAbandon_of n f hf is_byz hbyz hat hab) k i hi (by rw [hat]; exact hfin.1) j hj
      rw [TimedRun.byGstBound_iff]
      exact ⟨m, by rw [← hclk, ← hclk, ← hgst]; exact hm, _, by rw [← hat]; exact hc, rfl⟩)

/-- **`Chorus ⊨ SlotConsensus`**: the full contract, the proven fragment and
the proven temporal level joined by `slotConsensus_of_temporal`. -/
@[implicit_reducible]
noncomputable def slotConsensusFull (fs : FamilySchedule slot view time)
    (hprop : ∃ J, is_proposer J = true)
    (vfin : ViewOrderEnum view vord) (hrot : Mvba.LeaderRotation (nset := nsetF) vfin fs.mvba.k thMC) :
    SlotConsensus slot (Fin n) merkle_root (slot × (Fin n → Option merkle_root))
      (SlotState slot (Fin n) (ByzNSet n) merkle_root view Phase PathChoice) time
      (Message (Fin n) merkle_root (Fin n → Option merkle_root) (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)))
      (fun i => (nsetF).is_byz i = true) :=
  slotConsensus_of_temporal (nset := nsetF) (cnt := cntF) (mvba := Mvba.mvbaSafety (nset := nsetF) thMC) thC
    (chorusTemporal n f hf is_byz hbyz fs hprop vfin hrot)

/-- The join hands back exactly the proven fragment. -/
theorem slotConsensusFull_toSafety (fs : FamilySchedule slot view time)
    (hprop : ∃ J, is_proposer J = true)
    (vfin : ViewOrderEnum view vord) (hrot : Mvba.LeaderRotation (nset := nsetF) vfin fs.mvba.k thMC) :
    (slotConsensusFull (is_proposer := is_proposer) (well_encoded := well_encoded) (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader) n f hf is_byz hbyz fs hprop vfin hrot).toSlotConsensusSafety =
      slotConsensusSafety (nset := nsetF) (cnt := cntF) (mvba := Mvba.mvbaSafety (nset := nsetF) thMC) thC := rfl

/-- **`ℓ`, pinned**: Chorus's termination latency over the MVBA's. -/
theorem chorusWithTotality_ℓ (fs : FamilySchedule slot view time)
    (hprop : ∃ J, is_proposer J = true)
    (vfin : ViewOrderEnum view vord) (hrot : Mvba.LeaderRotation (nset := nsetF) vfin fs.mvba.k thMC) :
    (chorusWithTotality (is_proposer := is_proposer) (well_encoded := well_encoded) (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader) n f hf is_byz hbyz fs hprop vfin hrot).ℓ =
      Lchorus fs.mvba.Δ fs.mvba.δ (Mvba.mvbaTemporal (nset := nsetF) thMC (hqeFin n f hf is_byz hbyz) fs.mvba vfin hrot).ℓ :=
  rfl

/-- **`d_tot`, pinned**: Chorus's totality latency at tolerance `Δ`. -/
theorem chorusWithTotality_d_tot (fs : FamilySchedule slot view time)
    (hprop : ∃ J, is_proposer J = true)
    (vfin : ViewOrderEnum view vord) (hrot : Mvba.LeaderRotation (nset := nsetF) vfin fs.mvba.k thMC) :
    (chorusWithTotality (is_proposer := is_proposer) (well_encoded := well_encoded) (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader) n f hf is_byz hbyz fs hprop vfin hrot).d_tot =
      Ltot fs.mvba.Δ fs.mvba.δ fs.mvba.Δ :=
  rfl

/-- At `δ = 0`, the paper's instantaneous local computation, `ℓ` is the
paper's `5Δ + ℓ_MVBA` (Lemma 11 (`lemma:chorus-termination`)). -/
theorem chorusWithTotality_ℓ_paper (fs : FamilySchedule slot view time)
    (hprop : ∃ J, is_proposer J = true)
    (vfin : ViewOrderEnum view vord) (hrot : Mvba.LeaderRotation (nset := nsetF) vfin fs.mvba.k thMC)
    (hδ : fs.mvba.δ = 0) :
    (chorusWithTotality (is_proposer := is_proposer) (well_encoded := well_encoded) (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader) n f hf is_byz hbyz fs hprop vfin hrot).ℓ =
      5 • fs.mvba.Δ + (Mvba.mvbaTemporal (nset := nsetF) thMC (hqeFin n f hf is_byz hbyz) fs.mvba vfin hrot).ℓ := by
  rw [chorusWithTotality_ℓ, hδ]
  exact Lchorus_paper _ _

/-- At `δ = 0`, `d_tot` is the paper's `Δ` (Proposition 4
(`prop:chorus-totality`)). -/
theorem chorusWithTotality_d_tot_paper (fs : FamilySchedule slot view time)
    (hprop : ∃ J, is_proposer J = true)
    (vfin : ViewOrderEnum view vord) (hrot : Mvba.LeaderRotation (nset := nsetF) vfin fs.mvba.k thMC)
    (hδ : fs.mvba.δ = 0) :
    (chorusWithTotality (is_proposer := is_proposer) (well_encoded := well_encoded) (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader) n f hf is_byz hbyz fs hprop vfin hrot).d_tot = fs.mvba.Δ := by
  rw [chorusWithTotality_d_tot, hδ]
  exact Ltot_paper _

end WithTotality

end Chorus

/-! ## The pinned trust base

The standard Lean trio and nothing else: no `sorryAx`. -/

/--
info: 'Chorus.participating_of_mvba_proposed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.participating_of_mvba_proposed

/--
info: 'Chorus.mvba_abandoned_of_abandoned' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.mvba_abandoned_of_abandoned

/--
info: 'Chorus.relayedWhileActive_of_timedJustice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.relayedWhileActive_of_timedJustice

/--
info: 'Chorus.mvba_sent_new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.mvba_sent_new

/--
info: 'Chorus.sent_new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.sent_new

/--
info: 'Chorus.not_enabled_of_idle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.not_enabled_of_idle

/--
info: 'Chorus.not_certified_of_idle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.not_certified_of_idle

/--
info: 'Chorus.idleRun_fJustice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.idleRun_fJustice

/--
info: 'Chorus.idleRun_mvbaAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.idleRun_mvbaAdmissible

/--
info: 'Chorus.idleRun_timedJustice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.idleRun_timedJustice

/--
info: 'Chorus.idleRun_phasePunctual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.idleRun_phasePunctual

/--
info: 'Chorus.idleRun_mvbaOwnTiming' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.idleRun_mvbaOwnTiming

/--
info: 'Chorus.admissible_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.admissible_exists

/--
info: 'Chorus.chorusTemporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.chorusTemporal

/--
info: 'Chorus.chorusWithTotality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.chorusWithTotality

/--
info: 'Chorus.slotConsensusFull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensusFull

/--
info: 'Chorus.slotConsensusFull_toSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensusFull_toSafety

/--
info: 'Chorus.chorusWithTotality_ℓ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.chorusWithTotality_ℓ

/--
info: 'Chorus.chorusWithTotality_d_tot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.chorusWithTotality_d_tot

/--
info: 'Chorus.chorusWithTotality_ℓ_paper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.chorusWithTotality_ℓ_paper

/--
info: 'Chorus.chorusWithTotality_d_tot_paper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.chorusWithTotality_d_tot_paper
