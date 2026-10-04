import Cadence.Composed.Glue

/-! # Composed.Corollary4 — the loop closed: each side's caller conditions, discharged

[ConductorBounds.md](../../docs/ConductorBounds.md) §4.2–§4.3, stage K7.
Within Cadence, each of Chorus and the Conductor is the other's caller, and
each one's timed claims are conditional on its caller. This file discharges
every such condition as a theorem about the composed run
([Schedule.lean](Schedule.lean)):

| condition | of | discharged from | theorem |
|---|---|---|---|
| C1: no abandonment before finalizing | Chorus | the glue's `[abandoned_after_finalize]` | `c1_slot` |
| C2: no start before `D − Δ` | Chorus | the glue's `[participating_opened]`, the Conductor's `integrity_timing` and its clock, `D = start + Δ` | `c2_slot` |
| participation by `t` | Chorus | the Conductor's openings and the `on_open` row | `participating_by` |
| Δ-synchronized participation | Chorus | Lemma 15 within Cadence and the `on_open` row | `sync_slot`, `openings_sync` |
| (R-tot) | the Conductor | Chorus's `d_tot`-Totality, through `on_open` and `on_finalize` | `caller_totality` |
| (R-term) | the Conductor | Chorus's `ℓ`-Termination, through `on_open` and `on_finalize` | `caller_termination` |

The loop is not circular, as the paper's "No circularity" paragraph after
Corollary 4 (`cor:chorus-correctness-within-cadence`) explains, and the
types show it: (R-tot) is a statement per slot ("openings synchronized ⇒
completions synchronized"), proven from Chorus's totality *under* that
slot's synchronized openings; the Conductor's window induction
(`Conductor.totality`) then yields every slot's synchronized openings
(`openings_sync`), and Corollary 4 is the one-way application of that to
Chorus (`corollary4`).

Each side is consumed through what is proven of it: Chorus through its
contract instance `Chorus.chorusWithTotality` (bounded termination and
totality) and `Chorus.chorusTemporal` (termination), on each slot's part
of the run; the Conductor through `Conductor.totality` (Lemma 15
(`lemma:conductor-totality`)), on the orchestrator's part, which takes only
the premises Totality uses. Every conclusion is brought back to the
composed run by [PartProjection.lean](../PartProjection.lean)'s transfer
lemmas. -/

namespace Composed

open Cadence Conductor
open scoped Cadence.Timed

attribute [local instance] natSlotOrder

/-! ## The inputs the instances accept -/

section Accept

open Classical ByzNodeSet

variable {merkle_root view Phase PathChoice : Type}
  [Inhabited merkle_root] [Inhabited view] [Inhabited Phase] [Inhabited PathChoice]
  [vord : TotalOrderWithMinimum view]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
  [node_inhabited : Inhabited (Fin n)]
  {thS : ChorusTh merkle_root view Phase PathChoice n} {thM : MvbaTh merkle_root view n}

set_option maxHeartbeats 1000000 in
/-- **Chorus accepts `participate()` everywhere**: the input has no guard. -/
theorem sc_participate_exists (s : SlotSt merkle_root view Phase PathChoice n) (i : Fin n) :
    ∃ s', (SC n f hf is_byz hbyz thS thM).participate s i s' := by
  have : ∃ s2, (Chorus.atMvba (slot := ℕ) (nset := byzNodeSetFin n f hf is_byz hbyz)
      (Phase := Phase) (PathChoice := PathChoice) thM).tr thS s.2 (.participate i) s2 := by
    simp only [Chorus.atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp]
    exact ⟨_, rfl⟩
  obtain ⟨s2, h⟩ := this
  exact ⟨(s.1, s2), rfl, h⟩

/-- **Chorus accepts `abandon()` everywhere**: it forwards the input to the
MVBA, whose `abandon()` has no guard. -/
theorem sc_abandon_exists (s : SlotSt merkle_root view Phase PathChoice n) (i : Fin n) :
    ∃ s', (SC n f hf is_byz hbyz thS thM).abandon s i s' := by
  obtain ⟨mn, hm⟩ := Chorus.mvba_abandon_exists (nset := byzNodeSetFin n f hf is_byz hbyz) (thM := thM) s.2.mvba_st i
  obtain ⟨s2, h⟩ := Chorus.abandon_exists (slot := ℕ) (nset := byzNodeSetFin n f hf is_byz hbyz) (Phase := Phase) (PathChoice := PathChoice)
    (thS := thS) (s := s.2) hm
  exact ⟨(s.1, s2), rfl, mn, h⟩

end Accept

section AcceptConductor

variable {window node acsstate time : Type} [Inhabited window] [Inhabited node] [Inhabited acsstate]
  [Inhabited time] [win_ord : TotalOrderWithMinimum window] [time_ord : TotalOrder time]
  [fm : FaultModel node] [A : ACSSafety node ℕ acsstate fm.byz]
  {th : Conductor.Theory ℕ window time node acsstate}

set_option maxHeartbeats 1000000 in
/-- **The Conductor accepts `complete(s)`** of an opened, uncompleted slot
at a correct validator (`complete_slot`'s guards). -/
theorem orch_complete_exists (o : CState window time node acsstate) (i : node) (x : ℕ)
    (hi : ¬ fm.byz i) (ho : (orchestratorSafety th).opened o i x)
    (hnc : ¬ (orchestratorSafety th).completed o i x) :
    ∃ o', (orchestratorSafety th).complete o i x o' := by
  change ∃ o', (Conductor.relationalTransitionSystem ℕ window time node acsstate).tr th o (.complete_slot i x) o'
  simp only [Conductor.relationalTransitionSystem, Conductor.Next, Conductor.NextAct, trSimp]
  exact ⟨_, hi, ho, hnc, rfl⟩

end AcceptConductor

/-! ## Corollary 4: Chorus's caller conditions, discharged in the composed run -/

section Main

open Classical ByzNodeSet

variable {merkle_root view Phase PathChoice window acsstate : Type}
  [Inhabited merkle_root] [Inhabited view] [Inhabited Phase] [Inhabited PathChoice]
  [Inhabited window] [Inhabited acsstate]
  [vord : TotalOrderWithMinimum view] [win_ord : TotalOrderWithMinimum window]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
  [node_inhabited : Inhabited (Fin n)]
  {time : Type} [LinearOrder time] [Inhabited time] [AddCommMonoid time]
  [IsOrderedCancelAddMonoid time] [Archimedean time]
  [A : ACSSafety (Fin n) ℕ acsstate (fmF n f hf is_byz hbyz).byz]
  {vfin : ViewOrderEnum view vord} {msg : Type}
  {thO : Conductor.Theory ℕ window time (Fin n) acsstate}
  {is_proposer : Fin n → Bool} {well_encoded : merkle_root → Bool}
  {mvba_init_state : Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)}
  {mvalid : MetaBlock (Fin n) merkle_root → Bool} {mleader : view → Fin n → Bool}
  {thG : GTheory merkle_root view Phase PathChoice window time acsstate n}

/-- The Chorus configuration at the system's instantiation. -/
local notation "thC" => Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice)
  is_proposer well_encoded mvba_init_state
/-- The MVBA configuration at the system's instantiation. -/
local notation "thMC" => Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader
local notation "OSI" => OS n f hf is_byz hbyz (A := A) thO
local notation "SCI" => SC n f hf is_byz hbyz thC thMC
local notation "PO" => stutterComp (orchC n f hf is_byz hbyz (A := A) thO thC thMC thG)
local notation "LO" => liftRun (orchC n f hf is_byz hbyz (A := A) thO thC thMC thG)
local notation "PS" x:max => stutterComp (slotC n f hf is_byz hbyz (A := A) thO thC thMC thG x)
local notation "LS" x:max => liftRun (slotC n f hf is_byz hbyz (A := A) thO thC thMC thG x)
/-- The glue's instance arguments at the system's instances. -/
local notation "GI" => TotalOrderWithMinimum.toTotalOrder

variable {r : TSysRun n f hf is_byz hbyz (A := A) thO
  (Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer well_encoded
    mvba_init_state)
  (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader) thG}

omit [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- **The Conductor's clock never runs ahead of the run's**: at every
composed index, the orchestrator's `now` is at most the run's clock. Its
part's run reads `now` as its clock (`ClockAgrees`), at the index where the
part entered its current state, which is no later. -/
theorem clock_le (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal (Fin n) ℕ acsstate time msg (fmF n f hf is_byz hbyz).byz)
    (po : (PO).Projection (LO r).toLRun)
    (hadm : Conductor.Admissible (fm := fmF n f hf is_byz hbyz) sch TA thO (partRun po)) (m : Nat) :
    (r.at' m).os.now ≤ r.clk m := by
  obtain ⟨r', hr', -, -, hc, -⟩ := hadm
  have h1 : ∀ k, (partRun po).clk k = ((partRun po).at' k).now := by
    rw [← hr']; exact hc
  have h2 := h1 ((PO).cover (LO r).toLRun m)
  rw [partRun_at'_cover] at h2
  rw [show (r.at' m).os.now = (partRun po).clk _ from h2.symm, partRun_clk]
  exact (LO r).clk_le_of_le (po.entry_cover_le m)

omit [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- Synchronized openings, read on the orchestrator's part, give
synchronized openings in the composed run. -/
theorem openSync_composed [IsOrderedAddMonoid time] (po : (PO).Projection (LO r).toLRun) {x : ℕ} {d : time}
    (h : (OSI).OpeningsSyncWithin (partRun po) x d) {N : Nat} {i : Fin n}
    (hi : ¬ (fmF n f hf is_byz hbyz).byz i) (ho : (OSI).opened (r.at' N).os i x)
    {j : Fin n} (hj : ¬ (fmF n f hf is_byz hbyz).byz j) :
    ∃ m, r.clk m ≤ max (r.clk N) r.gst + d ∧ (OSI).opened (r.at' m).os j x :=
  composed_byGst_of_cover po N d _ (h _ i hi (by rw [partRun_at'_cover]; exact ho) j hj)

omit [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- **Synchronized openings give synchronized participation** — the glue's
`on_open` row at `δ = 0`: a correct validator that participates in `x` has
opened it, every correct validator opens it within `d`, and participates in
the same instant. -/
theorem partSync_composed [IsOrderedAddMonoid time] (sch : ConductorSchedule view time vfin)
    (rows : GlueRows (slot_ord := TotalOrderWithMinimum.toTotalOrder) (fm := fmF n f hf is_byz hbyz)
      (orch := OSI) (sc := SCI) thG sch.δ r)
    (po : (PO).Projection (LO r).toLRun) {x : ℕ} {d : time} (hd : 0 ≤ d)
    (h : (OSI).OpeningsSyncWithin (partRun po) x d) {N : Nat} {i : Fin n}
    (hi : ¬ (fmF n f hf is_byz hbyz).byz i) (hp : (SCI).participating ((r.at' N).sc_state x) i)
    {j : Fin n} (hj : ¬ (fmF n f hf is_byz hbyz).byz j) :
    ∃ m, r.clk m ≤ max (r.clk N) r.gst + d ∧ (SCI).participating ((r.at' m).sc_state x) j := by
  have ho := inv_participating_opened (slot_ord := TotalOrderWithMinimum.toTotalOrder)
    (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) (r.reachable N) hi hp
  obtain ⟨m1, hm1, ho1⟩ := openSync_composed n f hf is_byz hbyz po h hi ho hj
  obtain ⟨m2, -, hc2, hp2⟩ := within_participating (slot_ord := TotalOrderWithMinimum.toTotalOrder)
    (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) rows
    (sc_participate_exists n f hf is_byz hbyz) hj ho1
  refine ⟨m2, le_trans hc2 ?_, hp2⟩
  rw [show sch.δ = 0 from sch.δ_zero, add_zero]
  exact max_le hm1 (le_trans (le_max_right _ _) (le_add_of_nonneg_right hd))

/-! ### The caller conditions on a slot's part -/

omit [AddCommMonoid time] [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- **C1 on slot `x`'s part**: no correct validator abandons before it has
finalized — the glue's `[abandoned_after_finalize]` (Algorithm 1, line 23
(`line:abandon`) is in the handler of `finalize`), at every state of the
part's run. -/
theorem c1_slot {x : ℕ} (ps : (PS x).Projection ((LS x) r).toLRun) :
    ∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true → ∀ k,
      (SCI).abandoned ((partRun ps).at' k) i → ∃ V, (SCI).finalized ((partRun ps).at' k) i V := by
  intro i hi k h
  rw [partRun_at'] at h ⊢
  exact inv_abandoned_finalized (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
    (r.reachable _) hi h

omit [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- **C2 on slot `x`'s part**: no correct validator starts participating
before `D − Δ`. A participant has opened `x` (the glue's
`[participating_opened]`), the Conductor opens no slot before its starting
time (`integrity_timing`), its clock is the run's, and the slot's deadline is
its starting time plus `Δ` (`D_eq`, at τ-spaced starting times). -/
theorem c2_slot [IsOrderedAddMonoid time] (sch : ConductorSchedule view time vfin)
    (TA : ACSTemporal (Fin n) ℕ acsstate time msg (fmF n f hf is_byz hbyz).byz)
    (hstart : StartTimes sch thO)
    (po : (PO).Projection (LO r).toLRun)
    (hpo : Conductor.Admissible (fm := fmF n f hf is_byz hbyz) sch TA thO (partRun po))
    {x : ℕ} (ps : (PS x).Projection ((LS x) r).toLRun) :
    ∀ k i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true →
      (SCI).participating ((partRun ps).at' k) i →
      sch.D ((SCI).tag ((partRun ps).at' k)) ≤ (partRun ps).clk k + sch.Δ := by
  intro k i hi hp
  rw [partRun_at'] at hp ⊢
  rw [partRun_clk]
  have hr := r.reachable (ps.entry k)
  have htag := inv_sc_tagged (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) hr x
  have ho := inv_participating_opened (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) hr hi hp
  have hint := (OSI).integrity_timing _
    (inv_orch_reachable (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) hr) i x hi ho
  have hcl := clock_le n f hf is_byz hbyz sch TA po hpo (ps.entry k)
  change sch.D ((SCI).tag ((r.at' (ps.entry k)).sc_state x)) ≤ _
  rw [show (SCI).tag ((r.at' (ps.entry k)).sc_state x) = x from htag, sch.D_eq x]
  have h1 : sch.start₀ + x • sch.τ ≤ (r.at' (ps.entry k)).os.now := by
    have := hstart x
    simp only [ConductorSchedule.startTime] at this
    rw [← this]
    exact hint
  exact add_le_add_left (le_trans h1 hcl) _

omit [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- **Δ-synchronized participation on slot `x`'s part** (Definition 5
(`def:delta-synchronized-participation`)), from synchronized openings of
`x` within `Δ` and the glue's `on_open` row: the form Chorus's
`SyncParticipation` takes. -/
theorem sync_slot [IsOrderedAddMonoid time] (sch : ConductorSchedule view time vfin)
    (rows : GlueRows (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) thG sch.δ r)
    (po : (PO).Projection (LO r).toLRun) {x : ℕ}
    (h : (OSI).OpeningsSyncWithin (partRun po) x sch.Δ) (ps : (PS x).Projection ((LS x) r).toLRun) :
    ∀ k i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true →
      ((partRun ps).at' k).2.participating i = true →
      ∀ j, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz j = true →
        (partRun ps).byGstBound ((partRun ps).clk k) sch.Δ (fun st => st.2.participating j = true) := by
  intro k i hi hp j hj
  rw [partRun_byGstBound_iff]
  rw [partRun_at'] at hp
  exact partSync_composed n f hf is_byz hbyz sch rows po sch.mvba.Δ_pos.le h hi hp hj

/-! ### The two directions of the loop -/

variable (sch : ConductorSchedule view time vfin)
  (TA : ACSTemporal (Fin n) ℕ acsstate time msg (fmF n f hf is_byz hbyz).byz)
  (hprop : ∃ J, is_proposer J = true)
  (hrot : Mvba.LeaderRotation (nset := byzNodeSetFin n f hf is_byz hbyz) vfin sch.mvba.k
    (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader))

/-- Chorus's timed contract level at the system's configuration. -/
local notation "CWT" => Chorus.chorusWithTotality (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice)
  (is_proposer := is_proposer) (well_encoded := well_encoded) (mvba_init_state := mvba_init_state)
  (mvalid := mvalid) (mleader := mleader) n f hf is_byz hbyz sch.toFamilySchedule hprop vfin hrot

omit [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- A `δ`-row read from `M` lands by `B` when `M`'s clock and GST do. -/
theorem ref_le_bound [IsOrderedAddMonoid time] {M : Nat} {B : time} (hM : r.clk M ≤ B) (hg : r.gst ≤ B) :
    r.ref M + sch.δ ≤ B := by
  rw [show sch.δ = 0 from sch.δ_zero, add_zero]
  exact max_le hM hg

include hprop hrot in
/-- **(R-tot), discharged** — the Conductor's caller condition at `d_tot`,
from Chorus's `d_tot`-Totality (Proposition 4 (`prop:chorus-totality`))
through the glue: for every slot whose openings are synchronized within
`d_tot = Δ`, participation is (`on_open`), so the finalizations are
(Chorus's totality, with C1), and so are the completions (`on_finalize`).
Each slot's Chorus is consumed through its contract instance,
`Chorus.chorusWithTotality`, on the slot's part of the run. -/
theorem caller_totality
    (rows : GlueRows (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) thG sch.δ r)
    (hslot : SlotAdmissible n f hf is_byz hbyz (A := A) sch r)
    (po : (PO).Projection (LO r).toLRun) :
    (OSI).CallerTotality (partRun po) sch.d_tot := by
  intro x hos
  rw [sch.d_tot_paper] at hos ⊢
  intro k i hi hc j hj
  rw [partRun_byGstBound_iff]
  rw [partRun_at'] at hc
  rw [partRun_clk]
  have hr := r.reachable (po.entry k)
  obtain ⟨v, hd⟩ := inv_completed_delivered (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) hr hi hc
  have hfin := inv_delivered_finalized (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) hr hi hd
  have ho := inv_delivered_opened (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) hr hi hd
  obtain ⟨m0, -, -, hp0⟩ := within_participating (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
    (orch := OSI) (sc := SCI) rows (sc_participate_exists n f hf is_byz hbyz) hi ho
  obtain ⟨ps, hps⟩ := hslot x ⟨m0, i, hi, hp0⟩
  have htot := (CWT).totality (partRun ps) hps (sync_slot n f hf is_byz hbyz sch rows po hos ps)
    (c1_slot n f hf is_byz hbyz ps) ((PS x).cover ((LS x) r).toLRun (po.entry k)) i v hi
    (by rw [partRun_at'_cover]; exact hfin) j hj
  obtain ⟨m1, hm1, V', hV'⟩ := composed_byGst_of_cover ps (po.entry k) _ _ htot
  change r.clk m1 ≤ max (r.clk (po.entry k)) r.gst + sch.d_tot at hm1
  rw [sch.d_tot_paper] at hm1
  obtain ⟨m2, hm2, ho2⟩ := openSync_composed n f hf is_byz hbyz po hos hi ho hj
  have hcM := r.clk_max_le' hm1 hm2
  obtain ⟨m3, -, hc3, v3, hd3⟩ := within_delivered (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
    (orch := OSI) (sc := SCI) rows
    (fun o i x _ hi ho hnc => orch_complete_exists (fm := fmF n f hf is_byz hbyz) (A := A) o i x hi ho hnc)
    (sc_abandon_exists n f hf is_byz hbyz) hj
    (run_opened_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
      ho2 _ (le_max_right m1 m2))
    (run_finalized_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
      hV' _ (le_max_left m1 m2))
  refine ⟨m3, le_trans hc3 (ref_le_bound n f hf is_byz hbyz sch hcM
    (le_trans (le_max_right _ _) (le_add_of_nonneg_right sch.mvba.Δ_pos.le))), ?_⟩
  exact inv_delivered_completed (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) (r.reachable m3) hj hd3

omit [IsOrderedCancelAddMonoid time] [Archimedean time] in
/-- Participation by `max(t, GST)` of every correct validator that opened
`x` by `t` — the `on_open` row at `δ = 0`. -/
theorem participating_by
    (rows : GlueRows (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) thG sch.δ r)
    {x : ℕ} {t : time} {i : Fin n} (hi : ¬ (fmF n f hf is_byz hbyz).byz i) {N : Nat}
    (hN : r.clk N ≤ t) (ho : (OSI).opened (r.at' N).os i x) :
    ∃ m, r.clk m ≤ max t r.gst ∧ (SCI).participating ((r.at' m).sc_state x) i := by
  obtain ⟨m, -, hc, hp⟩ := within_participating (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
    (orch := OSI) (sc := SCI) rows (sc_participate_exists n f hf is_byz hbyz) hi ho
  refine ⟨m, le_trans hc ?_, hp⟩
  rw [show sch.δ = 0 from sch.δ_zero, add_zero]
  exact max_le_max hN le_rfl

include hprop hrot in
/-- **(R-term), discharged** — the Conductor's caller condition at `d_tot`
and `ℓ_chorus`, from Chorus's `ℓ`-Termination (Lemma 11
(`lemma:chorus-termination`)) through the glue: if every correct validator
opens a slot by `t`, with its openings synchronized within `Δ`, every correct
validator participates by `max(t, GST)` (`on_open`), finalizes by
`max(t, GST) + ℓ_chorus` (Chorus's bounded termination, with C1 and C2),
and completes then (`on_finalize`). -/
theorem caller_termination
    (rows : GlueRows (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) thG sch.δ r)
    (hslot : SlotAdmissible n f hf is_byz hbyz (A := A) sch r)
    (po : (PO).Projection (LO r).toLRun)
    (hpo : Conductor.Admissible (fm := fmF n f hf is_byz hbyz) sch TA thO (partRun po))
    (hstart : StartTimes sch thO) :
    (OSI).CallerTermination (partRun po) sch.d_tot sch.ℓchorus := by
  intro x hos t hall j hj
  rw [sch.d_tot_paper] at hos
  rw [partRun_byGstBound_iff]
  have hopen : ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
      ∃ N, r.clk N ≤ t ∧ (OSI).opened (r.at' N).os i x := fun i hi =>
    (partRun_byTime_iff po t _).1 (hall i hi)
  have hpart : ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
      ∃ m, r.clk m ≤ max t r.gst ∧ (SCI).participating ((r.at' m).sc_state x) i := fun i hi => by
    obtain ⟨N, hN, ho⟩ := hopen i hi
    exact participating_by n f hf is_byz hbyz sch rows hi hN ho
  obtain ⟨m0, -, hp0⟩ := hpart j hj
  obtain ⟨ps, hps⟩ := hslot x ⟨m0, j, hj, hp0⟩
  have hbt := (CWT).bounded_termination (partRun ps) hps (sync_slot n f hf is_byz hbyz sch rows po hos ps)
    (c1_slot n f hf is_byz hbyz ps) (c2_slot n f hf is_byz hbyz sch TA hstart po hpo ps) (max t r.gst)
    (fun i hi => (partRun_byTime_iff ps _ _).2 (hpart i hi)) j hj
  obtain ⟨m1, hm1, V, hV⟩ := (partRun_byGstBound_iff ps _ _ _).1 hbt
  change r.clk m1 ≤ max (max t r.gst) r.gst + sch.ℓchorus at hm1
  rw [max_assoc, max_self] at hm1
  obtain ⟨N, hN, hoj⟩ := hopen j hj
  have hNb : r.clk N ≤ max t r.gst + sch.ℓchorus :=
    le_trans hN (le_trans (le_max_left _ _) (le_add_of_nonneg_right sch.ℓchorus_nonneg))
  have hcM := r.clk_max_le' hm1 hNb
  obtain ⟨m3, -, hc3, v3, hd3⟩ := within_delivered (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
    (orch := OSI) (sc := SCI) rows
    (fun o i x _ hi ho hnc => orch_complete_exists (fm := fmF n f hf is_byz hbyz) (A := A) o i x hi ho hnc)
    (sc_abandon_exists n f hf is_byz hbyz) hj
    (run_opened_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
      hoj _ (le_max_right m1 N))
    (run_finalized_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
      hV _ (le_max_left m1 N))
  refine ⟨m3, le_trans hc3 (ref_le_bound n f hf is_byz hbyz sch hcM
    (le_trans (le_max_right _ _) (le_add_of_nonneg_right sch.ℓchorus_nonneg))), ?_⟩
  exact inv_delivered_completed (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) (r.reachable m3) hj hd3

include hprop hrot in
/-- **Lemma 15 (`lemma:conductor-totality`), within Cadence**: in the
composed run every slot's openings are synchronized within `d_tot = Δ`.
The Conductor's `d_tot`-Totality (`Conductor.totality`) on its part of the
run, with its caller condition (R-tot) discharged by `caller_totality`. -/
theorem openings_sync
    (rows : GlueRows (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) thG sch.δ r)
    (hslot : SlotAdmissible n f hf is_byz hbyz (A := A) sch r)
    (po : (PO).Projection (LO r).toLRun)
    (hpo : Conductor.Admissible (fm := fmF n f hf is_byz hbyz) sch TA thO (partRun po))
    (hunb : StartsUnbounded thO) (hΔ : TA.Δ = sch.Δ) :
    ∀ x, (OSI).OpeningsSyncWithin (partRun po) x sch.Δ := by
  have hcall := caller_totality n f hf is_byz hbyz sch hprop hrot rows hslot po
  obtain ⟨r', hr', hsync⟩ := hpo
  intro x
  rw [← sch.d_tot_paper]
  have := Conductor.totality (fm := fmF n f hf is_byz hbyz) sch TA thO hunb hΔ r' hsync
    (by rw [hr']; exact hcall) x
  rw [hr'] at this
  exact this

/-! ### Corollary 4 -/

/-- Chorus's temporal contract level at the system's configuration. -/
local notation "CT" => Chorus.chorusTemporal (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice)
  (is_proposer := is_proposer) (well_encoded := well_encoded) (mvba_init_state := mvba_init_state)
  (mvalid := mvalid) (mleader := mleader) n f hf is_byz hbyz sch.toFamilySchedule hprop vfin hrot

include hprop hrot in
/-- **Corollary 4 (`cor:chorus-correctness-within-cadence`), the caller
conditions** — in every admissible composed run, every started slot's
Chorus part meets every condition Chorus's timed claims take from their
caller: Δ-synchronized participation (Definition 5
(`def:delta-synchronized-participation`)), no abandonment before finalizing
(C1) and no start before `D − Δ` (C2). The first is the Conductor's
`d_tot`-Totality (Lemma 15 (`lemma:conductor-totality`)) read through the
glue's `on_open`, as the paper's proof says; C1 and C2 are the glue's
invariants with the Conductor's integrity. -/
theorem corollary4_conditions (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r)
    (hstart : StartTimes sch thO) (hunb : StartsUnbounded thO) (hΔ : TA.Δ = sch.Δ)
    {x : ℕ} (ps : (PS x).Projection ((LS x) r).toLRun) :
    (CWT).SyncParticipation (partRun ps) ∧
    (∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true → ∀ k,
      (SCI).abandoned ((partRun ps).at' k) i → ∃ V, (SCI).finalized ((partRun ps).at' k) i V) ∧
    (∀ k i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true →
      (SCI).participating ((partRun ps).at' k) i →
      (CWT).deadline ((SCI).tag ((partRun ps).at' k)) ≤ (partRun ps).clk k + (CWT).Δ) := by
  obtain ⟨rows, ⟨po, hpo⟩, hslot⟩ := hs
  have hsync := openings_sync n f hf is_byz hbyz sch TA hprop hrot rows hslot po hpo hunb hΔ
  exact ⟨((CWT).syncParticipation_def _).2 (sync_slot n f hf is_byz hbyz sch rows po (hsync x) ps),
    c1_slot n f hf is_byz hbyz ps, c2_slot n f hf is_byz hbyz sch TA hstart po hpo ps⟩

include hprop hrot in
/-- **Corollary 4 (`cor:chorus-correctness-within-cadence`)**: within
Cadence, every slot's Chorus part meets every caller condition of Chorus's
timed contract (`Corollary4Claim`). -/
theorem corollary4 :
    Corollary4Claim n f hf is_byz hbyz (A := A) (is_proposer := is_proposer) (well_encoded := well_encoded)
      (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader)
      (Phase := Phase) (PathChoice := PathChoice) sch TA thO hprop hrot :=
  fun hstart hunb hΔ _ _ hs _ ps =>
    corollary4_conditions n f hf is_byz hbyz sch TA hprop hrot hs hstart hunb hΔ ps

include hprop hrot in
/-- **Corollary 4: `ℓ`-Termination of every slot, within Cadence** — Chorus's
`bounded_termination` (Lemma 11 (`lemma:chorus-termination`), `ℓ = 5Δ +
ℓ_MVBA` at `δ = 0`) on every started slot's part of an admissible composed
run, with no caller premise left. -/
theorem corollary4_bounded_termination (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r)
    (hstart : StartTimes sch thO) (hunb : StartsUnbounded thO) (hΔ : TA.Δ = sch.Δ)
    {x : ℕ} (ps : (PS x).Projection ((LS x) r).toLRun) (hps : (CT).Admissible (partRun ps)) :
    ∀ t, (∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true →
        (partRun ps).byTime t (fun st => (SCI).participating st i)) →
      ∀ j, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz j = true →
        (partRun ps).byGstBound t (CWT).ℓ (fun st => ∃ V, (SCI).finalized st j V) := by
  obtain ⟨h1, h2, h3⟩ := corollary4_conditions n f hf is_byz hbyz sch TA hprop hrot hs hstart hunb hΔ ps
  exact (CWT).bounded_termination (partRun ps) hps h1 h2 h3

include hprop hrot in
/-- **Corollary 4: `d_tot`-Totality of every slot, within Cadence** —
Chorus's `totality` (Proposition 4 (`prop:chorus-totality`), `d_tot = Δ` at
`δ = 0`) on every started slot's part of an admissible composed run, with
no caller premise left. -/
theorem corollary4_totality (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r)
    (hunb : StartsUnbounded thO) (hΔ : TA.Δ = sch.Δ)
    {x : ℕ} (ps : (PS x).Projection ((LS x) r).toLRun) (hps : (CT).Admissible (partRun ps)) :
    ∀ k i V, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true →
      (SCI).finalized ((partRun ps).at' k) i V →
      ∀ j, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz j = true →
        (partRun ps).byGstBound ((partRun ps).clk k) (CWT).d_tot
          (fun st => ∃ V', (SCI).finalized st j V') := by
  obtain ⟨rows, ⟨po, hpo⟩, hslot⟩ := hs
  have hsync := openings_sync n f hf is_byz hbyz sch TA hprop hrot rows hslot po hpo hunb hΔ
  exact (CWT).totality (partRun ps) hps
    (((CWT).syncParticipation_def _).2 (sync_slot n f hf is_byz hbyz sch rows po (hsync x) ps))
    (c1_slot n f hf is_byz hbyz ps)

include hprop hrot in
/-- **Corollary 4: Termination of every slot, within Cadence** — Module 1
(`mod:slotconsensus`)'s Termination (`Chorus.chorusTemporal`'s
`termination`) on every started slot's part of an admissible composed run:
if every correct validator participates, every correct validator finalizes.
Its one caller condition, C1, is discharged. -/
theorem corollary4_termination
    {x : ℕ} (ps : (PS x).Projection ((LS x) r).toLRun) (hps : (CT).Admissible (partRun ps)) :
    (∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true →
        (partRun ps).eventually (fun st => (SCI).participating st i)) →
      ∀ j, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz j = true →
        (partRun ps).eventually (fun st => ∃ V, (SCI).finalized st j V) := fun hpart =>
  (CT).termination (partRun ps) hps hpart (c1_slot n f hf is_byz hbyz ps)

end Main

end Composed

/-! ## The pinned trust base

The standard Lean trio and nothing else: no `sorryAx`. -/

/--
info: 'Composed.clock_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.clock_le

/--
info: 'Composed.caller_totality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.caller_totality

/--
info: 'Composed.caller_termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.caller_termination

/--
info: 'Composed.openings_sync' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.openings_sync

/--
info: 'Composed.corollary4' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.corollary4

/--
info: 'Composed.corollary4_bounded_termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.corollary4_bounded_termination

/--
info: 'Composed.corollary4_totality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.corollary4_totality

/--
info: 'Composed.corollary4_termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.corollary4_termination
