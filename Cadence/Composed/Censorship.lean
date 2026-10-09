import Cadence.Composed.Liveness
import Cadence.Chorus.Inclusion

/-! # Composed.Censorship — censorship resistance within Cadence

[ConductorBounds.md](../../docs/ConductorBounds.md) §9, stage K7 (R31.2).
Definition 3 (`def:censorship-resistance`): for every slot `s` starting at
least `𝓡` after GST and every correct proposer `j` of `s`, every correct
validator appends a vector for `s` that holds `j`'s proposal. The paper's
proof, in Appendix B.3 (`subsection:correctness_cadence`), followed step by
step (`censorship_of`):

* Recovery within Cadence opens `s` at `j` by its starting time
  (`recovery_in`); `j` participates and proposes then (`on_open`,
  `on_propose`, at `δ = 0`). It has not abandoned `s`, since a finalization
  postdates the deadline (`Chorus.committed_post_deadline`);
* its chunk reaches every correct validator by the deadline, which records
  it (`Chorus.within_proposal_recorded_incl`, with (P-incl)), so its
  proposal is on time;
* `𝓡`-Liveness appends a vector for `s` everywhere (`liveness_in`), and
  Chorus's proposal inclusion puts the proposal in it.

At the paper's `𝓡 = 2Wτ` (`censorship`) and at `(W + p − 1)τ`
(`censorship_sharp`, P18). The glue's proposer assignment is Chorus's, by
construction in the claim; the premises beyond Liveness's are (P-incl) on
every started slot (`SlotInclusive`) and a well-encoded root for a correct
proposer to propose. -/

namespace Composed

open Cadence Conductor
open scoped Cadence.Timed

attribute [local instance] natSlotOrder

section Censorship

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

variable (sch : ConductorSchedule view time vfin)
  (TA : ACSTemporal (Fin n) ℕ acsstate time msg (fmF n f hf is_byz hbyz).byz)
  (hprop : ∃ J, is_proposer J = true)
  (hrot : Mvba.LeaderRotation (nset := byzNodeSetFin n f hf is_byz hbyz) vfin sch.mvba.k
    (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader))

/-! ## Censorship resistance, from the proposer's opening and the appends -/

omit [Archimedean time] in
/-- **The core of censorship resistance** (Definition 3
(`def:censorship-resistance`)): if a correct proposer `j` of slot `s` opens
it by its starting time, at or after GST, and every correct validator
appends a vector for `s`, then `j` proposes some `P` and every correct
validator's vector for `s` includes `P` for `j`. The paper's proof, step by
step: `j` participates and proposes at the starting time (`on_open`,
`on_propose`); its chunk reaches every correct validator by the deadline,
which records it (Chorus's `within_proposal_recorded_incl`, with (P-incl)); so the
proposal is on time, and Chorus's proposal inclusion puts it in every
finalized vector, hence in every appended one. -/
theorem censorship_of (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r)
    (hincl : SlotInclusive n f hf is_byz hbyz (A := A) sch r) (hstart : StartTimes sch thO)
    (hwe : ∃ m, well_encoded m = true) {s : ℕ} (hgs : r.gst ≤ thO.start_time s)
    {j : Fin n} (hj : ¬ (fmF n f hf is_byz hbyz).byz j) (hJ : is_proposer j = true)
    (hJg : thG.is_proposer j s = true)
    (hoj : ∃ m, r.clk m ≤ thO.start_time s ∧ (OSI).opened (r.at' m).os j s)
    (hlive : ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i → ∃ m v, (r.at' m).appended i s v = true) :
    ∃ P, (∃ k, (SCI).proposed ((r.at' k).sc_state s) j P) ∧
      ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
        ∃ m v, (r.at' m).appended i s v = true ∧ (SCI).slot_of v = s ∧ (SCI).includes v j P := by
  letI : ByzNodeSet (Fin n) (ByzNSet n) := byzNodeSetFin n f hf is_byz hbyz
  letI : FaultModel (Fin n) := fmF n f hf is_byz hbyz
  letI : MVBASafety (Fin n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)
      (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view))
      (ByzNSet n) (byzNodeSetFin n f hf is_byz hbyz) (fun i => (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true) :=
    Mvba.mvbaSafety (Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader)
  obtain ⟨rows, ⟨po, hpo⟩, hslot⟩ := hs
  obtain ⟨m0, hc0, ho0⟩ := hoj
  obtain ⟨m1, hc1, hp1⟩ := participating_by n f hf is_byz hbyz sch rows hj hc0 ho0
  rw [max_eq_left hgs] at hc1
  have hstarted : ∃ k i, ¬ (fmF n f hf is_byz hbyz).byz i ∧
      (SCI).participating ((r.at' k).sc_state s) i := ⟨m1, j, hj, hp1⟩
  obtain ⟨ps, hps⟩ := hslot s hstarted
  obtain ⟨r', hat, hclk, hgst, -, -, -, hTJ, hPP, -⟩ := hps
  have htag0 : ((partRun ps).at' 0).1 = s := by
    rw [partRun_at']
    exact inv_sc_tagged (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
      (r.reachable _) s
  rw [htag0] at hTJ hPP
  have hDI := hincl s hstarted ps r' hat hclk
  have hΔpos : 0 < sch.Δ := sch.mvba.Δ_pos
  have hD : (sch.toFamilySchedule.at s).D = thO.start_time s + sch.Δ := by
    show sch.D s = _
    rw [sch.D_eq s, hstart s]
    rfl
  -- The slot's part at a composed index: the covering index of the labelling.
  have hcov : ∀ m, r'.at' ((PS s).cover ((LS s) r).toLRun m) = ((r.at' m).sc_state s).2 ∧
      r'.clk ((PS s).cover ((LS s) r).toLRun m) ≤ r.clk m := fun m => by
    refine ⟨by rw [hat, partRun_at'_cover]; rfl, ?_⟩
    rw [hclk, partRun_clk]
    exact ((LS s) r).clk_le_of_le (ps.entry_cover_le m)
  have hpre : ∀ m, r.clk m ≤ thO.start_time s →
      ((r.at' m).sc_state s).2.phase = Chorus.Phase_EnumClass.pre_deadline := fun m hm => by
    rw [← (hcov m).1]
    refine Chorus.phase_pre_of_lt _ hPP _ (lt_of_le_of_lt ((hcov m).2.trans hm) ?_)
    rw [hD]
    exact lt_add_of_pos_right _ hΔpos
  have hnab : ∀ m, r.clk m ≤ thO.start_time s → ¬ ((r.at' m).sc_state s).2.abandoned j = true := by
    intro m hm hab
    obtain ⟨V, hV⟩ := inv_abandoned_finalized (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
      (orch := OSI) (sc := SCI) (r.reachable m) hj hab
    have hreach := r'.reachable ((PS s).cover ((LS s) r).toLRun m)
    rw [(hcov m).1] at hreach
    exact Chorus.committed_post_deadline hreach hj hV.1 hJ (hpre m hm)
  obtain ⟨wm, hwm⟩ := hwe
  -- `on_propose`'s row, from the later of the opening and the participation.
  have hcN : r.clk (max m0 m1) ≤ thO.start_time s := r.clk_max_le' hc0 hc1
  have hB : r.ref (max m0 m1) + sch.δ ≤ thO.start_time s := ref_le_bound n f hf is_byz hbyz sch hcN hgs
  obtain ⟨np, -, hcnp, P, hP⟩ := r.withinFrom_of_bufferedFairFamily
    (GlueRows.propose (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) rows j s hj) le_rfl (bufWindow_self (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) (max m0 m1)) (B := r.ref (max m0 m1) + sch.δ)
    (P := fun st => ∃ p, (SCI).proposed (st.sc_state s) j p)
    (fun l ⟨p, a, hl⟩ st st' htr => by
      subst hl
      obtain ⟨hpr, he⟩ := on_propose_sc (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) htr
      exact ⟨p, by rw [he s, if_pos rfl]; exact (SCI).propose_effect _ _ _ _ hpr⟩)
    (fun m hm hcm hnot => ⟨trivial, fun hg => by
      have hcm' := le_trans hcm hB
      obtain ⟨s2, hs2⟩ := Chorus.propose_exists (thM := Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader)
        (thS := Cadence.chorusTheory (slot := ℕ) (Phase := Phase) (PathChoice := PathChoice) is_proposer
          well_encoded mvba_init_state)
        (nset := byzNodeSetFin n f hf is_byz hbyz) (m := wm) hj hg.2.1 (hnab m hcm') hJ hwm (hpre m hcm')
        (fun m2 h2 => absurd ⟨m2, h2⟩ hg.2.2.2)
      exact ⟨_, ⟨wm, (((r.at' m).sc_state s).1, s2), rfl⟩,
        enabled_on_propose (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
          hj hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 ⟨rfl, hs2⟩⟩⟩)
    (fun m hm _ hnot => ⟨run_opened_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
        (sc := SCI) ho0 m (le_trans (le_max_left _ _) hm),
      run_participating_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
        hp1 m (le_trans (le_max_right _ _) hm), hJg, hnot⟩)
  have hcnp' := le_trans hcnp hB
  -- The proposal is well-encoded: it is `j`'s own `propose` input.
  have hweP : well_encoded P = true :=
    run_proposed_of (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
      (W := fun p => well_encoded p = true) (fun _ _ _ _ h => Chorus.propose_well_encoded h.2) hj s np P hP
  -- Every correct validator records it, on the slot's labelled run.
  set cp := (PS s).cover ((LS s) r).toLRun np with hcpdef
  have hsig : (r'.at' cp).msg_proposer_signed j P = true := by rw [(hcov np).1]; exact hP
  have hX : max (thO.start_time s) r'.gst + (sch.toFamilySchedule.at s).Δ ≤
      (sch.toFamilySchedule.at s).D := by
    rw [hgst, show (partRun ps).gst = r.gst from rfl, max_eq_left hgs, hD]
    exact le_rfl
  have hrec := fun i (hi : ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true) =>
    Chorus.within_proposal_recorded_incl (sch.toFamilySchedule.at s) hDI hj hJ ((hcov np).2.trans hcnp') hsig hX hi
  obtain ⟨K, -, hK⟩ := r'.toLRun.eventually_forall
    (P := fun i st => ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true → st.local_entry_pos i j P = true)
    (fun a k h hi => Chorus.local_entry_pos.mono (r'.steps k) a j P (h hi)) 0 (List.finRange n)
    (fun a _ => by
      by_cases ha : (byzNodeSetFin n f hf is_byz hbyz).is_byz a = true
      · exact ⟨0, le_rfl, fun h => absurd ha h⟩
      · obtain ⟨k, -, hk⟩ := hrec a ha
        exact ⟨k, Nat.zero_le _, fun _ => hk⟩)
  have hon : (SCI).on_time ((r.at' (ps.entry K)).sc_state s) j P := by
    have h2 : ((r.at' (ps.entry K)).sc_state s).2 = r'.at' K := by rw [hat, partRun_at']; rfl
    have key : ∀ i, ¬ (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true →
        ((r.at' (ps.entry K)).sc_state s).2.local_entry_pos i j P = true := by
      rw [h2]; exact fun i hi => hK i (List.mem_finRange i) hi
    exact ⟨hj, hJ, key, hweP⟩
  refine ⟨P, ⟨np, hP⟩, fun i hi => ?_⟩
  obtain ⟨ma, v, ha⟩ := hlive i hi
  have hd : (r.at' ma).delivered i s v = true := Cadence.reachable_appended_delivered
    (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI) (r.reachable ma) i s v ⟨hi, ha⟩
  have hfin := inv_delivered_finalized (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) (r.reachable ma) hi hd
  have hfinM := run_finalized_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) hfin _ (le_max_left ma (ps.entry K))
  have honM := run_on_time_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) hon _ (le_max_right ma (ps.entry K))
  exact ⟨ma, v, ha, inv_appended_slot (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) (r.reachable ma) hi ha,
    (SCI).proposal_inclusion _ (inv_sc_reachable (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
      (orch := OSI) (sc := SCI) (r.reachable _) s) i j v P hi hfinM honM⟩

include hprop hrot in
/-- **`𝓡`-Censorship resistance of the composed system at the paper's
`𝓡 = 2Wτ`** (Definition 3 (`def:censorship-resistance`), with Theorem 2
(`thm:conductor-correctness`)'s `𝓡`): Recovery within Cadence opens the
slot at the proposer by its starting time (`recovery_in`), `𝓡`-Liveness
appends a vector for it everywhere (`liveness_in`), and
`censorship_of` puts the proposal in each. -/
theorem censorship :
    CensorshipClaim n f hf is_byz hbyz (A := A) (is_proposer := is_proposer) (well_encoded := well_encoded)
      (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader)
      (Phase := Phase) (PathChoice := PathChoice) sch TA thO sch.recoveryTime :=
  fun hstart hshift hunb hwin hΔ hℓ hwe _ _ r hs hincl s hs' j hj hJ => by
    have hgs : r.gst ≤ thO.start_time s :=
      le_trans (le_add_of_nonneg_right (nsmul_nonneg sch.τ_pos.le _)) hs'
    obtain ⟨m, hm, ho⟩ := recovery_in n f hf is_byz hbyz sch TA hprop hrot hs hstart hshift hunb hwin hΔ hℓ
      s hs' j hj
    exact censorship_of n f hf is_byz hbyz sch TA hs hincl hstart hwe hgs hj hJ hJ ⟨m, hm, ho⟩
      (fun i hi => by
        obtain ⟨m, v, ha, -⟩ := liveness_in n f hf is_byz hbyz sch TA hprop hrot hs hstart hshift hunb hwin
          hΔ hℓ s hs' i hi
        exact ⟨m, v, ha⟩)

include hprop hrot in
/-- **Censorship resistance at the sharper `(W + p − 1)τ`** (P18): the
same, from `recovery_sharp_in` and `liveness_sharp_in`. -/
theorem censorship_sharp :
    CensorshipClaim n f hf is_byz hbyz (A := A) (is_proposer := is_proposer) (well_encoded := well_encoded)
      (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader)
      (Phase := Phase) (PathChoice := PathChoice) sch TA thO ((sch.W + (sch.p - 1)) • sch.τ) :=
  fun hstart hshift hunb hwin hΔ hℓ hwe _ _ r hs hincl s hs' j hj hJ => by
    have hgs : r.gst ≤ thO.start_time s :=
      le_trans (le_add_of_nonneg_right (nsmul_nonneg sch.τ_pos.le _)) hs'
    obtain ⟨m, hm, ho⟩ := recovery_sharp_in n f hf is_byz hbyz sch TA hprop hrot hs hstart hshift hunb hwin
      hΔ hℓ s hs' j hj
    exact censorship_of n f hf is_byz hbyz sch TA hs hincl hstart hwe hgs hj hJ hJ ⟨m, hm, ho⟩
      (fun i hi => by
        obtain ⟨m, v, ha, -⟩ := liveness_sharp_in n f hf is_byz hbyz sch TA hprop hrot hs hstart hshift
          hunb hwin hΔ hℓ s hs' i hi
        exact ⟨m, v, ha⟩)

end Censorship

end Composed

/-! ## The pinned trust base

The standard Lean trio and nothing else: no `sorryAx`. -/

/--
info: 'Composed.censorship_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.censorship_of

/--
info: 'Composed.censorship' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.censorship

/--
info: 'Composed.censorship_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.censorship_sharp
