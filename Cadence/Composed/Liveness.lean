import Cadence.Composed.Corollary4

/-! # Composed.Liveness — Recovery within Cadence, and `𝓡`-Liveness

[ConductorBounds.md](../../docs/ConductorBounds.md) §9, stage K7.

* **Recovery within Cadence** (`recovery_in`, Lemma 16
  (`lemma:conductor-recovery`)): the Conductor's `Conductor.recovery` on the
  orchestrator's part of the composed run, with (R-tot) and (R-term)
  discharged ([Corollary4.lean](Corollary4.lean)), at the paper's
  `𝓡 = 2Wτ`; `recovery_sharp_in` at `(W + p − 1)τ` (P18).
* **`𝓡`-Liveness** (`liveness`, Definition 2 (`def:liveness`), Lemma 2
  (`lemma:cadence-liveness`)): every slot starting at least `𝓡` after GST
  ends up in every correct validator's local log. The paper's proof,
  followed step by step (`liveness_of_opens`): Recovery opens the slot
  everywhere; every slot below it is opened by every correct validator or
  by none (Totality within Cadence, `openings_sync`); in the first case
  each participates, Chorus terminates on the slot's part (Corollary 4),
  and each delivers and appends (`appended_of_all_open`); in the second
  each records the slot as skipped. By induction over the slots below, the
  slot's `ready_to_append` holds, and the vector is appended.
  `liveness_sharp` is the same at `(W + p − 1)τ`.

Censorship resistance (Definition 3 (`def:censorship-resistance`)) is not
here: its timed premise meets the deadline tie of
[Bounds.md](../../docs/Bounds.md) §6.4.2 ("What `s.deadline − Δ ≥ GST`
becomes"), recorded as F31 in
[ConductorBounds.md](../../docs/ConductorBounds.md) §7. -/

namespace Composed

open Cadence Conductor
open scoped Cadence.Timed

attribute [local instance] natSlotOrder

section Liveness

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

/-! ## Recovery, within Cadence -/

include hprop hrot in
/-- **Lemma 16 (`lemma:conductor-recovery`), within Cadence, at `𝓡 = 2Wτ`**:
in an admissible composed run, every slot whose starting time is at least
`GST + 2Wτ` is opened by every correct validator by its starting time. The
Conductor's `Conductor.recovery` on its part of the run, with its two
caller conditions, (R-tot) and (R-term), discharged by Chorus through the
glue (`caller_totality`, `caller_termination`). -/
theorem recovery_in (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r)
    (hstart : StartTimes sch thO) (hshift : WindowShifts sch thO) (hunb : StartsUnbounded thO)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter (fmF n f hf is_byz hbyz).byz).card ≤ TA.fault_bound) :
    ∀ x, r.gst + sch.recoveryTime ≤ thO.start_time x →
      ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
        ∃ m, r.clk m ≤ thO.start_time x ∧ (OSI).opened (r.at' m).os i x := by
  obtain ⟨rows, ⟨po, hpo⟩, hslot⟩ := hs
  have hcall := caller_totality n f hf is_byz hbyz sch hprop hrot rows hslot po
  have hterm := caller_termination n f hf is_byz hbyz sch TA hprop hrot rows hslot po hpo hstart
  obtain ⟨r', hr', hsync⟩ := hpo
  have hg : r'.gst = r.gst := congrArg TimedRun.gst hr'
  intro x hx i hi
  have := Conductor.recovery (fm := fmF n f hf is_byz hbyz) sch TA thO hstart hshift hunb hwin hΔ hℓ hfault
    r' hsync (by rw [hr']; exact hcall) (by rw [hr']; exact hterm) x (by rw [hg]; exact hx) i hi
  rw [hr'] at this
  exact (partRun_byTime_iff po _ _).1 this

include hprop hrot in
/-- **Recovery within Cadence at the sharper `(W + p − 1)τ`** (P18): the
same, from `Conductor.recovery_sharp`. -/
theorem recovery_sharp_in (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r)
    (hstart : StartTimes sch thO) (hshift : WindowShifts sch thO) (hunb : StartsUnbounded thO)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter (fmF n f hf is_byz hbyz).byz).card ≤ TA.fault_bound) :
    ∀ x, r.gst + (sch.W + (sch.p - 1)) • sch.τ ≤ thO.start_time x →
      ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
        ∃ m, r.clk m ≤ thO.start_time x ∧ (OSI).opened (r.at' m).os i x := by
  obtain ⟨rows, ⟨po, hpo⟩, hslot⟩ := hs
  have hcall := caller_totality n f hf is_byz hbyz sch hprop hrot rows hslot po
  have hterm := caller_termination n f hf is_byz hbyz sch TA hprop hrot rows hslot po hpo hstart
  obtain ⟨r', hr', hsync⟩ := hpo
  have hg : r'.gst = r.gst := congrArg TimedRun.gst hr'
  intro x hx i hi
  have := Conductor.recovery_sharp (fm := fmF n f hf is_byz hbyz) sch TA thO hstart hshift hunb hwin hΔ hℓ
    hfault r' hsync (by rw [hr']; exact hcall) (by rw [hr']; exact hterm) x (by rw [hg]; exact hx) i hi
  rw [hr'] at this
  exact (partRun_byTime_iff po _ _).1 this

/-! ## `𝓡`-Liveness, within Cadence -/

include hprop hrot in
/-- **A slot every correct validator opens is appended**, once every slot
below it is resolved at every correct validator: each participates
(`on_open`), Chorus terminates on the slot's part (Corollary 4), each
delivers the finalization (`on_finalize`), and appends it (`append`). The
case (1) of the paper's proof of Lemma 2 (`lemma:cadence-liveness`). -/
theorem appended_of_all_open (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r) {y : ℕ}
    (hall : ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i → ∃ m, (OSI).opened (r.at' m).os i y)
    (hbelow : ∀ y' < y, ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i → ∃ m, (r.at' m).resolved i y' = true) :
    ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i → ∃ m v, (r.at' m).appended i y v = true := by
  obtain ⟨rows, -, hslot⟩ := hs
  have hpart : ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
      ∃ m, (SCI).participating ((r.at' m).sc_state y) i := fun i hi => by
    obtain ⟨m, hm⟩ := hall i hi
    obtain ⟨m', -, -, hp⟩ := within_participating (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
      (orch := OSI) (sc := SCI) rows (sc_participate_exists n f hf is_byz hbyz) hi hm
    exact ⟨m', hp⟩
  intro i hi
  obtain ⟨m0, hp0⟩ := hpart i hi
  obtain ⟨ps, hps⟩ := hslot y ⟨m0, i, hi, hp0⟩
  have hfin := corollary4_termination n f hf is_byz hbyz sch hprop hrot ps hps
    (fun j hj => (partRun_eventually_iff ps _).2 (hpart j hj)) i hi
  obtain ⟨m1, V, hV⟩ := (partRun_eventually_iff ps _).1 hfin
  obtain ⟨m2, ho2⟩ := hall i hi
  obtain ⟨m3, -, -, v, hd⟩ := within_delivered (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
    (orch := OSI) (sc := SCI) rows
    (fun o i x _ hi ho hnc => orch_complete_exists (fm := fmF n f hf is_byz hbyz) (A := A) o i x hi ho hnc)
    (sc_abandon_exists n f hf is_byz hbyz) hi
    (run_opened_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
      ho2 _ (le_max_right m1 m2))
    (run_finalized_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
      hV _ (le_max_left m1 m2))
  obtain ⟨m4, -, hres⟩ := r.toLRun.eventually_forall (P := fun y' st => st.resolved i y' = true)
    (fun a k h => run_resolved_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
      (sc := SCI) h (k + 1) (Nat.le_succ k)) 0 (List.range y)
    (fun a ha => by
      obtain ⟨m, hm⟩ := hbelow a (List.mem_range.1 ha) i hi
      exact ⟨m, Nat.zero_le _, hm⟩)
  obtain ⟨m5, -, -, w, hw⟩ := within_appended (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
    (orch := OSI) (sc := SCI) rows hi
    (run_delivered_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI) (sc := SCI)
      hd _ (le_max_left m3 m4))
    (fun y' hle hne => run_resolved_mono (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
      (sc := SCI) (hres y' (List.mem_range.2 (lt_of_le_of_ne hle hne))) _ (le_max_right m3 m4))
  exact ⟨m5, w, hw⟩

include hprop hrot in
/-- **Liveness from the openings**: if every correct validator opens slot
`s`, every correct validator appends a proposal vector for `s`. The paper's
proof of Lemma 2 (`lemma:cadence-liveness`), by induction over the slots
below `s`: each is opened by every correct validator or by none (the
Conductor's Totality, within Cadence, `openings_sync`), and is then appended
(`appended_of_all_open`) or skipped (`record_skip`'s row, with `s` opened
above it). -/
theorem liveness_of_opens (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r)
    (hunb : StartsUnbounded thO) (hΔ : TA.Δ = sch.Δ) {s : ℕ}
    (hopen : ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i → ∃ m, (OSI).opened (r.at' m).os i s) :
    ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i → ∃ m v, (r.at' m).appended i s v = true := by
  have hs' := hs
  obtain ⟨rows, ⟨po, hpo⟩, hslot⟩ := hs'
  have hsync := openings_sync n f hf is_byz hbyz sch TA hprop hrot rows hslot po hpo hunb hΔ
  have key : ∀ y, y ≤ s → ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
      ∃ m, (r.at' m).resolved i y = true := by
    intro y
    induction y using Nat.strong_induction_on with
    | _ y ih =>
      intro hy i hi
      by_cases hex : ∃ m j, ¬ (fmF n f hf is_byz hbyz).byz j ∧ (OSI).opened (r.at' m).os j y
      · obtain ⟨m, j, hj, ho⟩ := hex
        have hall : ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i → ∃ m, (OSI).opened (r.at' m).os i y :=
          fun i hi => by
            obtain ⟨m', -, ho'⟩ := openSync_composed n f hf is_byz hbyz po (hsync y) hj ho hi
            exact ⟨m', ho'⟩
        obtain ⟨m', v, ha⟩ := appended_of_all_open n f hf is_byz hbyz sch TA hprop hrot hs hall
          (fun y' hy' i hi => ih y' hy' (le_trans hy'.le hy) i hi) i hi
        exact ⟨m', inv_appended_resolved (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
          (sc := SCI) (r.reachable m') hi ha⟩
      · push Not at hex
        obtain ⟨m, hm⟩ := hopen i hi
        have hys : y ≠ s := fun h => hex m i hi (h ▸ hm)
        obtain ⟨m', -, -, hsk⟩ := within_skipped (slot_ord := GI) (fm := fmF n f hf is_byz hbyz)
          (orch := OSI) (sc := SCI) rows hi hm hy hys (fun m'' _ => hex m'' i hi)
        exact ⟨m', inv_skipped_resolved (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
          (sc := SCI) (r.reachable m') hi hsk⟩
  exact appended_of_all_open n f hf is_byz hbyz sch TA hprop hrot hs hopen
    (fun y' hy' i hi => key y' hy'.le i hi)

include hprop hrot in
/-- **`𝓡`-Liveness of the composed system at `𝓡 = 2Wτ`** (Definition 2
(`def:liveness`); Lemma 2 (`lemma:cadence-liveness`) with Theorem 2
(`thm:conductor-correctness`)'s `𝓡`): in every admissible composed run, for
every slot `s` with `s.deadline − Δ ≥ GST + 2Wτ`, every correct validator
appends a proposal vector for `s` to its local log. Recovery within Cadence
(`recovery_in`) opens `s` everywhere; `liveness_of_opens` does the rest. -/
theorem liveness_in (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r)
    (hstart : StartTimes sch thO) (hshift : WindowShifts sch thO) (hunb : StartsUnbounded thO)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter (fmF n f hf is_byz hbyz).byz).card ≤ TA.fault_bound) :
    ∀ s, r.gst + sch.recoveryTime ≤ thO.start_time s →
      ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
        ∃ m v, (r.at' m).appended i s v = true ∧ (SCI).slot_of v = s := by
  intro s hs' i hi
  obtain ⟨m, v, ha⟩ := liveness_of_opens n f hf is_byz hbyz sch TA hprop hrot hs hunb hΔ (fun i hi => by
    obtain ⟨m, -, hm⟩ := recovery_in n f hf is_byz hbyz sch TA hprop hrot hs hstart hshift hunb hwin hΔ hℓ
      hfault s hs' i hi
    exact ⟨m, hm⟩) i hi
  exact ⟨m, v, ha, inv_appended_slot (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) (r.reachable m) hi ha⟩

include hprop hrot in
/-- **`𝓡`-Liveness at the sharper `𝓡 = (W + p − 1)τ`** (P18): the same, from
`recovery_sharp_in`. -/
theorem liveness_sharp_in (hs : SysSync n f hf is_byz hbyz (A := A) sch TA r)
    (hstart : StartTimes sch thO) (hshift : WindowShifts sch thO) (hunb : StartsUnbounded thO)
    (hwin : WindowsUnbounded window) (hΔ : TA.Δ = sch.Δ) (hℓ : TA.ℓ = sch.ℓ)
    (hfault : (Finset.univ.filter (fmF n f hf is_byz hbyz).byz).card ≤ TA.fault_bound) :
    ∀ s, r.gst + (sch.W + (sch.p - 1)) • sch.τ ≤ thO.start_time s →
      ∀ i, ¬ (fmF n f hf is_byz hbyz).byz i →
        ∃ m v, (r.at' m).appended i s v = true ∧ (SCI).slot_of v = s := by
  intro s hs' i hi
  obtain ⟨m, v, ha⟩ := liveness_of_opens n f hf is_byz hbyz sch TA hprop hrot hs hunb hΔ (fun i hi => by
    obtain ⟨m, -, hm⟩ := recovery_sharp_in n f hf is_byz hbyz sch TA hprop hrot hs hstart hshift hunb hwin
      hΔ hℓ hfault s hs' i hi
    exact ⟨m, hm⟩) i hi
  exact ⟨m, v, ha, inv_appended_slot (slot_ord := GI) (fm := fmF n f hf is_byz hbyz) (orch := OSI)
    (sc := SCI) (r.reachable m) hi ha⟩

include hprop hrot in
/-- **`𝓡`-Liveness of the composed system at the paper's `𝓡 = 2Wτ`**
(Definition 2 (`def:liveness`); Lemma 2 (`lemma:cadence-liveness`), with
Theorem 2 (`thm:conductor-correctness`)'s `𝓡`). -/
theorem liveness :
    LivenessClaim n f hf is_byz hbyz (A := A) (is_proposer := is_proposer) (well_encoded := well_encoded)
      (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader)
      (Phase := Phase) (PathChoice := PathChoice) sch TA thO sch.recoveryTime :=
  fun hstart hshift hunb hwin hΔ hℓ hfault _ _ hs =>
    liveness_in n f hf is_byz hbyz sch TA hprop hrot hs hstart hshift hunb hwin hΔ hℓ hfault

include hprop hrot in
/-- **`𝓡`-Liveness at the sharper `𝓡 = (W + p − 1)τ`** (P18). -/
theorem liveness_sharp :
    LivenessClaim n f hf is_byz hbyz (A := A) (is_proposer := is_proposer) (well_encoded := well_encoded)
      (mvba_init_state := mvba_init_state) (mvalid := mvalid) (mleader := mleader)
      (Phase := Phase) (PathChoice := PathChoice) sch TA thO ((sch.W + (sch.p - 1)) • sch.τ) :=
  fun hstart hshift hunb hwin hΔ hℓ hfault _ _ hs =>
    liveness_sharp_in n f hf is_byz hbyz sch TA hprop hrot hs hstart hshift hunb hwin hΔ hℓ hfault

end Liveness

end Composed

/-! ## The pinned trust base

The standard Lean trio and nothing else: no `sorryAx`. -/

/--
info: 'Composed.recovery_in' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.recovery_in

/--
info: 'Composed.recovery_sharp_in' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.recovery_sharp_in

/--
info: 'Composed.liveness_of_opens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.liveness_of_opens

/--
info: 'Composed.liveness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.liveness

/--
info: 'Composed.liveness_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.liveness_sharp
