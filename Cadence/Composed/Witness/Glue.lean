import Cadence.Composed.Witness.Steps

/-! # Composed.Witness.Glue — the glue's rows on the composed witness

[ConductorBounds.md](../../../docs/ConductorBounds.md) §8.2, stage K8.
`GlueRows` ([Composed/Schedule.lean](../Schedule.lean)) on the run of
[Steps.lean](Steps.lean). Every handler of the glue fires in the plateau
its gate opens in: at the last index of every plateau, every correct
validator participates in, has proposed in, has delivered the finalization
of, and has appended every slot whose gate is open, and nothing is
skippable, since every slot below an opened one is opened too. So each row
holds with its gate closed at that index (`bufferedFairFamily_of_ends`). -/

namespace Composed.Witness

open Cadence Conductor Chorus
open scoped Cadence.Timed

attribute [local instance] Chorus.Witness.nsetC Chorus.Witness.cntC natViewOrder FM AS OSI SCI

/-- The slots' contract instance, at the fault model's own `byz`. -/
noncomputable local instance scInst : SlotConsensusSafety ℕ (Fin 4) Unit (ℕ × (Fin 4 → Option Unit))
    (SlotSt Unit ℕ Ph PC 4) (@FaultModel.byz (Fin 4) FM) := SCI

/-- The last index of plateau `t`, the one the clock moves after. -/
abbrev pEnd (N : ℕ) : ℕ := N / 56 * 56 + 55

theorem pEnd_ge (N : ℕ) : N ≤ pEnd N := by have := idx_eq N; have := pos_lt N; simp only [pEnd]; omega

theorem pEnd_clk (N : ℕ) : run.clk (pEnd N) = run.clk N := by
  simp only [run_clk, pEnd]; omega

theorem glue_open (t : ℕ) (i : Fin 4) (x : ℕ) :
    ¬ openGate (orch := OSI) (sc := SCI) i x (gs (t * 56 + 55)) := by
  rintro ⟨ho, hp⟩
  have := i.isLt
  change decide _ = true at ho
  change ¬ (cst (loc x _)).participating i = true at hp
  simp only [decide_eq_true_eq] at ho
  simp only [cst, decide_eq_true_eq, loc] at hp
  omega

theorem glue_propose (t : ℕ) (i : Fin 4) (x : ℕ) :
    ¬ proposeGate (orch := OSI) (sc := SCI) (ℕ × (Fin 4 → Option Unit)) thG i x (gs (t * 56 + 55)) := by
  rintro ⟨ho, -, hpr, hnp⟩
  have := i.isLt
  change decide _ = true at ho
  change decide _ = true at hpr
  simp only [decide_eq_true_eq] at ho hpr
  refine hnp ⟨(), ?_⟩
  change (cst (loc x _)).msg_proposer_signed i () = true
  simp only [cst, decide_eq_true_eq, loc]
  omega

theorem glue_finalize (t : ℕ) (i : Fin 4) (x : ℕ) (hi : i.val < 3) :
    ¬ finalizeGate (orch := OSI) (sc := SCI) i x (gs (t * 56 + 55)) := by
  rintro ⟨ho, ⟨v, hf, -⟩, hnd⟩
  change decide _ = true at ho
  change (cst (loc x _)).local_committed i = true at hf
  have hd := hnd (vec x)
  change decide _ = false at hd
  simp only [decide_eq_true_eq] at ho
  simp only [cst, decide_eq_true_eq, loc] at hf
  simp only [decide_eq_false_iff_not, and_true] at hd
  omega

theorem glue_skip (t : ℕ) (i : Fin 4) (x : ℕ) :
    ¬ skipGate (slot_ord := TotalOrderWithMinimum.toTotalOrder) (orch := OSI) i x
      (gs (t * 56 + 55)) := by
  rintro ⟨⟨w, hw, hle, hne⟩, hno, -⟩
  have hle : x ≤ w := hle
  change decide _ = true at hw
  change ¬ decide _ = true at hno
  simp only [decide_eq_true_eq] at hw hno
  omega

theorem glue_append (t : ℕ) (i : Fin 4) (x : ℕ) :
    ¬ appendGate (slot_ord := TotalOrderWithMinimum.toTotalOrder) i x
      (gs (t * 56 + 55)) := by
  rintro ⟨⟨v, hd⟩, hna, -⟩
  have ha := hna v
  change decide _ = true at hd
  change decide _ = false at ha
  simp only [decide_eq_true_eq] at hd
  obtain ⟨h1, h2, rfl⟩ := hd
  simp only [decide_eq_false_iff_not, and_true] at ha
  omega

theorem row_propose (i : Fin 4) (x : ℕ) :
    BufferedFairFamily run sch.δ sch.δ (fun _ => True)
      (proposeGate (slot_ord := TotalOrderWithMinimum.toTotalOrder) (orch := OSI) (sc := SCI)
        (ℕ × (Fin 4 → Option Unit)) thG i x)
      (fun l => ∃ p a, l = .on_propose i x p a) :=
  bufferedFairFamily_of_ends (Nat.zero_le _) fun N =>
    ⟨pEnd N, pEnd_ge N, pEnd_clk N, fun ⟨_, hg, _⟩ => glue_propose (N / 56) i x hg⟩

theorem row_open (i : Fin 4) (x : ℕ) :
    BufferedFairFamily run sch.δ sch.δ (fun _ => True) (openGate (orch := OSI) (sc := SCI) i x)
      (fun l => ∃ a, l = .on_open i x a) :=
  bufferedFairFamily_of_ends (Nat.zero_le _) fun N =>
    ⟨pEnd N, pEnd_ge N, pEnd_clk N, fun ⟨_, hg, _⟩ => glue_open (N / 56) i x hg⟩

theorem row_finalize (i : Fin 4) (x : ℕ) (hi : i.val < 3) :
    BufferedFairFamily run sch.δ sch.δ (fun _ => True) (finalizeGate (orch := OSI) (sc := SCI) i x)
      (fun l => ∃ v a b, l = .on_finalize i x v a b) :=
  bufferedFairFamily_of_ends (Nat.zero_le _) fun N =>
    ⟨pEnd N, pEnd_ge N, pEnd_clk N, fun ⟨_, hg, _⟩ => glue_finalize (N / 56) i x hi hg⟩

theorem row_skip (i : Fin 4) (x : ℕ) :
    BufferedFairFamily run sch.δ sch.δ (fun _ => True)
      (skipGate (slot_ord := TotalOrderWithMinimum.toTotalOrder) (orch := OSI) i x)
      (fun l => ∃ w, l = .record_skip i x w) :=
  bufferedFairFamily_of_ends (Nat.zero_le _) fun N =>
    ⟨pEnd N, pEnd_ge N, pEnd_clk N, fun ⟨_, hg, _⟩ => glue_skip (N / 56) i x hg⟩

theorem row_append (i : Fin 4) (x : ℕ) :
    BufferedFairFamily run sch.δ sch.δ (fun _ => True)
      (appendGate (slot_ord := TotalOrderWithMinimum.toTotalOrder) i x)
      (fun l => ∃ v, l = .append i x v) :=
  bufferedFairFamily_of_ends (Nat.zero_le _) fun N =>
    ⟨pEnd N, pEnd_ge N, pEnd_clk N, fun ⟨_, hg, _⟩ => glue_append (N / 56) i x hg⟩

/-- **The glue's rows**: each fires within `δ = 0` of its gate, because
every gate is closed at the end of every plateau. -/
theorem glueRows :
    GlueRows (slot_ord := TotalOrderWithMinimum.toTotalOrder) (fm := FM) (orch := OSI) (sc := SCI)
      thG sch.δ run :=
  ⟨fun i x _ => row_open i x, fun i x _ => row_propose i x,
    fun i x hi => row_finalize i x ((correct_iff i).1 hi), fun i x _ => row_skip i x,
    fun i x _ => row_append i x⟩

end Composed.Witness

/-! ## The pinned trust base -/

/--
info: 'Composed.Witness.glueRows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Composed.Witness.glueRows
