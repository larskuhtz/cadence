import Cadence.Chorus.Schedule

/-! # Chorus/Totality — `d_tot`-totality, proven

[Bounds.md](../../docs/Bounds.md) §6.4.4, stage S3. The first of the two
timed claims of [Schedule.lean](Schedule.lean), proven in the
tolerance-parametric form R7 stated (F3):

**`Chorus.totality`** — `TotalityClaim sch d`, at every schedule and every
participation tolerance `d`: under (Δδ-justice), participation synchronized
within `d`, and no abandonment before finalizing (C1), if a correct
validator finalizes at an index whose clock reads `c`, every correct
validator finalizes by `max(c, GST) + max(Δ, d) + 2δ` (`Ltot`).

**`Chorus.totality_paper`** — the paper's Proposition 4 (`prop:chorus-totality`) read off
it: at `δ = 0` and the paper's tolerance `d = Δ`, every correct validator
finalizes by `max(c, GST) + Δ`, which is `d_tot = Δ`. The `δ > 0`
degradation stays parametric; what the Conductor makes of it is that leg's
question (F3, C3).

## The route, which is the paper's

The finalizer's commitment proof is on the network from its finalization on
(`proofs_of_finalized`: it committed an entry for every proposer, and its
finalization re-broadcast the proof). For another correct validator `j`:

* **the gate.** The finalizer participated at or before its finalization
  (`committed_participating`), so `j` participates by `max(c, GST) + d`
  (synchronized participation). If `j` abandons, it has already finalized
  (C1). So whenever `j` has not finalized, its gate `Active j` is open from
  that index on;
* **the assignments**, one per proposer, in parallel: `commit_assign_*` is a
  `Δ`-row whose message part — the proof — holds from the finalization, and
  whose gate opens by `max(c, GST) + d`. (Δδ-justice) fires it by
  `max(max(c, GST) + Δ, max(c, GST) + d + δ) ≤ max(c, GST) + max(Δ, d) + δ`;
* **the finalization**, a `δ`-row with the same gate: a further `δ`.

The proof never needs `δ ≤ Δ`, the phase timers, the MVBA or the bridge,
which is why `TotalityClaim` does not take them. Payload recovery
(Algorithm 6, line 14 (`line:da-recover-slot`)), half of the paper's proof, has no counterpart: the
model's `finalized` is the committed entry vector ([Bounds.md](../../docs/Bounds.md) §6.4.4).

## How it is built

Each link is one (Δδ-justice) clause through `TLRun.withinFrom_of_bufferedFair`
below, the buffered twin of `Mvba`'s `withinFrom_of_boundedFair`: if every
firing establishes the goal, and wherever the goal does not yet hold inside
the window the step is owed, enabled when its gate is open, and its gate is
open from the second index on, then the goal holds within the window. The
assignments are collapsed into one index by `TLRun.withinFrom_forall` over a
finite validator set (`[Fintype node]`, the convention of the MVBA leg's
contract-level results, §6.2.8). -/

/-! ## The buffered link, generic -/

namespace Cadence

open Veil

section

variable {ρ σ lbl : Type} {sys : RelationalTransitionSystem ρ σ lbl} {th : ρ}
variable {time : Type} [LinearOrder time]

namespace TLRun

variable {r : TLRun sys th time}

/-- **One buffered link.** The shape of every timed link of the Chorus leg:
if every firing of `l` establishes `P`; wherever `P` does not yet hold inside
the window from `N`, the step is owed (`C`) and enabled when its gate is
open; and wherever `P` does not yet hold from `N'` on, the gate is open —
then `P` holds within the buffered window, widened to any `B` above it.

A lapse of an anti-monotone guard can be made part of `P`, which is how a
link reads "the guard fails only by the progress wanted". -/
theorem withinFrom_of_bufferedFair [Add time] {D δ : time} {C gate : σ → Prop} {l : lbl}
    (hbf : BufferedFair r D δ C gate l) {N N' : Nat} (hNN : N ≤ N') {B : time}
    (hB : r.bufWindow N N' D δ ≤ B) {P : σ → Prop}
    (heff : ∀ st st', sys.tr th st l st' → P st')
    (hen : ∀ n, N ≤ n → r.clk n ≤ B → ¬ P (r.at' n) →
      C (r.at' n) ∧ (gate (r.at' n) → Enabled sys th (r.at' n) l))
    (hg : ∀ n, N' ≤ n → r.clk n ≤ B → ¬ P (r.at' n) → gate (r.at' n)) :
    r.WithinFrom N B P := by
  by_cases hP : ∃ n, N ≤ n ∧ r.clk n ≤ r.bufWindow N N' D δ ∧ P (r.at' n)
  · obtain ⟨n, hn, hc, hp⟩ := hP
    exact ⟨n, hn, le_trans hc hB, hp⟩
  · push Not at hP
    obtain ⟨k, hk, hl, hc⟩ := hbf N N' hNN
      (fun n hn hc => hen n hn (le_trans hc hB) (hP n hn hc))
      (fun n hn hc => hg n hn (le_trans hc hB) (hP n (le_trans hNN hn) hc))
    exact ⟨k + 1, Nat.le_succ_of_le hk, le_trans hc hB, heff _ _ (hl ▸ r.steps k)⟩

/-- **One buffered link, for a family**: as `withinFrom_of_bufferedFair`, with
some member of the family enabled where the gate is open, and every member's
firing establishing `P`. -/
theorem withinFrom_of_bufferedFairFamily [Add time] {D δ : time} {C gate : σ → Prop}
    {S : lbl → Prop}
    (hbf : BufferedFairFamily r D δ C gate S) {N N' : Nat} (hNN : N ≤ N') {B : time}
    (hB : r.bufWindow N N' D δ ≤ B) {P : σ → Prop}
    (heff : ∀ l, S l → ∀ st st', sys.tr th st l st' → P st')
    (hen : ∀ n, N ≤ n → r.clk n ≤ B → ¬ P (r.at' n) →
      C (r.at' n) ∧ (gate (r.at' n) → ∃ l, S l ∧ Enabled sys th (r.at' n) l))
    (hg : ∀ n, N' ≤ n → r.clk n ≤ B → ¬ P (r.at' n) → gate (r.at' n)) :
    r.WithinFrom N B P := by
  by_cases hP : ∃ n, N ≤ n ∧ r.clk n ≤ r.bufWindow N N' D δ ∧ P (r.at' n)
  · obtain ⟨n, hn, hc, hp⟩ := hP
    exact ⟨n, hn, le_trans hc hB, hp⟩
  · push Not at hP
    obtain ⟨k, hk, hS, hc⟩ := hbf N N' hNN
      (fun n hn hc => hen n hn (le_trans hc hB) (hP n hn hc))
      (fun n hn hc => hg n hn (le_trans hc hB) (hP n (le_trans hNN hn) hc))
    exact ⟨k + 1, Nat.le_succ_of_le hk, le_trans hc hB, heff _ hS _ _ (r.steps k)⟩

/-- A buffered window is bounded by a bound on each of its two parts. -/
theorem bufWindow_le [Add time] {N N' : Nat} {D δ B : time}
    (h₁ : r.ref N + D ≤ B) (h₂ : r.ref N' + δ ≤ B) : r.bufWindow N N' D δ ≤ B :=
  max_le h₁ h₂

/-- The clock at the later of two indices is at most a bound on both. -/
theorem clk_max_le' {m n : Nat} {t : time} (hm : r.clk m ≤ t) (hn : r.clk n ≤ t) :
    r.clk (max m n) ≤ t := by
  rcases le_total m n with h | h
  · rw [max_eq_right h]; exact hn
  · rw [max_eq_left h]; exact hm

end TLRun

end

end Cadence

namespace Chorus

open Cadence
open scoped Cadence.Timed

/-- Expose an action's transition body. -/
local macro "chorus_tr" h:ident : tactic =>
  `(tactic| (simp only [Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair. -/
local macro "chorus_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id] at *)

/-! ## A finalizer participated -/

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

open Lean in
/-- One `case <action> => have <h> := Chorus.<action>.frame_<field> <htr>; <tac>`
line per listed action — [Termination.lean](Termination.lean)'s local macro. -/
local macro "frame_cases " htr:ident fld:ident hfr:ident "[" acts:ident,* "]" "=>" tac:tactic : tactic => do
  let mut acc ← `(tactic| skip)
  for a in acts.getElems do
    let lem := mkIdent (`Chorus ++ a.getId ++ Name.mkSimple ("frame_" ++ fld.getId.toString))
    acc ← `(tactic| ($acc; case $a:ident => (have $hfr := $lem:ident $htr; $tac)))
  return acc

set_option maxHeartbeats 1000000 in
/-- **The finalization is the validator's own `finalize_commit`**, whose
guard is its participation: `local_committed i` is written only by
`finalize_commit i`, and every other action frames it. -/
theorem committed_flip {l} {i : node}
    (htr : (RTS).tr th s l s')
    (h0 : ¬ s.local_committed i = true) (h1 : s'.local_committed i = true) :
    s.participating i = true := by
  cases l
  case finalize_commit i' =>
    chorus_tr htr
    obtain ⟨-, hp, -, -, -, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne i' i with rfl | hne
    · exact hp
    · simp_all
  frame_cases htr local_committed hfr
    [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose,
     deliver_chunk_assigned, record_chunk, vote, aggregate_fastqc_pos, aggregate_fastqc_neg,
     commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos,
     broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose,
     accept_mvba_commitqc, on_mvba_decide_pos, on_mvba_decide_neg, on_mvba_commitqc_pos, on_mvba_commitqc_neg, mvba_avail_ready, mvba_terminate,
     redisseminate_chunk, cast_fb_commit, commit_assign_pos, commit_assign_neg,
     byz_sign_proposer, byz_deliver_chunk, byz_redisseminate_chunk,
     byz_sign_vote_pos, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg,
     byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit,
     byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit,
     byz_release_msg_decrypt_share] => exact absurd (hfr ▸ h1) h0

/-- **A validator that has finalized participates**, at every point of every
run: the finalization was its own gated `finalize_commit` (`committed_flip`),
and participation is monotone. -/
theorem committed_participating (r : LRun RTS th) {i : node} :
    ∀ n, (r.at' n).local_committed i = true → (r.at' n).participating i = true :=
  record_backed r (F := fun st => st.local_committed i = true)
    (Q := fun st => st.participating i = true)
    (by simp [Chorus.local_committed.init r.starts i])
    (fun n h0 h1 => Chorus.participating.mono (r.steps n) i (committed_flip (r.steps n) h0 h1))
    (fun n h => Chorus.participating.mono (r.steps n) i h)

end Steps

/-! ## Totality -/

section Totality

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
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]

/-- The `MVBASafety` instance the composed system runs, as a local instance
for the generic step lemmas. -/
local macro "mvba_inst" : tactic =>
  `(tactic| letI : MVBASafety node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset nset (fun i => nset.is_byz i = true) := Mvba.mvbaSafety thM)

/-- `j` has an entry for proposer `J`, or has finalized: the goal of one
assignment link, monotone along every run. -/
def AssignedOrDone
    (st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) (j J : node) : Prop :=
  (∃ m, st.local_committed_pos j J m = true) ∨ st.local_committed_neg j J = true ∨
    st.local_committed j = true

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
theorem AssignedOrDone.step {r : TChorusRun thS thM time} {n : Nat} {j J : node}
    (h : AssignedOrDone (r.at' n) j J) : AssignedOrDone (r.at' (n + 1)) j J := by
  mvba_inst
  rcases h with ⟨m, hm⟩ | hm | hm
  · exact Or.inl ⟨m, Chorus.local_committed_pos.mono (r.steps n) j J m hm⟩
  · exact Or.inr (Or.inl (Chorus.local_committed_neg.mono (r.steps n) j J hm))
  · exact Or.inr (Or.inr (Chorus.local_committed.mono (r.steps n) j hm))

omit [IsOrderedAddMonoid time] in
/-- **The assignment link** (`commit_assign_*`, a `Δ`-row): from an index `N`
at which `j`'s entry for proposer `J` has a commitment proof from a correct
sender, and an index `P` at which `j` participates, `j` has an entry for `J`
— or has finalized — by any `B` that bounds both parts of the buffered
window: `ref N + Δ` (the proof's delivery) and `ref (max N P) + δ` (the gate). -/
theorem within_assigned (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hab : NoAbandonBeforeFinalizing r.toLRun)
    {j : node} (hj : ¬ nset.is_byz j = true) {J : node} (hJ : thS.is_proposer J = true)
    {N P : Nat} (hproof : (∃ m, ProofPos (nset := nset) (r.at' N) J m) ∨ ProofNeg (nset := nset) (r.at' N) J)
    (hP : (r.at' P).participating j = true) {B : time}
    (hB : r.bufWindow N (max N P) sch.Δ sch.δ ≤ B) :
    r.WithinFrom N B (fun st => AssignedOrDone st j J) := by
  mvba_inst
  have hact : ∀ n, max N P ≤ n → ¬ AssignedOrDone (r.at' n) j J → Active (r.at' n) j :=
    fun n hn hnot => ⟨r.mono (P := fun st => st.participating j = true)
        (fun k hk => Chorus.participating.mono (r.steps k) j hk) hP n (by omega),
      fun h => hnot (Or.inr (Or.inr (hab j hj n h)))⟩
  rcases hproof with ⟨m, hm⟩ | hm
  · have hm' := r.mono (P := fun st => ProofPos (nset := nset) st J m)
      (fun k h => proofPos_step (r.steps k) h) hm
    refine r.withinFrom_of_bufferedFair
      (hTJ.rows (.commit_assign_pos j J m) .net rfl (fun h => h)) (le_max_left _ _) hB
      (fun _ _ h => Or.inl ⟨m, commit_assign_pos_effect h⟩) (fun n hn _ hnot => ?_)
      (fun n hn _ hnot => hact n hn hnot)
    refine ⟨hm' n hn, fun hg => enabled_commit_assign_pos hj hg
      (fun h => hnot (Or.inr (Or.inr h))) hJ (assignable_pos_of_proof r.toLRun n (hm' n hn))
      (fun m' h => hnot (Or.inl ⟨m', h⟩)) (fun h => hnot (Or.inr (Or.inl h)))⟩
  · have hm' := r.mono (P := fun st => ProofNeg (nset := nset) st J)
      (fun k h => proofNeg_step (r.steps k) h) hm
    refine r.withinFrom_of_bufferedFair
      (hTJ.rows (.commit_assign_neg j J) .net rfl (fun h => h)) (le_max_left _ _) hB
      (fun _ _ h => Or.inr (Or.inl (commit_assign_neg_effect h))) (fun n hn _ hnot => ?_)
      (fun n hn _ hnot => hact n hn hnot)
    refine ⟨hm' n hn, fun hg => enabled_commit_assign_neg hj hg
      (fun h => hnot (Or.inr (Or.inr h))) hJ (assignable_neg_of_proof r.toLRun n (hm' n hn))
      (fun m' h => hnot (Or.inl ⟨m', h⟩)) (fun h => hnot (Or.inr (Or.inl h)))⟩

omit [IsOrderedAddMonoid time] in
/-- **The finalization link** (`finalize_commit`, a `δ`-row): from an index
`N` at which `j` has an entry for every proposer, and an index `P` at which
it participates, `j` has finalized by any `B` bounding the buffered window. -/
theorem within_finalized (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hab : NoAbandonBeforeFinalizing r.toLRun)
    {j : node} (hj : ¬ nset.is_byz j = true) {N P : Nat}
    (hall : ∀ J, thS.is_proposer J = true →
      (∃ m, (r.at' N).local_committed_pos j J m = true) ∨ (r.at' N).local_committed_neg j J = true)
    (hP : (r.at' P).participating j = true) {B : time}
    (hB : r.bufWindow N (max N P) sch.δ sch.δ ≤ B) :
    r.WithinFrom N B (fun st => st.local_committed j = true) := by
  mvba_inst
  have hall' : ∀ n, N ≤ n → ∀ J, thS.is_proposer J = true →
      (∃ m, (r.at' n).local_committed_pos j J m = true) ∨ (r.at' n).local_committed_neg j J = true :=
    r.mono (P := fun st => ∀ J, thS.is_proposer J = true →
        (∃ m, st.local_committed_pos j J m = true) ∨ st.local_committed_neg j J = true)
      (fun k h J hJ => (h J hJ).imp (fun ⟨m, hm⟩ => ⟨m, Chorus.local_committed_pos.mono (r.steps k) j J m hm⟩)
        (Chorus.local_committed_neg.mono (r.steps k) j J)) hall
  refine r.withinFrom_of_bufferedFair
    (hTJ.rows (.finalize_commit j) .loc rfl (fun h => h)) (le_max_left _ _) hB
    (fun _ _ h => finalize_commit_effect h)
    (fun n hn _ hnot => ⟨trivial, fun hg => enabled_finalize_commit hj hg hnot (hall' n hn)⟩)
    (fun n hn _ hnot => ⟨r.mono (P := fun st => st.participating j = true)
        (fun k hk => Chorus.participating.mono (r.steps k) j hk) hP n (by omega),
      fun h => hnot (hab j hj n h)⟩)

/-- **`d_tot`-totality** (Proposition 4 (`prop:chorus-totality`)), in the tolerance-parametric
form: `TotalityClaim sch d` at every schedule and every tolerance `d`, over a
finite validator set. If a correct validator `i` finalizes at index `n`,
every correct validator `j` finalizes by `max(clk n, GST) + max(Δ, d) + 2δ`.

Write `u = max(clk n, GST)` and `e = max(Δ, d)`. `i` participated
(`committed_participating`), so `j` participates at some `P` with clock at
most `u + d ≤ u + e`. Every proposer's entry has a commitment proof from `n`
on (`proofs_of_finalized`), so each assignment fires by
`max(u + Δ, u + e + δ) = u + e + δ` (`within_assigned`), all of them at one
index (`withinFrom_forall`); then `finalize_commit` by `u + e + 2δ`
(`within_finalized`). At every step, a `j` that has already finalized is
done; otherwise it has not abandoned (C1), so its gate is open. -/
theorem totality [Fintype node] (sch : Schedule view time) (d : time) :
    TotalityClaim (nset := nset) sch d thS thM := by
  mvba_inst
  intro r hTJ hsync hab n i hi hci j hj
  set u := r.ref n with hu
  set e := max sch.Δ d with he
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have he0 : 0 ≤ e := le_trans sch.mvba.Δ_pos.le (le_max_left _ _)
  have hue : u ≤ u + e := le_add_of_nonneg_right he0
  have hgu : r.gst ≤ u := r.gst_le_ref n
  have hcu : r.clk n ≤ u := r.clk_le_ref n
  -- `j` participates by `u + e`.
  obtain ⟨P, hPc, hP⟩ := hsync n i hi (committed_participating r.toLRun n hci) j hj
  have hPc' : r.clk P ≤ u + e := le_trans hPc (add_le_add_right (le_max_right _ _) _)
  have hrefP : r.ref (max n P) ≤ u + e :=
    r.ref_le (r.clk_max_le' (le_trans hcu hue) hPc') (le_trans hgu hue)
  -- Every proposer's entry assigned (or `j` done) by `u + e + δ`.
  have hB1 : u + e ≤ u + e + sch.δ := le_add_of_nonneg_right hδ
  obtain ⟨N2, hN2, hc2, hall⟩ := r.withinFrom_forall
    (fun J st => thS.is_proposer J = true → AssignedOrDone st j J)
    (fun J k h hJ => (h hJ).step) n (u + e + sch.δ) (le_trans hcu (le_trans hue hB1))
    (Finset.univ : Finset node).toList
    (fun J _ => by
      by_cases hJ : thS.is_proposer J = true
      · obtain ⟨k, hk, hck, hk'⟩ := within_assigned sch hTJ hab hj hJ
          (proofs_of_finalized r.toLRun hi hci J hJ) hP (B := u + e + sch.δ)
          (r.bufWindow_le
            (le_trans (add_le_add_right (le_max_left _ _) _) hB1)
            (by gcongr))
        exact ⟨k, hk, hck, fun _ => hk'⟩
      · exact ⟨n, le_rfl, le_trans hcu (le_trans hue hB1), fun h => absurd h hJ⟩)
  have hbound : u + e + sch.δ + sch.δ = max (r.clk n) r.gst + sch.dtot d := by
    simp only [hu, he, Schedule.dtot, Ltot, TLRun.ref, two_nsmul, add_assoc]
  have hB2 : u + e + sch.δ ≤ u + e + sch.δ + sch.δ := le_add_of_nonneg_right hδ
  by_cases hdone : (r.at' N2).local_committed j = true
  · exact ⟨N2, by rw [← hbound]; exact le_trans hc2 hB2, hdone⟩
  · have hall2 : ∀ J, thS.is_proposer J = true →
        (∃ m, (r.at' N2).local_committed_pos j J m = true) ∨
          (r.at' N2).local_committed_neg j J = true := fun J hJ => by
      rcases hall J (by simp) hJ with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hdone
    have hrefN2 : r.ref N2 ≤ u + e + sch.δ := r.ref_le hc2 (le_trans hgu (le_trans hue hB1))
    have hrefN2P : r.ref (max N2 P) ≤ u + e + sch.δ :=
      r.ref_le (r.clk_max_le' hc2 (le_trans hPc' hB1)) (le_trans hgu (le_trans hue hB1))
    obtain ⟨k, -, hck, hk⟩ := within_finalized sch hTJ hab hj hall2 hP
      (B := u + e + sch.δ + sch.δ)
      (r.bufWindow_le (by gcongr) (by gcongr))
    exact ⟨k, by rw [← hbound]; exact hck, hk⟩

/-- **The paper's `d_tot = Δ`** (Proposition 4 (`prop:chorus-totality`)): at `δ = 0` and the
paper's tolerance `d = Δ` (Δ-synchronized participation), once a correct
validator finalizes at clock `c`, every correct validator finalizes by
`max(c, GST) + Δ`. `totality` at `d = Δ`, read through `Ltot_paper`. -/
theorem totality_paper [Fintype node] (sch : Schedule view time) (hδ0 : sch.δ = 0)
    (r : TChorusRun thS thM time) (hTJ : TimedJustice sch r)
    (hsync : SyncParticipationWithin sch.Δ r) (hab : NoAbandonBeforeFinalizing r.toLRun)
    (n : Nat) (i : node) (hi : ¬ nset.is_byz i = true) (hc : (r.at' n).local_committed i = true)
    (j : node) (hj : ¬ nset.is_byz j = true) :
    ∃ m, r.clk m ≤ max (r.clk n) r.gst + sch.Δ ∧ (r.at' m).local_committed j = true := by
  have h := totality (nset := nset) sch sch.Δ r hTJ hsync hab n i hi hc j hj
  have hd : sch.dtot sch.Δ = sch.Δ := by
    simp only [Schedule.dtot]; rw [hδ0]; exact Ltot_paper sch.Δ
  rwa [hd] at h

end Totality

end Chorus

/-! ## The pinned trust base

The standard Lean trio and nothing else — no `sorryAx`. -/

/--
info: 'Cadence.TLRun.withinFrom_of_bufferedFair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cadence.TLRun.withinFrom_of_bufferedFair

/--
info: 'Chorus.committed_participating' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.committed_participating

/--
info: 'Chorus.totality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.totality

/--
info: 'Chorus.totality_paper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.totality_paper
