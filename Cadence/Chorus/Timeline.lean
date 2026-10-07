import Cadence.Chorus.Totality

/-! # Chorus/Timeline — the timeline of Proposition 5 (`prop:chorus-finalization-time`) to the MVBA proposals

[Bounds.md](../../docs/Bounds.md) §6.4.3, stage S3. The untimed chains of
[Termination.lean](Termination.lean) re-run with deadlines, from
`M := max(t, GST)`, up to the MVBA proposals. Each milestone is a named
lemma whose statement carries its deadline, so the `δ`-multiple of every
step is read off the statement:

| milestone | lemma | by |
|---|---|---|
| everyone participating | `exists_start` | `t` |
| the deadline has passed | `deadline_le_of_start`, (P2) | `D ≤ t + Δ` |
| a correct proposer's chunk recorded, if before the deadline | `within_entry_recorded`, `within_proposal_recorded` | `max(X, GST) + Δ < D` |
| a correct validator's first-round vote | `within_voted` | `M + Δ + δ` |
| every correct vote, at one index | `within_all_voted` | `M + Δ + δ` |
| the honest quorum's votes received | `within_received` | `M + 2Δ + δ` |
| a fallback signature per proposer | `within_fb_sig` | `M + 2Δ + 2δ` |
| the second-round vote, fast or fallback | `within_cast` | `M + 2Δ + 3δ` |
| every correct validator saturated | `within_all_saturated` | `M + 2Δ + 3δ` |
| the MVBA's trigger from correct senders | `correctTrigger_of_saturated` | (same index) |
| a correct fast voter's FastQCs adopted (F7) | `within_complete_fast_metablock` | `M + 3Δ + 3δ` |
| the proposal on a correct `FBCert` | `within_input_of_fbcert` | `M + 3Δ + 3δ` |
| the proposal on the own fast meta-block (F9) | `within_input_of_fast` | `M + 3Δ + 4δ` |
| every correct validator's MVBA proposal | `within_all_input` | `M + 3Δ + 4δ` |

The chain that is assumed of the run is (Δδ-justice) and (P-phase) only:
neither the MVBA's timing nor the bridge enters before the proposals. What
the lemmas take besides is the gate, as the untimed links take
`ActiveFrom`: every correct validator is actively participating on the
window (`ActiveUntil`). On the branch S4 uses, where nobody has finalized by
the window's end, C1 gives it (`activeUntil_of_not_finalized`).

**Every `Δ`-row costs `Δ` because `δ ≤ Δ`.** With its gate already open, a
row's window is `ref N + max(Δ, δ)`; the schedule's `δ_le_Δ` (F10,
[Bounds.md](../../docs/Bounds.md) §6.4.2) makes it `ref N + Δ`.

## How it is built

Each link is one (Δδ-justice) clause through `TLRun.withinFrom_of_bufferedFair`
([Totality.lean](Totality.lean)): the message part from the index at which
the step became owed, the gate from the index at which the landmark was
reached, and the goal widened by the lapse of the step's anti-monotone
guards, as in the untimed links. Two facts the untimed chain did not need:

* **a correct vote is frozen once cast** (`vote_pos_sig_frozen`): from the
  invariants `vote_cast_entries`, `vote_unique_pos` and
  `vote_unique_pos_neg`. So whether the honest quorum's votes are positive
  evidence for a proposer is settled at the index at which they have all
  voted, and the fallback entry's case split (`fb_sign_pos` on the evidence,
  `fb_sign_neg` on its absence among the votes received, each of which is
  the sender's signed entry, `vote_rcv_pos_backed`) is made once, without
  restarting the window. The negative entry reads the validator's own
  receipts, so it is a `δ`-row after the receipts' `Δ`-rows: the one `δ`
  the receipts add to the timeline;
* **the phase is `pre_deadline` before `D`** (`phase_pre_of_lt`), from (P1),
  for the chunk to be recorded. -/

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

/-- Turn an enabledness goal into the action's guards. -/
local macro "chorus_enabled" : tactic =>
  `(tactic| simp only [Enabled, Chorus.relationalTransitionSystem, Chorus.Next,
      Chorus.NextAct, trSimp])

/-! ## Step facts -/

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
/-- **The phase leaves `pre_deadline` only by its marker**: a step from
`pre_deadline` to another phase is `advance_to_deadline`. The other two
markers are enabled only at later phases, and every other action frames the
phase. -/
theorem leave_pre_label {l}
    (htr : (RTS).tr th s l s')
    (h0 : s.phase = Phase_EnumClass.pre_deadline) (h1 : s'.phase ≠ Phase_EnumClass.pre_deadline) :
    l = .advance_to_deadline := by
  obtain ⟨d1, d2, -, -, -, -⟩ := phase_distinct (Phase := Phase)
  cases l
  case advance_to_deadline => rfl
  case advance_to_fb_arm =>
    chorus_tr htr
    obtain ⟨h, -⟩ := htr
    exact absurd (h0.symm.trans h) d1
  case advance_to_mvba_arm =>
    chorus_tr htr
    obtain ⟨h, -⟩ := htr
    exact absurd (h0.symm.trans h) d2
  frame_rest htr phase hfr=> exact absurd (hfr ▸ h0) h1

/-- At the MVBA arm stays at the MVBA arm. -/
theorem phase_mvbaArm_step {l} (htr : (RTS).tr th s l s')
    (h : s.phase = Phase_EnumClass.post_mvba_arm) : s'.phase = Phase_EnumClass.post_mvba_arm := by
  obtain ⟨-, -, d3, -, d5, d6⟩ := phase_distinct (Phase := Phase)
  rcases phase_step htr with h' | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h']; exact h
  · exact absurd (h1.symm.trans h) d3
  · exact absurd (h1.symm.trans h) d5
  · exact absurd (h1.symm.trans h) d6

/-- **A landmark, once reached, stays reached**: the phase only moves forward. -/
theorem Landmark.reached_step {l} (htr : (RTS).tr th s l s') {L : Landmark}
    (h : L.Reached s) : L.Reached s' := by
  cases L
  · exact phase_ne_pre_step htr h
  · exact AtArm.step htr h
  · exact phase_mvbaArm_step htr h

set_option maxHeartbeats 1000000 in
/-- **A correct proposer's signature comes with its chunks** (Algorithm 2
(`alg:proposer-dissemination`)): the step that sets `msg_proposer_signed j m`
for a correct `j` is its `propose j m`, which sends every validator its
chunk under `m` in the same step. -/
theorem signed_chunks_flip {l} {j : node} {m : merkle_root}
    (htr : (RTS).tr th s l s') (hj : ¬ nset.is_byz j = true)
    (h0 : ¬ s.msg_proposer_signed j m = true) (h1 : s'.msg_proposer_signed j m = true) :
    ∀ i, s'.msg_chunk j i j m = true := by
  cases l
  case propose j' m' =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    intro i
    by_cases h : j' = j ∧ m' = m
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp_all
  case byz_sign_proposer j' m' =>
    chorus_tr htr
    obtain ⟨hb, rfl⟩ := htr
    chorus_field_simp
    rcases eq_or_ne j' j with rfl | hne
    · simp_all
    · simp_all
  frame_rest htr msg_proposer_signed hfr => exact absurd (hfr ▸ h1) h0

/-- **A correct proposer has sent every validator its chunk**, at every
point of every run at which it has signed its root (`signed_chunks_flip`). -/
theorem signed_chunks (r : LRun RTS th) {j : node} {m : merkle_root} (hj : ¬ nset.is_byz j = true) :
    ∀ n, (r.at' n).msg_proposer_signed j m = true → ∀ i, (r.at' n).msg_chunk j i j m = true :=
  record_backed r (F := fun st => st.msg_proposer_signed j m = true)
    (Q := fun st => ∀ i, st.msg_chunk j i j m = true)
    (by simp [Chorus.msg_proposer_signed.init r.starts j m])
    (fun n h0 h1 => signed_chunks_flip (r.steps n) hj h0 h1)
    (fun n h i => Chorus.msg_chunk.mono (r.steps n) j i j m (h i))

theorem enabled_record_chunk {i j : node} {m : merkle_root}
    (hi : ¬ nset.is_byz i = true) (hj : th.is_proposer j = true)
    (hc : Chorus.chunk_received i j m th s) (hs : s.msg_proposer_signed j m = true)
    (hph : s.phase = Phase_EnumClass.pre_deadline)
    (hnp : ∀ m2, ¬ s.local_entry_pos i j m2 = true) (hnn : ¬ s.local_entry_neg i j = true) :
    Enabled RTS th s (.record_chunk i j m) := by
  chorus_enabled
  exact ⟨_, hi, hj, hc, hs, hph, hnp, hnn, rfl⟩

theorem record_chunk_effect {i j : node} {m : merkle_root}
    (htr : (RTS).tr th s (.record_chunk i j m) s') :
    s'.local_entry_pos i j m = true := by
  chorus_tr htr
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ := htr
  chorus_field_simp

/-- **A correct vote is frozen once cast.** If a correct validator `a` has
voted at `N`, a positive vote signature of `a` for a proposer at a later
index was already there at `N`: at `N` its vote carries an entry for the
proposer (`vote_cast_entries`), which is unique (`vote_unique_pos`) and
excludes a negative one (`vote_unique_pos_neg`), and both persist. -/
theorem vote_pos_sig_frozen (r : LRun RTS th) {a J : node} {M : merkle_root}
    (ha : ¬ nset.is_byz a = true) (hJ : th.is_proposer J = true) {N n : Nat}
    (hv : (r.at' N).local_voted a = true) (hn : N ≤ n)
    (h : (r.at' n).msg_vote_pos_sig a J M = true) : (r.at' N).msg_vote_pos_sig a J M = true := by
  have hc := Chorus.reachable_voted_implies_cast (r.reachable N) a ⟨ha, hv⟩
  rcases Chorus.reachable_vote_cast_entries (r.reachable N) a J ⟨hc, hJ⟩ with ⟨M', hM'⟩ | hneg
  · have hM'n := r.mono (P := fun st => st.msg_vote_pos_sig a J M' = true)
      (fun k hk => msg_vote_pos_sig_mono (r.steps k) a J M' hk) hM' n hn
    obtain rfl := Chorus.reachable_vote_unique_pos (r.reachable n) a J M M' ⟨ha, h, hM'n⟩
    exact hM'
  · have hnegn := r.mono (P := fun st => st.msg_vote_neg_sig a J = true)
      (fun k hk => msg_vote_neg_sig_mono (r.steps k) a J hk) hneg n hn
    exact absurd ⟨h, hnegn⟩ (Chorus.reachable_vote_unique_pos_neg (r.reachable n) a J M ha)

end Steps

/-! ## The timeline, at the system's MVBA -/

section Timeline

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

/-! ### The gate on a window -/

/-- **Every correct validator is actively participating on the window**: at
every index from `N₀` on whose clock is at most `B`. The timed form of
[Termination.lean](Termination.lean)'s `ActiveFrom`, which the honest links
take as their gate. -/
def ActiveUntil (r : TChorusRun thS thM time) (N₀ : Nat) (B : time) : Prop :=
  ∀ n, N₀ ≤ n → r.clk n ≤ B → ∀ i, ¬ nset.is_byz i = true → Active (r.at' n) i

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
theorem ActiveUntil.mono {r : TChorusRun thS thM time} {N₀ : Nat} {B B' : time}
    (h : ActiveUntil r N₀ B) (hB : B' ≤ B) : ActiveUntil r N₀ B' :=
  fun n hn hc => h n hn (le_trans hc hB)

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **The gate on S4's branch.** If every correct validator participates at
`N₀` and none has finalized at any index whose clock is at most `B`, then by
C1 none has abandoned there either, so all are active on the window. -/
theorem activeUntil_of_not_finalized {r : TChorusRun thS thM time} {N₀ : Nat} {B : time}
    (hpart : ∀ i, ¬ nset.is_byz i = true → (r.at' N₀).participating i = true)
    (hab : NoAbandonBeforeFinalizing r.toLRun)
    (hnf : ∀ n i, ¬ nset.is_byz i = true → r.clk n ≤ B → ¬ (r.at' n).local_committed i = true) :
    ActiveUntil r N₀ B := by
  mvba_inst
  exact fun n hn hc i hi => ⟨r.mono (P := fun st => st.participating i = true)
      (fun k hk => Chorus.participating.mono (r.steps k) i hk) (hpart i hi) n hn,
    fun h => hnf n i hi hc (hab i hi n h)⟩

/-! ### The start and the landmarks -/

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **Milestone 0: everyone participating, by `t`.** With finitely many
validators, the caller's `AllParticipateBy t` gives one index at which every
correct validator participates, and its clock is at most `t`. `hex` (some
validator is correct) only rules out the vacuous case, where no index need
read at most `t`. -/
theorem exists_start [Fintype node] {r : TChorusRun thS thM time} {t : time}
    (hex : ∃ i, ¬ nset.is_byz i = true) (h : AllParticipateBy t r) :
    ∃ N₀, r.clk N₀ ≤ t ∧ ∀ i, ¬ nset.is_byz i = true → (r.at' N₀).participating i = true := by
  mvba_inst
  obtain ⟨i0, hi0⟩ := hex
  obtain ⟨n0, hn0, -⟩ := h i0 hi0
  obtain ⟨N₀, -, hc, hall⟩ := r.withinFrom_forall
    (fun i st => ¬ nset.is_byz i = true → st.participating i = true)
    (fun i k h hi => Chorus.participating.mono (r.steps k) i (h hi)) 0 t
    (le_trans (r.clk_le_of_le (Nat.zero_le n0)) hn0) (Finset.univ : Finset node).toList
    (fun i _ => by
      by_cases hi : nset.is_byz i = true
      · exact ⟨0, le_rfl, le_trans (r.clk_le_of_le (Nat.zero_le n0)) hn0, fun h => absurd hi h⟩
      · obtain ⟨n, hn, hp⟩ := h i hi
        exact ⟨n, Nat.zero_le _, hn, fun _ => hp⟩)
  exact ⟨N₀, hc, fun i hi => hall i (by simp) hi⟩

omit [IsOrderedAddMonoid time] in
/-- **The deadline is at most `Δ` after the start** (C2, the Conductor's
integrity): a correct validator participates at `N₀`, so `D ≤ clk N₀ + Δ`. -/
theorem deadline_le_of_start (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hC2 : NoEarlyStart sch r) {N₀ : Nat} {t : time} (hN₀ : r.clk N₀ ≤ t) [IsOrderedAddMonoid time]
    {i0 : node} (hi0 : ¬ nset.is_byz i0 = true) (hp : (r.at' N₀).participating i0 = true) :
    sch.D ≤ t + sch.Δ :=
  le_trans (hC2 N₀ i0 hi0 hp) (by gcongr)

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **(P2), as a milestone**: each landmark is reached at some index whose
clock is at most the landmark's time, and stays reached. -/
theorem reached_within [AddCommMonoid time] (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hPP : PhasePunctual sch r) (L : Landmark) :
    ∃ n, r.clk n ≤ L.time sch ∧ ∀ m, n ≤ m → L.Reached (r.at' m) := by
  mvba_inst
  obtain ⟨n, hR, hc⟩ := (hPP L).2
  exact ⟨n, hc, r.mono (P := fun st => L.Reached st) (fun k hk => Landmark.reached_step (r.steps k) hk) hR⟩

/-! ### The first round -/

/-- `M ≤ M + x` for a non-negative `x`. -/
private theorem le_add_nn {a x : time} (hx : 0 ≤ x) : a ≤ a + x := le_add_of_nonneg_right hx

/-- **Milestone: a correct validator's first-round vote, by `M + Δ + δ`**
(`M = max(t, GST)`). `vote` is a `δ`-row whose gate — active participation
and the phase past the deadline — opens by `max(t, D)`, and `D ≤ t + Δ`; its
guard `¬ local_voted` lapses only by the vote. -/
theorem within_voted (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r) {t : time}
    (hD : sch.D ≤ t + sch.Δ) {N₀ : Nat} (hN₀ : r.clk N₀ ≤ t)
    (hact : ActiveUntil r N₀ (max t r.gst + sch.Δ + sch.δ))
    {i : node} (hi : ¬ nset.is_byz i = true) :
    r.WithinFrom N₀ (max t r.gst + sch.Δ + sch.δ) (fun st => st.local_voted i = true) := by
  mvba_inst
  obtain ⟨Nd, hNdc, hNd⟩ := reached_within sch hPP .deadline
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hM : t ≤ max t r.gst := le_max_left _ _
  have hg : r.gst ≤ max t r.gst := le_max_right _ _
  have href0 : r.ref N₀ ≤ max t r.gst + sch.Δ :=
    r.ref_le (le_trans hN₀ (le_trans hM (le_add_nn hΔ))) (le_trans hg (le_add_nn hΔ))
  have hrefd : r.ref (max N₀ Nd) ≤ max t r.gst + sch.Δ :=
    r.ref_le (r.clk_max_le' (le_trans hN₀ (le_trans hM (le_add_nn hΔ)))
      (le_trans hNdc (le_trans hD (by gcongr)))) (le_trans hg (le_add_nn hΔ))
  refine r.withinFrom_of_bufferedFair (hTJ.rows (.vote i) .loc rfl (fun h => h)) (le_max_left _ _)
    (r.bufWindow_le (add_le_add href0 le_rfl) (add_le_add hrefd le_rfl)) (fun _ _ h => vote_effect h)
    (fun n hn hc hnot => ⟨trivial, fun hg => enabled_vote hi hg.1 hg.2 hnot⟩)
    (fun n hn hc _ => ⟨hact n (by omega) hc i hi, hNd n (by omega)⟩)

/-- **Milestone: every correct validator's first-round vote, at one index,
by `M + Δ + δ`** — each vote is on the network with it (`voted_implies_cast`). -/
theorem within_all_voted [Fintype node] (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r) {t : time}
    (hD : sch.D ≤ t + sch.Δ) {N₀ : Nat} (hN₀ : r.clk N₀ ≤ t)
    (hact : ActiveUntil r N₀ (max t r.gst + sch.Δ + sch.δ)) :
    r.WithinFrom N₀ (max t r.gst + sch.Δ + sch.δ)
      (fun st => ∀ i, ¬ nset.is_byz i = true → st.local_voted i = true ∧ st.msg_vote_cast i = true) := by
  mvba_inst
  have hx : 0 ≤ sch.Δ + sch.δ := add_nonneg sch.mvba.Δ_pos.le sch.mvba.δ_nonneg
  obtain ⟨N, hN, hc, hall⟩ := r.withinFrom_forall
    (fun i st => ¬ nset.is_byz i = true → st.local_voted i = true)
    (fun i k h hi => Chorus.local_voted.mono (r.steps k) i (h hi)) N₀ (max t r.gst + sch.Δ + sch.δ)
    (le_trans hN₀ (le_trans (le_max_left _ _) (by rw [add_assoc]; exact le_add_nn hx)))
    (Finset.univ : Finset node).toList
    (fun i _ => by
      by_cases hi : nset.is_byz i = true
      · exact ⟨N₀, le_rfl, le_trans hN₀ (le_trans (le_max_left _ _)
          (by rw [add_assoc]; exact le_add_nn hx)), fun h => absurd hi h⟩
      · obtain ⟨n, hn, hcn, hv⟩ := within_voted sch hTJ hPP hD hN₀ hact hi
        exact ⟨n, hn, hcn, fun _ => hv⟩)
  exact ⟨N, hN, hc, fun i hi => ⟨hall i (by simp) hi,
    Chorus.reachable_voted_implies_cast (r.reachable N) i ⟨hi, hall i (by simp) hi⟩⟩⟩

/-! ### The second round -/

/-- `i` has a fallback signature for proposer `J`, or has cast a
second-round vote: the goal of one fallback-entry link, monotone. -/
def FbSigOrCast (st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice)
    (i J : node) : Prop :=
  (∃ m, st.msg_fb_pos_sig i J m = true) ∨ st.msg_fb_neg_sig i J = true ∨
    st.msg_commit_cast i = true ∨ st.msg_fallback_sig i = true

/-- `i` has cast a second-round vote, fast or fallback. -/
def Cast (st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) (i : node) : Prop :=
  st.msg_commit_cast i = true ∨ st.msg_fallback_sig i = true

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
theorem FbSigOrCast.step {r : TChorusRun thS thM time} {n : Nat} {i J : node}
    (h : FbSigOrCast (r.at' n) i J) : FbSigOrCast (r.at' (n + 1)) i J := by
  mvba_inst
  rcases h with ⟨m, hm⟩ | hm | hm | hm
  · exact Or.inl ⟨m, Chorus.msg_fb_pos_sig.mono (r.steps n) i J m hm⟩
  · exact Or.inr (Or.inl (Chorus.msg_fb_neg_sig.mono (r.steps n) i J hm))
  · exact Or.inr (Or.inr (Or.inl (Chorus.msg_commit_cast.mono (r.steps n) i hm)))
  · exact Or.inr (Or.inr (Or.inr (Chorus.msg_fallback_sig.mono (r.steps n) i hm)))

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
theorem Cast.step {r : TChorusRun thS thM time} {n : Nat} {i : node}
    (h : Cast (r.at' n) i) : Cast (r.at' (n + 1)) i := by
  mvba_inst
  rcases h with hm | hm
  · exact Or.inl (Chorus.msg_commit_cast.mono (r.steps n) i hm)
  · exact Or.inr (Chorus.msg_fallback_sig.mono (r.steps n) i hm)

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- A correct validator that has cast a second-round vote is saturated: the
vote carries a signature per proposer (`commit_cast_sigs`, `fallback_sig_sigs`). -/
theorem saturated_of_cast {r : TChorusRun thS thM time} {n : Nat} {i : node}
    (hi : ¬ nset.is_byz i = true) (h : Cast (r.at' n) i) :
    Saturated thS (r.at' n) i := by
  mvba_inst
  rcases h with h | h
  · exact Or.inl ⟨h, commit_cast_sigs r.toLRun hi n h⟩
  · exact Or.inr ⟨h, fallback_sig_sigs r.toLRun hi n h⟩

/-- **Milestone: the honest quorum's votes received, by `M + 2Δ + δ`.**
From the index `Nv` at which every correct validator has voted (by
`M + Δ + δ`), `i` takes each correct voter's vote: `receive_vote_*` is a
`Δ`-row on the vote, owed because its sender is correct, and its guard
lapses only by the receipt. The vote carries an entry for every proposer
(`vote_cast_entries`). -/
theorem within_received [Fintype node] (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) {t : time}
    {Nv : Nat} (hcv : r.clk Nv ≤ max t r.gst + sch.Δ + sch.δ)
    (hvoted : ∀ a, ¬ nset.is_byz a = true → (r.at' Nv).local_voted a = true)
    {qv : nodeset} (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true)
    {i : node} (hi : ¬ nset.is_byz i = true) {J : node} (hJ : thS.is_proposer J = true) :
    r.WithinFrom Nv (max t r.gst + 2 • sch.Δ + sch.δ)
      (fun st => ∀ a, nset.member a qv = true → Received st i a J) := by
  mvba_inst
  set M := max t r.gst with hMdef
  have hg : r.gst ≤ M := le_max_right _ _
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have hrefv : r.ref Nv ≤ M + sch.Δ + sch.δ :=
    r.ref_le hcv (le_trans hg (by rw [add_assoc]; exact le_add_nn (add_nonneg hΔ hδ)))
  have hB : M + sch.Δ + sch.δ ≤ M + 2 • sch.Δ + sch.δ := by
    rw [two_nsmul]; gcongr; exact le_add_nn hΔ
  have hW : r.bufWindow Nv (max Nv Nv) sch.Δ sch.δ ≤ M + 2 • sch.Δ + sch.δ := by
    rw [max_self]
    refine r.bufWindow_le ?_ ?_
    · calc r.ref Nv + sch.Δ ≤ M + sch.Δ + sch.δ + sch.Δ := add_le_add hrefv le_rfl
        _ = M + 2 • sch.Δ + sch.δ := by rw [two_nsmul]; abel
    · calc r.ref Nv + sch.δ ≤ M + sch.Δ + sch.δ + sch.Δ := add_le_add hrefv sch.δ_le_Δ
        _ = M + 2 • sch.Δ + sch.δ := by rw [two_nsmul]; abel
  obtain ⟨N, hN, hc, hall⟩ := r.withinFrom_forall
    (fun a st => nset.member a qv = true → Received st i a J)
    (fun a k h hm => (h hm).step (r.steps k)) Nv (M + 2 • sch.Δ + sch.δ) (le_trans hcv hB)
    (Finset.univ : Finset node).toList
    (fun a _ => by
      by_cases hm : nset.member a qv = true
      · have ha := hqvh a hm
        have hcast : ∀ n, Nv ≤ n → (r.at' n).msg_vote_cast a = true := fun n hn =>
          Chorus.reachable_voted_implies_cast (r.reachable n) a
            ⟨ha, r.mono (P := fun st => st.local_voted a = true)
              (fun k hk => Chorus.local_voted.mono (r.steps k) a hk) (hvoted a ha) n hn⟩
        rcases Chorus.reachable_vote_cast_entries (r.reachable Nv) a J ⟨hcast Nv le_rfl, hJ⟩ with
          ⟨m, hsm⟩ | hsn
        · obtain ⟨k, hk, hck, hk'⟩ := r.withinFrom_of_bufferedFair (P := fun st => Received st i a J)
            (hTJ.rows (.receive_vote_pos i a J m) .net rfl (fun h => h)) (le_max_left _ _) hW
            (fun _ _ h => Or.inl ⟨m, receive_vote_pos_effect h⟩)
            (fun n hn _ hnot => ⟨ha, fun _ => enabled_receive_vote_pos hi hJ (hcast n hn)
              (r.mono (P := fun st => st.msg_vote_pos_sig a J m = true)
                (fun k hk => msg_vote_pos_sig_mono (r.steps k) a J m hk) hsm n hn)
              (fun m2 h => hnot (Or.inl ⟨m2, h⟩)) (fun h => hnot (Or.inr h))⟩)
            (fun _ _ _ _ => trivial)
          exact ⟨k, hk, hck, fun _ => hk'⟩
        · obtain ⟨k, hk, hck, hk'⟩ := r.withinFrom_of_bufferedFair (P := fun st => Received st i a J)
            (hTJ.rows (.receive_vote_neg i a J) .net rfl (fun h => h)) (le_max_left _ _) hW
            (fun _ _ h => Or.inr (receive_vote_neg_effect h))
            (fun n hn _ hnot => ⟨ha, fun _ => enabled_receive_vote_neg hi hJ (hcast n hn)
              (r.mono (P := fun st => st.msg_vote_neg_sig a J = true)
                (fun k hk => msg_vote_neg_sig_mono (r.steps k) a J hk) hsn n hn)
              (fun m2 h => hnot (Or.inl ⟨m2, h⟩)) (fun h => hnot (Or.inr h))⟩)
            (fun _ _ _ _ => trivial)
          exact ⟨k, hk, hck, fun _ => hk'⟩
      · exact ⟨Nv, le_rfl, le_trans hcv hB, fun h => absurd h hm⟩)
  exact ⟨N, hN, hc, fun a ha => hall a (by simp) ha⟩

/-- **Milestone: a fallback signature per proposer, by `M + 2Δ + 2δ`**,
unless the validator has already cast its second-round vote. From the index
`Nv` at which the honest quorum `qv` and `i` have voted (by `M + Δ + δ`),
with the fallback arm open by `D + Δ ≤ M + 2Δ`. The honest quorum's votes
are frozen (`vote_pos_sig_frozen`), so the case split is made at `Nv`:
positive evidence among them makes `fb_sign_pos` owed and enabled
throughout, a `Δ`-row on those votes, by `M + 2Δ + δ`; its absence is
`fb_sign_neg`'s guard over the votes `i` has received (by `M + 2Δ + δ`,
`within_received`), each of which is the sender's signed entry
(`vote_rcv_pos_backed`), and `fb_sign_neg` is a `δ`-row on `i`'s own
receipts, by `M + 2Δ + 2δ`. -/
theorem within_fb_sig [Fintype node] (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r) {t : time}
    (hD : sch.D ≤ t + sch.Δ) {N₀ : Nat}
    (hact : ActiveUntil r N₀ (max t r.gst + 2 • sch.Δ + 2 • sch.δ))
    {qv : nodeset} (hqv : nset.supermajority qv)
    (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true)
    {Nv : Nat} (hNv : N₀ ≤ Nv) (hcv : r.clk Nv ≤ max t r.gst + sch.Δ + sch.δ)
    (hvoted : ∀ a, ¬ nset.is_byz a = true → (r.at' Nv).local_voted a = true)
    {i : node} (hi : ¬ nset.is_byz i = true) {J : node} (hJ : thS.is_proposer J = true) :
    r.WithinFrom Nv (max t r.gst + 2 • sch.Δ + 2 • sch.δ) (fun st => FbSigOrCast st i J) := by
  mvba_inst
  obtain ⟨Nf, hNfc, hNf⟩ := reached_within sch hPP .fbArm
  set M := max t r.gst with hMdef
  have hg : r.gst ≤ M := le_max_right _ _
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have hB1 : M + 2 • sch.Δ + sch.δ ≤ M + 2 • sch.Δ + 2 • sch.δ := by
    rw [two_nsmul sch.δ, ← add_assoc]; exact le_add_nn hδ
  -- The window.
  have hrefv : r.ref Nv ≤ M + sch.Δ + sch.δ :=
    r.ref_le hcv (le_trans hg (by rw [add_assoc]; exact le_add_nn (add_nonneg hΔ hδ)))
  have hcf : r.clk Nf ≤ M + 2 • sch.Δ := by
    mvba_inst
    refine le_trans hNfc ?_
    show sch.D + sch.Δ ≤ M + 2 • sch.Δ
    calc sch.D + sch.Δ ≤ t + sch.Δ + sch.Δ := by gcongr
      _ ≤ M + sch.Δ + sch.Δ := by gcongr; exact le_max_left _ _
      _ = M + 2 • sch.Δ := by rw [two_nsmul, add_assoc]
  have hcv' : r.clk Nv ≤ M + 2 • sch.Δ := le_trans hcv (by
    rw [two_nsmul, ← add_assoc]; exact add_le_add le_rfl sch.δ_le_Δ)
  -- What a validator that has not reached the goal satisfies.
  have hstuck : ∀ n, ¬ FbSigOrCast (r.at' n) i J →
      ¬ (r.at' n).msg_commit_cast i = true ∧
      ¬ (r.at' n).local_path i = PathChoice_EnumClass.fallback ∧
      ¬ (r.at' n).local_fb_entry i J = true := fun n hnot =>
    ⟨fun h => hnot (Or.inr (Or.inr (Or.inl h))),
     fun h => hnot (Or.inr (Or.inr (Or.inr (path_fallback_sig r.toLRun n h)))),
     fun h => hnot (by
      rcases fb_entry_sigs r.toLRun n h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))⟩
  have hvi : ∀ n, Nv ≤ n → (r.at' n).local_voted i = true := fun n hn =>
    r.mono (P := fun st => st.local_voted i = true)
      (fun k hk => Chorus.local_voted.mono (r.steps k) i hk) (hvoted i hi) n hn
  have hcast : ∀ n, Nv ≤ n → ∀ a, nset.member a qv = true → (r.at' n).msg_vote_cast a = true :=
    fun n hn a ha => Chorus.reachable_voted_implies_cast (r.reachable n) a
      ⟨hqvh a ha, r.mono (P := fun st => st.local_voted a = true)
        (fun k hk => Chorus.local_voted.mono (r.steps k) a hk) (hvoted a (hqvh a ha)) n hn⟩
  by_cases hpos : ∃ M0 q, nset.greater_than_third q ∧
      (∀ a, nset.member a q = true → nset.member a qv = true ∧ (r.at' Nv).msg_vote_pos_sig a J M0 = true) ∧
      thS.well_encoded M0 = true
  · -- Positive evidence among the honest quorum's votes: `fb_sign_pos`.
    obtain ⟨M0, q, hq1, hq2, hwe⟩ := hpos
    have hQ : Mvba.CorrectQuorum (node := node) q := fun a ha => hqvh a (hq2 a ha).1
    have hsig : ∀ n, Nv ≤ n → ∀ a, nset.member a q = true → (r.at' n).msg_vote_pos_sig a J M0 = true :=
      fun n hn a ha => r.mono (P := fun st => st.msg_vote_pos_sig a J M0 = true)
        (fun k hk => msg_vote_pos_sig_mono (r.steps k) a J M0 hk) (hq2 a ha).2 n hn
    have hrefN' : r.ref (max Nv Nf) ≤ M + 2 • sch.Δ :=
      r.ref_le (r.clk_max_le' hcv' hcf) (le_trans hg (le_add_nn (nsmul_nonneg hΔ 2)))
    have hW : r.bufWindow Nv (max Nv Nf) sch.Δ sch.δ ≤ M + 2 • sch.Δ + 2 • sch.δ := by
      mvba_inst
      refine le_trans (r.bufWindow_le ?_ (by gcongr)) hB1
      calc r.ref Nv + sch.Δ ≤ M + sch.Δ + sch.δ + sch.Δ := by gcongr
        _ = M + 2 • sch.Δ + sch.δ := by rw [two_nsmul]; abel
    refine r.withinFrom_of_bufferedFair (hTJ.rows (.fb_sign_pos i J M0 q) .net rfl (fun h => h))
      (le_max_left _ _) hW (fun _ _ h => Or.inl ⟨M0, fb_sign_pos_effect h⟩)
      (fun n hn hc hnot => ⟨⟨hQ, qv, hqv, hqvh, hcast n hn⟩, fun hg => ?_⟩)
      (fun n hn hc _ => ⟨hact n (by omega) hc i hi, hNf n (by omega)⟩)
    obtain ⟨hnc, hnp, hnf⟩ := hstuck n hnot
    exact enabled_fb_sign_pos hi hg.1 hg.2 (hvi n hn) hnc hnp hJ hqv (hcast n hn) hq1 (hsig n hn)
      hwe hnf
  · -- None, and none ever appears among `i`'s receipts: each receipt is the
    -- sender's signed entry, frozen since `Nv`. `fb_sign_neg` once `i` holds
    -- an entry of every vote of `qv`.
    obtain ⟨Nr, hNr, hcr, hrcv⟩ := within_received sch hTJ hcv hvoted hqvh hi hJ
    have hrcv' : ∀ n, Nr ≤ n → ∀ a, nset.member a qv = true → Received (r.at' n) i a J :=
      fun n hn a ha => r.mono (P := fun st => Received st i a J)
        (fun k h => h.step (r.steps k)) (hrcv a ha) n hn
    have hnone : ∀ n, Nv ≤ n → ∀ M0 q, ¬ (nset.greater_than_third q ∧
        (∀ a, nset.member a q = true → nset.member a qv = true ∧ (r.at' n).local_vote_rcv_pos i a J M0 = true) ∧
        thS.well_encoded M0 = true) := by
      mvba_inst
      rintro n hn M0 q ⟨hq1, hq2, hwe⟩
      have hq2' : ∀ a, nset.member a q = true →
          nset.member a qv = true ∧ (r.at' Nv).msg_vote_pos_sig a J M0 = true := fun a ha =>
        ⟨(hq2 a ha).1, vote_pos_sig_frozen r.toLRun (hqvh a (hq2 a ha).1) hJ
          (hvoted a (hqvh a (hq2 a ha).1)) hn
          (Chorus.reachable_vote_rcv_pos_backed (r.reachable n) i a J M0 ⟨hi, (hq2 a ha).2⟩).2⟩
      exact hpos ⟨M0, q, hq1, hq2', hwe⟩
    have hrefr : r.ref Nr ≤ M + 2 • sch.Δ + sch.δ :=
      r.ref_le hcr (le_trans hg (by rw [add_assoc]; exact le_add_nn (add_nonneg (nsmul_nonneg hΔ 2) hδ)))
    have hrefN' : r.ref (max Nr Nf) ≤ M + 2 • sch.Δ + sch.δ :=
      r.ref_le (r.clk_max_le' hcr (le_trans hcf (le_add_nn hδ)))
        (le_trans hg (by rw [add_assoc]; exact le_add_nn (add_nonneg (nsmul_nonneg hΔ 2) hδ)))
    have hW : r.bufWindow Nr (max Nr Nf) sch.δ sch.δ ≤ M + 2 • sch.Δ + 2 • sch.δ := by
      mvba_inst
      have : M + 2 • sch.Δ + sch.δ + sch.δ = M + 2 • sch.Δ + 2 • sch.δ := by rw [two_nsmul sch.δ]; abel
      exact r.bufWindow_le (by rw [← this]; gcongr) (by rw [← this]; gcongr)
    obtain ⟨k, hk, hck, hk'⟩ := r.withinFrom_of_bufferedFair (P := fun st => FbSigOrCast st i J)
      (hTJ.rows (.fb_sign_neg i J qv) .loc rfl (fun h => h))
      (le_max_left _ _) hW (fun _ _ h => Or.inr (Or.inl (fb_sign_neg_effect h)))
      (fun n hn hc hnot => ⟨hqvh, fun hg => by
        obtain ⟨hnc, hnp, hnf⟩ := hstuck n hnot
        exact enabled_fb_sign_neg hi hg.1 hg.2 (hvi n (by omega)) hnc hnp hJ hqv (hrcv' n hn)
          (hnone n (by omega)) hnf⟩)
      (fun n hn hc _ => ⟨hact n (by omega) hc i hi, hNf n (by omega)⟩)
    exact ⟨k, by omega, hck, hk'⟩

/-- **Milestone: the second-round vote, fast or fallback, by `M + 2Δ + 3δ`.**
Every proposer has `i`'s fallback signature at one index by `M + 2Δ + 2δ`
(`within_fb_sig`, `withinFrom_forall`), unless `i` has already voted; then
`cast_fallback_vote` is a `δ`-row with the fallback arm as its gate. A
validator that casts its fast commit vote first has its second-round vote
all the same. -/
theorem within_cast [Fintype node] (sch : Schedule view time)
    {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r) {t : time}
    (hD : sch.D ≤ t + sch.Δ) {N₀ : Nat}
    (hact : ActiveUntil r N₀ (max t r.gst + 2 • sch.Δ + 3 • sch.δ))
    {qv : nodeset} (hqv : nset.supermajority qv)
    (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true)
    {Nv : Nat} (hNv : N₀ ≤ Nv) (hcv : r.clk Nv ≤ max t r.gst + sch.Δ + sch.δ)
    (hvoted : ∀ a, ¬ nset.is_byz a = true → (r.at' Nv).local_voted a = true)
    {i : node} (hi : ¬ nset.is_byz i = true) :
    r.WithinFrom Nv (max t r.gst + 2 • sch.Δ + 3 • sch.δ) (fun st => Cast st i) := by
  mvba_inst
  obtain ⟨Nf, hNfc, hNf⟩ := reached_within sch hPP .fbArm
  set M := max t r.gst with hMdef
  have hg : r.gst ≤ M := le_max_right _ _
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have h32 : M + 2 • sch.Δ + 3 • sch.δ = M + 2 • sch.Δ + 2 • sch.δ + sch.δ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel
  have hB1 : M + 2 • sch.Δ + 2 • sch.δ ≤ M + 2 • sch.Δ + 3 • sch.δ := by
    rw [h32]; exact le_add_nn hδ
  have hcv1 : r.clk Nv ≤ M + 2 • sch.Δ + 2 • sch.δ := le_trans hcv (by
    rw [two_nsmul, two_nsmul]; gcongr <;> exact le_add_nn (by assumption))
  obtain ⟨Ns, hNs, hcs, hall⟩ := r.withinFrom_forall
    (fun J st => thS.is_proposer J = true → FbSigOrCast st i J)
    (fun J k h hJ => (h hJ).step) Nv (M + 2 • sch.Δ + 2 • sch.δ) hcv1
    (Finset.univ : Finset node).toList
    (fun J _ => by
      by_cases hJ : thS.is_proposer J = true
      · obtain ⟨k, hk, hck, hk'⟩ := within_fb_sig sch hTJ hPP hD (hact.mono hB1) hqv hqvh hNv hcv
          hvoted hi hJ
        exact ⟨k, hk, hck, fun _ => hk'⟩
      · exact ⟨Nv, le_rfl, hcv1, fun h => absurd h hJ⟩)
  by_cases hdone : Cast (r.at' Ns) i
  · exact ⟨Ns, hNs, le_trans hcs hB1, hdone⟩
  have hsigs : ∀ J, thS.is_proposer J = true →
      (∃ m, (r.at' Ns).msg_fb_pos_sig i J m = true) ∨ (r.at' Ns).msg_fb_neg_sig i J = true :=
    fun J hJ => by
      rcases hall J (by simp) hJ with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (Or.inl h) hdone
      · exact absurd (Or.inr h) hdone
  have hsigs' : ∀ n, Ns ≤ n → ∀ J, thS.is_proposer J = true →
      (∃ m, (r.at' n).msg_fb_pos_sig i J m = true) ∨ (r.at' n).msg_fb_neg_sig i J = true :=
    r.mono (P := fun st => ∀ J, thS.is_proposer J = true →
        (∃ m, st.msg_fb_pos_sig i J m = true) ∨ st.msg_fb_neg_sig i J = true)
      (fun k h J hJ => (h J hJ).imp (fun ⟨m, hm⟩ => ⟨m, Chorus.msg_fb_pos_sig.mono (r.steps k) i J m hm⟩)
        (Chorus.msg_fb_neg_sig.mono (r.steps k) i J)) hsigs
  have hcf : r.clk Nf ≤ M + 2 • sch.Δ + 2 • sch.δ := by
    mvba_inst
    refine le_trans hNfc ?_
    show sch.D + sch.Δ ≤ M + 2 • sch.Δ + 2 • sch.δ
    calc sch.D + sch.Δ ≤ t + sch.Δ + sch.Δ := by gcongr
      _ ≤ M + sch.Δ + sch.Δ := by gcongr; exact le_max_left _ _
      _ = M + 2 • sch.Δ := by rw [two_nsmul, add_assoc]
      _ ≤ M + 2 • sch.Δ + 2 • sch.δ := le_add_nn (nsmul_nonneg hδ 2)
  have hrefs : r.ref Ns ≤ M + 2 • sch.Δ + 2 • sch.δ :=
    r.ref_le hcs (le_trans hg (by
      rw [add_assoc]; exact le_add_nn (add_nonneg (nsmul_nonneg hΔ 2) (nsmul_nonneg hδ 2))))
  have hrefN' : r.ref (max Ns Nf) ≤ M + 2 • sch.Δ + 2 • sch.δ :=
    r.ref_le (r.clk_max_le' hcs hcf) (le_trans hg (by
      rw [add_assoc]; exact le_add_nn (add_nonneg (nsmul_nonneg hΔ 2) (nsmul_nonneg hδ 2))))
  have hW : r.bufWindow Ns (max Ns Nf) sch.δ sch.δ ≤ M + 2 • sch.Δ + 3 • sch.δ :=
    r.bufWindow_le (by rw [h32]; gcongr) (by rw [h32]; gcongr)
  obtain ⟨k, hk, hck, hkP⟩ := r.withinFrom_of_bufferedFair (P := fun st => Cast st i)
    (hTJ.rows (.cast_fallback_vote i) .loc rfl (fun h => h)) (le_max_left _ _) hW (fun _ _ h => Or.inr (cast_fallback_vote_effect h))
    (fun n hn hc hnot => ⟨trivial, fun hg => enabled_cast_fallback_vote hi hg.1 hg.2
      (r.mono (P := fun st => st.local_voted i = true)
        (fun k hk => Chorus.local_voted.mono (r.steps k) i hk) (hvoted i hi) n (by omega))
      (fun h => hnot (Or.inl h))
      (fun h => hnot (Or.inr (path_fallback_sig r.toLRun n h))) (hsigs' n hn)⟩)
    (fun n hn hc _ => ⟨hact n (by omega) hc i hi, hNf n (by omega)⟩)
  exact ⟨k, by omega, hck, hkP⟩

/-- **Milestone: every correct validator saturated, at one index, by
`M + 2Δ + 3δ`**: the first-round votes (`within_all_voted`), then each
second-round vote (`within_cast`), collapsed; a cast carries its signatures
(`saturated_of_cast`). This is the timed `eventually_all_saturated`. -/
theorem within_all_saturated [Fintype node] (sch : Schedule view time)
    {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r) {t : time}
    (hD : sch.D ≤ t + sch.Δ) {N₀ : Nat} (hN₀ : r.clk N₀ ≤ t)
    (hact : ActiveUntil r N₀ (max t r.gst + 2 • sch.Δ + 3 • sch.δ))
    {qv : nodeset} (hqv : nset.supermajority qv)
    (hqvh : ∀ a, nset.member a qv = true → ¬ nset.is_byz a = true) :
    r.WithinFrom N₀ (max t r.gst + 2 • sch.Δ + 3 • sch.δ)
      (fun st => ∀ i, ¬ nset.is_byz i = true →
        Saturated thS st i) := by
  mvba_inst
  set M := max t r.gst with hMdef
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have hB : M + sch.Δ + sch.δ ≤ M + 2 • sch.Δ + 3 • sch.δ := by
    mvba_inst
    rw [two_nsmul, show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, two_nsmul]
    gcongr
    · exact le_add_nn hΔ
    · exact le_add_of_nonneg_left (add_nonneg hδ hδ)
  obtain ⟨Nv, hNv, hcv, hvoted⟩ := within_all_voted sch hTJ hPP hD hN₀ (hact.mono hB)
  obtain ⟨Ns, hNs, hcs, hall⟩ := r.withinFrom_forall
    (fun i st => ¬ nset.is_byz i = true → Cast st i)
    (fun i k h hi => (h hi).step) Nv (M + 2 • sch.Δ + 3 • sch.δ) (le_trans hcv hB)
    (Finset.univ : Finset node).toList
    (fun i _ => by
      by_cases hi : nset.is_byz i = true
      · exact ⟨Nv, le_rfl, le_trans hcv hB, fun h => absurd hi h⟩
      · obtain ⟨k, hk, hck, hk'⟩ := within_cast sch hTJ hPP hD hact hqv hqvh hNv hcv
          (fun a ha => (hvoted a ha).1) hi
        exact ⟨k, hk, hck, fun _ => hk'⟩)
  exact ⟨Ns, by omega, hcs, fun i hi => saturated_of_cast hi (hall i (by simp) hi)⟩

/-! ### The MVBA's trigger, the FastQCs, and the proposals -/

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **At saturation the MVBA's trigger holds from correct senders**
(`CorrectTrigger`), as in the untimed `eventually_mvba_route`: some correct
validator cast its fast commit vote — then it holds a complete fast
meta-block (its commit signatures come from its FastQCs) — or none did, and
the honest quorum `H` all cast fallback votes, a correct `FBCert`. -/
theorem correctTrigger_of_saturated {r : TChorusRun thS thM time} {N : Nat}
    {H : nodeset} (hH : nset.supermajority H)
    (hHh : ∀ a, nset.member a H = true → ¬ nset.is_byz a = true)
    (hsat : ∀ i, ¬ nset.is_byz i = true → Saturated thS (r.at' N) i) :
    CorrectTrigger (nset := nset) (mvba := Mvba.mvbaSafety thM) thS (r.at' N) := by
  mvba_inst
  by_cases hexfast : ∃ i0, ¬ nset.is_byz i0 = true ∧ (r.at' N).msg_commit_cast i0 = true
  · obtain ⟨i0, hi0, hcast⟩ := hexfast
    refine Or.inr ⟨i0, hi0, hcast, ?_⟩
    unfold Chorus.complete_fast_metablock
    intro j hj
    rcases commit_cast_sigs r.toLRun hi0 N hcast j hj with ⟨m, hp⟩ | hn
    · exact Or.inl ⟨m, Chorus.reachable_commit_pos_sig_from_local_fastqc (r.reachable N) i0 j m ⟨hi0, hp⟩⟩
    · exact Or.inr (Chorus.reachable_commit_neg_sig_from_local_fastqc (r.reachable N) i0 j ⟨hi0, hn⟩)
  · push Not at hexfast
    refine Or.inl ⟨H, hH, hHh, fun a ha => ?_⟩
    rcases hsat a (hHh a ha) with ⟨hc, -⟩ | ⟨hfb, -⟩
    · exact absurd hc (hexfast a (hHh a ha))
    · exact hfb

/-- **Milestone: a correct fast voter's FastQCs are adopted, by
`ref N + Δ`** (F7). If a correct validator `i0` that cast its fast commit
vote holds a complete fast meta-block at `N`, every correct validator holds
one by `ref N + Δ`: the same rule broadcast its `FastBlock`, so each
`aggregate_fastqc_*` is owed from `N` (no gate) and enabled, its vote quorum
being on the network (`local_fastqc_*_backed`). -/
theorem within_complete_fast_metablock [Fintype node] (sch : Schedule view time)
    {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) {N : Nat} {i0 : node} (hi0 : ¬ nset.is_byz i0 = true)
    (hcast0 : (r.at' N).msg_commit_cast i0 = true)
    (h0 : Chorus.complete_fast_metablock (nset := nset) (mvba := Mvba.mvbaSafety thM) i0 thS (r.at' N))
    {i : node} (hi : ¬ nset.is_byz i = true) :
    r.WithinFrom N (r.ref N + sch.Δ)
      (fun st => Chorus.complete_fast_metablock (nset := nset) (mvba := Mvba.mvbaSafety thM) i thS st) := by
  mvba_inst
  have hδΔ : sch.δ ≤ sch.Δ := sch.δ_le_Δ
  have hW : r.bufWindow N (max N N) sch.Δ sch.δ ≤ r.ref N + sch.Δ := by
    rw [max_self]; exact r.bufWindow_le le_rfl (add_le_add le_rfl hδΔ)
  have hcN : r.clk N ≤ r.ref N + sch.Δ :=
    le_trans (r.clk_le_ref N) (le_add_of_nonneg_right sch.mvba.Δ_pos.le)
  have hcast' : ∀ n, N ≤ n → (r.at' n).msg_commit_cast i0 = true :=
    fun n hn => r.mono (P := fun st => st.msg_commit_cast i0 = true)
      (fun k hk => Chorus.msg_commit_cast.mono (r.steps k) i0 hk) hcast0 n hn
  unfold Chorus.complete_fast_metablock at h0
  obtain ⟨M, hM, hcM, hall⟩ := r.withinFrom_forall
    (fun J st => thS.is_proposer J = true →
      (∃ m, st.local_fastqc_pos i J m = true) ∨ st.local_fastqc_neg i J = true)
    (fun J k h hJ => (h hJ).imp (fun ⟨m, hm⟩ => ⟨m, Chorus.local_fastqc_pos.mono (r.steps k) i J m hm⟩)
      (Chorus.local_fastqc_neg.mono (r.steps k) i J))
    N (r.ref N + sch.Δ) hcN (Finset.univ : Finset node).toList
    (fun J _ => by
      by_cases hJ : thS.is_proposer J = true
      · rcases h0 J hJ with ⟨m, hm⟩ | hm
        · obtain ⟨q, hq, hqs⟩ := Chorus.reachable_local_fastqc_pos_backed (r.reachable N) i0 J m ⟨hi0, hm⟩
          obtain ⟨k, hk, hck, hk'⟩ := r.withinFrom_of_bufferedFair
            (P := fun st => (∃ m, st.local_fastqc_pos i J m = true) ∨ st.local_fastqc_neg i J = true)
            (hTJ.rows (.aggregate_fastqc_pos i J m q) .net rfl (fun h => h)) (le_max_left _ _) hW
            (fun _ _ h => Or.inl ⟨m, aggregate_fastqc_pos_effect h⟩)
            (fun n hn _ hnot => ⟨Or.inr ⟨i0, hi0, hcast' n hn,
                r.mono (P := fun st => st.local_fastqc_pos i0 J m = true)
                  (fun k hk => Chorus.local_fastqc_pos.mono (r.steps k) i0 J m hk) hm n hn⟩,
              fun _ => enabled_aggregate_fastqc_pos hi hq (fun a ha =>
                r.mono (P := fun st => st.msg_vote_pos_sig a J m = true)
                  (fun k hk => msg_vote_pos_sig_mono (r.steps k) a J m hk) (hqs a ha) n hn)
                (fun h => hnot (Or.inl ⟨m, h⟩))⟩)
            (fun _ _ _ _ => trivial)
          exact ⟨k, hk, hck, fun _ => hk'⟩
        · obtain ⟨q, hq, hqs⟩ := Chorus.reachable_local_fastqc_neg_backed (r.reachable N) i0 J ⟨hi0, hm⟩
          obtain ⟨k, hk, hck, hk'⟩ := r.withinFrom_of_bufferedFair
            (P := fun st => (∃ m, st.local_fastqc_pos i J m = true) ∨ st.local_fastqc_neg i J = true)
            (hTJ.rows (.aggregate_fastqc_neg i J q) .net rfl (fun h => h)) (le_max_left _ _) hW
            (fun _ _ h => Or.inr (aggregate_fastqc_neg_effect h))
            (fun n hn _ hnot => ⟨Or.inr ⟨i0, hi0, hcast' n hn,
                r.mono (P := fun st => st.local_fastqc_neg i0 J = true)
                  (fun k hk => Chorus.local_fastqc_neg.mono (r.steps k) i0 J hk) hm n hn⟩,
              fun _ => enabled_aggregate_fastqc_neg hi hq (fun a ha =>
                r.mono (P := fun st => st.msg_vote_neg_sig a J = true)
                  (fun k hk => msg_vote_neg_sig_mono (r.steps k) a J hk) (hqs a ha) n hn)
                (fun h => hnot (Or.inr h))⟩)
            (fun _ _ _ _ => trivial)
          exact ⟨k, hk, hck, fun _ => hk'⟩
      · exact ⟨N, le_rfl, hcN, fun h => absurd h hJ⟩)
  refine ⟨M, hM, hcM, ?_⟩
  unfold Chorus.complete_fast_metablock
  exact fun J hJ => hall J (by simp) hJ

/-- **Milestone: the FastQCs at the deadline of the timeline, `M + 3Δ + 3δ`**:
`within_complete_fast_metablock` from a fast voter's index at or before the
second-round deadline `M + 2Δ + 3δ`. -/
theorem within_complete_fast_metablock_by [Fintype node] (sch : Schedule view time)
    {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) {t : time} {N : Nat}
    (hcN : r.clk N ≤ max t r.gst + 2 • sch.Δ + 3 • sch.δ)
    {i0 : node} (hi0 : ¬ nset.is_byz i0 = true)
    (hcast0 : (r.at' N).msg_commit_cast i0 = true)
    (h0 : Chorus.complete_fast_metablock (nset := nset) (mvba := Mvba.mvbaSafety thM) i0 thS (r.at' N))
    {i : node} (hi : ¬ nset.is_byz i = true) :
    r.WithinFrom N (max t r.gst + 3 • sch.Δ + 3 • sch.δ)
      (fun st => Chorus.complete_fast_metablock (nset := nset) (mvba := Mvba.mvbaSafety thM) i thS st) := by
  mvba_inst
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have hrefN : r.ref N ≤ max t r.gst + 2 • sch.Δ + 3 • sch.δ :=
    r.ref_le hcN (le_trans (le_max_right _ _) (by
      rw [add_assoc]; exact le_add_of_nonneg_right (add_nonneg (nsmul_nonneg hΔ 2) (nsmul_nonneg hδ 3))))
  refine (within_complete_fast_metablock sch hTJ hi0 hcast0 h0 hi).mono_time ?_
  calc r.ref N + sch.Δ ≤ max t r.gst + 2 • sch.Δ + 3 • sch.δ + sch.Δ := add_le_add hrefN le_rfl
    _ = max t r.gst + 3 • sch.Δ + 3 • sch.δ := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel

/-- **Milestone: the MVBA proposal on a correct `FBCert`, by `M + 3Δ + 3δ`**
(Algorithm 5, line 36 (`line:fb-mvba-propose`)). From an index `N` by the second-round deadline at
which a correct supermajority's fallback votes are on the network, the
proposal family for `i` and a vector `v` certified from `N` on and `Valid`
is a `Δ`-row on those votes whose gate — the MVBA arm — opens by
`D + 2Δ ≤ M + 3Δ`. Its guard "no input yet" lapses only by an input, which is
the goal. The certified vector and its validity are the bridge's (S4,
`certifiedVector`, `ValidBridge`'s soundness clause). -/
theorem within_input_of_fbcert (sch : Schedule view time)
    {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r) {t : time}
    (hD : sch.D ≤ t + sch.Δ) {N₀ : Nat}
    (hact : ActiveUntil r N₀ (max t r.gst + 3 • sch.Δ + 3 • sch.δ))
    {N : Nat} (hN : N₀ ≤ N) (hcN : r.clk N ≤ max t r.gst + 2 • sch.Δ + 3 • sch.δ)
    (hfb : CorrectFBCert (nset := nset) (r.at' N))
    {i : node} (hi : ¬ nset.is_byz i = true) {v : MetaBlock node merkle_root}
    (hcert : ∀ n, N ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) v)
    (hvalid : (Mvba.mvbaSafety (nset := nset) thM).Valid v) :
    r.WithinFrom N (max t r.gst + 3 • sch.Δ + 3 • sch.δ)
      (fun st => ∃ E, st.mvba_st.input i E = true) := by
  mvba_inst
  have hδΔ : sch.δ ≤ sch.Δ := sch.δ_le_Δ
  obtain ⟨Nm, hNmc, hNm⟩ := reached_within sch hPP .mvbaArm
  set M := max t r.gst with hMdef
  have hg : r.gst ≤ M := le_max_right _ _
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have h3 : M + 3 • sch.Δ + 3 • sch.δ = M + 2 • sch.Δ + 3 • sch.δ + sch.Δ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel
  have h3' : M + 3 • sch.Δ + 3 • sch.δ = M + 3 • sch.Δ + 2 • sch.δ + sch.δ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul _ 2 1, one_nsmul]; abel
  have hrefN : r.ref N ≤ M + 2 • sch.Δ + 3 • sch.δ :=
    r.ref_le hcN (le_trans hg (by
      rw [add_assoc]; exact le_add_of_nonneg_right (add_nonneg (nsmul_nonneg hΔ 2) (nsmul_nonneg hδ 3))))
  have hcN' : r.clk N ≤ M + 3 • sch.Δ + 2 • sch.δ := le_trans hcN (by
    calc M + 2 • sch.Δ + 3 • sch.δ = M + 2 • sch.Δ + 2 • sch.δ + sch.δ := by
          rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul _ 2 1, one_nsmul]; abel
      _ ≤ M + 2 • sch.Δ + 2 • sch.δ + sch.Δ := add_le_add le_rfl hδΔ
      _ = M + 3 • sch.Δ + 2 • sch.δ := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel)
  have hcm : r.clk Nm ≤ M + 3 • sch.Δ + 2 • sch.δ := by
    refine le_trans hNmc ?_
    show sch.D + 2 • sch.Δ ≤ M + 3 • sch.Δ + 2 • sch.δ
    calc sch.D + 2 • sch.Δ ≤ t + sch.Δ + 2 • sch.Δ := add_le_add hD le_rfl
      _ ≤ M + sch.Δ + 2 • sch.Δ := add_le_add (add_le_add (le_max_left _ _) le_rfl) le_rfl
      _ = M + 3 • sch.Δ := by rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel
      _ ≤ M + 3 • sch.Δ + 2 • sch.δ := le_add_of_nonneg_right (nsmul_nonneg hδ 2)
  have hrefN' : r.ref (max N Nm) ≤ M + 3 • sch.Δ + 2 • sch.δ :=
    r.ref_le (r.clk_max_le' hcN' hcm) (le_trans hg (by
      rw [add_assoc]; exact le_add_of_nonneg_right (add_nonneg (nsmul_nonneg hΔ 3) (nsmul_nonneg hδ 2))))
  have hW : r.bufWindow N (max N Nm) sch.Δ sch.δ ≤ M + 3 • sch.Δ + 3 • sch.δ :=
    r.bufWindow_le (by rw [h3]; exact add_le_add hrefN le_rfl) (by rw [h3']; exact add_le_add hrefN' le_rfl)
  have hfb' : ∀ n, N ≤ n → CorrectFBCert (nset := nset) (r.at' n) :=
    r.mono (P := fun st => CorrectFBCert (nset := nset) st) (fun k hk => correctFBCert_step (r.steps k) hk) hfb
  refine r.withinFrom_of_bufferedFairFamily (P := fun st => ∃ E, st.mvba_st.input i E = true)
    (hTJ.propose i v) (le_max_left _ _) hW
    (fun l ⟨mn, hl⟩ _ _ htr => by subst hl; exact ⟨v, Mvba.propose_effect_tr thM (mvba_propose_tr htr)⟩)
    (fun n hn _ hnot => ⟨hfb' n hn, fun hgate => ?_⟩)
    (fun n hn hc _ => ⟨hact n (by omega) hc i hi, hNm n (by omega)⟩)
  obtain ⟨st', hst'⟩ := enabled_propose_mvba (fun E h => hnot ⟨E, h⟩)
    (fun h => hgate.1.2 (abandoned_of_mvba_abandoned r.toLRun i n h)) hvalid
  obtain ⟨h1, h2, h3⟩ := hcert n hn
  exact ⟨_, ⟨st', rfl⟩, enabled_mvba_propose hi hgate.1
    (Or.inl ⟨fbcert_of_correct (hfb' n hn), Or.inr hgate.2⟩) h1 h2 h3 hst'⟩

/-! ### The proposer's chunk -/

omit [IsOrderedAddMonoid time] in
/-- **The phase is `pre_deadline` before the deadline** (P1): the phase
leaves `pre_deadline` only by its marker (`leave_pre_label`), which fires at
a clock at or after `D`, and the clock is monotone. -/
theorem phase_pre_of_lt (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hPP : PhasePunctual sch r) :
    ∀ n, r.clk n < sch.D → (r.at' n).phase = Phase_EnumClass.pre_deadline
  | 0, _ => by mvba_inst; exact Chorus.phase.init r.starts
  | n + 1, hc => by
    mvba_inst
    by_contra h
    have hn := phase_pre_of_lt sch hPP n (lt_of_le_of_lt (r.clk_mono n) hc)
    have hl := leave_pre_label (r.steps n) hn h
    have := (hPP .deadline).1 n hl
    exact absurd (lt_of_le_of_lt (le_trans this (r.clk_mono n)) hc) (lt_irrefl _)

/-- **Milestone: a chunk from a correct sender is recorded, `Δ` after it was
sent, if that is still before the deadline.** `record_chunk` is a `Δ`-row
with no gate, owed because the chunk's sender is correct, and the sender
sent it whatever it does next. It is enabled while the phase is
`pre_deadline` (`phase_pre_of_lt`, hence the strict `< D`) and `i` holds no
entry for the proposer — a negative entry would mean `i` had voted, past the
deadline. The strict inequality is the tie §6.4.2 of
[Bounds.md](../../docs/Bounds.md) records: a chunk due exactly at `D` ties
with the marker. -/
theorem within_entry_recorded (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r)
    {i : node} (hi : ¬ nset.is_byz i = true) {j : node} (hJ : thS.is_proposer j = true)
    {k : node} (hk : ¬ nset.is_byz k = true) {m : merkle_root} {Nd : Nat}
    (hc : (r.at' Nd).msg_chunk k i j m = true) (hs : (r.at' Nd).msg_proposer_signed j m = true)
    (hlt : r.ref Nd + sch.Δ < sch.D) :
    r.WithinFrom Nd (r.ref Nd + sch.Δ) (fun st => ∃ m', st.local_entry_pos i j m' = true) := by
  mvba_inst
  have hW : r.bufWindow Nd (max Nd Nd) sch.Δ sch.δ ≤ r.ref Nd + sch.Δ := by
    rw [max_self]; exact r.bufWindow_le le_rfl (add_le_add le_rfl sch.δ_le_Δ)
  have hc' : ∀ n, Nd ≤ n → (r.at' n).msg_chunk k i j m = true :=
    r.mono (P := fun st => st.msg_chunk k i j m = true)
      (fun n h => Chorus.msg_chunk.mono (r.steps n) k i j m h) hc
  refine r.withinFrom_of_bufferedFair (P := fun st => ∃ m', st.local_entry_pos i j m' = true)
    (hTJ.rows (.record_chunk i j m) .net rfl (fun h => h)) (le_max_left _ _) hW
    (fun _ _ h => ⟨m, record_chunk_effect h⟩)
    (fun n hn hcn hnot => ⟨⟨k, hk, hc' n hn⟩, fun _ => ?_⟩) (fun _ _ _ _ => trivial)
  have hpre := phase_pre_of_lt sch hPP n (lt_of_le_of_lt hcn hlt)
  refine enabled_record_chunk hi hJ ⟨k, hc' n hn⟩
    (r.mono (P := fun st => st.msg_proposer_signed j m = true)
      (fun k hk => Chorus.msg_proposer_signed.mono (r.steps k) j m hk) hs n hn)
    hpre (fun m2 h => hnot ⟨m2, h⟩) (fun h => ?_)
  have hv := Chorus.reachable_local_entry_neg_implies_voted (r.reachable n) i j ⟨hi, h⟩
  exact Chorus.reachable_voted_post_deadline (r.reachable n) i ⟨hi, hv⟩ hpre

/-- **Milestone: the proposal recorded**: if a correct proposer `j` signed
its root by `X`, it sent every validator its chunk in the same step
(`signed_chunks`), and every correct validator holds a positive entry for
`j` by `max(X, GST) + Δ`, provided that is before the deadline. -/
theorem within_proposal_recorded (sch : Schedule view time)
    {r : TChorusRun thS thM time} (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r)
    {j : node} (hj : ¬ nset.is_byz j = true) (hJ : thS.is_proposer j = true)
    {m : merkle_root} {Np : Nat} {X : time} (hcp : r.clk Np ≤ X)
    (hs : (r.at' Np).msg_proposer_signed j m = true)
    (hlt : max X r.gst + sch.Δ < sch.D)
    {i : node} (hi : ¬ nset.is_byz i = true) :
    r.WithinFrom Np (max X r.gst + sch.Δ) (fun st => ∃ m', st.local_entry_pos i j m' = true) := by
  mvba_inst
  have hrefp : r.ref Np ≤ max X r.gst := r.ref_le (le_trans hcp (le_max_left _ _)) (le_max_right _ _)
  exact (within_entry_recorded sch hTJ hPP hi hJ hj (signed_chunks r.toLRun hj Np hs i) hs
    (lt_of_le_of_lt (add_le_add hrefp le_rfl) hlt)).mono_time (add_le_add hrefp le_rfl)

/-! ### The case-(a) proposal, and every proposal -/

/-- **Milestone: the MVBA proposal on the proposer's own complete fast
meta-block, `δ` after it holds one** (Algorithm 5, line 23 (`line:fb-mvba-propose-fast`), the
`proposeFast` family, F9). From an index `N` at which `i` holds a FastQC for
every proposer — by `M + 3Δ + 3δ` on the timeline — the proposal is a
`δ`-row whose gate, the MVBA arm, opens by `D + 2Δ ≤ M + 3Δ`. -/
theorem within_input_of_fast (sch : Schedule view time)
    {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r) {t : time}
    (hD : sch.D ≤ t + sch.Δ) {N₀ : Nat}
    (hact : ActiveUntil r N₀ (max t r.gst + 3 • sch.Δ + 4 • sch.δ))
    {N : Nat} (hN : N₀ ≤ N) (hcN : r.clk N ≤ max t r.gst + 3 • sch.Δ + 3 • sch.δ)
    {i : node} (hi : ¬ nset.is_byz i = true)
    (hfq : Chorus.complete_fast_metablock (nset := nset) (mvba := Mvba.mvbaSafety thM) i thS (r.at' N))
    {v : MetaBlock node merkle_root}
    (hcert : ∀ n, N ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) v)
    (hvalid : (Mvba.mvbaSafety (nset := nset) thM).Valid v) :
    r.WithinFrom N (max t r.gst + 3 • sch.Δ + 4 • sch.δ)
      (fun st => ∃ E, st.mvba_st.input i E = true) := by
  mvba_inst
  obtain ⟨Nm, hNmc, hNm⟩ := reached_within sch hPP .mvbaArm
  set M := max t r.gst with hMdef
  have hg : r.gst ≤ M := le_max_right _ _
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have h3 : M + 3 • sch.Δ + 4 • sch.δ = M + 3 • sch.Δ + 3 • sch.δ + sch.δ := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, add_nsmul _ 3 1, one_nsmul]; abel
  have hpos : M ≤ M + 3 • sch.Δ + 3 • sch.δ := by
    rw [add_assoc]; exact le_add_of_nonneg_right (add_nonneg (nsmul_nonneg hΔ 3) (nsmul_nonneg hδ 3))
  have hcm : r.clk Nm ≤ M + 3 • sch.Δ + 3 • sch.δ := by
    refine le_trans hNmc ?_
    show sch.D + 2 • sch.Δ ≤ M + 3 • sch.Δ + 3 • sch.δ
    calc sch.D + 2 • sch.Δ ≤ t + sch.Δ + 2 • sch.Δ := add_le_add hD le_rfl
      _ ≤ M + sch.Δ + 2 • sch.Δ := add_le_add (add_le_add (le_max_left _ _) le_rfl) le_rfl
      _ = M + 3 • sch.Δ := by rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel
      _ ≤ M + 3 • sch.Δ + 3 • sch.δ := le_add_of_nonneg_right (nsmul_nonneg hδ 3)
  have hrefN : r.ref N ≤ M + 3 • sch.Δ + 3 • sch.δ := r.ref_le hcN (le_trans hg hpos)
  have hrefN' : r.ref (max N Nm) ≤ M + 3 • sch.Δ + 3 • sch.δ :=
    r.ref_le (r.clk_max_le' hcN hcm) (le_trans hg hpos)
  have hW : r.bufWindow N (max N Nm) sch.δ sch.δ ≤ M + 3 • sch.Δ + 4 • sch.δ :=
    r.bufWindow_le (by rw [h3]; exact add_le_add hrefN le_rfl) (by rw [h3]; exact add_le_add hrefN' le_rfl)
  have hfq' : ∀ n, N ≤ n →
      Chorus.complete_fast_metablock (nset := nset) (mvba := Mvba.mvbaSafety thM) i thS (r.at' n) :=
    r.mono (P := fun st => Chorus.complete_fast_metablock (nset := nset) (mvba := Mvba.mvbaSafety thM) i thS st)
      (fun k hk => complete_fast_metablock_step (r.steps k) hk) hfq
  refine r.withinFrom_of_bufferedFairFamily (P := fun st => ∃ E, st.mvba_st.input i E = true)
    (hTJ.proposeFast i v) (le_max_left _ _) hW
    (fun l ⟨mn, hl⟩ _ _ htr => by subst hl; exact ⟨v, Mvba.propose_effect_tr thM (mvba_propose_tr htr)⟩)
    (fun n hn _ hnot => ⟨hfq' n hn, fun hgate => ?_⟩)
    (fun n hn hc _ => ⟨hact n (by omega) hc i hi, hNm n (by omega)⟩)
  obtain ⟨st', hst'⟩ := enabled_propose_mvba (fun E h => hnot ⟨E, h⟩)
    (fun h => hgate.1.2 (abandoned_of_mvba_abandoned r.toLRun i n h)) hvalid
  obtain ⟨h1, h2, h3⟩ := hcert n hn
  exact ⟨_, ⟨st', rfl⟩, enabled_mvba_propose hi hgate.1
    (Or.inr ⟨hfq' n hn, hgate.2⟩) h1 h2 h3 hst'⟩

/-- **Milestone: every correct validator proposes to the MVBA, by
`t_M = M + 3Δ + 4δ`** — the paper's "by `M + 3Δ`: MVBA proposals", with the
local steps counted. From the index `Ns` at which every correct validator is
saturated (by `M + 2Δ + 3δ`, `within_all_saturated`), the MVBA's trigger
holds from correct senders (`correctTrigger_of_saturated`): either a correct
`FBCert`, and every correct validator proposes on it by `M + 3Δ + 3δ`
(`within_input_of_fbcert`); or a correct fast voter's complete meta-block,
whose FastQCs every correct validator adopts by `M + 3Δ + 3δ`
(`within_complete_fast_metablock_by`, F7) and proposes on `δ` later
(`within_input_of_fast`, F9). The vector `v` is certified from `Ns` on and
`Valid`: S4 supplies it (`certifiedVector` at the evidence, `ValidBridge`'s
soundness). -/
theorem within_all_input [Fintype node] (sch : Schedule view time)
    {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hPP : PhasePunctual sch r) {t : time}
    (hD : sch.D ≤ t + sch.Δ) {N₀ : Nat}
    (hact : ActiveUntil r N₀ (max t r.gst + 3 • sch.Δ + 4 • sch.δ))
    {H : nodeset} (hH : nset.supermajority H)
    (hHh : ∀ a, nset.member a H = true → ¬ nset.is_byz a = true)
    {Ns : Nat} (hNs : N₀ ≤ Ns) (hcs : r.clk Ns ≤ max t r.gst + 2 • sch.Δ + 3 • sch.δ)
    (hsat : ∀ i, ¬ nset.is_byz i = true → Saturated thS (r.at' Ns) i)
    {v : MetaBlock node merkle_root}
    (hcert : ∀ n, Ns ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) v)
    (hvalid : (Mvba.mvbaSafety (nset := nset) thM).Valid v)
    {i : node} (hi : ¬ nset.is_byz i = true) :
    r.WithinFrom Ns (max t r.gst + 3 • sch.Δ + 4 • sch.δ)
      (fun st => ∃ E, st.mvba_st.input i E = true) := by
  mvba_inst
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have h23 : max t r.gst + 3 • sch.Δ + 3 • sch.δ ≤ max t r.gst + 3 • sch.Δ + 4 • sch.δ :=
    add_le_add le_rfl (nsmul_le_nsmul_left hδ (by norm_num))
  rcases correctTrigger_of_saturated hH hHh hsat with hfb | ⟨i0, hi0, hcast0, h0⟩
  · exact (within_input_of_fbcert sch hTJ hPP hD (hact.mono h23) hNs hcs hfb hi hcert hvalid).mono_time h23
  · obtain ⟨Nf, hNf, hcf, hfq⟩ := within_complete_fast_metablock_by sch hTJ hcs hi0 hcast0 h0 hi
    obtain ⟨k, hk, hck, hk'⟩ := within_input_of_fast sch hTJ hPP hD hact (by omega) hcf hi hfq
      (fun n hn => hcert n (by omega)) hvalid
    exact ⟨k, by omega, hck, hk'⟩

end Timeline

end Chorus

/-! ## The pinned trust base

The standard Lean trio and nothing else — no `sorryAx`. -/

/--
info: 'Chorus.leave_pre_label' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.leave_pre_label

/--
info: 'Chorus.vote_pos_sig_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.vote_pos_sig_frozen

/--
info: 'Chorus.activeUntil_of_not_finalized' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.activeUntil_of_not_finalized

/--
info: 'Chorus.exists_start' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.exists_start

/--
info: 'Chorus.deadline_le_of_start' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.deadline_le_of_start

/--
info: 'Chorus.reached_within' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.reached_within

/--
info: 'Chorus.within_voted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_voted

/--
info: 'Chorus.within_all_voted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_all_voted

/--
info: 'Chorus.within_fb_sig' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_fb_sig

/--
info: 'Chorus.within_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_cast

/--
info: 'Chorus.within_all_saturated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_all_saturated

/--
info: 'Chorus.correctTrigger_of_saturated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.correctTrigger_of_saturated

/--
info: 'Chorus.within_complete_fast_metablock' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_complete_fast_metablock

/--
info: 'Chorus.within_complete_fast_metablock_by' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_complete_fast_metablock_by

/--
info: 'Chorus.within_input_of_fbcert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_input_of_fbcert

/--
info: 'Chorus.phase_pre_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.phase_pre_of_lt

/--
info: 'Chorus.within_received' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_received

/--
info: 'Chorus.signed_chunks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.signed_chunks

/--
info: 'Chorus.within_entry_recorded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_entry_recorded

/--
info: 'Chorus.within_proposal_recorded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_proposal_recorded

/--
info: 'Chorus.within_input_of_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_input_of_fast

/--
info: 'Chorus.within_all_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_all_input
