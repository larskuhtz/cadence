import Cadence.Chorus.Timeline

/-! # Chorus/TimedTermination — ℓ-termination, proven

[Bounds.md](../../docs/Bounds.md) §6.4.3, stage S4. The second timed claim of
[Schedule.lean](Schedule.lean), proven:

**`Chorus.timed_termination`** — `TimedTerminationClaim` at the paper's
bound `ℓ = 5Δ + ℓ_MVBA + 9δ` (`Lchorus`; Lemma 11
(`lemma:chorus-termination`), whose `5Δ + ℓ_MVBA` it is at `δ = 0`), for
every MVBA contract `T` at the fragment Chorus consumes whose latency
`T.ℓ` is non-negative; **`Chorus.timed_termination_atMvba`** is the same at
the system's MVBA, `T := Mvba.mvbaTemporal`, where that holds
(`mvbaSchedule_ℓ_nonneg`) and the MVBA instance's correct supermajority is
a theorem of the family (`hqeFin`).

## The milestones

From `M := max(t, GST)`, on the branch where no correct validator has
finalized by the vote deadline `X_v` — so none has abandoned (C1), and every
correct validator is active on the window (`activeUntil_of_not_finalized`).
Up to the proposals the milestones are [Timeline.lean](Timeline.lean)'s.

| milestone | lemma | by | `δ`s |
|---|---|---|---|
| every correct validator saturated | `within_all_saturated` | `M + 2Δ + 3δ` | 3 |
| every correct validator's MVBA proposal | `within_all_input` | `t_M = M + 3Δ + 4δ` | 4 |
| a FallbackQC signer's chunk, sent to every validator | `fb_pos_sig_at_cast`, `fb_pos_sig_chunks` | (saturation; its hop due `M + 3Δ + 3δ`) | 3 |
| every correct validator decides in the MVBA | `within_all_decided` (`T.termination`) | `X_d = t_M + ℓ_MVBA` | 4 |
| each correct validator's decision handled, entry by entry | `within_recorded` | `X_d + δ` | 5 |
| each correct validator's termination record `local_mvba_complete` | `within_complete` | `X_d + 2δ` | 6 |
| each fallback commit vote, under its own `B′` | `within_fbcommit_sig` | `X_v = X_d + 3δ` | 7 |
| the honest quorum's votes over the decided entries | (collapsed, the MVBA's agreement) | `X_v` | 7 |
| the finalizer's own fallback commit certificate | `within_fbcommitqc_sent` | `X_v + Δ` | 7 |
| every proposer's entry assigned | `within_assigned` | `X_v + 2Δ` | 7 |
| finalized | `within_finalized` | `T₀ = M + 5Δ + ℓ_MVBA + 8δ` | 8 |

`within_finalized_late` is that chain. Every message is acted on by its
receiver's own step, so the chain counts the vote receipts before the
negative fallback entry (a `δ`, [Timeline.lean](Timeline.lean)) and the
fallback commit certificate's two hops: formed from the votes, then
received.

**The split** (`within_finalized_split`) is made once, at `X_v`: a correct
validator that finalized by `X_v` gives everyone totality's `Δ + 2δ`
(`totality`), `M + 4Δ + ℓ_MVBA + 9δ`; otherwise the chain above finalizes
everyone by `T₀ = M + 5Δ + ℓ_MVBA + 8δ`. Both are within
`M + 5Δ + ℓ_MVBA + 9δ`, `Lchorus`: the `δ`-multiple fixed before the proof
stands. The paper's own split, at `T₀` with totality's `Δ` after it, would
now give one `Δ` more, so the split point is the vote deadline.

## What the round needs, and what it does not

* **No common `B′`** (P2 of [PaperAlignment.md](../../docs/PaperAlignment.md)
  §6). Each validator handles its own decision and casts its fallback commit
  vote under it, after the wait under that decision's FallbackQC entries;
  the votes sign entries only, which the MVBA's agreement makes one vector,
  and that is all the fbCommitQC and the assignments read.
* **The chunks arrive before the decision.** A FallbackQC entry of any
  correct decision has a correct signer, which signed before its own
  second-round vote (`fb_pos_sig_flip`: `fb_sign_pos` requires that the
  signer has not voted yet), so its signature is there at saturation, and
  it sent every validator its chunk in that same step
  (`fb_pos_sig_chunks`, Algorithm 5, line 12 (`line:fb-redisseminate`)). The
  vote's row is split at its trigger (`TimedJustice.fbCommit`): the chunks'
  hop is due `Δ` after saturation, before the decision, so the vote is `δ`
  after the decision.
* **The MVBA enters only through `T`**: `T.termination` on the projected
  timed run (`TimedMvbaAdmissible`), `T.ℓ`, and nothing of the MVBA's
  constants. Its three antecedents are Chorus's: the proposals by `t_M`
  (forward transfer), their validity (the MVBA's own `input_valid`), and no
  abandonment before `t_M + ℓ_MVBA` (the branch).
* **`0 ≤ T.ℓ`.** The claim is generic in `T`, and over a time type with
  negative elements a contract could state a negative latency, which would
  put the decision before the proposals' deadline on the time line. The two
  theorems take the latency's non-negativity as a hypothesis on `T`; the
  system's MVBA has it (`mvbaSchedule_ℓ_nonneg`), so the `…_atMvba` forms
  take nothing beyond the MVBA instance's own hypotheses, and not its
  correct supermajority, which the family proves (`hqeFin`).
* **Nothing new of the model**, and no Veil cell: plain Lean over the
  existing step lemmas and invariants.
* **At the system's MVBA the MVBA's clauses on its caller are derived.**
  The handoff from the decider's certificate broadcast and the handoff row
  (`relayed_of_timedJustice`, with `DecisionOutput` and the schedule's
  `δ ≤ ρ`), and (Δ-avail) from the availability row
  (`availWithin_of_timedJustice`, with the schedule's `Δ ≤ Δ_sync`).
  `timed_termination_atMvba` takes `SyncAtMvba`, whose MVBA premise is the
  MVBA's own two clauses. -/

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
/-- **A correct validator signs a positive fallback entry only before its
second-round vote**: the step that sets `msg_fb_pos_sig k j m` for a correct
`k` is `k`'s own `fb_sign_pos`, whose guards say `k` has cast no fast commit
vote and is not on the fallback path. -/
theorem fb_pos_sig_flip {l} {k j : node} {m : merkle_root}
    (htr : (RTS).tr th s l s') (hk : ¬ nset.is_byz k = true)
    (h0 : ¬ s.msg_fb_pos_sig k j m = true) (h1 : s'.msg_fb_pos_sig k j m = true) :
    ¬ s.msg_commit_cast k = true ∧ s.local_path k ≠ PathChoice_EnumClass.fallback := by
  cases l
  case fb_sign_pos i' j' m' q =>
    chorus_tr htr
    obtain ⟨-, -, -, -, -, hc, hp, -, -, -, -, -, -, rfl⟩ := htr
    chorus_field_simp
    by_cases hik : i' = k
    · subst hik
      exact ⟨hc, hp⟩
    · simp_all
  case byz_sign_fb_pos r' j' m' =>
    chorus_tr htr
    obtain ⟨hb, -, rfl⟩ := htr
    chorus_field_simp
    by_cases hrk : r' = k
    · subst hrk
      simp_all
    · simp_all
  frame_rest htr msg_fb_pos_sig hfr=> exact absurd (hfr ▸ h1) h0

end Steps

/-! ## The MVBA tail and the fallback commit round, with deadlines -/

section Round

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

omit [AddCommMonoid time] [IsOrderedAddMonoid time] in
/-- **A correct validator's positive fallback entry is there at its
second-round vote**: if `k` has cast its second-round vote at `Nc` and holds
a positive fallback signature at any index, it held it at `Nc` already. After
the vote no step sets it (`fb_pos_sig_flip`; a cast fallback vote puts `k` on
the fallback path, `fallback_sig_path_fallback`). -/
theorem fb_pos_sig_at_cast {r : TChorusRun thS thM time} {k J : node} {M : merkle_root}
    (hk : ¬ nset.is_byz k = true) {Nc : Nat} (hc : Cast (r.at' Nc) k) {n : Nat}
    (hs : (r.at' n).msg_fb_pos_sig k J M = true) : (r.at' Nc).msg_fb_pos_sig k J M = true := by
  mvba_inst
  by_contra h0
  rcases le_total n Nc with hle | hle
  · exact h0 (r.mono (P := fun st => st.msg_fb_pos_sig k J M = true)
      (fun m h => Chorus.msg_fb_pos_sig.mono (r.steps m) k J M h) hs Nc hle)
  · have hnot : ∀ m, Nc ≤ m → ¬ (r.at' m).msg_fb_pos_sig k J M = true := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact h0
      | succ m hm ih =>
        intro h1
        obtain ⟨hnc, hnp⟩ := fb_pos_sig_flip (r.steps m) hk ih h1
        have hcm : Cast (r.at' m) k :=
          r.mono (P := fun st => Cast st k) (fun j h => Cast.step (r := r) h) hc m hm
        rcases hcm with h | h
        · exact hnc h
        · exact hnp (Chorus.reachable_fallback_sig_path_fallback (r.reachable m) k ⟨hk, h⟩)
    exact hnot n hle hs

omit [IsOrderedAddMonoid time] in
/-- **Milestone: every correct validator decides in the MVBA, by
`t_M + ℓ_MVBA`** — the MVBA tail, through the contract. If every correct
validator has proposed to the MVBA by `t_M ≥ GST` and none has abandoned at
a clock up to `t_M + T.ℓ`, `T.termination` on the projection's timed run
(`TimedMvbaAdmissible`) decides every correct validator by
`max(t_M, GST) + T.ℓ = t_M + T.ℓ`, and the decision comes back to the
composed run at a clock no later (`Projection.timed_back`). The proposals
reach the projection by `Projection.timed_forward`; their validity is the
MVBA's own `input_valid` (its `propose` checks `valid`); an abandonment in
the MVBA is Chorus's `abandon` (`abandoned_of_mvba_abandoned`). -/
theorem within_all_decided
    (T : MVBATemporal node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset time nset (fun i => nset.is_byz i = true) (S := Mvba.mvbaSafety thM))
    {r : TChorusRun thS thM time} (hadm : TimedMvbaAdmissible T r) {tM : time}
    (hgst : r.gst ≤ tM)
    (hprop : ∀ i, ¬ nset.is_byz i = true →
      ∃ n, r.clk n ≤ tM ∧ ∃ E, (r.at' n).mvba_st.input i E = true)
    (hnab : ∀ i, ¬ nset.is_byz i = true → ∀ n, r.clk n ≤ tM + T.ℓ →
      ¬ (r.at' n).abandoned i = true)
    {q : node} (hq : ¬ nset.is_byz q = true) :
    ∃ n, r.clk n ≤ tM + T.ℓ ∧
      ∃ v, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st q v := by
  mvba_inst
  obtain ⟨p, hT⟩ := hadm
  have hmax : max tM (mvbaTimedRun p).gst = tM := max_eq_left hgst
  have h := T.termination (mvbaTimedRun p) hT tM
    (fun i hi => by
      obtain ⟨n, hc, E, hE⟩ := hprop i hi
      obtain ⟨k, hk, hP⟩ := p.timed_forward (P := fun st => st.input i E = true) hc hE
      exact ⟨k, hk, E, hP⟩)
    (fun i _ n v hv => Mvba.reachable_input_valid (p.run.reachable n) i v hv)
    (fun i hi n hab => by
      obtain ⟨h1, h2, h3⟩ := gstLub_iff.mpr hmax.symm
      refine ⟨tM, h1, h2, h3, fun hle => ?_⟩
      have hab' : (r.at' (p.entry n)).mvba_st.abandoned i = true := by
        have he : (r.at' (p.entry n)).mvba_st = p.run.at' n := (p.run_at'_entry n).symm
        rw [he]
        exact hab
      exact hnab i hi (p.entry n) hle (abandoned_of_mvba_abandoned r.toLRun i _ hab'))
    q hq
  rw [TimedRun.byGstBound_iff, hmax] at h
  obtain ⟨k, hk, v, hv⟩ := h
  obtain ⟨n, hn, hP⟩ := p.timed_back
    (P := fun st => (Mvba.mvbaSafety (nset := nset) thM).decided st q v) hk hv
  exact ⟨n, hn, v, hP⟩

/-- **Milestone: the decision handlers, `δ` after a correct decision.** From
an index `N` at which a correct validator `i` has decided `w`, it has handled
every proposer's entry of `w` by `ref N + δ`: each handler `on_mvba_decide_*`
is a `δ`-row with no gate, enabled — its bridge check is `ValidBridge`'s
completeness at the decision — until `i` has handled the entry, which is
the handler's own fired-once record. The handlers of different proposers run
in parallel (`withinFrom_forall`). -/
theorem within_recorded [Fintype node] (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hbr : ValidBridge r.toLRun) {N : Nat}
    {i : node} (hi : ¬ nset.is_byz i = true) {w : MetaBlock node merkle_root}
    (hd : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' N).mvba_st i w) :
    r.WithinFrom N (r.ref N + sch.δ)
      (fun st => ∀ J, thS.is_proposer J = true → st.local_mvba_recorded i J = true) := by
  mvba_inst
  have hdec := decided_persists r.toLRun hd
  have hcert : ∀ n, N ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) w :=
    r.mono (P := fun st => Certified (thS := thS) (thM := thM) st w)
      (fun n h => h.step (r.steps n)) (hbr.2.1 N i w hi hd)
  have hx : r.clk N ≤ r.ref N + sch.δ :=
    le_trans (r.clk_le_ref N) (le_add_of_nonneg_right sch.mvba.δ_nonneg)
  have hW : r.bufWindow N N sch.δ sch.δ ≤ r.ref N + sch.δ := r.bufWindow_le le_rfl le_rfl
  obtain ⟨n, hn, hc, hall⟩ := r.withinFrom_forall
    (fun J st => thS.is_proposer J = true → st.local_mvba_recorded i J = true)
    (fun J k h hJ => Chorus.local_mvba_recorded.mono (r.steps k) i J (h hJ)) N (r.ref N + sch.δ) hx
    (Finset.univ : Finset node).toList
    (fun J _ => by
      by_cases hJ : thS.is_proposer J = true
      · obtain ⟨-, -, hent⟩ := hcert N le_rfl
        rcases hent J hJ with ⟨M, hM⟩ | hM
        · obtain ⟨k, hk, hck, hP⟩ := r.withinFrom_of_bufferedFair
            (P := fun st => st.local_mvba_recorded i J = true)
            (hTJ.rows (.on_mvba_decide_pos i J M w) .loc rfl (fun h => h)) le_rfl hW
            (fun _ _ h => (on_mvba_decide_pos_effect h).2)
            (fun n hn _ hnr => ⟨trivial, fun _ => by
              obtain ⟨hp, -, -⟩ := hcert n hn
              exact enabled_on_mvba_decide_pos hi hJ (hdec n hn) hM (hp J M hM).2 hnr⟩)
            (fun _ _ _ _ => trivial)
          exact ⟨k, hk, hck, fun _ => hP⟩
        · obtain ⟨k, hk, hck, hP⟩ := r.withinFrom_of_bufferedFair
            (P := fun st => st.local_mvba_recorded i J = true)
            (hTJ.rows (.on_mvba_decide_neg i J w) .loc rfl (fun h => h)) le_rfl hW
            (fun _ _ h => (on_mvba_decide_neg_effect h).2)
            (fun n hn _ hnr => ⟨trivial, fun _ => by
              obtain ⟨-, hng, -⟩ := hcert n hn
              exact enabled_on_mvba_decide_neg hi hJ (hdec n hn) hM (hng J hM).2 hnr⟩)
            (fun _ _ _ _ => trivial)
          exact ⟨k, hk, hck, fun _ => hP⟩
      · exact ⟨N, le_rfl, hx, fun h => absurd h hJ⟩)
  exact ⟨n, hn, hc, fun J hJ => hall J (by simp) hJ⟩

omit [IsOrderedAddMonoid time] in
/-- **Milestone: the termination record, `δ` after the decision handlers.**
With every proposer's entry of a correct validator's decision handled at
`N`, its `mvba_terminate` is a `δ`-row with no gate, enabled until its own
`local_mvba_complete`. -/
theorem within_complete (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) {N : Nat}
    {i : node} (hi : ¬ nset.is_byz i = true) {w : MetaBlock node merkle_root}
    (hd : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' N).mvba_st i w)
    (hrec : ∀ J, thS.is_proposer J = true → (r.at' N).local_mvba_recorded i J = true) :
    r.WithinFrom N (r.ref N + sch.δ) (fun st => st.local_mvba_complete i = true) := by
  mvba_inst
  have hdec := decided_persists r.toLRun hd
  refine r.withinFrom_of_bufferedFair (hTJ.rows (.mvba_terminate i w) .loc rfl (fun h => h))
    le_rfl (r.bufWindow_le le_rfl le_rfl) (fun _ _ h => mvba_terminate_effect h)
    (fun n hn _ hnc => ⟨trivial, fun _ => enabled_mvba_terminate hi hnc (hdec n hn)
      (fun J hJ => r.mono (P := fun st => st.local_mvba_recorded i J = true)
        (fun m h => Chorus.local_mvba_recorded.mono (r.steps m) i J h) (hrec J hJ) n hn)⟩)
    (fun _ _ _ _ => trivial)

omit [IsOrderedAddMonoid time] in
/-- **Milestone: the fallback commit vote, `δ` after the termination record**
(Algorithm 5, line 41 (`line:fb-commitvote`)). `cast_fb_commit i w` is a
`Δ`-row split at its trigger (`TimedJustice.fbCommit`). Its message part is
the chunks sent to `i` under the positive `FallbackQC` entries of `w` (the
DA wait, Algorithm 5, line 39 (`line:fb-commit-wait`)), present from `Nc` on
and due `Δ` after it. Its gate is the trigger: from `N` on, `i` is active,
has decided `w`, its own `B′` and nothing else (the MVBA's integrity), and
holds its own `local_mvba_complete`. So the vote is cast by
`max(ref Nc + Δ, ref N + δ)`. No common `B′` is assumed: each validator
waits under its own decision. -/
theorem within_fbcommit_sig (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) {N₀ Nc N : Nat} (hN : N₀ ≤ N) (hNc : Nc ≤ N) {B : time}
    (hBc : r.ref Nc + sch.Δ ≤ B) (hB : r.ref N + sch.δ ≤ B) (hact : ActiveUntil r N₀ B)
    {i : node} (hi : ¬ nset.is_byz i = true) {w : MetaBlock node merkle_root}
    (hd : (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' N).mvba_st i w)
    (hc : (r.at' N).local_mvba_complete i = true)
    (hda : ∀ J M, thS.mval_pos (thM.ent w) J M = true → thS.mval_fb w J = true →
      Chorus.chunk_received (nset := nset) (mvba := Mvba.mvbaSafety thM) i J M thS (r.at' Nc)) :
    r.WithinFrom Nc B (fun st => ∃ e, st.msg_fbcommit_sig i e = true) := by
  mvba_inst
  have hdec := decided_persists r.toLRun hd
  refine r.withinFrom_of_bufferedFair (hTJ.fbCommit i w) hNc (r.bufWindow_le hBc hB)
    (fun _ _ h => ⟨_, cast_fb_commit_effect h⟩)
    (fun n hn _ hnv => ⟨trivial, fun hg => enabled_cast_fb_commit hi hg.1 hg.2.1 hg.2.2.2
        (fun J M hM hfb => r.mono
          (P := fun st => Chorus.chunk_received (nset := nset) (mvba := Mvba.mvbaSafety thM) i J M thS st)
          (fun m h => chunk_received_step (r.steps m) h) (hda J M hM hfb) n hn)
        (fun hf => hnv (fbcommit_voted_sig r.toLRun n hf))⟩)
    (fun n hn hcl _ => ⟨hact n (by omega) hcl i hi, hdec n hn, fun w' h => Mvba.reachable_integrity
        (Chorus.reachable_mvba_reachable (r.reachable n)) i w' w hi h (hdec n hn),
      r.mono (P := fun st => st.local_mvba_complete i = true)
        (fun m h => Chorus.local_mvba_complete.mono (r.steps m) i h) hc n hn⟩)

omit [IsOrderedAddMonoid time] in
/-- **Milestone: a correct validator's fallback commit certificate, `Δ` after
the votes** (Algorithm 5, lines 42–44
(`line:fb-collect-commit`–`line:fb-commit-broadcast`)). From an index `N` at
which a correct quorum `H`'s fallback commit votes over `e` are on the
network, `broadcast_fbcommitqc c e H` is a `Δ`-row owed on them (their
senders are correct), with `c`'s active participation as its gate (from its
participation at `P` on, until it finalizes, by C1), and enabled until `c`
has sent a certificate. So by any `B` bounding the buffered window, `c` has
sent a fallback commit certificate, or has finalized. -/
theorem within_fbcommitqc_sent (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hab : NoAbandonBeforeFinalizing r.toLRun)
    {c : node} (hc : ¬ nset.is_byz c = true) {e : node → Option merkle_root}
    {H : nodeset} (hH : nset.supermajority H)
    (hHh : ∀ a, nset.member a H = true → ¬ nset.is_byz a = true)
    {N P : Nat} (hvotes : ∀ a, nset.member a H = true → (r.at' N).msg_fbcommit_sig a e = true)
    (hP : (r.at' P).participating c = true) {B : time}
    (hB : r.bufWindow N (max N P) sch.Δ sch.δ ≤ B) :
    r.WithinFrom N B
      (fun st => (∃ e', st.msg_fbcommitqc c e' = true) ∨ st.local_committed c = true) := by
  mvba_inst
  have hvotes' : ∀ n, N ≤ n → ∀ a, nset.member a H = true → (r.at' n).msg_fbcommit_sig a e = true :=
    fun n hn a ha => r.mono (P := fun st => st.msg_fbcommit_sig a e = true)
      (fun k h => Chorus.msg_fbcommit_sig.mono (r.steps k) a e h) (hvotes a ha) n hn
  refine r.withinFrom_of_bufferedFair
    (hTJ.rows (.broadcast_fbcommitqc c e H) .net rfl (fun h => h)) (le_max_left _ _) hB
    (fun _ _ h => Or.inl ⟨e, broadcast_fbcommitqc_effect h⟩)
    (fun n hn _ hnot => ⟨hHh, fun hg => enabled_broadcast_fbcommitqc hc hg hH (hvotes' n hn)
      (fun hs => hnot (Or.inl (fbcommitqc_sent_msg r.toLRun n hs)))⟩)
    (fun n hn _ hnot => ⟨r.mono (P := fun st => st.participating c = true)
        (fun k hk => Chorus.participating.mono (r.steps k) c hk) hP n (by omega),
      fun h => hnot (Or.inr (hab c hc n h))⟩)

/-! ### The assembly -/

/-- The evidence at an index, in the proposals' form: every proposer has a
positive certificate (a FastQC, or a FallbackQC under `FBCert`) or a negative
one. `mvba_evidence_of_saturation` supplies it at saturation, at the concrete
quorum family. -/
def Evidence (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view)
    (st : StateAtMvba slot node nodeset merkle_root view Phase PathChoice) : Prop :=
  ∀ j, thS.is_proposer j = true →
    (∃ m, Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS st ∨
      (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) j m thS st ∧
        Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS st)) ∨
    (Chorus.vote_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS st ∨
      ((Chorus.fb_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS st ∨
        Chorus.equiv_evidence (nset := nset) (mvba := Mvba.mvbaSafety thM) j thS st) ∧
        Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS st))

set_option maxHeartbeats 4000000 in
/-- **The late branch: nobody finalized by the vote deadline, everyone
finalizes by `T₀ = M + 5Δ + ℓ_MVBA + 8δ`** (`M = max(t, GST)`), the timeline
of Proposition 5 (`prop:chorus-finalization-time`) with every local step counted.

If no correct validator has finalized at any index whose clock is at most
`X_v = M + 3Δ + ℓ_MVBA + 7δ`, none has abandoned there (C1), so every correct
validator is active on that window (`activeUntil_of_not_finalized`), and:

* every correct validator is saturated by `M + 2Δ + 3δ`
  (`within_all_saturated`), where the evidence certifies one vector `v` that
  is `Valid` (`ValidBridge`'s soundness), and proposes to the MVBA by
  `t_M = M + 3Δ + 4δ` (`within_all_input`);
* every correct validator decides in the MVBA by `X_d = t_M + ℓ_MVBA`
  (`within_all_decided`, nobody having abandoned);
* each handles every entry of its own decision by `X_d + δ`
  (`within_recorded`), and records its termination by `X_d + 2δ`
  (`within_complete`);
* every correct validator holds its chunk under each positive FallbackQC
  entry of its own decision by `M + 3Δ + 3δ`: the entry's FallbackQC has a
  correct signer, whose signature was there at its second-round vote
  (`fb_pos_sig_at_cast`), and it sent every validator its chunk when it
  signed (`fb_pos_sig_chunks`); the chunks' hop is due by `M + 3Δ + 3δ`;
* every correct validator casts its fallback commit vote under its own `B′`
  by `X_v = X_d + 3δ` (`within_fbcommit_sig`), over its decided entries,
  which agree (the MVBA's agreement), so the honest quorum's votes are on
  the network over one entry vector;
* the finalizing validator forms and sends its fallback commit certificate,
  a `Δ`-row on those votes, by `X_v + Δ` (`within_fbcommitqc_sent`), which is
  over the decided entries (`fbcommitqc_decided`);
* each assignment is then a `Δ`-row owed on that certificate, from a correct
  sender, by `X_v + 2Δ` (`within_assigned`), and the finalization a `δ`-row,
  by `X_v + 2Δ + δ = T₀` (`within_finalized`). The last three use only the
  finalizing validator's own gate: it is active until it finalizes (C1).

`0 ≤ ℓ_MVBA` orders the MVBA's decision after the proposals' deadline on the
time line; it is a fact about the MVBA instance, and true of the system's
(`mvbaTemporal_ℓ_nonneg`). -/
theorem within_finalized_late [Fintype node] (sch : Schedule view time)
    (T : MVBATemporal node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset time nset (fun i => nset.is_byz i = true) (S := Mvba.mvbaSafety thM))
    (hℓ : 0 ≤ T.ℓ)
    (hmp : ∀ (e : node → Option merkle_root) j m, thS.mval_pos e j m = true ↔ e j = some m)
    (hmn : ∀ (e : node → Option merkle_root) j,
      thS.mval_neg e j = true ↔ e j = none ∧ thS.is_proposer j = true)
    (hent : ∀ v, thM.ent v = MetaBlock.entries v)
    (hmf : ∀ v j, thS.mval_fb v j = true ↔ (v j).map Prod.snd = some CertKind.fallbackQC)
    {H : nodeset} (hH : nset.supermajority H)
    (hHh : ∀ a, nset.member a H = true → ¬ nset.is_byz a = true)
    {r : TChorusRun thS thM time}
    (hevid : ∀ N, (∀ i, ¬ nset.is_byz i = true → Saturated thS (r.at' N) i) →
      Evidence thS thM (r.at' N))
    (hsync : Sync sch T r) (hbr : ValidBridge r.toLRun)
    (hab : NoAbandonBeforeFinalizing r.toLRun) (hC2 : NoEarlyStart sch r)
    {t : time} {N₀ : Nat} (hN₀ : r.clk N₀ ≤ t)
    (hpart : ∀ i, ¬ nset.is_byz i = true → (r.at' N₀).participating i = true)
    (hnf : ∀ n i, ¬ nset.is_byz i = true →
      r.clk n ≤ max t r.gst + 3 • sch.Δ + 4 • sch.δ + T.ℓ + 3 • sch.δ →
        ¬ (r.at' n).local_committed i = true)
    {j : node} (hj : ¬ nset.is_byz j = true) :
    ∃ n, r.clk n ≤ max t r.gst + 5 • sch.Δ + T.ℓ + 8 • sch.δ ∧
      (r.at' n).local_committed j = true := by
  mvba_inst
  obtain ⟨hTJ, hPP, hadm⟩ := hsync
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have hδΔ : sch.δ ≤ sch.Δ := sch.δ_le_Δ
  set M := max t r.gst with hMdef
  have hgM : r.gst ≤ M := le_max_right _ _
  -- The time line's points, and their order.
  set P2 := M + 2 • sch.Δ + 3 • sch.δ with hP2
  set P3 := M + 3 • sch.Δ + 3 • sch.δ with hP3
  set tM := M + 3 • sch.Δ + 4 • sch.δ with htM
  set Xd := tM + T.ℓ with hXd
  set Xv := Xd + 3 • sch.δ with hXv
  have hMP2 : M ≤ P2 := by
    rw [hP2, add_assoc]; exact le_add_of_nonneg_right (add_nonneg (nsmul_nonneg hΔ 2) (nsmul_nonneg hδ 3))
  have hP2P3 : P2 ≤ P3 := by
    rw [hP2, hP3]; exact add_le_add (add_le_add le_rfl (nsmul_le_nsmul_left hΔ (by norm_num))) le_rfl
  have hP3tM : P3 ≤ tM := by
    rw [hP3, htM]; exact add_le_add le_rfl (nsmul_le_nsmul_left hδ (by norm_num))
  have htMXd : tM ≤ Xd := le_add_of_nonneg_right hℓ
  have hXd1 : Xd ≤ Xd + sch.δ := le_add_of_nonneg_right hδ
  have hXd2 : Xd + sch.δ ≤ Xd + 2 • sch.δ := by
    refine add_le_add le_rfl ?_; rw [two_nsmul]; exact le_add_of_nonneg_right hδ
  have hXd3 : Xd + 2 • sch.δ + sch.δ = Xv := by
    rw [hXv]; abel
  have hXdXv : Xd + 2 • sch.δ ≤ Xv := by rw [← hXd3]; exact le_add_of_nonneg_right hδ
  have hP3Xv : P3 ≤ Xv := le_trans hP3tM (le_trans htMXd (le_trans hXd1 (le_trans hXd2 hXdXv)))
  have hgXv : r.gst ≤ Xv := le_trans hgM (le_trans hMP2 (le_trans hP2P3 hP3Xv))
  have hsat_le : P2 ≤ Xv := le_trans hP2P3 hP3Xv
  have hnfv : ∀ n i, ¬ nset.is_byz i = true → r.clk n ≤ Xv → ¬ (r.at' n).local_committed i = true :=
    fun n i hi hc => hnf n i hi hc
  -- The gate: everyone active until `X_v`.
  have hact : ActiveUntil r N₀ Xv := activeUntil_of_not_finalized hpart hab hnfv
  obtain ⟨i0, hH0, hi0⟩ := ByzNodeSet.greater_than_third_one_honest H
    (ByzNodeSet.supermajority_greater_than_third _ hH)
  have hi0 : ¬ nset.is_byz i0 = true := hHh i0 hH0
  have hD : sch.D ≤ t + sch.Δ := deadline_le_of_start sch hC2 hN₀ hi0 (hpart i0 hi0)
  -- Saturation, the evidence, one certified and valid vector.
  obtain ⟨Ns, hNs, hcs, hsat⟩ := within_all_saturated sch hTJ hPP hD hN₀ (hact.mono hsat_le) hH hHh
  set v := certifiedVector thS thM (r.at' Ns) with hv
  have hcert : ∀ n, Ns ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) v :=
    r.mono (P := fun st => Certified (thS := thS) (thM := thM) st v)
      (fun n h => h.step (r.steps n)) (certified_certifiedVector hmp hmn hent hmf (hevid Ns hsat))
  have hvalid := hbr.1 Ns v (hcert Ns le_rfl)
  -- Every correct validator proposes to the MVBA by `t_M`.
  have hprop : ∀ i, ¬ nset.is_byz i = true →
      ∃ n, r.clk n ≤ tM ∧ ∃ E, (r.at' n).mvba_st.input i E = true := fun i hi => by
    obtain ⟨n, -, hc, hE⟩ := within_all_input sch hTJ hPP hD
      (hact.mono ((le_trans htMXd (le_trans hXd1 (le_trans hXd2 hXdXv)))))
      hH hHh hNs hcs hsat hcert hvalid hi
    exact ⟨n, hc, hE⟩
  -- Every correct validator decides by `X_d`.
  have hdec : ∀ q, ¬ nset.is_byz q = true → ∃ n, r.clk n ≤ Xd ∧
      ∃ w, (Mvba.mvbaSafety (nset := nset) thM).decided (r.at' n).mvba_st q w :=
    fun q hq => within_all_decided T hadm (le_trans hgM (le_trans hMP2 (le_trans hP2P3 hP3tM))) hprop
      (fun i hi n hc ha => hnfv n i hi (le_trans hc (le_trans hXd1 (le_trans hXd2 hXdXv)))
        (hab i hi n ha)) hq
  have hrefle : ∀ {n : Nat} {X : time}, r.clk n ≤ X → r.gst ≤ X → r.ref n ≤ X :=
    fun hc hg => r.ref_le hc hg
  have hgXd : r.gst ≤ Xd := le_trans hgM (le_trans hMP2 (le_trans hP2P3 (le_trans hP3tM htMXd)))
  have hgXd2 : r.gst ≤ Xd + 2 • sch.δ := le_trans hgXd (le_trans hXd1 hXd2)
  -- `i0`'s decision, whose entries every correct decision has.
  obtain ⟨n0, hc0, v0, hd0⟩ := hdec i0 hi0
  have hd0' := decided_persists r.toLRun hd0
  -- Every correct validator's fallback commit vote over `entries(v0)`, by `X_v`.
  have hvote : ∀ i, ¬ nset.is_byz i = true →
      ∃ n, Ns ≤ n ∧ r.clk n ≤ Xv ∧ (r.at' n).msg_fbcommit_sig i (thM.ent v0) = true := by
    intro i hi
    obtain ⟨ni, hci, w, hdw⟩ := hdec i hi
    have hdw' := decided_persists r.toLRun hdw
    -- `i` handles its own decision's entries by `X_d + δ`, and transports it by `X_d + 2δ`.
    set Nw := max ni Ns with hNw
    have hcw : r.clk Nw ≤ Xd :=
      r.clk_max_le' hci (le_trans hcs (le_trans hP2P3 (le_trans hP3tM htMXd)))
    obtain ⟨N2, hN2, hc2, hrec⟩ := within_recorded sch hTJ hbr hi (hdw' Nw (le_max_left _ _))
    have hc2' : r.clk N2 ≤ Xd + sch.δ := le_trans hc2 (add_le_add (hrefle hcw hgXd) le_rfl)
    obtain ⟨N3, hN3, hc3, hcomp⟩ := within_complete sch hTJ hi (hdw' N2 (by omega)) hrec
    have hc3' : r.clk N3 ≤ Xd + 2 • sch.δ := by
      refine le_trans hc3 ?_
      calc r.ref N2 + sch.δ ≤ Xd + sch.δ + sch.δ :=
            add_le_add (hrefle hc2' (le_trans hgXd hXd1)) le_rfl
        _ = Xd + 2 • sch.δ := by rw [two_nsmul, add_assoc]
    have hcwc : Certified (thS := thS) (thM := thM) (r.at' ni) w := hbr.2.1 ni i w hi hdw
    -- The chunks under `w`'s FallbackQC entries, at saturation already: each
    -- entry's correct signer signed before its second-round vote, and sent
    -- every validator its chunk when it signed.
    have hchunks : ∀ J M', thS.mval_pos (thM.ent w) J M' = true → thS.mval_fb w J = true →
        Chorus.chunk_received (nset := nset) (mvba := Mvba.mvbaSafety thM) i J M' thS (r.at' Ns) :=
      fun J M' hM hfb => by
        obtain ⟨-, hkind⟩ := hcwc.1 J M' hM
        obtain ⟨q, hq, hallq⟩ := (hkind.resolve_left fun h => h.1 hfb).2.1
        obtain ⟨k, hkq, hkh⟩ := ByzNodeSet.greater_than_third_one_honest q hq
        have hcastk : Cast (r.at' Ns) k := by
          rcases hsat k hkh with ⟨h, -⟩ | ⟨h, -⟩
          · exact Or.inl h
          · exact Or.inr h
        exact ⟨k, fb_pos_sig_chunks r.toLRun hkh Ns (fb_pos_sig_at_cast hkh hcastk (hallq k hkq)) i⟩
    -- The vote: the chunks' hop is due by `M + 3Δ + 3δ`, before the decision.
    obtain ⟨n, hn, hcn, e, he⟩ := within_fbcommit_sig sch hTJ (N₀ := N₀) (Nc := Ns) (N := N3)
      (by omega) (by omega) (B := Xv)
      (le_trans (le_trans (add_le_add (hrefle hcs (le_trans hgM hMP2)) le_rfl)
        (le_of_eq (by rw [hP3, hMdef]; abel)))
        hP3Xv)
      (by rw [← hXd3]; exact add_le_add (hrefle hc3' hgXd2) le_rfl) hact hi
      (hdw' N3 (by omega)) hcomp hchunks
    -- It signs `i`'s decided entries, which are `v0`'s.
    obtain ⟨w', hdw'', rfl⟩ := fbcommit_sig_decided r.toLRun hi n he
    have heq : thM.ent w' = thM.ent v0 :=
      (Mvba.mvbaSafety (nset := nset) thM).agreement _
        (Chorus.reachable_mvba_reachable (r.reachable (max n n0))) i i0 w' v0 hi hi0
        (decided_persists r.toLRun hdw'' _ (le_max_left _ _)) (hd0' _ (le_max_right _ _))
    exact ⟨n, hn, hcn, heq ▸ he⟩
  -- The honest quorum's votes, at one index.
  obtain ⟨N4, hN4, hc4, hq4⟩ := r.withinFrom_forall
    (fun a st => nset.member a H = true → st.msg_fbcommit_sig a (thM.ent v0) = true)
    (fun a n h hm => Chorus.msg_fbcommit_sig.mono (r.steps n) a _ (h hm)) Ns Xv
    (le_trans hcs hsat_le) (Finset.univ : Finset node).toList
    (fun a _ => by
      by_cases hm : nset.member a H = true
      · obtain ⟨n, hn, hcn, h⟩ := hvote a (hHh a hm)
        exact ⟨n, hn, hcn, fun _ => h⟩
      · exact ⟨Ns, le_rfl, le_trans hcs hsat_le, fun h => absurd h hm⟩)
  have hP : (r.at' N₀).participating j = true := hpart j hj
  have hrefN4 : r.ref N4 ≤ Xv := hrefle hc4 hgXv
  have hmax4 : max N4 N₀ = N4 := max_eq_left (by omega)
  have hbound : Xv + 2 • sch.Δ + sch.δ = M + 5 • sch.Δ + T.ℓ + 8 • sch.δ := by
    rw [hXv, hXd, htM]; abel
  have hXΔ : Xv + sch.Δ ≤ Xv + 2 • sch.Δ := by
    refine add_le_add le_rfl ?_; rw [two_nsmul]; exact le_add_of_nonneg_right hΔ
  have hX2 : Xv + 2 • sch.Δ ≤ Xv + 2 • sch.Δ + sch.δ := le_add_of_nonneg_right hδ
  -- `j` sends its own fallback commit certificate by `X_v + Δ`, or has finalized.
  obtain ⟨N5, hN5, hc5, h5⟩ := within_fbcommitqc_sent sch hTJ hab hj hH hHh
    (fun a ha => hq4 a (by simp) ha) hP (B := Xv + sch.Δ)
    (r.bufWindow_le (add_le_add hrefN4 le_rfl) (by rw [hmax4]; exact add_le_add hrefN4 hδΔ))
  rcases h5 with ⟨e', he'⟩ | hdone5
  swap
  · exact ⟨N5, by rw [← hbound]; exact le_trans hc5 (le_trans hXΔ hX2), hdone5⟩
  -- The certificate is over `entries(v0)`, which has an entry for every proposer.
  have he0 : e' = thM.ent v0 := fbcommitqc_decided r.toLRun hi0 hd0 he'
  subst he0
  obtain ⟨-, -, htot⟩ := hbr.2.1 n0 i0 v0 hi0 hd0
  have hrefN5 : r.ref N5 ≤ Xv + sch.Δ := hrefle hc5 (le_trans hgXv (le_add_of_nonneg_right hΔ))
  have hmax5 : max N5 N₀ = N5 := max_eq_left (by omega)
  -- The assignments, by `X_v + 2Δ`.
  obtain ⟨N6, hN6, hc6, hall6⟩ := r.withinFrom_forall
    (fun J st => thS.is_proposer J = true → AssignedOrDone st j J)
    (fun J k h hJ => (h hJ).step) N5 (Xv + 2 • sch.Δ) (le_trans hc5 hXΔ)
    (Finset.univ : Finset node).toList
    (fun J _ => by
      by_cases hJ : thS.is_proposer J = true
      · have hproof : (∃ m c, ¬ nset.is_byz c = true ∧
              CertPos (mvba := Mvba.mvbaSafety thM) thS (r.at' N5) c J m) ∨
            (∃ c, ¬ nset.is_byz c = true ∧ CertNeg (mvba := Mvba.mvbaSafety thM) thS (r.at' N5) c J) := by
          rcases htot J hJ with ⟨M', hM⟩ | hM
          · exact Or.inl ⟨M', j, hj, Or.inr (Or.inl ⟨_, he', hM⟩)⟩
          · exact Or.inr ⟨j, hj, Or.inr (Or.inl ⟨_, he', hM⟩)⟩
        obtain ⟨k, hk, hck, hk'⟩ := within_assigned sch hTJ hab hj hJ hproof hP (B := Xv + 2 • sch.Δ)
          (r.bufWindow_le
            (by
              calc r.ref N5 + sch.Δ ≤ Xv + sch.Δ + sch.Δ := add_le_add hrefN5 le_rfl
                _ = Xv + 2 • sch.Δ := by rw [two_nsmul, add_assoc])
            (by
              rw [hmax5]
              calc r.ref N5 + sch.δ ≤ Xv + sch.Δ + sch.Δ := add_le_add hrefN5 hδΔ
                _ = Xv + 2 • sch.Δ := by rw [two_nsmul, add_assoc]))
        exact ⟨k, hk, hck, fun _ => hk'⟩
      · exact ⟨N5, le_rfl, le_trans hc5 hXΔ, fun h => absurd h hJ⟩)
  by_cases hdone : (r.at' N6).local_committed j = true
  · exact ⟨N6, by rw [← hbound]; exact le_trans hc6 hX2, hdone⟩
  · have hall : ∀ J, thS.is_proposer J = true →
        (∃ m, (r.at' N6).local_committed_pos j J m = true) ∨
          (r.at' N6).local_committed_neg j J = true := fun J hJ => by
      rcases hall6 J (by simp) hJ with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hdone
    have hrefN6 : r.ref N6 ≤ Xv + 2 • sch.Δ :=
      hrefle hc6 (le_trans hgXv (le_trans (le_add_of_nonneg_right hΔ) hXΔ))
    have hmax6 : max N6 N₀ = N6 := max_eq_left (by omega)
    obtain ⟨k, -, hck, hk⟩ := within_finalized sch hTJ hab hj hall hP
      (B := Xv + 2 • sch.Δ + sch.δ)
      (r.bufWindow_le (add_le_add hrefN6 le_rfl) (by rw [hmax6]; exact add_le_add hrefN6 le_rfl))
    exact ⟨k, by rw [← hbound]; exact hck, hk⟩

set_option maxHeartbeats 1000000 in
/-- **The single split**, at the vote deadline `X_v = M + 3Δ + ℓ_MVBA + 7δ`.
If a correct validator has finalized by `X_v`, totality finalizes everyone
by `X_v + Δ + 2δ = M + 4Δ + ℓ_MVBA + 9δ` (`totality` at the tolerance `Δ`);
otherwise the late branch finalizes everyone by
`T₀ = M + 5Δ + ℓ_MVBA + 8δ` (`within_finalized_late`). Either way by
`M + 5Δ + ℓ_MVBA + 9δ`, the paper's bound with the local steps counted. -/
theorem within_finalized_split [Fintype node] (sch : Schedule view time)
    (T : MVBATemporal node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset time nset (fun i => nset.is_byz i = true) (S := Mvba.mvbaSafety thM))
    (hℓ : 0 ≤ T.ℓ)
    (hmp : ∀ (e : node → Option merkle_root) j m, thS.mval_pos e j m = true ↔ e j = some m)
    (hmn : ∀ (e : node → Option merkle_root) j,
      thS.mval_neg e j = true ↔ e j = none ∧ thS.is_proposer j = true)
    (hent : ∀ v, thM.ent v = MetaBlock.entries v)
    (hmf : ∀ v j, thS.mval_fb v j = true ↔ (v j).map Prod.snd = some CertKind.fallbackQC)
    {H : nodeset} (hH : nset.supermajority H)
    (hHh : ∀ a, nset.member a H = true → ¬ nset.is_byz a = true)
    {r : TChorusRun thS thM time}
    (hevid : ∀ N, (∀ i, ¬ nset.is_byz i = true → Saturated thS (r.at' N) i) →
      Evidence thS thM (r.at' N))
    (hsync : Sync sch T r) (hbr : ValidBridge r.toLRun)
    (hsp : SyncParticipationWithin sch.Δ r)
    (hab : NoAbandonBeforeFinalizing r.toLRun) (hC2 : NoEarlyStart sch r)
    {t : time} (hall : AllParticipateBy t r)
    {j : node} (hj : ¬ nset.is_byz j = true) :
    ∃ n, r.clk n ≤ max t r.gst + 5 • sch.Δ + T.ℓ + 9 • sch.δ ∧
      (r.at' n).local_committed j = true := by
  mvba_inst
  have hδ : 0 ≤ sch.δ := sch.mvba.δ_nonneg
  have hΔ : 0 ≤ sch.Δ := sch.mvba.Δ_pos.le
  obtain ⟨i0, hH0, hi0⟩ := ByzNodeSet.greater_than_third_one_honest H
    (ByzNodeSet.supermajority_greater_than_third _ hH)
  obtain ⟨N₀, hN₀, hpart⟩ := exists_start ⟨i0, hHh i0 hH0⟩ hall
  set Xv := max t r.gst + 3 • sch.Δ + 4 • sch.δ + T.ℓ + 3 • sch.δ with hXv
  by_cases hA : ∃ n i, ¬ nset.is_byz i = true ∧ r.clk n ≤ Xv ∧ (r.at' n).local_committed i = true
  · -- An early finalization: totality.
    obtain ⟨n, i, hi, hcn, hci⟩ := hA
    obtain ⟨m, hcm, hm⟩ := totality (nset := nset) sch sch.Δ r hsync.1 hsp hab n i hi hci j hj
    refine ⟨m, le_trans hcm ?_, hm⟩
    have hgXv : r.gst ≤ Xv := by
      rw [hXv]
      refine le_trans (le_max_right t r.gst) ?_
      simp only [add_assoc]
      exact le_add_of_nonneg_right (add_nonneg (nsmul_nonneg hΔ 3)
        (add_nonneg (nsmul_nonneg hδ 4) (add_nonneg hℓ (nsmul_nonneg hδ 3))))
    calc max (r.clk n) r.gst + sch.dtot sch.Δ ≤ Xv + (sch.Δ + 2 • sch.δ) := by
          refine add_le_add (max_le hcn hgXv) ?_
          simp only [Schedule.dtot, Ltot, max_self]
          exact le_rfl
      _ = max t r.gst + 4 • sch.Δ + T.ℓ + 9 • sch.δ := by
          rw [hXv]; abel
      _ ≤ max t r.gst + 5 • sch.Δ + T.ℓ + 9 • sch.δ :=
          add_le_add (add_le_add (add_le_add le_rfl (nsmul_le_nsmul_left hΔ (by norm_num))) le_rfl) le_rfl
  · -- No early finalization: the late branch, by `T₀`.
    push Not at hA
    obtain ⟨n, hcn, hn⟩ := within_finalized_late sch T hℓ hmp hmn hent hmf hH hHh hevid hsync hbr hab
      hC2 hN₀ hpart (fun n i hi hc hci => (hA n i hi hc) hci) hj
    refine ⟨n, le_trans hcn ?_, hn⟩
    exact add_le_add le_rfl (nsmul_le_nsmul_left hδ (by norm_num))

/-! ### The MVBA's caller clauses, derived -/

/-- **F15: the MVBA's (Δ-avail) is derived, not assumed.** In every run
satisfying (Δδ-justice) and the bridge, at every schedule (whose
`Δ ≤ Δ_sync`, `Schedule.Δ_le_Δsync`), every projection's timed run
satisfies `Mvba.AvailWithin`: a correct validator that holds a meta-block
`v` is `AvailReady` for it within `Δ_sync` of holding it.

The argument. `v` is held, so its certificates are on the network
(`ValidBridge` at a held value). Each positive `FallbackQC` entry of `v` has
`f+1` signers, one of them correct, which sent every validator its chunk
when it signed (`fb_pos_sig_chunks`, Algorithm 5, line 12
(`line:fb-redisseminate`)). So the availability report's chunk wait is met
from the holding on, the report is owed (`i` holds `v`) and enabled until it
fires, and its `Δ`-row fires it within `max(Δ, δ) = Δ ≤ Δ_sync`. -/
theorem availWithin_of_timedJustice (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hTJ : TimedJustice sch r) (hbr : ValidBridge r.toLRun)
    (p : (mvbaComponent thS thM).Projection r.toLRun) : Mvba.AvailWithin sch.mvba p.timed := by
  mvba_inst
  intro m i V e hi hacc
  -- The holding, at the composed index at which the MVBA entered `m`.
  set N₀ := p.entry m with hN₀
  have hacc' : (r.at' N₀).mvba_st.accepted i V e = true := by
    have h := p.run_at'_entry m
    rw [show p.timed.at' m = p.run.at' m from rfl, h] at hacc
    exact hacc
  have hcert : ∀ n, N₀ ≤ n → Certified (thS := thS) (thM := thM) (r.at' n) e :=
    r.mono (P := fun st => Certified (thS := thS) (thM := thM) st e)
      (fun n h => Certified.step (r.steps n) h) (hbr.2.2 N₀ i V e hi hacc')
  have haccp : ∀ n, N₀ ≤ n → (r.at' n).mvba_st.accepted i V e = true :=
    r.mono (P := fun st => st.mvba_st.accepted i V e = true)
      (fun n h => mvba_st_step r.toLRun (fun st => st.accepted i V e = true)
        (fun _ _ _ htr h => Mvba.accepted.mono htr i V e h) n h) hacc'
  -- The chunk wait is met from the holding on.
  have hda : ∀ n, N₀ ≤ n → ∀ J M, thS.mval_pos (thM.ent e) J M = true → thS.mval_fb e J = true →
      Chorus.chunk_received (nset := nset) (mvba := Mvba.mvbaSafety thM) i J M thS (r.at' n) :=
      fun n hn J M hM hfb => by
    obtain ⟨-, hkind⟩ := (hcert n hn).1 J M hM
    obtain ⟨q, hq, hallq⟩ := (hkind.resolve_left fun h => h.1 hfb).2.1
    obtain ⟨k, hkq, hkh⟩ := ByzNodeSet.greater_than_third_one_honest q hq
    exact ⟨k, fb_pos_sig_chunks r.toLRun hkh n (hallq k hkq) i⟩
  -- The report's `Δ`-row, from the holding.
  have hW : r.bufWindow N₀ N₀ sch.Δ sch.δ ≤ r.ref N₀ + sch.mvba.Δsync :=
    r.bufWindow_le (add_le_add le_rfl sch.Δ_le_Δsync)
      (add_le_add le_rfl (le_trans sch.δ_le_Δ sch.Δ_le_Δsync))
  obtain ⟨n, hn, hcn, hP⟩ := r.withinFrom_of_bufferedFairFamily (hTJ.avail i e) le_rfl hW
    (P := fun st => st.mvba_st.avail_ready i e = true)
    (fun l ⟨mn, hl⟩ _ _ htr => by
      subst hl
      exact Mvba.avail_effect_tr thM (mvba_avail_ready_tr htr))
    (fun n hn _ hnP => ⟨⟨V, haccp n hn⟩, fun _ => by
      -- The `Mvba` model's availability input is unguarded.
      obtain ⟨st', hst'⟩ : ∃ st', (mvbaRTS (node := node) (nodeset := nodeset)
          (merkle_root := merkle_root) (view := view)).tr thM (r.at' n).mvba_st
          (.become_avail_ready i e) st' := by
        simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
        exact ⟨_, rfl⟩
      exact ⟨_, ⟨st', rfl⟩, enabled_mvba_avail_ready hi (hda n hn)
        (fun hf => hnP (avail_marked_ready r.toLRun n hf)) hst'⟩⟩)
    (fun _ _ _ _ => trivial)
  -- Read back at the projection: the state covering `n` was entered no later.
  refine ⟨(mvbaComponent thS thM).cover r.toLRun n, p.le_cover_of_entry_le hn, ?_,
    le_trans (r.clk_le_of_le (p.entry_cover_le n)) hcn⟩
  show (p.run.at' _).avail_ready i e = true
  rw [← p.proj_eq_run_cover n]
  exact hP

omit [IsOrderedAddMonoid time] in
/-- **The MVBA premise at the system's instance, from the MVBA's own two
clauses.** A projection whose timed run satisfies (Δ-justice) and
(T-timer), together with (Δδ-justice) and the bridge of the composed run,
gives the MVBA premise at `T := Mvba.mvbaTemporal`: its two clauses on the
caller are derived, the handoff by `relayed_of_timedJustice` (from the
decision output, `DecisionOutput`, and the schedule's `δ ≤ ρ`) and
(Δ-avail) by `availWithin_of_timedJustice`. -/
theorem timedMvbaAdmissible_of_rows [IsOrderedCancelAddMonoid time] [Archimedean time]
    [Fintype node] (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : Mvba.LeaderRotation vfin sch.mvba.k thM)
    {r : TChorusRun thS thM time} (hTJ : TimedJustice sch r) (hout : DecisionOutput sch r)
    (hbr : ValidBridge r.toLRun)
    (p : (mvbaComponent thS thM).Projection r.toLRun)
    (hown : Mvba.BoundedJustice sch.mvba p.timed ∧ Mvba.TimerPunctual sch.mvba p.timed) :
    TimedMvbaAdmissible (Mvba.mvbaTemporal thM hqe sch.mvba vfin hrot) r :=
  timedMvbaAdmissible_of_sync hqe sch vfin hrot p
    ⟨hown.1, hown.2, availWithin_of_timedJustice sch hTJ hbr p,
      relayed_of_timedJustice sch hTJ hout p⟩

omit [IsOrderedAddMonoid time] in
/-- **The timing model at the system's MVBA gives `Sync`.** `SyncAtMvba` and
the bridge imply `Sync` at `T := Mvba.mvbaTemporal`: what is assumed of the
MVBA is its own scheduling only, and of the decider its decision output. -/
theorem sync_of_syncAtMvba [IsOrderedCancelAddMonoid time] [Archimedean time]
    [Fintype node] (hqe : ByzNodeSetHonestQuorum node nodeset nset)
    (sch : Schedule view time) (vfin : ViewOrderEnum view vord)
    (hrot : Mvba.LeaderRotation vfin sch.mvba.k thM)
    {r : TChorusRun thS thM time} (hs : SyncAtMvba sch r) (hbr : ValidBridge r.toLRun) :
    Sync sch (Mvba.mvbaTemporal thM hqe sch.mvba vfin hrot) r :=
  ⟨hs.1, hs.2.1, let ⟨p, hp⟩ := hs.2.2.1
    timedMvbaAdmissible_of_rows hqe sch vfin hrot hs.1 hs.2.2.2 hbr p hp⟩

end Round

/-! ## At the concrete quorum family, at the system's configurations -/

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
  {time : Type} [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]
  {is_proposer : Fin n → Bool} {well_encoded : merkle_root → Bool}
  {mvba_init_state : Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view)}
  {mvalid : MetaBlock (Fin n) merkle_root → Bool} {mleader : view → Fin n → Bool}

/-- The Chorus configuration at the system's instantiation. -/
local notation "thC" => Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
  is_proposer well_encoded mvba_init_state

/-- The MVBA configuration at the system's instantiation. -/
local notation "thMC" => Cadence.mvbaTheory (nodeset := ByzNSet n) mvalid mleader

set_option maxHeartbeats 1600000 in
/-- **ℓ-termination, proven** (Lemma 11 (`lemma:chorus-termination`)):
`TimedTerminationClaim` at the paper's bound `ℓ = 5Δ + ℓ_MVBA + 9δ`
(`Lchorus`), which is the paper's `5Δ + ℓ_MVBA` at `δ = 0`
(`Lchorus_paper`). At every `n = 3f+1` with at most `f` Byzantine
validators, at the system's configurations, for every MVBA contract `T` at
the fragment Chorus consumes whose latency is non-negative.

The proof splits once, at the fallback commit votes' deadline
`M + 3Δ + ℓ_MVBA + 7δ` (`within_finalized_split`): an early finalizer gives
everyone totality's `Δ + 2δ` after it, `M + 4Δ + ℓ_MVBA + 9δ`; otherwise C1
keeps everyone active until then and the late branch finalizes everyone by
`T₀ = M + 5Δ + ℓ_MVBA + 8δ`, with the fallback commit certificate's two
hops (formed from the votes, then received). -/
theorem timed_termination (sch : Schedule view time)
    (T : MVBATemporal (Fin n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root)
      (Mvba.Msg view (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType (Fin n) (ByzNSet n) (MetaBlock (Fin n) merkle_root) (Fin n → Option merkle_root) view))
      (ByzNSet n) time (byzNodeSetFin n f hf is_byz hbyz)
      (fun i => (byzNodeSetFin n f hf is_byz hbyz).is_byz i = true)
      (S := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thMC))
    (hℓ : 0 ≤ T.ℓ) :
    TimedTerminationClaim (nset := byzNodeSetFin n f hf is_byz hbyz)
      (cnt := Cadence.byzNodeSetFin_counting n f hf is_byz hbyz) sch T thC := by
  intro r hsync hbr hsp hab hC2 t hall j hj
  obtain ⟨H, hH, hHh⟩ := honest_quorum_fin n f hf is_byz hbyz
  obtain ⟨m, hm, hc⟩ := within_finalized_split (nset := byzNodeSetFin n f hf is_byz hbyz) (cnt := Cadence.byzNodeSetFin_counting n f hf is_byz hbyz)
    sch T hℓ (fun _ _ _ => decide_eq_true_iff) (fun _ _ => decide_eq_true_iff) (fun _ => rfl)
    (fun _ _ => decide_eq_true_iff) hH hHh
    (fun N hsat => mvba_evidence_of_saturation
      (mvba := Mvba.mvbaSafety (nset := byzNodeSetFin n f hf is_byz hbyz) thMC) n f hf is_byz hbyz
      (r.reachable N) (fun i hi => hsat i (fun hb => hi (by simpa +instances [byzNodeSetFin] using hb))))
    hsync hbr hsp hab hC2 hall hj
  exact ⟨m, by rw [Schedule.ℓ, Lchorus, ← add_assoc, ← add_assoc]; exact hm, hc⟩

end Concrete

/-! ## At the system's MVBA

`T := Mvba.mvbaTemporal`, the instance [System.lean](../System.lean)'s MVBA
carries: its `ℓ` is `Mvba.Schedule.ℓ`, a sum of non-negative terms, so the
one hypothesis the two theorems above take of `T` is discharged. -/

section AtMvba

open Classical ByzNodeSet

/-- **`ℓ_MVBA` is non-negative** at every MVBA schedule: it is a sum of the
schedule's non-negative constants. -/
theorem mvbaSchedule_ℓ_nonneg {view time : Type} [Inhabited view] [vord : TotalOrderWithMinimum view]
    [LinearOrder time] [AddCommMonoid time] [IsOrderedAddMonoid time]
    (sch : Mvba.Schedule view time) (vfin : ViewOrderEnum view vord) : 0 ≤ sch.ℓ vfin := by
  have hΔ : 0 ≤ sch.Δ := sch.Δ_pos.le
  have hδ := sch.δ_nonneg
  have hρ := sch.ρ_nonneg
  have hτ : 0 ≤ sch.τmax := le_trans (sch.τ_nonneg default) (sch.τ_le_max default)
  have hb : 0 ≤ sch.burn := by
    unfold Mvba.Schedule.burn
    exact add_nonneg (add_nonneg hτ (nsmul_nonneg hδ 2)) (nsmul_nonneg hΔ 2)
  have hL : 0 ≤ Mvba.Lcert sch.Δ sch.δ sch.Δsync := by
    unfold Mvba.Lcert
    exact add_nonneg (add_nonneg (nsmul_nonneg hΔ 3) (le_trans hΔ (le_max_left _ _))) (nsmul_nonneg hδ 2)
  unfold Mvba.Schedule.ℓ
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hΔ hρ) (nsmul_nonneg hρ 2))
    (nsmul_nonneg hb _)) hL) (add_nonneg hΔ hρ)

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

/-- The family has a supermajority of correct validators
(`honest_quorum_fin`), which is what the MVBA's timed claim takes as
`ByzNodeSetHonestQuorum`. -/
@[implicit_reducible]
noncomputable def hqeFin :
    ByzNodeSetHonestQuorum (Fin n) (ByzNSet n) (byzNodeSetFin n f hf is_byz hbyz) where
  honestQuorum := (honest_quorum_fin n f hf is_byz hbyz).choose
  honestQuorum_supermajority := (honest_quorum_fin n f hf is_byz hbyz).choose_spec.1
  honestQuorum_correct := (honest_quorum_fin n f hf is_byz hbyz).choose_spec.2

/-- **ℓ-termination at the system's MVBA**: `TimedTerminationClaimAtMvba`,
the claim at `T := Mvba.mvbaTemporal` with the MVBA's timing premise its own
two clauses only (`SyncAtMvba`): the handoff and (Δ-avail), which Chorus
provides, are derived (`sync_of_syncAtMvba`). `ℓ_MVBA` is `Mvba.Schedule.ℓ`
(`mvbaTemporal_ℓ`). No hypothesis beyond the MVBA instance's own (§6.2.5 of
[Bounds.md](../../docs/Bounds.md)): a correct supermajority, the view order's
enumeration, and (A-leader-rotation-k); the first is a theorem of the
family (`hqeFin`), so the claim takes the other two only. -/
theorem timed_termination_atMvba (sch : Schedule view time)
    (vfin : ViewOrderEnum view vord)
    (hrot : Mvba.LeaderRotation (nset := byzNodeSetFin n f hf is_byz hbyz) vfin sch.mvba.k thMC) :
    TimedTerminationClaimAtMvba (nset := byzNodeSetFin n f hf is_byz hbyz) sch vfin thC thMC :=
  fun r hs hbr hsp hab hC2 t ht j hj =>
    timed_termination n f hf is_byz hbyz sch _ (mvbaSchedule_ℓ_nonneg sch.mvba vfin) r
      (sync_of_syncAtMvba (nset := byzNodeSetFin n f hf is_byz hbyz)
        (cnt := Cadence.byzNodeSetFin_counting n f hf is_byz hbyz)
        (hqeFin n f hf is_byz hbyz) sch vfin hrot hs hbr) hbr hsp hab hC2 t ht j hj

end AtMvba

end Chorus

/-! ## The pinned trust base

The standard Lean trio and nothing else — no `sorryAx`. -/

/--
info: 'Chorus.fb_pos_sig_flip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fb_pos_sig_flip

/--
info: 'Chorus.fb_pos_sig_at_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fb_pos_sig_at_cast


/--
info: 'Chorus.within_all_decided' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_all_decided

/--
info: 'Chorus.within_recorded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_recorded

/--
info: 'Chorus.within_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_complete

/--
info: 'Chorus.within_fbcommit_sig' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_fbcommit_sig

/--
info: 'Chorus.within_fbcommitqc_sent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_fbcommitqc_sent

/--
info: 'Chorus.within_finalized_late' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_finalized_late

/--
info: 'Chorus.within_finalized_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_finalized_split

/-- info: 'Chorus.mvbaSchedule_ℓ_nonneg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Chorus.mvbaSchedule_ℓ_nonneg

/--
info: 'Chorus.timed_termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.timed_termination

/--
info: 'Chorus.timed_termination_atMvba' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.timed_termination_atMvba

/--
info: 'Chorus.availWithin_of_timedJustice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.availWithin_of_timedJustice

/--
info: 'Chorus.timedMvbaAdmissible_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.timedMvbaAdmissible_of_rows

/--
info: 'Chorus.sync_of_syncAtMvba' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.sync_of_syncAtMvba
