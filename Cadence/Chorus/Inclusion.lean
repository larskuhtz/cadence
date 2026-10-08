import Cadence.Chorus.TimedTermination

/-! # Chorus.Inclusion — a correct proposer's root, recorded by the deadline

[ConductorBounds.md](../../docs/ConductorBounds.md) §7, F31. The timed
half of proposal inclusion that censorship resistance needs (Proposition 3
(`prop:honest-positive-entry`)): a correct proposer that signs its root at
the slot's starting time `D − Δ ≥ GST` has it recorded by every correct
validator, so its entry is on time (`all_honest_recorded`, the contract's
`on_time`). Its timing premise is (P-incl), `DeadlineInclusive`
([Schedule.lean](Schedule.lean)): a chunk due by the deadline is recorded,
the paper's "by the deadline" read inclusively (P19).

Also here: two facts about the `propose` input, its enabledness and the
well-encoded root it carries, and that a finalization postdates the
deadline (`committed_post_deadline`), which keeps a proposer from having
abandoned a slot before it proposes. -/

namespace Chorus

open Cadence
open scoped Cadence.Timed

section Inclusion

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

/-- **Milestone: a correct proposer's root is recorded by every correct
validator**, under (P-incl). If a correct proposer `j` signed its root `m` by
`X`, with `max(X, GST) + Δ ≤ D`, it sent each correct validator its chunk
in the same step (`signed_chunks`), due by the deadline, which the validator
records (P-incl); the entry is on `m`, the one root a correct proposer
signs. -/
theorem within_proposal_recorded_incl (sch : Schedule view time) {r : TChorusRun thS thM time}
    (hDI : DeadlineInclusive sch r)
    {j : node} (hj : ¬ nset.is_byz j = true) (hJ : thS.is_proposer j = true)
    {m : merkle_root} {Np : Nat} {X : time} (hcp : r.clk Np ≤ X)
    (hs : (r.at' Np).msg_proposer_signed j m = true)
    (hX : max X r.gst + sch.Δ ≤ sch.D)
    {i : node} (hi : ¬ nset.is_byz i = true) :
    ∃ k, Np ≤ k ∧ (r.at' k).local_entry_pos i j m = true := by
  mvba_inst
  have hsig : ∀ n, Np ≤ n → (r.at' n).msg_proposer_signed j m = true :=
    r.mono (P := fun st => st.msg_proposer_signed j m = true)
      (fun k hk => Chorus.msg_proposer_signed.mono (r.steps k) j m hk) hs
  have hrefp : r.ref Np ≤ max X r.gst := r.ref_le (le_trans hcp (le_max_left _ _)) (le_max_right _ _)
  obtain ⟨k, m', he⟩ := hDI Np i j m hi hj hJ (signed_chunks r.toLRun hj Np hs i)
    (le_trans (add_le_add hrefp le_rfl) hX)
  have heK : (r.at' (max k Np)).local_entry_pos i j m' = true :=
    r.mono (P := fun st => st.local_entry_pos i j m' = true)
      (fun n hn => Chorus.local_entry_pos.mono (r.steps n) i j m' hn) he _ (le_max_left _ _)
  have hs' := Chorus.reachable_local_entry_pos_signed (r.reachable (max k Np)) i j m' ⟨hi, heK⟩
  have hsm := hsig (max k Np) (le_max_right k Np)
  have heq : m' = m := Chorus.reachable_proposer_unique_root (r.reachable (max k Np)) j m' m ⟨hj, hs', hsm⟩
  exact ⟨max k Np, le_max_right k Np, heq ▸ heK⟩

/-- **A finalization postdates the deadline**: a correct validator that has
finalized has committed an entry for every proposer, each backed by a
certificate from a supermajority of votes, which has a correct voter, who
voted after the deadline; or by an MVBA decision, which is after it too. -/
theorem committed_post_deadline {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    (hr : (atMvba thM).reachable thS s) {i : node} (hi : ¬ nset.is_byz i = true)
    (hc : s.local_committed i = true) {J : node} (hJ : thS.is_proposer J = true) :
    s.phase ≠ Phase_EnumClass.pre_deadline := by
  mvba_inst
  rcases Chorus.reachable_local_committed_complete hr i ⟨hi, hc⟩ J hJ with ⟨M, hp⟩ | hn
  · rcases Chorus.reachable_local_committed_pos_backed hr i J M ⟨hi, hp⟩ with ⟨C, hq⟩ | hd
    · obtain ⟨q, hq, hall⟩ := Chorus.reachable_msg_commitqc_pos_votes hr C J M hq
      obtain ⟨a, ha, -, hha⟩ := nset.supermajorities_intersect_in_honest q q hq hq
      exact Chorus.reachable_voted_post_deadline hr a
        ⟨hha, Chorus.reachable_vote_sig_pos_implies_voted hr a J M ⟨hha, hall a ha⟩⟩
    · exact Chorus.reachable_mvba_decided_phase hr J M (Or.inl hd)
  · rcases Chorus.reachable_local_committed_neg_backed hr i J ⟨hi, hn⟩ with ⟨C, hq⟩ | hd
    · obtain ⟨q, hq, hall⟩ := Chorus.reachable_msg_commitqc_neg_votes hr C J hq
      obtain ⟨a, ha, -, hha⟩ := nset.supermajorities_intersect_in_honest q q hq hq
      exact Chorus.reachable_voted_post_deadline hr a
        ⟨hha, Chorus.reachable_vote_sig_neg_implies_voted hr a J ⟨hha, hall a ha⟩⟩
    · exact Chorus.reachable_mvba_decided_phase hr J default (Or.inr hd)

set_option maxHeartbeats 1000000 in
/-- **`propose` is enabled under its guards** (Algorithm 2
(`alg:proposer-dissemination`)): a correct proposer that participates, has
not abandoned and has signed no other root, before the deadline, on a
well-encoded root. -/
theorem propose_exists {s : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    {j : node} {m : merkle_root} (hj : ¬ nset.is_byz j = true) (hp : s.participating j = true)
    (ha : ¬ s.abandoned j = true) (hJ : thS.is_proposer j = true) (hwe : thS.well_encoded m = true)
    (hph : s.phase = Phase_EnumClass.pre_deadline)
    (hu : ∀ m2, s.msg_proposer_signed j m2 = true → m2 = m) :
    ∃ s', (atMvba thM).tr thS s (.propose j m) s' := by
  simp only [atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp]
  exact ⟨_, hj, hp, ha, hJ, hwe, hph, hu, rfl⟩

set_option maxHeartbeats 1000000 in
/-- A proposed root is well-encoded (`propose`'s guard). -/
theorem propose_well_encoded {s s' : StateAtMvba slot node nodeset merkle_root view Phase PathChoice}
    {j : node} {m : merkle_root} (htr : (atMvba thM).tr thS s (.propose j m) s') :
    thS.well_encoded m = true := by
  simp only [atMvba, Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct, trSimp] at htr
  obtain ⟨-, -, -, -, h, -⟩ := htr
  exact h

end Inclusion

end Chorus

/-! ## The pinned trust base -/

/--
info: 'Chorus.within_proposal_recorded_incl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.within_proposal_recorded_incl

/--
info: 'Chorus.committed_post_deadline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.committed_post_deadline
