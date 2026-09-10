import Cadence.Chorus.Certify
import Cadence.Interfaces

/-! # ChorusCompose — `Chorus ⊨ SlotConsensusSafety`

The final leg of the composition layer (`docs/ConductorDesign.md` §5.2,
`docs/CompositionContracts.md`): the Chorus transition system, packaged as
the state-level slot-consensus contract that the `Cadence` glue module
consumes as its `sc` constraint ([`Interfaces.lean`](../Interfaces.lean)).

**The family.** `mod:slotconsensus` is one instance per slot, and the
contract is stated as the family over slots. Chorus is a single-slot model,
so the instance runs one independent copy of it per slot: every slot's
`init`, `step`, `reachable` are Chorus's own, and a validator's finalized
proposal vector is its decision vector *tagged with the slot* —
`pvector := slot × (node → Option merkle_root)`. That tag is what makes the
contract's `slot_safety` hold by construction: the glue's "slot safety is
absorbed by indexing" and the paper's `V.slot = s` are the same fact here.

**The proposal-vector construction** (the "granularity note" of the
contract): a committed validator's vector maps each proposer `J` to its
committed positive root (`some M` iff `local_committed_pos i J M`), and
every non-proposer to `none`. The `is_proposer` gate is load-bearing: the
module's invariant clump does not record "committed entries exist only for
proposers" (it is a guard of `commit_assign_*`), so agreement at
non-proposer indices holds by construction rather than by invariant.
`finalized s st i V` requires `local_committed i` — the paper's
`finalize(V)` output — and pins `V` to the tagged vector; `on_time` is the
module's `all_honest_recorded` synchrony-premise ghost, exactly as the
contract's docstring says.

| `SlotConsensusSafety` field | discharged by |
|---|---|
| `agreement` | `safety [agreement_pos]` + `[agreement_pos_neg]` + `invariant [local_committed_complete]` |
| `slot_safety` | by construction (the slot tag) |
| `proposal_inclusion` | `safety [proposal_inclusion]` + `[proposal_inclusion_no_neg]` + `invariant [local_committed_complete]` |
| `finalized_mono`, `on_time_mono`, `init_finalized` | Veil's generated step lemmas (`local_committed.mono`, `local_committed_pos.mono`, `local_entry_pos.mono`, `local_committed.init`) through `committedAll_mono`, `committedPos_mono`, `recorded_mono`, `init_not_committed` below; plus `committedPos_frozen_of_reachable`, the `step_property [committed_pos_frozen]` cells exported by `#gen_composition` — the vector is frozen once committed because `commit_assign_*` require `¬ local_committed i`, which is a guard rather than an update record, so it needs the checked cells rather than the generated lemmas |
| `step_trans`, `reachable_init`, `reachable_trans` | the reachability constructors |

all consumed through the named reachability projections of
[`Chorus/Certify.lean`](./Certify.lean) (emitted by `#gen_composition` from
the proof-file family's preservation lemmas).

**What stays unproven.** Chorus models neither the participation interface
of `mod:slotconsensus` (`participate`/`abandon`/`propose` are absent — the
model is single-slot and its participation window is Cadence-driven) nor
time, and it has no message type at the interface. So the upper level's
inputs, their observables, the clock, the admissible-run model, Termination
and Quiescence are the fields of `SlotConsensusTemporal`, of which this
development has no instance —
`slotConsensus_of_temporal` proves that, given one, Chorus is a full
`SlotConsensus`, discharging on the way the one upper-level field Chorus
*does* prove: the protocol half of Hiding (`safety [hiding_until_deadline]`,
the contract's `hiding_residue`). The residual is the formal statement of
`docs/Architecture.md` §4 item 4 for this module.

Trust base: `[propext, Classical.choice, Quot.sound]` — the standard Lean
trio, nothing else — pinned by the `#guard_msgs` axiom checks at the end of
this file. The composition consumes the proof-file family
(`Chorus/Proofs/`, via `Chorus/Certify.lean`'s `#gen_composition`):
every VC statement re-created from the persistent registry, solved as a
fresh kernel-checked reconstruction, assembled per action into a
preservation lemma, and composed — kernel-checked at every `addDecl` —
inside Veil. -/

-- NOTE: deliberately NO `open Veil` here — it activates the Veil DSL's
-- scoped keywords, one of which (`includes`) collides with the
-- `SlotConsensusSafety` field name in the `where` block below. Veil names
-- are used fully qualified instead.

namespace Chorus
open Classical ByzNodeSet

section Instance

variable {slot node nodeset merkle_root Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase]
  [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

/- The abstract field representation of the Chorus state at the canonical
`Classical` instances (cf. `Composition.lean`'s `afr%`). -/
local macro "afr%" f:ident : term =>
  `(@Chorus.instAbstractFieldRepresentation slot node nodeset merkle_root Phase PathChoice
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    $f)

/-- `i` has committed a positive entry `⟨J, M⟩` (state read at the canonical
representation). -/
noncomputable abbrev CommittedPos
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    (i J : node) (M : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_committed_pos)
    st.local_committed_pos i J M = true

/-- `i` has finalized (`local_committed`). -/
noncomputable abbrev CommittedAll
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    (i : node) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_committed) st.local_committed i = true

/-- `r` has recorded proposer `j`'s entry `m` (`local_entry_pos`) — the
per-validator half of `all_honest_recorded`. -/
noncomputable abbrev Recorded
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    (r j : node) (m : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_entry_pos) st.local_entry_pos r j m = true

/-- The slot is past its deadline: the phase is no longer `pre_deadline`. -/
noncomputable abbrev DeadlinePassed
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)) : Prop :=
  ¬ (@Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.phase) st.phase = Phase_Enum.pre_deadline)

variable (th : Chorus.Theory slot node nodeset merkle_root Phase PathChoice)

/-- The proposal vector a committed validator holds: each proposer maps to
its committed positive root (if any), every non-proposer to `none`. -/
noncomputable def decisionVector
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
    (i : node) : node → Option merkle_root :=
  fun J =>
    if th.is_proposer J = true then
      if hpos : ∃ M, CommittedPos st i J M then some hpos.choose else none
    else none

/-! ### Step-level facts, uniformly over all 38 actions

None of these is a hand-written case analysis any more. Three of them —
`committedAll_mono`, `committedPos_mono`, `recorded_mono` — are Veil's
generated whole-system monotonicity lemmas (`<relation>.mono`, emitted at
`#gen_spec` because every action either frames the relation or only ever
writes `true` to it), and `init_not_committed` is the generated
initial-value lemma. The one fact the update records cannot give is that a
*committed* validator's entries are frozen: that rests on
`commit_assign_pos`'s guard `¬ local_committed i`, so it is a
`step_property` in the model, checked per action, and reaches this file as
`Chorus.reachable_committed_pos_frozen_step`. `docs/CompositionContracts.md`
§4 explains the three sources and when each applies. -/

section StepFacts
variable {st st' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)}

/-- `local_committed` stands across every action: the generated whole-system
monotonicity lemma. -/
theorem committedAll_mono
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (i : node) (h : CommittedAll st i) : CommittedAll st' i := by
  obtain ⟨l, htr⟩ := hn
  exact Chorus.local_committed.mono htr i h

/-- `local_committed_pos` stands across every action: the generated
whole-system monotonicity lemma. -/
theorem committedPos_mono
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (i J : node) (M : merkle_root) (h : CommittedPos st i J M) : CommittedPos st' i J M := by
  obtain ⟨l, htr⟩ := hn
  exact Chorus.local_committed_pos.mono htr i J M h

/-- A committed validator's positive entries are frozen (`commit_assign_pos`
requires `¬ local_committed i`): from the checked `step_property
[committed_pos_frozen]` cells, along any step from a reachable state
(`reachable_<property>_step`, emitted by `Chorus/Certify.lean`'s
`#gen_composition`). The contract's `finalized_mono` takes the pre-state's
reachability, which the glue tracks as an invariant. -/
theorem committedPos_frozen_of_reachable
    (hr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).reachable th st)
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (i : node) (hc : CommittedAll st i) (J : node) (M : merkle_root)
    (h : CommittedPos st' i J M) : CommittedPos st i J M := by
  obtain ⟨l, htr⟩ := hn
  exact Chorus.reachable_committed_pos_frozen_step hr htr i J M ⟨hc, h⟩

/-- `local_entry_pos` stands across every action: the generated whole-system
monotonicity lemma. -/
theorem recorded_mono
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (r j : node) (m : merkle_root) (h : Recorded st r j m) : Recorded st' r j m := by
  obtain ⟨l, htr⟩ := hn
  exact Chorus.local_entry_pos.mono htr r j m h

/-- Initially nobody has committed: the generated initial-value lemma. -/
theorem init_not_committed
    (hinit : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).init th st)
    (i : node) : ¬ CommittedAll st i :=
  fun h => Bool.false_ne_true ((Chorus.local_committed.init hinit i).symm.trans h)

/-- A committed validator's decision vector does not change along any step
from a reachable state. -/
theorem decisionVector_stable
    (hr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).reachable th st)
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th st st')
    (i : node) (hc : CommittedAll st i) : decisionVector th st' i = decisionVector th st i := by
  have hiff : ∀ J M, CommittedPos st' i J M ↔ CommittedPos st i J M :=
    fun J M => ⟨committedPos_frozen_of_reachable th hr hn i hc J M, committedPos_mono th hn i J M⟩
  funext J
  unfold decisionVector
  by_cases hp : th.is_proposer J = true
  · rw [if_pos hp, if_pos hp]
    -- The two branches differ only in the predicate under the `∃`, and the
    -- predicates are equal.
    have hpred : (fun M => CommittedPos st' i J M) = (fun M => CommittedPos st i J M) :=
      funext fun M => propext (hiff J M)
    exact congrArg
      (fun P : merkle_root → Prop => (if hpos : ∃ M, P M then some hpos.choose else none : Option merkle_root))
      hpred
  · rw [if_neg hp, if_neg hp]

end StepFacts

set_option maxHeartbeats 1000000 in
/-- **`Chorus ⊨ SlotConsensusSafety`** — for every Chorus theory `th`, the
slot-indexed copies of the Chorus transition system are an instance of the
state-level slot-consensus contract, with `byz` the Byzantine predicate of
the module's `ByzNodeSet` instance.

The contract is unindexed (`Interfaces.lean`, "Slot Consensus"): a state
carries the slot of the instance it belongs to. Chorus's own state does not,
because the model is single-slot — so the instance runs on **pairs**
`slot × Chorus.State`, whose first component is exactly the contract's
`tag`. Transitions leave it alone, which is `tag_frame`; `finalized` tags
each vector with it, which is what makes `slot_safety` hold by
construction. Nothing about the Chorus model changes: every field below
reads the pair's second component and defers to the same reachability
projections as before. -/
@[implicit_reducible]
noncomputable def slotConsensusSafety :
    SlotConsensusSafety slot node merkle_root (slot × (node → Option merkle_root))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
      (fun i => nset.is_byz i = true) where
  init p := (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).assumptions th ∧
    (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).init th p.2
  step p p' := p.1 = p'.1 ∧ (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th p.2 p'.2
  trans p p' := p.1 = p'.1 ∧ (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).next th p.2 p'.2
  reachable p := (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).reachable th p.2
  step_trans _ _ h := h
  reachable_init p h := Veil.RelationalTransitionSystem.reachable.init p.2 h.1 h.2
  reachable_trans p p' hr hn := Veil.RelationalTransitionSystem.reachable.step p.2 p'.2 hr hn.2
  tag p := p.1
  tag_frame _ _ h := h.1.symm
  finalized p i V := CommittedAll p.2 i ∧ V = (p.1, decisionVector th p.2 i)
  slot_of V := V.1
  includes V j P := V.2 j = some P
  on_time p j P := Chorus.all_honest_recorded (nset := nset)
    (χ := Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) j P th p.2
  finalized_mono _ _ i V hr hn h :=
    ⟨committedAll_mono th hn.2 i h.1,
      by rw [h.2, hn.1, decisionVector_stable th hr hn.2 i h.1]⟩
  on_time_mono _ _ j P _ hn h :=
    ⟨h.1, h.2.1, fun r hrec => recorded_mono th hn.2 r j P (h.2.2.1 r hrec), h.2.2.2⟩
  init_finalized _ i V h hf := init_not_committed th h.2 i hf.1
  agreement p hr i j V V' hci hcj hfi hfj := by
    obtain ⟨s, st⟩ := p
    obtain ⟨hci_com, hVi⟩ := hfi
    obtain ⟨hcj_com, hVj⟩ := hfj
    subst hVi; subst hVj
    refine Prod.ext rfl ?_
    show decisionVector th st i = decisionVector th st j
    funext J
    unfold decisionVector
    by_cases hp : th.is_proposer J = true
    · rw [if_pos hp, if_pos hp]
      by_cases hi : ∃ M, CommittedPos st i J M
      · -- `i` decided positively: so does `j` (completeness + pos/neg
        -- exclusion), and the roots agree.
        have hj' : ∃ M, CommittedPos st j J M := by
          rcases reachable_local_committed_complete hr j ⟨hcj, hcj_com⟩ J hp with hpos | hneg
          · exact hpos
          · obtain ⟨Mi, hMi⟩ := hi
            exact absurd hneg
              (reachable_agreement_pos_neg hr i j J Mi ⟨hci, hcj, hci_com, hcj_com, hMi⟩)
        rw [dif_pos hi, dif_pos hj']
        congr 1
        exact reachable_agreement_pos hr i j J hi.choose hj'.choose
          ⟨hci, hcj, hci_com, hcj_com, hi.choose_spec, hj'.choose_spec⟩
      · -- `i` decided negatively (completeness): so must `j`.
        have hj' : ¬ ∃ M, CommittedPos st j J M := by
          rintro ⟨M, hM⟩
          rcases reachable_local_committed_complete hr i ⟨hci, hci_com⟩ J hp with hpos | hneg
          · exact hi hpos
          · exact (reachable_agreement_pos_neg hr j i J M ⟨hcj, hci, hcj_com, hci_com, hM⟩) hneg
        rw [dif_neg hi, dif_neg hj']
    · rw [if_neg hp, if_neg hp]
  -- By construction: the instance tags its vectors with its own slot.
  slot_safety _ _ _ _ _ hf := by rw [hf.2]
  proposal_inclusion p hr i j V P hci hfi hot := by
    obtain ⟨s, st⟩ := p
    obtain ⟨hcom, hV⟩ := hfi
    subst hV
    show decisionVector th st i j = some P
    have hp : th.is_proposer j = true := hot.2.1
    unfold decisionVector
    rw [if_pos hp]
    have hex : ∃ M, CommittedPos st i j M := by
      rcases reachable_local_committed_complete hr i ⟨hci, hcom⟩ j hp with hpos | hneg
      · exact hpos
      · exact absurd hneg (reachable_proposal_inclusion_no_neg hr j i P ⟨hot, hci⟩)
    rw [dif_pos hex]
    congr 1
    exact reachable_proposal_inclusion hr j i P hex.choose ⟨hot, hci, hex.choose_spec⟩
  -- Hiding's protocol half: `payload_recoverable` is the module's
  -- `slot_key_released` (the decryption threshold has been reached),
  -- `deadline_passed` its phase leaving `pre_deadline`, and
  -- `safety [hiding_until_deadline]` is exactly the implication. It is
  -- first-order, so it belongs to the fragment.
  deadline_passed p := DeadlinePassed p.2
  payload_recoverable p := Chorus.slot_key_released (nset := nset)
    (χ := Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) th p.2
  hiding_residue _ hr hk := reachable_hiding_until_deadline hr hk

/-! ### What the full `SlotConsensus` still owes

Chorus has no participation interface, no clock and no message type at the
contract's level of abstraction. What stands between the fragment above and
the full `SlotConsensus` is therefore an instance of
**`SlotConsensusTemporal … (S := slotConsensusSafety th)`** — and there is
none. Its fields are exactly that missing interface (`participate`,
`abandon`, `propose` with their observables and frames) together with the
clock, the admissible-run model, Termination ((A-sc-termination) of
[`docs/Architecture.md`](../../docs/Architecture.md) §4 item 4) and
Quiescence, whose participation-window statement needs the interface Chorus
lacks — its in-model shadow being phase confinement.

Because every one of those fields is already stated over
`(slotConsensusSafety th)`'s own `init`, `trans`, `reachable` and
`finalized`, none of them is restated here: the gap is a missing instance,
not a structure. -/

/-- Given a temporal level **at this fragment**, Chorus is a full
`SlotConsensus`. Nothing is restated to join them, and the fragment comes
back out by `rfl`. -/
@[implicit_reducible]
noncomputable def slotConsensus_of_temporal {time message : Type} [TotalOrder time] [Add time]
    (h : SlotConsensusTemporal slot node merkle_root (slot × (node → Option merkle_root))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)) time message
      (fun i => nset.is_byz i = true) (S := slotConsensusSafety th)) :
    SlotConsensus slot node merkle_root (slot × (node → Option merkle_root))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))
      time message (fun i => nset.is_byz i = true) :=
  { slotConsensusSafety th, h with }

/-- The fragment the composition consumes is exactly the one that was
proven. -/
theorem slotConsensus_of_temporal_toSafety {time message : Type} [TotalOrder time] [Add time]
    (h : SlotConsensusTemporal slot node merkle_root (slot × (node → Option merkle_root))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice)) time message
      (fun i => nset.is_byz i = true) (S := slotConsensusSafety th)) :
    (slotConsensus_of_temporal th h).toSlotConsensusSafety = slotConsensusSafety th := rfl

end Instance
end Chorus

/-! ## The pinned trust base

The instance rests on the standard Lean trio and nothing else — in
particular, **no `sorryAx`**: no trusted-SMT step and no statement stub
anywhere in the chain. The Chorus model persists no per-VC theorems (its
VC *statements* are carried claim-free by the persistent VC registry);
the composition consumes the **proof-file family** (`Chorus/Proofs/`):
one file per action, each re-proving its action's
registered VC statements from scratch as fresh kernel-checked
reconstructions (`veil.smt.trust false`), persisted as real proofs in
small per-file oleans and assembled into one preservation lemma. A
regression anywhere in that chain — a proof silently degrading to a
stub, trusted SMT reappearing — fails this guard. The temporal-conditioned
full instance is pinned too: its assumptions enter as a *hypothesis*, never
as an axiom. -/

/--
info: 'Chorus.slotConsensusSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensusSafety

/--
info: 'Chorus.slotConsensus_of_temporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensus_of_temporal
