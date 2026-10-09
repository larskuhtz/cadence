import Cadence.Chorus.Certify
import Cadence.Interfaces

/-! # ChorusCompose — `Chorus ⊨ SlotConsensusSafety`

The final leg of the composition layer
([ConductorDesign.md](../../docs/ConductorDesign.md) §5.2,
[CompositionContracts.md](../../docs/CompositionContracts.md)): the Chorus
transition system, packaged as the state-level slot-consensus contract that
the `Cadence` glue module consumes as its `sc` constraint
([Interfaces.lean](../Interfaces.lean)).

**The family.** Module 1 (`mod:slotconsensus`) is one instance per slot, and the
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

Each entry is a `SlotConsensusSafety` field and what discharges it.

* **`agreement`** — `safety [agreement_pos]` + `[agreement_pos_neg]` +
  `invariant [local_committed_complete]`
* **`slot_safety`** — by construction (the slot tag)
* **`proposal_inclusion`** — `safety [proposal_inclusion]` +
  `[proposal_inclusion_no_neg]` + `invariant [local_committed_complete]`
* **`finalized_mono`, `on_time_mono`, `init_finalized`** — Veil's generated
  step lemmas (`local_committed.mono`, `local_committed_pos.mono`,
  `local_entry_pos.mono`, `local_committed.init`) through `committedAll_mono`,
  `committedPos_mono`, `recorded_mono`, `init_not_committed` below; plus
  `committedPos_frozen_of_reachable`, the `step_property
  [committed_pos_frozen]` cells exported by `#gen_composition` — the vector is
  frozen once committed because `commit_assign_*` require `¬ local_committed
  i`, which is a guard rather than an update record, so it needs the checked
  cells rather than the generated lemmas
* **`step_trans`, `reachable_init`, `reachable_trans`** — the reachability
  constructors
* **the three inputs** (`participate`, `abandon`, `propose`), their records
  (`participating`, `abandoned`, the proposer's signed root), effects,
  frames and initial values — the actions' bodies, read once each in "The
  participation interface" below, and Veil's generated lemmas

all consumed through the named reachability projections of
[Chorus/Certify.lean](Certify.lean) (emitted by `#gen_composition` from
the proof-file family's preservation lemmas).

**Internal steps and inputs.** Chorus models Module 1 (`mod:slotconsensus`)'s three
inputs as actions (`participate`, `abandon`, and the proposer's `propose`),
so the instance separates them: `trans` is every transition, and `step`,
the contract's internal steps, is every transition whose label is not an
input (`Label.isInput`). That split is what the frames need ("internal
steps do not change a correct validator's inputs"). The glue drives the
three inputs through the contract's `participate`, `propose` and `abandon`
fields, and its oracle step `sc_step` takes only `step`, so in the composed
system ([System.lean](../System.lean)) every Chorus transition is either one of Chorus's
own steps or an input the glue gave.

**The upper level.** The message type with `sent`, the admissible-run
model, Termination over timed runs and Quiescence are the fields of
`SlotConsensusTemporal`. `slotConsensus_of_temporal` joins any
instance of it with the fragment into a full `SlotConsensus`, and
[Chorus/Temporal.lean](Temporal.lean) proves one at the system's
configuration (`Chorus.chorusTemporal`, joined as `Chorus.slotConsensusFull`).
This file holds the message type and Quiescence's first half
(`own_sent_new`), which need nothing of the MVBA.

Trust base: `[propext, Classical.choice, Quot.sound]` — the standard Lean
trio, nothing else — pinned by the `#guard_msgs` axiom checks at the end of
this file. The composition consumes the proof-file family
([Chorus/Proofs](Proofs), via [Chorus/Certify.lean](Certify.lean)'s `#gen_composition`):
every VC statement re-created from the persistent registry, solved as a
fresh kernel-checked reconstruction, assembled per action into a
preservation lemma, and composed — kernel-checked at every `addDecl` —
inside Veil. -/

-- No `open Veil` here: the DSL's scoped keyword `includes` collides with the
-- `SlotConsensusSafety` field of that name ([CLAUDE.md](../../CLAUDE.md),
-- "Hard rules"). Veil names are qualified instead.

namespace Chorus
open Classical ByzNodeSet

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

open Lean in
/-- One `case` per listed action: rewrite with its generated frame lemma for
`fld`. -/
local macro "frame_iff " htr:ident fld:ident "[" acts:ident,* "]" : tactic => do
  let mut acc ← `(tactic| skip)
  for a in acts.getElems do
    let lem := mkIdent (`Chorus ++ a.getId ++ Name.mkSimple ("frame_" ++ fld.getId.toString))
    acc ← `(tactic| ($acc; case $a:ident => rw [$lem:ident $htr]))
  return acc

section Inputs

variable {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}

/-- The labels of the module's three inputs, `participate()`, `abandon()`
and `propose(P)` (Module 1 (`mod:slotconsensus`)); every other label is an internal
step of the protocol. The contract's `step` is the internal steps, so that
its frames ("internal steps do not change a correct validator's inputs")
are about exactly them. -/
def Label.isInput :
    Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice → Prop
  | .participate _ => True
  | .abandon _ _ => True
  | .propose _ _ => True
  | _ => False

/-- `Label.isInput` names the three input constructors, in a form that
survives leaving this module (at this many constructors the definition's
`match` does not reduce in an importing file; consumers case on this lemma,
as [Chorus/Liveness.lean](Liveness.lean) does). -/
theorem Label.isInput_cases
    {l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice}
    (h : Label.isInput l) :
    (∃ i, l = .participate i) ∨ (∃ i n, l = .abandon i n) ∨ (∃ j m, l = .propose j m) := by
  cases l <;> simp_all [Label.isInput]

end Inputs

section Instance

variable {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited mstate] [Inhabited mvalue] [Inhabited mentries] [Inhabited mmsg]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset]
  -- The quorum counting facts Chorus consumes (its `cnt` class constraint).
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  -- The MVBA contract Chorus consumes (its `mvba` class constraint), stated
  -- against the module's own fault pattern; [System.lean](../System.lean) instantiates it at
  -- `Mvba.mvbaSafety`.
  [mvba : MVBASafety node mvalue mentries mmsg mstate nodeset nset (fun i => nset.is_byz i = true)]
  [Phase_Enum : Chorus.Phase_EnumClass Phase]
  [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

/- The abstract field representation of the Chorus state at the canonical
`Classical` instances (cf. [Composition.lean](../Composition.lean)'s `afr%`). -/
local macro "afr%" f:ident : term =>
  `(@Chorus.instAbstractFieldRepresentation slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    $f)

/-- `i` has committed a positive entry `⟨J, M⟩` (state read at the canonical
representation). -/
noncomputable abbrev CommittedPos
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (i J : node) (M : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_committed_pos)
    st.local_committed_pos i J M = true

/-- `i` has finalized (`local_committed`). -/
noncomputable abbrev CommittedAll
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (i : node) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_committed) st.local_committed i = true

/-- `r` has recorded proposer `j`'s entry `m` (`local_entry_pos`) — the
per-validator half of `all_honest_recorded`. -/
noncomputable abbrev Recorded
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (r j : node) (m : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_entry_pos) st.local_entry_pos r j m = true

/-- The slot is past its deadline: the phase is no longer `pre_deadline`. -/
noncomputable abbrev DeadlinePassed
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) : Prop :=
  ¬ (@Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.phase) st.phase = Phase_Enum.pre_deadline)

variable (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)

/-- The proposal vector a committed validator holds: each proposer maps to
its committed positive root (if any), every non-proposer to `none`. -/
noncomputable def decisionVector
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (i : node) : node → Option merkle_root :=
  fun J =>
    if th.is_proposer J = true then
      if hpos : ∃ M, CommittedPos st i J M then some hpos.choose else none
    else none

/-! ### Step-level facts, uniformly over every action

None of these is a hand-written case analysis. Three of them —
`committedAll_mono`, `committedPos_mono`, `recorded_mono` — are Veil's
generated whole-system monotonicity lemmas (`<relation>.mono`, emitted at
`#gen_spec` because every action either frames the relation or only ever
writes `true` to it), and `init_not_committed` is the generated
initial-value lemma. The one fact the update records cannot give is that a
*committed* validator's entries are frozen: that rests on
the `commit_assign_pos_*` guard `¬ local_committed i`, so it is a
`step_property` in the model, checked per action, and reaches this file as
`Chorus.reachable_committed_pos_frozen_step`.
[CompositionContracts.md](../../docs/CompositionContracts.md) §4 explains the
three sources and when each applies. -/

section StepFacts
variable {st st' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}

/-- `local_committed` stands across every action: the generated whole-system
monotonicity lemma. -/
theorem committedAll_mono
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).next th st st')
    (i : node) (h : CommittedAll st i) : CommittedAll st' i := by
  obtain ⟨l, htr⟩ := hn
  exact Chorus.local_committed.mono htr i h

/-- `local_committed_pos` stands across every action: the generated
whole-system monotonicity lemma. -/
theorem committedPos_mono
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).next th st st')
    (i J : node) (M : merkle_root) (h : CommittedPos st i J M) : CommittedPos st' i J M := by
  obtain ⟨l, htr⟩ := hn
  exact Chorus.local_committed_pos.mono htr i J M h

/-- A committed validator's positive entries are frozen (every
`commit_assign_pos_*` requires `¬ local_committed i`): from the checked `step_property
[committed_pos_frozen]` cells, along any step from a reachable state
(`reachable_<property>_step`, emitted by [Chorus/Certify.lean](Certify.lean)'s
`#gen_composition`). The contract's `finalized_mono` takes the pre-state's
reachability, which the glue tracks as an invariant. -/
theorem committedPos_frozen_of_reachable
    (hr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).reachable th st)
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).next th st st')
    (i : node) (hc : CommittedAll st i) (J : node) (M : merkle_root)
    (h : CommittedPos st' i J M) : CommittedPos st i J M := by
  obtain ⟨l, htr⟩ := hn
  exact Chorus.reachable_committed_pos_frozen_step hr htr i J M ⟨hc, h⟩

/-- `local_entry_pos` stands across every action: the generated whole-system
monotonicity lemma. -/
theorem recorded_mono
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).next th st st')
    (r j : node) (m : merkle_root) (h : Recorded st r j m) : Recorded st' r j m := by
  obtain ⟨l, htr⟩ := hn
  exact Chorus.local_entry_pos.mono htr r j m h

/-- Initially nobody has committed: the generated initial-value lemma. -/
theorem init_not_committed
    (hinit : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).init th st)
    (i : node) : ¬ CommittedAll st i :=
  fun h => Bool.false_ne_true ((Chorus.local_committed.init hinit i).symm.trans h)

/-- A committed validator's decision vector does not change along any step
from a reachable state. -/
theorem decisionVector_stable
    (hr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).reachable th st)
    (hn : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).next th st st')
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

/-- **The commit availability condition, in Chorus's vocabulary**
(Supplement, Section 1.2 (`subsec:mvba-protocol`), "Commit availability
condition": "the MVBA ensures that each correct Commit signer holds and
broadcasts its assigned share before sending its vote"). A valid MVBA
commit certificate for `e` has a supermajority each of whose correct members
received its assigned chunk under every positive `FallbackQC` entry of a
valid representation of `e` of its own. This is the contract's
`certified_available` read through `avail_ready_chunks`: `AvailReady` is
the input Chorus drives with exactly that chunk wait. The representation is
the member's own, since two correct signers may hold different certificate
kinds for one root (PaperAlignment §6, P2). -/
theorem certified_available_chunks {st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}
    (hr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).reachable th st)
    {c : mmsg} {e : mentries} (hc : mvba.certifies st.mvba_st c e) :
    ∃ q, nset.supermajority q ∧ ∀ p, nset.member p q = true → ¬ nset.is_byz p = true →
      ∃ v, mvba.entries v = e ∧ mvba.Valid v ∧
        ∀ J M, th.mval_pos e J M = true → th.mval_fb v J = true →
          ∃ k, st.msg_chunk k p J M = true := by
  obtain ⟨q, hq, hall⟩ := mvba.certified_available _ (Chorus.reachable_mvba_reachable hr) c e hc
  refine ⟨q, hq, fun p hp hpc => ?_⟩
  obtain ⟨v, hv, hval, hav⟩ := hall p hp hpc
  refine ⟨v, hv, hval, fun J M hM hfb => ?_⟩
  subst hv
  exact Chorus.reachable_avail_ready_chunks hr p v J M ⟨hpc, hav⟩ hM hfb

/-- **Data availability of every correct positive commit** (the counterpart
of "`recoverProposals` does not block", Algorithm 6, line 12 (`line:da-wait`)):
at every reachable state, a root a correct validator committed positively
has `f+1` validators that broadcast their chunk under it with their votes,
so every validator receiving those votes holds `f+1` chunks. A commit is
backed by a fast commit certificate or an MVBA record
(`local_committed_pos_backed`), and the roots of both are decodable
(`msg_commitqc_pos_chunks_decodable`, `mvba_decided_pos_chunks_decodable`). -/
theorem local_committed_pos_implies_decodable {st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}
    (hr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).reachable th st)
    {I J : node} {M : merkle_root} (hI : ¬ nset.is_byz I = true)
    (hc : st.local_committed_pos I J M = true) :
    ∃ q, nset.greater_than_third q ∧ ∀ r, nset.member r q = true →
      st.msg_vote_chunk r J M = true := by
  rcases Chorus.reachable_local_committed_pos_backed hr I J M ⟨hI, hc⟩ with ⟨C, hC⟩ | haux
  · exact Chorus.reachable_msg_commitqc_pos_chunks_decodable hr C J M hC
  · exact Chorus.reachable_mvba_decided_pos_chunks_decodable hr J M haux

/-! ### The participation interface, from the transition bodies

Module 1 (`mod:slotconsensus`)'s three inputs are Chorus actions, and each
records itself in one relation: `participate i` sets `participating i`,
`abandon i` sets `abandoned i` (and forwards the abandonment to the MVBA),
and `propose j m` sets the proposer's signed root `msg_proposer_signed j m`.
The contract's facts about them come from two sources: Veil's generated
lemmas (each relation's monotonicity and initial value, and the frame of
every action that does not write it) and the three bodies, each read once
for its effect and for the rows it leaves alone. -/

section Interface
variable {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}

set_option maxHeartbeats 1000000 in
/-- `participate i` records `participating i`. -/
theorem participate_effect_tr {i : node} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s (.participate i) s') :
    s'.participating i = true := by
  chorus_tr htr
  subst htr
  chorus_field_simp

set_option maxHeartbeats 1000000 in
/-- `participate i` records nobody else's participation. -/
theorem participate_frame_tr {i j : node} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s (.participate i) s') (hne : j ≠ i) :
    s'.participating j = s.participating j := by
  chorus_tr htr
  subst htr
  chorus_field_simp
  intro h; exact absurd h.symm hne

set_option maxHeartbeats 1000000 in
/-- `abandon i` records `abandoned i`. -/
theorem abandon_effect_tr {i : node} {mn : mstate} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s (.abandon i mn) s') :
    s'.abandoned i = true := by
  chorus_tr htr
  obtain ⟨-, rfl⟩ := htr
  chorus_field_simp

set_option maxHeartbeats 1000000 in
/-- `abandon i` records nobody else's abandonment. -/
theorem abandon_frame_tr {i j : node} {mn : mstate} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s (.abandon i mn) s') (hne : j ≠ i) :
    s'.abandoned j = s.abandoned j := by
  chorus_tr htr
  obtain ⟨-, rfl⟩ := htr
  chorus_field_simp
  intro h; exact absurd h.symm hne

set_option maxHeartbeats 1000000 in
/-- `propose j m` records the proposer's signed root. -/
theorem propose_effect_tr {j : node} {m : merkle_root} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s (.propose j m) s') :
    s'.msg_proposer_signed j m = true := by
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  chorus_field_simp

set_option maxHeartbeats 1000000 in
/-- `propose j m` records no other signed root. -/
theorem propose_frame_tr {j k : node} {m m' : merkle_root} (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s (.propose j m) s')
    (hne : k ≠ j ∨ m' ≠ m) : s'.msg_proposer_signed k m' = s.msg_proposer_signed k m' := by
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  chorus_field_simp
  intro hk hm; subst hk; subst hm
  rcases hne with h | h <;> exact absurd rfl h

set_option maxHeartbeats 1000000 in
/-- A Byzantine proposer's signature is its own. -/
theorem byz_sign_proposer_frame {j k : node} {m m' : merkle_root}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s (.byz_sign_proposer j m) s') (hk : ¬ nset.is_byz k = true) :
    s'.msg_proposer_signed k m' = s.msg_proposer_signed k m' := by
  chorus_tr htr
  obtain ⟨hj, rfl⟩ := htr
  chorus_field_simp
  intro h; subst h; simp_all

/-- **Internal steps do not change participation**: only the input
`participate` writes it. -/
theorem participating_internal {l} (hl : ¬ Label.isInput l) (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s') (i : node) :
    s'.participating i = s.participating i := by
  cases l
  case participate => exact absurd trivial hl
  frame_iff htr participating [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share]

/-- **Internal steps do not change abandonment**: only the input `abandon`
writes it. -/
theorem abandoned_internal {l} (hl : ¬ Label.isInput l) (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s') (i : node) :
    s'.abandoned i = s.abandoned i := by
  cases l
  case abandon => exact absurd trivial hl
  frame_iff htr abandoned [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share]

/-- **Internal steps do not change a correct proposer's proposal**: only the
input `propose` writes a correct proposer's signed root; the adversary's
`byz_sign_proposer` writes only a Byzantine one's. -/
theorem proposed_internal {l} (hl : ¬ Label.isInput l) (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s') {k : node}
    (hk : ¬ nset.is_byz k = true) (m : merkle_root) :
    s'.msg_proposer_signed k m = s.msg_proposer_signed k m := by
  cases l
  case propose => exact absurd trivial hl
  case byz_sign_proposer => exact byz_sign_proposer_frame th htr hk
  frame_iff htr msg_proposer_signed [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share]

end Interface

set_option maxHeartbeats 1000000 in
/-- **`Chorus ⊨ SlotConsensusSafety`** — for every Chorus theory `th`, the
slot-indexed copies of the Chorus transition system are an instance of the
state-level slot-consensus contract, with `byz` the Byzantine predicate of
the module's `ByzNodeSet` instance.

The contract is unindexed ([Interfaces.lean](../Interfaces.lean), "Slot Consensus"): a state
carries the slot of the instance it belongs to. Chorus's own state does not,
because the model is single-slot — so the instance runs on **pairs**
`slot × Chorus.State`, whose first component is exactly the contract's
`tag`. Transitions leave it alone, which is `tag_frame`; `finalized` tags
each vector with it, which is what makes `slot_safety` hold by
construction. Every other field reads the pair's second component and
defers to the reachability projections of the Chorus model. -/
@[implicit_reducible]
noncomputable def slotConsensusSafety :
    SlotConsensusSafety slot node merkle_root (slot × (node → Option merkle_root))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
      (fun i => nset.is_byz i = true) where
  init p := (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).assumptions th ∧
    (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).init th p.2
  step p p' := p.1 = p'.1 ∧ ∃ l, ¬ Label.isInput l ∧
    (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th p.2 l p'.2
  trans p p' := p.1 = p'.1 ∧ (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).next th p.2 p'.2
  reachable p := (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).reachable th p.2
  step_trans _ _ h := ⟨h.1, h.2.choose, h.2.choose_spec.2⟩
  reachable_init p h := Veil.RelationalTransitionSystem.reachable.init p.2 h.1 h.2
  reachable_trans p p' hr hn := Veil.RelationalTransitionSystem.reachable.step p.2 p'.2 hr hn.2
  tag p := p.1
  tag_frame _ _ h := h.1.symm
  finalized p i V := CommittedAll p.2 i ∧ V = (p.1, decisionVector th p.2 i)
  slot_of V := V.1
  includes V j P := V.2 j = some P
  on_time p j P := Chorus.all_honest_recorded (nset := nset)
    (χ := Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) j P th p.2
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
    (χ := Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) th p.2
  hiding_residue _ hr hk := reachable_hiding_until_deadline hr hk
  -- The participation interface: Module 1's three inputs, each a Chorus
  -- action, and their records.
  participate p i p' := p.1 = p'.1 ∧ (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th p.2 (.participate i) p'.2
  abandon p i p' := p.1 = p'.1 ∧ ∃ mn, (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th p.2 (.abandon i mn) p'.2
  propose p i P p' := p.1 = p'.1 ∧ (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th p.2 (.propose i P) p'.2
  participate_trans _ _ _ h := ⟨h.1, _, h.2⟩
  abandon_trans _ _ _ h := ⟨h.1, _, h.2.choose_spec⟩
  propose_trans _ _ _ _ h := ⟨h.1, _, h.2⟩
  participating p i := p.2.participating i = true
  abandoned p i := p.2.abandoned i = true
  proposed p i P := p.2.msg_proposer_signed i P = true
  participating_mono _ _ i h hp := Chorus.participating.mono h.2.choose_spec i hp
  abandoned_mono _ _ i h hp := Chorus.abandoned.mono h.2.choose_spec i hp
  proposed_mono _ _ i P h hp := Chorus.msg_proposer_signed.mono h.2.choose_spec i P hp
  participate_effect _ _ _ h := participate_effect_tr th h.2
  abandon_effect _ _ _ h := abandon_effect_tr th h.2.choose_spec
  propose_effect _ _ _ _ h := propose_effect_tr th h.2
  participating_step_frame _ _ i h _ := by
    obtain ⟨-, l, hl, htr⟩ := h
    rw [participating_internal th hl htr i]
  abandoned_step_frame _ _ i h _ := by
    obtain ⟨-, l, hl, htr⟩ := h
    rw [abandoned_internal th hl htr i]
  proposed_step_frame _ _ i P h hi := by
    obtain ⟨-, l, hl, htr⟩ := h
    rw [proposed_internal th hl htr hi P]
  participate_frame _ _ _ j h _ hne := by rw [participate_frame_tr th h.2 hne]
  abandon_frame _ _ _ j h _ hne := by rw [abandon_frame_tr th h.2.choose_spec hne]
  propose_frame _ _ _ _ j P' h _ hne := by rw [propose_frame_tr th h.2 hne]
  participate_abandoned_frame _ _ _ j h _ := by rw [Chorus.participate.frame_abandoned h.2]
  participate_proposed_frame _ _ _ j P h _ := by rw [Chorus.participate.frame_msg_proposer_signed h.2]
  abandon_participating_frame _ _ _ j h _ := by rw [Chorus.abandon.frame_participating h.2.choose_spec]
  abandon_proposed_frame _ _ _ j P h _ := by rw [Chorus.abandon.frame_msg_proposer_signed h.2.choose_spec]
  propose_participating_frame _ _ _ _ j h _ := by rw [Chorus.propose.frame_participating h.2]
  propose_abandoned_frame _ _ _ _ j h _ := by rw [Chorus.propose.frame_abandoned h.2]
  init_participating _ i h hp := by simp [Chorus.participating.init h.2 i] at hp
  init_abandoned _ i h hp := by simp [Chorus.abandoned.init h.2 i] at hp
  init_proposed _ i P h hp := by simp [Chorus.msg_proposer_signed.init h.2 i P] at hp

/-! ### The join with the temporal level

What stands between the fragment above and the full `SlotConsensus` is an
instance of **`SlotConsensusTemporal … (S := slotConsensusSafety th)`**: the
message type with `sent`, the admissible-run model, Termination and
Quiescence. Every one of those fields is stated over
`(slotConsensusSafety th)`'s own `init`, `trans`, `reachable` and
`finalized`, so none is restated here. [Chorus/Temporal.lean](Temporal.lean)
proves the instance at the system's configuration and joins it here. -/

/-- Given a temporal level **at this fragment**, Chorus is a full
`SlotConsensus`. Nothing is restated to join them, and the fragment comes
back out by `rfl`. -/
@[implicit_reducible]
noncomputable def slotConsensus_of_temporal {time message : Type} [TotalOrder time] [Add time]
    (h : SlotConsensusTemporal slot node merkle_root (slot × (node → Option merkle_root))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) time message
      (fun i => nset.is_byz i = true) (S := slotConsensusSafety th)) :
    SlotConsensus slot node merkle_root (slot × (node → Option merkle_root))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
      time message (fun i => nset.is_byz i = true) :=
  { slotConsensusSafety th, h with }

/-- The fragment the composition consumes is exactly the one that was
proven. -/
theorem slotConsensus_of_temporal_toSafety {time message : Type} [TotalOrder time] [Add time]
    (h : SlotConsensusTemporal slot node merkle_root (slot × (node → Option merkle_root))
      (slot × Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) time message
      (fun i => nset.is_byz i = true) (S := slotConsensusSafety th)) :
    (slotConsensus_of_temporal th h).toSlotConsensusSafety = slotConsensusSafety th := rfl

end Instance

/-! ## Quiescence, Chorus's own half

Lemma 6 (`lemma:chorus-quiescence`) has two parts, and so does its proof
here. A correct validator's **own** messages are sent only by rules gated on
active participation, `participating i ∧ ¬ abandoned i`
([Chorus.lean](../Chorus.lean), "Participation inputs"): one step, read
from the transition bodies, below (`own_sent_new`). The **MVBA's** messages
are confined by the MVBA's own quiescence to the window between `i`'s MVBA
proposal, which Chorus makes only while participating, and its MVBA
abandonment, which Chorus forwards from its own `abandon`. That needs both
facts to hold along the run, so it is proven at the system's MVBA, with the
instance ([Chorus/Temporal.lean](Temporal.lean)).

`Message` is the module's protocol-message type: one constructor per
network relation of the model that records its **sender**, and the MVBA's
messages. The two network relations without a sender, a delivered chunk
and a broadcast commit certificate, are attributed to nobody. Each travels
with an attributed send: a chunk with its proposer's signed root or a
signer's positive fallback entry, a commit certificate with the commit
votes it aggregates. -/

section Quiescence

variable {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited mstate] [Inhabited mvalue] [Inhabited mentries] [Inhabited mmsg]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [mvba : MVBASafety node mvalue mentries mmsg mstate nodeset nset (fun i => nset.is_byz i = true)]
  [Phase_Enum : Chorus.Phase_EnumClass Phase]
  [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice}
  {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)}

/-- **A protocol message of one Chorus instance**, by what it says; its
sender is `Sent`'s second argument. -/
inductive Message (node merkle_root mentries mmsg : Type) where
  /-- Proposer `i`'s signed root `m` (Algorithm 2 (`alg:proposer-dissemination`)), with every chunk. -/
  | proposal (m : merkle_root)
  /-- A positive vote entry for `(j, m)`. -/
  | votePos (j : node) (m : merkle_root)
  /-- A negative vote entry for `j`. -/
  | voteNeg (j : node)
  /-- The proposal vote (Algorithm 3, line 14 (`line:vote-broadcast`)). -/
  | voteCast
  /-- The chunk a vote carries for its positive entry `(j, m)`. -/
  | voteChunk (j : node) (m : merkle_root)
  /-- A positive fallback entry for `(j, m)`, with the re-disseminated chunks. -/
  | fbPos (j : node) (m : merkle_root)
  /-- A negative fallback entry for `j`. -/
  | fbNeg (j : node)
  /-- The fallback vote. -/
  | fallback
  /-- A positive fast commit entry for `(j, m)`. -/
  | commitPos (j : node) (m : merkle_root)
  /-- A negative fast commit entry for `j`. -/
  | commitNeg (j : node)
  /-- The fast commit vote (Algorithm 4, line 24 (`line:fast-commitvote`)). -/
  | commitCast
  /-- The decryption share, released with the vote. -/
  | decryptShare
  /-- The fallback commit vote over the entries `e` (Algorithm 5, line 41 (`line:fb-commitvote`)). -/
  | fbCommit (e : mentries)
  /-- Validator `r`'s chunk under `(j, m)`, sent to `r` (Algorithm 2
  (`alg:proposer-dissemination`), Algorithm 5, line 12 (`line:fb-redisseminate`)). -/
  | chunk (r j : node) (m : merkle_root)
  /-- A positive fast commit certificate for `(j, m)` (Algorithm 4, line 33
  (`line:fast-broadcast-commitqc`), and its re-broadcast). -/
  | commitqcPos (j : node) (m : merkle_root)
  /-- A negative fast commit certificate for `j`. -/
  | commitqcNeg (j : node)
  /-- A fallback commit certificate over the entries `e` (Algorithm 5, line 44
  (`line:fb-commit-broadcast`), and its re-broadcast). -/
  | fbCommitQC (e : mentries)
  /-- The MVBA's commit certificate `c`, broadcast by Chorus (Supplement,
  Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"). -/
  | mvbaCert (c : mmsg)
  /-- A message of the slot's MVBA instance. -/
  | mvba (m : mmsg)

/-- `i` has sent `msg`: the message's network row with `i` as its sender,
or, for an MVBA message, the MVBA contract's `sent`. -/
def Sent
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice))
    (i : node) : Message node merkle_root mentries mmsg → Prop
  | .proposal m => st.msg_proposer_signed i m = true
  | .votePos j m => st.msg_vote_pos_sig i j m = true
  | .voteNeg j => st.msg_vote_neg_sig i j = true
  | .voteCast => st.msg_vote_cast i = true
  | .voteChunk j m => st.msg_vote_chunk i j m = true
  | .fbPos j m => st.msg_fb_pos_sig i j m = true
  | .fbNeg j => st.msg_fb_neg_sig i j = true
  | .fallback => st.msg_fallback_sig i = true
  | .commitPos j m => st.msg_commit_pos_sig i j m = true
  | .commitNeg j => st.msg_commit_neg_sig i j = true
  | .commitCast => st.msg_commit_cast i = true
  | .decryptShare => st.msg_decrypt_share i = true
  | .fbCommit e => st.msg_fbcommit_sig i e = true
  | .chunk r j m => st.msg_chunk i r j m = true
  | .commitqcPos j m => st.msg_commitqc_pos i j m = true
  | .commitqcNeg j => st.msg_commitqc_neg i j = true
  | .fbCommitQC e => st.msg_fbcommitqc i e = true
  | .mvbaCert c => st.msg_mvba_cert i c = true
  | .mvba m => mvba.sent st.mvba_st i m

set_option hygiene false in
/-- A writer of the row: expose its body. The new row is the acting
validator's, so its guards include the participation gate, or a Byzantine
signer's, which `i` is not. -/
local macro "own_close" : tactic =>
  `(tactic| (chorus_tr htr; chorus_field_simp; repeat (obtain ⟨_, htr⟩ := htr)
             simp only at hnew; (try split_ifs at hnew) <;> simp_all))

open Lean in
/-- One `case` per action: the generated frame lemma for the row where the
action has one (it does not write the row), else `own_close`. -/
local macro "own_frame " htr:ident fld:ident "[" acts:ident,* "]" "=>" tac:tacticSeq : tactic => do
  let mut acc ← `(tactic| skip)
  for a in acts.getElems do
    let lem := mkIdent (`Chorus ++ a.getId ++ Name.mkSimple ("frame_" ++ fld.getId.toString))
    acc ← `(tactic| ($acc; case $a:ident => first
      | (have hfr := $lem:ident $htr; simp only [hfr] at *; contradiction)
      | ($tac)))
  return acc

set_option maxHeartbeats 4000000 in
/-- A new `msg_proposer_signed` row of a correct sender comes from a gated rule. -/
theorem msg_proposer_signed_new {l} {i : node} {m : merkle_root}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_proposer_signed i m = true)
    (hold : ¬ s.msg_proposer_signed i m = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_proposer_signed [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_vote_pos_sig` row of a correct sender comes from a gated rule. -/
theorem msg_vote_pos_sig_new {l} {i : node} {j : node} {m : merkle_root}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_vote_pos_sig i j m = true)
    (hold : ¬ s.msg_vote_pos_sig i j m = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_vote_pos_sig [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_vote_chunk` row of a correct sender comes from a gated rule. -/
theorem msg_vote_chunk_new {l} {i : node} {j : node} {m : merkle_root}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_vote_chunk i j m = true)
    (hold : ¬ s.msg_vote_chunk i j m = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_vote_chunk [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_vote_neg_sig` row of a correct sender comes from a gated rule. -/
theorem msg_vote_neg_sig_new {l} {i : node} {j : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_vote_neg_sig i j = true)
    (hold : ¬ s.msg_vote_neg_sig i j = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_vote_neg_sig [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_vote_cast` row of a correct sender comes from a gated rule. -/
theorem msg_vote_cast_new {l} {i : node} 
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_vote_cast i  = true)
    (hold : ¬ s.msg_vote_cast i  = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_vote_cast [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_fb_pos_sig` row of a correct sender comes from a gated rule. -/
theorem msg_fb_pos_sig_new {l} {i : node} {j : node} {m : merkle_root}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_fb_pos_sig i j m = true)
    (hold : ¬ s.msg_fb_pos_sig i j m = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_fb_pos_sig [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_fb_neg_sig` row of a correct sender comes from a gated rule. -/
theorem msg_fb_neg_sig_new {l} {i : node} {j : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_fb_neg_sig i j = true)
    (hold : ¬ s.msg_fb_neg_sig i j = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_fb_neg_sig [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_fallback_sig` row of a correct sender comes from a gated rule. -/
theorem msg_fallback_sig_new {l} {i : node} 
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_fallback_sig i  = true)
    (hold : ¬ s.msg_fallback_sig i  = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_fallback_sig [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_commit_pos_sig` row of a correct sender comes from a gated rule. -/
theorem msg_commit_pos_sig_new {l} {i : node} {j : node} {m : merkle_root}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_commit_pos_sig i j m = true)
    (hold : ¬ s.msg_commit_pos_sig i j m = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_commit_pos_sig [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_commit_neg_sig` row of a correct sender comes from a gated rule. -/
theorem msg_commit_neg_sig_new {l} {i : node} {j : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_commit_neg_sig i j = true)
    (hold : ¬ s.msg_commit_neg_sig i j = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_commit_neg_sig [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_commit_cast` row of a correct sender comes from a gated rule. -/
theorem msg_commit_cast_new {l} {i : node} 
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_commit_cast i  = true)
    (hold : ¬ s.msg_commit_cast i  = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_commit_cast [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_decrypt_share` row of a correct sender comes from a gated rule. -/
theorem msg_decrypt_share_new {l} {i : node} 
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_decrypt_share i  = true)
    (hold : ¬ s.msg_decrypt_share i  = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_decrypt_share [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_fbcommit_sig` row of a correct sender comes from a gated rule. -/
theorem msg_fbcommit_sig_new {l} {i : node} {e : mentries}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_fbcommit_sig i e = true)
    (hold : ¬ s.msg_fbcommit_sig i e = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_fbcommit_sig [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_chunk` row of a correct sender comes from a gated rule: the proposal, or a positive fallback entry. -/
theorem msg_chunk_new {l} {i : node} {r j : node} {m : merkle_root}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_chunk i r j m = true)
    (hold : ¬ s.msg_chunk i r j m = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_chunk [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_commitqc_pos` row of a correct sender comes from a gated rule: the collector's, or a finalization's re-broadcast. -/
theorem msg_commitqc_pos_new {l} {i : node} {j : node} {m : merkle_root}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_commitqc_pos i j m = true)
    (hold : ¬ s.msg_commitqc_pos i j m = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_commitqc_pos [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_commitqc_neg` row of a correct sender comes from a gated rule. -/
theorem msg_commitqc_neg_new {l} {i : node} {j : node}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_commitqc_neg i j = true)
    (hold : ¬ s.msg_commitqc_neg i j = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_commitqc_neg [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_fbcommitqc` row of a correct sender comes from a gated rule: the collector's, or a finalization's re-broadcast. -/
theorem msg_fbcommitqc_new {l} {i : node} {e : mentries}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_fbcommitqc i e = true)
    (hold : ¬ s.msg_fbcommitqc i e = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_fbcommitqc [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

set_option maxHeartbeats 4000000 in
/-- A new `msg_mvba_cert` row of a correct sender comes from a gated rule: the decision's output, or a finalization's re-broadcast. -/
theorem msg_mvba_cert_new {l} {i : node} {c : mmsg}
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : s'.msg_mvba_cert i c = true)
    (hold : ¬ s.msg_mvba_cert i c = true) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases l
  own_frame htr msg_mvba_cert [advance_to_deadline, advance_to_fb_arm, advance_to_mvba_arm, participate, abandon, propose, record_chunk, receive_vote_pos, receive_vote_neg, vote, aggregate_fastqc_pos, aggregate_fastqc_neg, commit_sign_pos, commit_sign_neg, cast_fast_commit, broadcast_commitqc_pos, broadcast_commitqc_neg, fb_sign_pos, fb_sign_neg, cast_fallback_vote, mvba_step, mvba_propose, send_mvba_cert, accept_mvba_commitqc, mvba_avail_ready, on_mvba_decide_pos, on_mvba_decide_neg, mvba_terminate, cast_fb_commit, broadcast_fbcommitqc, commit_assign_pos_fast, commit_assign_pos_fb, commit_assign_pos_mvba, commit_assign_neg_fast, commit_assign_neg_fb, commit_assign_neg_mvba, finalize_commit, byz_sign_proposer, byz_send_chunk, byz_redisseminate_chunk, byz_sign_vote_pos, byz_carry_vote_chunk, byz_sign_vote_neg, byz_cast_vote, byz_sign_fb_pos, byz_sign_fb_neg, byz_sign_fallback, byz_sign_commit_pos, byz_sign_commit_neg, byz_cast_commit, byz_broadcast_commitqc_pos, byz_broadcast_commitqc_neg, byz_sign_fbcommit, byz_broadcast_fbcommitqc, byz_send_mvba_cert, byz_release_msg_decrypt_share] => own_close

/-- **Quiescence, Chorus's own half**: a correct validator's new message of
its own (every constructor but `mvba`) is sent by a rule whose guard is the
participation gate, so the sender is actively participating in the
pre-state. One step, read from the transition bodies, with no invariant. -/
theorem own_sent_new {l} {i : node} {msg : Message node merkle_root mentries mmsg}
    (hm : ∀ c, msg ≠ .mvba c)
    (htr : (Chorus.relationalTransitionSystem slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice).tr th s l s')
    (hi : ¬ nset.is_byz i = true) (hnew : Sent s' i msg) (hold : ¬ Sent s i msg) :
    s.participating i = true ∧ s.abandoned i = false := by
  cases msg with
  | proposal m => exact msg_proposer_signed_new htr hi hnew hold
  | votePos j m => exact msg_vote_pos_sig_new htr hi hnew hold
  | voteNeg j => exact msg_vote_neg_sig_new htr hi hnew hold
  | voteCast => exact msg_vote_cast_new htr hi hnew hold
  | voteChunk j m => exact msg_vote_chunk_new htr hi hnew hold
  | fbPos j m => exact msg_fb_pos_sig_new htr hi hnew hold
  | fbNeg j => exact msg_fb_neg_sig_new htr hi hnew hold
  | fallback => exact msg_fallback_sig_new htr hi hnew hold
  | commitPos j m => exact msg_commit_pos_sig_new htr hi hnew hold
  | commitNeg j => exact msg_commit_neg_sig_new htr hi hnew hold
  | commitCast => exact msg_commit_cast_new htr hi hnew hold
  | decryptShare => exact msg_decrypt_share_new htr hi hnew hold
  | fbCommit e => exact msg_fbcommit_sig_new htr hi hnew hold
  | chunk r j m => exact msg_chunk_new htr hi hnew hold
  | commitqcPos j m => exact msg_commitqc_pos_new htr hi hnew hold
  | commitqcNeg j => exact msg_commitqc_neg_new htr hi hnew hold
  | fbCommitQC e => exact msg_fbcommitqc_new htr hi hnew hold
  | mvbaCert c => exact msg_mvba_cert_new htr hi hnew hold
  | mvba c => exact absurd rfl (hm c)

end Quiescence
end Chorus

/-! ## The pinned trust base

The instance rests on the standard Lean trio and nothing else — in
particular, **no `sorryAx`**: no trusted-SMT step and no statement stub
anywhere in the chain. The Chorus model persists no per-VC theorems (its
VC *statements* are carried claim-free by the persistent VC registry);
the composition consumes the **proof-file family** ([Chorus/Proofs](Proofs)):
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

/--
info: 'Chorus.certified_available_chunks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.certified_available_chunks

/--
info: 'Chorus.own_sent_new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.own_sent_new

/--
info: 'Chorus.local_committed_pos_implies_decodable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.local_committed_pos_implies_decodable
