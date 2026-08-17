import Cadence.Chorus.Certify
import Cadence.Interfaces

/-! # ChorusCompose — C4: `Chorus ⊨ SlotConsensus`

The final leg of the C4 composition layer (`docs/ConductorPlan.md` §5.2),
unblocked 2026-07-07 by trusted statement-only `#gen_theorems`
persistence (Build #14): from any reachable state of the Chorus
transition system, the per-proposer commit decisions of a committed
validator assemble into a *proposal vector*, and the result is a
`SlotConsensus` structure ([`Interfaces.lean`](../Interfaces.lean)) whose
three formal contract fields are discharged by Chorus's proven safety
properties:

| `SlotConsensus` field | discharged by |
|---|---|
| `agreement` | `safety [agreement_pos]` + `[agreement_pos_neg]` + `invariant [local_committed_complete]` |
| `slot_safety` | trivial (single-slot model: every vector carries the instance's slot by construction) |
| `proposal_inclusion` | `safety [proposal_inclusion]` + `[proposal_inclusion_no_neg]` + `invariant [local_committed_complete]` |

all consumed through the named reachability projections of
[`Chorus/Certify.lean`](./Certify.lean) (emitted by
`#gen_composition` from the proof-file family's preservation lemmas).

**The proposal-vector construction** (the "granularity note" of
`Interfaces.lean`): `pvector := node → Option merkle_root`, and a
committed validator's vector maps each proposer `J` to its committed
positive root (`some M` iff `local_committed_pos i J M`), and every
non-proposer to `none`. The `is_proposer` gate is load-bearing: the
module's invariant clump does not record "committed entries exist only
for proposers" (it is a guard of `commit_assign_*`), so agreement at
non-proposer indices holds by construction rather than by invariant.
`finalized i V` requires `local_committed i` — the paper's
`finalize(V)` output — and pins `V` to the vector; `on_time_proposal`
is the module's `all_honest_recorded` synchrony-premise ghost, exactly
as documented in the `SlotConsensus` obligation table.

Temporal obligations (ℓ-Termination, `d_tot`-totality, Quiescence)
remain the documented meta-axioms of `Interfaces.lean` — this file adds
no claim about them.

Trust base: `[propext, Classical.choice, Quot.sound]` — the standard Lean
trio, nothing else — pinned by the `#guard_msgs` axiom check at the end of
this file. Since 2026-07-13 (M6) the composition consumes the proof-file
family (`Chorus/Proofs/`, via `Chorus/Certify.lean`'s `#gen_composition`):
every VC statement re-created from the persistent registry, solved as a
fresh kernel-checked reconstruction, assembled per action into a
preservation lemma, and composed — kernel-checked at every `addDecl` —
inside Veil. -/

-- NOTE: deliberately NO `open Veil` here — it activates the Veil DSL's
-- scoped keywords, one of which (`includes`) collides with the
-- `SlotConsensus` field name in the `where` block below. Veil names are
-- used fully qualified instead.

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

variable (th : Chorus.Theory slot node nodeset merkle_root Phase PathChoice)
  (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice))

/-- `i` has committed a positive entry `⟨J, M⟩` (state read at the canonical
representation). -/
private abbrev committedPos (i J : node) (M : merkle_root) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_committed_pos)
    st.local_committed_pos i J M = true

/-- `i` has finalized (`local_committed`). -/
private abbrev committedAll (i : node) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Chorus.State.Label.local_committed)
    st.local_committed i = true

/-- The proposal vector a committed validator holds: each proposer maps to
its committed positive root (if any), every non-proposer to `none`. -/
noncomputable def decisionVector (i : node) : node → Option merkle_root :=
  fun J =>
    if th.is_proposer J = true then
      if hpos : ∃ M, committedPos st i J M then some hpos.choose else none
    else none

set_option maxHeartbeats 1000000 in
/-- **`Chorus ⊨ SlotConsensus`** — any reachable Chorus state induces a
`SlotConsensus` contract instance (`docs/ConductorPlan.md` §5.2): validators'
finalization outputs are their decision vectors, and the contract's three
formal fields are Chorus's proven safety properties, projected out of
`invariants_of_reachable`. -/
noncomputable def slotConsensus_instance
    (h : (Chorus.relationalTransitionSystem slot node nodeset merkle_root Phase PathChoice).reachable th st) :
    SlotConsensus slot node merkle_root (node → Option merkle_root) where
  inst_slot := default
  slot_of _ := default
  correct i := ¬ is_byz i = true
  finalized i V := committedAll st i ∧ V = decisionVector th st i
  includes V j P := V j = some P
  on_time_proposal j P := Chorus.all_honest_recorded (nset := nset)
    (χ := Chorus.FieldAbstractType slot node nodeset merkle_root Phase PathChoice) j P th st
  agreement := by
    intro i j V V' hci hcj hfi hfj
    obtain ⟨hci_com, hVi⟩ := hfi
    obtain ⟨hcj_com, hVj⟩ := hfj
    subst hVi; subst hVj
    funext J
    unfold decisionVector
    by_cases hp : th.is_proposer J = true
    · rw [if_pos hp, if_pos hp]
      by_cases hi : ∃ M, committedPos st i J M
      · -- `i` decided positively: so does `j` (completeness + pos/neg
        -- exclusion), and the roots agree.
        have hj' : ∃ M, committedPos st j J M := by
          rcases reachable_local_committed_complete h j ⟨hcj, hcj_com⟩ J hp with hpos | hneg
          · exact hpos
          · obtain ⟨Mi, hMi⟩ := hi
            exact absurd hneg
              (reachable_agreement_pos_neg h i j J Mi ⟨hci, hcj, hci_com, hcj_com, hMi⟩)
        rw [dif_pos hi, dif_pos hj']
        congr 1
        exact reachable_agreement_pos h i j J hi.choose hj'.choose
          ⟨hci, hcj, hci_com, hcj_com, hi.choose_spec, hj'.choose_spec⟩
      · -- `i` decided negatively (completeness): so must `j`.
        have hj' : ¬ ∃ M, committedPos st j J M := by
          rintro ⟨M, hM⟩
          rcases reachable_local_committed_complete h i ⟨hci, hci_com⟩ J hp with hpos | hneg
          · exact hi hpos
          · exact (reachable_agreement_pos_neg h j i J M ⟨hcj, hci, hcj_com, hci_com, hM⟩) hneg
        rw [dif_neg hi, dif_neg hj']
    · rw [if_neg hp, if_neg hp]
  slot_safety := by
    intro _ _ _ _
    rfl
  proposal_inclusion := by
    intro i j V P hci hfi hot
    obtain ⟨hcom, hV⟩ := hfi
    subst hV
    show decisionVector th st i j = some P
    have hp : th.is_proposer j = true := hot.2.1
    unfold decisionVector
    rw [if_pos hp]
    have hex : ∃ M, committedPos st i j M := by
      rcases reachable_local_committed_complete h i ⟨hci, hcom⟩ j hp with hpos | hneg
      · exact hpos
      · exact absurd hneg (reachable_proposal_inclusion_no_neg h j i P ⟨hot, hci⟩)
    rw [dif_pos hex]
    congr 1
    exact reachable_proposal_inclusion h j i P hex.choose ⟨hot, hci, hex.choose_spec⟩

end Instance
end Chorus

/-! ## The pinned trust base

The instance rests on the standard Lean trio and nothing else — in
particular, **no `sorryAx`**: no trusted-SMT step and no statement stub
anywhere in the chain. The Chorus model persists no per-VC theorems (its
VC *statements* are carried claim-free by the persistent VC registry);
the composition consumes the **proof-file family** (`Chorus/Proofs/`,
M6 2026-07-13): one file per action, each re-proving its action's
registered VC statements from scratch as fresh kernel-checked
reconstructions (`veil.smt.trust false`), persisted as real proofs in
small per-file oleans and assembled into one preservation lemma. A
regression anywhere in that chain — a proof silently degrading to a
stub, trusted SMT reappearing — fails this guard. -/

/--
info: 'Chorus.slotConsensus_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.slotConsensus_instance
