import Cadence.Chorus.Compose
import Cadence.Mvba.Liveness

/-! # Chorus/Liveness — the run-level target for Chorus, and the premises it rests on

[Liveness.md](../../docs/Liveness.md) §4, stage 2. This file states
the run-level termination claim for Chorus at the system's instantiation —
the MVBA constraint filled by the `Mvba` model, as in
[System.lean](../System.lean) — **and every premise it takes**, as named
`Prop`s. The proof is [Termination.lean](Termination.lean), which adds no
premise. Its sibling is [Mvba/Liveness.lean](../Mvba/Liveness.lean): same
discipline, same shape, and its `Mvba.termination` is what the MVBA arm of
the argument consumes.

`grep -n '^def [A-Z]' Cadence/Chorus/Liveness.lean` prints the whole list:
the six label classes, the certificate predicate the bridge premise is
stated with, the five premises, the target and the claim, and nothing else.
Everything a human has to believe about scheduling, about the seam between
Chorus and its MVBA, or about the caller is one of those definitions, with
a docstring, and appears as an explicit hypothesis of `TerminationClaim`.

## What this makes formal

[Chorus.lean](../Chorus.lean)'s liveness section states three meta-axioms in
prose — (F-justice), (F-byz), (A-mvba) — over the state-level theorems
([Chorus/Progress.lean](Progress.lean), [Chorus/Counting.lean](Counting.lean),
[Chorus/Pigeonhole.lean](Pigeonhole.lean)). Here (F-justice) and (F-byz) become the label classification below and one
named premise, exactly as in the MVBA file; and (A-mvba) — "the MVBA
terminates" — is **retired** in favour of what it stood for: the MVBA's own
liveness theorem, applied to the composed run's MVBA projection
([Fairness.lean](../Fairness.lean), "Components"), under the MVBA's own scheduling
premises. What is assumed about the MVBA is then not that it terminates
but that its steps inside the composed run were scheduled the way
`Mvba.termination` requires (`MvbaAdmissible` below) — the untimed analogue
of `MVBATemporal.Admissible`.

## The five premises, and why each is one

Three are about the run's scheduling and the MVBA seam; two are about the
caller, and they are exactly the antecedents of the contract's own
`SlotConsensusTemporal.termination`.


* **(F-justice)** — `FJustice`: every honest label that is neither the
  oracle step nor one of the module's three inputs is weakly fair for the
  messages of correct senders, the MVBA proposal as one family per
  validator and value and the decision handoff as one family per receiver.
  Weakly fair means: if it is enabled from some point on, and what it
  consumes came from correct validators (`Owed`), it fires
  ([Fairness.lean](../Fairness.lean)). The premise asks nothing of a
  Byzantine validator's messages, which may reach some validators only.
  The classification is
  the `match` definitions below; the reasons weak fairness suffices are
  [Liveness.md](../../docs/Liveness.md) §2, and why the proposal is a family is §4.6
  (Finding 2). The inputs are excluded on purpose (`InputLabel` says why).
  Every fair action fires once, so whenever a fair label is enabled it can
  change the state (`justice_enabledMove`, "Every enabled fair label changes
  the state" below); that is what keeps the premise satisfiable at every
  quorum sort, and it makes it the same premise as weak fairness over
  state-changing steps (`fJustice_iff_move`).
* **The MVBA's scheduling** — `MvbaAdmissible`: the run *has* a projection
  onto the MVBA (a labelling of its steps plus infinitely many of them —
  `Component.Projection`, whose header says why both are data) whose
  projected run satisfies `Mvba.FJustice` and `Mvba.AViewSync`. Those are
  two of `Mvba.termination`'s six premises, stated with that file's own
  definitions and restated nowhere. The other four — every correct
  validator proposes, none is abandoned before deciding, decided
  certificates are handed on, and the availability shares arrive — are the
  *caller's* premises and the caller is Chorus, so they are **derived** in
  [Termination.lean](Termination.lean), not assumed: the first from (F-justice) on
  `mvba_propose` and the progress analysis, the second from
  `NoAbandonBeforeFinalizing` on the branch of the proof where no correct
  validator finalizes (the MVBA's `abandon()` is invoked only by Chorus's
  `abandon`, Algorithm 5, line 48 (`line:fb-abandon`)), the third from (F-justice) on the handoff
  `accept_mvba_commitqc` (`fRelay_of_fJustice`), and the fourth from
  (F-justice) on the availability report `mvba_avail_ready`, whose chunk wait
  the correct FallbackQC signers met when they signed (`fAvail_of_fJustice`). The
  premise is unconditional, as before: the proof uses the MVBA only on
  that branch.
* **The bridge** — `ValidBridge`: the MVBA's `Valid` agrees with Chorus's
  certificate check. Chorus consumes the MVBA through the class
  `MVBASafety`, whose `Valid` is a predicate on values alone, while the
  paper's `Valid B` inspects the certificates a meta-block *carries* — in
  the model, facts about Chorus's network relations. The two are tied by
  the **one stated bridge** of [CompositionContracts.md](../../docs/CompositionContracts.md) §3, and a
  liveness proof needs it in both directions: *soundness* — a vector every
  one of whose proposer entries is certificate-backed on the network is
  `Valid`, which is what lets `mvba_propose` fire at all, since at the
  `Mvba` instance the contract's `propose` is `Mvba.propose`, whose guard
  requires `valid e`; and *completeness* — a vector a correct
  validator decided has every proposer entry certificate-backed, which is
  what enables the decision handlers, whose bridge `require` is that
  check. The safety proofs need neither direction (the guard only removes
  behaviours, and `external_validity` is proven from `Mvba`'s own check).
  This is the run-level form of the seam [CompositionContracts.md](../../docs/CompositionContracts.md) §7
  item 1 names, and it is a statement about the MVBA theory's `valid`
  meeting Chorus's network — the cryptographic content that a certificate
  cannot be forged — not about either model alone.
* **Every correct validator participates** — `AllParticipate`: each
  eventually invokes `participate()`. Within Cadence the glue does so when
  it opens the slot.
* **No correct validator abandons before finalizing** —
  `NoAbandonBeforeFinalizing`. Within Cadence the glue abandons only after
  finalizing. Every sending rule, finalization included, is gated on
  active participation, so without this premise a validator that abandons
  at once never finalizes.

## What is deliberately absent

No timing premise: Chorus's phase markers are weakly fair like every other
honest action, and [Liveness.md](../../docs/Liveness.md) §2.1 says why that is sound here and
not in the MVBA. No `all_honest_recorded`-shaped premise: it buys proposal
inclusion, not termination. No quorum machinery: the concrete quorum family
(`byzNodeSetFin`, every `n = 3f+1`) that the counting theorems are stated
over is a hypothesis of the *theorem* to come, not part of the claim.

## The classification, against the model's prose

[Chorus.lean](../Chorus.lean)'s liveness section lists (F-justice)'s actions by name. The
definition here is the complement of the other three classes, which is the
checkable form (adding an action and forgetting it here lands it in
`JusticeLabel`, visibly), and it agrees with that list. The list includes
`deliver_chunk_assigned` and `broadcast_commitqc_*`, which the chain in
[ChorusDesign.md](../../docs/ChorusDesign.md) §7 uses as fair ("certificates
become broadcast certificates"). Both are honest network
capabilities — eventual delivery of a correct proposer's chunk, assembly of
a certificate whose signatures are all present — and weak fairness on them
is the eventual-delivery assumption the paper makes. -/

namespace Chorus

open Cadence

/-! ## The label classes

Each `match` lists its actions by name, so the classification is checkable
by reading rather than by trusting a sentence. This section carries no
instances: a label is a syntactic object. -/

section Labels

variable {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}

/-- **(F-byz).** The labels the adversary controls — the `byz_*` family,
including its share of the two anonymous capabilities (assembling a commit
certificate, re-disseminating a decodable chunk), whose correct forms are the
fair `broadcast_commitqc_*` and the sends inside `fb_sign_pos`. No premise
requires anything of them, which *is* the assumption: progress never relies
on adversarial help. `not_justice_of_byz` pins the disjointness. -/
def ByzLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice → Prop
  | .byz_sign_proposer .. => True
  | .byz_deliver_chunk .. => True
  | .byz_redisseminate_chunk .. => True
  | .byz_sign_vote_pos .. => True
  | .byz_sign_vote_neg .. => True
  | .byz_cast_vote .. => True
  | .byz_sign_fb_pos .. => True
  | .byz_sign_fb_neg .. => True
  | .byz_sign_fallback .. => True
  | .byz_sign_commit_pos .. => True
  | .byz_sign_commit_neg .. => True
  | .byz_cast_commit .. => True
  | .byz_broadcast_commitqc_pos .. => True
  | .byz_broadcast_commitqc_neg .. => True
  | .byz_sign_fbcommit .. => True
  | .byz_release_msg_decrypt_share .. => True
  | _ => False

/-- **The oracle step** `mvba_step`: the MVBA's internal move, taken by the
composed system on the MVBA's behalf. It is outside (F-justice) — its
scheduling is the MVBA's own, and `MvbaAdmissible` is what says how it was
scheduled. `mvba_propose` is *not* here: it is Chorus's own honest action
(a correct validator proposing to the MVBA), weakly fair like the rest, even
though it also advances the MVBA's state — see `MvbaStepLabel`. -/
def OracleLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice → Prop
  | .mvba_step _ => True
  | _ => False

/-- **The module's three inputs**: `participate`, `abandon` and the
proposer's `propose` (Module 1 (`mod:slotconsensus`)). The caller invokes them, so they
carry no fairness. What the claim needs of the caller is stated as two
premises instead (`AllParticipate`, `NoAbandonBeforeFinalizing`).

Leaving them out of (F-justice) is not a detail. `JusticeLabel` is the
complement of the other classes, so an input missing here would silently
become weakly fair — and weak fairness of `abandon`, which is always
enabled at the `Mvba` instance, would force every validator to abandon.
This restates `Chorus.Label.isInput` ([Compose.lean](Compose.lean)) for the
reason `Mvba.InputLabel` gives; `not_justice_of_input` ties the two. -/
def InputLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice → Prop
  | .participate .. => True
  | .abandon .. => True
  | .propose .. => True
  | _ => False

/-- The labels (F-justice) covers: every honest action of the module —
phase advancement, dissemination and delivery, voting, aggregation, the two
paths, the MVBA proposal and the decision handlers, the commit round and
finalization — which is everything that is neither the adversary's, nor the
oracle step, nor one of the caller's inputs. -/
def JusticeLabel (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) : Prop :=
  ¬ ByzLabel l ∧ ¬ OracleLabel l ∧ ¬ InputLabel l

/-- **The labels at which the MVBA's state moves**: the oracle step and the
four driven inputs, `mvba_propose`, the handoff `accept_mvba_commitqc`, the
availability report `mvba_avail_ready`, and `abandon` (which forwards to
the MVBA's `abandon()`, Algorithm 5, line 48 (`line:fb-abandon`)).
This is the component's `isSub` (`mvbaComponent` below), a different cut
from the fairness classes — `mvba_propose` and `accept_mvba_commitqc` are
justice labels *and* MVBA steps, and they appear in the projected run as the
MVBA's own `propose` and `decide` labels, which `Mvba.FJustice` excludes
precisely because the caller schedules them. -/
def MvbaStepLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice → Prop
  | .mvba_step _ => True
  | .mvba_propose .. => True
  | .accept_mvba_commitqc .. => True
  | .mvba_avail_ready .. => True
  | .abandon .. => True
  | _ => False

/-- **The three families**: the MVBA proposal `mvba_propose i v mvba_next`,
the handoff `accept_mvba_commitqc i c mvba_next`, and the availability
report `mvba_avail_ready i v mvba_next`. Each is a justice label whose last
parameter is a *result*, the MVBA's state after the input, not a choice the
validator makes. `FJustice` therefore makes the proposal and the report
fair per validator and value, and the handoff per receiver, over the rest
of the parameters (`Cadence.WeaklyFairFamilyWhen`) rather than per label;
[Liveness.md](../../docs/Liveness.md) §4.6 (Finding 2) says why. -/
def FamilyLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice → Prop
  | .mvba_propose .. => True
  | .accept_mvba_commitqc .. => True
  | .mvba_avail_ready .. => True
  | _ => False

/-- **(F-byz), machine-checked at the only level it can be**: no label the
adversary controls is subject to a fairness hypothesis. -/
theorem not_justice_of_byz (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)
    (h : ByzLabel l) : ¬ JusticeLabel l := fun hj => hj.1 h

/-- The oracle step is not under (F-justice) either. -/
theorem not_justice_of_oracle (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)
    (h : OracleLabel l) : ¬ JusticeLabel l := fun hj => hj.2.1 h

/-- **No input is under (F-justice)** — stated against `Label.isInput`
([Compose.lean](Compose.lean)), the module's own notion of an input, which
is what the contract's `step` excludes. In particular `abandon` is not
weakly fair. -/
theorem not_justice_of_input (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)
    (h : Label.isInput l) : ¬ JusticeLabel l := by
  rcases Label.isInput_cases h with ⟨i, rfl⟩ | ⟨i, n, rfl⟩ | ⟨j, m, rfl⟩
  · exact fun hj => hj.2.2 trivial
  · exact fun hj => hj.2.2 trivial
  · exact fun hj => hj.2.2 trivial

/-- The classification is exhaustive — by construction, since `JusticeLabel`
is the complement of the other three; so this is a classical case split, and
what checks the action list is the three `match` definitions above. -/
theorem label_classified (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) :
    JusticeLabel l ∨ ByzLabel l ∨ OracleLabel l ∨ InputLabel l := by
  classical
  by_cases hb : ByzLabel l
  · exact Or.inr (Or.inl hb)
  by_cases ho : OracleLabel l
  · exact Or.inr (Or.inr (Or.inl ho))
  by_cases hi : InputLabel l
  · exact Or.inr (Or.inr (Or.inr hi))
  exact Or.inl ⟨hb, ho, hi⟩

/-- The oracle step moves the MVBA's state. -/
theorem mvbaStepLabel_of_oracle (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)
    (h : OracleLabel l) : MvbaStepLabel l := by
  cases l <;> trivial

/-- An MVBA step is the oracle step or one of the four driven inputs
(`mvba_propose`, the handoff, the availability report, and `abandon`'s
forwarding), and nothing else. -/
theorem mvbaStepLabel_iff (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) :
    MvbaStepLabel l ↔ (∃ m, l = .mvba_step m) ∨ (∃ i v m, l = .mvba_propose i v m) ∨
      (∃ i m, l = .abandon i m) ∨ (∃ i c m, l = .accept_mvba_commitqc i c m) ∨
      (∃ i v m, l = .mvba_avail_ready i v m) := by
  cases l <;> simp [MvbaStepLabel]

end Labels

section PhaseOrder

variable {Phase : Type} [Phase_Enum : Chorus.Phase_EnumClass Phase]

/-- The four phases are distinct (the enum's `distinct` field, unpacked). -/
theorem phase_distinct :
    (Phase_EnumClass.pre_deadline : Phase) ≠ Phase_EnumClass.post_deadline ∧
    (Phase_EnumClass.pre_deadline : Phase) ≠ Phase_EnumClass.post_fb_arm ∧
    (Phase_EnumClass.pre_deadline : Phase) ≠ Phase_EnumClass.post_mvba_arm ∧
    (Phase_EnumClass.post_deadline : Phase) ≠ Phase_EnumClass.post_fb_arm ∧
    (Phase_EnumClass.post_deadline : Phase) ≠ Phase_EnumClass.post_mvba_arm ∧
    (Phase_EnumClass.post_fb_arm : Phase) ≠ Phase_EnumClass.post_mvba_arm := by
  have hd := Phase_Enum.distinct
  simp [distinctN, distinctPairs, andN] at hd
  tauto

end PhaseOrder

/-! ## The MVBA is a component of Chorus

The instance of `Cadence.Component` for Chorus at the system's
instantiation, from which the projection of a Chorus run onto the MVBA and
the fairness transfer follow ([Fairness.lean](../Fairness.lean)). Its five fields come
from the generated artefacts and one hand proof — nothing here needs a new
cell:

* `frame` — Veil's generated per-action `Chorus.<action>.frame_mvba_st`, one per
  action that is not an MVBA step;
* `step` — the two oracle actions' guards, read off their transition
  bodies: `mvba_step` requires `mvba.step`, which at the `Mvba` instance is
  "some non-input label's transition", and `mvba_propose` requires
  `mvba.propose`, the `propose` label's;
* `init` — `mvba_st` is seeded from the theory's `mvba_init_state`, not a
  literal, so there is no generated `mvba_st.init`; the value is read off
  the initializer's transition. At the `Mvba` instance Chorus's
  `[mvba_init]` assumption is exactly the part's `assumptions ∧ init`. -/

section Component

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  -- The quorum counting facts Chorus consumes (its `cnt` class constraint).
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

/-- **Chorus at the `Mvba` instance**: the module's transition system with its
MVBA constraint filled by `Mvba.mvbaSafety thM`, the abstract sorts at the
`Mvba` model's own types — the value is the meta-block representation
`MetaBlock node merkle_root`, the entry vector `node → Option merkle_root`,
the state the model's, the message type the model's ([System.lean](../System.lean), "Chorus at the `Mvba`
instance"). Every run-level statement in this file is about this system. -/
noncomputable abbrev atMvba (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view) :=
  Chorus.relationalTransitionSystem slot node nodeset merkle_root
    (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
    (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice
    (mvba := Mvba.mvbaSafety thM)

/-- The `Mvba` model's own transition system, the component's `sub`. -/
noncomputable abbrev mvbaRTS :=
  Mvba.relationalTransitionSystem node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view

variable {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}
  {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)}

/-- Expose an action's transition body ([Composition.lean](../Composition.lean)'s
`conductor_tr`, for Chorus). -/
local macro "chorus_tr" h:ident : tactic =>
  `(tactic| (simp only [Chorus.relationalTransitionSystem, Chorus.Next, Chorus.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation, in every hypothesis and the goal. -/
local macro "chorus_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
      instIsSubReaderOfRefl.readFrom_id] at *)

set_option maxHeartbeats 1000000 in
/-- Every action other than the two MVBA steps leaves `mvba_st` alone: the
generated per-action frame lemmas, one `case` each. (The `MVBASafety`
instance is a *term* at this instantiation, so it is put in scope first; and
the dispatch is by named case rather than a `first` over the lemmas, which
makes the unifier unfold the transition system at every miss.) -/
theorem mvba_st_frame_of_not_step
    (l : Chorus.Label slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (htr : (atMvba thM).tr thS s l s') (hl : ¬ MvbaStepLabel l) : s'.mvba_st = s.mvba_st := by
  letI : MVBASafety node (MetaBlock node merkle_root) (node → Option merkle_root)
      (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      nodeset nset (fun i => nset.is_byz i = true) := Mvba.mvbaSafety thM
  cases l
  case mvba_step => exact absurd trivial hl
  case mvba_propose => exact absurd trivial hl
  case accept_mvba_commitqc => exact absurd trivial hl
  case mvba_avail_ready => exact absurd trivial hl
  case abandon => exact absurd trivial hl
  case participate => exact Chorus.participate.frame_mvba_st htr
  case advance_to_deadline => exact Chorus.advance_to_deadline.frame_mvba_st htr
  case advance_to_fb_arm => exact Chorus.advance_to_fb_arm.frame_mvba_st htr
  case advance_to_mvba_arm => exact Chorus.advance_to_mvba_arm.frame_mvba_st htr
  case propose => exact Chorus.propose.frame_mvba_st htr
  case deliver_chunk_assigned => exact Chorus.deliver_chunk_assigned.frame_mvba_st htr
  case record_chunk => exact Chorus.record_chunk.frame_mvba_st htr
  case vote => exact Chorus.vote.frame_mvba_st htr
  case aggregate_fastqc_pos => exact Chorus.aggregate_fastqc_pos.frame_mvba_st htr
  case aggregate_fastqc_neg => exact Chorus.aggregate_fastqc_neg.frame_mvba_st htr
  case commit_sign_pos => exact Chorus.commit_sign_pos.frame_mvba_st htr
  case commit_sign_neg => exact Chorus.commit_sign_neg.frame_mvba_st htr
  case cast_fast_commit => exact Chorus.cast_fast_commit.frame_mvba_st htr
  case broadcast_commitqc_pos => exact Chorus.broadcast_commitqc_pos.frame_mvba_st htr
  case broadcast_commitqc_neg => exact Chorus.broadcast_commitqc_neg.frame_mvba_st htr
  case fb_sign_pos => exact Chorus.fb_sign_pos.frame_mvba_st htr
  case fb_sign_neg => exact Chorus.fb_sign_neg.frame_mvba_st htr
  case cast_fallback_vote => exact Chorus.cast_fallback_vote.frame_mvba_st htr
  case on_mvba_decide_pos => exact Chorus.on_mvba_decide_pos.frame_mvba_st htr
  case on_mvba_decide_neg => exact Chorus.on_mvba_decide_neg.frame_mvba_st htr
  case on_mvba_commitqc_pos => exact Chorus.on_mvba_commitqc_pos.frame_mvba_st htr
  case on_mvba_commitqc_neg => exact Chorus.on_mvba_commitqc_neg.frame_mvba_st htr
  case mvba_terminate => exact Chorus.mvba_terminate.frame_mvba_st htr
  case cast_fb_commit => exact Chorus.cast_fb_commit.frame_mvba_st htr
  case commit_assign_pos => exact Chorus.commit_assign_pos.frame_mvba_st htr
  case commit_assign_neg => exact Chorus.commit_assign_neg.frame_mvba_st htr
  case finalize_commit => exact Chorus.finalize_commit.frame_mvba_st htr
  case byz_sign_proposer => exact Chorus.byz_sign_proposer.frame_mvba_st htr
  case byz_deliver_chunk => exact Chorus.byz_deliver_chunk.frame_mvba_st htr
  case byz_sign_vote_pos => exact Chorus.byz_sign_vote_pos.frame_mvba_st htr
  case byz_sign_vote_neg => exact Chorus.byz_sign_vote_neg.frame_mvba_st htr
  case byz_cast_vote => exact Chorus.byz_cast_vote.frame_mvba_st htr
  case byz_sign_fb_pos => exact Chorus.byz_sign_fb_pos.frame_mvba_st htr
  case byz_sign_fb_neg => exact Chorus.byz_sign_fb_neg.frame_mvba_st htr
  case byz_sign_fallback => exact Chorus.byz_sign_fallback.frame_mvba_st htr
  case byz_sign_commit_pos => exact Chorus.byz_sign_commit_pos.frame_mvba_st htr
  case byz_sign_commit_neg => exact Chorus.byz_sign_commit_neg.frame_mvba_st htr
  case byz_cast_commit => exact Chorus.byz_cast_commit.frame_mvba_st htr
  case byz_sign_fbcommit => exact Chorus.byz_sign_fbcommit.frame_mvba_st htr
  case byz_redisseminate_chunk => exact Chorus.byz_redisseminate_chunk.frame_mvba_st htr
  case byz_broadcast_commitqc_pos => exact Chorus.byz_broadcast_commitqc_pos.frame_mvba_st htr
  case byz_broadcast_commitqc_neg => exact Chorus.byz_broadcast_commitqc_neg.frame_mvba_st htr
  case byz_release_msg_decrypt_share => exact Chorus.byz_release_msg_decrypt_share.frame_mvba_st htr

set_option maxHeartbeats 1000000 in
/-- `mvba_step`'s guard is `mvba.step`, which at the `Mvba` instance is some
non-input label's transition. -/
theorem mvba_step_tr {mvba_next}
    (htr : (atMvba thM).tr thS s (.mvba_step mvba_next) s') :
    ∃ l', (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      s.mvba_st l' s'.mvba_st := by
  chorus_tr htr
  obtain ⟨hstep, htr⟩ := htr
  chorus_field_simp
  obtain ⟨l', -, hl'⟩ := hstep
  subst htr
  exact ⟨l', hl'⟩

set_option maxHeartbeats 1000000 in
/-- `mvba_propose`'s last guard is `mvba.propose`, the `propose` label's
transition. -/
theorem mvba_propose_tr {i v mvba_next}
    (htr : (atMvba thM).tr thS s (.mvba_propose i v mvba_next) s') :
    (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      s.mvba_st (.propose i v) s'.mvba_st := by
  chorus_tr htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨hprop, htr⟩ := htr
  chorus_field_simp
  subst htr
  exact hprop

set_option maxHeartbeats 1000000 in
/-- `abandon`'s guard is `mvba.abandon`, the MVBA's `abandon` label's
transition: the forwarding of Algorithm 5, line 48 (`line:fb-abandon`). -/
theorem abandon_tr {i mvba_next}
    (htr : (atMvba thM).tr thS s (.abandon i mvba_next) s') :
    (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      s.mvba_st (.abandon i) s'.mvba_st := by
  chorus_tr htr
  obtain ⟨hab, htr⟩ := htr
  chorus_field_simp
  subst htr
  exact hab

set_option maxHeartbeats 1000000 in
/-- The availability report's last guard is `mvba.markAvail`, the `Mvba`
model's `become_avail_ready` label's transition. -/
theorem mvba_avail_ready_tr {i v mvba_next}
    (htr : (atMvba thM).tr thS s (.mvba_avail_ready i v mvba_next) s') :
    (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
      s.mvba_st (.become_avail_ready i v) s'.mvba_st := by
  chorus_tr htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨-, htr⟩ := htr
  obtain ⟨hav, htr⟩ := htr
  chorus_field_simp
  subst htr
  exact hav

set_option maxHeartbeats 1000000 in
/-- The handoff's guard is `mvba.accept`, which at the `Mvba` instance is the
model's `decide` on the transferred certificate, deciding a representation
of its entries. -/
theorem accept_mvba_commitqc_tr {i c mvba_next}
    (htr : (atMvba thM).tr thS s (.accept_mvba_commitqc i c mvba_next) s') :
    ∃ w e x, c = .commitqc w e ∧ thM.ent x = e ∧
      (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)).tr thM
        s.mvba_st (.decide i w x) s'.mvba_st := by
  chorus_tr htr
  obtain ⟨-, -, hacc, htr⟩ := htr
  chorus_field_simp
  subst htr
  cases c
  case commitqc w e =>
    have h' : Mvba.Accept thM s.mvba_st i (.commitqc w e) mvba_next := hacc
    obtain ⟨x, hx, h⟩ := h'
    -- The goal was simplified with `e` eliminated through `thM.ent x = e`.
    subst hx
    exact ⟨w, x, rfl, h⟩
  all_goals exact (hacc : False).elim

set_option maxHeartbeats 1000000 in
/-- The initial value of `mvba_st`, read off the initializer's transition. -/
theorem mvba_st_init (hi : (atMvba thM).init thS s) : s.mvba_st = thS.mvba_init_state := by
  simp only [Chorus.relationalTransitionSystem, Chorus.Init, Chorus.initializer.ext.tr] at hi
  subst_vars
  chorus_field_simp

/-- **The MVBA is a component of Chorus**, at the system's instantiation. -/
noncomputable def mvbaComponent
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view) :
    Component (atMvba thM) thS
      (mvbaRTS (node := node) (nodeset := nodeset) (merkle_root := merkle_root) (view := view)) thM where
  proj st := st.mvba_st
  isSub := MvbaStepLabel
  init s ha hi := by
    obtain ⟨hinit, -, -⟩ := ha
    rw [mvba_st_init hi]
    exact hinit
  frame _ l _ htr hl := mvba_st_frame_of_not_step l htr hl
  step _ l _ htr hl := by
    cases l with
    | mvba_step mvba_next => exact mvba_step_tr htr
    | mvba_propose i v mvba_next => exact ⟨.propose i v, mvba_propose_tr htr⟩
    | accept_mvba_commitqc i c mvba_next =>
      obtain ⟨w, e, x, -, -, h⟩ := accept_mvba_commitqc_tr htr
      exact ⟨.decide i w x, h⟩
    | abandon i mvba_next => exact ⟨.abandon i, abandon_tr htr⟩
    | mvba_avail_ready i v mvba_next => exact ⟨.become_avail_ready i v, mvba_avail_ready_tr htr⟩
    | _ => exact absurd hl id

/-! ## Every enabled fair label changes the state

The acceptance criterion of [Bounds.md](../../docs/Bounds.md) §6.4.7, for
Chorus: no fair action stays enabled after it has fired. Each honest action
of (F-justice) has a "not already" guard on a record it sets itself (or the
phase marker moves the phase), so whenever it can fire, firing it changes
that record. The consequence for the premises: for this model, weak fairness
over plain enabledness and weak fairness over state-changing steps
([Fairness.lean](../Fairness.lean)) are the same premise. `FJustice` is
stated with the first; `fJustice_iff_move`, from `justice_enabledMove`,
says it means the same as the second here.

One lemma per fair action says that its firing changes the state; each is
read off the action's transition body. -/

set_option maxHeartbeats 1000000 in
/-- The MVBA proposal changes the state: the `Mvba` model's `propose` guard
is that the validator has no input yet, and its effect records one. -/
theorem mvba_propose_moves {i : node} {v : MetaBlock node merkle_root} {n}
    (htr : (atMvba thM).tr thS s (.mvba_propose i v n) s') : s' ≠ s := by
  rintro rfl
  have hp := mvba_propose_tr htr
  have heff := Mvba.propose_effect_tr thM hp
  simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp] at hp
  exact hp.1 v heff

set_option maxHeartbeats 1000000 in
theorem advance_to_deadline_moves 
    (htr : (atMvba thM).tr thS s (.advance_to_deadline) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.phase) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem advance_to_fb_arm_moves 
    (htr : (atMvba thM).tr thS s (.advance_to_fb_arm) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.phase) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem advance_to_mvba_arm_moves 
    (htr : (atMvba thM).tr thS s (.advance_to_mvba_arm) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.phase) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem deliver_chunk_assigned_moves {i j : node} {m : merkle_root}
    (htr : (atMvba thM).tr thS s (.deliver_chunk_assigned i j m) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_chunk_sent j i j m) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem record_chunk_moves {i j : node} {m : merkle_root}
    (htr : (atMvba thM).tr thS s (.record_chunk i j m) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_entry_pos i j m) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem vote_moves {i : node}
    (htr : (atMvba thM).tr thS s (.vote i) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_voted i) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem aggregate_fastqc_pos_moves {i j : node} {m : merkle_root} {q : nodeset}
    (htr : (atMvba thM).tr thS s (.aggregate_fastqc_pos i j m q) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_fastqc_pos i j m) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem aggregate_fastqc_neg_moves {i j : node} {q : nodeset}
    (htr : (atMvba thM).tr thS s (.aggregate_fastqc_neg i j q) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_fastqc_neg i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem commit_sign_pos_moves {i j : node} {m : merkle_root}
    (htr : (atMvba thM).tr thS s (.commit_sign_pos i j m) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_commit_entry i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem commit_sign_neg_moves {i j : node}
    (htr : (atMvba thM).tr thS s (.commit_sign_neg i j) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_commit_entry i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem cast_fast_commit_moves {i : node}
    (htr : (atMvba thM).tr thS s (.cast_fast_commit i) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.msg_commit_cast i) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem broadcast_commitqc_pos_moves {c j : node} {m : merkle_root} {q : nodeset}
    (htr : (atMvba thM).tr thS s (.broadcast_commitqc_pos c j m q) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_commitqc_sent c j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem broadcast_commitqc_neg_moves {c j : node} {q : nodeset}
    (htr : (atMvba thM).tr thS s (.broadcast_commitqc_neg c j q) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_commitqc_sent c j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem fb_sign_pos_moves {i j : node} {m : merkle_root} {q qc : nodeset}
    (htr : (atMvba thM).tr thS s (.fb_sign_pos i j m q qc) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_fb_entry i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem fb_sign_neg_moves {i j : node} {qv : nodeset}
    (htr : (atMvba thM).tr thS s (.fb_sign_neg i j qv) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_fb_entry i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem cast_fallback_vote_moves {i : node}
    (htr : (atMvba thM).tr thS s (.cast_fallback_vote i) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_path i) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem on_mvba_decide_pos_moves {i j : node} {m : merkle_root} {v : MetaBlock node merkle_root}
    (htr : (atMvba thM).tr thS s (.on_mvba_decide_pos i j m v) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_mvba_recorded i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem on_mvba_decide_neg_moves {i j : node} {v : MetaBlock node merkle_root}
    (htr : (atMvba thM).tr thS s (.on_mvba_decide_neg i j v) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_mvba_recorded i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem on_mvba_commitqc_pos_moves {i j : node} {m : merkle_root} {c} {v : MetaBlock node merkle_root}
    (htr : (atMvba thM).tr thS s (.on_mvba_commitqc_pos i j m c v) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_mvba_recorded i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem on_mvba_commitqc_neg_moves {i j : node} {c} {v : MetaBlock node merkle_root}
    (htr : (atMvba thM).tr thS s (.on_mvba_commitqc_neg i j c v) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_mvba_recorded i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem mvba_avail_ready_moves {i : node} {v : MetaBlock node merkle_root} {n}
    (htr : (atMvba thM).tr thS s (.mvba_avail_ready i v n) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_avail_marked i v) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem mvba_terminate_moves {i : node} {v : MetaBlock node merkle_root}
    (htr : (atMvba thM).tr thS s (.mvba_terminate i v) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.mvba_complete) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem accept_mvba_commitqc_moves {i : node} {c : Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)} {n}
    (htr : (atMvba thM).tr thS s (.accept_mvba_commitqc i c n) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_mvba_qc_accepted i) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem cast_fb_commit_moves {i : node} {v}
    (htr : (atMvba thM).tr thS s (.cast_fb_commit i v) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_fbcommit_voted i) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem commit_assign_pos_moves {i j : node} {m : merkle_root}
    (htr : (atMvba thM).tr thS s (.commit_assign_pos i j m) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_committed_pos i j m) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem commit_assign_neg_moves {i j : node}
    (htr : (atMvba thM).tr thS s (.commit_assign_neg i j) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_committed_neg i j) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

set_option maxHeartbeats 1000000 in
theorem finalize_commit_moves {i : node}
    (htr : (atMvba thM).tr thS s (.finalize_commit i) s') : s' ≠ s := by
  rintro rfl
  chorus_tr htr
  repeat (obtain ⟨_, htr⟩ := htr)
  have h := congrArg (fun st => st.local_committed i) htr
  have hd := phase_distinct (Phase := Phase)
  chorus_field_simp
  simp_all

/-- **Every enabled fair label is move-enabled** — at every state, reachable
or not: whenever a label of (F-justice) can fire, it can fire to a
different state. This is [Bounds.md](../../docs/Bounds.md) §6.4.7's
acceptance criterion for Chorus, machine-checked: the model has no fair
action that stays enabled after it has fired, so for this model a label
that is enabled from some point on is also able to change the state from
that point on, and `FJustice` (over plain enabledness) asks exactly what
weak fairness over state-changing steps would (`fJustice_iff_move`). The MVBA
proposal is a justice label, so each member of its family is covered too
(`mvba_propose_enabledMove`). A label that failed it would need its fired-once
guard; none is dropped from `JusticeLabel`. -/
theorem justice_enabledMove
    (l : Chorus.Label slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (hl : JusticeLabel l) (hen : Enabled (atMvba thM) thS s l) : EnabledMove (atMvba thM) thS s l := by
  obtain ⟨s', htr⟩ := hen
  refine ⟨s', htr, ?_⟩
  cases l
  case advance_to_deadline => exact advance_to_deadline_moves htr
  case advance_to_fb_arm => exact advance_to_fb_arm_moves htr
  case advance_to_mvba_arm => exact advance_to_mvba_arm_moves htr
  case deliver_chunk_assigned => exact deliver_chunk_assigned_moves htr
  case record_chunk => exact record_chunk_moves htr
  case vote => exact vote_moves htr
  case aggregate_fastqc_pos => exact aggregate_fastqc_pos_moves htr
  case aggregate_fastqc_neg => exact aggregate_fastqc_neg_moves htr
  case commit_sign_pos => exact commit_sign_pos_moves htr
  case commit_sign_neg => exact commit_sign_neg_moves htr
  case cast_fast_commit => exact cast_fast_commit_moves htr
  case broadcast_commitqc_pos => exact broadcast_commitqc_pos_moves htr
  case broadcast_commitqc_neg => exact broadcast_commitqc_neg_moves htr
  case fb_sign_pos => exact fb_sign_pos_moves htr
  case fb_sign_neg => exact fb_sign_neg_moves htr
  case cast_fallback_vote => exact cast_fallback_vote_moves htr
  case on_mvba_decide_pos => exact on_mvba_decide_pos_moves htr
  case on_mvba_decide_neg => exact on_mvba_decide_neg_moves htr
  case on_mvba_commitqc_pos => exact on_mvba_commitqc_pos_moves htr
  case on_mvba_commitqc_neg => exact on_mvba_commitqc_neg_moves htr
  case mvba_avail_ready => exact mvba_avail_ready_moves htr
  case mvba_terminate => exact mvba_terminate_moves htr
  case cast_fb_commit => exact cast_fb_commit_moves htr
  case commit_assign_pos => exact commit_assign_pos_moves htr
  case commit_assign_neg => exact commit_assign_neg_moves htr
  case finalize_commit => exact finalize_commit_moves htr
  case mvba_propose => exact mvba_propose_moves htr
  case accept_mvba_commitqc => exact accept_mvba_commitqc_moves htr
  case byz_sign_proposer => exact absurd trivial hl.1
  case byz_deliver_chunk => exact absurd trivial hl.1
  case byz_redisseminate_chunk => exact absurd trivial hl.1
  case byz_sign_vote_pos => exact absurd trivial hl.1
  case byz_sign_vote_neg => exact absurd trivial hl.1
  case byz_cast_vote => exact absurd trivial hl.1
  case byz_sign_fb_pos => exact absurd trivial hl.1
  case byz_sign_fb_neg => exact absurd trivial hl.1
  case byz_sign_fallback => exact absurd trivial hl.1
  case byz_sign_commit_pos => exact absurd trivial hl.1
  case byz_sign_commit_neg => exact absurd trivial hl.1
  case byz_cast_commit => exact absurd trivial hl.1
  case byz_broadcast_commitqc_pos => exact absurd trivial hl.1
  case byz_broadcast_commitqc_neg => exact absurd trivial hl.1
  case byz_sign_fbcommit => exact absurd trivial hl.1
  case byz_release_msg_decrypt_share => exact absurd trivial hl.1
  case mvba_step => exact absurd trivial hl.2.1
  case participate => exact absurd trivial hl.2.2
  case abandon => exact absurd trivial hl.2.2
  case propose => exact absurd trivial hl.2.2

/-- **Every member of the MVBA proposal family is move-enabled when it is
enabled**: the family clause of `FJustice` asks nothing more than weak
fairness over state-changing steps would. -/
theorem mvba_propose_enabledMove {i : node} {v : MetaBlock node merkle_root} {n}
    (hen : Enabled (atMvba thM) thS s (.mvba_propose i v n)) :
    EnabledMove (atMvba thM) thS s (.mvba_propose i v n) :=
  justice_enabledMove _ ⟨fun h => h, fun h => h, fun h => h⟩ hen

/-- **Every member of the availability family is move-enabled when it is
enabled**, likewise. -/
theorem mvba_avail_ready_enabledMove {i : node} {v : MetaBlock node merkle_root} {n}
    (hen : Enabled (atMvba thM) thS s (.mvba_avail_ready i v n)) :
    EnabledMove (atMvba thM) thS s (.mvba_avail_ready i v n) :=
  justice_enabledMove _ ⟨fun h => h, fun h => h, fun h => h⟩ hen

/-- **Every member of the handoff family is move-enabled when it is
enabled**, likewise. -/
theorem accept_mvba_commitqc_enabledMove {i : node} {c : Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)} {n}
    (hen : Enabled (atMvba thM) thS s (.accept_mvba_commitqc i c n)) :
    EnabledMove (atMvba thM) thS s (.accept_mvba_commitqc i c n) :=
  justice_enabledMove _ ⟨fun h => h, fun h => h, fun h => h⟩ hen

end Component

/-! ## What a step is owed for: correct senders

The paper's network delivers "every message between correct validators"
(Proposition 5 (`prop:chorus-finalization-time`)'s proof). The model's network relations
hold from a message's first delivery to anyone, a Byzantine sender's
included, so a step that consumes a Byzantine validator's message would be
owed a delivery the paper does not promise: a Byzantine voter may send its
vote to some validators only. `Owed` is the condition under which the
paper's network owes the step, per label: the messages it consumes came from
correct validators. Each is a fact about who sent a message, never a
protocol conclusion. The untimed `FJustice` and the timed `TimedJustice`
([Schedule.lean](Schedule.lean)) take the same conditions, so the two read
alike. Stated for any MVBA, as the run-level chains of
[Termination.lean](Termination.lean) are. -/

section Owed

open Classical

variable {slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root]
  [Inhabited mstate] [Inhabited mvalue] [Inhabited mentries] [Inhabited mmsg]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset]
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [mvba : MVBASafety node mvalue mentries mmsg mstate nodeset nset (fun i => nset.is_byz i = true)]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

/-- A correct supermajority has broadcast its first-round votes. -/
def CorrectVotesCast
    (s : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) :
    Prop :=
  ∃ q, nset.supermajority q ∧ Mvba.CorrectQuorum (node := node) q ∧
    ∀ r, nset.member r q = true → s.msg_vote_cast r = true

/-- A correct supermajority has broadcast its fallback votes: `FBCert` from
correct senders. -/
def CorrectFBCert
    (s : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) :
    Prop :=
  ∃ q, nset.supermajority q ∧ Mvba.CorrectQuorum (node := node) q ∧
    ∀ r, nset.member r q = true → s.msg_fallback_sig r = true

/-- A correct supermajority has broadcast its fallback commit votes:
`fbCommitQC` from correct senders. -/
def CorrectFbCommitQC
    (s : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) :
    Prop :=
  ∃ q, nset.supermajority q ∧ Mvba.CorrectQuorum (node := node) q ∧
    ∀ r, nset.member r q = true → s.msg_fbcommit_sig r = true

/-- The MVBA proposal is owed when its trigger came from correct senders:
`FBCert` from a correct supermajority, or the proposer's own complete fast
meta-block, which is local. The certificates of a particular value need no
condition: if `i` proposes any value, every member of the family is disabled
for `i`. -/
def proposeOwed
    (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) (i : node)
    (s : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) :
    Prop :=
  CorrectFBCert s ∨ Chorus.complete_fast_metablock (nset := nset) (mvba := mvba) i th s

/-- The handoff is owed once a correct validator has decided: its decision
output carries the certificate (`mvba.decided_certified`), and Chorus
broadcasts it (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"). -/
def relayOwed
    (s : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice)) :
    Prop :=
  ∃ j v, ¬ nset.is_byz j = true ∧ mvba.decided s.mvba_st j v

/-- **What a step is owed for.** Per label, the condition under which the
environment owes the step at all.

* `aggregate_fastqc_*`: the vote quorum is correct, or a correct validator
  that cast its fast commit vote holds the FastQC — the same rule broadcasts
  its `FastBlock` (Algorithm 4, line 20 (`line:fast-metablock`)), whose FastQCs a receiver adopts;
* the other rows over a quorum parameter: the quorum is correct;
* `fb_sign_pos`: also the `2f+1` votes its guard counts, from correct voters.
  The same step re-encodes the proposal and sends every validator its chunk
  (Algorithm 5, line 12 (`line:fb-redisseminate`)), so re-dissemination has
  no row of its own. That rule is the main body's; the supplement's
  implementation replaces the re-encode-and-send by ChunkSync, which pulls
  the missing chunks within `Δ_sync` (Supplement, Section 1.2
  (`subsec:mvba-protocol`), Supplement, Section 7.4
  (`sec:fallback-transition`)), and the model follows the main body;
* the proposal: its trigger from correct senders (`proposeOwed`);
* the handoff and the `CommitQC` route's handlers: a correct validator has
  decided (`relayOwed`), and Chorus broadcasts that decision's certificate.
  The premise owes nothing on a certificate the adversary assembled and
  showed to nobody (F5);
* `commit_assign_*`: a commitment proof a correct validator sent — a correct
  validator's finalization re-broadcasts its proof
  (Algorithm 4, line 35 (`line:fast-rebroadcast-commitqc`), Algorithm 5, line 46 (`line:fb-commit-rebroadcast`)), and the
  fallback commit certificate from correct commit voters, over the decided
  entry;
* `cast_fb_commit i v`: the voter has decided `v` and no other
  representation. The paper's rule fires on the voter's own decision
  (Algorithm 5, line 37 (`line:fb-mvba-decide`)) and waits under that `B′`; under a redelivered
  decision with another representation the target does not say which `B′`
  the handler runs on (P11, [PaperAlignment.md](../../docs/PaperAlignment.md) §8.1 (d)), so the row
  owes nothing there, and never a vote the paper might not cast. The model's
  guard also reads the shared `mvba_complete`, which the first validator to
  decide sets;
* everything else: nothing (`True`). The chunk's delivery has a correct
  proposer by its guard, the decision handlers and `mvba_terminate` fire
  on the validator's own decision by theirs, and the availability report
  consumes only the validator's own chunk receipts. -/
def Owed (th : Chorus.Theory slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) :
    Chorus.Label slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice →
    Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root mstate mvalue mentries mmsg Phase PathChoice) →
      Prop
  | .aggregate_fastqc_pos _ j m q => fun s => Mvba.CorrectQuorum (node := node) q ∨
      ∃ k, ¬ nset.is_byz k = true ∧ s.msg_commit_cast k = true ∧ s.local_fastqc_pos k j m = true
  | .aggregate_fastqc_neg _ j q => fun s => Mvba.CorrectQuorum (node := node) q ∨
      ∃ k, ¬ nset.is_byz k = true ∧ s.msg_commit_cast k = true ∧ s.local_fastqc_neg k j = true
  | .broadcast_commitqc_pos _ _ _ q => fun _ => Mvba.CorrectQuorum (node := node) q
  | .broadcast_commitqc_neg _ _ q => fun _ => Mvba.CorrectQuorum (node := node) q
  | .fb_sign_pos _ _ _ q qc => fun s => Mvba.CorrectQuorum (node := node) q ∧
      Mvba.CorrectQuorum (node := node) qc ∧ CorrectVotesCast s
  | .fb_sign_neg _ _ qv => fun _ => Mvba.CorrectQuorum (node := node) qv
  | .mvba_propose i .. => proposeOwed th i
  | .accept_mvba_commitqc .. => relayOwed
  | .on_mvba_commitqc_pos .. => relayOwed
  | .on_mvba_commitqc_neg .. => relayOwed
  | .commit_assign_pos _ j m => fun s =>
      (∃ k, ¬ nset.is_byz k = true ∧ s.local_committed k = true ∧
        s.local_committed_pos k j m = true) ∨
      (CorrectFbCommitQC s ∧ s.mvba_decided_pos j m = true)
  | .commit_assign_neg _ j => fun s =>
      (∃ k, ¬ nset.is_byz k = true ∧ s.local_committed k = true ∧
        s.local_committed_neg k j = true) ∨
      (CorrectFbCommitQC s ∧ s.mvba_decided_neg j = true)
  | .cast_fb_commit i v => fun s => mvba.decided s.mvba_st i v ∧
      ∀ v', mvba.decided s.mvba_st i v' → v' = v
  | _ => fun _ => True

end Owed

/-! ## The premises, one named `Prop` each

From here on the full instance set is in scope: the premises talk about
states of the composed system. -/

section Runs

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  -- The quorum counting facts Chorus consumes (its `cnt` class constraint).
  [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view}

/-- A labelled run of Chorus at the `Mvba` instance: the object every premise
below is about. -/
abbrev ChorusRun
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view) :=
  LRun (atMvba (slot := slot) (Phase := Phase) (PathChoice := PathChoice) thM) thS

/-- The availability report is owed for a meta-block the validator holds:
the supplement's synchronization assumption is about "a valid meta-block `x`"
that "a correct validator `p_i` holds" (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Availability-synchronization assumption"), the
MVBA's accepted `x_v`. Read at the `Mvba` instance, since the abstract
module exposes no such observable ([PaperAlignment.md](../../docs/PaperAlignment.md) §6, P12). -/
def availOwed (i : node) (v : MetaBlock node merkle_root)
    (s : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)) :
    Prop :=
  ∃ w, s.mvba_st.accepted i w v = true

/-- **(F-justice)** — weak fairness of every honest action that is neither
the oracle step nor one of the three inputs, for the messages of correct
senders: if from some point on a correct validator's action is enabled at
every point, and the messages it consumes came from correct validators
(`Owed`), it eventually fires. The premise asks nothing of a step on a
Byzantine validator's message: such a message may reach some validators
only, and the paper's network promises delivery only between correct
validators.

Every such label is weakly fair on its own, except the two families. A
validator `i` proposing `v` is weakly fair as one family over the MVBA's
successor state, the label's result parameter — if `i` can propose `v` from
some point on, with its trigger from correct senders, it does. And the
handoff is one family per receiver `i` — once a correct validator has
decided, if `i` can take a transferred certificate from some point on, it
takes one.

Every fair action of this model fires once: its guard requires a record its
own step sets to be unset, so a fair label that is enabled can always
change the state (`justice_enabledMove`, at every state). That is why the
premise can hold at every quorum sort — a label that stayed enabled after
firing, one per quorum, would have to fire forever — and why it is the same
premise as weak fairness over state-changing steps, TLA+'s `WF_v`
(`fJustice_iff_move`). -/
def FJustice (r : ChorusRun thS thM) : Prop :=
  (∀ l, JusticeLabel l → ¬ FamilyLabel l →
    WeaklyFairWhen r (Owed (nset := nset) (mvba := Mvba.mvbaSafety thM) thS l) l) ∧
  (∀ i v, WeaklyFairFamilyWhen r (proposeOwed (nset := nset) (mvba := Mvba.mvbaSafety thM) thS i)
    (fun l => ∃ mvba_next, l = .mvba_propose i v mvba_next)) ∧
  (∀ i, WeaklyFairFamilyWhen r (relayOwed (nset := nset) (mvba := Mvba.mvbaSafety thM))
    (fun l => ∃ c mvba_next, l = .accept_mvba_commitqc i c mvba_next)) ∧
  ∀ i v, WeaklyFairFamilyWhen r (availOwed i v)
    (fun l => ∃ mvba_next, l = .mvba_avail_ready i v mvba_next)

/-- **The bridge**: for this model, (F-justice) over plain enabledness is the
same premise as weak fairness over state-changing steps (TLA+'s `WF_v`, the
form the premise had from R3 to R6), clause by clause, with the same
owed-conditions. -/
theorem fJustice_iff_move (r : ChorusRun thS thM) :
    FJustice r ↔
      (∀ l, JusticeLabel l → ¬ FamilyLabel l →
        WeaklyFairWhenMove r (Owed (nset := nset) (mvba := Mvba.mvbaSafety thM) thS l) l) ∧
      (∀ i v, WeaklyFairFamilyWhenMove r (proposeOwed (nset := nset) (mvba := Mvba.mvbaSafety thM) thS i)
        (fun l => ∃ mvba_next, l = .mvba_propose i v mvba_next)) ∧
      (∀ i, WeaklyFairFamilyWhenMove r (relayOwed (nset := nset) (mvba := Mvba.mvbaSafety thM))
        (fun l => ∃ c mvba_next, l = .accept_mvba_commitqc i c mvba_next)) ∧
      ∀ i v, WeaklyFairFamilyWhenMove r (availOwed i v)
        (fun l => ∃ mvba_next, l = .mvba_avail_ready i v mvba_next) := by
  refine and_congr (forall_congr' fun l => imp_congr_right fun hj => imp_congr_right fun _ =>
      weaklyFairWhen_iff_move fun _ => justice_enabledMove l hj)
    (and_congr (forall_congr' fun i => forall_congr' fun v =>
      weaklyFairFamilyWhen_iff_move fun _ l hl hen => ?_)
      (and_congr (forall_congr' fun i => weaklyFairFamilyWhen_iff_move fun _ l hl hen => ?_)
        (forall_congr' fun i => forall_congr' fun v =>
          weaklyFairFamilyWhen_iff_move fun _ l hl hen => ?_)))
  · obtain ⟨_, rfl⟩ := hl
    exact mvba_propose_enabledMove hen
  · obtain ⟨_, _, rfl⟩ := hl
    exact accept_mvba_commitqc_enabledMove hen
  · obtain ⟨_, rfl⟩ := hl
    exact mvba_avail_ready_enabledMove hen

/-- **The MVBA's scheduling premise**, replacing (A-mvba): the run has a
projection onto the MVBA — a labelling of its steps that explains them, and
infinitely many of them (`Component.Projection`) — whose projected run
satisfies the two scheduling premises of `Mvba.termination`: weak fairness
of the MVBA's honest actions, and the timer discipline of the good view.
Stated with [Mvba/Liveness.lean](../Mvba/Liveness.lean)'s own definitions. The theorem's other four
premises are the caller's, and the caller is Chorus, so they are derived,
not assumed (header): every correct validator proposes, none abandons
early, decided certificates are handed on, and availability (F-avail),
which Chorus reports itself (`mvba_avail_ready`).

The existential over the projection is the honest form: the composed run
records only the MVBA's post-states, so an assumption about how the MVBA's
*labels* were scheduled has to supply the labels. `Component.Projection.
weaklyFair_iff` says the fairness clause means the same thing read at the
composed run, so nothing is smuggled in by the re-indexing; and
`Projection.ofScheduled` says a labelling always exists, so the only content
is what is asked of it. -/
def MvbaAdmissible (r : ChorusRun thS thM) : Prop :=
  ∃ p : (mvbaComponent thS thM).Projection r,
    Mvba.FJustice p.run ∧ Mvba.AViewSync p.run

/-- **A certified meta-block**, in Chorus's vocabulary: every positive entry
is a proposer's and backed by the certificate the representation names — a
FastQC, or a FallbackQC under `FBCert` (`mval_fb`); every negative entry is
a proposer's, backed by a negative FastQC or, under `FBCert`, by a negative
FallbackQC or an EquivCert; and every proposer has an entry. These are
`mvba_propose`'s three validity guards **verbatim**, the first two clauses
being also the decision handlers' bridge `require`
([Chorus.lean](../Chorus.lean), "The MVBA instance"). -/
def Certified
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice))
    (v : MetaBlock node merkle_root) : Prop :=
  (∀ J M, thS.mval_pos (thM.ent v) J M = true → thS.is_proposer J = true ∧
    ((¬ thS.mval_fb v J = true ∧
        Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J M thS st) ∨
      (thS.mval_fb v J = true ∧
        Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J M thS st ∧
        Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS st))) ∧
  (∀ J, thS.mval_neg (thM.ent v) J = true → thS.is_proposer J = true ∧
    (Chorus.vote_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) J thS st ∨
      ((Chorus.fb_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) J thS st ∨
        Chorus.equiv_evidence (nset := nset) (mvba := Mvba.mvbaSafety thM) J thS st) ∧
        Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS st))) ∧
  (∀ J, thS.is_proposer J = true →
    (∃ M, thS.mval_pos (thM.ent v) J M = true) ∨ thS.mval_neg (thM.ent v) J = true)

/-- **The bridge** — the MVBA's `Valid` is Chorus's certificate check, in
both directions, at every point of the run:

* *soundness*: a certified meta-block is `Valid` — what lets a correct
  validator's `mvba_propose` fire, since the contract's `propose` requires
  `Valid` of its input;
* *completeness*: a meta-block a correct validator decided or accepted is
  certified — what enables the decision handlers, whose bridge `require` is
  that check, and what gives the availability report its chunks: a correct
  validator accepts only a `Valid` meta-block, so the `FallbackQC` entries
  it waits under are genuine, and each has a correct signer that
  re-disseminates.

The header says why this is a premise: `Valid` is a parameter of the class,
fixed before Chorus's state exists, and the certificates are facts about
that state. It is the cryptographic content of the seam — a `Valid`
meta-block's certificates are genuine, and genuine certificates are `Valid`
— which [CompositionContracts.md](../../docs/CompositionContracts.md) §7 item 1 names and no class field
can carry. It is *not* a statement about the protocol's outcome: it relates
the MVBA theory's `valid` to the network, and nothing else. -/
def ValidBridge (r : ChorusRun thS thM) : Prop :=
  (∀ (n : Nat) (v : MetaBlock node merkle_root),
    Certified (thS := thS) (thM := thM) (r.at' n) v → (Mvba.mvbaSafety thM).Valid v) ∧
  (∀ (n : Nat) (i : node) (v : MetaBlock node merkle_root), ¬ nset.is_byz i = true →
    (Mvba.mvbaSafety thM).decided (r.at' n).mvba_st i v → Certified (thS := thS) (thM := thM) (r.at' n) v) ∧
  (∀ (n : Nat) (i : node) (w : view) (v : MetaBlock node merkle_root), ¬ nset.is_byz i = true →
    (r.at' n).mvba_st.accepted i w v = true → Certified (thS := thS) (thM := thM) (r.at' n) v)

/-- **The caller's first premise: every correct validator participates.**
Each correct validator eventually invokes `participate()`. Within Cadence
the glue does so when it opens the slot (Algorithm 1, line 17 (`line:participate`)). This is the
first antecedent of `SlotConsensusTemporal.termination`. -/
def AllParticipate (r : ChorusRun thS thM) : Prop :=
  ∀ i, ¬ nset.is_byz i = true → ∃ n, (r.at' n).participating i = true

/-- **The caller's second premise: no correct validator abandons before
finalizing.** Whenever a correct validator has invoked `abandon()`, it has
already finalized. Within Cadence the glue abandons a slot only once it has
finalized it (Algorithm 1, line 23 (`line:abandon`)). This is the second antecedent of
`SlotConsensusTemporal.termination`, and the C1 antecedent of the timed
fields. Without it the claim is false: a validator that abandons at once
never finalizes, since finalizing is itself a gated rule. -/
def NoAbandonBeforeFinalizing (r : ChorusRun thS thM) : Prop :=
  ∀ i, ¬ nset.is_byz i = true → ∀ n,
    (r.at' n).abandoned i = true → (r.at' n).local_committed i = true

/-! ## The target -/

/-- **Termination**: every correct validator finalizes the slot —
`finalize_commit` fires for it, which is `local_committed`. The single-slot
form of Lemma 11 (`lemma:chorus-termination`), with the `5Δ + ℓ_MVBA` bound erased, and
the untimed sibling of `SlotConsensusTemporal.termination`, whose timed form
this development still has no instance of. -/
def Terminates (r : ChorusRun thS thM) : Prop :=
  ∀ i, ¬ nset.is_byz i = true → ∃ n, (r.at' n).local_committed i = true

/-- **The target, stated.** Written down, with its premises fixed and
type-checked, before the proof existed; the proof is `Chorus.termination`
in [Termination.lean](Termination.lean), at the concrete quorum family and the system's
configuration. The five premises are exactly the file's named definitions:
three about the run's scheduling and the MVBA seam, and two about the
caller, which are `SlotConsensusTemporal.termination`'s own antecedents. What is
deliberately absent is the quorum machinery — the concrete family the
counting theorems are stated over is a hypothesis of the theorem, not part
of the claim — and `Mvba.termination`'s three class hypotheses, for the same
reason. -/
def TerminationClaim
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view))
      (MetaBlock node merkle_root) (node → Option merkle_root) (Mvba.Msg view (MetaBlock node merkle_root) (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (MetaBlock node merkle_root) (node → Option merkle_root) view) : Prop :=
  ∀ r : ChorusRun thS thM, FJustice r → MvbaAdmissible r → ValidBridge r →
    AllParticipate r → NoAbandonBeforeFinalizing r → Terminates r

end Runs

end Chorus

/-! ## The pinned trust base

Definitions, four facts about the label classification, the component
instance, and the two acceptance lemmas (every enabled fair label, and every
enabled MVBA proposal, can change the state); the target itself is a
definition, so nothing here asserts termination. -/

/--
info: 'Chorus.label_classified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.label_classified

/-- info: 'Chorus.not_justice_of_byz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Chorus.not_justice_of_byz

/-- info: 'Chorus.not_justice_of_oracle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Chorus.not_justice_of_oracle

/--
info: 'Chorus.mvbaStepLabel_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.mvbaStepLabel_iff

/--
info: 'Chorus.mvbaComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.mvbaComponent

/--
info: 'Chorus.justice_enabledMove' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.justice_enabledMove

/--
info: 'Chorus.mvba_propose_enabledMove' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.mvba_propose_enabledMove

/--
info: 'Chorus.fJustice_iff_move' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.fJustice_iff_move
