import Cadence.Chorus
import Cadence.Mvba.Liveness

/-! # Chorus/Liveness — the run-level target for Chorus, and the premises it rests on

[`docs/Liveness.md`](../../docs/Liveness.md) §4, stage 2. This file states
the run-level termination claim for Chorus at the system's instantiation —
the MVBA constraint filled by the `Mvba` model, as in
[`System.lean`](../System.lean) — **and every premise it takes**, as named
`Prop`s, before any of the proof exists. Its sibling is
[`Mvba/Liveness.lean`](../Mvba/Liveness.lean): same discipline, same shape,
and its `Mvba.termination` is what the MVBA arm of the argument will
consume.

`grep -n '^def [A-Z]' Cadence/Chorus/Liveness.lean` prints the whole list:
the four label classes, the certificate predicate the bridge premise is
stated with, the three premises, the target and the claim, and nothing else.
Everything a human has to believe about scheduling or about the seam
between Chorus and its MVBA is one of those definitions, with a docstring,
and appears as an explicit hypothesis of `TerminationClaim`.

## What this replaces

Chorus's liveness claim has rested on three meta-axioms stated in prose —
(F-justice), (F-byz), (A-mvba) — and the state-level theorems
(`Chorus/Progress.lean`, `Chorus/Counting.lean`, `Chorus/Pigeonhole.lean`).
Here (F-justice) and (F-byz) become the label classification below and one
named premise, exactly as in the MVBA file; and (A-mvba) — "the MVBA
terminates" — is **retired** in favour of what it stood for: the MVBA's own
liveness theorem, applied to the composed run's MVBA projection
(`Cadence/Fairness.lean`, "Components"), under the MVBA's own scheduling
premises. What is assumed about the MVBA is then not that it terminates
but that its steps inside the composed run were scheduled the way
`Mvba.termination` requires (`MvbaAdmissible` below) — the untimed analogue
of `MVBATemporal.Admissible`.

## The three premises, and why each is one

* **(F-justice)** — `FJustice`: every honest, non-oracle label is weakly
  fair. The classification is the three `match` definitions below; the
  reasons weak fairness suffices are `docs/Liveness.md` §2.
* **The MVBA's scheduling** — `MvbaAdmissible`: the run *has* a projection
  onto the MVBA (a labelling of its steps plus infinitely many of them —
  `Component.Projection`, whose header says why both are data) whose
  projected run satisfies `Mvba.FJustice`, `Mvba.AViewSync` and
  `Mvba.FAvail`. Those are three of `Mvba.termination`'s five premises,
  stated with that file's own definitions and restated nowhere. The other
  two — every correct validator proposes, none is abandoned before deciding
  — are the *caller's* premises and the caller is Chorus, so they are
  **derived** here (stage 4), not assumed: the first from (F-justice) on
  `mvba_propose` and the progress dichotomy, the second because this
  single-slot model never drives `abandon`.
* **The bridge** — `ValidBridge`: the MVBA's `Valid` agrees with Chorus's
  certificate check. Chorus consumes the MVBA through the class
  `MVBASafety`, whose `Valid` is a predicate on values alone, while the
  paper's `Valid B` inspects the certificates a meta-block *carries* — in
  the model, facts about Chorus's network relations. The two are tied by
  the **one stated bridge** of `docs/CompositionContracts.md` §3, and a
  liveness proof needs it in both directions: *soundness* — a vector every
  one of whose proposer entries is certificate-backed on the network is
  `Valid`, which is what lets `mvba_propose` fire at all, since the
  contract's `propose` requires `Valid` of its input (`propose_valid`,
  `Mvba.propose`'s guard); and *completeness* — a vector a correct
  validator decided has every proposer entry certificate-backed, which is
  what enables the decision handlers, whose bridge `require` is that
  check. The safety proofs need neither direction (the guard only removes
  behaviours, and `external_validity` is proven from `Mvba`'s own check).
  This is the run-level form of the seam `CompositionContracts.md` §7
  item 1 names, and it is a statement about the MVBA theory's `valid`
  meeting Chorus's network — the cryptographic content that a certificate
  cannot be forged — not about either model alone.

## What is deliberately absent

No timing premise: Chorus's phase markers are weakly fair like every other
honest action, and `docs/Liveness.md` §2.1 says why that is sound here and
not in the MVBA. No `all_honest_recorded`-shaped premise: it buys proposal
inclusion, not termination. No quorum machinery: the concrete quorum family
(`byzNodeSetFin`, every `n = 3f+1`) that the counting theorems are stated
over is a hypothesis of the *theorem* to come, not part of the claim.

## The classification, against the model's prose

`Chorus.lean`'s liveness section lists (F-justice)'s actions by name. The
definition here is the complement of the other two classes, which is the
checkable form (adding an action and forgetting it here lands it in
`JusticeLabel`, visibly), and it agrees with that list except that it also
covers `deliver_chunk_assigned` and `broadcast_commitqc_*`, which the prose
does not name but the chain in `docs/ChorusDesign.md` §7 uses as fair
("certificates become broadcast certificates"). Both are honest network
capabilities — eventual delivery of a correct proposer's chunk, assembly of
a certificate whose signatures are all present — and weak fairness on them
is the eventual-delivery assumption the paper makes. The prose should be
aligned when `Chorus.lean` is next edited for another reason (an edit to a
model file, even a comment, re-solves its 4 222-cell family). -/

namespace Chorus

open Cadence

/-! ## The label classes

Each `match` lists its actions by name, so the classification is checkable
by reading rather than by trusting a sentence. This section carries no
instances: a label is a syntactic object. -/

section Labels

variable {slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice : Type}

/-- **(F-byz).** The labels the adversary controls — the `byz_*` family. No
premise requires anything of them, which *is* the assumption: progress never
relies on adversarial help. `not_justice_of_byz` pins the disjointness. -/
def ByzLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice → Prop
  | .byz_sign_proposer .. => True
  | .byz_deliver_chunk .. => True
  | .byz_sign_vote_pos .. => True
  | .byz_sign_vote_neg .. => True
  | .byz_cast_vote .. => True
  | .byz_sign_fb_pos .. => True
  | .byz_sign_fb_neg .. => True
  | .byz_sign_fallback .. => True
  | .byz_sign_commit_pos .. => True
  | .byz_sign_commit_neg .. => True
  | .byz_cast_commit .. => True
  | .byz_sign_fbcommit .. => True
  | .byz_release_msg_decrypt_share .. => True
  | _ => False

/-- **The oracle step** `mvba_step`: the MVBA's internal move, taken by the
composed system on the MVBA's behalf. It is outside (F-justice) — its
scheduling is the MVBA's own, and `MvbaAdmissible` is what says how it was
scheduled. `mvba_propose` is *not* here: it is Chorus's own honest action
(a correct validator proposing to the MVBA), weakly fair like the rest, even
though it also advances the MVBA's state — see `MvbaStepLabel`. -/
def OracleLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice → Prop
  | .mvba_step _ => True
  | _ => False

/-- The labels (F-justice) covers: every honest action of the module —
phase advancement, dissemination and delivery, voting, aggregation, the two
paths, the MVBA proposal and the decision handlers, the commit round and
finalization — which is everything that is neither the adversary's nor the
oracle step. -/
def JusticeLabel (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) : Prop :=
  ¬ ByzLabel l ∧ ¬ OracleLabel l

/-- **The labels at which the MVBA's state moves**: the oracle step and the
driven input. This is the component's `isSub` (`mvbaComponent` below), a
different cut from the fairness classes — `mvba_propose` is a justice label
*and* an MVBA step, and it appears in the projected run as the MVBA's own
`propose` label, which `Mvba.FJustice` excludes precisely because the
caller schedules it. -/
def MvbaStepLabel : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice → Prop
  | .mvba_step _ => True
  | .mvba_propose .. => True
  | _ => False

/-- **(F-byz), machine-checked at the only level it can be**: no label the
adversary controls is subject to a fairness hypothesis. -/
theorem not_justice_of_byz (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)
    (h : ByzLabel l) : ¬ JusticeLabel l := fun hj => hj.1 h

/-- The oracle step is not under (F-justice) either. -/
theorem not_justice_of_oracle (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)
    (h : OracleLabel l) : ¬ JusticeLabel l := fun hj => hj.2 h

/-- The classification is exhaustive — by construction, since `JusticeLabel`
is the complement of the other two; so this is a classical case split, and
what checks the action list is the two `match` definitions above. -/
theorem label_classified (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) :
    JusticeLabel l ∨ ByzLabel l ∨ OracleLabel l := by
  classical
  by_cases hb : ByzLabel l
  · exact Or.inr (Or.inl hb)
  by_cases ho : OracleLabel l
  · exact Or.inr (Or.inr ho)
  exact Or.inl ⟨hb, ho⟩

/-- The oracle step moves the MVBA's state. -/
theorem mvbaStepLabel_of_oracle (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice)
    (h : OracleLabel l) : MvbaStepLabel l := by
  cases l <;> trivial

/-- An MVBA step is the oracle step or the driven input, and nothing else. -/
theorem mvbaStepLabel_iff (l : Chorus.Label slot node nodeset merkle_root mstate mvalue mmsg Phase PathChoice) :
    MvbaStepLabel l ↔ (∃ m, l = .mvba_step m) ∨ (∃ i v m, l = .mvba_propose i v m) := by
  cases l <;> simp [MvbaStepLabel]

end Labels

/-! ## The MVBA is a component of Chorus

The instance of `Cadence.Component` for Chorus at the system's
instantiation, from which the projection of a Chorus run onto the MVBA and
the fairness transfer follow (`Cadence/Fairness.lean`). Its five fields come
from the generated artefacts and one hand proof — nothing here needs a new
cell:

* `frame` — M13's per-action `Chorus.<action>.frame_mvba_st`, one per
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
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]

/-- **Chorus at the `Mvba` instance**: the module's transition system with its
MVBA constraint filled by `Mvba.mvbaSafety thM`, the abstract sorts at the
`Mvba` model's own types — the value is the entry vector, the state the
model's, the message type the model's (`System.lean`, "Chorus at the `Mvba`
instance"). Every run-level statement in this file is about this system. -/
noncomputable abbrev atMvba (thM : Mvba.Theory node nodeset (node → Option merkle_root) view) :=
  Chorus.relationalTransitionSystem slot node nodeset merkle_root
    (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
    (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice
    (mvba := Mvba.mvbaSafety thM)

/-- The `Mvba` model's own transition system, the component's `sub`. -/
noncomputable abbrev mvbaRTS :=
  Mvba.relationalTransitionSystem node nodeset (node → Option merkle_root) view

variable {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (node → Option merkle_root) view}
  {s s' : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)}

/-- Expose an action's transition body (`Cadence/Composition.lean`'s
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
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (htr : (atMvba thM).tr thS s l s') (hl : ¬ MvbaStepLabel l) : s'.mvba_st = s.mvba_st := by
  letI : MVBASafety node (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root))
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (fun i => nset.is_byz i = true) := Mvba.mvbaSafety thM
  cases l
  case mvba_step => exact absurd trivial hl
  case mvba_propose => exact absurd trivial hl
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
  case mvba_terminate => exact Chorus.mvba_terminate.frame_mvba_st htr
  case redisseminate_chunk => exact Chorus.redisseminate_chunk.frame_mvba_st htr
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
  obtain ⟨hprop, htr⟩ := htr
  chorus_field_simp
  subst htr
  exact hprop

set_option maxHeartbeats 1000000 in
/-- The initial value of `mvba_st`, read off the initializer's transition. -/
theorem mvba_st_init (hi : (atMvba thM).init thS s) : s.mvba_st = thS.mvba_init_state := by
  simp only [Chorus.relationalTransitionSystem, Chorus.Init, Chorus.initializer.ext.tr] at hi
  subst_vars
  chorus_field_simp

/-- **The MVBA is a component of Chorus**, at the system's instantiation. -/
noncomputable def mvbaComponent
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view) :
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
    | _ => exact absurd hl id

end Component

/-! ## The premises, one named `Prop` each

From here on the full instance set is in scope: the premises talk about
states of the composed system. -/

section Runs

open Classical

variable {slot node nodeset merkle_root view Phase PathChoice : Type}
  [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
  [Inhabited Phase] [Inhabited PathChoice]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
  {thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice}
  {thM : Mvba.Theory node nodeset (node → Option merkle_root) view}

/-- A labelled run of Chorus at the `Mvba` instance: the object every premise
below is about. -/
abbrev ChorusRun
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view) :=
  LRun (atMvba (slot := slot) (Phase := Phase) (PathChoice := PathChoice) thM) thS

/-- **(F-justice)** — weak fairness of every honest, non-oracle action. -/
def FJustice (r : ChorusRun thS thM) : Prop :=
  ∀ l, JusticeLabel l → WeaklyFair r l

/-- **The MVBA's scheduling premise**, replacing (A-mvba): the run has a
projection onto the MVBA — a labelling of its steps that explains them, and
infinitely many of them (`Component.Projection`) — whose projected run
satisfies the three scheduling premises of `Mvba.termination`: weak
fairness of the MVBA's honest actions, the timer discipline of the good
view, and availability. Stated with `Mvba/Liveness.lean`'s own definitions;
the caller's two premises of that theorem are derived, not assumed (header).

The existential over the projection is the honest form: the composed run
records only the MVBA's post-states, so an assumption about how the MVBA's
*labels* were scheduled has to supply the labels. `Component.Projection.
weaklyFair_iff` says the fairness clause means the same thing read at the
composed run, so nothing is smuggled in by the re-indexing; and
`Projection.ofScheduled` says a labelling always exists, so the only content
is what is asked of it. -/
def MvbaAdmissible (r : ChorusRun thS thM) : Prop :=
  ∃ p : (mvbaComponent thS thM).Projection r,
    Mvba.FJustice p.run ∧ Mvba.AViewSync p.run ∧ Mvba.FAvail p.run

/-- **A certified meta-block**, in Chorus's vocabulary: every positive entry
is a proposer's, backed by a FastQC or by a FallbackQC under `FBCert`; every
negative entry is a proposer's, backed by a negative FastQC or, under
`FBCert`, by a negative FallbackQC or an EquivCert; and every proposer has an
entry. These are `mvba_propose`'s three validity guards **verbatim**, the
first two clauses being also the decision handlers' bridge `require`
(`Chorus.lean`, "The MVBA instance"). -/
def Certified
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice))
    (v : node → Option merkle_root) : Prop :=
  (∀ J M, thS.mval_pos v J M = true → thS.is_proposer J = true ∧
    (Chorus.vote_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J M thS st ∨
      (Chorus.fb_quorum_pos (nset := nset) (mvba := Mvba.mvbaSafety thM) J M thS st ∧
        Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS st))) ∧
  (∀ J, thS.mval_neg v J = true → thS.is_proposer J = true ∧
    (Chorus.vote_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) J thS st ∨
      ((Chorus.fb_quorum_neg (nset := nset) (mvba := Mvba.mvbaSafety thM) J thS st ∨
        Chorus.equiv_evidence (nset := nset) (mvba := Mvba.mvbaSafety thM) J thS st) ∧
        Chorus.fbcert (nset := nset) (mvba := Mvba.mvbaSafety thM) thS st))) ∧
  (∀ J, thS.is_proposer J = true → (∃ M, thS.mval_pos v J M = true) ∨ thS.mval_neg v J = true)

/-- **The bridge** — the MVBA's `Valid` is Chorus's certificate check, in
both directions, at every point of the run:

* *soundness*: a certified meta-block is `Valid` — what lets a correct
  validator's `mvba_propose` fire, since the contract's `propose` requires
  `Valid` of its input;
* *completeness*: a meta-block a correct validator decided is certified —
  what enables the decision handlers, whose bridge `require` is that check.

The header says why this is a premise: `Valid` is a parameter of the class,
fixed before Chorus's state exists, and the certificates are facts about
that state. It is the cryptographic content of the seam — a `Valid`
meta-block's certificates are genuine, and genuine certificates are `Valid`
— which `docs/CompositionContracts.md` §7 item 1 names and no class field
can carry. It is *not* a statement about the protocol's outcome: it relates
the MVBA theory's `valid` to the network, and nothing else. -/
def ValidBridge (r : ChorusRun thS thM) : Prop :=
  (∀ (n : Nat) (v : node → Option merkle_root),
    Certified (thS := thS) (thM := thM) (r.at' n) v → (Mvba.mvbaSafety thM).Valid v) ∧
  (∀ (n : Nat) (i : node) (v : node → Option merkle_root), ¬ nset.is_byz i = true →
    (Mvba.mvbaSafety thM).decided (r.at' n).mvba_st i v → Certified (thS := thS) (thM := thM) (r.at' n) v)

/-! ## The target -/

/-- **Termination**: every correct validator finalizes the slot —
`finalize_commit` fires for it, which is `local_committed`. The single-slot
form of `lemma:chorus-termination`, with the `5Δ + ℓ_MVBA` bound erased, and
the untimed sibling of `SlotConsensusTemporal.termination`, whose timed form
this development still has no instance of. -/
def Terminates (r : ChorusRun thS thM) : Prop :=
  ∀ i, ¬ nset.is_byz i = true → ∃ n, (r.at' n).local_committed i = true

/-- **The target, stated.** Not a theorem and not asserted anywhere: this is
the `Prop` stages 3–5 of `docs/Liveness.md` §4 have to prove, written down
so that its premises are fixed, type-checked and citable before the proof
exists. The three premises are exactly the file's named definitions. What is
deliberately absent is the quorum machinery — the concrete family the
counting theorems are stated over is a hypothesis of the theorem, not part
of the claim — and `Mvba.termination`'s three class hypotheses, for the same
reason. -/
def TerminationClaim
    (thS : Chorus.Theory slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice)
    (thM : Mvba.Theory node nodeset (node → Option merkle_root) view) : Prop :=
  ∀ r : ChorusRun thS thM, FJustice r → MvbaAdmissible r → ValidBridge r → Terminates r

end Runs

end Chorus

/-! ## The pinned trust base

Definitions, four facts about the label classification, and the component
instance; the target itself is a definition, so nothing here asserts
termination. -/

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
