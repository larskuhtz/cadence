import Cadence.Mvba.Certify
import Cadence.Interfaces

/-! # MvbaCompose — `Mvba ⊨ MVBASafety`, and the join toward `MVBA`

The provider step of the MVBA instantiation
([MvbaPlan.md](../../docs/MvbaPlan.md) §5): the `Mvba` transition system
([Mvba.lean](../Mvba.lean)), packaged as the state-level MVBA contract of
[Interfaces.lean](../Interfaces.lean) — the class Chorus consumes as its
`mvba` constraint ([System.lean](../System.lean) plugs this instance in) —
together with the join toward the full `MVBA` class. This is the only file
of the `Mvba` family that imports `Cadence.Interfaces`, on the pattern of
[Chorus/Compose.lean](../Chorus/Compose.lean).

**The instance.** Module 3 (`mod:mvba`) is one instance per Chorus slot, and the model
is one instance, so the contract is instantiated directly: `init`, `step`,
`trans`, `reachable` are the model's own relations, the state is the
model's state, the value is the model's meta-block representation and the
entry vector its `evec`, `Valid` is the theory's immutable `valid` and
`entries` its `ent`, `decided` is the relation of that name read at the
canonical field representation, the quorum family is the module's
`ByzNodeSet` instance, and `byz` is its Byzantine predicate.

Each entry is an `MVBASafety` field and what discharges it.

* **`agreement`, `integrity`, `external_validity`** — `safety [agreement]`,
  `[integrity]`, `[external_validity]`, through the named reachability
  projections of [Mvba/Certify.lean](Certify.lean); `[integrity]` is the
  stronger "decides at most once", and the field over entries follows
* **the certificate-level fields** — a certificate is a commit certificate
  some validator sent (`msg_commitqc s`); `commitqc_agree` (one certified
  entry vector), `decided_backed` and `decided_qc_sent` with it (the
  decided one), `commitqc_valid` (a valid representation), and
  `commitqc_backed` with `honest_commit_accepted` (the availability of the
  correct signers)
* **`decidedCert`, `decided_certified`, `decidedCert_certifies`** — a
  decision's output certificate is its `DecidedQC_i` (`decided_qc`):
  `decided_backed` (a decision has one), `decided_qc_sent` with
  `decided_qc_decided` and `[integrity]` (it certifies the decided entries)
* **`decided_mono`, `init_decided`** — the transition bodies of every
  action, uniformly (`decided_mono_tr`, `init_not_decided` below): `decided`
  is only ever set, and `after_init` clears it
* **`step_trans`, `reachable_init`, `reachable_trans`** — the reachability
  constructors

**The inputs and Quiescence are in the fragment.** The model has the
module's two inputs as actions (`propose`, `abandon`) and a per-party
message row for each message kind it sends — the five signed messages and
the four certificate rows — so the inputs, their
observables (`proposed := input`, `abandoned`, `sent` by cases on
`Mvba.Msg`), effects, frames, initial conditions **and Quiescence** are
proven here — Quiescence is the one-step fact `sent_new_tr`: a correct
party's new message row comes from an honest send, and every honest send
requires `∃ E, input i E` and `¬ abandoned i`. The timed part — the
admissible-run model, `ℓ` and `ℓ_MVBA`-Termination, the fields of
`MVBATemporal` — is proven in [Mvba/Temporal.lean](Temporal.lean)
(`Mvba.mvbaTemporal`, from named hypotheses). `mvba_of_temporal` joins the
two levels, which gives the full `MVBA` (`Mvba.mvbaFull`).
-/

-- No `open Veil` here, as in [Chorus/Compose.lean](../Chorus/Compose.lean):
-- Veil names are used fully qualified, which keeps the file in the generated
-- transition system's instance regime
-- ([Composition.lean](../Composition.lean)'s header).

namespace Mvba

/-- What crosses the wire: the contract's `message` type. The five signed
messages of the protocol, per sender — a `Pre-Prepare` carries the proposed
representation `x`, every vote an entry vector `e` — and the certificates:
the transferable commit certificate `commitqc v e` over entries that
`decide(x, CommitQC)` outputs and the composing layer hands to other
parties (the supplement's "Decision output and handoff"), the prepare
certificate a sender attaches, and the timeout certificates. A certificate
is data: `Sent` reads it at the row of the party that sent it. -/
inductive Msg (view value evec : Type) where
  | preprepare (v : view) (x : value)
  | prepare (v : view) (e : evec)
  | commit (v : view) (e : evec)
  | timeout_qc (v w : view) (e : evec)
  | timeout_noqc (v : view)
  | commitqc (v : view) (e : evec)
  | prepqc (v : view) (e : evec)
  | tc (v : view)
  | tc_lock (v w : view) (e : evec)
  | tc_nolock (v : view)

/-- A consumer that holds the message sort as an opaque parameter needs it
inhabited (Chorus's `[Inhabited mmsg]`); a view suffices for a witness. -/
instance {view value evec : Type} [Inhabited view] : Inhabited (Msg view value evec) :=
  ⟨.timeout_noqc default⟩

open Classical

section Instance

variable {node nodeset value evec view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited evec] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]

/-- The abstract field representation of the Mvba state at the canonical
`Classical` instances (cf. [Composition.lean](../Composition.lean)'s
`afr%`). -/
local macro "afr%" f:ident : term =>
  `(@Mvba.instAbstractFieldRepresentation node nodeset value evec view
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
    (fun a b => Classical.propDecidable (a = b))
    $f)

/-- `i` has decided the representation `e`: the contract's `decide(v)` output. -/
noncomputable abbrev Decided
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) (i : node) (e : value) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.decided) st.decided i e = true

/-- `i` has proposed `e` (`input`): the record of the `propose(v)` input. -/
noncomputable abbrev Proposed
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) (i : node) (e : value) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.input) st.input i e = true

/-- `i` is `AvailReady` for `e` (`avail_ready`). -/
noncomputable abbrev AvailReady
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) (i : node) (e : value) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.avail_ready) st.avail_ready i e = true

/-- `i` has abandoned: the record of the `abandon()` input. -/
noncomputable abbrev Abandoned
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) (i : node) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.abandoned) st.abandoned i = true

/-- `p` has sent `m`: the message's network row with `p` as its sender. -/
noncomputable def Sent
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) (p : node) :
    Msg view value evec → Prop
  | .preprepare v e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_preprepare) st.msg_preprepare p v e = true
  | .prepare v e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_prepare) st.msg_prepare p v e = true
  | .commit v e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_commit) st.msg_commit p v e = true
  | .timeout_qc v w e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_timeout_qc) st.msg_timeout_qc p v w e = true
  | .timeout_noqc v =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_timeout_noqc) st.msg_timeout_noqc p v = true
  | .commitqc v e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_commitqc) st.msg_commitqc p v e = true
  | .prepqc v e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_prepqc) st.msg_prepqc p v e = true
  | .tc v =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_tc) st.msg_tc p v = true
  | .tc_lock v w e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_tc_lock) st.msg_tc_lock p v w e = true
  | .tc_nolock v =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_tc_nolock) st.msg_tc_nolock p v = true

/-- `c` is a valid commitment proof for the entry vector `e`: a commit
certificate on `e`, of some view, that some validator sent
(`msg_commitqc s`: `2f+1` `Commit`s were aggregated). -/
noncomputable def Certifies
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) :
    Msg view value evec → evec → Prop
  | .commitqc w e, e' =>
    e' = e ∧ ∃ s,
      @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.msg_commitqc) st.msg_commitqc s w e = true
  | _, _ => False

/-- The certificate `p`'s decision outputs: `DecidedQC_p` (`decided_qc`). -/
noncomputable def DecidedCert
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) (p : node) :
    Msg view value evec → Prop
  | .commitqc w e =>
    @Veil.FieldRepresentation.get _ _ _ (afr% Mvba.State.Label.decided_qc) st.decided_qc p w e = true
  | _ => False

/-- The labels of the module's four inputs: `propose(v)`, `abandon()`,
the handoff of a transferred commit certificate, which the model's
`decide` handles (Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`): the composing
layer delivers the certificate, the MVBA accepts it), and the availability
report `become_avail_ready` (the composing dissemination layer says that a
party holds its shares, Supplement, Section 1.2 (`subsec:mvba-protocol`),
"Availability-synchronization assumption"). Every other label is an
internal step of the protocol; a party decides on a certificate it formed
itself by the internal `form_own_commitqc`. -/
def Label.isInput : Mvba.Label node nodeset value evec view → Prop
  | .propose _ _ => True
  | .abandon _ => True
  | .decide _ _ _ _ => True
  | .become_avail_ready _ _ => True
  | _ => False

omit [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited evec] [Inhabited view] nset vord in
/-- `Label.isInput` names the four input constructors, in a form that
survives leaving this module.

The definition itself does not: at this many constructors Lean compiles its
`match` to a bit-testing `Label.rec`, whose equation lemmas are available
here but do not let `Label.isInput (.decide …)` reduce in an importing file.
Consumers case on this lemma rather than unfold the definition, as
[Mvba/Liveness.lean](Liveness.lean) does. -/
theorem Label.isInput_cases {l : Mvba.Label node nodeset value evec view}
    (h : Label.isInput l) :
    (∃ i e, l = .propose i e) ∨ (∃ i, l = .abandon i) ∨ (∃ i s v e, l = .decide i s v e) ∨
      (∃ i e, l = .become_avail_ready i e) := by
  cases l <;> simp_all [Label.isInput]

variable (th : Mvba.Theory node nodeset value evec view)

/-! ### Step-level facts, uniformly over every action

Each is proven by exposing every action's pre-computed transition body
(`<action>.ext.derived_eq`, then the `reducible` `<action>.ext.tr` — Veil's
`trSimp` set is exactly those two per action, so one `simp only` covers all
of them),
substituting the post-state and evaluating the field-representation
`get`/`set` pair at the canonical representation
([CompositionContracts.md](../../docs/CompositionContracts.md) §4). -/

/-- Expose one action's transition body in `h`. -/
local macro "mvba_tr" h:ident : tactic =>
  `(tactic| (simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Evaluate the field-representation `get`/`set` pair at the canonical
representation, everywhere. -/
local macro "mvba_field_simp" : tactic =>
  `(tactic| simp +unfoldPartialApp [Decided, Proposed, Abandoned, AvailReady, Sent,
      Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id] at *)

section StepFacts
variable {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)}
  {l : Mvba.Label node nodeset value evec view}

set_option maxHeartbeats 4000000 in
/-- `decided` stands across every action. -/
theorem decided_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (i : node) (e : value) (h : Decided st i e) : Decided st' i e := by
  cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 4000000 in
/-- `input` stands across every action. -/
theorem proposed_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (i : node) (e : value) (h : Proposed st i e) : Proposed st' i e := by
  cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 4000000 in
/-- `abandoned` stands across every action. -/
theorem abandoned_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (i : node) (h : Abandoned st i) : Abandoned st' i := by
  cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 8000000 in
/-- Every message row stands across every action (the network is monotone). -/
theorem sent_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (p : node) (m : Msg view value evec) (h : Sent st p m) : Sent st' p m := by
  cases m <;> cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 4000000 in
/-- Internal steps leave `input` untouched: only `propose` sets it. -/
theorem proposed_frame_internal (hl : ¬ Label.isInput l)
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (i : node) (e : value) : Proposed st' i e ↔ Proposed st i e := by
  cases l <;> simp [Label.isInput] at hl <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp

set_option maxHeartbeats 4000000 in
/-- Internal steps leave `abandoned` untouched: only `abandon` sets it. -/
theorem abandoned_frame_internal (hl : ¬ Label.isInput l)
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (i : node) : Abandoned st' i ↔ Abandoned st i := by
  cases l <;> simp [Label.isInput] at hl <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp

set_option maxHeartbeats 4000000 in
/-- Every label but the availability input leaves `avail_ready` untouched. -/
theorem avail_frame_of_ne (hl : ∀ i e, l ≠ .become_avail_ready i e)
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (i : node) (e : value) : AvailReady st' i e ↔ AvailReady st i e := by
  cases l <;> simp at hl <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp

/-- Internal steps leave `avail_ready` untouched: only its input sets it. -/
theorem avail_frame_internal (hl : ¬ Label.isInput l)
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (i : node) (e : value) : AvailReady st' i e ↔ AvailReady st i e :=
  avail_frame_of_ne th (fun i e h => hl (by subst h; simp [Label.isInput])) htr i e

/-- The availability input records `avail_ready i e`. -/
theorem avail_effect_tr {i : node} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st
      (.become_avail_ready i e) st') : AvailReady st' i e := by
  mvba_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); mvba_field_simp

/-- The availability input marks its own party and representation only. -/
theorem avail_effect_frame_tr {i : node} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st
      (.become_avail_ready i e) st') (q : node) (w : value) (h : AvailReady st' q w) :
    AvailReady st q w ∨ (q = i ∧ w = e) := by
  mvba_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); mvba_field_simp
  rcases h with ⟨rfl, rfl⟩ | h
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl h

set_option maxHeartbeats 8000000 in
/-- A commit certificate stands across every action. -/
theorem certifies_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (c : Msg view value evec) (e : evec) (h : Certifies st c e) : Certifies st' c e := by
  cases c <;> simp only [Certifies] at h ⊢
  obtain ⟨rfl, s, h⟩ := h
  refine ⟨rfl, s, ?_⟩
  cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

set_option maxHeartbeats 8000000 in
/-- A decision's output certificate stands across every action. -/
theorem decidedCert_mono_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (p : node) (c : Msg view value evec) (h : DecidedCert st p c) : DecidedCert st' p c := by
  cases c <;> simp only [DecidedCert] at h ⊢
  cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> first | exact h | (right; exact h)

/-- `propose(e)` at `i` records `input i e`. -/
theorem propose_effect_tr {i : node} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st (.propose i e) st') :
    Proposed st' i e := by
  mvba_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); mvba_field_simp

/-- `propose(e)` carries a valid `e` — the model's own guard, which is the
supplement's precondition on the call ([Mvba.lean](../Mvba.lean)'s
`propose`). -/
theorem propose_valid_tr {i : node} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st
      (.propose i e) st') : th.valid e = true := by
  mvba_tr htr
  obtain ⟨-, -, hv, -⟩ := htr
  exact hv

/-- `abandon()` at `i` records `abandoned i`. -/
theorem abandon_effect_tr {i : node}
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st (.abandon i) st') :
    Abandoned st' i := by
  mvba_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); mvba_field_simp

set_option maxHeartbeats 8000000 in
/-- **Quiescence, one step.** A correct party's *new* message row comes from
one of its honest sends, each of which requires the party to have proposed
(`∃ E, input i E`) and not to have abandoned; a Byzantine signer's row is
its own. So the sender has proposed at the post-state and had not
abandoned at the pre-state. -/
theorem sent_new_tr
    (htr : (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st')
    (p : node) (m : Msg view value evec) (hp : ¬ nset.is_byz p = true)
    (hnew : Sent st' p m) (hold : ¬ Sent st p m) :
    (∃ v, Proposed st' p v) ∧ ¬ Abandoned st p := by
  cases m <;> cases l <;> mvba_tr htr <;> (repeat (obtain ⟨_, htr⟩ := htr)) <;>
    mvba_field_simp <;> simp_all <;> exact ⟨_, by assumption⟩

/-- The handoff input: `p` accepts the transferred certificate `c`, which is
the model's `decide p s w x` for `c = commitqc w e`, checked against the
row of a sender `s` that sent it, and a representation `x` of `e`
(`Recover(e)`); no transition for any other message. -/
def Accept (st : Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) (p : node) :
    Msg view value evec → Mvba.State (Mvba.FieldAbstractType node nodeset value evec view) → Prop
  | .commitqc w e, st' => ∃ s x, th.ent x = e ∧
    (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st (.decide p s w x) st'
  | _, _ => False

/-- Accepting a valid certificate for `e` decides a representation of `e`. -/
theorem accept_effect_tr {p : node} {c : Msg view value evec} {e : evec}
    (htr : Accept th st p c st') (hc : Certifies st c e) : ∃ v, th.ent v = e ∧ Decided st' p v := by
  cases c <;> simp only [Accept] at htr
  obtain ⟨rfl, -⟩ := hc
  obtain ⟨_, x, hx, htr⟩ := htr
  refine ⟨x, hx, ?_⟩
  mvba_tr htr; (repeat (obtain ⟨_, htr⟩ := htr)); mvba_field_simp

/-- **A transferred valid certificate is accepted**: a correct party that
has proposed, is not abandoned and has not decided can take any valid
certificate — `decide`'s guards, which accept a certificate of any view —
with a valid representation of its entries, which exists
(`commitqc_valid`). -/
theorem accept_enabled_tr {p : node} {c : Msg view value evec} {e : evec}
    (hr : (Mvba.relationalTransitionSystem node nodeset value evec view).reachable th st)
    (hp : ¬ nset.is_byz p = true) (hc : Certifies st c e) (hin : ∃ v', Proposed st p v')
    (hab : ¬ Abandoned st p) (hnd : ∀ v', ¬ Decided st p v') :
    ∃ st'', Accept th st p c st'' := by
  cases c <;> simp only [Certifies] at hc
  obtain ⟨-, s, hqc⟩ := hc
  rename_i w e0
  obtain ⟨x, hxv, hxe⟩ := Mvba.reachable_commitqc_valid hr s w e0 hqc
  simp only [Accept, Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct, trSimp]
  refine ⟨_, s, x, hxe, hp, hin, hab, ?_, hxv, hnd, rfl⟩
  simpa [instIsSubReaderOfRefl.readFrom_id, instIsSubStateOfRefl.getFrom_id, hxe] using hqc

/-- Initially nobody has decided. -/
theorem init_not_decided
    (hinit : (Mvba.relationalTransitionSystem node nodeset value evec view).init th st)
    (i : node) (e : value) : ¬ Decided st i e := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init] at hinit
  simp only [Mvba.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); mvba_field_simp

/-- Initially nobody has proposed. -/
theorem init_not_proposed
    (hinit : (Mvba.relationalTransitionSystem node nodeset value evec view).init th st)
    (i : node) (e : value) : ¬ Proposed st i e := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init] at hinit
  simp only [Mvba.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); mvba_field_simp

/-- Initially nobody is `AvailReady`. -/
theorem init_not_avail
    (hinit : (Mvba.relationalTransitionSystem node nodeset value evec view).init th st)
    (i : node) (e : value) : ¬ AvailReady st i e := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init] at hinit
  simp only [Mvba.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); mvba_field_simp

/-- Initially nobody has abandoned. -/
theorem init_not_abandoned
    (hinit : (Mvba.relationalTransitionSystem node nodeset value evec view).init th st)
    (i : node) : ¬ Abandoned st i := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init] at hinit
  simp only [Mvba.initializer.ext.tr] at hinit
  (repeat (obtain ⟨_, hinit⟩ := hinit)); mvba_field_simp

end StepFacts

set_option maxHeartbeats 1000000 in
/-- **`Mvba ⊨ MVBASafety`** — for every Mvba theory `th` (the validity
predicate and the leader schedule), the Mvba transition system is an
instance of the state-level MVBA contract, with `byz` the Byzantine
predicate of the module's `ByzNodeSet` instance. `init` is the model's
initial-state relation together with its theory assumption
(`leader_functional`), `step` its transitions other than the two inputs,
`trans` any transition, `reachable` its reachable set; `Valid` is the
theory's `valid`, `decided` the relation of that name. -/
@[implicit_reducible]
noncomputable def mvbaSafety :
    MVBASafety node value evec (Msg view value evec) (Mvba.State (Mvba.FieldAbstractType node nodeset value evec view))
      nodeset nset (fun i => nset.is_byz i = true) where
  Valid e := th.valid e = true
  entries := th.ent
  init st := (Mvba.relationalTransitionSystem node nodeset value evec view).assumptions th ∧
    (Mvba.relationalTransitionSystem node nodeset value evec view).init th st
  step st st' := ∃ l, ¬ Label.isInput l ∧
    (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st l st'
  trans st st' := (Mvba.relationalTransitionSystem node nodeset value evec view).next th st st'
  reachable st := (Mvba.relationalTransitionSystem node nodeset value evec view).reachable th st
  step_trans _ _ h := ⟨h.choose, h.choose_spec.2⟩
  reachable_init st h := Veil.RelationalTransitionSystem.reachable.init st h.1 h.2
  reachable_trans st st' hr hn := Veil.RelationalTransitionSystem.reachable.step st st' hr hn
  -- The two inputs are the model's own actions, so the interface, its
  -- observables, their frames and one-step Quiescence are all first-order
  -- facts this model proves — which is why they sit in the fragment rather
  -- than at the temporal level ([Interfaces.lean](../Interfaces.lean), the
  -- placement rule).
  propose st p v st' := (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st (.propose p v) st'
  abandon st p st' := (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st (.abandon p) st'
  propose_trans _ _ _ _ h := ⟨_, h⟩
  abandon_trans _ _ _ h := ⟨_, h⟩
  decided := Decided
  proposed := Proposed
  abandoned := Abandoned
  sent := Sent
  decided_mono _ _ i e hn h := decided_mono_tr th hn.choose_spec i e h
  proposed_mono _ _ p v hn h := proposed_mono_tr th hn.choose_spec p v h
  abandoned_mono _ _ p hn h := abandoned_mono_tr th hn.choose_spec p h
  sent_mono _ _ p m hn h := sent_mono_tr th hn.choose_spec p m h
  propose_effect _ _ _ _ h := propose_effect_tr th h
  abandon_effect _ _ _ h := abandon_effect_tr th h
  proposed_step_frame _ _ p v h _ := proposed_frame_internal th h.choose_spec.1 h.choose_spec.2 p v
  abandoned_step_frame _ _ p h _ := abandoned_frame_internal th h.choose_spec.1 h.choose_spec.2 p
  init_decided _ i e h := init_not_decided th h.2 i e
  init_proposed _ p v h := init_not_proposed th h.2 p v
  init_abandoned _ p h := init_not_abandoned th h.2 p
  agreement _ hr i j e e' hi hj hdi hdj := reachable_agreement hr i j e e' hi hj hdi hdj
  integrity _ hr i e e' hi hdi hdi' := congrArg th.ent (reachable_integrity hr i e e' hi hdi hdi')
  external_validity _ hr i e hi hd := reachable_external_validity hr i e hi hd
  -- **Quiescence**, in the one-step form the contract states: a new
  -- message row of a correct party at a transition comes with the input and
  -- with the party not having abandoned. `sent_new_tr` is exactly that, over
  -- all 9 message kinds × every action.
  quiescence _ _ p m hn hp hnew hold := sent_new_tr th hn.choose_spec p m hp hnew hold
  -- **The decision handoff.** A certificate is a commit certificate some
  -- validator sent; a decision outputs its `DecidedQC_i`
  -- (`decided_backed`, an invariant of the model); and the handoff is
  -- `decide`, which accepts a certificate of any view.
  availReady := AvailReady
  markAvail st p v st' := (Mvba.relationalTransitionSystem node nodeset value evec view).tr th st
    (.become_avail_ready p v) st'
  markAvail_trans _ _ _ _ h := ⟨_, h⟩
  markAvail_effect _ _ _ _ h := avail_effect_tr th h
  availReady_markAvail_frame _ _ _ _ q w h hq := avail_effect_frame_tr th h q w hq
  init_availReady _ p v h := init_not_avail th h.2 p v
  availReady_step_frame _ _ p v h := avail_frame_internal th h.choose_spec.1 h.choose_spec.2 p v
  availReady_propose_frame _ _ _ _ p v h := avail_frame_of_ne th (by intros; simp) h p v
  availReady_abandon_frame _ _ _ p v h := avail_frame_of_ne th (by intros; simp) h p v
  availReady_accept_frame _ _ c _ p v h := by
    cases c <;> simp only [Accept] at h
    obtain ⟨_, _, -, h⟩ := h
    exact avail_frame_of_ne th (by intros; simp) h p v
  certifies := Certifies
  certified_mono _ _ c e hn h := certifies_mono_tr th hn.choose_spec c e h
  decidedCert := DecidedCert
  decided_certified _ hr i e hi hd := by
    obtain ⟨V, hV⟩ := Mvba.reachable_decided_backed hr i e hi hd
    exact ⟨.commitqc V (th.ent e), hV⟩
  decidedCert_certifies _ hr p c hp hc := by
    cases c <;> simp only [DecidedCert] at hc
    rename_i V E
    obtain ⟨X, hX, hXE⟩ := Mvba.reachable_decided_qc_decided hr p V E hp hc
    exact ⟨X, hX, hXE, p, Mvba.reachable_decided_qc_sent hr p V E hp hc⟩
  accept := Accept th
  accept_trans _ _ c _ h := by
    cases c <;> simp only [Accept] at h
    obtain ⟨_, _, -, h⟩ := h
    exact ⟨_, h⟩
  accept_effect _ _ _ _ _ h hc := accept_effect_tr th h hc
  accept_enabled _ _ _ _ hr hp hc hin hab hnd := accept_enabled_tr th hr hp hc hin hab hnd
  -- **What a certificate guarantees.** A certificate is a commit certificate
  -- on the wire; the model's certificate-level invariants say the rest.
  certified_unique _ hr c c' e e' hc hc' := by
    cases c <;> simp only [Certifies] at hc
    cases c' <;> simp only [Certifies] at hc'
    obtain ⟨rfl, s, h⟩ := hc
    obtain ⟨rfl, s', h'⟩ := hc'
    exact Mvba.reachable_commitqc_agree hr _ _ _ _ _ _ h h'
  certified_decided _ hr c e p v hc hp hd := by
    cases c <;> simp only [Certifies] at hc
    obtain ⟨rfl, s, h⟩ := hc
    obtain ⟨V, hV⟩ := Mvba.reachable_decided_backed hr p v hp hd
    exact Mvba.reachable_commitqc_agree hr _ _ _ _ _ _
      (Mvba.reachable_decided_qc_sent hr p V _ hp hV) h
  certified_valid _ hr c e hc := by
    cases c <;> simp only [Certifies] at hc
    obtain ⟨rfl, s, h⟩ := hc
    obtain ⟨x, hxv, hxe⟩ := Mvba.reachable_commitqc_valid hr _ _ _ h
    exact ⟨x, hxe, hxv⟩
  certified_available _ hr c e hc := by
    cases c <;> simp only [Certifies] at hc
    obtain ⟨rfl, s, h⟩ := hc
    obtain ⟨q, hq, hmem⟩ := Mvba.reachable_commitqc_backed hr _ _ _ h
    refine ⟨q, hq, fun p hp hpc => ?_⟩
    obtain ⟨-, x, hxe, hacc, hav⟩ := Mvba.reachable_honest_commit_accepted hr p _ _ hpc (hmem p hp)
    exact ⟨x, hxe, Mvba.reachable_accepted_valid hr p _ x hpc hacc, hav⟩

/-! ### The join toward the full `MVBA`

With the inputs, their observables, the frames and one-step Quiescence all
proven above, what the full `MVBA` adds to the fragment is an instance of
**`MVBATemporal … (S := mvbaSafety th)`**: the admissible-run model, `ℓ`
and `ℓ_MVBA`-Termination (Supplement, Theorem 2 (`thm:termination`), `O(fΔ)`).
That instance is `Mvba.mvbaTemporal` ([Mvba/Temporal.lean](Temporal.lean)),
and this join makes it the full `MVBA` of the fragment Chorus consumes. -/

/-- Given a temporal level **at this fragment**, `Mvba` is a full `MVBA`.
Nothing is restated to join them, and the fragment comes back out by
`rfl`. -/
@[implicit_reducible]
noncomputable def mvba_of_temporal {time : Type} [TotalOrder time] [Add time]
    (h : MVBATemporal node value evec (Msg view value evec) (Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) nodeset time
      nset (fun i => nset.is_byz i = true) (S := mvbaSafety th)) :
    MVBA node value evec (Msg view value evec) (Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) nodeset time
      nset (fun i => nset.is_byz i = true) :=
  { mvbaSafety th, h with }

/-- The fragment the composition consumes is exactly the one that was
proven. -/
theorem mvba_of_temporal_toSafety {time : Type} [TotalOrder time] [Add time]
    (h : MVBATemporal node value evec (Msg view value evec) (Mvba.State (Mvba.FieldAbstractType node nodeset value evec view)) nodeset time
      nset (fun i => nset.is_byz i = true) (S := mvbaSafety th)) :
    (mvba_of_temporal th h).toMVBASafety = mvbaSafety th := rfl

end Instance
end Mvba

/-! ## The pinned trust base

The instance rests on the standard Lean trio and nothing else — no
`sorryAx`, no trusted-SMT step. The composition consumes the proof-file
family ([Mvba/Proofs](Proofs), via [Mvba/Certify.lean](Certify.lean)'s
`#gen_composition`): every VC statement re-created from the persistent
registry, solved as a fresh kernel-checked reconstruction, assembled per
action into a preservation lemma, and composed. The join is pinned too: the
temporal level enters it as a *hypothesis* — an `MVBATemporal` instance —
never as an axiom. -/

/--
info: 'Mvba.mvbaSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvbaSafety

/--
info: 'Mvba.mvba_of_temporal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.mvba_of_temporal
