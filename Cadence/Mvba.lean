import Veil
import Cadence.Tooling

/-! # Mvba — the leader-based MVBA instantiation

*This is a **model file** of the verified-module file family
([Architecture.md](../docs/Architecture.md) §6): it elaborates the
transition system and persists the VC registry, but runs **no invariant
sweep** — the proofs live in the per-action files under
[Mvba/Proofs](Mvba/Proofs), composed into the reachability certificate by
[Mvba/Certify.lean](Mvba/Certify.lean).*

## What this models, and where its specification lives

Module 3 (`mod:mvba`) in the main body is an interface and
five properties with no algorithm. The algorithm modelled here is the
leader-based protocol of the paper repository's **internal supplement** —
Supplement, Section 1 (`sec:mvba-instantiation`), with the data types
in Supplement, Section 1.1 (`subsec:mvba-datatypes`), the protocol in Supplement, Section 1.2 (`subsec:mvba-protocol`)
(Supplement, Algorithm 1 (`alg:mvba`–`alg:mvba-cont3`), in four blocks) and its correctness argument in
Supplement, Section 1.3 (`subsec:mvba-correctness`).

Paper target: [docs/PaperAlignment.md](../docs/PaperAlignment.md) §0.

What an auditor can
check without the supplement is the contract the model is proven against —
`safety [agreement]`, `[integrity]`, `[external_validity]` are the three
safety properties of Module 3 (`mod:mvba`); what needs the supplement is the model's
fidelity to the algorithm.

## The value type

The MVBA agrees on a **meta-block**, which carries for each proposer an
entry and the certificate that makes it valid, and it "votes and decides
over `entries(B)`" (Supplement, Section 1.1 (`subsec:mvba-datatypes`)).
The model has two opaque sorts for the two: `value`, a meta-block
representation, and `evec`, an entry vector, joined by the immutable
function `ent` (`entries(x)`). The system instantiates them at
`MetaBlock node merkle_root` and `node → Option merkle_root`
([Interfaces.lean](Interfaces.lean); [PaperAlignment.md](../docs/PaperAlignment.md) §8.1).
`valid` is an **uninterpreted immutable relation** on representations —
the algorithm only checks certificates, it does not interpret them, so the
external validity predicate is a parameter.

The split follows Supplement, Algorithm 1 (`alg:mvba`–`alg:mvba-cont3`)
exactly. What carries a meta-block carries the representation: the input,
the `Pre-Prepare` (which carries `x` and signs `H(entries(x))`), the
accepted proposal `x_v`, the decision, `AvailReady_i(x)` and `valid`. Every
vote and every certificate — `Prepare`, `Commit`, `Timeout`, the prepare,
commit and timeout certificates, and the lock — carries the entry vector.

**`Recover` is a choice among valid representations.** `Recover(e)`
returns "a valid meta-block with entry vector `e`", from the validator's own
store or from any peer that holds one (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Crash-recovery contract"). So a re-proposal of a
lock (`leader_repropose`, Supplement, Lemma 10 (`lem:reproposal`)) offers
any valid `x` whose entries are the lock, and a decision (`form_own_commitqc`
and `decide`, the procedure `Decide` in Supplement, Algorithm 1
(`alg:mvba-cont3`), reached from Supplement, Algorithm 1, line 31
(`line:mvba:qc-decide`)) decides any valid `x` whose entries the
certificate certifies. The supplement's `Decide` takes `x_v` when its
entries match, which is one of those choices, so the model has every run of
the supplement. Two correct validators may therefore decide different
representations of one entry vector: Agreement is over `ent`, and Integrity
is still at most one decision per validator.

## Views

One MVBA instance serves one Chorus slot and runs as many **views** as it
needs: `Leader(slot, v)` rotates, a view that does not decide is closed by
a timeout certificate `TC_{s,v}`, and the next leader re-proposes the lock
that certificate carries (Supplement, Algorithm 1 (`alg:mvba`) local state, Supplement, Algorithm 1, line 85 (`line:mvba:ht-advance`),
Supplement, Algorithm 1, line 91 (`line:mvba:sv`)). `view` is a `TotalOrderWithMinimum` as the Conductor's
slots and windows are: `vord.zero` is view 1, `vord.next v v'` is
`v' = v + 1`, and no arithmetic reaches the solver. The leader function is
the immutable relation `leader v l`, functional by assumption.

The model has no clock. Timing enters only in the timed liveness claim
([Mvba/Schedule.lean](Mvba/Schedule.lean)), over runs that carry one: the
view timeout is there a function of the view, and the supplement's fixed
`T := Δ_R + 4Δ + max{Δ, Δ_sync}` (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Views, leaders,
and timing parameters") is its constant case. The timed claim's view
arithmetic mirrors the supplement's termination argument: the first view
after `max(t, GST)` is paid for by retransmission, and the good view is
chosen at least two views above the highest view entered then, where the
one-view retention holds (Supplement, Lemma 15 (`lem:convergence`), Supplement, Lemma 16 (`lem:good-view`)).

## State

**Network relations** (`msg_*`, monotone, the sender first, read in
**positive position** by every correct validator's action other than its
own sends — the rules of [Locality.md](../docs/Locality.md)):

Each entry is a relation of this model and the supplement message it stands
for.

* **`msg_preprepare l v x`** — `⟨Pre-Prepare, s, v, x, J, σ_l⟩`; the
  justification `J` is not carried — the receiver checks the network for a
  `TC_{s,v-1}` and its lock (`msg_tc_lock` / `msg_tc_nolock` below)
* **`msg_prepare r v e`, `msg_commit r v e`** — `⟨Prepare, s, v, e, σ⟩`,
  `⟨Commit, s, v, e, σ⟩`
* **`msg_timeout_qc r v w e`, `msg_timeout_noqc r v`** — `⟨Timeout, s, v,
  PrepQC_i, σ⟩` carrying a prepare certificate of view `w` on `e`, or `⊥`
* **`msg_prepqc s v e`** — `prepareQC_{s,v}` on `e` as its former `s`
  attaches it to its messages; read only to check a carried certificate
* **`msg_commitqc s v e`** — the `CommitQC` of view `v` on `e` that `s`
  outputs with its decision (`decide(x, CommitQC)`), or that a Byzantine `s`
  aggregated
* **`msg_tc s v`, `msg_tc_lock s v w e`, `msg_tc_nolock s v`** — `s` has
  sent a `TC_{s,v}`; one whose `highPrepQC` is the certificate `(w, e)`;
  one whose `highPrepQC` is `⊥` (Supplement, Algorithm 1, line 4
  (`line:mvba:derived`)). A correct `s` formed it or forwards it.

**Certificates are formed in local state and sent under the former's
name** ([Locality.md](../docs/Locality.md) §6), each by an explicit step
whose guards are the signature quorums — Chorus's `broadcast_commitqc_*`
pattern, which keeps `∃`-quorum ghosts out of every consumer's guard. A
correct validator forms one by the supplement's rule, in its current view,
with the quorum as a label parameter and a local record whose absence is
the rule's "not already" condition: `adopt_prepqc` (`TryFormPrepQC`),
`form_own_commitqc` (`TryFormCommitQC` with `Decide`, guarded on
`DecidedQC_i = ⊥`) and `form_own_tc_lock` / `form_own_tc_nolock`
(`HandleTimeout`, "upon first collecting `2f+1` valid timeout messages").
It forwards a timeout certificate it advanced on (`sync_view_*`;
Supplement, Algorithm 1, line 98 (`line:mvba:sv-forward`)), and outputs
the commit certificate a transferred decision used (`decide`). The
adversary aggregates any certificate the signatures allow under its own
name (`byz_form_*`), so safety's adversary loses nothing. A view can have
several timeout certificates (different `2f+1` subsets) with different
locks; `msg_tc_lock` / `msg_tc_nolock` record each one that was sent, and a
proposal is checked against *some* certificate of the previous view, which
is what a leader may attach.

**Validator-local state**, free of the network contract, kept **monotone
and view-indexed** ([MvbaPlan.md](../docs/MvbaPlan.md) §3 says why: mutable current-view
fields would pull strong fairness into the liveness argument): `input i x`
(the `propose` argument); `entered i v` (the current view is the maximum
entered, `in_view`); `voted i v` (`lastVotedView_i` was raised to `v`, so
"`v_msg > lastVotedView_i`" is `∀ w, voted i w → w < v_msg`);
`accepted i v x` (`x_v`); `local_prepqc i w e` (`PrepQC_i` has been the
certificate `(w, e)`; the current one is the highest held); `timed_out i v`
(`timedOut_i`); `commit_sent i v` (`commitSent_i`); `proposed_in l v` (the
leader's `Pre-Prepare` in `v` was sent); `decided i x`; `abandoned i`;
`avail_ready i x` (`AvailReady_i(x)`, set by the caller's input); and
`tc_formed i v` (`i` has formed `TC_{s,v}`, the flag of
Supplement, Algorithm 1, line 85 (`line:mvba:ht-advance`)); and
`decided_qc i v e` (`DecidedQC_i`, the certificate `i`'s decision used and
outputs). `DecidedQC_i` is set exactly when `i` decides, so
`∀ E, ¬ decided i E` is `DecidedQC_i = ⊥`.

## Abstractions

* **Messages monotone, local state free.** The guards `¬ timed_out i v`,
  `¬ commit_sent i v`, `∀ w, voted i w → w < v`, `∀ V, entered i V → V ≤ v`
  and `∀ W E, local_prepqc i W E → W < w` read the acting validator's own
  local relations negatively ([Locality.md](../docs/Locality.md) R1).
* **`SyncView` is its own action.** The supplement runs `SyncView(J)`
  inside the `Pre-Prepare` handler before the checks; here the
  `sync_view_*` steps advance the view on any timeout certificate at or
  above the current view, and the handler requires the message's view to be
  the current one — the same reachable states in two steps. Adopting the
  certificate's lock (Supplement, Algorithm 1, line 95 (`line:mvba:sv-adopt`)) is `sync_view_adopt`;
  `sync_view_lock` advances on a lock certificate without adopting, which
  only adds behaviours (the safety argument never relies on adoption).
  Each forwards the certificate it advanced on.
* **A timeout carrying a certificate of view above its own** still counts
  towards the `2f+1` of a timeout certificate, but its certificate
  contributes to no `highPrepQC`: one "contributes to `highPrepQC` only if
  it is itself valid for the same slot and its view is no greater than the
  view of the timeout message carrying it" (Supplement, Section 1.3
  (`subsec:mvba-correctness`); Supplement, Algorithm 1, line 4
  (`line:mvba:derived`)). A Byzantine validator may send one
  (`byz_timeout_qc`), and the timeout-certificate rules read such a member
  as carrying `⊥`: the correct validator's (`form_own_tc_*`), as the
  supplement's receiver does, and the adversary's (`byz_form_tc_*`), whose
  certificate's `highPrepQC` its signatures determine.
* **The view timer is an abstract phase marker.** `timer_expired i v` is
  set by `i`'s own timer step `expire_timer` and guards both timeout
  actions. It is a clock with exactly one tick — before the timeout, after
  the timeout — and no arithmetic, which is what an *untimed* model can
  carry. Without it the timeout actions are always enabled in the current
  view, the scheduler chooses freely between timing out and making progress,
  and the timing discipline has to be restored by an assumption naming the
  protocol's own conclusion; with it, the choice is the timer's, the
  timeout actions are weakly fair like every other honest action, and the
  assumption becomes an ordering constraint on `expire_timer`
  ([MvbaPlan.md](../docs/MvbaPlan.md) §3.2,
  [Mvba/Liveness.lean](Mvba/Liveness.lean)). Safety is untouched: a
  guard only removes behaviours.
* **`timeout` covers the timer and the `f+1` echo rule**
  (Supplement, Algorithm 1, line 36 (`line:mvba:timeout-send`), Supplement, Algorithm 1, line 83 (`line:mvba:ht-send`)): both send the same
  message under the same local update; the rule that *enables* the second
  matters only for liveness and is left to the liveness step.
* **`AvailReady` is the caller's input**: `become_avail_ready` is
  unguarded, and `send_commit` reads `avail_ready` positively. The
  contract instance classifies it as the input `markAvail`
  ([Mvba/Compose.lean](Mvba/Compose.lean)), which Chorus drives with its
  chunk wait as the guard. The supplement states `AvailReady` over the
  dissemination layer's state, which Module 3 (`mod:mvba`) does not expose
  (finding P12, [PaperAlignment.md](../docs/PaperAlignment.md) §6).
  Safety-neutral, and the hook for the supplement's `Δ_sync` assumption.
* **`abandon` is modelled** as a monotone flag every honest send requires
  unset, and `propose` is the `input` record. `abandoned` is the *caller's*
  input only, the contract's `MVBA.abandon`.
* **A decided validator halts.** Both of the supplement's decision paths
  end in `decide(…); abandon()` (the procedure `Decide` in
  Supplement, Algorithm 1 (`alg:mvba-cont3`), reached from Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`), and the restart
  path at Supplement, Algorithm 1, line 49 (`line:mvba:restart-guard`)), where `abandon()` "halts all MVBA sending and
  stops `W`", and its timeout fires only when there is "no decision in view
  `v`" (Supplement, Algorithm 1, line 36 (`line:mvba:timeout-send`)). So every honest send also requires
  `∀ E, ¬ decided i E`: after deciding, `i` sends nothing, and in
  particular never times out. The halt is kept apart from `abandoned`,
  because the contract's Termination premise ("no correct validator
  abandons before the bound") is about the caller's `abandon()`, and a
  validator's own halt after deciding must not count against it.
  `expire_timer` sends nothing and needs no halt guard: once `i` has
  halted, no action reads its timer.
* **Integrity by construction**: `decide` and `form_own_commitqc` require
  `∀ E, ¬ decided i E`.
* **Delivery is in the premise, not in the model.** A sent message is
  visible at once, as for Chorus: each network relation holds from the
  message's first delivery to a correct validator, and the delay is put on
  the step that consumes it. The supplement's network — delivery within
  `Δ` for messages sent at or after GST, retransmission of timeouts,
  `ViewTC_i` and a decided `CommitQC` every `ρ`, one-view retention and
  lower-view discard (the termination setting before
  Supplement, Lemma 13 (`lem:decision-propagation`); Supplement, Section 10.3 (`sec:reliable-delivery`)) — is stated in the
  timed claim's premise over these relations, clause by clause
  (`Mvba.BoundedJustice`). The one guard it shaped is `adopt_prepqc`'s:
  a prepare certificate does not travel, so a validator forms its own
  from the prepares it received ([Bounds.md](../docs/Bounds.md) §6.2.4,
  (N4)).
* **Handler segments are atomic.** Each handler is one action, so the
  model reasons about uninterrupted handler segments, which is what the
  supplement's own Supplement, Remark 2 (`rem:execution-model`) justifies: `Recover` is the only
  suspension point, and with `Recover` a choice made in the same step here
  each of its three continuation guards (Supplement, Algorithm 1, line 12 (`line:mvba:leader-guard`), Supplement, Algorithm 1, line 79 (`line:mvba:decide-guard`),
  Supplement, Algorithm 1, line 49 (`line:mvba:restart-guard`)) is vacuous.
* **`propose` enters the first view.** The supplement's `propose` enters
  the view justified by the highest retained timeout certificate; here
  `propose` enters `vord.zero` and the `sync_view_*` steps advance in separate steps.
  The faithful rule would read "no higher certificate is retained", a
  negative read of `msg_tc` that the monotone-network contract forbids. So
  a late view-1 leader may still send its view-1 `Pre-Prepare` before it
  syncs, which the supplement suppresses: neutral for safety, and no
  liveness argument uses it.
* **Not modelled**: persistence and crash recovery (Supplement, Algorithm 1, line 42 (`line:mvba:reload`),
  Supplement, Corollary 1 (`cor:mvba-recovery-termination`)), the recovery layer's durable set
  `Accepted_i` of accepted meta-blocks (registered at
  Supplement, Algorithm 1, line 57 (`line:mvba:hp-record`); the model's counterpart of the supplement's
  invariant that a `Prepare` on `e` has a valid accepted `x` with
  `entries(x) = e` is `honest_prepare_accepted` with `accepted_valid`), the
  availability shares. Why that is sound for safety: with the state
  persisted before each send and reloaded atomically, a crash and restart
  is, to every other validator, a pause, and the model's runs already
  pause; persistence is the implementation's obligation, and termination
  under crashes is Supplement, Corollary 1
  (`cor:mvba-recovery-termination`), which nothing here claims. The
  shares belong to Chorus, which drives `AvailReady` from them. The
  certificate `decide(x, CommitQC)` returns is `DecidedQC_i`
  (`decided_qc`), output under `i`'s name (`msg_commitqc i`); the instance
  exports the first as the contract's `decidedCert` and checks a handed-in
  certificate against the second (`certifies`,
  [Mvba/Compose.lean](Mvba/Compose.lean)). The MVBA does not broadcast it:
  the composing layer does ("Decision output and handoff").

## The safety argument, and where it departs from the supplement's

The supplement proves Supplement, Theorem 1 (`thm:agreement`) from Supplement, Lemma 8 (`lem:lock-persistence`), whose
statement quantifies over every view `v' ≥ v` and whose proof is an
**induction on `v'`**. That statement is true at every reachable state, but
it is not an *inductive* invariant: when a commit certificate of view `v`
forms, timeout and prepare certificates of higher views may already exist,
and re-establishing the claim for all of them is exactly the induction —
which a one-step verification condition cannot perform. The clump
therefore carries the standard first-order strengthening (the shape of the
Paxos-made-EPR invariant): **every prepare certificate of view `w` blocks,
in every lower view `v` and for every other value `e`, a supermajority from
committing `e` in `v`** — every supermajority has a correct member that
either timed out at or after `v` without a lock of view `≥ v`, or holds a
view-`v` lock on a different value (`prepqc_blocks_lower_commits`,
`blocked`). Its inductive step at `adopt_prepqc` (and at `byz_form_prepqc`) is the supplement's
argument for one view transition (the honest preparer's justification, the
timeout quorum's honest intersection with the given supermajority, and the
invariant itself at the lock's certificate), and Supplement, Lemma 8 (`lem:lock-persistence`)
(i)/(ii), Supplement, Lemma 3 (`lem:cert-uniqueness`) across views (`commitqc_agree`) and
Supplement, Theorem 1 (`thm:agreement`) follow from it by instantiation.
[MvbaPlan.md](../docs/MvbaPlan.md) §2.6 maps the supplement's lemmas onto
this argument.

## Byzantine behaviour

A Byzantine node may sign any `Pre-Prepare`, `Prepare`, `Commit` or
`Timeout` (`byz_*`); a Byzantine timeout can carry only a certificate that
exists. It cannot forge a certificate: the four certificate relations are
assembled only from `2f+1` signatures (Supplement, Remark 1 (`rem:signature-separation`)). Honest
receivers check that a `Pre-Prepare` comes from `leader v`, so a Byzantine
leader may equivocate and a Byzantine non-leader's proposals are inert. -/

veil module Mvba

type node
type nodeset
/-- A meta-block representation: the entry vector together with the
certificate kind of each positive entry (the header, "The value type"),
opaque here. -/
type value
/-- An entry vector `entries(x)`, opaque here. -/
type evec
type view

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet
instantiate vord : TotalOrderWithMinimum view

/-- `entries(x)`: the entry vector of a representation (Supplement, Section 1.1
(`subsec:mvba-datatypes`)). The MVBA votes and decides over it. -/
immutable function ent : value → evec

/-- The external validity predicate `Valid` (Module 3 (`mod:mvba`); the supplement's
"`x` is a valid meta-block", Supplement, Section 1.1 (`subsec:mvba-datatypes`)) — uninterpreted. -/
immutable relation valid (e : value)

/-- `Leader(slot, v)`: a deterministic public function (functional by
`leader_functional`). -/
immutable relation leader (v : view) (l : node)

/-! ## Network — signed messages and certificates -/

relation msg_preprepare (l : node) (v : view) (x : value)
relation msg_prepare (r : node) (v : view) (e : evec)
relation msg_commit (r : node) (v : view) (e : evec)
relation msg_timeout_qc (r : node) (v : view) (w : view) (e : evec)
relation msg_timeout_noqc (r : node) (v : view)
/-- `s` attaches the prepare certificate `prepareQC_{s,v}` on `e` to its
messages: `s` formed it (an honest `adopt_prepqc`, or a Byzantine
`byz_form_prepqc`). Read only to check a certificate that another message
carries. -/
relation msg_prepqc (s : node) (v : view) (e : evec)
/-- `s` outputs the commit certificate of view `v` on `e` with its decision
(an honest `form_own_commitqc` or `decide`), or a Byzantine `s` aggregated
it (`byz_form_commitqc`). -/
relation msg_commitqc (s : node) (v : view) (e : evec)
/-- `s` has sent a timeout certificate `TC_{s,v}`, formed or forwarded. -/
relation msg_tc (s : node) (v : view)
/-- `s` has sent a `TC_{s,v}` whose `highPrepQC` is the certificate
`(w, e)`. -/
relation msg_tc_lock (s : node) (v : view) (w : view) (e : evec)
/-- `s` has sent a `TC_{s,v}` whose `highPrepQC` is `⊥`. -/
relation msg_tc_nolock (s : node) (v : view)

/-! ## Validator-local state -/

relation input (i : node) (x : value)
relation entered (i : node) (v : view)
relation voted (i : node) (v : view)
relation accepted (i : node) (v : view) (x : value)
relation local_prepqc (i : node) (w : view) (e : evec)
relation timed_out (i : node) (v : view)
relation commit_sent (i : node) (v : view)
relation proposed_in (l : node) (v : view)
relation decided (i : node) (x : value)
relation abandoned (i : node)
relation avail_ready (i : node) (x : value)
/-- The view timer, as an abstract phase marker: `timer_expired i v` says
`i`'s timer for view `v` has run out (the header, "Abstractions"). -/
relation timer_expired (i : node) (v : view)
/-- `i` has formed a timeout certificate for view `v` itself — the
supplement's "`TC_{s,v}` has already been formed" (Supplement, Algorithm 1, line 85 (`line:mvba:ht-advance`)),
which is what makes that rule fire once per view. -/
relation tc_formed (i : node) (v : view)
/-- `DecidedQC_i`: the commit certificate of view `v` on `e` that `i`'s
decision used, formed (`form_own_commitqc`) or received (`decide`). It is
the certificate `i`'s decision outputs, the contract's `decidedCert`. -/
relation decided_qc (i : node) (v : view) (e : evec)

#gen_state

/-- `Leader(slot, v)` names one leader per view. -/
assumption [leader_functional]
  ∀ (V : view) (L L' : node), leader V L → leader V L' → L = L'

/-! ## Derived state (ghosts) -/

/-- The current view is the maximum entered view (a negative observation of
own local state only). -/
ghost relation in_view (i : node) (v : view) :=
  entered i v ∧ ∀ V, entered i V → vord.le V v

/-- Some sent `TC_{s,pv}` has `lock = e`. -/
ghost relation lock_available (pv : view) (e : evec) :=
  ∃ s w, msg_tc_lock s pv w e

/-- Some sent `TC_{s,pv}` has `lock = ⊥`. -/
ghost relation nolock_available (pv : view) :=
  ∃ s, msg_tc_nolock s pv

/-- `n` sent a timeout at or after view `v` carrying no lock of view `≥ v`:
it left view `v` without a view-`v` lock and can no longer commit in it
(Supplement, Lemma 7 (`lem:timeout-closes-view`), Supplement, Lemma 2 (`lem:commit-provenance`)). -/
ghost relation left_view (n : node) (v : view) :=
  ∃ v', vord.le v v' ∧
    (msg_timeout_noqc n v' ∨ ∃ w e, msg_timeout_qc n v' w e ∧ vord.lt w v)

/-- `n` cannot commit `e` in view `v`: it left the view without a view-`v`
lock, or it holds a view-`v` lock on another value. -/
ghost relation blocked (n : node) (v : view) (e : evec) :=
  left_view n v ∨ ∃ e', ¬ e' = e ∧ local_prepqc n v e'

/-! ## Initial state -/

-- `after_init`, the longest action body, exceeds the default recursion
-- depth ([CLAUDE.md](../CLAUDE.md), "Hard rules", on `maxRecDepth`).
set_option maxRecDepth 8192

after_init {
  msg_preprepare L V E := false
  msg_prepare R V E := false
  msg_commit R V E := false
  msg_timeout_qc R V U E := false
  msg_timeout_noqc R V := false
  msg_prepqc S V E := false
  msg_commitqc S V E := false
  msg_tc S V := false
  msg_tc_lock S V U E := false
  msg_tc_nolock S V := false
  input I E := false
  entered I V := false
  voted I V := false
  accepted I V E := false
  local_prepqc I U E := false
  timed_out I V := false
  commit_sent I V := false
  proposed_in L V := false
  decided I E := false
  abandoned I := false
  avail_ready I E := false
  timer_expired I V := false
  tc_formed I V := false
  decided_qc I V E := false
}

/-! ## Inputs (Module 3 (`mod:mvba`)) -/

/-- `propose(B_i)` — sets the input, enters view 1 and begins participation.
Once per validator.

`require valid e` is the supplement's precondition on `propose`, checked
rather than assumed: Supplement, Section 1.2 (`subsec:mvba-protocol`) gives the call a validity
precondition and Supplement, Theorem 2 (`thm:termination`)'s proof relies on it in as many words
("the leader proposes its input `B_l`, which is a valid \metablock by the
precondition of `propose`"). The contract states the same obligation on the
caller's side, as an antecedent of `MVBATemporal.termination`
([Interfaces.lean](Interfaces.lean)); Chorus meets it with three `require` clauses,
and this guard is the implementation's own check of it. -/
action propose (i : node) (x : value) {
  require ∀ X, ¬ input i X
  require ¬ abandoned i
  require valid x
  input i x := true
  entered i vord.zero := true
}

/-- `abandon()` — halts this validator's MVBA sending: every honest send
below requires `¬ abandoned i`. -/
action abandon (i : node) {
  abandoned i := true
}

/-! ## The leader (Supplement, Algorithm 1 (`alg:mvba`), "upon entering view v") -/

/-- View 1: `x ← B_i`, `J ← ⊥`. -/
action leader_propose_first (l : node) (x : value) {
  require ¬ is_byz l
  require ¬ abandoned l
  require ∀ E, ¬ decided l E
  require leader vord.zero l
  require in_view l vord.zero
  require input l x
  require ¬ proposed_in l vord.zero
  proposed_in l vord.zero := true
  msg_preprepare l vord.zero x := true
}

/-- View `v > 1` with `lock(J) ≠ ⊥`: `x ← Recover(lock(J))`, a valid
representation of the lock's entries (Supplement, Lemma 10 (`lem:reproposal`)). `J` is `ViewTC_l`, the timeout
certificate that justified the leader's entry into `v`, which it forwarded
under its own name when it entered (`msg_tc_lock l pv …`, its own send). The participation guard `∃ E, input
l E` is redundant at reachable states (a view `> 1` is entered only through
the `sync_view_*` steps, which require it) and is what makes the contract's Quiescence
a one-step fact for this send too ([Mvba/Compose.lean](Mvba/Compose.lean)). -/
action leader_repropose (l : node) (pv : view) (v : view) (w : view) (x : value) {
  require ¬ is_byz l
  require ∃ E, input l E
  require ¬ abandoned l
  require ∀ E, ¬ decided l E
  require vord.next pv v
  require leader v l
  require in_view l v
  -- `x ← Recover(lock(J))`: a valid representation of the lock's entries.
  require msg_tc_lock l pv w (ent x)
  require valid x
  require ¬ proposed_in l v
  proposed_in l v := true
  msg_preprepare l v x := true
}

/-- View `v > 1` with `lock(J) = ⊥`: `x ← B_i`, with `J = ViewTC_l` as above. -/
action leader_propose_fresh (l : node) (pv : view) (v : view) (x : value) {
  require ¬ is_byz l
  require ¬ abandoned l
  require ∀ E, ¬ decided l E
  require vord.next pv v
  require leader v l
  require in_view l v
  require msg_tc_nolock l pv
  require input l x
  require ¬ proposed_in l v
  proposed_in l v := true
  msg_preprepare l v x := true
}

/-! ## The `Pre-Prepare` handler (Supplement, Algorithm 1, line 17 (`line:mvba:pp-guard`)) and `HandleProposal` -/

/-- View 1: current view, sender is the leader, `x` valid, `J = ⊥`,
`1 > lastVotedView_i`. Then `HandleProposal` (Supplement, Algorithm 1, line 57 (`line:mvba:hp-record`),
Supplement, Algorithm 1, line 59 (`line:mvba:hp-prepare`)): record `x_v`, raise `lastVotedView_i`, send the
`Prepare` on the entry vector. -/
action handle_preprepare_first (i : node) (l : node) (x : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i vord.zero
  require leader vord.zero l
  require msg_preprepare l vord.zero x
  require valid x
  require ∀ W, voted i W → vord.lt W vord.zero
  accepted i vord.zero x := true
  voted i vord.zero := true
  msg_prepare i vord.zero (ent x) := true
}

/-- View `v > 1`: additionally `J` is a `TC_{s,v-1}` and `entries(x) =
lock(J)` whenever `lock(J) ≠ ⊥` — against some timeout certificate of the
previous view (see the header on `msg_tc_lock`). -/
action handle_preprepare (i : node) (l : node) (pv : view) (v : view) (x : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require vord.next pv v
  require leader v l
  require msg_preprepare l v x
  require valid x
  require lock_available pv (ent x) ∨ nolock_available pv
  require ∀ W, voted i W → vord.lt W v
  accepted i v x := true
  voted i v := true
  msg_prepare i v (ent x) := true
}

/-! ## Prepare certificates and the commit -/


/-- `TryFormPrepQC` (Supplement, Algorithm 1, line 63 (`line:mvba:tfp-guard`), Supplement, Algorithm 1, line 65 (`line:mvba:tfp-store`)): `i`
holds `2f+1` `Prepare` signatures on the vector it prepared in its current
view — the quorum `q` is the label's parameter — has not yet formed a
certificate in this view (its held one is of a lower view), and has not
timed out. It forms `prepareQC_{s,v}` itself and stores it as `PrepQC_i`.

Prepare certificates do not travel: a validator holds one only from the
prepares it received itself, never from another validator's certificate
(the supplement). So the guard reads the prepares, not `msg_prepqc`, and
the step also writes the certificate under `i`'s name, since from then on
`i`'s timeouts carry it. A Byzantine validator forms one through
`byz_form_prepqc`. -/
action adopt_prepqc (i : node) (v : view) (x : value) (q : nodeset) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_prepare r v (ent x)
  require accepted i v x
  require ∀ W E, local_prepqc i W E → vord.lt W v
  require ¬ timed_out i v
  local_prepqc i v (ent x) := true
  msg_prepqc i v (ent x) := true
}

/-- **The view timer runs out.** `i`'s own timer for a view it has entered
expires; the two timeout actions are guarded on it. A step of the correct
validator `i` on its own rows only.

This is the whole of the timing that reaches the model — a phase marker, not
a clock: one tick, from before the timeout to after it. What it buys is
stated in the header: it takes the *choice* of timing out away from the
scheduler, so the timeout actions can be weakly fair like every other honest
action instead of being always enabled, and the timing assumption becomes an
ordering constraint on this action rather than a claim about the protocol's
outcome. Safety-neutral: it only removes behaviours from the timeout
actions. -/
action expire_timer (i : node) (v : view) {
  require ¬ is_byz i
  require entered i v
  timer_expired i v := true
}

/-- **The caller's availability input** at `i` (the contract's `markAvail`):
the composing dissemination layer reports that `i` holds its availability
shares for `x` (`AvailReady_i`; Supplement, Lemma 5 (`lem:avail-progress`)
bounds when). Unguarded; Chorus drives it with its chunk wait. -/
action become_avail_ready (i : node) (x : value) {
  avail_ready i x := true
}

/-- `TrySendCommit` (Supplement, Algorithm 1, line 90 (`line:mvba:commit-send`)): `entries(x_v) = e`, `PrepQC_i`
is of the current view and on `e`, `¬ timedOut_i`, `¬ commitSent_i`,
`AvailReady_i(x_v)`. -/
action send_commit (i : node) (v : view) (x : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require accepted i v x
  require local_prepqc i v (ent x)
  require ¬ timed_out i v
  require ¬ commit_sent i v
  require avail_ready i x
  commit_sent i v := true
  msg_commit i v (ent x) := true
}


/-- `TryFormCommitQC` then `Decide` (Supplement, Algorithm 1 (`alg:mvba-cont3`)): `i` holds `2f+1`
`Commit` signatures on `e` for its current view `v` — the quorum `q` is the
label's parameter — and has not already learned a decision certificate
(`DecidedQC_i = ⊥`). It forms the `CommitQC`, records it as `DecidedQC_i`
and decides a valid representation `x` of the certified entries, in one
handler segment (`x_v` or `Recover(e)`, chosen in the step, so `Decide`'s
continuation guard is vacuous). `DecidedQC_i ≠ ⊥` is exactly
"`i` has decided" in this model, since both of the supplement's decision
paths set it (here and Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`), the action `decide`), so the
guard is `∀ E, ¬ decided i E`. The step records the certificate as
`DecidedQC_i` (`decided_qc`) and outputs it under `i`'s name
(`msg_commitqc i`): the decision's output certificate, which the composing
layer hands on (Supplement, Lemma 13 (`lem:decision-propagation`)) and
`decide` checks elsewhere. -/
action form_own_commitqc (i : node) (v : view) (x : value) (q : nodeset) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit r v (ent x)
  -- `x_v` or `Recover(e)`: a valid representation of the certified entries.
  require valid x
  decided_qc i v (ent x) := true
  msg_commitqc i v (ent x) := true
  decided i x := true
}

/-- `decide(x, CommitQC)`: the procedure `Decide` (Supplement, Algorithm 1 (`alg:mvba-cont3`)),
reached from `TryFormCommitQC` and from the transferred-certificate handler
(Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)), is one action, deciding a valid representation of the certified entries (`Recover(e)`). A certificate of
any view is accepted: the one `s` output, read positively. Once
(`DecidedQC_i = ⊥`). The transferred certificate is recorded as
`DecidedQC_i` and output with the decision under `i`'s name, as for one `i`
formed ("it proceeds identically"). -/
action decide (i : node) (s : node) (v : view) (x : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require msg_commitqc s v (ent x)
  -- `Recover(e)`: a valid representation of the certified entries.
  require valid x
  require ∀ E, ¬ decided i E
  decided_qc i v (ent x) := true
  msg_commitqc i v (ent x) := true
  decided i x := true
}

/-! ## Timeouts, timeout certificates and view change -/

/-- The timer fires in the current view (Supplement, Algorithm 1, line 36 (`line:mvba:timeout-send`); also
the `f+1` echo, Supplement, Algorithm 1, line 83 (`line:mvba:ht-send`)): `timedOut_i ← true`, raise
`lastVotedView_i`, send `⟨Timeout, s, v, PrepQC_i, σ_i⟩` with the highest
held certificate. -/
action timeout_qc (i : node) (v : view) (w : view) (e : evec) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require timer_expired i v
  require ¬ timed_out i v
  require local_prepqc i w e
  require ∀ W E, local_prepqc i W E → vord.le W w
  timed_out i v := true
  voted i v := true
  msg_timeout_qc i v w e := true
}

/-- The same timeout when `i` holds no certificate: the `Timeout` carries
`PrepQC_i = ⊥`. -/
action timeout_noqc (i : node) (v : view) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require timer_expired i v
  require ¬ timed_out i v
  require ∀ W E, ¬ local_prepqc i W E
  timed_out i v := true
  voted i v := true
  msg_timeout_noqc i v := true
}

/-- `HandleTimeout`'s second rule (Supplement, Algorithm 1, line 85 (`line:mvba:ht-advance`)): "upon first
collecting `2f+1` valid timeout messages" for its current view `v`, `i`
forms `TC_{s,v}` (Supplement, Algorithm 1, line 4 (`line:mvba:derived`)).
Here it is the one whose `highPrepQC` is the certificate `(w, e)` carried
by member `r0`: a valid certificate of view `w ≤ v` (checked against the
certificate its former `s` attaches), and every member carries `⊥`, a
certificate of view `≤ w`, or one of a view above `v`, which counts as `⊥`
(the header, "A timeout carrying a certificate of view above its own"). `i` records that it has formed it
(`tc_formed i v`, whose absence is the "not already formed" condition) and
sends it under its own name. `i` then processes it through `SyncView`
(the `sync_view_*` steps, which read it), as every holder does: the
supplement's `SyncView(TC_{s,v})` in the same handler is the model's next
step, the same reachable states in two steps (the header, "`SyncView` is
its own action"). -/
action form_own_tc_lock (i : node) (v : view) (q : nodeset) (r0 : node) (s : node) (w : view) (e : evec) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require ¬ tc_formed i v
  require nset.supermajority q
  require nset.member r0 q
  require msg_timeout_qc r0 v w e
  require msg_prepqc s w e
  require vord.le w v
  require ∀ r, nset.member r q →
    msg_timeout_noqc r v ∨
      ∃ W E, msg_timeout_qc r v W E ∧ (vord.le W w ∨ vord.lt v W)
  tc_formed i v := true
  msg_tc i v := true
  msg_tc_lock i v w e := true
}

/-- The same rule when every member of the quorum carries `⊥`, or a
certificate of a view above `v`, which counts as `⊥`. -/
action form_own_tc_nolock (i : node) (v : view) (q : nodeset) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require ¬ tc_formed i v
  require nset.supermajority q
  require ∀ r, nset.member r q →
    msg_timeout_noqc r v ∨ ∃ W E, msg_timeout_qc r v W E ∧ vord.lt v W
  tc_formed i v := true
  msg_tc i v := true
  msg_tc_nolock i v := true
}

/-- `SyncView(TC_{s,pv})` (Supplement, Algorithm 1, line 91 (`line:mvba:sv`), Supplement, Algorithm 1, line 96 (`line:mvba:sv-advance`)) on a
lock-free certificate, sent by `s`, at or above the current view: enter
`pv + 1`, and forward the certificate under `i`'s own name
(Supplement, Algorithm 1, line 98 (`line:mvba:sv-forward`)). -/
action sync_view_nolock (i : node) (s : node) (pv : view) (v : view) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require vord.next pv v
  require msg_tc_nolock s pv
  require ∀ V, entered i V → vord.le V pv
  entered i v := true
  msg_tc i pv := true
  msg_tc_nolock i pv := true
}

/-- The same on a certificate whose lock is `(w, e)`, without adopting the
lock: enter `pv + 1` and forward. The supplement adopts a lock that outranks
the held certificate (`sync_view_adopt`); not adopting only adds
behaviours, which the safety argument does not rely on (the header,
"`SyncView` is its own action"). -/
action sync_view_lock (i : node) (s : node) (pv : view) (v : view) (w : view) (e : evec) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require vord.next pv v
  require msg_tc_lock s pv w e
  require ∀ V, entered i V → vord.le V pv
  entered i v := true
  msg_tc i pv := true
  msg_tc_lock i pv w e := true
}

/-- `SyncView` with adoption (Supplement, Algorithm 1, line 95 (`line:mvba:sv-adopt`)): the certificate's lock
`(w, e)` is of a higher view than every held certificate, so `PrepQC_i`
adopts it while `i` enters `pv + 1` and forwards the certificate. -/
action sync_view_adopt (i : node) (s : node) (pv : view) (v : view) (w : view) (e : evec) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require vord.next pv v
  require msg_tc_lock s pv w e
  require ∀ V, entered i V → vord.le V pv
  require ∀ W E, local_prepqc i W E → vord.lt W w
  local_prepqc i w e := true
  entered i v := true
  msg_tc i pv := true
  msg_tc_lock i pv w e := true
}

/-! ## Byzantine behaviour — arbitrary signatures, no forged certificates -/

action byz_preprepare (l : node) (v : view) (x : value) {
  require is_byz l
  msg_preprepare l v x := true
}

action byz_prepare (r : node) (v : view) (e : evec) {
  require is_byz r
  msg_prepare r v e := true
}

action byz_commit (r : node) (v : view) (e : evec) {
  require is_byz r
  msg_commit r v e := true
}

/-- A Byzantine timeout carries `⊥` or a certificate that exists, of any
view; one above its own view counts as `⊥` at every timeout-certificate
rule (the header). -/
action byz_timeout_qc (r : node) (s : node) (v : view) (w : view) (e : evec) {
  require is_byz r
  require msg_prepqc s w e
  msg_timeout_qc r v w e := true
}

action byz_timeout_noqc (r : node) (v : view) {
  require is_byz r
  msg_timeout_noqc r v := true
}

/-! The adversary aggregates any certificate the signatures allow, under its
own name: `2f+1` signatures, read wherever they are, form the certificate,
and the Byzantine `r` sends it. A certificate cannot be forged (Supplement,
Remark 1 (`rem:signature-separation`)). -/

/-- `2f+1` `Prepare` signatures on `e` in view `v` form `prepareQC_{s,v}`. -/
action byz_form_prepqc (r : node) (v : view) (e : evec) (q : nodeset) {
  require is_byz r
  require nset.supermajority q
  require ∀ R, nset.member R q → msg_prepare R v e
  msg_prepqc r v e := true
}

/-- `2f+1` `Commit` signatures on `e` in view `v` form the `CommitQC`. -/
action byz_form_commitqc (r : node) (v : view) (e : evec) (q : nodeset) {
  require is_byz r
  require nset.supermajority q
  require ∀ R, nset.member R q → msg_commit R v e
  msg_commitqc r v e := true
}

/-- `2f+1` timeouts of view `v` form `TC_{s,v}` whose `highPrepQC` is the
certificate `(w, e)` carried by member `r0`, with the guards of
`form_own_tc_lock`. -/
action byz_form_tc_lock (r : node) (v : view) (q : nodeset) (r0 : node) (s : node) (w : view) (e : evec) {
  require is_byz r
  require nset.supermajority q
  require nset.member r0 q
  require msg_timeout_qc r0 v w e
  require msg_prepqc s w e
  require vord.le w v
  require ∀ R, nset.member R q →
    msg_timeout_noqc R v ∨
      ∃ W E, msg_timeout_qc R v W E ∧ (vord.le W w ∨ vord.lt v W)
  msg_tc r v := true
  msg_tc_lock r v w e := true
}

/-- `2f+1` timeouts of view `v`, each carrying `⊥` or a certificate of a
view above `v`, form a lock-free `TC_{s,v}`. -/
action byz_form_tc_nolock (r : node) (v : view) (q : nodeset) {
  require is_byz r
  require nset.supermajority q
  require ∀ R, nset.member R q →
    msg_timeout_noqc R v ∨ ∃ W E, msg_timeout_qc R v W E ∧ vord.lt v W
  msg_tc r v := true
  msg_tc_nolock r v := true
}

/-! ## Safety — the three safety properties of Module 3 (`mod:mvba`)

Stated in the class's vocabulary (`MVBASafety` in
[Interfaces.lean](Interfaces.lean)) so that the provider step can discharge
the fields by the `reachable_*` projections of
[Mvba/Certify.lean](Mvba/Certify.lean). -/

/-- Supplement, Theorem 1 (`thm:agreement`) (entries level): correct validators that decide, decide
the same entry vector. -/
safety [agreement]
  ∀ (I J : node) (X X' : value),
    ¬ is_byz I → ¬ is_byz J → decided I X → decided J X' → ent X = ent X'

/-- Integrity: a correct validator decides at most one value. -/
safety [integrity]
  ∀ (I : node) (X X' : value),
    ¬ is_byz I → decided I X → decided I X' → X = X'

/-- Supplement, Lemma 9 (`lem:external-validity`): a decided value is valid. -/
safety [external_validity]
  ∀ (I : node) (X : value), ¬ is_byz I → decided I X → valid X

/-! ## Invariants — the supplement's lemmas

[MvbaPlan.md](../docs/MvbaPlan.md) §2.6 has the map from the supplement's
lemmas to the
rows below; the header explains the one departure (Supplement, Lemma 8 (`lem:lock-persistence`)
is a corollary, `prepqc_blocks_lower_commits` is the inductive form). -/

/-- Entering a view requires having proposed: `propose` sets `input` and
enters view 1 in the same step, and the three `sync_view_*` steps require
`∃ E, input i E`. Liveness uses it to read the participation premise off
`SettledIn` rather than carrying it as a second hypothesis
([Mvba/Liveness.lean](Mvba/Liveness.lean)). -/
invariant [entered_implies_input]
  ∀ (R : node) (V : view),
    ¬ is_byz R → entered R V → ∃ E, input R E

/-- The converse of `entered_implies_input`: having proposed means having
entered view 1. The same single step of `propose` read the other way round, and `propose` is the only
action that sets `input`.

Liveness needs it to start the climb. (F-justice) can only move a validator
that is *somewhere*, and the participation premise (`AllPropose`) says the
caller invoked `propose` — which this turns into a view the validator sits
in. Keeping it here rather than widening the premise is what lets that
premise stay the paper's sentence ("once every correct validator has invoked
propose") and nothing more. -/
invariant [input_implies_entered]
  ∀ (R : node) (E : value),
    ¬ is_byz R → input R E → entered R vord.zero

/-! ### The honest leader's single proposal

Invariants for **liveness** ([MvbaPlan.md](../docs/MvbaPlan.md) §3.5
step 3), and the formal content of Supplement, Theorem 2 (`thm:termination`)'s "the correct leader
broadcasts a single valid proposal `x_v`". Safety does not need them — it
does not care how many vectors a leader offers, only what a certificate
proves. -/

/-- An honest `Pre-Prepare` is recorded in `proposedIn_l`, which is what the
three leader actions check before sending. Support for the uniqueness
below: without it the `¬ proposed_in l v` guard cannot rule out an earlier
proposal. -/
invariant [honest_preprepare_proposed]
  ∀ (L : node) (V : view) (E : value),
    ¬ is_byz L → msg_preprepare L V E → proposed_in L V

/-- The converse of `honest_preprepare_proposed`: `proposedIn_l` is backed by
the `Pre-Prepare` it records, the two being set in the same step by all
three leader actions.

Liveness needs it for the same reason it needed `commit_sent_backed`: the
leader actions' `¬ proposed_in l v` guard is anti-monotone, so a fairness
argument has to know that the guard can only die by the proposal it was
waiting for ([Mvba/Liveness.lean](Mvba/Liveness.lean),
`eventually_preprepare_of_settled_leader`). -/
invariant [proposed_in_backed]
  ∀ (L : node) (V : view),
    ¬ is_byz L → proposed_in L V → ∃ E, msg_preprepare L V E

/-- Inputs are valid, by `propose`'s guard. It holds of Byzantine validators too:
`propose` is the contract's input and has no `is_byz` guard, so the check
applies to whoever calls it. -/
invariant [input_valid]
  ∀ (R : node) (E : value), input R E → valid E

/-- **An honest leader's proposal is valid.** The two fresh cases propose the
leader's own input (`input_valid`); the re-proposal case offers a certified
lock, which `tc_lock_backed` and `prepqc_valid` show is valid.

Liveness needs it because `handle_preprepare` requires `valid e`, so a
proposal no correct validator can accept is a wasted view. -/
invariant [honest_preprepare_valid]
  ∀ (L : node) (V : view) (E : value),
    ¬ is_byz L → msg_preprepare L V E → valid E

/-- **And it carries the justification the handler checks.** Above view 1 an
honest leader proposes either a lock of the previous view
(`leader_repropose`) or its own input against a lock-free certificate
(`leader_propose_fresh`) — which are exactly the two disjuncts of
`handle_preprepare`'s `lock_available pv e ∨ nolock_available pv`. In view 1 there
is no previous view, and `vord.next PV vord.zero` is impossible. -/
invariant [honest_preprepare_justified]
  ∀ (L : node) (V : view) (E : value) (PV : view),
    ¬ is_byz L → msg_preprepare L V E → vord.next PV V →
      lock_available PV (ent E) ∨ nolock_available PV

/-- An honest leader proposes at most one vector per view. -/
invariant [honest_preprepare_unique]
  ∀ (L : node) (V : view) (E E' : value),
    ¬ is_byz L → msg_preprepare L V E → msg_preprepare L V E' → E = E'

/-! ### Supplement, Lemma 1 (`lem:vote-uniqueness`) — one `Prepare` per view, on the accepted vector -/

/-- An honest `Prepare` is on the vector its sender accepted in that view. -/
invariant [honest_prepare_accepted]
  ∀ (R : node) (V : view) (E : evec),
    ¬ is_byz R → msg_prepare R V E → ∃ X, accepted R V X ∧ ent X = E

/-- The converse of `honest_prepare_accepted`: accepting and sending the
`Prepare` are the same step in both handlers, so for an honest validator the
two relations agree. Liveness needs this direction — the acceptance link's
guard analysis yields `accepted`, while the prepare quorum needs
`msg_prepare` ([Mvba/Liveness.lean](Mvba/Liveness.lean)). -/
invariant [accepted_implies_prepare]
  ∀ (R : node) (V : view) (X : value),
    ¬ is_byz R → accepted R V X → msg_prepare R V (ent X)

/-- Accepting raised `lastVotedView_i` to the view (Supplement, Algorithm 1, line 57 (`line:mvba:hp-record`)),
which is what makes the acceptance unique per view. -/
invariant [accepted_implies_voted]
  ∀ (R : node) (V : view) (E : value),
    ¬ is_byz R → accepted R V E → voted R V

invariant [accepted_unique]
  ∀ (R : node) (V : view) (E E' : value),
    ¬ is_byz R → accepted R V E → accepted R V E' → E = E'

/-- **A vote never outruns the views its holder has entered**, in the same
bound form as `local_prepqc_within_entered` and for the same reason: both
ways of voting — accepting a proposal and timing out — happen in the
current view.

A guard-analysis invariant for liveness: `handle_preprepare`'s
`∀ W, voted i W → W < v` is anti-monotone, and this pins a lapse to the
current view rather than one above it. -/
invariant [voted_within_entered]
  ∀ (R : node) (W : view) (U : view),
    ¬ is_byz R → voted R W → (∀ V, entered R V → vord.le V U) → vord.le W U

/-- **A vote that is not a timeout means the leader has already proposed.**
Accepting is the only other way to vote, and it requires the leader's
`Pre-Prepare`, which for an honest leader is recorded in `proposedIn_l`
(`honest_preprepare_proposed`).

Support for `voted_implies_accepted_proposal`: at the three leader actions the guard is `¬ proposed_in l v`, so this is what makes
"nobody can have voted in `v` yet" available there — without it, a
validator that had somehow voted before the honest leader's first proposal
could not be ruled out. -/
invariant [voted_implies_leader_proposed]
  ∀ (R : node) (V : view) (L : node),
    ¬ is_byz R → voted R V → ¬ timed_out R V →
      leader V L → ¬ is_byz L → proposed_in L V

/-- **And a vote that is not a timeout is an acceptance of the leader's
proposal.** A validator votes in a view in exactly two ways
(Supplement, Algorithm 1, line 57 (`line:mvba:hp-record`), Supplement, Algorithm 1, line 36 (`line:mvba:timeout-send`)), and the timeout sets
`timedOut_i` in the same step — so an honest validator that has voted in `V`
without timing out there accepted, and under an honest leader what it
accepted is the one vector that leader proposed
(`honest_preprepare_unique`, with `leader_functional`).

This completes the lapse analysis for `handle_preprepare`'s vote guard: at a
validator settled in `V`, the guard can only die by the acceptance the
argument was waiting for ([Mvba/Liveness.lean](Mvba/Liveness.lean),
`eventually_accepted_of_settled`). -/
invariant [voted_implies_accepted_proposal]
  ∀ (R : node) (V : view) (L : node) (E : value),
    ¬ is_byz R → voted R V → ¬ timed_out R V →
      leader V L → ¬ is_byz L → msg_preprepare L V E → accepted R V E

/-- Supplement, Lemma 9 (`lem:external-validity`)'s premise: only valid vectors are accepted
(Supplement, Algorithm 1, line 17 (`line:mvba:pp-guard`)). -/
invariant [accepted_valid]
  ∀ (R : node) (V : view) (E : value),
    ¬ is_byz R → accepted R V E → valid E

/-- The lifted justification check of Supplement, Algorithm 1, line 17 (`line:mvba:pp-guard`): an acceptance
in a view `v > 1` was justified by a `TC_{s,v-1}` whose lock is `⊥` or
the accepted vector. -/
invariant [accepted_justified]
  ∀ (R : node) (V : view) (E : value),
    ¬ is_byz R → accepted R V E → ¬ V = vord.zero →
      ∃ PV, vord.next PV V ∧ (nolock_available PV ∨ lock_available PV (ent E))

/-! ### Supplement, Lemma 2 (`lem:commit-provenance`) and Supplement, Remark 3 (`rem:lock-monotonicity`) -/

/-- An honest `Commit` on `e` in `v` was sent with `entries(x_v) = e` and a
`PrepQC_i` of view `v` on `e`. -/
invariant [honest_commit_accepted]
  ∀ (R : node) (V : view) (E : evec),
    ¬ is_byz R → msg_commit R V E →
      local_prepqc R V E ∧ ∃ X, ent X = E ∧ accepted R V X ∧ avail_ready R X

/-- `commitSent_i` implies the sender had voted in the view — it accepted
there first (`accepted_implies_voted`). On its own this says little; it is
what makes `commit_sent_backed` inductive, by ruling out the one case that breaks
it: a validator that has already sent its `Commit` in `v` cannot then accept
a *different* vector in `v`, because both `Pre-Prepare` handlers require
`∀ W, voted i W → W < v`. -/
invariant [commit_sent_implies_voted]
  ∀ (R : node) (V : view), ¬ is_byz R → commit_sent R V → voted R V

/-- An invariant for **liveness** rather than safety
([MvbaPlan.md](../docs/MvbaPlan.md) §3.5 step 3): `commitSent_i` is
backed by the `Commit` it records. `send_commit`'s `¬ commit_sent i v` guard
is anti-monotone, so a fairness argument has to know that the only way the
guard dies is the send it was waiting for — otherwise the guard could lapse
with nothing on the network and weak fairness would deliver nothing
([Mvba/Liveness.lean](Mvba/Liveness.lean),
`eventually_msg_commit_of_settled`). Stated against
the accepted vector rather than as `∃ E, msg_commit R V E` to keep it
quantifier-free in the conclusion; `accepted_unique` makes the two
equivalent at reachable states. -/
invariant [commit_sent_backed]
  ∀ (R : node) (V : view) (X : value),
    ¬ is_byz R → commit_sent R V → accepted R V X → msg_commit R V (ent X)

/-- A held certificate is one some validator formed. -/
invariant [local_prepqc_backed]
  ∀ (R : node) (W : view) (E : evec),
    ¬ is_byz R → local_prepqc R W E → ∃ S, msg_prepqc S W E

/-- **A held certificate never outruns the views its holder has entered.**
Stated against an arbitrary upper bound `U` on the entered views rather than
against the current view: `in_view` asserts a *maximum* entered view, whose
existence is not first-order derivable, and the bound form is also exactly
the shape of the `sync_view_*` guards, which is what makes the induction direct.
Applying it at `U := v` for a validator in view `v` recovers the reading
"every held certificate is of view at most `v`".

An invariant for **liveness** ([MvbaPlan.md](../docs/MvbaPlan.md) §3.5
step 3): `adopt_prepqc`'s guard `∀ W E, local_prepqc i W E → W < v` is anti-monotone,
so a fairness argument has to know what its failure means: with this, a
failure at a validator in view `v` pins the offending certificate to view
`v` exactly, and `local_prepqc_backed` and `prepqc_backed` with the
quorum intersection then pin its value — so the guard can only die by the
adoption the argument was waiting for ([Mvba/Liveness.lean](Mvba/Liveness.lean),
`eventually_local_prepqc_of_settled`). -/
invariant [local_prepqc_within_entered]
  ∀ (R : node) (W : view) (E : evec) (U : view),
    ¬ is_byz R → local_prepqc R W E → (∀ V, entered R V → vord.le V U) →
      vord.le W U

/-- Certificates are adopted with strictly increasing views
(Supplement, Algorithm 1, line 63 (`line:mvba:tfp-guard`), Supplement, Algorithm 1, line 95 (`line:mvba:sv-adopt`)), so one per view. -/
invariant [local_prepqc_unique]
  ∀ (R : node) (W : view) (E E' : evec),
    ¬ is_byz R → local_prepqc R W E → local_prepqc R W E' → E = E'

/-! ### Certificate backing (the lifted assembly guards) -/

invariant [prepqc_backed]
  ∀ (S : node) (V : view) (E : evec), msg_prepqc S V E →
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_prepare r V E

invariant [commitqc_backed]
  ∀ (S : node) (V : view) (E : evec), msg_commitqc S V E →
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_commit r V E

/-- Every carried certificate exists (honest senders carry held ones,
Byzantine senders may carry only existing ones). -/
invariant [timeout_qc_backed]
  ∀ (R : node) (V W : view) (E : evec),
    msg_timeout_qc R V W E → ∃ S, msg_prepqc S W E

/-- A timeout certificate is one of the two kinds. Every step that sends
`msg_tc s v` — forming one (`form_own_tc_*`, `byz_form_tc_*`) or forwarding
one (`sync_view_*`) — sends `msg_tc_nolock s v` or `msg_tc_lock s v w e`
with it, and nothing else sends it.

Liveness needs it to get from a sent `msg_tc s pv` to a `sync_view_*`
step it enables, and to the timeout quorum behind it, and from there to a *correct* validator
that has timed out in `pv`. That is the step showing a run cannot advance
past the honest-led view without some correct validator timing out there,
which (A-viewsync) forbids before deciding
([Mvba/Liveness.lean](Mvba/Liveness.lean)). -/
invariant [msg_tc_backed]
  ∀ (S : node) (V : view), msg_tc S V →
    msg_tc_nolock S V ∨ ∃ W E, msg_tc_lock S V W E

invariant [tc_nolock_backed]
  ∀ (S : node) (V : view), msg_tc_nolock S V →
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q →
      msg_timeout_noqc r V ∨ ∃ W E, msg_timeout_qc r V W E ∧ vord.lt V W

/-- A sent lock is a certificate of view `≤ v` carried by a member of
a `2f+1` timeout quorum none of whose members carries a higher one of view
`≤ v`. -/
invariant [tc_lock_backed]
  ∀ (S : node) (V W : view) (E : evec), msg_tc_lock S V W E →
    (∃ S', msg_prepqc S' W E) ∧ vord.le W V ∧
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q →
      msg_timeout_noqc r V ∨
        ∃ W' E', msg_timeout_qc r V W' E' ∧ (vord.le W' W ∨ vord.lt V W')

/-- **Every sent lock is a timeout certificate.** The converse direction
of `msg_tc_backed` for the lock case: every step that sends `msg_tc_lock`
sends `msg_tc` from the same sender, so the two never come apart.

Safety does not need it, because it reads certificates only to *justify*
things and a lock justifies more than a bare `msg_tc`. Liveness reads a
sent certificate as `msg_tc` and needs every lock to count as one
([Mvba/Liveness.lean](Mvba/Liveness.lean), `exists_tc_below_of_entered`). -/
invariant [tc_lock_implies_tc]
  ∀ (S : node) (V W : view) (E : evec), msg_tc_lock S V W E → msg_tc S V

/-- **A validator's record of having formed a timeout certificate is backed
by the certificate it sent.** `form_own_tc_lock` and `form_own_tc_nolock`
set `tc_formed i v` and `msg_tc i v` in one step, and nothing else sets the
record.

Liveness needs it for the rule's "not already formed" guard, which is
anti-monotone: its failure means the certificate the argument was waiting
for exists ([Mvba/Liveness.lean](Mvba/Liveness.lean)). -/
invariant [tc_formed_backed]
  ∀ (R : node) (V : view), tc_formed R V → msg_tc R V

/-- **A correct validator above view 1 has sent a timeout certificate for
the view below.** It entered that view through `SyncView`, which forwards
the certificate it advanced on (Supplement, Algorithm 1, line 98
(`line:mvba:sv-forward`)); view 1 it entered by `propose`.

Liveness needs it so that every correct validator is owed a view change by
a *correct* sender: the first correct validator in a view has sent the
certificate of the view below under its own name. -/
invariant [entered_forwarded]
  ∀ (I : node) (V : view),
    ¬ is_byz I → entered I V →
      V = vord.zero ∨ ∃ PV, vord.next PV V ∧ msg_tc I PV

/-! ### Supplement, Lemma 3 (`lem:cert-uniqueness`), within a view and across views -/

/-- All prepare certificates of a view are on one vector: the
two-supermajority intersection through an honest common signer and vote
uniqueness. -/
invariant [prepqc_unique]
  ∀ (S S' : node) (V : view) (E E' : evec),
    msg_prepqc S V E → msg_prepqc S' V E' → E = E'

/-- A commit certificate's honest signers held a prepare certificate of
the same view on the same vector (Supplement, Lemma 4 (`lem:lock-formation`)'s content). -/
invariant [commitqc_implies_prepqc]
  ∀ (S : node) (V : view) (E : evec), msg_commitqc S V E → ∃ S', msg_prepqc S' V E

/-- Supplement, Theorem 1 (`thm:agreement`) at the certificate level, across views: from
`prepqc_blocks_lower_commits` and the two-supermajority intersection. -/
invariant [commitqc_agree]
  ∀ (S S' : node) (V V' : view) (E E' : evec),
    msg_commitqc S V E → msg_commitqc S' V' E' → E = E'

/-- A prepare certificate is on a valid vector, by the same argument as
`commitqc_valid`: the `2f+1` signers contain an honest one, which accepted
the vector, and `accepted_valid` applies.

Liveness needs it where safety does not: `leader_repropose` re-proposes the
lock a timeout certificate carries **without** re-checking validity (the
supplement's `Recover`), while `handle_preprepare` requires `valid e`, so
the re-proposal is accepted only because the lock was valid all along. -/
invariant [prepqc_valid]
  ∀ (S : node) (V : view) (E : evec), msg_prepqc S V E → ∃ X, valid X ∧ ent X = E

/-- A commit certificate is on a valid vector: an honest signer accepted it. -/
invariant [commitqc_valid]
  ∀ (S : node) (V : view) (E : evec), msg_commitqc S V E → ∃ X, valid X ∧ ent X = E

/-- Every honest decision has its certificate, `DecidedQC_i`: both decision
paths set the two in one step. -/
invariant [decided_backed]
  ∀ (I : node) (X : value),
    ¬ is_byz I → decided I X → ∃ V, decided_qc I V (ent X)

/-- `DecidedQC_i` is the certificate `i` outputs under its own name. -/
invariant [decided_qc_sent]
  ∀ (I : node) (V : view) (E : evec),
    ¬ is_byz I → decided_qc I V E → msg_commitqc I V E

/-- `DecidedQC_i` is the certificate of `i`'s decision. -/
invariant [decided_qc_decided]
  ∀ (I : node) (V : view) (E : evec),
    ¬ is_byz I → decided_qc I V E → ∃ X, decided I X ∧ ent X = E

/-! ### Supplement, Lemma 7 (`lem:timeout-closes-view`) and the timeout's carried lock -/

/-- An honest `Timeout` carries a certificate its sender holds. -/
invariant [honest_timeout_qc_held]
  ∀ (R : node) (V W : view) (E : evec),
    ¬ is_byz R → msg_timeout_qc R V W E → local_prepqc R W E

/-- **Timing out means the timer had expired.** Both timeout actions are
guarded on the marker, and nothing else sets `timed_out`.

This is what lets the timing assumption be stated about `expire_timer` — the
validator's timer — rather than about the protocol's own outcome
([Mvba/Liveness.lean](Mvba/Liveness.lean), (A-viewsync)). -/
invariant [timed_out_implies_timer]
  ∀ (R : node) (V : view),
    ¬ is_byz R → timed_out R V → timer_expired R V

/-- **Timing out means having sent a `Timeout`.** The converse of
`honest_timeout_qc_timed_out` and `honest_timeout_noqc_timed_out`, and the
direction liveness needs: the timeout actions are reached
through the local `timedOut_i` flag, while the certificate assemblies read
the *messages*.

Both timeout actions set the flag and send the message in one step, and
nothing else sets the flag. -/
invariant [timed_out_implies_message]
  ∀ (R : node) (V : view),
    ¬ is_byz R → timed_out R V →
      msg_timeout_noqc R V ∨ ∃ W E, msg_timeout_qc R V W E

/-- **A correct validator's `Timeout` never carries a certificate of a view
above its own**: it carries the certificate it holds, which is of a view
it has entered (`local_prepqc_within_entered`), at most its current one. A
Byzantine `Timeout` may; the timeout-certificate rules read it as `⊥`
(the header).

Lock persistence needs it: the correct member a quorum intersection
yields is never one whose certificate the rules read as `⊥`. -/
invariant [timeout_qc_view_le]
  ∀ (R : node) (V W : view) (E : evec),
    ¬ is_byz R → msg_timeout_qc R V W E → vord.le W V

/-- An honest `Timeout` carrying a certificate records `timedOut_i` in its
view. -/
invariant [honest_timeout_qc_timed_out]
  ∀ (R : node) (V W : view) (E : evec),
    ¬ is_byz R → msg_timeout_qc R V W E → timed_out R V

/-- An honest `Timeout` carrying `⊥` records `timedOut_i` in its view. -/
invariant [honest_timeout_noqc_timed_out]
  ∀ (R : node) (V : view),
    ¬ is_byz R → msg_timeout_noqc R V → timed_out R V

/-- A validator times out only in a view it has entered. -/
invariant [timed_out_entered]
  ∀ (R : node) (V : view), ¬ is_byz R → timed_out R V → entered R V

/-- Supplement, Lemma 2 (`lem:commit-provenance`) across views: an honest validator that
committed in `v` sends no later timeout without a lock — its timeouts at
views `≥ v` carry a certificate of view `≥ v` (the `PrepQC_i` it held
when committing never decreases, Supplement, Remark 3 (`rem:lock-monotonicity`)). -/
invariant [commit_no_later_noqc_timeout]
  ∀ (R : node) (V V' : view) (E : evec),
    ¬ is_byz R → msg_commit R V E → msg_timeout_noqc R V' → vord.lt V' V

invariant [commit_later_timeout_carries_lock]
  ∀ (R : node) (V V' W : view) (E E' : evec),
    ¬ is_byz R → msg_commit R V E → msg_timeout_qc R V' W E' →
      vord.le V V' → vord.le V W

/-! ### Supplement, Lemma 8 (`lem:lock-persistence`), in inductive form -/

/-- Every prepare certificate of view `w` blocks, in every view `v < w` and
for every value `e` other than its own, every supermajority from
committing `e` in `v`: one correct member left `v` without a view-`≥ v`
lock, or holds a view-`v` lock on another value (see the header). -/
invariant [prepqc_blocks_lower_commits]
  ∀ (S : node) (W V : view) (E' E : evec) (Q : nodeset),
    msg_prepqc S W E' → vord.lt V W → ¬ E = E' → nset.supermajority Q →
      ∃ n, nset.member n Q ∧ ¬ is_byz n ∧ blocked n V E

/-! ## Step properties

Two-state facts, checked per action like an invariant
([Architecture.md](../docs/Architecture.md); [CLAUDE.md](../CLAUDE.md)'s
three sources for two-state facts, source (2)). -/

/-- **A newly entered view is view 1, or the successor of a view that already
has a timeout certificate.** The four actions that grow `entered` are
`propose`, which enters `vord.zero`, and the three `sync_view_*` steps,
whose guards read `msg_tc_nolock s pv` or `msg_tc_lock s pv w e` at the
pre-state.

Liveness needs it, and needs it as a *step* property rather than an
invariant because it relates the two states: it is what turns "a validator
advanced" into "a certificate for the view below existed", and with
`exists_honest_timed_out_of_tc` that becomes "a correct validator had timed
out there" — the induction showing a run cannot climb past the honest-led
view while no correct validator has decided
([Mvba/Liveness.lean](Mvba/Liveness.lean), `entered_le_of_no_timeout`). -/
step_property [entered_needs_certificate] {
  ∀ (I : node) (V : view),
    ¬ is_byz I ∧ ¬ entered I V ∧ entered' I V →
      V = vord.zero ∨
        ∃ PV S, vord.next PV V ∧ (msg_tc_nolock S PV ∨ ∃ W E, msg_tc_lock S PV W E) }

/- Proof reconstruction ON (this module only): captured at `#gen_spec`,
so it governs the background `doesNotThrow` dischargers this file still
runs. The invariant proofs live in the proof-file family, which sets the
option itself (read at tactic runtime on the cross-file path). -/
set_option veil.smt.trust false

/- VC registry ([Dependencies.md](../docs/Dependencies.md) §1): `#gen_spec` persists every
VC's statement plus its action/property metadata into the olean. This is
the model file's entire proof interface: the family's
`#prove_action`/`#prove_vc` commands re-create the VCs from these
statements. -/
set_option veil.gen.vcRegistry true

/- Proof cache ([Dependencies.md](../docs/Dependencies.md) §2), for the `doesNotThrow`
dischargers here; the proof files enable it themselves. -/
set_option veil.cache.proofs true

/- The label-enumeration instances the trace queries below need
(`ActionTag_EnumClass`) exceed the default instance-search budgets at this
action count and parameter arity ([CLAUDE.md](../CLAUDE.md), "Hard rules",
on `maxRecDepth`). -/
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192

-- A trace's cost is superlinear in its length, and the longest trace below
-- exceeds the default elaboration budget at `isDefEq`.
set_option maxHeartbeats 4000000

#gen_spec

/-! ## Non-vacuity witnesses ([MvbaPlan.md](../docs/MvbaPlan.md) §4 item 1)

`sat` verdicts here are trusted, deliberately: a wrong model can only make
a non-vacuity check vacuous, never a safety claim wrong
([Architecture.md](../docs/Architecture.md) §4 item 6). -/

-- Traces come last in the file: no `set_option … in` may follow a trace
-- block ([CLAUDE.md](../CLAUDE.md), "Hard rules").

-- A decision in view 1.
sat trace {
  propose
  leader_propose_first
  handle_preprepare_first
  adopt_prepqc
  become_avail_ready
  send_commit
  form_own_commitqc
  assert (∃ i x, ¬ is_byz i ∧ decided i x ∧ decided_qc i vord.zero (ent x) ∧
    msg_commitqc i vord.zero (ent x))
}

-- A Byzantine leader in view 1 that stays silent; a timeout certificate
-- without a lock; a decision under a correct leader in view 2.
sat trace {
  propose
  expire_timer
  timeout_noqc
  form_own_tc_nolock
  sync_view_nolock
  leader_propose_fresh
  handle_preprepare
  adopt_prepqc
  become_avail_ready
  send_commit
  form_own_commitqc
  assert (∃ i x v l0 l1, ¬ is_byz i ∧ decided i x ∧
    ¬ v = vord.zero ∧ msg_commitqc i v (ent x) ∧
    leader vord.zero l0 ∧ is_byz l0 ∧ leader v l1 ∧ ¬ is_byz l1)
}

-- A held lock forces re-proposal: view 1's leader proposes `e`, a
-- validator forms a prepare certificate on `e`, the view times out with that certificate as
-- its lock, and view 2's correct leader re-proposes `e` although its own
-- input is a different `e'`.
sat trace {
  propose
  propose
  leader_propose_first
  handle_preprepare_first
  adopt_prepqc
  expire_timer
  timeout_qc
  form_own_tc_lock
  sync_view_lock
  leader_repropose
  assert (∃ l v x x' s, ¬ is_byz l ∧ leader v l ∧ ¬ v = vord.zero ∧
    msg_preprepare l v x ∧ input l x' ∧ ¬ ent x = ent x' ∧
    msg_tc_lock s vord.zero vord.zero (ent x))
}

-- Two correct validators decide different representations of one entry
-- vector: one forms the commit certificate and decides its accepted
-- proposal, the other takes the certificate and decides another valid
-- representation of the same entries (`Recover`, the header's "The value
-- type").
sat trace {
  propose
  leader_propose_first
  handle_preprepare_first
  adopt_prepqc
  become_avail_ready
  send_commit
  form_own_commitqc
  propose
  decide
  assert (∃ i j x x', ¬ is_byz i ∧ ¬ is_byz j ∧ decided i x ∧ decided j x' ∧
    ¬ x = x' ∧ ent x = ent x')
}

end Mvba
