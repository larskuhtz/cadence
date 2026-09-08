import Veil
import Cadence.Tooling

/-! # Mvba — the leader-based MVBA instantiation

*This is a **model file** of the verified-module file family
(`docs/Architecture.md` §6): it elaborates the transition system and
persists the VC registry, but runs **no invariant sweep** — the proofs
live in the per-action files under [`Mvba/Proofs/`](./Mvba/Proofs),
composed into the reachability certificate by
[`Mvba/Certify.lean`](./Mvba/Certify.lean).*

## What this models, and where its specification lives

`mod:mvba` in the published paper (`arXiv:2607.02275v2`) is an interface and
five properties with no algorithm. The algorithm modelled here is the
leader-based protocol of the paper repository's **internal supplement** —
`supplementary-internal.tex`, `sec:mvba-instantiation`, with the data types
in `subsec:mvba-datatypes`, the protocol in `subsec:mvba-protocol`
(algorithm blocks `alg:mvba`, `alg:mvba-cont`, `alg:mvba-cont2`) and its
correctness argument in `subsec:mvba-correctness`. **The supplement is not
yet part of the published paper.** It has neither tags nor versions, so this
model pins the **paper-repository commit it was read against:
`026dc8b` (2026-09-03)**; a later change to `alg_mvba.tex` or to
`subsec:mvba-correctness` is the trigger to re-read the model against the
new commit and move this pin (`docs/MvbaPlan.md` §0). What an auditor can
check without the supplement is the contract the model is proven against —
`safety [agreement]`, `[integrity]`, `[external_validity]` are the three
safety properties of `mod:mvba`; what needs the supplement is the model's
fidelity to the algorithm.

## The value type

The class is instantiated at the **entry vector** (`docs/MvbaPlan.md`
§1.2): here `value` is an opaque sort standing for `node → Option
merkle_root`, and `valid` is an **uninterpreted immutable relation** — the
algorithm only checks certificates, it does not interpret them, so the
external validity predicate is a parameter. Because the value *is* the
entry vector, the supplement's `Recover(e)` is the identity: the leader
re-proposes a lock's entries directly (`lem:reproposal`) and `decide`
decides the certified vector (`line:mvba:qc-decide`, `line:mvba:td-decide`).

## Views

One MVBA instance serves one Chorus slot and runs as many **views** as it
needs: `Leader(slot, v)` rotates, a view that does not decide is closed by
a timeout certificate `TC_{s,v}`, and the next leader re-proposes the lock
that certificate carries (`alg:mvba` local state, `line:mvba:ht-advance`,
`line:mvba:sv`). `view` is a `TotalOrderWithMinimum` as the Conductor's
slots and windows are: `vord.zero` is view 1, `vord.next v v'` is
`v' = v + 1`, and no arithmetic reaches the solver. The leader function is
the immutable relation `leader v l`, functional by assumption.

## State

**Network relations** (`msg_*`, monotone, consulted in **positive position
only** — `docs/ChorusDesign.md` §3.1.1 governs them; this module adds no
exception category):

| relation | supplement message |
|---|---|
| `msg_preprepare l v e` | `⟨Pre-Prepare, s, v, x, J, σ_l⟩`; the justification `J` is not carried — the receiver checks the network for a `TC_{s,v-1}` and its lock (`tc_lock` / `tc_nolock` below) |
| `msg_prepare r v e`, `msg_commit r v e` | `⟨Prepare, s, v, e, σ⟩`, `⟨Commit, s, v, e, σ⟩` |
| `msg_timeout_qc r v w e`, `msg_timeout_noqc r v` | `⟨Timeout, s, v, PrepQC_i, σ⟩` carrying a prepare certificate of view `w` on `e`, or `⊥` |
| `msg_prepqc v e`, `msg_commitqc v e` | `prepareQC_{s,v}` on `e`, `CommitQC` of view `v` on `e` |
| `msg_tc v`, `tc_lock v w e`, `tc_nolock v` | a `TC_{s,v}` exists; a `TC_{s,v}` exists whose `highPrepQC` is the certificate `(w, e)`; a `TC_{s,v}` exists whose `highPrepQC` is `⊥` (`line:mvba:derived`) |

All five certificates are **materialised by explicit assembly actions**
(`form_prepqc`, `form_commitqc`, `form_tc_lock`, `form_tc_nolock`) whose
guards are the signature quorums — Chorus's `broadcast_commitqc_*`
pattern, which keeps `∃`-quorum ghosts out of every consumer's guard. A
view can have several timeout certificates (different `2f+1` subsets) with
different locks; `tc_lock` / `tc_nolock` record each one that was formed,
and a proposal is checked against *some* certificate of the previous view,
which is what a leader may attach.

**Validator-local state**, free of the network contract, kept **monotone
and view-indexed** (`docs/MvbaPlan.md` §3 says why: mutable current-view
fields would pull strong fairness into the liveness argument): `input i e`
(the `propose` argument); `entered i v` (the current view is the maximum
entered, `in_view`); `voted i v` (`lastVotedView_i` was raised to `v`, so
"`v_msg > lastVotedView_i`" is `∀ w, voted i w → w < v_msg`);
`accepted i v e` (`x_v`); `local_prepqc i w e` (`PrepQC_i` has been the
certificate `(w, e)`; the current one is the highest held); `timed_out i v`
(`timedOut_i`); `commit_sent i v` (`commitSent_i`); `proposed_in l v` (the
leader's `Pre-Prepare` in `v` was sent); `decided i e`; `abandoned i`; and
the environment relation `avail_ready i e` (`AvailReady_i`).

## Abstractions

* **Messages monotone, local state free.** The guards `¬ timed_out i v`,
  `¬ commit_sent i v`, `∀ w, voted i w → w < v`, `∀ V, entered i V → V ≤ v`
  and `∀ W E, local_prepqc i W E → W < w` read *local* relations
  negatively; no exception category is involved.
* **`SyncView` is its own action.** The supplement runs `SyncView(J)`
  inside the `Pre-Prepare` handler before the checks; here `sync_view`
  advances the view on any timeout certificate at or above the current
  view and the handler requires the message's view to be the current one
  — the same reachable states in two steps. Adopting the certificate's
  lock (`line:mvba:sv-adopt`) is the variant `sync_view_adopt`; the plain
  `sync_view` does not adopt, which only adds behaviours (the safety
  argument never relies on adoption).
* **A timeout carrying a certificate of view above its own** contributes
  to no `highPrepQC` (`line:mvba:derived`), so for every receiver it is a
  timeout carrying `⊥`. The model lets a Byzantine sender send the `⊥`
  form instead (`byz_timeout_qc` requires `w ≤ v`), and the assembly
  guards need no filter.
* **`timeout` covers the timer and the `f+1` echo rule**
  (`line:mvba:timeout-send`, `line:mvba:ht-send`): both send the same
  message under the same local update; the rule that *enables* the second
  matters only for liveness and is left to the liveness step.
* **`AvailReady` is an environment relation**: `become_avail_ready` is an
  unguarded environment action, `send_commit` reads it positively.
  Safety-neutral, and the hook for the supplement's `Δ_sync` assumption.
* **`abandon` is modelled** as a monotone flag every honest send requires
  unset, and `propose` is the `input` record; the paper's self-`abandon()`
  after a decision is the *caller's* input in the contract (`MVBA.abandon`),
  so `decide` records the decision and leaves `abandoned` to `abandon`.
* **Integrity by construction**: `decide` requires `∀ E, ¬ decided i E`.
* **Not modelled**: persistence and crash recovery (`line:mvba:reload`,
  `cor:mvba-recovery-termination`), the `Pool` cache, the availability
  shares. The supplement's `decide(x, CommitQC)` returns the certificate
  too; the public `mod:mvba` has `decide(B)`, so the certificate is not an
  observable here.

## The safety argument, and where it departs from the supplement's

The supplement proves `thm:agreement` from `lem:lock-persistence`, whose
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
`blocked`). Its inductive step at `form_prepqc` is the supplement's
argument for one view transition (the honest preparer's justification, the
timeout quorum's honest intersection with the given supermajority, and the
invariant itself at the lock's certificate), and `lem:lock-persistence`
(i)/(ii), `lem:cert-uniqueness` across views (`commitqc_agree`) and
`thm:agreement` follow from it by instantiation. `docs/MvbaPlan.md` §2.6
records the correction.

## Byzantine behaviour

A Byzantine node may sign any `Pre-Prepare`, `Prepare`, `Commit` or
`Timeout` (`byz_*`); a Byzantine timeout can carry only a certificate that
exists. It cannot forge a certificate: the four certificate relations are
assembled only from `2f+1` signatures (`rem:signature-separation`). Honest
receivers check that a `Pre-Prepare` comes from `leader v`, so a Byzantine
leader may equivocate and a Byzantine non-leader's proposals are inert. -/

veil module Mvba

type node
type nodeset
-- The entry vector `node → Option merkle_root` (`docs/MvbaPlan.md` §1.2),
-- opaque here.
type value
type view

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet
instantiate vord : TotalOrderWithMinimum view

-- The external validity predicate `Valid` (`mod:mvba`; the supplement's
-- "`x` is a valid meta-block", `subsec:mvba-datatypes`) — uninterpreted.
immutable relation valid (e : value)

-- `Leader(slot, v)`: a deterministic public function (functional by the
-- assumption below).
immutable relation leader (v : view) (l : node)

/-! ## Network — signed messages and certificates -/

relation msg_preprepare (l : node) (v : view) (e : value)
relation msg_prepare (r : node) (v : view) (e : value)
relation msg_commit (r : node) (v : view) (e : value)
relation msg_timeout_qc (r : node) (v : view) (w : view) (e : value)
relation msg_timeout_noqc (r : node) (v : view)
relation msg_prepqc (v : view) (e : value)
relation msg_commitqc (v : view) (e : value)
relation msg_tc (v : view)
relation tc_lock (v : view) (w : view) (e : value)
relation tc_nolock (v : view)

/-! ## Validator-local state -/

relation input (i : node) (e : value)
relation entered (i : node) (v : view)
relation voted (i : node) (v : view)
relation accepted (i : node) (v : view) (e : value)
relation local_prepqc (i : node) (w : view) (e : value)
relation timed_out (i : node) (v : view)
relation commit_sent (i : node) (v : view)
relation proposed_in (l : node) (v : view)
relation decided (i : node) (e : value)
relation abandoned (i : node)
relation avail_ready (i : node) (e : value)

#gen_state

assumption [leader_functional]
  ∀ (V : view) (L L' : node), leader V L → leader V L' → L = L'

/-! ## Derived state (ghosts) -/

-- The current view is the maximum entered view (a negative observation of
-- own local state only).
ghost relation in_view (i : node) (v : view) :=
  entered i v ∧ ∀ V, entered i V → vord.le V v

-- Some `TC_{s,pv}` has `lock = e`.
ghost relation lock_available (pv : view) (e : value) :=
  ∃ w, tc_lock pv w e

-- `n` sent a timeout at or after view `v` carrying no lock of view `≥ v`:
-- it left view `v` without a view-`v` lock and can no longer commit in it
-- (`lem:timeout-closes-view`, `lem:commit-provenance`).
ghost relation left_view (n : node) (v : view) :=
  ∃ v', vord.le v v' ∧
    (msg_timeout_noqc n v' ∨ ∃ w e, msg_timeout_qc n v' w e ∧ vord.lt w v)

-- `n` cannot commit `e` in view `v`: it left the view without a view-`v`
-- lock, or it holds a view-`v` lock on another value.
ghost relation blocked (n : node) (v : view) (e : value) :=
  left_view n v ∨ ∃ e', ¬ e' = e ∧ local_prepqc n v e'

/-! ## Initial state -/

/- Action bodies elaborate one nested `openStateAround` per statement, so
the depth scales with the longest body; the 21-statement `after_init`
exceeds the default (the `Chorus.lean` rule in `CLAUDE.md`). -/
set_option maxRecDepth 8192

after_init {
  msg_preprepare L V E := false
  msg_prepare R V E := false
  msg_commit R V E := false
  msg_timeout_qc R V U E := false
  msg_timeout_noqc R V := false
  msg_prepqc V E := false
  msg_commitqc V E := false
  msg_tc V := false
  tc_lock V U E := false
  tc_nolock V := false
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
}

/-! ## Inputs (`mod:mvba`) -/

/- `propose(B_i)` — sets the input, enters view 1 and begins participation.
Once per validator; `Valid B_i` is the caller's obligation. -/
action propose (i : node) (e : value) {
  require ∀ E, ¬ input i E
  require ¬ abandoned i
  input i e := true
  entered i vord.zero := true
}

/- `abandon()` — halts this validator's MVBA sending: every honest send
below requires `¬ abandoned i`. -/
action abandon (i : node) {
  abandoned i := true
}

/-! ## The leader (`alg:mvba`, "upon entering view v") -/

/- View 1: `x ← B_i`, `J ← ⊥`. -/
action leader_propose_first (l : node) (e : value) {
  require ¬ is_byz l
  require ¬ abandoned l
  require leader vord.zero l
  require in_view l vord.zero
  require input l e
  require ¬ proposed_in l vord.zero
  proposed_in l vord.zero := true
  msg_preprepare l vord.zero e := true
}

/- View `v > 1` with `lock(J) ≠ ⊥`: `x ← Recover(lock(J))`, the lock's
entries themselves (`lem:reproposal`). -/
action leader_repropose (l : node) (pv : view) (v : view) (w : view) (e : value) {
  require ¬ is_byz l
  require ¬ abandoned l
  require vord.next pv v
  require leader v l
  require in_view l v
  require tc_lock pv w e
  require ¬ proposed_in l v
  proposed_in l v := true
  msg_preprepare l v e := true
}

/- View `v > 1` with `lock(J) = ⊥`: `x ← B_i`. -/
action leader_propose_fresh (l : node) (pv : view) (v : view) (e : value) {
  require ¬ is_byz l
  require ¬ abandoned l
  require vord.next pv v
  require leader v l
  require in_view l v
  require tc_nolock pv
  require input l e
  require ¬ proposed_in l v
  proposed_in l v := true
  msg_preprepare l v e := true
}

/-! ## The `Pre-Prepare` handler (`line:mvba:pp-guard`) and `HandleProposal` -/

/- View 1: current view, sender is the leader, `x` valid, `J = ⊥`,
`1 > lastVotedView_i`. Then `HandleProposal` (`line:mvba:hp-record`,
`line:mvba:hp-prepare`): record `x_v`, raise `lastVotedView_i`, send the
`Prepare` on the entry vector. -/
action handle_preprepare_first (i : node) (l : node) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require in_view i vord.zero
  require leader vord.zero l
  require msg_preprepare l vord.zero e
  require valid e
  require ∀ W, voted i W → vord.lt W vord.zero
  accepted i vord.zero e := true
  voted i vord.zero := true
  msg_prepare i vord.zero e := true
}

/- View `v > 1`: additionally `J` is a `TC_{s,v-1}` and `entries(x) =
lock(J)` whenever `lock(J) ≠ ⊥` — against some timeout certificate of the
previous view (see the header on `tc_lock`). -/
action handle_preprepare (i : node) (l : node) (pv : view) (v : view) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require in_view i v
  require vord.next pv v
  require leader v l
  require msg_preprepare l v e
  require valid e
  require lock_available pv e ∨ tc_nolock pv
  require ∀ W, voted i W → vord.lt W v
  accepted i v e := true
  voted i v := true
  msg_prepare i v e := true
}

/-! ## Prepare certificates and the commit -/

/- Assembly: `2f+1` `Prepare` signatures on `e` in view `v` form
`prepareQC_{s,v}` on `e`. -/
action form_prepqc (v : view) (e : value) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_prepare r v e
  msg_prepqc v e := true
}

/- `TryFormPrepQC`'s local half (`line:mvba:tfp-guard`,
`line:mvba:tfp-store`): in the current view, on the vector it prepared,
if the held certificate is of a lower view, and not after timing out. -/
action adopt_prepqc (i : node) (v : view) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require in_view i v
  require msg_prepqc v e
  require accepted i v e
  require ∀ W E, local_prepqc i W E → vord.lt W v
  require ¬ timed_out i v
  local_prepqc i v e := true
}

/- The environment supplies `i`'s availability shares for `e`
(`AvailReady_i`; `lem:avail-progress` bounds when). Unguarded. -/
action become_avail_ready (i : node) (e : value) {
  avail_ready i e := true
}

/- `TrySendCommit` (`line:mvba:commit-send`): `entries(x_v) = e`, `PrepQC_i`
is of the current view and on `e`, `¬ timedOut_i`, `¬ commitSent_i`,
`AvailReady_i(x_v)`. -/
action send_commit (i : node) (v : view) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require in_view i v
  require accepted i v e
  require local_prepqc i v e
  require ¬ timed_out i v
  require ¬ commit_sent i v
  require avail_ready i e
  commit_sent i v := true
  msg_commit i v e := true
}

/- Assembly: `2f+1` `Commit` signatures on `e` in view `v` form the
`CommitQC` of view `v` on `e`. -/
action form_commitqc (v : view) (e : value) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit r v e
  msg_commitqc v e := true
}

/- `decide(x, CommitQC)`: `TryFormCommitQC`, the transferred-certificate
handler (`line:mvba:qc-decide`) and `TryDecide` (`line:mvba:td-decide`)
collapse into one action — `Recover(e)` is the identity. A certificate of
any view is accepted. Once (`DecidedQC_i = ⊥`). -/
action decide (i : node) (v : view) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require msg_commitqc v e
  require ∀ E, ¬ decided i E
  decided i e := true
}

/-! ## Timeouts, timeout certificates and view change -/

/- The timer fires in the current view (`line:mvba:timeout-send`; also
the `f+1` echo, `line:mvba:ht-send`): `timedOut_i ← true`, raise
`lastVotedView_i`, send `⟨Timeout, s, v, PrepQC_i, σ_i⟩` with the highest
held certificate … -/
action timeout_qc (i : node) (v : view) (w : view) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require in_view i v
  require ¬ timed_out i v
  require local_prepqc i w e
  require ∀ W E, local_prepqc i W E → vord.le W w
  timed_out i v := true
  voted i v := true
  msg_timeout_qc i v w e := true
}

/- … or with `PrepQC_i = ⊥`. -/
action timeout_noqc (i : node) (v : view) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require in_view i v
  require ¬ timed_out i v
  require ∀ W E, ¬ local_prepqc i W E
  timed_out i v := true
  voted i v := true
  msg_timeout_noqc i v := true
}

/- Assembly (`line:mvba:ht-advance`, `line:mvba:derived`): `2f+1` timeouts
of view `v` form `TC_{s,v}`; its `highPrepQC` is the certificate `(w, e)`
carried by member `r0` — a valid certificate of view `w ≤ v` — and every
member carries `⊥` or a certificate of view `≤ w`. -/
action form_tc_lock (v : view) (q : nodeset) (r0 : node) (w : view) (e : value) {
  require nset.supermajority q
  require nset.member r0 q
  require msg_timeout_qc r0 v w e
  require msg_prepqc w e
  require vord.le w v
  require ∀ r, nset.member r q →
    msg_timeout_noqc r v ∨ ∃ W E, msg_timeout_qc r v W E ∧ vord.le W w
  msg_tc v := true
  tc_lock v w e := true
}

/- Assembly, `highPrepQC = ⊥`: every member carries `⊥`. -/
action form_tc_nolock (v : view) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_timeout_noqc r v
  msg_tc v := true
  tc_nolock v := true
}

/- `SyncView(TC_{s,pv})` (`line:mvba:sv`, `line:mvba:sv-advance`) on a
certificate at or above the current view: enter `pv + 1`. -/
action sync_view (i : node) (pv : view) (v : view) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require vord.next pv v
  require msg_tc pv
  require ∀ V, entered i V → vord.le V pv
  entered i v := true
}

/- `SyncView` with adoption (`line:mvba:sv-adopt`): the certificate's lock
`(w, e)` is of a higher view than every held certificate, so `PrepQC_i`
adopts it while `i` enters `pv + 1`. -/
action sync_view_adopt (i : node) (pv : view) (v : view) (w : view) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require vord.next pv v
  require tc_lock pv w e
  require ∀ V, entered i V → vord.le V pv
  require ∀ W E, local_prepqc i W E → vord.lt W w
  local_prepqc i w e := true
  entered i v := true
}

/-! ## Byzantine behaviour — arbitrary signatures, no forged certificates -/

action byz_preprepare (l : node) (v : view) (e : value) {
  require is_byz l
  msg_preprepare l v e := true
}

action byz_prepare (r : node) (v : view) (e : value) {
  require is_byz r
  msg_prepare r v e := true
}

action byz_commit (r : node) (v : view) (e : value) {
  require is_byz r
  msg_commit r v e := true
}

/- A Byzantine timeout carries `⊥` or a certificate that exists, of view
at most its own (see the header: a higher one counts as `⊥`). -/
action byz_timeout_qc (r : node) (v : view) (w : view) (e : value) {
  require is_byz r
  require msg_prepqc w e
  require vord.le w v
  msg_timeout_qc r v w e := true
}

action byz_timeout_noqc (r : node) (v : view) {
  require is_byz r
  msg_timeout_noqc r v := true
}

/-! ## Safety — the three safety properties of `mod:mvba`

Stated in the class's vocabulary (`MVBASafety` in `Cadence/Interfaces.lean`)
so that the provider step can discharge the fields by the `reachable_*`
projections of `Mvba/Certify.lean`. -/

/- `thm:agreement` (entries level): correct validators that decide, decide
the same entry vector. -/
safety [agreement]
  ∀ (I J : node) (E E' : value),
    ¬ is_byz I → ¬ is_byz J → decided I E → decided J E' → E = E'

/- Integrity: a correct validator decides at most one value. -/
safety [integrity]
  ∀ (I : node) (E E' : value),
    ¬ is_byz I → decided I E → decided I E' → E = E'

/- `lem:external-validity`: a decided value is valid. -/
safety [external_validity]
  ∀ (I : node) (E : value), ¬ is_byz I → decided I E → valid E

/-! ## Invariants — the supplement's lemmas

`docs/MvbaPlan.md` §2.6 has the map from the supplement's lemmas to the
rows below; the header explains the one departure (`lem:lock-persistence`
is a corollary, `prepqc_blocks_lower_commits` is the inductive form). -/

/-! ### `lem:vote-uniqueness` — one `Prepare` per view, on the accepted vector -/

/- An honest `Prepare` is on the vector its sender accepted in that view. -/
invariant [honest_prepare_accepted]
  ∀ (R : node) (V : view) (E : value),
    ¬ is_byz R → msg_prepare R V E → accepted R V E

/- Accepting raised `lastVotedView_i` to the view (`line:mvba:hp-record`),
which is what makes the acceptance unique per view. -/
invariant [accepted_implies_voted]
  ∀ (R : node) (V : view) (E : value),
    ¬ is_byz R → accepted R V E → voted R V

invariant [accepted_unique]
  ∀ (R : node) (V : view) (E E' : value),
    ¬ is_byz R → accepted R V E → accepted R V E' → E = E'

/- `lem:external-validity`'s premise: only valid vectors are accepted
(`line:mvba:pp-guard`). -/
invariant [accepted_valid]
  ∀ (R : node) (V : view) (E : value),
    ¬ is_byz R → accepted R V E → valid E

/- The lifted justification check of `line:mvba:pp-guard`: an acceptance
in a view `v > 1` was justified by a `TC_{s,v-1}` whose lock is `⊥` or
the accepted vector. -/
invariant [accepted_justified]
  ∀ (R : node) (V : view) (E : value),
    ¬ is_byz R → accepted R V E → ¬ V = vord.zero →
      ∃ PV, vord.next PV V ∧ (tc_nolock PV ∨ lock_available PV E)

/-! ### `lem:commit-provenance` and `rem:lock-monotonicity` -/

/- An honest `Commit` on `e` in `v` was sent with `entries(x_v) = e` and a
`PrepQC_i` of view `v` on `e`. -/
invariant [honest_commit_accepted]
  ∀ (R : node) (V : view) (E : value),
    ¬ is_byz R → msg_commit R V E → accepted R V E ∧ local_prepqc R V E

/- A held certificate is a network certificate. -/
invariant [local_prepqc_backed]
  ∀ (R : node) (W : view) (E : value),
    ¬ is_byz R → local_prepqc R W E → msg_prepqc W E

/- Certificates are adopted with strictly increasing views
(`line:mvba:tfp-guard`, `line:mvba:sv-adopt`), so one per view. -/
invariant [local_prepqc_unique]
  ∀ (R : node) (W : view) (E E' : value),
    ¬ is_byz R → local_prepqc R W E → local_prepqc R W E' → E = E'

/-! ### Certificate backing (the lifted assembly guards) -/

invariant [prepqc_backed]
  ∀ (V : view) (E : value), msg_prepqc V E →
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_prepare r V E

invariant [commitqc_backed]
  ∀ (V : view) (E : value), msg_commitqc V E →
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_commit r V E

/- Every carried certificate exists (honest senders carry held ones,
Byzantine senders may carry only existing ones). -/
invariant [timeout_qc_backed]
  ∀ (R : node) (V W : view) (E : value),
    msg_timeout_qc R V W E → msg_prepqc W E

invariant [tc_nolock_backed]
  ∀ (V : view), tc_nolock V →
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_timeout_noqc r V

/- A recorded lock is a certificate of view `≤ v` carried by a member of
a `2f+1` timeout quorum none of whose members carries a higher one. -/
invariant [tc_lock_backed]
  ∀ (V W : view) (E : value), tc_lock V W E →
    msg_prepqc W E ∧ vord.le W V ∧
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q →
      msg_timeout_noqc r V ∨ ∃ W' E', msg_timeout_qc r V W' E' ∧ vord.le W' W

/-! ### `lem:cert-uniqueness`, within a view and across views -/

/- All prepare certificates of a view are on one vector: the
two-supermajority intersection through an honest common signer and vote
uniqueness. -/
invariant [prepqc_unique]
  ∀ (V : view) (E E' : value), msg_prepqc V E → msg_prepqc V E' → E = E'

/- A commit certificate's honest signers held a prepare certificate of
the same view on the same vector (`lem:lock-formation`'s content). -/
invariant [commitqc_implies_prepqc]
  ∀ (V : view) (E : value), msg_commitqc V E → msg_prepqc V E

/- `thm:agreement` at the certificate level, across views: from
`prepqc_blocks_lower_commits` and the two-supermajority intersection. -/
invariant [commitqc_agree]
  ∀ (V V' : view) (E E' : value),
    msg_commitqc V E → msg_commitqc V' E' → E = E'

/- A commit certificate is on a valid vector: an honest signer accepted it. -/
invariant [commitqc_valid]
  ∀ (V : view) (E : value), msg_commitqc V E → valid E

/- Lifted `decide` guard: every honest decision is certificate-backed. -/
invariant [decided_backed]
  ∀ (I : node) (E : value),
    ¬ is_byz I → decided I E → ∃ V, msg_commitqc V E

/-! ### `lem:timeout-closes-view` and the timeout's carried lock -/

/- An honest timeout carries a held certificate … -/
invariant [honest_timeout_qc_held]
  ∀ (R : node) (V W : view) (E : value),
    ¬ is_byz R → msg_timeout_qc R V W E → local_prepqc R W E

/- … and records `timedOut_i` in a view the sender had entered. -/
invariant [honest_timeout_qc_timed_out]
  ∀ (R : node) (V W : view) (E : value),
    ¬ is_byz R → msg_timeout_qc R V W E → timed_out R V

invariant [honest_timeout_noqc_timed_out]
  ∀ (R : node) (V : view),
    ¬ is_byz R → msg_timeout_noqc R V → timed_out R V

invariant [timed_out_entered]
  ∀ (R : node) (V : view), ¬ is_byz R → timed_out R V → entered R V

/- `lem:commit-provenance` across views: an honest validator that
committed in `v` sends no later timeout without a lock — its timeouts at
views `≥ v` carry a certificate of view `≥ v` (the `PrepQC_i` it held
when committing never decreases, `rem:lock-monotonicity`). -/
invariant [commit_no_later_noqc_timeout]
  ∀ (R : node) (V V' : view) (E : value),
    ¬ is_byz R → msg_commit R V E → msg_timeout_noqc R V' → vord.lt V' V

invariant [commit_later_timeout_carries_lock]
  ∀ (R : node) (V V' W : view) (E E' : value),
    ¬ is_byz R → msg_commit R V E → msg_timeout_qc R V' W E' →
      vord.le V V' → vord.le V W

/-! ### `lem:lock-persistence`, in inductive form -/

/- Every prepare certificate of view `w` blocks, in every view `v < w` and
for every value `e` other than its own, every supermajority from
committing `e` in `v`: one correct member left `v` without a view-`≥ v`
lock, or holds a view-`v` lock on another value (see the header). -/
invariant [prepqc_blocks_lower_commits]
  ∀ (W V : view) (E' E : value) (Q : nodeset),
    msg_prepqc W E' → vord.lt V W → ¬ E = E' → nset.supermajority Q →
      ∃ n, nset.member n Q ∧ ¬ is_byz n ∧ blocked n V E

/- Proof reconstruction ON (this module only): captured at `#gen_spec`,
so it governs the background `doesNotThrow` dischargers this file still
runs. The invariant proofs live in the proof-file family, which sets the
option itself (read at tactic runtime on the cross-file path). -/
set_option veil.smt.trust false

/- VC registry (`docs/Dependencies.md` §1): `#gen_spec` persists every
VC's statement plus its action/property metadata into the olean. This is
the model file's entire proof interface: the family's
`#prove_action`/`#prove_vc` commands re-create the VCs from these
statements. -/
set_option veil.gen.vcRegistry true

/- Proof cache (`docs/Dependencies.md` §2), for the `doesNotThrow`
dischargers here; the proof files enable it themselves. -/
set_option veil.cache.proofs true

/- The label-enumeration instances the trace queries below need
(`ActionTag_EnumClass`) exceed the default instance-search budgets at this
action count and parameter arity — the Conductor's lesson (`CLAUDE.md`). -/
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192

#gen_spec

/-! ## Non-vacuity witnesses (`docs/MvbaPlan.md` §4 item 1)

`sat` verdicts here are trusted, deliberately: a wrong model can only make
a non-vacuity check vacuous, never a safety claim wrong
(`docs/Architecture.md` §4 item 6). Traces come last in the file and no
`set_option … in` follows a trace block (the parser rule in `CLAUDE.md`). -/

-- A decision in view 1.
sat trace {
  propose
  leader_propose_first
  handle_preprepare_first
  form_prepqc
  adopt_prepqc
  become_avail_ready
  send_commit
  form_commitqc
  decide
  assert (∃ i e, ¬ is_byz i ∧ decided i e ∧ msg_commitqc vord.zero e)
}

-- A Byzantine leader in view 1 that stays silent; a timeout certificate
-- without a lock; a decision under a correct leader in view 2.
sat trace {
  propose
  timeout_noqc
  form_tc_nolock
  sync_view
  leader_propose_fresh
  handle_preprepare
  form_prepqc
  adopt_prepqc
  become_avail_ready
  send_commit
  form_commitqc
  decide
  assert (∃ i e v l0 l1, ¬ is_byz i ∧ decided i e ∧
    ¬ v = vord.zero ∧ msg_commitqc v e ∧
    leader vord.zero l0 ∧ is_byz l0 ∧ leader v l1 ∧ ¬ is_byz l1)
}

-- A held lock forces re-proposal: view 1's leader proposes `e`, a prepare
-- certificate on `e` forms, the view times out with that certificate as
-- its lock, and view 2's correct leader re-proposes `e` although its own
-- input is a different `e'`.
sat trace {
  propose
  propose
  leader_propose_first
  handle_preprepare_first
  form_prepqc
  adopt_prepqc
  timeout_qc
  form_tc_lock
  sync_view
  leader_repropose
  assert (∃ l v e e', ¬ is_byz l ∧ leader v l ∧ ¬ v = vord.zero ∧
    msg_preprepare l v e ∧ input l e' ∧ ¬ e = e' ∧
    tc_lock vord.zero vord.zero e)
}

end Mvba
