import Veil
import Cadence.Tooling

/-! # MvbaNoLock — the lock check removed, mechanically refuted

Companion to [`Mvba.lean`](../Mvba.lean) (read its header first): the same
leader-based MVBA with **one guard deleted** — the `Pre-Prepare` handler's
lock check `lock_available pv e ∨ tc_nolock pv` (the supplement's
`line:mvba:pp-guard`: "`entries(x) = lock(J)` whenever `lock(J) ≠ ⊥`"),
weakened to "a `TC_{s,v-1}` exists". This is the **mutation test** of
`docs/MvbaPlan.md` §4 item 3: the invariants of `Mvba.lean` are proven, but
a proof shows they are *true*, not that they are *load-bearing*. The model
checker below explores a concrete instance of the mutant exhaustively and
**finds a reachable violation of agreement** — two correct validators
deciding different vectors — which is exactly what the lock check exists to
prevent (`lem:lock-persistence`, `thm:agreement`). A green build **requires**
the violation: if a change makes the checker report success, the mutant has
been repaired and the test has lost its meaning.

## What is checked, and why it is a sound refutation

The faithful mutant — `Mvba.lean` with only that guard weakened — is far
too wide for exhaustive search at the smallest interesting instance
(`n = 4`, `f = 1`, two values, two views): the violation needs some 28
transitions (a commit certificate in view 1, a lock-carrying timeout
certificate, a second commit certificate on the other value in view 2, two
decisions), and the Byzantine node's five independent signing actions,
the environment's per-validator availability shares and the three honest
validators' interleavings put millions of states below that depth (the
interpreted checker had not finished depth 6 after half an hour). So this
file checks a **restriction** of the mutant, built so that every one of its
runs is a run of the mutant — its reachable states are a *subset* of the
mutant's, and a violation found here is a fortiori a violation of the
mutant, hence of `Mvba.lean` with the lock check deleted. The restrictions:

1. **Bulk steps that are sequences of the mutant's steps.** `propose_all e`
   is four `propose` steps (every validator inputs the same vector);
   `become_avail_ready_all e` is four `become_avail_ready` steps;
   `byz_sign r v e` is `byz_preprepare` + `byz_prepare` + `byz_commit` +
   `byz_timeout_noqc` on `(v, e)` in one step. Each intermediate state of
   the expanded sequence is reachable in the mutant, and the guards of the
   constituent steps hold along it (the local relations they read are not
   touched by the earlier steps of the same sequence).
2. **A scheduler and an adversary fixed by the theory.** `participant i`
   (validators 0–2 here) gates every honest per-validator action, so the
   fourth validator never acts; `byz_plan v e` (view `k` ↦ value `k`) gates
   the Byzantine signer. Both only *remove* enabled transitions.
3. **Dropped actions**: `abandon` and `byz_timeout_qc`. Removing actions
   only shrinks the reachable set. (The three honest leader actions are
   kept verbatim; the theory makes the Byzantine node the leader of every
   view, so they are simply never enabled.)

Everything else — the honest protocol steps, the certificate assemblies
with their `2f+1` guards, the view change — is verbatim from `Mvba.lean`
(with the mutation), and the model checks the same three safety properties,
of which `agreement` is the one violated.

The counterexample is the textbook lock-persistence scenario (`n = 4`,
`f = 1`; node 0 Byzantine and the leader of both views): view 1 — the
leader proposes value 0, validators 1 and 2 prepare, a prepare certificate
and their own commits plus the Byzantine commit form a **commit certificate
on value 0**; both time out carrying that certificate, and with the
Byzantine lock-free timeout a **timeout certificate whose lock is value 0**
forms; both sync into view 2. View 2 — the Byzantine leader proposes
**value 1**; without the lock check both validators accept it, prepare,
adopt the new certificate and commit, and a **commit certificate on value 1**
forms. Validator 1 decides value 0 from the first certificate, validator 2
value 1 from the second. In `Mvba.lean` the `handle_preprepare` guard
rejects the view-2 proposal (`lock_available 0 1` is false, `tc_nolock 0` is
false), and `prepqc_blocks_lower_commits` is exactly the invariant that
this run breaks at its view-2 prepare certificate.

The `#guard_msgs` pin below carries the checker's whole message — the theory
it ran with and every state of the trace — because `#guard_msgs` compares
the message verbatim; `sequential := true` is load-bearing for the pin, not
a performance choice (see the comment at the command). -/

veil module MvbaNoLock

type node
type nodeset
type value
type view

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet
instantiate vord : TotalOrderWithMinimum view

immutable relation valid (e : value)
immutable relation leader (v : view) (l : node)
-- The two theory-fixed restrictions (header, item 2).
immutable relation participant (i : node)
immutable relation byz_plan (v : view) (e : value)

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

ghost relation in_view (i : node) (v : view) :=
  entered i v ∧ ∀ V, entered i V → vord.le V v

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

/- `propose` for every validator at once, on one vector — four `propose`
steps of the mutant (header, item 1). -/
action propose_all (e : value) {
  require ∀ I E, ¬ input I E
  require ∀ I, ¬ abandoned I
  input I e := true
  entered I vord.zero := true
}

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

action leader_repropose (l : node) (pv : view) (v : view) (w : view) (e : value) {
  require ¬ is_byz l
  require ∃ E, input l E
  require ¬ abandoned l
  require vord.next pv v
  require leader v l
  require in_view l v
  require tc_lock pv w e
  require ¬ proposed_in l v
  proposed_in l v := true
  msg_preprepare l v e := true
}

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

action handle_preprepare_first (i : node) (l : node) (e : value) {
  require ¬ is_byz i
  require participant i
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

/- **The mutation.** `Mvba.lean` requires `lock_available pv e ∨ tc_nolock
pv` here: the justification's lock is `⊥` or the proposed vector. Only the
existence of a `TC_{s,v-1}` is checked — the lock is ignored. -/
action handle_preprepare (i : node) (l : node) (pv : view) (v : view) (e : value) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require in_view i v
  require vord.next pv v
  require leader v l
  require msg_preprepare l v e
  require valid e
  require msg_tc pv
  require ∀ W, voted i W → vord.lt W v
  accepted i v e := true
  voted i v := true
  msg_prepare i v e := true
}

action form_prepqc (v : view) (e : value) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_prepare r v e
  msg_prepqc v e := true
}

action adopt_prepqc (i : node) (v : view) (e : value) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require in_view i v
  require msg_prepqc v e
  require accepted i v e
  require ∀ W E, local_prepqc i W E → vord.lt W v
  require ¬ timed_out i v
  local_prepqc i v e := true
}

/- The environment supplies every validator's shares for `e` at once — four
`become_avail_ready` steps of the mutant (header, item 1). -/
action become_avail_ready_all (e : value) {
  avail_ready I e := true
}

action send_commit (i : node) (v : view) (e : value) {
  require ¬ is_byz i
  require participant i
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

action form_commitqc (v : view) (e : value) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit r v e
  msg_commitqc v e := true
}

action decide (i : node) (v : view) (e : value) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require msg_commitqc v e
  require ∀ E, ¬ decided i E
  decided i e := true
}

action timeout_qc (i : node) (v : view) (w : view) (e : value) {
  require ¬ is_byz i
  require participant i
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

action timeout_noqc (i : node) (v : view) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require in_view i v
  require ¬ timed_out i v
  require ∀ W E, ¬ local_prepqc i W E
  timed_out i v := true
  voted i v := true
  msg_timeout_noqc i v := true
}

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

action form_tc_nolock (v : view) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_timeout_noqc r v
  msg_tc v := true
  tc_nolock v := true
}

action sync_view (i : node) (pv : view) (v : view) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require vord.next pv v
  require msg_tc pv
  require ∀ V, entered i V → vord.le V pv
  entered i v := true
}

action sync_view_adopt (i : node) (pv : view) (v : view) (w : view) (e : value) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require vord.next pv v
  require tc_lock pv w e
  require ∀ V, entered i V → vord.le V pv
  require ∀ W E, local_prepqc i W E → vord.lt W w
  local_prepqc i w e := true
  entered i v := true
}

/- The adversary, scripted (header, items 1 and 2): a Byzantine node signs a
`Pre-Prepare`, a `Prepare` and a `Commit` on `(v, e)` and a lock-free
`Timeout` for `v` in one step — `byz_preprepare`, `byz_prepare`,
`byz_commit`, `byz_timeout_noqc` of the mutant — on the vector its plan
names for the view. -/
action byz_sign (r : node) (v : view) (e : value) {
  require is_byz r
  require byz_plan v e
  msg_preprepare r v e := true
  msg_prepare r v e := true
  msg_commit r v e := true
  msg_timeout_noqc r v := true
}

/-! ## The refuted properties — the three of `mod:mvba`, as in `Mvba.lean` -/

safety [agreement]
  ∀ (I J : node) (E E' : value),
    ¬ is_byz I → ¬ is_byz J → decided I E → decided J E' → E = E'

safety [integrity]
  ∀ (I : node) (E E' : value),
    ¬ is_byz I → decided I E → decided I E' → E = E'

safety [external_validity]
  ∀ (I : node) (E : value), ¬ is_byz I → decided I E → valid E

set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192

#gen_spec

/-! ## The mechanical refutation

Exhaustive exploration at `n = 4`, `f = 1` (node 0 Byzantine — the default
`ByzNodeSet` instance for `Fin (3 * f + 1)` makes the first `f` nodes
Byzantine — and, by the theory below, the leader of every view), two
values, two views; the theory is the one the checker is given (it
enumerates no others), and it satisfies `leader_functional`. Expected
outcome: **violation** of `agreement`, with the trace described in the
header. The same run is impossible in `Mvba.lean`: its `handle_preprepare`
rejects the view-2 proposal against the lock, and `Mvba/Certify.lean`
proves agreement at every reachable state. -/

/--
error: ❌ Violation: safety_failure (violates: agreement)
  Theory:
    byz_plan = [[0, 0], [1, 1]]
    leader = [[0, 0], [1, 0]]
    participant = [0, 1, 2]
    valid = [0, 1]
  State 0 (via init):
    abandoned = []
    accepted = []
    avail_ready = []
    commit_sent = []
    decided = []
    entered = []
    input = []
    local_prepqc = []
    msg_commit = []
    msg_commitqc = []
    msg_prepare = []
    msg_prepqc = []
    msg_preprepare = []
    msg_tc = []
    msg_timeout_noqc = []
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = []
  State 1 (via propose_all(e=0)):
    abandoned = []
    accepted = []
    avail_ready = []
    commit_sent = []
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = []
    msg_commit = []
    msg_commitqc = []
    msg_prepare = []
    msg_prepqc = []
    msg_preprepare = []
    msg_tc = []
    msg_timeout_noqc = []
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = []
  State 2 (via become_avail_ready_all(e=0)):
    abandoned = []
    accepted = []
    avail_ready = [[0, 0], [1, 0], [2, 0], [3, 0]]
    commit_sent = []
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = []
    msg_commit = []
    msg_commitqc = []
    msg_prepare = []
    msg_prepqc = []
    msg_preprepare = []
    msg_tc = []
    msg_timeout_noqc = []
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = []
  State 3 (via become_avail_ready_all(e=1)):
    abandoned = []
    accepted = []
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = []
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = []
    msg_commit = []
    msg_commitqc = []
    msg_prepare = []
    msg_prepqc = []
    msg_preprepare = []
    msg_tc = []
    msg_timeout_noqc = []
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = []
  State 4 (via byz_sign(e=0, r=0, v=0)):
    abandoned = []
    accepted = []
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = []
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = []
    msg_commit = [[0, [0, 0]]]
    msg_commitqc = []
    msg_prepare = [[0, [0, 0]]]
    msg_prepqc = []
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = []
  State 5 (via handle_preprepare_first(e=0, i=1, l=0)):
    abandoned = []
    accepted = [[1, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = []
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = []
    msg_commit = [[0, [0, 0]]]
    msg_commitqc = []
    msg_prepare = [[0, [0, 0]], [1, [0, 0]]]
    msg_prepqc = []
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0]]
  State 6 (via handle_preprepare_first(e=0, i=2, l=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = []
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = []
    msg_commit = [[0, [0, 0]]]
    msg_commitqc = []
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = []
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 7 (via form_prepqc(e=0, q=[0, 1, 2], v=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = []
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = []
    msg_commit = [[0, [0, 0]]]
    msg_commitqc = []
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 8 (via adopt_prepqc(e=0, i=1, v=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = []
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]]]
    msg_commit = [[0, [0, 0]]]
    msg_commitqc = []
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 9 (via adopt_prepqc(e=0, i=2, v=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = []
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]]]
    msg_commitqc = []
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 10 (via send_commit(e=0, i=1, v=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0]]
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [1, [0, 0]]]
    msg_commitqc = []
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 11 (via send_commit(e=0, i=2, v=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = []
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 12 (via form_commitqc(e=0, q=[0, 1, 2], v=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = []
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 13 (via decide(e=0, i=1, v=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = []
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 14 (via timeout_qc(e=0, i=1, v=0, w=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = [[1, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = [[1, 0]]
    voted = [[1, 0], [2, 0]]
  State 15 (via timeout_qc(e=0, i=2, v=0, w=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = []
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = []
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 16 (via form_tc_lock(e=0, q=[0, 1, 2], r0=1, v=0, w=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 17 (via sync_view(i=1, pv=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 18 (via sync_view(i=2, pv=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 19 (via byz_sign(e=1, r=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 20 (via handle_preprepare(e=1, i=1, l=0, pv=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0]]
  State 21 (via handle_preprepare(e=1, i=2, l=0, pv=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_prepqc = [[0, 0]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 22 (via form_prepqc(e=1, q=[0, 1, 2], v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_prepqc = [[0, 0], [1, 1]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 23 (via adopt_prepqc(e=1, i=1, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_prepqc = [[0, 0], [1, 1]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 24 (via adopt_prepqc(e=1, i=2, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_prepqc = [[0, 0], [1, 1]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 25 (via send_commit(e=1, i=1, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [1, 1], [2, 0]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_prepqc = [[0, 0], [1, 1]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 26 (via send_commit(e=1, i=2, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [1, 1], [2, 0], [2, 1]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_commitqc = [[0, 0]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_prepqc = [[0, 0], [1, 1]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 27 (via form_commitqc(e=1, q=[0, 1, 2], v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [1, 1], [2, 0], [2, 1]]
    decided = [[1, 0]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_commitqc = [[0, 0], [1, 1]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_prepqc = [[0, 0], [1, 1]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 28 (via decide(e=1, i=2, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [1, 1], [2, 0], [2, 1]]
    decided = [[1, 0], [2, 1]]
    entered = [[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0]]
    input = [[0, 0], [1, 0], [2, 0], [3, 0]]
    local_prepqc = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_commit = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_commitqc = [[0, 0], [1, 1]]
    msg_prepare = [[0, [0, 0]], [0, [1, 1]], [1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    msg_prepqc = [[0, 0], [1, 1]]
    msg_preprepare = [[0, [0, 0]], [0, [1, 1]]]
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0], [0, 1]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
-/
#guard_msgs in
/- `sequential := true` is load-bearing for the pin above, not a performance
choice. By default `#model_check` splits the BFS frontier into `numSubTasks`
parallel sub-tasks and that count defaults to the machine's **core count**, so
*which* of the violating states is reported first depends on the hardware
(`FallbackReceipt/PreFix.lean` records the measurement). The claim being
pinned is "a reachable state violates `agreement`" — the witness is
evidence, not the claim — but `#guard_msgs` compares the whole message, so
the search must be deterministic. -/
#model_check interpreted
  { node := Fin (3 * 1 + 1), nodeset := ByzNSet (3 * 1 + 1),
    value := Fin 2, view := Fin 2 }
  { valid := fun _ => true, leader := fun _ l => l == 0,
    participant := fun i => i.val != 3, byz_plan := fun v e => v.val == e.val }
  (sequential := true)

end MvbaNoLock
