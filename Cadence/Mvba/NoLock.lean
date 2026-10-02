import Veil
import Cadence.Tooling

/-! # MvbaNoLock — the lock check removed, mechanically refuted

Companion to [Mvba.lean](../Mvba.lean) (read its header first): the same
leader-based MVBA with **one guard deleted** — the `Pre-Prepare` handler's
lock check `lock_available pv e ∨ tc_nolock pv` (Supplement, Algorithm 1, line 17 (`line:mvba:pp-guard`): "`entries(x) = lock(J)` whenever `lock(J) ≠ ⊥`"),
weakened to "a `TC_{s,v-1}` exists". This is the **mutation test** of
[MvbaPlan.md](../../docs/MvbaPlan.md) §4 item 3: the invariants of
[Mvba.lean](../Mvba.lean) are proven, but
a proof shows they are *true*, not that they are *load-bearing*. The model
checker below explores a concrete instance of the mutant exhaustively and
**finds a reachable violation of agreement** — two correct validators
deciding different vectors — which is exactly what the lock check exists to
prevent (Supplement, Lemma 8 (`lem:lock-persistence`), Supplement, Theorem 1 (`thm:agreement`)). A green build **requires**
the violation: if a change makes the checker report success, the mutant has
been repaired and the test has lost its meaning.

## What is checked, and why it is a sound refutation

The faithful mutant — [Mvba.lean](../Mvba.lean) with only that guard weakened — is far
too wide for exhaustive search at the smallest interesting instance
(`n = 4`, `f = 1`, two values, two views): the violation needs some 25
transitions (a commit certificate in view 1, a lock-carrying timeout
certificate, a second commit certificate on the other value in view 2, two
decisions), and the Byzantine node's five independent signing actions,
the environment's per-validator availability shares and the three honest
validators' interleavings put millions of states below that depth (the
interpreted checker had not finished depth 6 after half an hour). So this
file checks a **restriction** of the mutant, built so that every one of its
runs is a run of the mutant — its reachable states are a *subset* of the
mutant's, and a violation found here is a fortiori a violation of the
mutant, hence of [Mvba.lean](../Mvba.lean) with the lock check deleted. The restrictions:

1. **Bulk steps that are sequences of the mutant's steps.** `propose_all e`
   is four `propose` steps (every validator inputs the same vector);
   `become_avail_ready_all e` is four `become_avail_ready` steps;
   `byz_sign r v e` is `byz_preprepare` + `byz_prepare` + `byz_commit` +
   `byz_timeout_noqc` on `(v, e)` in one step. Each intermediate state of
   the expanded sequence is reachable in the mutant, and the guards of the
   constituent steps hold along it (the local relations they read are not
   touched by the earlier steps of the same sequence). The view timer is
   folded the same way: this model has no `timer_expired` relation and no
   `expire_timer` action, so each of its timeout steps is the mutant's
   `expire_timer` followed by its timeout — `expire_timer` requires only
   that the view was entered, which the timeout's `in_view` guard implies.
2. **A scheduler and an adversary fixed by the theory.** `participant i`
   (validators 0–2 here) gates every honest per-validator action, so the
   fourth validator never acts; `byz_plan v e` (view `k` ↦ value `k`) gates
   the Byzantine signer. Both only *remove* enabled transitions.
3. **Dropped actions**: `abandon`, `byz_timeout_qc`, the anonymous
   assemblies `form_prepqc`, `form_tc_lock` and `form_tc_nolock` — the
   correct validators form those certificates themselves (`adopt_prepqc`,
   `form_own_tc_lock`, the supplement's rules) — and, since R6, three
   honest steps the scenario does not take: `timeout_noqc`,
   `form_own_tc_nolock` and `sync_view_adopt`.
   Removing actions only shrinks the reachable set. The anonymous
   `form_commitqc` stays: in the scenario below the view-1 commit
   certificate is aggregated without anyone deciding on it, which is the
   adversary's move (a correct validator that forms a commit certificate
   decides on it and halts). (The three honest leader actions are
   kept verbatim; the theory makes the Byzantine node the leader of every
   view, so they are simply never enabled.)
4. **The dropped assumption `leader_honest_cofinal`**, and this one is
   *not* of the same kind: 1–3 and 5 remove behaviours, whereas omitting an
   assumption **admits more theories**, and the theory below is one of
   them — node 0 is Byzantine and leads both views, so honest leaders are
   not cofinal in `Fin 2`. What is refuted here is therefore the mutant
   *without* that assumption. The refutation carries to the mutant with
   it, because the assumption constrains only the immutable leader
   schedule at views this run never enters: replay the same 25
   transitions at `view := Fin 3` with an honest leader at view 2 and
   every step is a step of the assumption-carrying mutant. That larger
   instance is not checked — a third view multiplies the search — so the
   embedding is an argument on this page rather than a machine-checked
   one. It is an argument about the *mutation test*: [Mvba.lean](../Mvba.lean)'s safety
   is proven, never model-checked, and nothing about it rests on this
   file.
5. **A fixed schedule for the environment and the timeouts** (since R6,
   for the search's cost): the shares are supplied before any proposal is
   accepted; the correct validators' common input is the vector the
   adversary's plan names for the first view; the adversary signs in a view
   once every correct participant has entered it, and aggregates a commit
   certificate only while no correct validator has decided; a correct
   validator times out only after it has sent its commit. Each is one
   more guard, so like 1–3 it only *removes* enabled transitions. Without
   them the environment's steps can fall anywhere in the 25-step run, and
   each position is a separate branch of the search: that is where the
   check's cost was, and with them it takes about a minute on one core
   ([History.md](../../docs/History.md) has the measurement). The scenario below satisfies all of them, so the
   counterexample did not move.

Everything else — the honest protocol steps with their halt after a
decision, the certificate assemblies with their `2f+1` guards, the view
change — is verbatim from [Mvba.lean](../Mvba.lean)
(with the mutation, the timer folded as item 1 says, and item 5's
guards), and the model
checks the same three safety properties,
of which `agreement` is the one violated.

The counterexample is the textbook lock-persistence scenario (`n = 4`,
`f = 1`; node 0 Byzantine and the leader of both views): view 1 — the
leader proposes value 0, validators 1 and 2 prepare, each forms its own
prepare certificate from the three prepares, and their commits plus the
Byzantine commit are aggregated by the adversary into a **commit
certificate on value 0** (`form_commitqc`), on which nobody decides yet;
both time out carrying their prepare certificate, and validator 1, with
the Byzantine lock-free timeout, forms a **timeout certificate whose lock
is value 0** (`form_own_tc_lock`); both sync into view 2. View 2 — the
Byzantine leader proposes **value 1**; without the lock check both
validators accept it, prepare, form the new prepare certificate and
commit, and validator 1 forms a **commit certificate on value 1** from
the three commits and decides value 1 on it (`form_own_commitqc`).
Validator 2 then decides value 0 from the first certificate (`decide`).
The decisions come last: a validator that has decided halts, so neither
could time out after deciding, and so the view-1 certificate has to be the
adversary's aggregation rather than a correct validator's own (which would
have decided on it and halted). In [Mvba.lean](../Mvba.lean) the `handle_preprepare` guard
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
type evec
type view

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet
instantiate vord : TotalOrderWithMinimum view

immutable function ent : value → evec
immutable relation valid (e : value)
immutable relation leader (v : view) (l : node)
/-- The validators that act: the scheduler restriction (header, item 2). -/
immutable relation participant (i : node)
/-- The value the Byzantine signer uses in each view: the adversary
restriction (header, item 2). -/
immutable relation byz_plan (v : view) (e : value)

relation msg_preprepare (l : node) (v : view) (e : value)
relation msg_prepare (r : node) (v : view) (e : evec)
relation msg_commit (r : node) (v : view) (e : evec)
relation msg_timeout_qc (r : node) (v : view) (w : view) (e : evec)
relation msg_timeout_noqc (r : node) (v : view)
relation msg_prepqc (v : view) (e : evec)
relation msg_commitqc (v : view) (e : evec)
relation msg_tc (v : view)
relation tc_lock (v : view) (w : view) (e : evec)
relation tc_nolock (v : view)

relation input (i : node) (e : value)
relation entered (i : node) (v : view)
relation voted (i : node) (v : view)
relation accepted (i : node) (v : view) (e : value)
relation local_prepqc (i : node) (w : view) (e : evec)
relation timed_out (i : node) (v : view)
relation commit_sent (i : node) (v : view)
relation proposed_in (l : node) (v : view)
relation decided (i : node) (e : value)
relation abandoned (i : node)
relation avail_ready (i : node) (e : value)
relation tc_formed (i : node) (v : view)

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
  tc_formed I V := false
}

/-- `propose` for every validator at once, on one vector — four `propose`
steps of the mutant (header, item 1) — and the vector is the one the
adversary's plan names for the first view (header, item 5). -/
action propose_all (e : value) {
  require ∀ I E, ¬ input I E
  require ∀ I, ¬ abandoned I
  require byz_plan vord.zero e
  input I e := true
  entered I vord.zero := true
}

action leader_propose_first (l : node) (e : value) {
  require ¬ is_byz l
  require ¬ abandoned l
  require ∀ E, ¬ decided l E
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
  require ∀ E, ¬ decided l E
  require vord.next pv v
  require leader v l
  require in_view l v
  require tc_lock pv w (ent e)
  require valid e
  require ¬ proposed_in l v
  proposed_in l v := true
  msg_preprepare l v e := true
}

action leader_propose_fresh (l : node) (pv : view) (v : view) (e : value) {
  require ¬ is_byz l
  require ¬ abandoned l
  require ∀ E, ¬ decided l E
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
  require ∀ E, ¬ decided i E
  require in_view i vord.zero
  require leader vord.zero l
  require msg_preprepare l vord.zero e
  require valid e
  require ∀ W, voted i W → vord.lt W vord.zero
  accepted i vord.zero e := true
  voted i vord.zero := true
  msg_prepare i vord.zero (ent e) := true
}

/-- **The mutation.** [Mvba.lean](../Mvba.lean) requires `lock_available pv e ∨ tc_nolock
pv` here: the justification's lock is `⊥` or the proposed vector. Only the
existence of a `TC_{s,v-1}` is checked — the lock is ignored. -/
action handle_preprepare (i : node) (l : node) (pv : view) (v : view) (e : value) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require vord.next pv v
  require leader v l
  require msg_preprepare l v e
  require valid e
  require msg_tc pv
  require ∀ W, voted i W → vord.lt W v
  accepted i v e := true
  voted i v := true
  msg_prepare i v (ent e) := true
}

action adopt_prepqc (i : node) (v : view) (x : value) (q : nodeset) {
  require ¬ is_byz i
  require participant i
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
  msg_prepqc v (ent x) := true
}

/-- The environment supplies every validator's shares for `e` at once — four
`become_avail_ready` steps of the mutant (header, item 1) — before any
proposal is accepted (header, item 5). -/
action become_avail_ready_all (e : value) {
  require ∀ I V E, ¬ accepted I V E
  avail_ready I e := true
}

action send_commit (i : node) (v : view) (x : value) {
  require ¬ is_byz i
  require participant i
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

/-- The adversary's aggregation of a commit certificate, while no correct
validator has decided (header, item 5). -/
action form_commitqc (v : view) (e : evec) (q : nodeset) {
  require ∀ I E, ¬ decided I E
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit r v e
  msg_commitqc v e := true
}

action form_own_commitqc (i : node) (v : view) (x : value) (q : nodeset) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit r v (ent x)
  require valid x
  msg_commitqc v (ent x) := true
  decided i x := true
}

action decide (i : node) (v : view) (x : value) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require msg_commitqc v (ent x)
  require valid x
  require ∀ E, ¬ decided i E
  decided i x := true
}

action timeout_qc (i : node) (v : view) (w : view) (e : evec) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require ¬ timed_out i v
  -- A correct validator times out only after its commit (header, item 5).
  require commit_sent i v
  require local_prepqc i w e
  require ∀ W E, local_prepqc i W E → vord.le W w
  timed_out i v := true
  voted i v := true
  msg_timeout_qc i v w e := true
}

action form_own_tc_lock (i : node) (v : view) (q : nodeset) (r0 : node) (w : view) (e : evec) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require in_view i v
  require ¬ tc_formed i v
  require nset.supermajority q
  require nset.member r0 q
  require msg_timeout_qc r0 v w e
  require msg_prepqc w e
  require vord.le w v
  require ∀ r, nset.member r q →
    msg_timeout_noqc r v ∨ ∃ W E, msg_timeout_qc r v W E ∧ vord.le W w
  tc_formed i v := true
  msg_tc v := true
  tc_lock v w e := true
}

action sync_view (i : node) (pv : view) (v : view) {
  require ¬ is_byz i
  require participant i
  require ∃ E, input i E
  require ¬ abandoned i
  require ∀ E, ¬ decided i E
  require vord.next pv v
  require msg_tc pv
  require ∀ V, entered i V → vord.le V pv
  entered i v := true
}

/-- The adversary, scripted (header, items 1 and 2): a Byzantine node signs a
`Pre-Prepare`, a `Prepare` and a `Commit` on `(v, e)` and a lock-free
`Timeout` for `v` in one step — `byz_preprepare`, `byz_prepare`,
`byz_commit`, `byz_timeout_noqc` of the mutant — on the vector its plan
names for the view, once every correct participant has entered it (header,
item 5). -/
action byz_sign (r : node) (v : view) (e : value) {
  require is_byz r
  require byz_plan v e
  require ∀ I, participant I → ¬ is_byz I → entered I v
  msg_preprepare r v e := true
  msg_prepare r v (ent e) := true
  msg_commit r v (ent e) := true
  msg_timeout_noqc r v := true
}

/-! ## The refuted properties — the three of Module 3 (`mod:mvba`), as in [Mvba.lean](../Mvba.lean) -/

safety [agreement]
  ∀ (I J : node) (X X' : value),
    ¬ is_byz I → ¬ is_byz J → decided I X → decided J X' → ent X = ent X'

safety [integrity]
  ∀ (I : node) (X X' : value),
    ¬ is_byz I → decided I X → decided I X' → X = X'

safety [external_validity]
  ∀ (I : node) (X : value), ¬ is_byz I → decided I X → valid X

set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192

#gen_spec

/-! ## The mechanical refutation

Exhaustive exploration at `n = 4`, `f = 1` (node 0 Byzantine — the default
`ByzNodeSet` instance for `Fin (3 * f + 1)` makes the first `f` nodes
Byzantine — and, by the theory below, the leader of every view), two
values, two views; the theory is the one the checker is given (it
enumerates no others), and it satisfies `leader_functional` — but not
[Mvba.lean](../Mvba.lean)'s `leader_honest_cofinal`, which this model does not declare
(header, restriction 4). Expected
outcome: **violation** of `agreement`, with the trace described in the
header. The same run is impossible in [Mvba.lean](../Mvba.lean): its
`handle_preprepare` rejects the view-2 proposal against the lock, and
[Mvba/Certify.lean](Certify.lean) proves agreement at every reachable
state. -/

/--
error: ❌ Violation: safety_failure (violates: agreement)
  Theory:
    byz_plan = [[0, 0], [1, 1]]
    ent = [[0, 0], [1, 1]]
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
    tc_formed = []
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
    tc_formed = []
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
    tc_formed = []
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
    tc_formed = []
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
    tc_formed = []
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
    tc_formed = []
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
    tc_formed = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 7 (via adopt_prepqc(i=1, q=[0, 1, 2], v=0, x=0)):
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
    tc_formed = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 8 (via adopt_prepqc(i=2, q=[0, 1, 2], v=0, x=0)):
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
    tc_formed = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 9 (via send_commit(i=1, v=0, x=0)):
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
    tc_formed = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 10 (via send_commit(i=2, v=0, x=0)):
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
    tc_formed = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 11 (via form_commitqc(e=0, q=[0, 1, 2], v=0)):
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
    tc_formed = []
    tc_lock = []
    tc_nolock = []
    timed_out = []
    voted = [[1, 0], [2, 0]]
  State 12 (via timeout_qc(e=0, i=1, v=0, w=0)):
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
    msg_timeout_qc = [[1, [0, [0, 0]]]]
    proposed_in = []
    tc_formed = []
    tc_lock = []
    tc_nolock = []
    timed_out = [[1, 0]]
    voted = [[1, 0], [2, 0]]
  State 13 (via timeout_qc(e=0, i=2, v=0, w=0)):
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
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_formed = []
    tc_lock = []
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 14 (via form_own_tc_lock(e=0, i=1, q=[0, 1, 2], r0=1, v=0, w=0)):
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
    msg_tc = [0]
    msg_timeout_noqc = [[0, 0]]
    msg_timeout_qc = [[1, [0, [0, 0]]], [2, [0, [0, 0]]]]
    proposed_in = []
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 15 (via sync_view(i=1, pv=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = []
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 16 (via sync_view(i=2, pv=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = []
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 17 (via byz_sign(e=1, r=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = []
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [2, 0]]
  State 18 (via handle_preprepare(e=1, i=1, l=0, pv=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = []
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0]]
  State 19 (via handle_preprepare(e=1, i=2, l=0, pv=0, v=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = []
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 20 (via adopt_prepqc(i=1, q=[0, 1, 2], v=1, x=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = []
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 21 (via adopt_prepqc(i=2, q=[0, 1, 2], v=1, x=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [2, 0]]
    decided = []
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 22 (via send_commit(i=1, v=1, x=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [1, 1], [2, 0]]
    decided = []
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 23 (via send_commit(i=2, v=1, x=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [1, 1], [2, 0], [2, 1]]
    decided = []
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 24 (via form_own_commitqc(i=1, q=[0, 1, 2], v=1, x=1)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [1, 1], [2, 0], [2, 1]]
    decided = [[1, 1]]
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
  State 25 (via decide(i=2, v=0, x=0)):
    abandoned = []
    accepted = [[1, [0, 0]], [1, [1, 1]], [2, [0, 0]], [2, [1, 1]]]
    avail_ready = [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1], [3, 0], [3, 1]]
    commit_sent = [[1, 0], [1, 1], [2, 0], [2, 1]]
    decided = [[1, 1], [2, 0]]
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
    tc_formed = [[1, 0]]
    tc_lock = [[0, [0, 0]]]
    tc_nolock = []
    timed_out = [[1, 0], [2, 0]]
    voted = [[1, 0], [1, 1], [2, 0], [2, 1]]
-/
#guard_msgs in
/- `sequential := true` is load-bearing for the pin above, not a performance
choice. By default `#model_check` splits the BFS frontier into `numSubTasks`
parallel sub-tasks and that count defaults to the machine's **core count**, so
*which* of the violating states is reported first depends on the hardware:
machines with different core counts report different, equally valid
witnesses. The claim being
pinned is "a reachable state violates `agreement`" — the witness is
evidence, not the claim — but `#guard_msgs` compares the whole message, so
the search must be deterministic.

The pin moved once since, in R15, when the value became the meta-block
representation ([PaperAlignment.md](../../docs/PaperAlignment.md) §8.1):
the theory gained `ent` (the identity, one representation per entry
vector), and the actions that take the accepted or decided representation
print it as `x`. The witness is the same 25 transitions in the same order. -/
#model_check interpreted
  { node := Fin (3 * 1 + 1), nodeset := ByzNSet (3 * 1 + 1),
    value := Fin 2, evec := Fin 2, view := Fin 2 }
  { ent := fun x => x, valid := fun _ => true, leader := fun _ l => l == 0,
    participant := fun i => i.val != 3, byz_plan := fun v e => v.val == e.val }
  (sequential := true)

end MvbaNoLock
