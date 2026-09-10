# MVBA instantiation — plan

*A plan with a status trail, not a status document. It records what the
work is, what had to be decided before it started, and which choices would
quietly foreclose later work if made carelessly; each step of §8 carries a
note saying whether and how it landed (steps 2, 3 and 5 landed 2026-09-08 on
branch `worktree-mvba-instantiation`; what is proven now is in
[`../README.md`](../README.md) and [`../Cadence.lean`](../Cadence.lean)).
Revised 2026-09-04, after the contract composition landed in `master`
([`CompositionContracts.md`](./CompositionContracts.md)); the first draft's
contract-fix step is gone and its analysis is superseded (§10).*

The MVBA is the last oracle in Chorus's trust base whose provider could
plausibly become a model. `mod:mvba` in the published paper is an interface
and five properties with no algorithm, which is why the development consumes
it under (A-mvba) and why `ℓ_MVBA` is a parametric hole
([`Bounds.md`](./Bounds.md) §1). The paper's internal implementation track
specifies a concrete leader-based protocol with its own correctness section,
so for the first time there is something to model.

## 0. The specification, and the commit to pin it to

Everything verified so far is checkable against `arXiv:2607.02275v2`. The
MVBA algorithm is not in it: it lives in the paper repository's **internal
supplement** (`supplementary-internal.tex` and
`src/supplementary-internal/`), which is not yet part of the published
paper ([`PaperAlignment.md`](./PaperAlignment.md) §2, §4). That is stated,
not worked around: the model's header, and every document that names the
model, say that its specification is the internal supplement, not yet part
of the published paper, and that `mod:mvba` — the contract the model is
proven to satisfy — is the public part. What an auditor can check without
the supplement is the theorem `Mvba ⊨ MVBASafety` against the public
contract; what needs the supplement is the model's fidelity to the
algorithm. The implementation in code is out of scope and is not cited.

**The referent is a paper-repository commit, recorded for our own future
iterations.** The paper has arXiv versions, and [`README.md`](../README.md)
maps each to the unique paper-repo commit that reproduces it. The
supplement has neither tags nor versions, and
`src/supplementary-internal/alg_mvba.tex` is the most-churned file in the
repository — some twenty commits since July, the latest on 2026-09-03 — so
the model pins the **commit SHA of the paper repository it was read
against**, and any later change to `alg_mvba.tex` or to
`subsec:mvba-correctness` is the trigger to re-read the model against the
new commit and move the pin. For this plan, and for the model's first
version, the referent is paper-repo commit **`026dc8b`** (2026-09-03).
The anchors to cite from it: `sec:mvba-instantiation`,
`subsec:mvba-datatypes`, `subsec:mvba-protocol`, the three algorithm blocks
`alg:mvba`, `alg:mvba-cont`, `alg:mvba-cont2` with their `line:mvba:*`
labels, and the correctness section `subsec:mvba-correctness` with
`rem:signature-separation`, `lem:vote-uniqueness`, `lem:commit-provenance`,
`rem:lock-monotonicity`, `lem:cert-uniqueness`, `lem:lock-formation`,
`lem:avail-progress`, `lem:commit-availability`, `lem:timeout-closes-view`,
`lem:lock-persistence`, `thm:agreement`, `lem:external-validity`,
`lem:reproposal`, `lem:lock-availability`, `lem:proposability`,
`thm:termination`, `cor:mvba-recovery-termination`. This is a new
convention here — everywhere else the citation discipline rests on stable
anchors in an immutable document — but it is cheap and it is the only honest
option while the supplement stays untagged.

**What moved between the first draft and `026dc8b`**, because each item
changes the model:

* `decide` now outputs the certificate too: `decide(x, CommitQC)`. The
  public `mod:mvba` has `decide(B)` and no certificate output; the class
  follows the public paper. The certificate is an implementation extra —
  Chorus's fallback commit round forms its own `fbCommitQC` — and is *not*
  a contract field.
* `TrySendCommit` gained an availability precondition `AvailReady_i(x_v)`
  under a new after-GST bound `Δ_sync` (the supplement's
  "availability-synchronization assumption"), plus a `commitSent_i` flag.
  Safety-wise this only removes behaviours; it adds a liveness assumption
  (§3).
* The `Pre-Prepare` handler runs `SyncView(J)` first, so a proposal
  carrying a higher timeout certificate advances the receiver's view before
  the checks; `ViewTC_i` records the certificate that justified the current
  view; `HandleTimeout` raises `lastVotedView_i` to at least the current
  view.
* `TryFormCommitQC` no longer requires `x_v ≠ ⊥ ∧ entries(x_v) = e`: a
  validator may form the certificate first and recover the value
  afterwards (`Recover(e)`). This *removes* a guard, so it is the one change
  that adds behaviour and cannot be ignored conservatively. With `value` the
  entry vector (§1.2) `Recover` collapses to the identity, so the model
  simply decides on the certificate.

## 1. Where the composition stands, and the seam that is left

**Done on `master`** (2026-09-04, [`CompositionContracts.md`](./CompositionContracts.md)):
the module contracts are two-level type classes over an explicit abstract
state; the glue and the Conductor consume the `…Safety` fragments as class
constraints; `Conductor.orchestratorSafety` and `Chorus.slotConsensusSafety`
are proven field for field; the unproven temporal obligations are class
structures type-checked against the full classes; and
`Cadence.system_positional_log_safety` composes MCP Safety with no contract
hypothesis left. The MVBA already has its two classes:

| Class | Fields |
|---|---|
| `MVBASafety party value state byz` | `Valid`; `init`, `step`, `trans`, `reachable` and their closure axioms; the observable `decided` with `decided_mono`, `init_decided`; `agreement`, `integrity`, `external_validity` at reachable states |
| `MVBA … extends MVBASafety` | inputs `propose`, `abandon` with observables `proposed`, `abandoned`, `sent`, their monotonicity, effects, frames and initial conditions; `clock`, `Admissible`, `admissible_exists`; the bound `ℓ`; `termination`, `quiescence` over timed runs |

**Chorus does not consume the class.** Alone among the consumers it inlines
the oracle's properties as guards of three actions — `mvba_decide_pos`,
`mvba_decide_neg`, `mvba_terminate` over the relations `mvba_decided_pos`,
`mvba_decided_neg`, `mvba_complete` — and the transcription is audited by
reading ([`CompositionContracts.md`](./CompositionContracts.md) §8, the
table). The reason is not the class's shape. The paper's `Valid B` is a
function of the meta-block, which *carries* its certificates; Chorus checks
a decided entry's certificate against its own network relations
(`vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)`) — a predicate on
Chorus's **state**, which a class parameter declared before `#gen_state`
cannot mention.

### 1.1 The resolution this plan adopts: one stated bridge

There is no bridge-free consumption, and the plan should say so rather than
promise one. The three routes, and why two of them fail:

* **Restate the evidence guards as the class's `Valid`.** Impossible for the
  reason above: `Valid` is fixed at `instantiate` time, before Chorus's
  state exists.
* **Relate the MVBA's `Valid` to Chorus's network at the system level.** In
  the MVBA model `Valid` is necessarily an *immutable* relation (the
  algorithm only checks certificates; it does not know what they mean), and
  Chorus's certificate predicate is a *mutable* state fact. A hypothesis
  relating an immutable to a state that varies along the run is not
  stateable, and a monotone "eventually" version smuggles in liveness.
* **Carry certificates in the value type and verify them at the receiver.**
  This works, and it is what the protocol does: Chorus's decision handler
  reads a correct validator's decision off the abstract MVBA state and,
  before acting on an entry, checks that its certificate verifies against
  the network — a positive read of `msg_*_sig` rows, which is how every
  certificate check in Chorus is modelled today (`broadcast_commitqc_*`
  requires its quorum's signatures). Whether the certificate is carried as
  data or only asserted, the *verification* step is the same guard, so the
  value type can stay the bare entry vector (§1.2) and the guard becomes the
  interpretation of `Valid` in Chorus's vocabulary.

That guard is a **bridge, not a restatement**: the class's
`external_validity` says the decided value's certificates are valid
objects; the guard says what a valid certificate *means* in a model where
signatures are network relations. It has exactly the shape of the
Conductor's one stated bridge — the median-range `require` of `acs_decide`,
justified by an upper-level class field through `Windows.lean`
([`CompositionContracts.md`](./CompositionContracts.md) §8 item 3). It is
sound in both directions that matter: it removes no real behaviour (public
verifiability means the receiver *can* re-check, and `external_validity`
guarantees the check passes against a correct MVBA), and if the MVBA were
wrong the handler would simply not fire — safety-conservative.

What the class then delivers to Chorus, replacing hand-written guards and
the invariants that lift them: agreement between correct deciders (hence
per proposer, by projection), integrity, monotonicity of decisions, and the
empty initial state. What stays a bridge: the interpretation of validity, at
one handler, documented at the action and in `Architecture.md` §4.

### 1.2 The value is the entry vector

`mod:mvba` states Agreement as meta-block equality; the supplement's
`thm:agreement` proves the entries-level statement and says so
deliberately — certificates are carried only so validity can be checked
([`PaperAlignment.md`](./PaperAlignment.md) §4 item 3). Chorus's oracle
already works per proposer. So the class is instantiated at
`value := node → Option merkle_root` (`some m` a positive entry, `none` a
negative one), in both the MVBA model's instance and Chorus's constraint.
Two consequences: the MVBA model's `Valid` is an uninterpreted immutable
relation on entry vectors, and `Recover(e)` is the identity — the leader
re-proposes the lock's entries directly.

## 2. The model

### 2.1 Placement

The verified-module file family, exactly as `FallbackReceipt` has it: a
model file `Cadence/Mvba.lean` (registry, no sweep) importing `Veil` and
`Cadence.Tooling` only; `Cadence/Mvba/Proofs/<Action>.lean`;
`Cadence/Mvba/Certify.lean` with the `#veil_status Mvba` pin;
`Cadence/Mvba/Compose.lean` (the only file importing `Interfaces.lean`)
with the instance, the join toward the full class and the axiom pins; rows and pins in
[`Cadence.lean`](../Cadence.lean). Nothing imports `Chorus.lean`, so steps
1–5 of §8 never rebuild the Chorus family. The model shares Chorus's `node`
/ `nodeset` / `ByzNodeSet` vocabulary so that the system composition needs
no fault-model transport between the two.

### 2.2 Types and immutable configuration

* `node`, `nodeset` with `instantiate nset : ByzNodeSet node nodeset` —
  the quorum interface, discharged for every `n = 3f+1` by `byzNodeSetFin`.
* `view` with `TotalOrderWithMinimum` — the Conductor's treatment of slots
  and windows: `zero` is view 1, `next v v'` is `v' = v + 1`, and no
  arithmetic reaches the solver.
* `value`, opaque, with `immutable relation valid (e : value)` — the
  external validity predicate the instance is parameterised by.
* `immutable relation leader (v : view) (l : node)`, functional — the
  paper's deterministic public `Leader(slot, v)`.

### 2.3 State

**Network relations** (`msg_*`, monotone, consulted in positive position
only — [`ChorusDesign.md`](./ChorusDesign.md) §3.1.1 governs them, and no
new exception category is expected):

| Relation | Paper message |
|---|---|
| `msg_preprepare l v e` | `⟨Pre-Prepare, s, v, x, J, σ_l⟩` — the justification `J` is not carried; the receiver checks the network for `msg_tc (prev v)` and its lock |
| `msg_prepare r v e`, `msg_commit r v e` | `⟨Prepare, s, v, e, σ⟩`, `⟨Commit, s, v, e, σ⟩` |
| `msg_timeout_qc r v w e`, `msg_timeout_noqc r v` | `⟨Timeout, s, v, PrepQC_i, σ⟩` carrying a prepare certificate of view `w` on `e`, or none |
| `msg_prepqc v e`, `msg_commitqc v e`, `msg_tc v` | the three certificates, **materialised by explicit assembly actions** whose guards are the signature quorums — the hard-VC playbook's rule against `∃`-quorum ghosts in consumers |
| `tc_lock v e`, `tc_nolock v` | `lock(TC_{s,v})`, recorded at assembly with the highest carried certificate as an explicit witness (`highPrepQC` is "some member carries `(w, e)` and no member carries a higher view", first-order over the member set) |

**Validator-local state**, free of the network contract, kept **monotone
and view-indexed** (§3 says why): `input i e` (the `propose` argument),
`entered i v` (current view = the maximum entered), `voted i v` (so
"`v_msg > lastVotedView_i`" is `∀ w, voted i w → w < v_msg`), `accepted i v e`
(`x_v`), `local_prepqc i v e` (certificates held; `PrepQC_i` is the highest),
`timed_out i v`, `commit_sent i v`, `decided i e`, `abandoned i`, and the
environment relation `avail_ready i e` (`AvailReady_i`).

### 2.4 Actions

Honest, roughly one per handler or procedure of `alg:mvba`–`alg:mvba-cont2`:
`propose i e` (sets the input, enters view 1); `leader_propose l v e` (the
view-entry rule: own input in view 1, else the lock of `TC_{v-1}` if any,
else own input); `handle_preprepare i v e` (`line:mvba:pp-guard`: current
view, leader, `valid e`, `msg_tc (prev v)` for `v > 1`, `e` equals the lock
when there is one, no vote at or above `v`; records `accepted`, `voted`,
sends `Prepare`); `form_prepqc v e q` (assembly, `2f+1` prepares);
`adopt_prepqc i v e` (`TryFormPrepQC`'s local half: `line:mvba:tfp-guard`);
`send_commit i v e` (`TrySendCommit`, `line:mvba:commit-send`, including
`avail_ready i e`); `form_commitqc v e q`; `decide i v e` (on `msg_commitqc
v e`, once — `TryDecide` / `TryFormCommitQC` / the transferred-certificate
handler collapse into one action, since `Recover` is the identity);
`timeout i v` (the timer, abstracted: enabled once `entered i v` and not
decided); `echo_timeout i v` (the `f+1` rule, `line:mvba:ht-send`);
`form_tc v q w e` / `form_tc_nolock v q` (assembly with the lock witness);
`sync_view i v` (`SyncView`, `line:mvba:sv`: enter `v+1`, adopt the carried
certificate if higher); `abandon i`. Byzantine: `byz_preprepare`,
`byz_prepare`, `byz_commit`, `byz_timeout` — arbitrary messages attributed
to Byzantine signers, subject to network validity (a Byzantine timeout can
carry only a certificate that exists). About 14 honest and 4 Byzantine
actions; parameter lists stay well under ten.

### 2.5 Abstractions to commit to

* **Messages monotone, local state free.** The `¬timedOut_i`,
  `¬commitSent_i` and `lastVotedView` guards are on local relations, so they
  need no exception category — worth stating, since they look like negative
  reads at first glance.
* **No persistence, no crash.** `persist state` and the atomic reload
  (`line:mvba:reload`) are implementation obligations, recorded as an
  obligation-table row; `cor:mvba-recovery-termination` stays a paper
  result. The model's local state is exactly the crash-free execution's.
* **`AvailReady` is an environment relation.** `become_avail_ready i e` is
  an unguarded honest action setting `avail_ready i e`; `send_commit` reads
  it positively. Safety-neutral (a guard), and the hook for the `Δ_sync`
  assumption (§3).
* **`abandon` is modelled**, unlike in Chorus: a monotone flag that every
  honest send requires to be unset, and `propose` is the `input` record.
  Cheap, and it is what lets the provider prove the class's input fields
  and Quiescence (§5) instead of leaving them unproven.
* **Integrity by construction.** `decide` requires `¬ ∃ e', decided i e'`.
* **The leader's `Recover(lock(J))`** is the lock's entries themselves
  (§1.2).

### 2.6 Safety properties and the invariant plan

The paper's proof structure maps onto invariants almost one to one; the
table is the working list, not a promise about count.

| Supplement | Invariant(s) |
|---|---|
| `lem:vote-uniqueness` | an honest `msg_prepare r v e` ⇒ `accepted r v e`, unique per view; an honest `msg_commit r v e` ⇒ the same `e` |
| `lem:commit-provenance` | honest `msg_commit r v e` ⇒ `local_prepqc r v e ∧ accepted r v e`; and an honest commit in view `v` together with an honest timeout in a view `v' ≥ v` carries a certificate of view at least `v` |
| `rem:lock-monotonicity` | `local_prepqc i w e ∧ entered i v ⇒ w ≤ v`; held certificates are network certificates |
| `lem:cert-uniqueness` | `msg_prepqc v e ∧ msg_prepqc v e' ⇒ e = e'`, and for `msg_commitqc` — the two-supermajority intersection; expect these to be **manual cells**, as Chorus's quorum-intersection cells are |
| `lem:timeout-closes-view` | honest `msg_timeout_* r v` ⇒ no later `accepted r v _`; `timed_out r v ⇒ voted r v` |
| `lem:lock-persistence` | **not an invariant** (see the correction below): the clump carries the inductive form `prepqc_blocks_lower_commits` — `msg_prepqc w e' ∧ v < w ∧ e ≠ e' ⇒` every supermajority has a correct member that left `v` without a view-`≥ v` lock or holds a view-`v` lock on another value; (i) `msg_commitqc v e ∧ v ≤ v' ∧ tc_lock v' e' ⇒ e' = e`, `¬ tc_nolock v'` and (ii) `msg_commitqc v e ∧ v ≤ w ∧ msg_prepqc w e' ⇒ e' = e` are corollaries, and `commitqc_agree` (agreement at the certificate level, across views) is the one the safety property uses |
| `thm:agreement` | `safety [agreement]`: `decided i e ∧ decided j e' ∧ ¬ byz i ∧ ¬ byz j ⇒ e = e'` — from (ii) and certificate uniqueness |
| Integrity | `safety [integrity]` — by construction, lifted |
| `lem:external-validity` | `safety [external_validity]`: `decided i e ⇒ valid e`, via honest `accepted _ _ e ⇒ valid e` and an honest preparer in every prepare quorum |

**A correction to the first draft's risk assessment.** The paper's
`lem:lock-formation` counts "at least `f+1` correct signers" of a commit
certificate, which *would* fall outside `ByzNodeSet`'s first-order language
(the wall Chorus hit, resolved in `Counting.lean` and `Pigeonhole.lean`).
The model does not need that form. Lock persistence's inductive step
intersects a timeout certificate's `2f+1` senders with a commit
certificate's `2f+1` signers and takes the *honest common member* — the
class's two-supermajority intersection axiom, the same one Chorus's
commitQC-versus-`FBCert` case uses. That member sent its commit in view
`v` after holding a view-`v` certificate on `e`, so its later timeout
carries a certificate of view at least `v` (lock monotonicity), which is on
`e` by (ii); any certificate outranking it is also on `e` by (ii). So the
whole safety argument stays inside the invariant clump. The risk is the
usual one: e-matching divergence at the intersection cells, cured by manual
cells, not a language gap.

**A second correction, found while building the full model (2026-09-08).**
`lem:lock-persistence` as stated is *not an inductive invariant*, and the
table's original rows (i)/(ii) could not have been proven cell by cell. The
supplement proves it by induction on the view `v'`; the model has no such
step. When a commit certificate of view `v` forms, timeout and prepare
certificates of views above `v` may already exist (asynchrony), and
re-establishing (i)/(ii) for all of them at that one transition *is* the
induction. The inductive form is the standard one from the Paxos-made-EPR
family: `prepqc_blocks_lower_commits` — a prepare certificate of view `w`
on `e'` blocks, in every view `v < w` and for every `e ≠ e'`, every
supermajority from committing `e` in `v`, by exhibiting a correct member
that either sent a timeout at or after `v` carrying no lock of view `≥ v`
or holds a view-`v` lock on another value (the ghost `blocked`). It is
stated for *all* lower views, not only committed ones, so the commit
transition has nothing to re-establish; its one non-trivial step is
`form_prepqc`, where the honest preparer's justification, the timeout
quorum's honest intersection with the given supermajority, and the
invariant itself at the lock's certificate give the supplement's argument
for a single view transition. `commitqc_agree` — agreement at the
certificate level across views — follows by instantiation, and so do (i)
and (ii). The model header of `Cadence/Mvba.lean` carries the same account.

## 3. Liveness

**Target.** Not `thm:termination`'s `O(fΔ)` — the models are untimed and
no artefact here claims a latency bound. The target is its bound-erased
skeleton, "every correct validator eventually decides", in the form Chorus
already uses: fair-progress invariants inside the sweep, the state-level
content kernel-checked, the temporal step carried by named assumptions
([`Liveness.md`](./Liveness.md)).

**Deferred, but it must not be designed out.** Two choices would foreclose
it:

* **Do not model view advancement as unguarded nondeterminism.** Letting any
  validator jump to any higher view is safety-sound — it only adds
  behaviours — and liveness-fatal: a run that advances views forever starves
  every decision, so no well-founded ranking can exist and the fair-progress
  chain cannot be stated, let alone proven. Keep the timeout-certificate
  structure that gates advancement (`form_tc` requires `2f+1` timeouts;
  `sync_view` requires `msg_tc`); abstract the *timing* only (`timeout i v`
  is enabled, not timed).
* **Keep view-indexed state monotone.** Accumulating relations
  (`entered i v`, `voted i v`, `local_prepqc i v e`) rather than mutable
  current-view fields. Veil's monotone framework is what makes enabledness
  monotone, which is why weak (F-justice) suffices; a mutable counter would
  break that and pull strong fairness — currently *not invoked* anywhere —
  into the argument.

Name the assumptions from the start even while the ranking is unfinished:
(F-justice) on the message handlers and assembly actions; (F-byz) for the
adversary; a view-synchronisation assumption standing in for after-GST
Δ-synchrony (`thm:termination`'s "all correct validators enter view `v+1`
within Δ of one another"); and **(F-avail)**, new with `026dc8b`, standing
in for `Δ_sync`: `avail_ready i e` eventually holds for every accepted
`e` (`lem:avail-progress`). Then the liveness work is additive rather than
a re-encoding — and once it exists, Chorus's (A-mvba) decomposes into these
plus the MVBA's own fair-progress theorems.

## 4. Vacuity

Four instruments, weakest to strongest. Only the first three are
machine-checked evidence.

1. **`sat trace` reachability witnesses.** A decision in view 1; a decision
   after a view change; a Byzantine leader in view 1 and a decision under
   an honest leader in view 2; a run where a held lock forces re-proposal
   of an earlier value. cvc5's `sat` verdicts here are trusted, and that is
   deliberately harmless — a wrong model can only make a non-vacuity check
   vacuous, never a safety claim wrong
   ([`Architecture.md`](./Architecture.md) §4 item 6). Mind the parser rule:
   traces go after `#check_invariants`, and never `set_option … in`
   immediately after a trace block. (The old `st'` rule is retired: the
   generated binders are hygienic since the 2026-09 Veil bump.)
2. **Quorum non-vacuity**, following [`ByzQuorum.lean`](../Cadence/ByzQuorum.lean)'s
   witness pattern, so the quorum interface cannot be vacuously satisfiable.
3. **Mutation testing with `#model_check`** — the strongest available, with
   precedent: [`FallbackReceipt/PreFix.lean`](../Cadence/FallbackReceipt/PreFix.lean)
   pins a counterexample with `#guard_msgs` and a green build *requires* the
   violation. Do the same here: a sibling `Mvba/NoLock.lean` with the lock
   check of `handle_preprepare` removed must fail agreement, with the witness
   pinned. That demonstrates the invariants are load-bearing rather than
   merely true — which is the question vacuity is really asking. It must
   use `(sequential := true)`; the parallel search's frontier split is
   core-count dependent and the pin would hold only on the machine that
   recorded it. **One risk to check early:** the model-check scaffolding's
   label enumeration is what Chorus disables at ~38 actions because the
   derived encodings blow the heartbeat budget; at ~18 actions it should
   fit (FallbackReceipt runs it at 9), but if it does not, the mutation pin
   moves to a reduced sibling model. *Outcome (2026-09-08): the enumeration
   fits; the state space does not — the pin lives on a restriction of the
   mutant (§8 step 4 and the header of `Cadence/Mvba/NoLock.lean`).*
4. **Monitor conformance** via `#gen_monitor`, following `Cadence/Monitor/`.
   Not in any trust base, and [`Monitor.md`](./Monitor.md) §8 already lists
   coverage gaps, so sequence this last and only if the monitor effort is
   being extended anyway. Note the `@[implicit_reducible]`
   warning-suppression trap that `ChorusMonitorGen.lean` documents.

**On deriving it from fairness:** no. The fairness assumptions are
meta-level and never reach the SMT layer, and they speak about *firing given
enabledness*, not about enabledness being reachable at all — which is what
vacuity asks. The machine-checked non-vacuity evidence is instruments 1–3.

## 5. The provider: `Mvba ⊨ MVBASafety`, and the join toward `MVBA`

`Mvba.mvbaSafety th : MVBASafety node value (Mvba.State …) (fun i =>
nset.is_byz i = true)` in `Cadence/Mvba/Compose.lean`, on the pattern of
`Chorus.slotConsensusSafety`:

| `MVBASafety` field | discharged by |
|---|---|
| `Valid` | `th.valid` |
| `init`, `step`, `trans`, `reachable`, closure axioms | the model's own relations and the reachability constructors |
| `decided` | `decided i e` at the canonical field representation |
| `decided_mono`, `init_decided` | the step-facts technique over every action (`mvba_tr` / `mvba_field_simp`, one tactic line each — `CompositionContracts.md` §4) |
| `agreement`, `integrity`, `external_validity` | the named `reachable_<property>` projections of `Certify.lean` |

**What is left unproven is smaller than for Chorus, and Quiescence left it.**
Because the model has `propose` and `abandon`, the upper class's inputs,
observables, effects, frames and initial conditions are *provable*, not
unproven: `propose := propose i e`'s transition, `proposed := input i e`,
`abandoned := abandoned i`, `sent st p m` by cases on a `Mvba.Msg` inductive
over the `msg_*` rows. Quiescence is then a *two-state* fact — a correct
party's new `sent` row at step `n` implies `input` by `n+1` and `¬ abandoned`
at `n` — which is exactly the shape the step-facts technique proves. What
must stay unproven is `clock`, `Admissible`, `admissible_exists`, `ℓ` and
`termination`: the fields of `MVBATemporal`, joined to the fragment by
`mvba_of_temporal`. Since 2026-09-09 the inputs, their observables, the
frames and one-step Quiescence sit in `MVBASafety` itself, so nothing
safety-shaped is left at the temporal level.
*Landed as predicted (2026-09-08; step 5 below).* One consumer-facing
detail worth knowing for step 6: the instance's `step` is the model's
transitions *other than* `propose` and `abandon` (the upper class's frame
fields demand it), so a consumer that advances the abstract state only by
`mvba.step` never sees a proposal — Chorus's oracle action should take
`mvba.trans`, or drive the inputs itself once they are available to it.

## 6. Chorus consumes the class — the expensive step

This is the step that changes every Chorus verification condition. The
edit, concretely:

* `instantiate mvba : MVBASafety node (node → Option merkle_root) mmsg
  mstate (fun i => nset.is_byz i = true)` after `nset`, with `type mstate`
  and `type mmsg` (the fragment carries the module's message type since
  2026-09-09, because Quiescence moved into it); then
  `individual mvba_st : mstate`. Spike first that a later `instantiate` can
  take `nset.is_byz i = true` as the `byz` argument (spike 05 established
  the analogous `fm.byz` projection).
* An oracle action `mvba_step (mvba_next : mstate)` — `require mvba.step
  mvba_st mvba_next` — replaces the three oracle actions. The `propose` /
  `abandon` **input** transitions Chorus needs to drive are in the fragment
  too (also since 2026-09-09), so the consumer no longer needs the full
  class for them.
* A handler `on_mvba_decide (i j m …)` transports a **correct** validator's
  decision entry into Chorus's own records: it reads `mvba.decided mvba_st
  i v` with `v j = some m` (or `none`), keeps Chorus's own guards
  (`phase = post_mvba_arm`, `is_proposer j`, `mvba_invoked` — a Chorus-side
  listening condition, not a contract property), carries the **one stated
  bridge** (`vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)`, resp. the
  negative form) as certificate verification, and sets `mvba_decided_pos j
  m` / `mvba_decided_neg j`. Keeping those relations as the *handler's
  records* — the glue's `delivered` pattern — leaves the ~16 downstream
  invariants that mention them untouched in form. `mvba_complete` becomes
  the record that some correct validator has decided; per-proposer
  completeness is by construction of the vector.
* The agreement guards of the old oracle actions go; in their place, the
  invariants `mvba_decided_pos_unique` and `mvba_decided_pos_neg_excl` are
  *proven* from the class's `agreement` at the reachable abstract state via
  a new invariant tying each record to a correct decision — kept as
  invariants because downstream cells e-match on them (the glue's
  `finalized_agreement` precedent).

**Check before starting:** whether any *safety* invariant relies on
`mvba_invoked` gating decisions (the guard exists for liveness). If one
does, it stays as the handler's guard — which is where it belongs anyway.

**Cost.** A full cold re-solve of the Chorus family (the ~4 000-cell,
~15–20 minute event; budget it deliberately), manual-cell repair where an
action's guards changed (`delta%` binders), the action lists of
`Chorus/Compose.lean`'s step-lemma macros (−3 +2 actions), the
`#veil_status Chorus` pin, the monitor suite under `Cadence/Monitor/`
(it extracts Chorus's actions and CI runs it — the oracle actions are
extracted today), and the "MVBA as an oracle" prose in
[`ChorusDesign.md`](./ChorusDesign.md) §4 and the Chorus header. Afterwards
`Chorus.slotConsensusSafety` carries the MVBA constraint as a parameter,
and [`System.lean`](../Cadence/System.lean) instantiates it at
`Mvba.mvbaSafety thM` — the composed theorem then has no contract
hypothesis left for the MVBA either, and no fault-model transport is
needed because both models share `nset`.

## 7. Scale and where the risk is

Cell counts track actions × properties closely. About eighteen actions and
a view-change safety argument of perhaps 30–45 invariants give roughly
**500–800 cells** — a small multiple of FallbackReceipt and well under a
fifth of Chorus (the pinned counts are in the two `Certify.lean` files).
Volume is not the risk.

The risk is concentrated in **lock persistence across views**
(`lem:lock-persistence`, `lem:cert-uniqueness`), the standard PBFT
view-change argument: several quorum-intersection cells that may diverge
under e-matching and become manual cells (§2.6). The single-view spike (§8
step 2) exercises `lem:cert-uniqueness` in isolation before the view-change
machinery is added, which is where the first manual cells will appear.

## 8. Proposed order

Each step names its exit criterion and what it costs to rebuild.

1. **Contract review — no class change expected.** `MVBASafety`/`MVBA`
   are `mod:mvba` and the plan instantiates them as they stand; the
   supplement's certificate output is not a field (§0). The one edit is
   the obligation table's discharge column and the header table's "out of
   scope" row, once the instance exists — a comment in `Interfaces.lean`,
   which rebuilds the small models and the composition files (minutes),
   not the Chorus family.
2. **Single-view spike.** `Cadence/Mvba.lean` with one view, no timeouts:
   agreement via certificate uniqueness, the whole file family
   (model / `Proofs/` / `Certify`), traces, the `#veil_status` pin, and
   the header that pins the referent (§0). Exit: green, and the
   quorum-intersection cells either solve or are manual. Shakes out the
   encoding; its cells warm the cache. *Done 2026-09-08 (History.md):
   224 cells, every one automatic — the intersection cells needed no
   manual proof at that clump size.*
3. **Full model and safety** (§2): views, timeouts, certificates, lock
   persistence. Exit: `safety [agreement]`, `[integrity]`,
   `[external_validity]` proven; pins updated; rows in `Cadence.lean`.
   *In progress 2026-09-08: the model as built has 24 actions (the
   leader's three view-entry cases and the two `Pre-Prepare` handlers are
   separate actions, `timeout_qc`/`timeout_noqc`, `form_tc_lock`/
   `form_tc_nolock`, `sync_view`/`sync_view_adopt`, five Byzantine
   signers) and 28 properties; names as in `Cadence/Mvba.lean`.*
4. **Vacuity** (§4): the four traces, then the `NoLock` mutation pin.
   *Done 2026-09-08 (three traces in `Mvba.lean`; `Cadence/Mvba/NoLock.lean`).
   The label enumeration does elaborate at 24 actions (the traces already
   needed it), but the faithful mutant — only the lock check weakened — is
   far too wide for the interpreted exhaustive search at `n = 4`, two
   values, two views: the violation needs 28 transitions, and a depth-6
   probe had not finished after half an hour; the first reduction (bulk
   `propose`/availability/Byzantine steps, `abandon` and `byz_timeout_qc`
   dropped) still holds ~27 000 states at depth 8 and did not finish in
   35 minutes. The pin therefore sits on a **second-level restriction**
   that additionally fixes the scheduler and the adversary's plan through
   the theory (`participant`, `byz_plan`) — every run of it is a run of
   the mutant, so the violation is a fortiori the mutant's — and finds
   `agreement` violated in about a minute and a half of search. The
   checker's `compiled` mode returns without waiting outside an editor and
   is unusable for a build-time pin. Details in the file's header.*
5. **Provider** (§5): `Mvba.mvbaSafety`, `mvba_of_temporal`,
   axiom pins. Exit: `Cadence.lean` pins the new declarations at the
   standard trio. *Done 2026-09-08 (`Cadence/Mvba/Compose.lean`): every
   field of `MVBASafety` discharged; what is left is exactly the five
   timed fields §5 predicted (`clock`, `Admissible`, `admissible_exists`,
   `ℓ`, `termination`), and Quiescence is proven as the one-step fact
   `sent_new_tr`. One model edit was needed for that: `leader_repropose`
   was the only honest send without the participation guard `∃ E, input
   l E` (redundant at reachable states, since a view `> 1` is entered
   only through `sync_view`, which requires it); it now has it, and the
   action's cells re-solved cold. `Cadence.lean` pins the six new
   declarations.*
6. **Chorus consumption** (§6). Its own piece of work — the one that pays
   the Chorus cold re-solve and touches the monitor.
7. **Liveness skeleton** (§3), on the hooks left in place.

Steps 2–5 are self-contained and touch no existing model. Step 6 is
scheduled last among the safety work on purpose: the provider is worth
having on its own (it retires the "no instance exists" caveat of
`Architecture.md` §4 item 3), and the consumption's cost is independent of
when it is paid.

### Working notes

* A fresh worktree has no `.lake`. Symlink `.lake/packages` and
  `.lake/build/veilcache` from the main checkout before building; then only
  this project's modules compile and the cache turns the family builds warm.
* Iterate with `scripts/scratch.sh` and `#prove_vc Mvba <action>
  <property> by <tac>` cells; count all four markers; one expensive build
  at a time. The `cadence-verification` skill has the loop.

## 9. Documentation consequences

Where the claims live once the work lands, so the "one home per fact" rule
holds: [`README.md`](../README.md) (end-results table; the §0 note that the
model's specification is the internal supplement, not yet part of the
published paper, pinned to a paper-repository commit);
[`Architecture.md`](./Architecture.md) §4
items 2 and 3 (the MVBA leaves the "no instance exists" list; the bridge
joins the ACS median bridge) and the file-family table;
[`CompositionContracts.md`](./CompositionContracts.md) §8 item 1 (closed,
with the bridge named); [`TODO.md`](./TODO.md) § Contract composition and
§ Soundness; [`ChorusDesign.md`](./ChorusDesign.md) §4 "MVBA as an oracle"
and §9 item 1; [`Bounds.md`](./Bounds.md) §1 (the hole has a referent);
[`PaperAlignment.md`](./PaperAlignment.md) §4; [`History.md`](./History.md)
(a ledger row); [`Cadence.lean`](../Cadence.lean) (rows and pins);
`CLAUDE.md` (orientation, the `#veil_status Mvba` pin in the
verification-status list); and the `Interfaces.lean` header table.

## 10. Superseded

The first draft (2026-09-03) proposed, as its step 2, to lift the contract
properties into standalone definitions over carrier arguments and have
consumer and provider reference one object. The analysis of Veil's
`instantiate` ordering it rested on was correct about the mechanics but
wrong about the fix: the real defect was that the contracts hid a state
index, and the validated replacement is the two-level, state-explicit
contract now on `master` — [`CompositionContracts.md`](./CompositionContracts.md),
whose §9 records what it superseded and §10 the Veil facts that cost time
to find. That draft also expected lock persistence to need a counting
theorem outside the invariant clump; §2.6 explains why it does not.
