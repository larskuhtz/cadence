import Veil
import Cadence.Tooling

/-! # Mvba — the leader-based MVBA instantiation (single-view spike)

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

## The single-view restriction (plan step 2)

This is the **single-view spike** of `docs/MvbaPlan.md` §8: one view, no
timeouts, no view change. Its purpose is to shake out the encoding and to
exercise `lem:cert-uniqueness` — the quorum-intersection argument — in
isolation before the view-change machinery (`SyncView`, `HandleTimeout`,
`ViewTC_i`, timeout certificates and the lock) is added. Consequences:

* the view index is dropped from every message and every local relation;
* `lastVotedView_i ∈ {0, 1}` collapses to the flag `voted i`;
* `Leader(slot, 1)` is the immutable individual `leader`;
* `PrepQC_i` is a certificate of the one view or `⊥`: `local_prepqc i e`;
* the paper's justification `J` is `⊥` in view 1 and is not carried.

The full model (plan step 3) replaces these by view-indexed relations over
a `TotalOrderWithMinimum` view type and adds the timeout path. Everything
kept here is meant to survive that step unchanged in shape.

## The value type

The class is instantiated at the **entry vector** (`docs/MvbaPlan.md`
§1.2): here `value` is an opaque sort standing for `node → Option
merkle_root`, and `valid` is an **uninterpreted immutable relation** — the
algorithm only checks certificates, it does not interpret them, so the
external validity predicate is a parameter. Because the value *is* the
entry vector, the supplement's `Recover(e)` is the identity and `decide`
simply decides the certified vector (`line:mvba:qc-decide`,
`line:mvba:td-decide`).

## State and abstractions

**Network relations** (`msg_*`, monotone, consulted in **positive position
only** — `docs/ChorusDesign.md` §3.1.1 governs them; this module adds no
exception category): the leader's `Pre-Prepare` (`msg_preprepare`), the
`Prepare` and `Commit` signatures (`msg_prepare`, `msg_commit`) and the two
certificates `msg_prepqc` / `msg_commitqc`, **materialised by explicit
assembly actions** (`form_prepqc`, `form_commitqc`) whose guards are the
signature quorums — Chorus's `broadcast_commitqc_*` pattern, which keeps
`∃`-quorum ghosts out of every consumer's guard.

**Validator-local state**, free of the network contract, kept monotone:
`input i e` (the `propose` argument), `voted i` (`lastVotedView_i ≥ 1`),
`accepted i e` (`x_v`), `local_prepqc i e` (`PrepQC_i`), `commit_sent i`
(`commitSent_i`), `decided i e`, `abandoned i`, and the environment
relation `avail_ready i e` (`AvailReady_i(x_v)`, set by an unguarded
environment action — the hook for the supplement's `Δ_sync` assumption,
safety-neutral here). The `¬ voted i`, `¬ commit_sent i` and
`¬ abandoned i` guards are negative reads of *local* state and need no
exception category.

**Not modelled** (implementation obligations, `docs/MvbaPlan.md` §2.5):
persistence and crash recovery (`line:mvba:reload`), the `Pool` cache, the
availability shares. The supplement's `decide(x, CommitQC)` returns the
certificate too; the public `mod:mvba` has `decide(B)`, so the certificate
is not an observable here. The paper's self-`abandon()` after a decision is
the *caller's* input in the contract (`MVBA.abandon`), so `decide` records
the decision and leaves `abandoned` to the `abandon` action; a validator
that has decided can still run its remaining sends, which only adds
behaviours.

## Byzantine behaviour

A Byzantine node may sign any `Pre-Prepare`, `Prepare` or `Commit`
(`byz_preprepare`, `byz_prepare`, `byz_commit`). It cannot forge a
certificate: `msg_prepqc` / `msg_commitqc` are assembled only from `2f+1`
signatures (unforgeability, `rem:signature-separation`). Honest receivers
check that a `Pre-Prepare` comes from `leader`, so a Byzantine non-leader's
proposals are inert, and a Byzantine leader may equivocate. -/

veil module Mvba

type node
type nodeset
-- The entry vector `node → Option merkle_root` (`docs/MvbaPlan.md` §1.2),
-- opaque here.
type value

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet

-- The external validity predicate `Valid` (`mod:mvba`; the supplement's
-- "`x` is a valid meta-block", `subsec:mvba-datatypes`) — uninterpreted.
immutable relation valid (e : value)

-- `Leader(slot, 1)`: a deterministic public function.
immutable individual leader : node

/-! ## Network — signed messages and certificates -/

relation msg_preprepare (l : node) (e : value)
relation msg_prepare (r : node) (e : value)
relation msg_commit (r : node) (e : value)
-- `prepareQC_{s,1}` on `e` / `CommitQC` on `e`: assembled from `2f+1`
-- signatures by `form_prepqc` / `form_commitqc`.
relation msg_prepqc (e : value)
relation msg_commitqc (e : value)

/-! ## Validator-local state -/

-- `propose(B_i)`: the input, and the mark of participation.
relation input (i : node) (e : value)
-- `lastVotedView_i ≥ 1`: a `Prepare` has been sent.
relation voted (i : node)
-- `x_v`: the accepted proposal.
relation accepted (i : node) (e : value)
-- `PrepQC_i`: the prepare certificate held (view 1, or none).
relation local_prepqc (i : node) (e : value)
-- `commitSent_i`.
relation commit_sent (i : node)
-- `decide(x, ·)` has been output.
relation decided (i : node) (e : value)
-- `abandon()` has been called by the composing caller.
relation abandoned (i : node)
-- `AvailReady_i(e)`: the environment (dissemination / ChunkSync) has
-- supplied `i`'s shares for `e`.
relation avail_ready (i : node) (e : value)

#gen_state

/-! ## Initial state -/

after_init {
  msg_preprepare L E := false
  msg_prepare R E := false
  msg_commit R E := false
  msg_prepqc E := false
  msg_commitqc E := false
  input I E := false
  voted I := false
  accepted I E := false
  local_prepqc I E := false
  commit_sent I := false
  decided I E := false
  abandoned I := false
  avail_ready I E := false
}

/-! ## Inputs (`mod:mvba`) -/

/- `propose(B_i)` — sets the input and begins participation. Once per
validator; `Valid B_i` is the caller's obligation, not checked here. -/
action propose (i : node) (e : value) {
  require ∀ E, ¬ input i E
  require ¬ abandoned i
  input i e := true
}

/- `abandon()` — halts this validator's MVBA sending: every honest send
below requires `¬ abandoned i`. -/
action abandon (i : node) {
  abandoned i := true
}

/-! ## Honest protocol steps (`alg:mvba`–`alg:mvba-cont2`, one view) -/

/- "Upon entering view 1": the leader proposes its own input
(`x ← B_i`, `J ← ⊥`) and broadcasts `⟨Pre-Prepare, s, 1, x, ⊥, σ_l⟩`. -/
action leader_propose (e : value) {
  require ¬ is_byz leader
  require input leader e
  require ¬ abandoned leader
  msg_preprepare leader e := true
}

/- The `Pre-Prepare` handler, `line:mvba:pp-guard` at `v = 1`: the sender
is the leader, `x` is valid, `J = ⊥`, and `1 > lastVotedView_i` (i.e.
`¬ voted i`). Then `HandleProposal` (`line:mvba:hp-record`,
`line:mvba:hp-prepare`): record `x_v`, raise `lastVotedView_i`, and send
the `Prepare` on the entry vector. -/
action handle_preprepare (i : node) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require msg_preprepare leader e
  require valid e
  require ¬ voted i
  accepted i e := true
  voted i := true
  msg_prepare i e := true
}

/- Certificate assembly: `2f+1` `Prepare` signatures on `e` form
`prepareQC_{s,1}` on `e` (`line:mvba:tfp-guard`'s quorum condition,
materialised as a network fact). -/
action form_prepqc (e : value) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_prepare r e
  msg_prepqc e := true
}

/- `TryFormPrepQC`'s local half (`line:mvba:tfp-guard`,
`line:mvba:tfp-store`): a validator adopts the certificate of the vector
*it prepared* (`entries(x_v) = e`) as `PrepQC_i`, once (`PrepQC_i = ⊥`;
no lower view exists here). The `¬ timedOut_i` conjunct has no timeout
path to refer to in this spike. -/
action adopt_prepqc (i : node) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require msg_prepqc e
  require accepted i e
  require ∀ E, ¬ local_prepqc i E
  local_prepqc i e := true
}

/- The environment supplies `i`'s availability shares for `e`
(`AvailReady_i` becomes true; `lem:avail-progress` is where the supplement
bounds when). Unguarded: safety-neutral, and the liveness hook (F-avail). -/
action become_avail_ready (i : node) (e : value) {
  avail_ready i e := true
}

/- `TrySendCommit` (`line:mvba:commit-send`): `x_v ≠ ⊥`, `entries(x_v) = e`,
`PrepQC_i` is of the current view and on `e`, `¬ commitSent_i`,
`AvailReady_i(x_v)`. -/
action send_commit (i : node) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require accepted i e
  require local_prepqc i e
  require ¬ commit_sent i
  require avail_ready i e
  commit_sent i := true
  msg_commit i e := true
}

/- Certificate assembly: `2f+1` `Commit` signatures on `e` form the
`CommitQC` on `e` (`TryFormCommitQC`'s quorum condition, materialised). -/
action form_commitqc (e : value) (q : nodeset) {
  require nset.supermajority q
  require ∀ r, nset.member r q → msg_commit r e
  msg_commitqc e := true
}

/- `decide(x, CommitQC)`: `TryFormCommitQC`, the transferred-certificate
handler (`line:mvba:qc-decide`) and `TryDecide` (`line:mvba:td-decide`)
collapse into one action, since with the value the entry vector
`Recover(e)` is the identity. Once per validator (`DecidedQC_i = ⊥`):
integrity by construction. -/
action decide (i : node) (e : value) {
  require ¬ is_byz i
  require ∃ E, input i E
  require ¬ abandoned i
  require msg_commitqc e
  require ∀ E, ¬ decided i E
  decided i e := true
}

/-! ## Byzantine behaviour — arbitrary signatures, no forged certificates -/

action byz_preprepare (l : node) (e : value) {
  require is_byz l
  msg_preprepare l e := true
}

action byz_prepare (r : node) (e : value) {
  require is_byz r
  msg_prepare r e := true
}

action byz_commit (r : node) (e : value) {
  require is_byz r
  msg_commit r e := true
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

/-! ## Invariants — the supplement's lemmas, one view

`docs/MvbaPlan.md` §2.6 has the map; the rows exercised here are
`lem:vote-uniqueness`, `lem:commit-provenance`, `lem:cert-uniqueness`. -/

/- `lem:vote-uniqueness` (i): an honest `Prepare` is on the vector the
sender accepted, and an honest validator accepts one vector — its
`lastVotedView_i` was raised when it did (`line:mvba:hp-record`), and the
`Pre-Prepare` guard refuses a second proposal in the view. -/
invariant [honest_prepare_accepted]
  ∀ (R : node) (E : value), ¬ is_byz R → msg_prepare R E → accepted R E

invariant [accepted_implies_voted]
  ∀ (R : node) (E : value), ¬ is_byz R → accepted R E → voted R

invariant [accepted_unique]
  ∀ (R : node) (E E' : value),
    ¬ is_byz R → accepted R E → accepted R E' → E = E'

/- `lem:external-validity`'s premise: an honest validator accepts only a
valid vector (`line:mvba:pp-guard`). -/
invariant [accepted_valid]
  ∀ (R : node) (E : value), ¬ is_byz R → accepted R E → valid E

/- `lem:commit-provenance`: an honest `Commit` on `e` was sent with
`entries(x_v) = e` and `PrepQC_i` of this view on `e`. -/
invariant [honest_commit_accepted]
  ∀ (R : node) (E : value),
    ¬ is_byz R → msg_commit R E → accepted R E ∧ local_prepqc R E

/- `rem:lock-monotonicity`'s base: a held certificate is a network
certificate. -/
invariant [local_prepqc_backed]
  ∀ (R : node) (E : value), ¬ is_byz R → local_prepqc R E → msg_prepqc E

/- Certificate backing (the lifted assembly guards): every certificate has
its `2f+1` signatures on the wire. -/
invariant [prepqc_backed]
  ∀ (E : value), msg_prepqc E →
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_prepare r E

invariant [commitqc_backed]
  ∀ (E : value), msg_commitqc E →
    ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → msg_commit r E

/- `lem:cert-uniqueness`: all prepare certificates of the view are on one
vector, and likewise all commit certificates — the two-supermajority
intersection through an honest common signer and vote uniqueness. -/
invariant [prepqc_unique]
  ∀ (E E' : value), msg_prepqc E → msg_prepqc E' → E = E'

invariant [commitqc_unique]
  ∀ (E E' : value), msg_commitqc E → msg_commitqc E' → E = E'

/- A commit certificate is on a valid vector: an honest signer accepted it
(`lem:external-validity`'s argument, at the assembly point). -/
invariant [commitqc_valid]
  ∀ (E : value), msg_commitqc E → valid E

/- Lifted `decide` guard: every honest decision is certificate-backed. -/
invariant [decided_backed]
  ∀ (I : node) (E : value), ¬ is_byz I → decided I E → msg_commitqc E

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

#gen_spec

/-! ## Non-vacuity witnesses (`docs/MvbaPlan.md` §4 item 1)

`sat` verdicts here are trusted, deliberately: a wrong model can only make
a non-vacuity check vacuous, never a safety claim wrong
(`docs/Architecture.md` §4 item 6). Traces come last in the file and no
`set_option … in` follows a trace block (the parser rule in `CLAUDE.md`). -/

-- A decision in view 1: the leader proposes, a prepare certificate and a
-- commit certificate form, a correct validator decides.
sat trace {
  propose
  leader_propose
  handle_preprepare
  form_prepqc
  adopt_prepqc
  become_avail_ready
  send_commit
  form_commitqc
  decide
  assert (∃ i e, ¬ is_byz i ∧ decided i e)
}

-- A Byzantine leader equivocates: two correct validators accept different
-- proposals, so neither vector can reach a prepare certificate from
-- honest signatures alone — no certificate has formed.
sat trace {
  byz_preprepare
  byz_preprepare
  propose
  propose
  handle_preprepare
  handle_preprepare
  assert (is_byz leader ∧
    ∃ i j e e', ¬ is_byz i ∧ ¬ is_byz j ∧ ¬ e = e' ∧
      accepted i e ∧ accepted j e' ∧ ∀ E, ¬ msg_prepqc E)
}

end Mvba
