import Veil
import Cadence.Tooling

/-! # FallbackReceiptPreFix — the pre-fix receipt rules, mechanically refuted

Companion to [`FallbackReceipt.lean`](../FallbackReceipt.lean) (read its
header first): the *pre-fix* fallback receipt/propose layer — the rules
`alg:fallback` carried **before** the 2026-07-07 fix — with the §7.2
finding (`docs/ChorusDesign.md` §7.2) reproduced mechanically: the paper's claim
"by the rules above, every `Ev(pid)` is a FastQC, FallbackQC, or
EquivCert" is stated as the invariant `prefix_valid_by_construction`,
and the concrete model checker **refutes it** with a reachable
counterexample — the EquivCert-harvest-omission scenario.

The pre-fix rules differ from the shipped ones in exactly two ways:

1. **Acceptance** (pre-restriction): a vote entry may be *any* valid
   evidence — in particular a carried **EquivCert** — not only a FastQC
   or the sender's own signed entry. Modelled by the additional
   `carried_equiv` wire kind, admitted by `accept_vote`. Only Byzantine
   senders emit it: a pre-fix *honest* sender broadcasts its `Ev`
   values, and the pre-fix harvest never places an EquivCert into `Ev`
   — which is the bug — so honest votes carry FastQCs or own entries
   only. (Carried FallbackQCs are omitted: they only *add* certified
   evidence and play no role in the finding; restricting the adversary
   only shrinks the reachable set, so a violation found here is a
   fortiori a violation of the full pre-fix model.)
2. **Propose** (pre-guard): `|M_i| ≥ 2f+1` fires the once-only propose
   *unconditionally* — there is no every-entry-certified guard; that
   guard's absence, combined with the harvest rules covering only
   FastQCs (and FallbackQCs), is the §7.2 liveness bug.

The refuted invariant quantifies over what the pre-fix harvest and the
standing formation rules can actually produce for `Ev(p)`: a harvested
FastQC, a locally-formed EquivCert (two conflicting positive signed
entries in `M_i`), or a locally-formed FallbackQC (`f+1` matching
entries in `M_i`). A carried-but-unharvested EquivCert contributes
nothing — exactly the omission. The model checker's counterexample is
the §7.2 scenario (`n = 4`, `f = 1`): at `|M_i| = 3 = 2f+1` with one
bare positive entry, one bare negative entry, and one vote carrying an
EquivCert, no case applies, yet propose fires — the proposed meta-block
entry is a bare signed entry, not a valid fallback meta-block.

This module carries **no** abstract SMT leg: its purpose is the
refutation, and reachability of the violation is a concrete, exhaustive
fact. -/

veil module FallbackReceiptPreFix

type node
type nodeset
type proposer
type merkle_root

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet

/-! ## Wire state — as in `FallbackReceipt.lean`, plus `carried_equiv` -/

relation carried_fastqc (r : node) (p : proposer) (m : merkle_root)
relation carried_pos (r : node) (p : proposer) (m : merkle_root)
relation carried_neg (r : node) (p : proposer)
-- Pre-fix only: `r`'s vote carries an EquivCert for `p` (roots elided —
-- the certificate is receiver-verified; its content plays no role
-- because the pre-fix rules never consume it).
relation carried_equiv (r : node) (p : proposer)

relation accepted (r : node)

individual proposed : Bool

#gen_state

/-! ## Derived state — the pre-fix harvest and formation rules -/

-- Harvest (`the two harvest loops`): FastQCs only. NO rule harvests a
-- carried EquivCert — the §7.2 omission.
ghost relation ev_fastqc (p : proposer) (m : merkle_root) :=
  ∃ r, accepted r ∧ carried_fastqc r p m

ghost relation received_supermajority :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → accepted r

-- Standing local formation: EquivCert from two conflicting positive
-- signed entries in `M_i` …
ghost relation equiv_available (p : proposer) :=
  ∃ r1 r2 m1 m2, m1 ≠ m2 ∧
    accepted r1 ∧ carried_pos r1 p m1 ∧
    accepted r2 ∧ carried_pos r2 p m2

-- … and FallbackQCs from `f+1` matching signed entries in `M_i`.
ghost relation fbqc_pos_available (p : proposer) (m : merkle_root) :=
  ∃ q, nset.greater_than_third q ∧
    ∀ r, nset.member r q → accepted r ∧ carried_pos r p m

ghost relation fbqc_neg_available (p : proposer) :=
  ∃ q, nset.greater_than_third q ∧
    ∀ r, nset.member r q → accepted r ∧ carried_neg r p

/-! ## Initial state -/

after_init {
  carried_fastqc R P M := false
  carried_pos R P M := false
  carried_neg R P := false
  carried_equiv R P := false
  accepted R := false
  proposed := false
}

/-! ## Delivery — one entry kind per proposer per vote -/

action deliver_entry_fastqc (r : node) (p : proposer) (m : merkle_root) {
  require ¬ accepted r
  require ∀ M, ¬ carried_fastqc r p M
  require ∀ M, ¬ carried_pos r p M
  require ¬ carried_neg r p
  require ¬ carried_equiv r p
  carried_fastqc r p m := true
}

action deliver_entry_pos (r : node) (p : proposer) (m : merkle_root) {
  require ¬ accepted r
  require ∀ M, ¬ carried_fastqc r p M
  require ∀ M, ¬ carried_pos r p M
  require ¬ carried_neg r p
  require ¬ carried_equiv r p
  carried_pos r p m := true
}

action deliver_entry_neg (r : node) (p : proposer) {
  require ¬ accepted r
  require ∀ M, ¬ carried_fastqc r p M
  require ∀ M, ¬ carried_pos r p M
  require ¬ carried_neg r p
  require ¬ carried_equiv r p
  carried_neg r p := true
}

-- Pre-fix only, Byzantine senders only (see the header): a vote entry
-- that is a (valid, receiver-verified) EquivCert.
action deliver_entry_equiv (r : node) (p : proposer) {
  require nset.is_byz r
  require ¬ accepted r
  require ∀ M, ¬ carried_fastqc r p M
  require ∀ M, ¬ carried_pos r p M
  require ¬ carried_neg r p
  require ¬ carried_equiv r p
  carried_equiv r p := true
}

/- Pre-fix receipt: any valid evidence is accepted — including a carried
EquivCert (which the handler validates and then never harvests). -/
action accept_vote (r : node) {
  require ¬ accepted r
  require ∀ P, (∃ M, carried_fastqc r P M) ∨ (∃ M, carried_pos r P M) ∨
    carried_neg r P ∨ carried_equiv r P
  accepted r := true
}

/- Pre-fix propose: fires unconditionally at `|M_i| ≥ 2f+1`, once-only
(`mvbaInvoked`) — no certified-entries guard. -/
action propose (q : nodeset) {
  require ¬ proposed
  require nset.supermajority q
  require ∀ r, nset.member r q → accepted r
  proposed := true
}

/-! ## The refuted claim

The paper's pre-fix comment at the propose rule: "by the rules above,
every `Ev(pid)` is a FastQC, FallbackQC, or EquivCert" — i.e. at
propose time, for every proposer, the harvest/formation rules have
produced certified evidence. **This is false**: the model checker below
finds a reachable violation (the §7.2 counterexample). -/
invariant [prefix_valid_by_construction]
  proposed →
    ∀ (P : proposer),
      (∃ M, ev_fastqc P M) ∨ equiv_available P ∨
      (∃ M, fbqc_pos_available P M) ∨ fbqc_neg_available P

#gen_spec

/-! ## The mechanical refutation

Exhaustive exploration at `n = 4, f = 1` (Byzantine sender: node 0),
one proposer, two roots — the §7.2 counterexample size. Expected
outcome: **violation** of `prefix_valid_by_construction`, with a trace
of the shape: two honest bare entries that agree on neither root nor
sign (e.g. one positive for `ρ₁`, one negative), one Byzantine vote
carrying an EquivCert, all three accepted (`= 2f+1`), propose fires —
and no certificate is harvestable or formable for the proposer.

The same state is unreachable in `FallbackReceipt.lean`: its
`accept_vote` rejects the EquivCert-carrying vote (`line:fb-accept`),
so a third *entry-carrying* vote arrives instead and the two-class
pigeonhole closes every case (`build_totality_of_reachable` in
`FallbackReceipt/Totality.lean`,
kernel-checked for every `n = 3f+1`).

The `#guard_msgs` below pins the checker's counterexample — found
2026-07-07, and exactly the §7.2 scenario (node 0 is the Byzantine
sender ≘ "D", node 3 ≘ "A" with the positive entry for root 0 ≘ `ρ₁`,
node 1 ≘ "C" with the negative entry): the violation IS the expected
result of this file. If a change makes this build green, the pre-fix
bug has been masked — that is a regression of the refutation, not a
fix. -/

/--
error: ❌ Violation: safety_failure (violates: prefix_valid_by_construction)
  State 0 (via init):
    accepted = []
    carried_equiv = []
    carried_fastqc = []
    carried_neg = []
    carried_pos = []
    proposed = false
  State 1 (via deliver_entry_pos(m=0, p=0, r=1)):
    accepted = []
    carried_equiv = []
    carried_fastqc = []
    carried_neg = []
    carried_pos = [[1, [0, 0]]]
    proposed = false
  State 2 (via deliver_entry_neg(p=0, r=2)):
    accepted = []
    carried_equiv = []
    carried_fastqc = []
    carried_neg = [[2, 0]]
    carried_pos = [[1, [0, 0]]]
    proposed = false
  State 3 (via deliver_entry_equiv(p=0, r=0)):
    accepted = []
    carried_equiv = [[0, 0]]
    carried_fastqc = []
    carried_neg = [[2, 0]]
    carried_pos = [[1, [0, 0]]]
    proposed = false
  State 4 (via accept_vote(r=0)):
    accepted = [0]
    carried_equiv = [[0, 0]]
    carried_fastqc = []
    carried_neg = [[2, 0]]
    carried_pos = [[1, [0, 0]]]
    proposed = false
  State 5 (via accept_vote(r=1)):
    accepted = [0, 1]
    carried_equiv = [[0, 0]]
    carried_fastqc = []
    carried_neg = [[2, 0]]
    carried_pos = [[1, [0, 0]]]
    proposed = false
  State 6 (via accept_vote(r=2)):
    accepted = [0, 1, 2]
    carried_equiv = [[0, 0]]
    carried_fastqc = []
    carried_neg = [[2, 0]]
    carried_pos = [[1, [0, 0]]]
    proposed = false
  State 7 (via propose(q=[0, 1, 2])):
    accepted = [0, 1, 2]
    carried_equiv = [[0, 0]]
    carried_fastqc = []
    carried_neg = [[2, 0]]
    carried_pos = [[1, [0, 0]]]
    proposed = true
-/
#guard_msgs in
/- `sequential := true` is load-bearing for the pin above, not a performance
choice. By default `#model_check` splits the BFS frontier into `numSubTasks`
parallel sub-tasks and that count defaults to the machine's **core count**, so
*which* of the many reachable violating states is reported first depends on the
hardware: measured on this model, 4, 8, 12 and 14 cores each yield a different
(equally valid) counterexample, as does a different OS. The claim being pinned
is "a reachable state violates `prefix_valid_by_construction`" — the witness is
evidence, not the claim — but `#guard_msgs` compares the whole message, so the
pin would break on any machine but the one that recorded it. The sequential
search is deterministic, and verified identical on macOS/arm64 and Linux/arm64
at 4, 8 and 12 cores. -/
#model_check interpreted
  { node := Fin (3 * 1 + 1), nodeset := ByzNSet (3 * 1 + 1),
    proposer := Fin 1, merkle_root := Fin 2 } {} (sequential := true)

end FallbackReceiptPreFix
