import Cadence.Interfaces

/-! Spike 10 (2026-09-10): the **negative control** for the MVBA consumer
encoding of `09_mvba_consumer_ok.lean`.

That spike ties every per-proposer record of the consumer to a correct
validator's decision on the abstract MVBA state (`[mvba_decided_pos_tied]`,
`[mvba_decided_neg_tied]`) and discharges the records' uniqueness and pos/neg
exclusion from the class's `agreement` through those ties.

This file is that module with **the two tie invariants deleted** and nothing
else changed — the agreement guards Chorus's old oracle actions carried are
absent here too. If uniqueness still passed, the encoding would be proving
itself for some other reason (a guard, the bridge) and spike 09 would be
vacuous. So the expected result is a counterexample at exactly the actions
that *write* a record: without the ties, nothing links an existing record to
a decision, so a second decision handler may record a different root.

**Expected: `exit 1`, and exactly three `❌`**: `mvba_decided_pos_unique`
under `on_mvba_decide_pos`, and `mvba_decided_pos_neg_excl` under both
`on_mvba_decide_pos` and `on_mvba_decide_neg`. Every other cell still passes
— each assumes the clump at the pre-state, and no other action writes a
record — which is the shape of an inductive counterexample. In particular the
bridge `require`s (`cert_pos`, `cert_neg`) do not rescue either invariant:
the agreement content comes from the class and the ties, not from the
certificate check. Read the exit code from `scratch.sh` itself. -/

set_option linter.unusedVariables false

veil module MvbaConsumerNoTie

type node
type nodeset
type merkle_root
-- The MVBA's abstract state, value and message sorts.
type mstate
type mvalue
type mmsg

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet

immutable relation is_proposer (j : node)
-- The projections of an entry vector: `v j = some m` / `v j = none`.
immutable relation mval_pos (v : mvalue) (j : node) (m : merkle_root)
immutable relation mval_neg (v : mvalue) (j : node)

instantiate mvba : MVBASafety node mvalue mmsg mstate (fun i => nset.is_byz i = true)

-- The instance's initial state: per-execution data, constrained below
-- (an `assumption` may mention immutable components only).
immutable individual mvba_init_state : mstate
-- The abstract MVBA state the consumer holds (oracle state).
individual mvba_st : mstate
-- The consumer's per-proposer records of the decision.
relation mvba_decided_pos (j : node) (m : merkle_root)
relation mvba_decided_neg (j : node)
-- A stand-in for the consumer's certificate check (the bridge).
relation cert_pos (j : node) (m : merkle_root)
relation cert_neg (j : node)

#gen_state

assumption [mvba_init] mvba.init mvba_init_state
-- The entry-vector projections: at most one root per entry, and an entry is
-- not both positive and negative.
assumption [mval_pos_functional]
  ∀ (V : mvalue) (J : node) (M1 M2 : merkle_root), mval_pos V J M1 → mval_pos V J M2 → M1 = M2
assumption [mval_pos_neg_excl]
  ∀ (V : mvalue) (J : node) (M : merkle_root), ¬ (mval_pos V J M ∧ mval_neg V J)

after_init {
  mvba_st := mvba_init_state
  mvba_decided_pos J M := false
  mvba_decided_neg J := false
  cert_pos J M := false
  cert_neg J := false
}

-- The environment produces certificates (stands in for Chorus's network).
action certify_pos (j : node) (m : merkle_root) {
  cert_pos j m := true
}
action certify_neg (j : node) {
  cert_neg j := true
}

-- The oracle step: any internal transition the contract allows.
action mvba_step (mvba_next : mstate) {
  require mvba.step mvba_st mvba_next
  mvba_st := mvba_next
}

-- The driven input: a correct validator proposes a certified vector.
action mvba_propose (i : node) (v : mvalue) (mvba_next : mstate) {
  require ¬ is_byz i
  require ∀ J M, mval_pos v J M → cert_pos J M
  require ∀ J, mval_neg v J → cert_neg J
  require mvba.propose mvba_st i v mvba_next
  mvba_st := mvba_next
}

-- The per-entry decision handler: a correct validator has decided `v`, whose
-- entry for proposer `j` is `m`, and the entry's certificate verifies.
action on_mvba_decide_pos (i : node) (j : node) (m : merkle_root) (v : mvalue) {
  require ¬ is_byz i
  require is_proposer j
  require mvba.decided mvba_st i v
  require mval_pos v j m
  -- the bridge
  require cert_pos j m
  mvba_decided_pos j m := true
}

action on_mvba_decide_neg (i : node) (j : node) (v : mvalue) {
  require ¬ is_byz i
  require is_proposer j
  require mvba.decided mvba_st i v
  require mval_neg v j
  -- the bridge
  require cert_neg j
  mvba_decided_neg j := true
}

-- Reachability of the abstract state: `[mvba_init]` and the closure axioms.
invariant [mvba_reachable] mvba.reachable mvba_st

-- The tie invariants deliberately REMOVED — this is the control.

-- **What the class buys**: uniqueness and exclusion of the consumer's records,
-- from `mvba.agreement` — which, without the ties, is out of reach.
invariant [mvba_decided_pos_unique]
  ∀ (J : node) (M1 M2 : merkle_root),
    mvba_decided_pos J M1 ∧ mvba_decided_pos J M2 → M1 = M2
invariant [mvba_decided_pos_neg_excl]
  ∀ (J : node) (M : merkle_root), ¬ (mvba_decided_pos J M ∧ mvba_decided_neg J)

#gen_spec
#check_invariants

end MvbaConsumerNoTie
