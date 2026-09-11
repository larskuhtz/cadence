import Cadence.Interfaces

/-! Spike 09 (2026-09-10): a toy consumer of the **real** `MVBASafety` class of
`Cadence/Interfaces.lean`, in the shape `docs/MvbaPlan.md` §6 prescribes for
Chorus — before paying the Chorus cold re-solve.

Chorus consumes the MVBA per proposer: its records are `mvba_decided_pos j m`
/ `mvba_decided_neg j`, while the contract's value is the whole entry vector
`node → Option merkle_root`. A Veil module needs a first-order sort for it, so
the value is an opaque sort `mvalue` read through two **immutable projection
relations** `mval_pos v j m` / `mval_neg v j`, constrained by two assumptions
— functional in `m`, and mutually exclusive — which the system composition
instantiates at `v j = some m` / `v j = none`. What has to hold for the
encoding to work, and is checked below:

1. `MVBASafety node mvalue mmsg mstate byz` is `instantiate`-able with the
   `byz` argument a *lambda* over an earlier instantiated parameter's
   projection (`fun i => nset.is_byz i = true` — spike 05 established the
   projection form), and its parent skeleton destructures for the solver;
2. the oracle step `mvba_step` (`mvba.step`) and the driven input
   `mvba_propose` (`mvba.propose`) keep `[mvba_reachable]` inductive through
   the closure axioms, and `decided_mono` along `trans` keeps the **tie
   invariant** inductive — every positive record is tied to some correct
   validator's decision through `mval_pos`;
3. the consumer's **uniqueness** of its records (`mvba_decided_pos_unique`),
   which Chorus's old oracle actions *enforced by a guard*, is now
   **discharged from `mvba.agreement`** at the reachable abstract state plus
   the functionality of `mval_pos` — no agreement guard anywhere;
4. the pos/neg exclusion likewise, from `agreement` plus the exclusivity of
   `mval_pos`/`mval_neg`.

Expected: `exit 0`, all `✅`. The negative control is
`10_mvba_consumer_no_tie.lean`: the same module with the tie invariants
deleted, where uniqueness must fail at exactly the handler.

Note the handler's one `require` on the consumer's *own* network relation
(`cert_pos j m`): in Chorus this is the certificate check of the decided
entry against the network — the **one stated bridge**, the MVBA counterpart of
the Conductor's ACS median bridge — and it is deliberately not a class
property (`docs/MvbaPlan.md` §1.1). Here it is a stand-in relation, so the
spike shows the bridge is *inert* for the agreement argument: uniqueness
comes from the class, not from the bridge. -/

set_option linter.unusedVariables false

veil module MvbaConsumer

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

-- **The tie invariants.** Every record is the projection of some correct
-- validator's decision. Inductive under `mvba_step`/`mvba_propose` by
-- `decided_mono` along `trans`.
invariant [mvba_decided_pos_tied]
  ∀ (J : node) (M : merkle_root), mvba_decided_pos J M →
    ∃ I V, ¬ is_byz I ∧ mvba.decided mvba_st I V ∧ mval_pos V J M
invariant [mvba_decided_neg_tied]
  ∀ (J : node), mvba_decided_neg J →
    ∃ I V, ¬ is_byz I ∧ mvba.decided mvba_st I V ∧ mval_neg V J

-- **What the class buys**: uniqueness and exclusion of the consumer's records,
-- from `mvba.agreement` at the reachable abstract state through the ties.
invariant [mvba_decided_pos_unique]
  ∀ (J : node) (M1 M2 : merkle_root),
    mvba_decided_pos J M1 ∧ mvba_decided_pos J M2 → M1 = M2
invariant [mvba_decided_pos_neg_excl]
  ∀ (J : node) (M : merkle_root), ¬ (mvba_decided_pos J M ∧ mvba_decided_neg J)

#gen_spec
#check_invariants

end MvbaConsumer
