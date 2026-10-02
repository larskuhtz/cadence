import Cadence.Interfaces

/-! Spike 13 (2026-10-02, R15 design): the meta-block representation in the
MVBA contract, consumed the way Chorus will consume it — before paying the
Mvba and Chorus cold re-solves.

The contract shape is the one `docs/PaperAlignment.md` §8.1 proposes for
`MVBASafety`, reduced to the fields that matter here and declared locally
(`Spike13.MetaMVBASafety`) so that `Cadence/Interfaces.lean` stays untouched
until the design is agreed:

* the value is the **representation** (`value`), and the class has a
  first-order projection `entries : value → entryvec`;
* Agreement and Integrity are stated over `entries`;
* the class takes the system's quorum family as a parameter
  (`B : ByzNodeSet party pset`), which the availability field needs, and is
  instantiated with the consumer's own `nset`;
* the certificate-level availability field quantifies over a quorum and a
  representation, and is withheld from the solver with `veil_smt_ignore`.

What has to hold, and is checked below:

1. the class instantiates with `nset` passed explicitly, as
   `Cadence.ByzNodeSetCounting` already is in Chorus;
2. a consumer can read the projection inside its guards and invariants,
   `mval_pos (mvba.entries v) j m`, and the tie invariants stay inductive;
3. record uniqueness and exclusion follow from `agreement` **over entries**,
   through the ties, exactly as spike 09 showed for the old value;
4. a per-validator commit vote that takes the validator's own decided
   representation as a parameter and waits only under that representation's
   `FallbackQC` entries (`mval_fb v j`) adds no proof obligation;
5. the withheld field is reported once and does not reach the solver.

Expected: `exit 0`, all `✅`. -/

set_option linter.unusedVariables false

namespace Spike13

/-- The proposed fragment, reduced. -/
class MetaMVBASafety (party value entryvec message state pset : Type)
    (B : ByzNodeSet party pset) (byz : party → Prop)
    extends TransitionSystemSafety state where
  Valid : value → Prop
  entries : value → entryvec
  propose : state → party → value → state → Prop
  propose_trans : ∀ st p v st', propose st p v st' → trans st st'
  decided : state → party → value → Prop
  availReady : state → party → value → Prop
  decided_mono : ∀ st st' p v, trans st st' → decided st p v → decided st' p v
  init_decided : ∀ st p v, init st → ¬ decided st p v
  agreement : ∀ st, reachable st → ∀ p q v v',
    ¬ byz p → ¬ byz q → decided st p v → decided st q v' → entries v = entries v'
  integrity : ∀ st, reachable st → ∀ p v v',
    ¬ byz p → decided st p v → decided st p v' → entries v = entries v'
  external_validity : ∀ st, reachable st → ∀ p v, ¬ byz p → decided st p v → Valid v
  certifies : state → message → entryvec → Prop
  certified_available : ∀ st, reachable st → ∀ c e, certifies st c e →
    ∃ q, B.supermajority q ∧ ∀ p, B.member p q = true → ¬ byz p →
      ∃ v, entries v = e ∧ Valid v ∧ availReady st p v

attribute [veil_smt_ignore] MetaMVBASafety.certified_available

end Spike13

veil module MetaConsumer

type node
type nodeset
type merkle_root
type mstate
type mvalue
type mentries
type mmsg

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet

immutable relation is_proposer (j : node)
-- The entry-vector projections, now over the entry vector itself.
immutable relation mval_pos (e : mentries) (j : node) (m : merkle_root)
immutable relation mval_neg (e : mentries) (j : node)
-- The representation's certificate kind of a positive entry.
immutable relation mval_fb (v : mvalue) (j : node)

instantiate mvba : Spike13.MetaMVBASafety node mvalue mentries mmsg mstate nodeset nset
  (fun i => nset.is_byz i = true)

immutable individual mvba_init_state : mstate
individual mvba_st : mstate
relation mvba_decided_pos (j : node) (m : merkle_root)
relation mvba_decided_neg (j : node)
relation vq_pos (j : node) (m : merkle_root)
relation fbq_pos (j : node) (m : merkle_root)
relation cert_neg (j : node)
individual fbcert : Bool
relation chunk (i : node) (j : node) (m : merkle_root)
relation fbcommit (i : node)

#gen_state

assumption [mvba_init] mvba.init mvba_init_state
assumption [mval_pos_functional]
  ∀ (E : mentries) (J : node) (M1 M2 : merkle_root), mval_pos E J M1 → mval_pos E J M2 → M1 = M2
assumption [mval_pos_neg_excl]
  ∀ (E : mentries) (J : node) (M : merkle_root), ¬ (mval_pos E J M ∧ mval_neg E J)

after_init {
  mvba_st := mvba_init_state
  mvba_decided_pos J M := false
  mvba_decided_neg J := false
  vq_pos J M := false
  fbq_pos J M := false
  cert_neg J := false
  fbcert := false
  chunk I J M := false
  fbcommit I := false
}

action net_vq (j : node) (m : merkle_root) { vq_pos j m := true }
action net_fbq (j : node) (m : merkle_root) { fbq_pos j m := true }
action net_neg (j : node) { cert_neg j := true }
action net_fbcert { fbcert := true }
action net_chunk (i : node) (j : node) (m : merkle_root) { chunk i j m := true }

action mvba_step (mvba_next : mstate) {
  require mvba.step mvba_st mvba_next
  mvba_st := mvba_next
}

-- The driven input, with `Valid B_i` checked per certificate kind.
action mvba_propose (i : node) (v : mvalue) (mvba_next : mstate) {
  require ¬ is_byz i
  require ∀ J M, mval_pos (mvba.entries v) J M →
    (¬ mval_fb v J ∧ vq_pos J M) ∨ (mval_fb v J ∧ fbq_pos J M ∧ fbcert)
  require ∀ J, mval_neg (mvba.entries v) J → cert_neg J
  require mvba.propose mvba_st i v mvba_next
  mvba_st := mvba_next
}

-- The decision handler: `i`'s own representation `v`, the bridge per kind.
action on_mvba_decide_pos (i : node) (j : node) (m : merkle_root) (v : mvalue) {
  require ¬ is_byz i
  require is_proposer j
  require mvba.decided mvba_st i v
  require mval_pos (mvba.entries v) j m
  require (¬ mval_fb v j ∧ vq_pos j m) ∨ (mval_fb v j ∧ fbq_pos j m ∧ fbcert)
  mvba_decided_pos j m := true
}

action on_mvba_decide_neg (i : node) (j : node) (v : mvalue) {
  require ¬ is_byz i
  require is_proposer j
  require mvba.decided mvba_st i v
  require mval_neg (mvba.entries v) j
  require cert_neg j
  mvba_decided_neg j := true
}

-- The commit vote: wait exactly under the FallbackQC entries of `i`'s own `v`.
action cast_fb_commit (i : node) (v : mvalue) {
  require ¬ is_byz i
  require mvba.decided mvba_st i v
  require ∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → chunk i J M
  fbcommit i := true
}

invariant [mvba_reachable] mvba.reachable mvba_st

invariant [mvba_decided_pos_tied]
  ∀ (J : node) (M : merkle_root), mvba_decided_pos J M →
    ∃ I V, ¬ is_byz I ∧ mvba.decided mvba_st I V ∧ mval_pos (mvba.entries V) J M
invariant [mvba_decided_neg_tied]
  ∀ (J : node), mvba_decided_neg J →
    ∃ I V, ¬ is_byz I ∧ mvba.decided mvba_st I V ∧ mval_neg (mvba.entries V) J

invariant [mvba_decided_pos_unique]
  ∀ (J : node) (M1 M2 : merkle_root),
    mvba_decided_pos J M1 ∧ mvba_decided_pos J M2 → M1 = M2
invariant [mvba_decided_pos_neg_excl]
  ∀ (J : node) (M : merkle_root), ¬ (mvba_decided_pos J M ∧ mvba_decided_neg J)
-- The per-kind bridge still yields the old disjunctive backing.
invariant [mvba_decided_pos_backed]
  ∀ (J : node) (M : merkle_root), mvba_decided_pos J M → vq_pos J M ∨ (fbq_pos J M ∧ fbcert)

set_option veil.smt.trust false
#gen_spec
#check_invariants

end MetaConsumer
