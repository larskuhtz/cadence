import Veil.Frontend.Std

/-! # Quorum counting facts beyond intersection

Veil's `ByzNodeSet` states four facts about quorums, all of them about a
single shared member: two supermajorities share an honest member, an
`f+1`-set has an honest member, a supermajority is an `f+1`-set, and an
`f+1`-set is not empty. Chorus and the MVBA ranking need three facts that
are about a shared *subset* or a shared member of sets of different
strengths. They follow from counting, with at most `f` of `n ≥ 3f+1`
validators Byzantine:

* a supermajority contains an all-honest `f+1`-subset
  (`(2f+1) − f = f+1`);
* a supermajority and an `f+1`-set share a member, possibly a Byzantine one
  (`(2f+1) + (f+1) − (3f+1) = 1`);
* two supermajorities share an `f+1`-subset (`2(2f+1) − (3f+1) = f+1`).

This class states them over an abstract `ByzNodeSet`. Like the other quorum
requirements (`ByzNodeSetEnum`, `ByzNodeSetHonestQuorum` in
[`ByzQuorum.lean`](./ByzQuorum.lean)) it takes the `ByzNodeSet` as an
explicit parameter, so a theorem that uses the facts names them in its
statement. A Veil model consumes the class with `instantiate`, and then
every field is a hypothesis of the model's solver queries, exactly like the
fields of `ByzNodeSet` itself.

The class is proven, never assumed, wherever the validator set is concrete:
[`ByzQuorum.lean`](./ByzQuorum.lean) instantiates it for Veil's
`byzNodeSetFin` (`n = 3f+1`) and for `byzNodeSetFinGen` (every `n ≥ 3f+1`).

The field names differ from the `ByzNodeSet` fields of the same content that
the current Veil pin still declares (see `Cadence/Tooling.lean`), so the two
never shadow each other. -/

namespace Cadence

class ByzNodeSetCounting (node nset : Type) (B : ByzNodeSet node nset) : Prop where
  /-- A supermajority contains an `f+1`-subset of honest members:
  `(2f+1) − f = f+1`. -/
  honest_third_in_supermajority :
    ∀ (s : nset), B.supermajority s →
      ∃ (t : nset), B.greater_than_third t ∧
        ∀ (a : node), B.member a t → B.member a s ∧ ¬ B.is_byz a
  /-- A supermajority and an `f+1`-set share a member, possibly a Byzantine
  one: `(2f+1) + (f+1) − (3f+1) = 1`. -/
  supermajority_meets_third :
    ∀ (s1 s2 : nset), B.supermajority s1 → B.greater_than_third s2 →
      ∃ (a : node), B.member a s1 ∧ B.member a s2
  /-- Two supermajorities share an `f+1`-subset: `2(2f+1) − (3f+1) = f+1`.
  This strengthens `ByzNodeSet.supermajorities_intersect_in_honest`, which
  exposes a single honest member of the intersection. -/
  supermajorities_share_third :
    ∀ (s1 s2 : nset), B.supermajority s1 → B.supermajority s2 →
      ∃ (t : nset), B.greater_than_third t ∧
        ∀ (a : node), B.member a t → B.member a s1 ∧ B.member a s2

end Cadence
