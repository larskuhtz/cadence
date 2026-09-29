import Cadence.Chorus.Liveness
import Cadence.System

/-! # Spike 12 — at `chorusTheory`, one non-proposer makes every vector uncertifiable

`docs/Liveness.md` §4.6, Finding 1. `System.lean`'s `chorusTheory` sets
`mval_neg v j := v j = none` for every node, and `Chorus.Certified` (verbatim
`mvba_propose`'s validity guards) requires `is_proposer J` of every `J` with an
entry — so a non-proposer `j0` has an entry in every `v`, and no vector is
certified: `mvba_propose` is disabled in every state at the system's
instantiation. Expected today: `exit 0` (the lemma proves). Once Finding 1's
fix lands (`mval_neg v j := v j = none ∧ is_proposer j`) this spike must stop
proving; delete it then, or turn it into the positive witness. -/

open Classical

/-- At `chorusTheory`, if some validator is not a proposer, no vector is
`Certified` — so `mvba_propose` (whose validity guards are `Certified`
verbatim) is never enabled. -/
example {slot node nodeset merkle_root view Phase PathChoice : Type}
    [Inhabited slot] [Inhabited node] [Inhabited nodeset] [Inhabited merkle_root] [Inhabited view]
    [Inhabited Phase] [Inhabited PathChoice]
    [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
    [cnt : Cadence.ByzNodeSetCounting node nodeset nset]
    [Phase_Enum : Chorus.Phase_EnumClass Phase] [PathChoice_Enum : Chorus.PathChoice_EnumClass PathChoice]
    (is_proposer : node → Bool) (well_encoded : merkle_root → Bool)
    (s0 : Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
    {thM : Mvba.Theory node nodeset (node → Option merkle_root) view}
    (st : Chorus.State (Chorus.FieldAbstractType slot node nodeset merkle_root
      (Mvba.State (Mvba.FieldAbstractType node nodeset (node → Option merkle_root) view))
      (node → Option merkle_root) (Mvba.Msg view (node → Option merkle_root)) Phase PathChoice))
    (j0 : node) (hj0 : is_proposer j0 = false) (v : node → Option merkle_root) :
    ¬ Chorus.Certified (thS := Cadence.chorusTheory (slot := slot) (Phase := Phase) (PathChoice := PathChoice)
        is_proposer well_encoded s0) (thM := thM) st v := by
  rintro ⟨hpos, hneg, -⟩
  cases h : v j0 with
  | none =>
    have := (hneg j0 (by simp [Cadence.chorusTheory, h])).1
    simp [Cadence.chorusTheory, hj0] at this
  | some m =>
    have := (hpos j0 m (by simp [Cadence.chorusTheory, h])).1
    simp [Cadence.chorusTheory, hj0] at this
