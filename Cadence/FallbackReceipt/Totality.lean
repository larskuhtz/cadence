import Cadence.FallbackReceipt.Certify

/-! # FallbackReceiptTotality — the build-totality pigeonhole, all `n`

Companion to [`FallbackReceipt.lean`](../FallbackReceipt.lean) (read its
header first). This file proves, in plain Lean, the one claim of the
receipt/propose layer that is *not* SMT-dischargeable — **build
totality**, the per-validator two-class pigeonhole behind the paper's
"one of the three cases always applies, by counting"
(`line:fb-build-entry`) — for the concrete instance family
`byzNodeSetFin n f`: **every** `n = 3f+1`, every Byzantine set of size
`≤ f`, arbitrary `proposer` and `merkle_root` types. It supersedes the
earlier bounded `#model_check` argument at `n = 4`.

Structure (the three layers):

1. `two_cover` — the combinatorial content: a list of length `≥ 2f+1`
   covered by a predicate and its negation contains a sorted sublist of
   length `≥ f+1` inside one class. Pure `List` counting.
2. `build_totality_of_complete` — the state-level theorem: any state of
   the `FallbackReceipt` module satisfying the (SMT-proven, all-`n`)
   structural invariant `accepted_entries_complete` satisfies build
   totality. Generic in the state representation `χ`/`σ`/`ρ`; the
   quorum arithmetic is where `byzNodeSetFin` enters.
3. `build_totality_of_reachable` — the closure: the module-generic
   `FallbackReceipt.invariants_of_reachable` certificate
   (`#gen_composition`, `FallbackReceipt/Certify.lean`) applied at the
   concrete instance family — every reachable state satisfies the full
   invariant clump, hence build totality.

Trust base: **none beyond the Lean kernel.** The proof-file family runs
with `veil.smt.trust false` (proof reconstruction — the module is small
enough to afford it), so the persisted VC theorems are real,
kernel-checked proofs; layers 1–3 are ordinary Lean. The final theorem
depends on exactly `propext`, `Classical.choice`, `Quot.sound` — pinned
by the `#guard_msgs` axiom check at the end of this file.

Why the abstract statement is deliberately avoided: over an arbitrary
`ByzNodeSet` model, build totality is not provable — and very likely
not even true (nothing forces a nodeset *value* collecting exactly the
positive-signers of a quorum to exist; set comprehension is outside the
class's language). Restricting to the intended instance family is what
makes the claim both true and provable, and loses nothing: the
protocol's fault model *is* `n = 3f+1` with `≤ f` Byzantine nodes. -/

open Veil FallbackReceipt

/-! ## Layer 1 — the two-class pigeonhole over sorted node lists -/

/-- A sorted node list `l` of length `≥ 2f+1`, every member classified by
`p` or its negation, contains a sorted sublist of length `≥ f+1` lying
entirely inside one class. The `ByzNSet` packaging (sortedness) is
carried through `List.filter`. -/
theorem ByzNSet.two_cover {n f : Nat} (q : ByzNSet n)
    (hq : 2 * f + 1 ≤ q.val.length) (p : Fin n → Prop) :
    (∃ t : ByzNSet n, f + 1 ≤ t.val.length ∧
      ∀ a, a ∈ t.val → a ∈ q.val ∧ p a) ∨
    (∃ t : ByzNSet n, f + 1 ≤ t.val.length ∧
      ∀ a, a ∈ t.val → a ∈ q.val ∧ ¬ p a) := by
  classical
  obtain ⟨l, hsorted⟩ := q
  simp only at hq ⊢
  set pb : Fin n → Bool := fun a => decide (p a) with hpb
  have hsum := List.length_eq_countP_add_countP (l := l) pb
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at hsum
  by_cases hcase : f + 1 ≤ (l.filter pb).length
  · left
    refine ⟨⟨l.filter pb, List.Pairwise.filter _ hsorted⟩, hcase, ?_⟩
    intro a ha
    have := List.mem_filter.mp ha
    exact ⟨this.1, by simpa [hpb] using this.2⟩
  · right
    have hlen : f + 1 ≤ (l.filter (fun a => decide (¬ pb a = true))).length := by
      omega
    refine ⟨⟨l.filter (fun a => decide (¬ pb a = true)),
      List.Pairwise.filter _ hsorted⟩, hlen, ?_⟩
    intro a ha
    have := List.mem_filter.mp ha
    refine ⟨this.1, ?_⟩
    have hnb : ¬ pb a = true := of_decide_eq_true this.2
    simpa [hpb] using hnb

/-! ## Layer 2 — build totality from `accepted_entries_complete`

Stated over the generated module vocabulary, generic in the state
representation (`ρ`, `σ`, `χ` — instantiated by layer 3 at the
transition system's canonical representation), concrete in the quorum
arithmetic (`node := Fin n`, `nodeset := ByzNSet n`,
`nset := byzNodeSetFin n f hf is_byz hbyz`). -/

section Layer2

variable {ρ σ : Type} {proposer merkle_root : Type}
  [proposer_dec_eq : DecidableEq proposer] [proposer_inhabited : Inhabited proposer]
  [merkle_root_dec_eq : DecidableEq merkle_root] [merkle_root_inhabited : Inhabited merkle_root]
  (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
  [node_dec_eq : DecidableEq (Fin n)] [node_inhabited : Inhabited (Fin n)]
  [nodeset_dec_eq : DecidableEq (ByzNSet n)] [nodeset_inhabited : Inhabited (ByzNSet n)]
  {χ : State.Label → Type}
  [χ_rep : (__veil_f : State.Label) →
    Veil.FieldRepresentation
      (State.Label.toDomain (Fin n) (ByzNSet n) proposer merkle_root __veil_f)
      (State.Label.toCodomain (Fin n) (ByzNSet n) proposer merkle_root __veil_f) (χ __veil_f)]
  [χ_rep_lawful : ∀ (__veil_f : State.Label),
    Veil.LawfulFieldRepresentation
      (State.Label.toDomain (Fin n) (ByzNSet n) proposer merkle_root __veil_f)
      (State.Label.toCodomain (Fin n) (ByzNSet n) proposer merkle_root __veil_f) (χ __veil_f)
      (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ]
  [ρ_sub : IsSubReaderOf (Theory (Fin n) (ByzNSet n) proposer merkle_root) ρ]

/-- **Build totality** (the statement the demoted invariant carried): at
the propose trigger, one of the three build cases applies for every
proposer. -/
def BuildTotality (th : ρ) (st : σ) : Prop :=
  received_supermajority (nset := byzNodeSetFin n f hf is_byz hbyz) th st →
    ∀ (P : proposer),
      (∃ M, ev_fastqc (nset := byzNodeSetFin n f hf is_byz hbyz) P M th st) ∨
      equiv_available (nset := byzNodeSetFin n f hf is_byz hbyz) P th st ∨
      (∃ M, fbqc_pos_available (nset := byzNodeSetFin n f hf is_byz hbyz) P M th st) ∨
      fbqc_neg_available (nset := byzNodeSetFin n f hf is_byz hbyz) P th st

/-- Layer 2: `accepted_entries_complete` (SMT-proven inductive for all
`n`) implies build totality, in every state — no reachability needed. -/
theorem build_totality_of_complete (th : ρ) (st : σ)
    (hcomp : accepted_entries_complete
      (nset := byzNodeSetFin n f hf is_byz hbyz) th st) :
    BuildTotality n f hf is_byz hbyz th st := by
  classical
  intro hsm P
  -- Cases 1 and 2 need no state internals: they are goal disjuncts.
  by_cases hfq : ∃ M, ev_fastqc (nset := byzNodeSetFin n f hf is_byz hbyz) P M th st
  · exact Or.inl hfq
  by_cases heqv : equiv_available (nset := byzNodeSetFin n f hf is_byz hbyz) P th st
  · exact Or.inr (Or.inl heqv)
  refine Or.inr (Or.inr ?_)
  -- Case 3: the pigeonhole. Open the definitions and the state.
  unfold received_supermajority at hsm
  unfold ev_fastqc at hfq
  unfold equiv_available at heqv
  unfold accepted_entries_complete at hcomp
  unfold fbqc_pos_available fbqc_neg_available
  -- Structure eta turns the `casesOn` bodies into projections of
  -- `getFrom st`, uniformly across hypotheses and goal.
  dsimp only at hsm hfq heqv hcomp ⊢
  -- Quorum arithmetic of `byzNodeSetFin`; `member`/`supermajority`/
  -- `greater_than_third` become list facts.
  simp only [byzNodeSetFin, decide_eq_true_eq] at hsm ⊢
  push_neg at hfq heqv
  obtain ⟨q, hq_sup, hq_acc⟩ := hsm
  rcases ByzNSet.two_cover q hq_sup
      (fun r => ∃ M,
        Veil.FieldRepresentation.get
          (self := χ_rep State.Label.carried_pos)
          (getFrom (self := σ_sub) st).carried_pos r P M = true)
    with ⟨t, ht_len, ht_mem⟩ | ⟨t, ht_len, ht_mem⟩
  · -- All-positive class: the roots agree (¬case 2), giving a positive
    -- FallbackQC. `t` is nonempty (`f+1 ≥ 1`); pick the shared root.
    have ht_ne : t.val ≠ [] := by
      intro hnil
      rw [hnil] at ht_len
      simp at ht_len
    obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ ht_ne
    obtain ⟨hr0q, m0, hr0p⟩ := ht_mem r0 hr0
    refine Or.inl ⟨m0, t, ht_len, ?_⟩
    intro r hr
    obtain ⟨hrq, m, hrp⟩ := ht_mem r hr
    have hracc := hq_acc r hrq
    have hr0acc := hq_acc r0 hr0q
    have hm : m = m0 := by
      by_contra hne
      exact (heqv r r0 m m0 hne hracc hrp hr0acc) hr0p
    exact ⟨hracc, hm ▸ hrp⟩
  · -- All-negative class: entry completeness (`hcomp`) + no FastQC
    -- (¬case 1) + no positive entry (class) leaves the negative entry.
    refine Or.inr ⟨t, ht_len, ?_⟩
    intro r hr
    obtain ⟨hrq, hrnp⟩ := ht_mem r hr
    have hracc := hq_acc r hrq
    refine ⟨hracc, ?_⟩
    rcases hcomp r P hracc with ⟨M, hM⟩ | ⟨M, hM⟩ | hM
    · exact absurd hM (hfq M r hracc)
    · exact absurd ⟨M, hM⟩ hrnp
    · exact hM

end Layer2

/-! ## Layer 3 — closure over reachable states

Every reachable state of the generated transition system satisfies the
assembled `Invariants` clump — this is the module-generic
`FallbackReceipt.invariants_of_reachable` certificate emitted by
`#gen_composition` in
[`FallbackReceipt/Certify.lean`](./Certify.lean) from the
per-action preservation lemmas of the proof-file family
([`FallbackReceipt/Proofs/`](./Proofs)) — applied here at
the concrete instance family, and closed under layer 2 into build
totality. The script-generated induction and its `fvc%`/`triple_of_meets`
scaffolding that used to live in this file died with the move to the
verified-module file family (`docs/Architecture.md` §6): the composition is
emitted, and
kernel-checked, inside Veil. -/

namespace FallbackReceipt

section Layer3

variable {proposer merkle_root : Type}
  [proposer_inhabited : Inhabited proposer]
  [merkle_root_inhabited : Inhabited merkle_root]
  (n f : Nat) (hf : n = 3 * f + 1)
  (is_byz : Fin n → Prop) [DecidablePred is_byz]
  (hbyz : (List.ofFn (n := n) id |>.filter (fun i => decide (is_byz i))).length ≤ f)
  [node_inhabited : Inhabited (Fin n)]

/-- **Build totality holds in every reachable state** — for every
`n = 3f+1`, every Byzantine set of size `≤ f`, and arbitrary `proposer`
and `merkle_root` types. The general-`n` closure of the demoted
`build_totality` invariant: layer 2 applied to the
`accepted_entries_complete` conjunct of `invariants_of_reachable`. -/
theorem build_totality_of_reachable
    {th : Theory (Fin n) (ByzNSet n) proposer merkle_root}
    {st : State (FieldAbstractType (Fin n) (ByzNSet n) proposer merkle_root)}
    (h : (relationalTransitionSystem (Fin n) (ByzNSet n) proposer merkle_root
      (nset := (byzNodeSetFin n f hf is_byz hbyz))).reachable th st) :
    @BuildTotality
      (Theory (Fin n) (ByzNSet n) proposer merkle_root)
      (State (FieldAbstractType (Fin n) (ByzNSet n) proposer merkle_root))
      proposer merkle_root
      (fun a b => Classical.propDecidable (a = b)) proposer_inhabited
      (fun a b => Classical.propDecidable (a = b)) merkle_root_inhabited
      n f hf is_byz _ hbyz
      (fun a b => Classical.propDecidable (a = b)) node_inhabited
      (fun a b => Classical.propDecidable (a = b)) inferInstance
      (FieldAbstractType (Fin n) (ByzNSet n) proposer merkle_root)
      (fun ff => @instAbstractFieldRepresentation (Fin n) (ByzNSet n) proposer merkle_root
        (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
        (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) ff)
      (fun ff => @instLawfulAbstractFieldRepresentation (Fin n) (ByzNSet n) proposer merkle_root
        (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
        (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) ff)
      instIsSubStateOfRefl instIsSubReaderOfRefl th st := by
  have hinv := invariants_of_reachable (nset := byzNodeSetFin n f hf is_byz hbyz) h
  exact @build_totality_of_complete
    (Theory (Fin n) (ByzNSet n) proposer merkle_root)
    (State (FieldAbstractType (Fin n) (ByzNSet n) proposer merkle_root))
    proposer merkle_root
    (fun a b => Classical.propDecidable (a = b)) proposer_inhabited
    (fun a b => Classical.propDecidable (a = b)) merkle_root_inhabited
    n f hf is_byz _ hbyz
    (fun a b => Classical.propDecidable (a = b)) node_inhabited
    (fun a b => Classical.propDecidable (a = b)) inferInstance
    (FieldAbstractType (Fin n) (ByzNSet n) proposer merkle_root)
    (fun ff => @instAbstractFieldRepresentation (Fin n) (ByzNSet n) proposer merkle_root
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) ff)
    (fun ff => @instLawfulAbstractFieldRepresentation (Fin n) (ByzNSet n) proposer merkle_root
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) (fun a b => Classical.propDecidable (a = b)) ff)
    instIsSubStateOfRefl instIsSubReaderOfRefl th st hinv.2.1

end Layer3
end FallbackReceipt

/-! ## The pinned trust base

The whole chain — reconstructed SMT proofs for the structural VCs, the
reachability induction, the state theorem, the pigeonhole — rests on the
standard Lean trio and nothing else (in particular: no `sorryAx`, i.e.
no trusted-SMT step). A regression that reintroduces trusted SMT (e.g.
dropping `veil.smt.trust false` in a `FallbackReceipt/Proofs/` file)
fails this guard. -/

/--
info: 'FallbackReceipt.build_totality_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FallbackReceipt.build_totality_of_reachable
