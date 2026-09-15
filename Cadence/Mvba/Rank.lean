import Cadence.Mvba.Progress
import Cadence.ByzQuorum

/-! # Mvba.Rank — the lexicographic ranking, and its decrease

The formal content of [`docs/MvbaPlan.md`](../../docs/MvbaPlan.md) §3.3.
[`Progress.lean`](./Progress.lean) proved the *disabling* half — a guard that
held and then failed means a monotone relation grew. This file supplies the
measure that growth is progress *in*, and the theorems that say so.

## What the ranking is

Two components, ordered lexicographically.

* **The view gap** — how many of a given list of views the validator has not
  yet entered. Zero exactly when it has entered all of them, in particular
  the honest-led view the run is waiting for.
* **The view-local residual** — at a fixed view and value, how much of that
  view's work is outstanding. It is a sum of seven counts of one shape, over
  two index lists:

  | over | counting | the step it measures |
  |---|---|---|
  | a quorum `q` | `msg_prepare r v e` | `form_prepqc`'s guard |
  | | `msg_commit r v e` | `form_commitqc`'s guard |
  | | `SentTimeout st r v` | what the two `form_tc_*` guards share |
  | the honest core of `q` | `accepted r v e` | `handle_preprepare` |
  | | `local_prepqc r v e` | `adopt_prepqc` / `sync_view_adopt` |
  | | `avail_ready r e` | `become_avail_ready` |
  | | `decided r e` | `decide` |

Everything is one `residual`: *how many entries of a finite index list do not
yet satisfy a monotone predicate*. That, plus the model's generated
monotonicity lemmas, is why each theorem below is a few lines and says
exactly one thing. The seven are summed rather than nested lexicographically
because each is independently non-increasing, so progress in any one lowers
the sum and no priority between them has to be invented.

## Two index lists, and why one of them is a sub-quorum

A quorum contains Byzantine members, so a residual over `q` can only reach
zero for relations a Byzantine member can also supply. That is exactly true
of the first three — `byz_prepare`, `byz_commit` and `byz_timeout_*` supply
them — and exactly false of the last four, which only an honest validator
ever sets. Counting those over `q` would give a bottom no run can reach.

They are counted over the **honest core** of `q` instead: the `f+1`
all-honest subset that any `2f+1` quorum contains, which is the quorum
interface's own
`ByzNodeSet.supermajority_contains_honest_greater_than_third`
(`exists_honest_core` below). The subset is itself an `nset`, so the *same*
`ByzNodeSetEnum` enumerates it — the honest dimension needs no second
enumeration hypothesis, and none is added.

What the honest core does not reach is the difference between `f+1` and the
`2f+1` correct validators, and it does not need to: `decide`'s guard is
per-validator and, once some `msg_commitqc v e` exists, holds at every
correct validator that has not decided. The count drives certificate
formation, which is the part that needs a quorum; the remaining validators
each need one weakly-fair firing, a chain of eventualities rather than a
count.

## Where the finiteness comes from — and a §3.3 correction

`MvbaPlan.md` §3.3 settled the finiteness question in two dimensions and got
a third one wrong. All three are visible in the types here.

* **The value dimension needs nothing.** Every count is taken at a fixed
  `(v, e)`, which is sound because the model proves `accepted_unique`: an
  honest validator accepts at most one value per view, and every relation it
  writes is gated on that acceptance. The value dimension collapses by
  protocol, not by cardinality.
* **The node dimension is `ByzNodeSetEnum`**
  ([`ByzQuorum.lean`](../ByzQuorum.lean)): a quorum's members as a list. It
  is an **explicit parameter** of every definition and theorem that uses it,
  never an instance, so a liveness result carries it as a visible hypothesis
  and nothing on the safety side acquires a cardinality assumption it does
  not need. One `ByzNodeSetEnum` serves both index lists, as above.
* **The view dimension needs finiteness too, and §3.3 said it came from
  `leader_honest_cofinal`. It does not.** Cofinality gives a *target* — above
  any view there is an honest-led one (`exists_honest_leader_above` below,
  the assumption's one consequence here) — but says nothing about how many
  views lie in between, and `TotalOrderWithMinimum` does not either: its
  order may have an infinite ascending chain below a bound, and then no
  measure on views is well-founded. So the views to be counted are an
  **explicit `List view` parameter** `Vs`, exactly as the quorum's members
  are. Supplying it is the view dimension's sibling of `ByzNodeSetEnum`, and
  keeping it a parameter is what stops it being silent: the run-level theorem
  of §3.5 step 4 must produce a list covering the interval from the current
  view to the honest-led target, and cannot pretend the model's abstract
  order handed it one.

## What is not here

No scheduling assumption, and no run. A rank that never increases and
strictly decreases on progress is a statement about single transitions; that
fair firings eventually drive it to `0` needs (F-justice), (A-viewsync) and
(F-avail), which enter at §3.5 step 4 as explicit hypotheses of the run-level
theorem. The one thing consumed beyond the model's transitions and its quorum
interface is `leader_honest_cofinal`, and only in
`exists_honest_leader_above`.

**Sign convention.** The rank is a residual — *what is left to do* — so
progress makes it **decrease**. (§3.4's table said "the rank strictly
increased" of the `Progress.lean` row; that direction was informal, and this
file fixes it.) -/

namespace Mvba

/-! ## The residual, once

All seven counts are the same count, so it is defined and reasoned about
once. The predicate is a `Prop`, not a `Bool`, because one of them is the
disjunction the `form_tc_*` guards share — a validator has sent *some*
`Timeout` for the view — whose existential quantifier over an abstract sort
has no decision procedure. `Classical.propDecidable` supplies the one
canonical instance, so every `residual` term is built the same way and the
arithmetic below sees one atom per summand.

The five lemmas are the whole interface: zero means the predicate holds
everywhere on the list, a head entry counts iff it fails the predicate,
growth of the predicate cannot raise the count, and a *new* witness inside
the list strictly lowers it. -/

open Classical in
/-- How many entries of `xs` do not yet satisfy `p`.

(`Decidable.decide`, spelled out: this namespace has an *action* named
`decide`, and the unqualified reference resolves to that instead.) -/
noncomputable def residual {α : Type u} (xs : List α) (p : α → Prop) : Nat :=
  xs.countP (fun a => ! Decidable.decide (p a))

theorem residual_eq_zero_iff {α : Type u} {xs : List α} {p : α → Prop} :
    residual xs p = 0 ↔ ∀ a ∈ xs, p a := by
  simp [residual, List.countP_eq_zero]

/-- A head entry that already satisfies `p` does not count. -/
theorem residual_cons_of_pos {α : Type u} {p : α → Prop} {a : α} (xs : List α)
    (h : p a) : residual (a :: xs) p = residual xs p := by
  simp [residual, h]

/-- A head entry that does not satisfy `p` counts once. -/
theorem residual_cons_of_neg {α : Type u} {p : α → Prop} {a : α} (xs : List α)
    (h : ¬ p a) : residual (a :: xs) p = residual xs p + 1 := by
  simp [residual, h]

/-- A predicate that has grown pointwise leaves no larger residual. -/
theorem residual_le {α : Type u} {p q : α → Prop} (hpq : ∀ a, p a → q a)
    (xs : List α) : residual xs q ≤ residual xs p := by
  refine List.countP_mono_left (fun a _ ha => ?_)
  by_cases hp : p a
  · simp [hpq a hp] at ha
  · simp [hp]

/-- A predicate that has grown pointwise *and* acquired a new witness inside
the list leaves a strictly smaller residual. -/
theorem residual_lt_of_new {α : Type u} {p q : α → Prop} (hpq : ∀ a, p a → q a)
    {xs : List α} {a₀ : α} (hmem : a₀ ∈ xs) (h0 : ¬ p a₀) (h1 : q a₀) :
    residual xs q < residual xs p := by
  induction xs with
  | nil => simp at hmem
  | cons a xs ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [residual_cons_of_pos xs h1, residual_cons_of_neg xs h0]
      have hle : residual xs q ≤ residual xs p := residual_le hpq xs
      omega
    · have hlt : residual xs q < residual xs p := ih hmem'
      by_cases hq : q a
      · rw [residual_cons_of_pos xs hq]
        by_cases hp : p a
        · rw [residual_cons_of_pos xs hp]; omega
        · rw [residual_cons_of_neg xs hp]; omega
      · rw [residual_cons_of_neg xs hq, residual_cons_of_neg xs (fun hp => hq (hpq a hp))]
        omega

/-! ## One order fact

`Progress.lean` needs `¬ le → lt`; the freshness argument below needs the
other direction. -/

section Order

variable {view : Type} [vord : TotalOrderWithMinimum view]

/-- In a total order, `v < W` rules out `W ≤ v`. (The converse of
`Progress.lean`'s `lt_of_not_le`.) -/
theorem not_le_of_lt {v W : view} (h : vord.lt v W) : ¬ vord.le W v := by
  intro hle
  have h' := (vord.le_lt v W).mp h
  exact h'.2 (vord.le_antisymm v W h'.1 hle)

end Order

/-! ## The order the rank lives in

`Nat × Nat` lexicographically, well-founded because both components are.
Naming it once keeps every decrease theorem below in the same relation. -/

/-- The order the rank decreases in: the view gap first, the view-local
residual second. -/
abbrev RankLt : Nat × Nat → Nat × Nat → Prop := Prod.Lex (· < ·) (· < ·)

theorem rankLt_wf : WellFounded RankLt := IsWellFounded.wf

/-- The one way the two components are combined: the first never grows, and
if it stays put the second strictly shrinks. -/
theorem rankLt_of {a a' b b' : Nat} (h1 : a' ≤ a) (h2 : a' = a → b' < b) :
    RankLt (a', b') (a, b) := by
  rcases Nat.lt_or_ge a' a with h | h
  · exact Prod.Lex.left _ _ h
  · have heq : a' = a := Nat.le_antisymm h1 h
    subst heq
    exact Prod.Lex.right _ (h2 rfl)

/-! ## The honest core of a quorum -/

section Core

variable {node nodeset : Type} [nset : ByzNodeSet node nodeset]

/-- **Projection onto an honest sub-quorum.** Every `2f+1` quorum contains an
`f+1` subset all of whose members are honest members of it: at most `f` of
its members are Byzantine, and `(2f+1) − f = f+1`. This is
`ByzNodeSet.supermajority_contains_honest_greater_than_third`, an axiom of
the quorum interface that the `n ≥ 3f+1` instance family proves
([`ByzQuorum.lean`](../ByzQuorum.lean)), so it costs nothing new.

The subset is itself an `nset`, which is the point: the same
`ByzNodeSetEnum` enumerates it, so `chainGap`'s honest-only counts are
finite for exactly the reason `assemblyGap`'s are, with no second
enumeration hypothesis. -/
theorem exists_honest_core (q : nodeset) (hq : nset.supermajority q) :
    ∃ hc : nodeset, nset.greater_than_third hc ∧
      ∀ r, nset.member r hc = true → nset.member r q = true ∧ ¬ nset.is_byz r = true :=
  nset.supermajority_contains_honest_greater_than_third q hq

end Core

/-! ## The components -/

section Defs

variable {node nodeset value view : Type} [nset : ByzNodeSet node nodeset]

/-- `r` has sent *some* `Timeout` for view `v` — with a certificate or
without one. This is what the two timeout-certificate assemblies have in
common and neither can do without, so it is the right thing to *count*; it
is deliberately weaker than either guard. `form_tc_nolock` additionally
needs every member's `Timeout` to be the lock-free form, and `form_tc_lock`
additionally needs one member's carried certificate to dominate the rest.
A zero residual here is therefore necessary for a `TC_{s,v}` to form and
not sufficient. -/
def SentTimeout (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view))
    (r : node) (v : view) : Prop :=
  st.msg_timeout_noqc r v = true ∨ ∃ W E, st.msg_timeout_qc r v W E = true

/-- **The view component.** How many of the views `Vs` the validator `i` has
not yet entered. `Vs` is the caller's finite index list — the header says why
it is a parameter and not a consequence of `leader_honest_cofinal`. -/
noncomputable def viewGap (Vs : List view)
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) (i : node) : Nat :=
  residual Vs (fun v => st.entered i v = true)

/-- **The quorum assemblies**, over the members of `q`: who still owes a
`Prepare`, a `Commit` and a `Timeout` at `(v, e)`. This is where liveness
needs `ByzNodeSetEnum` and safety does not: **safety consumes a quorum
intersection, liveness must assemble a quorum.** -/
noncomputable def assemblyGap (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (q : nodeset) (v : view) (e : value)
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) : Nat :=
  residual (enum.members q) (fun r => st.msg_prepare r v e = true)
    + residual (enum.members q) (fun r => st.msg_commit r v e = true)
    + residual (enum.members q) (fun r => SentTimeout st r v)

/-- **The per-validator chain**, over the members of an honest core `hc`: who
has not yet accepted the proposal, adopted the view's certificate, had its
availability shares delivered, or decided. These are honest-only relations,
which is why the index list is the honest core and not the quorum (the
header, and `exists_honest_core`). -/
noncomputable def chainGap (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (hc : nodeset) (v : view) (e : value)
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) : Nat :=
  residual (enum.members hc) (fun r => st.accepted r v e = true)
    + residual (enum.members hc) (fun r => st.local_prepqc r v e = true)
    + residual (enum.members hc) (fun r => st.avail_ready r e = true)
    + residual (enum.members hc) (fun r => st.decided r e = true)

/-- The lexicographic rank of a state, for validator `i` waiting on the views
`Vs`, on quorum `q`'s assemblies at `(v, e)`, and on the chain at `q`'s
honest core `hc`. -/
noncomputable def rank (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value)
    (st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)) : Nat × Nat :=
  (viewGap Vs st i, assemblyGap enum q v e st + chainGap enum hc v e st)

end Defs

/-! ## Rank zero is exactly the guard

A ranking earns its keep only if its bottom is the thing being waited for.
Every component has that property, and none of these needs a transition. -/

section Zero

variable {node nodeset value view : Type} [nset : ByzNodeSet node nodeset]
  {st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}
  {enum : Cadence.ByzNodeSetEnum node nodeset nset} {q hc : nodeset} {v : view} {e : value}

omit nset in
/-- View gap `0`: the validator has entered every view of the list — in
particular the honest-led target, once that is put in the list. -/
theorem entered_of_viewGap_zero {Vs : List view} {i : node}
    (h : viewGap Vs st i = 0) {u : view} (hu : u ∈ Vs) : st.entered i u = true :=
  residual_eq_zero_iff.mp h u hu

/-- Assembly residual `0`: the message guard of `form_prepqc` on `q`. (Its
other guard, `supermajority q`, is a fact about `q` alone and the caller's to
supply; the same holds of the lemmas below.) -/
theorem prepare_quorum_of_assemblyGap_zero (h : assemblyGap enum q v e st = 0)
    (r : node) (hr : nset.member r q = true) : st.msg_prepare r v e = true := by
  have hz : residual (enum.members q) (fun r => st.msg_prepare r v e = true) = 0 := by
    simp only [assemblyGap] at h; omega
  exact residual_eq_zero_iff.mp hz r ((enum.mem_members r q).mp hr)

/-- Assembly residual `0`: the message guard of `form_commitqc` on `q`. -/
theorem commit_quorum_of_assemblyGap_zero (h : assemblyGap enum q v e st = 0)
    (r : node) (hr : nset.member r q = true) : st.msg_commit r v e = true := by
  have hz : residual (enum.members q) (fun r => st.msg_commit r v e = true) = 0 := by
    simp only [assemblyGap] at h; omega
  exact residual_eq_zero_iff.mp hz r ((enum.mem_members r q).mp hr)

/-- Assembly residual `0`: every member of `q` has sent a `Timeout` for `v` —
the obligation the two `form_tc_*` assemblies share, so this is necessary for
either and sufficient for neither (`SentTimeout`). -/
theorem timeout_quorum_of_assemblyGap_zero (h : assemblyGap enum q v e st = 0)
    (r : node) (hr : nset.member r q = true) : SentTimeout st r v := by
  have hz : residual (enum.members q) (fun r => SentTimeout st r v) = 0 := by
    simp only [assemblyGap] at h; omega
  exact residual_eq_zero_iff.mp hz r ((enum.mem_members r q).mp hr)

/-- Chain residual `0`: every member of the honest core accepted `e` in `v`. -/
theorem accepted_of_chainGap_zero (h : chainGap enum hc v e st = 0)
    (r : node) (hr : nset.member r hc = true) : st.accepted r v e = true := by
  have hz : residual (enum.members hc) (fun r => st.accepted r v e = true) = 0 := by
    simp only [chainGap] at h; omega
  exact residual_eq_zero_iff.mp hz r ((enum.mem_members r hc).mp hr)

/-- Chain residual `0`: every member of the honest core holds the view's
certificate on `e`. -/
theorem local_prepqc_of_chainGap_zero (h : chainGap enum hc v e st = 0)
    (r : node) (hr : nset.member r hc = true) : st.local_prepqc r v e = true := by
  have hz : residual (enum.members hc) (fun r => st.local_prepqc r v e = true) = 0 := by
    simp only [chainGap] at h; omega
  exact residual_eq_zero_iff.mp hz r ((enum.mem_members r hc).mp hr)

/-- Chain residual `0`: every member of the honest core has its availability
shares for `e` — `send_commit`'s environment precondition. -/
theorem avail_ready_of_chainGap_zero (h : chainGap enum hc v e st = 0)
    (r : node) (hr : nset.member r hc = true) : st.avail_ready r e = true := by
  have hz : residual (enum.members hc) (fun r => st.avail_ready r e = true) = 0 := by
    simp only [chainGap] at h; omega
  exact residual_eq_zero_iff.mp hz r ((enum.mem_members r hc).mp hr)

/-- Chain residual `0`, the payoff: every member of the honest core has
decided `e`. -/
theorem decided_of_chainGap_zero (h : chainGap enum hc v e st = 0)
    (r : node) (hr : nset.member r hc = true) : st.decided r e = true := by
  have hz : residual (enum.members hc) (fun r => st.decided r e = true) = 0 := by
    simp only [chainGap] at h; omega
  exact residual_eq_zero_iff.mp hz r ((enum.mem_members r hc).mp hr)

/-- The bottom of the chain component is a real decision, not an artefact of
the encoding: an honest core is `greater_than_third`, hence non-empty of
honest members, so a zero chain residual exhibits a **correct** validator
that has decided `e`. -/
theorem exists_honest_decided_of_chainGap_zero
    (hgt : nset.greater_than_third hc) (h : chainGap enum hc v e st = 0) :
    ∃ r, ¬ nset.is_byz r = true ∧ st.decided r e = true := by
  obtain ⟨r, hmem, hhon⟩ := nset.greater_than_third_one_honest hc hgt
  exact ⟨r, hhon, decided_of_chainGap_zero h r hmem⟩

end Zero

/-! ## The rank never increases

Every `Mvba` relation is written only `true`, so M13's generated
`<relation>.mono` lemmas — hypothesis-free, kernel-checked, emitted at
`#gen_spec` — carry every component across an arbitrary transition. No
invariant and no guard is involved, which is why this holds of *every*
transition, the Byzantine ones included: the adversary can drive the rank
down but never up. -/

section Step

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}
  {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}
  {l : Label node nodeset value view}

/-- Having sent a `Timeout` is monotone: both disjuncts are. -/
theorem sentTimeout_mono
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (r : node) (v : view) (h : SentTimeout st r v) : SentTimeout st' r v := by
  rcases h with h | ⟨W, E, h⟩
  · exact Or.inl (Mvba.msg_timeout_noqc.mono htr r v h)
  · exact Or.inr ⟨W, E, Mvba.msg_timeout_qc.mono htr r v W E h⟩

theorem viewGap_le
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (i : node) : viewGap Vs st' i ≤ viewGap Vs st i :=
  residual_le (fun v => Mvba.entered.mono htr i v) Vs

theorem assemblyGap_le
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (enum : Cadence.ByzNodeSetEnum node nodeset nset) (q : nodeset) (v : view) (e : value) :
    assemblyGap enum q v e st' ≤ assemblyGap enum q v e st := by
  have hp := residual_le (fun r => Mvba.msg_prepare.mono htr r v e) (enum.members q)
  have hc := residual_le (fun r => Mvba.msg_commit.mono htr r v e) (enum.members q)
  have ht := residual_le (fun r => sentTimeout_mono htr r v) (enum.members q)
  simp only [assemblyGap]
  omega

theorem chainGap_le
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (enum : Cadence.ByzNodeSetEnum node nodeset nset) (hc : nodeset) (v : view) (e : value) :
    chainGap enum hc v e st' ≤ chainGap enum hc v e st := by
  have ha := residual_le (fun r => Mvba.accepted.mono htr r v e) (enum.members hc)
  have hl := residual_le (fun r => Mvba.local_prepqc.mono htr r v e) (enum.members hc)
  have hv := residual_le (fun r => Mvba.avail_ready.mono htr r e) (enum.members hc)
  have hd := residual_le (fun r => Mvba.decided.mono htr r e) (enum.members hc)
  simp only [chainGap]
  omega

/-- **The rank never increases along a transition** — it either stays put or
strictly decreases. -/
theorem rank_noninc
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value) :
    rank Vs enum i q hc v e st' = rank Vs enum i q hc v e st ∨
      RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) := by
  have hA := assemblyGap_le htr enum q v e
  have hC := chainGap_le htr enum hc v e
  rcases Nat.lt_or_ge (viewGap Vs st' i) (viewGap Vs st i) with h | h
  · exact Or.inr (Prod.Lex.left _ _ h)
  · have heq : viewGap Vs st' i = viewGap Vs st i :=
      Nat.le_antisymm (viewGap_le htr Vs i) h
    rcases Nat.lt_or_ge (assemblyGap enum q v e st' + chainGap enum hc v e st')
      (assemblyGap enum q v e st + chainGap enum hc v e st) with h2 | h2
    · exact Or.inr (by simp only [rank, heq]; exact Prod.Lex.right _ h2)
    · have h2eq : assemblyGap enum q v e st' + chainGap enum hc v e st'
          = assemblyGap enum q v e st + chainGap enum hc v e st := by omega
      exact Or.inl (by simp only [rank, heq, h2eq])

/-! ## The rank strictly decreases

One theorem per way of making progress, each taking the *fresh* witness — the
tuple unset before the step and set after it — which is exactly what
[`Progress.lean`](./Progress.lean)'s disabling lemmas produce. They share a
proof: the view gap cannot have grown, so either it shrank (and the first
component decides) or it is unchanged, and then the one summand that strictly
dropped decides against the six that cannot have grown. -/

/-- Entering a view of the list. -/
theorem rank_lt_of_entered
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value)
    {u : view} (hu : u ∈ Vs) (h0 : st.entered i u = false) (h1 : st'.entered i u = true) :
    RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) :=
  Prod.Lex.left _ _
    (residual_lt_of_new (fun w => Mvba.entered.mono htr i w) hu (by simp [h0]) h1)

/-- A quorum member's `Prepare` arriving at `(v, e)`. -/
theorem rank_lt_of_prepare
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value)
    {r : node} (hr : nset.member r q = true)
    (h0 : st.msg_prepare r v e = false) (h1 : st'.msg_prepare r v e = true) :
    RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) := by
  refine rankLt_of (viewGap_le htr Vs i) (fun _ => ?_)
  have hC := chainGap_le htr enum hc v e
  have hlt := residual_lt_of_new (fun r' => Mvba.msg_prepare.mono htr r' v e)
    ((enum.mem_members r q).mp hr) (by simp [h0]) h1
  have hc2 := residual_le (fun r' => Mvba.msg_commit.mono htr r' v e) (enum.members q)
  have ht := residual_le (fun r' => sentTimeout_mono htr r' v) (enum.members q)
  simp only [assemblyGap]
  omega

/-- A quorum member's `Commit` arriving at `(v, e)`. -/
theorem rank_lt_of_commit
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value)
    {r : node} (hr : nset.member r q = true)
    (h0 : st.msg_commit r v e = false) (h1 : st'.msg_commit r v e = true) :
    RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) := by
  refine rankLt_of (viewGap_le htr Vs i) (fun _ => ?_)
  have hC := chainGap_le htr enum hc v e
  have hp := residual_le (fun r' => Mvba.msg_prepare.mono htr r' v e) (enum.members q)
  have hlt := residual_lt_of_new (fun r' => Mvba.msg_commit.mono htr r' v e)
    ((enum.mem_members r q).mp hr) (by simp [h0]) h1
  have ht := residual_le (fun r' => sentTimeout_mono htr r' v) (enum.members q)
  simp only [assemblyGap]
  omega

/-- A quorum member's `Timeout` for `v` arriving — progress toward the
assembly that closes the view, which is the route by which the *first*
component advances past view 1. -/
theorem rank_lt_of_timeout
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value)
    {r : node} (hr : nset.member r q = true)
    (h0 : ¬ SentTimeout st r v) (h1 : SentTimeout st' r v) :
    RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) := by
  refine rankLt_of (viewGap_le htr Vs i) (fun _ => ?_)
  have hC := chainGap_le htr enum hc v e
  have hp := residual_le (fun r' => Mvba.msg_prepare.mono htr r' v e) (enum.members q)
  have hc2 := residual_le (fun r' => Mvba.msg_commit.mono htr r' v e) (enum.members q)
  have hlt := residual_lt_of_new (fun r' => sentTimeout_mono htr r' v)
    ((enum.mem_members r q).mp hr) h0 h1
  simp only [assemblyGap]
  omega

/-- An honest-core member accepting the proposal (`handle_preprepare`). -/
theorem rank_lt_of_accepted
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value)
    {r : node} (hr : nset.member r hc = true)
    (h0 : st.accepted r v e = false) (h1 : st'.accepted r v e = true) :
    RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) := by
  refine rankLt_of (viewGap_le htr Vs i) (fun _ => ?_)
  have hA := assemblyGap_le htr enum q v e
  have hlt := residual_lt_of_new (fun r' => Mvba.accepted.mono htr r' v e)
    ((enum.mem_members r hc).mp hr) (by simp [h0]) h1
  have hl := residual_le (fun r' => Mvba.local_prepqc.mono htr r' v e) (enum.members hc)
  have hv := residual_le (fun r' => Mvba.avail_ready.mono htr r' e) (enum.members hc)
  have hd := residual_le (fun r' => Mvba.decided.mono htr r' e) (enum.members hc)
  simp only [chainGap]
  omega

/-- An honest-core member adopting the view's certificate (`adopt_prepqc`,
`sync_view_adopt`). -/
theorem rank_lt_of_adopt
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value)
    {r : node} (hr : nset.member r hc = true)
    (h0 : st.local_prepqc r v e = false) (h1 : st'.local_prepqc r v e = true) :
    RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) := by
  refine rankLt_of (viewGap_le htr Vs i) (fun _ => ?_)
  have hA := assemblyGap_le htr enum q v e
  have ha := residual_le (fun r' => Mvba.accepted.mono htr r' v e) (enum.members hc)
  have hlt := residual_lt_of_new (fun r' => Mvba.local_prepqc.mono htr r' v e)
    ((enum.mem_members r hc).mp hr) (by simp [h0]) h1
  have hv := residual_le (fun r' => Mvba.avail_ready.mono htr r' e) (enum.members hc)
  have hd := residual_le (fun r' => Mvba.decided.mono htr r' e) (enum.members hc)
  simp only [chainGap]
  omega

/-- An honest-core member's availability shares arriving
(`become_avail_ready`; the (F-avail) hook). -/
theorem rank_lt_of_avail_ready
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value)
    {r : node} (hr : nset.member r hc = true)
    (h0 : st.avail_ready r e = false) (h1 : st'.avail_ready r e = true) :
    RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) := by
  refine rankLt_of (viewGap_le htr Vs i) (fun _ => ?_)
  have hA := assemblyGap_le htr enum q v e
  have ha := residual_le (fun r' => Mvba.accepted.mono htr r' v e) (enum.members hc)
  have hl := residual_le (fun r' => Mvba.local_prepqc.mono htr r' v e) (enum.members hc)
  have hlt := residual_lt_of_new (fun r' => Mvba.avail_ready.mono htr r' e)
    ((enum.mem_members r hc).mp hr) (by simp [h0]) h1
  have hd := residual_le (fun r' => Mvba.decided.mono htr r' e) (enum.members hc)
  simp only [chainGap]
  omega

/-- An honest-core member deciding (`decide`) — the last step, and the one the
whole rank is aimed at. -/
theorem rank_lt_of_decided
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value)
    {r : node} (hr : nset.member r hc = true)
    (h0 : st.decided r e = false) (h1 : st'.decided r e = true) :
    RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) := by
  refine rankLt_of (viewGap_le htr Vs i) (fun _ => ?_)
  have hA := assemblyGap_le htr enum q v e
  have ha := residual_le (fun r' => Mvba.accepted.mono htr r' v e) (enum.members hc)
  have hl := residual_le (fun r' => Mvba.local_prepqc.mono htr r' v e) (enum.members hc)
  have hv := residual_le (fun r' => Mvba.avail_ready.mono htr r' e) (enum.members hc)
  have hlt := residual_lt_of_new (fun r' => Mvba.decided.mono htr r' e)
    ((enum.mem_members r hc).mp hr) (by simp [h0]) h1
  simp only [chainGap]
  omega

/-! ## Leaving a view is progress

The junction with [`Progress.lean`](./Progress.lean). Its
`entered_higher_of_in_view_disabled` says a validator that leaves view `w`
has entered a strictly higher one; here that view is seen to be **fresh** as
well — it cannot have been entered before, because `InView st i w` said `w`
was the maximum — which is what turns "the guard failed" into "the rank went
down". -/

/-- The higher view `Progress.lean` produces is fresh. -/
theorem entered_fresh_above_of_in_view_disabled
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (i : node) (w : view) (h : InView st i w) (h' : ¬ InView st' i w) :
    ∃ W, vord.lt w W ∧ st.entered i W = false ∧ st'.entered i W = true := by
  obtain ⟨W, hW, hlt⟩ := entered_higher_of_in_view_disabled htr i w h h'
  refine ⟨W, hlt, ?_, hW⟩
  cases hb : st.entered i W with
  | false => rfl
  | true => exact absurd (h.2 W hb) (not_le_of_lt hlt)

/-- **Leaving a view strictly decreases the rank**, provided the view entered
is one of the views being counted. The proviso is the honest part: a
validator may sync *past* the target on a timeout certificate of a much
higher view, and then nothing has been gained. That is precisely the hole
(A-viewsync) fills at §3.5 step 4, and precisely why it is a hypothesis here
rather than a silent assumption. -/
theorem rank_lt_of_leaving_view
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st l st')
    (Vs : List view) (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (i : node) (q hc : nodeset) (v : view) (e : value) (w : view)
    (h : InView st i w) (h' : ¬ InView st' i w)
    (hcover : ∀ W, vord.lt w W → st.entered i W = false → st'.entered i W = true → W ∈ Vs) :
    RankLt (rank Vs enum i q hc v e st') (rank Vs enum i q hc v e st) := by
  obtain ⟨W, hlt, h0, h1⟩ := entered_fresh_above_of_in_view_disabled htr i w h h'
  exact rank_lt_of_entered htr Vs enum i q hc v e (hcover W hlt h0 h1) h0 h1

/-! ## The target view

`leader_honest_cofinal`'s single consequence, and the only place in this file
where the model's assumptions are used. It supplies the *target* of the view
gap; it does not, and cannot, supply the list of views leading up to it. -/

/-- **Honest leaders are cofinal.** Above any view there is an honest-led
one — the model's `leader_honest_cofinal` assumption, read off a theory the
transition system admits. -/
theorem exists_honest_leader_above
    (hasm : (Mvba.relationalTransitionSystem node nodeset value view).assumptions th)
    (V : view) :
    ∃ (W : view) (L : node), vord.le V W ∧ th.leader W L = true ∧ ¬ nset.is_byz L = true :=
  hasm.2 V

/-- The same at any reachable state: reachability carries the assumptions. -/
theorem exists_honest_leader_above_of_reachable
    (hr : (Mvba.relationalTransitionSystem node nodeset value view).reachable th st)
    (V : view) :
    ∃ (W : view) (L : node), vord.le V W ∧ th.leader W L = true ∧ ¬ nset.is_byz L = true :=
  exists_honest_leader_above
    (Veil.RelationalTransitionSystem.reachable_assumptions _ th _ hr) V

end Step

end Mvba

/-! ## The pinned trust base

Plain Lean over the model's generated monotonicity lemmas, the quorum
interface, and — in the last theorem only — one model assumption: the
standard trio and nothing else, no `sorryAx`, no solver.

One pin reads differently on purpose. `exists_honest_core` is a direct
projection of a `ByzNodeSet` field, so it depends on **no** axioms at all —
a strictly smaller footprint than the trio, and the machine-checked form of
"projecting a quorum onto its honest core costs nothing new". -/

/--
info: 'Mvba.rank_noninc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.rank_noninc

/--
info: 'Mvba.rank_lt_of_timeout' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.rank_lt_of_timeout

/--
info: 'Mvba.rank_lt_of_decided' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.rank_lt_of_decided

/--
info: 'Mvba.rank_lt_of_leaving_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.rank_lt_of_leaving_view

/-- info: 'Mvba.exists_honest_core' does not depend on any axioms -/
#guard_msgs in
#print axioms Mvba.exists_honest_core

/--
info: 'Mvba.exists_honest_decided_of_chainGap_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.exists_honest_decided_of_chainGap_zero

/--
info: 'Mvba.exists_honest_leader_above_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.exists_honest_leader_above_of_reachable
