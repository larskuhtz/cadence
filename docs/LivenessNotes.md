# Liveness for Chorus — implementation notes

*Working notes on the liveness layer of
[`Cadence/Chorus.lean`](../Cadence/Chorus.lean): what it encodes, which
design decisions were taken and why, and what is deliberately left out. The
approach as a whole — including the tool extension that would remove the
remaining meta-level step — is [`Liveness.md`](./Liveness.md); the assumptions
it currently leaves standing are [`Architecture.md`](./Architecture.md) §4.
Historical in places; the current invariant set is the model itself.*

## What was done

A **Liveness — meta-argument and fair-progress invariants** section
was added to `Cadence/Chorus.lean` between the safety-invariant block and
the `set_option veil.gen.modelCheckScaffolding false` line. It
contains:

* a long-form comment block laying out the **meta-argument** in
  three layers: fairness as meta-axioms, well-founded ranking as a
  structural property of monotone Veil semantics, and
  *fair-progress* (strictly stronger than deadlock freedom) as the
  SMT-checkable safety content;
* thirteen SMT-discharged invariants split into auxiliary, (E),
  and (D) groups, with an explicit (Fast)/(Fall) case-split on
  the commit step:
  * **Auxiliaries:**
    * `phase_ordering` — phase markers respect their intended order;
    * `mvba_complete_per_proposer` — `mvba_complete S` implies a
      per-proposer MVBA decision (lifted post-condition);
    * `commit_pos_sig_from_fastqc` /
      `commit_neg_sig_from_fastqc` — an honest validator's
      commit signature carries the matching FastQC;
    * `path_fast_implies_fastqcs` — an honest validator on the
      fast path is itself a witness for FastQC existence for
      every proposer of `S` (the key auxiliary for the fast
      branch).
  * **Fair-enabledness (E):**
    * `progress_pre_mvba_arm` — until past the MVBA arm, some
      `advance_to_*` action is enabled;
    * `progress_voting` — once past the deadline, an honest validator
      can always advance toward `finalize_vote`;
    * `progress_commit_post_mvba` (Fall branch) — once
      `mvba_complete S`, every honest non-committed validator can
      fire `commit_assign_*` for every proposer (factors through
      `mvba_complete_per_proposer`);
    * `progress_commit_via_fast` (Fast branch) — once any honest
      validator has taken the fast path, every honest
      non-committed validator can fire `commit_assign_*` for
      every proposer (factors through
      `path_fast_implies_fastqcs`).
  * **Strict-decrease (D):**
    * `decrease_pre_mvba_arm` — until past the MVBA arm, some
      phase marker is unset (the canonical helpful action's
      target);
    * `decrease_voting` — until `voted I S`, the residual unset
      tuple is `voted I S` itself;
    * `decrease_commit_post_mvba` (Fall branch) — until
      `committed I S`, the residual unset tuple is `committed I S`
      itself;
    * `decrease_commit_via_fast` (Fast branch) — symmetric.

`History.md` and `ChorusDesign.md` §7 were updated to reflect the new layer.

## Key design decisions

### 1. Fairness as meta-axioms, not Veil annotations

Veil has no first-class fairness annotations on actions. Two
options were considered:

* **Encode L2S** (auxiliary witness state + per-fairness-action
  flags + safety invariant prohibiting a closed fair lasso). This
  is what [`Liveness.md`](./Liveness.md) sketches. Out of scope per
  the user.
* **Treat fairness as meta-level**. The classical
  verification-diagram approach attaches fairness labels to actions
  externally and leaves the temporal quantifier on the meta side.
  The deductive content of the proof is then a state-level safety
  property: *in every reachable non-terminal state, some
  fairly-scheduled action is enabled*.

We chose the second. The four meta-axioms (F-justice,
F-compassion, F-byz, A-mvba) are documented in the comment block
inside `Cadence/Chorus.lean`.

### 2. Three-way ingredient decomposition

Following McMillan (*Toward Liveness Proofs at Scale*, CAV 2024,
§2), the meta-argument has three layers:

1. **Fairness assumptions** (meta-level).
2. **Well-founded ranking** (structural; follows from monotone
   Veil semantics + per-slot finiteness).
3. **Fair progress** (SMT-discharged here) — strictly stronger
   than deadlock freedom. Combined with the fair-scheduling
   axioms, this rules out livelocks of unfair (Byzantine) actions.

(1) and (2) are not encoded in Veil. (3) is the safety content of
the discharged invariants.

### 3. Per-slot finiteness as a structural argument

Chorus is a one-shot per-slot protocol. *Per slot*, the type
parameters `node`, `nodeset`, the proposer set (`is_proposer S _`),
and the set of *active* `merkle_root`s are fixed *a priori* (can be
treated as constants). The per-slot state space is therefore
finite, the lexicographic product of monotone relations is
well-founded by subset ordering, and the strict-shrinkage of the
residual measure follows from each action setting exactly one or
two relation tuples to `true`.

This argument lives at the meta level. Encoding it inside Lean
would require either (a) explicit `Finite` instances on opaque
types (`node`, `merkle_root`, `nodeset`), or (b) a per-slot
quotient construction. Both are out of scope here.

### 4. Statement style of progress invariants

Many of the progress invariants are **propositional tautologies**
on the state predicate (e.g. `progress_pre_mvba_arm`,
`progress_voting`, all three `decrease_*`). They are stated as
invariants — even though the SMT discharge is trivial — to make
explicit the link between the state predicate and the *enabled*
fact for each phase (the (E) side), and between non-terminality
and the *residual unset tuple* for the canonical helpful action
(the (D) side). The reader can trace from the disjunction in
each invariant's conclusion to the `require` clauses / update
tuples of the corresponding action(s).

A future extension that exposes action enablement and update
targets as first-class Lean predicates (`enabled_<action>` and
`writes_<action>` for each action declaration) would let us state
these invariants directly as `∃ a, enabled_a state ∧ ¬ writes_a
state` disjunctions. That is a Veil-level ergonomic improvement,
not a soundness fix.

## What is _not_ done

* **The temporal/fairness layer is paper-and-pencil.** Veil
  currently has no way to discharge `□ (p → ◇ q)` style
  obligations. L2S or a verification-diagram tactic would change
  this; both are future work.
* **The MVBA termination axiom is meta-level.** The (A-mvba)
  assumption is paper-only because the probability-1 termination
  argument of the underlying randomised primitive is paper-only.
* **Aggregation enablement is not invariant-checked.**
  `aggregate_fastqc_*`, `aggregate_fallbackqc_*`,
  `aggregate_commitqc_*`, `aggregate_fbcerts` enable on the
  existence of 2f+1 honest signatures. Whether such a quorum
  accumulates is a quorum-availability question that depends on
  protocol participation and partial synchrony — out of scope.
  The meta-argument under (A-mvba) bridges this gap: assuming
  quorum availability, MVBA terminates; combined with
  `progress_commit_post_mvba`, the chain to `committed I S`
  closes.

## Lessons learned / proposals for next iteration

### Result quality

The implementation cleanly separates the SMT-discharged content
from the meta-argument. The five new invariants are simple,
narrowly-scoped, and discharge via the existing safety pipeline
without requiring new Veil features. The long comment block keeps
all the meta-argument context co-located with the invariants
themselves, which should help future maintainers.

### What could be better

1. **Stating progress as "enabled action exists" is awkward.** We
   end up writing propositional tautologies (`P ∨ ¬ P` over
   relation existence) rather than direct enablement predicates.
   The natural fix is a Veil-level extension that exposes
   `enabled_<action>` for each action declaration — a small piece
   of metaprogramming over the action's `require` clauses. This
   would make the deadlock-freedom invariants self-documenting.

2. **The well-founded ranking is invisible.** We claim
   strict-shrinkage is structural under monotone Veil semantics,
   but it is not actually checked anywhere. A Lean-level
   `def stateRank : State → SomeWFOrder` plus
   `theorem action_decreases : ...` would internalise this. It is
   an ergonomic improvement and a hedge against accidental
   non-monotone actions in future edits.

3. **Verification time.** The full `#check_invariants` sweep takes
   ~3 h. With the new invariants adding ~205 VCs, the projected
   total is ~3.5 h. Inner-loop iteration using
   `#check_invariant <name>` is much faster (~30 min for the new
   ones), but the user-facing build still needs to re-verify the
   full sweep. A future improvement is per-VC caching
   (already partially in place via Veil's metadata filtering) so
   that adding new invariants only forces re-verification of those
   plus the VCs for which they appear in the hypothesis.

4. **The `progress_voting` invariant is per-proposer.** This is
   pragmatic but obscures the *aggregate* progress claim
   "eventually `voted I S` for honest I". A cleaner formulation
   would quantify over a *single* witness proposer for which no
   signature exists. Both are equivalent under classical logic;
   the choice was made to keep the SMT discharge straightforward.

5. **The meta-axiom (A-mvba) is heavyweight.** It collapses the
   entire MVBA termination + partial-synchrony + quorum
   availability story into one black-box assumption. A future
   iteration that decomposes (A-mvba) into (a) GST as a phase
   marker, (b) per-action quorum-availability assumptions, (c)
   the MVBA probability-1 argument as a separate paper proof,
   would make the gap between model and reality more legible.

### Possible next steps

* **(Highest leverage)** Implement the L2S extension in Veil itself,
  per [`Liveness.md`](./Liveness.md). Reuses the existing safety-VC
  pipeline; gives Veil first-class liveness semantics. This is the
  intervention that would let us internalise the meta-axioms.
* **(Medium)** Add the `enabled_<action>` metaprogram and rewrite
  the progress invariants to use it.
* **(Medium)** Add a Lean-level `theorem` template for the
  well-founded ranking, parametrised over the slot, with `sorry`
  proofs for the per-slot finiteness obligation.
* **(Low)** Decompose (A-mvba) as outlined above; track the
  individual axioms in `History.md`.
