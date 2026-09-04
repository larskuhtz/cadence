# MVBA instantiation — plan

*A plan, not a status document. Nothing here is built yet. It records what
the work is, what has to be decided before it starts, and which choices
would quietly foreclose later work if made carelessly.*

The MVBA is the last oracle in Chorus's trust base whose provider could
plausibly become a model. `mod:mvba` in the published paper is an interface
and five properties with no algorithm, which is why the development consumes
it as (A-mvba) and why `ℓ_MVBA` is a parametric hole
([`Bounds.md`](./Bounds.md) §1). The paper's implementation track now
specifies a concrete leader-based protocol with its own correctness section,
so for the first time there is something to model.

## 0. Two decisions that come before any Lean

### 0.1 The specification is internal

Everything verified so far is checkable by an auditor against
`arXiv:2607.02275v2`. The MVBA algorithm is not in it — only the internal
supplement has it. The algorithms are not secret; a Rust implementation
exists in the `monad-bft` tree. But an auditor reading a `Mvba.lean` would
have no specification to read it against, which is a real change to this
repository's audit story rather than a documentation detail.

**Open, and needed before the model is written:** the exact implementation
branch and commit to cite. The Cadence-named branches visible from here —
`xinyuan/chorus-core-sim`, `xinyuan/chorus-finalization-test`,
`xinyuan/chorus-modular-env`, `xinyuan/acs-interface-and-cadence-conductor`,
`xinyuan/conductor-revision`, `mcp-dev` — are all in the **private**
`monad-bft-private` remote. The only public branch matching any Cadence
keyword, `category-labs/monad-bft` `xinyuan/mcp-prototype` (`c7a9633`,
2026-03-27), predates the paper by four months and contains no
chorus/cadence/conductor paths. So the public referent still has to be
identified; this section should carry branch and commit once it is.

Three ways the trade-off can go, none of which blocks the modelling itself:
publish the MVBA section of the supplement; keep the component and mark it
internal-only; or keep the *public* claim at contract level — `mod:mvba` is
public — and treat the algorithm as an implementation detail whose model is
an internal artefact.

### 0.2 There is no immutable referent to pin to

The paper has arXiv versions, and [`../README.md`](../README.md) maps each to
the unique paper-repo commit that reproduces it (landing with the
paper-alignment branch). The supplement has neither tags nor versions, and
`alg_mvba.tex` is the most-churned file in the paper repository — roughly a
dozen commits since July. Modelling it means modelling a moving target.

Proposal: pin the model's header to a **supplement commit SHA**, and treat a
change to that file as a trigger to re-read. This is a new convention here —
everywhere else the citation discipline rests on stable anchors in an
immutable document — but it is cheap and it is the only honest option while
the supplement stays untagged.

## 1. What "plugging in" means, and what is actually unchecked

Worth stating precisely, because the mechanism is easy to over- and
under-sell.

**The class-parameter route exists and is used.** `Chorus.lean` declares
`instantiate nset : ByzNodeSet node nodeset`; the class's axioms are then
available inside the model (`nset.supermajority q` appears in guards), and
`byzNodeSetFin` discharges them for every `n = 3f+1`. That is a genuine
"instance witnesses an implementation with the properties" composition, and
it is machine-checked end to end. `ByzNodeSet` is **not** an assumption in
[`Architecture.md`](./Architecture.md) §4 precisely because of this.

**Module contracts do not currently use it.** `SlotConsensus`,
`Orchestrator` and `MVBA` are classes too, but no consuming model
`instantiate`s them. `Cadence.lean` instead *transcribes* each contract
field into a Veil `invariant` over its own relations — `finalized_agreement`
against `SlotConsensus.agreement`, `opened_prefix_agreement` against
`Orchestrator.open_prefix_agreement`, the latter with a comment asserting it
is the class field "verbatim". The provider side is fully machine-checked:
[`Chorus/Compose.lean`](../Cadence/Chorus/Compose.lean) really does build a
`SlotConsensus` from proven safety properties, axiom-pinned.

So the seam is **transcription fidelity**, not refinement: nothing checks
that the hand-written invariant says the same thing as the class field it
claims to restate. That is narrow and auditable — two statements read side
by side — but it is not machine-checked, and it is the only reason a
verified MVBA would not *automatically* discharge Chorus's (A-mvba).

### Why the class is not consumed directly, and how to fix it

The mechanical reason is specific. Veil's `instantiate` registers a
`Parameter` of kind `.moduleTypeclass`: a **universal parameter of the
module**, fixed for the entire run, and it must be declared before
`#gen_state`. `ByzNodeSet` and `TotalOrder` fit because quorum structure and
orderings *are* run-constants. `SlotConsensus` does not, because it bundles
`finalized` — and in the consumer `finalized` is mutable state
(`relation finalized (i : node) (s : slot) (v : pvector)`, written by
actions). A module parameter cannot be the state the module evolves.
Secondarily, the class describes one instance while `Cadence.lean` runs a
slot-indexed family of them.

But that is an artifact of how the class is **factored**, not a law about
classes. `SlotConsensus` conflates two different things:

* a **carrier** — `correct`, `finalized`, `includes`, `on_time_proposal`,
  `slot_of`, `inst_slot` — which the consumer already has, as its own state;
* the **properties** — `agreement`, `slot_safety`, `proposal_inclusion` —
  which are the only part the consumer actually wants to assume.

Because the properties are written as inline `∀`-statements *inside* the
class, they can only be referred to through an instance, and an instance
drags the carrier with it. Lift them into standalone definitions over
carrier arguments and the problem disappears:

```lean
def Agreement (correct : v → Prop) (finalized : v → pv → Prop) : Prop :=
  ∀ i j V V', correct i → correct j → finalized i V → finalized j V' → V = V'
```

Then the class field becomes `agreement : Agreement correct finalized`; the
consumer's Veil invariant becomes that *same definition* applied to its own
state, per slot; and the provider's instance supplies it applied to Chorus's
relations. Consumer and provider now reference one object, so there is
nothing to transcribe and nothing to drift. No `instantiate` is required or
wanted — what the consumer needs is the property, not the carrier — and the
top-level instance still does exactly the job it should: witness that the
assumed properties are satisfiable, so the composition is not vacuous.

The class stays, both as the packaging for the provider and because
`Interfaces.lean` deliberately keeps `SlotConsensus` "exactly the paper's
module"; only its fields are re-expressed through the shared definitions.

A residue remains, and it is real content rather than bookkeeping: mapping
the provider's carrier to the consumer's — Chorus's per-proposer commit
relations to a `pvector` — which is the construction `Chorus/Compose.lean`
already performs. That is honest composition work; the transcription gap is
not.

**For the MVBA specifically**, doing this refactor *first* is what makes the
rest cheap. Otherwise the deliverable is `Mvba ⊨ MVBA` plus bridging lemmas
tying Chorus's `mvba_decide_pos` / `mvba_decide_neg` guards to the contract
fields; afterwards there is nothing to bridge, because the guards are the
definitions. Either way the step touches Chorus's oracle section and so
changes every VC statement in that family — budget the cold re-solve
deliberately rather than meeting it by surprise.

## 2. Liveness

**Target.** Not `thm:termination`'s `O(fΔ)` — the models are untimed and no
artefact here claims a latency bound. The target is its bound-erased
skeleton, "every correct validator eventually decides", in the form Chorus
already uses: fair-progress invariants inside the sweep, the state-level
content kernel-checked, the temporal step carried by named axioms
([`Liveness.md`](./Liveness.md)).

**Deferred, but it must not be designed out.** Two choices would foreclose
it, and the first is a correction to this plan's own first draft:

* **Do not model view advancement as unguarded nondeterminism.** Letting any
  validator jump to any higher view is safety-sound — it only adds
  behaviours — and liveness-fatal: a run that advances views forever starves
  every decision, so no well-founded ranking can exist and the fair-progress
  chain cannot be stated, let alone proven. Keep the timeout-certificate
  structure that gates advancement; abstract the *timing* only.
* **Keep view-indexed state monotone.** Accumulating relations (`voted i v`,
  `prepared i v q`) rather than a mutable current-view field. Veil's
  monotone framework is what makes enabledness monotone, which is why weak
  (F-justice) suffices; a mutable counter would break that and pull strong
  fairness — currently *not invoked* anywhere — into the argument.

Name the assumptions from the start even while the ranking is unfinished:
(F-justice) on the message handlers, (F-byz) for the adversary, and a view
synchronisation assumption standing in for after-GST Δ-synchrony. Then the
liveness work is additive rather than a re-encoding.

## 3. Vacuity

Four instruments, weakest to strongest. Only the first three are
machine-checked evidence.

1. **`sat trace` reachability witnesses.** A decide in view 1; a decide after
   a view change; a decide under a Byzantine leader; a run where a held lock
   forces re-proposal of an earlier value. cvc5's `sat` verdicts here are
   trusted, and that is deliberately harmless — a wrong model can only make
   a non-vacuity check vacuous, never a safety claim wrong
   ([`Architecture.md`](./Architecture.md) §4 item 6). Mind the parser rule:
   traces go after `#check_invariants`, and never `set_option … in`
   immediately after a trace block.
2. **Quorum non-vacuity**, following [`ByzQuorum.lean`](../Cadence/ByzQuorum.lean)'s
   witness pattern, so the quorum interface cannot be vacuously satisfiable.
3. **Mutation testing with `#model_check`** — the strongest available, and
   there is precedent:
   [`FallbackReceipt/PreFix.lean`](../Cadence/FallbackReceipt/PreFix.lean)
   pins a counterexample with `#guard_msgs` and a green build *requires* the
   violation. Do the same here: a sibling model with the lock rule removed
   should fail agreement, with the witness pinned. That demonstrates the
   invariants are load-bearing rather than merely true — which is the
   question vacuity is really asking. It must use `(sequential := true)`;
   the parallel search's frontier split is core-count dependent and the pin
   would hold only on the machine that recorded it.
4. **Monitor conformance** via `#gen_monitor`, following `Cadence/Monitor/`.
   Not in any trust base, and [`Monitor.md`](./Monitor.md) §8 already lists
   coverage gaps, so I would sequence this last and only if the monitor
   effort is being extended anyway. Note the `@[implicit_reducible]`
   warning-suppression trap that `ChorusMonitorGen.lean` documents.

**On deriving it from fairness:** no. The fairness assumptions are
meta-level and never reach the SMT layer, and they speak about *firing given
enabledness*, not about enabledness being reachable at all — which is what
vacuity asks. The fair-progress invariants carry adjacent content, but the
machine-checked non-vacuity evidence is instruments 1–3.

## 4. The model

Where things live, and the abstractions worth committing to up front.

* **Contract in [`Interfaces.lean`](../Cadence/Interfaces.lean), not
  [`Primitives.lean`](../Cadence/Primitives.lean).** `Chorus.lean` imports
  `Primitives`; editing the existing `MVBA` class there changes every Chorus
  VC statement and forces a cold re-solve of the whole family. The contract
  classes live in `Interfaces.lean` for exactly this reason.
* **`value` is the entry vector, not the metablock.** `mod:mvba` states
  agreement as metablock equality; the supplement proves the entries-level
  statement deliberately, and Chorus's oracle already works per proposer.
  Instantiating at the entry vector matches what is actually needed and what
  is actually proven.
* **Views as a total order, no arithmetic**, following Conductor's
  `TotalOrderWithMinimum` treatment of slots and windows, which keeps `+W`
  arithmetic out of the SMT layer entirely.
* **Messages monotone, local state free.** `Pre-Prepare`, `Prepare`,
  `Commit` and timeout certificates become `msg_*` relations consulted
  positively; `lastVotedView`, `PrepQC`, `lock`, `timedOut` are `local_*`.
  The monotone-network contract governs `msg_*` only, so the `¬timedOut_i`
  guard needs no exception category — worth stating, since it looks like one
  at first glance.
* **No persistence.** `persist state` and atomic reload are implementation
  obligations, recorded as an obligation-table row rather than modelled.
* **The `Recover` decision.** `TryFormCommitQC` dropped its
  `x_v ≠ ⊥ ∧ entries(x_v) = e` guard, so a validator may form the
  certificate and only then recover the value. That *removes* a guard, so it
  is the one supplement change that adds behaviour and cannot be
  conservatively ignored. Model `Recover` as an oracle relation returning a
  valid value with the decided entries.

## 5. Scale and where the risk is

Cell counts track actions × invariants closely: FallbackReceipt is 9 × 21
with 220 cells, Chorus 40 × 101 with 3 861. The MVBA's handlers and
procedures suggest 12–16 actions, and a view-change safety argument perhaps
25–40 invariants: roughly **300–650 cells**, so a small multiple of
FallbackReceipt and well under a fifth of Chorus. Volume is not the risk.

The risk is concentrated in one place: **lock persistence across views**
(`lem:lock-persistence`, `lem:cert-uniqueness`), the standard PBFT
view-change argument. Expect the quorum-intersection-across-views step to
fall outside `ByzNodeSet`'s language, the same wall Chorus hit, with the
same resolution — demote it from the invariant clump and prove it in plain
Lean beside `Counting.lean` and `Pigeonhole.lean`.

## 6. Proposed order

1. **Settle §0.** Needs a decision on visibility and the implementation
   commit; everything else can start regardless.
2. **Lift the contract properties into standalone definitions** (§1). Do
   this before anything MVBA-specific: it is a contained refactor of
   `Interfaces.lean` plus the invariants in `Cadence.lean` that restate its
   fields, it removes an unchecked seam that exists *today* for
   `SlotConsensus` and `Orchestrator` independently of any MVBA work, and it
   is what stops the MVBA arriving with a bridging problem of its own. It
   changes the consuming models' invariant statements, so it re-solves
   `Cadence` and `Conductor` — both cheap — and is worth doing while nothing
   else is in flight.
3. **MVBA contract and obligation table** in `Interfaces.lean`, expressed
   through those definitions, splitting state-predicate fields from temporal
   obligations per the file's own doctrine. Forces the `value` question
   early.
4. **Single-view spike.** Agreement within one view, no view change — the
   FallbackReceipt precedent of proving the architecture at small scale
   first. Shakes out the encoding, and its cells warm the cache.
5. **Full model and safety**, including the lock-persistence core.
6. **Vacuity**: traces, then the mutation pin.
7. **Compose**: `Mvba ⊨ MVBA`. With step 2 done this is the provider side
   only; Chorus's oracle guards become the same definitions the instance
   satisfies. This is the step that touches Chorus and pays the cold
   re-solve of that family.
8. **Liveness skeleton**, on the hooks §2 leaves in place.

Steps 3–6 are self-contained and touch no existing model. Steps 2 and 7 both
change existing models and should each be scheduled as their own piece of
work — step 2 because it is the one that pays down existing debt, step 7
because it is the one that pays the Chorus re-solve.
