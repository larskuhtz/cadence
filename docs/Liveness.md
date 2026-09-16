# Liveness — what is proven, what is assumed

*The audit summary for the liveness claim. The model-level narrative — how
the theorems and assumptions compose against Chorus's actions and
invariants — is [`ChorusDesign.md`](./ChorusDesign.md) §7; the assumption
inventory is [`Architecture.md`](./Architecture.md) §4 items 2 and 4.*

## 1. The shape of the claim

The liveness claim — under the named assumptions below, every honest
validator eventually commits — factors into state-level facts and temporal
steps. **Every state-level fact is a kernel-checked, axiom-pinned theorem**
over reachable states, for every `n = 3f+1`:

| Theorem | Says |
|---|---|
| `progress_dichotomy_of_saturation` ([`Cadence/Chorus/Progress.lean`](../Cadence/Chorus/Progress.lean)) | in any reachable state where every honest validator has cast its path vote, commitQCs exist for every proposer from honest votes alone, **or** the MVBA is invoked with per-proposer evidence in exactly the certificate form of the decision handlers' bridge and of `mvba_propose`'s validity guards |
| `evidence_pigeonhole_of_reachable` ([`Cadence/Chorus/Pigeonhole.lean`](../Cadence/Chorus/Pigeonhole.lean)) | `2f+1` honest per-proposer fallback entries always yield a FallbackQC or an EquivCert |
| `fbcert_of_honest_fallback_votes`, `fbcommitqc_of_honest_commit_votes`, `commitqc_of_honest_fast_dominant` ([`Cadence/Chorus/Counting.lean`](../Cadence/Chorus/Counting.lean)) | certificate formation: the honest population is itself the quorum; a supermajority of honest fast commit votes is a per-proposer commitQC |
| `build_totality_of_reachable` (same file) | **any** supermajority of accepted receipts, Byzantine members included, yields a buildable fallback meta-block entry per proposer — "every correct validator can propose", at the state level |

plus the fair-progress and enabledness invariants of the sweep (the
"Liveness" section of [`Cadence/Chorus.lean`](../Cadence/Chorus.lean)).

**Every temporal step is an instance of one rule** — *a continuously
enabled fair action eventually fires* — applied at named seams:
(F-justice) drives every honest validator to the dichotomy's saturation
hypothesis and fires the certificate-to-commit actions after it, and
(A-mvba) consumes the dichotomy's conclusion. Nothing else is assumed: no
counting, no case analysis, no certificate or quorum reasoning lives
outside Lean.

## 2. The assumptions, exactly

* **(F-justice)** — honest actions are weakly fair. Weak (not strong)
  fairness suffices because the model is monotone: enabledness is itself
  monotone, so the enable/disable toggle that strong fairness exists for
  cannot occur. ((F-compassion) is reserved vocabulary for the
  non-monotone implementation and never invoked.) **This justification is
  specific to Chorus and does not generalise**: it holds because a slot is
  one-shot and its state purely accumulating. `Mvba` runs views, so nine of
  its honest actions are guarded by the current view and eleven can be
  disabled outright; what replaces the argument there, and why the answer
  is still weak fairness but for a different reason, is
  [`MvbaPlan.md`](./MvbaPlan.md) §3.1 and §3.2, with the disabling facts
  proven in [`Cadence/Mvba/Progress.lean`](../Cadence/Mvba/Progress.lean)
  and the measure they are progress in — a lexicographic rank that no
  transition can raise — in
  [`Cadence/Mvba/Rank.lean`](../Cadence/Mvba/Rank.lean). **`Mvba`'s
  bound-erased termination is now proven** from named premises:
  `Mvba.termination` in
  [`Cadence/Mvba/Liveness.lean`](../Cadence/Mvba/Liveness.lean), over the
  run vocabulary of [`Cadence/Fairness.lean`](../Cadence/Fairness.lean). It
  is the first liveness result in this development that is a *theorem*
  rather than a state-level fragment with the temporal step left to a named
  axiom — the scheduling assumptions are hypotheses of the statement, which
  is the discipline §2 of this document asks for. `Mvba` also needs a
  *third* scheduling class that Chorus does not, and the reason is the
  timeout: if a timeout action's guard says nothing about time, weak
  fairness forces it to fire out of every view, including the one the
  protocol is supposed to succeed in. The model therefore carries the view
  timer as an **abstract phase marker** — `expire_timer`, a clock with
  exactly one tick — and both timeout actions are guarded on it. With that
  the timeouts are weakly fair like every other honest action, and the
  third class contains the marker alone, governed by (A-viewsync): finite
  in every view below the good one, and in the good one not before a commit
  certificate exists. A *fifth* class holds `become_avail_ready`, the
  availability layer's action, governed by (F-avail): it is unguarded, so
  leaving it under weak fairness would have proven (F-avail) and hidden the
  MVBA's dependence on that layer behind "the scheduler is fair".
  Why (A-viewsync) has the shape it does, why the marker cannot be weakly
  fair, and why a GST marker alone would not change either, are
  [`MvbaPlan.md`](./MvbaPlan.md) §3.7. Those two clauses are the untimed skeleton of the
  supplement's timeout discipline, and they are the *whole* of what
  `Mvba.termination` assumes about timing —
  [`MvbaPlan.md`](./MvbaPlan.md) §3.2's correction, with the classification
  machine-checked in
  [`Cadence/Mvba/Liveness.lean`](../Cadence/Mvba/Liveness.lean).
* **(F-byz)** — Byzantine actions (the `byz_*` family) are unfair:
  progress never relies on adversarial help, which makes the discharged
  content strictly stronger than deadlock freedom.
* **(A-mvba)** — the MVBA primitive's own liveness: invoked with
  per-proposer evidence, it eventually decides every proposer and
  terminates. The randomised primitive terminates with probability 1,
  which no deductive framework expresses — the probability argument stays
  on paper, exactly as for any cryptographic primitive contract.
* Scheduling is distinct from **network delivery**. The monotone network
  makes broadcast signatures globally visible, so delivery surfaces only
  as fairness on the observation actions (`record_chunk`,
  `redisseminate_chunk`, `aggregate_fastqc_*`); the network abstraction's
  own soundness contract is [`Architecture.md`](./Architecture.md) §4
  item 1.

The well-founded ranking that makes the chain terminate is structural:
per-slot state is finite and all relations are monotone, so every fair
firing strictly shrinks the residual of unset tuples. It rests on the same
monotonicity audit as the network contract. Finiteness is what makes it
work, so this ranking is also Chorus-specific: `Mvba`'s view type is
unbounded and needs the different, lexicographic ranking of
[`MvbaPlan.md`](./MvbaPlan.md) §3.3.

### 2.1 Why `Mvba` assumes more than `Chorus`, and where that ends

`Chorus`'s liveness rests on fairness plus the sub-protocol's own
termination, and nothing that names a view or a deadline. `Mvba`'s rests on
those plus (A-viewsync). The difference looks like a weakness of the MVBA
proof and is not: it is the whole stack's one unavoidable assumption becoming
visible at the layer that has to carry it.

**The two models use the same timing device.** `Chorus.lean` has an abstract
`Phase` — `pre_deadline → post_deadline → post_fb_arm → post_mvba_arm`,
advanced by three non-deterministic actions — and `Mvba.lean` has
`timer_expired`, the same device with one tick instead of three. Both replace
wall-clock time by a monotone marker, and both gate real actions on it
(`record_chunk` needs `pre_deadline`; the two `timeout_*` need
`timer_expired`). So the shapes are the same.

**Chorus's markers are weakly fair and `Mvba`'s is not**, and the reason is
what each advance *does*. Chorus's phases move the protocol from one arm to
the next: fast path, then fallback, then the MVBA arm. Advancing early
forfeits the faster arm and nothing else — there is always somewhere to fall
— and termination is then delegated to **(A-mvba)**, the sub-protocol's own.
`Mvba`'s view *is* that last arm. A timer firing early forfeits the view, and
the only thing to fall onto is another view; if every view's timer fires
early, nothing terminates at all. There is no sub-protocol left to delegate
to, so the assumption that *some* view survives its timeout has to be made
here.

That is FLP, paid where it must be. The paper pays it twice over, in the two
MVBA options: the randomised primitive pays with probability-1 termination
(no deductive framework here expresses that), and the supplement's
leader-based protocol — the one modelled — pays with partial synchrony.
(A-viewsync) is the untimed shadow of the second payment.

**Chorus does have an (A-viewsync)-shaped premise; it is just somewhere
else.** `all_honest_recorded` — "every honest validator recorded the positive
entry", in the model's own words the protocol-level shadow of
`s.deadline − Δ ≥ GST` — is exactly "the work finished before the marker
advanced". It is carried as an **antecedent of the properties** (proposal
inclusion, and the fair-progress invariants that rest on it) rather than as a
run-level premise, and it buys *proposal inclusion* rather than termination,
which is why it does not appear in a fairness list. The accounting differs;
the assumption is of the same kind.

**Where it ends.** What this work does to the stack's trust base is replace
an unconditional consensus-termination assumption by a synchroniser interface
plus a proof: (A-mvba) says "the MVBA terminates", `Mvba.termination` says
"it terminates given (A-viewsync), (F-justice), (F-avail) and the callers'
two premises", and half of (A-viewsync) — the entry — is itself derived.
The replacement is not yet formal: `Mvba.termination` is the **bound-erased
shadow** of `MVBATemporal.termination`, not that field, which is stated over
timed runs with `gst` and `ℓ`. Connecting them is the bounded phase, and the
untimed theorem is already in the right shape for it — every premise is a
predicate on a run, so a timed layer discharges them as ordinary Lean
theorems without touching the model, which is the pattern
[`Bounds.md`](./Bounds.md) §6 sets out for Chorus. In that phase (A-viewsync)
stops being an assumption: with a clock, bounded post-GST delivery gives the
decision chain a finite latency, timeout growth makes some view's budget
exceed it, and both of its clauses become theorems.
[`MvbaPlan.md`](./MvbaPlan.md) §3.7 has the detail, including why no
intermediate step — a GST marker without a clock, say — gets there earlier.

## 3. What would close the rest

Veil has no fairness annotations and no quantification over runs, so the
rule "continuously enabled ⇒ eventually fires" is not expressible today.
The designed extension — fairness classes on actions,
ω-acceptance/response properties, discharged by the POPL'18
**liveness-to-safety** reduction on the existing safety-VC pipeline — is
Veil work and lives in the fork: **`docs/Liveness.md` on the
`lars/liveness` branch of `larskuhtz/veil`**. With it, (F-justice) becomes
the premise of a Lean theorem and the deterministic liveness properties
("honest fast-path commit eventually", "slot eventually decides") become
provable in-system. (A-mvba)'s probability-1 core, and real-time bounds
(GST, latency — the models are untimed), stay out of scope regardless.

The paper's concrete Δ-bounds are a separate, *incomparable* layer — they
assume strong partial synchrony, where the model's claims above need only
eventual delivery. How the two relate, and the routes by which bounds
could be brought into the model, is [`Bounds.md`](./Bounds.md).

## 4. The next leg: Chorus at run level

`Mvba.termination` is the pattern working at one layer. Applying it to
Chorus is what retires **(A-mvba)** — and with it the last of the
`(F-justice)`/`(F-byz)`/`(A-mvba)` meta-axioms — which
[`TODO.md`](./TODO.md) calls the single largest reduction of
[`Architecture.md`](./Architecture.md) §4 available. This section is the
kick-off record so a fresh session does not re-derive the design.

**Target.** A run-level theorem in the shape of `Mvba.termination`: every
correct validator eventually finalizes every slot, from named premises, each
a predicate on a run, with `Mvba.termination` consumed exactly where
(A-mvba) sits today. Same discipline as `Mvba/Liveness.lean`: the premises
are written down as named `Prop`s **before** the proof exists, so none can
become a hypothesis because a proof needed it.

**What is already there.** [`Cadence/Fairness.lean`](../Cadence/Fairness.lean)
is generic over any `RelationalTransitionSystem`, so `LRun`, `WeaklyFair`,
`eventually_forall` and the rest apply to Chorus unchanged. Chorus's
fair-progress content is proven at state level (`Chorus.lean`'s liveness
section), and the two hardest counting steps are already plain-Lean
theorems: `progress_dichotomy_of_saturation` and
`build_totality_of_reachable`. Chorus's phase markers are weakly fair, so
unlike the MVBA there is no timing premise to invent — §2.1 says why.

**Settle this first, because it is the whole design.** Chorus holds an
*abstract* MVBA state and advances it with the oracle action `mvba_step`,
which takes any transition the contract allows and is deliberately **outside**
(F-justice) — its scheduling is the instance's own admissible-execution
model. So consuming `Mvba.termination` needs a **projection**: from an
`LRun` of the composed system (`System.lean`, where the abstract state is
`Mvba.State`) to an `MvbaRun`, keeping only the steps at which the MVBA
state moved, and a proof that weak fairness survives the re-indexing — a
label continuously enabled in the projection was continuously enabled in the
composed run. The premise that replaces (A-mvba) is then "the composed run's
MVBA projection satisfies `Mvba.termination`'s premises", which is the
untimed analogue of `MVBATemporal.Admissible`. It must be built that way and
**not** by weakening a class field: that rule is in
[`../CLAUDE.md`](../CLAUDE.md) and it is what makes the absence of a
`…Temporal` instance mean something.

**Staging** (reassess after step 1, which is the risky one):

1. ~~The projection and the fairness transfer, generic, in `Fairness.lean`.~~
   **Done, 2026-09-16** — §4.2 is the record and the reassessment.
2. ~~Chorus's label classes and premises — one named `Prop` each, mirroring
   `Mvba/Liveness.lean`'s four-class discipline and its `label_classified`;
   and the `Component` instance for Chorus at the `Mvba` instantiation.~~
   **Done, 2026-09-16** — [`Cadence/Chorus/Liveness.lean`](../Cadence/Chorus/Liveness.lean);
   §4.3 is the record, including the one premise the sketch above did not
   foresee.
3. The fast-path chain to a commit certificate.
4. The fallback and MVBA arms, the second consuming `Mvba.termination`
   through the projection.
5. The assembly, the `Cadence.lean` row and pin, and retiring (A-mvba) from
   `Architecture.md` §4.

**Cost warning.** If the argument needs new Chorus invariants, that is a
4 222-cell family re-solve, not the MVBA's 1 325. Budget it before touching
`Chorus.lean`, even for a comment.

### 4.1 Running this leg and the bounds leg in parallel

This leg and [`Bounds.md`](./Bounds.md) §6.1 are **independent**: neither
needs the other's result, and the MVBA bounds leg discharges
(A-viewsync) while this one consumes `Mvba.termination` as it already
stands. Rules that keep them from colliding:

* **Neither leg edits [`Cadence/Interfaces.lean`](../Cadence/Interfaces.lean).**
  The bounds leg *instantiates* `MVBATemporal`, it does not change it; this
  leg needs no class change. An edit there re-solves the Chorus family and
  forces the other leg to rebase, so it is a decision to take jointly.
* **[`Cadence/Mvba/Liveness.lean`](../Cadence/Mvba/Liveness.lean) is
  read-only for both.** Both consume `Mvba.termination`; neither should need
  to restate or reshape it.
* **This leg owns `Fairness.lean` and everything under `Cadence/Chorus`**;
  the bounds leg owns its own new files and puts *timed* run vocabulary in
  one of them rather than in `Fairness.lean`.
* **The projection is shared conceptual territory** — the bounds leg needs
  the same relation between a composed run and an MVBA run, in its timed
  form. This leg owns the definition — it is `Cadence.Component` and
  `Component.Projection` in [`Cadence/Fairness.lean`](../Cadence/Fairness.lean)
  since 2026-09-16 (§4.2) — and the bounds leg should refine it rather than
  invent a second one: a timed projection is a `Projection` whose composed
  run carries a clock, and the index map `Component.idx`/`Component.cover`
  is what relates the two clocks.
* Both will append rows and pins to `Cadence.lean` and paragraphs to these
  docs. Expect small textual conflicts there and nothing worse.
* **One expensive build at a time.** That constraint does not parallelise:
  the machine runs one family re-solve at a time, and this leg's are the
  large ones. Two sessions can think in parallel; they cannot both re-solve
  in parallel.

### 4.2 Stage 1, done: the projection, and what it settled

*Record of 2026-09-16. The code is the "Components" half of
[`Cadence/Fairness.lean`](../Cadence/Fairness.lean); every declaration named
below is there, and the file's own docstrings carry the reasoning at the
point of use.*

**What was built.** A `Component sys th sub th'` is one Veil module held
inside another, given by five first-order facts: the state projection
`proj`, the outer labels `isSub` that are the part's own steps, the transfer
of initial states (`init`, which also hands over the part's theory
assumptions), the frame law for every other label, and `step` — a step of the
part taken by the whole is a transition of the part under *some* label of
its own. A `Component.Projection C r` of a composed run `r` is a labelling of
the part's steps by part labels that explain them (`lbl`, `realizes`)
together with `scheduled` — the part is stepped infinitely often. From it,
`Projection.run : LRun sub th'` is the projected run: the part's state at
each of its steps, indexed through Mathlib's `Nat.nth`. Then:

* `Projection.weaklyFair_iff` — **weak fairness survives the re-indexing, as
  an equivalence**: `WeaklyFair p.run l'` iff the composed-run reading
  `p.WeaklyFairIn l'` (enabled at the part's state at every composed index
  from `N` on ⇒ the whole takes a step of the part labelled `l'` at some
  composed index from `N` on). The right-to-left direction is the one §4
  asked for — "a label continuously enabled in the projection was
  continuously enabled in the composed run" — and it holds because the
  part's state is constant between its steps. That it is an *iff* is what
  makes the premise readable at either level with nothing smuggled in.
* `Projection.proj_eq_run_cover` — the state correspondence: the part's
  state at any composed index is a state of the projected run (at
  `Component.cover n`, the number of the part's steps before `n`), and every
  projected state is by definition the part of a composed one. The three
  temporal shapes follow as equivalences (`eventually_iff`, `always_iff`,
  `leadsTo_iff`); these carry a caller's premise into the part's run and the
  part's conclusion back.
* `Component.reachable_proj` — the part's state at every composed index is
  reachable in the part's own system, with **no** scheduling hypothesis. So
  every invariant the inner module proves holds of the state the outer
  module holds — which for Chorus is what its `mvba_reachable` invariant
  says, now derived rather than swept.
* `Projection.ofScheduled` — a labelling always exists, so the only content
  of a premise of the form "there is a projection satisfying …" is what is
  asked of the projection, never its existence.

Every pin is at the standard trio; `Fairness.lean`'s trust-base section
lists them.

**Two design decisions the stage forced, and why they went the way they did.**

1. *The premise quantifies over a labelling.* The composed run does not
   record which MVBA action fired: Chorus's `mvba_step` carries only the next
   MVBA state, and two MVBA labels can explain the same step (any always-
   enabled action that re-sets a bit already set, for one). A weak-fairness
   statement is about labels, so it cannot be *derived* for a projection
   whose labels are chosen by the projection; it has to be *assumed of* a
   labelling. The premise replacing (A-mvba) is therefore of the shape
   "∃ `p : C.Projection r`, `Mvba.FJustice p.run ∧ Mvba.AViewSync p.run ∧
   Mvba.FAvail p.run`" — literally "the composed run's MVBA projection
   satisfies `Mvba.termination`'s scheduling premises", stated with
   `Mvba/Liveness.lean`'s own definitions and restating none of them. This
   is the honest form: the composed model erased the labels, so an assumption
   about how the MVBA was scheduled has to put them back. The alternative —
   stating the MVBA fairness on the composed run in terms of `mvba.step`
   alone — is not weaker, it is *unstatable*: without a labelling there is no
   "this label fired".
2. *Infinitude is part of the projection.* `LRun` is an infinite sequence, so
   an MVBA that is stepped only finitely often has no run in its own
   vocabulary and `Mvba.termination` cannot be applied to it.
   `Component.Scheduled` — the part is stepped infinitely often — is
   therefore a field of `Projection` and so part of the premise. It is a
   scheduling assumption about the whole (the MVBA is not starved), weaker
   than weak fairness of `mvba_step` since it says nothing about *which* MVBA
   step is taken, and it is not vacuous at the `Mvba` instance because
   `become_avail_ready` is unguarded, so the MVBA always has a step
   available. It does **not** move `mvba_step` into Chorus's (F-justice): the
   oracle step stays unfair in Chorus's classification, and the MVBA's
   scheduling is entirely the new premise's business — which is where §4
   said it belongs.

**Reassessment (the point of stopping here).** The risky step was the
generic one, and it is done at the standard trio with no model change and
no cell added. Stage 2's first item — the `Component` instance for Chorus at
`mvba := Mvba.mvbaSafety thM` — was then validated in scratch to make sure
the generic shape fits the generated Chorus artefacts, and it does, from
three sources and one hand proof:

* `isSub` is a two-constructor match on `Chorus.Label`
  (`mvba_step`, `mvba_propose`);
* `frame` is one generated lemma per other action — M13's
  `Chorus.<action>.frame_mvba_st`, all 38 exist — dispatched by `cases l`
  with one `case <action> =>` line each. Two things to know: the `MVBASafety`
  instance has to be put in scope with `letI := Mvba.mvbaSafety thM` before
  the lemmas will apply (the instance is a *term* at the composed
  instantiation, not a local instance), and dispatching with a `first | …`
  list over the 40 lemmas instead of named cases times out in `whnf` — each
  failing alternative makes the unifier unfold the transition system;
* `step` is the two oracle actions' guards read off their transition bodies
  (`chorus_tr`-style: `simp only [Chorus.relationalTransitionSystem,
  Chorus.Next, Chorus.NextAct]`, then `trSimp`, then the canonical
  field-representation simp set): `mvba_step` requires `mvba.step`, which at
  the `Mvba` instance *is* "some non-input label's transition", and
  `mvba_propose` requires `mvba.propose`, which is the `propose` label's;
* `init` needs the one hand proof: `mvba_st` is seeded from the theory's
  `mvba_init_state`, not a literal, so M13 emits no `mvba_st.init` lemma. It
  is read off the initializer's transition (`Chorus.initializer.ext.tr`) by
  exposing it and evaluating the field representation — the initializer has
  a single leaf, so nothing has to be destructured — and the value it hands
  over is exactly what Chorus's `[mvba_init]` assumption speaks about: at
  the `Mvba` instance that assumption *is* `sub.assumptions ∧ sub.init`, the
  two halves of `Component.init`.

So the shape is right and stage 2 is bounded work: the instance file, the
label classes, and the premises (§4.3 — done the same day, and the scratch
instance graduated into it). Nothing in this stage touches `Chorus.lean`,
`Interfaces.lean` or `Mvba/Liveness.lean`, and the 4 222-cell family is
untouched.

**What to watch in stages 3–5.** The `Scheduled` field makes the final
theorem silent about runs in which the MVBA is stepped finitely often. That
is correct (it excludes unfair schedulers, as every fairness premise does),
but it is a premise the paper does not spell out, so it must appear by name
in `Architecture.md` §4 when (A-mvba) is retired, not be absorbed into
"(F-justice)".

### 4.3 Stage 2, done: the classification, the premises, the target

*Record of 2026-09-16. The file is
[`Cadence/Chorus/Liveness.lean`](../Cadence/Chorus/Liveness.lean), a
sibling of [`Cadence/Mvba/Liveness.lean`](../Cadence/Mvba/Liveness.lean)
in shape and discipline; `grep -n '^def [A-Z]'` on it prints everything a
human has to believe. Its header carries the reasoning at the point of
use; this section is the audit summary and the one correction to §4's
sketch.*

**The classification.** Three `match` definitions over `Chorus.Label`:
`ByzLabel` (the thirteen `byz_*` actions — (F-byz)), `OracleLabel` (the
oracle step `mvba_step` alone), and `JusticeLabel` as their complement —
(F-justice) — with `label_classified` pinning exhaustiveness and
`not_justice_of_byz` / `not_justice_of_oracle` the disjointness. A fourth,
`MvbaStepLabel` (`mvba_step` and `mvba_propose`), is the *component's* cut,
not a fairness class: `mvba_propose` is Chorus's own weakly fair action
that also advances the MVBA, and it appears in the projected run as the
MVBA's `propose` input, which `Mvba.FJustice` excludes for exactly that
reason. Against `Chorus.lean`'s prose list of (F-justice) actions the
complement form also covers `deliver_chunk_assigned` and
`broadcast_commitqc_*`, which §7 of `ChorusDesign.md` already uses as
fair; the model's prose should be aligned the next time `Chorus.lean` is
edited for another reason (a comment edit is a family re-solve).

**The component instance.** `Chorus.mvbaComponent thS thM : Component
(atMvba thM) thS mvbaRTS thM` — §4.2's recipe, landed: `frame` from the 38
generated lemmas, `step` from the two oracle guards, `init` from the
initializer, and no new cell.

**The premises, one named `Prop` each**, over `ChorusRun thS thM` (a
labelled run of Chorus with its MVBA constraint filled by `Mvba.mvbaSafety
thM`, the instantiation `System.lean` uses):

* **`FJustice`** — (F-justice): weak fairness of every `JusticeLabel`.
* **`MvbaAdmissible`** — replaces (A-mvba): `∃ p : (mvbaComponent thS
  thM).Projection r, Mvba.FJustice p.run ∧ Mvba.AViewSync p.run ∧
  Mvba.FAvail p.run` — the run's MVBA projection satisfies the three
  *scheduling* premises of `Mvba.termination`, stated with that file's
  definitions. The theorem's other two premises — every correct validator
  proposes, none is abandoned before deciding — are the caller's, and the
  caller is Chorus, so stage 4 derives them rather than assuming them.
* **`ValidBridge`** — **the premise §4 did not foresee.** The sketch
  planned one bridge-side premise, the *completeness* direction ("a
  decided vector's certificates are on the network", which enables the
  decision handlers). Writing the claim down showed the *soundness*
  direction is a premise too: `mvba_propose`'s last guard is the
  contract's `propose`, and `Mvba.propose` requires `valid e` of its
  input (`MVBASafety.propose_valid` — the "wart" `Interfaces.lean`
  documents), while the MVBA theory's `valid` is a predicate on the
  vector alone that nothing in the composed system relates to Chorus's
  certificates. So a correct validator that has built a certified
  meta-block can call `propose` only if certified vectors are `Valid`.
  The premise therefore has two clauses, both at every point of the run
  and both stated with `Certified` — `mvba_propose`'s three validity
  guards verbatim, the first two of which are the handlers' bridge
  `require`: certified ⇒ `Valid`, and decided by a correct validator ⇒
  certified. It is the run-level form of the one stated bridge
  (`CompositionContracts.md` §3, §7 item 1) and its content is the
  cryptographic one — a `Valid` meta-block's certificates are genuine and
  genuine certificates are `Valid` — which no class field can carry
  because `Valid` is fixed before Chorus's state exists. The safety proofs
  need neither direction.

**The target.** `Terminates r`: every correct validator eventually has
`local_committed` — `finalize_commit` fired for it — and
`TerminationClaim thS thM := ∀ r, FJustice r → MvbaAdmissible r →
ValidBridge r → Terminates r`. A definition, asserted nowhere; the theorem
is stages 3–5's. Absent by design: any timing premise (§2.1), any
`all_honest_recorded`-shaped premise (it buys proposal inclusion, not
termination), and the quorum machinery (the concrete family the counting
theorems are stated over, `byzNodeSetFin` at every `n = 3f+1`, and
`Mvba.termination`'s three class hypotheses are hypotheses of the theorem,
not part of the claim).

**What to watch in stages 3–5**, in addition to §4.2's note on
`Scheduled`: the theorem will be at the concrete quorum family and at
`System.lean`'s `chorusTheory` (the entry-vector projections have to be the
standard ones to *build* a proposal), so `TerminationClaim` stays generic
and the theorem instantiates it; and `ValidBridge` must be named in
`Architecture.md` §4 alongside `MvbaAdmissible` when (A-mvba) is retired —
it is not a fairness assumption and must not be filed as one.
