# Liveness — what is proven, what is assumed

*The untimed liveness claims, and the walk-through of the proof of
`Chorus.termination`. [The guide's chapter 6](https://larskuhtz.github.io/cadence/guide/components/) introduces
the claims.*

The audit summary for the untimed liveness claims, and how
`Chorus.termination` is proven (§4). The premises of every liveness claim,
timed and untimed, are listed once in [Premises.md](Premises.md). The
model-level narrative — how the theorems and assumptions compose against
Chorus's actions and invariants — is [ChorusDesign.md](ChorusDesign.md) §7;
the assumption inventory is [Architecture.md](Architecture.md) §4 items 2
and 4; the timed claims are [Bounds.md](Bounds.md). §4 is a proof
walk-through, step by step.

## 1. The shape of the claim

The liveness claim — under the named assumptions below, every honest
validator eventually commits — factors into state-level facts and temporal
steps. **Every state-level fact is a kernel-checked, axiom-pinned theorem**
over reachable states, for every `n = 3f+1`:

| Theorem | Says |
|---|---|
| `progress_dichotomy_of_saturation` ([Cadence/Chorus/Progress.lean](../Cadence/Chorus/Progress.lean)) | in any reachable state where every honest validator has cast its path vote, commitQCs exist for every proposer from honest votes alone, **or** the MVBA is invoked with per-proposer evidence in exactly the certificate form of the decision handlers' bridge and of `mvba_propose`'s validity guards |
| `evidence_pigeonhole_of_reachable` ([Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean)) | `2f+1` honest per-proposer fallback entries always yield a FallbackQC or an EquivCert |
| `fbcert_of_honest_fallback_votes`, `fbcommitqc_of_honest_commit_votes`, `commitqc_of_honest_fast_dominant` ([Cadence/Chorus/Counting.lean](../Cadence/Chorus/Counting.lean)) | certificate formation: the honest population is itself the quorum; a supermajority of honest fast commit votes is a per-proposer commitQC |
| `build_totality_of_reachable` (same file) | **any** supermajority of accepted receipts, Byzantine members included, yields a buildable fallback meta-block entry per proposer — "every correct validator can propose", at the state level |

plus the fair-progress and enabledness invariants of the sweep (the
"Liveness" section of [Cadence/Chorus.lean](../Cadence/Chorus.lean)).

**The temporal steps are a theorem too.** `Chorus.termination`
([Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)) is the claim itself, as a
Lean theorem over runs: at every `n = 3f+1`, in the configuration the
composed system runs, every run satisfying the five premises of §2
terminates — every correct validator finalizes the slot. Each temporal step
in its proof is an instance of one rule, *a continuously enabled fair action
eventually fires*. If some correct validator finalizes, the others finalize
from its commitment proof. If none does, (F-justice) drives every correct
validator to the dichotomy's saturation hypothesis, and then fires the
proposal to the MVBA, the decision handlers and the fallback commit round.
The MVBA's own termination is not assumed there. It is `Mvba.termination`,
applied to the run's MVBA steps. No counting, case analysis, certificate or
quorum reasoning lives outside Lean. What does is the premises, and whether
they can all hold at once: one model meets all of them
(`Chorus.termination_premises_satisfiable`,
[Premises.md](Premises.md)). §4 is the structure of the proof.

## 2. The assumptions, exactly

`Chorus.termination` takes five premises, each a named `Prop` in
[Cadence/Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean):
`FJustice`, `MvbaAdmissible`, `ValidBridge`, `AllParticipate` and
`NoAbandonBeforeFinalizing`. [Premises.md](Premises.md) has each in one
line, with why it is plausible, its witness and where it is used, for
this claim and every other; this section explains the choices behind
them.

The first three are about the run; the last two are about the caller, and
they are exactly the antecedents of the contract's own
`SlotConsensusTemporal.termination`. Within Cadence the glue meets them: it
participates when it opens a slot and abandons only once it has finalized
(Algorithm 1, line 17 (`line:participate`), Algorithm 1, line 23 (`line:abandon`)).

Its other hypotheses fix the setting: validators `Fin n` with `n = 3f+1`
and at most `f` Byzantine, the system's Chorus configuration
(`Cadence.chorusTheory`), and the view order's enumeration that
`Mvba.termination` takes. The bullets below give the detail, one premise
each.

* **(F-justice)** (`FJustice`) — honest actions are weakly fair, except the
  module's three inputs (`participate`, `abandon`, `propose`), which the
  caller invokes. *Weakly fair* means: an action enabled at every point
  from some index on fires at some point from that index on
  ([Cadence/Fairness.lean](../Cadence/Fairness.lean)). Every fair action
  of the model fires once: its guard requires a record its own step sets
  to be unset, as the paper's "not already" rules do. So an enabled fair
  action can always change the state, which the model checks for every
  fair label at every state (`Chorus.justice_enabledMove`), and the premise
  can hold at every quorum sort. It is therefore the same premise as TLA+'s
  `WF_v`, weak fairness over state-changing steps
  (`Chorus.fJustice_iff_move`; [Bounds.md](Bounds.md) §6.4.7 explains the
  fired-once guards). The inputs are classified apart (`Chorus.InputLabel`), and
  that is load-bearing: fairness of `abandon` would force every validator
  to abandon. Weak (not strong)
  fairness suffices because the model is monotone: apart from each
  action's fired-once guard, which only its own firing sets, enabledness is
  itself monotone, so the enable/disable toggle that strong fairness exists
  for cannot occur. ((F-compassion) is reserved vocabulary for the
  non-monotone implementation and never invoked.) **A step is owed only for
  messages from correct senders** (`Chorus.Owed`): the paper's
  network delivers "every message between correct validators", and a
  Byzantine validator may send to some validators only. So a vote quorum,
  a certificate or a chunk source a step relies on must be correct, or
  forwarded by a correct validator (a correct fast voter's `FastBlock`, a
  correct fallback signer's re-dissemination, a correct finalizer's
  commitment proof); the timed rows take the same conditions
  ([Bounds.md](Bounds.md) §6.4.2, F5, F7, F8). Two actions are fair as
  families rather than label by label: a correct validator proposing a
  value to the MVBA — if it can from some point on, it does, whatever the
  MVBA's state after the input turns out to be (§4.6, Finding 2) — and a
  correct validator handing a decided MVBA certificate to its own MVBA
  (`accept_mvba_commitqc`, owed once a correct validator has decided); the
  availability report `mvba_avail_ready` is a family in the same way. **This justification is
  specific to Chorus and does not generalise**: it holds because a slot is
  one-shot and its state purely accumulating. `Mvba` runs views, so nine of
  its honest actions are guarded by the current view and eleven can be
  disabled outright; what replaces the argument there, and why the answer
  is still weak fairness but for a different reason, is
  [MvbaPlan.md](MvbaPlan.md) §3.1 and §3.2, with the disabling facts
  proven in [Cadence/Mvba/Progress.lean](../Cadence/Mvba/Progress.lean)
  and the measure they are progress in — a lexicographic rank that no
  transition can raise — in
  [Cadence/Mvba/Rank.lean](../Cadence/Mvba/Rank.lean). **`Mvba`'s
  bound-erased termination is proven** from named premises:
  `Mvba.termination` in
  [Cadence/Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean), over the
  run vocabulary of [Cadence/Fairness.lean](../Cadence/Fairness.lean): its
  scheduling assumptions are hypotheses of the statement, as every
  premise in this section is. `Mvba` also needs a
  *third* scheduling class that Chorus does not, and the reason is the
  timeout: if a timeout action's guard says nothing about time, weak
  fairness forces it to fire out of every view, including the one the
  protocol is supposed to succeed in. The model therefore carries the view
  timer as an **abstract phase marker** — `expire_timer`, a clock with
  exactly one tick — and both timeout actions are guarded on it. With that
  the timeouts are weakly fair like every other honest action, and the
  third class contains the marker alone, governed by (A-viewsync): finite
  in every view below the good one, and in the good one not before a
  correct validator has decided. The MVBA's weak fairness is owed only for
  a correct leader's proposal and correct quorums' votes (`Mvba.Owed`), and
  taking a transferred certificate is the caller's input `decide`, whose
  handoff is its own premise (F-relay): the composing layer hands a correct
  validator's decided certificate on. A *fifth* class holds `become_avail_ready`, the
  availability layer's action, governed by (F-avail): it is unguarded, so
  leaving it under weak fairness would have proven (F-avail) and hidden the
  MVBA's dependence on that layer behind "the scheduler is fair".
  Why (A-viewsync) has the shape it does, why the marker cannot be weakly
  fair, and why a GST marker alone would not change either, are
  [MvbaPlan.md](MvbaPlan.md) §3.7. Those two clauses are the untimed skeleton of the
  supplement's timeout discipline, and they are the *whole* of what
  `Mvba.termination` assumes about timing —
  [MvbaPlan.md](MvbaPlan.md) §3.2's correction, with the classification
  machine-checked in
  [Cadence/Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean).
* **(F-byz)** — Byzantine actions (the `byz_*` family) are unfair:
  progress never relies on adversarial help, which makes the discharged
  content strictly stronger than deadlock freedom.
* **The MVBA's scheduling** (`MvbaAdmissible`) — the run's MVBA steps,
  read as a run of the MVBA model, satisfy the two scheduling premises of
  `Mvba.termination`: weak fairness of the MVBA's honest actions, and
  (A-viewsync) (above, and §2.1). The premise says the run *has*
  such a reading: a labelling of its MVBA steps (the composed run records
  only the MVBA's states), and infinitely many of them
  (`Component.Scheduled`, part of `Component.Projection` in
  [Cadence/Fairness.lean](../Cadence/Fairness.lean)). The other four premises of
  `Mvba.termination` belong to its caller, Chorus: every correct validator
  proposes, none is abandoned before deciding, decided certificates are
  handed on (F-relay), and the availability shares arrive (F-avail). They
  are **derived**, not assumed. The fourth is (F-justice) on Chorus's
  availability report `mvba_avail_ready`, owed once the validator holds the
  meta-block, whose chunk wait the correct FallbackQC signers met when they
  signed (`Chorus.fAvail_of_fJustice`). The timed (Δ-avail) is derived too
  (`Chorus.availWithin_of_timedJustice`, under the schedule's
  `Δ ≤ Δ_sync`; F15, [Bounds.md](Bounds.md) §6.4.2). The second holds
  on the branch of the proof that needs the MVBA: there no correct
  validator ever finalizes, so by `NoAbandonBeforeFinalizing` none
  abandons, and the MVBA's `abandon()` is invoked only by Chorus's
  `abandon` (Algorithm 5, line 48 (`line:fb-abandon`)). The third is (F-justice) on the
  decider's broadcast `send_mvba_cert` and the receiver's handoff
  `accept_mvba_commitqc`, on the same branch, where every correct decider
  is active (`Chorus.fRelay_of_fJustice`; the timed twin is
  `Chorus.relayedWhileActive_of_timedJustice`, for the MVBA's (Δ-relay),
  owed while the decider takes part). On the other branch some
  correct validator has finalized, and the others finalize from its
  commitment proof without the MVBA.
* **The bridge** (`ValidBridge`) — the MVBA's `Valid` holds exactly for
  the meta-blocks whose entries carry certificates on Chorus's network, in
  both directions the proof uses: a certified meta-block is `Valid` (so a
  correct validator can propose it), and a meta-block a correct validator
  decided or holds in its MVBA is certified (so the decision handlers are
  enabled, and the `FallbackQC` entries a validator waits under for its
  availability report have a correct signer). The second reading, at a
  held meta-block, reads the MVBA's internal `accepted`; the abstract
  module exposes no such observable ([PaperAlignment.md](PaperAlignment.md) §6, P12). This is the
  **cryptographic seam** between the two models: certificates cannot be
  forged, and a decided value's certificates are publicly verifiable. It
  says nothing about scheduling. `Valid` is a parameter of the MVBA contract,
  fixed before Chorus's state exists, so no class field can carry this.
  [CompositionContracts.md](CompositionContracts.md) §7 item 1 names the seam.
* **The MVBA's termination is a theorem, not a premise.** The instance
  Chorus runs is the supplement's leader-based protocol, and the two
  premises above are all `Chorus.termination` asks of it: its termination
  is `Mvba.termination`, applied to the run's MVBA steps. (The model's
  prose calls the assumption this replaced (A-mvba).) The randomised
  primitive of the published paper terminates with probability 1, which no
  deductive framework expresses, so that argument stays on paper, as for
  any cryptographic primitive; it is not part of this development's claim.
* Scheduling is distinct from **network delivery**. A message is on the
  network from its send on and names its sender, so delivery surfaces only
  as fairness on the receiving actions (`record_chunk`, the vote receipts
  `receive_vote_*`, `aggregate_fastqc_*`, the handoff
  `accept_mvba_commitqc`, the commit routes `commit_assign_*`), owed for
  correct senders; a proposer's chunks are sent inside its `propose`, a
  fallback signer's inside its signing step (F15); the network
  abstraction's own soundness contract is
  [Architecture.md](Architecture.md) §4 item 1.

The well-founded ranking that makes the chain terminate is structural:
per-slot state is finite and all relations are monotone, so every fair
firing strictly shrinks the residual of unset tuples. It rests on the same
monotonicity audit as the network contract. Finiteness is what makes it
work, so this ranking is also Chorus-specific: `Mvba`'s view type is
unbounded and needs the different, lexicographic ranking of
[MvbaPlan.md](MvbaPlan.md) §3.3.

### 2.1 Why `Mvba` assumes more than `Chorus`, and where that ends

**(A-viewsync) in short.** The MVBA model has a view timer but no clock, so
nothing in the model says *when* a timer fires. (A-viewsync) replaces the
timer's durations by two ordering constraints about some correct-led view
`W`:

* **not too late**: in every view below `W`, a correct validator's timer
  does eventually fire, so correct validators move on;
* **not too early**: in `W`, no correct validator's timer fires before a
  correct validator has decided, so `W` gets enough time. (A commit
  certificate alone is not enough: one the adversary assembles may reach
  nobody; [Bounds.md](Bounds.md) §6.4.2.)

Both are needed. Without the first, a Byzantine leader's view can stall
forever. Without the second, every view can be cut short. With them,
`Mvba.termination` says: *given enough time, the protocol decides*. The
bound is set aside, not the synchrony. The supplement's own assumptions,
delivery within `Δ` after GST and a timeout above the chain's latency,
imply both constraints (`Mvba.aViewSync_of_sync`), and they also give the
bound itself (`Mvba.mvbaTemporal`, [Bounds.md](Bounds.md) §6.2).

`Chorus`'s liveness rests on fairness plus the sub-protocol's own
termination, and nothing that names a view or a deadline. `Mvba`'s rests on
those plus (A-viewsync). The difference looks like a weakness of the MVBA
proof and is not: it is the whole stack's one unavoidable assumption becoming
visible at the layer that has to carry it.

**The two models use the same timing device.** [Chorus.lean](../Cadence/Chorus.lean) has an abstract
`Phase` — `pre_deadline → post_deadline → post_fb_arm → post_mvba_arm`,
advanced by three non-deterministic actions — and [Mvba.lean](../Cadence/Mvba.lean) has
`timer_expired`, the same device with one tick instead of three. Both replace
wall-clock time by a monotone marker, and both gate real actions on it
(`record_chunk` needs `pre_deadline`; the two `timeout_*` need
`timer_expired`). So the shapes are the same.

**Chorus's markers are weakly fair and `Mvba`'s is not**, and the reason is
what each advance *does*. Chorus's phases move the protocol from one arm to
the next: fast path, then fallback, then the MVBA arm. Advancing early
forfeits the faster arm and nothing else — there is always somewhere to fall
— and termination is then delegated to the sub-protocol's own, `Mvba.termination`.
`Mvba`'s view *is* that last arm. A timer firing early forfeits the view, and
the only thing to fall onto is another view; if every view's timer fires
early, nothing terminates at all. There is no sub-protocol left to delegate
to, so the assumption that *some* view survives its timeout has to be made
here.

That is FLP, paid where it must be. The paper pays it twice over, in the two
MVBA options: the randomised primitive pays with probability-1 termination
(no deductive framework here expresses that), and the supplement's
leader-based protocol — the one modelled — pays with partial synchrony.
(A-viewsync) is the untimed form of the second payment. Partial synchrony
bounds delays, but an untimed model has no delays to bound. What it does
have is the timer, and without a clock the timer can fire at any moment.
So the untimed model states partial synchrony as ordering constraints on
the timer.

**Chorus does have an (A-viewsync)-shaped premise; it is just somewhere
else.** `all_honest_recorded` — "every honest validator recorded the positive
entry", in the model's own words the protocol-level shadow of
`s.deadline − Δ ≥ GST` — is exactly "the work finished before the marker
advanced". It is carried as an **antecedent of the properties** (proposal
inclusion, and the fair-progress invariants that rest on it) rather than as a
run-level premise, and it buys *proposal inclusion* rather than termination,
which is why it does not appear in a fairness list. The accounting differs;
the assumption is of the same kind.

**Where it ends.** The stack's trust base has no unconditional
consensus-termination assumption, only a synchroniser interface plus a
proof: `Mvba.termination` says "the MVBA terminates given (A-viewsync),
(F-justice), (F-avail) and its caller's premises", and `Chorus.termination`
consumes exactly that (§2). With a clock, (A-viewsync) stops being an assumption. Over timed
runs of the same untimed model — no model change — the timing model of
[Cadence/Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean)
([Bounds.md](Bounds.md) §6.2) gives:

* the bound itself: `Mvba.bounded_termination`
  ([Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean)),
  from the two protocol lemmas `Mvba.good_view_decides` (a correct-led view
  whose budget exceeds the chain's latency decides within it,
  [Cadence/Mvba/Bound.lean](../Cadence/Mvba/Bound.lean)) and
  `Mvba.synced_succ` (any other view is left within a fixed cost);
* (A-viewsync) as a theorem, for finitely many validators:
  `Mvba.aViewSync_of_sync`, from `Mvba.termination`'s own caller premises.
  Its derivation needs only that *some* correct validator eventually
  decides (the header of
  [Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean));
* the contract: the `MVBATemporal` instance `Mvba.mvbaTemporal`
  ([Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)), at the
  fragment the composed system runs, and the full contract `Mvba.mvbaFull`.

[MvbaPlan.md](MvbaPlan.md) §3.7 explains why no intermediate step — a GST
marker without a clock, say — gets there without the clock.

## 3. What stays outside Veil

Veil has no fairness annotations and no quantification over runs, so the
rule "continuously enabled ⇒ eventually fires" cannot be stated inside a
Veil model. Every liveness claim here is therefore a plain-Lean theorem
over runs of the generated transition system, with its fairness and timing
premises as hypotheses of the statement: `Chorus.termination` and
`Mvba.termination`, and the timed claims over timed runs
([Bounds.md](Bounds.md) for Chorus and the MVBA,
[ConductorBounds.md](ConductorBounds.md) for the Conductor and the
composed system). The state-level content they use is proven inside the
models, by the sweep (§1).

A designed Veil extension would state and discharge such properties inside
the models: fairness classes on actions, ω-acceptance/response properties,
discharged by the POPL'18 **liveness-to-safety** reduction on the existing
safety-VC pipeline. It is Veil work and lives in the fork:
**[docs/Liveness.md](https://github.com/larskuhtz/veil/blob/lars/liveness/docs/Liveness.md)
on the `lars/liveness` branch of `larskuhtz/veil`**. It would move where
the proofs live, not what is claimed ([TODO.md](TODO.md)). The randomised
MVBA primitive's probability-1 termination stays out of scope either way.

The paper's concrete Δ-bounds and the untimed claims of §1–§2 are
*incomparable*: the bounds assume strong partial synchrony, the untimed
claims only eventual delivery and fair scheduling
([Bounds.md](Bounds.md) §2).

## 4. Chorus at run level: how `Chorus.termination` is proven

`Chorus.termination` follows the pattern of `Mvba.termination`: a
run-level theorem whose premises are named `Prop`s, each a predicate on a
run, stated before and apart from the proof.
[Cadence/Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean) holds the
claim (`TerminationClaim`), its premises and its vocabulary;
[Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)
holds the proof, and nothing there adds a premise. Both files' headers and
docstrings carry the reasoning at the point of use; this section is the
structure, for an auditor.

The proof has four parts: a **projection** from a composed run to a run of
the MVBA (§4.1–§4.2), through which `Mvba.termination` is consumed; the
**classification** of Chorus's actions and the premises (§4.3);
**saturation** and the **commit route**, from (F-justice) alone (§4.4–§4.5);
and the **MVBA arm** (§4.6). §4.7 assembles them.

### 4.1 The projection is shared with the timed claims

Chorus holds an *abstract* MVBA state and advances it with the oracle
action `mvba_step`, which takes any transition the contract allows and is
deliberately **outside** (F-justice): its scheduling is the MVBA's own
business. Consuming `Mvba.termination` therefore needs a projection from a
run of the composed system ([System.lean](../Cadence/System.lean), where
the abstract state is `Mvba.State`) to a run of the MVBA, keeping only the
steps at which the MVBA's state moved. It is `Cadence.Component` and
`Component.Projection` in [Cadence/Fairness.lean](../Cadence/Fairness.lean)
(§4.2). The timed claims use the same relation: a timed projection is a
`Projection` whose composed run carries a clock, and the index map
`Component.idx`/`Component.cover` relates the two clocks
([Bounds.md](Bounds.md) §6.2.1).

The premise that hands the MVBA's scheduling to the MVBA is
`MvbaAdmissible`: the composed run's MVBA projection satisfies
`Mvba.termination`'s scheduling premises. It is not obtained by weakening a
class field; that rule is in [../CLAUDE.md](../CLAUDE.md).

### 4.2 The projection: weak fairness survives the re-indexing

A `Component sys th sub th'` is one Veil module held inside another, given
by five first-order facts: the state projection `proj`, the outer labels
`isSub` that are the part's own steps, the transfer of initial states
(`init`, which also hands over the part's theory assumptions), the frame
law for every other label, and `step` — a step of the part taken by the
whole is a transition of the part under *some* label of its own. A
`Component.Projection C r` of a composed run `r` is a labelling of the
part's steps by part labels that explain them (`lbl`, `realizes`) together
with `scheduled` — the part is stepped infinitely often. From it,
`Projection.run : LRun sub th'` is the projected run: the part's state at
each of its steps, indexed through Mathlib's `Nat.nth`. Then:

* `Projection.weaklyFair_iff` — **weak fairness survives the re-indexing,
  as an equivalence**: `WeaklyFair p.run l'` iff the composed-run reading
  `p.WeaklyFairIn l'` (enabled at the part's state at every composed index
  from `N` on ⇒ the whole takes a step of the part labelled `l'` at some
  composed index from `N` on). It holds because the part's state is
  constant between its steps. That it is an *iff* makes the premise
  readable at either level with nothing smuggled in.
* `Projection.proj_eq_run_cover` — the state correspondence: the part's
  state at any composed index is a state of the projected run (at
  `Component.cover n`, the number of the part's steps before `n`). The
  three temporal shapes follow as equivalences (`eventually_iff`,
  `always_iff`, `leadsTo_iff`); they carry a caller's premise into the
  part's run and the part's conclusion back.
* `Component.reachable_proj` — the part's state at every composed index is
  reachable in the part's own system, with **no** scheduling hypothesis.
  So every invariant the inner module proves holds of the state the outer
  module holds.
* `Projection.ofScheduled` — a labelling always exists, so the only
  content of a premise of the form "there is a projection satisfying …" is
  what is asked of the projection, never its existence.

Two design decisions follow from the composed model's shape.

1. *The premise quantifies over a labelling.* The composed run does not
   record which MVBA action fired: `mvba_step` carries only the next MVBA
   state, and two MVBA labels can explain the same step. A weak-fairness
   statement is about labels, so it cannot be *derived* for a projection
   whose labels the projection chooses; it has to be *assumed of* a
   labelling. `MvbaAdmissible` is therefore "∃ `p : C.Projection r`,
   `Mvba.FJustice p.run ∧ Mvba.AViewSync p.run`", stated with
   [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)'s own definitions
   and restating none of them. Stating MVBA fairness on the composed run
   without a labelling is not weaker, it is unstatable: there is no "this
   label fired".
2. *Infinitude is part of the projection.* `LRun` is an infinite sequence,
   so an MVBA stepped only finitely often has no run in its own vocabulary.
   `Component.Scheduled` is a field of `Projection` and so part of the
   premise. It is a scheduling assumption about the whole (the MVBA is not
   starved), weaker than weak fairness of `mvba_step` since it says nothing
   about *which* MVBA step is taken, and it is not vacuous at the `Mvba`
   instance because `become_avail_ready` is unguarded. It does **not** put
   `mvba_step` under Chorus's (F-justice). It is a premise the paper does
   not spell out, so [Architecture.md](Architecture.md) §4 names it.

The instance for Chorus, `Chorus.mvbaComponent`
([Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)), adds no cell:
`frame` is one generated `Chorus.<action>.frame_mvba_st` lemma per other
action, `step` reads the two oracle actions' guards off their transition
bodies (`mvba_step` requires `mvba.step`, `mvba_propose` requires
`mvba.propose`), and `init` is read off the initializer's transition,
because `mvba_st` is seeded from the theory's `mvba_init_state`. At the
`Mvba` instance, Chorus's `[mvba_init]` assumption *is* `sub.assumptions ∧
sub.init`, the two halves of `Component.init`.

### 4.3 The classification, the premises, the target

**The classification.** Four `match` definitions over `Chorus.Label`:
`ByzLabel` (the `byz_*` actions — (F-byz)), `OracleLabel` (the oracle step
`mvba_step` alone), `InputLabel` (the module's three inputs `participate`,
`abandon`, `propose`, which the caller invokes), and `JusticeLabel` as
their complement — (F-justice). `label_classified` pins exhaustiveness, and
`not_justice_of_byz`, `not_justice_of_oracle` and `not_justice_of_input`
the disjointness. `MvbaStepLabel` (`mvba_step` and `mvba_propose`) is the
*component's* cut, not a fairness class: `mvba_propose` is Chorus's own
weakly fair action that also advances the MVBA, and it appears in the
projected run as the MVBA's `propose` input, which `Mvba.FJustice` excludes
for that reason.

**The premises**, over `ChorusRun thS thM` (a labelled run of Chorus with
its MVBA constraint filled by `Mvba.mvbaSafety thM`, the instantiation
[System.lean](../Cadence/System.lean) uses): `FJustice`, `MvbaAdmissible`,
`ValidBridge`, `AllParticipate` and `NoAbandonBeforeFinalizing`. §2 says
what each is, and [Premises.md](Premises.md) §3, §5 and §6 list them with
their plausibility, witness and use. Two points of design:

* `FJustice` is per label, except for three families that are fair as a
  whole (`FamilyLabel`): the proposal to the MVBA per validator and value,
  the certificate handoff per validator, and the availability report per
  validator and meta-block (§4.6, Finding 2, says why). Each clause is owed
  only under its `Owed` condition: the messages the step consumes came from
  correct validators.
* `ValidBridge` has two clauses, both stated with `Certified` —
  `mvba_propose`'s three validity guards verbatim, the first two of which
  are the decision handlers' bridge `require`. **Soundness**: a certified
  meta-block is `Valid`, so a correct validator that has built one can
  propose it (`Mvba.propose` requires `valid` of its input). **Completeness**:
  a meta-block a correct validator decided or holds is certified, so the
  decision handlers are enabled. It is the run-level form of the one stated
  bridge ([CompositionContracts.md](CompositionContracts.md) §3, §7 item
  1), and its content is cryptographic, not scheduling. No class field can
  carry it, because `Valid` is fixed before Chorus's state exists. The
  safety proofs need neither direction.

**The target.** `Terminates r`: every correct validator eventually has
`local_committed` — `finalize_commit` fired for it. `TerminationClaim thS
thM` is "every run satisfying the five premises `Terminates`". Absent by
design: any timing premise (§2.1); any `all_honest_recorded`-shaped premise
(it buys proposal inclusion, not termination); and the quorum machinery
(the concrete family, and `Mvba.termination`'s class hypotheses, are
hypotheses of the theorem, not part of the claim).

### 4.4 Saturation and the commit route

Both chains are in
[Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean) and
take `FJustice` and no other run premise, together with the participation
gate (`ActiveFrom`): every sending rule requires its validator to be
actively participating. Every temporal step consumes weak fairness in the
only way [Fairness.lean](../Cadence/Fairness.lean) allows
(`Cadence.exists_disabled_of_never_fires`): a label that stays enabled
fires, so each link shows the label stays enabled unless the disabling
event is the progress wanted. Finitely many eventualities collapse into one
index through `LRun.eventually_forall` over the complete list of validators
(`List.ofFn id`).

**Saturation** (`saturation_fin`): from some index on, every correct
validator is `Saturated` — it has cast its fast commit vote with a commit
signature per proposer, or its fallback vote with a fallback signature per
proposer. That is the hypothesis of `progress_dichotomy_of_saturation`, so
`eventually_progress_dichotomy` follows. The chain: the phase reaches
`post_mvba_arm` and stays there (the three `advance_to_*` actions are
weakly fair); every correct validator votes; the honest quorum's votes are
on the network (`voted_implies_cast`), and each correct validator receives
them (`eventually_received`: `receive_vote_*` is owed for a correct voter);
per proposer, `fb_sign_pos` or `fb_sign_neg` fires unless the validator has
cast fast; then `cast_fallback_vote`. The case split is excluded middle on
the positive evidence among the votes the validator received over the run:
receipts are monotone, so if it ever appears it persists and `fb_sign_pos`
fires; if it never does, its absence *is* `fb_sign_neg`'s guard, verbatim,
at every index.

Two facts the sweep does not give are derived at run level, from the first
step at which a flag holds (`commit_cast_sigs`, `fallback_sig_sigs`): a
correct validator's fast commit vote carries a commit signature per
proposer, and its fallback vote a fallback signature per proposer. A third,
`path_fallback_sig`, says `local_path i` becomes `fallback` only in the step
that casts the fallback vote. Each reads the one honest action that sets
the flag off its transition body.

**The commit route** (`eventually_committed_of_assignable`): from an index
at which every proposer's entry has a commitment proof from a correct
sender (`CertPos`/`CertNeg`: a fast commit certificate, a fallback commit
certificate, or a valid MVBA commit certificate, each with its sender),
every correct validator that participates and abandons only after
finalizing eventually has `local_committed`, through the route
`commit_assign_*_{fast,fb,mvba}` that reads the proof's form. A correct
validator's finalization re-broadcasts its proofs under its own name
(`proofs_of_finalized`). Nothing is assumed of the other validators.

### 4.5 What the chains take from the model

* **One invariant.** Saturation uses `voted_implies_cast`. The commit route
  uses none: the argument is by contradiction on the validator never
  assigning an entry for that proposer, and then `commit_assign_*`'s
  consistency and fired-once guards, which concern only its own earlier
  assignments, hold vacuously.
* **`vote` writes its network rows as monotone disjunctions.**
  `msg_vote_pos_sig`, `msg_vote_neg_sig` and `local_entry_neg` are written
  as `old || (…)`: the same transition at every reachable state (the old
  value is `false` there, by `vote_sig_pos_implies_voted` and its siblings)
  and monotone by syntax, so the (M-update) half of the network contract
  holds per step with no exception. Veil's generator emits `.mono` lemmas
  only for literal-`true` writes, so these three are proven by label
  dispatch (`msg_vote_pos_sig_mono`, `msg_vote_neg_sig_mono`,
  `local_entry_neg_mono`).
* **Generic chains, concrete theorems.** The chains are generic in the
  quorum instance and the MVBA, with the finiteness they consume as
  explicit hypotheses — a complete list of validators and an honest
  supermajority — and the concrete theorems (`Fin n`, `byzNodeSetFin` at
  every `n = 3f+1`) supply `List.ofFn id` and `honest_supermajority`'s
  quorum. The reason is the generated instance regime: the generic lemmas
  meet the canonical instantiation by unification. It also shows that the
  fast route does not depend on the MVBA instance.
* **Finiteness is a hypothesis of the argument, not of the scheduling.**
  Collapsing a family of per-validator eventualities into one index plays
  the ranking's role, and is sound only over a finite list: with infinitely
  many validators every one eventually acts, but no index need exist at
  which a quorum has.
* **Fairness over state-changing steps changes nothing.** Every label the
  chains fire is fired at a state where its effect is absent, so each such
  step changes the state; `FJustice` is equivalent to its move form
  (`Chorus.fJustice_iff_move`).

### 4.6 The MVBA arm

**The chain** (`eventually_committed_of_mvba_arm`, at the concrete family
`mvba_arm_fin` and `terminates_of_mvba_arm`), from `FJustice`,
`MvbaAdmissible` and `ValidBridge`, once every correct validator is active
and the MVBA route is open from correct senders (`eventually_mvba_route`:
at saturation, a correct fast voter's complete meta-block or else the
correct population's `FBCert`, `CorrectTrigger`, with a certificate for
every proposer from `mvba_evidence_of_saturation`):

1. *Every correct validator proposes* one certified vector, built once from
   the evidence at the start index (`certifiedVector`); the evidence is
   monotone, so the vector stays `Certified`, and the bridge's soundness
   clause makes it `Valid`.
2. *`Mvba.termination` is applied* to the projection `MvbaAdmissible`
   supplies. Its caller premises are derived: every correct validator
   proposes (step 1, through `Projection.proj_eq_run_cover`); nobody is
   abandoned in the MVBA, because on this branch nobody invokes Chorus's
   `abandon` and the MVBA's `abandoned` row moves only with it
   (`abandoned_of_mvba_abandoned`); decided certificates are handed on:
   each active correct decider broadcasts its certificate
   (`send_mvba_cert`, `eventually_cert_sent`) and every correct validator
   takes it (`fRelay_of_fJustice`); availability arrives
   (`fAvail_of_fJustice`).
3. *Every correct validator's decision is transported* into Chorus by its
   decision handlers `on_mvba_decide_pos/neg`, whose bridge `require` is the
   completeness clause, and completed by its own `mvba_terminate`
   (`local_mvba_complete i`, which its fallback commit vote waits for).
4. *The fallback commit round.* Every correct validator's chunks under the
   decision's `FallbackQC` entries are on the network (sent inside the
   positive fallback signer's step, F15), so it casts its fallback commit
   vote; the wait is stable once every proposer's entry is recorded
   (`mvba_decided_pos_unique`, `mvba_decided_pos_neg_excl`). A correct
   collector forms the correct voters' fallback commit certificate and
   broadcasts it (`broadcast_fbcommitqc`, `eventually_fbcommitqc_sent`); it
   is a commitment proof for every entry from a correct sender, and the
   commit route (§4.4) finalizes everyone.

Beyond the invariants the chain reads at reachable states (the FastQC
backing, the decision records' backing, uniqueness and decodability), one
fact is derived: a decided root is proposer-signed
(`proposer_signed_of_decided_pos`).

**Finding 1: a non-proposer has no entry.** `chorusTheory` in
[System.lean](../Cadence/System.lean) sets `mval_neg v j := v j = none ∧
is_proposer j`. With `v j = none` alone, a vector would have an entry at
every non-proposer, `mvba_propose`'s validity guards require `is_proposer`
of every entry, and if any validator were not a proposer no vector would be
`Certified`: the MVBA would never receive an input, and `TerminationClaim`
would be false at `chorusTheory` while `ValidBridge`'s soundness clause was
vacuous. Safety is unaffected either way, since the guard only removes
behaviours. The instantiation is where the reading belongs, and the model
is untouched by it.

**Finding 2: the proposal is fair as a family.** The action is
`mvba_propose (i) (v) (mvba_next)`, and its last guard is `mvba.propose
mvba_st i v mvba_next`. A single label is enabled only while `mvba_st`
stays at the one state whose propose-successor is `mvba_next`; the MVBA
keeps stepping, so no single label need stay enabled, and per-label weak
fairness could keep `i` from ever proposing. `FJustice` therefore covers
`mvba_propose` per `(i, v)` with `Cadence.WeaklyFairFamily`
([Fairness.lean](../Cadence/Fairness.lean)): if some label of the family is
enabled from some point on, some label of it fires. That is TLA+'s
`WF(∃ n. Propose(i, v, n))`, exactly the fairness of an action that picks
its successor in the body; for a one-label family it is plain weak
fairness (`weaklyFairFamily_eq_iff`). The pick itself is not in the model,
because the model also generates the executable actions the trace monitor
runs, and a pick is executable only over an enumerable type, which the
abstract MVBA state is not.

**The criterion behind Finding 2.** Whether a variable is an action
parameter or picked in the body makes no difference to safety, but a label
is the unit weak fairness speaks about. Parameters that identify **who acts
or on what** (the validator `i`, the proposer `j`, the proposed value `v`)
belong in the label: fairness per process is the standard assumption.
Parameters that are **witnesses or results** (a successor state, the quorum
`q` that witnesses a guard) belong in the body, because a label containing
them tracks state that other actions change. The test: a label's
enabledness should be stable under steps irrelevant to its action.
`mvba_propose i v next` fails it; `on_mvba_decide_pos i j m v` passes (`v`
is fixed once decided). The witness-parameterised assembly labels
(`broadcast_commitqc_* … q`, `aggregate_fastqc_* … q`) are sound as they
stand, because every fair action fires once
(`Chorus.justice_enabledMove`).

### 4.7 The claim, assembled

`Chorus.termination` proves `TerminationClaim` at every `n = 3f+1` with at
most `f` Byzantine validators (`Fin n`, `byzNodeSetFin`), at the
configuration the composed system runs: `Cadence.chorusTheory`, with the
MVBA constraint filled by `Mvba.mvbaSafety` at `Cadence.mvbaTheory`.
`Cadence.mvbaTheory` fixes one thing, that a meta-block's entry vector is
its own entries with the certificates dropped (`ent :=
MetaBlock.entries`), so that a validator can propose a certified
meta-block; its validity predicate and leader schedule stay arbitrary. Like
`Cadence.chorusTheory`, it is the configuration, not a premise.

**The proof splits on an early finalization**, as the paper's does:

* **Some correct validator finalizes.** Its commitment proofs are on the
  network, so every other correct validator finalizes through the commit
  route (`eventually_committed_of_finalized`), needing only the two caller
  premises at itself. This branch is the untimed totality, and it needs
  none of the MVBA's premises.
* **No correct validator ever finalizes.** Then none abandons
  (`NoAbandonBeforeFinalizing`), so from some index every correct validator
  is active (`activeFrom_of_never_finalized`), the MVBA route is open from
  correct senders, and the MVBA arm (§4.6) finalizes everyone.

The split is needed because a validator that finalizes on the fast path may
then abandon, which also abandons the MVBA.

**The setting.** The theorem's other hypotheses are the quorum family's
parameters (`n = 3f+1`, the Byzantine predicate and its bound) and
`ViewOrderEnum`, which, as in `Mvba.termination`, belongs to the proof and
not to the claim. The quorum counting facts are the family's own instance
(`Cadence.byzNodeSetFin_counting`), passed to `TerminationClaim` by name,
so the counting class is not a hypothesis. The theorem is pinned at the
standard trio there and in [Cadence.lean](../Cadence.lean).

**What builds on it.** The premises are jointly satisfiable
(`Chorus.termination_premises_satisfiable`,
[Cadence/Chorus/Witness.lean](../Cadence/Chorus/Witness.lean): everyone
finalizes on the fast path and then abandons, so the MVBA stays quiet and
the proposal family holds with its antecedent false). The timed claims,
`Chorus.timed_termination` at `5Δ + ℓ_MVBA + 9δ` and
`Chorus.timed_termination_tight` at `4Δ + ℓ_MVBA + 9δ`, are proven over
timed runs of the same model ([Bounds.md](Bounds.md) §6.4.3). The contract
instance `Chorus.chorusTemporal`
([Cadence/Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean)) has
`Chorus.termination` as its Termination, over runs whose labelling meets
the three run premises; the caller's two are the field's own antecedents.
Within Cadence the glue meets the caller's conditions, and the composed
claims discharge them ([Premises.md](Premises.md) §0.4).
