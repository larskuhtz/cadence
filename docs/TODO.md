# Open items

Everything *claimed* in this repository is proven and axiom-pinned — these
are places the development could go further, not gaps in what is asserted.
The authoritative, numbered list of Chorus-side open items is
[`ChorusDesign.md`](./ChorusDesign.md) §9 (and §§10.1–10.3 for the bigger
lifts); this file collects the cross-cutting ones and the model-hygiene
wishlist.

## Soundness — guarding against vacuous claims

These are the items that would most change an auditor's confidence, so they
come first.

* **Instantiate the primitive class stack end-to-end.** The Byzantine-quorum
  interface is already discharged for the concrete `byzNodeSetFin` family
  (see [`../Cadence/ByzQuorum.lean`](../Cadence/ByzQuorum.lean)), which is why
  it is *not* on the assumption list in
  [`Architecture.md`](./Architecture.md) §4. `MVBA` and `ThresholdIBE` are
  still axiomatic classes with no model instance: producing one would
  demonstrate the axiom set is satisfiable rather than accidentally
  contradictory. `ChorusDesign.md` §9 item 2.
* **Non-vacuity of the safety claims.** Each model carries `sat trace`
  reachability witnesses so that the properties are not vacuously true (if
  finalization were unreachable, agreement would hold trivially). The receipt
  layer additionally has an exhaustive `#model_check` whose explored graph is
  checked to contain proposing runs. Extending the same discipline to every
  new property is a standing rule, not a one-off task.
* **Syntactic audit of the monotone-network contract.** The (M-frame) half of
  the network abstraction — network relations consulted in positive position
  only — is checked by hand today and *not* enforced by the tool; a violation
  would not fail the build, it would silently void the asynchrony argument.
  A small Lean meta-program that walks each action's syntax and flags negative
  occurrences of a relation declared "network" would turn the top item of
  [`Architecture.md`](./Architecture.md) §4 into a machine check.
  `ChorusDesign.md` §9 item 5.

## Liveness

The fair-progress *safety content* is machine-checked; the temporal glue is
not (see [`Liveness.md`](./Liveness.md) for the approach and
[`LivenessNotes.md`](./LivenessNotes.md) for what the Chorus encoding does).
Remaining:

* Full liveness-to-safety, so that the (F-justice)/(F-byz)/(A-mvba)
  meta-axioms become premises of a Lean theorem rather than named
  assumptions. This is the single largest reduction of
  [`Architecture.md`](./Architecture.md) §4 available.
* Actions are annotated with their fairness class in prose only; Veil has no
  surface syntax for it. `Liveness.md` §2 sketches what that syntax should be.
* Reachability-directed trace generation, so that non-vacuity witnesses for
  the *progress* invariants can be produced mechanically rather than written
  by hand.

## Model hygiene

* Retire remaining cryptic abbreviations in state and action names; keep the
  `msg_` prefix convention on every network relation (it is what makes the
  monotonicity audit above tractable by grep).
* Prune comments describing superseded versions of the model — they are the
  main source of stale reading in the big files.
* Format the sources consistently against the Lean 4 style guide.

## Scope extensions

* **Multi-slot Chorus.** The model fixes a single slot; cross-slot
  independence is argued, not modelled. The `slot` type is retained as a
  placeholder. `ChorusDesign.md` §3.4 and §9.
* **Epochs and proposer rotation**, and deriving `is_proposer` from a VRF
  rather than taking it as immutable configuration. `ChorusDesign.md` §9
  item 3.
* **Monitor coverage** — positive-path emission, per-message emission at the
  network boundary, multi-slot (Conductor) traces, Byzantine
  validate-vs-admit tagging. [`Monitor.md`](./Monitor.md) §8.

## Verification-pipeline work

Not tracked here. The tooling this project depends on is the public Veil fork
(see [`Dependencies.md`](./Dependencies.md)); anything to be improved about it
belongs in that repository. The one measurement worth carrying forward is
recorded in [`Architecture.md`](./Architecture.md) §7.
