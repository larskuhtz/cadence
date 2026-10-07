# Open items

Everything *claimed* in this repository is proven and axiom-pinned, and
the premises of every claim are shown to hold together
([Premises.md](Premises.md)). The items below are places the development
could go further, not gaps in what is asserted. Each says why it is worth
doing. The Chorus-specific list is [ChorusDesign.md](ChorusDesign.md) §9.
What has been done, and when, is [History.md](History.md).

## The paper

* **Send the findings page to the paper's authors** — P1–P19,
  [PaperAlignment.md](PaperAlignment.md) §6. Each is open on the paper
  side; a finding the authors resolve is marked so at the next re-check.
* **Re-check at the next paper commit** — run
  [PaperAlignment.md](PaperAlignment.md) §1 against it and list it in §9,
  so the development keeps saying which paper it verifies. The commit
  becomes the target only when a session moves it.
* **Check the practical Conductor against the verified one, once it
  stabilises** — the supplement's practical Conductor (Supplement,
  Algorithm 2 (`alg:conductor-practical`)) is outside the verified surface
  ([PaperAlignment.md](PaperAlignment.md) §5.8, §9). If its behaviour is
  one the verified Conductor's contract (`OrchestratorSafety`,
  [Interfaces.lean](../Cadence/Interfaces.lean)) admits, under P9's
  narrower range `2 ≤ p ≤ W − 1`, the simpler main-body Conductor stays the
  verified one.

## Soundness instruments

* **Locality, the open models** ([Locality.md](Locality.md) §7). Mvba:
  the environment-written `timer_expired`/`avail_ready` rows become the
  validator's own timeout step and the caller's input; the sender-less
  certificates (`msg_prepqc`, `msg_commitqc`, `msg_tc`, `tc_lock`,
  `tc_nolock`) get a sender; the anonymous assemblies go. With it, the MVBA
  contract outputs the certificate a decision used at the decider's index,
  so Chorus's `send_mvba_cert` sends that certificate rather than any valid
  one. Conductor: `acs_decide` becomes a per-validator step writing
  per-validator window bounds, and `opened_win` an `aux_` record.
* **A locality checker** — the rules of [Locality.md](Locality.md) are
  checked by hand, action by action (the guide's audit table), and a
  violation would not fail the build ([Architecture.md](Architecture.md) §4
  item 1). The rules are stated for pattern matching over names, index
  positions and polarity, with the semantic steps marked; a meta-program
  applying them would make the audit a machine check (the V line).
* **A model instance of `ThresholdIBE`** — it is the one primitive class
  with no instance, and an instance would show its axioms are satisfiable
  rather than contradictory ([ChorusDesign.md](ChorusDesign.md) §9
  item 1). The quorum classes and the MVBA already have theirs.
* **A Chorus run through the MVBA arm** (optional) — the Chorus and
  composed witnesses finalize on the fast path, so the proposal and handoff
  families and `ValidBridge`'s completeness hold there vacuously. A second
  run through `mvba_propose` and a decision handler would show the MVBA
  certificate bridge satisfiable at the composed instance
  ([CompositionContracts.md](CompositionContracts.md) §7 item 1).
* **An in-build `sat trace` for Chorus** — Chorus cannot carry one: the
  trace pipeline needs the label enumeration that
  [Chorus.lean](../Cadence/Chorus.lean) disables for size, and every
  finalizing run passes through `vote`, whose bulk update uses a `decide`
  the trace pipeline cannot translate. Either fix is a model refactor. The
  standing reachability witness is the monitor's fast-path fixture, run in
  CI ([Monitor.md](Monitor.md)).

## The Veil fork

These belong to the public Veil fork ([Dependencies.md](Dependencies.md));
they are listed here because this project would use them.

* **Withheld fields still change the solver's queries** — two `ACSSafety`
  fields withheld with `veil_smt_ignore` made one Conductor cell diverge
  ([ConductorBounds.md](ConductorBounds.md) §7, F26). The cause is not
  diagnosed; until it is, a withheld field is not free.
* **Liveness inside the models** — liveness-to-safety, surface syntax for
  an action's fairness class, and reachability-directed trace generation
  would let the models state and check their liveness content per action,
  as they do safety; today the fairness premises are hypotheses of
  plain-Lean theorems ([Liveness.md](Liveness.md) §3).

## The monitor

* **The MVBA leg** — the monitor instantiates Chorus's MVBA constraint
  with a stub that never decides, so no fallback-path trace can be checked
  ([Monitor.md](Monitor.md) §8).
* **Coverage** — positive-path emission, per-message emission at the
  network boundary, multi-slot (Conductor) traces, Byzantine
  validate-vs-admit tagging ([Monitor.md](Monitor.md) §8).

## Scope extensions

* **Multi-slot Chorus** — the model fixes one slot, and cross-slot
  independence is argued, not modelled ([ChorusDesign.md](ChorusDesign.md)
  §3.4, §9).
* **Epochs and proposer rotation**, with `is_proposer` derived from a VRF
  rather than fixed configuration ([ChorusDesign.md](ChorusDesign.md) §9
  item 2).
* **A bound through the `CommitQC` route** (optional) — the timed claims
  use the main body's fallback commit round; a bound through Part I's route
  would record how the implementation's latency compares
  ([PaperAlignment.md](PaperAlignment.md) §5.7).

## Model hygiene

* **Atomic-action candidates** — `cast_commit`, `fb_vote` and `commit`
  could each replace three actions, as `vote` did; one A/B was
  inconclusive. The candidates and the measuring recipe are
  [History.md](History.md) § "Records moved out of the living documents
  (R33)".
* Retire the remaining cryptic abbreviations in state and action names;
  keep the `msg_` prefix on every network relation, which is what makes
  the monotonicity audit tractable by grep.
* Format the sources consistently against the Lean 4 style guide.
