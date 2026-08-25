*The report in this document was created by [Aristotle (Harmonic)](https://aristotle.harmonic.fun).*

# Independent audit — Cadence BFT formalization (Veil / Lean 4)

*Audit of the artefact in this repository against
[`paper/2607.02275v2.pdf`](../paper/2607.02275v2.pdf) (authoritative;
v1 is included only as the source of the deliberately-refuted bug).*

*Maintainers' note (2026-08-25): this report is frozen at the revision it
audited (`bfeee8c`), as is that revision itself. The only post-audit edits
are the blockquoted **Resolution note** lines under individual findings,
recording what has since been closed and by which commit; the report text is
otherwise verbatim.*

Three questions were asked:

1. Does the model **faithfully implement** the protocol as described in the paper?
2. Are the **properties claimed in the paper covered**?
3. Are the **proofs sound** — the Lean formalization *and* the documented
   meta-theoretic arguments (liveness, network model)?

**Summary verdict.**

| Question | Verdict |
|---|---|
| Faithfulness | **Yes, within a clearly declared abstraction boundary.** Every divergence I found is either documented in `docs/` or is listed below as a finding. No divergence I found makes a machine-checked property easier in a way the documentation hides, with the single partial exception of Finding 1. |
| Property coverage | **Substantially complete for the safety-shaped claims; the temporal/quantitative claims are honestly out of scope.** See the coverage table in §4. |
| Soundness | **Sound.** No `sorry`, no user-declared `axiom`, no `native_decide`, no `@[implemented_by]` anywhere in the Lean sources. Every SMT sweep runs with `veil.smt.trust false`, i.e. cvc5's `unsat` verdicts are *reconstructed and kernel-checked*, and this is pinned by seven `#guard_msgs`-guarded `#print axioms` checks that admit only `propext, Classical.choice, Quot.sound`. The meta-theoretic arguments are stated, named, and inventoried rather than smuggled in; the inventory in `docs/Architecture.md` §4 is, as far as I could check, complete. |
| Reproduction | **The whole suite was re-built cold in this environment and is green** (`ALL STAGES GREEN`; 0 counterexamples, 0 solver crashes). The seven end-theorem axiom footprints were re-derived independently of the in-file pins and are exactly `[propext, Classical.choice, Quot.sound]`. Details, including two environment-level reproduction snags, in §3.1. |

Findings are in §6, ordered by severity. None of them is a defect in a proof.
The most substantive is **Finding 1**
(the DA re-encode abstraction is load-bearing for the *speculative-finality*
properties, which `docs/ChorusDesign.md` §3.4 does not say). Nothing I found
invalidates a claimed theorem; the findings are about the *scope* of what the
theorems mean and about documentation precision.

---

## 1. Scope and method

Audited artefacts (70 Lean files, ~10.7 kLoC under `Cadence.lean` / `Cadence/`,
plus ~3.5 kLoC of design documentation under `docs/`):

* `Cadence/Chorus.lean` (2127 lines) — the single-slot Chorus model, plus its
  39 per-action proof files under `Cadence/Chorus/Proofs/`, the composition
  certificate `Cadence/Chorus/Certify.lean`, the end theorems
  `Cadence/Chorus/Compose.lean`, and `Cadence/Chorus/Pigeonhole.lean`.
* `Cadence/Conductor.lean` — the windowed orchestrator (ACS variant).
* `Cadence/Cadence.lean` — the glue module (`algorithm:cadence`).
* `Cadence/Composition.lean` — `Cadence.positional_log_safety` and
  `Conductor.orchestrator_instance` (`Chorus.slotConsensus_instance` lives in
  `Cadence/Chorus/Compose.lean`).
* `Cadence/Interfaces.lean`, `Cadence/Primitives.lean`, `Cadence/ByzQuorum.lean`,
  `Cadence/Windows.lean`.
* `Cadence/FallbackReceipt.lean` + 10 proof files + `Totality.lean` +
  `PreFix.lean` (the v1-bug refutation).
* `Cadence/Monitor/ChorusMonitor.lean` and `traces/*.jsonl`.
* `Cadence.lean` — the audit root with the axiom pins.
* `README.md` and all of `docs/`.

Paper material read in full: v2 main body §4 (including the
"Safety of speculative finalization" argument), §5 (Conductor), Appendix A
(MCP problem definition, Definitions 1–4), Appendix B (framework,
`mod:slotconsensus`, `mod:orchestrator_2`, Algorithm 1 = the Cadence glue),
Appendix C (Chorus: Algorithms 2–6, Lemmas 6–11, Propositions 1–5), Appendix D
(Conductor, `mod:acs`, Algorithm 7). Paper v1's Algorithm 5 was read to confirm
the bug reproduction.

Method: line-by-line comparison of each Veil `action` guard/body against the
corresponding paper algorithm line; comparison of each `safety` property
against the paper's property statement; a `grep`-level audit of the
monotone-network contract; a search for vacuity (unsatisfiable guards,
trivially-true properties, unreachable finalization); an axiom-footprint
review; and a re-build of the whole suite (§3).

---

## 2. What the artefact actually claims, and how it is layered

The formalization is three Veil relational-transition-system models plus a
plain-Lean composition layer:

```
plain Lean         Cadence.positional_log_safety   (paper Definition 1: MCP Safety)
                   Conductor.orchestrator_instance (Conductor ⊨ mod:orchestrator_2, formal field)
                   Chorus.slotConsensus_instance   (Chorus  ⊨ mod:slotconsensus, formal fields)
                   Chorus.evidence_pigeonhole_of_reachable
   ▲
Veil models        Cadence (glue) │ Chorus (single slot) │ Conductor (windows/ACS)
   ▲
class layer        SlotConsensus, Orchestrator, ACS, MVBA, ThresholdIBE, ByzNodeSet
```

The verification effort is dominated by Chorus: **38 protocol actions + the
initializer = 39 transitions**, **9 `safety` + 88 `invariant` = 97 properties**,
giving `39 × 97 = 3783` inductiveness VCs plus 39 `doesNotThrow` VCs =
**3822**, exactly the figure pinned by the in-file `#veil_status Chorus`
assertion. FallbackReceipt is 9 actions + init × (1 safety + 20 invariants) +
doesNotThrow = **220**, likewise pinned. I re-derived both counts from the
sources by hand; they match.

An important structural point for an auditor: the safety properties are
**not** proved by an external argument that could be gamed. They are proved
inductively: for each (action, property) pair Veil emits a Hoare triple and
cvc5 discharges it, with the proof *reconstructed* in Lean. The composition
layer then does the induction over `reachable` in ordinary Lean
(`invariants_of_reachable`), and the top-level theorems are ordinary Lean
proofs over that. `Cadence.positional_log_safety` in particular is a
hand-written ~40-line Lean proof from six projected invariants; I read it and
it is a genuine argument (sorted-list prefix agreement from same-slot
agreement + downward closure), not a repackaging of the goal.

---

## 3. Reproduction / build status

The repository pins its toolchain and all dependencies. `lake-manifest.json`
lists the dependency set as vendored `path` packages (the container image in
`docs/Container.md` supplies the vendor tree). Auditing outside that image, a
fresh checkout has no vendor tree, and `lake update -R` resolves the same
packages from their public remotes. The revisions it selected here, recorded so
this audit is reproducible, were:

| Package | Remote | Branch | Revision |
|---|---|---|---|
| `veil` | `larskuhtz/veil` | `port/integration` | `8406c0de7258f7ed9af9061fb376254cf91c6055` |
| `Loom` | `larskuhtz/loom` | `upgrade-v4.28-lakefile-fix` | `140825c54f259caddc5b3d9131da1f81d8ad3d80` |
| `smt` | `verse-lab/lean-smt` | `v4.28.0-for-veil-experimental` | `5c14319297bfa8c56dfda2772d18d9710ef2322a` |

plus `cvc5`, `auto`, `Qq`, Mathlib and its usual transitive set. These match
the forks `docs/Dependencies.md` documents. *The repository's own
`lake-manifest.json` was restored afterwards; no user file in the repository
was modified by this audit, which adds only this report.*

`scripts/revalidate.sh` was run cold in this environment; §3.1 records the
outcome. Two caveats an auditor reproducing this should know:

* A cold run rebuilds the whole Veil/lean-smt/lean-auto/cvc5 stack before any
  Cadence file is touched; this dominates wall-clock time. The README's ~85
  CPU-minutes figure for the Chorus sweep is *on top of* that.
* When reading the log, count **all four** verification markers — `✅` proven,
  `❌` counterexample, `💥` solver crash, `⏱` timeout — plus `♻` (proof-cache
  replay, still kernel-checked). Grepping only for `❌` would hide timeouts.
  The script itself says this; it is easy to miss.

The build is self-checking in three independent ways, which is the right
design and which I want to highlight because it means a *successful* build is
meaningful evidence and not just an absence of errors:

1. **Axiom pins.** `Cadence.lean` wraps seven `#print axioms` calls in
   `#guard_msgs`, so the build fails if any end theorem's axiom footprint ever
   grows beyond `[propext, Classical.choice, Quot.sound]`. This is what makes
   "`veil.smt.trust false` everywhere" checkable rather than a claim: a
   regression to trusted SMT would surface Loom's `trust_smt` axiom in a
   footprint and break the guard. `Cadence/Composition.lean` repeats two of
   the pins locally.
2. **Coverage pins.** `#veil_status Chorus` and `#veil_status FallbackReceipt`
   assert the exact VC counts as *real* (not cached-unchecked, not skipped),
   so a silently-dropped property fails the build.
3. **Non-vacuity pins.** `sat trace` reachability witnesses, and in
   `FallbackReceipt/PreFix.lean` a pinned `#model_check` counterexample.

### 3.1 Result recorded in this environment

**The whole suite was re-built cold and is green.** Machine: 8 cores, 64 GB.
Every target of `scripts/revalidate.sh` — the three model files with their
in-file sweeps, all 39 Chorus and 10 FallbackReceipt per-action proof files,
both `Certify` files, `Compose`, `Pigeonhole`, `Composition`, `Totality`,
`PreFix`, and the `Cadence` audit root — built successfully, ending in
`=== ALL STAGES GREEN`.

Aggregate verification markers over the run: **20464 OK**, **1202 cache
replays** (each re-checked against the live goal), **0 counterexamples**,
**0 solver crashes**, and 2 timeouts that were transient (see note 2 below).
Because the build is self-checking, this simultaneously confirms:

* the seven `#guard_msgs`-guarded axiom pins in `Cadence.lean`, the two in
  `Cadence/Composition.lean`, and those in `Chorus/Certify.lean`,
  `Chorus/Compose.lean` and `FallbackReceipt/Totality.lean`;
* the `#veil_status Chorus` pin (`3822/3822 real; axioms: propext,
  Classical.choice, Quot.sound`) and `#veil_status FallbackReceipt`
  (`220/220 real`);
* the `sat trace` reachability witnesses in `Cadence.lean` and `Conductor.lean`;
* the pinned `#model_check` counterexample to the **v1** rule in
  `FallbackReceipt/PreFix.lean`.

I additionally re-derived the axiom footprints **independently** of the pins,
by elaborating a scratch file that imports `Cadence` and runs bare
`#print axioms`. All seven end results report exactly the standard trio:

```
'Chorus.invariants_of_reachable'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Chorus.slotConsensus_instance'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Chorus.evidence_pigeonhole_of_reachable'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Conductor.orchestrator_instance'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Cadence.positional_log_safety'               depends on axioms: [propext, Classical.choice, Quot.sound]
'FallbackReceipt.invariants_of_reachable'     depends on axioms: [propext, Classical.choice, Quot.sound]
'FallbackReceipt.build_totality_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This matters more than it may look, because the dependency tree is *not* free
of `sorry`: the build log shows
`Smt/Reconstruct/BitVec/Bitblast.lean:36:4: declaration uses 'sorry'` in the
lean-smt package. That declaration is not reachable from any Cadence end
theorem — which is exactly what the footprints above establish, and exactly the
class of regression the pins exist to catch. An auditor who checked only "the
build is green" would not have ruled it out.

**Two reproduction notes, neither a defect in the artefact.**

1. *Toolchain.* On a fresh container the Veil frontend fails to load with
   `error loading library, libLake_shared.so: cannot open shared object file`.
   The library is present in the Lean toolchain; exporting
   `LD_LIBRARY_PATH` to the toolchain's `lib/lean` directory before
   `lake build` fixes it. Worth adding to `docs/Container.md`.
2. *Solver-scheduler contention.* With the script's default batching (6 proof
   files at once) two VCs hit the 60 s discharge limit on this machine --
   `byz_sign_fb_pos` preserving `msg_fb_pos_sig_backed`, and
   `byz_sign_vote_pos` preserving `fastqc_complete_implies_mvba_evidence`.
   Reducing the batch to 3 did not help; building those files **one at a time**
   discharged both, the first in **21.1 s** against its 60 s budget. The log's
   own "near timeout (60-64% of 60.0 s)" annotations on many neighbouring VCs
   confirm the cause is wall-clock contention between concurrently running
   dischargers rather than solver difficulty — the same diagnosis
   `docs/TODO.md` records for its A/B measurements (245 s CPU against 1420 s
   wall). The green run above was obtained with one proof file per `lake build`
   invocation. Making the batch size a parameter of `scripts/revalidate.sh`,
   with a note that a core-poor machine should use 1, would save the next
   auditor several hours.

---

## 4. Property coverage

Legend: **MC** = machine-checked in Lean; **MC(inst)** = machine-checked as a
contract-instance field; **meta** = argued in documentation against a named
assumption; **oos** = deliberately out of scope, documented.

### 4.1 MCP (paper Appendix A, Definitions 1–4) and Cadence-level claims

| Paper claim | Artefact | Status |
|---|---|---|
| Def. 1 **MCP Safety** (prefix consistency of correct validators' logs) | `Cadence.positional_log_safety` (`Composition.lean`), over any strictly-slot-ordered enumeration of `appended` | **MC** |
| Slot-level agreement / skip agreement / inclusion lift / bounded-concurrency interval | `Cadence.reachable_log_agreement`, `reachable_skip_agreement`, `reachable_inclusion_lift`, `reachable_bounded_concurrency_interval` | **MC** |
| Def. 2 **ℓ-Liveness** | timed statement; derived in `docs/Liveness.md` + Conductor header from (F-justice), (A-sc-termination), (A-acs-termination) | **meta** |
| Def. 3 **c-Censorship-Resistance** | timed; reduced to proposal inclusion + orchestrator recovery | **meta** |
| Def. 4 **Hiding** (simulation-based) | protocol half only: `Chorus.safety [hiding_until_deadline]`; the simulation/indistinguishability half is a `ThresholdIBE` class field | **MC** (protocol half) / **oos** (crypto half) |
| **B-Bounded-Concurrency** (numeric `2W−p`) | interval form is **MC** (`bounded_tail`); the cardinality corollary is meta | **MC** + **meta** |

### 4.2 Chorus (`mod:slotconsensus`, paper Appendix C)

| Paper claim | Artefact | Status |
|---|---|---|
| **Agreement** (Lemma: any two correct validators commit the same core) | `safety [agreement_pos]`, `[agreement_pos_neg]` | **MC** |
| **Slot safety / integrity** (one entry per proposer) | `safety [integrity_pos]`, `[integrity_pos_neg]` | **MC** |
| `mod:slotconsensus` **Slot safety** (`slot_of V = inst_slot`) | `SlotConsensus.slot_safety` field of `slotConsensus_instance` | **trivial** — discharged by `rfl` because the single-slot model sets `inst_slot := default` and `slot_of _ := default`; no content (see Finding 6) |
| **Proposal Inclusion** (Prop. 2, under the on-time/synchrony premise) | `safety [proposal_inclusion]`, `[proposal_inclusion_no_neg]`, with the premise modelled as `all_honest_recorded` | **MC** (premise assumed, see Finding 3) |
| **Hiding** (protocol level) | `safety [hiding_until_deadline]` | **MC** |
| **Safety of speculative finalization** (§4, v2 p. 16) | `safety [speculative_agreement_pos]`, `[speculative_agreement_pos_neg]` under `no_equivocation` | **MC** — but see **Finding 1** |
| **ℓ-Termination** (Prop. 5) | fair-progress invariants (`progress_voting`, `progress_fallback_signing`, `fast_path_implies_vote_quorums`, `fastqc_complete_implies_mvba_evidence`, `local_committed_complete`) carry the state content; the temporal glue is meta | **MC** (safety content) + **meta** |
| The termination argument's counting step (evidence pigeonhole) | `Chorus.evidence_pigeonhole_of_reachable` (`Pigeonhole.lean`), for every `n = 3f+1` | **MC** |
| **d_tot-Totality** (Prop.: `recoverProposals` does not block) | `*_chunks_decodable` invariant chain ending in `local_committed_pos_implies_decodable`; the timing is meta | **MC** (state content) + **meta** |
| `Chorus ⊨ SlotConsensus` | `Chorus.slotConsensus_instance` | **MC(inst)** |

### 4.3 Conductor (`mod:orchestrator_2`, paper §5 / Appendix D)

| Paper claim | Artefact | Status |
|---|---|---|
| **Integrity** (each window entered once, in order) | `entered_prefix`, `entered_zero`, `bounds_shape`, `decided_downward_closed` | **MC** |
| **Monotonicity** / window-assignment safety | `window_assignment_agreement`, `win_separation`, `win_bounds_ordered`, `open_prefix_agreement`, `open_local_order` | **MC** |
| **B-Boundedness** (interval form) | `bounded_tail` | **MC** (numeric corollary meta) |
| **Totality**, **(2Wτ)-Recovery** | genuinely temporal; per-window induction reproduced in the Conductor header against (F-justice), (A-acs-*), (A-sc-*) and the four `line:assumption-*` arithmetic side conditions | **meta** |
| `Conductor ⊨ Orchestrator` | `Conductor.orchestrator_instance` (formal field `open_prefix_agreement`) | **MC(inst)** |

### 4.4 v1 bug refutation

`Cadence/FallbackReceipt/PreFix.lean` models paper **v1** Algorithm 5 exactly
as written (line 17 accepts *any* valid evidence; lines 20–23 harvest only
FastQCs and FallbackQCs, silently dropping a carried EquivCert; lines 35–37
then propose while claiming every `Ev(j)` is certified) and pins a **reachable
counterexample** to `prefix_valid_by_construction` at `n = 4, f = 1` via
`#model_check`, with `sequential := true` for determinism. I checked the v1
text against the model line by line: the reproduction is faithful, and the
counterexample is a genuine reachable state of the v1 algorithm, not an
artefact of the encoding. The v2 model (`FallbackReceipt.lean`) carries the
fixed rule and proves the property. This is the strongest single piece of
evidence in the repository that the models have real content.

---

## 5. Soundness assessment

### 5.1 Trust base

| Trusted | Not trusted |
|---|---|
| Lean 4 kernel | cvc5 `unsat` verdicts (reconstructed + kernel-checked; pinned) |
| Veil's VC generation (transition-relation semantics, WP calculus) | — |
| Veil's concrete model checker (only for `sat trace` / `#model_check`) | — |
| The `ThresholdIBE` and `MVBA` / `ACS` class contracts | `ByzNodeSet` — **proved**, not assumed (see §5.3) |

I verified mechanically that:

* There is **no** `sorry`, `axiom`, `native_decide`, or `@[implemented_by]` in
  any Lean source in the repository. Every textual match for "sorry" is prose
  in a docstring discussing `sorryAx`.
* **All 49** per-action proof files (39 Chorus + 10 FallbackReceipt), plus all
  four model files that run in-file sweeps, set `set_option veil.smt.trust false`.
  There is no file where trusted SMT is silently left on.
* Loom's `axiom trust_smt` exists in the *dependency*, and is exactly what the
  seven axiom pins exclude from the end theorems' footprints. This is the
  right place to put the check.

### 5.2 Vacuity

The single most common way a formalization of this kind is worthless is that
the interesting states are unreachable, making safety vacuous. The repository
takes this seriously and mostly discharges it:

* `Cadence.lean` and `Conductor.lean` each carry `sat trace` reachability
  checks that exercise the pipeline end to end (open → complete → propose →
  ACS decide → enter next window).
* `FallbackReceipt/PreFix.lean` has an exhaustive `#model_check` whose explored
  graph is asserted to contain proposing runs.
* **Chorus does not carry an in-build `sat trace`** (Finding 4). Its
  non-vacuity currently rests on the monitor fixtures
  (`traces/fast_path_positive.jsonl`, `fast_path_negative.jsonl`), which do
  drive several validators to `finalize_commit` — but CI does not run the
  monitor.

I additionally traced the guards of the finalization chain by hand
(`propose` → `deliver_chunk_assigned` → `record_chunk` → `vote` →
`aggregate_fastqc_pos` → `commit_sign_pos` → `cast_fast_commit` →
`broadcast_commitqc_pos` → `commit_assign_pos` → `finalize_commit`) looking for
a mutual conflict at `n = 4, f = 1`, and found none; the monitor fixtures drive
exactly this chain to `finalize_commit`. So I have no reason to think the Chorus
properties are vacuous — but that is a hand argument plus an out-of-CI fixture,
not an in-build machine check, which is the gap Finding 4 records.

### 5.3 The quorum abstraction is consistent

`Cadence/ByzQuorum.lean` **proves** the `ByzNodeSet` interface (supermajority
intersection, `greater_than_third` counting, the honest-majority facts) for the
concrete `byzNodeSetFinGen` family, for all `n ≥ 3f+1` and any Byzantine set of
size ≤ f, with worked `example` instances at n = 4, 5, 6. This is important:
the quorum axioms are the heart of every intersection argument, and had they
been an unmodelled class they could in principle have been contradictory,
making all 97 Chorus properties vacuously provable. They are not. This is the
single best soundness feature of the artefact and it is easy to overlook.

### 5.4 Adversary model

Every network relation `msg_*` that an honest action reads has at least one
corresponding Byzantine producer action (`byz_sign_proposer`, `byz_cast_vote`,
`byz_sign_vote_pos/neg`, `byz_sign_fb_pos/neg`, `byz_sign_fallback`,
`byz_sign_commit_pos/neg`, `byz_cast_commit`, `byz_sign_fbcommit`,
`byz_deliver_chunk`, `byz_release_msg_decrypt_share`), and the certificate
assembly actions (`broadcast_commitqc_*`, `aggregate_fastqc_*`) are open to any
caller subject only to the signature-quorum guard. I checked this coverage
relation exhaustively by grep: there is no message type the adversary is
unable to forge that it should be able to forge. `is_byz` is immutable
configuration with `|byz| ≤ f` enforced through the `ByzNodeSet` interface.

### 5.5 The network model (meta-argument)

The models are **monotone**: network relations only ever go `false → true`, and
there is no explicit message-delivery step or delay. The soundness argument
(`docs/ChorusDesign.md` §3.1–§3.3) is the standard one: a monotone model
simulates an asynchronous one, *provided* network relations are read only in
**positive** position ((M-frame)); a negative read `¬ msg_x` would let an
action's enabledness depend on a message *not yet* having arrived, which the
asynchronous adversary can arrange but which monotonicity would then make
permanent.

The argument is correct, and the repository is refreshingly honest that
Veil does not enforce (M-frame) — it is hand-audited, and
`docs/Architecture.md` §4 item 1 puts it first on the assumption list, with
`docs/TODO.md` proposing the meta-program that would mechanize it.

**I re-ran that hand audit.** Result: the contract's *conclusion* holds — every
negative read of a network relation in `Cadence/Chorus.lean` is sound — but the
audit table in §3.1 that records the result is wrong in two rows, and the
justification needed for the reads it misses is a category the documentation
does not have. See **Finding 2**.

### 5.6 Liveness (meta-argument)

Nothing temporal is formalized, and the artefact says so plainly. What is done
instead is, in my judgement, the right decomposition:

* the *state-level* content of each liveness step is stated as an SMT-checked
  invariant (e.g. `progress_voting`, `progress_fallback_signing`,
  `fast_path_implies_vote_quorums`, `fastqc_complete_implies_mvba_evidence`,
  `local_committed_complete`, and on the Conductor side the whole
  `entered_*`/`win_*`/`opened_*` family);
* the *temporal* glue (fair scheduling ⇒ eventual firing) is a small number of
  **named** assumptions — (F-justice), (F-byz), (A-mvba), (A-sc-termination),
  (A-sc-totality), (A-acs-termination), (A-acs-totality), (A-orch-*) — that
  appear verbatim in the Lean sources at the point of use, so
  `grep -rn '(A-' Cadence/` enumerates the consumers and would expose an
  assumption that had crept in unlisted. I ran that grep; the consumers match
  the inventory.

I checked the Chorus termination argument (`Chorus.lean` liveness section)
against paper Proposition 5 and the case split is exactly the paper's: with
`x` = number of honest validators that reach a fast commit vote, the
fast-dominant / mixed / fallback branches map one-to-one onto the paper's
timeline. The one counting step (the evidence pigeonhole in the `x = 0`
branch) has since been promoted from a meta assumption to a real Lean theorem,
`Chorus.evidence_pigeonhole_of_reachable`, for every `n = 3f+1`. The
Conductor's per-window induction (`prop:enters-every-window`,
`prop:window-open-time` → `prop:smooth-windows` →
`prop:first-post-gst-window-time`) is likewise reproduced in prose with the
four parameter side conditions listed explicitly. Enabledness monotonicity —
the premise (F-justice) needs — is argued per action and I found the argument
correct.

The honest limitation: (A-mvba) bundles MVBA termination, partial synchrony,
and quorum availability into one black box. `docs/TODO.md` already flags this
as the assumption most worth decomposing, and I agree.

---

## 6. Findings

### Finding 1 — the DA re-encode abstraction is load-bearing for the speculative-finality properties (severity: medium; documentation + scope)

> **Resolution note (2026-08-25).** Closed at the model level by `3395fa9`
> (2026-08-19): the re-encode check is now modelled by its verdict predicate
> `well_encoded`, and the speculative-finality properties take the paper's
> full culprit hypothesis `no_equivocation → no_invalid_encoding → …`. The
> `docs/History.md` entry records the change (and a bonus: the manual-cell
> surface shrank 14 → 11).

**What the docs say.** `docs/ChorusDesign.md` §3.4 records that the DA
re-encode consistency check (`alg:da` `line:da-reencode`) is not modelled —
with `merkle_root` opaque, "`f+1` chunks for root `m`" is simply taken as
decodable — and asserts that this "weakens only the DA-decodability
auxiliaries (`*_decodable`), not agreement".

**What I found.** The abstraction is *also* load-bearing for
`safety [speculative_agreement_pos]` and `[speculative_agreement_pos_neg]`.
The chain is:

* `fb_sign_neg`'s guard forbids an honest negative fallback entry whenever some
  root `M` has, inside the witnessed quorum `qv`, an `f+1` positive sub-quorum
  **and** a global `f+1` chunk quorum;
* invariant `vote_pos_quorum_implies_decodable` makes the second conjunct a
  consequence of the first (valid positive votes carry chunks);
* so the guard collapses to "no `f+1` positive sub-quorum in `qv`", which is
  what `fb_neg_qv_no_pos_quorum` and then the keystone
  `fb_neg_no_pos_quorum` record, and what the speculative properties consume.

In the real protocol the collapse does **not** hold: an honest validator can
gather `f+1` yes votes on `r`, decode, find that the chunks re-encode to
something other than `r`, and cast fallback-no anyway. Paper v2 says this in
so many words, in the parenthetical closing the "Safety of speculative
finalization" argument (p. 16): *"There are two further ways an honest
validator casts a fallback-no for pj: it gathers f + 1 yes votes for a root r
whose chunks fail to re-encode to r, or it receives conflicting yes votes and
never gathers f + 1 on any single root. Either way the proposer is the culprit
— committing to an invalidly encoded root or disseminating several distinct
proposals."*

The model's `no_equivocation` hypothesis covers the *second* of those two cases
(`msg_proposer_signed j m1 ∧ msg_proposer_signed j m2 → m1 = m2` rules out
several distinct proposals) but **not the first**. So the model proves the
speculative claim under a strictly weaker culprit set than the paper admits,
and it can do so only because invalid encodings do not exist in the model.

**Assessment.** This is not an unsound proof — the theorem is true of the model
— and it is not a hidden assumption in the sense of §4's inventory, since the
abstraction *is* listed there (item 5) and in `docs/ChorusDesign.md` §3.4. It
is a case where the documented *consequence* of an abstraction is understated:
§3.4's "not agreement" is right for `agreement_pos`/`agreement_pos_neg` (which
assume nothing and rest on commitQC/MVBA quorum intersection, untouched by the
abstraction) and right for proposal inclusion (an honest proposal is correctly
encoded by hypothesis, so the re-encode check passes — the paper says exactly
this), but wrong for the speculative properties.

**Recommendation.** Either (a) strengthen `no_equivocation` — or add a sibling
ghost relation, e.g. `no_proposer_misbehaviour` — with a "no proposer committed
to an invalidly encoded root" conjunct, so the hypothesis matches the paper's
culprit set once a re-encode predicate is introduced; or, cheaper, (b) amend
`docs/ChorusDesign.md` §3.4 to say that the abstraction is load-bearing for
`speculative_agreement_*` and add a sentence to the `Chorus.lean` speculative
section recording that the paper's third culprit case is abstracted away.
(b) alone would fully resolve the finding as a documentation matter.

### Finding 2 — the (M-frame) audit table in `ChorusDesign.md` §3.1 has two incorrect ✓ entries (severity: low–medium; documentation of the top checklist item)

> **Resolution note (2026-08-25).** Closed by `fa4276f` (2026-08-19): the
> §3.1 table was corrected, and the seven *self-row* reads became their own
> documented exception category with the writer-condition justification;
> `742cf53` reconciled the exception count elsewhere (CLAUDE.md still said
> "two"). The Lean line numbers cited below are as of `bfeee8c` and have
> drifted since; the action names and the count (seven) remain exact. The
> recommended machine classification is open work — `docs/TODO.md`
> § Soundness.

`docs/ChorusDesign.md` §3.1 carries the hand-audit result as a table of which
relations satisfy (M-update) and (M-frame). Two rows claim **(M-frame) ✓** for
relations that are in fact read negatively:

| Table row | Actual negative reads in `Cadence/Chorus.lean` |
|---|---|
| `msg_commit_cast` (marked ✓, with only the `fb_sign_neg` caveat) | `require ¬ msg_commit_cast i` in **six** actions: `commit_sign_pos` (637), `commit_sign_neg` (646), `cast_fast_commit` (658), `fb_sign_pos` (733), `fb_sign_neg` (759), `cast_fallback_vote` (781) |
| `msg_proposer_signed` (marked ✓) | `require ∀ m2, msg_proposer_signed j m2 → m2 = m` in `propose` (540) — precisely the `∀ R, R(…) → …` shape that §3.1.1 lists as a contract violation |

Both reads are **sound**, and for the same reason, which is a *third*
justification not among the two the documentation records (`fb_sign_neg`'s
witnessed quorum; `cast_fb_commit`'s frozen decided vector): the relation row
being read negatively is indexed by the **acting honest validator itself**, and
only that validator's own actions write it (`msg_commit_cast i` is written by
`cast_fast_commit i` and, for Byzantine `i` only, `byz_cast_commit i`;
`msg_proposer_signed j` by `propose j` and, for Byzantine `j` only,
`byz_sign_proposer j`). Under the §3.2 simulation such a read has the same value
in the async run as in the monotone one, so no adversarial scheduling can
exploit it. Semantically they are the local checks "I have not already cast my
commit vote" and "I have not already proposed a different root" — exactly what a
real validator can observe about itself.

So the *conclusion* of the hand audit stands; what is wrong is the evidence a
reader would use to re-check it. That matters more than a usual documentation
slip, because `docs/Architecture.md` §4 puts (M-frame) **first** on the
assumption checklist precisely on the grounds that no tool enforces it and "it
takes a human to confirm each use is positive". A human doing so from the §3.1
table would be misled.

**Recommendation.** Correct the two rows to ✗-with-justification, add the
self-row category to the §3.1.1 contract text ("negative reads of a relation row
indexed by the acting validator, which only that validator writes, are sound —
enumerate them"), list the seven sites, and reconcile §3.1.1 with
`Architecture.md` §4 item 1 so both documents name the same exception set. The
automated syntactic check already proposed in `docs/TODO.md` would have caught
this and is worth prioritizing; it should *classify* occurrences rather than
merely reject them, so that self-row reads are reported and acknowledged
explicitly.

### Finding 3 — proposal inclusion is at Merkle-root granularity (severity: low; scope, documented)

`SlotConsensus.includes` / the glue's `pvector` are `node → Option merkle_root`.
The model therefore proves the paper's Proposition 2 up to *roots*: no honest
validator commits a negative entry for an on-time honest proposer, and every
positive entry carries that proposer's root. The paper's final step — from
"same root" to "same recovered proposal", i.e. decode/decrypt determinism plus
recovery guarantee (ii) — happens below the model's abstraction (documented as
"root opacity"). Similarly, the synchrony premise itself
("`s.deadline − Δ ≥ GST`, dissemination at the slot's starting time") is
modelled as the hypothesis `all_honest_recorded` rather than derived.

No action needed beyond what the docs already say; recorded so a reader does
not over-read `safety [proposal_inclusion]`.

### Finding 4 — Chorus has no in-build non-vacuity witness (severity: low; assurance)

> **Resolution note (2026-08-25).** The recommendation was taken by
> `bead354`: the monitor suites now run in CI after the verification stage
> (`.github/workflows/verify.yml`), making the fixture run the standing
> non-vacuity witness. The two blockers for an in-build `sat trace` stand,
> recorded in `docs/TODO.md` § Soundness.

`Cadence.lean` and `Conductor.lean` carry `sat trace` checks; Chorus — by far
the largest and most property-dense model — does not. Its non-vacuity rests on
the monitor fixtures under `traces/`, and `.github/workflows/verify.yml` runs
only `scripts/container.sh verify` plus marker assertions, not the monitor. A
future edit that made `finalize_commit` unreachable would leave all nine Chorus
safety properties vacuously true with a green build.

**Recommendation.** Add a named-step `sat trace` to `Chorus.lean` reaching
`local_committed i ∧ local_committed_pos i j m` for two distinct honest `i`
(named steps, not `any k actions` — the Conductor file already documents why),
and/or run the monitor in CI. `docs/TODO.md` already lists the general
discipline; this is the one model where it is not yet applied.

### Finding 5 — Conductor's `open_slot` guard turns a timing argument into a modelling assumption (severity: low; documented)

`open_slot` requires that all smaller scheduled slots have already been opened.
In the paper this is a *consequence* of punctual firing against the window
schedule (`prop:fate-order`); in the untimed model it is a guard, and
`open_local_order` then follows almost by construction. The Conductor header
declares this load-bearing, which is the right disclosure. `acs_decide`
similarly carries a "no honest validator has entered `w`" `require`, and the
median upper-half bracket is deliberately unmodelled (`Windows.lean` proves
only `lowerMedian_between_correct`).

Also worth flagging to the paper's authors rather than to the artefact: the
verified Conductor is the **appendix ACS variant**, not the main-body prose
"deadline agreement (median MVBA)" variant. `docs/ConductorDesign.md` §1
identifies this divergence in the paper itself — including the reviewer comment
left in the source — and chooses the version the proofs cover. That is the
correct choice, and the divergence is the paper's, not the model's.

### Finding 6 — composition is contract-level, not refinement-level (severity: low; scope, documented)

`Chorus ⊨ SlotConsensus` and `Conductor ⊨ Orchestrator` are proved as
*instances* over reachable states: the contract's formal (safety) fields are
discharged from the modules' proven invariants. What is **not** proved is a
trace-level refinement showing that the glue module's oracle actions are
correctly implemented by the two module models — i.e. the composition is sound
at the level of the interface contracts, not by simulation.
`docs/ChorusDesign.md` §10.1 says so explicitly. Combined with Chorus being
single-slot (cross-slot independence argued, not modelled), this is the largest
remaining scope gap in the development, and it is accurately advertised.

The practical shape of this is worth spelling out, because it determines how
much the glue module's own theorems say. In `Cadence/Cadence.lean` the oracle
contracts appear as `require` clauses: `sc_finalize` requires, among others,
`∀ j v', ¬ is_byz j → finalized j s v' → v' = v` (SlotConsensus agreement,
cross-validator half) and `orch_open` requires the two open-prefix-agreement
clauses. Consequently `safety [log_agreement]` — MCP safety's same-slot case —
follows almost immediately from its own guard via `[appended_finalized]` and
`[finalized_agreement]`. That mirrors the paper's `lemma:cadence-safety`, whose
same-slot case is likewise a one-line appeal to SlotConsensus agreement, so it
is faithful rather than circular; but it does mean the glue module's verified
content is concentrated in the *cross-slot* case (`skip_agreement`, which needs
the Orchestrator's open-prefix agreement, plus the resolved/appended prefix
bookkeeping) and in `Cadence.positional_log_safety`'s list-level prefix
argument. The two module models are where the quorum-intersection work actually
happens; the glue is the plumbing, and the two are joined by matching contract
signatures rather than by a simulation proof.

One concrete consequence worth naming, since a reader scanning
`slotConsensus_instance` might not notice: its `slot_safety` field is discharged
by `rfl`. The single-slot model sets `inst_slot := default` and
`slot_of _ := default`, so the paper's Slot-safety obligation
("a finalized vector carries this instance's slot number") is definitionally
true here and carries no content. That is the honest encoding of a single-slot
model — there is no other slot to confuse it with — but it means two of the
three formal `SlotConsensus` fields (`agreement`, `proposal_inclusion`) carry
the instance's whole verified weight. A note to that effect at the field would
save a future reader the check.

### Finding 7 — `Chorus.lean` prose lags the Pigeonhole promotion (severity: trivial)

> **Resolution note (2026-08-25).** Closed by `fa4276f`: the model's liveness
> section now states the pigeonhole is mechanised, and the acknowledging
> `NOTE` in `Chorus/Pigeonhole.lean` was removed.

The liveness section of `Cadence/Chorus.lean` still describes the evidence
pigeonhole as a meta step, although `Chorus.evidence_pigeonhole_of_reachable`
now proves it in Lean; `docs/Architecture.md` §4 item 2 and
`docs/ChorusDesign.md` §7 correctly say so and explicitly remove it from the
assumption list. `Cadence/Chorus/Pigeonhole.lean` already carries a `NOTE`
acknowledging the lag and deferring the touch-up to the next substantive
`Chorus.lean` edit, so this is a known item rather than an oversight. Recorded
only because a reader who starts from `Chorus.lean` — the natural entry point —
meets the stale wording first, and `docs/TODO.md` itself calls stale comments
"the most expensive kind of documentation error here".

### Finding 8 — reproduction friction on a fresh, core-poor machine (severity: trivial; tooling)

> **Resolution note (2026-08-25).** Closed by `bead354`:
> `scripts/revalidate.sh` and `scripts/container.sh` take `BATCH` (with the
> `BATCH=1` few-cores guidance in the script header), and the
> `LD_LIBRARY_PATH` workaround is recorded in `docs/Container.md`.

Both items are detailed in §3.1 and neither affects the artefact's claims:

* the `libLake_shared.so` load failure on a fresh container, fixed by exporting
  `LD_LIBRARY_PATH` to the toolchain's `lib/lean` — worth a line in
  `docs/Container.md`;
* `scripts/revalidate.sh`'s fixed batch size of 6 causes discharger contention
  on 8 cores, producing spurious 60 s VC timeouts that vanish when the same
  files are built alone — worth making the batch size a parameter, with a note
  that a core-poor machine should use 1. The script's own header already warns
  the reader to count `⏱` as a failure marker, so a spurious timeout is
  correctly *reported*; it is only the default that is tuned for a larger
  machine.

---

## 7. What I could not verify

* **The `ThresholdIBE` and `MVBA` / `ACS` class contracts have no model
  instance.** `ByzNodeSet` does (§5.3), which is the important one; but until
  the rest of the class stack is instantiated, one cannot rule out — by machine
  — that those axiom sets are contradictory. `docs/TODO.md` lists this first
  under "Soundness", correctly.
* **Definition 4 (Hiding) in its simulation-based form.** Only the protocol
  half is formalized; the cryptographic half is a class field, honestly
  labelled.
* **Everything timed.** ℓ-termination, `d_tot`-totality, quiescence, the
  numeric `2W−p` bound, `(2Wτ)`-recovery, ℓ-liveness and
  c-censorship-resistance. The models are untimed by design and no formal
  artefact in the repository claims a latency bound.
* **Veil's own VC generation.** Whether the emitted Hoare triples faithfully
  capture the Veil source's transition relation is part of the trusted base
  here, as it must be for any Veil development. I did spot-check the shape of
  several generated VC statements against their actions and found no surprise.
* **`#veil_status` re-run outside its pin.** The two coverage assertions passed
  as part of the green build (a mismatch would have failed `#guard_msgs`), but
  I was not able to re-invoke the command standalone in a scratch file to read
  its output directly, as I did for `#print axioms`. The independent evidence
  for coverage is therefore the hand count of actions and properties in §2
  (39 x 97 + 39 = 3822, matching the pin) rather than a second machine run.
* **Paper-text fidelity below the abstraction line** — erasure-code arithmetic,
  chunk indices, Merkle path verification, payload bytes, signature
  unforgeability. All abstracted, all listed in `docs/Architecture.md` §4 item 5.

---

## 8. Overall assessment

The suite re-builds green from cold in an environment other than the authors',
and the end theorems' axiom footprints re-derive independently to the standard
Lean trio, so the machine-checked claims in §4 stand on evidence I reproduced
rather than on the repository's own report of itself.

This is a careful and unusually honest formalization. The three features that
most distinguish it from typical protocol-verification artefacts are: (i) the
quorum interface is **proved** for a concrete family rather than assumed, so
the intersection arguments cannot be vacuous; (ii) trusted SMT is switched
**off** everywhere and this is enforced by axiom pins that fail the build on
regression, so the SMT solver is not in the trust base; and (iii) the
assumption inventory in `docs/Architecture.md` §4 is written to be *checked for
completeness*, with each named assumption appearing verbatim at its point of
use — and, as far as I could determine, it is complete.

The v1-bug refutation (`FallbackReceipt/PreFix.lean`) is strong independent
evidence that the models have real content: the same machinery that proves the
v2 rule safe finds a reachable violation of the v1 rule at n = 4.

The findings above are refinements, not corrections. Finding 1 is the only one
that changes what a reader should believe a proven theorem means, and it can be
fully resolved by a documentation amendment (or, better, by extending the
`no_equivocation` hypothesis to match the paper's culprit set).
