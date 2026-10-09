# History — how the verification reached its current state

**This is a historical ledger, not a status document.** For what is proven
now, read [the guide](https://larskuhtz.github.io/cadence/guide/) and the audit root
[`../Cadence.lean`](../Cadence.lean); the architecture and its trust bases
are [`Architecture.md`](./Architecture.md). Statements below describe the state at
the time they were written; where an old reading has since been superseded
that is said explicitly, but nothing here should be taken as current.

It is kept for three reasons: the per-build records show *what changed and
why* (several entries are model-fidelity corrections against the paper); the
failure tables document how each safety property came to be provable, which
is the interesting part of an inductive-invariant development; and the
"modelling contract" section records a load-bearing assumption that the tool
does not enforce.

The verification *pipeline* also changed a great deal over this period. That
work lives in the public Veil fork, one branch per change, and is not
re-documented here — [`Dependencies.md`](./Dependencies.md) says which
capabilities this project depends on and why. Where a build entry below
mentions pipeline mechanics, it is because the project's file layout or its
trust base changed with it.

## Module status (as of the last full re-validation)

The models are **build-independent**: none imports `Cadence/Chorus.lean`, and
`Cadence/Cadence.lean` / `Cadence/Conductor.lean` import only
`Cadence/Interfaces.lean`, `Cadence/Windows.lean` and `Cadence/Tooling.lean`.
So a from-scratch build verifies each component once, and editing the small
models never re-runs the Chorus family.

| Module | Content | Verification | Wall |
|---|---|---|---|
| `Cadence/Interfaces.lean` | the module contracts `SlotConsensus`/`Orchestrator`/`ACS`/`MVBA` as two-level type classes over explicit state (`…Safety` fragments + full classes), `FaultModel`, `Run`/`TimedRun` | plain Lean (no VCs) | ~2 s |
| `Cadence/Windows.lean` | `IsMedian`, `lowerMedian`, the median range lemma | plain Lean proofs, no sorries | ~1 s |
| `Cadence/Cadence.lean` | the pipelining glue: 6 actions (two oracle steps, two handlers, two protocol actions), 4 safety + 21 invariants, against `OrchestratorSafety`/`SlotConsensusSafety` as class constraints | 182 VCs ✅ + 2 `sat trace` ✅ + `#gen_theorems`, at **`veil.smt.trust false`** (since 2026-07-07; contract-constraint form since 2026-09-04) | ~30 s |
| `Cadence/Conductor.lean` | the orchestrator: 7 actions, 5 safety + 15 invariants + 3 step properties, against `ACSSafety` as a class constraint | 189 VCs ✅ + 2 `sat trace` ✅ + `#gen_theorems`, at **`veil.smt.trust false`** (since 2026-07-10; contract-constraint form since 2026-09-04) | ~60 s |
| `Cadence/Composition.lean` | `invariants_of_reachable` + named `reachable_<property>` projections for both small models (emitted by `#gen_composition`), `Conductor ⊨ OrchestratorSafety` (every field; the two-state ones from M13's generated step lemmas and the checked `step_property` cells, Integrity's timing half among them), `orchestrator_of_temporal` toward the full `Orchestrator`, positional MCP Safety (`positional_log_safety`) | plain Lean over the persisted VC theorems and Veil's generated step lemmas — kernel-checked; axioms `#guard_msgs`-pinned to the three-axiom form | ~10 s |
| `Cadence/System.lean` | the composed system: the glue's MCP Safety at the Conductor and Chorus instances, Chorus's MVBA constraint filled by `Mvba.mvbaSafety` (`system_positional_log_safety`); `chorusTheory_assumptions` discharges Chorus's two projection assumptions at the entry vector | plain Lean; axiom-pinned | ~5 s |
| `Cadence/Chorus.lean` | per-slot consensus: 40 actions, 9 safety + 92 invariants + 1 step property, against `MVBASafety` as a class constraint (since 2026-09-10; the decision handlers' certificate check is the one stated bridge) | **model file** — elaborates the transition system and persists the VC registry (two entries per cell, plus the initializer's); runs no sweep | ~3 min |
| `Cadence/Chorus/Proofs/` ×41 | one file per action (+ `Init`): `#prove_action` re-creates that action's registered VC statements and persists fresh kernel-checked reconstructions as **real proofs**, plus the per-action preservation lemma. The manual quorum-intersection cells are `#prove_vc … by <tactic>` cells in these files, consumed after a statement check | a fresh kernel-checked re-proof for each registered cell, the manual ones included; retry ladder + alternative-encoding fallback built in | warm ~20–30 s per 6-file batch; cold minutes per file |
| `Cadence/Chorus/Certify.lean` | `#gen_composition`: `Chorus.invariants_of_reachable` (41 cases over the preservation lemmas) + `Chorus.reachable_<property>` ×101 | kernel-checked at emission; three-axiom `#guard_msgs` pin **and** the pinned `#veil_status Chorus` audit (every registry cell real; the number lives in the pin itself) | ~40 s (dominated by the audit walk) |
| `Cadence/Chorus/Compose.lean` | `Chorus.slotConsensusSafety` — the Chorus copies as the state-level slot-consensus contract, over `slot × Chorus.State` so the instance's slot is the contract's `tag` (tagged decision vectors; agreement / slot-safety / proposal-inclusion / Hiding's protocol half; the two-state fields from the generated step lemmas and the checked step-property cells over all 40 actions), for every `MVBASafety` instance filling Chorus's constraint, plus `slotConsensus_of_temporal` toward the full `SlotConsensus` | plain Lean over the named reachability projections and Veil's transition bodies — kernel-checked, axiom-pinned | ~5 s |
| `Cadence/Chorus/Pigeonhole.lean` | the **evidence pigeonhole** (`ChorusDesign.md` §7, x = 0 branch) for every `n = 3f+1`: a supermajority of honest fallback entries yields `fb_quorum_pos ∨ fb_quorum_neg ∨ equiv_evidence` — formerly the liveness argument's one meta-level counting step | plain Lean (`two_cover` + the `reachable_*` projections); axiom-pinned | ~22 s |
| `Cadence/FallbackReceipt.lean` | the shipped receipt/propose layer: 9 actions, 1 safety + 20 invariants; discharges the (A-mvba) implementability seam | **model file** (registry, no sweep) + `#model_check` ✅ 23 975 states (`n=4, f=1`) | ~80 s |
| `Cadence/FallbackReceipt/Proofs/` ×10 + `Certify.lean` | the same family shape at small scale — the architecture's fast regression leg | 220 re-proofs + preservation lemmas + `#gen_composition`; three-axiom pin and the pinned `#veil_status` (220/220 real) | ~2–4 s per proof file warm |
| `Cadence/FallbackReceipt/Totality.lean` | build totality — the per-validator two-class pigeonhole, kernel-checked **for every `n = 3f+1`** (`two_cover` → `build_totality_of_complete` from `accepted_entries_complete` → `invariants_of_reachable` → `build_totality_of_reachable`); supersedes an earlier bounded `n = 4` argument | plain Lean over the reconstructed VC theorems; axiom-pinned | ~25 s |
| `Cadence/FallbackReceipt/PreFix.lean` | the *pre-fix* receipt rules; the §7.2 finding mechanically refuted | `#model_check` ❌ violation of `prefix_valid_by_construction` — the §7.2 counterexample trace, `#guard_msgs`-pinned (**the violation is the expected result**) | ~10 s |
| `Cadence/Mvba.lean` | the leader-based MVBA instantiation of the paper repository's **internal supplement** (referent pinned to paper-repo commit `026dc8b`, not yet part of the published paper): 24 actions, 3 safety + 25 invariants; `value` the entry vector, `valid` immutable, `view` a `TotalOrderWithMinimum`; the lock-persistence strengthening `prepqc_blocks_lower_commits` in place of the non-inductive `lem:lock-persistence` | **model file** (registry, no sweep) + 3 `sat trace` ✅ | ~55 s |
| `Cadence/Mvba/Proofs/` ×25 + `Certify.lean` | the family shape at mid scale: 725 re-proofs + preservation lemmas + `#gen_composition`; **exactly two manual cells** (`form_prepqc × prepqc_blocks_lower_commits`, `form_commitqc × commitqc_agree`), written out so a 4-core runner does not time out | three-axiom pin and the pinned `#veil_status` (725/725 real) | ~1 min warm for the whole family |
| `Cadence/Mvba/Compose.lean` | `Mvba.mvbaSafety` — Mvba ⊨ `MVBASafety` (every field: the three safety properties, the two-state fields from all 24 actions' transition bodies, and — since 2026-09-09 — the two inputs, their observables, effects, frames and one-step Quiescence), plus `mvba_of_temporal` toward the full `MVBA`, whose remaining four fields (`clock`, `Admissible`, `ℓ`, Termination) are the smallest gap of the three implementations | plain Lean over the named reachability projections and Veil's transition bodies — kernel-checked, axiom-pinned | ~5 s |
| `Cadence/Mvba/NoLock.lean` | the MVBA instantiation with the `Pre-Prepare` handler's lock check removed, on a restriction of the mutant (bulk `propose`/availability/Byzantine steps, a theory-fixed scheduler and adversary, dropped actions, and since R6 a fixed schedule for the environment and the timeouts) every run of which is a run of the mutant | `#model_check` ❌ violation of `agreement` — a 25-step trace with commit certificates on both values and two correct validators deciding differently, `#guard_msgs`-pinned with `sequential := true` (**the violation is the expected result**) | ~70 s |

## Build history

Numbered builds are full verification runs. The ✅ column counts discharged
verification conditions; ❌ counts counterexamples. Entries 1–13 are model
development; from 14 on the model changes little and the entries record how
the trust base and the file layout arrived where they are.

| # | Outcome | ❌ | ✅ | What it was |
|---|---|---|---|---|
| 1 | exit 1 | 13 | 576 | Baseline — see "Build #1 failure table" below. |
| 2 | exit 1 | 2 | 649 | After fixes 1–3 below. Only `finalize_commit` still failed (`agreement_pos`, `agreement_pos_neg`). |
| 3 | exit 1 | 3 | 803 | After fix 4. `agreement_pos`/`agreement_pos_neg` now ✅; the 3 new MVBA cross-path consistency invariants themselves fail inductively (see "Build #3 failure table"). |
| 4 | exit 1 | 0 | 806 | After fix 5 (MVBA-consistency precondition on `aggregate_fastqc_*`). All invariants pass at the SMT level; the build still failed on a `whnf` heartbeat timeout at `#gen_spec`. |
| — | exit 1 | 0 | 806 | Raising `maxHeartbeats` did not help. Diagnostics showed `FinEncodableInjOnly.card ↦ 429 909 951 unfoldings`: the model-check scaffolding is `O(nᵏ)` in the number of actions and exceeds Lean's reducer at ~40 actions. |
| 5 | exit 0 | 0 | n/a | After gating that scaffolding behind `veil.gen.modelCheckScaffolding` (set `false` in Chorus). `#gen_spec` elaborates in ~100 s. See "Why we disabled `veil.gen.modelCheckScaffolding`" below. |
| 6 | exit 0 | 0 | 1066 | **All safety invariants discharged** — 1 025 SMT goals + 41 does-not-throw checks. ~3 h wall, solver trusted at this point. |
| 7 | exit 0 | 0 | 205 | Added the liveness meta-argument and the 5 enabledness (E) fair-progress invariants. |
| 8 | — | — | — | Added the strict-decrease (D) companions and the fast-path liveness invariants; verification deferred to a full sweep. |
| 9 | exit 0 | 0 | 1960 | **Encoding refactors**: phase and path markers became `enum`s; the three vote actions became one atomic `vote` with bulk updates; two new auxiliaries. ~16 min wall. |
| 10 | exit 0 | 0 | 3312 | **Paper-alignment refactor** — commitQC finalization, the "model fidelity concession" removed, proposal inclusion + hiding + speculative safety added, MVBA evidence made certificate-checkable. Full inventory in the next section. 11 VCs by manual proofs. |
| 11 | exit 0 | 0 | 3348 | `[local_committed_complete]` appended (92nd declaration). The larger invariant clump tipped 3 formerly-green VCs into **e-matching divergence** — different subsets timed out at 300 s, 400 s and 900 s on an idle machine, the signature of seed luck rather than slowness. All three are now manual theorems (14 in total). |
| 12 | exit 0 | 0 | 3348 | **Configuration honesty** (model unchanged): the `set_option veil.smt.timeout 900 in #check_invariants` this project carried had always been *inert* — solver options are captured when the module elaborates its spec. Every sweep on record had run at the 60 s default, which is also the good configuration (the nominal 900 s + finite-model-finding-off, run for real, hit 17 CPU-hours and was killed). The models now state their configuration explicitly before `#gen_spec`. |
| 13 | exit 0 | 0 | 3822 | **Fallback commit round** — fidelity closure against the 2026-07-07 paper revision: new relation `msg_fbcommit_sig`, ghost `fbcommitqc`, honest actions `cast_fb_commit` + `redisseminate_chunk`, Byzantine `byz_sign_fbcommit`; `commit_assign_*` strengthened so that an MVBA decision alone no longer finalizes. Five invariants appended (97 declarations, 38 actions). Green on the first sweep. |
| 14–15 | exit 0 | 0 | 3822 | Content unchanged. Per-VC theorem persistence enabled, and witness-size instrumentation added: 3 809 witnesses, mean 16 900 heap objects, **flat distribution** — every proof carries a near-constant normalisation chain dominated by the 97-conjunct invariant clump rather than by its own action. That measurement is what motivated everything in 16–29. |
| 16–17 | exit 0 | 0 | 3822 | **Proof reconstruction made permanent** (2026-07-10). All 3 822 VCs reconstruct and are kernel-checked: cvc5's `unsat` verdicts are trusted nowhere from here on. Two instructive failures on the way: persisting all ~3 800 reconstructed proofs in one environment needs ~15 GB *on top of* the sweep's ~15 GB and does not fit a 32 GB machine. Chorus therefore persisted statement-only stubs for a while — which is exactly the problem the per-action proof files (25) solved properly. |
| 18 | exit 0 | 0 | 3822 | **The three-axiom pins** (2026-07-11). Splitting the re-proofs across 39 per-action modules — each re-proving the base module's *persisted* VC statements, so statement identity is by construction — made real proof persistence fit: 3 808 fresh kernel-checked reconstructions, ~5 GB per process, ~85 CPU-min in total. Every composition pin flipped to `propext`/`Classical.choice`/`Quot.sound`: **no `sorryAx` anywhere in the build**, which is still true. |
| 19–24 | exit 0 | 0 | 3822 | Pipeline work, model unchanged: the persistent VC registry (so the split above needs no generated scaffolding), and the content-addressed proof cache with kernel replay. Net effect on this project: a warm re-validation of the whole suite went from ~39 min to ~16 min, every cached hit is kernel-checked, and rebuilds stopped depending on solver seeds. |
| 25 | exit 0 | 0 | — | **The current file layout.** Composition emission moved into the tool (`#gen_composition`, `#gen_proof_files`), and both Chorus and FallbackReceipt moved to the model / `Proofs/` / `Certify.lean` family. All generated slice modules and the three Python generators that used to produce them were **deleted**; the 14 manual theorems moved verbatim into their actions' proof files. Measured: Chorus model-only build 90 s (was 1 050 s with an in-file sweep), editor-open proxy 72 s / 6.8 GB (was ~11 min / ~16 GB). |
| 26 | exit 0 | 0 | — | **The audit command.** `#veil_status <Module>` reports, per registry cell, whether a real, statement-matching, kernel-checked theorem is in scope, plus the axiom union over all of them. Pinned at `3822/3822 real` (Chorus) and `220/220 real` (FallbackReceipt): the README's trust chain became a command output rather than a reading exercise. |
| 27–29 | exit 0 | 0 | — | Proof-term slimming: 65–72 % of every reconstruction proof turned out to be the SMT pipeline re-deriving the `Bool → Prop` embedding of the whole hypothesis context. Removing that cut cached proof size ~59 % and the per-cell replay floor from ~0.35 s to ~0.10–0.15 s. **One model-visible consequence**: the cell `vote × fastqc_complete_implies_mvba_evidence` diverges under the new query shape — one cell of 3 822 — and turns the option off file-locally in `Cadence/Chorus/Proofs/Vote.lean`, where the reasoning is recorded. Entry 28 also retired a suspected sweep regression: it never existed, an earlier wall-clock figure had been mis-recorded. |

| — | exit 0 | 0 | 843 | **The standalone port** (2026-08-17): this repository extracted from the Veil monorepo onto the public `larskuhtz/veil @ port/integration` and `larskuhtz/loom @ upgrade-v4.28-lakefile-fix` forks. Veil module names were kept, so every VC statement — and therefore every proof-cache key — is unchanged, and the whole family replayed rather than re-solving. Staged re-validation `ALL STAGES GREEN` in **3 min 35 s**: 843 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 16 118 ♻, peak resident memory 18.8 GB, every axiom pin and both `#veil_status` pins holding, `sorryAx` count zero. New in the port: the audit root [`../Cadence.lean`](../Cadence.lean), which re-derives all seven end theorems' axiom footprints in one file. |

| — | exit 0 | 0 | 843 | **Deterministic refutation pin** (2026-08-17, found by building in a Linux container): the `#model_check` in `Cadence/FallbackReceipt/PreFix.lean` had its *full counterexample trace* pinned, but the model checker splits its BFS frontier into `numSubTasks` parallel chunks and that defaults to the machine's **core count** — so which of the many reachable violating states is reported first is hardware-dependent. Measured: 4, 8, 12 and 14 cores each yield a different (equally valid) witness, as does a different OS; the pin had held only because every recorded build ran on the same 14-core machine. Fixed by forcing `(sequential := true)`, which is deterministic and costs ~2 s on this model, and re-recording the trace. Verified identical on macOS/arm64 (14 cores) and Linux/arm64 (4 and 12 cores). No proof was affected — the violation is always found, and it is the violation, not the witness, that is the claim. |

| — | exit 0 | 0 | — | **The `well_encoded` refactor** (2026-08-19, closing external-audit Finding 1 — `docs/AuditReport.md`): the DA re-encode consistency check is now modelled by its *verdict*, the immutable predicate `well_encoded` — required by honest `propose` and `fb_sign_pos`, and admitted as a fallback-no cause in `fb_sign_neg`'s guard — and the speculative-finality properties (with their four support invariants) took the paper's full culprit hypothesis `no_equivocation → no_invalid_encoding → …` (`subsection:chorus-proof`, closing parenthetical). Counts unchanged (38 actions, 97 properties, 3 822 VCs; both `#veil_status` pins hold); the shared hypothesis clump changed, so the whole Chorus family re-solved **cold**: 3 683 ✅ fresh solves, 0 ❌ / 0 💥 / 0 ⏱, ~17 min wall at 12 CPUs in the container, then `ALL STAGES GREEN` end-to-end including the monitor suites (both monitor `Theory` instantiations gained `well_encoded := fun _ => true`). Two structural bonuses: the manual-proof surface **shrank from 14 cells to 11** — the three `fb_sign_neg` cells (`inclusion_no_honest_fb_neg`, `fb_neg_qv_no_pos_quorum`, `fb_neg_no_pos_quorum`) became SMT-tractable (6.2–17.0 s against the 60 s budget) because `no_invalid_encoding` supplies the signed-root-is-well-encoded bridge as an explicit premise, exactly the instantiation the old query shape e-matched on forever; and the 11 surviving manual proofs needed only intro-arity and argument-list adjustments, their by-name VC statements untouched. One transient during development: a single SIGSEGV of the `lean` worker on the first model build, unreproducible cold or warm afterwards. |

| — | exit 0 | 0 | — | **The proof-file prelude** (2026-08-24, ported from an Aristotle proof-simplification run): everything the 49 per-action proof files used to copy-paste moved into [`../Cadence/ProofPrelude.lean`](../Cadence/ProofPrelude.lean), and the 11 manual cells changed *form* without changing content — explicit theorems restating their VC types over ~40 lines of binders each became `#prove_vc … by <tactic>` cells, so the statement now always comes from the registry and a model change can no longer strand a stale hand-written type. The cells open with `unveil_local` instead of `unveil` (~0.4 s vs ~22 s per cell: it skips `veil_simp at *` over the 97-conjunct clump) and project invariant conjuncts **by name** (`inv_have h := <invariant>`) instead of by hand-counted `hinv.2.….1` chains — a stale name, or a clump that no longer matches the declaration list in length, is a loud elaboration error instead of a silently wrong conjunct, and adding or reordering invariants re-indexes nothing. `veil.smt.trust false` deliberately stays written out in every proof file so the no-trusted-solver rule remains greppable. Validated in the container: the 11 cells first re-elaborated **cold** (`veil.cache.proofs false`; 8.1 s total, 0.2–1.4 s per cell), then a staged verify that ran effectively cold (the volume's seeded cache contributed only 196 replays) — `ALL STAGES GREEN`, 16 967 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 196 ♻, ~18 min at 12 CPUs, both `#veil_status` pins and every axiom pin holding, and 4 031 fresh cache entries stored through the shared option macro. The change also put in writing the cache discipline it sharpens (CLAUDE.md § Build): entries are keyed by VC statement, so a warm hit consumes a cell without elaborating its tactic — an edited cell must be solved cold once. |

| — | exit 0 | 0 | — | **The counting theorems** (2026-08-25): the fair-progress argument's remaining counting steps became Lean theorems over the concrete instance family, in [`../Cadence/Chorus/Counting.lean`](../Cadence/Chorus/Counting.lean) — `honest_supermajority` (the honest population is itself a supermajority-sized node set), `fbcert_of_honest_fallback_votes` / `fbcommitqc_of_honest_commit_votes` (certificate formation from all-honest participation, reachability-free), and `commitqc_of_honest_fast_dominant` (the fast-dominant branch's per-proposer commitQC from honest votes alone, via the `commit_*_sig_from_local_fastqc` → `local_fastqc_pos_cross_unique` / `local_fastqc_pos_neg_excl` projection chain). With the evidence pigeonhole (above), **every counting step of `ChorusDesign.md` §7's case split is mechanised**; the remaining meta content of the fair-progress argument is purely temporal ((F-justice)/(F-byz)/(A-mvba)). Three new axiom pins at the standard trio, in-file and re-derived at the audit root. Validated in the container: staged verify `ALL STAGES GREEN`, 843 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 16 124 ♻ — the Chorus family replayed warm, since the model edit is prose-only and no VC statement changed. |

| — | exit 0 | 0 | — | **The progress dichotomy** (2026-08-25, same day as the counting theorems): the liveness case split composed into one theorem, `Chorus.progress_dichotomy_of_saturation` ([`../Cadence/Chorus/Progress.lean`](../Cadence/Chorus/Progress.lean)) — in any reachable state where every honest validator has cast its path vote (fast or fallback, with the per-proposer entries cast required), either a commitQC exists for every proposer from honest votes alone, or `mvba_invoked` holds with per-proposer evidence stated verbatim as `mvba_decide_pos` / `mvba_decide_neg`'s external-validity guards. Proof: all-fast ⇒ `commitqc_of_honest_fast_dominant` per proposer; some fast-caster ⇒ its commit signatures back the case-(a) meta-block trigger and `fast_path_implies_vote_quorums` supplies the evidence; no fast-caster ⇒ `fbcert_of_honest_fallback_votes` + the evidence pigeonhole. The remaining meta content of the fair-progress argument is exactly two temporal steps: (F-justice) delivers the saturation hypothesis, (A-mvba) consumes the conclusion. One new axiom pin at the standard trio, in-file and at the audit root. Validated in the container: staged verify `ALL STAGES GREEN`, 843 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 16 124 ♻ (warm — prose-only model edit). |

| — | exit 0 | 0 | 15 699 | **The (A-mvba) decomposition** (2026-08-25, same day): the oracle-termination assumption shrank to the primitive's own liveness. One new invariant — `fb_pos_sig_proposer_signed`, the `vote_pos_sig_chunk` sibling: every network-valid positive fallback entry, Byzantine signers included, pins a proposer-signed root (honest via the vote-quorum backing chain, Byzantine by `byz_sign_fb_pos`'s validity precondition) — takes the clump to 98 properties / 3 861 cells (both `#veil_status` pins updated). On it, `Chorus.build_totality_of_reachable` ([`../Cadence/Chorus/Counting.lean`](../Cadence/Chorus/Counting.lean)): the receipt layer's build totality restated over Chorus's network state — **any** supermajority of per-proposer fallback entries, arbitrary honest/Byzantine mix (a validator's `2f+1` accepted receipts), yields a buildable meta-block entry: positive FallbackQC, negative FallbackQC, or EquivCert. With it, (A-mvba)'s `ℓ_MVBA` premise *all correct validators propose* is state-level buildable (the fast side is definitional: `vote_quorum_pos` **is** `aggregate_fastqc_pos`'s guard witness), and §7.1's aggregation-enablement caveat is retired; what remains under the name (A-mvba) is only what one assumes of any randomised primitive. The model change forced the expected full cold re-solve: `ALL STAGES GREEN`, 15 699 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 580 ♻, ~21 min at 12 CPUs in the container — with **zero manual-cell repair and zero new divergence**: the eleven `#prove_vc` cells re-elaborated unchanged through the proof-prelude's by-name projections, the first model change to exercise that machinery. |

| — | exit 0 | 0 | 16 729 | **Lean 4.32 and the new Veil action frontend** (2026-09-01): re-pinned onto the fork rebased on upstream `main`, whose 26 new commits are the Lean 4.32 bump, a lean-smt refresh, VC-manager concurrency work and — 22 of them — a rewrite of action-body elaboration onto Lean's extensible `do`-notation. **No model content changed**: no invariant added, no VC statement rewritten, both `#veil_status` pins holding at their existing numbers, all seven axiom-root pins at the standard trio, the pre-fix refutation still finding its counterexample, and all three monitor suites `ALL PASS` with the `#gen_monitor` variant agreeing with the hand-written oracle. The proof cache went wholesale cold — statement expressions normalise differently on the new toolchain — so this was a full re-derivation rather than a replay: `ALL STAGES GREEN`,
16 729 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 588 ♻, and `leanchecker` then re-checked every
stored declaration in all 73 modules natively on macOS (13 min 15 s at
`LEAN_NUM_THREADS=4`). Thirteen files needed mechanical repair, in four categories: `simp`/`dsimp`/`simpa` calls that unfold a class-valued definition now need `+instances` (Lean 4.32 defaults `Simp.Config.instances` to `false`); eleven `def`s whose type is a class need `@[implicit_reducible]`, and in the monitor the missing attribute broke instance *synthesis*, not just the lint; `Chorus.lean` needs `maxRecDepth` raised **before** its action declarations, because the new frontend nests one `openStateAround` per statement; and one `acs_decide` call site in `Cadence/Composition.lean` lost a positional `_`, since Veil now deduplicates identical `Decidable` side conditions in a generated theorem's telescope. Two dependency simplifications came with it: the `larskuhtz/loom` fork was dropped (it existed only because the previous fork set `precompileModules`, which this one does not), and no `:shared` target is forced on Mathlib any more. A native build works on macOS from any checkout path, so every audit tier is reachable without a container — though that is the toolchain's doing rather than this port's: Lake 4.30 began writing linker arguments to a response file on every platform, which is what retired the macOS argument-limit failure. A full warm re-validation (project oleans deleted, cache kept) runs 10 min 54 s at the default `BATCH=6` against 3 min 35 s recorded before the port, with an identical workload (843 ✅ / 16 324 ♻) and lower peak memory (15.3 GB against 18.8 GB). **The cause is not the dropped `precompileModules`**, which was the obvious suspect and was tested three ways: no precompilation 654 s, Veil's library precompiled 688 s, this project's library precompiled 702 s. Precompiling is slightly *slower* — a warm run is dominated by statement re-creation and kernel replay rather than tactic search, so a native tactic layer has little to do. Getting those numbers required fixing three real upstream packaging bugs (recorded in [Dependencies.md](./Dependencies.md)), which is worth having but buys no speed. Most of the gap was the **dropped Bool-atom fold** (entries 27–29), which that fork head did not carry; it was restored the next day (below). Warm re-validation is kernel replay almost in full — building a Chorus proof file costs 39.68 s against 39.78 s to elaborate it without writing the olean, so serialization and Lean 4.32's new axiom-export extension are free — and replay is proportional to stored proof-term size. |

| — | exit 0 | 0 | 17 125 | **The Bool-atom fold restored** (2026-09-02): the fork's `port/bool-atom-fold` was ported forward and merged, so `veil.smt.foldBoolAtoms` is on by default again. Re-pinned, cache purged (4 081 entries — the fold changes proof *terms*, not VC statements, so cached hits otherwise keep replaying whichever shape produced them) and the family re-solved cold: `ALL STAGES GREEN`, 17 125 ✅ / 0 ❌ / 0 💥 / 0 ⏱ in 14 min 35 s, both `#veil_status` pins and all seven axiom pins holding, all three monitor suites `ALL PASS`. No cell became unsolvable and no new e-matching divergence appeared, which was the risk. Effect on the warm path, same machine and workload: per-cell kernel replay **402 ms → 79 ms**, warm re-validation **654 s → 389 s**, peak resident 15.3 → 12.1 GB, and a proof-file olean ~30 MB → 11–12 MB. `Vote.lean` keeps the fold off for the one divergent cell, which makes the comparison controlled inside a single build: its olean stays ~30 MB and its batch costs 42 s against its siblings' 13–15 s. What remains is elaboration, not replay: the three model files alone (Chorus 122 s, FallbackReceipt 63 s, Cadence+Conductor 35 s) account for 220 s of the 389 s. That also **retires the pre-port 3 min 35 s figure as a comparison target** — 220 s of unavoidable model elaboration plus 16 000 replays at that entry's own recorded 100–150 ms floor cannot fit inside 215 s, so the two recorded numbers are not mutually consistent and one of them describes less work than a full re-validation. |

| — | exit 0 | 0 | 1 394 | **The module contracts, mechanised** (2026-09-04; `docs/CompositionContracts.md`): the contracts of `Cadence/Interfaces.lean` were restated as two-level type classes over an *explicit* abstract state — a first-order `…Safety` fragment (state, transitions with the paper's inputs as relations, observables, monotonicity and frame axioms, the paper's safety properties at reachable states) that a Veil module `instantiate`s, and the full class extending it with every temporal and quantitative obligation over `Run`/`TimedRun`, bounds as data, and an implementation-defined admissible-execution model — and the consumers were rewritten to **consume them as class constraints**. The glue holds the orchestrator's and each slot's consensus state (`os`, `sc_state s`), advances them by oracle steps (`orch_step`, `sc_step`), reacts to their observables in handlers (`on_finalize` drives the orchestrator's `complete` input; `participate()` is definitionally the opening) and restates *no* contract property: `finalized_agreement`, `finalized_inclusion` and `opened_prefix_agreement` are now proven from the class axioms. The Conductor likewise consumes `ACSSafety` (one abstract state per window, `acs_step`, `acs_propose` as the `propose` input; `byz_acs_propose` is subsumed by the contract's internal steps), with the median-range `require` of `acs_decide` the one stated bridge to the upper-level quantitative validity. Both re-solved cold and green: the glue 175 VCs (6 actions × 24 properties, initializer, does-not-throw) + 2 traces, the Conductor 168 + 2. On the provider side `Conductor.orchestratorSafety` and `Chorus.slotConsensusSafety` prove every field of the fragments — the **two-state fields** (monotonicity of the observables, the frames, the paper's Monotonicity, a committed validator's frozen entries) from Veil's pre-computed transition bodies (`<action>.ext.tr` via `derived_eq`, one uniform tactic; all 38 Chorus actions in seconds) — and what each does not prove of its full contract is a residual structure (`Conductor.OrchestratorResidual`: Totality, `B`-Boundedness, `R`-Recovery, the execution model; `Chorus.SlotConsensusResidual`: the participation interface Chorus does not model, the clock, Termination, Quiescence) with `…_of_residual` type-checking the restatement against the class and discharging Integrity's timing half resp. Hiding's protocol half on the way. New: `Cadence/System.lean`, `Cadence.system_positional_log_safety` — MCP Safety for the glue running the Conductor's and Chorus's own transition systems, no contract hypothesis left, only the theories and the agreement of the two fault patterns (`hbyz`). `class MVBA` moved from `Primitives.lean` to `Interfaces.lean` (the Chorus family replayed warm — no VC statement changed); the `openPrefixAgreement%` shared-syntax scaffolding of the previous day was removed as superseded. Every new declaration pinned at the standard trio at its site and at the audit root (17 pins). Named seams left (`CompositionContracts.md` §8): the MVBA oracle inside Chorus stays inlined — the model checks validity against its own state, which a class parameter cannot mention — and is tabulated against `MVBASafety`; Chorus's missing participation interface; the ACS median bridge. Validated: staged re-validation from deleted project oleans with the warm cache `ALL STAGES GREEN` in 6 min 42 s at `BATCH=6` — 1 394 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 20 185 ♻, peak resident 13.1 GB — all three monitor suites `ALL PASS`, every `#guard_msgs` pin and both `#veil_status` pins holding. Full record: `docs/CompositionContracts.md`. |
| — | exit 0 | 0 | 224 | **The MVBA single-view spike** (2026-09-08; `docs/MvbaPlan.md` §8 step 2, on branch `worktree-mvba-instantiation`): `Cadence/Mvba.lean` — the leader-based MVBA of the paper repository's **internal supplement** (`subsec:mvba-protocol`, `subsec:mvba-correctness`; pinned to paper-repo commit `026dc8b`, not yet part of the published paper) at **one view and no timeouts**, in the FallbackReceipt file-family shape: model file with registry and no sweep, `Mvba/Proofs/` ×14, `Mvba/Certify.lean`. 13 actions — the two `mod:mvba` inputs (`propose`, `abandon`), seven honest protocol steps including the two certificate assemblies `form_prepqc`/`form_commitqc` that materialise `msg_prepqc`/`msg_commitqc` from `2f+1` signatures (no `∃`-quorum ghost in any consumer's guard), one environment action for `AvailReady_i`, three Byzantine signers — with `safety [agreement]`/`[integrity]`/`[external_validity]` stated in `MVBASafety`'s vocabulary and 12 invariants along `lem:vote-uniqueness`, `lem:commit-provenance`, `lem:cert-uniqueness`; `value` opaque (the entry vector), `valid` an uninterpreted immutable relation, `leader` an immutable individual. **Every cell solved automatically and cold** — 0 cache hits, 2–4.5 s per proof file, no seed retries — including the two quorum-intersection cells `form_prepqc × prepqc_unique` and `form_commitqc × commitqc_unique` that were budgeted as manual cells: at a 15-conjunct clump cvc5 finds the honest-common-member instantiation itself, so the family has **no manual cells**. `#veil_status Mvba` pinned (`224/224 real`: 15 properties plus the per-action `doesNotThrow` cell, × 13 actions and the initializer), axioms the standard trio; two `sat trace` witnesses (a decision in view 1; a Byzantine leader equivocating, two correct validators split, no certificate formed). `scripts/revalidate.sh` stages the family like its siblings. Not yet in `Cadence.lean` or the module-status table above — those rows come with the full model (step 3) and the provider `Mvba ⊨ MVBASafety` (step 5). |
| — | exit 0 | 0 | 725 | **The full MVBA model** (2026-09-08, same branch; `docs/MvbaPlan.md` §8 step 3): `Cadence/Mvba.lean` grew from the single-view spike to the supplement's algorithm with **views, timeouts, timeout certificates and the lock** — `view` a `TotalOrderWithMinimum`, `leader v l` functional by assumption, every message and local relation view-indexed and monotone, `SyncView` as its own action (with and without lock adoption), the leader's three view-entry cases and the two `Pre-Prepare` handlers as separate actions, five Byzantine signers. 24 actions, 3 safety + 25 invariants, the certificates `msg_prepqc`/`msg_commitqc`/`msg_tc` with the lock witness `tc_lock v w e` / `tc_nolock v` all materialised by assembly actions. **One correction to the plan** (§2.6, second correction): `lem:lock-persistence` is not an inductive invariant — the supplement proves it by induction on the view, which a one-step VC cannot do — so the clump carries the Paxos-made-EPR-shaped `prepqc_blocks_lower_commits` (a prepare certificate blocks every lower view's commit quorum from another value, via the ghost `blocked`), and lock persistence, cross-view certificate agreement (`commitqc_agree`) and `thm:agreement` follow by instantiation. Cold family build: 25 proof files, every cell solved by the solver, 0 ❌ / 0 💥 / 0 ⏱; the two argument-carrying cells solved slowly — `form_prepqc × prepqc_blocks_lower_commits` 43 s (71 % of budget) and `form_commitqc × commitqc_agree` 25 s — and are **written out as the family's two manual cells** so a 4-core runner does not time out on them (each elaborates in ~0.3 s cold; the supplement's one-view-transition argument and its agreement proof, respectively). `#veil_status Mvba` pinned at `725/725 real` (28 properties plus the per-action `doesNotThrow` cell, × 24 actions and the initializer), axioms the standard trio; three `sat trace` witnesses (a decision in view 1; a silent Byzantine leader in view 1, a lock-free timeout certificate and a decision under a correct leader in view 2; a held lock forcing view 2's leader to re-propose view 1's value over its own input). Still to come: `Cadence.lean` rows and the module-status table (with the provider, step 5), the `NoLock` mutation pin (step 4). |

| — | exit 0 | 0 | 1 505 | **The MVBA provider and the lock-check mutation test** (2026-09-08, same branch; `docs/MvbaPlan.md` §8 steps 4 and 5): `Cadence/Mvba/Compose.lean` — `Mvba.mvbaSafety : MVBASafety node value (Mvba.State …) (fun i => nset.is_byz i = true)` with **every field discharged**: the three safety properties through the named `reachable_*` projections of `Mvba/Certify.lean`, `decided_mono`/`init_decided` from all 24 actions' transition bodies by the step-facts technique (`mvba_tr`/`mvba_field_simp`, one tactic line each). `Mvba.MvbaResidual` is exactly the five timed fields §5 predicted — `clock`, `Admissible`, `admissible_exists`, `ℓ`, `termination` — **the first residual with no safety-shaped field**: `mvba_of_residual` proves the upper class's inputs (`propose`/`abandon` are actions), observables (`input`, `abandoned`, `Sent` by cases on a `Mvba.Msg` inductive over the five signed message kinds), effects, frames, initial conditions and **Quiescence** (`sent_new_tr`: a correct party's new message row comes from an honest send, each of which requires the input and `¬ abandoned`; one tactic over 5 message kinds × 24 actions). One model edit made that a one-step fact: `leader_repropose` was the only honest send without the participation guard `∃ E, input l E` (redundant at reachable states) and now has it — that action's 29 cells re-solved cold, everything else replayed, `#veil_status Mvba` unchanged at 725/725. `Cadence/Mvba/NoLock.lean` — the **mutation test** (§4 item 3): the faithful mutant (only the lock check weakened) is not exhaustively checkable at `n = 4`, two values, two views — its violation needs 28 transitions and the interpreted checker had not finished depth 6 after 30 minutes; a first reduction (bulk `propose`/availability/Byzantine steps, `abandon` and `byz_timeout_qc` dropped) holds 26 870 states at depth 8 and did not finish in 35 minutes; the checker's `compiled` mode returns without waiting outside an editor and pins nothing. The pin sits on a **second-level restriction** that also fixes the scheduler and the adversary's plan through the theory (`participant`, `byz_plan`) — every run of it is a run of the mutant, so the violation is a fortiori the mutant's — and finds `agreement` violated in about 1½ minutes of search: a 28-step trace with commit certificates on both values and two correct validators deciding differently, `#guard_msgs`-pinned verbatim (theory block and every state; `sequential := true`). `Cadence.lean` imports the leg and pins the six new declarations (21 axiom pins at the root now); docs per §9; the `Interfaces.lean` header row and obligation table; the proof-file counts (39 + 10 + 25). Validated in the branch's worktree, which had only the Mvba family built: staged re-validation with the shared warm cache `ALL STAGES GREEN` in 8 min 55 s at `BATCH=6` — 1 505 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 22 276 ♻, peak resident 12.9 GB — all three `#veil_status` pins, every axiom pin and both refutation pins holding; the only warnings the two known `simpa` suggestions. Chorus untouched (its family replayed warm); step 6, the consumption, is next. |
| — | exit 0 | 0 | 1 418 | **The Veil L-items — the composition is emitted now** (2026-09-09, branch `worktree-veil-integration-a`; Part A of the fork-integration plan): Veil re-pinned `6003fc7f` → `8a2f00f7` on `port/integration`, the *only* manifest change (Loom and the rest of the tree unmoved), taking up the seven capabilities the fork landed on 2026-09-08. **No model file changed and no VC statement moved** — this is a change to how the composition is *written*, not to what is proven, and all three `#veil_status` pins and every axiom pin hold unaltered. `#gen_theorems` now emits each action's preservation lemma, so `Cadence/Composition.lean`'s two hand-assembled reachability inductions and its `cvc%`/`ovc%` explicit-instance macros — which had to mirror the generated transition system's instantiation term-for-term and pass each action's deduplicated `Decidable` side conditions positionally — became **one `#gen_composition` per module**: 24 + 20 named `reachable_<property>` projections in 9 ms and 4 ms, from 7 + 8 preservation lemmas emitted in ~330 ms and ~360 ms. The emitter *extracts* that instantiation from the module's own `relationalTransitionSystem` rather than reconstructing it, which is why the two inductions collapse to a command each; the file went from 1 105 to 647 lines. **Every positional `hinv.2.2.….1` chain in the development is gone**: `positional_log_safety`, `orchestratorSafety`, `orchestrator_of_residual` and `monotonicity_tr` (which now takes the single `open_local_order` conjunct) project by name, so a renamed or reordered property is an elaboration error rather than a silently wrong conjunct — the audit point of L14. Veil's `trSimp` simp set (exactly the actions' `derived_eq` theorems and `tr` definitions) replaced the three per-action lemma lists in `conductor_tr`/`chorus_tr`/`mvba_tr`, and the abstract state's `Inhabited` instance is derived rather than hand-written in `Chorus/Compose.lean`: −458, −47 and −25 lines across the three composition files, and **adding an action to a model now touches none of them**. Three CLAUDE.md hard rules retired — the `Decidable` side-condition counts; `actSimp` defeating the `derived_eq` rewrite together with "adding an action means extending the macro"; and "never name an action parameter `st'`", verified here and not only in the fork (a scratch module with `action mark (st' : node)` sweeps clean and its `sat trace` returns `mark(st'=0)`) — and one rewritten: a non-first-order field in an instantiated class is now an **error naming class and field before any solver starts**, with `attribute [veil_smt_ignore] C.field` as the escape hatch (unused here, since the two-level split is what keeps the instantiated fragment first-order). `spikes/03` was re-run and re-documented as the reproduction of that check: `exit 1` with one named error, where it used to be `💥` on every VC. Also measured, and filed as an observation in the fork's roadmap: **the two small models' in-file sweeps neither hit nor store the proof cache** — with the shared cache and with an emptied one they take the same 27 s / 38 s and write nothing — so they re-solve on every build and need no cold-solve discipline; the cross-file path is unaffected (`Chorus/Proofs/Vote.lean` re-solved cold as the canary: 98 ✅ / 0 ♻ in 52 s, its manual cell 6.2 s). Validated: staged re-validation `ALL STAGES GREEN` in 6 min 49 s at `BATCH=6` — 1 418 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 22 360 ♻, peak resident 7.9 GB — all three monitor suites `ALL PASS` with the `#gen_monitor` variant agreeing with the hand-written oracle on every fixture, every `#guard_msgs` axiom pin holding and `#veil_status` at 3861/3861, 220/220 and 725/725. |
| — | exit 0 | 0 | 1 699 | **Step lemmas and step properties — the two-state proofs move into the tool** (2026-09-10, branch `worktree-veil-integration-c`; Part C of the fork-integration plan, on the template the fork session validated): Veil re-pinned `8a2f00f7` → `1ab4be74` (a fast-forward: **M13** generated step lemmas, **M14** `step_property`, **L17** the trace path with `extends` parents). **No model semantics changed** — no invariant added, no VC statement rewritten — but the *sources* of the contracts' step-level fields did, and with them ~150 lines of hand-written case analysis. M13 emits, at `#gen_spec` and kernel-checked, everything an action's update records already determine: `<Module>.<f>.mono` over every label, `<Module>.<action>.frame_<f>`, `<Module>.<f>.init`. Nine instance fields that were 38-case (Chorus) or 7-case (Conductor) `cases l` scripts — `opened_mono_tr`, `completed_mono_tr`, `completed_frame_internal`, `init_not_opened`, `init_not_completed`, `committedAll_mono`, `committedPos_mono`, `recorded_mono`, `init_not_committed` — are now one-line applications, and the `set_option maxHeartbeats 2000000/4000000` lines they needed are gone with them. M14 takes the two facts the update records *cannot* give, because they need the action guards or the invariants at the pre-state, and makes them **SMT-checked cells in the model**: `step_property [monotonicity]` in `Conductor.lean` (the paper's Monotonicity, which needs `[open_local_order]` at the pre-state together with `open_slot`'s guard) and `step_property [committed_pos_frozen]` in `Chorus.lean` (a committed validator's positive entries do not change, from `commit_assign_pos`'s `¬ local_committed i`). The 30-line `monotonicity_tr` and the 38-case `committedPos_frozen` are deleted in favour of `Conductor.monotonicity_step` and `Chorus.reachable_committed_pos_frozen_step`. Step properties are registry cells like any other, so the counts move: the Conductor sweeps **189** cells (was 168; 3 properties × 7 actions) and `#veil_status Chorus` goes to **3899/3899** (was 3861; 38 new cells at ≈ 12 s on first solve). **The one contract change**: `OrchestratorSafety.opened_mono`/`completed_mono` and `SlotConsensusSafety.finalized_mono`/`on_time_mono` now take `reachable st` before `trans`, because a step cell's hypotheses are the invariants at the pre-state and an all-states field cannot consume them. It costs the consumers nothing — they already carry the sub-protocols' reachability as invariants, and the glue re-solves at the same **175** cells — and the contracts' own convention had always promised properties at reachable states. Only two step-level facts stay hand-written, both about a single action rather than all of them: `complete_effect_tr` and `complete_frame_other`. L17 needed nothing on this side; what it unblocks is the shared transition-system skeleton deferred by the interface redesign. Validated: staged re-validation `ALL STAGES GREEN` in 13 min 30 s at `BATCH=4` — 1 699 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 22 550 ♻, peak resident 10.9 GB — all three monitor suites `ALL PASS`, every `#guard_msgs` axiom pin holding and `#veil_status` at 3899/3899, 220/220 and 725/725. **One follow-up, and a lesson about where budgets are measured**: this passed locally and then failed on CI at `Cadence.Chorus.Proofs.FbSignNeg`, because `fb_sign_neg × inclusion_no_honest_fb_neg` — 6.2–17.0 s on the workstation — takes 52.8 s on a 4-core CI runner and had been sitting at **88% of the 60 s budget** for some time; the new `committed_pos_frozen` cell, which costs 30–42 s on *every* action, pushed it to 62.5 s (with its TR retry at 63.3 s) and over the line. Both attempts *completed*, so this was slowness, not divergence, and the remedy was the budget rather than a manual proof: `veil_proof_options` now sets `veil.smt.timeout 180`. The general lesson is recorded in `CLAUDE.md` § Build — **CI is the budget measurement that counts**, because it is the only place the family runs cold, and a local green run replays the old cells from the cache on faster hardware. A census of the same CI run found 33 cells above the 5 s reporting threshold, the next-closest at 95%. |
| — | exit 0 | 0 | 1 530 | **The interface redesign — one skeleton, and the residual structures are gone** (2026-09-10, branch `worktree-veil-integration-b`, stacked on the step-property work above; Part B of the fork-integration plan, and what L9 in the 2026-09-09 bump was for): the four `…Safety` fragments now extend a single **`TransitionSystemSafety`** — `init`, the internal `step`, their union `trans`, an over-approximated `reachable` and the three closure facts, stated once instead of four times — and the temporal half of each contract became a class **over the safety instance**, `XTemporal … [S : XSafety …]`, every field stated in terms of `S.init`/`S.trans`/`S.reachable` and `S`'s observables, with `class X extends XSafety, XTemporal` joining the two. `spikes/06_dependent_temporal_parent.lean` established that Lean takes the dependent parent and, decisively, that `X.toXTemporal`'s instance argument elaborates to `X.toXSafety self`, so the two levels cannot be about different transition systems. With that, **the three residual structures were deleted** — `Conductor.OrchestratorResidual`, `Chorus.SlotConsensusResidual`, `Mvba.MvbaResidual` — and with them every restatement of an unproven obligation at an implementation's own types. What each implementation still owes is now *the absence of an `XTemporal` instance at the fragment it proved*: `orchestrator_of_temporal`, `slotConsensus_of_temporal` and `mvba_of_temporal` are each `{ theSafetyInstance, h with }`, each paired with a `…_toSafety` `rfl` lemma pinning that the join hands back exactly the proven fragment. **Field placement** followed "first-order and proven by every implementation ⇒ the fragment": Integrity's timing half into `OrchestratorSafety` (which therefore carries `time`, `clock` and `start_time`, and the glue a phantom `time` sort it never mentions again), Hiding's protocol half with `deadline_passed`/`payload_recoverable` into `SlotConsensusSafety`, and the MVBA's two inputs, their observables, effects, frames and one-step Quiescence into `MVBASafety` — leaving `MVBATemporal` at four fields. Quiescence is one-step in all four contracts now, so they read alike. **`SlotConsensusSafety` also lost its slot index**, which is what let the skeleton be unindexed and serve all four: a state carries its instance's slot as the observable `tag`, preserved by `tag_frame`, so `Chorus.slotConsensusSafety` runs on `slot × Chorus.State` pairs and the glue carries one assumption `[sc_tag_init]` and one invariant `[sc_tagged]` (`spikes/07_sc_state_tag_ok.lean`; `08_sc_tag_frame_removed.lean` is its negative control — delete `tag_frame` and exactly one cell fails, `sc_tagged` under `sc_step`). **The skeleton is here because of a fork bug this work found.** In its first cut the four fragments could not extend a parent: the sweeps passed (the Conductor's 168/168 at the time) but both small models' `sat trace` witnesses failed, the trace pipeline mis-destructuring an instantiated class with an `extends` parent. It was filed as L17 with a controlled reproduction pair — parented fails, identical flat passes, sweep green in both — fixed in the fork on 2026-09-10, and the skeleton went in on top of that fix; the branch's own `sat trace` blocks are the regression test. **Measured**: widening the consumers' constraints cost nothing — the glue re-solves 182 cells + 2 traces in 35 s, the 7 added cells being the new `[sc_tagged]` invariant, with an extra uninterpreted sort, two uninterpreted functions and four more class axioms per verification condition — so no field was withheld with `veil_smt_ignore` and the attribute stays documented as the escape hatch. `Cadence.system_positional_log_safety` carries exactly the hypotheses it carried before the redesign: the two theories, `hbyz`, and `ACSSafety` as the one assumed contract — no residual, nothing temporal. Validated: staged re-validation `ALL STAGES GREEN` in 11 min 43 s at `BATCH=6` — 1 530 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 22 550 ♻, peak resident 10.1 GB — all three monitor suites `ALL PASS`, every `#guard_msgs` axiom pin holding and `#veil_status` at 3899/3899, 220/220 and 725/725. |
| — | exit 0 | 0 | 6 726 | **Chorus consumes the MVBA as a class constraint** (2026-09-10, branch `worktree-mvba-consumption`; `docs/MvbaPlan.md` §6 and §8 step 6 — the step that pays the Chorus cold re-solve). The three inlined oracle actions `mvba_decide_pos`/`mvba_decide_neg`/`mvba_terminate`, whose `require`s transcribed the MVBA contract's fields and were audited by reading, are gone. In their place `Chorus.lean` declares three abstract sorts `mstate`/`mvalue`/`mmsg`, `instantiate mvba : MVBASafety node mvalue mmsg mstate (fun i => nset.is_byz i = true)` after its `nset`, an abstract state `individual mvba_st` seeded from the immutable `mvba_init_state` under `assumption [mvba_init]` and carried by `invariant [mvba_reachable]`, two immutable projections `mval_pos`/`mval_neg` of the opaque value (the entry vector, `MvbaPlan.md` §1.2) with the two assumptions the agreement argument needs (functional, exclusive), the oracle step `mvba_step` (`mvba.step`), the driven input `mvba_propose` (`mvba.propose`, under the proposer's own trigger — `fbcert` from the fallback arm on, or its own complete fast meta-block at the MVBA arm — and with `Valid B_i` as guards; `abandon` stays undriven), two **per-entry decision handlers** `on_mvba_decide_pos i j m v` / `on_mvba_decide_neg i j v` that transport a correct validator's `mvba.decided mvba_st i v` into the existing records, and `mvba_terminate i v` guarded by a correct validator's full recorded decision. The records' agreement — `mvba_decided_pos_unique`, `mvba_decided_pos_neg_excl`, formerly *enforced* by the oracle's guards — is now **proven from `mvba.agreement`** at `mvba_reachable` through two tie invariants (`mvba_decided_pos_tied`, `mvba_decided_neg_tied`: every record is the projection of some correct validator's decision; `decided_mono` keeps them inductive under the oracle step). **One stated bridge** remains, by design and documented at the handlers, in `ChorusDesign.md` §4 and `CompositionContracts.md` §8 item 1: each handler `require`s the decided entry's certificate against Chorus's network relations (`vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)`, resp. the negative form) — the interpretation of the class's `Valid`, a parameter fixed before the module's state exists, in a model whose signatures are network relations; the same disjunction is the caller's obligation in `mvba_propose`, and it is stated nowhere else. Spikes `09_mvba_consumer_ok.lean` (green) and `10_mvba_consumer_no_tie.lean` (exactly three `❌`, at the handlers) are the shape experiment and its negative control. Chorus went from 38 to **40 actions** and from 98 to **101 properties**; `#veil_status Chorus` is re-pinned at **4222/4222** (every cell real; the cold re-solve needed **no new manual cell** — the four cells of the retired `MvbaDecidePos`/`MvbaDecideNeg` files moved to `OnMvbaDecidePos`/`OnMvbaDecideNeg` with only their `intro` pattern changed, the other seven manual cells re-solved unchanged, and the manual count stays at 11). `Chorus/Compose.lean` gains the three sorts and the `[mvba : MVBASafety …]` binder and nothing else (no action list anywhere: `#gen_composition`, `trSimp`, the generated step lemmas); `System.lean` fills the constraint with **`Mvba.mvbaSafety thM`** — `mvalue := node → Option merkle_root`, `mstate` the `Mvba` model's abstract state, `mmsg := Mvba.Msg` — so `system_positional_log_safety` gains `thM` and the `view` sort and **no MVBA contract hypothesis remains anywhere in the composed system**; no fault-model transport is needed between Chorus and the MVBA (both are stated against `nset.is_byz`), and `chorusTheory_assumptions` shows the two projection assumptions are theorems at that instantiation, leaving `[mvba_init]` as the one genuine hypothesis among the three. Two consequences worth knowing: `Chorus.lean` now imports `Interfaces.lean`, so a contract edit rebuilds the Chorus family (`Interfaces.lean`, "Why this file"); and the **monitor** instantiates the constraint with a *silent* stub (`Monitor/MvbaStub.lean`: state and message `Unit`, a finite entry-vector record, a class instance that never decides), so its MVBA leg is a coverage gap (`Monitor.md` §8) and the published alphabet changed — `mvba_step`, `mvba_propose`, `on_mvba_decide_*`, a binary `mvba_terminate`. The CI measurement (`CLAUDE.md` § Build: CI is where the budget is sized) then settled the `veil_smt_ignore` question: with every axiom of the instantiated class a hypothesis of every cell, `vote × committed_pos_frozen` went from 61 s to 120 s cold on the 4-core runner (66% of the 180 s budget), the `Vote` file from 143 s to 334 s and the other step-property cells up by a third, nothing timing out — and a scratch A/B of that cell with the twelve unused `MVBASafety` axioms withheld showed **no effect** (9.8–10.4 s either way), so nothing is withheld and the numbers live in `Dependencies.md` §7. The first CI run of the branch failed for an unrelated reason that became a fix: the re-verification copied the sources *over* the image's checkout, so the two retired proof files survived there and `revalidate.sh`'s glob built them; `container.sh` now mirrors the sources (the workspace tree is removed first, `.lake` and `.git` excepted). The second run was green end to end in 1 h 47 min. Validated: staged re-validation at `BATCH=3` with the Chorus family **cold** (every VC statement changed: three new invariants, three new sorts and the instantiated class's axioms in every cell) — the 41 Chorus proof stages green in 28 min 13 s (16:34:31–17:02:44), 6 726 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 4 070 ♻ over the run, peak resident 25.3 GB in the proof stages (the three concurrent `Certify` processes then read as 57.7 GB, which triple-counts the family's memory-mapped oleans); the run stopped, as it must, at the stale `#veil_status Chorus` pin (3899 → **4222**), and after re-pinning the remaining stages — the three certificates, the composition files, `System`, the audit root with the monitor — were built and green, all three monitor suites `ALL PASS`, every `#guard_msgs` axiom pin holding and `#veil_status` at 4222/4222, 220/220 and 725/725. |
| — | exit 0 | 0 | 26 374 | **The cheap rung — most cells stop calling the solver** (2026-09-10, branch `worktree-veil-integration-cheap-discharger`): Veil re-pinned `1ab4be74` → `1eb6b70e` on `port/integration`, and the whole diff between those two revisions is the one commit — `veil.vc.cheapRung`, a cheap non-SMT **first rung inside each invariant-preservation cell's existing discharger**: `by first | veil_solve_frame <invariant> | veil_solve_wp`. Most verification conditions in this development are frame obligations — the action writes nothing the invariant reads — and after the local-WP bridge such a goal is already the invariant at the pre-state behind the action's guards, so projecting the right conjunct out of the clump closes it. The rung is **tried, never predicted**: it closes the goal or fails, a miss falls through to cvc5, both paths end in a kernel-checked term, and **no VC statement moves** — so this changes how cells are proven, not what is proven, and every `#veil_status` pin and every axiom pin is unaltered (4222/4222, 725/725, 220/220 at the three standard axioms). On this project the hit rate is what the fork measured it to be: **80–91% of a Chorus proof file's 101 cells close without a solver** (`commit_assign_pos` 90, `record_chunk` 81, `fb_sign_neg` 92; the `foldBoolAtoms false` outlier `vote` 64 of 100), and the per-file cold A/B against the rung turned off is in [`Dependencies.md`](./Dependencies.md) § 2. **On this side the migration was a deletion**: `unveil_local` and the by-name clump projection `inv_have`/`inv%` — written here on 2026-08-24 and, being the two halves of `veil_solve_frame`, exactly what the rung needed — are Veil's now (`unveil_local`, `veil_inv_have`), so the `Veil.InvProjection` namespace left `Cadence/ProofPrelude.lean` entirely and that file is down to this project's two option blocks; the ten proof files with manual cells dropped an `open` and renamed one tactic, and nothing else in the development changed. **One structural consequence worth knowing before reading a build log**: a cell the rung closes never reaches the proof cache, so the cache now holds only the solver-touched cells (2 990 entries against the ~22 000 replays a warm build used to report) and the rest re-run the rung — a warm re-validation's output is therefore mostly ✅ where it used to be mostly ♻, and the cold path is where the saving lands. Validated: staged re-validation cold in every cell, `ALL STAGES GREEN` in **15 min 25 s** at `BATCH=3` — 26 374 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 345 ♻, peak resident 10.8 GB — and green again warm at `BATCH=6` (23 433 ✅ / 3 327 ♻, 12 min 46 s with every project olean deleted, the three model rebuilds and the root audit module 486 s of it), with only the two expected `Composition.lean` `simpa` suggestions in either run. |
| — | exit 0 | 0 | 28 774 | **The fork re-ported onto upstream Veil `517f2bad`** (2026-09-26, branch `worktree-veil-517f-repin`; session C of the upstream-sync plan `../VEIL-UPSTREAM-517F-PLAN.md`): Veil re-pinned `5da189d5` → `73fa6fd4` on `port/integration`, the fork's feature branches re-cut onto an upstream that adopted Lean's module system and **dropped Mathlib**. Three dependency changes followed: the `larskuhtz/loom` lakefile fork is gone (upstream's standalone Loom has no case-study library, and the fork only mattered to precompilation, which this project measured as not paying); **Mathlib is now a direct dependency** at `v4.32.0`, whose batteries/aesop/Qq/ProofWidgets pins are the ones Veil requires, so the Mathlib cache still applies; and the fork's three `ByzNodeSet` counting fields are gone, so the transitional `veil_smt_ignore` block in `Cadence/Tooling.lean` and the matching fields of `byzNodeSetFinGen` were deleted (the facts live in `Cadence.ByzNodeSetCounting` since the B0 move). Seven files had used Mathlib only through `import Veil` and now import the modules they use (`ByzQuorum`, `Primitives`, `Windows`, `Fairness`, `Composition`, `FallbackReceipt/Totality`, and `ProofPrelude`, which switches off Mathlib's `linter.unusedTactic` only where an import registers it). Two `simpa using` steps in `Composition.lean` became `List.getElem_mem` applications, which retired the two expected `simpa` suggestions — **the build now prints no warnings**. **One regression in the fork, found here and fixed there**: in a module with a zero-arity `Bool` component (Chorus's `mvba_complete`), every `step_property` cell crashed cvc5 ("Expected SMT-LIBv2 sort constructor"), because the transition route's field concretization left `CanonicalField [] Bool` as the implicit type of the component's frame equation, which lean-smt's Bool embedding matches syntactically — squashed into `port/concretize-field-arrows`, with the regression test `VeilTest/StepPropertyBoolIndividual.lean` on `port/step-properties`. **No VC statement moved** and every pin is unaltered: `#veil_status` 4222/4222, 220/220, 1325/1325 at the three standard axioms, every axiom pin at the root, both refutation pins, all three monitor suites `ALL PASS` (hand-written == generated), and the Verso site builds. Validated: staged re-validation cold in every cell (project oleans and proof cache deleted), `ALL STAGES GREEN` in **19 min 58 s** at `BATCH=3` — 28 774 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 349 ♻, no seed retries, peak resident 13.0 GB, 792 cache entries stored — and warm at `BATCH=6` in **12 min 58 s** (peak 15.3 GB; the three model rebuilds and the root audit module 477 s of it). The cold figure is not comparable with the 15 min 25 s above, whose workload predates the MVBA growth (`#veil_status Mvba` 725 then, 1 325 now); against B0's cold run of the same workload on the old pin it is within noise — model files 44 / 172 / 61 / 75 s against 55 / 177 / 65 / 77 s, 1 045 s against ~1 074 s up to the certificates, slowest cell `vote × committed_pos_frozen` 51.5 s against 52 s of its 180 s budget. |
| — | exit 0 | 0 | 5 967 | **Chorus models the participation interface** (2026-09-29, branch `worktree-chorus-participation`; [Bounds.md](Bounds.md) §6.4.6 S1, option A with C1/C2): per-validator `participating`/`abandoned` state, the input actions `participate` and `abandon` (which forwards to the MVBA's `abandon()`), every sending rule gated on active participation, and a sender parameter for `broadcast_commitqc_*` and `redisseminate_chunk`. **No invariant added**; 40 → 42 actions, `#veil_status Chorus` 4222 → **4428** (101 + 42 × 102 + 43, predicted before the build). The contract's timed fields gained C1 (no abandonment before finalizing) and C2 (no start before `D − Δ`, with the datum `deadline`) as antecedents; `Chorus.slotConsensusSafety`'s `step` now excludes the inputs, so the composed system's Chorus is inert until the glue drives them (glue safety unaffected). `Chorus.termination` was re-proven at the trio against two new caller premises (`AllParticipate`, `NoAbandonBeforeFinalizing`), split on an early finalization; `MvbaAdmissible` kept its shape. The (A-mvba) prose was retired from the Lean files and MvbaPlan §11.5 stage 1 rode along. Validated: one `revalidate.sh` run at JOBS=8 with the Chorus family **cold** (every VC statement changed), 659 s, 5 967 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 451 ♻, peak resident 25.8 GB, slowest cell `vote × committed_pos_frozen` 94.9 s of 180 s under JOBS=8 contention; the run stopped only at the plain-Lean files still being edited, and the following full build was green with no warnings, every axiom pin at the trio, and all three monitor suites `ALL PASS`. |
| — | exit 0 | 0 | 5 413 | **The MVBA timed premise follows the supplement's network** (2026-09-29, branch `worktree-mvba-upgrade-5b`; `docs/MvbaPlan.md` §11.5 stages 2–5, the review of §11 acted on): the model's pin moved from paper-repository `026dc8b` to `eb1bb51` (comments and citations only; `#veil_status Mvba` and the `NoLock.lean` pin unmoved). `Mvba.BoundedJustice` was refined from one clause — every network step within `Δ` of `max(clk, GST)` — to the six clauses of the supplement's network (delivery within `Δ` of messages sent at or after GST by correct validators and retained; retransmission of timeouts, `ViewTC_i` and a decided `CommitQC` within `Δ + ρ`; `decide` a network step), with `Schedule.ρ`. The bound was re-proven: the good view at or above `M + 2` with a retention lemma (`retained_before`), the first burnt view at retransmission cost, and a new `Schedule.ℓ`; `Mvba.mvbaTemporal`, `Mvba.aViewSync_of_sync` and both `…_premises_satisfiable` theorems stand, and the untimed premise and every Chorus file are untouched. One item left open, (N4): prepare certificates do not travel (`docs/Bounds.md` §6.2.4); it is closed in R3 (model change: `adopt_prepqc` from the prepares, Mvba re-solve). Plain-Lean work plus a warm re-validation (the ✅ count is the `JOBS=8` log's). |
| — | exit 0 | 0 | 5 812 | **Fairness over state-changing steps, and (N4) closed** (2026-09-29, branch `worktree-r3-fairness`, session R3; [Bounds.md](Bounds.md) §6.2.4). *(The premise form (1) is superseded by R6, below: since S1b every fair action fires once, and the premises are over plain enabledness again.)* Two premise corrections, one model change. (1) [Fairness.lean](../Cadence/Fairness.lean)'s `WeaklyFair`, `WeaklyFairFamily` and `StronglyFair` are stated over `EnabledMove` (moved there from `Timed.lean`, so the timed and untimed sides share one notion): a label is owed a firing only while it can take a step that changes the state, TLA+'s `WF_v`. Under plain enabledness the idempotent quorum-indexed assembly labels stayed enabled as stutters and each had to fire forever, so the premise sets of `Mvba.termination` and `Chorus.termination` were unsatisfiable at any quorum sort with infinitely many supermajorities; both `FJustice`s (Chorus's proposal family included) are restated over it, and every link pays the side condition once (`EnabledMove.of_enabled_of_effect`, the new `eventually_of_weaklyFair`). (2) (N4): `adopt_prepqc i v e q` forms the validator's own prepare certificate from a supermajority `q` of `Prepare`s it received, the supplement's `TryFormPrepQC` at `eb1bb51`, instead of adopting a certificate formed anywhere, and records it (`msg_prepqc`); in the timed premise it is a network hop with a first-delivery clause, the good-view chain loses a milestone and `Lcert` tightens to `3Δ + max(Δ, Δ_sync) + 2δ` (unchanged at `δ = 0`, so `ℓ = 24` at the witness stands). One new manual cell, `adopt_prepqc × prepqc_blocks_lower_commits` (the `form_prepqc` twin's argument); `#veil_status Mvba` unchanged at 1325; `Mvba/NoLock.lean` mirrors the change, still finds its agreement violation, and its pinned witness is 26 transitions (was 28). The MVBA witness idles on one stutter step, and its untimed fairness is now `quiet` at the idle state rather than a finite-sort lemma. Also: `vote × committed_pos_frozen` (73 % of budget on #46's CI) is a manual cell, the fork's step-cell route with the clump cleared (2.5 s cold); `scripts/scratch.sh` now picks a build setup that loads cvc5. Validated: one `scripts/revalidate.sh` run with the Mvba family and `Chorus/Proofs/Vote.lean` cold against an empty cache (every Mvba proof file 0 hits), 3 min 30 s, peak 17.9 GB, 5 812 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 614 ♻ (the ♻ are re-printed logs of the untouched Chorus files), lake exit 0, no warnings; pins 4428/4428, 220/220, 1325/1325 and every axiom pin, `Chorus.termination`, `Mvba.termination`, `Mvba.bounded_termination`, `Mvba.mvbaTemporal` and both `…_premises_satisfiable` included, at the standard trio. |
| — | exit 0 | 0 | 6 266 | **Chorus S1b: every fair action fires once** (2026-09-30, branch `worktree-r5-chorus-s1b`, session R5; [Bounds.md](Bounds.md) §6.4.7). The acceptance lemma `Chorus.justice_enabledMove` (every enabled fair label can change the state, at every state) found more self-re-enabling actions than the plan listed, and each got a "not already" guard on a local record of its own: six new records (`local_chunk_sent`, `local_commit_entry`, `local_fb_entry`, `local_commitqc_sent`, `local_mvba_recorded`, `local_fbcommit_voted`), and `aggregate_fastqc_*` / `commit_assign_*` guarded on the absence of their own effect. The Byzantine branches of `broadcast_commitqc_*` and `redisseminate_chunk` became the unfair `byz_broadcast_commitqc_*` and `byz_redisseminate_chunk`. No invariant; `#veil_status Chorus` 4428 → 4737 (45 actions), manual cells 12 → 15. `Chorus.termination` re-proven at the trio with `TerminationClaim` unchanged; the records' backing is plain Lean (`record_backed`). One cold family re-solve, `revalidate.sh` at JOBS=8: 452 s, 0 ❌ / 0 💥 / 0 ⏱ / 459 ♻, every Chorus proof file 0 cache hits; the run stopped only at the two monitors (`synthInstance.maxSize`, raised), after which the root and all three monitor suites passed. The premises keep their move form; the flip to plain enabledness is R6. |
| — | exit 0 | 0 | 6 417 | **Mvba S1b: fired-once flags** (2026-09-30, branch `worktree-r4-mvba-s1b`, session R4; [Bounds.md](Bounds.md) §6.4.7). The supplement's two remaining "not already" rules are one correct validator's step each: `form_own_commitqc i v e q` (`TryFormCommitQC` with `Decide`, guarded on `DecidedQC_i = ⊥`, which in this model is "has not decided") and `form_own_tc_lock` / `form_own_tc_nolock` (`HandleTimeout`, "upon first collecting `2f+1` valid timeout messages", with the new local record `tc_formed i v` and the invariant `tc_formed_backed`). The four anonymous assemblies stay as the adversary's capability in the unfair class `AssemblyLabel` and left the hop table. New lemma `Mvba.enabledMove_of_enabled`: at every state an enabled `JusticeLabel` is move-enabled (no label failed it). `#veil_status Mvba` 1325 → 1507 (50 + 28 × 51 + 29); manual cells 3 → 5. The chains, the timed stack and both witness theorems were re-proven with the premises unchanged in form (Fairness.lean and Timed.lean untouched); `Delivers` lost its receiver parameter; `good_view_decides` now concludes a decision by `E₀ + Lcert`; `Lcert`, `Schedule.ℓ` and `ℓ = 24` at the witness are unchanged; no Chorus file changed. `Mvba/NoLock.lean` mirrors the steps and drops the anonymous `form_prepqc`/`form_tc_*` (restriction); agreement is still violated, witness re-pinned at 25 transitions (was 26), search 27 min single-core (was ~3.5 min). Validated: one cold Mvba-family re-solve against an empty cache (every proof file 0 hits), 2 min 29 s, 1 505 ✅ / 0 ❌ / 0 💥 / 0 ⏱, lake exit 0; then a warm full re-validation (every project olean deleted, cache kept, `JOBS=8`), 29 min 55 s (NoLock 1 791 s of it), peak 25.1 GB, 6 417 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 184 ♻, exit 0, no warnings; pins 4428/4428, 220/220, 1507/1507 and every axiom pin at the standard trio. |
| — | exit 0 | 0 | 5 888 | **Fairness over plain enabledness — the flip** (2026-09-30, branch `worktree-r6-fairness-flip`, session R6; [Bounds.md](Bounds.md) §6.4.7, "R6 done"). With S1b's fired-once guards in both models, the fairness notions of [Fairness.lean](../Cadence/Fairness.lean) (`WeaklyFair`, `WeaklyFairFamily`, `StronglyFair`, the projection's `WeaklyFairIn`), [Timed.lean](../Cadence/Timed.lean)'s `BoundedFair` and [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean)'s `BoundedFairWhile` are over `Enabled` again: an action enabled from some point on eventually fires. Both `FJustice`s and `Mvba.BoundedJustice` read that way, with no qualifier; the definitions' text is unchanged. Per model the bridge to R3's state-changing form is a theorem, from the acceptance lemmas: `Mvba.fJustice_iff_move`, `Chorus.fJustice_iff_move`, `Mvba.boundedFair_iff_move`, `Mvba.boundedFairWhile_iff_move`, pinned at the trio here and in `Cadence.lean`. The proofs lost every `EnabledMove.of_enabled_of_effect` side condition (the lemma is gone); no end theorem's statement changed, and `Mvba.termination`, `Mvba.bounded_termination`, `Mvba.mvbaTemporal`, both MVBA witnesses and `Chorus.termination` are re-proven at the trio. Alongside, CI headroom: `Mvba/NoLock.lean`'s search fixes the environment's schedule and drops three honest steps its scenario does not take, keeping `sequential := true` and the pinned 25-step witness byte for byte — 1 433 s → 69 s on one core here (54 min on #51's CI runner); and the Conductor's in-file sweep turned out to be at 180 s already, so #51's 81% / 73% were 27% / 24% (CLAUDE.md corrected). No model under `Chorus.lean`/`Mvba.lean`, no proof file and no pin changed. Validated: every project olean deleted, cache kept, `scripts/revalidate.sh` (JOBS=8) `ALL GREEN` in 10 min 18 s, peak 16.2 GB — 5 888 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 036 ♻, no warnings; `#veil_status` 4737 / 1507 / 220, every axiom pin, `Mvba.Witness.ell` and the NoLock witness holding. |
| — | exit 0 | 0 | 5 888 | **Chorus S2: timed scaffolding, statements only** (2026-09-30, branch `worktree-r7-chorus-s2`, session R7; [Bounds.md](Bounds.md) §6.4.2, §6.4.5, §6.4.6 item 2). [Timed.lean](../Cadence/Timed.lean) gains (Δδ-justice), the buffered hop, as `BufferedFair` / `BufferedFairFamily` (message part due `Δ` after sending, the rule `δ` after its local gate), which is `BoundedFair` at `N = N'` with a trivial gate (`bufferedFair_iff_boundedFair`); `BoundedFairFamily`; and the timed projection `Component.Projection.timed` with `timed_back`, `timed_forward` and `boundedFair_iff`. The new [Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean) states the Chorus schedule (the MVBA's plus `D`), the hop table (`hop_isSome_iff`), the gates (the actor's participation and the phase only), (P-phase), the MVBA premise as `T.Admissible` of the timed projection for any MVBA contract `T`, the caller's conditions, and the two targets `TimedTerminationClaim` (`ℓ = 5Δ + T.ℓ + 8δ`, the paper's at `δ = 0`) and `TotalityClaim` (tolerance-parametric, `max(Δ, d) + 2δ`), as definitions. Two findings against the planned table, built into the statement: the paper owes delivery only between correct validators, so each `Δ`-row is owed only for messages from correct senders (F5, which applies to both untimed `FJustice` definitions, Chorus's and the MVBA's; open, closed in R8 before the witness and S3); and `cast_fb_commit`'s shared `mvba_complete` guard would have owed a vote before the voter's own decision (F6). The decision handlers stay `δ`-rows after (N3). The MVBA's `decisions` clause (C15) stays assumed inside `T.Admissible`, named: the certificate's delivery is Chorus's "Decision output and handoff" step, which the model does not have yet; R8 models it and derives the clause. No Veil file, no Interfaces.lean edit. Validated: `scripts/revalidate.sh` (JOBS mode) on R6's warm tree, `ALL GREEN`, lake exit 0, nothing re-solved (the Veil oleans were current); 5 888 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 036 ♻ from re-printed logs; no warnings; `#veil_status` 4737 / 1507 / 220 unchanged; every new declaration's axiom pin at or below the trio. |
| — | exit 0 | 0 | 5 888 | **The v1 refutation moves to a tag** (2026-09-30, branch `worktree-r9-drop-prefix`, session R9): `Cadence/FallbackReceipt/PreFix.lean`, the model checker's pinned counterexample to the receipt rules of `arXiv:2607.02275v1`, is deleted from the working tree and kept at the annotated tag `v1-receipt-refutation` (commit `8b13627`). The bug is long fixed in v2 and its repro carries no lasting insight, while keeping it cost a hard CLAUDE.md invariant, a pinned trace and some thirty-six cross-references. The living documents now tell the current story: [ChorusDesign.md](ChorusDesign.md) §7.2 explains why the v2 receipt rules are shaped as they are, and the README's paper section has one paragraph with the tag link. No model, invariant or proof changed; `#veil_status FallbackReceipt` stays 220/220. Rows above that name `PreFix.lean` describe the state they were written at. |
| — | exit 0 | 0 | 5 986 | **Premise fixes: correct-sender fairness (F5) and the decision handoff (C15)** (2026-09-30, branch `worktree-r8-premise-fixes`, session R8; [Bounds.md](Bounds.md) §6.4.2, "The decision handoff (C15): the design", and §6.4.6 item 2). Both untimed fairness premises are owed only for messages from correct senders, with the timed rows' own conditions (`Chorus.Owed`, now shared; `Mvba.Owed`, the sender part of `Delivers`); the re-proof found F7 (a correct fast voter's `FastBlock` spreads FastQCs) and F8 (the decoding fallback signer re-disseminates). The MVBA's decision handoff is modelled: `MVBASafety` gains `certifies`, `decided_certified`, `accept` (+ `accept_trans`, `accept_effect`, `accept_enabled`, the three liveness facts `veil_smt_ignore`d), `decide` becomes an input of the instance, and Chorus gains `accept_mvba_commitqc` with a fired-once record, so the MVBA's handoff clause (`Mvba.Relayed`, the former `decisions`; untimed (F-relay)) is derived (`Chorus.relayed_of_timedJustice`, `Chorus.fRelay_of_fJustice`). (A-viewsync)'s second clause names a correct decision. `Chorus.termination`'s late branch always takes the MVBA arm; the commit-route lemmas are gone. `#veil_status Chorus` 4737 → **4840** (101 + 46 × 102 + 47), Mvba 1507 and FallbackReceipt 220 unchanged. Validated: the Chorus family **cold** (0 cache hits in all 47 files) in 7 min 12 s at `LEAN_NUM_THREADS=8`, 4 825 ✅ / 0 ❌ / 0 💥 / 0 ⏱, peak 7.8 GB; then a warm re-validation (every project olean deleted, cache kept) in 10 min 12 s, 5 986 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 854 ♻, peak 17.0 GB, lake exit 0, no warnings; all three monitor suites `ALL PASS`. **Then a Veil re-pin** (`73fa6fd4` → `461c6832`, `port/registry-memory` and `port/info-trees` via `port/integration`): CI's 4-core build of the Chorus model ran out of memory in the 13 GB container (exit 137 after 1 069 s). A `LEAN_NUM_THREADS=2` stopgap failed with a registry heartbeat timeout and was reverted. The first fix, per-statement registry runs with hash-consed types, took 1–2 GB off locally but did not move the CI failure. A CI probe (run 36806058255) then showed master's model already filling the 13 GB cap (anon 10.7 GB), R8's 0.8 GB above it, both climbing steadily over the whole file. The cause was info-tree retention: Veil's declarations recorded the info trees of all their generated code, with the metavariable contexts behind them, and the frontend keeps every command's tree to the end of the file. They now keep one reference per identifier the user wrote (a variable with the minimal local context its hover needs), and `#gen_spec` keeps none. The `.ilean` is unchanged and the site's Chorus page keeps its hovers (2 602 `var` / 582 `const`, against master's 2 585 / 577); a constants-only version, which dropped them to 293 `var`, was rejected. Local model peak 10.3 → 8.6 GB, with the climb gone ([Dependencies.md](Dependencies.md) § "The Chorus model's memory"). Warm re-validation on the new pin: 12 min 7 s, 5 986 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 042 ♻, largest process 9.0 GB, lake exit 0, no warnings; monitor suites `ALL PASS`. |
| — | exit 0 | 0 | 5 986 | **Chorus S3: totality and the timeline to `M + 3Δ`** (2026-10-01, branch `worktree-r11-chorus-s3`, session R11; [Bounds.md](Bounds.md) §6.4.2 "Four findings from S3", §6.4.3 "The milestones as proven", §6.4.4 "Proven", §6.4.6 item 3). `Chorus.totality` proves `TotalityClaim` in the tolerance-parametric form (`max(c, GST) + max(Δ, d) + 2δ`), and `Chorus.totality_paper` gives the paper's `d_tot = Δ` at `δ = 0`, `d = Δ` ([Chorus/Totality.lean](../Cadence/Chorus/Totality.lean)). [Chorus/Timeline.lean](../Cadence/Chorus/Timeline.lean) proves the milestones of `prop:chorus-finalization-time` up to the MVBA proposals, each with its deadline, ending in `Chorus.within_all_input` (every correct validator proposes by `M + 3Δ + 3δ`). Four findings: F9, the case-(a) proposal is a local step (the premise now has the paper's two proposal rules, `propose` and `proposeFast`); F10, a Δ-row costs `max(Δ, δ)` (the schedule gains `δ_le_Δ`); F11 (R10's), re-dissemination was owed on the fast path (now only after the sender's own decision or its positive fallback entry; `Chorus.termination` re-proven, one lemma); F12 (R10's), the model's `cast_fb_commit` waits under FastQC roots too, open for R12 before S4. `ℓ`'s δ-multiple restated 8 → 9. No model or Veil proof file changed. Validated: `scripts/revalidate.sh` (JOBS=8), every project olean deleted, cache kept, `ALL GREEN` in 1 711 s, lake exit 0, 5 986 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 042 ♻, no warnings; `#veil_status` 4840 / 1507 / 220 unchanged; every new theorem pinned at the trio. |
| — | exit 0 | 0 | 5 986 | **Chorus S6: the premises are jointly satisfiable** (2026-10-01, branch `worktree-r10-chorus-witness`, session R10; [Bounds.md](Bounds.md) §6.4.5). The new [Chorus/Witness.lean](../Cadence/Chorus/Witness.lean) gives one instance (`Fin 4` under `byzNodeSetFin 4 1`, validator 3 Byzantine and silent, one proposer, `chorusTheory`, `valid := (· = v⋆)`), one schedule (`Δ = 1`, `δ = 0`, `D = 1`, GST 0) and one run: everyone finalizes on the fast path at clock 1 and then abandons; the MVBA stays quiet; the clock advances only at plateau ends where no row is enabled, or, for re-dissemination, where its gate closes inside its window. Three theorems, premises only, each pinned at the trio: `Chorus.termination_premises_satisfiable`, `Chorus.timedTermination_premises_satisfiable` (at `T := Mvba.mvbaTemporal`), `Chorus.totality_premises_satisfiable`. Finding **F11**: the re-dissemination row was owed off the fallback path, where the paper never re-disseminates, so the timed claims excluded ordinary fast-path runs; fixed by R11 (`bd887c5`) before this merged. No model or Veil file touched. Validated: warm re-validation (every project olean deleted, cache kept), one `LEAN_NUM_THREADS=8 lake build`, 697 s, lake exit 0, 5 986 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 042 ♻, no warnings; `#veil_status` 4840 / 1507 / 220 unchanged. |
| — | exit 0 | 0 | 5 986 | **F12: the fallback commit vote waits as the paper's rule does** (2026-10-01, branch `worktree-r12-fb-commit-guard`, session R12; [Bounds.md](Bounds.md) §6.4.2 "F12 closed", §6.4.5, §6.4.6 item 3). `cast_fb_commit`'s DA wait was `mvba_decided_pos J M → msg_chunk_received i J M`, under every decided positive root; it is now `mvba_decided_pos J M → vote_quorum_pos J M ∨ msg_chunk_received i J M`, the paper's "for each FallbackQC in B′ with a positive entry" (`line:fb-commit-foreach`) read as "no positive FastQC for it exists", both reads positive, no invariant added. Safety held: one cold Chorus-family re-solve, 4 825 ✅ / 0 ❌ / 0 💥 / 0 ⏱, 0 cache hits, 437 s at `LEAN_NUM_THREADS=8`. `Chorus.termination` re-proven (`eventually_fbcommit_sig`: a FastQC root needs no chunk, a FallbackQC root's correct signer re-disseminates); Timeline, Totality, Witness and the monitor unchanged, all three monitor suites ALL PASS. The fallback commit vote is now `δ` after the transported decision, `T₀ = M + 4Δ + ℓ_MVBA + 7δ`. Findings reported, not acted on: F13 (a root with both certificates: the model does not wait where the paper may) and F14 (re-dissemination's "decided" owed-disjunct is unused and owes more than the paper sends). The premise ledger gains its "used in" entries. Validated: `scripts/revalidate.sh` (JOBS=8), every project olean deleted, cache kept, `ALL GREEN` in 819 s, lake exit 0, 5 986 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 854 ♻, no warnings; `#veil_status` 4840 / 1507 / 220 unchanged. |
| — | exit 0 | 0 | 5 986 | **Realignment 1: indexed fragments, F14, citations to the rendered PDF** (2026-10-02, branch `worktree-r14-realign-statements`, session R14; [PaperAlignment.md](PaperAlignment.md) §8 "R14", [Bounds.md](Bounds.md) §6.4.2 "F14 closed"). `Primitives.ErasureCoding` takes `n` and `f` and decodes a `Finset (Fin n × fragment)` with `f+1` distinct indices (M3; uninstantiated, no Chorus VC moved: a warm proof file added no cache entry). `Chorus.Owed (.redisseminate_chunk …)` is `msg_fb_pos_sig k j m` alone (F14); `CorrectChunkQuorum` removed; `Chorus.termination`, the timeline, totality and the witnesses re-checked in plain Lean. The (d) items M5, M1/S15, M2, S4 as comment and doc edits. Citations: `scripts/paper-labels.sh` builds the target with tectonic and writes `docs/paper-labels.tsv` (377 labels); 1 135 citations in 40 files now read "<rendered> (`label`)", checked by `scripts/paper-cites.sh` (Interfaces.lean and System.lean deferred to R15). Lean edits outside `Owed`/Termination/Primitives are comment-only. Validated: `scripts/revalidate.sh` (JOBS=8), warm, `ALL GREEN` in 706 s, lake exit 0, 5 986 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 042 ♻, no warnings; `#veil_status` 4840 / 1507 / 220 unchanged; `scripts/site-links.sh check` and `scripts/paper-cites.sh` clean. |
| — | exit 0 | 0 | 5 987 | **Realignment 2: the meta-block representation and the MVBA contract** (2026-10-02, branch `worktree-r15-metablock-contract`, session R15; [PaperAlignment.md](PaperAlignment.md) §8 "R15" and §8.1, [Bounds.md](Bounds.md) §6.4.2 "F13 closed"). The MVBA's value is the meta-block representation (`MetaBlock`: entries plus each positive entry's certificate kind); `MVBASafety` gains `entries`, the quorum family as a parameter, Agreement and Integrity over entries, the certificate over entries and four certificate-level fields (withheld from the solver with the handoff facts). Mvba splits `value`/`evec` with `ent`; `Recover` a choice among valid representations; a fourth trace with two representations of one entry vector. Chorus: per-kind bridge at the handlers and `mvba_propose`; `cast_fb_commit i v` waits under the FallbackQC entries of its own decision (F13 closed); `Chorus.termination` stated at `Cadence.mvbaTheory`; finding P11 (redelivered decisions). Pins unchanged by design (1507 / 4840 / 220). Cold Mvba family: lake exit 0, 1 506 ✅ / 29 ♻, 63 s; NoLock re-pinned (same 25 transitions, `x` in labels), 85 s; cold Chorus family: lake exit 0, 4 825 ✅ / 47 ♻, 534 s, 6.9 GB. Validated: `scripts/revalidate.sh` (JOBS=8), warm, every project olean deleted, `ALL GREEN` in 758 s, lake exit 0, 5 987 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 042 ♻, no warnings; monitor suites ALL PASS; `scripts/site-links.sh check` and `scripts/paper-cites.sh` (no exemption left) clean. |
| — | exit 0 | 0 | 6 209 | **Realignment 3: Chorus finalizes on the MVBA's commit certificate** (2026-10-02, branch `worktree-r16-commitqc-route`, session R16; [PaperAlignment.md](PaperAlignment.md) §8 "R16" and §8.2). Part I's `CommitQC` route: `on_mvba_commitqc_pos`/`_neg` record a valid certificate's entries after the certificate bridge on the recovered representation, and `commit_assign_*` finalize on `fbcommitqc ∨ mvba_commitqc`. `MVBASafety` gains `certified_mono` and `AvailReady` as an input the caller drives (`markAvail` with its effect and frames); Chorus drives it (`mvba_avail_ready`, `avail_ready_chunks`); (F-avail) derived (`fAvail_of_fJustice`) and out of `MvbaAdmissible`; `ValidBridge` covers held values; (Δ-avail) left to S4. The MVBA-arm gates of the decision rules removed (our modelling error); `mvba_decided_phase` restated, `mvba_complete_phase` and `fbcommit_sig_phase` deleted (not provable over Module 3). Finding P12. `#veil_status Chorus` 4840 → 5099 (Mvba 1507, FallbackReceipt 220). Cold Chorus family: first run 2 ❌ (missing `availReady_markAvail_frame`; `mvba_complete_phase` without the gate), final run lake exit 0, 5 030 ✅ / 100 ♻, 955 s with the model; 19 manual cells re-run cold. Validated: `scripts/revalidate.sh` (JOBS=8), warm, every project olean deleted, `ALL GREEN` in 776 s, lake exit 0, 6 209 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 082 ♻, no warnings, peak 19.5 GB; monitor suites ALL PASS; `scripts/site-links.sh check` and `scripts/paper-cites.sh` clean. |
| — | exit 0 | 0 | 6 209 | **Realignment to `48cac9a` complete** (2026-10-02, branch `worktree-r17-realign-close`, session R17; [PaperAlignment.md](PaperAlignment.md) §0, §5.10, §6, §8 "R17"). Sessions R13–R17 moved the development from the mixed target tagged `paper-target/arxiv-v2` (arXiv v2, the MVBA at `eb1bb51`) to the single target `48cac9a` (main body plus internal supplement), tagged `paper-target/48cac9a` on this session's merge commit. R17 re-checked by §1 (the regenerated label map byte-identical, 377 labels; citations clean; paper `master` unmoved), walked the classification once more (every (b)/(c) item modelled, every remaining difference argued or a finding, none needing a model change), and ran the interface check, which found P13 (Module 1's Termination lacks the abandon and start conditions; the contract already states both). The findings page for the authors has **13 findings**, P1–P13. Every model header names no revision any more and points to §0 (comment-only; every family rebuilt warm). Full warm re-validation (`JOBS=8 scripts/revalidate.sh`, project oleans deleted, cache kept): ALL GREEN in 788 s, ✅ 6 209 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 082, no warnings; pins unchanged (Chorus 5099, Mvba 1507, FallbackReceipt 220, NoLock, `Mvba.Witness.ell = 24`, every axiom pin at the trio); the monitor suites pass. |
| — | exit 0 | 0 | 6 209 | **Chorus S4: the MVBA tail, the fallback commit round, and ℓ-termination** (2026-10-02, branch `worktree-r18-chorus-s4`, session R18; [Bounds.md](Bounds.md) §6.4.3 "The MVBA tail and the round, as proven", §6.4.5, §6.4.6 item 4). `TimedTerminationClaim` proven at the paper's bound `5Δ + ℓ_MVBA + 9δ` (`Chorus.timed_termination`; at the system's MVBA `Chorus.timed_termination_atMvba`), in plain Lean in the new [Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean): the MVBA tail through `T.termination` on the projection, the decision handlers, the termination record, the FallbackQC signer's chunk (a new first-flip fact: a correct signer signs before its second-round vote), the fallback commit vote under each validator's own `B′`, and the assignments and finalization by `T₀ = M + 4Δ + ℓ_MVBA + 7δ`. `Lchorus` stands. **F4 confirmed**: `Chorus.timed_termination_tight`, `4Δ + ℓ_MVBA + 8δ`, one split at the vote deadline (P5 of [PaperAlignment.md](PaperAlignment.md) §6, confirmed by proof). Plan changes: the generic theorems take `0 ≤ T.ℓ` of the MVBA contract (a theorem at the system's MVBA); the (Δ-avail) derivation was **not** done: it found **F15** (the model's re-dissemination is gated on the signer's participation at delivery, where the paper sends inside the fallback-entry rule), a model change left to R19 with the schedule constraint `Δ + δ ≤ Δ_sync`. The R10 witness run instantiates the proven claim. [Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean): comments only. No model or Veil proof file touched, nothing re-solved. Full warm re-validation (`JOBS=8 scripts/revalidate.sh`, project oleans deleted, cache kept): ALL GREEN in 784 s, lake exit 0, ✅ 6 209 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 082, no warnings; pins unchanged (Chorus 5099, Mvba 1507, FallbackReceipt 220), every new axiom pin at the trio (two arithmetic lemmas at `[propext]`); `scripts/paper-cites.sh` and `scripts/site-links.sh check` clean. |
| — | exit 0 | 0 | 6 121 | **F15 closed: the fallback signer re-disseminates inside the fallback-entry rule** (2026-10-02, branch `worktree-r19-fb-redisseminate`, session R19; [Bounds.md](Bounds.md) §6.4.2 "F15: the design" and "F15 closed", §6.4.6). `fb_sign_pos` sends every validator its chunk in the same step (Algorithm 5, line 12 (`line:fb-redisseminate`); bulk updates of `msg_chunk_received` and `local_chunk_sent`), `redisseminate_chunk` for correct senders is removed, and — added at the design review, the same shape — the proposer's `deliver_chunk_assigned` no longer requires the proposer to be active (its send is `propose`, Algorithm 2 (`alg:proposer-dissemination`)). The two readers of a re-disseminated chunk, `cast_fb_commit` (now `TimedJustice.fbCommit`, split at its trigger) and the `avail` family, are `Δ`-rows; the gate checklist admits the actor's own MVBA output. The schedule gains `Δ_le_Δsync : mvba.Δ ≤ mvba.Δsync` (what the derivation uses; R18's `Δ + δ ≤ Δ_sync` implies it). (Δ-avail) is derived (`Chorus.availWithin_of_timedJustice`); `timedMvbaAdmissible_of_rows` takes only (Δ-justice) and (T-timer); `SyncAtMvba`/`TimedTerminationClaimAtMvba` and the re-proven `Chorus.timed_termination_atMvba` assume no availability fact Chorus provides. `fAvail_of_fJustice` lost its `ActiveFrom`. P12 updated (the coupling remains a finding; the assumption is derived). The witness overrides `Δsync := 1` (`Mvba.Schedule.fixedNat` untouched, `Mvba.Witness.ell = 24`). `#veil_status Chorus` 5099 → 4997 (Mvba 1507, FallbackReceipt 220). Cold Chorus family (empty proof cache): lake exit 0, 4 978 ✅ / 0 ❌ / 0 💥 / 0 ⏱, no cache hit, 505 s after the model's 407 s. Validated: `scripts/revalidate.sh` (JOBS=8), warm, every project olean deleted, ALL GREEN in 793 s, lake exit 0, ✅ 6 121 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 067, no warnings, peak 22.2 GB; every axiom pin at the trio; the monitor suites pass; `scripts/paper-cites.sh` and `scripts/site-links.sh check` clean. |
| — | exit 0 | 0 | 6 109 | **Chorus S5: `SlotConsensusTemporal` and `SlotConsensusWithTotality`, proven** (2026-10-02, branch `worktree-r20-chorus-s5`, session R20; [Bounds.md](Bounds.md) §6.4.5, §6.4.6 item 5; [CompositionContracts.md](CompositionContracts.md) §5). The new [Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean) instantiates Module 1 (`mod:slotconsensus`)'s temporal level at the system's configuration, every field proven: `Chorus.chorusTemporal` (the participation interface from the transition bodies; `Admissible` = the claims' premises by name; `admissible_exists` from a generic idle run in which every proposer stays silent; Termination from `Chorus.termination`; Quiescence in Lemma 6 (`lemma:chorus-quiescence`)'s two parts, Chorus's own sends gated (`own_sent_new`, with the message type `Chorus.Message`, in [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean)) and the MVBA's inside the window between a gated `mvba_propose` and a forwarded `abandon` (two run invariants)), `Chorus.chorusWithTotality` (`timed_termination_atMvba`, `Chorus.totality`; `ℓ` and `d_tot` pinned by `rfl`, the paper's `5Δ + ℓ_MVBA` and `Δ` at `δ = 0`), joined into `Chorus.slotConsensusFull` with `…_toSafety` by `rfl`. (A-sc-termination) discharged; the Chorus bounds leg complete. **Contract correction** (approved by Lars): `SlotConsensusTemporal.quiescence` and `ACSTemporal.quiescence` quantified over unreachable states, our mis-statement of a property about executions; both now take `S.reachable st` (no consumer). **P14** (new): the target lets a slot's proposer set be empty; the instance assumes it non-empty, used only for `admissible_exists`. Plan changes: Termination from the untimed claim (the field gives no synchronized participation or C2); a generic idle run rather than the R10 witness; a per-slot deadline (`FamilySchedule`); `ByzNodeSetHonestQuorum` built for the family. No model or Veil proof file touched, nothing re-solved. Full warm re-validation (`JOBS=8 scripts/revalidate.sh`, project oleans deleted, cache kept): ALL GREEN in 769 s, lake exit 0, ✅ 6 109 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 079, no warnings, peak 19.6 GB; pins unchanged (Chorus 4997, Mvba 1507, FallbackReceipt 220, NoLock, `Mvba.Witness.ell = 24`), every new axiom pin at the trio; the monitor suites pass; `scripts/paper-cites.sh` and `scripts/site-links.sh check` clean. |
| — | exit 0 | 0 | 7 081 | **A solver-free first rung for step-property cells** (2026-10-02, branch `x1-step-rung`, CI-speed line X1; [Dependencies.md](Dependencies.md) § 2). Veil re-pinned `461c6832` → `288d11c9` (`port/step-rung`: a step cell's discharger is `first | veil_solve_step_frame | veil_solve_step`, the rung being the step route with the invariant clump and the assumptions cleared, closed by `grind` under a heartbeat budget whose overrun is a decline). Chorus's `committed_pos_frozen`, the slowest cell of 47 of 50 proof files on CI (39–53 s), is closed by the rung on every action at ~1 s; with the Mvba and Conductor step cells, 96 of 97 step cells close without a solver, the remaining Conductor cell needing an invariant. The `vote × committed_pos_frozen` manual cell, written for solver budget headroom, is removed (manual cells counted in [Architecture.md](Architecture.md)). Validated: `scripts/revalidate.sh` (JOBS=8), cache deleted, every project olean rebuilt, `ALL GREEN` in 1 101 s, lake exit 0, 7 081 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 88 ♻, no warnings; then warm (every project olean deleted, cache kept) `ALL GREEN` in 936 s, 6 185 ✅ / 1 006 ♻; `#veil_status` 4997 / 1507 / 220 unchanged; the `Mvba/NoLock.lean` pin holds. |
| — | exit 0 | 0 | 6 442 | **Conductor K1: the glue drives Chorus; ACS one pair per validator** (2026-10-03, branch `worktree-r25-conductor-k1`, session R25; [ConductorBounds.md](ConductorBounds.md) §9 "K1", §7 F18–F20, F22; [CompositionContracts.md](CompositionContracts.md) §3, §7). One [Interfaces.lean](../Cadence/Interfaces.lean) edit: Slot Consensus's three inputs with their records, frames, per-validator frames and cross-frames move into `SlotConsensusSafety` (C8); the ACS's `abandon` into `ACSSafety` with its cross-frames (C7); `ACSSafety.decided_unique`, and `validity_quantitative` counts distinct validators (C6, P16). The glue's `on_open`, `on_propose` and `on_finalize` drive `sc.participate`, `sc.propose` and `sc.abandon` (the last with `orch.complete`, in one step); its record relations are gone; new invariant `[participating_opened]`; `[bounded_concurrency_interval]` is now the one direction Lemma 5 uses (a claim-surface change: the separate handlers over-approximate the paper's atomic ones). The Conductor's `enter_window` reads its own decision and abandons the instance; new invariant `[acs_abandoned_decided]` (Proposition 12). The Chorus field proofs moved to [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean). `Cadence.acs_median_bracket` ([AcsMedian.lean](../Cadence/AcsMedian.lean)) justifies the median bridge. Sweeps cold: the glue 182 → 216, the Conductor 189 → 197. Veil pin unchanged (`288d11c9`); the ✅ count is a single `JOBS=8` `lake build` of the suite. |
| — | exit 0 | 0 | 6 427 | **Premise trims: `hqe` derived, `leader_honest_cofinal` removed** (2026-10-03, branch `worktree-r23-premise-trims`, session R23; [Premises.md](Premises.md) §7). Lars's decisions on R21's three independence findings. (1) `MVBATemporal.termination`'s `Valid` antecedent is kept: it is the paper's caller condition, not used by this instance's proof. (2) `Chorus.timed_termination_atMvba` and `…_tight_atMvba` no longer take `hqe : ByzNodeSetHonestQuorum`; they derive it from `Chorus.hqeFin`, which moved into [Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean) unchanged. Plain Lean. (3) **A premise removed:** the Mvba model's `assumption [leader_honest_cofinal]` (A-leader-rotation) is gone, with its one reader `Mvba.exists_honest_leader_above[_of_reachable]` (unused); `LeaderRotation` implies it. It was a conjunct of `mvbaSafety.init`, so the MVBA's safety claims now hold for every leader schedule rather than for schedules with cofinally many correct leaders. Every Mvba VC statement changed and the family re-solved with an empty proof cache (`lake build Cadence.Mvba.Certify`: ✅ 1 506, ❌/💥/⏱ 0, 0 hits, 323 entries stored, the four manual cells' tactics run; `#veil_status Mvba` stays 1507: an assumption changes statements, not cells); the [Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) witness survived unchanged, and its header loses the restriction that the mutant dropped the assumption, so its refutation is now of the exact lock-free mutant. `Mvba.Witness.ell` is 24 and every MVBA and Chorus result re-proves. JOBS-mode build, warm, 897 s (after the `288d11c9` re-pin rebuilt Veil); ✅ count from that single `lake build`. |
| — | exit 0 | 0 | 6 189 | **Conductor K2: the model fixes what the timed claims need** (2026-10-03, branch `worktree-r26-conductor-k2`, session R26; [ConductorBounds.md](ConductorBounds.md) §7 F21 and F25, §9 "K2"; [PaperAlignment.md](PaperAlignment.md) §5.10). One [Conductor.lean](../Cadence/Conductor.lean) edit, each rule a constraint the paper's protocol satisfies: the shift functions `win_last`/`win_boundary`, with `acs_decide` recording exactly the window's `W` slots from its first and `[genesis_window]` tying window 1 and the initial clock to slot 1; the full `s*` rule over `now` in `acs_propose`; the median's upper bracket as a second witness pair; `[start_time_strict]`. New invariant `[win_bounds_shift]`. F25, found here: the readiness boundary was a slot readiness asked to be complete, so the model covered only `p ≥ 1`; now it is the window's `(p + 1)`-th slot with readiness strictly below it, and the model covers the paper's `0 ≤ p ≤ W − 1`. The "Timing relaxation" joined §5.10's table, where it had been missing. Sweep cold: the Conductor 197 → 205, green; Composition and System re-proved unedited. Veil pin unchanged (`288d11c9`); the ✅ count is a single `JOBS=8` `lake build` of the suite. |
| — | exit 0 | 0 | 7 072 | **`Vote.lean` keeps the Bool-atom fold for all but one cell** (2026-10-03, branch `x4-vote-fold-scope`, CI-speed line X4; [Dependencies.md](Dependencies.md) § "Native shared libraries"). The file-level `set_option veil.smt.foldBoolAtoms false` in [Cadence/Chorus/Proofs/Vote.lean](../Cadence/Chorus/Proofs/Vote.lean) became `set_option … in` on a `#prove_vc` line for the one divergent cell, `fastqc_complete_implies_mvba_evidence`, whose tactic is the automatic `veil_solve_wp`; the other cells of `vote` now take the fold. No VC statement moves. The real module consumes the scoped cell (the `set_option … in` trap for declaring commands does not apply to `#prove_vc`). Measured cold, cache off, `LEAN_NUM_THREADS=4`: the file's build 87 s → 49 s wall (423 s → 182 s CPU), peak 7.4 → 4.8 GB, olean 53 → 26 MB; 100 ✅ / 0 ❌ / 0 💥 / 0 ⏱. `lake build Cadence.Chorus.Certify Cadence` then exit 0 with every proof file cold: 7 072 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 147 ♻, no warnings, all `#veil_status` and axiom pins holding. |
| — | exit 0 | 0 | 7 132 | **The cheap rung matches goals with introduced binders** (2026-10-03, branch `x5-rung-binders`, CI-speed line X5; [Dependencies.md](Dependencies.md) § 2). Veil re-pinned `288d11c9` → `6662c257` (`port/cheap-rung`: when `exact` misses, `veil_solve_frame` opens the projected conjunct as a metavariable telescope, unifies its conclusion with the goal and fills its hypotheses from the context). Guard-free actions reach the rung with the invariant's variables already introduced, which the `exact` matcher could not close: `participate`'s file went from 11/101 cells closed without a solver to 101/101 (cold, cache off, one file at `LEAN_NUM_THREADS=8`: 45.6 s / 375 s CPU → 10.8 s / 70 s). Over every proof file the rung's wins went from 4 460 to 4 573 of 4 930 on Chorus, from 1 184 to 1 313 of 1 473 on the Mvba (that baseline from a tree one premise behind), and stayed at 161 of 210 on the receipt layer; no cell the rung closed before declines now, and files where it already won are unchanged within noise. No VC statement moved. Validated: `scripts/revalidate.sh` (JOBS=8), cache deleted, every project olean rebuilt, `ALL GREEN` in 1 123 s (8 535 s CPU), lake exit 0, 7 132 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 88 ♻, no warnings; `#veil_status` 4997 / 1507 / 220 and the axiom pins unchanged; the `Mvba/NoLock.lean` pin holds. |
| — | exit 0 | 0 | 7 131 | **Frame cells share one bridge theorem per action** (2026-10-03, branch `x7-frame-setup`, CI-speed line X7; [Dependencies.md](Dependencies.md) § 2). Veil re-pinned `6662c257` → `862b4e25` (`port/frame-bridge`, option `veil.vc.frameBridge`, on by default). A frame cell's ~0.35 s had gone to work that was the same for every cell of an action: the local-WP bridge (half of it an instance search over all ~125 `LocalRProp` instances, which the reducible invariants key alike) and a simp of goal and conjunct to the same normal form. Now `#prove_action` proves the bridge once per action as `<action>.ext.frame_bridge`, a kernel-checked theorem over an abstract postcondition; a cell instantiates it with its invariant's instance by name and closes by projection and `exact`, with the previous simps and both matchers as the fallback. No VC statement moved; the bridge theorems are not cells. Cold, cache deleted, `LEAN_NUM_THREADS=8`, per family with the option off → on: Chorus 5 071 → 2 141 s CPU (344 → 158 s wall), Mvba 559 → 312 s (39 → 24 s), receipt layer 58 → 36 s (7 → 6 s); the rung's wins unchanged at 4 573 / 1 313 / 161. Validated: `scripts/revalidate.sh` (JOBS=8), cache deleted, every project olean rebuilt, `ALL GREEN` in 296 s (3 425 s CPU), lake exit 0, 7 131 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 88 ♻, no warnings; `#veil_status` 4997 / 1507 / 220 and the axiom pins unchanged; the `Mvba/NoLock.lean` pin holds. |
| — | exit 0 | 0 | 6 189 | **Conductor K3: the contract in rely form, and the timed claims stated** (2026-10-03, branch `worktree-r27-conductor-k3`, session R27; [ConductorBounds.md](ConductorBounds.md) §9 "K3", F26; [Premises.md](Premises.md) §9). One [Interfaces.lean](../Cadence/Interfaces.lean) edit, decided by Lars (C4, C5): `OrchestratorTemporal`'s Totality and Recovery take the caller's two conditions as antecedents, (R-tot) `CallerTotality` and (R-term) `CallerTermination`, at the caller's latencies `caller_d_tot` and `caller_ℓ`, and `OrchestratorWithTotality` carries `d_tot` and the bounded Totality that Corollary 4 consumes; the boundedness entry no longer says the widths are meta. Upper-class only: no Veil module instantiates either level, so no VC moved — the warm re-validation re-elaborated everything downstream at the same ✅ count as K2. New plain-Lean files: [PartProjection.lean](../Cadence/PartProjection.lean), the K0 spike's generic half (the stutter lift, `partRun` and the transfer lemmas, the ACS and slot-consensus fields read in a composed run; updated for R25's field moves); [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean), with `ConductorSchedule` (Chorus's family schedule plus `W`, `p`, `τ`, the ACS's `ℓ`, slot 1's start, the four parameter assumptions over the Chorus instance's own `Lchorus`/`Ltot` and `δ = 0`), timed Conductor runs, the rows and gates, (P-open), the per-window ACS component and the guarded `AcsAdmissible`, and the three claims as `Prop`s whose conclusions are the contract's fields at the Conductor's fragment; [Conductor/IdealAcs.lean](../Cadence/Conductor/IdealAcs.lean), the ACS contract's model, both levels proven, as the consistency witness. F26 found and closed by Lars's decision: the ACS contract did not say that its inputs are accepted; `ACSTemporal.propose_enabled` and `abandon_enabled` now do (a second Interfaces.lean edit). They sit in the upper class because in `ACSSafety`, even withheld with `veil_smt_ignore`, they took the Conductor's `open_slot × open_prefix_agreement` from ~5 s past its 180 s budget, reproducibly; the cause is a question for the Veil fork. Every new declaration axiom-pinned at the trio or less. Validated: `scripts/revalidate.sh` (JOBS mode, project oleans warm) `ALL GREEN` in 755 s, 6 189 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 053 ♻, no warnings; then `lake build` with the new files, exit 0; `#veil_status` pins unchanged; paper-cites and site-links clean. Veil pin unchanged (`288d11c9`). |
| — | exit 0 | 0 | 6 189 | **Conductor K4: the window induction; Boundedness and Totality proven** (2026-10-03, branch `worktree-r28-conductor-k4`, session R28; [ConductorBounds.md](ConductorBounds.md) §7 F27–F29, §9 "K4"; [Premises.md](Premises.md) §9). Two new plain-Lean files. [Conductor/Boundedness.lean](../Cadence/Conductor/Boundedness.lean): `Conductor.boundedness`, the `BoundednessClaim` at the paper's `2W − p` exactly, from `[bounded_tail]` and the window widths, with the model facts both files share (the handlers' guards and effects, `entered_pred` by an induction over reachability, unique and persistent window bounds). [Conductor/Induction.lean](../Cadence/Conductor/Induction.lean): Definition 6's four conditions as `Prop`s and Proposition 13 (`window_synchronized`) by strong induction over first slots, Corollaries 1–3 (`entry_sync`, `prop_sync`, `comp_sync`) and Lemma 15 (`open_sync`, `totality` = `TotalityClaim`), every deadline `max(t, GST) + Δ`, no slack. The ACS enters only through its contract (Δ-Totality on the window's part of the run, `integrity`, input-enabledness), Chorus only through (R-tot). Three statement fixes in [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean), each found by the proof and approved by Lars: F27 (`[IsOrderedAddMonoid time]` on the timed claims), F28 (`StartsUnbounded`, without which `s*` can fail to exist and Totality is false; not derivable from `StartTimes` even at an Archimedean time) and F29 (Totality's unused fault bound dropped). Composition.lean's stale note fixed (comment only); `Cadence.lean` indexes and pins the new results. Validated: `scripts/revalidate.sh` (JOBS mode, project oleans deleted, cache warm) `ALL GREEN` in 767 s, 6 189 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 053 ♻, no warnings, exit 0; `#veil_status` pins unchanged (no VC moved); paper-cites and site-links clean. Veil pin unchanged (`288d11c9`). |
| — | exit 0 | 0 | 6 189 | **Conductor K5: `(2Wτ)`-Recovery proven** (2026-10-03, branch `worktree-r29-conductor-k5`, session R29; [ConductorBounds.md](ConductorBounds.md) §7 F30, §9 "K5"; [PaperAlignment.md](PaperAlignment.md) §6 P18; [Premises.md](Premises.md) §9). One new plain-Lean file, [Conductor/Recovery.lean](../Cadence/Conductor/Recovery.lean): Propositions 14–19 (`open_to_complete`, `enters_every_window`, `window_open_time`, `window_progression`, `smooth_windows`, `first_post_gst_window_time`) and Lemma 16 (`recovery` = `RecoveryClaim` at `𝓡 = 2Wτ`), each at the paper's deadline, all through one engine, `succ_window` (R-term, the three rows, the ACS's ℓ-termination). `recovery_sharp` proves the same at `(W + p − 1)τ`. One statement edit in [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean), approved by Lars: `RecoveryClaim` takes `StartsUnbounded` (F28, as planned) and the new `WindowsUnbounded` (F30: at `window := Fin 1` the claim was false). Slack for the authors (P18): (1)–(2) need only `ℓ_chorus` in place of `Φ_oc`, (2) only in Proposition 19, (3) only `0 < ℓ`. Every premise is used. `Cadence.lean` indexes and pins `recovery` and `recovery_sharp`. Validated: `scripts/revalidate.sh` (JOBS mode, project oleans deleted, cache warm) `ALL GREEN` in 595 s, 6 189 ✅ / 0 ❌ / 0 💥 / 0 ⏱ / 1 053 ♻, no warnings, exit 0; `#veil_status` pins unchanged; paper-cites and site-links clean. Built at master's Veil pin `862b4e25` (the session's private package tree, re-checked out from `288d11c9`). |
| — | exit 0 | 0 | 6 189 | **Conductor K6: `OrchestratorTemporal` and `OrchestratorWithTotality`, proven** (2026-10-03, branch `worktree-r30-conductor-k6`, session R30; [ConductorBounds.md](ConductorBounds.md) §9 "K6"; [CompositionContracts.md](CompositionContracts.md) §5; [Premises.md](Premises.md) §9.5). The new [Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean) instantiates Module 2 (`mod:orchestrator_2`)'s temporal level at `Conductor.orchestratorSafety`, for an arbitrary ACS meeting its contract, every field proven: `Conductor.conductorTemporal` (`Admissible` = `contractRun` of a labelled run meeting `Sync`; `admissible_exists` from an idle run in blocks of `|node| + 1` steps, a `tick` to each slot's starting time and then window 1's openings, its rows shut because assumption (4) forces `p ≥ 2`; Totality, `(2W − p)`-Boundedness and `(2Wτ)`-Recovery from `Conductor.totality`, `boundedness`, `recovery`), `Conductor.conductorWithTotality` (`d_tot` by `rfl`, the paper's `Δ` at `δ = 0` by rewriting), joined into `Conductor.conductorFull` with `…_toSafety` by `rfl`; `bound`, `recovery_time` and the caller's constants pinned by `rfl`. Hypotheses: the claims' configuration premises by name. `WindowsUnbounded` holds at `window := ℕ` and `StartsUnbounded` over an Archimedean time with `0 ≤ start₀` (`Conductor.conductorFullNat`). System.lean keeps the fragments (safety, generic in slot and time). No class, claim or model statement changed; status text edited, comment only, in Interfaces.lean, Composition.lean and Conductor.lean's header (approved by Lars), CLAUDE.md, Cadence.lean (index, 14 pins), README, Architecture, CompositionContracts. **Pin figures moved here** from session records in [Bounds.md](Bounds.md) and [PaperAlignment.md](PaperAlignment.md) §8 R16: R16's `#veil_status Chorus` came out at 5099, two helper invariants (100 cells) below the designed 5199; R19 took it 5099 → 4997. Validated: `scripts/revalidate.sh` (JOBS=8, project oleans deleted, cache warm) ALL GREEN in 609 s, lake exit 0, ✅ 6 189 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 053, no warnings, peak 19.4 GB; pins unchanged (Chorus 4997, Mvba 1507, FallbackReceipt 220, NoLock); every new axiom pin at the trio (`startsUnbounded_of_startTimes` at `[propext, Quot.sound]`); `scripts/paper-cites.sh` and `scripts/site-links.sh check` clean. |
| — | exit 0 | 0 | 6 189 | **K7: the composed timed claims — Corollary 4, Lemma 5, `𝓡`-Liveness** (2026-10-03, branch `worktree-r31-composed-timed`, session R31, draft PR #84; [ConductorBounds.md](ConductorBounds.md) §9 "K7"; [Premises.md](Premises.md) §0; [CompositionContracts.md](CompositionContracts.md) §6). Five new plain-Lean files under [Composed/](../Cadence/Composed/Schedule.lean): the composed timed run (the glue at the Conductor and Chorus, one fault pattern, one clock, one `Δ`, `δ = 0`; both parts stutter-lifted; the glue's five rows; `SysSync`) and the three claims stated; every caller condition of either side discharged (C1, C2, participation, Δ-synchronized participation; (R-tot), (R-term)); `Composed.corollary4` and Chorus's three claims per slot with no caller premise left; `Composed.boundedConcurrency` (Lemma 5 at `2W − p`); `Composed.recovery_in` and `Composed.liveness` at `2Wτ`, `…_sharp` at `(W + p − 1)τ`. Censorship resistance not proven: F31 / P19, the deadline tie, put to Lars. No model, proof file or shared statement file edited; System.lean unchanged. Validated: `scripts/revalidate.sh` (JOBS=8, project oleans deleted, cache warm) ALL GREEN in 636 s, lake exit 0, ✅ 6 189 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 053, no warnings, peak 16.7 GB; pins unchanged (Chorus 4997, Mvba 1507, FallbackReceipt 220, NoLock); 22 new axiom pins at the trio; `scripts/paper-cites.sh` and `scripts/site-links.sh check` clean. |
| — | exit 0 | 0 | 6 189 | **K7 complete: censorship resistance within Cadence, after F31** (2026-10-04, same branch and PR #84, session R31.2; [ConductorBounds.md](ConductorBounds.md) §7 F31, §9 "K7"; [Premises.md](Premises.md) §0, §4.8; [PaperAlignment.md](PaperAlignment.md) P19). Lars decided F31 (option A, approved in session): a standalone premise of Chorus's timing model, (P-incl) `Chorus.DeadlineInclusive` ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)), a chunk delivered by the deadline is recorded, the paper's "by the deadline" read inclusively; not part of `SyncAtMvba`, so no existing claim changed. New [Chorus/Inclusion.lean](../Cadence/Chorus/Inclusion.lean) (`within_proposal_recorded_incl`, `committed_post_deadline`) and [Composed/Censorship.lean](../Cadence/Composed/Censorship.lean) (`Composed.censorship` at `2Wτ`, `…_sharp` at `(W + p − 1)τ`); the glue's proposer assignment is Chorus's by construction, a well-encoded root a plain premise; the `propose` row now used. The Chorus witness meets (P-incl) (`Chorus.Witness.deadlineInclusive`). Validated: `scripts/revalidate.sh` (JOBS=8, project oleans deleted, cache warm) ALL GREEN in 615 s, lake exit 0, ✅ 6 189 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 053, no warnings, peak 16.6 GB; pins unchanged (Chorus 4997, Mvba 1507, FallbackReceipt 220, NoLock); new axiom pins at the trio; `scripts/paper-cites.sh` and `scripts/site-links.sh check` clean. |
| — | exit 0 | 0 | 6 189 | **K8: the composed claims' premises are jointly satisfiable; the Conductor leg complete** (2026-10-04, branch `worktree-r32-composed-witness`, session R32; [ConductorBounds.md](ConductorBounds.md) §8.2, §9 "K8"; [Premises.md](Premises.md) §0, §0.5). New [Composed/Witness.lean](../Cadence/Composed/Witness.lean) over eight files in [Composed/Witness/](../Cadence/Composed/Witness/): one model of the composed system (`Fin 4`, validator 3 Byzantine and silent, `Δ = τ = 1`, `δ = 0`, `ℓ_MVBA = 24`, `ℓ_ACS = 2`, `p = 4`, `W = 36`, the ideal ACS) and one infinite run, built one 56-step clock plateau at a time (`Cadence.plateauRun`, the periodic extension), in which every slot takes the fast path and every window repeats the first. `Composed.Witness.corollary4_`, `boundedConcurrency_`, `liveness_`, `censorship_` and `conductor_premises_satisfiable`, each claim applied to the model as a check. Rows hold at quiet plateau ends (`Cadence.bufferedFairFamily_of_ends`); a slot's part starts at its first step (its initial state cannot stutter) and is one labelled run up to a clock shift. No finding; no model, proof or statement file edited; one session instead of the planned two. Validated: `scripts/revalidate.sh` (JOBS=8, project oleans deleted, cache warm) ALL GREEN in 651 s, lake exit 0, ✅ 6 189 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 053, no warnings, peak 17.7 GB; pins unchanged (Chorus 4997, Mvba 1507, FallbackReceipt 220, NoLock); every new axiom pin at the trio (the two generic plateau lemmas at `[propext]`); `scripts/paper-cites.sh` and `scripts/site-links.sh check` clean. |
| — | exit 0 | 0 | 6 189 | **Final documentation pass: the current story, one home per fact** (2026-10-04, branch `worktree-r33-docs-final`, session R33). Comments and docs only. Session records, finished plans, staging and superseded figures moved here (§ "The realignment to `48cac9a` (R14–R17), and its designs"; § "Records moved out of the living documents (R33)"): PaperAlignment §8, most of Bounds.md §3–§6, ConductorBounds.md's kick-off and staging, Liveness.md §4's stage records, TODO.md's done items. Stale statements fixed, among them `Conductor.lean`'s "Liveness — meta-argument" (both Conductor and Chorus model files edited, comment only, families rebuilt warm). Architecture §2's canonical table brought current (Conductor sweep 205, glue 216); repeated counts made pointers. PaperAlignment §6 made send-ready (intro, three groups). TODO.md open items only. Validated: `scripts/revalidate.sh` (JOBS=8, project oleans deleted, cache warm) ALL GREEN in 643 s, lake exit 0, ✅ 6 189 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 053, no warnings, peak 18.1 GB; pins unchanged (Chorus 4997, Mvba 1507, FallbackReceipt 220, NoLock); `scripts/paper-cites.sh` and `scripts/site-links.sh check` clean. |
| — | exit 0 | 0 | 6 348 | **The MVBA decision handlers without `mvba_invoked`; the completion record per validator** (2026-10-07, branch `worktree-r34-mvba-decide-gate`, session R34; [ChorusDesign.md](ChorusDesign.md) §3.1, §4; [Bounds.md](Bounds.md) F6; [PaperAlignment.md](PaperAlignment.md) §8.2 (d)). The docs line's audit of every Chorus action (D5, [guide/audit/Chorus.tsv](guide/audit/Chorus.tsv)) found that `on_mvba_decide_pos`/`_neg` and `mvba_terminate` required `mvba_invoked`, a ghost over every validator's FastQC rows and the fault pattern, which the target's handler (Algorithm 5, line 37 (`line:fb-mvba-decide`)) does not read: the paper's `mvbaInvoked` is the proposer's own flag. Our divergence, the guard R16 missed when it dropped these handlers' arm gates; removed. `cast_fb_commit` read the global `mvba_complete` that the first validator to transport its decision set (F6), and `mvba_terminate` guarded on `¬ mvba_complete`, a negative read of a shared record; both replaced by the per-validator `local_mvba_complete i` (own-row fired-once guard, own-row read), with `mvba_complete` now a ghost `∃ i, local_mvba_complete i` so the invariant texts stand. Lars approved the one premise text change: `fbCommitGate` reads `local_mvba_complete i` (weaker; it now meets the gate checklist). No claim statement changed and the bounds are unchanged (each correct validator transports by `X_d + 2δ`). Re-proven at the trio: `Chorus.termination`, the timeline, totality, `timed_termination`(`_tight`)(`_atMvba`), both witnesses, the Composed files. Cold re-solve of the whole Chorus family (no cache hit): 4 978 ✅, 0 ❌/💥/⏱, slowest cell 30.3 s locally (`aggregate_fastqc_pos × speculative_agreement_pos_neg`); pin unchanged at `4997/4997`. Warm re-validation `JOBS=6`, 658 s. Docs: ChorusDesign §3.1 made exact (all fired-once records, `fb_sign_neg`'s unscoped chunk conjunct and why it equals the `qv`-scoped guard, the positive reads of the MVBA records argued); `participating`/`abandoned` got doc comments. `Chorus.termination`'s docstring and [Termination.lean](../Cadence/Chorus/Termination.lean)'s header carried history: until R8 the late branch split on the progress dichotomy and took the commit route on its left disjunct; they now state why it does not. |
| — | exit 0 | 0 | 7 515 | **The locality idiom: one rule, no case-by-case arguments** (2026-10-07, branch `r35-locality-idiom`, session R35; [Locality.md](Locality.md), [ChorusDesign.md](ChorusDesign.md) §3, [Premises.md](Premises.md) §4). Lars's rule: one generic idiom, checkable by pattern matching; then his principles — the network is the only global state a correct validator writes, monotone because it encodes a Byzantine network up to synchrony; the environment touches only its own state; certificates are formed in local state and sent as messages. [Locality.md](Locality.md) states them once for every model, as the specification of the planned checker. Inventory: the glue and FallbackReceipt conform; Mvba (environment timers, sender-less certificates) and the Conductor (`acs_decide`) are open for later sessions. Chorus was brought into conformance: chunks became sender-indexed point-to-point messages sent by `propose` and `fb_sign_pos` (the environment's `deliver_chunk_assigned` and `local_chunk_sent` went); `fb_sign_neg` reads its own vote receipts (`receive_vote_*`) instead of a negative read of the network within `qv`; the shared `mvba_decided_*` became read-by-no-action auxiliary records and `mvba_terminate` reads its own rows; `msg_commitqc_*` gained a sender; the fallback commit vote and certificate carry their entry vector, and the MVBA's CommitQC is a message (`send_mvba_cert`), with finalization in three routes per sign, each re-broadcasting (the `on_mvba_commitqc_*` handlers and the old two `commit_assign_*` went). ChorusDesign §3.1.1's two "documented exception categories" are gone: the self-row reads are the rule for one's own sends, and the witnessed quorum is a read of one's own receipts. `#veil_status Chorus` 4997 → 6215 (+1 274 = 7 new actions × 102 + 10 new invariants × 56, then − 56 when `local_committed_pos_implies_decodable` became a theorem, below); nineteen new manual cells: five after the cold re-solve (two cells had crossed 180 s, one with a spurious empty counterexample), and fourteen after CI's first run, where a cell that takes 18.9 s locally took 183 s — every new or changed cell at 40 s or more on CI was written out. CI's second run failed on the same invariant through another action (`local_committed_pos_implies_decodable`, 184 s), so the invariant was demoted to the theorem `Chorus.local_committed_pos_implies_decodable` ([Chorus/Compose.lean](../Cadence/Chorus/Compose.lean)), derived from `local_committed_pos_backed` and the two decodability invariants (no claim changed; its cells went for every action), and from a complete local cold timing table every automatic cell above 25 s became manual too (twelve more, among them `mvba_recorded_entries` at the five actions that move the MVBA's state, from the contract's agreement). Cold re-solve of the family 0 ❌/💥/⏱; 44 manual cells. Premise changes, all approved by Lars: receiver steps carry the `Δ` rows; a certificate the actor itself sent is read in a local `δ` step ("sending a message to oneself should cost as much as an internal step"), which restores `timed_termination_tight` at `4Δ + ℓ_MVBA + 9δ` (one `δ` more, for the vote-receipt step; at `δ = 0` the paper's `4Δ + ℓ_MVBA`, P5); `Schedule.δ_le_ρ` new; `Mvba.Relayed` weakened to deciders that have proposed and not abandoned (Supplement, Lemma 13's termination setting) instead of a `DecisionOutput` premise; `DeadlineInclusive` restated over `msg_chunk`. Main bound, totality and every safety claim unchanged. The R34 history sentence in [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) (the handoff premise named a commit certificate until R8) moved here. Warm re-validation `JOBS=8`, 890 s; the Chorus model alone 671 s. |
| — | — | — | — | **The guide: the D line (D1–D10)** (2026-10-06 – 2026-10-08, sessions D1–D10, PRs #87–#93, #95, #97, #98 and #99). Docs and guide sources only. The Verso guide became the auditor's entry point: one page per chapter, the claims box, eight chapters, elements computed from the compiled development, SVG diagrams, and the README as the developer's landing page. The design plan, `docs/GuidePlan.md`, was removed in D10; it is in git history at `68818a2`. |
| — | exit 0 | 0 | 7 699 | **The MVBA follows the locality idiom; Chorus sends its own decision's certificate** (2026-10-08, branch `worktree-r36-mvba-locality`, session R36; [MvbaPlan.md](MvbaPlan.md) §11, [Locality.md](Locality.md) §7). Design first, approved by Lars with option A. The view timer is the validator's own step (`expire_timer` gains `¬ is_byz i`); `become_avail_ready` is documented as the caller's input. Every certificate row carries its sender and is written only by its former or forwarder: `msg_prepqc s`, `msg_commitqc s`, `msg_tc s`, `msg_tc_lock s`, `msg_tc_nolock s` (`tc_lock`/`tc_nolock` renamed); `decided_qc` records `DecidedQC_i`; `decide` reads the certificate at its sender and outputs it under its own name; the anonymous `form_*` went, the adversary aggregates as `byz_form_*`; `sync_view` split into `sync_view_nolock`/`_lock`, every `sync_view_*` forwards (Supplement, Algorithm 1, line 98 (`line:mvba:sv-forward`)); the leaders read their own `ViewTC_l`. New invariants `decided_qc_sent`, `decided_qc_decided`, `entered_forwarded`. Contract (approved): `MVBASafety.decidedCert`, `decided_certified` onto it, `decidedCert_certifies` (stated with the decision's existence, which implies the approved form via Integrity), both withheld; Chorus's `send_mvba_cert i c` reads `mvba.decidedCert` at its own index, closing Locality §7's Chorus item. Premises: (F-justice)'s `Owed` and (Δ-justice)'s `forwarded`/`certificates` owe a timeout-certificate step only for a correct sender (weaker, the paper's network); (F-relay) and (Δ-relay) take the decider's own output. `#veil_status Mvba` 1507 → 1649 (29 actions × 55 + 54), solved cold; Chorus 6271 unchanged but re-solved cold (the contract change moved every statement), green. Manual cells: Mvba +4 (timeout frame cells, 9.8–53.4 s by the solver), Chorus +2 (the MVBA-route inclusion cells, `commit_assign_neg_mvba × proposal_inclusion_no_neg` 114.9 s on CI before, now 0.6 s). The withheld fields slowed no Chorus cell: the MVBA-touching cells take at most 11.0 s in isolation. NoLock re-pinned: the same 25 transitions, changed only by senders, `byz_form_commitqc` at node 0, `decided_qc` and the forwards; 152 s module build. Warm re-validation `JOBS=8`, 893 s. |
| — | exit 0 | 0 | 7 736 | **Byzantine rules as prohibitions; the knowledge guards dropped** (2026-10-08, branch `worktree-r36b-byzantine-rules`, session R36b; [Locality.md](Locality.md) §4.2). Lars: a correct validator's rules are permissions, a Byzantine validator's are prohibitions, since every restriction of the adversary weakens the claims. Locality §4 split into §4.1 (correct, R1–R6/W1–W3), §4.2 (Byzantine: B1 own writes only, B2 unforgeability — an invalid signature is modelled by the message's absence, B3 sub-protocol through the contract, B4 receiver checks stated on the sender, listed as gaps) and §4.3. `byz_redisseminate_chunk` drops `is_proposer`, `msg_proposer_signed` and `chunk_quorum` (any chunk of any root, under its own name); one manual cell's intro changed. The drop experiment classified the other guards: `byz_sign_fb_pos`'s proposer signature is B2 and stays; `byz_sign_vote_pos` (`chunk_received`), `byz_cast_vote` (an entry per proposer) and Mvba `byz_timeout_qc` (`vord.le w v`) are B4 — each failed its invariants when dropped — and move to the correct receivers in two scheduled sessions (option A, [TODO.md](TODO.md)). No knowledge assumption about the adversary remains. PaperAlignment §5.10 rows and P20 (channel privacy unstated). Pins unchanged (Chorus 6271, Mvba 1649, FallbackReceipt 220). Validated: `JOBS=8 scripts/revalidate.sh`, project oleans deleted, cache warm: exit 0, 932 s, ✅ 7 736 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 868, no warnings; monitor suites ALL PASS; guide build, `scripts/paper-cites.sh` and `scripts/site-links.sh check` clean. |
| — | exit 0 | 0 | 7 687 | **The Conductor follows the locality idiom** (2026-10-08, branch `worktree-r37-conductor-locality`, session R37; [ConductorBounds.md](ConductorBounds.md) §10, [Locality.md](Locality.md) §7). Design first, approved by Lars with option A and all six decisions. Each validator computes its window's interval from its own ACS decision in its entry step (Algorithm 7, line 48 (`line:median-compute`) is a step of the handler at Algorithm 7, line 44 (`line:acs-decide`)) and keeps it in its own row `local_bounds`; `acs_decide`, which had no actor, and the global `acs_decided` went; `opened_win` became `aux_opened_win`. The first slot is the configuration function `acs_first`, constrained by the model assumptions `[acs_first_local]` (a function of the decided set alone, stated over two validators after the sweep refuted the one-validator form) and `[acs_first_bracket]` (the median bridge, moved out of a `require` that read other validators' fault status); the lower median meets both under the fault bound (`Cadence.lowerMedian_first_assumptions`). Contract (approved): `ACSSafety.decided_stable`, a decision is final. Agreement on the intervals is the safety property `[window_assignment_agreement]`; the helper invariant `[first_agree]` and a derivable entry guard ("beyond the current window", proven at every reachable state by `Conductor.entry_beyond`) replace the planned manual cells (an in-file sweep has none); a first helper invariant `[first_above_prev]` over `acs_first` of the current state ran 146.2 s of 180 s on CI (8.3 s locally) and was replaced by the guard. Premises (approved): `TimedRows.decide` went; the fault bound left `RecoveryClaim`, `Conductor.recovery`/`recovery_sharp`, the contract instances and the composed `LivenessClaim`/`CensorshipClaim`, where it had become unused; it enters through the configuration and the median theorem ([PaperAlignment.md](PaperAlignment.md) §5.10). Conductor sweep 205 → 193 cells, solved cold; slowest 3.6 s locally (`enter_window × bounded_tail`, `open_slot × open_prefix_agreement`), the three historically slow cells 3.6 s, 3.3 s and removed. K4–K8 and the composed witness re-proven (its first slot is `Cadence.medianOf` of the ideal ACS's set). Warm re-validation of the merged head (every project olean deleted) `JOBS=8`, 874 s. |
| — | exit 0 | 0 | 7 734 | **The MVBA's timeout view check at the receivers** (2026-10-08, branch `worktree-r38-mvba-timeout-check`, session R38, stacked on R36b; [Locality.md](Locality.md) §4.2, B4). The supplement states the receiver's rule: a prepare certificate carried by a timeout "contributes to `highPrepQC` only if it is itself valid for the same slot and its view is no greater than the view of the timeout message carrying it" (Supplement, Section 1.3 (`subsec:mvba-correctness`); Supplement, Algorithm 1, line 4 (`line:mvba:derived`)). Lars's option A: `byz_timeout_qc` drops `vord.le w v`; the timeout-certificate rules, correct (`form_own_tc_*`) and Byzantine (`byz_form_tc_*`), read a member carrying a certificate above the view as `⊥` (the lock rule's member condition gains `∨ v < W`, the lock-free rule accepts such a member); `tc_lock_backed` and `tc_nolock_backed` follow; `timeout_qc_view_le` holds of correct senders only, and the two lock-persistence manual cells use it to exclude the new disjunct at the honest intersection member. Liveness: `exists_dominating_timeout` sorts each member's pick into `⊥` or a certificate of view `≤ v`, so the lock rule's `w ≤ v` comes from the selection rather than the invariant. No invariant added: `#veil_status Mvba` stays 1649 (29 × 55 + 54), Chorus unchanged (its model and contract untouched). The cold solve put `sync_view_adopt × local_prepqc_within_entered` at 53.6 s and `× prepqc_blocks_lower_commits` at 25.5 s; both are manual cells now (frame steps, ~0.2 s). NoLock takes the same member condition in its verbatim `form_own_tc_lock` and keeps its pinned counterexample under `(sequential := true)`: none of its timeouts carries a certificate above its view, so the reachable graph is unchanged. Cold `JOBS=8` re-validation 261 s, warm (project oleans deleted) 902 s, both green. |
| — | exit 0 | 0 | 7 950 | **Chorus vote validity at the receivers; no B4 guard remains** (2026-10-09, branch `worktree-r39-chorus-vote-receivers`, session R39; [ChorusDesign.md](ChorusDesign.md) §3.5.3, [Locality.md](Locality.md) §4.2). Design first, approved by the verification coordinator for Lars. The paper states both checks in its vote handler (Algorithm 4 (`alg:fast-path-certification`), the vote handler; `tryIngestChunk` and `tryIngestShare`, Algorithm 6 (`alg:da`)): a vote counts only if it has an entry for every proposer, each positive entry carries the chunk with the sender's index, and the share verifies. `byz_cast_vote` and `byz_sign_vote_pos` drop their guards; the new broadcast relation `msg_vote_chunk r j m` is the chunk a vote carries, written by `vote` and by the new unfair `byz_carry_vote_chunk`; the ghost `vote_valid` is the receiver's check, read by `receive_vote_*` and `fb_sign_pos`. `aggregate_fastqc_*` keeps its signature check, a change to the kick-off's plan: a FastQC is also adopted from a `FastBlock` or a fallback vote on its signatures alone. `chunk_quorum` counts carried chunks, so the internal claim `Chorus.local_committed_pos_implies_decodable` states that `f+1` validators broadcast their chunk (`msg_vote_chunk`) where it said they held it. `vote_cast_entries` became `vote_cast_valid` (correct senders) and the receipt invariants carry `vote_valid`. No timing row, Owed condition, premise or contract changed. Pin 6215 → 6326 (56 · 111 + 110); 17 manual cells for every cell over 15 s in the cold solve, 4 frame cells removed. Cold Chorus family 231 s after the 820 s model build (✅ 6 284, no ❌/💥/⏱); full warm re-validation, every project olean deleted: exit 0, 975 s, peak 20.3 GB, ✅ 7 950 / ❌ 0 / 💥 0 / ⏱ 0 / ♻ 750, no warnings. Monitor suites ALL PASS. After R39 the adversary is constrained only by B1–B3. |

Three readings that entries above have **superseded**, spelled out because
they were true when written and are false now: Chorus once persisted
`sorryAx` statement stubs (retired in 25 — a VC now either has a real proof
or is reported as missing by `#veil_status`); the solver was once trusted
by default (retired in 16–17 — see "SMT trust mode" below); and the
`Bool → Prop` witness fold of 27–29 no longer exists (the fork stopped
carrying it in the 2026-09-01 entry, so `Vote.lean` no longer disables it
and the cell that diverged under the folded query shape solves normally).

## Build #10 — paper-alignment refactor

Triggered by reviewing the model against the public-preview paper
(`papers/cadence`). The paper's finalization rule and its agreement proof
(`prop:agreement-entries`) made the Build #4 "model fidelity concession"
unnecessary; the fallback-path guard and two whole properties (proposal
inclusion, hiding) were missing. Change inventory:

**Commit rule (fidelity fix).**
* `commit_assign_pos/neg` now require a *commitment proof*: a commitQC
  certificate (`commitqc_pos/neg` ghost — 2f+1 matching **broadcast**
  commit votes) or an MVBA decision. Previously a validator finalized on
  its own FastQCs, i.e. the paper's *speculative* commit was treated as
  final.
* The MVBA-consistency preconditions on `aggregate_fastqc_*` and the
  honest-state gates on `mvba_decide_*` (the Build #4 concession) are
  **removed**. Agreement is re-proven by the paper's asynchronous quorum
  argument: commitQC∩commitQC via `supermajorities_intersect_in_honest`
  + `commit_pos_sig_unique`; commitQC∩MVBA via the decision's recorded
  evidence (`mvba_decided_pos_backed`) — vote-supermajority evidence
  meets the commitQC in an honest double-voter, fallback evidence
  carries `fbcert`, which meets the commitQC in an honest validator
  violating the `pathVote` exclusion
  (`commit_cast_fallback_sig_excl`).
* The dead `local_commitqc_*` relations and their actions are deleted;
  transferable certificates (FallbackQC, EquivCert, FBCert) are
  `ghost relation`s over the signature state, and the commitQC
  additionally has a broadcast network form (`msg_commitqc_pos/neg`,
  assembled by `broadcast_commitqc_*` — the paper's
  `line:fast-broadcast-commitqc`) that finalization consumes.

**MVBA oracle (fidelity fix).**
* External validity is certificate-checkable (`vote_quorum_*`,
  `fb_quorum_*`, `equiv_evidence`, with `fbcert` required for
  fallback-shaped entries) instead of referencing honest validators'
  internal FastQC state.
* Both of the paper's invocation triggers are modelled
  (`mvba_invoked = fbcert ∨ ∃ honest complete_fast_metablock`); the
  case-(a) trigger is load-bearing for liveness in the mixed regime
  (see `ChorusDesign.md` §7).

**New guards (fidelity fixes).**
* `fb_sign_pos/neg` carry the paper's "received ≥ 2f+1 votes" guard
  (`line:fb-pathvote-guard`) as a witnessed supermajority of
  `msg_vote_cast`; `fb_sign_neg`'s complement condition is relative to
  the witnessed quorum, not global.
* Byzantine actions mirror receivers' validity checks:
  `byz_sign_vote_pos` requires the signer's chunk, `byz_cast_vote`
  requires per-proposer entries, `byz_sign_fb_pos` requires σ_p
  (`msg_proposer_signed`).
* EquivCert is `equiv_evidence` = two proposer-signed distinct roots
  (matches the certificate's content; the old `record_equivcert`
  required two *honest* fallback signers — stronger than the paper).

**New properties.**
* `proposal_inclusion` / `proposal_inclusion_no_neg` — censorship
  resistance relative to the `all_honest_recorded` premise, with an
  8-invariant inductive support chain.
* `hiding_until_deadline` — the slot key (f+1 shares) is not
  reconstructible pre-deadline; `msg_decrypt_share` is no longer dead
  state. Crypto half stays axiomatised in `Cadence/Primitives.lean`.
* `speculative_agreement_pos` / `_pos_neg` — the paper's
  speculative-finality claim, conditional on `no_equivocation`, via the
  `local_fb_neg_qv` history variable and its witness-invariant family
  (`fb_neg_sig_has_witness`, `fb_neg_qv_backed`,
  `fb_neg_qv_no_pos_quorum`, `fb_neg_no_pos_quorum`).

**ByzNodeSet.** Three counting axioms added to the class and proven for
`byzNodeSetFin` (`Veil/Frontend/Std.lean`):
`supermajority_contains_honest_greater_than_third`,
`supermajority_greater_than_third_intersect`,
`supermajorities_intersect_in_greater_than_third`.

> **Superseded (2026-09-25).** The three facts moved out of Veil ahead of the
> upstream re-port: they are now Cadence's own class
> `Cadence.ByzNodeSetCounting` (`Cadence/QuorumCounting.lean`), proven in
> `Cadence/ByzQuorum.lean`, with the fields renamed
> `honest_third_in_supermajority`, `supermajority_meets_third` and
> `supermajorities_share_third`.

**Liveness scaffolding.** `decrease_*` tautologies removed (the (D)
obligation is structural — see `ChorusDesign.md` §7); `progress_commit_*`
family replaced by `fast_path_implies_vote_quorums`,
`fastqc_complete_implies_mvba_evidence`, `progress_fallback_signing`;
(A-mvba) restated over `mvba_invoked`. The evidence pigeonhole for the
all-fallback branch remains deliberately meta-level (set comprehension
is outside `ByzNodeSet`'s language).

**Verification-driven fixes.** The sweep surfaced four model gaps, each
closed at the paper-faithful spot:
* `record_chunk` now requires `is_proposer j` (the paper's
  `tryIngestChunk` rejects chunks from non-proposers) — a missing check
  the SMT counterexample found.
* Scoping invariants pin protocol artefacts to proposers, excluding
  unreachable non-proposer states from the inductive state space:
  `fb_sig_is_proposer`, `fb_neg_qv_is_proposer`,
  `mvba_decided_is_proposer`; `voted_entry_pos_signed` gained an
  `is_proposer` antecedent.

**Verification engineering.** Three interventions were needed to get the
sweep green, all documented inline:
* `synthInstance.maxHeartbeats/maxSize` + `maxRecDepth` raised before
  `#gen_spec`: the `LocalRProp` instance over the ~91-conjunct
  `Invariants` clump exceeds the default budgets, and without its
  pre-simplification every VC re-simplifies the full clump (the first
  sweep attempt burned 9+ CPU-hours before being killed; with the fix a
  full sweep is ~45 min wall).
* CommitQC certificates are materialised as broadcast network relations
  (`msg_commitqc_pos/neg` + `broadcast_commitqc_*` assembly actions,
  mirroring the paper's `line:fast-broadcast-commitqc`) rather than
  `∃`-quorum ghosts in `commit_assign_*` preconditions; likewise
  `fb_sign_neg`'s witnessed quorum is recorded in the auxiliary history
  variable `local_fb_neg_qv`. Both keep deep quorum reasoning at single
  actions with explicit witnesses instead of in every consumer VC —
  the `∃`-ghost formulations sent cvc5's e-matching into timeouts.
* 11 VCs — each needing one or two explicit `ByzNodeSet` counting-axiom
  instantiations against witnessed quorums at bulk-update or
  quorum-completing actions — are discharged by manual `@[veil]`
  theorems (Veil's interactive-discharger mechanism; stubs generated by
  the "insert theorem stubs" suggestion, placed *after*
  `#check_invariants` so the VCs exist when the attribute registers).
  The proofs project the needed conjuncts out of the assembled
  `Invariants` hypothesis by declaration-order index — reordering
  declarations requires re-indexing them.

**Known elaboration note.** `veil.smt.timeout` is raised to 300s for the
sweep; `#gen_spec` warnings about deprecated `String.next` come from the
Smt dependency, not this model.

## Build #1 failure table (baseline)

All failures were `Counterexample (WP)` / `Counterexample (TR)` pairs.
Action arguments are the SMT witness (typically degenerate `i=j=m=s=0`).

| Action | Failing invariant | Root cause |
|---|---|---|
| `vote_pos` (`i=0, j=0, m=0, s=0`) | `vote_pos_from_local` | invariant required `voted R S`, but `vote_pos` only sets `vote_pos_sig`; `voted` is set later by `finalize_vote`. |
| `vote_neg` (`i=0, j=0, s=0`) | `vote_neg_from_local` | same mismatch — `voted R S` is set in `finalize_vote`, not `vote_neg`. |
| `aggregate_fastqc_pos` (`s=0, j=0, m=0, q=0`) | `fastqc_pos_unique` | needs quorum-intersection over two supermajorities of `vote_pos_sig` for distinct roots. Missing "backing-quorum" auxiliary linking `fastqc_pos` to a supermajority of `vote_pos_sig`. |
| `aggregate_fastqc_pos` (same) | `fastqc_pos_neg_excl` | same root cause: needs `fastqc_neg` to be backed by a supermajority of `vote_neg_sig` so the intersection argument applies. |
| `aggregate_fastqc_neg` (`s=0, j=0, q=0`) | `fastqc_pos_neg_excl` | dual: needs `fastqc_pos` to be backed by `vote_pos_sig` for the intersection lemma to fire. |
| `commit_assign_pos` (`i=0, j=0, m=0, s=0`) | `integrity_pos` | action set `committed_pos i s j m := true` without requiring no other `committed_pos i s j m'` (m'≠m). |
| `commit_assign_pos` (same) | `integrity_pos_neg` | also missing `require ¬ committed_neg i s j`. |
| `commit_assign_pos` (same) | `committed_pos_unique` | same as `integrity_pos`. |
| `commit_assign_pos` (same) | `committed_pos_neg_excl` | same as `integrity_pos_neg`. |
| `commit_assign_neg` (`i=0, j=0, s=0`) | `integrity_pos_neg` | action set `committed_neg i s j := true` without requiring `¬ committed_pos i s j _`. |
| `commit_assign_neg` (same) | `committed_pos_neg_excl` | same as above. |
| `finalize_commit` (`i=0, s=0`) | `agreement_pos` | cross-validator agreement on positive committed roots. |
| `finalize_commit` (`i=1, s=0`) | `agreement_pos_neg` | cross-validator agreement between positive and negative decisions. |

## Build #3 failure table

| Action | Failing invariant | Counterexample analysis |
|---|---|---|
| `aggregate_fastqc_pos` (`j=0, m=1, q=0, s=0`) | `fastqc_mvba_pos_consistent` | Pre-state has `mvba_decided_pos[s=0,j=0,m=0]` and `vote_pos_sig[r=0,s=0,j=0,m=1]` (with degenerate supermajority `{0}`). Aggregating `fastqc_pos[s=0,j=0,m=1]` succeeds, but the post-state then has both `mvba_decided_pos m=0` and `fastqc_pos m=1`. The MVBA precondition `∀ m', fastqc_pos s j m' → m = m'` was satisfied at decision time (no FastQC yet), but is not stable under later FastQC aggregation. |
| `aggregate_fastqc_pos` (same) | `fastqc_pos_mvba_neg_excl` | Symmetric: an MVBA negative decision can be made when no positive FastQC has yet been aggregated; later aggregation breaks the invariant. |
| `aggregate_fastqc_pos` (same) | `fastqc_neg_mvba_pos_excl` | Symmetric. |

### Root cause

In the actual Cadence protocol, this is prevented by the
*partial-synchrony timing*: by the MVBA arm time `Ds + 2Δ`, any
FastQC that *could* be aggregated *would* be observed by every MVBA
validator in time to influence the decision (bounded message delay
after GST). Our async-conservative monotone model has no such timing
argument, so the action `aggregate_fastqc_pos` is free to fire after
`mvba_decide_pos`, creating a post-state in which an MVBA decision
for `m=0` and a FastQC for `m=1` coexist.

A pure quorum-intersection argument would require an axiom about
"supermajority + greater-than-third quorums sharing an honest node"
which is *not* derivable from the standard `ByzNodeSet` axioms (see
`Veil/Frontend/Std.lean:365` — only `supermajority + supermajority`
and `greater_than_third → ≥1 honest` are provided). The set sizes do
intersect (`(2f+1) + (f+1) - (3f+1) = 1`) but that single overlap
node could be the one Byzantine validator, so the lemma is in fact
*false* in general.

### Fix 5 — model-fidelity concession

Strengthen `aggregate_fastqc_pos` / `aggregate_fastqc_neg` with
MVBA-consistency preconditions:

```
action aggregate_fastqc_pos (s j m q) {
  …
  require ¬ mvba_decided_neg s j
  require ∀ m', mvba_decided_pos s j m' → m = m'
  …
}

action aggregate_fastqc_neg (s j q) {
  …
  require ∀ m, ¬ mvba_decided_pos s j m
  …
}
```

This is a **deliberate model fidelity concession**: in the real
protocol, FastQC aggregation is unilateral observation, not
coordination. We are encoding the partial-synchrony safety
implication directly into the model. The alternative options
considered were:

* **Strengthen MVBA preconditions** to forbid "could-be FastQC"
  (`∀ m' q, m' ≠ m → ¬(supermajority q ∧ ∀ r ∈ q, vote_pos_sig r s j m')`).
  More faithful to protocol intent, but non-EPR and likely
  SMT-heavier; also potentially unsound under monotone Byzantine
  vote growth (Byzantine validators can sign vote_pos_sig for many
  `m` via `byz_step`, potentially completing a `supermajority` for
  `m'` after MVBA has decided).
* **Phase-marker fix**: `require ¬ past_mvba_arm s` in `aggregate_fastqc_*`.
  Cleanest semantics but eliminates the model's representation of
  late aggregation entirely.
* **Sorry / unproven**: demote the 3 invariants and accept
  `agreement_pos` / `agreement_pos_neg` as conditional. Honest but
  doesn't verify safety.

The chosen fix is the lightest weight option that gets `safety` to
pass. ~~The concession is recorded in `ChorusDesign.md` §3 and §10 so that
future model-fidelity work has a clear pointer.~~

> **Superseded in Build #10.** The concession rested on the belief that
> the protocol's cross-path safety needs a partial-synchrony timing
> argument. The published paper's `prop:agreement-entries` shows it does
> not: with the *actual* finalization rule (commitQC or MVBA
> certificate), cross-path agreement is a pure quorum argument through
> the `pathVote` exclusion and the `FBCert` that every fallback
> meta-block carries. Build #10 adopts that rule and removes the
> concession; the analysis above is kept for the historical record.

## Build #2 failure table

| Action | Failing invariant | Counterexample analysis |
|---|---|---|
| `finalize_commit` (`i=0, s=0`) | `agreement_pos` | Pre-state has `committed_pos[i=0, s=0, j=0, m=0]` and `committed_pos[i=1, s=0, j=0, m=1]` (validator 1 already committed). After `finalize_commit(i=0, s=0)` both validators are committed but disagree on `m`. The pre-state is admitted because `mvba_decided_pos[s=0, j=0, m=0]` and `mvba_decided_pos[s=0, j=0, m=1]` both hold — i.e., we don't yet have a `mvba_decided_pos_unique` invariant. |
| `finalize_commit` (`i=0, s=0`) | `agreement_pos_neg` | Same family — needs MVBA-vs-FastQC and MVBA-vs-MVBA exclusion. |

## Fixes applied (cumulative)

1. **Weakened `vote_pos_from_local` / `vote_neg_from_local`** to drop the
   `voted R S` conjunct. The protocol intentionally permits signing
   individual per-proposer entries before `finalize_vote`; the
   "`voted ↔ all proposers signed`" link is captured by `finalize_vote`'s
   precondition.

2. **Strengthened `commit_assign_pos` / `commit_assign_neg`** with
   intra-validator exclusion preconditions:
   - `commit_assign_pos`: `require ∀ m', committed_pos i s j m' → m' = m`
     and `require ¬ committed_neg i s j`.
   - `commit_assign_neg`: `require ∀ m, ¬ committed_pos i s j m`.

3. **Added backing-quorum auxiliaries** (non-EPR, mirrors
   `voted_requires_echo_quorum_or_vote_quorum` in
   `Examples/Ivy/ReliableBroadcast.lean`):

   - `fastqc_pos_backed`:
     `fastqc_pos S J M → ∃ q, supermajority q ∧ ∀ r ∈ q, vote_pos_sig r S J M`.
   - `fastqc_neg_backed`:
     `fastqc_neg S J → ∃ q, supermajority q ∧ ∀ r ∈ q, vote_neg_sig r S J`.

4a. **Added MVBA uniqueness + cross-path consistency invariants** (Build #3).
   The MVBA `require` clauses enforce these properties at firing time,
   but they were not exposed as invariants so the inductive check on
   downstream actions (`commit_assign_pos`, `finalize_commit`) could not
   use them:

   - `mvba_decided_pos_unique`:
     `mvba_decided_pos S J M1 ∧ mvba_decided_pos S J M2 → M1 = M2`.
   - `mvba_decided_pos_neg_excl`:
     `¬ (mvba_decided_pos S J M ∧ mvba_decided_neg S J)`.
   - `fastqc_mvba_pos_consistent`:
     `fastqc_pos S J M1 ∧ mvba_decided_pos S J M2 → M1 = M2`.
   - `fastqc_pos_mvba_neg_excl`:
     `¬ (fastqc_pos S J M ∧ mvba_decided_neg S J)`.
   - `fastqc_neg_mvba_pos_excl`:
     `¬ (fastqc_neg S J ∧ mvba_decided_pos S J M)`.

5. **Strengthened `aggregate_fastqc_*` with MVBA-consistency
   preconditions** (Build #4). See the "Build #3 failure table"
   above for the detailed root-cause analysis and the rationale for
   choosing this option over the alternatives.

## Per-action ✅/❌ summary (Build #2)

Actions with **zero** failures (passed all 21 invariants):

```
advance_to_deadline  advance_to_fb_arm    advance_to_mvba_arm
propose              record_chunk         vote_pos
vote_neg             finalize_vote
aggregate_fastqc_pos aggregate_fastqc_neg
aggregate_fallbackqc_pos  aggregate_fallbackqc_neg
fb_sign_pos          fb_sign_neg          cast_fallback_vote
commit_sign_pos      commit_sign_neg      cast_fast_commit
aggregate_commitqc_pos    aggregate_commitqc_neg    finalize_commitqc
record_equivcert     aggregate_fbcerts
mvba_decide_pos      mvba_decide_neg      mvba_terminate
commit_assign_pos    commit_assign_neg
byz_step
```

The only action with failures after Build #2 is `finalize_commit`
(`agreement_pos`, `agreement_pos_neg`). After Build #3, this is expected
to clear.

## Modelling contract — load-bearing assumption

The async-soundness argument in [`ChorusDesign.md`](./ChorusDesign.md) §3.2 relies on
the **network relations** of `Cadence/Chorus.lean` being consulted only in
*positive position* — both in action preconditions and in update
right-hand sides. This includes subtler negative patterns:

* literal `¬R(…)` in preconditions;
* universal-over-relation `∀ R, R(…) → P(R)` (which is a `¬ ∃` in
  disguise);
* `if-then-else` whose `else` branch fires on `¬R`;
* update expressions of the form `X := if R then a else b`.

This is **not** enforced by Veil. If a future edit violates it, the SMT
proofs may still discharge but the simulation from monotone → async
silently breaks and the safety claim ceases to be a claim about
asynchronous networks. See `ChorusDesign.md` §3.1.1 for the contract.

The list of network relations covered by the contract is in
`ChorusDesign.md` §3.1; the audit confirmed (as of Build #10) that all
preconditions and updates in `Cadence/Chorus.lean` respect it, with one
**documented scoped exception**: `fb_sign_neg`'s complement guard
negates vote signatures *within its witnessed quorum parameter `qv`*
only — the model-level rendering of "no positive quorum among the
votes this validator received", which a real validator can observe.
See `ChorusDesign.md` §3.1.1 for why this preserves the simulation.

> **Superseded (2026-08-19).** The 2026-08 external audit re-ran this
> hand audit and found its enumeration incomplete: seven further
> negative reads exist (`propose`'s guard on its own
> `msg_proposer_signed` row, and `¬ msg_commit_cast i` in six actions),
> all sound for a *third* reason the documentation did not then name —
> **self-row reads**, of a row indexed by and writable only by the
> acting validator. The contract's conclusion stood; the audit table
> and the §3.1.1 exception set in `ChorusDesign.md` now record all
> three categories.

A useful future addition is an **automated syntactic audit** — a small
Lean meta-program or external script that walks each action's AST and
flags negative occurrences of any relation declared as "network". This
is tracked here so the next iteration doesn't lose context.

## Tooling

[`Cadence/Tooling.lean`](../Cadence/Tooling.lean) provides two project-local
Veil commands: `#check_invariant <name>` (one invariant × all actions) and
`#check_vc <action> <invariant>` (a single cell). Useful for tight inner-loop
iteration without re-running the full sweep. They are small and orthogonal to
the rest of the framework, and would be worth upstreaming. (Veil itself has
since gained *cross-file* forms with an extra module argument — `#check_vc
<Module> <action> <property>` — which do not collide with these.)

## Open items / future iterations

Kept for the record; the current, maintained list is
[`TODO.md`](./TODO.md) and [`ChorusDesign.md`](./ChorusDesign.md) §9.
Tool-level observations are not tracked here — see
[`Dependencies.md`](./Dependencies.md).

* `assumption` cannot be used to axiomatise `mvba_decided_*` properties
  because they are mutable state, not immutable parameters. This is
  documented in the source. We use action preconditions + lifted
  invariants instead.
* Liveness: the fair-progress layer was rewritten in Build #10 for the
  commitQC finalization rule — see `ChorusDesign.md` §7 for the current
  three-branch case split (`x ≥ 2f+1` commitQC / mixed case-(a) MVBA /
  all-fallback FBCert), the meta-axioms ((F-justice), (F-byz),
  (A-mvba) over `mvba_invoked`), and — at the time this was written — the
  deliberately meta-level evidence pigeonhole. **That last part is
  superseded**: the pigeonhole is a theorem for every `n = 3f+1` in
  `Cadence/Chorus/Pigeonhole.lean`. Full liveness-to-safety remains future
  work — see [`Liveness.md`](./Liveness.md).
* The `LocalRProp` simplification warning at `#gen_spec` (Build #10) is
  benign but worth upstreaming a fix for: the pass does not handle the
  ghost-relation-heavy invariant clump.
* Instantiate the whole module against concrete finite types (via
  `byzNodeSetFin`) to demonstrate end-to-end satisfiability of the
  axiom set (tracked as [`ChorusDesign.md`](./ChorusDesign.md) §9 item 1; also
  guards against a vacuous safety claim — [`TODO.md`](./TODO.md),
  "Soundness"). Still open, and still the highest-value remaining item.

## Why we disabled `veil.gen.modelCheckScaffolding`

We set `set_option veil.gen.modelCheckScaffolding false` in
[`Cadence/Chorus.lean`](../Cadence/Chorus.lean) before `#gen_spec`. The underlying
reason is that the label-enumeration instances Veil derives for
`#model_check` are `O(nᵏ)` in the number of actions; at 38 actions they
exceed Lean's reducer, so `#gen_spec` cannot elaborate at all with them on
(Builds #4–#5 above). The same argument makes `#model_check` unattractive
for BFT-shaped protocols in general at the quorum sizes that matter.

For this project: the effect on safety verification is none —
`#check_invariants` and `#check_action` remain fully supported.
`#model_check` becomes unavailable, which we would not have been
able to use at meaningful quorum sizes anyway.

## SMT trust mode

**Superseded — this section describes Builds #1–#15 only.** At that time the
solver was trusted (`veil.smt.trust = true`) and a ✅ meant "cvc5 returned
`unsat` and we believe it". Since Build #16 (2026-07-10) every module in this
repository elaborates with `veil.smt.trust false`: each discharge reconstructs
a proof term that Lean's kernel re-checks, so a ✅ means "kernel-checked".
The cost of that switch — roughly 2× the CPU of a trusted sweep, and a
reconstruction proof term per VC that has to be persisted somewhere — is what
drove the per-action file layout (Build #18) and the proof cache (#19–#24).

## Notes moved out of the current documentation (2026-09-29)

The 2026-09-29 documentation pass rewrote the Lean comments and `docs/` in the
present tense. These facts about how things got here were in that text, and
are kept here instead.

* **Precompiling on the older pins.** Before the 2026-09 re-port,
  `precompileModules` also failed on Loom's `CaseStudies` library, which
  globbed `Loom.*` and carried broken `NonDetT.Extract` imports — worked
  around with a lakefile-only Loom fork, since dropped — and on
  `Loom/MonadAlgebras/WP/Gen.lean`, whose body was commented out.
* **`#veil_status` cost.** `#veil_status Chorus` took about 40 s before
  oleans stored per-declaration axiom sets, and about 2 s after.
* **The cheap rung and the cache.** A warm suite before the rung reported
  over 22 000 cache replays; after it, the cache held 2 990 entries, the
  solver-touched cells only.
* **Counting facts.** The Veil fork carried the three quorum-counting facts
  as `ByzNodeSet` fields before they became theorems of
  `Cadence.ByzNodeSetCounting`.
* **Contract-instance step facts.** `Chorus/Compose.lean` provided the
  `Inhabited` state instance by hand, and the contract instances proved each
  frame and monotonicity fact with a 38-case `cases l` script per field,
  before Veil generated those lemmas.
* **Solver configuration.** For a while the solver configuration was
  mis-measured because `set_option … in #check_invariants` is captured at
  `#gen_spec`, not at the command (Build #12).
* **The MVBA referent.** The paper-repository pin in `Cadence/Mvba.lean`
  was re-checked against `b838e17` on 2026-09-14: the 19 commits in between
  rewrite the practical Conductor instantiation and its recovery layer and tag
  Chorus's proposer signatures, none of it in the model's scope, and leave the
  modelled sections byte-identical.
* **Mvba traces.** The `sat trace` witnesses gained a step when the view
  timer became an explicit action (`expire_timer`).
* **Mvba budgets.** Adding `entered_needs_certificate` pushed the Mvba proof
  family past the default elaboration budgets, which is why its proof files
  carry `veil_large_clump_budgets`.
* **Chorus `fb_sign_neg`.** Its proof file carried three manual
  theorems (against `inclusion_no_honest_fb_neg`, `fb_neg_qv_no_pos_quorum`
  and `fb_neg_no_pos_quorum`) until 2026-08-19: under the pre-`well_encoded`
  guard those queries diverged. After the `well_encoded` refactor (audit
  Finding 1) cvc5 solves them directly — 6.2–17.0 s on a workstation,
  52.8–62.5 s on CI's 4-core runner, which is what raised the proof families'
  budget from 60 s to 180 s on 2026-09-10.
* **Chorus decision handlers.** The two manual cells of each of
  `Chorus/Proofs/OnMvbaDecidePos.lean` and `OnMvbaDecideNeg.lean` were ported
  on 2026-09-10 from the retired oracle actions `mvba_decide_pos` /
  `mvba_decide_neg` (MvbaPlan §6), with only the `intro` pattern changed.
* **Doc comments on Veil declarations.** Until the Veil pin gained
  `port/doc-comments` (merged into this project's pin `73fa6fd4`), a
  `/-- … -/` before a Veil `safety`, `invariant` or `action` failed to parse,
  so every model declaration was explained in a plain `/- … -/` comment. This
  pass converted them to doc comments.

## Records moved out of the living documents (R33)

Session R33's documentation pass rewrote the living documents in the
present tense. The plan, staging and session records they carried, and the
figures they superseded, are kept here, verbatim except that bare section
references are qualified with the document they point into. Each block says
where it came from.

### From TODO.md: refactors explored and deferred

#### Atomic-action candidates

The atomic-action pattern was applied successfully to `vote`. Four
analogous candidates were *not* applied:

| Candidate | Status | Reason |
|---|---|---|
| `cast_commit` = `commit_sign_pos` + `commit_sign_neg` + `cast_fast_commit` | Deferred | A/B `#check_vc cast_commit agreement_pos` ran in 1420 s wall / 245 s user CPU. Most likely the wall-time blowup was discharger-scheduler contention rather than genuine SMT cost (245 s of CPU against 1 420 s of wall). With the `commit_pos_sig_unique` / `commit_pos_sig_neg_excl` invariants stated explicitly, a re-test via `#check_action cast_commit` (bundles VCs under one awaiter — less contention surface) is the right next experiment. If that's clean, integrate. |
| `fb_vote` = `fb_sign_pos` + `fb_sign_neg` + `cast_fallback_vote` | Not attempted | Bulk update body is more complex than vote/cast_commit because each per-proposer fb-sign decision depends on an *existential* quorum witness (`∃ q : nodeset, …`). Plausibly tractable as an atomic action but the quantifier shape is genuinely different. Worth its own A/B. |
| `commit` = `commit_assign_pos` + `commit_assign_neg` + `finalize_commit` | Not attempted | Same shape as `cast_commit`; touches `agreement_pos` directly. If the `cast_commit` re-test goes well, this is the natural next candidate. |
| `mvba` = `on_mvba_decide_pos` + `on_mvba_decide_neg` + `mvba_terminate` | Deliberately *not* wanted | The decision handlers transport a correct validator's decision off the abstract MVBA state entry by entry, which keeps every update a monotone `:= true` and lets `#gen_proof_files` map proof files one for one. A bulk transport of the whole vector would be one action with a `∀ J`-quantified update over the two projections: possible, but it trades the monotone-update shape for one fewer action. |

The pattern for each is the same as `vote`/`cast_commit`: replace the
three actions with one atomic action whose body has universally-quantified
bulk updates on the per-proposer signature relations, with auxiliary
uniqueness/exclusion invariants stated explicitly so cvc5 has direct
hypotheses instead of multi-step chains.

#### Measuring a candidate

Read the A/B numbers above with care: each `#check_vc` in them paid the
module's full DSL elaboration, and concurrent check commands contended for
one discharger scheduler, so fixed cost dominates them.

The recipe is to put `#prove_vc Chorus <action> <property> by …` cells in
a scratch file importing `Cadence.Chorus` — seconds per cell, since the model
elaborates once and the proof cache makes a statement-unchanged rebuild a
kernel replay. Prefer bundled measurement (`#check_action <action>`, many
invariants under one awaiter) over per-VC checks: it is closer to how the
action behaves in a full build.

#### Other ideas not pursued

* **Payload-carrying pos/neg pairs** (`local_entry_*`, `committed_*`,
  `mvba_decided_*`, `fastqc_*`, `fallbackqc_*`, `msg_*_sig`): would need
  a Lean inductive (`inductive Outcome | none | pos (m : merkle_root) | neg`)
  as the codomain of a `function`, since Veil's `enum` can't hold the
  merkle_root payload. Plausibly correct but unclear whether the SMT
  cost stays manageable — the per-VC cost change measured for the
  payload-free `phase`/`path` enums was within noise, but those have a
  qualitatively different encoding signature from payload-carrying
  inductives. Not pursued.
* **`procedure` for inductive decomposition**: investigated, but Veil
  `procedure`s inline at WP elaboration — same transition relation as
  inlining. They don't help SMT.

### From CLAUDE.md and Premises.md

* **A contract statement corrected, not weakened.** On the way to the
  temporal instances, `SlotConsensusTemporal.quiescence` (and
  `ACSTemporal.quiescence`) quantified over unreachable states, which was
  this project's mis-statement of a property about executions; it was
  corrected to the one-step form from a reachable state
  ([CompositionContracts.md](CompositionContracts.md) §5).
* **Staged suite timings** (CLAUDE.md until R33). Measured 2026-09-26
  (Veil on upstream `517f2bad`): a cold re-validation of the whole suite was
  19 min 58 s at `BATCH=3` (28 774 ✅ / 349 ♻, peak 13.0 GB), storing 792
  cache entries; a warm one, every project olean deleted and the cache kept,
  12 min 58 s at `BATCH=6` (peak 15.3 GB), of which 477 s was the three
  model rebuilds plus the root audit module. The cold figure grew from
  15 min 25 s (2026-09-10) with the workload (the MVBA from 725 to 1 325
  cells). Both are superseded by the JOBS mode
  ([scripts/revalidate.sh](../scripts/revalidate.sh)'s header). A single
  `lake build` of the suite printed about 5 350 ✅ at the time.
* **The warm-path figures** (CLAUDE.md until R33; their home is
  [Dependencies.md](Dependencies.md) § "Native shared libraries"): one
  Chorus proof file 39.7 s, about 400 ms of replay per cell; the Bool-atom
  fold took per-cell replay from 402 ms to 79 ms and a warm re-validation
  from 654 s to 389 s; `precompileModules` 654 / 688 / 702 s; the cheap rung
  closing 80–91 % of a Chorus proof file's cells.
* **The independence analysis's result** (Premises.md §7 until R33):

**Result (R21, acted on in R23).** Every premise of every claim in Premises.md §1 is
used, with three exceptions. One is kept by decision, and the other two
are gone from the claims' statements:

* **Unused: the timed MVBA claim's `Valid` antecedent.**
  `Mvba.timed_termination` (and so `Mvba.mvbaTemporal`'s `termination`)
  does not use "every correct validator proposes a `Valid` value": the
  model's `propose` checks validity itself. The antecedent is part of the
  contract field `MVBATemporal.termination`, Module 3 (`mod:mvba`)'s
  caller condition, which another implementation may need. *Kept*
  (decided 2026-10-03): it is the paper's caller condition; not used by
  this instance's proof.
* **Implied, and now derived: `ByzNodeSetHonestQuorum` in the timed
  Chorus claims at the system's MVBA.** `Chorus.timed_termination_atMvba`
  and `Chorus.timed_termination_tight_atMvba` took it as a hypothesis,
  but at the family they are stated at it is a theorem (`Chorus.hqeFin`).
  The two theorems derive it inside and no longer take it (R23).
* **Unused and implied, and now removed: the model assumption
  `leader_honest_cofinal`** ("above every view there is a correct-led
  one"). No proof of a claim in Premises.md §1 read it, and `LeaderRotation` (Premises.md §2.5)
  implies it. As a model `assumption` it was a conjunct of every reachable
  state's premises, so the MVBA's safety claims were stated for leader
  schedules with cofinally many correct leaders. R23 removed it from
  [Mvba.lean](../Cadence/Mvba.lean), together with its one reader
  (`Mvba.exists_honest_leader_above`, itself unused): the MVBA's safety
  claims now hold for every leader schedule.

### From Bounds.md

*The plan and staging records of the MVBA and Chorus bounds legs, with the superseded designs and figures, moved out of [Bounds.md](Bounds.md) in R33. The section numbers are Bounds.md's at the time; the text is verbatim, with bare section references qualified.*

#### The frame and Bounds.md §1, as written during the legs

# Bounds — the paper's Δ-bounds and the model

*Design notes, not a description of what is proven. This document records
how the paper's concrete finite bounds relate to the model's theorems, why
the two are incomparable rather than ordered by strength, and the routes by
which bounds could be brought into the model — including tooling
constraints observed in practice. The proven liveness state of affairs is
[Liveness.md](Liveness.md); the open-items list is
[TODO.md](TODO.md).*

## 1. What the paper proves, and how the model relates

The paper proves concrete finite bounds end-to-end, parametric in exactly
two assumed primitive bounds:

* **Chorus**: `ℓ`-termination with `ℓ = 5Δ + ℓ_MVBA`
  (Lemma 11 (`lemma:chorus-termination`)), via a deterministic post-GST timeline
  (Proposition 5 (`prop:chorus-finalization-time`), Proposition 4 (`prop:chorus-totality`)), conditional
  on *Δ-synchronized participation*
  (Definition 5 (`def:delta-synchronized-participation`)).
* **Conductor**: totality with `d_tot = Δ` (Lemma 15 (`lemma:conductor-totality`)),
  boundedness `𝓑 = 2W − p` and recovery `𝓡 = 2Wτ`
  (Theorem 2 (`thm:conductor-correctness`)); the composition closes non-circularly
  (Corollary 4 (`cor:chorus-correctness-within-cadence`)).
* **The parametric holes**: `ℓ_MVBA` (Module 3 (`mod:mvba`)) and the ACS's `ℓ`
  (Module 4 (`mod:acs`)) are *assumed module properties*, stated as deterministic
  bounds — an idealisation, since the randomised constructions satisfy
  them only in expectation / with high probability. The first hole is
  closed in this development: the MVBA instantiation of the paper
  repository's internal supplement is modelled
  ([Cadence/Mvba.lean](../Cadence/Mvba.lean)), `ℓ_MVBA` is the field `ℓ`
  of `MVBATemporal` ([Cadence/Interfaces.lean](../Cadence/Interfaces.lean)),
  and the instance `Mvba.mvbaTemporal`
  ([Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean)) proves the
  Termination it bounds — Supplement, Theorem 2 (`thm:termination`), `O(fΔ)` — over
  timed runs of the untimed model (Bounds.md §6.2).

The model relates to these in three distinct ways:

1. **Bound-free paper theorems** (agreement, slot safety, integrity, …)
   appear as the *same* theorems in the model.
2. **Timed-premise theorems** appear with the premise transported to its
   state-level consequence (proposal inclusion's `deadline − Δ ≥ GST`
   becomes the hypothesis `all_honest_recorded`; the liveness theorems'
   *saturation* hypotheses are the state consequences of what fairness
   delivers).
3. **The bounded statements themselves** are not model theorems at any
   abstraction level — they are fields of the full module contracts,
   stated over timed runs, and for the two implementations the fields of
   the `…Temporal` classes ((A-sc-termination), (A-acs-termination),
   (A-acs-totality), (A-orch-totality), (A-orch-boundedness),
   (A-orch-recovery); [Architecture.md](Architecture.md) §4 item 4,
   [Cadence/Interfaces.lean](../Cadence/Interfaces.lean),
   `OrchestratorTemporal`, `SlotConsensusTemporal`). What the
   model proves instead is the **bound-erased skeleton of their paper
   proofs**: each timeline milestone's state content is a theorem
   (saturation ⇒ dichotomy; buildability; certificate formation; the
   commit-round chain), and the Δ-arithmetic that orders the milestones
   in the paper is replaced by the named temporal assumptions that glue
   them in the model. Even inside the rows, the maximal state-shaped
   residue is extracted as a theorem (quiescence ↔ phase confinement;
   boundedness ↔ the interval-inclusion invariant, with the number
   `2W − p` a meta corollary).

#### Bounds.md §3 Routes to bounds in the model

## 3. Routes to bounds in the model

Three options, in ascending order of invasiveness; the first is the
preferred entry point, the last is taken only if the benefit is clear.

**(a) An add-on schedule theorem (no model change).** Mechanise
Lemma 11 (`lemma:chorus-termination`)'s *proof arithmetic* as a standalone plain-Lean
theorem over an abstract ordered time (an order plus an abstract
`+Δ`-successor; no `Real`, no Archimedean axiom — finite schedules need
neither): parameterise by one named per-seam bound assumption for each
temporal step of the chain ("this seam completes within Δ after GST",
"(A-mvba) within `ℓ_MVBA`"), take the chain's state theorems as the step
justifications, and conclude finalization by
`max(t, GST) + 5Δ + ℓ_MVBA`. This is the same treatment the unbounded
argument received — state content proven, temporal steps named — with the
schedule *composition* additionally kernel-checked. The gain is real if
modest: the paper's timeline arithmetic is exactly the kind of detail
that drifts (the `d_tot` bound changed `2Δ → Δ` between paper revisions),
and the theorem pins it. The per-seam `≤ Δ` facts remain assumptions —
they are the strong-partial-synchrony content itself.

**(b) A ghost clock in the model (Zeno-guard).** Add a monotone `now`
whose `tick` is guarded so that time cannot pass a deadline while an
obligated step is pending; bounded claims become sweep-shaped safety
invariants, and the temporal residue consolidates to fairness plus
non-Zenoness, whose state-level half (tick-enabledness in every reachable
state) is dischargeable like the existing enabledness content. Design
costs, all named: keep the time theory order-only (uninterpreted
monotone `laterΔ`, deadlines as ghost elements — mixed quantifiers with
arithmetic is where e-matching pain returns); route deadline bookkeeping
through ghost obligation relations so `tick`'s universal guard does not
read network relations negatively (the (M-frame) contract,
[ChorusDesign.md](ChorusDesign.md) §3.1.1); and guard vacuity — in
this encoding the bounded invariants are safe *by construction of the
guard*, so the theorems are the tick-enabledness results and the
non-vacuity witnesses that `now` exceeds the interesting thresholds.
Estimated bill at Chorus scale: a tick action, deadline ghosts on ~10
actions, 10–15 timing invariants — roughly +600–800 VCs, inside the
demonstrated envelope. If taken, stage it Conductor-first: Conductor
already carries an abstract monotone `now` with a clock-guarded `open`,
and the paper's own decomposition puts the timing in the orchestrator.

**(c) A full timed refactor or a timed overlay model.** A second, timed
model with a simulation to the untimed one re-raises the embedding cost
for little audit gain; a full refactor of Chorus is justified only if the
model would become *simpler* — which nothing currently suggests. Both
deferred absent a clear benefit.

#### Bounds.md §4 Tooling constraints (recorded from practice)

## 4. Tooling constraints (recorded from practice)

Observed while building a Veil model of a different, inherently timed
protocol. They are recorded here so that they inform the decision above;
tool-side work belongs in the Veil fork, not in this repository.

* Veil has no support for `Real` time, although the SMT solvers and Lean
  itself would allow it. Workable substitute: time as an abstract ordered
  structure (there, an ordered Archimedean field; for the uses above, an
  order with an abstract `+Δ` suffices — Archimedean-ness is only ever
  needed for divergence, which stays meta regardless).
* Veil does not handle Mathlib's universe polymorphism, which blocks
  pulling in Mathlib's ordered-field theory directly. Upstream Veil work
  may address this; maturity and timeline unclear.
* A viable escape hatch exists: disable SMT and prove all VCs in plain
  Lean. For that (much simpler) protocol this was efficient — most VCs
  were one-liners. It is **not** an attractive route for Chorus, whose
  combinatorial/discrete core (quorum reasoning at the scale of
  [Architecture.md](Architecture.md) §2) is exactly where SMT earns its
  keep.

None of these constraints bites route (a): the add-on schedule theorem is
plain Lean over an abstract order, outside the Veil pipeline entirely.

#### Bounds.md §5 Recorded decision

## 5. Recorded decision

Beyond the MVBA's `ℓ_MVBA` (Bounds.md §6.2, proven), bounds are out of scope
([Architecture.md](Architecture.md) §4 item 4) until timing claims become a
priority; where they rank against the two items ahead of them in
[TODO.md](TODO.md) § Soundness is a call to make deliberately. When they do
go ahead: route (a) first — cheap, no model change, pins the schedule
arithmetic; route (b) Conductor-first if in-model timing is wanted, with
the three design costs above addressed up front; route (c) only against
demonstrated benefit. Ordering relative to the L2S extension (the fork's
`lars/liveness` branch) is decided then — the two are complementary, and
the ghost clock would incidentally hand L2S its simplest ω-target
(`infinitely_often tick`).

#### Bounds.md §6 Route (a): the worked plan, and Bounds.md §6.1 The MVBA leg (the plan)

## 6. Route (a): the worked plan

Recorded so a future session can pick this up without re-deriving the
design. Priority context: this ranks *behind* primitive instantiation and
the (M-frame) checker ([TODO.md](TODO.md) § Soundness) on
auditor-confidence per effort, and *ahead* of L2S on near-term
value-per-effort — it is executable today, entirely in plain Lean, with
none of Bounds.md §4's tooling constraints in play.

**Depth decision.** Prove the theorem over **real timed runs of the
generated transition system**, not over abstract milestone propositions.
A run is `σ : ℕ → State` stepping through the actual Chorus transitions
with a monotone clock `c : ℕ → T`, where `T` carries a linear order plus
two abstract inflationary monotone shifts (`+Δ`, `+ℓ_MVBA`) — no `Real`,
no Archimedean axiom, `max` from the order. Every run point is reachable,
so the chain theorems of [Liveness.md](Liveness.md) §1 apply at every
milestone state. The abstract-propositions variant is the fallback only:
it checks arithmetic an auditor can check by eye.

**Hypotheses.** One named per-seam bound assumption per temporal step of
the chain ([ChorusDesign.md](ChorusDesign.md) §7): "this seam
completes within Δ after GST" for the (F-justice) seams, `ℓ_MVBA` for the
oracle seam. These hypotheses *are* the strong-partial-synchrony content;
the design rule is that they stay minimal and checkable against the
paper's premises — a hypothesis that smuggles a conclusion voids the
exercise. Workshop the exact statements in this section before writing
Lean.

**Target statement** (Chorus leg): for every timed run satisfying the
per-seam assumptions in which all correct validators participate by `t`,
every correct validator finalizes by `max(t, GST) + 5Δ + ℓ_MVBA` — the
statement shape of Lemma 11 (`lemma:chorus-termination`), with
Proposition 5 (`prop:chorus-finalization-time`)'s milestone table (`M+2Δ`, `M+3Δ`,
`T−Δ`, `T`) as the internal schedule.

**Staging** (reassess after step 2; each step is one focused session,
give or take):

1. Scaffolding: timed runs over the generated transition system, the
   time theory, the per-seam assumption vocabulary.
2. Milestones `M+2Δ` and `M+3Δ` — mostly plugging the proven theorems
   (saturation, `build_totality_of_reachable`, the definitional
   aggregation witness). This validates the scaffolding cheaply.
3. The MVBA tail, the commit round, and the two-case termination lemma;
   axiom pins at the standard trio; docs. Watch for per-validator
   "holds-by-time" content that may need one or two new invariants
   (a model change and cold re-solve — a known ~20-minute event).
4. Conductor: `d_tot = Δ` totality, the window induction, `2W − p`
   boundedness, `2Wτ` recovery.
5. The composition: Corollary 4 (`cor:chorus-correctness-within-cadence`) and the
   alternating-window non-circularity — the subtlest statement work and
   the highest-value single piece.

### 6.1 The MVBA leg

*Complete: Bounds.md §6.2 is the design as carried out, and Bounds.md §6.2.8 the record of each
step. This subsection is the plan it started from, kept for the argument.*

Step 3 above treats `ℓ_MVBA` as a **per-seam hypothesis** — "the oracle seam
completes within `ℓ_MVBA`". The MVBA's liveness theorem
(`Mvba.termination`, [Liveness.md](Liveness.md) §2.1) makes a second leg
available: *prove* `ℓ_MVBA` rather than assume it.

**Why it is tractable.** The untimed theorem was built so that this would be
the only remaining step. Every one of its five premises is a predicate on a
run, so a timed layer discharges them as ordinary Lean theorems over timed
runs of the same generated transition system — **no model change**, exactly
the depth decision of Bounds.md §6. Two of the five are immediate under any reasonable
timing model (the callers' premises are hypotheses either way), one is fair
scheduling, and the work is entirely in (A-viewsync)'s two clauses.

**What it needs that the Chorus leg does not.** The Chorus leg's time theory
is a linear order with two abstract inflationary shifts, because its schedule
is a fixed milestone table. The MVBA's is not fixed: the argument is that
*timeouts grow* until one view's budget exceeds the chain's latency, so the
time theory needs a **sequence** `Δ_v` unbounded relative to a fixed bound,
not two constants. That is the one genuinely new piece of arithmetic, and it
should be workshopped before any Lean, exactly as Bounds.md §6 says of the per-seam
statements. Do not assume this leg is cheaper than the Chorus leg because the
skeleton exists; it probably is not.

**What it buys, and why it may still rank first.** It is the only piece of
the bounds work that *removes an assumption* rather than attaching a bound to
one. (A-viewsync) is the strongest premise of the liveness result and the
only one not derivable in an untimed model ([MvbaPlan.md](MvbaPlan.md)
§3.7); with a clock both of its clauses become theorems — bounded post-GST
delivery gives the decision chain a finite latency, timeout growth makes some
view's budget exceed it, and (A-leader-rotation-k) supplies the honest leader.
That in turn is what `MVBATemporal.termination` needs, and it is the formal
version of the trust-base move [Liveness.md](Liveness.md) §2.1 describes informally.

**It does not subsume the premise witness.** [TODO.md](TODO.md) § Liveness
asks for a run witnessing that `Mvba.termination`'s five premises are jointly
satisfiable. `MVBATemporal.admissible_exists` is a run in which nobody
proposes (Bounds.md §6.2.7), so that item stays open.

This leg can run **in parallel with** the Chorus run-level liveness leg;
the rules that keep the two from colliding — and the one piece of design
they share, the projection from a composed run to an MVBA run — are
[Liveness.md](Liveness.md) §4.1.

**Staging**, in the shape of Bounds.md §6's:

1. Timed runs over `Mvba`'s generated transition system, and the time
   theory with a growing timeout schedule. Reuses Bounds.md §6 step 1's scaffolding if
   the Chorus leg went first.
2. The chain latency bound: the links of [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) from the
   leader's `Pre-Prepare` to the commit certificate, each with a Δ attached.
   Mostly plugging in proven theorems, and the cheap validation of the
   scaffolding.
3. The entry bound — every correct validator enters the good view within Δ
   of the first — which is the quantitative refinement of
   `eventually_entered_good`. The untimed argument's structure carries over
   (the climb, the common view, the overshoot bound); the bounds are new.
4. Discharge both (A-viewsync) clauses, then `MVBATemporal.termination`;
   axiom pins, docs, and the [Cadence.lean](../Cadence.lean) row moves from conditional to
   a discharged instance.


**Placement.** A sibling of the end-theorem files — e.g. a new
`Cadence/Chorus/Schedule.lean` at the `Compose`/`Pigeonhole`/`Counting`
layer: plain Lean, kernel-only, in-file `#guard_msgs` pins, a row and pin
at the audit root. On completion, the corresponding fields leave the
`…Temporal` classes (`SlotConsensusTemporal`,
`OrchestratorTemporal`) and are proven in the `…_of_temporal`
definitions — the contract fields in
[Cadence/Interfaces.lean](../Cadence/Interfaces.lean) themselves do not
change, which is the point of stating them there.

**Effort and risk.** Chorus-only (steps 1–3) ≈ 2–4 sessions; the full
bounded story ≈ 5–8. The dominant risk is statement-design churn, not
proof difficulty — the state-level content is already proven. Expected
finding class: a misstated or missing premise in one of the paper's
bounded lemmas (the timeline arithmetic has drifted once already,
`d_tot`: `2Δ → Δ`); protocol-level findings are unlikely, since the state
content is verified. The timed-run scaffolding is reusable by a later
L2S bring-up — nothing here is throwaway.

#### Bounds.md §6.2 The MVBA leg: the original framing, decisions, and the Bounds.md §6.2.1 decision record

### 6.2 The MVBA leg, as designed and carried out

The per-seam statements Bounds.md §6 asked to be settled before any Lean. Everything
below is a *design*, not a result: what is proven is what
[Cadence/Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean) says is proven,
and its `#guard_msgs` pins, not this section. The section exists so that the
decisions and the two findings are not re-derived, and so that a reader can
check the premises against the supplement without reading Lean.

**Decisions in one place.**

* The clock belongs to the run: timed runs are labelled runs of the
  generated `Mvba` transition system with a clock sequence, and the
  contract is instantiated at `mvbaSafety th` itself (Bounds.md §6.2.1). No model change; nothing under `Mvba/Proofs/` re-solves.
* Time is a linearly ordered additive commutative monoid with `max`
  (Bounds.md §6.2.2). The theorem needs no Archimedean axiom; the non-vacuity
  witness `admissible_exists` needs an unbounded clock and gets it from
  Mathlib's `Archimedean` and `0 < Δ`.
* The timeout schedule is a function of the view, **bounded above** and
  **eventually above the chain latency** (Bounds.md §6.2.3). The paper's fixed known
  timeout is the special case; *unbounded* backoff is incompatible with the
  contract's fixed `ℓ`, which is the first finding.
* Fairness is bounded weak fairness after GST over plain enabledness,
  with the window measured from `max(now, gst)` so that a clock jump over a
  pending obligation's deadline is inadmissible (Bounds.md §6.2.4). A local step is
  held to `δ`. A step that consumes another party's message is held to what
  the supplement's network guarantees (since step 5b, 2026-09-29): `Δ` for
  messages sent at or after GST by correct validators and retained, `Δ + ρ`
  for the retransmitted classes (`ρ` is the supplement's retransmission
  interval `ρ_mvba`, the schedule's field `ρ`). While some fair labels stayed enabled
  after firing, plain enabledness made every admissible model
  unsatisfiable once a proposal existed. That was the second finding
  (Bounds.md §6.2.4), answered first in the premises (R3: fairness over
  state-changing steps) and since R4–R6 in the model: every fair action
  fires once, and the premises read plainly again (Bounds.md §6.4.7).
* (A-viewsync) is not assumed anywhere. Its two clauses are derived as a
  corollary of the timed premises; the bound itself is proven directly by
  a timed re-run of the chain and does **not** consume `Mvba.termination`
  (Bounds.md §6.2.7 says why it cannot).

#### 6.2.1 The clock belongs to the run

*Outcome first: `TimedRun` carries its own clock (route 2 below); the
product-state lift the section goes on to weigh no longer exists. The rest
of the section is the decision record, ending in the outcome.*

`MVBATemporal.clock : state → time`, and `TimedRun … clock` reads the clock
off each state; that is right for the Conductor, whose `now` is a state
field, and it was written that way for all three modules. `Mvba.State` has
no clock, and Bounds.md §6's "monotone clock `c : ℕ → T`" alongside the state is a
different object. Three ways to reconcile them were weighed:

1. **A ghost `now` in [Mvba.lean](../Cadence/Mvba.lean)** (Bounds.md §3(b)'s device with no guards). Changes
   every VC statement — a cold re-solve of the family — moves the audit pin,
   and adds a 26th label that the read-only label classification of
   [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) would silently file under `JusticeLabel`, so
   `FJustice` would demand weak fairness of `tick`. Out, on
   [Liveness.md](Liveness.md) §4.1's rules alone.
2. **Change `TimedRun` to carry its own clock sequence.** Arguably the right
   design for untimed models, but an edit to [Interfaces.lean](../Cadence/Interfaces.lean) — a joint
   decision under Bounds.md §4.1, and a Chorus-family rebuild.
3. **Pair the state with the clock.** `MVBASafety.timed S : MVBASafety … (state × time) byz`
   is a generic lift — every field is `S`'s on the first component, and a
   transition is an `S`-transition whose clock does not decrease — and
   `MVBATemporal` is instantiated at `(mvbaSafety th).timed time`. Nothing
   is restated: the lifted fragment *is* `mvbaSafety th` on the first
   component, definitionally.

Route 3 is taken. What it costs is a **seam**, stated so it is not
mistaken for a gap: the full `MVBA` instance this leg produces is at the
lifted fragment, while Chorus consumes `mvbaSafety th` at `Mvba.State`, so
`mvba_of_temporal` is not the join used and [System.lean](../Cadence/System.lean) does not
automatically inherit the timed instance. Closing it is one of two edits —
instantiate Chorus at the lifted fragment in [System.lean](../Cadence/System.lean) (the composed
system's MVBA sub-state then carries the clock the composition's own timing
needs anyway), or route 2 — and both are decisions to take with the Chorus
leg when its composition step (Bounds.md §6 step 5) is designed. The labelled timed
run `Cadence.TLRun` is the load-bearing object; the product is a thin
bridge, and if route 2 is taken later the bridge is deleted and the
premises are restated on `TLRun` unchanged.

The Chorus leg's projection from a composed run to an MVBA run
([Liveness.md](Liveness.md) §4.1) lifts to `TLRun` by carrying the
clock along the projected indices; `TLRun.toLRun` is the forgetful map, so
the projection is theirs to define and this leg's timed form is its
pullback, not a second definition.

**The seam, as a proposal to the Chorus leg** (step 4, 2026-09-28; the
decision is open). The instance now exists: `Mvba.mvbaTemporal` at
`(mvbaSafety th).timed time`, and the full `Mvba.mvbaTimed`. Chorus holds
the MVBA state as an abstract sort `mstate` and [System.lean](../Cadence/System.lean) fills it with
`Mvba.State`. There are two ways to hand the composed system the timed
instance:

* **(a) Plug the lifted fragment in at [System.lean](../Cadence/System.lean).** Fill `mstate` with
  `Mvba.State × time` and Chorus's constraint with `(mvbaSafety thM).timed
  time`. No class changes and nothing in Chorus re-solves: Chorus is generic
  in the class, and the lift is the same fragment on the first component, so
  `system_positional_log_safety` goes through unchanged. The cost is on the
  liveness side. The MVBA's clock is then a state component that only the
  MVBA's own steps advance (`mvba_step`, `mvba_propose` and the decision
  handlers choose it, subject only to monotonicity). A composed timed run
  would have to require, as a run predicate, that each such step stamps the
  composed run's current time, so that the MVBA's `TimedRun` reads the real
  clock. The projection would carry that requirement.
* **(b) Route 2: `TimedRun` carries its own clock sequence.** Drop
  `clock : state → time` from the temporal classes. The Conductor, whose
  state has `now`, then states `clk n = now (at' n)` inside its
  `Admissible`. `MVBATemporal` is instantiated at `mvbaSafety th` itself,
  the existing `mvba_of_temporal` gives the full `MVBA`, and [System.lean](../Cadence/System.lean)
  inherits it with no lift. The Chorus leg's projection takes the composed
  run's clock at the projected indices, with no ghost state and no stamping
  condition. On this leg's side, `MVBASafety.timed` and `TLRun.toTimedRun`
  are deleted and `Admissible` keeps its `TLRun` form, as said above. The
  cost is one [Interfaces.lean](../Cadence/Interfaces.lean) edit, which is a warm Chorus-family rebuild,
  and a joint decision.

**Recommendation: (b), bundled with the next [Interfaces.lean](../Cadence/Interfaces.lean) edit** (the
one that also carries `propose_valid`'s move to the rely form,
[CompositionContracts.md](CompositionContracts.md) §2), and taken when
the Chorus leg designs its composition step (Bounds.md §6 step 5). (a) works too, but
it puts a clock into the state that nothing but the MVBA steps maintain, and
that is the device route 1 was rejected for, moved one level up.

**Outcome (2026-09-29): (b), done before Chorus stage 4 started**, in one
[Interfaces.lean](../Cadence/Interfaces.lean) edit together with `propose_valid`'s move to the rely
form. `TimedRun` carries `clk : Nat → time`, the temporal classes have no
`clock` field, and `OrchestratorTemporal.clock_agrees` ties a Conductor run's
clock to its `now`. `Mvba.mvbaTemporal` is at `mvbaSafety th`, and the full
class is `Mvba.mvbaFull := mvba_of_temporal th (mvbaTemporal …)`, whose
fragment is by `rfl` the one [System.lean](../Cadence/System.lean) plugs into Chorus. The seam is
gone. `MVBASafety.timed` and the product state are deleted, and
`TLRun.toTimedRun` is the label-forgetting map. The witness run's clock is
`n • Δ`, since a run no longer has to start at a state's clock value, so the
negative-initial-clock remark of the step-4 reassessment no longer applies.

#### Bounds.md §6.2.4 Superseded paragraphs: the C15 note, the one-line clause, (N4) in R3, move-enabledness

*Since R8 (Bounds.md §6.4.2, C15) the last row is the caller's, not the MVBA's:
`decide` on a transferred certificate is the contract's input `accept`, so
the row left `BoundedJustice` for a clause of its own, `Mvba.Relayed`,
verbatim, and `decide` left the hop table and `Delivers`. Inside Cadence
Chorus's handoff row derives it (`Chorus.relayed_of_timedJustice`).*

Against the pin `026dc8b` the clause was one line: every network label
within `Δ` of `max(clk N, gst)`, regardless of its messages' history. That
held a correct validator to consuming within `Δ` a message sent before GST
(which the supplement may lose), a message two views ahead (which it may
discard), a certificate that has to travel (which costs `ρ` more), a
Byzantine leader's `Pre-Prepare` and Byzantine votes (which reach whom the
adversary chooses), and an assembly in a view everyone has left. A
supplement run of any of these kinds was not admissible, so the timed
claim said nothing about it. None was a misreading of the pinned text,
which did not yet state its network.

**Closed in R3: (N4), prepare certificates do not travel.** Until R3
`adopt_prepqc` was a local step once `msg_prepqc v e` held, a certificate
formed anywhere. In the supplement a validator holds a prepare certificate
only if it received a quorum of prepares itself; nobody forwards one. So a
supplement run in which one correct validator forms a view's prepare
certificate and another, which accepted the same proposal, never does
(Byzantine votes sent to some, or prepares lost before GST) was not
admissible: the timed claim held that second validator to adopting within
`δ`. Since R3 the model does what the supplement does
([Mvba.lean](../Cadence/Mvba.lean), `adopt_prepqc`, the supplement's
`TryFormPrepQC` at the paper target):

* the step takes the supermajority `q` of `Prepare`s as a parameter, as
  `form_prepqc v e q` does, and requires each member's `Prepare` on
  `(v, e)`, in place of `msg_prepqc v e`;
* it records the certificate it formed (`msg_prepqc v e`), since from then
  on the certificate exists and the validator's timeouts carry it;
* it is a network hop with a first-delivery clause — a correct quorum's
  `Prepare`s sent at or after GST and retained by the forming validator —
  and nothing is owed for a quorum with Byzantine members, whose votes
  reach whom the adversary chooses.

`form_prepqc` stays as the anonymous assembly, so the adversary's power is
unchanged. *(Superseded in R4, Bounds.md §6.4.7: the four anonymous assemblies carry
no fairness at all, `AssemblyLabel`; the rest of this paragraph is the R3
record.)* Its weak fairness assumes nothing of the supplement: a firing
move-enables no fair label by itself, since no honest guard reads
`msg_prepqc` and the one assembly that does, `form_tc_lock`, also needs a
timeout carrying the certificate, which the run has only if its sender
held it or, for the adversary, could form it from the broadcast prepares
anyway. The Mvba family was re-solved cold; the one new cell the solver
would have to search, `adopt_prepqc × prepqc_blocks_lower_commits`, is
manual, as its `form_prepqc` twin is. `#veil_status Mvba` is unchanged,
since no action or property was added. The good view is unaffected: there
every correct validator receives the whole correct quorum's prepares within
the same `Δ`, and the chain gets one milestone shorter (Bounds.md §6.2.6).

**Move-enabledness, and the second finding.** *(History, superseded by R6
(Bounds.md §6.4.7): the finding is resolved in the model, and every fairness premise
is stated over plain `Enabled` again. The two paragraphs below are the R3
record; "Resolved in the model" after them is the current state.)*
[Fairness.lean](../Cadence/Fairness.lean)'s `Enabled`
holds whenever *some* transition under the label exists — a stutter
included. Two of the model's assembly labels differ only in the quorum
parameter `q`, and the actions are idempotent: once `msg_prepqc v e` is
set, `form_prepqc v e q'` is still enabled for every other supermajority
`q'`, forever. Weak fairness per label then demands infinitely many
firings for one effect, and if `nodeset` has infinitely many
supermajorities no run satisfies it. In the *timed* form this is fatal
outright: infinitely many firings within `Δ`. So (Δ-justice) is stated for
`EnabledMove` — a transition under `l` to a **different** state, TLA+'s
`⟨A⟩_v` — under which one firing discharges every `q'` at once. *(Since R4,
Bounds.md §6.4.7, no fair label of this model has that property any more: the
anonymous assemblies are unfair, and each correct validator's step is
guarded on the record it sets, which `Mvba.enabledMove_of_enabled` checks.)* Veil's
actions are deterministic in their parameters, so a firing of a
move-enabled label is a move; the proofs pay one side condition per link
(the guard's negative flag becomes the effect's positive one, so the
states differ).

**Resolved in R3 for the untimed leg too.** The finding applied to the
untimed claims as well: `FJustice` was stated with `Enabled`, so the premise
sets of `Mvba.termination` and `Chorus.termination` were unsatisfiable at
any instance with infinitely many supermajorities. Since R3 every fairness
notion in [Fairness.lean](../Cadence/Fairness.lean) — `WeaklyFair`,
`WeaklyFairFamily`, `StronglyFair` — is stated over `EnabledMove`, which
moved there from [Timed.lean](../Cadence/Timed.lean) so that both sides use
one notion, and both `FJustice`s, Chorus's proposal family included, are
restated over it. In plain words: a correct validator's action is owed a
step only while it can take one that changes the state. The premise can
therefore hold at every quorum sort, not only at finite ones, and the
witness of Bounds.md §6.3 shows it holding without the finite-sort argument it used
to need. Each link of the untimed chains pays the side condition once,
with the effect it waits for (`EnabledMove.of_enabled_of_effect`, or
`eventually_of_weaklyFair`, which pays it inside).

**Resolved in the model (R4–R6, 2026-09-30).** The finding was about the
model, not the premise: it had fair labels that stay enabled after firing.
S1b (Bounds.md §6.4.7) removed them. Every fair action now has a "not already" guard
on a record its own step sets, as the paper's rules do, and each model
proves that no fair label is enabled without being able to change the
state, at every state: `Mvba.enabledMove_of_enabled` and
`Chorus.justice_enabledMove`. So the premises are stated with plain
enabledness again — an action enabled from some point on eventually fires
— with no qualifier: `WeaklyFair`, `WeaklyFairFamily`, `StronglyFair`,
`BoundedFair` and `BoundedFairWhile` are over `Enabled`, and so both
`FJustice`s and `BoundedJustice` are. For these models that is the same
premise as R3's: `Mvba.fJustice_iff_move`, `Chorus.fJustice_iff_move`,
`Mvba.boundedFair_iff_move` and `Mvba.boundedFairWhile_iff_move` state the
equivalence, from the acceptance lemmas. `EnabledMove` remains only as the
vocabulary of those four bridges, and the proofs lost the side condition
(`EnabledMove.of_enabled_of_effect` is gone).

#### Bounds.md §6.2.6 The certificate before R4

so a correct validator has decided by `E₀ + L_cert` with
**`L_cert = 3Δ + max(Δ, Δ_sync) + 2δ`** — Supplement, Lemma 16 (`lem:good-view`)'s
`t*_w − τ_w` at `δ = 0`, `Δ_R = 0`. (Until R4 the certificate was the
anonymous assembly's at `E₀ + L_cert` and everyone decided on it by
`E₀ + L_cert + Δ`, a first delivery; since the validator that forms the
certificate now also decides, the good-view lemma concludes one decision,
and the others come by the transfer below, as they already did when a
decision preceded the chain.)

#### Bounds.md §6.2.8 Staging, revised, and the reassessments after steps 2, 3 and 4 and the non-vacuity step

#### 6.2.8 Staging, revised

Reassess after step 2, as Bounds.md §6 says. No step touches the model, the proof
files, [Interfaces.lean](../Cadence/Interfaces.lean), [Fairness.lean](../Cadence/Fairness.lean) or [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean).

1. **This session.** [Cadence/Timed.lean](../Cadence/Timed.lean): `TLRun`,
   the `TotalOrder` bridge, move-enabledness, bounded fairness and its
   contrapositive, the bounded finite-conjunction lemma, `MVBASafety.timed`
   and `TLRun.toTimedRun`. [Cadence/Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean):
   `hop`, `Schedule` with its hypotheses, the four clauses, `Admissible`,
   (A-leader-rotation-k), `ℓ`, and the target as a `Prop`-valued
   definition **before** any proof — [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)'s discipline.
2. **Done (2026-09-28).** The good-view lemma: the eight timed links, the
   prefix form of `entered_le_of_no_timeout`, the stability arguments. The
   cheap validation of the scaffolding, and where a misclassified `hop`
   would show up. [Cadence/Mvba/Bound.lean](../Cadence/Mvba/Bound.lean),
   `Mvba.good_view_decides`; the reassessment is below.
3. **Done (2026-09-28).** The burn lemma, the finite starting point, the
   successor-chain count against `below v_L`, the assembly, and `ℓ`.
   [Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean),
   `Mvba.bounded_termination`; the reassessment is below step 2's.
4. **Done (2026-09-28).** `MVBATemporal` at the lifted fragment
   (`Mvba.mvbaTemporal`, with `Mvba.admissible_exists` and
   `Mvba.timed_termination`) and the full class (then `Mvba.mvbaTimed`, now
   `Mvba.mvbaFull`), in
   [Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean).
   (A-viewsync) as a corollary is `Mvba.aViewSync_of_sync`, and the
   assembly's first half is factored out as `Mvba.exists_good_view`, both in
   [Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean).
   The axiom pins, the [Cadence.lean](../Cadence.lean) rows and the verification-status text
   in [CLAUDE.md](../CLAUDE.md) and [Architecture.md](Architecture.md) §4 are updated, and the seam is put
   to the Chorus leg in Bounds.md §6.2.1. The reassessment is below step 3's.
5. **Done (2026-09-29).** Non-vacuity: the premise ledger (Bounds.md §6.3) and one
   model satisfying every premise of both termination theorems,
   [Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean). The
   reassessment is the last one below.

**Reassessment after step 2** (2026-09-28, as Bounds.md §6 asks). The good-view lemma
is `Mvba.good_view_decides` in
[Cadence/Mvba/Bound.lean](../Cadence/Mvba/Bound.lean), kernel-checked, axioms
at the standard trio. Its premises are the three clauses of `Sync` and the
two quorum classes; it builds in seconds and touched nothing under Bounds.md §4.1's
rules. The three questions the plan left open:

* **Which links cost more than one `BoundedFair` application.** None. Each
  of the eight links (`sync_view`, the leader's proposal, `handle_preprepare`,
  `form_prepqc`, `adopt_prepqc`, `send_commit`, `form_commitqc`, `decide`) is
  one application, through one generic lemma
  (`TLRun.withinFrom_of_boundedFair`) that also pays the move-enabledness
  side condition once for all of them. The leader link splits on the
  certificate below `W` (re-propose under a lock, fresh proposal without
  one), but that is a case split on the state with one application in each
  branch, exactly as in the untimed link. The quorum steps are one
  application per member plus `TLRun.withinFrom_forall`; availability is
  (Δ-avail) directly, joined to the adoption by taking the later of two
  indices (`TLRun.clk_max_le`). (Since R3 there are seven: each validator
  forms its own prepare certificate, so `form_prepqc` left the chain and
  `adopt_prepqc` is a network hop; Bounds.md §6.2.4, (N4).) The cost the plan did not foresee was on the
  *stability* side, not the fairness side. Three state facts
  [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) does not export had to be proven locally:
  `timer_set_label` (only `expire_timer i v` sets `timer_expired i v`, one
  case per action from M13's frame lemmas), the prefix form of
  `entered_le_of_no_timeout`, and the timeout certificate below `W` present
  *at* the first correct entry (`msg_tc_below_of_entered`). Each is a short
  plain-Lean proof.
* **Whether the hop table survived contact with the guards.** It did. Each
  link asks `hop` for its bound by `rfl`, so a disagreement between a link and
  the table fails to elaborate. No link needed a different class. Two δ-rows
  read a certificate built from other parties' messages, and both are right
  for the reason the table gives: `leader_*` reads `tc_lock`/`tc_nolock`,
  which `form_tc_*` sets in the same step as the `msg_tc` whose delivery
  `sync_view` has already paid for (`msg_tc_backed` at the entry index); and
  `adopt_prepqc`/`decide` read certificates whose delivery `Δ` sits on the
  assembly. The good view does not exercise the view-zero labels, the
  timeouts, `form_tc_*` or `sync_view_adopt`, so their rows are tested by
  step 3's burn lemma, not here.
* **Whether `Lcert`'s constant is still the one derived in Bounds.md §6.2.6.** It is,
  with no slack and no extra term. The proof names the eight milestone
  deadlines and closes `E₀ + Lcert = ` their sum by `abel`, so the table and
  the constant agree term for term.

Two findings, both about statements rather than about the protocol:

* **The time theory needs cancellation.** Bounds.md §6.2.2's linearly ordered monoid
  is not enough for the step "`L_cert < τ W`, hence `E₀ + L_cert < E₀ + τ W`".
  In `ℕ∞`, which satisfies Bounds.md §6.2.2's axioms, a clock at `⊤` makes both sides
  `⊤`. A correct `W`-timer may then fire inside the window, and a validator
  that times out in `W` stops the chain. The lemma therefore takes
  `[IsOrderedCancelAddMonoid time]`; `ℕ`, `ℚ≥0` and `ℝ≥0` are instances, so
  the intended models are unaffected. The claims in [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean) are
  stated over the weaker class and are unchanged. The theorem proving
  `BoundedTerminationClaim` (step 3's `bounded_termination`) carries the cancellative class as an explicit
  hypothesis. No run predicate can express it, because it constrains the
  sort, just like the instance hypotheses of Bounds.md §6.2.5.
* **Only the leader and the honest quorum move through the view.** Bounds.md §6.2.6's
  "every correct validator is in `W` / accepted" rows hold of every correct
  validator (the links are stated per validator), but the proof moves only
  `L` and `ByzNodeSetHonestQuorum`'s quorum through `W`. Decisions need no
  view (`decide` reads a certificate of any view), so the final row covers
  every correct validator regardless. The lemma's premises are therefore:
  every correct validator has proposed by the first entry `N₀`; none is
  abandoned by `E₀ + L_cert + δ`; `N₀` is the *first* correct entry, which
  step 3's assembly gets by `Nat.find`; and the clock at `N₀` is at or after
  GST.

The rest of the staging stands. Step 3 is where the burn lemma's `2δ` (one
adoption restarting the timeout's window) gets its first test, and it reuses
this file's link shape and prefix facts unchanged.

**Reassessment after step 3** (2026-09-28). The bound is
`Mvba.bounded_termination` in
[Cadence/Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean):
`BoundedTerminationClaim`, kernel-checked, axioms at the standard trio,
from the two quorum classes and a cancellative time theory. The burn lemma
is `Mvba.synced_succ`, and its iteration is `Mvba.synced_iterate`. Nothing
under Bounds.md §4.1's rules was touched: no model change, no new invariant or step
property, nothing exported from [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean), and so the
`#veil_status Mvba` pin is unchanged. The questions the plan left open:

* **Whether the `2δ` timeout restart held.** It did, and it was the first
  thing tested. The claim needs one fact: *a certificate a validator
  acquires while it stays in `v` is a certificate of `v`*
  (`local_prepqc_new_in_view`). `adopt_prepqc` is guarded on `in_view` for
  the certificate's own view, and `sync_view_adopt` leaves the view. This
  is a two-state fact about labels, not an invariant. It is proven like
  step 2's `timer_set_label`, one case per action from M13's frame lemmas
  (`local_prepqc_set`), and then by induction along the run. From it,
  `within_timed_out` is three cases:
  * the goal already holds;
  * a certificate of `v` is held somewhere in the first `δ` window, after
    which the label is fixed for one more `δ`;
  * no certificate is acquired in the window, so the label chosen at its
    start stays enabled.

  The highest held certificate at the start is found over `below v`, as in
  the untimed link.
* **Whether the hop table survived the rows step 2 did not exercise.** It
  did. `timeout_qc`/`timeout_noqc` are `δ` steps, and `form_tc_lock`,
  `form_tc_nolock` and `sync_view` are `Δ` hops, each asked of `hop` by
  `rfl`. Three rows are still exercised by no proof. `sync_view_adopt` is
  never needed, because `tc_lock_implies_tc` lets a validator holding a
  higher certificate advance through `sync_view`. The two view-zero labels
  are never needed either, because `W` is strictly above a view already
  entered. Their fairness is a premise the bound does not use, which
  weakens nothing. Step 4's `admissible_exists` must still satisfy it,
  which it does vacuously where the labels are never move-enabled.
* **Whether `burn` and `ℓ` are still the constants in [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean).**
  `burn = τ_max + 2δ + 2Δ` is. The proof names the four deadlines and closes
  `X + burn =` their sum by `abel`. **`ℓ` moved**, from
  `Δ + (1 + |below v_L| + k) • C + L_cert + δ` to
  `Δ + (|below v_L| + k) • C + L_cert + δ`. The count is `a + j` burns:
  `1 ≤ a ≤ |below v_L|` successors of `M` clear the ramp
  (`exists_iterate_succ_ge`, a pigeonhole over `below v_L`), and `j < k`
  more reach a correct leader. The step out of `M` is the first of the `a`,
  so the `1 +` counted it twice. `Schedule.ℓ` is redefined to match, and
  Bounds.md §6.2.6 is updated. `a + j ≤ |below v_L| + k - 1` would be tighter still;
  it is not taken, because the natural-number subtraction buys one burn and
  costs readability.
* **How the finite starting point is proven.** As Bounds.md §6.2.6 said: a maximum
  over a finite list, since each step enters at most one view
  (`entered_set_view`, a label case split, then `entered_covered` by
  induction on the index). Neither the node sort nor the view sort is
  assumed finite, and `ViewOrderEnum` is not used for `M`. It is used for
  three other things: `succ`, the pigeonhole count, and the highest held
  certificate in the timeout step. `M` ranges over *correct* validators'
  views, which is all the argument needs.
* **Where cancellation goes.** On the theorem only.
  `bounded_termination` takes `[IsOrderedCancelAddMonoid time]`, and
  [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean)'s variables and both claims keep the weaker class. The
  burn lemma needs no cancellation. The assembly needs it twice: through
  `good_view_decides` (step 2's `ℕ∞` finding), and for `u < u + Δ`, which
  is how the last index at or before `u` is found by `Nat.find`. Keeping the
  claim at the supplement's theory means the extra class appears only where
  a proof uses it, and is not built into the definitions a reader checks
  against the paper.

Three facts are proven locally that neither [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) nor step 2
had: the certificate below a view with its predecessor produced
(`exists_tc_pred_of_entered`); that the first correct validator at or above
a view is *in* it (`entered_eq_of_first_above`, since skipping it needs a
correct timeout there); and the successor facts of `ViewOrderEnum`. Each is
a short plain-Lean proof.

**What step 4 now needs.** The protocol argument is complete. What remains
is plumbing between the claim and the contract, plus the corollary:

* `MVBATemporal.termination` at `(mvbaSafety th).timed time`, from
  `bounded_termination` through `Admissible`'s labelling. The observables
  are definitional (Bounds.md §6.2.8 step 1), so the work is `byGstBound`'s shape
  against `max t gst + ℓ`.
* `admissible_exists`, as Bounds.md §6.2.7 planned.
* `AViewSyncClaim`. Its second clause is the good view, and the assembly
  constructs that view (`W`, `N_W`) but does not export it. Step 4 should
  first factor the assembly's first half into a lemma that returns `W`
  with `good_view_decides`'s premises, then prove both
  `bounded_termination` and `AViewSyncClaim` from it. The first clause is
  (T2) plus `clk_unbounded`, as planned.
* The axiom pins, the [Cadence.lean](../Cadence.lean) row, and the text in [CLAUDE.md](../CLAUDE.md) and
  [Architecture.md](Architecture.md) §4 about the timed instance and its seam, as listed in
  the staging above.

**Reassessment after step 4** (2026-09-28; the names are those before the
Bounds.md §6.2.1 outcome: `mvbaTimed` is now `mvbaFull`, and the instance is at
`mvbaSafety th`). The instance is
`Mvba.mvbaTemporal : MVBATemporal … (S := (mvbaSafety th).timed time)` and
the full class is `Mvba.mvbaTimed`, in
[Cadence/Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean). Both are
kernel-checked, with axioms at the standard trio, and
`Mvba.mvbaTimed_toSafety` hands back the lifted fragment by `rfl`. Nothing
under Bounds.md §4.1's rules was touched except one docstring sentence in
[Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) (`Terminates`, which said the timed form had no
instance). No model change, and the `#veil_status Mvba` pin is unchanged.
The **MVBA bounds leg is complete**; what it leaves open is the seam
proposal in Bounds.md §6.2.1. The questions the task set:

* **Whether the instance needed any hypothesis beyond the plan's.** No.
  The hypotheses are exactly Bounds.md §6.2.5's, with the time theory of Bounds.md §6.2.2 as
  step 2 amended it:
  * finitely many validators (`Fintype node`) in place of
    `ByzNodeSetEnum`, which it supplies (`ByzNodeSetEnum.ofFintype`; see the
    last point below);
  * `ByzNodeSetHonestQuorum` and `ViewOrderEnum`;
  * `LeaderRotation vfin sch.k th`;
  * `IsOrderedCancelAddMonoid time` for `termination`;
  * `Archimedean time` for `admissible_exists`. `0 < Δ` was already a
    field of `Schedule`.

  The hypotheses can be met. `Schedule.fixedNat` is the paper's fixed
  timeout at `time := ℕ`. An `example` in the same file instantiates
  `MVBATemporal` there, with the class's `TotalOrder ℕ` found by instance
  search (Veil's own), so the scoped bridge the instance was built with
  agrees with it. The contract's observables are the model's fields by
  `Iff.rfl` (`timed_decided_iff`, `timed_proposed_iff`,
  `timed_abandoned_iff`). The least upper bound in `byGstBound` and in the
  abandonment premise is `max` by one generic lemma, `Cadence.gstLub_iff`
  in [Timed.lean](../Cadence/Timed.lean), with `TimedRun.byGstBound_iff` built on it. So
  `timed_termination` is `bounded_termination` read through `Admissible`'s
  labelling and nothing else.
* **One correction to the plan, not a hypothesis.** The witness clock
  `c + n • Δ` of Bounds.md §6.2.7 is not unbounded in general. In an Archimedean
  linearly ordered cancellative monoid with negative elements, `c + n • Δ`
  can stay below `0` for all `n`. An example is
  `{(0, b)} ∪ {(a, b) : a < 0} ⊆ ℤ × ℤ` under the lexicographic order, with
  `c = (-1, 0)` and `Δ = (0, 1)`. That monoid is Archimedean because every
  positive element is `(0, b)` with `b > 0`, and every element is at most
  some `n • (0, b)`. The witness therefore uses `c`, then
  `max c ((n + 1) • Δ)`, which the Archimedean axiom bounds from below
  directly. The witness run fires `become_avail_ready` forever. It is
  admissible because every state is *quiet*: no input, entry, acceptance,
  or prepare/commit/timeout message. At a quiet state no hop-table label is
  move-enabled, which one case split over the transition bodies shows. The
  three labels no proof uses are covered by the same fact, vacuously.
* **Whether `AViewSyncClaim`'s statement survived.** Its premises did, and
  it gained one hypothesis: a finite validator set, `[Fintype node]`. The
  plan's premise `AllPropose` ("every correct validator proposes at some
  index") gives a common deadline only over finitely many validators, and
  without a deadline the bound has no starting point: nothing stops every
  correct-led view from being burnt before its leader has proposed. The
  first version of this step removed the need for finiteness by changing
  the premise to "proposed by some time `t`". Following review, the claim
  instead keeps `Mvba.termination`'s own caller premises (`AllPropose`,
  `NoEarlyAbandon`) and assumes finitely many validators (see the last
  point). The deadline form survives as the lemma behind it,
  `Mvba.aViewSync_of_proposedBy`, for any node sort. The claim does not
  need "no abandonment up to `u + ℓ`", because an abandoned correct
  validator has decided, and a decision is certificate-backed
  (`decided_backed`).
* **How it was proven: not through the good view, and why that matters.**
  The second clause of `AViewSync` only asks that a `W`-timer does not
  expire before *some* commit certificate exists. So **any** correct-led
  view above every view entered when a certificate first exists satisfies
  both clauses. The first clause follows from (T2), and the second from
  (T1), since the timer of such a view starts after the certificate
  (`Mvba.aViewSync_of_commitqc`). Neither step uses timing beyond the two
  timer clauses. The certificate itself comes from `bounded_termination`,
  or from an early abandonment. The factored good view (`GoodView`,
  `exists_good_view`) is what `bounded_termination` consumes, but this proof
  does not need it. **The finding** is about what kind of premise
  (A-viewsync) is, and [Liveness.md](Liveness.md) §2.1 now opens with
  the short account. It does not weaken `Mvba.termination`. It is the view
  timer stated as ordering constraints: the untimed model has the timer but
  no clock, so on its own a timer may fire at any moment, and the premise
  fixes the two orderings that matter. It holds in every run that
  terminates (`aViewSync_of_commitqc`), so the untimed theorem reads *given
  enough time, the protocol decides*, with the bound set aside and not the
  synchrony. The synchrony itself is the timed premises', in the
  supplement's terms, and `aViewSync_of_sync` derives the ordering
  constraints from them.

  **Both clauses are needed**, and the second does not imply the first
  through a least good view. Let a Byzantine leader of `V` never propose,
  and let `V`'s timer never fire, which is allowed because the marker is
  under no fairness obligation. Every correct validator stays in `V`. Every
  correct-led `W` above `V` is never entered, so it satisfies the second
  clause vacuously, and nobody decides. A least `W` would not help for two
  reasons. It constrains only correct-led candidates. And a candidate's
  failing the second clause means that *some* correct validator's timer
  fired early, not every one. The view order is also not assumed
  well-founded, except through `ViewOrderEnum`. In the timed model the two
  clauses are (T2), not late, and (T1) with `τ W > L_cert`, not early.
* **What the seam proposal says.** Two ways to hand the composed system the
  instance (Bounds.md §6.2.1). (a) plugs the lifted fragment in at [System.lean](../Cadence/System.lean): no
  class change, but the composed run must require each MVBA step to stamp
  the global time into the sub-state. (b) is route 2: `TimedRun` carries its
  own clock sequence, the instance moves to `mvbaSafety th` itself, and the
  existing `mvba_of_temporal` joins it. The recommendation is (b), bundled
  with the next [Interfaces.lean](../Cadence/Interfaces.lean) edit and decided with the Chorus leg's
  composition step. The decision is open.
* **The obligations list in [Interfaces.lean](../Cadence/Interfaces.lean)** was left naming
  `termination, ℓ` as unproven until the next edit of that file; it now
  names `Mvba.mvbaTemporal`.
* **Finiteness of the validator set, as a convention for claims.** It came
  up three times, spelled three ways: the class `ByzNodeSetEnum` (the
  MVBA's quorum enumeration), a complete list `nodes` with a proof that it
  contains every validator ([Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)), and the deadline
  form of this claim. None of them concerns the protocol. They are the
  point at which a liveness argument collapses finitely many per-validator
  eventualities into one index, which is sound only over a finite set. So
  the contract-level results of this leg (`mvbaTemporal`, `mvbaTimed`,
  `timed_termination`, `aViewSync_of_sync`) take `[Fintype node]`, and
  `ByzNodeSetEnum.ofFintype` ([ByzQuorum.lean](../Cadence/ByzQuorum.lean)) supplies the enumeration
  their proofs use. The building-block lemmas keep `ByzNodeSetEnum`, which
  is weaker: finite quorums over any node sort. `bounded_termination` keeps
  it too, as the general form.

  What finiteness does **not** do is simplify the proofs. Every step that
  consumes it is local and already existed. It also does not touch the two
  other finiteness questions of the leg: the abstract `nodeset` sort may
  still have infinitely many supermajorities (Bounds.md §6.2.4's caveat on
  `FJustice`, resolved in R3 by stating fairness over state-changing
  steps), and the view order is infinite by nature (`below vL`). It
  stays out of the Veil models and the safety theorems, which hold at any
  cardinality and whose solver could not use it anyway. **Proposal to the
  Chorus leg:** adopt the same convention. That means `[Fintype node]` in
  place of the `nodes`/`hnodes` argument in [Chorus/Termination.lean](../Cadence/Chorus/Termination.lean), and,
  when `Mvba.termination` is next touched, `[Fintype node]` in place of its
  `ByzNodeSetEnum` argument. At the concrete families `Fin n` both are
  instances already.

**Reassessment after the non-vacuity step** (2026-09-29). The results are
`Mvba.timedTermination_premises_satisfiable` and
`Mvba.termination_premises_satisfiable` in
[Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean), axioms at the
standard trio. Each is an existential over the whole premise set: the
sorts, the instances, the schedule, the theory and the run. No premise's
statement changed. **The model did change**, once, and that is the step's
main finding (Bounds.md §6.3.2): building the witness showed the model did not halt
a validator after it decides, as the supplement does, so the halt was added
([Cadence/Mvba.lean](../Cadence/Mvba.lean), "A decided validator halts").
The `#veil_status Mvba` count is unchanged, since only guards were added,
but every VC changed and the family was re-solved; the mutation test
[Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) mirrors the guard, still
finds its agreement violation, and its pinned trace moved (the two
decisions now come last). The questions the task set:

* **Whether any premise was harder to satisfy than the ledger expected.**
  One, and not the one flagged. The expected hard premise was `FJustice`
  with plain `Enabled` (Bounds.md §6.2.4). At the concrete family it cost one lemma:
  once the run is idle only two assembly labels are enabled, because a
  certificate has one quorum that can assemble it at `ByzNSet 4`
  (`Mvba.Witness.enabled_idle`), and the tail fired both forever. (Since
  R3 `FJustice` is stated over state-changing steps, the idle tail owes
  nothing, and that lemma is gone; Bounds.md §6.3.) The
  premise that mattered was the caller's `NoEarlyAbandon` together with the
  view timer. In the model as it was, a decision did not stop a validator,
  so a witness had either to change views forever or to have the caller
  abandon every validator after `max(t, GST) + ℓ`; the first version of the
  witness did the latter, through five views. That is what exposed the
  divergence from the supplement. With the halt, the witness is the run the
  plan asked for: everyone decides in view 0, then idles.
* **What the halt cost the proofs.** Every honest link now needs its
  validator *active*: neither abandoned nor decided (`Mvba.Active`, which
  replaced `¬ abandoned` in `SettledIn` and in the link hypotheses). The
  untimed proof already ran under "nobody has decided", so it needed only
  that substitution. The timed proof needed one new case split, in
  `bounded_termination`: either a correct validator decides by the
  certificate deadline `max(t, GST) + ℓ − δ`, and then everyone decides
  within `δ` of its certificate (`within_decided_ref`, the decide link
  measured from `ref N`), or nobody does, and the chain runs as before with
  every correct validator active up to that deadline. `ℓ` is unchanged.
* **Whether bounded weak fairness needed a real argument.** No. The run
  advances its clock only out of states at which no fair label is
  move-enabled (`Mvba.Witness.quiet`), so every window contains such a
  state on its own clock reading, and (Δ-justice) holds with its antecedent
  false. That is a property of this run, which is as eager as possible, and
  not of the premise.
* **Whether one run serves both claims.** It does. The untimed projection
  satisfies the five untimed premises; (A-viewsync) holds at `W = 1`,
  because the view-0 timers expire and nobody enters view 1. The file ends
  with both theorems applied to the witness.
* **What the proof costs.** Each state is a closed formula in its index,
  so the 25 prefix steps, the quiescence facts and the premises are linear
  arithmetic. The file elaborates in seconds and touches no VC.

#### Bounds.md §6.4 The Chorus leg: the kick-off record (findings F1–F4 as found, decisions as proposed)

### 6.4 The Chorus leg: the kick-off record

*Written 2026-09-29, after `Chorus.termination` (PR #43) and before any
Lean. S1, S1b, S2, S3, S4 and S5 are done since (Bounds.md §6.4.6, items 1–5, have their records): the leg is complete. It supersedes Bounds.md §6's staging for Chorus
(steps 1–3), which predates the MVBA leg. Bounds.md §6.2 and Bounds.md §6.3 are the template.
Decisions are recorded with their reasons. Those marked **open** are for
Lars to take: item 1 above all, and the two class changes it depends on.*

**In short, for an auditor.** The paper proves two timed properties of
Chorus:

* **ℓ-termination** (Lemma 11 (`lemma:chorus-termination`)): if every correct
  validator starts participating in the slot by time `t`, every correct
  validator finalizes by `max(t, GST) + 5Δ + ℓ_MVBA`;
* **d_tot-totality** (Proposition 4 (`prop:chorus-totality`)): if one correct validator
  finalizes at time `t`, every correct validator finalizes by
  `max(t, GST) + Δ`.

Both hold under *Δ-synchronized participation*
(Definition 5 (`def:delta-synchronized-participation`)): once one correct validator
starts, every correct validator starts within Δ. Both also hold "when run
within Cadence". The contract states the two properties as the fields
`bounded_termination` and `totality` of `SlotConsensusWithTotality`
([Interfaces.lean](../Cadence/Interfaces.lean)). Nothing instantiates
them yet.

The timed claims would assume what the MVBA's did (Bounds.md §6.2): messages arrive
within Δ after GST, local steps take at most δ (zero in the paper), and
the slot's three time landmarks (the deadline `D`, then `D + Δ` and
`D + 2Δ`) happen on time on synchronized clocks. They would further
assume that the MVBA's own timing premises hold of its steps inside the
run, and that the certificate bridge `ValidBridge` holds; the bridge is
unchanged from the untimed claim. The rest are the caller's conditions,
which the composition later discharges: everyone starts by `t`, starts are
Δ-synchronized, nobody starts before `D − Δ`, and nobody abandons before
finalizing.

**The main question is item 1.** The contract's fields speak about
`participate`, `abandon` and `propose`, and the Chorus model has none of
them. **Recommendation (open):** model the participation interface in
[Chorus.lean](../Cadence/Chorus.lean), exactly as the paper's standing
convention states it (option A, Bounds.md §6.4.1). Bundle it into the same
re-solve with one small [Interfaces.lean](../Cadence/Interfaces.lean) edit,
which adds the two "within Cadence" premises the paper's proofs use and
the class omits (finding F1). This is the only option under which the
timed claims are the paper's statements and the contract instances exist.

**Four findings, all about statements, none about the protocol.**

* **F1: the class's timed fields omit two premises the paper uses.**
  `bounded_termination` and `totality` lack "a correct validator abandons
  only after finalizing" (Algorithm 1 (`algorithm:cadence`), Algorithm 1, line 23 (`line:abandon`)). The
  untimed `SlotConsensusTemporal.termination` has that premise.
  `bounded_termination` also lacks "no correct validator starts before
  `D − Δ`", which is the Conductor's integrity
  (Lemma 12 (`lemma:conductor-integrity`)); the proof of
  Proposition 5 (`prop:chorus-finalization-time`) uses it in its first step. Without the
  first premise, a validator that abandons at once never finalizes.
  Without the second, a slot whose deadline lies far after `t` cannot
  finalize by `max(t, GST) + ℓ`. Either way the field is false for every
  faithful implementation, unless the implementation's own `Admissible`
  smuggles in the caller's conditions. The rely form of
  `MVBATemporal.termination` was adopted precisely to avoid that
  (Bounds.md §6.4.1, "The class change").
* **F2: the paper's message buffering needs a split hop.** "A message
  whose rule is blocked by this convention is not lost"
  (Appendix C.3 (`subsection:chorus-protocol-overview`)). A rule's network input is
  therefore due Δ after it was sent, and its local gate (a phase landmark,
  or participation) is due δ after it opened. Measuring a Δ-hop from the
  later of the two, as Bounds.md §6.2.4's `BoundedFair` does, costs one extra Δ at
  every step where a landmark opens last. The model's bound would then be
  `6Δ + ℓ_MVBA` or worse, not the paper's `5Δ`. Bounds.md §6.4.2 states the clause
  that keeps the paper's arithmetic.
* **F3: at δ > 0 the totality latency is `Δ + 2δ`, not Δ.** The
  Conductor's window induction closes *because* Chorus's totality
  latency equals the synchronization tolerance its condition grants.
  "Both equal `Δ = d_tot`", in the words of the paragraph before
  Definition 6 (`def:window-synchronized`). With local steps that take time the ratchet
  loses δ per window. This is the Conductor leg's question. Bounds.md §6.4.6 states
  what this leg provides so that it is not blocked.
* **F4: to be confirmed. The 5Δ bound looks loose by one Δ.**
  Lemma 11 (`lemma:chorus-termination`) splits at `T₀ = M + 4Δ + ℓ_MVBA` and adds Δ
  for totality (`M = max(t, GST)`). The inner split of
  Proposition 5 (`prop:chorus-finalization-time`) at `T₀ − Δ` already handles early
  finalizers, and the only use of that proposition's premise "no correct
  validator stops before `T`" is covered by "abandon only after
  finalizing". So a single split at `T₀ − Δ` should give `M + 4Δ + ℓ_MVBA`,
  which is the bound an earlier, commented-out draft next to the lemma
  states. Bounds.md §6.4.3 records how to handle it if the proof confirms it.
  **Confirmed by S4** (R18): `Chorus.timed_termination_tight` proves
  `M + 4Δ + ℓ_MVBA + 8δ`; the claim stays the paper's 5Δ
  (`Chorus.timed_termination`).

**Decisions in one place.**

* Participation interface: **option A (open)**. The model gains
  `participate` and `abandon`, and `propose` becomes the contract's input.
  Every sending rule is gated on active participation (Bounds.md §6.4.1).
* Class change C1/C2: **recommended (open)**, bundled with option A into
  one Chorus-family re-solve. C3 (the tolerance) goes to the Conductor leg.
* The clock is the run's (`TLRun`, `TimedRun.clk`), as in the MVBA leg.
  No clock goes into the model (Bounds.md §6.2.1).
* The time theory is Bounds.md §6.2.2's, including cancellation. The timing
  constants are the MVBA schedule's `Δ` and `δ`. Chorus adds only the
  deadline (Bounds.md §6.4.2).
* Fairness is bounded fairness over plain enabledness with a hop table.
  The hop is split into a network part and a local gate (F2). The phase
  markers leave the table and become punctual timers (Bounds.md §6.4.2).
* The MVBA is consumed **through the contract**: `T.Admissible` of the
  timed projection, `T.ℓ` and `T.termination`, for
  `T := Mvba.mvbaTemporal …` (Bounds.md §6.4.3). The upgrade step 5b can therefore
  refine the MVBA's timed premise without touching this leg.
* The proof re-runs the untimed chains with deadlines. It case-splits on
  an early finalization, as the paper does, and not on the progress
  dichotomy (Bounds.md §6.4.3).
* Non-vacuity comes from one witness, built after the model edit, that
  serves both the untimed and the timed claims (Bounds.md §6.4.5).

#### Bounds.md §6.4.1 The participation interface: options A–C, costs, the recommendation

#### 6.4.1 The participation interface

**What the contract asks.** `SlotConsensusTemporal` has three inputs
(`participate`, `abandon`, `propose`) with their observables, effects,
frames and initial conditions. It has the admissible-run model, and
Termination and Quiescence stated over them. `SlotConsensusWithTotality`
takes an instance of it as a parameter. So the timed fields cannot even be
stated at Chorus until the participation interface exists at the
fragment. There is a second constraint: the class's frames say that
*internal* steps leave a correct validator's inputs unchanged.
`Chorus.slotConsensusSafety` currently sets `step := trans`, so any input
it had would also count as an internal step. Every option that
instantiates the class must therefore separate the input labels from
`step` in [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean).

**Option A: model the interface in [Chorus.lean](../Cadence/Chorus.lean).** Add
per-validator `participating i` and `abandoned i` as local state. Add two
input actions:

* `participate i`;
* `abandon i`, which forwards to the MVBA's `abandon` when the validator
  has invoked it, as Algorithm 5, line 48 (`line:fb-abandon`) does. Its successor-state parameter
  is harmless, since inputs carry no fairness.

The existing `propose j m` becomes the contract's `propose(P)`, with
`P ↦ m`, the class's `proposal := merkle_root` at
[Chorus/Compose.lean](../Cadence/Chorus/Compose.lean). Then gate every
rule that sends, with `participating i ∧ ¬ abandoned i`, and exempt the
rules that only process. That is the standing convention of
Appendix C.3 (`subsection:chorus-protocol-overview`), rule for rule:

* **Gated, because they send.** `propose` and `deliver_chunk_assigned`
  (at the proposer), `vote`, `commit_sign_*`, `cast_fast_commit`,
  `fb_sign_*`, `cast_fallback_vote`, `mvba_propose` (the convention names
  it explicitly), `cast_fb_commit`, and `commit_assign_*`/`finalize_commit`.
  The paper's finalization rules re-broadcast the proof
  (Algorithm 4, line 35 (`line:fast-rebroadcast-commitqc`), Algorithm 5, line 46 (`line:fb-commit-rebroadcast`)), and
  its totality proof relies on their being gated. The model's comment at
  "Commit decision" ("finalization on receipt has no active-participation
  precondition") then changes.
* **Exempt, because they process.** `record_chunk`, `aggregate_fastqc_*`,
  the decision handlers and `mvba_terminate`.
* **Anonymous capabilities.** `broadcast_commitqc_*` and
  `redisseminate_chunk` have no actor today. In the paper both are sends
  by a correct validator: the collector (Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)),
  and the fallback-entry caster (Algorithm 5, line 12 (`line:fb-redisseminate`)). The faithful
  form gives each a sender parameter, gated when the sender is correct and
  unconstrained when it is Byzantine. Without that, Quiescence cannot
  attribute those messages. **Recommended**, since the family re-solves
  anyway.

Quiescence is then provable in the paper's own two-part shape
(Lemma 6 (`lemma:chorus-quiescence`)):

* Chorus's own sends are gated;
* the MVBA's sends are the MVBA's `sent`, confined by its `quiescence` to
  the window between a gated `propose` and a forwarded `abandon`.

The message type is a sum of Chorus's attributed network relations and
`mmsg`, defined in [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) and
not in the model. The proof reads the transition bodies, like the MVBA's
`sent_new_tr`, so no `step_property` cell is needed.

*Cost.* Every VC statement changes (new state components), so the whole
Chorus family re-solves cold. The measured cold figures live in
[CLAUDE.md](../CLAUDE.md) and [Dependencies.md](Dependencies.md). Other
effects:

* **The audit pin.** The `#veil_status Chorus` pin in
  [Chorus/Certify.lean](../Cadence/Chorus/Certify.lean) grows by two
  actions' cells per property. The Chorus.lean edit adds no invariant: the
  new guards only strengthen hypotheses.
* **Manual cells.** They keep their statements' shape (`veil_inv_have` is
  by name), but their tactics must be re-run cold (CLAUDE.md,
  "The cache hides derivation drift").
* **The label classification.** [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)
  gains an `InputLabel` class (`participate`, `abandon`, `propose`). This
  is **a trap to avoid**: `JusticeLabel` is the complement of the other
  classes, so a new input would silently become weakly fair, and fairness
  of `abandon` would force every validator to abandon.
* **The component.** `MvbaStepLabel` and `mvbaComponent` gain the
  forwarding `abandon`.
* **The untimed claim.** `TerminationClaim` gains the caller's premises
  (every correct validator eventually participates; none abandons before
  finalizing), which are exactly `SlotConsensusTemporal.termination`'s.
  Its proof restructures, because a validator that finalizes on the fast
  path and then abandons also abandons the MVBA. So the MVBA's
  `NoEarlyAbandon` holds only on the branch where nobody has finalized.
  The re-proof therefore splits on an early finalization, which is the
  split the timed proof uses (Bounds.md §6.4.3). Each honest link gains the gate as
  a hypothesis, as the MVBA's links gained `Active` in PR #42.
* **The monitor.** Its label decoders learn the new actions.
* **Unaffected**: the FallbackReceipt and Mvba families, and the glue's
  safety theorem, which is generic in the fragment.

*Faithfulness.* This is the highest of the three options. The claims are
the paper's statements over the paper's interface. Both `…Temporal`
instances become possible, Quiescence stops being "out of scope" in
Chorus.lean's header, and `TerminationClaim` becomes the class's own
Termination.

**Option B: state the claims over what Chorus models.** Two variants.

* *B1, implicit participation.* Every validator participates from the
  run's start. The claim becomes: all correct validators participate from
  `D − Δ`, and all finalize by `max(D − Δ, GST) + ℓ`. That is a true and
  honest special case, and it is exactly the Conductor's steady state
  after recovery. It is not the paper's lemma, which quantifies over late
  and staggered starts. It cannot instantiate `SlotConsensusTemporal`,
  because `init_participating` and the input frames have nothing to bind
  to. Quiescence is false in it: an implicitly participating validator
  votes before any `open`. And it blocks the next leg:
  Proposition 14 (`prop:conductor-open-to-complete`) applies ℓ-termination at a start time
  `max(t, GST) + d_tot` set by the Conductor, not at `D − Δ`.
* *B2, a gated product in Lean.* Wrap the Chorus transition system with
  participation ghosts and gate its labels outside Veil. Safety transfers
  by simulation, and nothing re-solves. The wrapper cannot forward
  `abandon` to the MVBA (Algorithm 5, line 48 (`line:fb-abandon`)) without stepping `mvba_st`
  outside Chorus's transitions. That breaks the simulation to Chorus's
  reachable states, on which every invariant rests. Without forwarding,
  Quiescence is false for the MVBA's messages after a fast-path
  finalization. The wrapper would also be a second semantics of Chorus
  that an auditor has to read beside the model. Every run-level lemma of
  stages 3–4 would have to be transported through it.

**Option C: change the class.** For example, drop the inputs from the
Chorus-facing class, or state Termination over "participates from the
start". Either is unfaithful to Module 1 (`mod:slotconsensus`), whose interface
*is* the three inputs, and whose Quiescence is about them. **Not
recommended as the resolution.**

**The class change needed under every option (C1, C2; open, joint).**
Separate from the interface question, F1's two premises have to enter the
class. The proposed form, in the rely style of `MVBATemporal.termination`,
as antecedents rather than `Admissible` content:

* **C1**, in `bounded_termination` and `totality`:
  `∀ i, ¬ byz i → ∀ n, abandoned (r.at' n) i → ∃ V, finalized (r.at' n) i V`.
  This is the same antecedent `SlotConsensusTemporal.termination` already
  has.
* **C2**, in `bounded_termination`, with a datum
  `deadline : slot → time` beside `Δ`:
  `∀ n i, ¬ byz i → participating (r.at' n) i → deadline (S.tag (r.at' n)) ≤ r.clk n + Δ`.
  This is "no start before `D − Δ`", stated over the observable
  `participating`. It is equivalent to the paper's form at the start
  index, and it is implied at every later one. The composition
  discharges it from `OrchestratorSafety.integrity_timing` with
  `deadline s = start_time s + Δ`. The paper keeps this datum out of the
  module: its commented-out "assumed behaviour" block in
  Module 1 (`mod:slotconsensus`) lists it, and the lemmas carry it as "within
  Cadence". That is why it is an antecedent here and not a field of
  `SlotConsensusSafety`.

`ℓ` and `d_tot` stay data. The instance sets them to closed terms,
pinned by `rfl` lemmas in the style of `Lcert_paper`: at `δ = 0` they are
the paper's `5Δ + ℓ_MVBA` and `Δ`.

**Recommendation: A with C1/C2, in one edit of
[Chorus.lean](../Cadence/Chorus.lean) and [Interfaces.lean](../Cadence/Interfaces.lean) and
one re-solve.** Three things ride along in the same edit:

* the **(A-mvba) prose clean-up** that [TODO.md](TODO.md) § Liveness
  leaves for these files' next real edit: Chorus.lean's liveness section,
  and the SlotConsensus obligations row in Interfaces.lean;
* Chorus.lean's (F-justice) prose list, which should name
  `deliver_chunk_assigned` and `broadcast_commitqc_*`
  ([Liveness.md](Liveness.md) §4.3);
* PR #44's Module 3 (`mod:mvba`) Agreement prose edit in Interfaces.lean.

Chorus.lean's header paragraphs on Termination and Quiescence are
rewritten there too. [FallbackReceipt.lean](../Cadence/FallbackReceipt.lean)'s
(A-mvba) mention stays for its own next edit.

#### Bounds.md §6.4.2 The hop table as designed and built, F5–F15 as found and closed, the C15 and F15 designs, expected pins

The hop table, classified as Bounds.md §6.2.4's is, by what the guard consumes:

| `Δ` (another party's message or certificate) | `δ` (local, or carried by an input already received) |
|---|---|
| `deliver_chunk_assigned` (the proposer's chunk) | `record_chunk`, `vote` (gate: phase past the deadline) |
| `aggregate_fastqc_*` (others' vote signatures) | `commit_sign_*`, `cast_fast_commit` |
| `fb_sign_*` (others' votes and chunks; gate: the fallback arm) | `cast_fallback_vote` |
| `broadcast_commitqc_*` (others' commit votes) | `on_mvba_decide_*`, `mvba_terminate` (the certificates travel inside the decided value, whose `Valid` checks them) |
| `mvba_propose` family (others' fallback votes via `fbcert`; gate: the arm) | `cast_fb_commit` |
| `redisseminate_chunk` (the caster's chunk; removed by R19, F15) | `finalize_commit` |
| `commit_assign_*` (a certificate someone else broadcast) | |

The table has three consequences:

* **Participation.** Every row whose rule is gated (Bounds.md §6.4.1) adds
  participation to its gate.
* **`mvba_propose` is two rules** (corrected by S3, F9 below). This
  bullet first said that one Δ-row suffices, because "with the split hop
  that costs nothing". That holds for the case-(b) trigger, others' fallback
  votes, but not for case (a) (Algorithm 5, line 23 (`line:fb-mvba-propose-fast`)), whose trigger
  is the proposer's own complete fast meta-block: it exists only once the
  FastQCs have arrived, so a Δ-row on it costs a second Δ. The premise
  therefore has the paper's two rules, a Δ-family and a δ-family.
* **The check.** At δ = 0 the table reproduces the paper's timeline term
  for term (Bounds.md §6.4.3), as Bounds.md §6.2.4's did for the MVBA. The MVBA leg's own
  finding C16 (N3, PR #44) questions a δ-row that consumes another
  party's certificate: the MVBA's `decide`. The two δ-rows above that
  read certificates, the decision handlers, rest on a different argument:
  the certificates travel inside the decided value. If step 5b
  reclassifies `decide`, re-check these two rows against that argument.

**The table as built** (S2, 2026-09-30; `Chorus.hop`, `Chorus.gate` and
`Chorus.Owed` in [Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)).
Each row has a bound, a gate, and a condition under which it is owed at all.

| row | bound | gate | owed when |
|---|---|---|---|
| `deliver_chunk_assigned i j m` | `Δ` | none (since R19: the send was `propose`) | always (the proposer is correct by the guard) |
| `record_chunk` | `δ` | none | always |
| `vote i` | `δ` | `Active i`, phase past `D` | always |
| `aggregate_fastqc_* … q` | `Δ` | none | the quorum `q` is correct |
| `commit_sign_* i …`, `cast_fast_commit i` | `δ` | `Active i` | always |
| `broadcast_commitqc_* c … q` | `Δ` | `Active c` | the quorum `q` is correct |
| `fb_sign_pos i j m q qc` | `Δ` | `Active i`, the fallback arm | `q` and `qc` correct, and a correct supermajority has cast its votes |
| `fb_sign_neg i j qv` | `Δ` | `Active i`, the fallback arm | `qv` correct |
| `cast_fallback_vote i` | `δ` | `Active i`, the fallback arm | always |
| `mvba_propose i v _` on `FBCert` (`propose`, one family per `(i, v)`) | `Δ` | `Active i`, the MVBA arm | `FBCert` from a correct supermajority |
| `mvba_propose i v _` on the fast meta-block (`proposeFast`, one family per `(i, v)`, F9) | `δ` | `Active i`, the MVBA arm | `i`'s own complete fast meta-block |
| `on_mvba_decide_*`, `mvba_terminate` | `δ` | the MVBA arm | always (the guard reads `i`'s own decision) |
| `redisseminate_chunk k i j m` (removed by R19: inside `fb_sign_pos`, F15) | `Δ` | `Active k` | `k` signed a positive fallback entry for `(j, m)` (F8), or `k` has itself decided and `f+1` correct validators hold their chunk under `(j, m)` (F11) |
| `cast_fb_commit i v` (since R19: `TimedJustice.fbCommit`, split at its trigger) | `Δ` (was `δ`) | `fbCommitGate`: `Active i`, `i`'s own decision of `v` only, `mvba_complete` | (the gate; was: `i` has itself decided) |
| `mvba_avail_ready i v` (the family `avail`) | `Δ` (was `δ`, R19) | none | `i` holds `v` |
| `commit_assign_* i j …` | `Δ` | `Active i` | a correct validator finalized with that entry, or the fallback commit certificate from correct voters over the decided entry |
| `finalize_commit i` | `δ` | `Active i` | always |

The reconciliation with the labels since R5: the Byzantine splits
(`byz_broadcast_commitqc_*`, `byz_redisseminate_chunk`) are unfair and have
no row, and the honest collector and re-disseminator are rows at their
correct sender. `hop_isSome_iff` pins that the table covers exactly the fair
labels that are not phase markers. `mvba_propose`'s gate is the MVBA arm,
not the fallback arm, because the case-(a) trigger waits for it and Bounds.md §6.4.3's
timeline reaches the proposals only after it.

**The decision-handler re-check.** Step 5b made the MVBA's `decide` a
network hop ((N3), `Mvba.BoundedJustice.decisions`). The two δ-rows
**stand**. Each handler fires on the acting validator's *own* MVBA decision,
which is a local output, and the certificates its bridge check reads hold at
that decision by `ValidBridge`'s completeness. The transfer (N3) is about is
the transfer of a decision to a validator that did not decide first, which
is the MVBA's own `decide` step. Its cost, `Δ + ρ`, is inside `ℓ_MVBA`.

**Two findings against the table above, both built into the statement.**

* **F5: the paper owes delivery only between correct validators**
  (Proposition 5 (`prop:chorus-finalization-time`)'s proof: "every message between correct
  validators is delivered within Δ"). The model's network relations hold
  from a message's first delivery to anyone, a Byzantine sender's included.
  So a Δ-row that consumes a Byzantine validator's message would owe a
  delivery the paper does not promise, since a Byzantine voter may send to
  some validators only. That is the MVBA's C16 finding, on Chorus's side.
  Each Δ-row is therefore owed only when the messages it consumes came from
  correct senders (the last column). Both untimed `FJustice` definitions,
  Chorus's and the MVBA's, have the same shape, and the finding applies to
  both. **Closed in R8** (2026-09-30): both untimed `FJustice`s take the same
  owed-conditions (`Chorus.Owed`, `Mvba.Owed`), and re-proving
  `Chorus.termination` against them found F7 and F8 (below).
* **F6: `cast_fb_commit` reads a shared flag.** Its guard is
  `mvba_complete`, which the first validator to decide sets. The paper's
  rule fires on the voter's own decision (Algorithm 5, line 41 (`line:fb-commitvote`)). As a δ-row
  with no condition it would owe a vote from a validator whose MVBA has not
  decided. The row is owed once the voter itself has decided.

**The decision handoff (C15): the design** (R8, 2026-09-30, written before
the build). The supplement's paragraph "Decision output and handoff" (Supplement,
Section 1.2 (`subsec:mvba-protocol`)) says
four things: `decide(x, CommitQC)` outputs the certificate; Chorus broadcasts
it; a correct validator that receives a valid one re-broadcasts it and
finalizes; and the MVBA accepts a transferred `CommitQC` of any view
(Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)). Until R8 the MVBA's `decide` (its
transferred-certificate handler) was an *internal* MVBA step, taken by the
oracle `mvba_step`, so its timing was assumed inside `T.Admissible`
(`Mvba.BoundedJustice.decisions`). The design makes the transfer the
caller's, so that Chorus's own rows carry it.

* **(a) Where the relay lives.** A new Chorus action
  `accept_mvba_commitqc i c mvba_next` in [Chorus.lean](../Cadence/Chorus.lean),
  beside `mvba_propose`: a correct validator hands a valid certificate `c`
  to its MVBA through the contract's new input `mvba.accept mvba_st i c
  mvba_next`, and sets `mvba_st := mvba_next`. It reads no network relation
  at all. What stands for the certificate on the wire is the MVBA's own
  monotone record that it exists (`mvba.certifies`, read inside
  `mvba.accept`), so the monotone-network contract of
  [ChorusDesign.md](ChorusDesign.md) §3.1.1 is untouched: the only other
  guards are `¬ is_byz i` and the fired-once record below. **Chorus's
  broadcast is folded into the decision output.** A correct validator's
  decision counts as its broadcast of the certificate that commits it:
  that is the supplement's "upon receiving this output, Chorus broadcasts",
  with its instantaneous local computation. A separate broadcast rule,
  gated on participation, would let a validator decide, finalize on the
  fast path and abandon before it hands off, which the paper's
  instantaneous reaction rules out, and the MVBA would then wait for a
  certificate nobody sends. The re-broadcast needs no step either: once
  `i` has accepted, it has decided, so it is a sender in turn. The
  finalization the supplement attaches to the certificate is **not**
  modelled yet: the model has the main body's fallback commit round only. At
  the target the supplement adds the route, and R16 models it
  ([PaperAlignment.md](PaperAlignment.md) §5.7).
* **(b) The contract change** ([Interfaces.lean](../Cadence/Interfaces.lean),
  `MVBASafety`, additions only, first-order):
  * `certifies st c v`: `c` is a valid commitment proof for `v` at `st`;
  * `decided_certified`: a correct party's decision has a valid
    certificate — **decide exposes its certificate**;
  * the input `accept st p c st'`, with `accept_trans`;
  * `accept_effect`: accepting a valid certificate for `v` decides `v`,
    and `accept_enabled`: a correct party that has proposed, is not
    abandoned and has not decided can accept any valid certificate — **a
    transferred valid certificate is accepted**, in the rely form (the
    caller transfers; the MVBA accepts).

  `Mvba.mvbaSafety` proves them: `certifies (.commitqc w e) v` is
  `v = e ∧ msg_commitqc w e`, `accept` on `.commitqc w e` is the model's
  `decide p w e`, and `decided_certified` is the existing
  `reachable_decided_backed`. `Mvba.Msg` gains the constructor `commitqc`
  (sent by no MVBA party: `Sent` is `False` on it). **At the instance,
  `decide` becomes an input** (`Label.isInput`), so `mvbaSafety.step`, and
  with it Chorus's oracle `mvba_step`, no longer takes it: in the composed
  system an MVBA decides on a transferred certificate only when Chorus
  hands it over. `decided_certified`, `accept_effect` and `accept_enabled`
  are liveness facts and are withheld from the solver
  (`veil_smt_ignore`), so the Chorus cells see two new symbols and
  `accept_trans`. Nothing is weakened; `MVBATemporal` is unchanged. The
  MVBA's own claims change on the caller's side, since the transfer is now
  the caller's: the untimed claim gains the premise (F-relay)
  (`Mvba.FRelay`, a transfer is owed once a correct party has decided on
  the value), the timed `Sync` gains `Mvba.Relayed` (the old `decisions`
  clause, moved out of `BoundedJustice`, verbatim), and `decide` leaves
  the hop table and `Delivers`.
* **(c) The rows, and the derivation.** One row, a family per receiver:
  `accept_mvba_commitqc i _ _` is a `Δ`-row with no gate (it processes a
  message, like `aggregate_fastqc_*`), owed once **a correct validator has
  decided** (its certificate was sent at its decision). The derivation is
  the lemma `Chorus.relayed_of_timedJustice`: for `δ ≤ Δ + ρ` (the paper's
  `δ = 0` included), in every run satisfying `TimedJustice`, every
  projection's timed run satisfies `Mvba.Relayed`. In words: if `decide i
  v e` stayed enabled for `Δ + ρ` after a correct validator decided `e`,
  the relay row would have made `i` decide within `Δ`, which disables it.
  `Chorus.timedMvbaAdmissible_of_rows` is the form a witness uses: the
  MVBA's own three clauses on a projection, plus `TimedJustice`, give
  `TimedMvbaAdmissible` at the system's instance. The untimed twin is
  `Chorus.fRelay_of_fJustice`, which makes `MvbaAdmissible`'s premise set
  exactly the MVBA's own (`Mvba.FJustice ∧ AViewSync ∧ FAvail`) and
  derives the rest.
* **(d) The fired-once guard.** `local_mvba_qc_accepted i`, unset by the
  guard and set by the step, so the step always changes the state and
  `Chorus.justice_enabledMove` keeps holding with one more case. A validator
  that has accepted has decided, so the record never blocks a step that
  is owed.

**F5 closed, and what it needed besides.** Both untimed `FJustice`
definitions take the owed-conditions of the timed rows: Chorus's `Owed`
(moved to [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)), and the
MVBA's correct-sender part of `Delivers` (`Mvba.Owed`, a leader or a quorum
that is correct). Re-proving `Chorus.termination` against them showed
that R7's `Owed` was stricter than the paper's network in two rows, both
places where a correct validator forwards what it received:

* **F7: the fast meta-block travels.** `aggregate_fastqc_*` is also owed
  when a correct validator that cast its fast commit vote holds the FastQC:
  the same rule broadcasts its `FastBlock` (Algorithm 4, line 20 (`line:fast-metablock`)), and a
  correct validator that receives one adopts its FastQCs. The paper's
  finalization-time proof uses exactly this ("that validator held a fast
  meta-block and broadcast it"). Without it the case-(a) proposals would
  owe nothing whenever the FastQC's quorum had Byzantine voters.
* **F8: re-dissemination by the decoder.** `redisseminate_chunk k …` is
  also owed when its correct sender `k` signed a positive fallback entry
  for the root: it decoded the proposal to sign (Algorithm 5, line 12 (`line:fb-redisseminate`)
  sends every validator its chunk). A `FallbackQC`'s correct signer is the
  paper's source of the chunks (Proposition 5 (`prop:chorus-finalization-time`), "by
  `M + 3Δ`").

A third consequence is on the MVBA's untimed premise: (A-viewsync)'s second
clause now names a correct validator's **decision** rather than a commit
certificate, because a certificate the adversary assembled reaches only
whom the adversary chooses, so no transfer of it is owed. The timed model
implies the new clause as it implied the old one (`Mvba.aViewSync_of_sync`).
The proof of `Chorus.termination` no longer takes the commit route on the
late branch: saturation always yields a correct trigger for the MVBA (a
correct fast voter's meta-block, or a correct `FBCert`), and the MVBA arm
finalizes.

**Four findings from S3** (2026-10-01, R11, while proving the milestones;
each is built into the statement in the same PR; F12 was left for a
model session, R12, which closed it). Three are about premises, one about the model.

* **F9: the case-(a) proposal is a local step.** The table had one Δ-row for
  `mvba_propose`, owed on `CorrectFBCert ∨ i`'s own complete fast meta-block.
  In case (a) a correct validator cast its fast commit vote by
  `M + 2Δ + 2δ`, its FastQCs reach every correct validator through
  `aggregate_fastqc_*` (F7) by `M + 3Δ + 2δ`, and only then is the row owed,
  because the trigger is the receiver's local state. A Δ-row from there puts
  the proposals at `M + 4Δ + 2δ`, one Δ beyond the paper's `M + 3Δ`. The
  premise now has the paper's two rules (`TimedJustice.propose`,
  Algorithm 5, line 36 (`line:fb-mvba-propose`), a Δ-family owed on a correct `FBCert`; and
  `TimedJustice.proposeFast`, Algorithm 5, line 23 (`line:fb-mvba-propose-fast`), a δ-family owed
  on the own meta-block), and the proposals are by `M + 3Δ + 3δ`
  (`Chorus.within_all_input`). This raises `ℓ`'s δ-multiple from 8 to 9.
* **F10: a Δ-row costs `max(Δ, δ)`.** With its gate already open
  (`N = N'`), a buffered row's window is `ref N + max(Δ, δ)`; a row without a
  gate is always in this case. At `δ > Δ` every such hop costs `δ`, and
  `5Δ + ℓ_MVBA + 8δ` was then not reachable on the paper's route (a run may
  delay each step to the end of its window). The schedule now has the field
  `Chorus.Schedule.δ_le_Δ`: a local step is no slower than a network hop,
  true at the paper's `δ = 0`. It implies the `δ ≤ Δ + ρ` that
  `relayed_of_timedJustice` takes. `TotalityClaim` never needed it.
* **F11: re-dissemination was owed on the fast path** (found by R10, during
  the witness). `Owed (.redisseminate_chunk k …)` was
  `CorrectChunkQuorum j m ∨ msg_fb_pos_sig k j m`, with gate `Active k`, so
  every active correct validator owed every validator its chunk within Δ of
  a chunk quorum. The paper re-disseminates in two places only: inside the
  fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`), F8's disjunct) and after the
  validator's own MVBA decision (Algorithm 5, line 39 (`line:fb-commit-wait`)). R10's run: `Δ = 1`,
  `δ = 0`, `D = 1`, a fast-path finalization at clock 3, but the row for
  `k = 1` owed and open from clock 0 and due by 1. Both untimed and timed
  premises excluded such paper runs. The chunk-quorum disjunct is now owed
  only once `k` has itself decided. `Chorus.termination` is re-proven
  against it with no model change: `eventually_fbcommit_sig` used the
  disjunct only with `k := i`, the voter, which has decided.
* **F12: the model's fallback commit vote waited under more roots than the
  paper's** (found by R10). The paper waits only under FallbackQC entries:
  "**for each** FallbackQC in B′ with a positive entry ⟨s, j, root⟩: **wait
  until** p_i has received and validated its assigned chunk for root"
  (Algorithm 5, line 38 (`line:fb-commit-foreach`), Algorithm 5, line 39 (`line:fb-commit-wait`)). The model's
  `cast_fb_commit` required
  `∀ J M, is_proposer J → mvba_decided_pos J M → msg_chunk_received i J M`,
  under every decided positive root, FastQC-backed ones included. So the
  model had fewer runs than the paper: the safety claims did not cover a
  paper run in which the vote is cast without that wait, and the liveness
  bound had to pay for a chunk the paper does not wait for. **Closed in
  R12** (2026-10-01), see "F12 closed" below.

**F12 closed** (R12). The guard now reads like the paper line:

| | `cast_fb_commit`'s DA wait |
|---|---|
| paper | for each FallbackQC in B′ with a positive entry ⟨s, j, root⟩: wait until p_i has received and validated its assigned chunk for root |
| before | `∀ J M, is_proposer J → mvba_decided_pos J M → msg_chunk_received i J M` |
| after | `∀ J M, is_proposer J → mvba_decided_pos J M → vote_quorum_pos J M ∨ msg_chunk_received i J M` |

The decided entry vector does not record which certificate holds an
entry. The decision handlers check that one does
(`vote_quorum_pos j m ∨ (fb_quorum_pos j m ∧ fbcert)`). So the model reads
"held by a FallbackQC" as "no positive FastQC for it exists". Both network
reads are positive, the antecedent is the frozen decided-vector read
already documented ([ChorusDesign.md](ChorusDesign.md) §3.1), and the
action keeps its one parameter, `i`. No invariant was needed:
none mentions the DA wait, and all 103 of the action's cells re-solved
cold. The `#veil_status Chorus` count was written down before the build as
unchanged, `101 + 46 × (101 + 1) + 47 = 4840`, and it is. `Chorus.termination`
is re-proven with a simpler argument (`eventually_fbcommit_sig`): under a
FastQC root there is nothing to wait for, and under a FallbackQC root one
of its `f+1` signers is correct and owes the re-dissemination (F8's
disjunct). Timeline, Totality and Witness needed no edit.

Two findings from the fix, both reported, neither acted on:

* **F13: where a root has both certificates, the model does not wait and
  the paper may.** If B′ carries a FallbackQC for `(j, m)` while a
  positive FastQC for `(j, m)` also exists (the MVBA proposer held only
  the former), the paper's validator waits for its chunk and the model's
  does not. For safety this only adds runs. For the timed claim it leaves
  a residual: in such a run the δ-row of `cast_fb_commit` is owed from the
  decision, while the paper's validator may wait for its chunk until the
  correct FallbackQC signer's re-dissemination arrives (a Δ-row). The run
  then violates the premise, and the claim says nothing about it. Closing
  this exactly needs the certificate kind in the MVBA's value (an entry
  vector that says FastQC or FallbackQC), which changes the value type
  `System.lean` instantiates. That is outside this session's scope.
  **Proposal:** carry the certificate kind in the entry vector in the
  composition leg, or accept the residual as stated here. *Re-scoped by
  R13:* F13 is an artefact of the hybrid target. At `48cac9a` each
  validator's own `B′` carries its certificates, and the realignment closes
  F13 exactly ([PaperAlignment.md](PaperAlignment.md) §5.5, Bounds.md §8 R15).
  **Closed in R15**, see "F13 closed" below.
* **F14: re-dissemination's "decided" owed-disjunct was used by no proof,
  and it was stronger than the paper.** `Owed (.redisseminate_chunk k i j
  m)` was `(CorrectChunkQuorum j m ∧ k has decided) ∨ msg_fb_pos_sig k j
  m`. The left disjunct was used only by the old `eventually_fbcommit_sig`,
  for FastQC roots, which no longer need a chunk. The paper's decided
  validator broadcasts only *its own* chunk, and only under FallbackQC
  entries (Algorithm 5, line 39 (`line:fb-commit-wait`)). It does not send other validators their
  chunks. So the disjunct owed steps that paper runs need not take.
  **Closed in R14**, see "F14 closed" below.

**F14 closed** (R14). The row now owes exactly what the paper sends:

| | `Owed (.redisseminate_chunk k i j m)` |
|---|---|
| paper | the fallback-entry rule re-encodes and sends each validator its assigned chunk (Algorithm 5, line 12 (`line:fb-redisseminate`)); a decided validator broadcasts only its own chunk (Algorithm 5, line 39 (`line:fb-commit-wait`)) |
| before | `(CorrectChunkQuorum j m ∧ ∃ v, mvba.decided k v) ∨ msg_fb_pos_sig k j m` |
| after | `msg_fb_pos_sig k j m` |

`FJustice` and `TimedJustice` are weaker (fewer obligations), and
`CorrectChunkQuorum`, which only the dropped disjunct used, is gone. No Veil
statement moved: `Owed` is a premise of the run-level theorems, not part of
the model. `eventually_fbcommit_sig` used only F8's disjunct, the FallbackQC
signer's own positive entry, and is unchanged up to the disjunction's
injection. `Chorus.termination`, the timeline milestones, `Chorus.totality`
and the three witness theorems re-checked in plain Lean, all at
`[propext, Classical.choice, Quot.sound]`.

**F13 closed** (R15). The MVBA's value is now the meta-block
representation, each validator decides its own, and the wait runs under
exactly the FallbackQC entries of the validator's own `B′`
([PaperAlignment.md](PaperAlignment.md) §8.1 (d)):

| | `cast_fb_commit`'s DA wait |
|---|---|
| paper | upon `MVBA[s].decide(B′)`: for each FallbackQC in B′ with a positive entry ⟨s, j, root⟩: wait until p_i has received and validated its assigned chunk for root (Algorithm 5, line 37 (`line:fb-mvba-decide`) to Algorithm 5, line 39 (`line:fb-commit-wait`)) |
| before | `∀ J M, is_proposer J → mvba_decided_pos J M → vote_quorum_pos J M ∨ msg_chunk_received i J M` |
| after | `cast_fb_commit i v`: `mvba.decided mvba_st i v` and `∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → msg_chunk_received i J M` |

A root that is FastQC-certified somewhere but FallbackQC-certified in the
validator's `B′` is now waited for, as in the paper, so the residual is
gone. `Owed (.cast_fb_commit i v)` is "`i` decided `v` and no other
representation" (P11 of [PaperAlignment.md](PaperAlignment.md) §6), and
the row stays a δ-row: its chunk is delivered by `redisseminate_chunk`'s
Δ-row from the correct FallbackQC signer, so the premise owes the vote δ
after the wait is over, when the paper's validator casts it.
`eventually_fbcommit_sig` reads the FallbackQC entries of the validator's
own decision; the fallback quorum is `ValidBridge`'s completeness, and the
correct signer's own signature gives the proposer's root and the decode
quorum. The `#veil_status Chorus` count is unchanged, `47 · 102 + 46 = 4840`.

**F15: re-dissemination is gated at delivery, so (Δ-avail) is not derivable**
(found by R18, 2026-10-02, while deriving the MVBA's (Δ-avail) from the
availability row; **closed in R19**, see "F15 closed" below). The paper sends a validator's chunk inside the fallback-entry
rule (Algorithm 5, line 12 (`line:fb-redisseminate`)), while the signer is
active, so the chunk is in flight from the signature on and is delivered
within `Δ` after GST whatever the signer does next. The model splits the send
off: `redisseminate_chunk k i j m` is a separate step, and for a correct `k`
it requires `participating k ∧ ¬ abandoned k` *at delivery*; its row's gate
is `Active k`. An abandonment between signing and delivery therefore drops a
message the paper has already sent. **Counterexample run.** The FallbackQC
for `(j, m)` has exactly one correct signer `k`, and `j` is Byzantine. `k`
signs at `D + Δ`, then receives another validator's fast commit certificate,
finalizes and abandons, all within `Δ` of signing (C1 permits it). A correct
`i` later accepts an MVBA value with that FallbackQC entry. Its chunk wait
can never be met, so `mvba_avail_ready` stays disabled and `Mvba.AvailWithin`
fails, while `TimedJustice` holds: `k`'s row lapsed when its gate closed. So
`timedMvbaAdmissible_of_rows` cannot drop (Δ-avail) for every run, and
`TimedMvbaAdmissible` still assumes it (P12's ledger line). It is our
divergence from the paper, not a finding about the paper. The timed
termination proof does not meet it: on its late branch nobody has abandoned
before the votes. Two designs for R19:

* **(a) a guard change**: the correct sender's `redisseminate_chunk` is
  guarded on its own `msg_fb_pos_sig k j m` (the send happened) instead of
  `Active k`. Small, but it lets a send fire *after* the abandonment, which
  conflicts with the Quiescence half of S5's `SlotConsensusTemporal`
  instance;
* **(b) one atomic step**: `fb_sign_pos` also delivers the chunk to every
  receiver (a bulk update), exactly as the paper's single rule does. This
  keeps Quiescence, and `redisseminate_chunk`'s correct-sender row becomes
  unnecessary.

The derivation needs one more fact, a property of the timing model: the
availability window covers a Chorus network hop and a local step,
`Δ + δ ≤ Δ_sync` (the chunk by `Δ` after the acceptance's reference time, the
report `δ` later). It belongs in the schedule, as a field like `δ_le_Δ`, not
as a lemma hypothesis. That is a statement change (`Chorus.Schedule` or
`Mvba.Schedule`), so it goes to R19 too, and with it the witness's schedule:
`Mvba.Schedule.fixedNat` has `Δ_sync = 0`.

**F15: the design** (R19, 2026-10-02, written before the build).

*(a) Where the paper re-disseminates.* At two points, both in Algorithm 5
(`alg:fallback`):

| paper | the model today | the model after R19 |
|---|---|---|
| Inside the fallback-entry rule. Its guard is "upon local time reaches `s.deadline + Δ`, at least `2f+1` valid Vote messages have been received, and `pathVote = none`" (Algorithm 5, line 7 (`line:fb-pathvote-guard`)). Then "for each proposer `p_j` … with `Ev(j) = ⊥`" (Algorithm 5, line 8 (`line:fb-cast-entry`)): "if collected `f+1` valid positive votes for `(p_j, ρ)` … and `isDecoded(ρ)`", it signs the positive entry (Algorithm 5, line 11 (`line:fb-positive-entry`)) and then "re-encode proposal; **send** each validator its assigned chunk for `ρ`" (Algorithm 5, line 12 (`line:fb-redisseminate`)). | Two steps. `fb_sign_pos i j m q qc` signs. `redisseminate_chunk k i j m` later delivers `i`'s chunk, once per receiver, while `k` is active (F15). | **One step.** `fb_sign_pos i j m q qc` signs *and* sends every validator its chunk, as the paper's rule does. |
| After the MVBA decision: "**wait until** `p_i` has received and validated its assigned chunk for `ρ`, then **broadcast** that chunk" (Algorithm 5, line 39 (`line:fb-commit-wait`)). | The wait is `cast_fb_commit`'s guard. The broadcast has no step, because it needs none. `msg_chunk_received i j m` says that `i`'s assigned chunk is on the network, and the decoding threshold `chunk_quorum` counts it from then on, wherever it travels next. Broadcasting it to the others changes no relation. Since F14 no row owes it either. | Unchanged. |

*(b) The fix: one atomic step*, the form R18 called (b). The rule gains
two bulk updates, each over a single-capital index:

```
action fb_sign_pos (i : node) (j : node) (m : merkle_root) (q qc : nodeset) {
  … the guards, unchanged …
  require ¬ local_fb_entry i j
  msg_fb_pos_sig i j m := true
  local_fb_entry i j := true
  -- Algorithm 5, line 12: re-encode, send each validator its assigned chunk.
  msg_chunk_received I j m := true
  local_chunk_sent i I j m := true
}
```

* **The parameter list stays at five.** The guards are unchanged, since the
  rule already requires `chunk_quorum j m` (`isDecoded`) and `well_encoded m`.
* **No VC is put at risk by the new writes.** No invariant reads
  `msg_chunk_received` or `local_chunk_sent` on its left-hand side. The
  three that mention `chunk_quorum` inside a negation
  (`progress_fallback_signing` and its kin) see no change in its truth
  value, because the rule's own guard already has `chunk_quorum j m`.
* **Quiescence is kept.** Every send of the rule happens inside the gated
  step (`participating i ∧ ¬ abandoned i`). `local_chunk_sent i I j m` is
  the per-sender send record, and S5's one-step Quiescence can read it as
  the `sent` observable for chunks, since `msg_chunk_received` has no
  sender index. After an abandonment, `i` sends nothing.
* **The fired-once guard is kept.** `fb_sign_pos` keeps `¬ local_fb_entry
  i j`, so its sends happen once. `Chorus.justice_enabledMove` loses a
  case and gains none.

*A consequence for the timed premise, which the design fixes.* After the
atomic step, `msg_chunk_received i j m` holds from the correct signer's
send. That is the convention every broadcast relation of the model already
follows: a relation holds from the send, and the *reader's* row is a
`Δ`-row that times the delivery. Two post-deadline rules read a validator's
own re-disseminated chunk. Today both are `δ`-rows, because until now the
chunk arrived through its own `Δ`-row:

* `cast_fb_commit i v`, the DA wait (Algorithm 5, line 39 (`line:fb-commit-wait`)), and
* `mvba_avail_ready i v`, the availability report.

Kept as `δ`-rows, they would owe their step `δ` after the decision or the
acceptance, even in a paper run whose chunk is still in flight. After GST
that is up to `Δ` after the send, and the MVBA can decide sooner than that
when every other message is fast. Such paper runs would then violate
`TimedJustice`, the F11 kind of gap. So both rows become `Δ`-rows, by
the hop table's own classification (they consume another party's
message):

* **`mvba_avail_ready`**: the `avail` family's bound goes from `δ` to `Δ`.
  Its owed-condition is unchanged (`i` holds `v`), and so is its gate (none).
* **`cast_fb_commit`**: a buffered `Δ`-row, split at its trigger. The
  message part is the chunks, due `Δ` after they were sent. The gate is
  the rule's trigger, "upon `MVBA[s].decide(B′)`" (Algorithm 5, line 37
  (`line:fb-mvba-decide`)): `Active i`, `i`'s own decision of `v` (the only
  one, P11), and the decision landmark `mvba_complete`, which is the model's
  shadow of the decided vector having arrived. The vote is then due by
  `max(chunks sent + Δ, trigger + δ)`, the paper's timing. The row moves out
  of the generic `rows` into its own `TimedJustice` field (`fbCommit`),
  because its owed-condition is now the gate. The untimed `Owed` is
  unchanged. **The gate checklist gains one item**: a rule's gate may name
  the acting validator's own MVBA output that the rule fires upon. That is
  local state, and the clause still says only "the rule fires `δ` after its
  trigger".

Both changes only remove or postpone obligations, so the premise gets
weaker. The bound does not move. On the late branch the chunks are sent by
saturation (`M + 2Δ + 2δ`, `fb_pos_sig_at_cast`), so they are due by
`M + 3Δ + 2δ`, which is before the decision. The vote stays at
`X_v = X_d + 3δ`, and `Lchorus` and `Ltight` are unchanged.

*The alternative, not taken.* The send could happen in the rule with
delivery as a separate step of the network: an in-flight relation written
by `fb_sign_pos`, and an ungated delivery step owed `Δ` after it. That
keeps the readers' rows as they are. But it needs a new relation, a
delivery record for the fired-once guard (`¬ msg_chunk_received` would be a
negative network read), and a kind of step the model does not have: one
taken by the network rather than by a validator. Its Quiescence argument
also rests on a convention, namely which record counts as `sent`. The
atomic step is the paper's rule as written, so the cost lands on two
premise rows instead.

*(c) `redisseminate_chunk` for correct senders is removed.* It stood for
line 12, which now lives inside `fb_sign_pos`. Line 39 needs no step,
by (a). Its `Owed` line, its hop row and its gate go with it, and so does
its untimed fairness row. `byz_redisseminate_chunk` stays: it is the
adversary's capability, which any holder of `f+1` chunks has, and it is
unfair. The proofs that consumed the row read the chunk at the signature
instead, through a first-flip fact proven in plain Lean as
`fb_pos_sig_flip` was: a correct `k` with `msg_fb_pos_sig k j m` has sent
every validator its chunk. No invariant is needed for it. This affects
`eventually_fbcommit_sig`, `within_fb_chunk` and `fAvail_of_fJustice`.
The last one also loses its `ActiveFrom` hypothesis, which existed only
for the signer's gate. That is the untimed face of F15.

*(d) The schedule constraint, and the witness.* The derivation of
(Δ-avail) needs exactly the following:

* A correct `i` accepts `v`. Then `v`'s FallbackQC entries are certified on
  the network (`ValidBridge` at a held value), each has a correct signer,
  and by (c) each signer has already sent `i` its chunk.
* So the `avail` row is owed and enabled from the acceptance on, and it
  fires within `max(Δ, δ) = Δ` (`δ_le_Δ`).

What is used is therefore **`Δ ≤ Δ_sync`**, not `Δ + δ ≤ Δ_sync`. The
`+ δ` belongs to a reading in which the chunk arrives through its own
`Δ`-row and the report then adds `δ`, which the atomic step retires.
**Decided at review:** the field

```
/-- **The MVBA's availability window covers one Chorus network hop**:
`Δ ≤ Δ_sync`. … -/
Δ_le_Δsync : mvba.Δ ≤ mvba.Δsync
```

beside `δ_le_Δ` in `Chorus.Schedule`
([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)). The Chorus
schedule composes the MVBA's, and the constraint relates the two layers, so
it belongs to the composing layer and not to `Mvba.Schedule`. R18's
`Δ + δ ≤ Δ_sync` implies it, and the two coincide at the paper's `δ = 0`.
The design review also extends the gate checklist by one item: a gate may
name the acting validator's own MVBA output that its rule fires upon.

The witness then needs `Δ_sync ≥ Δ = 1`. **Decided at review:** the
Chorus witness overrides `Δsync := 1` in its own schedule, and
`Mvba.Schedule.fixedNat` and the MVBA's witness stay untouched. So
`Mvba.Witness.ell = 24` cannot move. (At `Δ_sync = 1` the supplement's
timeout `T = 4Δ + max{Δ, Δ_sync}` is still `5`, and the ramp holds,
`Lcert 1 0 1 = 4 < 5`.)

`timedMvbaAdmissible_of_rows` then takes only the MVBA's own two clauses,
(Δ-justice) and (T-timer), and derives (Δ-avail) and the handoff from
`TimedJustice` and the schedule. The new lemma is
`Chorus.availWithin_of_timedJustice`, the twin of
`relayed_of_timedJustice`. No interim conditional derivation from R18
exists to remove.

*(e) The pin.* One action leaves, and no invariant or step property is
added: `A = 48`, `I = 100`, `S = 1`, so `#veil_status Chorus`, which is
`(A + 1)(I + S) + A`, loses one action's `101 + 1` cells and its
does-not-throw cell (the counts are [History.md](History.md)'s R19 row). Mvba `1507` and
FallbackReceipt `220` are unchanged. The Mvba model file does not change,
so NoLock needs no mirror.

*(f) The proposer's dissemination, the same shape* (added at the design
review: a gap of F15's shape is closed in the same re-solve, not parked).
`deliver_chunk_assigned i j m` required `participating j ∧ ¬ abandoned j`
at delivery. Algorithm 2 (`alg:proposer-dissemination`) sends every chunk in
the proposing step itself, in the `send` of its "for each validator `p_r`"
loop. So the model could not deliver a correct proposer's chunks once the
proposer had abandoned, while the paper's are in flight from the proposal
on. The safety claims therefore covered a different set of runs from the
paper's. The fix needs no new relation and no new kind of step:

| | `deliver_chunk_assigned i j m` |
|---|---|
| paper | upon `propose`: … for each validator `p_r`: send `p_r` its chunk (Algorithm 2 (`alg:proposer-dissemination`)) |
| before | `¬ is_byz j`, `participating j`, `¬ abandoned j`, `msg_proposer_signed j m`, `¬ local_chunk_sent j i j m` |
| after | `¬ is_byz j`, `msg_proposer_signed j m`, `¬ local_chunk_sent j i j m` |

* **The send is `propose`.** It is gated on participation and is the
  paper's proposing step. Its record is `msg_proposer_signed j m`, which
  for a correct `j` is written only there, so the guard that remains reads
  exactly that "the chunk was sent". The delivery stays a step, so
  `record_chunk`'s pre-deadline timing is unchanged.
* **Quiescence: a delivery of an earlier send is not a new send.** The
  proposer's `sent` record for its chunks is the proposal, which the gated
  `propose` writes. A later delivery writes the receiver's
  `msg_chunk_received` and the step's fired-once record, and sends
  nothing.
* **Its row.** It is still the `Δ`-row it was, owed always (the proposer is
  correct by the guard). Its gate `Active j` is dropped, so the delivery
  is due `Δ` after the send whatever the proposer does next. That
  *strengthens* the premise in one place, since the row is now owed after
  the proposer abandons. The paper's network promises exactly that: the
  message was sent between correct validators. No invariant reads the participation
  relations against chunk delivery, and the pin is unchanged by it.

**F15 closed** (R19, 2026-10-02). Built as designed, with the review's
decisions:

| | the fallback-entry rule's re-dissemination |
|---|---|
| paper | "re-encode proposal; send each validator its assigned chunk for `ρ`" inside the positive branch of the fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`)) |
| before | a separate step `redisseminate_chunk k i j m`, requiring `participating k ∧ ¬ abandoned k` at delivery |
| after | in `fb_sign_pos i j m q qc` itself: `msg_chunk_received I j m := true`, `local_chunk_sent i I j m := true` |

| | the proposer's dissemination |
|---|---|
| paper | upon `propose`: … for each validator `p_r`: send `p_r` its chunk (Algorithm 2 (`alg:proposer-dissemination`)) |
| before | `deliver_chunk_assigned i j m` required `participating j ∧ ¬ abandoned j` |
| after | the delivery reads the send (`msg_proposer_signed j m`) and nothing of the proposer's later state |

* **The model.** One action fewer; no invariant changed; no manual cell.
  `#veil_status Chorus` lost that action's cells, as predicted (the
  counts: [History.md](History.md), the R19 row).
  The family re-solved cold, with an empty proof cache: lake exit 0, 4 978 ✅
  / 0 ❌ / 0 💥 / 0 ⏱, no cache hit, 505 s for the proof family after
  407 s for the model.
* **The premise.** `TimedJustice` has no re-dissemination row any more.
  `cast_fb_commit` and the `avail` family are `Δ`-rows, the first in its own
  field `fbCommit`, split at its trigger `fbCommitGate`. The gate
  checklist ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)'s
  header) admits the actor's own MVBA output. `deliver_chunk_assigned` has
  no gate. The untimed `FJustice` loses the re-dissemination row, and its
  `Owed` loses that line.
* **The schedule.** `Chorus.Schedule.Δ_le_Δsync : mvba.Δ ≤ mvba.Δsync`.
* **(Δ-avail), derived.** `Chorus.availWithin_of_timedJustice`: in every run
  satisfying `TimedJustice` and `ValidBridge`, at every schedule, every
  projection's timed run satisfies `Mvba.AvailWithin`.
  `timedMvbaAdmissible_of_rows` takes only (Δ-justice) and (T-timer) of the
  MVBA. `SyncAtMvba` and `TimedTerminationClaimAtMvba` state the timing
  model and the claim at the system's MVBA with only those two clauses
  assumed, and `Chorus.timed_termination_atMvba` and
  `…_tight_atMvba` are proven over them (`sync_of_syncAtMvba`). The timed
  claim at the system's MVBA therefore assumes no availability fact that
  Chorus provides.
* **The proofs.** The chunk is there from the correct signer's signature on
  (`fb_pos_sig_chunks`, by `record_backed` over `fb_pos_sig_chunks_flip`).
  `eventually_fbcommit_sig` and `fAvail_of_fJustice` read it directly, and
  the latter no longer takes `ActiveFrom`. `within_fb_chunk` is gone, and
  `within_finalized_late` meets the vote's split row with the chunks at
  saturation. The bound is unchanged: `T₀ = M + 4Δ + ℓ_MVBA + 7δ`,
  `Lchorus`, `Ltight`.
* **The witness.** `schC` overrides `Δsync := 1` (`Mvba.Schedule.fixedNat`
  and the MVBA's witness are untouched, and `Mvba.Witness.ell = 24`). Its
  clock-0 re-dissemination case is gone, and
  `timedTermination_premises_satisfiable` states `SyncAtMvba`.

**Expected pins, written before the build.** Chorus: one action and one
state relation, no property: `101 + 46 × (101 + 1) + 47 = 4840` (from
4737). Mvba: the model file does not change (`decide` becomes an input in
[Mvba/Compose.lean](../Cadence/Mvba/Compose.lean) only), so `1507` stays,
and NoLock, which copies the model, needs no mirror. FallbackReceipt:
`220`.

#### Bounds.md §6.4.2 What `s.deadline − Δ ≥ GST` becomes, as written before R31

**What `s.deadline − Δ ≥ GST` becomes.** Today it is
`all_honest_recorded`, the antecedent of proposal inclusion, and the
`on_time` of the contract. It stays exactly that: `on_time` is a state
fact in the fragment, and neither timed target needs it. A timed
corollary would derive it from "a correct proposer proposes at
`D − Δ ≥ GST`" with the deliver-Δ and record-δ rows, before the marker
fires at `D`. That meets a boundary. At δ > 0 a chunk that arrives exactly
at `D` is recorded too late. At δ = 0 it ties with the marker, which
leaves the chunk and the marker at the same instant. So the paper's
premise needs strict delivery or a tie-break. This is a finding for
whoever takes that corollary on, and it is not needed here.

#### Bounds.md §6.4.3 The S3 and S4 milestone records, as written

**The milestones as proven** (S3, 2026-10-01,
[Chorus/Timeline.lean](../Cadence/Chorus/Timeline.lean)). Up to the MVBA
proposals, each milestone is a lemma whose statement carries its deadline.
The premises are (Δδ-justice), (P-phase), C2 (for `D ≤ t + Δ`), and the
gate on the window (`ActiveUntil`, from C1 on S4's branch,
`activeUntil_of_not_finalized`). Neither the MVBA's timing nor the bridge
enters before the proposals, except that the proposed vector must be
certified and `Valid` (S4 supplies it from the evidence at saturation).

| milestone | lemma | by | `δ`s |
|---|---|---|---|
| every correct validator participating | `exists_start` | `t` | 0 |
| the deadline | `deadline_le_of_start` + (P2) | `D ≤ t + Δ` | 0 |
| first-round votes, all at one index | `within_voted`, `within_all_voted` | `M + Δ + δ` | 1 |
| a fallback signature per proposer | `within_fb_sig` | `M + 2Δ + δ` | 1 |
| the second-round vote, fast or fallback | `within_cast`, `within_all_saturated` | `M + 2Δ + 2δ` | 2 |
| the MVBA's trigger from correct senders | `correctTrigger_of_saturated` | (the same index) | 2 |
| a correct fast voter's FastQCs, everywhere (F7) | `within_complete_fast_metablock_by` | `M + 3Δ + 2δ` | 2 |
| the proposal on a correct `FBCert` | `within_input_of_fbcert` | `M + 3Δ + 2δ` | 2 |
| the proposal on the own meta-block (F9) | `within_input_of_fast` | `M + 3Δ + 3δ` | 3 |
| every correct validator's proposal | `within_all_input` | `t_M = M + 3Δ + 3δ` | 3 |
| a correct proposer's chunk, delivered and recorded | `within_proposal_recorded` | `max(X, GST) + Δ + δ`, if `< D` | 1 |

The last row is not on the termination path: it is the proposal-inclusion
corollary's first step, with the strict `< D` that Bounds.md §6.4.2's "What
`s.deadline − Δ ≥ GST` becomes" anticipated. The fallback chunks of the
paper's `M + 3Δ` milestone are left to S4, where the fallback commit round
needs them (Bounds.md §6.4.6, the reassessment).

**The MVBA tail and the round, as proven** (S4, 2026-10-02, R18,
[Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean)).
On the branch where no correct validator has finalized by the vote deadline
`X_v`, everyone is active until then (C1, `activeUntil_of_not_finalized`).
With `t_M = M + 3Δ + 3δ` and `X_d = t_M + ℓ_MVBA`:

| milestone | lemma | by | `δ`s |
|---|---|---|---|
| a FallbackQC signer's signature is there at its second-round vote | `fb_pos_sig_flip`, `fb_pos_sig_at_cast` | (saturation, `M + 2Δ + 2δ`) | 2 |
| its chunk sent to every validator with the signature (F8; F15, R19) | `fb_pos_sig_chunks` (was `within_fb_chunk`) | (saturation; the hop due by `M + 3Δ + 2δ`) | 2 |
| every correct validator decides in the MVBA | `within_all_decided` (`T.termination` on the projection) | `X_d` | 3 |
| a correct decision's entries recorded (the handlers) | `within_recorded` | `X_d + δ` | 4 |
| `mvba_complete` (`mvba_terminate`) | `within_complete` | `X_d + 2δ` | 5 |
| each fallback commit vote, under the validator's own `B′` | `within_fbcommit_sig` | `X_v = X_d + 3δ` | 6 |
| a correct fbCommitQC (the honest quorum's votes) | (collapsed in `within_finalized_late`) | `X_v` | 6 |
| every proposer's entry assigned | `within_assigned` | `X_v + Δ` | 6 |
| finalized | `within_finalized`, `within_finalized_late` | `T₀ = M + 4Δ + ℓ_MVBA + 7δ` | 7 |
| the split: early finalizers by totality | `within_finalized_tight` | `X_v + Δ + 2δ = M + 4Δ + ℓ_MVBA + 8δ` | 8 |

`T₀` is the reassessment's expectation, term for term. Five facts of the
proof, each in the file's header:

* **No common `B′`** (P2). Each validator waits and votes under its own
  decision. The handlers run on one correct decision, and the MVBA's
  agreement makes every correct decision's entries the recorded ones
  (`mvba_recorded_entry`, as in the untimed `eventually_mvba_complete`).
* **The chunks precede the decision.** A correct FallbackQC signer signed
  before its second-round vote (`fb_sign_pos`'s guards), so its signature is
  at the saturation index. This is the first-flip fact the reassessment
  asked for. Since R19 (F15) the same step sent every validator its chunk
  (`fb_pos_sig_chunks`), and the chunks' hop is timed at the vote's split
  row.
* **The MVBA tail is the contract's.** `T.termination` on `mvbaTimedRun p`,
  the proposals carried forward (`Projection.timed_forward`), their validity
  the MVBA's own `input_valid`, no abandonment before `t_M + ℓ_MVBA` (the
  branch, with `abandoned_of_mvba_abandoned`), the decision carried back
  (`Projection.timed_back`, `TimedRun.byGstBound_iff`).
* **`0 ≤ ℓ_MVBA`.** `TimedTerminationClaim` is generic in the MVBA contract
  `T`, and a time type may have negative elements. A contract with a negative
  latency would put the decision before the proposals' deadline, and the
  arithmetic of the round fails. The generic theorems take `0 ≤ T.ℓ`. It is
  a hypothesis on the contract instance, not on runs, and the system's MVBA
  has it (`mvbaSchedule_ℓ_nonneg`): `Chorus.timed_termination_atMvba` and
  `Chorus.timed_termination_tight_atMvba` take nothing beyond the MVBA
  instance's own hypotheses, less its correct supermajority, which the
  family proves (`hqeFin`). `TimedTerminationClaim` is unchanged.
* **The δ-multiple.** The paper's route, the outer split at `T₀` with
  totality's `Δ + 2δ`, gives `5Δ + ℓ_MVBA + 9δ`, exactly `Lchorus`. So
  `Lchorus` stands as S3 restated it.


#### Bounds.md §6.4.5 F11 and the second run, as written

**What the model found: F11, re-dissemination off the fallback path.**
The first version of the run had validators 1 and 2 re-disseminate the
proposer's chunk at clock 0. The model's `redisseminate_chunk` has no
fallback-path guard, and its row was owed whenever `f+1` correct validators
held the chunk (`CorrectChunkQuorum`), with only `Active k` as its gate. So
`TimedJustice` obliged every active correct validator to re-disseminate
within `Δ`, on the fast path too. The paper re-disseminates only on the
fallback path: inside the fallback-entry rule (Algorithm 5, line 12 (`line:fb-redisseminate`)) and
in the fallback commit round's wait (Algorithm 5, line 39 (`line:fb-commit-wait`)). **Counterexample**
(`Δ = 1`, `δ = 0`, `D = 1`): a fast-path run whose messages take their full
`Δ` (FastQCs at 2, finalization and abandonment at 3) leaves the row for
validator 1 owed, enabled and gated open from clock 0 to clock 1. It must
fire by clock 1, and the paper's validator never sends it. Such paper runs
violated the premise, so both timed claims said nothing about them. A forced
re-delivery could even change outcomes: a chunk arriving before the
deadline turns a negative vote entry positive. The untimed `FJustice` had
the same gap for a validator that stays active. **Fixed in R11**
(`bd887c5`): the row is owed on the fallback signer's own positive entry
(F8), or once the sender has itself decided in the MVBA and the chunk is
decodable from correct holders. `Chorus.termination` was re-proven against
it. The witness needed no change, because its proof never used the
owed-condition; it only drops the forced re-dissemination steps.

**A second run, through the MVBA arm** (recommended, not required). This
run satisfies the proposal families, the handoff family and `ValidBridge`'s
completeness vacuously: nobody proposes to the MVBA and nobody decides.
That is enough for joint satisfiability, since one model suffices (Bounds.md §6.3).
A run that fires the case-(a) proposals, decides in the MVBA and finalizes
through the fallback commit round would show those three premises holding
non-vacuously, together with the rows that guard them. It would also be the
first witness in which `valid := (· = v⋆)` meets an actual decision. **Not done in R12:** it needs a hand-stepped MVBA decision (views,
votes and the commit certificate of `Mvba.Witness`'s run, driven from
Chorus's fallback or case-(a) proposals) and the fallback commit round, well
over the half day it was allowed. Consistency does not depend on it.

#### Bounds.md §6.4.6 Staging and sizing, with the S1–S6 records and the reassessment after S3

#### 6.4.6 Staging and sizing

One focused session each, give or take. Reassess after S3, as Bounds.md §6 asked
after its step 2.

1. **S1: the joint edit** (option A, C1/C2, and the ride-alongs of
   Bounds.md §6.4.1). It touches [Chorus.lean](../Cadence/Chorus.lean) and
   [Interfaces.lean](../Cadence/Interfaces.lean), and gives
   [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) its step/trans
   split.
   * It adds `InputLabel` to [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean).
   * It re-proves `Chorus.termination` against the extended
     `TerminationClaim`, with the early-finalization split.
   * It updates the monitor decoders.
   * It does the cold re-solve, updates the `#veil_status` pin, and
     re-states the axiom pins.
   Probably two sessions. **Must not overlap** the untimed non-vacuity
   work (which waits, Bounds.md §6.4.5), MVBA upgrade step 5b if it edits
   Interfaces.lean (bundle into S1 or serialize), or any other
   Interfaces.lean edit. One family re-solve at a time.

   **Done** (2026-09-29, one session, the "R1" PR). Option A with C1/C2 and
   the sender parameters, as decided. What an auditor should know:

   * **The model.** `participating`/`abandoned` per validator, written only
     by the inputs `participate i` and `abandon i mvba_next`. Every sending
     rule of Bounds.md §6.4.1's list is gated on `participating i ∧ ¬ abandoned i`,
     and the processing rules are exempt. `broadcast_commitqc_*` and
     `redisseminate_chunk` take a sender, gated when it is correct. The
     gates read only the acting validator's local state: no new network
     read, no fourth exception category. **No invariant was added.**
     `#veil_status Chorus` goes from 4222 to 4428: 101 init cells +
     42 actions × (101 + 1 step property) + 43 does-not-throw, as predicted
     before the build.
   * **The contract.** C1 in `bounded_termination` and `totality`; C2, with
     the datum `deadline : slot → time`, in `bounded_termination`. Both are
     antecedents in the rely form. The `…Safety` fragment is untouched, and
     no field was weakened.
   * **The claim.** `TerminationClaim` gains `AllParticipate` and
     `NoAbandonBeforeFinalizing`, the antecedents of
     `SlotConsensusTemporal.termination`. `Chorus.termination` is re-proven
     at the trio, split on an early finalization
     ([Liveness.md](Liveness.md) §4.7 has the record). `MvbaAdmissible` did
     **not** change shape: the MVBA's abandonment premise is derived on the
     branch that needs it.
   * **The composition.** `Chorus.slotConsensusSafety`'s `step` now
     excludes the inputs. The consequence Bounds.md §6.4.6 named holds: the composed
     system's Chorus is inert until the glue drives the inputs, and glue
     safety is unaffected ([CompositionContracts.md](CompositionContracts.md) §5).
     The glue drives the inputs since R25 ([ConductorBounds.md](ConductorBounds.md) §9, K1).

   Deviations from the plan, each small:

   * **`abandon` forwards every time**, not only "if mvbaInvoked"
     (Algorithm 5, line 48 (`line:fb-abandon`)). The difference is unobservable: the MVBA's own
     `abandon()` has no precondition, a party that has not proposed sends
     nothing in the MVBA, and after `abandon` Chorus never proposes to it.
     The conditional form would have needed a negative read of the MVBA's
     state, or a new local flag.
   * **`propose` loses its fairness.** It was weakly fair before; as the
     contract's `propose(P)` input it now carries none. No link of the
     proof fired it.
   * **Two run-level first-flip facts** (`committed_pos_assignable`,
     `committed_neg_assignable`) replace what an invariant would have given:
     `local_committed_*_backed` keeps the MVBA record but not the fallback
     commit certificate beside it, and the early-finalization branch needs
     both.
   * **FallbackReceipt.lean's header** was aligned too (Bounds.md §6.4.1 had left it
     for its own next edit). The receipt family replays warm.
   * **The monitor**: the silent MVBA stub has no `abandon`, so `abandon` is
     never enabled under the monitor, a coverage gap of the same kind as
     the decision handlers ([Monitor.md](Monitor.md) §8). The fixtures gained
     `participate` lines and the collector argument by hand.
   * **Quiescence** is not proven here. The gates make it provable in the
     paper's two-part shape; the one-step statement belongs to S5 with the
     rest of the `SlotConsensusTemporal` instance.

   **Then S1b: fired-once flags, and fairness over plain enabledness**
   (decided 2026-09-30, after R3; Bounds.md §6.4.7 is the plan). Both models change:
   every fair action that can stay enabled after it has fired gets the
   local "not already" guard the paper gives it. Then the fairness
   premises go back to plain enabledness. It comes **before S2 and before
   the witness (S6)**, since both are written against the final model and
   the final premises. **Three sessions:** R4 (the Mvba model) and R5 (the
   Chorus model), in parallel, with their cold re-solves serialized, then
   R6 (the flip to plain enabledness, plain Lean only), after both have
   merged. The flip waits for both because the fairness definitions are
   shared (Bounds.md §6.4.7, "Staging").
2. **S2: timed scaffolding, statements only.** In [Timed.lean](../Cadence/Timed.lean):
   * the (Δδ-justice) clause and `BoundedFairFamily`;
   * the timed projection (`Component.Projection` plus a clock), with its
     back-transfer lemma and, optionally, `boundedFair_iff`.

   A new `Cadence/Chorus/Schedule.lean`, holding:
   * the Chorus schedule (the MVBA's, plus `D`) and the hop table with its
     gates, with a `hop_isSome_iff` coverage pin;
   * (P-phase) and the timed `MvbaAdmissible`;
   * the two claims as `Prop` definitions **before any proof**, the
     discipline of [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean).

   **Done** (2026-09-30, the "R7" PR). Plain Lean only; no Veil file, no
   Interfaces.lean edit, nothing re-solved, and every `#veil_status` pin
   unchanged. What an auditor should know:

   * **Timed.lean.** (Δδ-justice) is `BufferedFair` (one label) and
     `BufferedFairFamily`. With `N = N'`, a trivial gate and `δ ≤ D` it is
     `BoundedFair` (`bufferedFair_iff_boundedFair`). `BoundedFairFamily` is
     the timed twin of `WeaklyFairFamily`. The timed projection is
     `Component.Projection.timed`, with the back-transfer (`timed_back`), a
     forward transfer (`timed_forward`) and `boundedFair_iff`, the timed
     twin of `weaklyFair_iff`.
   * **Chorus/Schedule.lean.** The schedule, `hop` (pinned by
     `hop_isSome_iff`), `gate`, `Owed`, `TimedJustice`, `PhasePunctual`,
     `TimedMvbaAdmissible`, the caller's conditions, and the two claims
     `TimedTerminationClaim` and `TotalityClaim`. The header states the
     gate checklist. Bounds.md §6.4.2 has the table as built and Bounds.md §6.4.5 the ledger
     draft.

   Changes to the plan, each small:

   * **An owed-condition per row** (F5, F6, Bounds.md §6.4.2). The generic clause
     takes a condition `C` beside the gate: what the environment must have
     supplied for the step to be owed. For Chorus that is correct senders,
     and, for `cast_fb_commit`, the voter's own decision. With `C` trivially
     true the clause is Bounds.md §6.4.2's verbatim.
   * **The claims are generic in the MVBA contract `T`.** Both consume only
     `T.Admissible` and `T.ℓ`, so the statement holds for any
     `T : MVBATemporal … (S := mvbaSafety thM)`, and the system's MVBA is
     the instance `T := Mvba.mvbaTemporal …` (`mvbaTemporal_ℓ`,
     `timedMvbaAdmissible_atMvba_iff`, by `rfl`).
   * **The `δ`-multiple of `ℓ` is fixed now**, at `8`
     (`Lchorus Δ δ ℓM = 5Δ + ℓM + 8δ`; restated as `9` by S3, F9). The docstring derives it milestone
     by milestone. S3–S4 confirm it, or restate it before the instance, as
     `Lcert` was.
   * **`TotalityClaim` takes fewer premises than the class field allows**:
     (Δδ-justice), participation synchronized within `d`, and C1. Neither
     the phase timers, nor the MVBA, nor the bridge is a premise. That makes
     the claim stronger, and it implies the field.
   * **`mvba_propose`'s gate is the MVBA arm** (Bounds.md §6.4.2), and the family is
     owed on a correct trigger only.

   Two findings were left open for R8, before the witness and S3:

   * **F5 on the untimed premises**: both `FJustice`s, Chorus's and the
     MVBA's, owed steps enabled by Byzantine senders' messages.
   * **C15**: the MVBA decision certificate's delivery is Chorus's protocol
     step (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff"), which the
     model did not have.

   **Both closed in R8** (2026-09-30, Bounds.md §6.4.2 "The decision handoff (C15):
   the design" is the plan as written before the build). What an auditor
   should know:

   * **The premises.** Both untimed `FJustice`s owe a step only for
     messages from correct senders, with the timed rows' own
     owed-conditions: `Chorus.Owed` (now in
     [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean), shared with
     `TimedJustice`) and `Mvba.Owed` (a correct leader, a correct quorum:
     `Delivers`' sender part, `Mvba.owed_of_delivers`). Two amendments to
     R7's table came out of the re-proof, both the paper's forwarding rules:
     F7 (a correct fast voter's `FastBlock`) and F8 (the decoding fallback
     signer's re-dissemination), Bounds.md §6.4.2.
   * **The model.** One action, `accept_mvba_commitqc`, with its fired-once
     record; no invariant. `#veil_status Chorus` 4737 → **4840** = 101 +
     46 × (101 + 1) + 47, as predicted. The Chorus family re-solved cold,
     every file with 0 cache hits.
   * **The contract.** `MVBASafety` gains the supplement's strengthened
     interface, additions only (Bounds.md §6.4.2 (b)). At the instance `decide` is an
     input, so the MVBA's claims gain the caller's side: (F-relay) untimed,
     `Relayed` timed (the former `decisions` clause, verbatim), both derived
     inside Cadence. (A-viewsync)'s second clause names a correct decision.
   * **The proof.** `Chorus.termination`'s late branch always takes the
     MVBA arm (`eventually_mvba_route`); the commit route there rested on
     commit certificates that may include Byzantine votes. `Mvba.termination`,
     `Mvba.bounded_termination`, `Mvba.aViewSync_of_sync` and both MVBA
     witness theorems are re-proven; `Mvba.Witness.ell` is unchanged.
3. **S3: totality and the timeline to `M + 3Δ`.** Totality comes first,
   because it is small and validates the scaffolding. Then the links up to
   the MVBA proposals. The reassessment asks two things: did the hop table
   survive the guards, and does the split hop keep the paper's arithmetic.

   **Done** (2026-10-01, the "R11" PR). Totality (Bounds.md §6.4.4, "Proven") and the
   timeline to the proposals (Bounds.md §6.4.3, "The milestones as proven"), plain
   Lean in two new files, every theorem at the standard trio. Three
   statement fixes went in with it, under one commit before the proofs that
   need them: F9 (the proposal's two rules), F10 (`δ_le_Δ`) and F11
   (re-dissemination owed only where the paper sends), Bounds.md §6.4.2. F11 changed
   `Chorus.termination`'s premise, and its proof was re-run (one lemma). No
   model file, no Veil proof file, nothing re-solved, every `#veil_status`
   pin unchanged. F12 was left for a model session, and R12 closed it
   (Bounds.md §6.4.2, "F12 closed").

   **Reassessment after S3.**

   *(a) Did the hop table survive the guards?* Row by row, for the rows the
   proofs exercise:

   * `vote` (δ, gate: active, past `D`): yes, exactly. Its fired-once guard
     `¬ local_voted` lapses only by the vote.
   * `fb_sign_pos`/`fb_sign_neg` (Δ, gate: the fallback arm): yes, with one
     fact the untimed chain did not need. Whether the honest quorum's votes
     are positive evidence must be settled once, at the index where they
     have all voted; otherwise late evidence would disable `fb_sign_neg` and
     restart the window. It is: a correct vote is frozen once cast
     (`vote_pos_sig_frozen`, from three existing invariants). The lapses of
     `¬ msg_commit_cast`, `local_path ≠ fallback` and R5's fired-once
     `¬ local_fb_entry` are each the progress wanted.
   * `cast_fallback_vote` (δ): yes.
   * `aggregate_fastqc_*` (Δ, no gate): yes, through F7's disjunct only (a
     correct fast voter's meta-block), the quorum disjunct is not needed.
     Its fired-once `¬ local_fastqc` lapses by the goal.
   * `mvba_propose`: **no**, as one Δ-row (F9); as the paper's two rules,
     yes. Its "no input yet" guard lapses only by an input.
   * `commit_assign_*` (Δ, gate: active) and `finalize_commit` (δ):
     yes, in totality, with the owed-conditions verbatim the commitment
     proofs (`ProofPos`, `ProofNeg`).
   * `deliver_chunk_assigned` (Δ, gate: the proposer active) and
     `record_chunk` (δ): yes; R5's fired-once `local_chunk_sent` lapses only
     with the delivery. `record_chunk`'s phase guard *closes* at `D`, so its
     milestone needs the strict `< D` (the tie Bounds.md §6.4.2 recorded).
   * `redisseminate_chunk`: its owed-condition was wrong (F11); not on the
     path to the proposals.
   * R8's handoff row `accept_mvba_commitqc` is not on the path to the
     proposals; its derivation (`relayed_of_timedJustice`) is unchanged and
     its `δ ≤ Δ + ρ` now follows from `δ_le_Δ`.
   * Not exercised by S3: `commit_sign_*`/`cast_fast_commit` (the fast
     commit vote is never awaited, only counted when it happens),
     `broadcast_commitqc_*` (R8: the late branch takes the MVBA arm), the
     decision handlers, `mvba_terminate` and `cast_fb_commit` (S4).

   Every R5 fired-once guard met on the way lapsed only by the progress its
   link wanted, which `TLRun.withinFrom_of_bufferedFair` absorbs by widening
   the goal; none blocked an owed step. Across all rows, a Δ-row costs
   `max(Δ, δ)`, which is F10.

   *(b) Does the split hop keep the paper's arithmetic at δ = 0?* Yes, term
   for term, once F9 is in: first-round votes by `M + Δ`, the second-round
   vote by `M + 2Δ`, the FastQCs and the proposals by `M + 3Δ` — the
   paper's three milestones — and totality's `Δ`. The split is what keeps
   the fallback entry at `M + 2Δ`: its message part (the votes, by
   `M + Δ`) and its gate (the arm, by `D + Δ ≤ M + 2Δ`) are measured
   separately, where one hop from the later of the two would cost
   `M + 3Δ`. At δ > 0 the multiples are those of the table in Bounds.md §6.4.3,
   `t_M = M + 3Δ + 3δ`, so `ℓ = 5Δ + ℓ_MVBA + 9δ` (restated in
   `Chorus.Lchorus` from R7's 8; S4 confirms the rest).

   *(c) What S4 needs, and what F4 looks like now.*

   * **The MVBA tail.** `T.termination` on `mvbaTimedRun p` of a projection:
     proposals by `t_M` (`within_all_input`, carried to the projection by
     `Projection.timed_forward`); a `Valid` input (`certifiedVector` at the
     saturation index's evidence, `mvba_evidence_of_saturation`, and
     `ValidBridge`'s soundness); no abandonment before
     `max(t_M, GST) + ℓ_MVBA` (`activeUntil_of_not_finalized` on the branch
     where nobody finalizes before the inner split, then the MVBA's
     `abandoned` row through `abandoned_of_mvba_abandoned`). The decision
     comes back by `Projection.timed_back` and `TimedRun.byGstBound_iff`.
   * **The handoff** is already derived (`relayed_of_timedJustice`); S4
     consumes it only through `T.Admissible`.
   * **The fallback commit round**: the decision handlers and
     `mvba_terminate` (δ each, per proposer collapsed by
     `withinFrom_forall`), then `cast_fb_commit` (δ, owed on the own
     decision, F6), the fallback commit certificate (a ghost), the
     assignments and the finalization (`within_assigned`/`within_finalized`
     from Totality.lean, as they stand). **F12 bit here, and is fixed
     (R12).** Before the fix, the DA wait in `cast_fb_commit` covered
     FastQC-backed roots too, and after F11 the only owed source of a
     validator's own chunk under such a root was its own re-dissemination
     after its decision, so the commit vote was due `Δ + δ` after the
     decision. *Reassessed after R12:* a FastQC root now needs no chunk, so
     the vote's own hop is `δ` after the transported decision, as in the
     paper. A FallbackQC root's chunk comes from the correct signer (F8) by
     `M + 3Δ + 2δ`, before the decision at `t_M + ℓ_MVBA`; that needs the
     one first-flip fact recorded above (a correct validator signs
     fallback entries only before its second-round vote), which is S4's to
     prove. F13 is closed (R15): the vote's row is owed under the
     validator's own `B′`, so a root with both certificates is waited for
     as in the paper, and no run is outside the premise for it.
   * **The case split, and F4.** From the milestones: the decision by
     `t_M + ℓ_MVBA`, the fallback commit vote `3δ` later (the two decision
     handlers and `mvba_terminate`, then the vote, `δ` each with the
     handlers collapsed per proposer), the commitment `Δ`, the finalization
     `δ`, so `T₀ = t_M + ℓ_MVBA + Δ + 4δ = M + 4Δ + ℓ_MVBA + 7δ`, now that
     F12 is fixed (R12), and `M + 4Δ + ℓ_MVBA` at `δ = 0`. F4's single split at `T₀ − Δ` still looks right: a validator
     that finalizes before `T₀ − Δ` hands everyone totality's `Δ + 2δ`, and
     on the other branch nobody has abandoned by then, so the chain runs to
     `T₀`, giving `M + 4Δ + ℓ_MVBA + O(δ)`. Nothing in the milestones uses
     the outer split. F4 is decided in S4.
4. **S4: the MVBA tail and the assembly.** *Scheduled after the
   realignment to the paper target `48cac9a`
   ([PaperAlignment.md](PaperAlignment.md) §8), on the realigned model.*
   `T.termination` through the
   projection, the fallback commit round, and the case split, giving the
   bound. F4 is decided here.

   **Done** (2026-10-02, the "R18" PR). Plain Lean in one new file,
   [Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean),
   every theorem at the standard trio; no model file, no Veil proof file,
   nothing re-solved, every `#veil_status` pin unchanged. What an auditor
   should know:

   * **The claim.** `Chorus.timed_termination` is `TimedTerminationClaim`
     at the paper's bound `5Δ + ℓ_MVBA + 9δ` (`Lchorus`, unchanged), at
     the concrete family and the system's configurations, for every MVBA
     contract with `0 ≤ T.ℓ`; `Chorus.timed_termination_atMvba` at the
     system's MVBA, where that is a theorem. The R10 witness run
     instantiates it.
   * **F4, confirmed.** `Chorus.timed_termination_tight` proves
     `4Δ + ℓ_MVBA + 8δ` from the same premises, with one split at the
     fallback commit votes' deadline (Bounds.md §6.4.3, "The assembly, and F4").
   * **The milestones** are Bounds.md §6.4.3's "The MVBA tail and the round, as
     proven". `T₀ = M + 4Δ + ℓ_MVBA + 7δ`, as the reassessment expected.

   Changes to the plan, each small:

   * **`0 ≤ T.ℓ`**, a hypothesis of the two generic theorems on the MVBA
     contract (Bounds.md §6.4.3); the claim's statement is unchanged.
   * **The split point** is `T₀ − Δ − δ`, the vote deadline, rather than
     `T₀ − Δ`: the late branch needs everyone active only until the votes.
   * **(Δ-avail) is not derived** (task 1 of the session). The derivation
     met F15 (Bounds.md §6.4.2), a divergence of the model from the paper's
     re-dissemination, which needs a model change. It is R19's, with the
     schedule constraint `Δ + δ ≤ Δ_sync` the derivation needs.
     `timedMvbaAdmissible_of_rows` still takes the MVBA's three clauses.
   * **The comments of [Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)**
     were brought up to date (comment-only, approved in session).

   **Then R19: F15 closed** (2026-10-02, the "R19" PR; Bounds.md §6.4.2 "F15: the
   design" and "F15 closed"). A model session between S4 and S5. The
   fallback signer re-disseminates inside `fb_sign_pos`, the proposer's
   chunk delivery no longer requires the proposer to be active, and
   `redisseminate_chunk` is gone: `#veil_status Chorus` lost that action's
   cells ([History.md](History.md), the R19 row), the family re-solved cold. (Δ-avail) is derived
   (`availWithin_of_timedJustice`), and the claim at the system's MVBA
   (`TimedTerminationClaimAtMvba`) assumes only the MVBA's own two clauses.
   Changes to the plan:

   * **`Δ ≤ Δ_sync`, not `Δ + δ ≤ Δ_sync`.** Once the chunk is sent with the
     signature, the availability report is a `Δ`-row, which costs
     `max(Δ, δ) = Δ`. The `+ δ` belonged to a sequential reading that the
     atomic step retires.
   * **Two premise rows changed shape**, both weakenings. `cast_fb_commit`
     and `mvba_avail_ready` read a re-disseminated chunk, which now holds
     from its send, so they are `Δ`-rows (the first split at its trigger,
     `TimedJustice.fbCommit`). The gate checklist admits the actor's own
     MVBA output.
   * **The proposer's dissemination**, the same shape as F15, was closed in
     the same re-solve, at the design review's request, not parked.
   * **The witness overrides `Δ_sync`** in its own schedule.
     `Mvba.Schedule.fixedNat` and the MVBA's witness are untouched.
5. **S5: the contract instances. Done** (R20, 2026-10-02):
   [Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean). With it the
   Chorus bounds leg is complete. The plan was `SlotConsensusTemporal` at the new
   fragment, which includes:
   * Quiescence from the gates and the MVBA's `quiescence`. Since R19 every
     correct chunk send happens inside a gated step: the proposer's in
     `propose` (whose record is `msg_proposer_signed`) and a fallback
     signer's in `fb_sign_pos` (`local_chunk_sent i I j m`). A later
     `deliver_chunk_assigned` delivers an earlier send and is not a new
     send;
   * `admissible_exists` from an idle run;
   * Termination, as the unbounded corollary of the bounded one.

   Then `SlotConsensusWithTotality`, and the `…_of_temporal` join with its
   `rfl` lemma. After that:
   * the [Cadence.lean](../Cadence.lean) rows and pins, with the verification-status
     text in [CLAUDE.md](../CLAUDE.md), [Architecture.md](Architecture.md)
     §4 and [CompositionContracts.md](CompositionContracts.md) §5;
   * the (A-sc-termination) entry, which moves from assumed to discharged.

   **The record.** `Chorus.chorusTemporal` and `Chorus.chorusWithTotality`,
   at the system's configuration, every field proven, none weakened;
   `Chorus.slotConsensusFull` joins them with the fragment through
   `slotConsensus_of_temporal`, and `slotConsensusFull_toSafety` is `rfl`.
   `ℓ = Lchorus Δ δ ℓ_MVBA` and `d_tot = Ltot Δ δ Δ` are pinned by `rfl`,
   and are the paper's `5Δ + ℓ_MVBA` and `Δ` at `δ = 0`. Four changes to
   the plan:
   * **Termination is `Chorus.termination`, not the unbounded corollary of
     the bounded claim.** The untimed field's antecedents are participation
     and C1 only; the bounded claim also needs Δ-synchronized participation
     and C2, which the field does not give. `Admissible` carries both
     claims' premises, each by name.
   * **The contract's Quiescence was mis-stated, and is corrected** (approved
     by Lars): `SlotConsensusTemporal.quiescence` quantified over every
     transition, reachable or not, and its MVBA half needs two facts that
     hold only along a run, an MVBA proposal is made while participating
     (`participating_of_mvba_proposed`) and an abandonment is forwarded
     (`mvba_abandoned_of_abandoned`). The field now takes `S.reachable st`,
     as does `ACSTemporal.quiescence`, which had the same shape and no
     consumer ([CompositionContracts.md](CompositionContracts.md) §5).
   * **`admissible_exists` is a generic idle run, not the R10 witness**,
     which is one fixed instance: from any initial state of any
     configuration, nobody participates, the markers fire at the landmarks,
     and the caller abandons one validator at every other step. It needs a
     non-empty proposer set (Bounds.md §6.4.5; P14) and a view after the first with a
     correct leader, which `LeaderRotation` gives.
   * **The deadline is per slot** (`FamilySchedule`: one MVBA schedule and
     `D : slot → time`), since the class's `deadline` is a function of the
     slot; `ByzNodeSetHonestQuorum` is built for the family (`hqeFin`)
     rather than taken.
6. **S6: non-vacuity. Done** (R10, 2026-10-01): the final ledger and the
   one witness, [Chorus/Witness.lean](../Cadence/Chorus/Witness.lean)
   (Bounds.md §6.4.5). It touched no model file. It found F11 (re-dissemination owed
   off the fallback path), which R11 fixed in the statements.

Total: six to eight sessions. As in the MVBA leg, the dominant risk is
statement churn: F1–F4 are the churn this record tries to absorb up
front, before any Lean.

**What the Conductor's timed claims need from this leg.** The
Conductor's Totality, `B`-Boundedness and `R`-Recovery
(`OrchestratorTemporal`) consume Chorus's claims in
Proposition 13 (`prop:window-synchronization`) (totality), Proposition 14 (`prop:conductor-open-to-complete`)
(ℓ-termination), and the recovery chain through `Φ_oc = ℓ_chorus + d_tot`
and the parameter assumptions of Algorithm 7 (`algorithm:conductor`). For those proofs
to go through, this leg must hand over the following.

* **Premises the composition can discharge.** Each of Chorus's caller
  conditions has to be one a composed run proves:
  * participation by `t`: the glue invokes `participate` at `open`
    (Algorithm 1, line 17 (`line:participate`));
  * Δ-synchronized participation: the Conductor's own opening totality
    (Lemma 15 (`lemma:conductor-totality`));
  * C2: `integrity_timing`, with `deadline s = start_time s + Δ`;
  * C1: the glue abandons only after finalizing (Algorithm 1, line 23 (`line:abandon`)).

  C1/C2 are phrased with that in mind, as antecedents over the class's
  own observables.
* **`ℓ` and `d_tot` as data, with closed values.** They appear in
  assumptions (1)–(4) of Algorithm 7 (`algorithm:conductor`). They are fields already;
  the instance pins them.
* **Totality in the tolerance-parametric form of Bounds.md §6.4.4.** This is F3.
  The ratchet needs Chorus's latency not to exceed the tolerance the
  Conductor grants. At δ = 0 both are Δ, and the paper's induction goes
  through. At δ > 0 `max(Δ, d) + 2δ > d` for every `d`, so the Conductor
  leg has to choose. It can work at δ = 0, the paper's instantaneous
  local computation. It can find a δ-robust statement, for instance by
  re-synchronizing on the absolute start times, as
  Algorithm 7, line 27 (`line:conductor-wait-for-open`) does once the windows are ahead of the
  clock. Or it can record the degradation as a finding. **Proposal (C3,
  to the Conductor leg):** leave `syncParticipation_def`'s tolerance at Δ
  for now. The parametric lemma means this leg's statement does not
  pre-empt the choice.
* **One time theory and one Δ across the system.** Chorus, the MVBA, the
  Conductor and the ACS share the run's clock. So the Conductor leg
  should take the same schedule record rather than a second Δ.
* **Two edits outside this leg**, recorded so that neither comes as a
  surprise:
  * After S1, `Chorus.slotConsensusSafety`'s `step` excludes the inputs,
    so the glue's `sc_step` (which requires `sc.step`) can no longer
    participate. The composed system's Chorus is then inert until the
    composition leg gives the glue its `participate` / `propose` /
    `abandon` actions. The glue's safety theorem is unaffected: it is
    generic, and inertness only removes behaviours. Done in R25
    ([ConductorBounds.md](ConductorBounds.md) §9, K1).
  * Corollary 4 (`cor:chorus-correctness-within-cadence`) then closes the loop, which
    is Bounds.md §6 step 5.

#### Bounds.md §6.4.7 The S1b plan (frame, inventory caveat, fairness side, costs, staging) and the R4, R5 and R6 records

#### 6.4.7 Fired-once flags: fairness over plain enabledness

*The plan for S1b (Bounds.md §6.4.6), decided 2026-09-30 after R3 (PR #48). **S1b is
done**: the Chorus half in R5 ("The Chorus half: done"), the Mvba half in R4
("R4 done: the Mvba half") and the flip in R6 ("R6 done: the flip"), the
records at the end of this section.*

**The decision.** Disabledness is modelled in the protocol, not resolved
in the proof. Every fair action that can stay enabled after it has fired
gets a local "not already" guard, as the paper describes the rule. Once
none is left, the fairness premises use **plain enabledness** again: an
action enabled from some point on eventually fires. The auditor's premise
then has no qualifier about state-changing steps. Today it has one, and
the reason for it takes Bounds.md §6.2.4 to explain. R3 made fairness count only
state-changing steps (TLA+'s `⟨A⟩_v`). That was sound, and weaker than
before, but it resolves scheduling non-determinism in the proof that an
implementation resolves in its protocol logic. The model moves closer to
the paper; the premises and the proofs get simpler.

**Where the non-determinism is.** Most honest per-validator actions
already disable themselves after firing: `vote` (`¬ local_voted`),
`send_commit` (`¬ commit_sent`), the timeouts (`¬ timed_out`), `decide`
(`∀ E, ¬ decided`), the leader's proposal (`¬ proposed_in`),
`commit_assign_*` (`¬ local_committed`), and since R3 `adopt_prepqc` (the
lock-view guard). Two sets do not; they are **the inventory to work
from**.

* **Mvba: the anonymous assemblies** `form_prepqc`, `form_commitqc`,
  `form_tc_lock` and `form_tc_nolock`. They have no validator, and a quorum
  parameter `q`, so once the certificate exists every `q`-variant stays
  enabled without effect. In the supplement (at the paper target) each is a step of
  one validator with a local condition:
  * `TryFormPrepQC`: pᵢ forms `prepareQC` if it "has not already formed a
    prepare certificate in the current view". This is `adopt_prepqc` since
    R3, and it is done;
  * the commit certificate: pᵢ forms `CommitQC` "provided that it has not
    already learned a decision certificate", and records it as
    `DecidedQC_i`;
  * the timeout certificate: "upon first collecting 2f+1 valid timeout
    messages", pᵢ forms `TC_{s,v}` and processes it through `SyncView`
    (Supplement, Algorithm 1, line 85 (`line:mvba:ht-advance`)).
* **Chorus:** `aggregate_fastqc_pos/neg i j …` (Algorithm 4, line 18 (`line:fast-formqc`)) and
  `broadcast_commitqc_pos/neg c j …` (Algorithm 4, line 31 (`line:fast-collect-commit`),
  Algorithm 4, line 33 (`line:fast-broadcast-commitqc`)). Each has an actor and no fired-once
  guard. **An assumption to confirm:** the published paper writes these as
  `upon` handlers of an event-driven protocol, without "first time" (only
  the fast meta-block rule says it). The plan reads an `upon` handler as
  running once when its condition becomes true. That is the conventional
  reading, but the paper states no convention, so it is a question for the
  authors, recorded as paper-side finding P6 in
  [PaperAlignment.md](PaperAlignment.md) §6.

The inventory may not be complete. The acceptance criterion below is what
decides that, not this list. Candidates to check first:
`redisseminate_chunk` (re-delivery of a chunk already received),
`record_chunk`, the phase markers, and every assembly with a quorum
parameter.

**The shape.**

* A **per-validator** action with a quorum parameter (no `∃`-quorum ghost
  in a guard, as in `adopt_prepqc i v e q`). It sets a **local** record of
  what it formed, and a guard on that record's absence disables every
  `q`-variant at once. A negative read of the actor's *own local* state is
  what every existing honest guard does; no network relation is read
  negatively, so the monotone-network contract is untouched
  ([ChorusDesign.md](ChorusDesign.md) §3.1.1). It also sets the network
  certificate relation, as `adopt_prepqc` sets `msg_prepqc`, where the
  certificate is carried on (timeouts, broadcasts).
* The **anonymous forming stays**, but is **not fair**: it is the
  adversary's capability to aggregate signatures it saw, so safety's
  adversary is unchanged. It moves into an unfair label class (with the
  `byz_*` family, or its own class, with a `not_justice_of_*` pin), and
  the hop tables lose it. Where an honest per-validator action replaces it
  in a chain, the chain's link changes accordingly.
* Where the effect record itself is the natural flag (`aggregate_fastqc_*`
  sets `local_fastqc_*`), the guard is its absence, and no new relation is
  needed.
* At most 10 action parameters. An invariant only if the cleanest proof
  needs one (backing of the new local records is the likely one).

**The fairness side (R6).**

* [Fairness.lean](../Cadence/Fairness.lean): `WeaklyFair`,
  `WeaklyFairFamily` and `StronglyFair` over `Enabled` again.
  [Timed.lean](../Cadence/Timed.lean)'s `BoundedFair` over `Enabled` too.
  `EnabledMove` stays only as the vocabulary of the lemma below.
* Both `FJustice`s and `Mvba.BoundedJustice` are restated with plain
  enabledness, and their docstrings drop the state-changing qualifier. The
  proofs lose their side conditions (`EnabledMove.of_enabled_of_effect`,
  `eventually_of_weaklyFair`), unless keeping `eventually_of_weaklyFair`
  in plain form reads better.
* **The acceptance criterion, machine-checked, per model (R4 for Mvba,
  R5 for Chorus):** at every
  reachable state, every enabled fair label is move-enabled
  (`∀ l, JusticeLabel l → Enabled … st l → EnabledMove … st l`). It says
  the model has no fair action that stays enabled without effect, so the
  flag discipline is checked rather than read. For the audit surface it is
  the statement that, for this model, weak fairness over plain enabledness
  and over state-changing steps are the same premise. A label that fails
  it belongs in the inventory above. Proven per action from the guards and
  the generated frame lemmas, in plain Lean, not as a Veil cell. R6's
  docstrings cite both lemmas: they are what makes the plain premise the
  same premise as R3's.

**What it touches, and what it costs.**

* **R4:** [Mvba.lean](../Cadence/Mvba.lean), with
  [Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) mirroring it (the
  witness moves and is re-pinned, with `sequential := true`), and the
  whole Mvba liveness and timed stack: the hop table, `Delivers`, the
  chains, `Lcert` if a milestone moves, and the witness. Check
  [Mvba/Compose.lean](../Cadence/Mvba/Compose.lean)'s step facts (the
  `mvba_tr` proofs) against the new per-validator actions. If the label
  change reaches Chorus's projection of the MVBA
  ([Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)'s
  `MvbaStepLabel` and `mvbaComponent`) or
  [Chorus/Termination.lean](../Cadence/Chorus/Termination.lean), R4 says so
  and coordinates with R5; it does not edit those files silently.
* **R5:** [Chorus.lean](../Cadence/Chorus.lean) and the Chorus liveness
  files, and the monitor, which R1 needed in full: both label decoders,
  `Cadence/Monitor/ChorusMonitorGen.lean` and the `traces/*.jsonl`
  fixtures, with all three monitor suites `ALL PASS` afterwards.
* **R6:** plain Lean only — Fairness.lean, Timed.lean, both `FJustice`s,
  `Mvba.BoundedJustice`, the chains' side conditions, and the ledgers.
* Interfaces.lean should not need to change; if a contract field turns out
  to need it, stop and report.
* Two cold family re-solves, one at a time. The `#veil_status` pins
  change with every added action: compute them before the build, update
  them where CLAUDE.md and [Architecture.md](Architecture.md) own them.
  Budget the manual cells: `adopt_prepqc`'s lock-persistence cell is the
  precedent for any per-validator action that creates a prepare
  certificate.
* Docs: R4 and R5 record their model changes (the inventory above, pins,
  History rows). R6 does the premise docs: Bounds.md §6.2.4 (the move-enabledness
  finding becomes history), the Bounds.md §6.3 and Bounds.md §6.4.5 ledgers,
  [Liveness.md](Liveness.md) §2, and a History row.

**Staging, and why the flip waits.** `WeaklyFair` and `WeaklyFairFamily`
in [Fairness.lean](../Cadence/Fairness.lean) are shared by both `FJustice`
definitions ([Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) and
[Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)). Flipping them to
plain enabledness in the Mvba session would put Chorus's premise back on
plain `Enabled` while `aggregate_fastqc_*` and `broadcast_commitqc_*` still
stay enabled without effect. Master would then carry a Chorus premise that
is unsatisfiable at infinite quorum sorts, and `Chorus.termination`'s proof
would break. So:

1. **R4 — Mvba S1b**: the model, NoLock, the Mvba liveness and timed stack
   and the witness, and the Mvba acceptance lemma. The premises stay in
   their current form (state-changing steps); the lemma shows that for
   this model it is equivalent to the plain one.
2. **R5 — Chorus S1b**: the model, the Chorus liveness chains, the
   monitor, and the Chorus acceptance lemma, with the premises again in
   their current form. It can run **in parallel with R4**: the two touch
   disjoint files, provided R4 keeps to the rule above about Chorus's
   projection of the MVBA. Their cold family re-solves run one at a time.
3. **R6 — the flip**, after R4 and R5 have both merged: plain Lean and
   docs, as listed above.

At no point does master carry a premise that is unsatisfiable at some
quorum sort.

**The Chorus half: done** (2026-09-30, session R5). The acceptance lemma is
**`Chorus.justice_enabledMove`**
([Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)): for every state,
reachable or not, and every label `l` with `JusticeLabel l`,
`Enabled (atMvba thM) thS st l → EnabledMove (atMvba thM) thS st l`. The
MVBA proposal is a justice label, so `Chorus.mvba_propose_enabledMove` is its
corollary for each member of the family. Both are pinned at
`[propext, Classical.choice, Quot.sound]`, the first also in
[Cadence.lean](../Cadence.lean). No reachability hypothesis is needed: each
fair action's firing sets a record its guard requires to be unset. The
proof is one lemma per action, read off the transition body.

*The inventory, as the lemma found it.* It was larger than the list above.
Every fair action that could stay enabled after firing now has a "not
already" guard on a record it sets itself. All the reads are negative reads
of the acting validator's own local state (category (L)). No network
relation is read negatively, and there is no new exception category
([ChorusDesign.md](ChorusDesign.md) §3.1.1).

| action | old guard, in words | new guard, in words |
|---|---|---|
| `aggregate_fastqc_pos/neg` | a supermajority signed | … and `i` does not hold this FastQC yet |
| `broadcast_commitqc_pos/neg` | a correct and active collector, or any Byzantine one; `2f+1` cast commit votes | a correct and active collector that has not broadcast a certificate for `j` yet (`local_commitqc_sent c j`); the Byzantine branch is now `byz_broadcast_commitqc_*` |
| `deliver_chunk_assigned` | an honest, active proposer that signed `m` | … that has not sent `i` this chunk yet (`local_chunk_sent j i j m`) |
| `redisseminate_chunk` | a correct and active sender, or any Byzantine one; the data is decodable | a correct and active sender that has not sent `i` this chunk yet (`local_chunk_sent k i j m`); the Byzantine branch is now `byz_redisseminate_chunk` |
| `commit_sign_pos/neg` | `i` holds the FastQC and has not cast | … and has not signed an entry for `j` yet (`local_commit_entry i j`) |
| `fb_sign_pos/neg` | the fallback-entry conditions | … and `i` has not signed its fallback entry for `j` yet (`local_fb_entry i j`) |
| `on_mvba_decide_pos/neg` | `i` decided `v`, the entry is certified | … and `i` has not recorded entry `j` of its decision yet (`local_mvba_recorded i j`) |
| `cast_fb_commit` | the DA wait holds | … and `i` has not cast its fallback commit vote yet (`local_fbcommit_voted i`) |
| `commit_assign_pos` | no *other* root committed for `j` | no root committed for `j` yet |
| `commit_assign_neg` | no positive entry committed for `j` | … and not the negative one either |

Where the plan was wrong or short:

* **`commit_assign_*` did not disable itself.** The list above credits it
  with `¬ local_committed`, but `finalize_commit` sets that, not
  `commit_assign_*`. The per-entry guards were the missing ones.
* **Six more families than listed** (the plan named two): the dissemination
  and re-dissemination of chunks, the commit and fallback entries, the
  decision handlers and the fallback commit vote. For those whose effect is
  a network tuple or a shared record (`mvba_decided_*`), the flag is a new
  local record. The six records are `local_chunk_sent`,
  `local_commit_entry`, `local_fb_entry`, `local_commitqc_sent`,
  `local_mvba_recorded` and `local_fbcommit_voted` (Chorus.lean,
  "Fired-once records"). Where the effect was already local
  (`aggregate_fastqc_*`, `commit_assign_*`), the guard is its absence.
* **The Byzantine branches of the two anonymous capabilities became their
  own unfair actions**, `byz_broadcast_commitqc_*` and
  `byz_redisseminate_chunk`. With the branch left inside the fair action and
  unconstrained, a label with a Byzantine sender would stay enabled after
  firing, which the lemma forbids. Guarding the Byzantine branch would
  constrain the adversary. This is the shape "The shape" gives the Mvba
  assemblies: the adversary's forming stays and is not fair. The honest
  actions now require a correct sender. The termination links already used
  the validator itself as collector and sender.
* **Flag granularity.** One record per actor and proposer, not per root or
  polarity: the paper's commit vote, fallback vote, commit certificate and
  decision each carry one entry per proposer.
* **No invariant.** What the links need of a record (that it comes with its
  effect) is plain Lean: a first-flip lemma per record and one induction
  (`Chorus.record_backed` in
  [Termination.lean](../Cadence/Chorus/Termination.lean)). The decision
  handler's link also uses the MVBA's agreement, to identify the recorded
  entry with the one it waits for.
* **The other candidates** needed nothing. `record_chunk` already requires
  that no positive entry is recorded, the phase markers move the phase, and
  the MVBA proposal's effect is the `Mvba` model's input record, whose
  absence its guard requires.

*Costs.* `#veil_status Chorus`: 4428 → **4737** = 101 initializer cells +
45 actions × (101 + 1 step property) + 46 does-not-throw, written down before
the build and matched (+309: three new actions × 103). Manual cells 12 → 15,
the three additions being the Byzantine assembly actions' copies of the
collector's cells. `TerminationClaim` did not change, and `Chorus.termination`
is re-proven at the trio. The premises keep their move form, and the flip is
R6.

**R4 done: the Mvba half** (2026-09-30, PR #51). What an auditor should
know:

* **The model.** The three rules the supplement gives a "not already"
  condition are one correct validator's step each, in its current view,
  with the quorum as a label parameter, as `adopt_prepqc i v e q` has been
  since R3:
  * `form_own_commitqc i v e q` — `TryFormCommitQC` and `Decide` in one
    handler segment: from `2f+1` `Commit`s of the current view, "provided
    that it has not already learned a decision certificate", form the
    `CommitQC`, record it as `DecidedQC_i` and decide. `DecidedQC_i` is set
    exactly when a validator decides (both decision paths set it), so the
    guard is `∀ E, ¬ decided i E` and no new relation was needed. The
    certificate is put on the network, where `decide` reads it.
  * `form_own_tc_lock i v q r₀ w e` and `form_own_tc_nolock i v q` —
    `HandleTimeout`, "upon first collecting `2f+1` valid timeout messages":
    the local record `tc_formed i v` is new, and its absence is the guard.
    The certificate goes on the network; `SyncView` is the next step
    (`sync_view`, `sync_view_adopt`), as the model has always split it.

  The four anonymous assemblies stay, as the adversary's capability, in a
  new unfair class `AssemblyLabel` (`not_justice_of_assembly`), and left
  the hop table. Only positive reads of `msg_*`; at most 6 parameters. One
  invariant, `tc_formed_backed` (the record is backed by `msg_tc v`), which
  the "not already formed" guard's lapse needs; `form_own_commitqc`'s
  record needs none, since its lapse is the goal.
* **The acceptance criterion**, `Mvba.enabledMove_of_enabled`:

  ```
  theorem enabledMove_of_enabled (l : Mvba.Label node nodeset value view)
      (hj : JusticeLabel l) (hen : Enabled … th st l) : EnabledMove … th st l
  ```

  It holds at **every** state, not only reachable ones: each fair action's
  guard, by itself, rules out that its update is a no-op. It is proven per
  action, in plain Lean, from the guards and the transition bodies, and
  pinned at the trio. **No label failed it**, so the inventory above was
  complete for the Mvba: the four assemblies were the only fair labels
  that could stay enabled after firing.
* **The pins.** `#veil_status Mvba` **1325 → 1507**: 50 properties (3
  safety + 47 invariants), 1 step property and 28 actions give
  50 + 28 × (50 + 1) + 29 = 1507, written down before the build and
  matched. Manual cells 3 → 5: `form_own_commitqc × commitqc_agree` (the
  `form_commitqc` cell's argument) and `form_own_commitqc × agreement` (the
  same argument at the decision the step makes, with `decided_backed`).
  R4 moves neither the Chorus pin (4737 since R5) nor FallbackReceipt's 220.
* **The liveness and timed stack**, re-proven with the premises in their
  current move form ([Fairness.lean](../Cadence/Fairness.lean) and
  [Timed.lean](../Cadence/Timed.lean) untouched):
  * the untimed chains go through a settled correct validator, which
    forms the commit certificate (`eventually_commitqc_of_settled`) and
    the view's timeout certificate (`eventually_tc_of_timed_out_quorum`);
    `Mvba.termination`'s statement is unchanged;
  * the timed premise: the new steps are network hops with first-delivery
    clauses; `Delivers` and `Receiving` lost their separate receiver,
    since every network label is now one validator's step and its
    `in_view` guard is the lower-view discard; the `timeouts` clause names
    the validator that forms the certificate;
  * `good_view_decides` now concludes that some correct validator has
    decided by `E₀ + Lcert`, since the step that forms the certificate
    decides; `bounded_termination`'s second case is therefore
    contradictory, and the transfer term already charged the others'
    decisions. `Lcert`, `Schedule.ℓ` and `Mvba.Witness.ell = 24` are
    unchanged;
  * both witness theorems stand: each correct validator forms its own
    commit certificate, and at the idle state no fair label is enabled at
    all.
* **NoLock** ([Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean)) mirrors
  the three steps. As a restriction, it drops the anonymous `form_prepqc`
  and `form_tc_*`, whose certificates the correct validators now form
  themselves. It keeps `form_commitqc`: the counterexample's view-1 commit
  certificate has to be the adversary's aggregation, since a correct
  validator that forms one decides on it and halts. The checker, still
  with `sequential := true`, finds agreement violated. The witness moved
  and is re-pinned at 25 transitions (was 26): the view-2 certificate is
  now formed and decided on in one step. The search takes 27 min on one
  core (was about 3½ min), because the per-validator steps and
  `tc_formed` multiply the states below that depth. *(Superseded in R6: a fixed
  environment schedule brings it to about a minute, with the same witness;
  "R6 done" below.)*
* **Chorus** is untouched: `MvbaStepLabel`, `mvbaComponent` and
  `Chorus.termination` re-elaborate against the new model without an edit.
  The one change a Chorus reader sees is in meaning, not text:
  `MvbaAdmissible`'s `Mvba.FJustice` of the projected run now ranges over
  the per-validator steps instead of the anonymous assemblies.

Deviations from the plan, each small:

* **No `DecidedQC_i` relation**: the decision is the record (above).
* **`Delivers` lost its receiver parameter**, which had been used only by
  the anonymous assemblies. With it went `NotPast` from `Receiving`; the
  guard's `in_view` says the same.
* **`decide`'s first-delivery clause is no longer used by the bound**: the
  good view's decision now comes with the certificate, and the others'
  come by transfer. The clause is kept, as the supplement's network
  rule; R6 may drop it.

**R6 done: the flip** (2026-09-30). What an auditor should know:

* **The premises read plainly.** [Fairness.lean](../Cadence/Fairness.lean)'s
  `WeaklyFair`, `WeaklyFairFamily`, `StronglyFair` and the projection's
  `WeaklyFairIn`, [Timed.lean](../Cadence/Timed.lean)'s `BoundedFair` and
  [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean)'s `BoundedFairWhile`
  are over `Enabled`: an action enabled from some point on eventually fires
  (within its window, for the timed ones). Both `FJustice`s and
  `Mvba.BoundedJustice` are stated with these notions. Their definitions'
  text did not change; their docstrings dropped the state-changing
  qualifier and cite the acceptance lemma.
* **The bridge, per model**, from the acceptance lemmas and pinned at the
  trio (also in [Cadence.lean](../Cadence.lean)):

  ```
  theorem Mvba.fJustice_iff_move (r : MvbaRun th) :
      FJustice r ↔ ∀ l, JusticeLabel l → WeaklyFairMove r l
  theorem Chorus.fJustice_iff_move (r : ChorusRun thS thM) :
      FJustice r ↔
        (∀ l, JusticeLabel l → ¬ ProposeLabel l → WeaklyFairMove r l) ∧
        ∀ i v, WeaklyFairFamilyMove r (fun l => ∃ mvba_next, l = .mvba_propose i v mvba_next)
  ```

  and, for every fair label, `Mvba.boundedFair_iff_move` and
  `Mvba.boundedFairWhile_iff_move` for (Δ-justice)'s clauses. The right-hand
  sides are R3's premises, TLA+'s `WF_v`. So the plain premise is not a new
  assumption: for these models it is the same one. `EnabledMove` and the
  move forms remain only as the vocabulary of those bridges.
* **The proofs lost their side conditions.** Every
  `EnabledMove.of_enabled_of_effect` is gone, the lemma with them.
  `eventually_of_weaklyFair` and `withinFrom_of_boundedFair(While)` kept
  their statements. The quiet-state lemmas now say what their proofs
  already showed, that no fair label is *enabled* (`Mvba.not_enabled_of_quiet`,
  `Mvba.Witness.quiet`), so both MVBA witnesses stand unchanged in
  statement. `Mvba.termination`, `Mvba.bounded_termination`,
  `Mvba.mvbaTemporal`, both witness theorems and `Chorus.termination` are
  re-proven at `[propext, Classical.choice, Quot.sound]`. No end theorem's
  statement changed.
* **Deviations from the plan.** The helper lemmas that name the vocabulary
  changed with it: `exists_disabled_of_never_fires` concludes `¬ Enabled`,
  `exists_not_moveEnabled_of_not_firesWithin` became
  `exists_not_enabled_of_not_firesWithin`, `not_moveEnabled_of_quiet`
  became `not_enabled_of_quiet`, `boundedJustice_of_quiet`'s hypothesis is
  plain disabledness, and the unused `enabledMove_of_fires_of_ne` is gone.
  `decide`'s first-delivery clause is kept, as the supplement's network
  rule.
* **CI headroom, alongside.** [Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean)'s
  search fixes the environment's schedule (its header, item 5) and drops
  three honest steps the scenario does not take (item 3). The check keeps
  `sequential := true`, and it reports the same pinned witness, in about a
  minute instead of 24 on one core. The Conductor's in-file sweep already
  had a 180 s budget; #51 read its two slowest cells against 60 s.

#### Bounds.md §6.5 The Conductor leg: the kick-off pointer

### 6.5 The Conductor leg: the kick-off record

*Written 2026-10-02 (R22), before any Lean.* The plan for the Conductor's
timed claims (`OrchestratorTemporal`: Totality, `𝓑`-Boundedness,
`𝓡`-Recovery) and for the composition that closes the Cadence loop
(Corollary 4 (`cor:chorus-correctness-within-cadence`)) is its own page,
[ConductorBounds.md](ConductorBounds.md). It takes up the hand-over list of
Bounds.md §6.4.6 ("What the Conductor's timed claims need from this leg"). It answers
F3 and C3 (its Bounds.md §5), and records the findings F16–F24 and the staging K0–K8.

### From ConductorBounds.md

*The Conductor leg's kick-off plan (R22), its decisions with their option analyses, and its staging and per-session records K0–K8 (R24–R32), moved out of [ConductorBounds.md](ConductorBounds.md) in R33. The findings F16–F31 keep their substance there; below is their original wording, with the proposals and closing records.*

#### The kick-off frame, and ConductorBounds.md §1's decisions as written (updated through R32)

*Written 2026-10-02 (session R22), before any Lean. Nothing here is proven
or modelled: it is the plan for the Conductor's timed claims and for the
composition that closes the Cadence loop. [Bounds.md](Bounds.md) §6.4 (the
Chorus leg) set the shape, and ConductorBounds.md §6.2 (the MVBA leg) the timing machinery
this leg reuses. Decisions are recorded with their reasons. The three
questions put to Lars are **decided (2026-10-03)**, each as recommended.
K1, the untimed composition edit, is **done** (2026-10-03, R25; ConductorBounds.md §9), and so
are K2, the model's timing completion (2026-10-03, R26; F21 closed), K3,
the contract edit and the claims stated (2026-10-03, R27; ConductorBounds.md §9), K4, the
window induction with Boundedness and Totality proven (2026-10-03, R28;
ConductorBounds.md §9), K5, Recovery proven (2026-10-03, R29; ConductorBounds.md §9), K6, the contract
instances (2026-10-03, R30; ConductorBounds.md §9), K7, the composed claims (2026-10-03,
R31; censorship resistance 2026-10-04, R31.2, after F31; ConductorBounds.md §9), and K8,
non-vacuity (2026-10-04, R32; ConductorBounds.md §8.2, ConductorBounds.md §9). **The Conductor leg is complete.***
**What those claims feed.** Within Cadence, Recovery gives `𝓡`-Liveness
(Definition 2 (`def:liveness`), Lemma 2 (`lemma:cadence-liveness`)) and
censorship resistance (Definition 3 (`def:censorship-resistance`)) for every
slot starting `2Wτ` after GST. Boundedness gives bounded concurrency (Lemma 5
(`lemma:cadence-bounded-concurrency`)). Corollary 4 makes Chorus's timed
claims (`ℓ = 5Δ + ℓ_MVBA`, `d_tot = Δ`; [Bounds.md](Bounds.md) §6.4) hold
unconditionally in the composed system.

**What the development has today.** The contract states the three properties
as fields of `OrchestratorTemporal`, Totality and Recovery in rely form, with
the `d_tot` form on top in `OrchestratorWithTotality`
([Interfaces.lean](../Cadence/Interfaces.lean); C4, C5, since K3), and
nothing instantiates them. The three claims are stated, with their premises,
in [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean). All three
are proven. K4 proved Boundedness at the paper's `2W − p`, from the
interval form `safety [bounded_tail]` of
[Conductor.lean](../Cadence/Conductor.lean) and the window widths
(`Conductor.boundedness`). It also proved `d_tot`-Totality, by the window
induction (`Conductor.totality`, with Proposition 13 and its three
corollaries; [Conductor/Induction.lean](../Cadence/Conductor/Induction.lean)).
K5 proved Recovery at the paper's `2Wτ`, through Propositions 14–19
(`Conductor.recovery`;
[Conductor/Recovery.lean](../Cadence/Conductor/Recovery.lean)). The safety half of the
composition is proven (`Cadence.system_positional_log_safety`,
[System.lean](../Cadence/System.lean)), and since K1 the glue drives
Chorus's `participate`, `propose` and `abandon` inputs through the contract,
so the composed system's Chorus is not inert
([CompositionContracts.md](CompositionContracts.md) §3, ConductorBounds.md §7 item 2). K6
instantiated the full orchestrator contract
(`Conductor.conductorFull`). K7 closed the loop in the composed run
([Composed/](../Cadence/Composed/Corollary4.lean)): every condition each
side takes from its caller is a theorem, Corollary 4 is proven
(`Composed.corollary4`), and so are Lemma 5 at `2W − p`
(`Composed.boundedConcurrency`), `𝓡`-Liveness at `2Wτ`
(`Composed.liveness`) and censorship resistance at `2Wτ`
(`Composed.censorship`, after F31).

**What the timed claims would assume.** The same timing model as the MVBA and
Chorus claims: one clock, one time theory and one Δ for the whole system.
Messages between correct validators arrive within Δ after GST, and local
steps are instantaneous (δ = 0, decided in ConductorBounds.md §5). Timers fire on time.
They would also assume that the ACS meets its module (Module 4 (`mod:acs`)),
since the target leaves the ACS unspecified (ConductorBounds.md §3), and that the four parameter
assumptions of Algorithm 7 (`algorithm:conductor`) hold. Every condition the
Conductor needs from its caller, and every condition Chorus needs from the
Conductor, is discharged by the composition. None is left as a premise of
the composed claims.

**The three questions, decided by Lars (2026-10-03).**

1. **The ACS (ConductorBounds.md §3).** The target has no concrete ACS: the supplement's
   section is empty. **Decided:** keep the ACS as a contract,
   so the timed claims are relative to an `ACSTemporal` instance and the ACS
   is an assumed module named in the trust statement, as the MVBA was
   before ConductorBounds.md §6.2. A plain-Lean ideal ACS is the consistency witness only.
   P17 records the gap, and (a) replaces the assumption once the paper
   specifies an ACS.
2. **How "within Cadence" enters the contract (ConductorBounds.md §2.3).** **Decided:**
   state the Conductor's Totality and Recovery in the rely form
   already used for Chorus and the MVBA. The conditions the paper takes from
   Cadence become antecedents over the orchestrator's own observables (C5),
   and a Conductor-specific level states the `d_tot` form that Corollary 4
   consumes (C4).
3. **δ (ConductorBounds.md §5, C3 from the Chorus leg).** **Decided:** prove the
   Conductor's and the composed claims at δ = 0, the paper's instantaneous
   local computation, stated as a plain schedule premise. Chorus's and the
   MVBA's theorems keep their δ-general forms, and F3 records the
   degradation at δ > 0.

**Fifteen findings about statements (ConductorBounds.md §7, F16–F30) and four for the
paper's authors (P15–P18, [PaperAlignment.md](PaperAlignment.md) §6).** Two
of them
reach the existing safety claims. **F18 / P16:** Module 4's Validity
bounds the size of the decided set but not the number of pairs per
validator. The median argument behind Proposition 7 (`prop:acs-nonoverlap`),
and the model's stated bridge at `acs_decide`, need at most `f`
Byzantine-attributed pairs. With the module as stated, a decided set could
consist entirely of one Byzantine validator's pairs. The fix is one
first-order field, and every natural ACS satisfies it. **F25:** the model covered only `p ≥ 1` of the paper's `p ∈ {0, …, W − 1}`,
closed by R26. The other findings concern the timed statements and the
model's timing freedoms.

**Decisions in one place.**

* ACS: **(b), a contract, decided (2026-10-03)**, with (c1), the ideal
  ACS, as the consistency witness (ConductorBounds.md §3.3).
* C4 (an `OrchestratorWithTotality` level) and C5 (rely antecedents for
  Totality and Recovery): **decided (2026-10-03), jointly** (ConductorBounds.md §2.3).
* C6 (one pair per validator in a decided ACS set): **done (R25)**, and
  independent of the timed leg, because it repairs the justification of a
  safety bridge (F18).
* C7 (the ACS's `abandon` moves into `ACSSafety`) and C8 (Slot Consensus's
  inputs move into `SlotConsensusSafety`), each with the cross-frames:
  **done (R25)**. They are the composition leg's prerequisites (ConductorBounds.md §4, F19,
  F20).
* δ = 0 for the Conductor's and the composed claims, as a plain schedule
  premise: **decided (2026-10-03)** (ConductorBounds.md §5).
* The clock is the run's. The Conductor's `now` equals it through
  `OrchestratorTemporal.clock_agrees`, so `tick` is the system's clock step
  (ConductorBounds.md §6.1).
* One schedule record extends Chorus's `FamilySchedule` with the windows and
  the four parameter assumptions as fields, in the `δ_le_Δ` style (ConductorBounds.md §6.3).
* F24 (a part that stops stepping): **settled by K0 (R24, 2026-10-03)**. The
  composed run is relabelled so that a part's stutters, where its own
  `trans` allows them, count as its steps, and the per-part premise applies
  only once a correct validator has started the part. No class edit, no new
  field, and `TransitionSystemSafety` unchanged (ConductorBounds.md §7 F24, ConductorBounds.md §9 K0).
* Order: the glue's untimed composition edit first (K1), then the model's
  timing completion (K2), then the timed Conductor claims (K3–K6), then
  Corollary 4 and the composed claims (K7), then non-vacuity (K8) (ConductorBounds.md §9).

#### ConductorBounds.md §2.2–§2.3 as written (the contract before K3, and the decision)

##### 2.2 The contract today

`OrchestratorTemporal` ([Interfaces.lean](../Cadence/Interfaces.lean)) has
`Admissible`, `admissible_exists`, `clock_agrees`, an *eventual*
`totality`, `bound` with `boundedness` (a state-level count), and
`recovery_time` with `recovery`. The Conductor proves the fragment,
`Conductor.orchestratorSafety`
([Composition.lean](../Cadence/Composition.lean)). The paper's chain needs
three things the contract does not have:

* the `d_tot` form of Totality, which Proposition 14 and Corollary 4 consume
  (F16);
* a way to say "within Cadence" (F17);
* the ACS's abandonment, and a one-pair-per-validator decided set, at the
  fragment the Conductor instantiates (F18, F19).

##### 2.3 How "within Cadence" enters: C4 and C5

The Conductor's Totality and Recovery are false for the Conductor alone. A
caller that never completes a slot leaves every correct validator in window
1 forever. Two forms are faithful to "when run within Cadence":

* **(i) The rely form (C5).** Totality and Recovery take, as antecedents over
  the orchestrator's own observables (`opened`, `completed`), the two
  conditions the paper's proof takes from Cadence. Both are conditional,
  exactly as Chorus's fields are:
  * **(R-tot)** for every slot `s`: if the openings of `s` are
    `d`-synchronized (each opening at `t` is followed by every correct
    validator's by `max(t, GST) + d`), then the completions of `s` are
    `d_tot`-total;
  * **(R-term)** for every slot `s`: if the openings of `s` are
    `d`-synchronized and every correct validator opens `s` by `t`, every
    correct validator completes `s` by `max(t, GST) + ℓ_chorus`;
  * and "a correct validator completes only slots it has opened", which the
    fragment already gives through the glue's `[delivered_opened]`.

  `Admissible` then stays what it is for the MVBA and Chorus: the scheduler,
  the network and the timers, nothing about the caller. The composition
  discharges (R-tot) and (R-term) from `Chorus.chorusWithTotality`'s
  `totality` and `bounded_termination` through the glue (open ↦ participate,
  finalize ↦ complete). Non-circularity is then visible in the types: each
  side is a conditional statement about one slot, and the window induction
  lives inside the Conductor's proof.
* **(ii) A "within Cadence" `Admissible`.** `Admissible r` says that `r` is
  the orchestrator part of an admissible composed run. This is literally
  the paper's phrase. But it puts the caller's behaviour into `Admissible`,
  which the rely form was adopted to avoid ([Bounds.md](Bounds.md) §6.4.1,
  "The class change"). It also makes the Conductor's instance depend on
  Chorus's model.

**C4.** Module 2's Totality is eventual, so a `d_tot` field belongs at a
Conductor-specific level, as `SlotConsensusWithTotality` holds Chorus's.
`OrchestratorWithTotality` would have `Δ`, `d_tot` and the bounded
`totality` (in rely form under (i)). The instance pins `d_tot` by `rfl` to
the Chorus instance's `d_tot`. Corollary 4 and Proposition 14 consume it.

**Decided (Lars, 2026-10-03): (i) with C4**, in one
[Interfaces.lean](../Cadence/Interfaces.lean) edit. No Veil module
instantiates `OrchestratorTemporal`, so the edit is a warm rebuild of the
Chorus family and re-solves nothing. The paper side of this is P15.

#### ConductorBounds.md §3.3–§3.4 as written (the ACS options, and the repairs C6–C7)

##### 3.3 The options

**(a) Instantiate the ACS concretely, from the MVBA.** The standard
reduction: each validator broadcasts its signed proposal; once it holds
`2f + 1` signed proposals from distinct validators, it proposes that set to
an MVBA whose validity predicate checks the signatures; the MVBA's decision
is the ACS's. That would need:

* a fourth model or a plain-Lean wrapper over `Mvba`: the dissemination
  round, the candidate set as the MVBA's value, and the validity predicate;
* `ACSSafety` from the MVBA's agreement, external validity and integrity;
* Termination with `ℓ_ACS = Δ + ℓ_MVBA`;
* Δ-Totality, which `MVBATemporal` does not state. It would come from the
  decision handoff the supplement describes (a decided party's `CommitQC`,
  transferred and accepted; [Bounds.md](Bounds.md) §6.4.2, "The decision
  handoff (C15)"), now owed by the ACS layer instead of by Chorus.

The target specifies none of this. Every choice (the candidate-set
predicate, signatures, the one-proposal-per-validator rule, the transfer)
would be ours. The resulting claim would be about *an* ACS, not the paper's,
which is the hybrid the single-target rule forbids. **Not recommended at
this target.** It becomes the faithful option once the paper specifies the
ACS. The supplement's MVBA is then the natural base, and its timed instance
`Mvba.mvbaTemporal` already exists.

**(b) Keep the ACS as a contract.** The timed claims are stated for an
arbitrary `[ACSTemporal …]` at the fragment the Conductor instantiates, with
the per-window projections as `T.Admissible` runs. Exactly as the MVBA was
consumed before ConductorBounds.md §6.2 closed it, the ACS is then **an assumed module, named
in the trust statement**. This is exactly what Algorithm 7 says ("Uses: ACS")
and what Theorem 2's proof does. The cost is the class edits C6 and C7, and
two consequences for non-vacuity (ConductorBounds.md §8.2): an ideal instance has to exist, and
the Conductor's own `admissible_exists` needs the ACS to be able to stay
idle.

**(c) Other forms.**

* *(c1) An ideal ACS.* A plain-Lean instance of `ACSSafety` and
  `ACSTemporal`: one global decided set per window, fixed by the first
  correct decision; each correct validator decides within `Δ`. It is the
  class's model, not a protocol, so claiming it as "the ACS" would mislead.
  Its use is the **consistency witness** for (b).
* *(c2) A multi-shot consensus*, as the second margin note suggests: not in
  the target.

**Decided (Lars, 2026-10-03): (b), with (c1) as the consistency
witness.** The ACS is an assumed module, named in the trust statement. P17
records the gap. Once a target revision specifies the ACS, (a) replaces the
assumption with a proof, along the path the MVBA took.

##### 3.4 Two contract repairs needed under every option

* **C6: one pair per validator (F18, P16).** Add to `ACSSafety` the
  first-order field "a correct decider's set holds at most one slot per
  validator", and let `validity_quantitative` count distinct validators.
  With the system's fault bound (at most `f` Byzantine validators), the
  median lemma's hypothesis (`IsMedian.between_correct`'s "at most `f`
  Byzantine-attributed entries", [Windows.lean](../Cadence/Windows.lean))
  then follows from the contract. **Done (R25):** `ACSSafety.decided_unique`,
  and `Cadence.acs_median_bracket` ([AcsMedian.lean](../Cadence/AcsMedian.lean))
  proves the link.
* **C7: the ACS's `abandon` in the fragment (F19).** Move `abandon`,
  `abandoned` and their frames from `ACSTemporal` into `ACSSafety`, as
  `MVBASafety` has them. Add the cross-frames: `propose` leaves `abandoned`
  unchanged, and `abandon` leaves `proposed` unchanged. Then model Algorithm
  7, line 45 (`line:acs-abandon`) in `enter_window`, so that Proposition 12
  is a fact of the model and not a reading of the paper. **Done (R25):** the
  model's invariant `[acs_abandoned_decided]`.

Both are [Interfaces.lean](../Cadence/Interfaces.lean) edits that change the
Conductor's VCs (one in-file sweep, about a minute cold) and nothing in the
Chorus or Mvba families.

#### ConductorBounds.md §4 as written (the composition plan for K1 and K7)

##### 4. The glue: the composition leg

##### 4.1 What changes

**[Interfaces.lean](../Cadence/Interfaces.lean) (C8, F20).** The glue
instantiates only `SlotConsensusSafety`, and `participate`, `abandon` and
`propose` live in `SlotConsensusTemporal`. So the glue cannot even mention
them. Move the three inputs, their observables (`participating`,
`abandoned`, `proposed`), effects, step frames and initial conditions into
`SlotConsensusSafety`, all first-order, and add what is missing:

* the per-input cross-frames ("`participate` at `i` leaves `abandoned` and
  `proposed` unchanged", and so on, the `complete_frame` pattern);
* the per-validator frames ("an input at `i` leaves `j`'s records
  unchanged").

Without them, "the glue abandons only after finalizing" does not imply C1 at
the contract level, since a `participate` could set `abandoned`.
`SlotConsensusTemporal` keeps `sent`, `Admissible`, Termination and
Quiescence. Chorus does not instantiate `SlotConsensusSafety`, so its family
does not re-solve. The field proofs move from
[Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean) to
[Chorus/Compose.lean](../Cadence/Chorus/Compose.lean), where they are plain
Lean.

**[Cadence.lean](../Cadence/Cadence.lean).** Three handlers drive the
contract's inputs, as `acs_propose` drives the ACS's:

* `on_open i s sc_next`, Algorithm 1, line 17 (`line:participate`): requires
  `orch.opened os i s` and `sc.participate (sc_state s) i sc_next`. The
  ghost `sc_started` becomes the instance's own `participating`.
* `on_propose`, Algorithm 1, line 19 (`line:propose`): drives `sc.propose`
  instead of only recording `proposed`.
* `on_finalize`, Algorithm 1, lines 20–23
  (`line:upon-finalize`–`line:abandon`): performs `sc.abandon` in the same
  step as `orch.complete`, which is one more parameter. The glue's record
  `sc_abandoned` becomes the instance's `abandoned`.

The glue gains first-order invariants, each sweep-checked:

* `sc.abandoned (sc_state s) i → ∃ v, sc.finalized (sc_state s) i v`
  (C1's state form);
* `sc.participating (sc_state s) i → orch.opened os i s` (with
  `integrity_timing`, C2's state form).

Its own safety claims are unchanged: the edit adds behaviours only through
contract-legal input transitions.

**[System.lean](../Cadence/System.lean).** The end theorem is re-proven at
the moved fields. The composed system's Chorus is no longer inert, and
[CompositionContracts.md](CompositionContracts.md) §7's seam 2 ("the glue
does not drive Chorus's inputs") closes.

##### 4.2 What the composition discharges

Each of Chorus's caller conditions ([Bounds.md](Bounds.md) §6.4.6, "What
the Conductor's timed claims need from this leg") becomes a theorem about
the composed run:

| Chorus's condition | discharged from | needs |
|---|---|---|
| C1: abandon only after finalizing | Algorithm 1, line 23 (`line:abandon`): the glue's invariant above | K1 only |
| C2: no start before `D − Δ` | `OrchestratorSafety.integrity_timing`, with `deadline s = start_time s + Δ` (a schedule tie, ConductorBounds.md §6.2) and `clock_agrees` | K1, and the composed timed run (K7) |
| participation by `t` | the Conductor opens by `t` (Recovery, or Proposition 15), and the glue's `on_open` row | K5, K7 |
| Δ-synchronized participation | Lemma 15 plus the `on_open` row; at δ = 0 exactly `d_tot = Δ` | K4, K7 |

And the Conductor's caller conditions, (R-tot) and (R-term) of ConductorBounds.md §2.3, come
from `Chorus.chorusWithTotality`'s two fields through the same table read
backwards.

##### 4.3 Corollary 4 as a theorem

Yes. Its Lean form is: for every admissible composed run and every slot `s`,
the run's slot-`s` Chorus projection satisfies `SyncParticipation`, C1 and
C2. So `Chorus.chorusWithTotality`'s `bounded_termination` and `totality`,
and `Chorus.chorusTemporal`'s `termination`, hold for it with no caller
premise left. It is the last step of the leg (K7) because it needs Lemma 15
within Cadence. The paper orders it the same way: "one finished result
applied to another".

##### 4.4 Order

The glue edit (K1) is untimed and depends on nothing in this leg. Doing it
first makes the composed system non-inert, the safety theorem keeps holding,
and every later session works on the final glue. Corollary 4 and the
composed timed claims (K7) come after the Conductor's timed claims (K4–K6),
which they consume.

#### ConductorBounds.md §5, the δ decision as written

**The choices.**

* **(α) δ = 0.** The paper's model: "validators' clocks are synchronized,
  so they share one global timeline", and local computation is
  instantaneous throughout the main body. It is a field `δ = 0` of the
  Conductor's schedule, used by the Conductor's and the composed claims
  only. Chorus's and the MVBA's theorems stay δ-general. The composed
  theorem instantiates them at δ = 0, where `Lchorus` and `Ltot` are the
  paper's values by `rfl` (`chorusWithTotality_ℓ_paper`,
  `chorusWithTotality_d_tot_paper`).
* **(β) A δ-robust statement.** Re-synchronize on absolute time: a window
  whose correct validators all enter before its first slot's starting time
  opens every slot at that starting time (Algorithm 7, line 27
  (`line:conductor-wait-for-open`)). Its openings are then synchronized by
  the clock, to within one δ, whatever the spread of the entries. That
  resets the ratchet in the smooth regime of Proposition 18. It does not
  cover the windows before it, and Propositions 14–16 use `d_tot`-totality
  there. A δ-robust Recovery would need a new argument for those windows,
  with a tolerance that stays inside Chorus's Δ. That is new mathematics,
  not a formalization of the paper's.
* **(γ) Record the degradation.** State the δ-general per-window lemma
  (tolerance `d_ω`, recurrence `d_{ω+1} = d_ω + cδ`), and the claims as
  holding while `d_ω ≤ Δ`. Faithful, but nothing downstream can use it.

**Decided (Lars, 2026-10-03): (α)**, as a plain schedule premise of the
Conductor's and the composed timed claims. The Chorus and MVBA results stay
general in δ, and the tolerance-parametric lemmas are kept wherever they
cost nothing (Chorus's already are), so that (β) remains possible later. F3
records the degradation at δ > 0. It is a finding about the model, not about
the paper, whose model is δ = 0.

#### ConductorBounds.md §7 as written (the findings with their proposals and closing records)

F1–F15 are the MVBA and Chorus legs' ([Bounds.md](Bounds.md) §6.4). These
continue the numbering. "Faithful implementation" means one that meets the
paper's module.

* **F16: the contract's Totality is eventual, and the paper's consumers need
  `d_tot`.** `OrchestratorTemporal.totality` is Module 2's ("eventually
  opens"). Proposition 14 and Corollary 4 use Lemma 15's "more specifically"
  form, `max(t, GST) + d_tot`, and no class states it. **Proposal:** C4
  (ConductorBounds.md §2.3). Paper side: P15.
* **F17: Totality and Recovery are stated unconditionally, but the
  Conductor has them only within Cadence.** A caller that never completes a
  slot leaves the Conductor in window 1. So the fields as stated are false
  of every faithful Conductor, unless `Admissible` encodes the caller's
  behaviour. That is P13's pattern, one module up. Module 2's commented-out
  "assumed behaviour" block, which lists "complete only after opening" and
  "complete within `Φ_oc` of opening", would not repair it either. The
  proofs use the *conditional* completion guarantees (R-tot) and (R-term).
  An unconditional `Φ_oc` bound is itself a consequence of the Conductor's
  totality (Proposition 14), so a module assumption stating it would assume
  the conclusion. **Proposal:** C5 (ConductorBounds.md §2.3). Paper side: P15.
* **F18: a decided ACS set may hold several pairs of one validator.**
  Module 4's Validity: "`|set| ≥ 2f + 1`, and for every validator-slot pair
  `(p_i, s_i) ∈ set` such that `p_i` is a correct validator, `p_i` proposed
  slot `s_i`". `ACSTemporal.validity_quantitative` says the same: `2f + 1`
  distinct *pairs*. The median argument ("the decided vector contains at
  least `f + 1` pairs contributed by correct validators", before
  Proposition 7) and the model's stated bridge at `acs_decide` (justified by
  `lowerMedian_between_correct`, whose hypothesis is "at most `f`
  Byzantine-attributed entries") need at most `f` Byzantine *pairs*. Under
  the module as stated, a single Byzantine validator's `2f + 1` pairs are a
  valid decision. The median is then the adversary's choice, the next
  window can overlap the previous one, and the proofs of Integrity (Lemma 12
  (`lemma:conductor-integrity`)) and Monotonicity (Lemma 13
  (`lemma:conductor-monotonicity`)) through Proposition 8
  (`prop:acs-fate-range`) fail. **The model's safety theorems are unaffected
  as theorems:** the bridge is a `require`, and they hold of the model. What
  fails is the bridge's justification, that it removes no behaviour of a
  correct ACS. Any ACS that collects one signed proposal per validator meets
  the stronger property. **Proposal:** C6 (ConductorBounds.md §3.4). Paper side: P16.
  **Closed (R25):** C6 is in the contract, and the bridge's justification
  is a theorem, `Cadence.acs_median_bracket`: with at most `f` Byzantine
  validators, the median of a correct decider's set lies between two of its
  correct pairs. The `require` itself stays, a stated bridge: the model
  computes no median, and cardinality is outside the solver's fragment.
* **F19: the ACS's `abandon` is outside the fragment the Conductor
  instantiates, and nothing frames it against `propose`.** Algorithm 7,
  line 45 (`line:acs-abandon`) is therefore not modelled, and Proposition 12
  cannot be derived even in the weak form "the Conductor never abandons",
  since no field says that a `propose` leaves `abandoned` unchanged.
  **Proposal:** C7 (ConductorBounds.md §3.4). **Closed (R25):** `abandon`, `abandoned` and
  their frames are in `ACSSafety` with both cross-frames, `enter_window`
  abandons the instance, and Proposition 12 is the invariant
  `[acs_abandoned_decided]`.
* **F20: Slot Consensus's inputs are outside the fragment the glue
  instantiates, and the inputs have no cross-frames.** The same gap as F19
  for Chorus. The glue cannot drive Algorithm 1, line 17 (`line:participate`),
  Algorithm 1, line 19 (`line:propose`) or Algorithm 1, line 23
  (`line:abandon`), and even if it could, C1 would not follow at the contract level. **Proposal:** C8 (ConductorBounds.md §4.1).
  **Closed (R25):** the three inputs are in `SlotConsensusSafety` with the
  per-input cross-frames and the per-validator frames; the glue's
  `on_open`, `on_propose` and `on_finalize` drive them, and C1 and C2 hold
  in state form (`[abandoned_after_finalize]`, `[participating_opened]`).
* **F21: the Conductor model leaves free what the timed claims fix.** Each
  freedom is sound for safety and makes a timed claim false of the model:
  * the decided interval's width is unconstrained (Conductor.lean,
    `acs_decide`: "deliberately *not* forced to be exactly `W` slots
    wide"), so boundedness's count `2W − p` and Proposition 17's "no gap"
    fail;
  * `acs_propose` keeps only the lower bound of Algorithm 7, lines 39–41
    (`line:sstar-compute`–`line:sstar-update`), "strictly beyond the current
    window", and not "the earliest slot whose starting time has not
    passed". Propositions 16 and 19 use the latter;
  * `acs_decide` brackets the first slot from below only. Propositions 17
    and 19 need the upper bracket (the median is at most some correct
    proposal), which [Windows.lean](../Cadence/Windows.lean) already
    proves;
  * `start_time` is only monotone, not τ-spaced, and `genesis_time` is not
    tied to slot 1's starting time;
  * `open_slot` may fire late ("Timing relaxation" in the model's header);
    its row (ConductorBounds.md §6.4) closes that in the timed premise.

  **Proposal (K2):** immutable shift functions `win_last`, `win_boundary`
  (the `+ (W − 1)` and `+ (p − 1)` of a window's first slot; R26 made the
  boundary `+ p`, F25), required by
  `acs_decide` and the genesis assumption; the full `s*` rule over `now` in
  `acs_propose`; the upper bracket as a second witness pair; and
  `start_time` strictly increasing. All are first-order, and the instance
  at `ℕ` fixes the arithmetic.
  **Closed (R26):** in [Conductor.lean](../Cadence/Conductor.lean), each a
  constraint the paper's protocol satisfies, so the model loses only runs
  the paper does not have:
  * `win_last` and `win_boundary` (Algorithm 7, line 52
    (`line:last-update`); Algorithm 7, line 23 (`line:ready-check`)):
    `acs_decide` records `[first, win_last first]` with boundary
    `win_boundary first` (Algorithm 7, lines 49–52
    (`line:open-foreach`–`line:last-update`)), and `[genesis_window]` makes
    window 1 the shifts of slot 1 (Algorithm 7, lines 31–34
    (`line:startup-foreach`–`line:startup-last`)). The paper's window is
    exactly that interval. The invariant `[win_bounds_shift]` states the
    width for every window;
  * the `s*` rule (Algorithm 7, lines 38–41
    (`line:ready-time`–`line:sstar-update`)) as three `require`s over
    `now`: beyond the window's last slot `l0`, not yet started, and every
    slot strictly between `l0` and `s*` already started. The paper's `s*`
    is `max(earliest not passed, l0 + 1)`, which meets all three; with
    strictly increasing starting times nothing else does;
  * the upper bracket: a second correct witness pair `(r2, s2)` with
    `first ≤ s2`. The paper's median is between two correct estimates
    (the paragraph before Algorithm 7 (`algorithm:conductor`)), proven from
    the contract by `Cadence.acs_median_bracket` (R25);
  * `[start_time_strict]` (Appendix A.1 (`subsection:mcp-preliminaries`):
    `τ > 0`), and `[genesis_window]` starts the clock at slot 1's starting
    time (the proof of Proposition 16 (`prop:window-open-time`): "every
    correct validator enters window 1 at time `0 = T₁(1)`"). The spacing
    itself, `+ (s − 1)τ`, is K3's, at the instance.

  The `open_slot` freedom stays in the model, as planned: it is an
  over-approximation (the paper's punctual openings are among the model's
  runs), and the row closes it in the timed premise
  ([PaperAlignment.md](PaperAlignment.md) §5.10). Every safety property
  and `Conductor ⊨ OrchestratorSafety` re-proved unchanged.
* **F22: `enter_window` reads the first correct decision anywhere, not the
  validator's own.** Its guard is the global `acs_decided`, which
  `acs_decide` sets on some correct validator's decision. Algorithm 7, line
  44 (`line:acs-decide`) fires on `p_i`'s own `decide`. As a δ-row,
  `enter_window` would owe an entry before `p_i`'s ACS has decided, which
  the paper's protocol cannot do; ACS's Δ-Totality would then go unused,
  and the bound would come out tighter than the paper's for the wrong
  reason. **Proposal (K1):** add `require acs.has_decided (acs_state w') i`
  (the F6 pattern of [Bounds.md](Bounds.md) §6.4.2). **Closed (R25)**, as
  proposed.
* **F23: the classes allow several Δs, and the paper uses one.** See ConductorBounds.md §6.2.
  **Proposal:** schedule ties, not class edits.
* **F24: a part that stops stepping has no timed run.** A contract's
  `TimedRun` steps along `trans` forever, and no class gives a stutter
  step. In a composed run most per-slot Chorus instances and per-window ACS
  instances eventually stop. The Chorus leg met the same question for the
  MVBA inside Chorus: `Component.Projection` asks that the part be stepped
  infinitely often (`scheduled`, [Liveness.md](Liveness.md) §4.2), and the
  idle run kept the MVBA stepping through repeated `abandon` inputs. At the
  contract level there are two further obstacles. Whether the ACS has an
  always-enabled step is unknown. And `admissible_exists` gives *some*
  admissible run from each initial state, not one with the inputs this
  consumer gives, so the Conductor cannot build its own admissible runs
  from it (the "vacuity does not compose" point of
  [CompositionContracts.md](CompositionContracts.md) §7). **Decided by the
  K0 spike (R24, 2026-10-03): a stutter lift at the projection, and a
  per-part premise that applies once a correct validator has started the
  part. No class changes, `TransitionSystemSafety` included.**
  [spikes/14_part_projection.lean](../spikes/14_part_projection.lean)
  builds it over the contracts as they are; ConductorBounds.md §9 K0 has what K3 takes from
  it.

  **How a part that stops is projected.** The composed run is relabelled
  (`liftRun`): a composed step counts as a step of the part whenever it is
  a transition of the part's own contract. That covers a real step, and also
  a step in which the part stays where it is, provided the contract's `trans`
  allows that stutter. The relabelled run has the same states, clock and
  `gst`, so [Timed.lean](../Cadence/Timed.lean)'s
  `Component.Projection.timed` applies to it unchanged, over the contract
  read as a one-label transition system (`contractRTS`). The part's run,
  `partRun p`, is then a `TimedRun` of exactly the class's `init` and
  `trans`. A part stepped only finitely often is scheduled exactly when its
  final state can stutter (`lift_scheduled_of_finite`). A part already
  scheduled stays scheduled (`lift_scheduled_of_scheduled`). The consumer
  needs no stutter action: its own steps that leave the part alone (a
  `tick`, say) serve as the part's stutters. This is the paper's picture: a
  silent instance whose time goes on passing.

  The stutter is tested against `trans`, not `step`, and that matters.
  Chorus has no internal step that stays enabled once every correct
  validator has abandoned the slot: its honest actions fire once, and its
  phase markers end. What it has is the input `abandon`, re-issued to a
  validator that has already abandoned. Chorus's `abandon` only sets
  `abandoned i` and forwards to the MVBA's, which only sets the same flag,
  so the re-issue leaves the state unchanged. A finished slot can therefore
  stutter in `trans`, and in an all-correct run nothing else would keep its
  projection going.

  **Meaning is kept.** Every shape a contract field uses ("at every index",
  "eventually", "by time `t`", "by `max(t, GST) + d`", and "from index `n`,
  by `max(clk n, GST) + d`") reads the same on `partRun p` and on the
  composed run, with the part's state read off each composed state
  (`partRun_forall_iff`, `partRun_eventually_iff`, `partRun_byTime_iff`,
  `partRun_byGstBound_iff`, `partRun_byGst_at`, `composed_byGst_of_cover`).
  With these, `ACSTemporal.termination`, `ACSTemporal.totality` and
  `SlotConsensusTemporal.termination` are restated wholly in the composed
  run's vocabulary and proven from the fields (`acs_termination_in`,
  `acs_totality_in`, `sc_termination_in`).

  **The premise, and the ACS's idle admissibility.** The consumer's
  `Admissible` asks for a part's run only once a correct validator has
  started the part. For window `w`'s ACS, in the spike's form:

  ```lean
  ∀ w, (∃ n i s, ¬ byz i ∧ A.proposed ((r.at' n).acs w) i s) →
    ∃ p : (stutterComp (acsComp w)).Projection (liftRun (acsComp w) r).toLRun,
      TA.Admissible (partRun p)
  ```

  The slot form is the same, over "a correct validator participates in
  slot `s`". The guard loses nothing. Every use of an ACS field at window
  `w` has a correct proposal there: Termination's antecedent says so
  outright, and Totality's antecedent, a correct decision, implies one by
  `integrity`. Likewise every use of a slot field has a correct participant.

  The Conductor cannot build its admissible runs from
  `ACSTemporal.admissible_exists`, whatever inputs it gives, for three
  reasons:

  * the run that field provides has its own clock and `gst`, while a part's
    run carries the composed ones;
  * its steps may be inputs, or proposals, that the Conductor's guards do
    not give;
  * it is one run per instance, while the Conductor interleaves infinitely
    many instances on one clock.

  The guard makes that unnecessary. The Conductor's idle run moves only the
  clock (and fires `open_slot` at the starting times). No correct validator
  ever proposes, since readiness needs a completion and the idle run gives
  none. The premise therefore holds vacuously, by the fragment's
  `init_proposed` alone. `toy_admissible_exists` proves this for a consumer
  of the Conductor's shape, at every ACS, using no `ACSTemporal` field.
  **No new ACS field is needed.** The ACS then only has to be a module
  whose admissible runs exist (the class already says so) and whose
  finished instances can stutter. That second condition is part of the
  premise: a composed run in which a started instance deadlocks has no
  admissible part run, so it is not admissible. Module 4 (`mod:acs`) gives
  the ACS an `abandon()` input, as Module 1 gives Chorus one. In Chorus and
  the MVBA, re-issuing that input is the stutter, and the ideal ACS (ConductorBounds.md §3.3
  (c1)) will have the same by construction. Whether a deadlock is
  plausible is the auditor's judgement, on the premises page.

  **The other candidates, and why not.**
  * *A stutter-closed run in the contracts* (`TimedRun` steps by `trans` or
    equality, or a reflexivity field in `TransitionSystemSafety`): the
    first would re-prove the MVBA and Chorus temporal instances, whose
    `Admissible` is over labelled runs. The second would re-solve all four
    families cold, and is false of every Veil model without a no-op action,
    Chorus's initial state included.
  * *A contract field for an always-enabled step*: needless for the
    consumer's claims, since the lift reads stutters off `trans`. As an
    internal step it is false of Chorus in an all-correct run, so it
    would also constrain (a).
  * *A finite-run `Admissible`*: changes all four temporal classes and
    their two proven instances.
  * *`scheduled` through repeated inputs* (the Chorus idle run's device),
    with a consumer action that re-issues `abandon`: the lift gets the same
    stutters without a model edit, and without an action the paper does
    not have.
* **F25: the model's readiness boundary was a slot it asked to be
  complete, so the model covered only `p ≥ 1`.** The main body allows
  `p ∈ {0, …, W − 1}` (Algorithm 7 (`algorithm:conductor`)). Its readiness
  check, Algorithm 7, line 23 (`line:ready-check`), "return `k − j ≤ W − p`"
  over the opened slots `s_1 < … < s_k` with `s_1, …, s_j` complete, asks
  in window `ω` for every slot of the earlier windows and the window's
  first `p`; at `p = 0` for the earlier windows only, and in window 1 for
  nothing. The paper is precise here. The model's boundary was the
  window's `p`-th slot with readiness asking for the slots *up to* it, so
  `first ≤ boundary` (from the first model on: `genesis_shape` and
  `acs_decide`'s interval shape) excluded `p = 0`, and the Conductor's
  safety theorems said nothing about that configuration. Found by R26.
  **Closed (R26)**, at the coordinator's request, in the same cold sweep:
  the boundary is the window's `(p + 1)`-th slot (`win_boundary s = s + p`),
  readiness asks for the scheduled slots *strictly below* it, and
  `[shift_shape]`'s `s ≤ win_boundary s ≤ win_last s` is then exactly
  `0 ≤ p ≤ W − 1`. `[bounded_tail]` reads the boundary with `<`: at
  `p ≥ 1` it states what it stated before, at `p = 0` the paper's content.
  No new state, every property kept, the sweep green. The timed claims
  need `p ≥ 2` anyway (ConductorBounds.md §6.3, P9's note).

* **F26: the ACS contract does not say that its inputs are accepted.**
  Found by K3. `ACSSafety` states `propose`'s and `abandon`'s effects and
  frames, but not that a correct validator can give them: a contract whose
  `propose` relation is empty meets every field. The Conductor's handlers
  `acs_propose` and `enter_window` give these inputs, so their rows are
  owed only where the ACS accepts them, and with an ACS that refuses a
  correct validator's proposal no later window is ever entered: Recovery
  fails, and Totality can fail when it refuses some validators only.
  Module 4 (`mod:acs`) has the two inputs in its interface, and an input is
  the caller's to give, so every ACS meets it. The MVBA's contract states
  its one caller-driven input this way (`MVBASafety.accept_enabled`, rely
  form). **Closed (R27, decided by Lars 2026-10-03):** two first-order
  fields in that rely form, `propose_enabled` (a correct validator that has
  neither abandoned nor proposed can propose any slot) and
  `abandon_enabled` (a correct validator can abandon; window entry gives
  this input), in **`ACSTemporal`**. They were first placed in `ACSSafety`,
  withheld from the solver with `veil_smt_ignore`. The Conductor's in-file
  sweep then failed: `open_slot × open_prefix_agreement` went from about 5 s
  to over the 180 s budget on both attempts, reproducibly in isolation,
  with the fields in the middle of the class or at its end, and other
  cells slowed severalfold. Without the fields the sweep is green in 44 s.
  So withholding did not leave the solver's queries as they were (the
  cause is not diagnosed; a question for the Veil fork). Only a
  consumer's timed claims need the two fields, and no Veil module
  instantiates `ACSTemporal`, so no VC moves. The ideal ACS proves both
  (`Cadence.IdealAcs.acsTemporal`), and the claims lost the premise they
  carried in between. Not a paper issue: Module 4's inputs are
  invocations by the caller, and the module formalism has no refusal
  ([PaperAlignment.md](PaperAlignment.md) §6's table of facts used).

* **F27: the claims' time had no ordered addition.** Found by K4.
  [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean)'s claims
  were stated over a `time` with a linear order and an additive monoid, but
  no axiom tying the two. Then `max(t, GST) + Δ` is not monotone in `t`, an
  opening at `t` need not be before `t + Δ`, and Totality is unprovable as
  stated. The time theory of ConductorBounds.md §6.2 is ordered, and Chorus's and the MVBA's
  timed claims assume it. **Closed (R28, decided by Lars 2026-10-03):**
  `TotalityClaim` and `RecoveryClaim` take `[IsOrderedAddMonoid time]`;
  `BoundednessClaim`, a state property, needs no time theory. Not a paper
  issue: the paper's time is the real line.
* **F28: Totality needs a slot whose starting time has not passed.** Found
  by K4. `acs_propose`'s `s*` is the first slot beyond the window whose
  starting time has not passed (Algorithm 7, lines 38–41
  (`line:ready-time`–`line:sstar-update`)), and `TotalityClaim` assumed
  nothing of the starting times beyond `[start_time_strict]`, so they could
  be bounded. Once the clock passes them all, no correct validator can
  propose to the next ACS. A validator that becomes ready only then never
  proposes, the ACS's synchronized-proposals assumption fails, and nothing
  makes it decide or enter a window that an earlier-ready correct validator
  entered: the claim is false in such runs. The paper's slots are
  infinitely many and τ-spaced on the real line (Appendix A.1
  (`subsection:mcp-preliminaries`)), so its `s*` always exists. **Closed
  (R28, decided by Lars 2026-10-03):** a plain premise,
  `StartsUnbounded th` ("whatever the time, some slot has not started
  yet"), used only to pick `s*` (`Conductor.sstar_exists`). `StartTimes`
  does not imply it, even with an Archimedean time: with
  `start₀ = (−1, 0)` and `τ = (0, 1)` in the lexicographic monoid
  `{(a, b) : a < 0, or a = 0 ∧ b ≥ 0}`, every starting time stays below
  `(0, 0)`. Deriving it would need `0 ≤ start₀` or a group. For K5,
  `RecoveryClaim` proposes too, so it needs `StartsUnbounded` as well, or
  `StartTimes` together with `[Archimedean time]` and `0 ≤ start₀`.
  **Done in K5 (R29, decided by Lars 2026-10-03):** `RecoveryClaim` takes
  `StartsUnbounded`, the same premise as Totality. Recovery also uses it
  to find a window of the chain that starts after GST
  (`Conductor.exists_post_gst`). Not a paper issue.
* **F29: Totality's fault-bound premise was unused.** Found by K4. K3 gave
  `TotalityClaim` the premise "at most the ACS's `fault_bound` validators
  are Byzantine", for the decided interval's row (its correct median
  witnesses). The window induction never needs that row: a validator
  enters a window only after a correct validator has, and by then the
  interval is recorded. **Closed (R28, decided by Lars 2026-10-03):** the
  premise is dropped from `TotalityClaim`. The decided interval's row and
  the fault bound remain premises of `RecoveryClaim`, where Propositions 15
  and 16 need the interval to be recorded.
* **F30: Recovery needs every window to have a successor.** Found by K5.
  The model's window order is abstract (`TotalOrderWithMinimum window`), and
  a validator leaves a window only for its successor: `acs_propose` and
  `enter_window` read `win_ord.next`. `RecoveryClaim` assumed nothing of
  the order. At `window := Fin 1` every validator stays in window 1 for
  good, and every premise of the claim holds. The rows are vacuous
  without a successor, the ACS is never proposed to, and the caller
  completes window 1's slots. No slot past window 1 is ever opened, so the
  claim is false. The paper's windows are the numbers `ω ∈ ℕ≥1`, with one
  ACS instance for each `ω ≥ 2` (Algorithm 7, line 12
  (`line:acs-instances`)), and Proposition 15 (`prop:enters-every-window`)
  inducts over them. **Closed (R29, decided by Lars 2026-10-03):** a plain
  configuration premise, `WindowsUnbounded` ("every window has a
  successor"), beside `StartsUnbounded` in
  [Conductor/Schedule.lean](../Cadence/Conductor/Schedule.lean), and a
  premise of `RecoveryClaim` only. Totality and Boundedness speak only of
  windows a correct validator has entered and need none. The alternative,
  stating the claim at `window := ℕ`, was declined: the claim stays generic
  in the window type, and K6's instance carries the premise, which is
  trivial at `ℕ`. Not a paper issue.

* **F31: censorship resistance's timed premise ties with the deadline.**
  Found by K7. The paper's proof that Algorithm 1 (`algorithm:cadence`)
  meets Definition 3 (`def:censorship-resistance`), in Appendix B.3
  (`subsection:correctness_cadence`), has a correct proposer open its slot and propose at its starting time
  `D − Δ ≥ GST`, and reads Chorus's proposal inclusion off Proposition 3
  (`prop:honest-positive-entry`): every correct validator "receives and
  validates its assigned chunk under `root_P` by the deadline". In the
  model the chunk arrives by `max(D − Δ, GST) + Δ = D` and is recorded at
  `δ = 0` by `D`, while the deadline marker, punctual, also fires at `D`
  (P1 lets it fire at clock `D`). Once it has fired, recording is closed,
  so `Chorus.within_proposal_recorded` needs the strict `< D`. That is the
  tie [Bounds.md](Bounds.md) §6.4.2 ("What `s.deadline − Δ ≥ GST`
  becomes") anticipated. No choice of `𝓡` removes it, since the proposal
  is always made exactly `Δ` before the deadline. The paper resolves the
  tie in the chunk's favour without saying so. **Proposal:** a tie-break
  premise in Chorus's timing model (a chunk record owed at clock `≤ D`
  fires before the deadline marker), with the paper side recorded as P19;
  alternatives: leave Definition 3 out of the composed claims, or a strict
  network bound (not the paper's). **Open: put to Lars (R31).** The
  composed claim also needs two plain configuration ties: the glue's
  proposer assignment is Chorus's, and a correct proposer has a
  well-encoded root.
  **Closed (R31.2, decided by Lars 2026-10-04, option A):** the tie-break
  is a standalone premise of Chorus's timing model, (P-incl)
  `DeadlineInclusive` ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)):
  a chunk a correct validator holds at a clock at or before `D` is
  recorded. It is not part of `SyncAtMvba`, so no existing claim takes it;
  the Chorus witness meets it (`Chorus.Witness.deadlineInclusive`). The
  milestone is `Chorus.within_proposal_recorded_incl`
  ([Chorus/Inclusion.lean](../Cadence/Chorus/Inclusion.lean)), and
  censorship resistance is proven (`Composed.censorship`). The proposer
  tie is definitional: the claim's glue configuration takes Chorus's
  proposer set for every slot. What stays a premise is a well-encoded root
  for the proposer. P19 records the paper side.

#### ConductorBounds.md §8 as written (the ledger note and the witness record)

##### 8. Premises and non-vacuity from the start

##### 8.1 The ledger

The draft ledger this section started from has its one home on the
premises page now: [Premises.md](Premises.md) §0 (the composed claims) and
ConductorBounds.md §9 (the Conductor's own), each line with its role, use, plausibility and
witness. Git history has the draft (this section before R32).

##### 8.2 The witness. Done (K8, R32, 2026-10-04)

[Composed/Witness.lean](../Cadence/Composed/Witness.lean): one model of the
composed system meets every premise of the four composed claims at once,
and the orchestrator's part of it every premise of the Conductor's three
(`Composed.Witness.*_premises_satisfiable`; the run in plain words is
[Premises.md](Premises.md) §0.5). As planned: `Fin 4` with validator 3
Byzantine and silent, one proposer, `Δ = τ = 1`, `δ = 0`, the MVBA
witness's schedule with the Chorus witness's `Δ_sync = 1` (`ℓ_MVBA = 24`),
`ℓ_ACS = 2`, `p = 4`, `W = p + Φ_oc + ℓ_ACS = 36`, the ideal ACS, a
periodic run in which every slot takes the fast path. The four parameter
assumptions hold by `decide`. Differences from the plan:

* **The period is one clock reading.** The run is built from one block of
  56 steps, checked once for every clock reading `t` (`Composed.Witness.gstep`,
  through `Cadence.plateauRun`, the generic periodic extension): the block
  holds slot `t`'s start, slot `t − 1`'s fast path, slots `t − 2` and
  `t − 3`'s arm markers, and, when `t ≡ 4 (mod 36)`, the next window's ACS
  and entry. So every slot repeats the one before it shifted by `τ`, and
  every window repeats the first shifted by `Wτ` and `W` slots, as planned.
  A position whose slot or window does not exist yet is the Conductor's
  `tick` in place.
* **Every row holds at the end of a clock reading**
  (`Cadence.bufferedFairFamily_of_ends`): each handler fires in the
  reading its gate opens at, so no gate is open, or nothing it covers is
  enabled, when the clock moves. This is what makes `δ = 0` rows
  satisfiable.
* **A slot stutters by its `participate` re-issued until validator 0 has
  abandoned it, by its `abandon` after** (F24's re-issued `abandon` is the
  second half). Its initial state cannot stutter
  (`Composed.Witness.no_stutter_init`), so its part starts at its first
  step; every slot's part is then one labelled run with the clock shifted
  by the slot's number (`Composed.Witness.srun`). The orchestrator stutters
  by its `tick` in place, the ideal ACS by `trans_refl`, so both parts are
  stepped at every index.
* **Validator 3 sends nothing**, not even the Chorus witness's MVBA
  `Pre-Prepare`: the composed clock moves on the Conductor's `tick`, and the
  re-issued `abandon` keeps each slot's MVBA stepped.
* **One model at fixed types.** The theorems quantify over the claims'
  configuration and run, at `Fin 4` and `ℕ`, rather than over the types
  too; one model is all consistency asks.
* **The Conductor's own claims are covered too**
  (`Composed.Witness.conductor_premises_satisfiable`): their caller
  conditions, (R-tot) and (R-term), hold on the orchestrator's part as
  theorems of the composition (`Composed.caller_totality`,
  `Composed.caller_termination`).

##### 9. Staging and sizing

Each stage is one R-session, numbered when it is scheduled. K0 can run in
parallel with K1. Everything else is in order.

* **K0: the projection spike (F24). Done (R24, 2026-10-03).** Decision: the
  stutter lift plus the per-part premise guarded by a start (F24). No class
  or model edit, and no field implied. The evidence is
  [spikes/14_part_projection.lean](../spikes/14_part_projection.lean). What
  the later stages take from it:
  * **K3** moves the spike's generic half into the library, next to the
    timed projection in [Timed.lean](../Cadence/Timed.lean), with axiom
    pins: `contractRTS`, `stutterSys`, `stutterComp`, `liftRun`, the two
    scheduling lemmas, `partRun` and its transfer lemmas. It builds the
    Conductor's per-window component, `acsComponent w`, whose frame and
    step come from the generated frame lemmas of `acs_state`, as
    `Chorus.mvbaComponent`'s do. It also states the guarded ACS clause of
    the Conductor's `Admissible` in the form quoted in F24.
  * **K6** proves `admissible_exists` by the idle run, which moves only the
    clock and fires `open_slot`. It shows that the rows `acs_propose` and
    `enter_window` are disabled there (no completion, so no readiness), as
    `Chorus.not_enabled_of_idle` does for Chorus. The ACS clause then holds
    by `init_proposed`.
  * **K7** builds the glue's per-slot component, `scComponent s`, with the
    same guarded clause over a correct participant.
  * **K8** shows that the witness's finished parts can stutter: a finished
    slot by re-issuing `abandon` (Chorus's and the MVBA's `abandon` only set
    the flag), and the ideal ACS by construction. It also shows that the
    part's `Admissible` accepts the inserted stutters.
* **K1: the composition edit, untimed.**
  * [Interfaces.lean](../Cadence/Interfaces.lean): C6, C7, C8 with the
    cross-frames.
  * [Cadence.lean](../Cadence/Cadence.lean): `on_open`, the `propose` and
    `abandon` inputs, two invariants.
  * [Conductor.lean](../Cadence/Conductor.lean): `enter_window` reads its
    own decision and abandons the ACS (F19, F22).
  * [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) and
    [Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean): the moved
    field proofs. [Composition.lean](../Cadence/Composition.lean) and
    [System.lean](../Cadence/System.lean): re-proven.
  * A `sat trace` in the glue showing participation.
  * Re-solves: the Conductor's and the glue's sweeps cold (about a minute
    each). The Chorus, FallbackReceipt and Mvba families rebuild warm
    (Interfaces.lean is imported, and their VC statements do not change).
  * Pins: the end-theorem axiom pins re-stated. No `#veil_status` count
    changes. Closes [CompositionContracts.md](CompositionContracts.md) §7
    seam 2, and repairs F18's justification.
  * **Done (2026-10-03, R25).** As planned, with these differences:
    * the glue's record relations `sc_abandoned` and `proposed` are gone;
      `participating`, `abandoned` and `proposed` are ghosts reading the
      instance's own records, so no glue-side copy of a call remains;
    * `on_propose` also requires `participating i s`, the order of
      Algorithm 1, lines 17–19 (`line:participate`–`line:propose`);
    * `[bounded_concurrency_interval]` now states one direction, "an
      active instance is opened and not completed", which is what Lemma 5
      (`lemma:cadence-bounded-concurrency`)'s bound needs. The converse,
      which the paper's proof also states, holds only when `participate()`
      is atomic with `open(s)`; with `on_open` a separate handler, a
      validator that has opened `s` and not yet run it has one active
      instance fewer. Classified as an abstraction with its argument
      ([PaperAlignment.md](PaperAlignment.md) §5.10): the separate
      handlers over-approximate the paper's atomic ones, and the paper's
      runs are among the model's;
    * the Conductor gains the invariant `[acs_abandoned_decided]`
      (Proposition 12 (`prop:acs-no-premature-abandonment`) in state form),
      so the paper's reading is a fact of the model;
    * F18's link is the new [AcsMedian.lean](../Cadence/AcsMedian.lean)
      (`Cadence.acs_median_bracket`, both brackets, so K2's upper bracket
      has its justification already); the `require` stays a stated bridge;
    * sweeps, cold: the glue 182 → 216 cells, the Conductor 189 → 197, both
      green; the slowest cell, `enter_window × bounded_tail`, at 24 s of the
      180 s budget on this machine. K2 is not bundled.
* **K2: the Conductor's timing completion (F21).** Conductor.lean only:
  shift functions, the `s*` rule, the upper bracket, τ-spacing. Re-solves the
  Conductor's sweep, plus
  [Composition.lean](../Cadence/Composition.lean). Can be bundled with K1's
  Conductor edit if K1 stays reviewable.
  * **Done (2026-10-03, R26).** As planned (F21's record), with these
    differences:
    * `acs_decide` takes `first` only: `boundary` and `last` are the shifts
      of it, which keeps the action at 10 parameters with the second
      witness pair;
    * one new invariant, `[win_bounds_shift]` (every window's bounds are the
      shifts of its first slot), so K4 reads the widths off a reachable
      state instead of re-deriving them from the transitions;
    * `[genesis_window]` also ties `genesis_time` to slot 1's starting time
      (the fourth bullet of F21), and `[shift_shape]` replaces
      `genesis_shape`, which it implies at slot 1;
    * F25 found and closed: the boundary is the window's `(p + 1)`-th slot
      and readiness asks for the slots strictly below it, so the model
      covers the paper's `p = 0` (one further commit, re-solved cold);
    * two comments still say the model keeps the widths meta:
      [Interfaces.lean](../Cadence/Interfaces.lean)'s boundedness field
      (K3's file) and [Composition.lean](../Cadence/Composition.lean)'s
      boundedness note (a shared file). They are left for K3 and K4, which
      touch both;
    * the sweep, cold: the Conductor 197 → 205 cells, all green; the slowest
      cell at 19 s of the 180 s budget on this machine.
      [Composition.lean](../Cadence/Composition.lean) and
      [System.lean](../Cadence/System.lean) re-proved without an edit; no
      VC outside the Conductor changed.
* **K3: scaffolding and statements.** C4 and C5 (one
  [Interfaces.lean](../Cadence/Interfaces.lean) edit, warm), timed Conductor
  runs, `ConductorSchedule`, the rows, the per-window ACS projection, the
  ideal ACS, and the claims stated in rely form. Plain Lean, no re-solve.
  * **Done (2026-10-03, R27).** As planned, with these differences:
    * **C5's tolerance is one constant.** (R-tot) is "openings synchronized
      within `d` ⇒ completions synchronized within `d`", at the caller's
      latency `caller_d_tot`: the paper's induction closes because Chorus's
      totality latency equals the tolerance its condition grants ("both
      equal `Δ = d_tot`"). (R-term) takes the same tolerance and
      `caller_ℓ`. Both latencies are data of `OrchestratorTemporal`, since
      Recovery's `2Wτ` holds only at the instance's constants;
      `OrchestratorWithTotality` adds only `d_tot` and the bounded
      Totality. Eventual Totality takes (R-tot) only, as the paper's proof
      uses no termination for it;
    * the generic half of the K0 spike is a new file,
      [PartProjection.lean](../Cadence/PartProjection.lean), next to
      [Timed.lean](../Cadence/Timed.lean) rather than inside it (a shared
      file), with the two field lemmas updated for R25's moves
      (`abandoned` and `participating` are fragment fields now);
    * slots are `ℕ` from `0`: `s : ℕ` is the paper's slot `s + 1`, so
      starting times are `start₀ + s • τ` with no truncated subtraction;
    * the claims' conclusions are the contract's fields read at the
      Conductor's fragment (`orchestratorSafety th`), the caller's
      conditions likewise, through `contractRun`; K6 consumes them as
      stated;
    * the rows are the Conductor's three handlers and the punctual opening;
      the glue's rows of ConductorBounds.md §6.4 time the caller's side and are K7's, over the
      glue's own runs;
    * Boundedness is a state property at bound `2W − p`, with
      `WindowShifts` its only premise; it is exactly what Lemma 5 needs
      (K7), so no separate Lemma-5 statement is made;
    * F26 found (ConductorBounds.md §7) and closed in the same PR, by Lars's decision: the
      ACS contract states that its two inputs are accepted
      (`ACSTemporal.propose_enabled`, `abandon_enabled`, a second
      [Interfaces.lean](../Cadence/Interfaces.lean) edit, in the upper class
      because in `ACSSafety` they diverged a Conductor cell even when
      withheld from the solver, ConductorBounds.md §7 F26). No VC moved;
    * the fault bound (at most `TA.fault_bound` Byzantine) is a premise of
      Totality too, not only of Recovery: the decided interval's row needs
      a correct pair in the decided set;
    * of the two stale "widths kept meta" comments R26 listed, the
      [Interfaces.lean](../Cadence/Interfaces.lean) one is fixed; the
      [Composition.lean](../Cadence/Composition.lean) one stays for K4
      (a shared file K3 does not edit).
* **K4: the window induction.** Proposition 13, Lemma 15, Corollaries 1–3,
  and the count `2W − p` (Proposition 11, Lemma 14) from `[bounded_tail]`
  and the widths. Plain Lean.
  * **Done (2026-10-03, R28).** Two new files, every theorem pinned at the
    standard trio, and the three claims' statements edited once (F27–F29,
    each decided by Lars in the session). What is proven, each item at the
    paper's deadline, with no slack:

    | the paper | Lean | deadline |
    |---|---|---|
    | Proposition 11 (`prop:open-count-window`), interval form | `Conductor.opened_above` | — (a state fact) |
    | Lemma 14 (`lem:boundedness`) | `Conductor.boundedness` (`BoundednessClaim`) | `2W − p` opened, uncompleted slots, exactly |
    | Definition 6 (`def:window-synchronized`) | `EntrySync`, `OpenSync`, `CompSync`, `PropSync`, `WindowSynchronized` | — |
    | Proposition 12 (`prop:acs-no-premature-abandonment`) | the model's `[acs_abandoned_decided]` (K1), consumed as the ACS's `NoPrematureAbandon` | — |
    | Proposition 13 (`prop:window-synchronization`) | `Conductor.window_synchronized` | `max(t, GST) + Δ`, all four conditions |
    | Corollary 1 (`cor:entry-synchronization`) | `Conductor.entry_sync` | `max(t, GST) + Δ` |
    | Corollary 2 (`cor:proposal-synchronization`) | `Conductor.prop_sync` | `max(t, GST) + Δ` |
    | Lemma 15 (`lemma:conductor-totality`) | `Conductor.open_sync`, and `Conductor.totality` (`TotalityClaim`) | `max(t, GST) + d_tot`, `d_tot = Δ` |
    | Corollary 3 (`cor:completion-totality`) | `Conductor.comp_sync` | `max(t, GST) + Δ` |

    Totality closes here, as planned, not in K5. Differences from the plan:
    * **the induction runs over first slots, not windows**
      (`Conductor.window_induction`). The window order is abstract and not
      known to be well-founded. A window is named by its first slot, and the
      entry into a window depends only on smaller slots: its predecessor's
      entry, the completions below the predecessor's boundary, and the
      proposals to its ACS. The paper's four per-window steps are the lemmas
      `entry_step`, `open_step` and `prop_step`, with (R-tot) for the
      completions (`comp_of_open`);
    * **Boundedness needs no successor window in the order**: the one
      window above `s`'s that can hold an opened slot is found from that
      slot's own window, through its entered predecessor. That is a new
      plain-Lean reachability induction, `Conductor.entered_pred`, since the
      model records the predecessor only in a guard. It lives with the
      other model facts in
      [Conductor/Boundedness.lean](../Cadence/Conductor/Boundedness.lean);
    * **three statement changes**, each found by the proof and decided by
      Lars (F27, F28, F29): an ordered time, unbounded starting times, and
      no fault bound for Totality. K3's note that the fault bound was "a
      premise of Totality too" is superseded by F29;
    * the ACS is consumed through its contract only: Δ-Totality on the
      window's part of the run (`Cadence.acs_totality_in` under
      `AcsAdmissible`), `integrity`, `propose_enabled` and
      `abandon_enabled`. Its termination, its fault bound and the median
      bracket are not used. Chorus enters only through (R-tot). The
      decided interval's row (`TimedRows.decide`) is not used by Totality;
      it is Recovery's;
    * the two rows are consumed in their diagonal form
      (`BufferedFairFamily.diag`), at `δ = 0`: a gate open from an index
      whose clock is within the deadline fires its row by that deadline;
    * [Composition.lean](../Cadence/Composition.lean)'s stale note about the
      widths is fixed (comment only). The model header of
      [Conductor.lean](../Cadence/Conductor.lean) still lists
      `B`-Boundedness as unproven in its discharge map. It is a model
      file, so editing it re-runs the sweep; it is left for K6, which
      rewrites the status text.
* **K5: Recovery.** Propositions 14–19 and Lemma 16. Plain Lean; the
  schedule arithmetic is where F4-style slack would show.
  * **Done (2026-10-03, R29).** One new file,
    [Conductor/Recovery.lean](../Cadence/Conductor/Recovery.lean), every
    theorem pinned at the standard trio. `RecoveryClaim` is proven at the
    paper's `𝓡 = 2Wτ` (`Conductor.recovery`), after one statement edit
    with two premises added (F28's `StartsUnbounded`, as planned, and
    F30's `WindowsUnbounded`), both decided by Lars in the session. What is
    proven, each item at the paper's deadline (`d_tot = Δ` at `δ = 0`):

    | the paper | Lean | deadline |
    |---|---|---|
    | Proposition 14 (`prop:conductor-open-to-complete`) | `Conductor.open_to_complete` | `max(t, GST) + d_tot + ℓ_chorus`, for every correct validator |
    | Proposition 15 (`prop:enters-every-window`) | `Conductor.enters_every_window` (and `window_entered_by`, by some time) | eventually, for window 1 and each of its successors |
    | Proposition 16 (`prop:window-open-time`) | `Conductor.window_open_time` | `max(T₁(ω), GST) + d_tot + ℓ` |
    | Proposition 17 (`prop:window-progression`) | `Conductor.window_progression` | (1) the next window's first slot is `slot(ω, W) + 1`; (2) entered by `T₁(ω + 1)` |
    | Proposition 18 (`prop:smooth-windows`) | `Conductor.smooth_windows` | every slot of a later window opened by its starting time |
    | Proposition 19 (`prop:first-post-gst-window-time`) | `Conductor.first_post_gst_window_time` | `T₁(ω) ≤ GST + Wτ` |
    | Lemma 16 (`lemma:conductor-recovery`) | `Conductor.recovery` (`RecoveryClaim`) | `𝓡 = 2Wτ` |
    | (slack) | `Conductor.recovery_sharp` | `𝓡 = (W + p − 1)τ` |

    Differences from the plan:
    * **one engine instead of separate arguments.** `succ_window`: once
      every correct validator has entered a window by `X`, every correct
      validator proposes to the next ACS by
      `max(X, T, GST) + ℓ_chorus`, where `T` bounds the starting times
      below the readiness boundary, and enters the next window `ℓ` later.
      Propositions 15–19 instantiate it. The paper's case splits on an
      early correct decision or entry, in Propositions 15, 16 and 17
      point 2, are not needed: once every correct validator has proposed,
      the ACS's `ℓ`-termination applies whatever happened before;
    * **Proposition 16 needs neither Proposition 15 nor assumption (3).**
      It is stated for a window whose interval is recorded. The median's
      lower bracket, a correct proposal at or below the first slot, was
      made by `T₁(ω)`, since the `s*` rule never picks a slot that has
      started. Corollaries 1–3 then make every correct validator ready
      and proposing by `max(T₁(ω), GST) + Δ`;
    * **Proposition 15 and the windows' existence are one induction**
      along the chain of successors (`WinSucc`), which `WindowsUnbounded`
      makes infinite (F30). The smallest post-GST window is found on it
      (`exists_post_gst`): the chain's first slots grow (`chain_bounds`),
      and `StartsUnbounded` puts one past GST;
    * **window 1 may be post-GST with `T₁(1) > GST + Wτ`.** The paper's
      time starts at `0 = T₁(1)` with `GST ≥ 0`. A run here starts at slot
      1's starting time, and GST is arbitrary, so Proposition 19's `ω = 1`
      case does not carry over. `recovery` treats window 1 apart: it is
      entered at its starting time, so its slots are opened at theirs, and
      Proposition 19 is stated for `ω > 1` (a predecessor that starts
      before GST). Not a paper issue: at `GST ≥ T₁(1)` the cases agree;
    * **the decided interval's row is fed one correct pair**, used as
      both median witnesses (`correct_pair`, from `validity_quantitative`
      and the fault bound). The model records any first slot between two
      correct pairs, and the timing argument reads only those brackets
      (`recorded_bracket`), so it holds at the median as well;
    * **the ACS through its contract only:** `T_acs.Admissible` of the
      window's part (`AcsAdmissible`), its ℓ-Termination
      (`Cadence.acs_termination_in`), Δ-Totality through Lemma 15's
      corollaries, Validity's two halves and its input-enabledness. Chorus
      enters only through (R-tot) and (R-term), at `d_tot` and
      `ℓ_chorus`. `0 ≤ ℓ_chorus` is derived from the MVBA schedule
      (`ConductorSchedule.ℓchorus_nonneg`), so no premise like
      [Premises.md](Premises.md) §2.9 is added.

    **The schedule arithmetic: slack (P18), no shortfall.** The proof
    needs:
    * `(p − 1)τ + ℓ_chorus + ℓ ≤ Wτ` (Proposition 17, both points), not
      (1) with `Φ_oc`;
    * `(p − 1)τ + ℓ_chorus ≤ (W − 1)τ` (Proposition 19 only), not (2)
      with `Φ_oc`;
    * `0 < ℓ`, not (3)'s `Δ < ℓ`;
    * (4) as stated (Propositions 18 and 19).

    Where every correct validator has already opened the slots, Chorus's
    termination applies directly, and Proposition 14's `d_tot` is not paid.
    Proposition 17 point 1 needs the proposals only by `T₁(ω + 1)`, which
    (1) implies. `𝓡 = (W + p − 1)τ ≤ 2Wτ` suffices, because the smallest
    post-GST window is itself entered by its `T_p` (`recovery_sharp`).
    With P5's tight `ℓ_chorus = 4Δ + ℓ_MVBA` (F4) as well, the `Φ_oc` of
    (1)–(2) could shrink from the paper's `6Δ + ℓ_MVBA` to `4Δ + ℓ_MVBA`,
    one `Δ` below the ConductorBounds.md §6.3 remark's `5Δ + ℓ_MVBA`. The claim keeps the paper's values,
    as the Chorus leg did. The proof needs nothing beyond the stated
    assumptions, so no finding of the F-kind arises from the arithmetic.

    **Premises: each is used** ([Premises.md](Premises.md) §9, "Used in").
    The one weakly used is assumption (3), for `0 < ℓ` only; the others
    enter their named steps. No removal is proposed, since (3) is a field
    the composed claims share with the paper, and P18 reports the slack
    to the authors.
* **K6: the contract instances.** `OrchestratorTemporal` and
  `OrchestratorWithTotality` at `Conductor.orchestratorSafety`, the join
  with its `…_toSafety` `rfl` lemma, then the
  [Cadence.lean](../Cadence.lean) rows and pins,
  [CLAUDE.md](../CLAUDE.md)'s status text,
  [Architecture.md](Architecture.md) §4 (after R21), and
  [CompositionContracts.md](CompositionContracts.md) §5.
  * **Done (2026-10-03, R30).** One new file,
    [Conductor/Temporal.lean](../Cadence/Conductor/Temporal.lean), every
    declaration pinned (at the standard trio, except
    `Conductor.startsUnbounded_of_startTimes` at `[propext, Quot.sound]`).
    No class, claim or model statement changed; the model file's header
    and the shared files' status text were edited, comment only. What is
    proven:

    | field | value | proven by |
    |---|---|---|
    | `Admissible` | `Conductor.Admissible`: `contractRun` of a labelled run meeting `Sync` | — (a definition: the claims' run premises by name) |
    | `admissible_exists` | | `Conductor.admissible_exists`, the idle run (`Conductor.idleRun_sync`) |
    | `clock_agrees` | | `ClockAgrees`, a conjunct of `Sync` |
    | `caller_d_tot`, `caller_ℓ` | `d_tot`, `ℓ_chorus` | `rfl` (`Conductor.conductorTemporal_caller`) |
    | `totality` | | `Conductor.totality` (Lemma 15) |
    | `bound`, `boundedness` | `2W − p` | `Conductor.boundedness` (Lemma 14); `rfl` (`Conductor.conductorTemporal_bound`) |
    | `recovery_time`, `recovery` | `2Wτ` | `Conductor.recovery` (Lemma 16); `rfl` (`Conductor.conductorTemporal_recovery_time`) |
    | `OrchestratorWithTotality.d_tot`, `.totality` | `d_tot`, the paper's `Δ` at `δ = 0` | `Conductor.totality`; `rfl` (`Conductor.conductorWithTotality_d_tot`), and `Conductor.conductorWithTotality_d_tot_paper` by rewriting |

    `Conductor.conductorFull` is the join, and `Conductor.conductorFull_toSafety`
    hands back `Conductor.orchestratorSafety th` by `rfl`. The sharper
    `Conductor.recovery_sharp` and P18's slack stay separate theorems; the
    class carries the paper's values. Differences from the plan:
    * **the instance's hypotheses are the claims' configuration
      premises**, by name (`StartTimes`, `WindowShifts`, `StartsUnbounded`,
      `WindowsUnbounded`, the ACS's `Δ`, `ℓ` and fault bound), as R20 took
      Chorus's; `Admissible` is the run premises only, so that
      `admissible_exists` needs no configuration it cannot build;
    * **the idle run opens window 1's slots.** The plan said it "moves
      only the clock and fires `open_slot`". (P-open) obliges every
      scheduled slot to open at its starting time, so the run proceeds in
      blocks, one per slot: a `tick` to the slot's starting time, then
      one step per validator, which opens the slot there if the validator
      is correct and the slot lies in window 1, and is a `tick` in place
      otherwise. Its clock is the model's `now`, unbounded because the
      starting times are (`StartsUnbounded`, used here a second time);
    * **the rows stay shut because `p ≥ 2`**, which assumption (4) implies
      (`ConductorSchedule.two_le_p`: `0 ≤ d_tot` and `0 < ℓ`, so
      `(p − 1)τ > 0`). Window 1's first slot then lies below its readiness
      boundary (`WindowShifts`, `Conductor.genesis_boundary_pos`) and is
      never completed, so no correct validator is ready; at `p = 0` the
      proposal row would be owed at once. So `admissible_exists` takes
      `WindowShifts` and `StartsUnbounded`, both already premises;
    * **two configuration premises are discharged at the system's types**
      (task 4): `WindowsUnbounded` at `window := ℕ`
      (`Conductor.windowsUnbounded_nat`), and `StartsUnbounded` from
      `StartTimes` over an Archimedean time once `0 ≤ start₀`
      (`Conductor.startsUnbounded_of_startTimes`; F28's example shows the
      condition is needed). `Conductor.conductorFullNat` is the full
      contract with both discharged, available to K7;
    * **[System.lean](../Cadence/System.lean) keeps the fragments.** Its
      theorem is safety, generic in the slot order and the time; the full
      instance would narrow it to `slot := ℕ`, an ordered time, a schedule
      and an `ACSTemporal`, which changes its statement and adds nothing
      safety needs;
    * the model file's header ([Conductor.lean](../Cadence/Conductor.lean),
      comment only) is updated, so the Conductor's sweep re-ran warm. Its
      liveness section ("Liveness — meta-argument") still narrates
      totality and recovery as meta-axioms. It is not the header, so it
      is left for a later model edit ([TODO.md](TODO.md)).
* **K7: the composed timed claims.** The composed run, the per-slot Chorus
  projections, C1/C2/participation/synchronized participation discharged,
  (R-tot)/(R-term) from Chorus, **Corollary 4 as a theorem**, and the timed
  `𝓡`-Liveness and censorship resistance at `𝓡 = 2Wτ`. Plain Lean.
  Also **Lemma 5 (`lemma:cadence-bounded-concurrency`)'s bound** as a
  theorem: at most `𝓑` instances actively participated in, from the glue's
  `[bounded_concurrency_interval]` (an active instance is opened and not
  completed) and `OrchestratorTemporal.boundedness` at the instance K6
  provides (take the least of `𝓑 + 1` active slots: the other `𝓑` are
  opened above an opened, uncompleted slot). Possibly two sessions.
  * **Done (2026-10-03, R31; censorship resistance 2026-10-04, R31.2).**
    Six new files under [Composed/](../Cadence/Composed/Schedule.lean) and
    [Chorus/Inclusion.lean](../Cadence/Chorus/Inclusion.lean), every
    theorem pinned at the standard trio. One shared statement file edited,
    by Lars's decision on F31: [Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)
    gains the standalone premise (P-incl). What is proven:

    | the paper | Lean | at |
    |---|---|---|
    | the composed timed run | `Composed.sysRTS`, `Composed.TSysRun`, `Composed.orchComponent`, `Composed.slotComponent`, `Composed.GlueRows`, `Composed.SysSync` | — (definitions: the claims' run premises by name) |
    | C1, C2, participation, Δ-synchronized participation (Chorus's caller conditions) | `Composed.c1_slot`, `Composed.c2_slot`, `Composed.participating_by`, `Composed.sync_slot` | `D = start + Δ`; `Δ` |
    | (R-tot), (R-term) (the Conductor's caller conditions) | `Composed.caller_totality`, `Composed.caller_termination` | `d_tot = Δ`, `ℓ_chorus` |
    | Lemma 15 (`lemma:conductor-totality`) within Cadence | `Composed.openings_sync` | `Δ` |
    | Corollary 4 (`cor:chorus-correctness-within-cadence`) | `Composed.corollary4` (`Corollary4Claim`); `Composed.corollary4_bounded_termination`, `…_totality`, `…_termination` | `5Δ + ℓ_MVBA`, `Δ` |
    | Lemma 5 (`lemma:cadence-bounded-concurrency`) | `Composed.boundedConcurrency` (`BoundedConcurrencyClaim`) | `𝓑 = 2W − p` |
    | Lemma 16 (`lemma:conductor-recovery`) within Cadence | `Composed.recovery_in`, `Composed.recovery_sharp_in` | `2Wτ`; `(W + p − 1)τ` |
    | `𝓡`-Liveness (Definition 2 (`def:liveness`), Lemma 2 (`lemma:cadence-liveness`)) | `Composed.liveness`, `Composed.liveness_sharp` (`LivenessClaim`) | `2Wτ`; `(W + p − 1)τ` |
    | Proposition 3 (`prop:honest-positive-entry`), timed | `Chorus.within_proposal_recorded_incl` | by the deadline, under (P-incl) |
    | `𝓡`-Censorship resistance (Definition 3 (`def:censorship-resistance`)) | `Composed.censorship`, `Composed.censorship_sharp` (`CensorshipClaim`) | `2Wτ`; `(W + p − 1)τ` |

    Differences from the plan:
    * **the parts are stutter-lifted, both of them**: the orchestrator's
      as well as each slot's, so both premises read
      "`T.Admissible (partRun p)`" with the instance's own `Admissible`
      (`Conductor.Admissible`, `Chorus.Admissible`), restated nowhere;
    * **one fault pattern, Chorus's** (`fmF`): the Conductor, the ACS
      and the glue are stated at it, so no transport like
      [System.lean](../Cadence/System.lean)'s `hbyz` is needed;
    * **the Conductor is consumed through its lemmas**
      (`Conductor.totality`, `Conductor.recovery`), not through the
      contract instance: the instance takes Recovery's configuration
      premises, and Corollary 4 needs only Totality's. Chorus is consumed
      through its contract instance (`Chorus.chorusWithTotality`,
      `Chorus.chorusTemporal`), whose fields are exactly the claims used;
    * **Corollary 4's Termination needs no Conductor premise**: its one
      caller condition, C1, is the glue's invariant;
    * **Liveness concludes `V.slot = s`** as Definition 2 asks, from the
      contract's `slot_safety` through the glue (`Composed.inv_appended_slot`);
    * **System.lean is unchanged.** The composed timed claims sit in
      [Composed/](../Cadence/Composed/Liveness.lean), indexed in
      [Cadence.lean](../Cadence.lean) next to the safety theorem;
    * **censorship resistance needed F31's decision** (R31.2): the
      tie-break premise (P-incl), a proof that a proposer has not
      abandoned before proposing (`Chorus.committed_post_deadline`: a
      finalization postdates the deadline), and that a correct proposer's
      proposals are its own inputs (`Composed.run_proposed_of`, from the
      contract's frames), for the root's well-encodedness.

    **Premises** ([Premises.md](Premises.md) §0, each with its "Used
    in"): the union of the parts' environment premises (the glue's rows,
    the Conductor's `Sync` on its part, Chorus's `Admissible` on every
    started slot's part, the configuration, the assumed ACS), with every
    caller condition discharged; censorship resistance adds (P-incl) on
    every started slot and a well-encoded root. One is reported, not
    removed: Chorus's non-empty proposer set (`hprop`) enters only to form
    Chorus's contract instance. The glue's `propose` row, reported in R31,
    is used by censorship resistance since R31.2.
* **K8: non-vacuity. Done (2026-10-04, R32).** The periodic composed
  witness (ConductorBounds.md §8.2) and the ledger moved to the premises page
  ([Premises.md](Premises.md) §0, ConductorBounds.md §0.5, ConductorBounds.md §9). One session; the plan's
  second was not needed. No model, proof or statement file changed. What
  K0 asked of K8 holds: a finished slot stutters by its re-issued `abandon`,
  the ideal ACS by construction, and each part's `Admissible` accepts the
  stutters. **The Conductor leg is complete.**

**Total:** nine to eleven sessions. **No stage re-solves the Chorus or Mvba
families cold.** K0 settled F24 without a `TransitionSystemSafety` change.

**Constraints:**

* one [Interfaces.lean](../Cadence/Interfaces.lean) edit at a time, so K1
  and K3 are serialized with each other and with any other contract edit;
* K1 and K2 both edit [Conductor.lean](../Cadence/Conductor.lean);
* the premise-presentation pass (R21) owns the premises page and
  [Architecture.md](Architecture.md) §4 until it lands.

As in the Chorus leg, the dominant risk is statement churn. F16–F25 are the
churn this record tries to absorb before any Lean.

### From Liveness.md

*The Chorus run-level liveness leg's stage records (2026-09-16 to
2026-09-29), with the section that framed the work left at the time, moved
here in R33. Inside this record, §4 and §4.1–§4.7 are its own subsections;
§1–§3 are [Liveness.md](Liveness.md)'s. What the leg built is
[Liveness.md](Liveness.md) §4 today.*

#### Two passages of Liveness.md §2, as they read before R33

From the (F-justice) bullet: "([Bounds.md](Bounds.md) §6.2.4 and §6.4.7
have the history: from R3 to R6 the premise was stated in that form,
because until the fired-once guards some fair labels stayed enabled after
firing, one per quorum)"; "**A step is owed only for messages from correct
senders** (`Chorus.Owed`, since R8)". From the `MvbaAdmissible` bullet:
"(`Chorus.fAvail_of_fJustice`, since R16; until then (F-avail) was part of
this premise). The timed (Δ-avail) is derived too, since R19"; "(F-justice)
on Chorus's handoff `accept_mvba_commitqc` (`Chorus.fRelay_of_fJustice`,
since R8 …)"; "`MvbaAdmissible` itself did not change shape." From the
(A-viewsync) summary of §2.1: "(Until R8: before a commit certificate
exists. A certificate the adversary assembles may reach nobody, so it is no
longer enough; [Bounds.md](Bounds.md) §6.4.2.)"

The (A-mvba) bullet:

* **(A-mvba), retired.** Until `Chorus.termination` existed, the MVBA's
  termination was an assumption: invoked with per-proposer evidence, the
  MVBA eventually decides. The two premises above replace it. The
  instance Chorus runs is the supplement's leader-based protocol, whose
  termination is a theorem (`Mvba.termination`). The randomised
  primitive of the published paper terminates with probability 1, which no
  deductive framework expresses, so that argument stays on paper, as for
  any cryptographic primitive; it is not part of this development's claim.
  The Lean prose names it only as retired (aligned in the participation
  edit, [Bounds.md](Bounds.md) §6.4.6 S1).

#### 3. What would close the rest

Veil has no fairness annotations and no quantification over runs, so the
rule "continuously enabled ⇒ eventually fires" is not expressible today.
The designed extension — fairness classes on actions,
ω-acceptance/response properties, discharged by the POPL'18
**liveness-to-safety** reduction on the existing safety-VC pipeline — is
Veil work and lives in the fork:
**[docs/Liveness.md](https://github.com/larskuhtz/veil/blob/lars/liveness/docs/Liveness.md)
on the `lars/liveness` branch of `larskuhtz/veil`**. (F-justice) is already
the premise of a Lean theorem (`Chorus.termination`, `Mvba.termination`),
proven over runs of the generated transition system outside Veil's
pipeline. With the extension, deterministic liveness properties
("honest fast-path commit eventually", "slot eventually decides") would be
stated and discharged inside the models, like their safety properties. The
randomised MVBA primitive's probability-1 termination stays out of scope
regardless, and so do real-time bounds (GST, latency) other than the MVBA's,
which is proven over timed runs outside the Veil models (Liveness.md §2.1).

The paper's concrete Δ-bounds are a separate, *incomparable* layer — they
assume strong partial synchrony, where the model's claims above need only
eventual delivery. How the two relate, and the routes by which bounds
could be brought into the model, is [Bounds.md](Bounds.md).
#### 4. The next leg: Chorus at run level

`Mvba.termination` is the pattern working at one layer. Applying it to
Chorus is what retires **(A-mvba)** — and with it the last of the
`(F-justice)`/`(F-byz)`/`(A-mvba)` meta-axioms — which
[TODO.md](TODO.md) calls the single largest reduction of
[Architecture.md](Architecture.md) §4 available. This section is that
leg's working record — its design, the record of each finished stage, and
the kick-off of the current one — so a fresh session does not re-derive the
design. Liveness.md §1–§3 above state what is proven. **The leg is complete**
(2026-09-29): §4.7 is its closing record.

**Target.** A run-level theorem in the shape of `Mvba.termination`: every
correct validator eventually finalizes every slot, from named premises, each
a predicate on a run, with `Mvba.termination` consumed exactly where
(A-mvba) sits today. Same discipline as [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean): the premises
are written down as named `Prop`s **before** the proof exists, so none can
become a hypothesis because a proof needed it.

**What is already there.** [Cadence/Fairness.lean](../Cadence/Fairness.lean)
is generic over any `RelationalTransitionSystem`, so `LRun`, `WeaklyFair`,
`eventually_forall` and the rest apply to Chorus unchanged. Chorus's
fair-progress content is proven at state level ([Chorus.lean](../Cadence/Chorus.lean)'s liveness
section), and the two hardest counting steps are already plain-Lean
theorems: `progress_dichotomy_of_saturation` and
`build_totality_of_reachable`. Chorus's phase markers are weakly fair, so
unlike the MVBA there is no timing premise to invent — Liveness.md §2.1 says why.

**Settle this first, because it is the whole design.** Chorus holds an
*abstract* MVBA state and advances it with the oracle action `mvba_step`,
which takes any transition the contract allows and is deliberately **outside**
(F-justice) — its scheduling is the instance's own admissible-execution
model. So consuming `Mvba.termination` needs a **projection**: from an
`LRun` of the composed system ([System.lean](../Cadence/System.lean), where the abstract state is
`Mvba.State`) to an `MvbaRun`, keeping only the steps at which the MVBA
state moved, and a proof that weak fairness survives the re-indexing — a
label continuously enabled in the projection was continuously enabled in the
composed run. The premise that replaces (A-mvba) is then "the composed run's
MVBA projection satisfies `Mvba.termination`'s premises", which is the
untimed analogue of `MVBATemporal.Admissible`. It must be built that way and
**not** by weakening a class field: that rule is in
[../CLAUDE.md](../CLAUDE.md) and it is what makes the absence of a
`…Temporal` instance mean something.

**Staging** (reassess after step 1, which is the risky one):

1. ~~The projection and the fairness transfer, generic, in [Fairness.lean](../Cadence/Fairness.lean).~~
   **Done, 2026-09-16** — §4.2 is the record and the reassessment.
2. ~~Chorus's label classes and premises — one named `Prop` each, mirroring
   [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)'s four-class discipline and its `label_classified`;
   and the `Component` instance for Chorus at the `Mvba` instantiation.~~
   **Done, 2026-09-16** — [Cadence/Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean);
   §4.3 is the record, including the one premise the sketch above did not
   foresee.
3. ~~The fast-path chain to a commit certificate — §4.4 is the kick-off
   record: what to prove, from which facts, and the traps already known.~~
   **Done, 2026-09-28** — [Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean);
   §4.5 is the record, including four corrections to §4.4.
4. ~~The fallback and MVBA arms, the second consuming `Mvba.termination`
   through the projection.~~ **Done, 2026-09-29** — §4.6 is the kick-off
   record and, at its end, the record of the stage.
5. ~~The assembly, the [Cadence.lean](../Cadence.lean) row and pin, and retiring (A-mvba) from
   [Architecture.md](Architecture.md) §4.~~ **Done, 2026-09-29** — §4.7.

**Cost warning.** If the argument needs new Chorus invariants, that is a
re-solve of the Chorus family, several times the MVBA's (the
`#veil_status` pins in [Chorus/Certify.lean](../Cadence/Chorus/Certify.lean)
and [Mvba/Certify.lean](../Cadence/Mvba/Certify.lean) have the cell counts).
Budget it before touching [Chorus.lean](../Cadence/Chorus.lean), even for a comment.

##### 4.1 Running this leg and the bounds leg in parallel

This leg and [Bounds.md](Bounds.md) §6.1 are **independent**: neither
needs the other's result, and the MVBA bounds leg discharges
(A-viewsync) while this one consumes `Mvba.termination` as it already
stands. **The MVBA bounds leg is complete** (2026-09-28, [Bounds.md](Bounds.md)
§6.2.8). The rules below held throughout, with one prose exception: step 4
updated the docstring of `Terminates` in [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean), which had said
the timed form had no instance. No statement changed. The seam proposal of
[Bounds.md](Bounds.md) §6.2.1 was decided and carried out before stage
4, together with the finiteness convention (`Mvba.termination` takes
`[Fintype node]`) and the fixes §4.6 asks for first; §4.6's update says what
changed for this leg.
Rules that keep them from colliding:

* **Neither leg edits [Cadence/Interfaces.lean](../Cadence/Interfaces.lean).**
  The bounds leg *instantiates* `MVBATemporal`, it does not change it; this
  leg needs no class change. An edit there re-solves the Chorus family and
  forces the other leg to rebase, so it is a decision to take jointly.
* **[Cadence/Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) is
  read-only for both.** Both consume `Mvba.termination`; neither should need
  to restate or reshape it.
* **This leg owns [Fairness.lean](../Cadence/Fairness.lean) and everything under `Cadence/Chorus`**;
  the bounds leg owns its own new files and puts *timed* run vocabulary in
  one of them rather than in [Fairness.lean](../Cadence/Fairness.lean).
* **The projection is shared conceptual territory** — the bounds leg needs
  the same relation between a composed run and an MVBA run, in its timed
  form. This leg owns the definition — it is `Cadence.Component` and
  `Component.Projection` in [Cadence/Fairness.lean](../Cadence/Fairness.lean)
  since 2026-09-16 (§4.2) — and the bounds leg should refine it rather than
  invent a second one: a timed projection is a `Projection` whose composed
  run carries a clock, and the index map `Component.idx`/`Component.cover`
  is what relates the two clocks.
* Both will append rows and pins to [Cadence.lean](../Cadence.lean) and paragraphs to these
  docs. Expect small textual conflicts there and nothing worse.
* **One expensive build at a time.** That constraint does not parallelise:
  the machine runs one family re-solve at a time, and this leg's are the
  large ones. Two sessions can think in parallel; they cannot both re-solve
  in parallel.

##### 4.2 Stage 1, done: the projection, and what it settled

*Record of 2026-09-16. The code is the "Components" half of
[Cadence/Fairness.lean](../Cadence/Fairness.lean); every declaration named
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

Every pin is at the standard trio; [Fairness.lean](../Cadence/Fairness.lean)'s trust-base section
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
   [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)'s own definitions and restating none of them. This
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
instance graduated into it). Nothing in this stage touches [Chorus.lean](../Cadence/Chorus.lean),
[Interfaces.lean](../Cadence/Interfaces.lean) or [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean), and the Chorus family is
untouched.

**What to watch in stages 3–5.** The `Scheduled` field makes the final
theorem silent about runs in which the MVBA is stepped finitely often. That
is correct (it excludes unfair schedulers, as every fairness premise does),
but it is a premise the paper does not spell out, so it must appear by name
in [Architecture.md](Architecture.md) §4 when (A-mvba) is retired, not be absorbed into
"(F-justice)".

##### 4.3 Stage 2, done: the classification, the premises, the target

*Record of 2026-09-16. The file is
[Cadence/Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean), a
sibling of [Cadence/Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)
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
reason. Against [Chorus.lean](../Cadence/Chorus.lean)'s prose list of (F-justice) actions the
complement form also covers `deliver_chunk_assigned` and
`broadcast_commitqc_*`, which §7 of [ChorusDesign.md](ChorusDesign.md) already uses as
fair; the model's prose should be aligned the next time [Chorus.lean](../Cadence/Chorus.lean) is
edited for another reason (a comment edit is a family re-solve).

**The component instance.** `Chorus.mvbaComponent thS thM : Component
(atMvba thM) thS mvbaRTS thM` — §4.2's recipe, landed: `frame` from the 38
generated lemmas, `step` from the two oracle guards, `init` from the
initializer, and no new cell.

**The premises, one named `Prop` each**, over `ChorusRun thS thM` (a
labelled run of Chorus with its MVBA constraint filled by `Mvba.mvbaSafety
thM`, the instantiation [System.lean](../Cadence/System.lean) uses):

* **`FJustice`** — (F-justice): weak fairness of every `JusticeLabel`.
  (Since stage 4, `mvba_propose` is covered per validator and value as one
  family over its successor-state parameter; §4.6.)
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
  input (the MVBA's own check of the caller's obligation, which the
  contract states as an antecedent of `MVBATemporal.termination`), while the MVBA theory's `valid` is a predicate on the
  vector alone that nothing in the composed system relates to Chorus's
  certificates. So a correct validator that has built a certified
  meta-block can call `propose` only if certified vectors are `Valid`.
  The premise therefore has two clauses, both at every point of the run
  and both stated with `Certified` — `mvba_propose`'s three validity
  guards verbatim, the first two of which are the handlers' bridge
  `require`: certified ⇒ `Valid`, and decided by a correct validator ⇒
  certified. It is the run-level form of the one stated bridge
  ([CompositionContracts.md](CompositionContracts.md) §3, §7 item 1) and its content is the
  cryptographic one — a `Valid` meta-block's certificates are genuine and
  genuine certificates are `Valid` — which no class field can carry
  because `Valid` is fixed before Chorus's state exists. The safety proofs
  need neither direction.

**The target.** `Terminates r`: every correct validator eventually has
`local_committed` — `finalize_commit` fired for it — and
`TerminationClaim thS thM := ∀ r, FJustice r → MvbaAdmissible r →
ValidBridge r → Terminates r`. A definition, asserted nowhere; the theorem
is stages 3–5's. Absent by design: any timing premise (Liveness.md §2.1), any
`all_honest_recorded`-shaped premise (it buys proposal inclusion, not
termination), and the quorum machinery (the concrete family the counting
theorems are stated over, `byzNodeSetFin` at every `n = 3f+1`, and
`Mvba.termination`'s three class hypotheses are hypotheses of the theorem,
not part of the claim).

**What to watch in stages 3–5**, in addition to §4.2's note on
`Scheduled`: the theorem will be at the concrete quorum family and at
[System.lean](../Cadence/System.lean)'s `chorusTheory` (the entry-vector projections have to be the
standard ones to *build* a proposal), so `TerminationClaim` stays generic
and the theorem instantiates it; and `ValidBridge` must be named in
[Architecture.md](Architecture.md) §4 alongside `MvbaAdmissible` when (A-mvba) is retired —
it is not a fairness assumption and must not be filed as one.

##### 4.4 Stage 3, the kick-off record: saturation, and the commit route

*Written 2026-09-24 at the hand-over between sessions, so the next one does
not re-derive the design. Nothing below is done; §4.2 and §4.3 are what is.
Stage 3 has since landed as planned, with four corrections — §4.5.*

**Where it goes.** A new file, [Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean), importing
[Cadence/Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean) (the
claim and its vocabulary) and
[Cadence/Chorus/Progress.lean](../Cadence/Chorus/Progress.lean) (the
dichotomy; it brings `Counting`, `Pigeonhole` and, through them,
[Chorus/Certify.lean](../Cadence/Chorus/Certify.lean)'s `reachable_*` projections). Stages 3–5 all live
there, one section each, and it is split by arm if it outgrows
[Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean). [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean) stays the statement file and
keeps its light imports. Add the new module to [scripts/revalidate.sh](../scripts/revalidate.sh)'s
end-theorem stage as `Chorus.Liveness` was.

**The regime.** Work at the concrete quorum family from the start — `node :=
Fin n`, `nodeset := ByzNSet n`, `nset := byzNodeSetFin n f hf is_byz hbyz` —
because the dichotomy is stated there and because "every proposer" needs a
complete list of nodes, which `List.ofFn (n := n) id` gives and no generic
class in the development does. The `cpv%`/`pafr%` macros of [Chorus/Progress.lean](../Cadence/Chorus/Progress.lean)
are the canonical instantiation; copy them verbatim. The quorum classes
`Mvba.termination` takes exist at that family as `byzNodeSetFinGen_enum` and
`byzNodeSetFinGen_honest` ([Cadence/ByzQuorum.lean](../Cadence/ByzQuorum.lean));
the honest quorum they hand over is the witness for every assembly guard.
Stay in the generated instance regime (`open Classical`, no `DecidableEq`
binders), and put the `MVBASafety` instance in scope with `letI :=
Mvba.mvbaSafety thM` before applying generated lemmas (§4.3).

**The one rule of consumption.** Every temporal step is
`Cadence.exists_disabled_of_never_fires` — a weakly fair label that never
fires from `N` on is disabled somewhere from `N` on — and the proof of each
link shows the label *stays* enabled unless the disabling event is itself the
progress wanted. [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)'s first link (`enabled_decide`,
`decide_effect`, `eventually_decided_of_commitqc`) is the template: an
enabledness lemma that turns `Enabled` into the action's guards, an effect
lemma that reads the firing off the post-state, and the fairness step.
Monotone facts along the run come from M13's `Chorus.<f>.mono` through
`LRun.mono`; finitely many eventualities collapse through
`LRun.eventually_forall` over `enum.members` or the node list.

**What stage 3 proves**, in two theorems the assembly (stage 5) will use:

1. *Every correct validator is eventually saturated* — for each correct `i`,
   some index at which `i` has cast fast (`msg_commit_cast i` with a commit
   signature per proposer) or cast fallback (`msg_fallback_sig i` with a
   fallback signature per proposer). This is the `hsat` hypothesis of
   `progress_dichotomy_of_saturation` for one validator; the theorem's
   hypothesis is the conjunction over the honest population, which is the
   collapse above. The chain:
   * the phase reaches `post_mvba_arm` and stays there: the three
     `advance_to_*` actions are weakly fair and each is enabled at exactly
     its phase; `Chorus.phase.init` starts it at `pre_deadline`, and every
     other action has a generated `frame_phase`;
   * every correct validator votes: `vote i` needs only `phase ≠
     pre_deadline ∧ ¬ local_voted i`, and `local_voted` is monotone; then
     the honest quorum has voted at one index, so `msg_vote_cast` holds on
     it (`voted_implies_cast`), which is the witnessed supermajority the
     fallback guards need;
   * per proposer, `fb_sign_pos i J M q qc` or `fb_sign_neg i J qv` is
     enabled with `qv := honestQuorum` unless `i` has cast fast or already
     cast fallback — `progress_fallback_signing` at the reachable state says
     which, and supplies the `q`/`qc` witnesses the label carries; once
     every proposer is signed, `cast_fallback_vote i` is enabled under the
     same proviso. Each step fires or is disabled by the very event that is
     the other saturation branch.
   Two facts the sweep does **not** give and that must be derived at run
   level rather than added to the model: `msg_commit_cast i` for a correct
   `i` implies a commit signature per proposer, and `msg_fallback_sig i`
   implies a fallback signature per proposer. Both are the guards of the one
   honest action that sets the flag (`cast_fast_commit`, `cast_fallback_vote`)
   and the signatures are monotone, so the proof is: find the first index at
   which the flag holds, read the step there off its transition body (the
   `chorus_tr`/`chorus_field_simp` pattern, or the label dispatch of
   `mvba_st_frame_of_not_step`), and carry the signatures forward. Do not
   add an invariant for them — that is a Chorus-family re-solve.
2. *The commit route finalizes* — from an index at which a commit
   certificate exists for every proposer (the dichotomy's left disjunct,
   `commitqc_pos j m ∨ commitqc_neg j`, each an `∃ q` over broadcast commit
   signatures), every correct validator eventually has `local_committed`:
   * `broadcast_commitqc_pos j m q` with the certificate's own `q` is
     enabled until it fires, and `msg_commitqc_pos` is monotone;
   * `commit_assign_pos i j m` is enabled for a correct uncommitted `i` once
     the broadcast certificate exists: its two consistency guards follow
     from `local_committed_pos_backed` / `local_committed_neg_backed`
     together with `commitqc_pos_unique`, `commitqc_pos_neg_excl`,
     `commitqc_pos_mvba_consistent` and `commitqc_pos_mvba_neg_excl` at the
     reachable state — an earlier assignment of `i` is backed by a
     certificate, and certificates agree;
   * `finalize_commit i` is enabled once every proposer is assigned, and
     `local_committed` is what `Terminates` asks for.
   Every invariant named here exists in [Chorus.lean](../Cadence/Chorus.lean) and is available as
   `Chorus.reachable_<name>` (the `(nset := byzNodeSetFin …) hreach` pattern
   of [Chorus/Progress.lean](../Cadence/Chorus/Progress.lean)).

**What stage 3 does not do.** It does not touch the right disjunct of the
dichotomy — the MVBA arm is stage 4, where `AllPropose` and `NoEarlyAbandon`
are derived for the projection and `Mvba.termination` is applied to
`p.run` — and it does not assemble. It needs none of the three premises but
`FJustice`, which is worth stating in its theorems' hypotheses: the fast
route is the part of the claim that rests on fairness alone.

**Traps already known.** Those of §4.2 and §4.3 (the `letI`, the `case`
dispatch, no generated `.init` for theory-seeded fields, docstrings after
`set_option … in`), plus: a `match` on `Chorus.Label` defined in one module
may not reduce in another ([Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)'s `Label.isInput` note), so
export characterisations like `mvbaStepLabel_iff` rather than relying on
`rfl`; the honest quorum's *members* are what `eventually_forall` iterates,
and `ByzNodeSetEnum.mem_members` is the bridge to `member`; and a run-level
"first index at which a monotone flag holds" is `Nat.find` on a decidable
predicate under `open Classical`, with the predecessor state still having the
flag false.

##### 4.5 Stage 3, done: saturation and the commit route, from (F-justice) alone

*Record of 2026-09-28. The file is
[Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean);
its header carries the structure and its docstrings the reasoning at the
point of use. [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean) — the claim and its premises — is
unchanged.*

**What was proven**, at the concrete quorum family (`Fin n`,
`byzNodeSetFin` at every `n = 3f+1`) and the system's MVBA (`Mvba.mvbaSafety
thM`), each theorem taking `FJustice` and no other premise:

* `saturation_fin` — from some index on, every correct validator is
  `Saturated`: it has cast its fast commit vote with a commit signature per
  proposer, or its fallback vote with a fallback signature per proposer.
  That is `progress_dichotomy_of_saturation`'s `hsat`, so
  `eventually_progress_dichotomy` follows: **in every run satisfying
  (F-justice), the progress dichotomy holds at some index.**
* `commit_route_fin` — from an index at which every proposer has a commit
  certificate (the dichotomy's left disjunct, verbatim), every correct
  validator eventually has `local_committed`;
  `terminates_of_commit_route` restates it as the claim's own `Terminates`.

So the fast route of `TerminationClaim` is closed: what stage 4 has to add
is exactly the dichotomy's right disjunct. Every pin is at the standard
trio, with no new cell and one model edit — `vote`'s updates written as
monotone disjunctions (correction 1 below), which changes no reachable
behaviour.

**How.** Three layers, the last two in [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)'s first-link
shape: per-action enabledness and effect lemmas plus five two-state step
facts read off the transition bodies by label dispatch; the two chains over
any labelled Chorus run; and one-line instantiations at the concrete family.
Every temporal step consumes `WeaklyFair` as §4.4 prescribes — a label that
stays enabled fires — and every per-member family collapses through
`LRun.eventually_forall` over `List.ofFn id`.

**Four corrections to §4.4**, each found by writing the proof:

1. *Three network relations had no monotonicity lemma — fixed in the model.*
   `msg_vote_pos_sig`, `msg_vote_neg_sig` and `local_entry_neg` were
   monotone at every reachable state ([ChorusDesign.md](ChorusDesign.md) §3.1's audit
   table), but `vote` *wrote* them as a plain overwrite of the voter's row
   (`msg_vote_pos_sig i J M := is_proposer J && local_entry_pos i J M`);
   only the guard `¬ local_voted i` and the invariants
   `vote_sig_pos_implies_voted` & co. (the row is empty before the vote)
   made that an addition. So no hypothesis-free `.mono` was even true, and
   the chain's positive fallback evidence needed a dedicated argument. The
   model now writes each of the three as a disjunction with its old value
   (`msg_vote_pos_sig i J M := msg_vote_pos_sig i J M || (…)`): the same
   transition at every reachable state (the old value is `false` there, by
   those invariants), and monotone by its syntax, so the (M-update) half of
   the network contract holds per step with no exception. M13 still emits
   no `.mono` for them — it recognises only literal-`true` writes — so the
   three statements it would emit are proven here by the same label
   dispatch (`msg_vote_pos_sig_mono`, `msg_vote_neg_sig_mono`,
   `local_entry_neg_mono`); teaching M13 the `old || e` shape would
   generate them and retire the hand proofs. The model edit re-solved
   `vote`'s cells only; every other statement is unchanged.
2. *`progress_fallback_signing` is not needed.* The case split is excluded
   middle on the positive evidence over the run: if it ever appears it
   persists (monotonicity, item 1) and `fb_sign_pos` fires; if it never does, its absence
   *is* `fb_sign_neg`'s guard against `qv`, verbatim, at every index.
3. *The commit route uses no invariant.* §4.4 planned to discharge
   `commit_assign_*`'s two consistency guards from six invariants
   (`local_committed_*_backed`, `commitqc_pos_unique`, …). They are
   unnecessary: the argument is by contradiction on the validator never
   assigning an entry for that proposer, and then both guards — which
   concern only its own earlier assignments — hold vacuously.
4. *A third first-flip fact.* Besides the two §4.4 names
   (`commit_cast_sigs`, `fallback_sig_sigs`, both derived as planned), the
   fallback guards' `local_path i ≠ fallback` needs `path_fallback_sig`:
   `local_path i` becomes `fallback` only at `cast_fallback_vote i`, which
   casts the fallback vote in the same step. Same technique, same status —
   a run-level theorem, not an invariant.

The sweep contributes `voted_implies_cast` and nothing else.

**One structural choice.** §4.4 said to work at the concrete family from the
start. The chains are instead proven **generic in the quorum instance and the
MVBA**, with the finiteness they consume as explicit hypotheses — a complete
list of validators and an honest supermajority — and the concrete theorems
supply `List.ofFn id` and `honest_supermajority`'s quorum. The reason is the
instance regime rather than taste. At `Fin n`, a generated ghost relation
written with named arguments elaborates with `instDecidableEqFin` where the
generated system has `Classical.propDecidable`, so statements have to go
through the canonical instantiation ([Chorus/Progress.lean](../Cadence/Chorus/Progress.lean)'s `cpv%`, copied as
`cpvm%` at the `Mvba` types). The generic lemmas take the instances as
implicit arguments read off the run's type, so they meet that
instantiation by unification and need no instance search at `byzNodeSetFin`
at all. It also shows something true: the fast route does not depend on
the MVBA instance.

**What to watch in stages 4–5**, in addition to §4.2's and §4.3's notes:

* The right disjunct needs `mvba_propose` enabled for every correct
  validator: its validity guards are the disjunct's evidence (that is what
  [Chorus/Progress.lean](../Cadence/Chorus/Progress.lean)'s header says), its last guard is the contract's
  `propose`, and that is where `ValidBridge`'s soundness clause enters.
  After that comes `Mvba.termination` through the projection (`AllPropose`
  and `NoEarlyAbandon` derived, §4.3), the decision handlers
  (`ValidBridge`'s completeness clause), and the fallback commit round.
* **Finiteness is a hypothesis of the argument, not of the scheduling.**
  Each chain collapses a family of per-validator eventualities into one
  index (`LRun.eventually_forall`) — the step that plays the ranking's role
  — and that is sound only over a finite list: with infinitely many
  validators every individual one eventually acts, but no index need exist
  at which a quorum has. Stage 3 therefore works at the finite family
  (`Fin n`, `ByzNSet n`), and later stages should too; restricting the
  node sorts to finite ones is expected, not a concession. The bounds
  workshop's caveat ([Bounds.md](Bounds.md) §6.2.4) is a separate,
  *non-vacuity* question — whether any run satisfies `FJustice` at all when
  uncountably many stuttering labels are enabled — and does not arise for
  the finite quorum sets used here; it is answered by exhibiting a run
  ([TODO.md](TODO.md) § Liveness), not by weakening the assumption. The
  chains are in any case robust to fairness of state-changing steps
  (`Cadence.EnabledMove`): every label they fire is fired at a state where
  its effect is absent — the contradiction hypothesis of each link — so each
  such step is a move (by inspection, not yet checked). *Checked since R3*:
  `FJustice` is stated over state-changing steps, and every link pays that
  side condition in Lean.

##### 4.6 Stage 4, the kick-off record: the MVBA arm

*Written 2026-09-29 at the hand-over after stage 3 (§4.5), so the next
session does not re-derive the design. Nothing below is done. Two findings
come first, because the stage cannot be proven until both are settled.*

**Update, 2026-09-29: the pre-stage-4 revision.** Before stage 4 started,
one PR bundled every change that touches the Chorus family, so that stage 4
starts on the final shapes and the family re-solved once. What it changed
for this stage:

* **Finding 1 is fixed as recommended.** `chorusTheory` in
  [System.lean](../Cadence/System.lean) sets `mval_neg v j := v j = none
  ∧ is_proposer j`, and `chorusTheory_assumptions` is re-proved. A
  non-proposer now has no entry, so the vector of step 2 below (`none` at
  non-proposers) is `Certified` when its proposer entries are.
* **Finding 2 is resolved at the premise, not in the model.** The model fix
  (`let mvba_next :| mvba.propose mvba_st i v mvba_next` in the body) was
  tried and does not build. [Chorus.lean](../Cadence/Chorus.lean) emits the executable extraction
  the trace monitor runs (`veil.gen.executableActions`), and a pick is
  extractable only over a finitely enumerable type, which the abstract MVBA
  state `mstate` is not. The alternative this record names is the right one
  and is semantically the same: a value picked in the body is an existential
  in the transition relation, so weak fairness of `mvba_propose i v` over the
  family `∃ mvba_next` is exactly the fairness of the picked form, TLA+'s
  `WF(∃ n. Propose(i, v, n))`. **Stage 4's first task** is to state it:
  * a generic `WeaklyFairFamily r (S : lbl → Prop)` in
    [Fairness.lean](../Cadence/Fairness.lean): if some label in `S` is
    enabled at every index from `N` on, some label in `S` fires from `N` on;
  * in `Chorus.FJustice`, `mvba_propose` is taken out of the per-label
    clause and covered per `(i, v)` by `WeaklyFairFamily r (fun l => ∃ n,
    l = .mvba_propose i v n)`.

  The criterion below (identifying parameters in the label, results and
  witnesses in the body) still says which labels need this. The label keeps
  its result parameter, and the fairness premise quantifies it away. No
  model change, no re-solve.
* **The contracts changed shape, not content, where stage 4 touches them.**
  * `Mvba.termination` takes `[Fintype node]` in place of a
    `ByzNodeSetEnum` argument. Prerequisite 1 below shrinks: no
    `ByzNodeSetEnum` instance for `byzNodeSetFin` is needed, since `Fin n`
    is a `Fintype`. The `ByzNodeSetHonestQuorum` instance from
    `honest_supermajority` is still needed.
  * `MVBASafety.propose_valid` is gone: the caller's validity obligation is
    an antecedent of `MVBATemporal.termination` (the rely form,
    [CompositionContracts.md](CompositionContracts.md) §7 item 1). At
    the composed instance nothing changes for step 2: `mvba_propose`'s last
    guard is the contract's `propose`, which at `Mvba.mvbaSafety` is
    `Mvba.propose` and still requires `valid e`, so `ValidBridge`'s
    soundness clause plays the same role.
  * `TimedRun` carries its own clock, and `MVBATemporal` is instantiated at
    `Mvba.mvbaSafety` (`Mvba.mvbaTemporal`, full `Mvba.mvbaFull`). The MVBA
    the composed system runs is a full `MVBA`. This does not change
    stage 4, which consumes the untimed `Mvba.termination`. It is what the
    later Chorus bounds work (`ℓ = 5Δ + ℓ_MVBA`) will consume.
* **Unchanged**: [Chorus.lean](../Cadence/Chorus.lean), [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)'s label classes, the
  monitor, and stage 3's theorems. The generic stage-3 lemmas keep their
  `nodes`/`hnodes` arguments: they are internal, and the headline theorems
  are stated at `Fin n`, where finiteness is visible already. Switching them
  to `[Fintype node]` is optional tidying.

**Where it goes.** [Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean), a new section after
stage 3's, in the same three layers: step facts, generic run-level chains,
concrete-family theorems. Split into `Termination/` files by arm if it
outgrows [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean).

**Finding 1 — at [System.lean](../Cadence/System.lean)'s instantiation, `mvba_propose` never fires
unless every validator is a proposer.** `chorusTheory` sets `mval_pos v j m
:= v j = some m` and `mval_neg v j := v j = none` for *every* node `j`.
`mvba_propose`'s first two validity guards (and `Certified`, which is those
guards verbatim) require `is_proposer J` of every `J` with an entry, and at
a non-proposer `j` the vector `v` has an entry either way. So if any
validator is not a proposer, no vector is `Certified`, `mvba_propose` is
disabled in every state, the MVBA never receives an input, and every run in
which the fast route does not close fails to terminate. `TerminationClaim`
is then *false* at `chorusTheory`, and `ValidBridge`'s soundness clause is
vacuous. Checked in scratch: a twelve-line lemma, `¬ Certified st v` for
every `st` and `v` given one non-proposer. Safety is unaffected, since the
guard only removes behaviours. This is exactly the seam [TODO.md](TODO.md)
§ Liveness's composition-level non-vacuity item warned could hide behind a
green build. **Recommended fix, at the instantiation:** `mval_neg v j :=
v j = none ∧ is_proposer j`, so that a non-proposer has no entry. The two
projection assumptions still hold and `chorusTheory_assumptions` needs only
a re-proof; [Chorus.lean](../Cadence/Chorus.lean) is untouched. The alternative — restricting the
guards to proposers in [Chorus.lean](../Cadence/Chorus.lean) — has the same effect at a family
re-solve's cost and moves the fix away from where the mismatch is.

**Finding 2 — `mvba_propose`'s label carries the MVBA's successor state, so
weak fairness per label cannot force a proposal.** The action is
`mvba_propose (i) (v) (mvba_next)`, and its last guard is `mvba.propose
mvba_st i v mvba_next`. A given label is therefore enabled only while
`mvba_st` stays at the one state whose propose-successor is `mvba_next`.
The MVBA keeps stepping (other validators' proposals, views, timers —
`MvbaAdmissible` even requires infinitely many steps), so no single label
need stay enabled, and a scheduler that satisfies `FJustice` can keep `i`
from ever proposing. Then `AllPropose` cannot be derived, and neither can
termination. (Argued, not machine-checked; the obstacle is structural.)
**Recommended fix, in the model:** choose the successor inside the action
— `let n :| mvba.propose mvba_st i v n; mvba_st := n` (Veil's
`pickSuchThat`; `pick` plus a `require` is the same) — so that the label is
`mvba_propose i v`, the paper's `propose(B_i)`, and it is enabled whenever
*some* successor exists. It is faithful: `mvba_next` is not a choice the
validator makes but the MVBA's state after the input, which the contract
determines (at the `Mvba` instance, uniquely). In the transition relation a
picked value is an existential, so for safety nothing changes — it is a
free parameter of the relation, only no longer of the label. That is one
[Chorus.lean](../Cadence/Chorus.lean) edit whose statement change reaches only `mvba_propose`'s
cells; [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)'s `MvbaStepLabel`, `mvbaStepLabel_iff`,
`mvba_propose_tr` and `mvbaComponent.step` follow the new arity (a change to
the statement file, to be recorded here), and so does the monitor's label
decoder ([Monitor/ChorusMonitor.lean](../Cadence/Monitor/ChorusMonitor.lean) and the generated
[Monitor/ChorusMonitorGen.lean](../Cadence/Monitor/ChorusMonitorGen.lean) both decode `mvba_propose` with three
arguments). `mvba_step` stays as it is — it is the oracle step, outside
(F-justice), and its labels are the projection's business. Strong fairness
of the old label would not help: it still needs the one successor-specific
label enabled infinitely often. The alternative is to state `FJustice` for
`mvba_propose` over the family `∃ mvba_next`, TLA+'s `WF(∃ n. Propose(i, v,
n))`; it keeps the model but makes one premise different in kind from all
the others.

**The criterion behind Finding 2**, for every label this leg relies on.
Whether a variable is an action parameter or picked in the body makes no
difference to safety — an invariant is proven over every transition either
way — but a label is the unit weak fairness speaks about, so its parameters
decide *what* is fair. Parameters that identify **who acts or on what**
(the validator `i`, the proposer `j`, the proposed value `v`) belong in the
label: fairness per process is the standard assumption, and the coarser
`WF(∃ i. A i)` only promises that *some* validator acts, which starves a
repeated action at one of them. Parameters that are **witnesses or results**
(a successor state, the quorum `q` that witnesses a guard) belong in the
body, because a label containing them tracks state that other actions
change. The test: a label's enabledness should be stable under steps
irrelevant to its action. `mvba_propose i v next` fails it;
`on_mvba_decide_pos i j m v` passes (`v` is fixed once decided). The
witness-parameterised assembly labels (`broadcast_commitqc_* … q`,
`aggregate_fastqc_* … q`, the MVBA's `form_* … q`) are also the ones that
stay enabled as stutters — the bounds workshop's caveat (§4.5) — and
picking `q` in the body would settle that in the model; it is not needed for
stage 4, whose uses of them are sound as they stand, but it is the uniform
fix if the caveat is taken up. *R3 took the caveat up without a model
change*: fairness is stated over state-changing steps, so the stutters owe
nothing ([Bounds.md](Bounds.md) §6.2.4).

**What stage 4 proves**, given both fixes, at the concrete family and
`chorusTheory`, from `FJustice`, `MvbaAdmissible` and `ValidBridge`: from
an index at which the dichotomy's right disjunct holds, every correct
validator eventually has `local_committed`. The chain:

1. *Prerequisites.* `ByzNodeSetEnum` and `ByzNodeSetHonestQuorum` instances
   for `byzNodeSetFin` — they exist only for `byzNodeSetFinGen`
   ([ByzQuorum.lean](../Cadence/ByzQuorum.lean)); members are `s.val`,
   and `honest_supermajority` gives the quorum. `Mvba.termination` also
   takes a `ViewOrderEnum`, which becomes a hypothesis of the theorem.
   The phase reaches `post_mvba_arm` and stays there: stage 3's
   `eventually_atArm` plus the `advance_to_mvba_arm` link.
2. *Every correct validator proposes.* Build its vector from the
   dichotomy's evidence at index `N`: `v j := some m` where a positive
   certificate for `(j, m)` exists (a `Classical.choose`), `none`
   otherwise — at non-proposers too, which Finding 1's fix makes an
   absence rather than an entry. The evidence is monotone (the vote
   relations since #31, fallback signatures, `fbcert`,
   `equiv_evidence`), so `v` stays `Certified`; `ValidBridge`'s soundness
   clause makes it `Valid` once, and `Valid` is state-independent. The
   trigger: `fbcert` directly, or — in the case-(a) branch — the
   validator's own complete fast meta-block, which needs an
   `aggregate_fastqc_*` link per proposer from the vote quorums that
   `fastqc_complete_implies_mvba_evidence` puts on the network. The MVBA's
   `propose` guards (`∀ E, ¬ input i E`, `¬ abandoned i`, `valid e`) stay
   true until `i` proposes: no other label writes `input` or `abandoned`.
3. *Consume `Mvba.termination`.* `MvbaAdmissible` supplies the projection
   `p` and its three scheduling premises. `AllPropose p.run` is step 2
   carried through `Projection.proj_eq_run_cover`. `NoEarlyAbandon p.run`
   holds vacuously: `abandoned` starts false (`init_abandoned`) and no step
   of the composed run sets it (`abandoned_step_frame` for `mvba_step`,
   the `Mvba` model's `propose` frame for `mvba_propose`). The conclusion
   comes back through `Projection.eventually_iff`: every correct validator
   has `mvba.decided (r.at' n).mvba_st i v` at some `n`, and decisions
   persist (`decided_mono`), so by agreement there is one decided `v`.
4. *Transport the decision.* `on_mvba_decide_pos/neg i j m v` per proposer,
   whose bridge `require` is `ValidBridge`'s completeness clause — its guards
   are monotone once `v` is decided — then `mvba_terminate i v` sets
   `mvba_complete`.
5. *The fallback commit round.* Per decided-positive `(j, m)`,
   `redisseminate_chunk i j m` delivers `i`'s chunk (its guards come from
   `mvba_decided_pos_proposer_signed` and
   `mvba_decided_pos_chunks_decodable` at the reachable state), so
   `cast_fb_commit i` fires for every correct `i`; the honest quorum's
   `msg_fbcommit_sig` at one index is `fbcommitqc`. Then `commit_assign_*`
   through its second disjunct (`fbcommitqc ∧ mvba_decided_*`) and
   `finalize_commit`. Generalise stage 3's
   `eventually_committed_of_commitqcs` to "every proposer has an assignable
   certificate — broadcast commit certificate, or `fbcommitqc` with the
   decision" rather than duplicating it; its no-invariant argument
   (§4.5, correction 3) carries over unchanged.

**What stage 4 does not do.** It does not assemble `TerminationClaim` —
that is stage 5, which case-splits on `eventually_progress_dichotomy`,
adds the [Cadence.lean](../Cadence.lean) row and pin, and retires (A-mvba) from
[Architecture.md](Architecture.md) §4 with `MvbaAdmissible` (including `Scheduled`) and
`ValidBridge` named there.

**Traps already known**, beyond §4.2–§4.5's: every ghost relation stated at
`Fin n` goes through `cpvm%`; `Mvba.mvbaSafety` needs `(nset := …)` by
name; `Mvba.Label.isInput` does not reduce outside its module — use
`Label.isInput_cases`; a label with a state-valued parameter is Finding 2
again, so check each new label's parameters before relying on its
fairness (`on_mvba_decide_*` and `mvba_terminate` carry the decided `v`,
which is fixed once decided, and are fine).

**Stage 4, done (2026-09-29): the record and the reassessment.** The proof
is in [Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean), in the same
three layers as stage 3 and in the same file (it did not outgrow it); its
header carries the chain and its docstrings the reasoning at the point of
use. At the concrete family, at `Cadence.chorusTheory`, from `FJustice`,
`MvbaAdmissible` and `ValidBridge`:

* `mvba_arm_fin` — from an index at which the progress dichotomy's right
  disjunct holds (verbatim, as `eventually_progress_dichotomy` states it),
  every correct validator eventually has `local_committed`;
  `terminates_of_mvba_arm` restates it as the claim's `Terminates`. The one
  further hypothesis is the view order's enumeration (`ViewOrderEnum`),
  which `Mvba.termination` takes; the validators' finiteness is `Fin n`'s,
  and in the generic core (`eventually_committed_of_mvba_arm`) it is
  `[Fintype node]`.

Every pin is at the standard trio. No model change, no new invariant, no
new cell: `#veil_status Chorus` is unchanged.

*Why Finding 2 is resolved at the premise and not in the model.* Picking
the MVBA's successor state inside `mvba_propose` does not build: the model
also generates the executable form of every action that the trace monitor
runs, and a pick can be made executable only over a type whose values can
be enumerated, which the abstract MVBA state is not. The premise says the
same thing as the pick would. A value picked in an action's body is an
existential in its transition relation, so "`i` proposing `v` is weakly
fair, whichever successor state results" is exactly the fairness of the
picked action — TLA+'s `WF(∃ n. Propose(i, v, n))`. That is
`Cadence.WeaklyFairFamily` ([Fairness.lean](../Cadence/Fairness.lean)), and `FJustice` now covers
`mvba_propose` per `(i, v)` with it, and every other justice label per
label as before (`ProposeLabel` in [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean) names the one
exception). For a one-label family it is plain weak fairness
(`weaklyFairFamily_eq_iff`).

**What the chain needed beyond this section's plan.** Six things, none of
them a new assumption:

1. *Stage 3 adjusted, statements unchanged.* The per-label clause of
   `FJustice` now excludes `ProposeLabel`, so stage 3's generic chains take
   that clause (one more `fun h => h` at each firing) and the concrete
   theorems pass `hfj.1`. `enabled_commit_assign_*` take the full
   certificate guard, and `eventually_committed_of_commitqcs` is now a
   corollary of `eventually_committed_of_assignable` — the generalisation
   step 5 asked for, with the no-invariant argument unchanged.
2. *`mvba_decided_pos_proposer_signed` does not exist.* Step 5 named it
   for `redisseminate_chunk`'s signature guard. It is derived instead at the
   reachable state (`proposer_signed_of_decided_pos`): a decided root is
   backed by a FastQC or a FallbackQC (`mvba_decided_pos_backed`), each has
   an honest member, and that member's signature pins the proposer's
   (`vote_pos_from_local` with `local_entry_pos_signed`, resp.
   `fb_pos_sig_proposer_signed`).
3. *The DA wait is anti-monotone.* `cast_fb_commit`'s guard ("a FastQC or
   my chunk under every decided-positive root", since F12; "my chunk" before
   it) could in principle be disabled by a
   new decision record. It is not: once every proposer's entry is recorded,
   `mvba_decided_pos_unique` and `mvba_decided_pos_neg_excl` rule out any
   other record, so the guard is stable from then on.
4. *One decision suffices, and agreement is not used.* `mvba_complete` is a
   single flag, so it is enough to transport one correct validator's
   decision. Step 3's appeal to agreement drops out, and the records match
   that decision.
5. *The MVBA's state needs one more step fact.* That nobody is ever
   abandoned (`not_abandoned`, which is `NoEarlyAbandon`'s content) needs
   `mvba_step`'s guard with its "not an input" half, which
   [Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)'s `mvba_step_tr` drops; `mvba_step_internal`
   keeps it. The case-(a) trigger needs no dedicated lemma: a complete fast
   meta-block spreads to every correct validator through
   `local_fastqc_*_backed` and `aggregate_fastqc_*`
   (`eventually_complete_fast_metablock`).
6. *One vector for everybody.* The certified vector is built once, from the
   dichotomy's evidence at the start index (`certifiedVector`), so the
   bridge's soundness clause is used once. The generic core states how the
   theory reads a vector entrywise as two hypotheses; `Cadence.chorusTheory`
   discharges them by `decide`. [Termination.lean](../Cadence/Chorus/Termination.lean) now imports
   [System.lean](../Cadence/System.lean) for that definition.

The chains stay robust to fairness of state-changing steps, as §4.5 noted
for stage 3: the proposal family is fired only while the validator has no
input, the handlers only while their record is absent, and
`mvba_terminate` only while `mvba_complete` is unset.

**What stage 5 needs.** The assembly is short now: `TerminationClaim` at
`Fin n`, `byzNodeSetFin` and `Cadence.chorusTheory` is
`eventually_progress_dichotomy` followed by `terminates_of_commit_route` on
the left disjunct and `terminates_of_mvba_arm` on the right, with
`ViewOrderEnum` as a hypothesis of the theorem — like `Mvba.termination`'s,
it belongs to the proof, not to the claim. Then the
[Cadence.lean](../Cadence.lean) row and pin, and the retirement of (A-mvba) in
[Architecture.md](Architecture.md) §4 and Liveness.md §2 here, naming `MvbaAdmissible` (with
`Scheduled`) and `ValidBridge` in its place. The satisfiability of the
premises — now including the proposal family — is the non-vacuity question
of [TODO.md](TODO.md) § Liveness, unchanged by this stage.

##### 4.7 Stage 5, done: the claim, and what remains

*Record of 2026-09-29, the leg's closing record.*

**What the claim now says.** `Chorus.termination`
([Cadence/Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)) proves
[Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean)'s `TerminationClaim`: at every `n = 3f+1` with
at most `f` Byzantine validators (`Fin n`, `byzNodeSetFin`), at the
configuration the composed system runs (`Cadence.chorusTheory`, the MVBA
constraint filled by `Mvba.mvbaSafety` at `Cadence.mvbaTheory`), every run
satisfying the three premises terminates, i.e. every correct validator
finalizes the slot. `Cadence.mvbaTheory` fixes one thing, that a
meta-block's entry vector is its own entries with the certificates dropped
(`ent := MetaBlock.entries`); termination needs it so that a validator can
propose a certified meta-block. Its validity predicate and leader schedule
stay arbitrary. Like `Cadence.chorusTheory` it is the configuration, not a
premise. The
proof is what "What stage 5 needs" (end of §4.6) said it would be:
`eventually_progress_dichotomy`, then `terminates_of_commit_route` on the
left disjunct and `terminates_of_mvba_arm` on the right. It is pinned at the
standard trio there and in [Cadence.lean](../Cadence.lean). No model change,
no new invariant, no new cell: `#veil_status Chorus` is unchanged. Stage 4
built unchanged on the halting MVBA model of PR #42, as expected: it
relies only on `Mvba.propose`'s guards, the abandoned frames and
`Mvba.termination`'s statement.

**The premises.** Each is a named `Prop`, and Liveness.md §2 has them in short:

* `FJustice` — correct validators' actions are weakly fair over steps
  that change the state; the MVBA proposal is fair as one family per
  validator and value;
* `MvbaAdmissible` — the run's MVBA steps have a labelling, with infinitely
  many of them (`Component.Scheduled`), that satisfies `Mvba.termination`'s
  three scheduling premises;
* `ValidBridge` — the MVBA's `Valid` agrees with Chorus's certificates, in
  both directions: the cryptographic seam, not a fairness assumption.

The theorem's other hypotheses fix the setting: the quorum family's
parameters (`n = 3f+1`, the Byzantine predicate and its bound) and
`ViewOrderEnum`, which, as in `Mvba.termination`, belongs to the proof and
not to the claim. The quorum counting facts are the family's own instance
(`Cadence.byzNodeSetFin_counting`), so they are not a hypothesis. (A-mvba)
is retired from [Architecture.md](Architecture.md) §4 item 2 and Liveness.md §2 above.

**One surface decision.** The concrete section's `[cnt]` binder is omitted
from `Chorus.termination` (`omit cnt in`, with the instance passed to
`TerminationClaim` by name), so the counting class does not appear as a
hypothesis. The stage-3 and stage-4 theorems keep the binder; they are
internal steps, and the family's instance discharges it at every use.

**What remains.**

* ~~**Non-vacuity.** The premises have to be shown jointly satisfiable.~~
  **Done** (R10, 2026-10-01): `Chorus.termination_premises_satisfiable`
  ([Cadence/Chorus/Witness.lean](../Cadence/Chorus/Witness.lean)), with
  the timed claims' premises in the same file and the ledger in
  [Bounds.md](Bounds.md) §6.4.5. One model and one run, in the pattern of
  the MVBA leg's [Cadence/Mvba/Witness.lean](../Cadence/Mvba/Witness.lean):
  everyone finalizes on the fast path and then abandons, so the MVBA stays
  quiet and the proposal family holds with its antecedent false.
  `ValidBridge` at `chorusTheory` holds with `valid := (· = v⋆)`, the one
  vector a certificate check can pass in the run.
* ~~**The timed claim.** `SlotConsensusTemporal.termination`, finalization
  within `5Δ + ℓ_MVBA`, still has no instance.~~ **Proven** (R18,
  2026-10-02) as `Chorus.timed_termination`
  ([Cadence/Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean)):
  `TimedTerminationClaim` at `5Δ + ℓ_MVBA + 9δ`, by the route the MVBA leg
  took ([Bounds.md](Bounds.md) §6.4.3), consuming the MVBA contract's
  `T.termination` for the `ℓ_MVBA` part; `Chorus.timed_termination_tight`
  gives `4Δ + ℓ_MVBA + 8δ` from the same premises (F4).
* ~~**The contract instance.**~~ **Proven** (R20, 2026-10-02):
  `Chorus.chorusTemporal` and `Chorus.chorusWithTotality`
  ([Cadence/Chorus/Temporal.lean](../Cadence/Chorus/Temporal.lean)), joined
  into the full `SlotConsensus` as `Chorus.slotConsensusFull`. The
  contract's Termination is `Chorus.termination` over runs whose labelling
  meets the five premises above less the caller's two, which are the
  field's own antecedents; its timed fields are the two timed claims; its
  `Admissible` names every premise once; and a run in which every proposer
  stays silent shows that it can hold ([Bounds.md](Bounds.md) §6.4.5).
* ~~**Prose alignment.** The model files that still name (A-mvba) in their
  comments.~~ Done by the participation edit below.

**Revised by the participation edit** (2026-09-29, [Bounds.md](Bounds.md)
§6.4.6 S1). Chorus now models the module's participation interface:
`participate` and `abandon` are input actions over per-validator
`participating`/`abandoned` state, `abandon` forwards to the MVBA's
`abandon()`, and every sending rule is gated on active participation.
The claim changed with it, in three ways an auditor should know.

* **Two premises more, and they are the caller's.** `TerminationClaim` now
  also takes `AllParticipate` (every correct validator eventually invokes
  `participate()`) and `NoAbandonBeforeFinalizing` (none invokes
  `abandon()` before it has finalized). They are the antecedents of
  `SlotConsensusTemporal.termination`, so the untimed claim is now the
  contract's Termination over the contract's own interface. Without the
  second the claim would be false, since finalizing is itself a gated rule.
* **The inputs carry no fairness.** `FJustice` excludes the three inputs
  (`Chorus.InputLabel`, pinned against the contract's `step` split by
  `not_justice_of_input`). `propose`, the proposer's root commitment, was
  weakly fair before and is an input now. No link of the proof fired it.
* **The proof splits on an early finalization**, as the paper's does. If a
  correct validator finalizes, the others finalize from its certificates
  (`eventually_committed_of_finalized`, the untimed totality). The MVBA's
  premises are not needed there. If none ever does, none ever abandons, every
  correct validator is active from some index on
  (`activeFrom_of_never_finalized`), and the old dichotomy argument runs
  unchanged except that each honest link takes that gate as a hypothesis.
  The split is needed because a validator that finalizes on the fast path
  and then abandons also abandons the MVBA. `MvbaAdmissible` keeps its
  shape; the MVBA's abandonment premise is derived on the second branch
  (`abandoned_of_mvba_abandoned`: the MVBA's `abandoned` row moves only
  with Chorus's `abandon`).

No invariant was added. Two run-level first-flip facts replace one:
`committed_pos_assignable` / `committed_neg_assignable` recover, for a
committed entry, the certificate its `commit_assign_*` guard saw. The
invariant `local_committed_*_backed` keeps only the MVBA record, not the
fallback commit certificate beside it.

## Paper alignment before the single target

Until 2026-10-01 the development had **no single paper target**. Chorus,
the Conductor, the glue and the receipt layer were built against arXiv
`2607.02275v2`. The MVBA was built against the paper repository's internal
supplement, first at `026dc8b` and then at `eb1bb51`. The MVBA contract
took the post-v2 Agreement over entries (paper commit `d598c5a`). The
commit up to which this held is tagged **`paper-target/arxiv-v2`**, and
`docs/PaperAlignment.md` at that tag holds the full record summarised
here. Session R13 froze the single target `48cac9a` (main body plus
supplement) and re-ran the review against it
([PaperAlignment.md](PaperAlignment.md)).

**The revisions involved.** The paper repository has no release tags. The
mapping below was established by comparing every `.tex` file of each arXiv
e-print with the repository:

| arXiv | date | paper-repo commit | role here |
|---|---|---|---|
| v1 | 2026-07-02 | `89322be` | the receipt rules with the liveness bug; refuted by the model checker (tag `v1-receipt-refutation`) |
| v2 | 2026-07-07 | `3efdbfe` | the target of Chorus, the Conductor, the glue and the receipt layer until R13 |
| — | 2026-09-03 | `026dc8b` | the supplement's MVBA as first modelled |
| — | 2026-09-28 | `eb1bb51` | the supplement at the MVBA's pin until R13 |
| — | 2026-10-02 | `48cac9a` | the single target from R13 on |

Citations were resolved against the public e-print: `curl -sL
https://arxiv.org/e-print/2607.02275v2 | tar -xz`, a flat layout
(`alg_da.tex` where the repository has `src/alg_da.tex`). From R13 on,
anchors are resolved in the paper repository at the target commit.

**The 2026-09-03 audit** found the verified surface (the algorithm floats,
Part 2 and one Part 1 anchor) byte-identical to v2 at `026dc8b`, apart from
`\input` path prefixes. It also recorded seven divergences between the
supplement's implementation notes and the published algorithms. In every
case the models followed the published algorithm. The seven: the
witness-chunk `EquivCert`; a revised practical Conductor; the MVBA's
availability precondition and `Δ_sync`; ChunkSync replacing the signer's
re-encode-and-send; the finalize wait moved outside consensus; domain
separation; MVBA entry gated on the slot's ticket. Paper-side defects
recorded then: three truncated `\mainref` citations (resolved by
`eb1bb51`), the supplement's internal `EquivCert` contradiction (still
present at `48cac9a`, finding P3), the stale
`supplementary-internal-bkp.tex` (still present), and the capped-backoff
issue in the MVBA timeout (resolved at `eb1bb51` by the fixed `T`).

**The 2026-09-29 re-check against `eb1bb51`** (the change list is
below, "The supplement at `eb1bb51`, reviewed against the pin `026dc8b`") moved the MVBA's pin, left its safety untouched,
and led to the timed premise stating the supplement's network (C16). It
also found that six of the eleven verified-surface files had moved since v2
(68 insertions, 38 deletions over 18 commits). These were the domain tags,
positional fragments, the per-slot dispatch, `mod:mvba`'s Agreement, and
prose. That drift left the development without one target, which R13
resolved.

**The decision handoff.** Until R13 the model kept v2's fallback commit
round. Of the supplement's ending it took only the handoff of the MVBA's
certificate (`accept_mvba_commitqc`, R8), on the grounds that v2 was the
verified paper. At the target the supplement's route is part of the
specified protocol ([PaperAlignment.md](PaperAlignment.md) §5.7).

**The README's paper section before R13** named v2 as what the
development verifies, kept the revision table above, and explained the v1
receipt bug in a paragraph. That bug was found by a parallel verification
effort, reproduced here, and fixed in v2.

### The realignment to `48cac9a` (R14–R17), and its designs

Section 8 of [PaperAlignment.md](PaperAlignment.md) until R33: the session
records of the realignment, and the R15 and R16 designs as they were
written before each model edit. Section references without a file name
are to PaperAlignment.md. Its §8 now says, in the present tense, what the
realignment built.

#### The sessions

Sessions in order. Each is one PR off `master`, and the next starts after
the last one merges. "Cold" means the Veil family re-solves from scratch,
because VC statements move. "Warm" means only kernel replay. One
Interfaces.lean edit moves every Chorus VC, since class fields are
hypotheses of every cell, so the plan makes exactly **one** contract edit,
and puts the Chorus model changes in the same session.

**R14 · Statements that need no Veil re-solve. Done** (2026-10-02; the
build is [History.md](History.md)'s R14 row).
* `Primitives.ErasureCoding` (M3). Before, `Decode : List fragment →
  Option cipher`, and `decode_sound` held for any list of `f+1` encoded
  fragments, duplicates included, at every `f`. After, the class takes the
  system's `n` and `f`, `Encode : cipher → Fin n → fragment`, `Decode`
  takes a `Finset (Fin n × fragment)`, and `decode_sound` requires `f+1`
  distinct indices, each fragment at its own index, as Appendix C.1
  (`appendix:crypto`) states the interface. No Chorus VC statement moved:
  a warm Chorus proof file replayed with no new cache entry.
* F14 (§5.6): `Owed (.redisseminate_chunk k i j m)` is
  `msg_fb_pos_sig k j m`. `Chorus.termination`, the timeline milestones,
  `Chorus.totality` and the three witness theorems re-checked in plain
  Lean at `[propext, Classical.choice, Quot.sound]`.
* The (d) items: the per-slot dispatch sentence in the
  [Cadence.lean](../Cadence/Cadence.lean) header (M5); domain separation in
  [ChorusDesign.md](ChorusDesign.md) §3.1 and in
  [Architecture.md](Architecture.md) §4 item 3 (M1, S15); the
  positional-fragment remark beside ChorusDesign's network table (M2);
  `ρ_mvba` in the MVBA schedule's prose (S4); and, from
  [TODO.md](TODO.md), ChunkSync and `Δ_sync` beside the (F-justice)
  justification of re-dissemination (`Chorus.Owed`).
* Families: none cold. The pins are unchanged.
* F13, F14, S4: F14 closed; F13 and S4 untouched.

*Plan changes made in R14:*
* **Citations to the rendered PDF** (Lars, 2026-10-02), added to R14. Every
  citation reads as the target's rendered PDF shows it, with the label in
  parentheses, and names the supplement where it is the supplement. The
  label map [paper-labels.tsv](paper-labels.tsv) is generated from the
  target by `scripts/paper-labels.sh`, and `scripts/paper-cites.sh` checks
  every citation against it (§1). Citations by `.tex` path or by paragraph
  title are replaced by the enclosing numbered unit; an unlabelled unit
  (several of the supplement's Part II subsections) is cited by its
  labelled parent, with its title as a description. The model headers
  say that citations name the target's references.
* **Two files keep the bare-label form until R15**:
  [Interfaces.lean](../Cadence/Interfaces.lean) and
  [System.lean](../Cadence/System.lean), which R14 does not touch.
  `scripts/paper-cites.sh` checks their labels against the map but not
  their form. R15 rewrites their citations in the same edit and removes
  the exemption.
* **The citation check runs in the docs build.** `scripts/docs.sh` runs
  `scripts/paper-cites.sh` beside the link resolution, so the docs workflow
  fails on a cited label missing from the map as it fails on a dead link.
  No workflow file or limit changed.
* **R17's anchor re-check** is §1's check: regenerate the map at the new
  pin and run the citation check.

**R15 · The meta-block representation, and the contract. Done**
(2026-10-02; the builds are [History.md](History.md)'s R15 row). The one
Interfaces.lean edit, together with every model change it needs; the design
is §8.1.
* **Contract (c).** `MVBASafety` has the `entries` projection; Agreement
  and Integrity are stated over it in the supplement's words (M9, S6,
  §5.4); the commit certificate is over entries; the four certificate-level
  fields of §5.7 (`certified_unique`, `certified_decided`, `certified_valid`,
  `certified_available` over the observable `availReady`) are proven by
  `Mvba.mvbaSafety` and withheld from the solver with the three handoff
  facts. The class takes the system's quorum family as a parameter, which
  the availability field counts with.
* **Mvba (b).** `value` is the representation and `evec` the entry vector,
  joined by `ent`; votes, certificates and locks are over `evec`; `Recover`
  is a choice among valid representations (`leader_repropose`,
  `form_own_commitqc`, `decide`); `avail_ready` is indexed by the
  representation (S7). Every property keeps its name; a fourth trace
  shows two correct validators deciding different representations of one
  entry vector.
* **Chorus (b).** The decision handlers check the certificate the
  validator's own representation names, and `cast_fb_commit i v` waits
  exactly under the `FallbackQC` entries of its own decision `v`. F13 is
  closed with no residual (§5.5, [Bounds.md](Bounds.md) §6.4.2).
* **System.lean** re-instantiates at `MetaBlock node merkle_root` and
  defines the MVBA configuration `Cadence.mvbaTheory` beside
  `Cadence.chorusTheory`.
* **Citations** of Interfaces.lean and System.lean are in the rendered form,
  and `scripts/paper-cites.sh` has no exemption left.
* Families cold: Mvba (`Mvba/NoLock.lean` re-run, its witness the same 25
  transitions, re-pinned with `(sequential := true)` because labels print
  the representation as `x`) and Chorus. FallbackReceipt, Cadence and
  Conductor warm.
* Pins: unchanged, as §8.1 (f) wrote down before the build — Mvba
  `29 · 51 + 28 = 1507`, Chorus `47 · 102 + 46 = 4840`, FallbackReceipt
  `220`.
* Re-established at `[propext, Classical.choice, Quot.sound]`:
  `Mvba.mvbaSafety`, `Mvba.mvba_of_temporal`, `Mvba.termination`,
  `Mvba.bounded_termination`, `Mvba.mvbaTemporal`, `Mvba.mvbaFull` and both
  Mvba witnesses (`Mvba.Witness.ell = 24`); `Chorus.slotConsensusSafety`,
  `Chorus.termination`, the timeline, `Chorus.totality`, the three Chorus
  witnesses, System.lean's end theorem and every pin of
  [Cadence.lean](../Cadence.lean). The monitor suites pass.
* F13: closed. F14: closed in R14. S4: re-based on the new model; its
  fallback commit round rows owe `cast_fb_commit` under the validator's own
  `B′`.

*Plan changes made in R15:*
* **The pins do not move.** The plan expected new counts; the design keeps
  every action and property, restating them over the split, and the
  availability fact rides on the restated `honest_commit_accepted`. Both
  families still re-solved cold, since every statement changed.
* **The contract takes the quorum family as a parameter** (§8.1 (b)), for
  `certified_available`.
* **A redelivered decision** (P11, new): the target does not say what
  Chorus's decision handler does with a second decision output that has
  the same entries and another representation. The model's rule is safe
  under every reading (§8.1 (d)), and `Owed (.cast_fb_commit i v)` owes
  the vote only to a validator with one representation.
* **No per-validator Chorus record.** The plan said the handlers "record
  the validator's own representation"; `cast_fb_commit` reads it directly
  from the positive observable `mvba.decided mvba_st i v` instead (§8.1
  (d)).
* **`Chorus.termination` is stated at the system's MVBA configuration**
  `Cadence.mvbaTheory`, where `ent := MetaBlock.entries`; before, it held
  for every MVBA theory. A validator must be able to propose a certified
  meta-block, and under an arbitrary `ent` no representation need have the
  certified entries. It fixes configuration, as `Cadence.chorusTheory`
  does; it adds no premise. System.lean's safety theorem stays generic.
* **One scoped exception of the monotone-network audit is gone.**
  `cast_fb_commit` no longer reads the shared decision records under a
  universal, so [ChorusDesign.md](ChorusDesign.md) §3.1 and
  [Architecture.md](Architecture.md) §4 item 1 list two categories.
* **The monitor's MVBA value** is a representation; a `FallbackQC`-held
  positive entry is written `{"fallback": k}` ([Monitor.md](Monitor.md)).
* **One session.** The plan expected two sessions on one branch; R15 and
  its Chorus side fit one.

**R16 · The `CommitQC` finalization route (S8). Done** (2026-10-02; the
builds are [History.md](History.md)'s R16 row). The design and what the
build decided are §8.2.
* **Chorus has Part I's route.** `on_mvba_commitqc_pos` / `_neg` record a
  valid MVBA certificate's entries after the certificate bridge on the
  recovered representation. `commit_assign_*` finalize on `fbcommitqc ∨
  mvba_commitqc` together with the records. The re-broadcast is folded
  into the handoff. The main body's route stays.
* **Contract.** `certified_mono`, and `AvailReady` as an input the caller
  drives: `markAvail`, its effect, its own-party frame, `init_availReady`
  and four frames. `certified_unique` and `certified_decided` reach the
  solver. `Mvba.mvbaSafety` proves every field, with no Mvba model
  change.
* **Chorus drives `AvailReady`** (`mvba_avail_ready`, the chunk wait as its
  guard). `avail_ready_chunks` proves what it means, and
  `Chorus.certified_available_chunks` reads `certified_available` in
  Chorus's vocabulary.
* **Gates.** The MVBA-arm gates of the decision handlers, `mvba_terminate`
  and `cast_fb_commit` are gone: our modelling error, since the target has
  none. `mvba_decided_phase` reads `phase ≠ pre_deadline`, and the two
  helpers `mvba_complete_phase` and `fbcommit_sig_phase` are deleted.
* **Liveness.** (F-avail) is derived (`Chorus.fAvail_of_fJustice`) and has
  left `MvbaAdmissible`. `ValidBridge`'s completeness covers held
  (accepted) meta-blocks. The availability report is a fair family, owed
  for a held meta-block (`availOwed`). The timed premise has its δ-row, and
  (Δ-avail) is assumed inside `TimedMvbaAdmissible` until S4.
* **Findings.** P12 (§6): the MVBA's availability couples it to the
  dissemination layer through state Module 3 (`mod:mvba`) does not
  expose. The interface check is §8.2 (h).
* Families: Chorus cold; Mvba warm (instance proofs and liveness in plain
  Lean); FallbackReceipt warm.
* Pins: `#veil_status Chorus` moved with the route's actions and
  properties (§8.2 (i); the counts are [History.md](History.md)'s R16
  row); the Mvba and FallbackReceipt pins unchanged.
* Re-established at `[propext, Classical.choice, Quot.sound]`:
  `Chorus.slotConsensusSafety`, `Chorus.termination`, the timeline,
  `Chorus.totality`, the three Chorus witnesses, System.lean's end theorems
  and every pin of [Cadence.lean](../Cadence.lean). The monitor suites
  pass.
* S4: the paper's bound still uses the main body's route. (Δ-avail) is now
  S4's to derive ([TODO.md](TODO.md) § Liveness).

*Plan changes made in R16:*
* **No second stated bridge.** §5.7 expected the route's data availability
  to need one. The certificate bridge the route needs for agreement also
  gives DA.
* **AvailReady is an input**, which the plan left open. On Lars's decision
  it is driven by Chorus, which needed one premise change (`ValidBridge` at
  held values) and the owed condition `availOwed`. Both read the MVBA's
  internal `accepted` (P12).
* **The gates.** The plan did not foresee them. Dropping them deleted two
  helper invariants, so the pin came out two invariants' cells below the
  design ([History.md](History.md), the R30 row).
* **Contract shape.** `availReady_markAvail_frame` was added after the
  first cold solve found it missing (❌). `markAvail_enabled` was dropped,
  because no cell reads it and the monitor stub could not satisfy it.
* **The design's new invariants were fewer than planned.** The route's
  agreement and DA are covered by the existing invariants, restated over
  the widened ties. The one new invariant is `avail_ready_chunks`.

**R17 · Close the realignment. Done** (2026-10-02; the build is
[History.md](History.md)'s R17 row).
* **Re-check by §1.** The map regenerated from `48cac9a` is byte-identical,
  and the citation check is clean. Paper `master` has not moved (§9).
* **The classification walked once more** against the realigned models:
  every (b) and (c) item is modelled (§4), and every remaining difference
  is an abstraction with its argument or a finding (§5.10). None needs a
  model change.
* **The interface check** (§6.1): one new finding, P13. Module 1's
  Termination is stated without the abandon and start conditions Chorus
  needs; the contract already states both as antecedents.
* **§6 is the findings page for the authors**, P1–P13.
* **Status flipped.** §0, the README's paper section and the
  [Cadence.lean](../Cadence.lean) header say "corresponds to paper
  revision `48cac9a` (main body plus internal supplement)", and §0 is the
  one home of the target. Every model header has one pointer to §0 in
  place of its paper pin. The edit is comment-only, but it rebuilt every
  family, warm.
* **Verification.** A full warm re-validation: lake exit 0, ✅ 6 209 /
  ❌ 0 / 💥 0 / ⏱ 0 / ♻ 1 082, no warnings. Every pin is unchanged, and
  the three monitor suites pass.
* **The tag** `paper-target/48cac9a` is on the merge commit of this
  session's PR.

*Plan change made in R17:* the plan had each model header's pin become
`48cac9a`. Instead, every model header points to §0 and names no
revision, so a later re-pin edits no model file and rebuilds no family.

**After the realignment: the Chorus bounds leg resumes** at the stage it
stopped ([Bounds.md](Bounds.md) §6.4.6):

* **S4: the MVBA tail and the assembly.** `T.termination` through the
  projection, the fallback commit round (rows over the validator's own
  `B′`), the case split, and the bound. **F4 is decided here** (P5).
  **Done in R18** (2026-10-02): `Chorus.timed_termination` and
  `Chorus.timed_termination_tight`; F4 and P5 confirmed. (Δ-avail) was not
  derived: F15 (§5.10) needs a model change, R19.
* **R19: F15 closed** (2026-10-02). The fallback signer re-disseminates
  inside the fallback-entry rule, and a proposer's chunk is delivered
  whatever the proposer does after proposing. (Δ-avail) is derived, and P12
  is updated ([Bounds.md](Bounds.md) §6.4.2, "F15 closed").
* **S5: the contract instances.** `SlotConsensusTemporal` at the new
  fragment (Quiescence, `admissible_exists`, Termination as the unbounded
  corollary), then `SlotConsensusWithTotality` and the `…_of_temporal` join
  with its `rfl` lemma. After that: the [Cadence.lean](../Cadence.lean)
  rows, and (A-sc-termination) moving from assumed to discharged.

#### R15: the design (PaperAlignment §8.1 until R33)

Written before any model edit. [spikes/13_metablock_consumer_ok.lean](../spikes/13_metablock_consumer_ok.lean)
checks the two Veil mechanisms the design rests on: a class field
`entries : value → entryvec` read inside a consumer's guards and invariants,
and a class that takes the system's quorum family as a parameter. It
reconstructs every cell, and the withheld field is reported as withheld.

**(a) The value.** The MVBA's value is the target's meta-block
representation: an entry vector together with the certificate kind of each
positive entry. The MVBA "votes and decides over `entries(B)`"
(Supplement, Section 1.1 (`subsec:mvba-datatypes`)), and two valid
meta-blocks "may carry different certificates for the same verdicts"
(Supplement, Section 1.2 (`subsec:mvba-protocol`), "Agreement and Integrity
over entries"). At the system's instantiation
([Interfaces.lean](../Cadence/Interfaces.lean), beside the MVBA classes):

```lean
inductive CertKind | fastQC | fallbackQC
abbrev MetaBlock (node merkle_root : Type) := node → Option (merkle_root × CertKind)
def MetaBlock.entries (b : MetaBlock node merkle_root) : node → Option merkle_root :=
  fun j => (b j).map Prod.fst
```

`MetaBlock.entries` is `entries(B)`. The representation leaves out what no
rule of either document reads: the certificate kinds of negative entries,
and the `FBCert`. `AvailReady` (Supplement, Algorithm 1, line 90
(`line:mvba:commit-send`)) and the fallback commit wait (Algorithm 5,
line 38 (`line:fb-commit-foreach`)) read only the positive `FallbackQC`
entries. Whether the left-out certificates verify is part of `Valid`, which
stays a predicate on the representation.

**(b) The contract.** One edit of `MVBASafety`. Unchanged fields are elided.

```lean
class MVBASafety (party value entryvec message state pset : Type)
    (B : ByzNodeSet party pset) (byz : party → Prop)
    extends TransitionSystemSafety state where
  Valid : value → Prop
  entries : value → entryvec
  …
  agreement : ∀ st, reachable st → ∀ p q v v',
    ¬ byz p → ¬ byz q → decided st p v → decided st q v' → entries v = entries v'
  integrity : ∀ st, reachable st → ∀ p v v',
    ¬ byz p → decided st p v → decided st p v' → entries v = entries v'
  external_validity : ∀ st, reachable st → ∀ p v, ¬ byz p → decided st p v → Valid v
  availReady : state → party → value → Prop
  certifies : state → message → entryvec → Prop
  decided_certified : ∀ st, reachable st → ∀ p v, ¬ byz p → decided st p v →
    ∃ c, certifies st c (entries v)
  accept : state → party → message → state → Prop
  accept_trans : ∀ st p c st', accept st p c st' → trans st st'
  accept_effect : ∀ st p c st' e, accept st p c st' → certifies st c e →
    ∃ v, entries v = e ∧ decided st' p v
  accept_enabled : ∀ st p c e, reachable st → ¬ byz p → certifies st c e →
    (∃ v', proposed st p v') → ¬ abandoned st p → (∀ v', ¬ decided st p v') →
    ∃ st', accept st p c st'
  certified_unique : ∀ st, reachable st → ∀ c c' e e',
    certifies st c e → certifies st c' e' → e = e'
  certified_decided : ∀ st, reachable st → ∀ c e p v,
    certifies st c e → ¬ byz p → decided st p v → entries v = e
  certified_valid : ∀ st, reachable st → ∀ c e,
    certifies st c e → ∃ v, entries v = e ∧ Valid v
  certified_available : ∀ st, reachable st → ∀ c e, certifies st c e →
    ∃ q, B.supermajority q ∧ ∀ p, B.member p q = true → ¬ byz p →
      ∃ v, entries v = e ∧ Valid v ∧ availReady st p v
```

* **Agreement and Integrity** are the supplement's sentences: "if correct
  validators decide `x` and `x′`, then `entries(x) = entries(x′)`", and
  "all decision outputs of a correct validator carry the same entry
  vector". Redelivery with the same entry vector is permitted, which is why
  Integrity is not "at most one representation" (§5.4).
* **The commit certificate is over entries.** It is "an aggregate of
  `2f+1` Commit signatures over `entries(x)`" (Supplement, Section 1.2
  (`subsec:mvba-protocol`), "Decision output and handoff"). So `certifies`
  takes an entry vector, a decision exposes a certificate for its entries,
  and accepting a certificate decides *some* representation with those
  entries. That representation is `Recover(e)` (Supplement, Algorithm 1,
  line 79 (`line:mvba:decide-guard`)).
* **The certificate-level fields of §5.7.** A certified entry vector is the
  only one: `certified_unique` against another certificate and
  `certified_decided` against every correct decision. Both are needed: a
  certificate can exist before any correct validator decides, because the
  adversary can aggregate it. A certified entry vector has a valid
  representation (`certified_valid`). The **availability field**
  (`certified_available`): a certificate's `2f+1` signers include, among
  their correct members, only validators that were `AvailReady` for a valid
  representation of the certified entries. That is the supplement's "the
  MVBA ensures that each correct Commit signer holds and broadcasts its
  assigned share before sending its vote" (Supplement, Section 1.2
  (`subsec:mvba-protocol`), "Commit availability condition").
  `availReady` is the observable `AvailReady_p(v)`, indexed by the
  representation (S7).
* **All first-order.** The availability field needs a quorum: a certified
  meta-block's entries are available because a supermajority signed the
  certificate and each of its correct members held its share. So the class
  takes the system's quorum family `B` as a parameter, as
  `Cadence.ByzNodeSetCounting` does. Chorus passes its own `nset`, and
  `Mvba.mvbaSafety` passes the model's. `byz` stays the class's notion of
  correct; `B` is used only for counting.
* **`veil_smt_ignore`:** `decided_certified`, `accept_effect` and
  `accept_enabled`, as now, and the four `certified_*` fields. No Chorus
  cell in R15 reads a certificate (`accept_mvba_commitqc` needs only
  `accept` and `accept_trans`). Every field that reaches the solver is a
  hypothesis of every one of Chorus's cells, and three of the four have an
  `∃` in their conclusion. Withheld fields stay declared axioms of the
  class, proven by `Mvba.mvbaSafety`. R16 lifts the attribute on exactly
  the fields its new cells use. That changes no statement, and R16 re-solves
  Chorus cold anyway.
* **Nothing is weakened.** `external_validity`, the inputs, the frames and
  Quiescence keep their statements. Agreement is the module's
  (Module 3 (`mod:mvba`)), Integrity is the supplement's (§5.4, P1), and
  every certificate field is new. `MVBATemporal` and `MVBA` take the new
  parameters and keep their fields, so Termination still says every correct
  party decides *some* representation.

**(c) The MVBA model.** [Mvba.lean](../Cadence/Mvba.lean) gets two sorts:
`value`, the representation, and `evec`, the entry vector. They are joined
by `immutable function ent : value → evec`, which the instance exports as
`entries`. Every relation of the supplement that carries a meta-block
carries the representation: `input`, `msg_preprepare` (the `Pre-Prepare`
carries `x` and signs `H(entries(x))`), `accepted` (`x_v`), `decided`,
`avail_ready` and `valid`. Every signed vote and every certificate carries
the entry vector: `msg_prepare`, `msg_commit`, `msg_timeout_qc`,
`msg_prepqc`, `msg_commitqc`, `tc_lock` and `local_prepqc`. This is exactly
the split of Supplement, Algorithm 1 (`alg:mvba`–`alg:mvba-cont3`).

* `handle_preprepare*` accept a valid `x`, check the lock against
  `ent x` (Supplement, Algorithm 1, line 17 (`line:mvba:pp-guard`):
  "`entries(x) = lock(J)` whenever `lock(J) ≠ ⊥`"), and send the `Prepare`
  on `ent x`. `adopt_prepqc (i v x q)` and `send_commit (i v x)` take the
  accepted `x` and act on `ent x`. `send_commit` requires `avail_ready i x`,
  the supplement's `AvailReady_i(x_v)`.
* **`Recover` is a choice among valid representations.**
  `leader_repropose (l pv v w x)` re-proposes any valid `x` with
  `ent x` the lock. `form_own_commitqc (i v q x)` and `decide (i v x)`
  decide any valid `x` whose entries the certificate certifies. The
  supplement's `Decide` takes `x_v` when its entries match and `Recover(e)`
  otherwise, and `Recover(e)` returns "a valid meta-block with entry vector
  `e`" from any holder (Supplement, Section 1.2 (`subsec:mvba-protocol`),
  "Crash-recovery contract"). The model's choice includes both, so the
  model has every run of the supplement and some where a validator decides
  a representation it fetched although it held one.
* **How two correct validators decide different representations with the
  same entries.** A Byzantine leader sends two valid representations with
  one entry vector to different validators. Both pass the guard, both
  validators prepare and commit the same entries, and each decides its own
  `x_v`. The `Recover` choices in a re-proposal and in `decide` give
  further runs of the same kind.
* **Why every safety property survives.** The safety argument
  (`prepqc_blocks_lower_commits`, `commitqc_agree`, Supplement, Theorem 1
  (`thm:agreement`)) is about votes and certificates, and those are over
  entry vectors exactly as before. Agreement over `ent` follows from
  `decided_backed` (a decision's entries carry a commit certificate) and
  `commitqc_agree`. Integrity is still by construction: one decision per
  validator, so the model proves the stronger at-most-once. External
  validity is now the decide guards' `valid x`. Every invariant keeps its
  name and is restated over the split. Where a fact links a vote to the
  meta-block behind it, the conclusion is existential. One example is
  `honest_commit_accepted`: `msg_commit R V E → local_prepqc R V E ∧ ∃ X,
  ent X = E ∧ accepted R V X ∧ avail_ready R X`, the lifted `TrySendCommit`
  guard. That invariant is what `certified_available` is proven from.
  Others are `prepqc_valid` and `commitqc_valid`: a certified entry vector
  has a valid representation, which is `Recover`'s correctness ("any
  correct signer of a valid prepare certificate on `e` is such a peer").
* **NoLock.** [Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) is the same
  model with the lock check removed, so it takes the same split. Its theory
  sets `value = evec = Fin 2` and `ent = id`: one representation per entry
  vector, since the mutation test is about the lock and not about
  representations. The scenario is unchanged. The pinned message is
  expected to change, because labels print the new parameter lists. It is
  re-pinned with `(sequential := true)`, and the reason is recorded in the
  file.
* **The witness and liveness.** [Mvba/Witness.lean](../Cadence/Mvba/Witness.lean)
  instantiates `value = evec = Unit`. The liveness chain needs a `Recover`
  output wherever a re-proposal or a decision fires: `prepqc_valid` and
  `commitqc_valid` supply it. (Δ-avail) is indexed by the representation, as
  the supplement's synchronization assumption is ("whenever a correct
  validator holds a valid meta-block `x`"). `Mvba.termination`,
  `Mvba.bounded_termination`, `Mvba.mvbaTemporal` and both witnesses are
  re-proven on the new labels.

**(d) Chorus.** [Chorus.lean](../Cadence/Chorus.lean) gets the sort
`mentries` beside `mvalue`, and
`instantiate mvba : MVBASafety node mvalue mentries mmsg mstate nodeset nset
(fun i => nset.is_byz i = true)`.

* `mval_pos (e : mentries) j m` and `mval_neg (e : mentries) j` project the
  entry vector, and every read goes through the class:
  `mval_pos (mvba.entries v) j m`. The new immutable relation
  `mval_fb (v : mvalue) j` says entry `j` of the representation is
  certified by a `FallbackQC`. The two assumptions are unchanged, now over
  `mentries`, and System.lean proves them as before.
* **The decision handlers read the validator's own representation.**
  `on_mvba_decide_pos (i j m v)` requires `mvba.decided mvba_st i v` and
  `mval_pos (mvba.entries v) j m`. Its bridge now checks the certificate the
  representation names:
  `(¬ mval_fb v j ∧ vote_quorum_pos j m) ∨ (mval_fb v j ∧ fb_quorum_pos j m ∧ fbcert)`.
  This implies the old disjunction, so `mvba_decided_pos_backed` and every
  invariant downstream keep their statements. The shared per-entry records
  stay. They hold the agreed entries, and their uniqueness is still proven
  from `agreement`, now over entries, through the tie invariants (spike 13
  checks this shape).
* **`cast_fb_commit (i v)` waits exactly under its own `B′`:**

  | | the fallback commit wait |
  |---|---|
  | target | "upon `MVBA[s].decide(B′)`: for each `FallbackQC` in `B′` with a positive entry `⟨s, j, root⟩`: wait until `p_i` has received and validated its assigned chunk for `root`" (Algorithm 5, line 37 (`line:fb-mvba-decide`) to Algorithm 5, line 39 (`line:fb-commit-wait`)) |
  | before (R12) | `∀ J M, is_proposer J → mvba_decided_pos J M → vote_quorum_pos J M ∨ msg_chunk_received i J M` |
  | after | `require mvba.decided mvba_st i v` and `∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → msg_chunk_received i J M` |

  The `B′` is the validator's own decision, a parameter of the label, and
  the wait runs over its `FallbackQC` entries and no others. F13 closes
  with no residual: a root that is `FastQC`-certified elsewhere but
  `FallbackQC`-certified in this `B′` is waited for, as in the paper.
  `require mvba_complete`, the transport of the vector, stays as it is. The
  vote's content is the entry vector, so `msg_fbcommit_sig` is unchanged.
* **A redelivered decision** (P11). The contract's Integrity lets a correct
  validator output several representations with one entry vector, so
  `mvba.decided mvba_st i v` may hold for two `v`. The target does not say
  what the handler of Algorithm 5, line 37 (`line:fb-mvba-decide`) does with
  the second output. It may re-run, be ignored, or replace the first `B′`.
  The model's rule is safe under all three readings:
  1. **The vote is cast once per validator.** The fired-once guard
     `¬ local_fbcommit_voted i` stays, so `cast_fb_commit` moves the state
     whenever it fires, and `Chorus.justice_enabledMove` keeps its proof.
     Every reading casts the same message, because the vote's content is
     the entry vector.
  2. **The wait reads the `FallbackQC` entries of the `v` it is cast for.**
     That `v` is some representation `i` decided. Under every reading the
     paper's validator casts after waiting under the `FallbackQC` entries of
     one of its decided `B′`s, so every paper vote is a model vote. The
     model may also cast under a later `v` where the "first `B′` only"
     reading would not. That adds runs, which is safe, because no safety
     property reads the wait.
  3. **The premise owes the vote only for a validator with one
     representation:** `Owed (.cast_fb_commit i v)` is
     `mvba.decided s.mvba_st i v ∧ ∀ v', mvba.decided s.mvba_st i v' → v' = v`.
     With one decision output, all three readings cast after the wait under
     that `B′`, and the δ-row owes exactly that vote. With several, the row
     owes nothing, so the premise never owes a vote the paper might not
     cast. At the system's instance the case does not arise: `Mvba` decides
     once per validator (it proves the stronger at-most-once Integrity), so
     the conjunct costs `Chorus.termination` one application of
     `reachable_integrity`.
* **No new per-validator record.** The validator's own representation is
  already a per-validator observable that the model reads positively,
  `mvba.decided mvba_st i v`, which the handlers read too. A Chorus-side
  copy would need its own tie invariant and would say nothing more.
* `mvba_propose` checks `Valid B_i` per kind, the same way as the handlers,
  for positive entries. `mvba_terminate` reads through `mvba.entries`.
* **Reads and sizes.** Every new read is positive. `mvba.decided` is read in
  positive position (oracle state, category (A) of
  [ChorusDesign.md](ChorusDesign.md) §3.5), as are `msg_chunk_received` and
  the network ghosts. `mval_*` are immutable. Parameters: `cast_fb_commit`
  2, `on_mvba_decide_pos` 4, `on_mvba_decide_neg` 3, `mvba_propose` 3.
* **P1 and P2 do not block.** P1: the contract states Integrity in the
  supplement's form. The vote fires once and its content is the entry
  vector, so a redelivered decision with another representation would cast
  the same message. Nothing in the model relies on the main body's "decides
  at most once". P2: the model never assumes a common `B′`. Termination is
  re-proven per validator, which is the repair P2 describes.

**(e) What the liveness vocabulary becomes.**

* **`ValidBridge`** keeps its two directions over the representation, and
  `Certified st x` names the certificate per kind. For a positive entry
  `(j, m)` of `entries x`, a `FastQC`-kind entry has `vote_quorum_pos j m`
  and a `FallbackQC`-kind entry has `fb_quorum_pos j m ∧ fbcert`. Negative
  entries are unchanged. This is sharper than before, where either
  certificate would do. It is still the cryptographic content of the seam:
  a valid meta-block's certificates are genuine, and genuine certificates
  make it valid.
* **The handoff.** `accept_mvba_commitqc` is unchanged. `relayOwed` is
  unchanged ("a correct validator has decided"). The MVBA's `Relayed`
  premise reads the `decide` family, whose representation is the `Recover`
  choice. `relayed_of_timedJustice` and `fRelay_of_fJustice` are re-proven.
* **`Owed`:** the one row that changes is
  `.cast_fb_commit i v => mvba.decided s.mvba_st i v ∧ ∀ v', mvba.decided s.mvba_st i v' → v' = v`
  (was `∃ v, mvba.decided s.mvba_st i v`). (d) gives the reason.
* **The hop rows:** `cast_fb_commit` stays a δ-row with the same gate. Its
  chunk is delivered by `redisseminate_chunk`'s own Δ-row from the correct
  `FallbackQC` signer (`Owed` is `msg_fb_pos_sig k j m`, F14). So the
  premise owes the vote δ after the wait is over, which is when the paper's
  validator casts it. The run F13 excluded from the timed claim's premise
  is now a run of the premise.

**(f) The pins, written down before the build.** Cells are
`(A + 1)(I + 1) + A·S`: invariant-type properties and one does-not-throw
cell at every action and at the initializer, and each step property at
every action.

* `#veil_status Mvba`: `A = 28`, `I = 50`, `S = 1`, all unchanged. No action
  or property is added or removed, and the availability fact rides on the
  restated `honest_commit_accepted`. **`29 · 51 + 28 = 1507` → 1507.**
* `#veil_status Chorus`: `A = 46`, `I = 101`, `S = 1`, all unchanged.
  **`47 · 102 + 46 = 4840` → 4840.**
* `#veil_status FallbackReceipt`: 220, warm.
* Every Mvba and Chorus VC statement changes, so both families re-solve
  cold although the counts stay. If the cold solve needs a helper
  invariant, each one costs `A + 1` cells (29 on Mvba, 47 on Chorus). It is
  recorded as a plan change with the new arithmetic.

#### R16: the design (PaperAlignment §8.2 until R33)

Written before any model edit, and sent to the coordinator before one.

**(a) The route, as the target states it.**

| | the `CommitQC` finalization route |
|---|---|
| target | "Upon receiving this output, Chorus broadcasts the `CommitQC`. A correct validator that receives a valid such certificate re-broadcasts it and finalizes the certified outcome, recovering a matching meta-block or the underlying proposals as required by the ordinary commitment-proof recovery path. Thus the concrete MVBA's internal Commit round also serves as the fallback commitment-certification round." (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff") |
| the MVBA's side | "upon receiving a valid `CommitQC` … if `DecidedQC_i = ⊥`: `Decide(CommitQC)`" (Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)); every correct validator decides within `2Δ_R + Δ` of the first learner (Supplement, Lemma 13 (`lem:decision-propagation`)) |
| the recovery path | "A correct validator finalizes only the proposal vector `recoverProposals(entries(B))` (Algorithm 6, line 14 (`line:da-recover-slot`)) for a meta-block `B` whose entries are backed by a commitment proof it holds" (Lemma 9 (`lemma:chorus-agreement`), proof) |
| model | a correct validator `i` that holds a valid MVBA certificate `c` recovers a matching representation `v` (`mvba.certifies mvba_st c (mvba.entries v)`), checks the certificates `v` names, and records the certified entries (`on_mvba_commitqc_pos` / `_neg`). It then commits and finalizes them by the ordinary `commit_assign_*` / `finalize_commit`, whose certificate disjunct gains "a valid MVBA `CommitQC` exists" |

The re-broadcast is folded into the handoff, as the decision broadcast is
today: a certificate is transferable and stays valid, so its existence is
its availability to every validator, and nothing is written. The handoff
into the MVBA (`accept_mvba_commitqc`) is unchanged. The main body's
`fbCommitQC` route stays.

**(b) The new actions.** Two handlers and one guard disjunct.

```lean
ghost relation mvba_commitqc := ∃ C E, mvba.certifies mvba_st C E

action on_mvba_commitqc_pos (i : node) (j : node) (m : merkle_root) (c : mmsg) (v : mvalue) {
  require ¬ is_byz i
  require is_proposer j
  -- `i` holds a valid commit certificate, and `v` is a representation of
  -- its entries whose entry for `j` is `m` (`Recover(e)`).
  require mvba.certifies mvba_st c (mvba.entries v)
  require mval_pos (mvba.entries v) j m
  -- The bridge, as at the decision handlers: the certificate `v` names for
  -- the entry verifies against the network.
  require (¬ mval_fb v j ∧ vote_quorum_pos j m) ∨ (mval_fb v j ∧ fb_quorum_pos j m ∧ fbcert)
  require ¬ local_mvba_recorded i j
  mvba_decided_pos j m := true
  local_mvba_recorded i j := true
}
-- on_mvba_commitqc_neg (i j c v): the same with `mval_neg` and the
-- negative bridge of `on_mvba_decide_neg`.
```

`commit_assign_pos` requires
`msg_commitqc_pos j m ∨ ((fbcommitqc ∨ mvba_commitqc) ∧ mvba_decided_pos j m)`
(was `… ∨ (fbcommitqc ∧ mvba_decided_pos j m)`), and `commit_assign_neg`
likewise. `finalize_commit` is unchanged.

* **The records stay shared and keep their meaning**, "the agreed
  entries". They now have two sources: a correct validator's decision, and
  a valid certificate. The new handlers write the records the decision
  handlers write, so every invariant downstream of the records
  (`*_backed`, `*_chunks_decodable`, `*_proposer_signed`, the
  commitQC-consistency invariants, proposal inclusion, speculative safety)
  keeps its statement and now covers the route. A separate pair of records
  would duplicate about twenty of them.
* **Why a handler, and not only the guard disjunct.** A certificate can
  exist before any correct validator decides (the adversary aggregates
  `2f+1` `Commit`s), and the paper's validator finalizes on it then. With
  only the disjunct, finalization would wait for a correct decision's
  records. The handler records from the certificate itself.
* **Reads.** All positive. `mvba.certifies` is oracle state read in
  positive position (category (A) of [ChorusDesign.md](ChorusDesign.md)
  §3.5), and the ghosts and `mval_*` are read as at the decision handlers.
  The one negative read is the fired-once record `local_mvba_recorded i j`,
  which is local state (category (L)). No network relation is read
  negatively, so the §3.1.1 audit gains no entry.
* **Parameters**: 5 and 4.
* **Fired once.** `local_mvba_recorded i j` is shared with the decision
  handlers: a validator records entry `j` once, from whichever source comes
  first, and both sources write the same value (`mvba_decided_pos_unique`).
  Every firing sets the record, so `Chorus.justice_enabledMove` keeps its
  proof.
* **Gates.** `¬ is_byz i` and `is_proposer j`, as at the decision handlers.
  **No phase gate**: the target's rule has none ("A correct validator that
  receives a valid such certificate re-broadcasts it and finalizes",
  Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and
  handoff"), so the sketch above loses its `require phase = post_mvba_arm`
  (see "The MVBA-arm gates" below). `mvba_invoked` is **not** required: a
  validator on the fast path that receives a `CommitQC` finalizes on it,
  and no safety invariant relies on the condition. There is no
  participation gate, because the handler only processes, like the
  decision handlers. `commit_assign_*` and `finalize_commit` keep theirs.
* **Liveness classification.** Both handlers are honest labels, so they
  are under (F-justice). Their `Owed` is the handoff's `relayOwed` ("a
  correct validator has decided", and Chorus broadcasts that decision's
  certificate). The premise asks nothing on a certificate the adversary
  assembled and showed to nobody (F5). `Owed` of `commit_assign_*` is
  unchanged, so the liveness argument keeps the main body's route, and S4
  is unaffected.

**The bridge is the existing one, at one more site. This is for Lars.**
The route needs the certificate check on the recovered `v`, and there is
no way around it. Chorus's agreement with the fast path needs the
certified entries' certificates to be genuine. The contract's only
statement about a certified entry vector's certificates is
`certified_valid` (`Valid v` for some representation), and `Valid` is a
predicate fixed before Chorus's network exists. That is exactly the gap
the decision handlers' bridge closes. The route uses the same statement
("a valid meta-block's certificates verify against the network") with the
same soundness argument: the check removes no real behaviour, because
`Recover(e)` returns a valid representation (`certified_valid`) and a valid
one passes it. The content of the trust-base item does not change. Its
sites become the two decision handlers and the two route handlers, and its
wording in [CompositionContracts.md](CompositionContracts.md) §3/§7 and
[Architecture.md](Architecture.md) §4 says "at the decision handlers and
the `CommitQC` route". **No second bridge is needed for data
availability**, although §5.7 expected one: the route's DA follows from
the same check, through `mvba_decided_pos_chunks_decodable` (see (e)).

**(c) `AvailReady`: an MVBA input that Chorus drives.** The target makes
the DA layer the source of availability. `AvailReady_i(x)` holds "if, for
every positive entry `⟨s, j, ρ⟩` of `x` that is certified by a
`FallbackQC`, validator `p_i` holds its assigned availability share for
`ρ`", and "the MVBA treats availability synchronization as a service of the
composing dissemination and ChunkSync layer" (Supplement, Section 1.2
(`subsec:mvba-protocol`), "Commit availability condition" and
"Availability-synchronization assumption"). So `become_avail_ready`
becomes the contract's fourth input, and Chorus drives it with the chunk
wait as its guard:

```lean
-- Interfaces.lean, MVBASafety
  markAvail : state → party → value → state → Prop
  markAvail_trans : ∀ st p v st', markAvail st p v st' → trans st st'
  markAvail_effect : ∀ st p v st', markAvail st p v st' → availReady st' p v
  markAvail_enabled : ∀ st p v, ∃ st', markAvail st p v st'           -- withheld
  init_availReady : ∀ st p v, init st → ¬ availReady st p v
  availReady_frame : ∀ st st' p v, ¬ byz p →
    (step st st' ∨ (∃ q w, propose st q w st') ∨ (∃ q, abandon st q st') ∨
      (∃ q c, accept st q c st')) → (availReady st' p v ↔ availReady st p v)

-- Chorus.lean
action mvba_avail_ready (i : node) (v : mvalue) (mvba_next : mstate) {
  require ¬ is_byz i
  require ∀ J M, mval_pos (mvba.entries v) J M → mval_fb v J → msg_chunk_received i J M
  require ¬ local_avail_marked i v
  require mvba.markAvail mvba_st i v mvba_next
  mvba_st := mvba_next
  local_avail_marked i v := true
}
```

* **On the MVBA side the model does not change.** `become_avail_ready` is
  already an unguarded action, and the instance classifies it as an input
  (`Label.isInput` in [Mvba/Compose.lean](../Cadence/Mvba/Compose.lean),
  and `InputLabel` in place of `AvailLabel` in
  [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean)). (F-avail) stays a
  premise of `Mvba.termination`, now as a caller's premise beside
  `AllPropose`. The Mvba family stays warm. The instance proofs,
  `Mvba.Liveness`, `Mvba.Temporal` and the Mvba witnesses re-check in plain
  Lean.
* **On the Chorus side the premise `MvbaAdmissible` loses `Mvba.FAvail`.**
  `Chorus.termination` derives it instead, as it derives `AllPropose`. The
  derivation uses (F-justice) on the new family (per validator and value,
  with `Owed` true, since it consumes only the validator's own chunk
  receipts), and the chunk under a `FallbackQC` entry reaches `i` by
  `redisseminate_chunk` from the entry's correct signer (`Owed` is
  `msg_fb_pos_sig k j m`, F14). The derivation needs the accepted value's
  `FallbackQC` entries to be genuine. That is the bridge's completeness
  direction at an **accepted** value, and `ValidBridge` states it today at a
  decided one. So `ValidBridge`'s second clause is extended from decided to
  accepted values. **This is a premise change, for Lars.** In the timed
  claim ([Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean)), the
  `Mvba.AvailWithin` premise is replaced by a δ-row for the new family.
  That is a statement change; the proof is S4's. The three Chorus witnesses
  fire the new family where the MVBA's environment marked availability
  before.
* **What this buys.** The supplement's `Δ_sync` assumption becomes a
  consequence of Chorus's rows (§8, R16's "to decide"). One premise of the
  composed liveness claim is removed and one is extended.
* **The alternative** is to keep `AvailReady` the MVBA's environment
  relation. It needs no bridge either (by (e)), and it costs nothing in
  Chorus's liveness. But (F-avail) then stays an assumption, in the
  composed system, about a step that is Chorus's own. It has one action and
  one invariant fewer: `#veil_status Chorus` is then 5046 instead of 5199.

**(d) Fields that reach the solver.** The new cells read
`certified_unique` (two certificate-sourced records), `certified_decided`
(a certificate-sourced record against a decision-sourced one), the new
`certified_mono` (the certificate tie survives every transition, below)
and, for (c), `markAvail_trans`, `markAvail_effect`, `init_availReady` and
`availReady_frame`. All of them are universally quantified implications,
so they are first-order. They leave `veil_smt_ignore`, or are added
outside it. `decided_certified`, `accept_effect`, `accept_enabled`,
`certified_valid`, `certified_available` and the new `markAvail_enabled`
stay withheld: each has an `∃` in its conclusion, and no cell reads it.

```lean
  certified_mono : ∀ st st' c e, trans st st' → certifies st c e → certifies st' c e
```

`certified_mono` is new: "a valid certificate stays valid", which is what
makes it transferable. `Mvba.mvbaSafety` proves it from the generated
monotonicity of `msg_commitqc`. Together with (c) this is the one contract
edit of R16. Nothing is weakened.

**(e) Invariants.**

* **Restated: the tie invariants.** A record is now the projection of a
  correct decision *or* of a valid certificate:

  ```lean
  invariant [mvba_decided_pos_tied]
    ∀ J M, mvba_decided_pos J M →
      (∃ I V, ¬ is_byz I ∧ mvba.decided mvba_st I V ∧ mval_pos (mvba.entries V) J M) ∨
      (∃ C E, mvba.certifies mvba_st C E ∧ mval_pos E J M)
  ```

  The negative form is the same. Uniqueness of the records then follows
  from `agreement` (two decisions), `certified_decided` (a decision and a
  certificate) and `certified_unique` (two certificates). The ties are read
  nowhere outside [Chorus.lean](../Cadence/Chorus.lean).
* **Agreement of the route with the fast path and with the `fbCommitQC`
  route needs no new invariant.** Every route finalizes either on
  `msg_commitqc_*` or on a record, and the existing invariants relate the
  two: `local_committed_pos_unique`, `local_committed_pos_neg_excl`,
  `commitqc_pos_mvba_consistent` and its two exclusion siblings, then the
  `safety` statements `agreement_pos` and `agreement_pos_neg`. Their cells
  at the new handlers are the decision handlers' cells, from the same
  bridge evidence. The four manual cells there (two per handler) are
  mirrored.
* **DA on the route needs no new invariant either.**
  `local_committed_pos_implies_decodable` covers the route through
  `mvba_decided_pos_chunks_decodable`, which follows from the bridge
  evidence as at the decision handlers.
* **New, for (c): what `AvailReady` means.**

  ```lean
  invariant [avail_ready_chunks]
    ∀ I V J M, ¬ is_byz I ∧ mvba.availReady mvba_st I V →
      mval_pos (mvba.entries V) J M → mval_fb V J → msg_chunk_received I J M
  ```

  With `certified_available`, this turns §5.7's reading of the R15 field
  in Chorus's vocabulary from a stated bridge into a theorem. A certified
  entry vector has a supermajority whose correct members each received
  its assigned chunk under every `FallbackQC` entry of its own
  representation. That is a plain-Lean corollary,
  `Chorus.certified_available_chunks`.
* **P2.** The proofs assume no common `B′`. Records and certificates are
  over entries, and the bridge is per representation. The agreement case
  P2 says the main body omits, a `CommitQC` against a fast `commitQC`, is
  `commitqc_pos_mvba_consistent` at the new handler. It is proven by the
  main body's fast-path argument (vote-quorum intersection, and the
  `FBCert`/commit intersection), not by Part I's conditional sentence. P2's
  representation divergence does matter for
  `Chorus.certified_available_chunks`: two `Commit` signers may have waited
  under different certificate kinds for one root. So the corollary is
  stated per signer's own representation, and for a root a signer held by
  a `FastQC` the chunks come from the vote quorum instead.

**The MVBA-arm gates.** Before R16, four actions required
`phase = post_mvba_arm`: `on_mvba_decide_pos`, `on_mvba_decide_neg`,
`mvba_terminate` and `cast_fb_commit`. The target's rules have no such
gate. The decision handler is "upon `MVBA[s].decide(B′)`" (Algorithm 5,
line 37 (`line:fb-mvba-decide`)), and the receipt rules are "upon
receiving a valid `fbCommitQC`" (Algorithm 5, line 45
(`line:fb-recv-commit`)) and the supplement's sentence quoted under
"Gates". `Ds + 2Δ` gates only the case-1 *proposal* (Algorithm 5, line 23
(`line:fb-mvba-propose-fast`)), and the case-2 proposal needs only
`2f+1` fallback votes, which exist from `Ds + Δ` on. So a paper validator
can decide, cast its fallback commit vote and hold a `CommitQC` before
`Ds + 2Δ`, and the gate delayed all of that to the MVBA arm. That is a gap
of the same kind as the new handlers' gate, and R16 closes both: none of
the four existing actions and neither new handler has a phase gate. The
remaining phase guards are the target's own: the deadline (`propose`,
`record_chunk`, `vote`), the fallback arm (`fb_sign_*`,
`cast_fallback_vote`), and the two triggers of `mvba_propose`.

*What dropping the gates breaks, by analysis* (the trial build waits for
the go-ahead on the model edit). Exactly three invariants state the gate
and so fail by construction: `mvba_decided_phase` (records exist only at
the MVBA arm), `fbcommit_sig_phase` and `mvba_complete_phase`. Each is
restated as `phase ≠ pre_deadline`, and in that form it follows from the
bridge evidence every record carries. A positive record has a vote
quorum, or a `FallbackQC` under `FBCert`. A negative one has a negative
vote quorum, or `FBCert`. Each of these contains a correct signer, whose
signature postdates the deadline (`voted_post_deadline`, `fb_sig_phase`).
`mvba_complete` and an honest fallback commit vote come after records.
Only the deadline is needed, by the one consumer: proposal inclusion uses
`mvba_decided_phase` to show that `all_honest_recorded`, which can only
become true before the deadline (`record_chunk`), never becomes true after
a conflicting record exists. `mvba_complete_phase` was the phase leg of
`cast_fb_commit`'s enabledness, which no longer has one. No file outside
[Chorus.lean](../Cadence/Chorus.lean) reads the three, so the plain-Lean
liveness proofs are unaffected. Their frames cover the new labels, and
the derivations that stepped through the MVBA arm only lose a premise.
No monotone-network exception is needed, since a gate removed is a guard
removed. The restatement keeps every count, so (f) is unchanged. What
analysis cannot settle is whether a cold solve finds the restated
invariants' cells at the four actions. If one diverges, it is made manual
from the derivation above, and if one turns out false, the counterexample
is reported before anything else changes.

**(f) The pins, written down before the build.** Cells are
`(A + 1)(I + 1) + A·S`.

* `#veil_status Chorus`: `A = 46 + 3 = 49` (`on_mvba_commitqc_pos`,
  `on_mvba_commitqc_neg`, `mvba_avail_ready`), `I = 101 + 1 = 102`
  (`avail_ready_chunks`), `S = 1`. **`50 · 103 + 49 = 5199`**, which is
  `4840 + 3 · 103 + 1 · 50`. Each new action adds one cell per property and
  step property plus its does-not-throw cell (`102 + 1`), and the new
  invariant adds one cell per action and one at the initializer
  (`49 + 1`). Without (c): `A = 48`, `I = 101`, `49 · 102 + 48 = 5046`.
* `#veil_status Mvba`: 1507, warm (no model change).
* `#veil_status FallbackReceipt`: 220, warm.
* A helper invariant found during the cold solve costs `A + 1 = 50` cells,
  and is recorded as a plan change.

**(g) What the cold solve found, and what was decided** (after the
go-ahead; Lars's decisions relayed by the coordinator).

* **The MVBA-arm gates were our modelling error**, not a paper finding.
  The target is clear that the decision handler runs "upon
  `MVBA[s].decide(B′)`" with no time condition (Algorithm 5, line 37
  (`line:fb-mvba-decide`)). The four gates are dropped, and the new
  handlers have none.
* **Two helper invariants are deleted**: `mvba_complete_phase` and
  `fbcommit_sig_phase`. Without the gate they are false. With no
  proposers, `complete_fast_metablock` holds vacuously, so `mvba_invoked`
  holds before the deadline. The contract lets a correct decision appear
  there, and `mvba_terminate`'s per-proposer check is vacuous, so
  `mvba_complete` and then a fallback commit vote can precede the
  deadline. Proving the helpers would need "a correct party decides only
  after proposing". Module 3 (`mod:mvba`) does not state that: its
  interface says only that `propose(B)` is how a validator "thereby
  start[s] to participate", and its Quiescence covers messages, not
  outputs. So the helpers relied on more than the module promises, and
  deleting them is correct. Nothing consumed them: their one use was the
  phase leg of `cast_fb_commit`'s enabledness, which no longer exists.
  `mvba_decided_phase` stays, in the form `phase ≠ pre_deadline`, because
  a record carries a certificate whose correct signers postdate the
  deadline.
* **One contract frame was missing**: `availReady_markAvail_frame` (the
  report concerns its own party and representation). Without it
  `avail_ready_chunks` failed at `mvba_avail_ready` (❌). It is first-order,
  and `Mvba` proves it from the transition body.
* **`markAvail_enabled` is not a contract field.** No Chorus cell reads
  it, and the monitor's silent stub, whose state is `Unit`, could not
  satisfy it together with `init_availReady`. The one liveness proof that
  needs the input to be enabled runs at the `Mvba` instance, where
  `become_avail_ready` is unguarded.
* **The availability report is owed for a meta-block the validator holds**
  (`availOwed i v := ∃ w, accepted i w v`, at the `Mvba` instance). The
  supplement's assumption is about "a correct validator `p_i` [that]
  holds a valid meta-block `x`". Owing the report for every
  representation would make (F-justice) demand reports nobody makes.
* **(Δ-avail) stays assumed inside `TimedMvbaAdmissible` until S4 derives
  it.** The timed premise gains the δ-row (`TimedJustice.avail`).
  Deriving the MVBA's timed clause from it and from the re-dissemination
  rows is a timed proof of the `relayed_of_timedJustice` kind, and it
  belongs to the bounds leg ([TODO.md](TODO.md) § Liveness). The untimed
  (F-avail) is derived (`fAvail_of_fJustice`) and has left
  `MvbaAdmissible`.

**(h) The interface check.** Each R16 addition, against what Module 3
(`mod:mvba`) and the supplement's concrete MVBA expose:

| addition | exposed by the target? | verdict |
|---|---|---|
| `AvailReady` as an input (`markAvail` and its frames) | not by Module 3 (`mod:mvba`); the supplement defines it over the dissemination layer's shares and calls synchronization "a service of the composing dissemination and ChunkSync layer" | the composition needs more than the abstract module states: P12 |
| `availOwed` and `ValidBridge`'s accepted clause, reading `accepted` | neither document exposes the MVBA's `x_v`; the supplement's `Δ_sync` is stated over it | the same seam, P12. Read at the system's instance; no class field carries it |
| `certified_mono` | the commit certificate is the supplement's strengthened interface ("serves as a transferable commitment proof"); transferability is persistence | stated by the supplement, not extra |
| the certificate bridge at the route | `Valid` is "publicly verifiable" in both documents; the bridge says what a valid certificate means in a network of relations | the existing bridge, one more site, not extra |

P12 does not break the claimed abstraction for **safety**. The safety
proofs read the MVBA only through the contract, and the `AvailReady`
input changes no safety statement of the MVBA. It does for **liveness**:
the main body's `ℓ_MVBA` is a constant of a self-contained module, while
the supplement's depends on the composing layer's `Δ_sync`, triggered by
MVBA-internal state. The model states that dependency rather than hiding
it.

**(i) The pins, after the build.** `A = 49`, `I = 100` (101 + 1 new − 2
deleted), `S = 1`, counted `(A + 1)(I + S) + A`; the count is
[History.md](History.md)'s R16 row (R19 later removed one action). The
Mvba and FallbackReceipt pins unchanged, both warm.

### The MVBA's own pins: the review records

Before R13 the MVBA model pinned a supplement revision of its own, first
`026dc8b` and then `eb1bb51` (the revision table above). The two records
below were sections of [MvbaPlan.md](MvbaPlan.md) (§0 and §11) until R21.
Their bare section numbers (§0, §2.4, §3, §8, §11.x) are MvbaPlan's, and
their references to PaperAlignment section numbers are to that document as
it stood at the tag `paper-target/arxiv-v2`.

#### Three notes moved out of the living documents (R21)

* **The view timeout at `026dc8b`** (until R21 in
  [Bounds.md](Bounds.md) §6.2.3). The supplement fixed the timer in one
  sentence (Supplement, Section 1.2 (`subsec:mvba-protocol`)): *"The view timeout is chosen so that,
  after GST, it exceeds `Δ_R + 3Δ + max{Δ, Δ_sync}`. If the implementation
  uses timeout backoff rather than fixed known bounds, the timeout is
  eventually increased beyond this value."* The termination proof then
  counted with a fixed timeout, *"the view timeout is itself `O(Δ)`"*, to
  reach `O(fΔ)`. Bounds §6.2.3's Finding 1 (unbounded backoff has no fixed
  `ℓ`) was about that backoff sentence. It was resolved upstream at
  `eb1bb51` (C13 below): the timeout became the fixed `T` and the backoff
  remark was deleted.
* **The MVBA hop table at `026dc8b`** (until R21 in the header of the hop
  table, [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean)). The table
  classed `decide` as a local step, which the good view could not catch,
  since there every correct validator forms the commit certificate itself
  (C16 (N3) below). From step 5b to R8 `decide` was a network hop, whose
  delivery clause stood in for the composing layer; since R8 it is the
  contract's input and its timing is the caller's `Relayed`. Until R3
  `adopt_prepqc` was a local step that consumed a prepare certificate
  formed anywhere ((N4)). Until R4 the table timed the anonymous commit
  and timeout assemblies, which are the adversary's and carry no bound
  ([Bounds.md](Bounds.md) §6.4.7).
* **R14's model headers** (until R21 in [PaperAlignment.md](PaperAlignment.md)
  §8, "Plan changes made in R14"). R14 made the model headers say that
  citations name the target's references, and left their statement that
  the models were built against v2 in place until R17 replaced it with the
  pointer to [PaperAlignment.md](PaperAlignment.md) §0.

#### What moved between the first draft and `026dc8b`

Each item below changed the model:
changes the model:

* `decide` now outputs the certificate too: `decide(x, CommitQC)`. The
  public Module 3 (`mod:mvba`) has `decide(B)` and no certificate output; the class
  follows the public paper. The certificate is an implementation extra —
  Chorus's fallback commit round forms its own `fbCommitQC` — and is *not*
  a contract field.
* `TrySendCommit` gained an availability precondition `AvailReady_i(x_v)`
  under a new after-GST bound `Δ_sync` (the supplement's
  "availability-synchronization assumption"), plus a `commitSent_i` flag.
  Safety-wise this only removes behaviours; it adds a liveness assumption
  (§3).
* The `Pre-Prepare` handler runs `SyncView(J)` first, so a proposal
  carrying a higher timeout certificate advances the receiver's view before
  the checks; `ViewTC_i` records the certificate that justified the current
  view; `HandleTimeout` raises `lastVotedView_i` to at least the current
  view.
* `TryFormCommitQC` no longer requires `x_v ≠ ⊥ ∧ entries(x_v) = e`: a
  validator may form the certificate first and recover the value
  afterwards (`Recover(e)`). This *removes* a guard, so it is the one change
  that adds behaviour and cannot be ignored conservatively. With `value` the
  entry vector (§1.2) `Recover` collapses to the identity, so the model
  simply decides on the certificate.

#### The supplement at `eb1bb51`, reviewed against the pin `026dc8b`

*Review of 2026-09-29, for step 5b to act on. When it was written no Lean
file had changed and the pin was still `026dc8b`. **Step 5b has since acted
on it (stages 2–5, 2026-09-29): the pin is `eb1bb51`, and the timed
premise states the supplement's network — §11.5 stage 3 has the design
decision, [Bounds.md](Bounds.md) §6.2.4 the clauses.** The change list and the plan are here; the
audit trail (what was compared, and how to re-run the comparison) is
[History.md](History.md) § "Paper alignment before the single target".
This section is a dated record: its references to PaperAlignment
section numbers are to that document as it stood at the tag
`paper-target/arxiv-v2`. The review against the current target
`48cac9a` is [PaperAlignment.md](PaperAlignment.md) §4.*

##### 11.0 Summary, for an auditor

**Which revision.** The paper repository's `master` at **`eb1bb51`**
(2026-09-28). It is 29 commits past `b838e17`, the revision last
re-checked. `b838e17` is itself byte-identical to the pin `026dc8b` in
everything the model rests on, and §7 of PaperAlignment repeats that check.
Six of the 29 commits touch the MVBA.

**How much changed.** The algorithm file was rewritten: it gained a fourth
block, Supplement, Algorithm 1 (`alg:mvba-cont3`), and `TryDecide` was folded into a new `Decide`
procedure. The protocol and correctness prose of Supplement, Section 1 (`sec:mvba-instantiation`)
was rewritten as well. The protocol the model mirrors is the same in every
respect that matters to it: the same messages, certificates, guards, lock
and view change. Every safety lemma, and Supplement, Theorem 1 (`thm:agreement`), keeps its
statement up to whitespace. Three things changed in substance.

* **The termination argument.** Supplement, Theorem 2 (`thm:termination`) is now proven from four
  new lemmas. They rest on a network model that is now written out: which
  messages are delivered after GST, which are retransmitted, and which a
  validator may discard.
* **The timeout.** It is now a fixed value `T`. The backoff remark behind
  this repository's first bounds finding has been removed.
* **The published contract.** In the main body, Module 3 (`mod:mvba`)'s Agreement now
  reads `entries(B) = entries(B')`. That is exactly what this development
  already instantiates.

**What it means for the claims.**

* **Safety: no change.** `Mvba ⊨ MVBASafety`, the agreement proof and the
  pins stand as they are. Each protocol change falls into one of three
  cases: the model does not model it (crash recovery, `Recover`), the
  monotone network already over-approximates it, or the model's action
  split already covers it.
* **The contract: prose only.** The class needs no change of statement. At
  its one instance, the `agreement` field now *is* the published sentence,
  so only prose in [Interfaces.lean](../Cadence/Interfaces.lean) moves.
* **Liveness: one finding.** The new termination argument states the
  paper's network explicitly. Against it, the timed claim's timing premise
  `Mvba.Admissible` is **stronger than that network in three places**
  (§11.3, C16). The theorem is still true, and its premises are still
  jointly satisfiable (the witness is unaffected). But as with the halting
  finding of PR #42, it says nothing about some runs the supplement
  produces. This is the one item that needs design work.

**Sizing, in one line.** A **leg of its own**, on the liveness side only.
No re-solve and no model change are needed, and the interface changed in
prose only. The correctness argument did change, and by this plan's own
criterion that makes it a leg (§11.4).

##### 11.1 Anchors: renamed, removed, new

The check was mechanical, over two ranges: the MVBA algorithm's source,
and the supplement from Supplement, Section 1 (`sec:mvba-instantiation`)
to the end of Supplement, Section 1.3 (`subsec:mvba-correctness`) ([PaperAlignment.md](PaperAlignment.md)
§7 has the method).

* **Removed.**
  * `line:mvba:td-decide`: `TryDecide` no longer exists (C2).
  * `line:mvba:hp-pool`: the `Pool` cache is gone (C3).
  * `line:mvba:tfp-commit` sat inside a LaTeX comment and was never a
    rendered anchor.

  No correctness anchor was removed: all seventeen listed in §0 still
  resolve.
* **Renamed.** None. Supplement, Corollary 1 (`cor:mvba-recovery-termination`) keeps its label,
  gains a new title ("Eventual termination under recovery") and has a
  sharper statement (C18).
* **New.**
  * The block Supplement, Algorithm 1 (`alg:mvba-cont3`).
  * The line labels Supplement, Algorithm 1, line 12 (`line:mvba:leader-guard`), Supplement, Algorithm 1, line 79 (`line:mvba:decide-guard`),
    Supplement, Algorithm 1, line 49 (`line:mvba:restart-guard`), Supplement, Algorithm 1, line 40 (`line:mvba:viewtc-retx`) and
    Supplement, Algorithm 1, line 98 (`line:mvba:sv-forward`).
  * The results Supplement, Remark 2 (`rem:execution-model`), Supplement, Lemma 13 (`lem:decision-propagation`),
    Supplement, Lemma 14 (`lem:view-sync`), Supplement, Lemma 15 (`lem:convergence`) and Supplement, Lemma 16 (`lem:good-view`).
  * Outside the section, Supplement, Section 10.3 (`sec:reliable-delivery`) now contains protocol
    text: a "Future-view message retention" paragraph, which the MVBA
    liveness argument cites. Before, it only pointed to an external design
    note.
* **Moved between blocks.** `HandleTimeout`, `TryFormCommitQC`,
  `TrySendCommit` and `SyncView` are now in Supplement, Algorithm 1 (`alg:mvba-cont3`). The timeout
  and restart rules, `HandleProposal` and `TryFormPrepQC` are in
  Supplement, Algorithm 1 (`alg:mvba-cont2`). The model cites `line:mvba:*` labels without their
  block, so those citations survive. What goes stale is the model header's
  "three algorithm blocks".

**Where the removed labels are cited today.**

* `line:mvba:td-decide`:
  * [Mvba.lean](../Cadence/Mvba.lean): the header item "A decided validator
    halts", and the docstring of its `decide` action;
  * `Mvba.Active`'s docstring ([Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean));
  * [Bounds.md](Bounds.md) §6.3.2, [PaperAlignment.md](PaperAlignment.md)
    §4 item 4, and §2.4 above.
* `Pool`: the Mvba.lean header's "Not modelled" item.
* `TryDecide`: the `decide` docstring and §2.4.

##### 11.2 How to read the change list

Each entry gives what changed (by label), its class, and its consequence.
The classes are the task's five:

* **editorial** — no model effect;
* **anchor** — citations only;
* **protocol** — guards, updates, messages, the view or timer discipline,
  the lock;
* **argument** — a lemma or constant the proofs mirror;
* **interface** — Module 3 (`mod:mvba`), which reaches the Chorus family through
  Interfaces.lean.

"No re-solve" means no VC statement moves: the Veil families replay warm,
the cheap rung closes the frame cells, and neither `#veil_status Mvba` nor
`#veil_status Chorus` moves.

##### 11.3 The change list

**Interface (the main body)**

* **C1. Module 3 (`mod:mvba`) Agreement now reads `entries(B) = entries(B')`**
  (paper commit `d598c5a`; arXiv v2 reads `B = B'`).
  *Class: interface, with no statement change.*
  `MVBASafety.agreement` says `v = v'` over the class's `value`, and the
  one instance sets `value` to the entry vector (§1.2). So at that
  instance, the field is now the published sentence word for word. Before,
  it was the weaker of the two forms, and
  [PaperAlignment.md](PaperAlignment.md) §4 item 3 argued that the gap was
  sound.

  *Consequence:* the `agreement` docstring and the Module 3 (`mod:mvba`) block in
  [Interfaces.lean](../Cadence/Interfaces.lean) should say this. The edit
  is prose only, but the Chorus family imports the file, so the family
  rebuilds warm; no Chorus VC changes. The (A-mvba) clean-up from
  [TODO.md](TODO.md) § Liveness goes into the same edit (§11.5 stage 1).
  **Resolves** PaperAlignment §4 item 3 upstream, pending the next arXiv
  version.

  The supplement's new paragraph "Agreement and Integrity over entries"
  (Supplement, Section 1.2 (`subsec:mvba-protocol`)) also restates **Integrity**: "all decision outputs of a correct validator
  carry the same entry vector, and redelivery … is permitted". It says the
  main-body module "should be revised to these forms", but only Agreement
  was. Nothing follows for the model. At the entry-vector instance, and
  over a monotone `decided`, `integrity` already is the entries form. This
  is recorded as a paper-side observation (PaperAlignment §7.4).

**Anchors and editorial**

* **C2. `TryDecide` is merged into `Decide`** (Supplement, Algorithm 1 (`alg:mvba-cont3`)). `Decide`
  is reached from `TryFormCommitQC` and from the transferred-certificate
  handler (Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)). Its one `Recover` continuation
  re-checks only that the instance has not been abandoned
  (Supplement, Algorithm 1, line 79 (`line:mvba:decide-guard`)). `line:mvba:td-decide` is gone.
  *Class: anchor.*
  The semantics are the same for the model. A certificate of any view is
  accepted, the validator decides once, and `Recover` is the identity. So
  the model's single `decide` action still stands for every path.

  *Consequence:* in the places listed in §11.1, re-cite
  `line:mvba:td-decide` as "`Decide` (Supplement, Algorithm 1 (`alg:mvba-cont3`)), reached from
  Supplement, Algorithm 1, line 31 (`line:mvba:qc-decide`)". `Decide`'s last line, `decide(x, CommitQC);
  abandon()`, has no label, so cite the procedure.
* **C3. `Pool` is gone.** Accepted meta-blocks go to a durable set
  `Accepted_i`, registered at Supplement, Algorithm 1, line 57 (`line:mvba:hp-record`) before the `Prepare`
  is sent. A new stated invariant says that a `Prepare` on `e` implies
  `Accepted_i` holds a valid `x` with `entries(x) = e`.
  *Class: editorial*, since the model has neither.

  *Consequence:* the header's "Not modelled" item names `Accepted_i` (the
  recovery layer's registration) in place of the `Pool` cache. The new
  invariant is the supplement's counterpart of the model's
  `honest_prepare_accepted` with `accepted_valid`, and the header may cite
  it.
* **C4. A fourth algorithm block, Supplement, Algorithm 1 (`alg:mvba-cont3`)**, with the procedures
  redistributed as §11.1 describes. *Class: anchor.*

  *Consequence:* "three algorithm blocks" becomes four in three places:
  the Mvba.lean header, §0 above, and PaperAlignment §4.
* **C5. Supplement, Remark 2 (`rem:execution-model`) and the execution-model paragraph.** Handler
  segments run without interleaving. `Recover` is the only suspension
  point, and each of its three continuations re-checks a guard
  (Supplement, Algorithm 1, line 12 (`line:mvba:leader-guard`), Supplement, Algorithm 1, line 79 (`line:mvba:decide-guard`),
  Supplement, Algorithm 1, line 49 (`line:mvba:restart-guard`)). *Class: editorial*: with `Recover` the
  identity, every continuation guard is vacuous in the model.

  It is still worth citing. It is the supplement's own justification for
  reasoning about atomic handler segments, which is what the model's
  one-action-per-handler structure does. *Consequence:* one sentence in
  the header's "Abstractions".
* **C6. Timer and signature wording.** *Class: editorial.* The changes:
  * the timeout rule now names the fixed `T`;
  * the `Timeout` signature is written out;
  * `highPrepQC` filters by slot, and the `Pre-Prepare` check reads
    "valid meta-block *for slot `s`*";
  * a timeout whose carried certificate fails to verify is still valid,
    but contributes `⊥` to `highPrepQC`.

  The model is one instance, so the slot filters are vacuous. The last
  point is already covered by the header's abstraction "a timeout carrying
  a certificate of view above its own": honest senders carry only
  certificates that exist, and a Byzantine sender may send the `⊥` form.

**Protocol**

* **C7. `propose` enters the view justified by the highest retained
  timeout certificate**, and does not first run a view-1 leader action
  (the Interface line of Supplement, Algorithm 1 (`alg:mvba`); Supplement, Section 1.2 (`subsec:mvba-protocol`), first
  paragraph). *Class: protocol.*
  The model's `propose` enters `vord.zero`, and `sync_view` advances in a
  separate step. The faithful rule would need "no higher certificate is
  retained", which is a negative read of `msg_tc`, and the monotone-network
  contract forbids those ([ChorusDesign.md](ChorusDesign.md) §3.1.1). So
  the model keeps its over-approximation: a late view-1 leader may still
  send its view-1 `Pre-Prepare` (`leader_propose_first`) before it syncs,
  where the supplement suppresses that send. The extra behaviour is
  neutral for safety, and no liveness argument uses it.

  *Consequence:* one header sentence. Not a model change.
* **C8. A self-formed timeout certificate now goes through `SyncView`.**
  Supplement, Algorithm 1, line 85 (`line:mvba:ht-advance`) reads: "`≥ 2f+1`, and `TC` not already formed;
  form it; `SyncView(TC)`". At the pin the advance was inline and did not
  adopt the certificate's `highPrepQC`. Now the forming validator adopts
  and forwards like any receiver. *Class: protocol*, already covered.
  The model separates assembly (`form_tc_lock`, `form_tc_nolock`) from the
  advance (`sync_view`, `sync_view_adopt`). The header's "the plain
  `sync_view` does not adopt, which only adds behaviours" stays true.

  *Consequence:* none beyond re-reading that header sentence.
* **C9. Forwarding and retransmission.** *Class: protocol.* The new rules:
  * `SyncView` forwards the certificate it processes
    (Supplement, Algorithm 1, line 98 (`line:mvba:sv-forward`));
  * while in a view `v > 1` and not abandoned, a validator re-broadcasts
    `ViewTC_i` every `ρ` (Supplement, Algorithm 1, line 40 (`line:mvba:viewtc-retx`));
  * a timed-out validator re-broadcasts its `Timeout` every `ρ` until it
    advances;
  * a view-advancing certificate is processed on arrival.

  All of this is neutral for safety. It adds no new message kind, and the
  monotone network already keeps every sent message available. For
  liveness, these rules are what implement the model's delivery premise
  for timeouts and certificates. *Consequence:* C16 (N1).
* **C10. One-view retention** (the Convention of Supplement, Algorithm 1 (`alg:mvba`);
  Supplement, Section 10.3 (`sec:reliable-delivery`), "Future-view message retention"). Messages of a
  lower view are discarded. Messages of the next view are retained.
  Messages of farther views *may* be discarded: retaining them is an
  optional implementation choice. *Class: protocol.*
  Neutral for safety, since the model over-approximates. For liveness, the
  model in effect retains everything. *Consequence:* C16 (N2).
* **C11. The halt after deciding still follows the supplement, and the
  supplement's own proof now relies on it.** *Class: protocol, unchanged in
  effect.* The halt is visible in four places:
  * `Decide` and the restart path both end in `decide(…); abandon()`;
  * the timeout still fires only when there is "no decision in view `v`"
    (Supplement, Algorithm 1, line 36 (`line:mvba:timeout-send`));
  * the `ViewTC_i` retransmission runs only while the instance is not
    abandoned;
  * the termination proof limits its synchronisation lemmas to the prefix
    before any correct validator learns a commit certificate ("no correct
    validator has decided or abandoned"), and Supplement, Lemma 13 (`lem:decision-propagation`)
    takes over after that.

  This **confirms** PR #42's halting rule against the newer revision.
  *Consequence:* citations only (C2).

**Correctness argument and constants**

* **C12. The safety lemmas keep their statements.** These twelve are
  unchanged up to whitespace: Supplement, Remark 1 (`rem:signature-separation`),
  Supplement, Lemma 1 (`lem:vote-uniqueness`), Supplement, Lemma 2 (`lem:commit-provenance`), Supplement, Lemma 3 (`lem:cert-uniqueness`),
  Supplement, Lemma 4 (`lem:lock-formation`), Supplement, Lemma 6 (`lem:commit-availability`),
  Supplement, Lemma 7 (`lem:timeout-closes-view`), Supplement, Lemma 8 (`lem:lock-persistence`), Supplement, Theorem 1 (`thm:agreement`),
  Supplement, Lemma 9 (`lem:external-validity`), Supplement, Lemma 10 (`lem:reproposal`) and Supplement, Lemma 11 (`lem:lock-availability`).
  Supplement, Remark 3 (`rem:lock-monotonicity`) adds "if `p_i` is in view `v`, the view of
  `PrepQC_i` is at most `v`", which is the model's
  `local_prepqc_within_entered`. The proofs gained crash-recovery cases,
  and the model does not model crashes. *Class: editorial* for the model.

  *Consequence:* none. §2.6's table stands.
* **C13. The view timeout is fixed: `T := Δ_R + 4Δ + max{Δ, Δ_sync}`**
  (Supplement, Section 1.2 (`subsec:mvba-protocol`), "Views, leaders, and
  timing parameters"). The termination setting says
  "the view timeout is the fixed `T`", and the backoff sentence is
  deleted. *Class: argument.*
  At the pin, the text said the timeout "exceeds
  `Δ_R + 3Δ + max{Δ, Δ_sync}`", and it allowed backoff. The model's
  schedule already admits a fixed value as a special case: `vL` is the
  first view and `τ` is constant. `T` clears the chain latency, because
  `T − Lcert = Δ_R + Δ` at `δ = 0`. And `Schedule.fixedNat` (Δ = 1,
  Δ_sync = 0, τ = 5) is exactly `T` at `Δ_R = 0`, so the witness already
  runs at the paper's timeout.

  **Resolves** the capped-backoff finding upstream
  ([Bounds.md](Bounds.md) §6.2.3 Finding 1; PaperAlignment §6), with one
  residue: the Supplement, Section 10.1 (`sec:timing-constants`) stub still lists "the MVBA view
  timeout and its backoff policy".

  *Consequence:* (S-cap) and (S-ramp) stay. They are strictly more
  general, and they still describe capped backoff if an implementation
  wants it. Bounds.md §6.2.3 gets three wording changes: it quotes the new
  sentence, marks Finding 1 resolved upstream at `eb1bb51`, and presents
  the schedule as the supplement's fixed `T` plus a harmless
  generalisation. No Lean statement changes. The module docstring of
  Schedule.lean says the backoff remark "is incompatible"; that moves to
  the past tense.
* **C14. Supplement, Theorem 2 (`thm:termination`) is restructured** into a *termination
  setting* and four lemmas. *Class: argument.*

  The termination setting assumes:
  * `t₀ = max(t_last, GST)`, and every correct validator is operational
    from `t₀` on;
  * no correct validator is abandoned by its caller before deciding;
  * a message *sent at or after GST* is delivered within `Δ`;
  * the timeout is the fixed `T`, and the retransmission interval is
    `ρ_mvba = O(Δ)` (the schedule's field `ρ`);
  * the composing layer delivers a decided `CommitQC` to every undecided
    validator within `ρ + Δ`.

  The four lemmas:
  * Supplement, Lemma 13 (`lem:decision-propagation`) (C15);
  * Supplement, Lemma 14 (`lem:view-sync`): views first entered after `t₀` are synchronised
    within `Δ`, and nobody leaves them before `T`;
  * Supplement, Lemma 15 (`lem:convergence`): the hop bound `τ_{w+1} ≤ τ_w + 2Δ + T`, plus a
    retention clause from view `V + 2` on;
  * Supplement, Lemma 16 (`lem:good-view`).

  Supplement, Lemma 12 (`lem:proposability`) becomes quantitative, in `Δ_R`. The bound, in closed
  form, is a decision by
  `t₀ + ρ + 4Δ + max{T, ρ} + T + f(2Δ + T) + T`, plus the decision
  propagation `ρ + Δ + 2Δ_R`.

  Compared milestone by milestone with [Bounds.md](Bounds.md) §6.2.6, at
  `δ = 0` and `Δ_R = 0`:
  * **The good view.** Supplement, Lemma 16 (`lem:good-view`) gives
    `t*_w − τ_w = Δ_R + 3Δ + max{Δ, Δ_sync}`. That is `Lcert`, so
    `Mvba.Lcert_paper` still holds, and it now has a named lemma to cite.
  * **A burnt view.** `τ_{w+1} ≤ τ_w + 2Δ + T` is `Schedule.burn`.
  * **The start and the end** differ; C16 explains why. The supplement
    pays `ρ` to reach the highest view, gives up views `V` and `V + 1` as
    possibly unproductive, and pays the transfer cost of a certificate that
    others learned. The model pays one `Δ` hop at the start, may use
    `V + 1` as its good view, and pays `δ` for the final `decide`.

  The *statement* of Supplement, Theorem 2 (`thm:termination`) changes only in its framing:
  "within `O(fΔ)` of `t₀`", where `t₀ = max(t_last, GST)` is the model's
  `max(t, gst)`.

  *Consequence:* the good-view and burnt-view constants, and
  `Mvba.Lcert_paper`, are cited against Supplement, Lemma 16 (`lem:good-view`) and
  Supplement, Lemma 15 (`lem:convergence`) instead of the old proof prose. The rest is C16.
* **C15. Decision propagation is now a lemma with its own cost**
  (Supplement, Lemma 13 (`lem:decision-propagation`); Supplement, Section 1.2 (`subsec:mvba-protocol`), "Decision output and handoff").
  *Class: argument.* A validator that learns a `CommitQC` decides within
  `Δ_R`. Every other validator decides within `2Δ_R + Δ`, or by
  `t₀ + ρ + Δ + 2Δ_R` if the certificate was learned before `t₀`. The
  certificate travels by Chorus's broadcast plus the composing layer's
  delivery guarantee.

  *Consequence:* C16 (N3). On the Chorus side this is a composing-layer
  obligation, stated in the MVBA's terms, and it is recorded for the timed
  Chorus leg (§11.5 stage 5).

  *Closed in R8 (2026-09-30).* The handoff is modelled: `MVBASafety` carries
  the supplement's strengthened interface (`decide` exposes its
  certificate; a transferred valid certificate is accepted), at the
  instance `decide` is that input, and Chorus's `accept_mvba_commitqc` is
  the composing layer's step. The obligation left `BoundedJustice` as the
  caller's clause `Mvba.Relayed` (verbatim), untimed as (F-relay), and both
  are derived inside Cadence (`Chorus.relayed_of_timedJustice`,
  `Chorus.fRelay_of_fJustice`). [Bounds.md](Bounds.md) §6.4.2 has the
  design.
* **C16. The finding: in three places the timed premise assumes more than
  the paper's network provides.** *Class: argument; a fidelity finding of
  the same class as PR #42's.*
  `Mvba.BoundedJustice` holds every fair label to its hop bound, measured
  from `max(clk N, gst)`, regardless of the message's history. The new
  termination setting says what the network actually guarantees, and in
  three places that is less.

  * **(N1) Messages sent before GST.** The supplement guarantees delivery
    within `Δ` only for messages *sent at or after GST*. It retransmits
    only the recovery classes: `Timeout`, `ViewTC_i`, and the `CommitQC`
    through the composing layer. A `Pre-Prepare`, `Prepare` or `Commit`
    sent before GST may be lost for good. The model's clause, by contrast,
    requires such a message, if it can still be consumed at GST, to be
    consumed by `gst + Δ`. For the retransmitted classes, the model's
    single `Δ` has to be read as covering `ρ + Δ`.
  * **(N2) One-view retention.** A `Pre-Prepare` or vote of view `w` that
    reaches a validator two views behind may be discarded (C10). In the
    model, `handle_preprepare` becomes enabled once the validator catches
    up, and the clause then demands that it fire. The supplement copes by
    giving up views `V` and `V + 1`: its retention clause
    (Supplement, Lemma 15 (`lem:convergence`)) holds only from `V + 2`. The model's assembly may
    instead pick `M + 1` as its good view.
  * **(N3) The transfer of a decision.** *(Superseded in R8: `decide` is
    the caller's input and its timing the caller's clause `Relayed`, see
    C15.)* The hop table `Mvba.hop` classes
    `decide` as a local step (`δ`). By the table's own rule, "a step whose
    guard consumes … a certificate assembled from others' signatures" is
    a network step. A validator that did not form the certificate itself
    gets it only through C15's transfer path, at a cost of `Δ` plus `ρ`
    and `Δ_R`. The table's check against the paper ("at `δ = 0` the
    latency is the paper's constant") only exercises the good view, where
    every correct validator forms the certificate locally, so it could not
    catch this.

  **What this does and does not affect.** The theorem is true, and its
  premises are jointly satisfiable. The witness runs everything at clock
  0 = `gst`, in the first view, with nobody lagging, so it meets the
  stronger premise and the weaker one alike. But a supplement run of any
  of three kinds is not admissible in the model, so the timed claim says
  nothing about it: a run that loses a `Pre-Prepare` sent before GST, one
  that discards a far-future message, or one in which a certificate has to
  travel.

  **None of the three is a misreading of the pinned text.** At `026dc8b`:
  * Supplement, Section 10.3 (`sec:reliable-delivery`) was a pointer to an external design note;
  * the only discard rule was for *lower* views (Supplement, Algorithm 1, line 85 (`line:mvba:ht-advance`));
  * the termination proof argued only the good view.

  The new text is what makes the three differences visible.

  **The untimed premise.** `Mvba.FJustice` has the (N1)/(N2) shape as
  well. Weak fairness on `handle_preprepare` models a reliable, fully
  retaining link. That is the standard reading of eventual delivery, but
  the supplement's links are not reliable before GST and do not retain
  everything. `Chorus.MvbaAdmissible` is defined as
  `Mvba.FJustice ∧ Mvba.AViewSync ∧ Mvba.FAvail` of the projected run. So
  whatever is decided for the untimed premise reaches `Chorus.termination`
  without being restated anywhere.

  *Consequence:* §11.5 stages 3 and 4. Until then, the ledger line
  "(Δ-justice) … post-GST delivery within `Δ`"
  ([Bounds.md](Bounds.md) §6.2.4) overstates how faithful the premise is.
  That line, and §6.3's "The run is admissible", each get a sentence
  naming (N1)–(N3).

**Not modelled, or on the Chorus side**

* **C17. Crash-recovery contract.** It is rewritten:
  * accepted meta-blocks live in `Accepted_i`, which is restored on
    restart;
  * `Recover` is bounded by `Δ_R` "for calls initiated after that point
    and calls already outstanding at it";
  * there is a restart guard, Supplement, Algorithm 1, line 49 (`line:mvba:restart-guard`).

  The availability paragraphs are reworded, but Supplement, Lemma 5 (`lem:avail-progress`) and
  (Δ-avail) are unchanged. *Class: editorial* for the model, which models
  neither crashes nor `Recover`.
* **C18. Supplement, Corollary 1 (`cor:mvba-recovery-termination`)** now requires that every correct
  validator invokes `propose` and that none is abandoned by its caller
  before deciding. It also says "no latency bound is claimed in this
  setting". *Class: editorial.* The header still lists it as not modelled.
* **C19. Chorus-side sentences in the MVBA section.** *Class: editorial*
  for the MVBA model. There are two:
  * "the concrete MVBA's internal `Commit` round also serves as the
    fallback commitment-certification round" ("Decision output and
    handoff"). This bears on the row "the finalize wait moves outside
    consensus" in [PaperAlignment.md](PaperAlignment.md) §3, and on
    Chorus's own fallback commit round;
  * the fast-path proposition now requires Chorus to persist `pathVote`
    before casting either vote. This is below the Chorus model's level of
    detail, since that model has no crashes.

  Neither touches the MVBA model. Both are recorded for the Chorus
  alignment re-check (PaperAlignment §7.3).

##### 11.4 Sizing

Against the three sizes this step was asked to choose from:

* **Not a small edit.** Anchors and comments make up most of the list
  (C2–C6, C11, C17, C18). But the correctness argument changed (C13–C16),
  and so did the interface (C1).
* **Not a contained model change.** No entry calls for a change to the
  guards, updates or invariants of [Mvba.lean](../Cadence/Mvba.lean). The
  faithful form of C7 would break the monotone-network contract, and
  C8–C10 are already covered. So nothing needs to be re-solved:
  * `#veil_status Mvba` does not move;
  * the pin of [Mvba/NoLock.lean](../Cadence/Mvba/NoLock.lean) is
    untouched;
  * nothing under `Mvba/Proofs/` changes.
* **A leg of its own, on the liveness side.** C16 changes the timed
  claim's premise set. The files affected:
  * [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean): the hop table, a
    `ρ` constant, and the scoping of `BoundedJustice`;
  * [Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean):
    the assembly skips two views;
  * `Schedule.ℓ`, and with it the `ℓ` of `Mvba.mvbaTemporal`;
  * [Mvba/Witness.lean](../Cadence/Mvba/Witness.lean), and the ledger.

  If the untimed premise is refined too, the leg also reaches
  [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) and its consumers.
  C1 touches [Interfaces.lean](../Cadence/Interfaces.lean), in prose only.

**Every consequence on the Chorus side:**

* the prose edit of [Interfaces.lean](../Cadence/Interfaces.lean) (C1,
  with the (A-mvba) clean-up). This is a warm rebuild of the Chorus
  family.
* `Chorus.termination`
  ([Chorus/Termination.lean](../Cadence/Chorus/Termination.lean)) and its
  premise `Chorus.MvbaAdmissible`, *only if* stage 4 changes
  `Mvba.FJustice` or `Mvba.AViewSync`. The proof applies
  `Mvba.termination` to the projected run, so a change in the premises'
  shape reaches exactly the step that supplies them. The Chorus
  non-vacuity item in [TODO.md](TODO.md) § Liveness then reads the new
  premise.
* the timed Chorus claim, not yet started. It inherits the refined
  `Mvba.bounded_termination` and the transfer cost of C15.
* the Chorus alignment re-check of the main-body drift that turned up
  during this review (PaperAlignment §7.3). This is separate from the MVBA
  upgrade.

##### 11.5 Plan for step 5b, in order

Each stage is its own commit, and the work can stop after any of them.
Stages 1 and 2 are cheap and move the pin. Stages 3 and 4 are the liveness
work. Stage 5 records the result.

1. **Done** (2026-09-29, folded into the Chorus participation edit,
   [Bounds.md](Bounds.md) §6.4.6 S1, as that plan asked: one Interfaces.lean
   edit and one Chorus-family re-solve). The Module 3 (`mod:mvba`) block and the
   `agreement` docstring say the three things below. The
   Module 1 (`mod:slotconsensus`) `termination` row names `Chorus.termination` and its
   five premises, with the timed field still open. The (A-mvba) mentions in
   Chorus.lean's liveness section and in FallbackReceipt.lean's header are
   aligned. The check changed with the bundling: the Chorus family re-solved
   cold, because the same edit moved every Chorus VC statement, and the
   `#veil_status Chorus` pin moved with the model. The Mvba pins did not
   move. The original plan follows.

   **Contract prose: one edit of [Interfaces.lean](../Cadence/Interfaces.lean).**
   The Module 3 (`mod:mvba`) block and the `agreement` docstring should say three
   things:
   * the paper's module now states Agreement over `entries` (paper commit
     `d598c5a`, which is after v2);
   * the one instance sets `value` to the entry vector;
   * so the field is the published sentence.

   Bundle into the same edit the (A-mvba) prose that
   [TODO.md](TODO.md) § Liveness leaves for this file. That is the
   `termination` row of the Module 1 (`mod:slotconsensus`) obligation table, which
   still reads "**not proven**: Chorus's fair-progress layer +
   (F-justice)/(F-byz)/(A-mvba)". It becomes `Chorus.termination` and its
   three premises, with the timed field still open. If it can be arranged,
   let the same Chorus-family rebuild carry the (A-mvba) mentions in the
   liveness section of Chorus.lean, which the TODO bundles with "the next
   change that touches the file".

   *Check:* a warm build of the Chorus family. Every `#veil_status` and
   axiom pin stays unchanged, and nothing re-solves, since no VC statement
   moves.
2. **Move the pin to `eb1bb51`: comments and citations only.**

   In the header of [Mvba.lean](../Cadence/Mvba.lean):
   * the pin paragraph: record the move, and the `b838e17` re-check the
     way it is recorded now;
   * four algorithm blocks instead of three;
   * `Decide` in place of `TryDecide` and `line:mvba:td-decide`;
   * `Accepted_i` in place of `Pool`;
   * a sentence on Supplement, Remark 2 (`rem:execution-model`) (C5) and one on the
     over-approximation of C7.

   Elsewhere in the Lean files: the `decide` docstring, `Mvba.Active`'s
   docstring, and the backoff sentence of Schedule.lean (C13).

   In the docs:
   * §0 and §2.4 here;
   * [Bounds.md](Bounds.md) §6.2.3 (Finding 1 resolved upstream, the new
     `T` quoted) and §6.3.2 (the new citation);
   * [PaperAlignment.md](PaperAlignment.md) §4.

   *Check:* the model file's comments change but no VC statement does, so
   the Mvba family replays warm and `#veil_status Mvba` does not move.
   Afterwards, grep for `td-decide`, `TryDecide` and `Pool`: they should
   remain only in [History.md](History.md).
3. **Refine the timed premise to the paper's network (C16).**

   This needs a design decision first, taken with Lars. The recommendation
   is to refine the premise rather than document the gap, for two
   reasons. This repository's rule is that the claim surface outranks
   proof simplicity. And PR #42 set the precedent: there, the premise side
   (the model) was changed so that the theorem speaks about the
   supplement's own runs.

   The proposed shape, in [Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean):
   * **(N3)** Reclassify `decide` as a network step. That is one line in
     `Mvba.hop`, and `hop_isSome_iff` is unaffected. The last term of
     `Schedule.ℓ` becomes a network hop.
   * **(N1)** Add `ρ` to `Schedule`, with `0 ≤ ρ`. Hold the retransmitted
     classes (`form_tc_*`, `sync_view*`, `decide`) to `Δ + ρ`, measured
     from `max(clk N, gst)`. Hold the other classes (`handle_preprepare*`,
     `form_prepqc`, `form_commitqc`) to `Δ`, but only for obligations
     whose message first appears at a clock `≥ gst`. "First appears" can
     be defined over the run as the first index at which the network
     relation holds, so no model ghost is needed.
   * **(N2)** Restrict the view-scoped consumption clauses further, to
     receivers that had already entered a view `≥ w − 1` when the view-`w`
     message first appeared. That is the retention the supplement
     guarantees.

   **Open, for the design step:** whether (N1) and (N2) are better stated
   per label, as above, or by restricting the whole clause to views first
   entered after `max(t, gst)`, which is closer to the supplement's "fresh
   view". The per-label form is more faithful; the per-view form is
   simpler to state.

   **Decided (2026-09-29, step 5b): per label.** Both forms were written
   as Lean definitions and compared. The per-view form ("a view-`w` label
   is held to `Δ` once `w − 1` is fresh") assumes a *consequence* of the
   protocol: that nobody is two views behind when a fresh view's messages
   arrive. The supplement derives that in Supplement, Lemma 15 (`lem:convergence`) from `T > Δ`,
   and the model's schedule allows views below the ramp whose budget is
   not above `Δ`, so there the per-view premise would assume what the
   paper's network does not give. It also cannot say who sent a message,
   and it names a protocol quantity (the first entry into a view) where
   every other clause names only environment events. The per-label form
   states each rule of the network as the supplement writes it, so an
   auditor can check it sentence by sentence. The two are not close, so
   the decision did not wait for a review round.

   Writing the per-label form out showed that C16's three items do not
   quite cover the paper's network. The form taken also says three things
   C16 did not:

   * **Correct senders.** The supplement guarantees delivery only between
     correct validators. The old clause also held the correct validators
     to handling a Byzantine leader's `Pre-Prepare`, and to assembling
     certificates from Byzantine votes, within `Δ`. Now a first delivery
     is owed only for a correct leader's `Pre-Prepare` and for a quorum of
     correct validators' votes.
   * **Lower views are discarded** (C10's first half). An assembly is
     owed only while its forming validator has not moved past the view.
   * **Retransmission stops.** Timeouts are retransmitted by validators
     still in the view, `ViewTC_i` by active validators, and a decided
     `CommitQC` by the composing layer. Each retransmission clause says
     so.

   (N4), prepare certificates do not travel, was open here and is
   **closed in R3**: `adopt_prepqc i v e q` forms the validator's own
   certificate from a supermajority `q` of `Prepare`s it received (the
   supplement's `TryFormPrepQC`), a network hop with a first-delivery
   clause. It was done together with the fairness clean-up, in one Mvba
   re-solve; see [Bounds.md](Bounds.md) §6.2.4.

   **R4 (2026-09-30), the other two assemblies.** Commit and timeout
   certificates follow the same pattern since R4: `form_own_commitqc i v e q`
   (the supplement's `TryFormCommitQC` and `Decide`, guarded on
   `DecidedQC_i = ⊥`, i.e. `∀ E, ¬ decided i E`) and `form_own_tc_lock` /
   `form_own_tc_nolock` (`HandleTimeout`, "upon first collecting `2f+1`
   valid timeout messages", with the local record `tc_formed i v`). Both
   are network hops with first-delivery clauses; the `timeouts`
   retransmission clause now names the validator that forms the
   certificate. The four anonymous assemblies left the hop table and
   carry no fairness (`AssemblyLabel`). `Lcert` and `Schedule.ℓ` are
   unchanged: the good view's last hop now forms the certificate and a
   decision together, and the others' decisions were already charged to
   the transfer term. [Bounds.md](Bounds.md) §6.4.7 has the record.
4. **Re-prove the bound and re-check the witness against the refined
   premise.**
   * **The good view.** In
     [Mvba/BoundedTermination.lean](../Cadence/Mvba/BoundedTermination.lean),
     choose it at or above `M + 2`, which is what the supplement charges.
     This needs the model's analogue of the retention clause of
     Supplement, Lemma 15 (`lem:convergence`): at `w`'s first entry, every correct validator is
     in `w − 1` or `w`. It follows from the existing `Synced` hop and
     `Mvba.entered_le_of_no_timeout`, provided view `w − 1`'s budget
     exceeds `Δ`. Check whether the ramp must then start one view earlier.
   * **The bound.** `Schedule.ℓ` gains two `burn` terms and the `ρ` terms,
     and stays `O(kΔ)`. The good-view lemma of
     [Mvba/Bound.lean](../Cadence/Mvba/Bound.lean) should need only its
     hop bounds re-read.
   * **(A-viewsync).** Check that `Mvba.aViewSync_of_sync` survives the
     scoping. Its "not too late" clause uses the timeout path, which is a
     retransmitted class. Its "not too early" clause uses the good view.
   * **The instance.** In
     [Mvba/Temporal.lean](../Cadence/Mvba/Temporal.lean),
     `Mvba.mvbaTemporal` takes the new `ℓ`, and `Schedule.fixedNat` gains
     `ρ`.
   * **The witness.** The run in
     [Mvba/Witness.lean](../Cadence/Mvba/Witness.lean) stays the same:
     nothing is sent before GST, nothing is discarded, and every validator
     forms the certificate itself. Only the value of `ℓ` and the hop of
     `decide` move.
   * **The untimed premise.** Decide whether `Mvba.FJustice` gets the (N2)
     restriction. (N1) has no untimed form, because the untimed model has
     no GST. If it does, the change flows through the chain of
     [Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean), then
     `Mvba.termination`, then `Chorus.MvbaAdmissible`, then the
     application in [Chorus/Termination.lean](../Cadence/Chorus/Termination.lean).

     The recommendation is to keep the untimed premise as it is and say so
     in the ledger. Weak fairness is the eventual-delivery reading, and
     (A-viewsync) is already a corollary of the timed premise. Keeping it
     leaves the Chorus proofs untouched.

   *Check:* the standard axiom trio on every changed declaration, and the
   `#guard_msgs` pins of Schedule.lean. The Veil families are untouched,
   so `lake build` of the plain-Lean files is enough, followed by one
   staged re-validation at the end.
5. **Record the result.**
   * [Bounds.md](Bounds.md) §6.2:
     * the "Paper" column of the per-seam table cites Supplement, Lemma 14 (`lem:view-sync`),
       Supplement, Lemma 15 (`lem:convergence`), Supplement, Lemma 13 (`lem:decision-propagation`) and
       Supplement, Section 10.3 (`sec:reliable-delivery`);
     * §6.2.6 gets the new milestones;
     * §6.3's ledger gets the admissibility line.
   * [PaperAlignment.md](PaperAlignment.md) §4 and §6.
   * The "Views" and "Abstractions" parts of the Mvba.lean header.
   * [TODO.md](TODO.md) § Liveness:
     * the `MvbaAdmissible` wording of the Chorus non-vacuity item, if
       stage 4 changed it;
     * a note for the timed Chorus leg that C15's transfer cost is its
       composing-layer obligation.
   * [History.md](History.md): a ledger row.

   The pinned `#veil_status` counts do not move in any stage.

   *Done (2026-09-29).* The result is recorded in the places listed. The
   Chorus non-vacuity item did not need rewording, since the untimed
   premise did not change. PaperAlignment §6 needed nothing new: its
   backoff item already carried the resolution. (N4) was left open here
   and is closed in R3 (model change: `adopt_prepqc` from the prepares,
   Mvba re-solve); [Bounds.md](Bounds.md) §6.2.4.

   *R8 (2026-09-30).* The note for the timed Chorus leg is discharged: the
   decision's transfer is Chorus's handoff step, and the MVBA's clause for
   it is derived (C15 above). Two consequences for the MVBA's own claims,
   neither touching the model file: `Mvba.FJustice` is owed only for
   correct senders (`Mvba.Owed`, [Bounds.md](Bounds.md) §6.4.2, F5), and
   (A-viewsync)'s second clause names a correct validator's decision. The
   pinned `#veil_status Mvba` does not move.
