# History — how the verification reached its current state

**This is a historical ledger, not a status document.** For what is proven
now, and its trust base, read [`../README.md`](../README.md),
[`Architecture.md`](./Architecture.md) and the audit root
[`../Cadence.lean`](../Cadence.lean). Statements below describe the state at
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
