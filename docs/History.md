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
| `Cadence/Interfaces.lean` | `SlotConsensus`/`ACS`/`Orchestrator` contract classes + obligation tables | plain Lean (no VCs) | ~2 s |
| `Cadence/Windows.lean` | `IsMedian`, `lowerMedian`, the median range lemma | plain Lean proofs, no sorries | ~1 s |
| `Cadence/Cadence.lean` | the pipelining glue: 4 actions, 4 safety + 18 invariants | 115 VCs ✅ + 2 `sat trace` ✅ + `#gen_theorems`, at **`veil.smt.trust false`** (every proof reconstructed and kernel-checked — since 2026-07-07) | ~60 s |
| `Cadence/Conductor.lean` | the orchestrator: 7 actions, 5 safety + 14 invariants | 160 VCs ✅ + 2 `sat trace` ✅ + `#gen_theorems`, at **`veil.smt.trust false`** (since 2026-07-10; one encoding-divergent attempt is covered by its alternative form) | ~60 s |
| `Cadence/Composition.lean` | `invariants_of_reachable` for both small models, the `Conductor ⊨ Orchestrator` instance, positional MCP Safety (`positional_log_safety`) | plain Lean over the persisted VC theorems — kernel-checked since 2026-07-10; axioms `#guard_msgs`-pinned to the three-axiom form | ~10 s |
| `Cadence/Chorus.lean` | per-slot consensus: 38 actions, 9 safety + 88 invariants | **model file** — elaborates the transition system and persists a 7 605-entry VC registry; runs no sweep | ~90 s |
| `Cadence/Chorus/Proofs/` ×39 | one file per action (+ `Init`): `#prove_action` re-creates that action's registered VC statements and persists fresh kernel-checked reconstructions as **real proofs**, plus the per-action preservation lemma. The 14 manual quorum-intersection cells are preproven theorems in these files, consumed after a statement check | 3 808 re-proofs (3 822 cells − 14 manual); retry ladder + alternative-encoding fallback built in | warm ~20–30 s per 6-file batch; cold minutes per file |
| `Cadence/Chorus/Certify.lean` | `#gen_composition`: `Chorus.invariants_of_reachable` (39 cases over the preservation lemmas) + `Chorus.reachable_<property>` ×97 | kernel-checked at emission; three-axiom `#guard_msgs` pin **and** the pinned `#veil_status Chorus` audit (3822/3822 real) | ~40 s (dominated by the audit walk) |
| `Cadence/Chorus/Compose.lean` | `Chorus.slotConsensus_instance` — decision vectors, agreement / slot-safety / proposal-inclusion fields | plain Lean; axiom-pinned to the three-axiom form | ~21 s |
| `Cadence/Chorus/Pigeonhole.lean` | the **evidence pigeonhole** (`ChorusDesign.md` §7, x = 0 branch) for every `n = 3f+1`: a supermajority of honest fallback entries yields `fb_quorum_pos ∨ fb_quorum_neg ∨ equiv_evidence` — formerly the liveness argument's one meta-level counting step | plain Lean (`two_cover` + the `reachable_*` projections); axiom-pinned | ~22 s |
| `Cadence/FallbackReceipt.lean` | the shipped receipt/propose layer: 9 actions, 1 safety + 20 invariants; discharges the (A-mvba) implementability seam | **model file** (registry, no sweep) + `#model_check` ✅ 23 975 states (`n=4, f=1`) | ~80 s |
| `Cadence/FallbackReceipt/Proofs/` ×10 + `Certify.lean` | the same family shape at small scale — the architecture's fast regression leg | 220 re-proofs + preservation lemmas + `#gen_composition`; three-axiom pin and the pinned `#veil_status` (220/220 real) | ~2–4 s per proof file warm |
| `Cadence/FallbackReceipt/Totality.lean` | build totality — the per-validator two-class pigeonhole, kernel-checked **for every `n = 3f+1`** (`two_cover` → `build_totality_of_complete` from `accepted_entries_complete` → `invariants_of_reachable` → `build_totality_of_reachable`); supersedes an earlier bounded `n = 4` argument | plain Lean over the reconstructed VC theorems; axiom-pinned | ~25 s |
| `Cadence/FallbackReceipt/PreFix.lean` | the *pre-fix* receipt rules; the §7.2 finding mechanically refuted | `#model_check` ❌ violation of `prefix_valid_by_construction` — the §7.2 counterexample trace, `#guard_msgs`-pinned (**the violation is the expected result**) | ~10 s |

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

Two readings that entries above have **superseded**, spelled out because
they were true when written and are false now: Chorus once persisted
`sorryAx` statement stubs (retired in 25 — a VC now either has a real proof
or is reported as missing by `#veil_status`), and the solver was once trusted
by default (retired in 16–17 — see "SMT trust mode" below).

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
