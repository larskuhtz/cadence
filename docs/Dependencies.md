# Dependencies

This project is a plain Lean 4 package with two direct dependencies:

| Dependency | Pin | Upstream |
|---|---|---|
| [Veil](https://github.com/larskuhtz/veil) | branch `port/integration` | [verse-lab/veil](https://github.com/verse-lab/veil) |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | tag `v4.32.0` | — |

Veil pins the verification tree — Loom (the monad-algebra layer Veil's
action semantics is built on), `lean-smt` (which bundles the cvc5 SMT solver
and its proof reconstruction) and `lean-auto` — at revisions this project
does not override. Upstream Veil dropped its Mathlib dependency, so Mathlib
is required here directly, for the `Finset` counting in
[Cadence/ByzQuorum.lean](../Cadence/ByzQuorum.lean) and
[Cadence/Primitives.lean](../Cadence/Primitives.lean); Mathlib's own pins
of batteries, aesop, Qq and ProofWidgets are the ones Veil requires, so the
two resolve to one tree and Mathlib's binary cache applies.
[lake-manifest.json](../lake-manifest.json) records the
exact revision of every package, so a checkout builds the same tree whatever
the branches those pins name have since moved to. The toolchain is pinned by
[lean-toolchain](../lean-toolchain) and fetched automatically by `elan`.

Nothing in this repository patches Veil. The changes this project needs are
in the fork, each on its own branch, documented there — this file only says
**which** capabilities are relied on and **why**, so that an auditor can see
what the verification pipeline is made of without reading the tool's source.

## Veil — `larskuhtz/veil @ port/integration`

`port/integration` is the union of the fork's `port/*` feature branches;
each of those is a self-contained change against Veil's `main`, kept separate
so it can be reviewed (and upstreamed) on its own. The branch inventory and
the dependency order between them live in the fork. Everything below is
*additive*: the fork changes no upstream verification semantics, and the
capabilities it adds are options and commands this project switches on.

Grouped by what they buy this project:

### 1. Making the verification fit on one machine at all

This is the load-bearing group: without it the Chorus proof does not build
on ordinary hardware, so the shape of this repository is a direct
consequence of it.

* **A persistent registry of verification conditions** (`veil.gen.vcRegistry`)
  and the cross-file commands that consume it — `#check_invariants <Module>`,
  `#check_action`, `#check_vc`, `#prove_action`, `#prove_vc`. A model file
  elaborates the transition system and records its VC *statements* in its
  `.olean`, running no solver; importing files re-create those statements and
  prove them. This is what lets the Chorus proofs — thousands of cells, counted by
  the `#veil_status` pin in [Chorus/Certify.lean](../Cadence/Chorus/Certify.lean)
  — be produced by one small, independent file per action
  ([Cadence/Chorus/Proofs/](../Cadence/Chorus/Proofs)) instead of in one Lean
  process, which would need to hold every reconstructed proof term in one
  environment at once, which does not fit in 32 GB. Statement identity is by
  construction: the proof files read the statements the model wrote, they do
  not restate them.
* **Composition emission** — `#gen_composition <Module>` assembles the
  per-action preservation lemmas into "every reachable state satisfies every
  invariant", plus one named projection per property, all through the kernel;
  `#gen_proof_files <Module>` scaffolds a proof-file family once.
* **`#veil_status <Module>`** — the audit command: it walks the registry
  against the environment and reports, per VC, whether a real,
  statement-matching, kernel-checked theorem is in scope, together with the
  axiom union over all of them. This project pins its output
  ([Cadence/Chorus/Certify.lean](../Cadence/Chorus/Certify.lean), [Cadence/FallbackReceipt/Certify.lean](../Cadence/FallbackReceipt/Certify.lean)), so
  the claim "no verification condition is stubbed" is re-derived on every
  build rather than asserted in prose. The audit walk is cheap
  and does not grow with the proofs: each olean stores the axiom set of every
  declaration it exports, computed when the olean is written, so collecting
  axioms for an imported constant is a lookup rather than a traversal of its
  proof term. `#veil_status Chorus` resolves every cell theorem across the
  proof-file oleans in a few seconds.
* **A code-generation switch for the model checker's scaffolding**
  (`veil.gen.modelCheckScaffolding`). The label-enumeration instances Veil
  derives for `#model_check` are `O(nᵏ)` in the number of actions; at Chorus's
  action count they exceed Lean's reducer, and `#gen_spec` cannot elaborate at
  all. Chorus turns the scaffolding off (it does not use `#model_check`); the
  receipt layer leaves it on and does.

### 2. Keeping the solver out of the trust base, affordably

* **A cheap non-SMT first rung in every invariant-preservation discharger**
  (`veil.vc.cheapRung`, on by default). Most cells in a
  Veil development are *frame* obligations — the action writes nothing the
  invariant reads — and after the local-WP bridge such a goal is already the
  invariant at the pre-state behind the action's guards, because the WP
  simplification has eliminated the untouched post-state fields. Nothing is
  then left to prove but the right conjunct. So each cell's discharger term
  is a two-rung ladder, `by first | veil_solve_frame <invariant> |
  veil_solve_wp`: the cheap branch is **tried, never predicted**, and a miss
  falls through to the solver. Both paths end in a kernel-checked term and no
  VC statement moves, so this changes *how* cells are proven, not what is
  proven — and for the cells it closes it takes cvc5, and cvc5's proof
  reconstruction, out of the loop entirely. On Chorus 96% of
  (action, property) pairs are footprint-disjoint, and measured here that is
  what the rung collects. Per Chorus proof file, `veil.report.cheapRung`'s
  hit rate against a cold A/B of the same file with the rung off (both arms
  at `veil.cache.proofs false`, one file at a time):

  | proof file | closed without a solver | rung on | rung off |
  |---|---|---|---|
  | `commit_assign_pos` | 90/101 (89%) | 23 s | 37 s |
  | `record_chunk` | 81/101 (80%) | 23 s | 35 s |
  | `fb_sign_neg` | 92/101 (91%) | 30 s | 41 s |
  | `vote` (the `foldBoolAtoms false` file) | 64/100 (64%) | 45 s | — |

  Three things are worth reading off it. The wall-clock saving understates
  the change: for four cells in five cvc5 is not called at all, and neither
  is its proof reconstruction, so what is left is a small kernel-checked
  projection instead of a reconstructed `unsat` derivation. The rung is
  *cheap when it loses* — the files where it collects least are the ones
  whose actions write most, which is exactly where the solver has real work
  to do. And these figures are a **floor** on what a real build saves: each
  arm above ran one file alone with every core free, which is the condition
  most favourable to the SMT arm, whose per-cell queries parallelise; in a
  staged build at `BATCH=3` or more the solver arm competes for the cores
  the cheap arm barely uses.

  One structural consequence, worth knowing before reading a build log: a
  cell the rung closes never reaches the **proof cache**, because nothing was
  searched for. After a cold re-validation the cache therefore holds only the
  solver-touched cells ([CLAUDE.md](../CLAUDE.md), "Build", has the
  measured sizes), and on the next build the rung's cells re-run the rung
  instead of replaying a stored term. So a warm build's output reads mostly
  ✅ rather than ♻, at a comparable per-cell cost (the rung's ~0.1 s against
  a folded cell's ~79 ms of replay), and the saving is concentrated on the
  **cold** path — the one CI runs.
  The rung's two halves are also what this project's manual cells are written
  with: **`unveil_local`**, the goal-only
  counterpart of `unveil` that leaves the ~100-conjunct invariant clump
  unsimplified (~0.4 s a cell against ~22 s — `unveil`'s closing `veil_simp
  at *` is what dominates at this clump size), and **`veil_inv_have h :=
  <invariant>`**, which projects a clump conjunct *by declaration name*, with
  the index derived from the module's own assembled `Invariants` and a
  conjunct-count check that fails loudly rather than projecting the wrong
  one. [Cadence/ProofPrelude.lean](../Cadence/ProofPrelude.lean) carries only this project's two option
  blocks.
* **Proof caching with kernel replay** (`veil.cache.proofs`,
  `veil.cache.kernelReplay`). Reconstructed proof terms are stored on disk
  keyed by the goal statement, and replayed on a later build. The cache never
  skips *checking* — a replayed proof is re-checked by the kernel before
  anything depends on it; it only skips proof *search*. Two consequences
  matter here: a re-validation run costs minutes instead of CPU-hours, and it
  is deterministic — no dependence on solver seeds or timeouts.
* **Seed retries and a slowest-VC report** — a timed-out query is retried
  with perturbed solver seeds before it is called a failure. Some Chorus
  cells sit close enough to the time budget that whether they solve depends
  on luck; the retry ladder is what makes an unattended build reproducible.
* **Verifier scaling fixes** — the verification-results pretty-printer runs
  outside the scheduler's lock (under it, every refresh is quadratic in the
  number of VCs), and completed solver tasks release their proof witnesses.
  Both matter only at scale, and both are fatal at Chorus's without the fix ([Architecture.md](Architecture.md) §2).

### 3. Persisting proofs as ordinary Lean theorems

* **`#gen_theorems`** persists each discharged VC as a named theorem in the
  module's `.olean`, with its real reconstructed proof. The two small models
  ([Cadence/Cadence.lean](../Cadence/Cadence.lean), [Cadence/Conductor.lean](../Cadence/Conductor.lean)) use it directly; their
  compositions in [Cadence/Composition.lean](../Cadence/Composition.lean) are plain Lean over those
  theorems. (The large models use the registry route of group 1 instead.)
* **Per-action preservation lemmas and `#gen_composition`** — the step from
  per-VC theorems to "every reachable state satisfies the invariants" is
  emitted, not written. `#prove_action` (per proof file) and `#gen_theorems`
  (in-module, every action at once) each emit the action's preservation
  lemma; `#gen_composition <Module>`, run in the module's namespace, assembles
  those into `<Module>.invariants_of_reachable` plus one named
  `<Module>.reachable_<property>` projection per invariant conjunct. It
  *extracts* the canonical instantiation of the generated definitions from
  the module's own `relationalTransitionSystem` rather than reconstructing
  it, which is what makes the composition writable at all: applying those VC
  theorems by hand needs every shared instance argument spelled out, and
  instance synthesis for the field-representation arguments diverges. All
  five verified modules use it ([Cadence/Composition.lean](../Cadence/Composition.lean)
  and the three `Certify.lean` files). Everything it emits goes through
  `addDecl`, so the kernel checks it; nothing here widens the trust base.
* **The `trSimp` simp set** — exactly the actions' `derived_eq` theorems and
  `tr` definitions. Two-state facts (frames, monotonicity of an observable)
  are proven from the pre-computed transition bodies, and the `actSimp` /
  `nextSimp` sets unfold the action *bodies* first and defeat that rewrite;
  without `trSimp` each consumer would carry a hand-maintained list of every
  action's two lemmas. With it, each of the composition files' `*_tr` macros
  is one `simp only [trSimp]`, and adding an action changes nothing.
* **A derived `Inhabited` instance for the abstract state**
  (`instInhabitedStateFieldAbstractType`), emitted with the state theory
  rather than with the model-check scaffolding that [Chorus.lean](../Cadence/Chorus.lean) has to
  disable. The composed system needs it (the glue's `scstate` sort must be
  inhabited).
* **Generated step lemmas** (`veil.gen.stepLemmas`, on by default). At
  `#gen_spec`, for every imperative action `a` and mutable component `f`,
  Veil emits and kernel-checks what the update records already determine:
  `M.a.tr_of_step` (the exposed transition body), `M.a.frame` and its
  per-field projections `M.a.frame_f`, `M.a.mono_f` (only `true` is
  written), the whole-system `M.f.mono` when every action frames or
  monotonically writes `f`, and `M.f.init` from the initializer's closed
  literal. These are the frame and monotonicity facts the contract
  instances need; in [Composition.lean](../Cadence/Composition.lean) and
  [Chorus/Compose.lean](../Cadence/Chorus/Compose.lean) each is a one-line
  application of a generated lemma rather than a case split over every
  action. Silent on success (`set_option trace.veil.stepLemmas true`
  for the verdicts); about 5 s of Chorus's ~127 s model build.
* **`step_property [name] { … f' … }`** — a **two-state** property of a
  module, stated in the `transition` priming notation before `#gen_spec`,
  with capitals quantified as in an `invariant`. Veil checks one cell
  `<action>_<property>` per action, with the module's assumptions and
  invariants at the pre-state as hypotheses, through the same TR route as
  every other cell: they appear in the sweep, in the VC registry
  (`#check_action`, `#prove_action`, and `#veil_status` counts them), and in
  `#gen_theorems`. The exports are `M.<P>_step` and — from
  `#gen_composition` — `M.reachable_<P>_step`. This is what lets a
  step-level *specification* live in the model and be SMT-checked rather
  than hand-proven downstream: the paper's Monotonicity for the Conductor,
  and Chorus's frozen-entries fact, are checked cells. The cost is one
  cell per action, so they are stated for the facts the contracts need —
  what follows from the update records alone comes free from the generated
  lemmas above.
* **Solver-option capture guards** — Veil captures solver options when a
  module elaborates its specification, so a `set_option … in
  #check_invariants` *after* that point is silently inert. The fork warns
  instead, and the models state their solver configuration explicitly
  before `#gen_spec`.

### 4. Proving things about quorums

* **Nothing from the fork.** Veil's `ByzNodeSet` interface is axiomatic,
  and Veil proves its axioms for the concrete `byzNodeSetFin` family
  (`n = 3f+1`). The three counting facts beyond intersection that Chorus
  and the MVBA ranking need are this project's own class,
  `Cadence.ByzNodeSetCounting`
  ([Cadence/QuorumCounting.lean](../Cadence/QuorumCounting.lean)), proven
  for `byzNodeSetFin` and for `byzNodeSetFinGen` (`n ≥ 3f+1`) in
  [Cadence/ByzQuorum.lean](../Cadence/ByzQuorum.lean). This is why the
  quorum interface is **not** on the assumption list in
  [Architecture.md](Architecture.md) §4.

### 5. The model-conformance monitor

* **`veil.gen.executableActions`** emits a per-label executable step function
  for a model, without the `O(nᵏ)` label-enumeration scaffolding that
  `#model_check` needs — which is what makes an executable Chorus monitor
  possible at all (see group 1).
* **`#gen_monitor`** generates the monitor's instantiation boilerplate. Used
  in [Cadence/Monitor/ChorusMonitorGen.lean](../Cadence/Monitor/ChorusMonitorGen.lean), which the regression suite
  cross-checks against the hand-written monitor.

### 6. Working comfortably

* **`veil.noVerify` / `VEIL_NO_VERIFY`** — an editor hatch: open a Veil file
  in the language server without it running any solving. Every skipped
  command emits a visible `⏭ skipped (veil.noVerify)` warning, so "no errors"
  in this mode can never be mistaken for "verified". See
  [CLAUDE.md](../CLAUDE.md).
* **…and under it, no VC-manager loop** (part of the fork's VC-registry
  branch). The manager loop never terminates by design, so under
  `veil.noVerify` — where it can have no work — `#gen_spec` does not start
  it. That matters to any program that *embeds* the frontend and returns
  from `main`, because the runtime then joins every worker thread: Verso's
  literate renderer is such a program (it re-elaborates each module to
  recover its `InfoTree`s), and it renders the documentation site under
  `VEIL_NO_VERIFY=1` ([Documentation.md](Documentation.md)).
* **Doc comments on Veil declarations** (`port/doc-comments`). A `/-- … -/`
  may precede any Veil command that declares something, and becomes the
  docstring of the constant the command generates — an action's, a
  property's, `State.<f>` for a state component. The models document their
  declarations this way, so the explanation of a relation, an action or a
  property sits with it on the site and in the editor's hover.
* **Source locations for generated declarations** (`port/decl-ranges`,
  `port/decl-ranges-generated`). Veil adds what it generates through
  `addDecl`, which records no location; the fork records the command each
  declaration comes from, selecting the name the user wrote — and, for the
  declaration that name denotes (`safety [p]` and `p`, `action a` and `a`),
  the binder information a Lean declaration command leaves at its name. The
  documentation site needs both: the renderer gives a declaration an anchor
  only where it finds that definition site, and the guide and the trust
  boundary link generated declarations to the command that emits them by
  their location.
* **Hygienic generated binders.** The generated transition relations bind a
  reader, a pre-state, a label and a post-state; those binders are
  hygienic, so an action parameter may take any name (`st'` included)
  without being captured by them.

### 7. Keeping the contract classes honest

The two-level contract design ([CompositionContracts.md](CompositionContracts.md))
rests on one Veil fact: **every `Prop` field of an `instantiate`d class is a
solver hypothesis**. That is what lets a consumer *use* a contract property
without restating it — and what makes a badly-shaped field fatal.

* **The first-order check.** A field that quantifies over a function (a run,
  say) is outside the fragment the SMT translation accepts. Without the check
  it aborts *every* verification condition of the consuming module with an
  opaque solver error naming neither the class nor the field; the check
  commands report it once, by class and field, before any solver starts.
  [spikes/03_nonfirstorder_field_breaks_smt.lean](../spikes/03_nonfirstorder_field_breaks_smt.lean)
  is the reproduction.
* **`attribute [veil_smt_ignore] C.field`** withholds one field from the
  solver: it stays a declared axiom of the class, the consuming module
  verifies, and each check command reports the withheld fields once per
  module — so the trust statement stays one line ("every axiom of the
  instantiated classes except these"). It applies to `Prop` fields only; a
  data field is never a hypothesis. This project does not withhold
  anything today; the attribute is the escape hatch for a field that must
  live in the class but need not reach the solver. **The measurement
  behind that "nothing"** — every `MVBASafety` axiom is a hypothesis of
  every Chorus cell — is CI's cold solve of the Chorus family
  on the 4-core runner at `BATCH=1`, without the MVBA constraint (run
  34528363622) and with it (run 34551700787):

  | cell / file | without the MVBA constraint | with it |
  |---|---|---|
  | `vote × committed_pos_frozen` | 61.4 s (34% of 180 s) | 119.5 s (66%) |
  | `fb_sign_neg × inclusion_no_honest_fb_neg` | 53.0 s | 51.1 s |
  | the other `× committed_pos_frozen` step cells | 33–37 s | 38–47 s |
  | `Proofs/Vote.lean` | 143 s | 334 s |
  | a typical proof file | 90–105 s | 110–130 s |

  Nothing timed out and no cell needed a retry. The step-property cells —
  one per action, the largest verification conditions in the family —
  are the ones that slowed, so the twelve `MVBASafety` axioms Chorus's
  proofs never use (`sent_mono`, `quiescence`, `external_validity`, the
  monotonicity, effects, frames and initial conditions of
  `proposed`/`abandoned`, `abandon_trans`) were tried as a `veil_smt_ignore`
  set on the worst cell, cold, in a scratch A/B ([scripts/scratch.sh](../scripts/scratch.sh) with
  `veil.cache.proofs false`, two runs each): **10.4 / 9.8 s with every
  axiom, 10.0 / 9.8 s with the twelve withheld** — no effect. The cost is
  the sorts, the class's load-bearing axioms and the larger clump, not the
  unused fields, so nothing is withheld; if the `vote` step cell ever
  approaches the budget the remedy is a manual proof of that cell, not
  the attribute ([CLAUDE.md](../CLAUDE.md) § Build, "slow versus divergent").
* **A readable rejection for an `assumption` over mutable state.** An
  `assumption` is a background axiom and ranges over the immutable part of
  the state only. Naming a mutable component in one fails with a message that
  says what an `assumption` may range over and points at `invariant` / `trusted invariant`
  instead — which is the choice the contract design keeps making.

## The Chorus model's memory

Two fixes in the fork (2026-10-01, PR #54), both merged into
`port/integration` and pinned here at `461c6832`:

- **`port/registry-memory`**, stacked on `port/vc-registry`. The VC registry
  elaborates each statement in its own run and hash-conses the stored types.
  The fork's record is
  [`docs/VCRegistry.md`](https://github.com/larskuhtz/veil/blob/port/integration/docs/VCRegistry.md).
- **`port/info-trees`**, stacked on `port/decl-ranges-generated`. Veil's
  declaration commands keep only slim info trees, and `#gen_spec` keeps none.
  The fork's record is
  [`docs/InfoTrees.md`](https://github.com/larskuhtz/veil/blob/port/integration/docs/InfoTrees.md).

The first fix was smaller than expected. The second removed the actual cause.
This section is what they mean here, and the starting point for any further
work on build memory.

**What happened.** CI's `verify` job killed the `Cadence.Chorus` stage, the
model build alone, with exit 137 after 1 069 s. That is out of memory in the
13 GB container on the 4-vCPU runner. The stage had been growing for weeks:
660 s in #46, 824 s in #50, 873 s in #51. R8's one action and one relation
tipped it over.

An interim `LEAN_NUM_THREADS=2` for the stage failed instead, with a registry
heartbeat timeout, both locally and on CI (run 36794438116). It was reverted.

### The instrument

macOS peak RSS does not predict the runner's cgroup. Master's model measured
17.7 GB locally and passes on CI, while R8's measured 16.7 GB locally and was
killed. So the measurement was taken on CI itself, with a temporary probe
commit that was later reverted.

The probe ran the model through `scripts/scratch.sh` inside the `verify`
container (4 CPUs, 13 GB), before the normal stages. Every 10 s it sampled
cgroup `memory.current`, the `anon` and `file` lines of `memory.stat`, and
the lean RSS. Lean's output carried timestamps alongside, and at the end it
printed `memory.peak` and `memory.events`. Run 36806058255 gave these
figures:

| model | Veil | elaboration | anon peak | lean RSS peak | `memory.peak` | `max` events | OOM kills |
|---|---|---|---|---|---|---|---|
| master (image oleans) | `73fa6fd4` | 794 s | 10.69 GB | 11.91 GB | 13.00 GB (the cap) | 3 034 | 0 |
| R8 | `d0532f70` (registry fix) | 859 s | 11.47 GB | 12.13 GB | 13.00 GB (the cap) | 6 335 | 0 |

Both runs filled the container and survived only by evicting cached olean
pages: R8's file pages fell from 2.1 GB to 0.6 GB. That is why R8's stage
passed on some runs and was killed on others. Master was already at the cap.

Anonymous memory rose about 1 GB a minute through the whole file, with a
further jump in the last minute. The olean the module writes is 136 MB, so
almost all of that memory was transient.

### What was tried, and what it showed

Every row below is a local measurement on a scratch copy of the model or a
`lake build Cadence.Chorus`: 4 threads, peak RSS of the model's `lean`
process, about ±1 GB of noise.

| variant | peak | memory over time |
|---|---|---|
| as is (registry fix in) | 12.3 GB | climbs to the end |
| `veil.gen.vcRegistry false` | 12.5 GB | the same climb: the registry is no longer a factor |
| info trees switched off for the whole file | 6.2 GB | flat at about 5.3 GB after the first minute |
| … off for the declarations only | 10.4 GB | flat until `#gen_spec`, which then adds about 5 GB |
| … off for `#gen_spec` only | 13.0 GB | the full climb |
| `lake build`, Veil `d0532f70` | 10.3 GB | climbs to the end |
| `lake build`, Veil `023fd53a` (constants only) | 8.6 GB | flat at 4.8–5.3 GB, then the registry and olean write |
| `lake build`, Veil `461c6832` (the fix) | 8.6 GB | flat at 4.8–5.2 GB, then the registry and olean write |

The registry's per-statement runs (the first fix) took about 1–2 GB off the
local peak, and its `ShareCommon` costs 135 ms. It did not move the CI
failure.

Lean's `profiler` reports time, not memory. With `trace.profiler` on, the
model's `#gen_spec` fails (`unable to synthesize LocalRProp instance`), so
neither helped here.

### The cause

Lean's frontend keeps every command's info tree alive until the end of the
file, for the `.ilean`. The language server does the same for an open file.
Veil's declarations recorded the info trees of all the code they generate,
together with the metavariable contexts behind them.

The fix keeps one reference per identifier the user wrote:
- a constant with no context;
- a variable with the minimal local context its hover needs, such as an
  action's parameter or a state component in an action body.

The `.ilean` of `Chorus` is identical before and after: 242 names, 207
definitions, 432 usage ranges, the same enclosing declarations.

The site keeps its hovers. On the rendered Chorus page:

| site | `var` hovers | `const` hovers |
|---|---|---|
| master's docs CI (run 36806672953) | 2 585 | 577 |
| constants only (`023fd53a`) | 293 | 582 |
| the fix (`461c6832`) | 2 602 | 582 |

The variables' types render in full (`i : node`, `local_mvba_qc_accepted :
node → Bool`). Only hovers on the types of compound subterms go. Rendering
the page peaks at 6.0 GB, against about 10 GB before the fix.

### What to look at next

The remaining peak is the end of the file: the VC registry and the olean
write, about 3–4 GB on top of a flat 5 GB. Two leads:

- the registry still holds all 9 587 types until the extension write;
- the olean write compacts the whole module.

The proof files keep their info trees as before, which is untouched by this
fix and a candidate for the same treatment if they ever matter. They peak at
2–4 GB cold, and `Chorus/Proofs/Vote.lean` at 9.2 GB.

The CI run on the re-pinned head, with its stage times, is recorded in PR #54.

## Native shared libraries

`lean-smt` is built with `precompileModules`, so its translation and
preprocessing meta-code runs natively rather than interpreted, which is where
most of the per-query overhead sits. Veil's own library is *not*
precompiled (upstream ships that flag off), so no `:shared` target is forced
on Mathlib at all.

**It costs this project nothing measurable.** That is worth stating, because
it is easy to assume otherwise: precompiling makes a library's meta-code run
natively, and Veil's tactic layer is meta-code. Measured on one machine, same
workload (843 ✅ / 16 324 ♻), warm re-validation at the default `BATCH=6`:

| configuration | wall |
|---|---|
| no precompilation (what this project ships) | **654 s** |
| Veil's library precompiled | 688 s |
| this project's library precompiled (native Veil *and* native Cadence) | 702 s |

Precompiling is, if anything, slightly slower — the extra native compilation
costs more than native tactics save. The reason is where the time actually
goes: a warm re-validation is **kernel replay, almost entirely**. Building one
Chorus proof file takes 39.68 s, and elaborating the same file without writing
its olean takes 39.78 s — so serialization is free and the work is all in
checking. Per cell, that is ~400 ms of kernel replay, 16 280 times over. A
faster tactic layer has nothing to bite on.

Which also identifies what the warm path *is* sensitive to: **the size of the
stored proof terms**, since kernel replay is proportional to it. That is the
lever, and the only one measured to matter here. It is why
`veil.smt.foldBoolAtoms` is on: it stops the SMT pipeline re-deriving the
`Bool → Prop` embedding of the whole hypothesis context in every proof.
Measured by turning it off and on over the same suite:

| | per-cell replay | warm re-validation | proof-file olean |
|---|---|---|---|
| fold off | 402 ms | 654 s | ~30 MB |
| fold on | **79 ms** | **389 s** | **11–12 MB** |

One file opts out — [Cadence/Chorus/Proofs/Vote.lean](../Cadence/Chorus/Proofs/Vote.lean), whose
`fastqc_complete_implies_mvba_evidence` cell diverges under the folded query
shape at any budget. Its olean stays ~30 MB against its siblings' 11–12 MB,
and its batch costs 42 s against their 13–15 s, which is a clean measure of
what the fold is worth.

Enabling or disabling it requires **re-solving cold**: cache entries are keyed
by VC statement, and the fold changes only the proof term, so existing hits
keep replaying whichever shape produced them.

**On the current pins it does not build either.** Precompiling forces every
package underneath to be available as a shared library, and loading
Mathlib's then crashes Lean on the ProofWidgets version Mathlib v4.32.0 pins.
`ProofWidgets/Component/RefreshComponent` is imported by Mathlib
(`Mathlib/Tactic/ClickSuggestions/Util.lean`) but is not reachable from
ProofWidgets' root module at **v0.0.105**, so it is never compiled into that
library's shared object; four symbols are then undefined, and on macOS they
bind lazily to null and Mathlib's generated module initializer jumps to
address zero. **Fixed upstream in v0.0.106** by adding the import to the root
module. ProofWidgets is inherited from Mathlib, not chosen here, and the pin
has to match Mathlib's (below), so this resolves itself with the next Mathlib
bump. `precompileModules` with Mathlib is a lightly-tested configuration in
general — Lean has several open issues about it, on Linux as well as macOS.
The table is the reason not to use it in any case: the interpreted tactic
layer is the price of a dependency tree that builds anywhere, and the proof
cache is what keeps that price affordable.

A general rule for changing the pins: a fork of Loom costs nothing, because
Mathlib does not depend on Loom, while a fork of anything in Mathlib's own
dependency set costs the Mathlib binary cache — `lake exe cache get` then
computes wrong hashes and refuses, and the container's `deps` stage runs
exactly that command.

Mathlib's shared *link* does not depend on the checkout path: it passes
7 649 object files, and since Lake 4.30 linker arguments go through a
response file on every platform (`Lake/Build/Actions.lean`, `mkArgs`), so the
1 MiB `execve` limit on macOS is never reached.

Two operational consequences:

* On Linux, modules importing `lean-smt` are elaborated with its compiled
  `.so`s `dlopen`ed, and those record a `DT_NEEDED` on the toolchain's own
  `libLake_shared.so` with no `RPATH`. If the loader is not told where to
  look the build fails with `error loading library, libLake_shared.so`. The
  published images and the devcontainer set `LD_LIBRARY_PATH` once; an
  auditor's own container needs the same
  ([Container.md](Container.md) §4).
* Build the dependency tree at bounded parallelism. `lean-smt` and `lean-auto`
  compile their own plugins, and if the build is OOM-killed mid-link the
  half-written `.so`s are left **trace-complete**, so every later build dies
  in milliseconds loading them and the build tool never regenerates them. The
  recovery is `rm -rf .lake/packages/{auto,smt}/.lake/build`; the prevention
  is `LEAN_NUM_THREADS=4` (Lake 5 has no `-j` flag — parallelism comes from
  that variable).

## Trusted computing base

For completeness, the things whose correctness the results *do* rest on:

* **Lean's kernel**, and the three standard axioms it is used with
  (`propext`, `Classical.choice`, `Quot.sound`) — pinned per end theorem in
  [Cadence.lean](../Cadence.lean).
* **Veil's VC generation** — the translation from a model's declared actions
  and invariants into the verification conditions. A bug here would prove the
  wrong thing rather than nothing, so this is a real trust dependency; it is
  mitigated by the model checker being an independent implementation of the
  model's semantics (used as a redundant regression on the receipt layer),
  and by the monitor running the model's own action bodies.

  Within that surface, the largest single concentration is how an action
  *body* becomes a state predicate. Veil elaborates bodies
  through Lean's own extensible `do`-notation extension points rather than by
  rewriting syntax: every statement re-opens the state from a fresh `get`, so
  the stale-binder failure mode is structurally absent rather than patched,
  and a statement kind Veil does not recognise — including one a future
  toolchain adds — is **rejected** instead of silently bypassing state
  handling. That does not shrink the trust base, but it is the reason to
  believe it, and it means a toolchain change cannot quietly alter what this
  project's actions mean.

* **Veil's elaboration-time defeq relaxation.** Veil wraps its own
  elaboration hot paths in a compatibility shim that opts out of Lean 4.32's
  stricter definitional-equality discipline. This affects which terms Veil's
  *tactics* treat as equal while they build a proof; the finished term is
  still re-checked by the kernel under the kernel's own rules, so the shim
  can make elaboration succeed or fail but cannot make an unsound proof
  accepted.
* **cvc5's `unsat` verdicts are *not* trusted.** Every discharge reconstructs
  a proof term that Lean's kernel re-checks. The one place a solver verdict
  is taken at face value is the `sat trace` reachability sanity checks, which
  are non-load-bearing: a wrong `sat` there could make a sanity check vacuous,
  never a safety claim wrong.
* **The concrete model checker**, for the MVBA's lock-check mutation test
  and the receipt-layer regression.

The full picture, including everything the Lean development deliberately
does not establish, is [Architecture.md](Architecture.md) §4 and §6.
