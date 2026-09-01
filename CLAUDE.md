# Project: Cadence — machine-checked verification (Veil / Lean 4)

Standalone Lean 4 project holding the formal verification of the Cadence BFT
consensus protocol. **The audience is auditors who do not necessarily know
Lean or formal verification** — that constraint governs every documentation
decision here: claims are stated in the paper's vocabulary, evidence is
machine-derived rather than narrated, and what has to be believed by a human
is a short named list rather than an exercise in reading proofs.

Read first: [README.md](./README.md) (what is proven, and the audit/trust
split) and [`Cadence.lean`](./Cadence.lean) (the end theorems and their axiom
pins on one page). This file carries the development workflow and the
hard-learned rules. The detailed working guide for touching the models is the
`cadence-verification` skill in [`.claude/skills/`](./.claude/skills).

## Orientation

Four Veil models plus support files, mirroring the paper's architecture:

* **`Cadence/Chorus.lean`** — per-slot one-shot BFT consensus (⊨
  `SlotConsensus`). The big one: agreement, proposal inclusion, hiding,
  speculative safety, fair-progress liveness content. It is a **model file**:
  it runs no invariant sweep and persists no theorems — its VC statements live
  in a persistent registry, the real kernel-checked proofs are produced per
  action by `Cadence/Chorus/Proofs/<Action>.lean`, and
  `Cadence/Chorus/Certify.lean` composes them. Model-only build ~2 min. Do not
  touch its imports casually (it imports `Primitives.lean` and `Tooling.lean`
  only).
* **`Cadence/Cadence.lean`** — the extreme-pipelining glue: consumes
  `SlotConsensus` + `Orchestrator` as oracles; slot-indexed MCP safety. Small
  and fast (~60 s, sweep included).
* **`Cadence/Conductor.lean`** — the window-based orchestrator: ACS as oracle,
  abstract clock, window structure. Fast (~60 s).
* **`Cadence/FallbackReceipt.lean`** (+ `Totality.lean`, `PreFix.lean`) — the
  per-validator fallback receipt/propose layer, where a real protocol bug was
  found and fixed. Same family shape as Chorus at 1/17 the scale, so it is the
  architecture's **cheap validation leg**: try any pipeline change here first.
  `PreFix.lean` pins the model checker's counterexample to the *pre-fix*
  rules — a green build **requires** the violation; do not "fix" it.
* Support: `Interfaces.lean` (module contracts + obligation tables),
  `Primitives.lean` (cryptographic primitive classes), `ByzQuorum.lean`
  (quorum instances and non-vacuity witnesses), `Windows.lean` (the ACS median
  lemma), `Tooling.lean` (targeted check commands).
* `Cadence/Monitor/` — the model-conformance monitor. Not part of any
  theorem's trust base; see [docs/Monitor.md](./docs/Monitor.md).

The models are **build-independent**: none imports `Chorus.lean`, and
`Cadence`/`Conductor` import only `Interfaces`/`Windows`/`Tooling`. Editing
the small models never re-runs the Chorus family — keep it that way (it is why
the contract classes live in `Interfaces.lean` and not `Primitives.lean`).

Reading order for context: [README.md](./README.md) →
[docs/Architecture.md](./docs/Architecture.md) (methods, trust bases, and §4,
the meta-assumption inventory) → [docs/ChorusDesign.md](./docs/ChorusDesign.md)
(Chorus modelling choices, the network abstraction and its soundness contract,
the bug record §7.2, open items §9) →
[docs/ConductorDesign.md](./docs/ConductorDesign.md) (the module decomposition
behind Cadence/Conductor; those two models' own headers carry the detail).
History: [docs/History.md](./docs/History.md).

## Build

* Always build from the **project root**.
* `lake build` verifies everything. But it schedules all 49 per-action proof
  files at once and a *cold* proof file peaks ~5 GB (lake has no job cap):
  on <64 GB use `scripts/revalidate.sh`, which stages the same targets.
* Per-module: `lake build Cadence.<Module>` — e.g. `Cadence.Chorus` (model
  only, ~2 min), `Cadence.Chorus.Proofs.Vote` (one action's ~98 cells),
  `Cadence.Chorus.Certify` (composition + the 3 861-cell audit pin, ~40 s).
* Run **one** expensive build at a time and kill stale `lean` processes first.
  Near-timeout VCs are noisy under load: a cell that times out in a full build
  may pass in isolation. Distinguish *slow* from *divergent* — if different
  subsets of the same few cells time out across runs and budgets (300 s vs
  900 s makes no difference), that is e-matching divergence and no budget
  fixes it; write a manual proof.
* When reading output, count **all four** markers: `✅` `❌` (counterexample)
  `💥` (solver crash) `⏱` (timeout), plus `♻` (proof-cache replay,
  kernel-checked). Grepping only `❌` silently hides failures.
* Proof cache: `.lake/build/veilcache/`, safe to delete at any time, age-GC'd
  after 14 days. **Every hit is kernel-checked** — the cache skips search, not
  checking. A warm re-validation of the whole suite is ~10–15 min; a cold one
  re-solves ~4 000 VCs (~85 CPU-min for the Chorus family alone).
* **The cache hides derivation drift.** Entries are keyed by VC statement,
  not by proof script: a kernel-replay hit consumes a `#prove_vc … by <tac>`
  cell *without elaborating the tactic*, so a warm green build proves the
  theorems without testing an edited script. After any statement-preserving
  change to a manual cell, to solver options, or to the discharge pipeline,
  solve the affected cells cold once — a scratch run with `set_option
  veil.cache.proofs false`, or delete their entries — before trusting the
  script. Statement-changing edits need no discipline: they miss the cache
  by construction.
* Scratch iteration (the fast loop): put `#prove_vc Chorus <action>
  <property> by <tac>` cells in a scratch file importing `Cadence.Chorus` and
  run **`scripts/scratch.sh <file>`**. Seconds per cell once the model is
  built. Probe goal shapes by ending the tactic early and reading the
  unsolved-goals dump. Cells proven in scratch warm the cache for the real
  proof file.

  Use that script, not bare `lake env lean`: cvc5, lean-smt, lean-auto and Qq
  are loaded as native *plugins*, and lake passes them only for modules it
  builds itself. Without them a file with a solver call aborts with
  `Could not find native implementation of external declaration
  'cvc5.TermManager.new'` — an abort with no Lean diagnostic, which reads like
  a crash rather than a missing flag. The script reads the plugin list out of
  a real module's build setup, so it cannot drift.
* Editor: set `VEIL_NO_VERIFY=1` in the *editor's* environment (VS Code
  `lean4.serverEnv`) — never in your shell profile, since `lake build` must
  still verify. Skipped commands emit `⏭ skipped (veil.noVerify)`, so "no
  errors" in that mode never means "verified".

### Expected warnings

A green build is not a silent build. These are known and harmless — do not
"fix" them by changing working proofs:

* `Cadence/Composition.lean` — two `try 'simp' instead of 'simpa'`
  suggestions.

That is the whole list: the dependency tree builds silently. Anything else —
and in particular any `❌`, `💥`, `⏱`, or a `sorry` warning from a `Cadence/`
file — is real.

### Building natively, and building in a container

A native build works on macOS and Linux from any checkout path. Veil's library
is not precompiled, so no `:shared` target is forced on Mathlib and there is
no link step to overrun.

**Build the dependency tree with `LEAN_NUM_THREADS=4`.** `lean-smt` and
`lean-auto` compile their own plugins; if the build is OOM-killed mid-link the
half-written `.so`s are left *trace-complete*, so every later build dies in
milliseconds loading them and lake never regenerates them. Recovery:
`rm -rf .lake/packages/{auto,smt}/.lake/build`. Lake 5 has no `-j` flag —
parallelism comes from that variable alone.

The container path is for a **fixed, published environment**: the toolchain,
the whole dependency tree, and (in the `verified` image) this project's own
oleans, so an auditor re-checks the proofs without building anything and CI
runs the identical tree.

**`RUNTIME=podman scripts/container.sh {verify,check,shell}`**, or the
devcontainer. Both pull the published images
(`ghcr.io/larskuhtz/cadence-*:latest`, multi-arch) on first use, so nothing
has to be built; `container.sh build` exists for changes to the dependency
tree and is documented in [docs/Images.md](./docs/Images.md). Usage,
measurements and the audit ladder:
[docs/Container.md](./docs/Container.md). Rules worth memorising:

* **Build images with podman or docker; run them with anything.** Apple's
  `container` cannot build the ~12 GB `deps` layer on a 36 GB machine (its
  builder VM OOMs holding the layer plus the elaboration), and it cannot back a
  devcontainer either (no Docker socket). It runs the images fine.
* **One volume per image.** A named volume is initialised from whichever image
  first mounts it and is sticky after that, so `dev` (dependencies only) and
  `verified` (+ this project's oleans) must not share one. The script derives
  the name from the image; do not override `VOLUME` without thinking.
* **Build every image target in one pass before pushing.** Layer sharing —
  which is what makes the second image a 21–251 MiB pull instead of ~4 GiB —
  only holds if the images came from the same Containerfile state. A tag left
  one build stale silently costs GiBs, and both images still work.
* **Do not try to slim the images by deleting build artefacts.** Measured: the
  generated `.c`, the `.c.o.export` objects and the `.ilean` files are all
  *declared lake outputs*, so removing any of them makes every module out of
  date; and removing a dependency's `.git` makes lake re-resolve it and **delete
  the checkout**. Only the widget's `node_modules` and npm's cache are free, and
  they are already removed in the layer that creates them. The size analysis,
  with what was measured and how, is
  [docs/Images.md](./docs/Images.md) § "Why the images are the size they are".

## Hard rules (each has bitten before)

* **No doc comments on Veil declarations.** `/-- … -/` before `safety`,
  `invariant`, `action` makes the parser expect `lemma` and fail. Use plain
  block comments `/- … -/`. (And mind that `-/` inside prose closes a block
  comment — "pre-/post-state".)
* **The monotone-network contract is not enforced by the tool.** Network
  relations (`msg_*`) may be consulted in **positive position only**.
  Violations do not fail the build — they silently void the async-safety
  claim. Read [docs/ChorusDesign.md](./docs/ChorusDesign.md) §3.1.1 before
  adding or modifying an action. Three scoped exception categories are
  documented there (the third — the seven *self-row* reads — was added by the
  2026-08 audit response); do not add a fourth without updating that section
  and [docs/Architecture.md](./docs/Architecture.md) §4.
* **Invariants live in the model; proofs live in the proof files.** Manual
  cells do not index the invariant clump by hand: `inv_have h := <invariant>`
  / `inv% hinv <invariant>`
  ([`Cadence/ProofPrelude.lean`](./Cadence/ProofPrelude.lean)) look the
  conjunct up *by name*, deriving its position from the model's own
  `Invariants` at elaboration time and checking that the clump and the
  invariant list still have the same length. Adding, removing or reordering
  a `safety`/`invariant` therefore needs no re-indexing in the proof files
  (it still changes every VC statement, so the family still re-solves), and
  a stale name is an elaboration error rather than a silently wrong
  conjunct.
* **`Chorus.lean` needs `maxRecDepth` raised twice, for different reasons.**
  Before the action declarations: action bodies elaborate one nested
  `openStateAround` per statement, so depth scales with the longest body and
  `after_init` alone exceeds the default. Before `#gen_spec`, together with
  the `synthInstance.*` raises: without it the pre-simplification of the large
  invariant clump fails — as a *warning*, not an error — and every VC
  re-simplifies the clump, degrading the sweep from minutes to hours.
* **Universal indices in bulk assignments are single capital letters.** A
  multi-letter capitalised name is not recognised and fails with "unknown
  identifier". If the letter also names a declaration in scope (Mathlib's `W`,
  for instance) Veil warns that it shadows it and treats it as an index
  anyway; pick a free letter rather than leaving the warning.
* **A `def` whose type is a class needs `@[implicit_reducible]`.** Without it
  Lean 4.32 warns, and downstream instance synthesis for that class fails.
  `#gen_monitor` emits one such declaration and cannot be annotated from the
  call site, so `Cadence/Monitor/ChorusMonitorGen.lean` turns the warning off
  file-locally — otherwise it lands on stdout and breaks the monitor suite's
  comparison against the hand-written oracle. The real fix belongs in the
  Veil fork.
* **Simp and dsimp do not see through instances by default.** Lean 4.32
  defaults `Simp.Config.instances` to `false`, so anything unfolding a
  class-valued definition needs `simp +instances only [...]` /
  `dsimp +instances [...]` — the flag goes *before* `only`. The failure mode
  is `made no progress`, sometimes with a note that the target is not
  type-correct at `instances` transparency.
* **Instance telescopes of generated VC theorems are deduplicated.** Veil
  canonicalises an action's extra parameters, so two identical `Decidable`
  side conditions collapse into one and the theorem's arity drops. The
  explicit-instance macros in `Cadence/Composition.lean` pass those positions
  as `_`, so the count must match; a mismatch is a loud "application type
  mismatch" naming the first argument that landed in the wrong slot.
* **Never put `set_option … in` directly after a `sat trace { … }` block** —
  the trace command's optional proof-term suffix greedily parses it. Put
  traces after `#check_invariants`, before `end`.
* **No `decide (…)` in update right-hand sides** if the module has (or may
  get) trace queries: `decide` over order atoms elaborates to
  `Classical.propDecidable`, which the trace pipeline cannot translate. The
  failure is silent until a trace is added. Decompose bulk conditional updates
  into per-tuple actions instead (the `record_skip` pattern in
  `Cadence/Cadence.lean`).
* **Keep action parameter lists ≤ 10.** The enumeration derivation over the
  action label sum blows up in parameter arity.
* **Do not `open Veil` in a file that writes a `SlotConsensus` instance** —
  the Veil DSL's scoped keywords include `includes`, which collides with the
  field name. `Cadence/Chorus/Compose.lean` qualifies Veil names instead.
* **The hand-written composition files must stay in the generated transition
  system's exact instance regime** — no `DecidableEq` binders, `open
  Classical`, VC theorems applied through the explicit-instance macros — or
  elaboration dies in `whnf` timeouts with no useful error. Read the header of
  `Cadence/Composition.lean` first.
* **Manual cells are `#prove_vc <Module> <action> <property> by <tac>`
  lines** before the file's `#prove_action`, which consumes them after a
  statement check. The statement comes from the model's VC registry, never
  from the file, so a model change cannot leave a stale hand-written type
  behind; what it can break is the tactic, which fails loudly on the next
  cold solve of that cell (see the cache-discipline rule under Build).

## Verification-status invariants (keep true)

These are the properties the repository advertises. A change that breaks one
is a change to what this project *claims*, not a refactor.

* **No trusted solver step.** Every module elaborates with
  `veil.smt.trust false`; every discharge is reconstructed and kernel-checked.
* **No `sorryAx` anywhere.** Every axiom pin stays at exactly
  `[propext, Classical.choice, Quot.sound]`, in every per-result pin and
  in [`Cadence.lean`](./Cadence.lean).
* **The audit pins stay complete**: `#veil_status Chorus` at `3861/3861 real`
  and `#veil_status FallbackReceipt` at `220/220 real`. If an invariant is
  added, these numbers change — update the pins, and check the new numbers are
  the ones you expect.
* **The pre-fix refutation keeps failing.** `FallbackReceipt/PreFix.lean`
  builds only while the model checker still finds the documented
  counterexample. Its `#model_check` **must** keep `(sequential := true)`:
  the parallel search splits the frontier into `numSubTasks` chunks and that
  defaults to the machine's *core count*, so which of the many violating
  states is reported first is hardware-dependent — 4, 8, 12 and 14 cores each
  produce a different, equally valid witness, and the pin would then only hold
  on the machine that recorded it. The reasoning is in the file.
* Headline results stay readable by non-FV reviewers: named `safety`
  declarations in the models, corollaries and contract instances in the
  composition files, and one index page in `Cadence.lean`.

## Documentation rules

* **Veil's own changes are documented in the Veil fork, not here.** This
  repository records only *which* fork capabilities it depends on and why:
  [docs/Dependencies.md](./docs/Dependencies.md). Do not re-import
  Veil-internal plan documents, option-level design notes, or tool
  measurements into `docs/` — a pointer plus the reason is the right amount.
* Cite the paper by **stable LaTeX anchors** (`lemma:chorus-agreement`,
  `line:fb-pathvote-guard`), never by page or line number. The paper is public —
  `arXiv:2607.02275`, **v2 is what this development verifies**, v1 is the
  pre-fix version `FallbackReceipt/PreFix.lean` refutes — and so is its LaTeX
  source, whose `src/*.tex` layout is exactly what the citations name. Before
  adding an anchor, check it exists:
  `mkdir -p papers/cadence && curl -sL https://arxiv.org/e-print/2607.02275v2 | tar -xz -C papers/cadence`
  then grep for `\label{…}`. Neither the PDF (`hypertexnames=false`) nor arXiv's
  HTML exposes label anchors, so they are grep targets, not links. The same
  rule applies inward: cite Lean code by declaration name, never by line
  number — the 2026-08 audit report's Lean line citations had all drifted
  within a week.
* [docs/History.md](./docs/History.md) is a historical ledger and says so at
  the top. When something in it becomes false, mark it superseded rather than
  quietly editing history.
* Relative links in `docs/` and in Lean doc comments are repo-root-relative
  paths in backticks; keep them checkable (a broken link is a small lie).
* **Every repeated fact has one home.** A count or measurement lives in its
  canonical place — a machine-checked pin where one exists (`#veil_status`,
  `#guard_msgs`), else the tables in
  [docs/Architecture.md](./docs/Architecture.md), else the doc that owns the
  measurement — and every other mention stays qualitative with a pointer.
  Before writing a number into prose, find where it already lives. (The
  2026-08 "14 manual cells" drift happened because one number was spelled
  out in six files; a 2026-08-25 audit swept the stragglers.)
