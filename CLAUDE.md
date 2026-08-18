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
  `Cadence/Chorus/Certify.lean` composes them. Model-only build ~90 s. Do not
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
the bug record §7.2, open items §9). The Cadence/Conductor design docs are the
long module headers of those files. History:
[docs/History.md](./docs/History.md).

## Build

* Always build from the **project root**.
* `lake build` verifies everything. But it schedules all 49 per-action proof
  files at once and a *cold* proof file peaks ~5 GB (lake has no job cap):
  on <64 GB use `scripts/revalidate.sh`, which stages the same targets.
* Per-module: `lake build Cadence.<Module>` — e.g. `Cadence.Chorus` (model
  only, ~90 s), `Cadence.Chorus.Proofs.Vote` (one action's ~96 cells),
  `Cadence.Chorus.Certify` (composition + the 3 822-cell audit pin, ~40 s).
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
* Scratch iteration (the fast loop): put `#prove_vc Chorus <action>
  <property> by <tac>` cells in a scratch file importing `Cadence.Chorus` and
  run `lake env lean <file>`. Seconds per cell once the model is built. Probe
  goal shapes by ending the tactic early and reading the unsolved-goals dump.
  Cells proven in scratch warm the cache for the real proof file.
* Editor: set `VEIL_NO_VERIFY=1` in the *editor's* environment (VS Code
  `lean4.serverEnv`) — never in your shell profile, since `lake build` must
  still verify. Skipped commands emit `⏭ skipped (veil.noVerify)`, so "no
  errors" in that mode never means "verified".

### Expected warnings

A green build is not a silent build. These are known and harmless — do not
"fix" them by changing working proofs:

* `Cadence/Chorus/Proofs/FbSignNeg.lean` — two `Try this: intro …`
  suggestions from the tactic linter.
* `Cadence/Composition.lean:161–162` — two `try 'simp' instead of 'simpa'`
  suggestions.
* Dependency-side: one `declaration uses 'sorry'` in `lean-smt`'s
  bit-vector reconstruction (a module this project never uses), plus
  deprecation notices from Loom and `lean-smt`.

Anything else — and in particular any `❌`, `💥`, `⏱`, or a `sorry` warning
from a `Cadence/` file — is real.

### Building in a container (and the macOS wall it avoids)

A **cold** build has to link Mathlib's shared library, ~7 650 objects on one
command line. macOS caps exec arguments at 1 MiB and this overruns it by a few
kilobytes once the checkout path exceeds ~35 characters (each character costs
~7.6 KB); the symptom is `could not execute external process '.../clang'` on
`Mathlib:shared`. On Linux the limit is 2 MiB and the link takes 0.8 s.

So: **`RUNTIME=podman scripts/container.sh {build,verify,check,shell}`**, or the
devcontainer. Full detail, measurements and the audit ladder:
[docs/Container.md](./docs/Container.md). Two rules worth memorising:

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
  [docs/Container.md](./docs/Container.md) § "Why the images are the size they
  are".

Failing all that, a native macOS build works from a checkout path of ≲35
characters; see [docs/Dependencies.md](./docs/Dependencies.md).

## Hard rules (each has bitten before)

* **No doc comments on Veil declarations.** `/-- … -/` before `safety`,
  `invariant`, `action` makes the parser expect `lemma` and fail. Use plain
  block comments `/- … -/`. (And mind that `-/` inside prose closes a block
  comment — "pre-/post-state".)
* **The monotone-network contract is not enforced by the tool.** Network
  relations (`msg_*`) may be consulted in **positive position only**.
  Violations do not fail the build — they silently void the async-safety
  claim. Read [docs/ChorusDesign.md](./docs/ChorusDesign.md) §3.1.1 before
  adding or modifying an action. Two scoped exceptions are documented there;
  do not add a third without updating that section and
  [docs/Architecture.md](./docs/Architecture.md) §4.
* **Invariants live in the model; proofs live in the proof files.** Append new
  invariants at the **end** of the model. The manual cells' `hinv.2.….1`
  projections index the invariant clump by *declaration order*, so adding,
  removing or reordering a `safety`/`invariant` requires re-indexing them
  (the index list is reproducible with
  `grep -nE '^(safety|invariant) \[' Cadence/Chorus.lean`).
* **Keep the `set_option synthInstance.* / maxRecDepth` block** before
  `#gen_spec` in `Chorus.lean`. Without it the pre-simplification of the large
  invariant clump fails — as a *warning*, not an error — and every VC
  re-simplifies the clump, degrading the sweep from minutes to hours.
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
* **A model change invalidates the manual theorems' statements.** Rebuild them
  from fresh stubs (Veil prints ready-made statement stubs when a cell fails)
  rather than patching types by hand.

## Verification-status invariants (keep true)

These are the properties the repository advertises. A change that breaks one
is a change to what this project *claims*, not a refactor.

* **No trusted solver step.** Every module elaborates with
  `veil.smt.trust false`; every discharge is reconstructed and kernel-checked.
* **No `sorryAx` anywhere.** Every axiom pin stays at exactly
  `[propext, Classical.choice, Quot.sound]`, in the seven per-result pins and
  in [`Cadence.lean`](./Cadence.lean).
* **The audit pins stay complete**: `#veil_status Chorus` at `3822/3822 real`
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
  `line:fb-pathvote-guard`), never by page or line number.
* [docs/History.md](./docs/History.md) is a historical ledger and says so at
  the top. When something in it becomes false, mark it superseded rather than
  quietly editing history.
* Relative links in `docs/` and in Lean doc comments are repo-root-relative
  paths in backticks; keep them checkable (a broken link is a small lie).
