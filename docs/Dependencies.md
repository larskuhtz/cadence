# Dependencies

This project is a plain Lean 4 package with two direct dependencies:

| Dependency | Pin | Upstream |
|---|---|---|
| [Veil](https://github.com/larskuhtz/veil) | branch `port/integration` | [`verse-lab/veil`](https://github.com/verse-lab/veil) |
| [Loom](https://github.com/larskuhtz/loom) | branch `v4.32.0-for-veil-lakefile-fix` | [`verse-lab/loom`](https://github.com/verse-lab/loom) |

The Loom pin is a lakefile-only override — identical Loom sources, with the
unbuildable case-study libraries disabled. It matters only to a consumer that
precompiles modules, which this project currently does not, so it is inert
today; see § "Native shared libraries" for why it is carried anyway. Veil
pins the rest of the tree — `lean-smt` (which bundles the cvc5 SMT solver and
its proof reconstruction) and Mathlib — at revisions this project does not
override. [`lake-manifest.json`](../lake-manifest.json) records the
exact revision of every package, so a checkout builds the same tree whatever
the branches those pins name have since moved to. The toolchain is pinned by
[`lean-toolchain`](../lean-toolchain) and fetched automatically by `elan`.

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
  prove them. This is what lets the ~3 800 Chorus proofs be produced by 39
  small, independent files (`Cadence/Chorus/Proofs/`) instead of in one Lean
  process — the latter needs to hold every reconstructed proof term in one
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
  (`Cadence/Chorus/Certify.lean`, `Cadence/FallbackReceipt/Certify.lean`), so
  the claim "no verification condition is stubbed" is re-derived on every
  build rather than asserted in prose. The audit walk is cheap on Lean 4.32
  and gets no more expensive as the proofs grow: each olean now stores the
  axiom set of every declaration it exports, computed when the olean is
  written, so collecting axioms for an imported constant is a lookup rather
  than a traversal of its proof term. `#veil_status Chorus` resolves 3 861
  cell theorems across 39 proof-file oleans in about two seconds; before that
  change it walked all 3 861 reconstructed proof terms and took roughly
  forty.
* **A code-generation switch for the model checker's scaffolding**
  (`veil.gen.modelCheckScaffolding`). The label-enumeration instances Veil
  derives for `#model_check` are `O(nᵏ)` in the number of actions; at Chorus's
  38 actions they exceed Lean's reducer, and `#gen_spec` cannot elaborate at
  all. Chorus turns the scaffolding off (it does not use `#model_check`); the
  receipt layer leaves it on and does.

### 2. Keeping the solver out of the trust base, affordably

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
* **Verifier scaling fixes** — the verification-results pretty-printer used
  to run under the scheduler's lock for every VC on every refresh, which is
  quadratic in the number of VCs; and completed solver tasks retained their
  proof witnesses. Both are invisible at textbook scale and both are fatal at
  Chorus's ~4 000-VC scale.

### 3. Persisting proofs as ordinary Lean theorems

* **`#gen_theorems`** persists each discharged VC as a named theorem in the
  module's `.olean`, with its real reconstructed proof. The two small models
  (`Cadence/Cadence.lean`, `Cadence/Conductor.lean`) use it directly; their
  compositions in `Cadence/Composition.lean` are plain Lean over those
  theorems. (The large models use the registry route of group 1 instead.)
* **Solver-option capture guards** — Veil captures solver options when a
  module elaborates its specification, so a `set_option … in
  #check_invariants` *after* that point is silently inert. The fork warns
  instead. This project was mis-measuring its own solver configuration for a
  while because of exactly that; the models now state their configuration
  explicitly before `#gen_spec`.

### 4. Proving things about quorums

* **Byzantine-quorum counting lemmas** for the concrete `byzNodeSetFin`
  instance family. Veil's `ByzNodeSet` interface is axiomatic; the fork
  proves those axioms, plus the counting facts this project's pigeonhole
  arguments need, for every `n = 3f+1` with any Byzantine set of size ≤ f.
  This is why the quorum interface is **not** on the assumption list in
  [Architecture.md](./Architecture.md) §4 — see also
  [`Cadence/ByzQuorum.lean`](../Cadence/ByzQuorum.lean).

### 5. The model-conformance monitor

* **`veil.gen.executableActions`** emits a per-label executable step function
  for a model, without the `O(nᵏ)` label-enumeration scaffolding that
  `#model_check` needs — which is what makes an executable Chorus monitor
  possible at all (see group 1).
* **`#gen_monitor`** generates the monitor's instantiation boilerplate. Used
  in `Cadence/Monitor/ChorusMonitorGen.lean`, which the regression suite
  cross-checks against the hand-written monitor.

### 6. Working comfortably

* **`veil.noVerify` / `VEIL_NO_VERIFY`** — an editor hatch: open a Veil file
  in the language server without it running any solving. Every skipped
  command emits a visible `⏭ skipped (veil.noVerify)` warning, so "no errors"
  in this mode can never be mistaken for "verified". See
  [../CLAUDE.md](../CLAUDE.md).

## Native shared libraries

`lean-smt` is built with `precompileModules`, so its translation and
preprocessing meta-code runs natively rather than interpreted, which is where
most of the per-query overhead used to sit. Veil's own library is *not*
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
costs more than native tactics save. The reason is the proof cache: a warm
re-validation is dominated by re-creating VC statements and kernel-replaying
stored proofs, not by tactic search, so a faster tactic layer has little to
work with.

**And it does not work on the current pins anyway.** Precompiling forces every
package underneath to be available as a shared library, and three separate
things break:

* Loom's `CaseStudies` library globs `Loom.*` *and* `CaseStudies.*`, so every
  Loom module belongs to two libraries — and Lake loads a precompiled import
  "as part of their whole library". It therefore fetches `CaseStudies:shared`
  (never `Loom:shared`) for the Loom modules Veil imports, and that library
  also contains nine files importing `Loom.MonadAlgebras.NonDetT.Extract`,
  which does not exist at this revision — the tree has `NonDetT'`. So the
  build stops at `CaseStudies: some modules have bad imports`. This is a
  lakefile problem, not a platform one: it fails the same way on Linux, and
  it is what the project's second fork used to exist to patch. With the flag
  off, no Loom `:shared` target is requested and the broken library is never
  visited.
* Loom's core library does not build in full either, and this is *not* fixed
  by the pin above. `Loom/MonadAlgebras/WP/Gen.lean` has its body — lines 32
  to 285, including `WPGen` — inside a block comment at this revision, and
  `Loom.Meta` and `Loom.MonadAlgebras.WP.Matcher` still reference what it no
  longer defines. Nothing notices during a normal build because Veil imports
  neither; precompiling has to build the whole library, and those two fail.
* Loading Mathlib's shared library then crashes Lean — but for a small and
  fixable reason. `ProofWidgets`' library uses Lake's default globs, so it
  contains only what its root module reaches, and that does not include
  `ProofWidgets/Component/RefreshComponent.lean`; the only importer inside
  the package is a `Demos` module, which is a *separate* library. Mathlib
  imports it anyway, from `Mathlib/Tactic/ClickSuggestions/Util.lean`. So the
  module gets an olean but is never compiled into ProofWidgets' shared
  object, leaving four symbols undefined; on macOS those bind lazily to null
  and Mathlib's generated initializer jumps to address zero. Adding that one
  module to the `ProofWidgets` library's globs makes Mathlib load cleanly —
  verified, and available as a branch on a fork — but that fix **cannot be
  pinned here**. Overriding any package Mathlib also pins makes
  `lake exe cache get` compute the wrong hashes and refuse, which would mean
  building Mathlib from source (the container's `deps` stage runs exactly that
  command). So this one has to land upstream, in ProofWidgets or Mathlib,
  rather than being carried downstream.

That asymmetry is worth remembering in general: a fork of Loom costs nothing,
because Mathlib does not depend on Loom, while a fork of anything in Mathlib's
own dependency set costs the Mathlib binary cache.

Mathlib's shared *link* is not one of the reasons any more. It passes 7 649
object files, which on macOS used to overrun the 1 MiB `execve` limit and fail
with `could not execute external process '.../clang'`. Lake fixed that in
**4.30** by writing linker arguments to a response file on every platform
(`Lake/Build/Actions.lean`, `mkArgs`; 4.28 and 4.29 did so only on Windows),
so the link no longer depends on where the repository is checked out.

All three have been worked around and the configuration made to build — the
Loom pin above, plus a one-line ProofWidgets fix applied as a local Lake
package override. That is how the numbers above were obtained. None of it is
shipped, because none of it pays: see the table. `precompileModules` with
Mathlib is a lightly-tested configuration in general — Lean has several open
issues about it, on Linux as well as macOS. Until both are fixed upstream, the interpreted tactic layer is the
price of a dependency tree that builds anywhere, and the proof cache is what
keeps that price affordable.

Two operational consequences:

* On Linux, modules importing `lean-smt` are elaborated with its compiled
  `.so`s `dlopen`ed, and those record a `DT_NEEDED` on the toolchain's own
  `libLake_shared.so` with no `RPATH`. If the loader is not told where to
  look the build fails with `error loading library, libLake_shared.so`. The
  published images and the devcontainer set `LD_LIBRARY_PATH` once; an
  auditor's own container needs the same
  ([Container.md](./Container.md) §4).
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
  [`Cadence.lean`](../Cadence.lean).
* **Veil's VC generation** — the translation from a model's declared actions
  and invariants into the verification conditions. A bug here would prove the
  wrong thing rather than nothing, so this is a real trust dependency; it is
  mitigated by the model checker being an independent implementation of the
  model's semantics (used as a redundant regression on the receipt layer),
  and by the monitor running the model's own action bodies.

  Within that surface, the largest single concentration is how an action
  *body* becomes a state predicate. Upstream Veil now elaborates bodies
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
* **The concrete model checker**, for the pre-fix refutation and the
  receipt-layer regression.

The full picture, including everything the Lean development deliberately
does not establish, is [Architecture.md](./Architecture.md) §4 and §6.
