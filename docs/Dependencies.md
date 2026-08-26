# Dependencies

This project is a plain Lean 4 package. It pins two dependencies, both to
**public forks**, and nothing else:

| Dependency | Pin | Upstream |
|---|---|---|
| [Veil](https://github.com/larskuhtz/veil) | branch `port/integration` | [`verse-lab/veil`](https://github.com/verse-lab/veil) |
| [Loom](https://github.com/larskuhtz/loom) | branch `upgrade-v4.28-lakefile-fix` | [`verse-lab/loom`](https://github.com/verse-lab/loom) |

Veil in turn pulls in `lean-smt` (which bundles the cvc5 SMT solver and its
proof reconstruction), Mathlib, and Loom. The toolchain is pinned by
[`lean-toolchain`](../lean-toolchain) and fetched automatically by `elan`.

Nothing in this repository patches Veil. The changes this project needs are
in the fork, each on its own branch, documented there — this file only says
**which** capabilities are relied on and **why**, so that an auditor can see
what the verification pipeline is made of without reading the tool's source.

## Veil — `larskuhtz/veil @ port/integration`

`port/integration` is the union of the fork's `port/*` feature branches;
each of those is a self-contained change against Veil's `veil-2.0-preview`,
kept separate so it can be reviewed (and upstreamed) on its own. The
branch inventory and the dependency order between them live in the fork.

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
  build rather than asserted in prose.
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
* **Reconstruction-witness slimming** (`veil.smt.foldBoolAtoms`). Veil's
  models use `Bool`-valued relations; without this, the proof-reconstruction
  pipeline re-derives the `Bool → Prop` embedding of the entire hypothesis
  context once per verification condition, which measured as 65–72 % of every
  proof term at this project's scale. Folding it away cut cached proof size
  by ~60 %. One Chorus cell solves *worse* under the folded query shape and
  turns the option off file-locally — see the note in
  `Cadence/Chorus/Proofs/Vote.lean`.
* **Verifier scaling fixes** — the verification-results pretty-printer used
  to run under the scheduler's lock for every VC on every refresh, which is
  quadratic in the number of VCs; and completed solver tasks retained their
  proof witnesses. Both are invisible at textbook scale and both are fatal at
  Chorus's ~4 000-VC scale.
* **`precompileModules` for Veil's own library** — the proof-discharging
  tactics run natively instead of interpreted, which is what makes the
  per-action proof files usefully parallel.

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

## Loom — `larskuhtz/loom @ upgrade-v4.28-lakefile-fix`

A lakefile-only fix, and a *build* concern rather than a verification one.
Veil's own transitive pin (`verse-lab/loom @ upgrade-v4.28`) declares
case-study libraries that import a module that branch's core-only toolchain
bump removed, and whose globs overlap the core library; that breaks any
consumer which precompiles modules — which this project does, via Veil (see
group 2 above). The root `lakefile.lean` overrides the pin, and a root
`require` shadows transitive ones. **Do not remove that override**: a
consumer of the Veil fork without it hits the upstream breakage until Veil's
own `require Loom` is repointed.

## Consequence: the native precompile path, and the macOS link wall

`precompileModules` on Veil's library (group 2) is what makes the two Loom and
macOS build issues in this file *build* issues rather than curiosities. It
requires every upstream package — including Mathlib — to be available as a
shared library, and that has two knock-on effects:

1. It is why the Loom pin has to be overridden (above): the upstream lakefile
   declares libraries a precompiling consumer cannot build.
2. Linking `libmathlib_Mathlib.dylib` passes **7 649** object files to the
   compiler in one command, ~987 KB of command line. macOS caps arguments plus
   environment at 1 MiB per `exec`, and the measured ceiling on an
   arm64/macOS 15 machine is ~971 KB of arguments with a 2.6 KB environment —
   so the link is over by roughly 16 KB. Each character of the checkout's
   absolute path appears once per object, costing ~7.6 KB, which makes the
   whole thing depend on **where the repository is checked out**: about 35
   characters of absolute path is the ceiling. The symptom is

   ```
   could not execute external process '.../bin/clang'
   error: external command '.../bin/clang' exited with code 255
   ```

   on `Mathlib:shared`. Check out at a shorter path, or build on Linux. It is
   a one-time cost: once that library is linked, nothing rebuilds it.

   Workarounds that look promising and are not: an `LEAN_CC` wrapper that
   forwards to a compiler *response file* (the exec of the wrapper is itself
   what overruns), stripping the environment (worth ~2.5 KB of the needed
   16 KB), building from a symlinked short path (Lake resolves the working
   directory to its physical path), a non-default `packagesDir` (short enough,
   but Mathlib's and ProofWidgets' post-update hooks hardcode
   `.lake/packages/…`), and transplanting a prebuilt `.dylib` from another
   checkout (dependency dylibs embed their absolute install names, so the
   recorded link-input hashes never match and the build tool relinks anyway).

   The real fix belongs upstream — a response-file link in Lake, or Mathlib
   linking in chunks — and is not something this project can carry.

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
* **cvc5's `unsat` verdicts are *not* trusted.** Every discharge reconstructs
  a proof term that Lean's kernel re-checks. The one place a solver verdict
  is taken at face value is the `sat trace` reachability sanity checks, which
  are non-load-bearing: a wrong `sat` there could make a sanity check vacuous,
  never a safety claim wrong.
* **The concrete model checker**, for the pre-fix refutation and the
  receipt-layer regression.

The full picture, including everything the Lean development deliberately
does not establish, is [Architecture.md](./Architecture.md) §4 and §6.
