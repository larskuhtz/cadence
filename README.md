# Cadence — machine-checked verification (Veil / Lean 4)

A formal verification of the [**Cadence**](https://www.category.xyz/cadence)
BFT consensus protocol (see [§ The protocol paper](#the-protocol-paper)): the
per-slot consensus **Chorus**, the window-based orchestrator **Conductor**, the
pipelining **Cadence** layer that composes them, and the fallback
receipt/propose layer.

Written in [Veil](https://github.com/larskuhtz/veil) on Lean 4. Veil is an
embedded DSL: a `.lean` file *is* the model, and elaborating the file *runs*
its verification. There is no separate proof script — `lake build` elaborates
the files, the verification commands fire during elaboration, and **if any of
them fails, the build fails**.

> **Status.** Everything is green. The SMT solver is not in the trust base.
> Every end-to-end theorem is pinned to exactly `propext` /
> `Classical.choice` / `Quot.sound` — Lean's three standard axioms; no
> `sorry`, no trusted solver verdict. Every automated proof is re-checked by
> Lean's kernel, and every proof the final theorems rest on is persisted as a
> real, checked term. The receipt layer additionally keeps a bug from an
> earlier version of the paper as a machine-checked refutation.

**Start here:** [`Cadence.lean`](./Cadence.lean) — the audit root. It imports
every finished result and re-derives each axiom's footprint as a build-checked
pin: seven theorems, one trust base.

---

## Audit Guide

### A. Machine-checked

You do not need to trust this project's authors, for any of the
following claims. They are re-derived by the machine on every build, and a violation
is a build failure.

| What is guaranteed | How it is enforced |
|---|---|
| Every stated theorem has a **complete proof**, checked by Lean's kernel | the build; plus the axiom pins in [`Cadence.lean`](./Cadence.lean) — a `sorry` anywhere shows up as the axiom `sorryAx` and fails the pin |
| The trust base has not drifted (no extra axiom crept in) | `#guard_msgs in #print axioms <thm>` for all seven end theorems, in [`Cadence.lean`](./Cadence.lean) and at each result's own site |
| **cvc5's verdicts are not believed.** Every solver discharge is reconstructed as a Lean proof term and re-checked by the kernel | all models elaborate with `veil.smt.trust false`; if a proof cannot be reconstructed, the cell fails |
| **Nothing is stubbed.** All 3 822 Chorus verification conditions (3 783 action × property obligations + 39 does-not-throw checks), and all 220 of the receipt layer's, have a real, statement-matching, kernel-checked theorem in scope | the pinned `#veil_status` lines in `Cadence/Chorus/Certify.lean` and `Cadence/FallbackReceipt/Certify.lean` — `3822/3822 real` and `220/220 real`, with the axiom union over all of them |
| The verification conditions are the ones the model states — they are not re-typed by hand anywhere | the proof files read their statements out of the model's own persisted registry; identity is by construction |
| The receipt-layer bug found in 2026-07 **is** a bug in the pre-fix rules | `Cadence/FallbackReceipt/PreFix.lean` pins the model checker's counterexample; the file builds only if the bug is still found, verbatim |

In short: `lake build` succeeding is the claim. You can re-derive any pin
yourself — drop a `#guard_msgs in` line, or run `#print axioms <name>` in a
scratch file (see [Building](#building) below).

The script `scripts/container.sh check` re-runs **Lean's kernel over every
declaration in the development** — all 3 808 reconstructed Chorus proofs
included — in **4 minutes**, with no SMT solver, no tactic execution and no
elaboration. Forcing the elaborator to redo the whole project from source on
top of that is a further 9 minutes; re-solving every verification condition
with cvc5 from scratch, about 90 minutes. What each of those does and does not
establish — and how both differ from simply *importing* prebuilt `.olean`
files, which are trusted rather than re-checked — is the audit ladder in
[docs/Container.md](./docs/Container.md) §3–§4.

### B. To be checked by an auditor

Machine checking says the proofs are complete. It cannot say the *statements*
are the right ones. Three things need eyes:

1. **Does the model faithfully describe the protocol?** The models are the
   `.lean` files listed under [What is where](#what-is-where); each carries a
   long header explaining its modelling choices, and
   [docs/ChorusDesign.md](./docs/ChorusDesign.md) is the full design-rationale
   document for the big one. The abstractions deliberately taken (chunk
   indices, erasure coding, payload bytes, single slot for Chorus) are listed
   in [docs/Architecture.md](./docs/Architecture.md) §4 item 5 and
   [docs/ChorusDesign.md](./docs/ChorusDesign.md) §3.4 and §8.
2. **Are the top-level properties the right properties?** The seven end
   theorems, in the paper's own vocabulary, are tabulated in
   [`Cadence.lean`](./Cadence.lean) and in [What is proven](#what-is-proven)
   below. The paper's *module contracts* — the interfaces the layers are
   proven against, with their obligation tables — are
   [`Cadence/Interfaces.lean`](./Cadence/Interfaces.lean).
3. **Are the meta-theoretic assumptions sound?** Everything deliberately kept
   outside Lean — the network abstraction's soundness contract, the fairness
   axioms and the fairness-to-liveness reduction, the cryptographic
   primitives, the timing/quantitative module obligations — is a **named,
   complete inventory**: [docs/Architecture.md](./docs/Architecture.md) §4.
   That inventory is the audit checklist. It is short on purpose.

Item 3 lists assumptions *by name*, and the fairness and oracle axioms appear
verbatim in the Lean sources where they are consumed — `grep -rn '(A-'
Cadence/` enumerates them — so the inventory's completeness is checkable. The
one assumption without that property is the network contract, which is why it
is item 1 of the inventory and a standing rule in [CLAUDE.md](./CLAUDE.md): a
violation of it would not fail the build.

*The file [docs/AuditReport.md](./docs/AuditReport.md) contains an audit report
that was created by by [Aristotle (Harmonic)](https://aristotle.harmonic.fun) for
the revision bfeee8c of this project against the version 2 of the Cadence
paper published on arxiv.*

---

## What is proven

| Claim | Where | Method / trust base |
|---|---|---|
| **Agreement** — correct validators never finalize conflicting proposal vectors | `Cadence/Chorus.lean` (`agreement_pos`, `agreement_pos_neg`) → `Chorus.slotConsensus_instance` | 3 822 inductive-invariant verification conditions (cvc5, **proof-reconstructed — kernel-checked**), proved per action under `Cadence/Chorus/Proofs/`, plus plain-Lean reachability composition — kernel-checked end to end, axiom-pinned, per-VC audit pinned |
| **Proposal inclusion** (censorship resistance, under the paper's synchrony premise) | `Cadence/Chorus.lean` → instance field | same |
| **Hiding until the deadline** (protocol half) | `Cadence/Chorus.lean` (`hiding_until_deadline`) | reconstructed VCs; the cryptographic half is axiomatised (`Cadence/Primitives.lean`) |
| **Speculative-finality revertibility** ("reverted only if the proposer is the culprit") | `Cadence/Chorus.lean` (`speculative_agreement_*`) | reconstructed VCs, conditional on `no_equivocation` + `no_invalid_encoding` — the paper's full culprit set: equivocation, or committing to an invalidly encoded root |
| **Fair-progress liveness content** (no livelock of fair actions — strictly stronger than deadlock-freedom) | `Cadence/Chorus.lean`, liveness section | reconstructed VCs + named meta-axioms ([docs/Architecture.md](./docs/Architecture.md) §4) |
| **Evidence pigeonhole** — `2f+1` honest fallback entries always yield certified per-proposer evidence (the counting step of the fallback liveness branch), for **every** `n = 3f+1` | `Cadence/Chorus/Pigeonhole.lean` (`evidence_pigeonhole_of_reachable`) | plain Lean over reachable states, axiom-pinned |
| **MCP Safety, positional form** | `Cadence/Composition.lean` (`positional_log_safety`) | Cadence/Conductor sweeps (reconstructed) + plain-Lean composition — kernel-checked, axiom-pinned |
| **`Conductor ⊨ Orchestrator`**, **`Chorus ⊨ SlotConsensus`** (the paper's module contracts) | `Cadence/Composition.lean`, `Cadence/Chorus/Compose.lean` | plain Lean over persisted VC theorems — kernel-checked, axiom-pinned |
| **Fallback meta-block "valid by construction"**, including the counting argument, for **every** `n = 3f+1` | `Cadence/FallbackReceipt.lean` + `Cadence/FallbackReceipt/Totality.lean` | reconstructed SMT + kernel-checked Lean — **no trusted step**, axiom-pinned |
| **The pre-fix receipt rules are broken** ("pre-fix" = the paper's rules *before* the 2026-07-07 bug fix; the bug, mechanically reproduced) | `Cadence/FallbackReceipt/PreFix.lean` | exhaustive model check; the counterexample trace is pinned in the build |

What is *not* proven in Lean — timing bounds, the scheduling (fairness)
assumptions and the fairness-to-liveness reduction (the fair-progress *safety
content* of liveness **is** machine-checked), the cryptographic primitives,
the monotone-network soundness contract — is the named assumption inventory in
[docs/Architecture.md](./docs/Architecture.md) §4.

---

## Checking the proofs

Prebuilt images — this project already built and verified inside the image —
are published for `linux/arm64` and `linux/amd64`.
[`scripts/container.sh`](./scripts/container.sh) pulls what it needs on first
use (~4 GiB, once); nothing has to be built:

```bash
RUNTIME=podman scripts/container.sh check    # kernel-re-check every proof — 4 min, no solver
RUNTIME=podman scripts/container.sh verify   # re-verify against the checkout's sources
```

`RUNTIME` selects `podman`, `docker`, or Apple's `container`. The two commands
are tiers 1 and 2 of an audit ladder that ends at "re-solve every verification
condition from scratch". What each tier does and does not establish — in
particular, what a prebuilt `.olean` proves — is
[docs/Container.md](./docs/Container.md) §3–§4.

## Working on the models

The `dev` image is the same environment with the sources mounted. Open the
folder in VS Code with the **Dev Containers** extension —
[`.devcontainer/`](./.devcontainer) uses the published image — or work from a
terminal:

```bash
RUNTIME=podman scripts/container.sh shell    # interactive shell in the workspace
RUNTIME=podman scripts/container.sh verify   # staged re-verification, after an edit
```

Opening a file costs what it elaborates: `Cadence/Chorus.lean` runs no
invariant sweep but elaborates the model plus its background does-not-throw
checks (a couple of minutes); a `Cadence/Chorus/Proofs/` file re-proves one
action's cells (seconds with a warm cache, minutes cold); the consumer files
load prebuilt `.olean`s in seconds. To suppress solving entirely while
editing, set `VEIL_NO_VERIFY=1` in the *editor's* environment — the
devcontainer already does; never set it in a shell profile, since `lake build`
must still verify. Every skipped command reports a visible
`⏭ skipped (veil.noVerify)` warning, so "no errors" in this mode never means
"verified".

The development workflow and the model-specific rules are in
[CLAUDE.md](./CLAUDE.md). Building the images yourself — needed only when the
dependency tree changes — is [docs/Images.md](./docs/Images.md).

### Building natively

Requires [elan](https://github.com/leanprover/elan); the pinned toolchain and
both dependencies are fetched automatically on the first build. Building also
needs a system `clang` with a version-matched `libc++` development package
(providing the compiler's resource-dir headers): that is a transitive native
dependency of the cvc5 binding used for proof reconstruction, whose build
compiles an FFI shim with a hardcoded `clang -std=c++17 -stdlib=libc++`
invocation. elan's bundled toolchain `clang` does not ship those headers and
cannot substitute.

```bash
lake build          # everything: models, all 49 per-action proof files,
                    # composition certificates, end theorems, the audit
                    # root's axiom pins, and the monitor
```

**Memory.** `lake build` schedules the 39 Chorus and 10 receipt-layer proof
files all at once, and a *cold* proof file peaks around 5 GB of resident
memory (lake has no job cap). On a machine with less than ~64 GB, build in
stages instead — this does the same work in the same order, batched:

```bash
scripts/revalidate.sh          # staged full build; keeps a cold run under ~30 GB
scripts/revalidate.sh /tmp     # ... and write the RSS sample log there
```

Individual pieces, for iteration:

```bash
lake build Cadence.Chorus                    # the per-slot consensus MODEL (no sweep) — ~90 s
lake build Cadence.Chorus.Proofs.Vote        # one action's ~96 proof cells
lake build Cadence.Chorus.Certify            # composition certificate + the 3 822-cell audit pin
lake build Cadence.Cadence Cadence.Conductor # the two small models, sweeps included
lake build Cadence.FallbackReceipt           # receipt model + its n=4 exhaustive model check
lake build Cadence                           # the audit root: every axiom pin, re-derived
```

**Reading the output.** Verification results are marked `✅` proven, `❌`
counterexample, `💥` solver crash, `⏱` timeout, and `♻` proof-cache replay
(kernel-checked). Count **all four** of the first group: grepping only for
`❌` hides timeouts and crashes. A healthy build has only `✅` and `♻`.

**Two timing regimes.** Discharged proofs are cached on disk under
`.lake/build/veilcache/` and replayed (kernel-checked) on later builds, so a
re-validation is much cheaper than a first build. A first build re-solves all
~4 000 verification conditions and reconstructs every proof: budget around 85
CPU-minutes for the Chorus family. A warm re-validation replays them instead —
on a 14-core Apple-Silicon machine, `scripts/revalidate.sh` end to end takes
under 4 minutes, with a peak of 18.8 GB resident during the cold proof-file
stage. The cache is a build artefact, not shipped, and safe to delete at any
time: it only ever skips proof *search*, never checking.

Do not run other heavy jobs concurrently with a *cold* proof-file build: some
verification conditions sit close to the solver time budget, and stolen cores
turn them into spurious timeouts.

**macOS.** A *first* native build links Mathlib as a shared library — 7 649
object files, ~987 KB of command line — and macOS caps a process's arguments
at 1 MiB, so the link fails (`could not execute external process '…/clang'`)
unless the checkout's absolute path is about 35 characters or fewer. The
container path avoids this entirely. The details, and the workarounds that do
not help, are in [docs/Container.md](./docs/Container.md) §5 and
[docs/Dependencies.md](./docs/Dependencies.md).

---

## How the proof fits together

### The commands that do the work

| Command | What it does |
|---|---|
| `veil module …` / `#gen_spec` (in the model files) | turns the declared state, actions and invariants into a transition system, and prepares one *verification condition* (VC) per action × property — "if the invariants hold and this action fires, this property still holds" — plus a does-not-throw VC per action |
| `#prove_action <Module> <action>` (one per file under `<Model>/Proofs/`) | re-creates every VC of one action from the module's persisted registry, discharges it with cvc5, **reconstructs** each `unsat` verdict as a Lean proof term that the kernel re-checks — the solver's word is never taken — persists the theorems, and emits the action's preservation lemma. Cells SMT cannot find are plain hand-written theorems in the same file, consumed after a statement check |
| `#gen_composition <Module>` (in `<Model>/Certify.lean`) | composes the per-action preservation lemmas into `<Module>.invariants_of_reachable` — every reachable state satisfies every invariant — plus one named `reachable_<property>` projection per property; kernel-checked at every step |
| `#veil_status <Module>` (pinned in `<Model>/Certify.lean`) | the audit command: walks the module's VC registry against the environment and reports, per VC, whether a real, statement-matching, kernel-checked theorem is in scope, and the axiom union over all of them. `#veil_status <Module> table` prints the full per-VC table |
| `#model_check` (receipt layer) | exhaustively explores a small concrete instance (`n = 4`, `f = 1`) — an independent, solver-free check over the same properties |
| `#gen_theorems` (the small models `Cadence/Cadence.lean`, `Cadence/Conductor.lean`) | after an in-file `#check_invariants` sweep, persists each proven VC as a named theorem in the module's `.olean` |
| `#guard_msgs in #print axioms <thm>` | the trust-base pin: the build fails unless the theorem depends on *exactly* the expected axioms |

### How the files feed each other

The Chorus leg; the other legs are smaller instances of the same shape.

```
Cadence/Chorus.lean          the MODEL: state, actions, invariants. Elaborating it
   │                         persists every VC statement (the "VC registry") — it
   │                         runs no invariant sweep and persists no proofs
   ▼ imported by
Cadence/Chorus/Proofs/*.lean one file per action (39): #prove_action re-proves every
   │                         registered VC statement of that action → real
   │                         kernel-checked proofs, plus one exported preservation
   │                         lemma ("this action preserves all invariants"). The 14
   │                         manual quorum-intersection proofs live here too
   ▼ imported by
Cadence/Chorus/Certify.lean  #gen_composition: induction over all reachable states —
   │                         one case per action, applying its preservation lemma —
   │                         plus a named projection per property; ends in its
   │                         #guard_msgs axiom pin and the #veil_status audit pin
   ▼ imported by
Cadence/Chorus/Compose.lean      hand-written end theorems: Chorus ⊨ SlotConsensus,
Cadence/Chorus/Pigeonhole.lean   and the evidence pigeonhole — each ending in its
                                 own #guard_msgs axiom pin
```

Why the per-action file layer exists, in one sentence: a module's real proofs
would otherwise all have to sit in one process's environment to be persisted,
which exceeds a 32 GB machine — one small file per action keeps every process
small, and the composition only needs one lemma per action. Those files are
ordinary hand-owned Lean files, scaffolded once by `#gen_proof_files`.

`Cadence/Cadence.lean` and `Cadence/Conductor.lean` are small enough to
persist their real proofs directly, and `Cadence/Composition.lean` consumes
them the same way. The receipt layer uses the same family shape and doubles
as the architecture's fast regression leg.

---

## What is where

```
Cadence.lean                       AUDIT ROOT: every end theorem, every axiom pin
Cadence/
  Chorus.lean                      per-slot consensus MODEL — no sweep; persists a
                                    7 605-entry VC registry (both proof encodings of
                                    each obligation), of which 3 822 cells are audited
  Chorus/Proofs/                    one proof file per action (39): #prove_action —
                                    persisted real proofs + one preservation lemma each;
                                    the manual cells live here
  Chorus/Certify.lean               #gen_composition: reachability induction + named
                                    per-property projections (axiom- and audit-pinned)
  Chorus/Compose.lean               Chorus ⊨ SlotConsensus  (axiom-pinned)
  Chorus/Pigeonhole.lean            evidence pigeonhole for every n = 3f+1  (axiom-pinned)
  Conductor.lean                   window-based orchestrator MODEL (+ sweep, traces, theorems)
  Cadence.lean                     extreme-pipelining MODEL (+ sweep, traces, theorems)
  Composition.lean                 Cadence + Conductor reachability inductions,
                                    Conductor ⊨ Orchestrator, positional MCP Safety
  FallbackReceipt.lean             fallback receipt/propose MODEL, shipped design
                                    (+ the n=4 exhaustive model check)
  FallbackReceipt/Proofs/, FallbackReceipt/Certify.lean
                                   the receipt layer's proof-file family (axiom-pinned)
  FallbackReceipt/Totality.lean    build totality for every n = 3f+1 (axiom-pinned)
  FallbackReceipt/PreFix.lean      pre-fix rules, mechanically refuted (pinned counterexample)
  Interfaces.lean                  SlotConsensus / ACS / Orchestrator contracts + obligations
  Primitives.lean                  cryptographic primitive classes (ThresholdIBE, MVBA)
  ByzQuorum.lean                   Byzantine-quorum instances, non-vacuity witnesses
  Windows.lean                     the ACS median lemma (plain Lean)
  Tooling.lean                     targeted #check_vc / #check_invariant commands
  Monitor/
    Alphabet.lean                  reflects Chorus.Label → published alphabet (JSON) + Rust stub
    ChorusMonitor.lean             model-conformance monitor (hand-written oracle) + CLI
    ChorusMonitorGen.lean          same monitor, instantiation generated by #gen_monitor
    TraceMutate.lean               corrupt a valid trace, to model implementation bugs
Containerfile                      multi-stage OCI image: toolchain / deps / dev /
                                    build / verified / verified-cache
.devcontainer/                     opens the dev image in VS Code
.github/workflows/                 CI: re-verify every commit; publish the images
scripts/                           staged build, container dispatch, monitor suites
traces/                            JSONL trace fixtures for the monitor
docs/                              see the reading guide below
```

---

## Model-conformance monitor

The proofs above establish Chorus's safety invariants over *all* reachable
states of the model. A separate, complementary question is whether a real
execution of the Rust implementation refines the model. The monitor answers
it by replaying a projected implementation trace against the model and
reporting whether the model *accepts* (simulates) it — it runs the model's own
action bodies, one trace label at a time, and a failed guard means the
implementation diverged. It is **not** model checking and not a re-proof.

```bash
scripts/run-chorus-monitor.sh < traces/fast_path_negative.jsonl
#   → ACCEPTED — 18 step(s) simulated by the model ✓   (exit 0)

scripts/test-chorus-monitor.sh        # acceptance regression (both monitors must agree)
scripts/test-monitor-divergence.sh    # negative regression: every mutated trace must be REJECTED
scripts/test-single-node-monitor.sh   # per-node projection mode
```

Design, scope, the emitter contract and the full flag reference:
[docs/Monitor.md](./docs/Monitor.md).

---

## Reading guide

| You want… | Read |
|---|---|
| The end theorems and the trust base on one page | [`Cadence.lean`](./Cadence.lean) |
| The verification architecture: methods, trust bases, and the complete meta-assumption inventory | [docs/Architecture.md](./docs/Architecture.md) |
| The Chorus model's design rationale (network abstraction and its soundness contract, property coverage, the liveness meta-argument, the bug record §7.2, open items §9) | [docs/ChorusDesign.md](./docs/ChorusDesign.md) |
| The Cadence / Conductor model designs | [docs/ConductorDesign.md](./docs/ConductorDesign.md) (module decomposition, the class layer, where the top-level properties live), then the module headers of [`Cadence/Cadence.lean`](./Cadence/Cadence.lean) and [`Cadence/Conductor.lean`](./Cadence/Conductor.lean) |
| The module contracts and their obligation tables | [`Cadence/Interfaces.lean`](./Cadence/Interfaces.lean) |
| What the two forked dependencies provide, and why | [docs/Dependencies.md](./docs/Dependencies.md) |
| Using the published images; **what a prebuilt `.olean` proves**, and the audit ladder | [docs/Container.md](./docs/Container.md) |
| Building and publishing the images (maintainers) | [docs/Images.md](./docs/Images.md) |
| The model-conformance monitor | [docs/Monitor.md](./docs/Monitor.md) |
| The liveness approach: what is safety-shaped and machine-checked, what stays temporal | [docs/ChorusDesign.md](./docs/ChorusDesign.md) §7 (what the model encodes), [docs/Liveness.md](./docs/Liveness.md) (the proposal to close the gap) |
| The project's goal and horizon: the human-edits-model / agents-maintain-proofs workflow and the audit model | [docs/Scenario.md](./docs/Scenario.md) |
| The paper's notation, and which model relation each term stands for | [docs/ChorusDesign.md](./docs/ChorusDesign.md) §2 (types) and §3.5 (the state-locality contract, with a paper-analogue column per relation) |
| The paper itself, and how it is cited | [§ The protocol paper](#the-protocol-paper) — arXiv:2607.02275v2 |
| Open items | [docs/TODO.md](./docs/TODO.md), and [docs/ChorusDesign.md](./docs/ChorusDesign.md) §9 |
| History: how the verification reached this state | [docs/History.md](./docs/History.md) |
| How to *work on* the models (workflow, gotchas) | [CLAUDE.md](./CLAUDE.md) |

## The protocol paper

The models are verified against the Cadence preprint:

> Kushal Babel, Fatima Elsheimy, Lioba Heimbach, Mohammad Mussadiq Jalalzai,
> Tobias Klenze, Jovan Komatovic, Jason Milionis, Mike Setrin, Victor Shoup.
> **Cadence: Extreme Pipelining with Multiple Concurrent Proposers.**
> arXiv:[2607.02275](https://arxiv.org/abs/2607.02275) \[cs.DC].

This development verifies **v2** (2026-07-07). v1 (2026-07-02) contained a
liveness bug in the fallback receipt rules, corrected in v2. Both versions are
modelled: [`Cadence/FallbackReceipt.lean`](./Cadence/FallbackReceipt.lean)
verifies the v2 design, and
[`Cadence/FallbackReceipt/PreFix.lean`](./Cadence/FallbackReceipt/PreFix.lean)
mechanically refutes the v1 rules.

### Resolving a citation

The sources and documentation cite the paper by its LaTeX `\label` names —
`lemma:chorus-agreement`, `alg:fallback`, `mod:slotconsensus`,
`line:fb-pathvote-guard`. Citations are to v2 unless the surrounding text says
otherwise.

These labels are grep targets rather than hyperlinks: the PDF is compiled with
`hypertexnames=false` and carries no label-named destinations, and arXiv's HTML
rendering substitutes its own generated ids. To resolve one, fetch the paper
source, whose file layout is what the references name (`src/p2_chorus.tex`,
`src/alg_fallback.tex`, `src/p2_conductor_proofs.tex`, …):

```bash
mkdir -p papers/cadence && curl -sL https://arxiv.org/e-print/2607.02275v2 \
  | tar -xz -C papers/cadence
grep -rn 'label{lemma:chorus-agreement}' papers/cadence/src/
```
