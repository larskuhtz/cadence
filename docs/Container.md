# Auditing and developing in a container

Everything in this repository can be re-checked and developed inside a Linux
container, and for most readers that is the easiest path — on macOS it is
currently the *only* turnkey path (see [§5](#5-why-a-container-at-all)).

The images are built and verified by CI and published for `linux/arm64` and
`linux/amd64`: `ghcr.io/larskuhtz/cadence-{verified,dev,deps,verified-cache}`.
[`../scripts/container.sh`](../scripts/container.sh) pulls the image a command
needs on first use — nothing has to be built. Building the images yourself,
and how CI publishes them, is [Images.md](./Images.md); that is needed only
when the dependency tree or the Containerfile changes.

## 1. Quick start

```bash
RUNTIME=podman scripts/container.sh check    # kernel-re-check every proof (4 min)
RUNTIME=podman scripts/container.sh verify   # re-verify against your sources (~1 min unmodified)
RUNTIME=podman scripts/container.sh shell    # interactive shell in the workspace
```

The first command pulls the `verified` image (~4 GiB) by itself. `check` and
`verify` are tiers 1 and 2a of the audit ladder — [§4](#4-the-audit-ladder)
says what each establishes, and how to go further.

Runtime and resources are environment variables:

```bash
RUNTIME=podman scripts/container.sh verify     # container | podman | docker
CPUS=8 MEMORY=16G scripts/container.sh verify
```

Sources are bind-mounted **read-only** and copied in, so a container never
writes to your checkout. `.lake` — the dependency tree, the oleans and the
proof cache, ~17 GB — lives in a named volume, one per image, which the
runtime seeds from the image on first use; the volume also keeps build I/O
off the (on macOS, slower) host-shared filesystem.

To move to a newer published image, refresh it and re-seed its volume:

```bash
RUNTIME=podman scripts/container.sh pull     # verified; or: pull dev verified-cache …
podman volume rm cadence-lake-verified       # was seeded from the old image
```

`check` has a memory trap, and the script handles it: `leanchecker` allocates
aggressively per worker thread, and at the default (one per core) it wants
~19 GB and is OOM-killed inside a 20 GB container 11 seconds in. Measured on
the Chorus model alone: 12 threads → killed; 4 threads → 131 s at an 11.0 GB
peak; 2 threads → 226 s at 4.8 GB. All 66 modules at `LEAN_NUM_THREADS=4`
take 4 min 12 s with a 12.9 GB peak, which is what the script sets. Lower it
if you have less memory. `verify` needs no such care —
`scripts/revalidate.sh` bounds its own concurrency and is comfortable at
12 CPUs / 20 GB.

For an editor, open the folder in VS Code with the **Dev Containers**
extension; [`../.devcontainer/devcontainer.json`](../.devcontainer/devcontainer.json)
uses the published `dev` image, so nothing is built there either. The
extension drives a *Docker-compatible* CLI: podman works
(`"dev.containers.dockerPath": "podman"`), docker works, but Apple's
`container` does not — it exposes no Docker socket. Use the script with that
runtime.

## 2. The images

| image | contains | on disk | first pull | for |
|---|---|---|---|---|
| `deps` | the whole dependency tree built: Mathlib, Loom, lean-smt, auto, cvc5, Veil | 12.4 GB | 3.71 GiB | base of everything |
| `dev` | + ripgrep, jq, … — the devcontainer base; sources mounted | 12.4 GB | 3.73 GiB | working on the models |
| `verified` | + this project's own oleans — **no proof cache** | 13.1 GB | **3.96 GiB** | reading and auditing (tiers 1, 2a) |
| `verified-cache` | + Veil's proof cache | 17.5 GB | 5.30 GiB | re-elaborating without re-solving (tiers 2b, 3) |

A registry transfers *compressed* layers, so a pull is about a third of the
on-disk size — and the images share their base layers, so the second image is
nearly free:

| you already have | pulling | costs |
|---|---|---|
| `deps` | `dev` | 21 MiB |
| `deps` or `dev` | `verified` | 251 MiB |
| `verified` | `verified-cache` | 1371 MiB |

Pull `verified`, not `verified-cache`, unless you intend to re-elaborate the
project: nothing in tier 1 or 2a reads the cache.

The `verified` image is built by running the staged verification *inside* the
image build, so its oleans come from a run that printed `ALL STAGES GREEN` —
every axiom pin and both `#veil_status` pins included. What that is worth to a
reader, and what it leaves open, is §3–§4.

Two things about the images that are easy to get wrong:

* **The workspace path is baked in** (`/workspaces/cadence`). Lake records
  absolute paths in its trace files, so a build tree is only reusable at the
  path it was built at. Anything that mounts sources over the image must use the
  same path — which is why `devcontainer.json` pins `workspaceFolder`.
* A bind mount of your checkout would **shadow** the image's `.lake`. Both
  entry points therefore keep `.lake` in a named volume, which the runtime
  initialises from the image's content the first time it is mounted.

## 3. What an olean does and does not establish

This section decides what a published `verified` image is worth, so it is the
part an auditor should read closely.

* **`import` never re-typechecks.** An `.olean` is a serialized image of a
  module's environment; importing it memory-maps the file and merges the
  declarations as they are. No kernel work happens. An olean is the *only*
  form of persistence in this project that is trusted without a re-check.
* **Elaborating a module from source does check it**: every `theorem` and `def`
  goes through the kernel on the way into the environment. So the same module is
  checked when built and trusted when loaded.
* **The Veil proof cache is a third case.** On a hit at build time the stored
  proof term is re-checked by the kernel before anything depends on it. But a
  recipient of the resulting olean did not witness that.
* **`#print axioms` recomputes** the axiom closure by walking the stored
  declarations. It is cheap and it typechecks nothing: it tells you what the
  stored proof depends on, *assuming that proof is well-typed*.
* **`leanchecker` replays declarations from the oleans through the kernel.**
  That is what turns the first bullet into a verified claim.

## 4. The audit ladder

Each tier is a superset of the one above it. Times measured on a 14-core
Apple-Silicon machine.

| tier | what you check | how | measured |
|---|---|---|---|
| 0 | nothing — you read the sources and trust the image | — | — |
| 1 | every stored proof is well-typed, and every axiom footprint is as claimed | `scripts/container.sh check` | **4 min 08 s** |
| 2a | tier 1, **plus** that the image's oleans correspond to these sources — on lake's source hashing | `scripts/container.sh verify` | **1 min** |
| 2b | as 2a, but the elaborator actually redoes the project rather than trusting a trace file | delete the project oleans, then re-verify (below) — needs `verified-cache` | **9 min 12 s** |
| 3 | as 2b with no cached proof reused: every verification condition re-solved by cvc5 and re-reconstructed | as 2b from `verified`, whose image has no cache | ~90 min |

Tier 1 is what makes a published image worth having: Lean's kernel over all 66
modules — the 3 808 reconstructed Chorus proofs included — in four minutes, with
**no** SMT solver, no tactic execution and no elaboration. Silence is success.

Tier 2 comes in two strengths, and the difference is worth understanding.
`verify` on unmodified sources completes in about a minute with every stage
green: lake compares each source file's hash against the trace it recorded when
the olean was built, finds them equal, and rebuilds nothing. That *is* a
source-to-olean correspondence check — but it rests on lake's hashing and trace
bookkeeping, not on Lean. To make the elaborator redo the work:

```bash
IMAGE=cadence-verified-cache RUNTIME=podman scripts/container.sh shell
# inside the container:
rm -rf .lake/build/lib/lean/Cadence .lake/build/lib/lean/Cadence.*
bash scripts/revalidate.sh /tmp        # 9 min 12 s, proof cache retained
```

On few cores, set `BATCH=1` (it passes through `scripts/container.sh` into
`revalidate.sh`): the default batch of 6 proof files makes concurrent
dischargers contend for wall-clock, and near-limit verification conditions
then time out spuriously — VCs that pass comfortably built alone. Measured
by the 2026-08 external audit on 8 cores: 21 s alone against a 60 s budget,
versus a timeout inside a batch of 6. This matters only when VCs are
actually re-solved (tier 3, or edited files); cache replays do not contend.

Tier 3 additionally throws away the proof cache, so cvc5 re-derives every
verification condition and Lean re-reconstructs every proof term. That is the
strongest thing you can do short of auditing Veil itself, and it is what
`IMAGE=cadence-dev scripts/container.sh verify` does from a fresh volume.

Be clear about the gap between tiers 1 and 2. Tier 1 proves the proofs in the
image typecheck with the claimed axioms. It does *not* prove those oleans were
produced from the source you are reading — the statements. Only a rebuild
establishes that correspondence, which is tier 2, and why the proof cache is
worth shipping: it makes tier 2 fifteen minutes rather than an hour and a half.

For the complementary question — what the *statements* mean, and what is
assumed rather than proven — see [Architecture.md](./Architecture.md) §4.

**Reproduction note — `libLake_shared.so` (auditing outside these
images).** In a fresh Linux environment that is not one of the images
above (an auditor's own container, say), the Veil frontend can fail to
load with `error loading library, libLake_shared.so: cannot open shared
object file`. The library ships with the Lean toolchain; export

```bash
TC="$HOME/.elan/toolchains/<toolchain>"
export LD_LIBRARY_PATH="$TC/lib/lean:$TC/lib:${LD_LIBRARY_PATH:-}"
```

before `lake build` (this is exactly what `scripts/run-chorus-monitor.sh`
does for the interpreter). The published images and the devcontainer do
not need this. Reported by the 2026-08 external audit.

## 5. Why a container at all

Veil's library is built with `precompileModules`, which forces a shared-library
link of all of Mathlib: ~7 650 object files, about 987 KB of command line. macOS
caps a process's arguments plus environment at 1 MiB, and each character of the
checkout's absolute path costs ~7.6 KB across that object list — so on macOS the
link fails unless the checkout path is around 35 characters or shorter. On Linux
the limit is `RLIMIT_STACK/4`, 2 MiB by default, and the same link takes **under
a second**.

Measured, container (Apple `container`, 12 vCPU/24 GB) against the macOS host
(14 cores), same seeded proof cache:

| | container | macOS |
|---|---|---|
| all native compilation (7 653 Mathlib objects + the Mathlib shared link + Veil) and the two small model sweeps | **373 s** | 2 362 s, then **fails at the link** |
| the Mathlib shared link alone | 0.8 s | not possible |
| Chorus model | 119 s | 118 s |
| seven Chorus proof batches (kernel replay) | 19–28 s | 18–28 s |
| certificates incl. the 3 822-cell audit walk | 23 s | 24 s |
| no-op `lake build` | 5.3 s | 5.2 s |
| edit one proof file, rebuild | 25 s | ~25 s |
| cold end-to-end, empty volume | **~15.5 min** | not possible |

So steady-state development in a container is indistinguishable from native, and
the cold native phase is both possible and about six times faster — almost
certainly macOS process-spawn overhead across 7 650 short-lived compiler
invocations.

## 6. Building and publishing the images

In [Images.md](./Images.md): building the images locally, sizing the image
build, the layer-sharing rules, why the images are the size they are, and the
CI pipeline that publishes them. None of it is needed to *use* the published
images.
