# Building and auditing in a container

Everything in this repository can be built and re-checked inside a Linux
container, and for most readers that is the easiest path — on macOS it is
currently the *only* turnkey path (see [§5](#5-why-a-container-at-all)).

The image is a plain multi-stage OCI build, [`../Containerfile`](../Containerfile).
It assumes no particular runtime: build it with Apple's `container`, with
podman, or with docker. [`../scripts/container.sh`](../scripts/container.sh)
only dispatches.

## 1. Quick start

```bash
RUNTIME=podman scripts/container.sh build deps      # dependencies, once (11 min)
RUNTIME=podman scripts/container.sh build verified  # + this project (11 min)
RUNTIME=podman scripts/container.sh check           # kernel-re-check everything (4 min)
RUNTIME=podman scripts/container.sh verify          # re-verify against your sources (1 min)
RUNTIME=podman scripts/container.sh shell           # interactive shell
```

**Build the images with podman or docker.** Apple's `container` runs them
perfectly well, but it cannot *build* them on a machine this size — see
[§ Sizing the image build](#sizing-the-image-build).

Runtime and resources are environment variables:

```bash
RUNTIME=podman scripts/container.sh verify     # container | podman | docker
CPUS=8 MEMORY=16G scripts/container.sh verify
```

Sources are bind-mounted **read-only** and copied in, so a container never
writes to your checkout. `.lake` — the dependency tree, the oleans and the
proof cache, ~17 GB — lives in a named volume, which is also what keeps build
I/O off the (much slower) host-shared filesystem.

### Sizing the image build

Building the `deps` layer elaborates the whole dependency tree, and that is the
most memory-hungry thing in this project. Two traps:

* Apple's `container` builds images inside a **separate builder VM** whose
  resources are independent of `container run`, defaulting to **2 CPUs / 2 GB**.
  That is far too small: the dependency layer stalls part-way through Veil with
  no error message at all. `scripts/container.sh` resizes it for you
  (`BUILDER_CPUS`, `BUILDER_MEMORY`, default 8 / 24G); by hand it is
  `container builder stop && container builder start --cpus 8 --memory 24G`.
  Podman and docker build inside their normal machine, so size that instead.
* **Lake has no job-limit flag**, so the only lever on peak memory is the VM's
  CPU count — fewer CPUs, fewer concurrent Lean processes. Measured: 12 CPUs
  with 20 GB runs out of memory in `Auto.Embedding.LamPrep`; 8 CPUs with 24 GB
  completes. If you see `cannot allocate memory`, lower `BUILDER_CPUS` before
  raising `BUILDER_MEMORY`.

Apple's `container` could not build the `deps` layer at all on a 36 GB machine:
its builder OOMs in `Auto.Embedding.LamPrep` even at 8 CPUs / 24 GB, because it
must hold the ~12 GB accumulating layer *as well as* the elaboration. Podman
builds the same Containerfile in 11 minutes, because its overlay storage is on
the machine's disk. So: **build with podman or docker; run with whatever you
like.**

`check` has its own memory trap, and the script handles it: `leanchecker`
allocates aggressively per worker thread, and at the default (one per core) it
wants ~19 GB and is OOM-killed inside a 20 GB container 11 seconds in. Measured
on the Chorus model alone: 12 threads → killed; 4 threads → 131 s at an 11.0 GB
peak; 2 threads → 226 s at 4.8 GB. All 66 modules at
`LEAN_NUM_THREADS=4` take 4 min 12 s with a 12.9 GB peak, which is what the
script sets. Lower it if you have less memory.

None of this affects the *staged verification* — `verify` is comfortable at
12 CPUs / 20 GB, because `scripts/revalidate.sh` bounds concurrency itself.

For an editor, open the folder in VS Code with the **Dev Containers**
extension; [`../.devcontainer/devcontainer.json`](../.devcontainer/devcontainer.json)
builds the same `dev` stage. That extension drives a *Docker-compatible* CLI, so
it works with podman (`"dev.containers.dockerPath": "podman"`) or docker, but
**not** with Apple's `container`, which exposes no Docker socket. Use the script
with that runtime.

## 2. The image stack

| stage | contains | size | for |
|---|---|---|---|
| `toolchain` | OS, clang + version-matched libc++, Node, elan, the pinned Lean toolchain | 3.5 GB | base layer |
| `deps` | + **the whole dependency tree built**: Mathlib, Loom, lean-smt, auto, cvc5, Veil | 12.4 GB | nobody should rebuild this |
| `dev` | + ripgrep, jq, … — the devcontainer base; sources mounted | 12.4 GB | development |
| `verified` | + this project's own oleans — **no proof cache** | **13.1 GB** | reading and auditing (tiers 1, 2a) |
| `verified-cache` | + Veil's proof cache | 17.5 GB | re-elaborating without re-solving (tiers 2b, 3) |

Measured with podman on arm64: `deps` builds in **11 min 13 s**, `verified` in a
further **10 min 32 s** with a seeded proof cache. The `verified` build runs the
staged verification *inside the image*, so its oleans come from a run that
printed `ALL STAGES GREEN` — every axiom pin and both `#veil_status` pins
included.

Two things about `deps` that are easy to get wrong:

* **The workspace path is baked in** (`/workspaces/cadence`). Lake records
  absolute paths in its trace files, so a build tree is only reusable at the
  path it was built at. Anything that mounts sources over the image must use the
  same path — which is why `devcontainer.json` pins `workspaceFolder`.
* A bind mount of your checkout would **shadow** the image's `.lake`. Both entry
  points therefore keep `.lake` in a volume and seed it once from
  `/opt/cadence-lake-seed` inside the image.

`verified` builds the project inside the image. Veil's proof cache reaches it as
a **build-time bind mount** (`RUN --mount=type=bind,source=.veilcache-seed`), so
it is used during the build without ever entering a layer; `scripts/container.sh
build verified` fills that directory from your local cache. With the seed the
stage takes ~11 minutes because proofs are replayed; without it, ~90, because
cvc5 solves every verification condition. Replay is not a shortcut around
checking — every cache hit is kernel-checked before use — so the oleans are
equally trustworthy either way, and the build prints `ALL STAGES GREEN` from
inside the image in both cases.

Pull `verified`, not `verified-cache`, unless you intend to re-elaborate the
project: nothing in tier 1 or 2a reads the cache.

### What actually crosses the wire

The sizes above are uncompressed, on-disk. A registry stores and transfers
*compressed* layers, so a pull is roughly a third of that. Measured by pushing
to a local `registry:2` and reading the resulting manifests, which record exact
compressed layer sizes:

| image | on disk | first pull (gzip) | ratio |
|---|---|---|---|
| `deps` | 12.4 GB | 3.71 GiB | 3.3× |
| `dev` | 12.3 GB | 3.73 GiB | 3.3× |
| **`verified`** | 13.1 GB | **3.96 GiB** | 3.3× |
| `verified-cache` | 17.5 GB | 5.30 GiB | 3.3× |

So **an auditor pulls about 4 GiB**, not 13 GB. Publishing the whole set costs
**5.32 GiB** of registry storage, not the 55 GB the four on-disk figures suggest,
because the shared layers are stored once.

Where `verified`'s 3.96 GiB goes: Ubuntu base 29 MiB · clang/libc++/Node
201 MiB · elan 5 MiB · Lean toolchain 740 MiB · the whole dependency tree
2825 MiB · this project's oleans 251 MiB.

Because layers are shared, the second image is nearly free:

| you already have | pulling | costs |
|---|---|---|
| `deps` | `dev` | 21 MiB |
| `deps` or `dev` | `verified` | 251 MiB |
| `verified` | `verified-cache` | 1371 MiB |

**Build every target in one pass before pushing.** Layer sharing only happens
when the images were built from the same Containerfile state. While preparing
this I left a `deps` tag one build stale, and it cost an extra 2.8 GiB of
registry storage and turned that 251 MiB pull into a 3 GiB one — with nothing to
warn you, since both images work fine.

zstd instead of gzip saves about 9 % (`verified` 3.59 GiB, `verified-cache`
4.75 GiB) and compresses a little slower. It is not obviously worth it here:
gzip is pullable by every client, whereas zstd layers need a recent one (podman
4+, or docker with the containerd image store). Use `--compression-format zstd`
if you know your consumers.

### Why the images are the size they are

They are close to irreducible, and it is worth knowing why before trying to
shrink them. Measured by asking `lake build --no-build` — which reports whether
anything is out of date without doing the work — after removing each candidate:

| candidate | size | can it go? |
|---|---|---|
| `lib/lean` in the Lean toolchain | 2.5 GB | **no** — 1.1 GB of `*.olean.private`, 331 MB of `*.olean`, 226 MB of shared libraries. This is just Lean 4.28 on arm64 |
| installed clang-18 + libc++ + Node | 722 MB | **no** — the cvc5 binding's FFI shim hardcodes `clang -std=c++17 -stdlib=libc++`, and Veil's widget target needs `npm` |
| Mathlib's `.olean` tree | 5.6 GB | **no** — this is what you are here for |
| generated `.c` files | 485 MB | **no** — a declared lake output; removing it makes every module out of date |
| native objects (`.c.o.export`) | 374 MB | **no** — likewise |
| `.ilean` editor metadata | 259 MB | **no** — likewise (lake tracks it per module) |
| dependency `.git` checkouts | 544 MB | **no**, and dangerously so: lake re-resolves a git dependency whose `.git` is missing and *deletes the checkout* to re-clone it |
| toolchain static archives (`libLean.a` …) | 363 MB | prunable, but not *reclaimable*: they live in the `toolchain` layer, where `deps` still needs them to link Mathlib's `cache` executable, and a delete in a later layer frees nothing |
| widget `node_modules` + npm cache | 113 MB | **yes** — removed in the same layer that creates them |

The one genuinely large saving was a bug rather than fat: the proof cache used to
be stored **twice** — once by `COPY .`, once by the `RUN` that installed it —
because a `rm` in a later layer reclaims nothing. Fixing that plus splitting the
cache into `verified-cache` took the audit image from 22 GB to 13.1 GB.

A `.containerignore` keeps the build context to the sources. Without it `COPY .`
would ship a developer's local `.lake` — up to 17 GB — *over* the image's
prebuilt dependency tree, quietly producing a broken image.

## 3. What an olean does and does not establish

This is the part worth reading slowly, because it decides what a published
`verified` image is worth.

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
RUNTIME=podman scripts/container.sh shell
# inside the container:
rm -rf .lake/build/lib/lean/Cadence .lake/build/lib/lean/Cadence.*
bash scripts/revalidate.sh /tmp        # 9 min 12 s, proof cache retained
```

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

## 6. Publishing

No CI publishes these images yet. To do it by hand:

```bash
REG=ghcr.io/<org>
TAG=$(git rev-parse --short HEAD)

# Build every target first, in one pass, so they share layers (see above).
for t in deps dev verified verified-cache; do
  RUNTIME=podman scripts/container.sh build $t
done

for t in deps dev verified verified-cache; do
  podman tag  cadence-$t $REG/cadence-$t:$TAG
  podman push --compression-format gzip $REG/cadence-$t:$TAG
done
```

That uploads 5.32 GiB in total. Most consumers only ever want `verified`
(3.96 GiB), so consider tagging that one `:latest` as well.

Tag images by the **commit they were built from** — an image whose provenance is
unclear is worth nothing for tier 1, since the whole claim is "these oleans came
from that source". `deps` only changes when `lake-manifest.json` or the toolchain
does, so re-publishing after a source change costs just the 251 MiB project
layer.
