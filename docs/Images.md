# Building and publishing the images

How the container images are built, why they are the size they are, and how CI
publishes them. This is maintainer material: *using* the published images —
auditing, developing, the devcontainer — is [Container.md](./Container.md) and
needs nothing from this page. Building locally is needed only when the
dependency tree (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`) or
the `Containerfile` changes — and CI rebuilds and republishes on exactly those
changes by itself, so even then a local build is a convenience, not a duty.

## 1. Building locally

```bash
RUNTIME=podman scripts/container.sh build deps      # dependencies (11 min)
RUNTIME=podman scripts/container.sh build verified  # + this project (11 min seeded)
RUNTIME=podman scripts/container.sh build dev       # devcontainer base
RUNTIME=podman scripts/container.sh build verified-cache
```

Measured with podman on arm64: `deps` builds in **11 min 13 s**, `verified` in
a further **10 min 32 s** with a seeded proof cache.

The stages, in [`../Containerfile`](../Containerfile): `toolchain` → `deps` →
(`dev`, `build`) — where `build` runs the staged verification and keeps the
proof cache it produced — then `verified` (the built workspace *minus* the
cache) and `verified-cache` (`verified` *plus* exactly that cache).
`verified-cache` refuses to build with an empty cache: publishing one would
silently break the CI seed chain.

**The proof-cache seed.** The `build` stage reads `.veilcache-seed` from the
build context as a build-time bind mount, so the seed never enters a layer;
`scripts/container.sh build verified` fills that directory from your local
cache (or from `VEILCACHE=<dir>`). With a seed the verification replays,
kernel-checked, in ~11 minutes; without one cvc5 re-solves every verification
condition, ~90 minutes on a workstation. The image is equally trustworthy
either way — every cache hit is kernel-checked before use — and prints
`ALL STAGES GREEN` from inside the build in both cases.

**BATCH.** `scripts/revalidate.sh`'s proof-file batch width is a build ARG
(default 6, sized for a workstation). On few cores lower it — near-limit VCs
time out spuriously under discharger contention, and a cold run at width 6
peaks ~30 GB. CI passes `BATCH=1` for its 4-vCPU runners.

### Sizing the image build

Building the `deps` layer elaborates the whole dependency tree, the most
memory-hungry thing in this project.

* **Build with podman or docker; run with anything.** Apple's `container`
  runs the images fine, but builds inside a **separate builder VM** that it
  cannot size large enough here: the builder must hold the ~12 GB
  accumulating layer *as well as* the elaboration, and OOMs in
  `Auto.Embedding.LamPrep` even at 8 CPUs / 24 GB on a 36 GB machine. (With
  its 2 CPU / 2 GB defaults the build stalls with no error at all;
  `scripts/container.sh` resizes the builder automatically — `BUILDER_CPUS`,
  `BUILDER_MEMORY`, default 8 / 24G.) Podman builds the same Containerfile in
  11 minutes, because its overlay storage is on the machine's disk.
* **Lake has no job-limit flag**, so the only lever on peak memory is the CPU
  count — fewer CPUs, fewer concurrent Lean processes. Measured: 12 CPUs with
  20 GB runs out of memory in `Auto.Embedding.LamPrep`; 8 CPUs with 24 GB
  completes. If you see `cannot allocate memory`, lower the CPU count before
  raising memory.

## 2. Layer sharing, and what crosses the wire

The on-disk and pull sizes are tabulated in
[Container.md §2](./Container.md#2-the-images). The registry-side view:
publishing the whole four-image set costs **5.32 GiB** of storage, not the
55 GB the on-disk figures suggest, because shared layers are stored once.
Where `verified`'s 3.96 GiB goes: Ubuntu base 29 MiB · clang/libc++/Node
201 MiB · elan 5 MiB · Lean toolchain 740 MiB · the whole dependency tree
2825 MiB · this project's oleans 251 MiB.

**Build every target in one pass before pushing.** Layer sharing only happens
when the images were built from the same Containerfile state. Leaving one tag
a build stale costs about 2.8 GiB of registry storage and turns a 251 MiB pull
into a 3 GiB one. Nothing warns about it, because both images still work.

zstd instead of gzip saves about 9 % (`verified` 3.59 GiB, `verified-cache`
4.75 GiB) and compresses a little slower — a poor trade by default, since gzip
is pullable by every client whereas zstd layers need a recent one (podman 4+,
or docker with the containerd image store). Use `--compression-format zstd`
only if the consumers are known.

## 3. Why the images are the size they are

They are close to irreducible. Each candidate below was measured by removing
it and asking `lake build --no-build`, which reports whether anything is out of
date without doing the work:

| candidate | size | can it go? |
|---|---|---|
| `lib/lean` in the Lean toolchain | 2.5 GB | **no** — 1.1 GB of `*.olean.private`, 331 MB of `*.olean`, 226 MB of shared libraries. This is just Lean 4.28 on arm64 |
| installed clang-18 + libc++ + Node | 722 MB | **no** — the cvc5 binding's FFI shim hardcodes `clang -std=c++17 -stdlib=libc++`, and Veil's widget target needs `npm` |
| Mathlib's `.olean` tree | 5.6 GB | **no** — the prebuilt dependency the images exist to ship |
| generated `.c` files | 485 MB | **no** — a declared lake output; removing it makes every module out of date |
| native objects (`.c.o.export`) | 374 MB | **no** — likewise |
| `.ilean` editor metadata | 259 MB | **no** — likewise (lake tracks it per module) |
| dependency `.git` checkouts | 544 MB | **no**, and dangerously so: lake re-resolves a git dependency whose `.git` is missing and *deletes the checkout* to re-clone it |
| toolchain static archives (`libLean.a` …) | 363 MB | prunable, but not *reclaimable*: they live in the `toolchain` layer, where `deps` still needs them to link Mathlib's `cache` executable, and a delete in a later layer frees nothing |
| widget `node_modules` + npm cache | 113 MB | **yes** — removed in the same layer that creates them |

The general rule behind the table: a `rm` in a later layer reclaims nothing, so
anything copied in must be consumed or deleted **in the same layer**. Keeping
the proof cache out of `verified` and adding it to `verified-cache` as a single
layer is what keeps the audit image at 13.1 GB rather than 22 GB.

A `.containerignore` keeps the build context to the sources. Without it `COPY .`
would ship a developer's local `.lake` — up to 17 GB — *over* the image's
prebuilt dependency tree, quietly producing a broken image.

## 4. Publishing

Two GitHub Actions workflows do this, in
[`../.github/workflows`](../.github/workflows):

| Workflow | Trigger | What it does |
|---|---|---|
| `verify.yml` | every push to the default branch, every pull request | pulls the published `verified` image and re-runs the staged verification against the commit's sources — the per-commit gate. It builds no images |
| `publish-images.yml` | push to the default branch; manual | rebuilds and publishes `verified` + `verified-cache` for both architectures and combines the `:latest` manifest lists. `deps`/`dev` are rebuilt only when `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` or the `Containerfile` changes, or on request |

The split matters because the two halves cost very different amounts: `deps` is
the whole dependency tree, `verified` is this project on top of it.

**How the layer-sharing rule is enforced.** Rather than trusting that the tags
were built in one pass, `publish-images.yml` resolves the published `deps` to
its **digest** and passes it as the `DEPS_IMAGE` build argument, so `verified`
is layered onto exactly the image already in the registry. A later step then
asserts that the two share every base layer and fails the run if they do not —
without it the drift is invisible, because both images work perfectly either
way. The default of that argument is the in-file `deps` stage, so a local
`scripts/container.sh build verified` is unaffected.

**Bootstrap.** The first run must be a manual `publish-images` with
`rebuild_deps: true`. Its `verified` build has no published proof cache to seed
from, so it re-solves every verification condition (slow — hours on a hosted
runner, which the workflow keeps inside its memory by passing `BATCH=1`).
Every run after that seeds from the previous `verified-cache` image, which
carries **the cache that build produced** — the seed plus everything solved
fresh, at `/workspaces/cadence/.lake/build/veilcache`; the `verified-cache`
stage refuses to build with an empty cache, and the workflow's seed step skips
an empty candidate in favour of the other architecture's, since the cache is
architecture-portable. So the cache sustains and refreshes itself without
depending on the Actions cache, whose 10 GB budget and weekly eviction suit it
poorly. If one architecture's cold leg fails during bootstrap, re-run the
failed jobs once the other's cache is published — the re-run seeds across
architectures and runs warm.

**Architecture.** The published `:latest` tags are manifest lists covering
`linux/arm64` and `linux/amd64`. An x86 stage cannot be layered onto an arm64
base — and a cross-build under qemu makes Lean elaboration 10–20× slower — so
`publish-images.yml` builds each architecture natively on its own runner
(`ubuntu-24.04-arm` / `ubuntu-24.04`), pushes arch-suffixed tags
(`:latest-arm64`, `:latest-amd64`), and combines each pair into the `:latest`
list with `docker buildx imagetools create` in a final job. Everything
per-architecture — the `DEPS_IMAGE` digest pin, the layer-sharing assertion,
the attestations — runs inside a matrix leg against that leg's own arch tag;
nothing ever pins the list. Consumers just pull `:latest` and get their
platform's entry. The proof cache is architecture-portable (its key is the
closed goal statement), so the two legs seed from each other's
`verified-cache` when their own is missing; only `verify.yml` stays
single-architecture (arm64, matching a local Apple Silicon build), because the
proofs are architecture-independent and the amd64 image verifies inside its
own build.

**Seeding the registry from a local build.** The first publish does not have to
be a cold CI build. If the four images already exist locally — and share their
layers, which `scripts/container.sh build` in one pass guarantees — pushing
them *is* the bootstrap, and every later CI run seeds its proof cache from the
`verified-cache` image it finds there:

```bash
REG=ghcr.io/<owner>
ARCH=$(uname -m | sed 's/aarch64/arm64/; s/x86_64/amd64/')
printenv CR_PAT | podman login ghcr.io -u <owner> --password-stdin
for t in deps dev verified verified-cache; do        # deps first: later pushes
  podman tag  cadence-$t $REG/cadence-$t:latest-$ARCH # then skip the layers it
  podman push $REG/cadence-$t:latest-$ARCH            # already has
done
```

Seed the arch-suffixed tag, not `:latest`: the workflow's per-architecture
legs pull `latest-<arch>`, and `:latest` is the manifest list its `combine`
job assembles from the two — a plain image pushed over it would break the
other architecture's consumers until the next publish. The `verified` image
this publishes is only as current as the sources it was built from, so let CI
rebuild it on the next push; the point of the exercise is the cache, which is
content-addressed, architecture-portable, and stays valid across any change
that does not alter a verification condition — a single seeded architecture
warms both legs.

**Resource notes.** A standard runner has ~14 GB free disk against a job that
needs ~25 GB, so both workflows reclaim the preinstalled toolchains first; and
the dependency build has been measured to OOM at 12 CPUs / 20 GB, against a
runner's 16 GB — but a hosted runner's 4 vCPUs mean fewer concurrent Lean
processes and a lower peak, and the 2026-08 bootstrap run confirmed the whole
pipeline, `deps` build included, fits a standard runner. If a future
dependency tree will not, that job needs a larger runner.

To publish by hand instead:

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
