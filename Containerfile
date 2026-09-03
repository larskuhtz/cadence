# syntax=docker/dockerfile:1
#
# Cadence — machine-checked verification: container image stack.
#
# A plain multi-stage OCI build. It is deliberately runtime-agnostic: build it
# with `container build`, `podman build` or `docker build`; the accompanying
# scripts/container.sh only dispatches, it adds no requirements of its own.
#
#   toolchain   OS + clang/libc++ + node + elan + the pinned Lean toolchain
#     └─ deps   + the whole dependency tree BUILT (Mathlib, Loom, lean-smt,
#     │           auto, cvc5, Veil). This is the layer nobody should have to
#     │           rebuild, and the reason the stack exists.
#     ├─ dev    + development conveniences; the devcontainer base. Source is
#     │           mounted; .lake comes from a volume seeded off this image.
#     ├─ build  + the staged verification run, with the proof cache it
#     │           produced. Never published; the two images below are carved
#     │           out of it.
#     ├─ verified
#     │         + this project's own oleans (no proof cache): a reader can
#     │           kernel-re-check every proof in ~4 minutes without running a
#     │           solver, elaborating anything, or building at all.
#     │           See docs/Container.md for what that does and does not prove.
#     └─ verified-cache
#               + the proof cache `build` produced (+4.1 GB). Only needed to
#                 re-elaborate the project without re-solving every
#                 verification condition.
#
# BUILD THIS WITH PODMAN OR DOCKER. Apple's `container` runs these images fine,
# but its image builder is a separate memory-limited VM that cannot produce the
# ~13 GB `deps` layer on a 36 GB machine (it OOMs in `Auto.Embedding.LamPrep`
# even at 24 GB, because the builder must hold the accumulating layer as well as
# the elaboration). Podman builds it in 11 minutes. See docs/Container.md.
#
# Why containers at all: a fixed, published environment — the toolchain, the
# whole dependency tree and (in the `verified` image) this project's own
# oleans, so an auditor re-checks the proofs without building anything, and CI
# and a reviewer run the identical tree. Native builds work on Linux and macOS
# alike; see docs/Container.md.

# The base of the `verified` stage. Defaults to the `deps` stage in this file,
# which is what a local `scripts/container.sh build verified` uses. CI overrides
# it with a published image *pinned by digest*, so that `verified` is layered
# onto exactly the `deps` image already in the registry rather than onto a
# freshly re-executed stage. Container builds are not bit-reproducible (apt
# resolves versions at build time, files carry timestamps), so re-executing
# `deps` yields different layer digests for the same logical content — and two
# images that no longer share a base cost several GiB of extra registry storage
# and turn a 251 MiB pull into a ~3 GiB one, with nothing failing to warn you.
# Overriding this ARG makes that sharing structural instead of a discipline.
ARG DEPS_IMAGE=deps

# ---------------------------------------------------------------- toolchain --
FROM ubuntu:24.04 AS toolchain

ARG DEBIAN_FRONTEND=noninteractive

# `clang -std=c++17 -stdlib=libc++` is hardcoded by the cvc5 Lean binding's FFI
# shim (a transitive dependency of Veil via lean-smt), so a matching libc++
# development package must be present. Pin ONE LLVM major for the whole set: if
# clang and libc++-dev land on different majors, libc++'s
# `#include_next <stddef.h>` resolves through the wrong include tree and fails.
ARG LLVM_VERSION=18

# nodejs/npm: Veil's `lean_lib Veil` declares `needs := #[widgetJsAll]`, which
# runs `npm clean-install && npm run build` in its widget/ directory. That is an
# infoview UI component nothing here uses, but it is a hard edge in lake's
# dependency graph — without a Node toolchain the Veil library does not build.
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git unzip xz-utils \
      nodejs npm \
      clang-${LLVM_VERSION} \
      libc++-${LLVM_VERSION}-dev \
      libc++abi-${LLVM_VERSION}-dev \
      libclang-common-${LLVM_VERSION}-dev \
      libclang-rt-${LLVM_VERSION}-dev \
 && ln -sf clang-${LLVM_VERSION}  /usr/bin/clang \
 && ln -sf clang++-${LLVM_VERSION} /usr/bin/clang++ \
 && rm -rf /var/lib/apt/lists/* \
 # Fail HERE, at image build, if the toolchain is mismatched — not later,
 # obscurely, inside `lake build`.
 && printf '#include <ostream>\nint main(){}\n' > /tmp/probe.cpp \
 && clang -c -std=c++17 -stdlib=libc++ -o /dev/null /tmp/probe.cpp \
 && rm /tmp/probe.cpp

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Bake the pinned toolchain in, so a container starts ready to build. Keep in
# step with lean-toolchain.
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.32.0
RUN elan toolchain install ${LEAN_TOOLCHAIN} \
 && elan default ${LEAN_TOOLCHAIN} \
 && lean --version \
 && ln -sfn "$(lean --print-prefix)" /opt/lean-toolchain

# lean-smt is built with `precompileModules`, so modules importing it are
# elaborated with its compiled `.so`s `dlopen`ed. Those carry a DT_NEEDED on the
# toolchain's own libLake_shared.so with no RPATH, and the loader is not told
# where to look — on Linux that is a hard failure ("error loading library,
# libLake_shared.so"). macOS does not hit it because Mach-O records absolute
# install names. Put the toolchain's library directories on the path once, here,
# through the /opt/lean-toolchain symlink above so that no toolchain version is
# spelled out twice and this cannot drift from ${LEAN_TOOLCHAIN}.
#
# This is still only correct for the toolchain baked into the image. A checkout
# whose `lean-toolchain` names a *different* version makes elan fetch that one,
# and `lake` then loads a mismatched `libleanshared.so` and dies with
# `undefined symbol: runtime_initialize_Init_System_IO`. `scripts/revalidate.sh`
# therefore re-derives the path from `lean --print-prefix` at run time, which is
# authoritative; keep that in place.
ENV LD_LIBRARY_PATH="/opt/lean-toolchain/lib/lean:/opt/lean-toolchain/lib"

# The workspace path is BAKED IN and load-bearing: lake records absolute paths
# in its trace files, so a build tree is only reusable at the path it was built
# at. Anything mounting sources over this image must use the same path — that is
# why .devcontainer/devcontainer.json pins `workspaceFolder` to match.
ENV CADENCE_WORKSPACE=/workspaces/cadence
WORKDIR /workspaces/cadence
CMD ["/bin/bash"]

# --------------------------------------------------------------------- deps --
# Everything except this project: Mathlib, Loom, lean-smt, auto, cvc5, Veil,
# built and ready. ~13 GB, and the whole point of publishing an image.
FROM toolchain AS deps

# Only the dependency-defining files, so editing the project's sources never
# invalidates this layer.
COPY lakefile.lean lake-manifest.json lean-toolchain ./

# A stub root module that pulls in Veil (and hence the entire dependency tree),
# so the dependency build is driven by this project's own pinned revisions. The
# stub is removed again; the real sources arrive in a later stage or by mount.
# The `.submodules` glob requires the directory to exist even when empty.
RUN mkdir -p Cadence \
 && printf 'import Veil\n' > Cadence.lean \
 && lake resolve-deps \
 && lake exe cache get \
 && lake build Cadence \
 && rm -f Cadence.lean \
 && rmdir Cadence \
 && rm -rf .lake/build/lib/lean/Cadence.* /root/.cache/mathlib \
 # Reclaimed in THIS layer, because a delete in a later one frees nothing.
 # The widget's node_modules and npm's cache are build inputs only — lake still
 # considers everything up to date without them (verified by probe). If the
 # widget is ever invalidated, `npm clean-install` re-runs and needs network.
 && rm -rf .lake/packages/veil/widget/node_modules /root/.npm

# NOTE on how `.lake` survives a source mount. A bind mount of the project
# sources over the workspace would shadow `.lake`, so both entry points mount a
# named *volume* at `<workspace>/.lake` instead. Docker and podman initialise a
# fresh named volume from whatever the image has at that path, so the dependency
# tree below lands in the volume automatically on first use — no duplicate copy
# in the image, and nothing to seed by hand.

# ---------------------------------------------------------------------- dev --
# The devcontainer base and the target scripts/container.sh uses.
FROM deps AS dev
ARG DEBIAN_FRONTEND=noninteractive
# `vim`, not `vim-tiny` (which is `-eval` and has no syntax highlighting) and not
# `vim-nox` (18 MB over 21 packages for perl/lua/ruby/tcl bindings): the plain
# package is 11 MB over 6 and already `+eval +python3 +syntax`. It also provides
# `vi`. `--no-install-recommends` throughout.
RUN apt-get update && apt-get install -y --no-install-recommends \
      ripgrep fd-find less vim jq python3 \
 && rm -rf /var/lib/apt/lists/*

# -------------------------------------------------------------------- build --
# Runs the staged verification against the sources and KEEPS the proof cache it
# produces — the seed's entries plus every VC solved fresh this build. Never
# published: `verified` below takes this workspace minus the cache, and
# `verified-cache` re-adds exactly this stage's cache. That is what keeps the
# published cache *current*. (Shipping the seed instead is the bug this layout
# replaces: `verified-cache` used to COPY `.veilcache-seed`, so a cold build —
# no local cache, as on any fresh clone or the CI bootstrap — published an
# EMPTY cache image, and the CI seed chain silently never warmed up.)
FROM ${DEPS_IMAGE} AS build
# Fail HERE, loudly, if the base image was built for a different toolchain than
# this checkout asks for — otherwise elan silently fetches the requested one and
# `lake` loads the *image's* libleanshared.so through LD_LIBRARY_PATH, dying as
# `undefined symbol: runtime_initialize_Init_System_IO` several minutes later.
# A toolchain bump therefore needs the `deps` image rebuilt: dispatch
# publish-images with `rebuild_deps: true` (the automatic trigger only inspects
# the last commit, so a bump landing earlier in a branch does not fire it).
COPY lean-toolchain /tmp/want-toolchain
RUN want="$(sed -n 's|.*lean4:v\([0-9][0-9.]*\).*|\1|p' /tmp/want-toolchain)" \
 && have="$(lean --version | sed -n 's|.*version \([0-9][0-9.]*\).*|\1|p')" \
 && if [ -z "$want" ] || [ "$want" != "$have" ]; then \
      echo "TOOLCHAIN MISMATCH: image has Lean '$have', checkout wants '$want'." >&2 ; \
      echo "Rebuild the deps image: publish-images with rebuild_deps: true." >&2 ; \
      exit 1 ; \
    fi \
 && rm /tmp/want-toolchain

# An explicit list, not `COPY . .`: the context also holds .veilcache-seed, and
# copying that here would defeat mounting it below. (.containerignore keeps a
# developer's local .lake out too.)
COPY Cadence.lean lakefile.lean lake-manifest.json lean-toolchain README.md CLAUDE.md ./
COPY Cadence ./Cadence
COPY scripts ./scripts
COPY traces ./traces
COPY docs ./docs

# The proof-cache seed arrives as a build-time bind mount, so it never enters a
# layer: without it this stage re-solves ~4 000 verification conditions with
# cvc5 (~90 min on a workstation); with it they are replayed and kernel-checked
# (~11 min). Requires BuildKit-style mounts — podman >= 4 and docker with
# buildx have them. `scripts/container.sh build verified` fills .veilcache-seed
# for you.
#
# BATCH is scripts/revalidate.sh's proof-file batch width (see its header),
# reaching it through the environment ARG provides. The default suits a large
# workstation; a builder with few cores must lower it — near-limit VCs time out
# spuriously under discharger contention, and a cold run at width 6 peaks
# ~30 GB. CI passes BATCH=1 for its 4-vCPU runners. The trailing mkdir keeps
# the cache directory present even if caching were disabled, so the COPYs
# below fail with the guard's clear message instead of a missing-path error.
ARG BATCH=6
RUN --mount=type=bind,source=.veilcache-seed,target=/seed \
    if [ -n "$(ls -A /seed 2>/dev/null | grep -v '^\.keep$')" ]; then \
      mkdir -p .lake/build/veilcache \
      && cp -a /seed/. .lake/build/veilcache/ \
      && rm -f .lake/build/veilcache/.keep \
      && echo "seeded proof cache: $(ls .lake/build/veilcache | wc -l) entries" ; \
    else echo "no proof-cache seed — cvc5 will solve every VC from scratch" ; fi \
 && bash scripts/revalidate.sh /tmp \
 && mkdir -p .lake/build/veilcache \
 && rm -rf /root/.cache/mathlib

# ----------------------------------------------------------------- verified --
# The project built: this repository's own oleans on top of the dependency tree.
# This is the image for readers and auditors — `scripts/container.sh check`
# kernel-re-checks every proof from here in ~4 minutes, with no solver and no
# elaboration. It deliberately does NOT contain Veil's proof cache: nothing in
# tier 1 or tier 2a needs it (verified by probe), and it is 4.1 GB.
#
# The sources are COPY'd with the same instructions as in `build` (same base,
# same content — the layers deduplicate); the build outputs arrive from that
# stage, with the cache stripped in the SAME layer that copies them, because a
# delete in a later layer reclaims nothing.
FROM ${DEPS_IMAGE} AS verified
COPY Cadence.lean lakefile.lean lake-manifest.json lean-toolchain README.md CLAUDE.md ./
COPY Cadence ./Cadence
COPY scripts ./scripts
COPY traces ./traces
COPY docs ./docs
# tar with an exclude rather than cp-then-rm: the cache is ~4 GB, and copying
# it into the layer just to delete it would cost that much transient disk on
# an already-tight CI runner.
RUN --mount=type=bind,from=build,source=/workspaces/cadence/.lake/build,target=/built \
    mkdir -p .lake/build \
 && tar -C /built --exclude='./veilcache' -cf - . | tar -C .lake/build -xf -

# ----------------------------------------------------------- verified-cache --
# `verified` plus the proof cache the `build` stage produced (+4.1 GB) — the
# seed plus everything solved fresh, so consumers of this image (and the CI
# runs that seed from it) always get the cache matching these sources. Only
# needed to re-elaborate the project without re-solving — tier 2b and tier 3
# of docs/Container.md. Pull `verified` instead if you just want to check the
# proofs.
FROM verified AS verified-cache
COPY --from=build /workspaces/cadence/.lake/build/veilcache/ /workspaces/cadence/.lake/build/veilcache/
# An empty cache means a broken seed chain downstream: refuse to publish one.
RUN n=$(ls /workspaces/cadence/.lake/build/veilcache | grep -vc '^\.keep$') ; \
    echo "proof cache: $n entries" ; \
    [ "$n" -gt 0 ]
