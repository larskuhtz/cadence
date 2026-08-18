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
#     └─ verified
#               + this project's own oleans and proof cache: a reader can
#                 kernel-re-check every proof in ~4 minutes without running a
#                 solver, elaborating anything, or building for 15 minutes.
#                 See docs/Container.md for what that does and does not prove.
#
# BUILD THIS WITH PODMAN OR DOCKER. Apple's `container` runs these images fine,
# but its image builder is a separate memory-limited VM that cannot produce the
# ~13 GB `deps` layer on a 36 GB machine (it OOMs in `Auto.Embedding.LamPrep`
# even at 24 GB, because the builder must hold the accumulating layer as well as
# the elaboration). Podman builds it in 11 minutes. See docs/Container.md.
#
# Why containers at all: Veil precompiles its library, which forces a shared
# library link of all of Mathlib — ~7 650 objects, ~987 KB of command line.
# macOS caps exec arguments at 1 MiB, so that link fails there unless the
# checkout path is very short. Linux allows RLIMIT_STACK/4 (2 MiB), where the
# same link takes under a second.

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
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.28.0
RUN elan toolchain install ${LEAN_TOOLCHAIN} \
 && elan default ${LEAN_TOOLCHAIN} \
 && lean --version

# Veil's library is built with `precompileModules`, so downstream modules are
# elaborated with its compiled `.so`s `dlopen`ed. Those carry a DT_NEEDED on the
# toolchain's own libLake_shared.so with no RPATH, and the loader is not told
# where to look — on Linux that is a hard failure ("error loading library,
# libLake_shared.so"). macOS does not hit it because Mach-O records absolute
# install names. Put the toolchain's library directories on the path once, here.
ENV LD_LIBRARY_PATH="/root/.elan/toolchains/leanprover--lean4---v4.28.0/lib/lean:/root/.elan/toolchains/leanprover--lean4---v4.28.0/lib"

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
 && rm -rf .lake/build/lib/lean/Cadence.* /root/.cache/mathlib

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
RUN apt-get update && apt-get install -y --no-install-recommends \
      ripgrep fd-find less nano jq python3 \
 && rm -rf /var/lib/apt/lists/*

# ----------------------------------------------------------------- verified --
# The project built: its own oleans plus the Veil proof cache. Intended for
# readers and auditors — `scripts/container.sh check` kernel-re-checks every
# proof in ~4 minutes from here, with no solver and no elaboration.
#
# If a directory `.veilcache-seed/` exists in the build context it is used to
# seed the proof cache, and the build replays those proofs (each hit is
# kernel-checked before use) instead of re-solving ~4 000 verification
# conditions from scratch. Without it this stage is honest but slow: budget
# ~85 CPU-minutes of cvc5. Either way the oleans in the image are
# kernel-checked, because that is what `lake build` does.
FROM deps AS verified
COPY . /workspaces/cadence
RUN if [ -d .veilcache-seed ]; then \
      mkdir -p .lake/build/veilcache && cp -a .veilcache-seed/. .lake/build/veilcache/ ; \
      echo "seeded proof cache: $(ls .lake/build/veilcache | wc -l) entries" ; \
    else echo "no proof-cache seed in the build context — solving from scratch" ; fi \
 && rm -rf .veilcache-seed \
 && bash scripts/revalidate.sh /tmp \
 && rm -rf /root/.cache/mathlib
