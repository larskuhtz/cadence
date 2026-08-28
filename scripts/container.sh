#!/usr/bin/env bash
# Verify and develop Cadence inside a Linux container.
#
# The images are published to GHCR for linux/arm64 and linux/amd64, built and
# verified by CI. Commands pull the image they need on first use — nothing has
# to be built:
#
#   scripts/container.sh verify        staged verification against your sources
#                                     (tier 2, ~9 min; IMAGE=cadence-dev for a
#                                     cold build that re-solves everything)
#   scripts/container.sh check         kernel-re-check every proof (~4 min, no solver)
#   scripts/container.sh monitor       model-conformance monitor suites over the
#                                     trace fixtures (docs/Monitor.md; needs a
#                                     `verify` first after any source edit)
#   scripts/container.sh shell         interactive shell in the workspace
#   scripts/container.sh pull [image ...]
#                                      fetch or refresh published images
#                                      (default: verified)
#   scripts/container.sh build [toolchain|deps|dev|verified|verified-cache]
#                                      build an image locally instead of pulling
#                                      — needed only when the dependency tree
#                                      changes (docs/Images.md)
#
# Runtime selection, in order: $RUNTIME, then whichever of container / podman /
# docker is found first.
#   RUNTIME=podman scripts/container.sh verify
#
# Resources:  CPUS (default 12)   MEMORY (default 20G)
#             BATCH (proof-file batch width for verify's revalidate.sh; use
#             BATCH=1 on few cores — see scripts/revalidate.sh)
# Images:     pulled from ${IMAGE_REPO}-<name>:latest (default
#             ghcr.io/larskuhtz/cadence); PULL=never disables pulling.
# Persistence: a named volume ($VOLUME, default cadence-lake-<image>) holds
# .lake — oleans, the dependency tree and the proof cache. Sources are
# bind-mounted read-only and copied in, so the container never writes to your
# checkout. After pulling a newer image, remove the volume to re-seed it.
#
# Why a container: see the header of ../Containerfile and docs/Container.md.
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE=/workspaces/cadence          # must match the path baked into the image
IMAGE="${IMAGE:-}"                     # per-command default, see the dispatch below
VOLUME="${VOLUME:-}"                   # defaults to cadence-lake-<image>, see below
CPUS="${CPUS:-12}"
MEMORY="${MEMORY:-20G}"
VOLUME_SIZE="${VOLUME_SIZE:-80G}"
# Where published images come from. The :latest tags are multi-arch manifest
# lists (linux/arm64 + linux/amd64); a pull resolves this machine's platform.
IMAGE_REPO="${IMAGE_REPO:-ghcr.io/larskuhtz/cadence}"
PULL="${PULL:-auto}"                   # auto | never

die() { echo "error: $*" >&2; exit 2; }

# ---------------------------------------------------------------- runtime ----
if [ -n "${RUNTIME:-}" ]; then
  command -v "$RUNTIME" >/dev/null || die "RUNTIME=$RUNTIME not found on PATH"
else
  for r in container podman docker; do
    command -v "$r" >/dev/null && { RUNTIME=$r; break; }
  done
  [ -n "${RUNTIME:-}" ] || die "no container runtime found (container, podman or docker)"
fi

# Apple's container spells a read-only bind mount `readonly`; podman and docker
# spell it `ro`. Everything else in the invocations below is common.
case "$RUNTIME" in
  container) RO=readonly ;;
  *)         RO=ro ;;
esac

# Apple's container needs its services running; the others need nothing.
#
# It also builds images inside a SEPARATE builder VM whose resources are
# independent of `container run`, and which defaults to 2 CPUs / 2 GB. That is
# far too small for this image: the dependency build stalls part-way through
# Veil with no error. Size it up before building.
# Defaults tuned by failure: 12 CPUs with 20 GB OOMs in `Auto.Embedding.LamPrep`
# during the dependency build. Lake has no job-limit flag, so the only lever on
# peak memory is the VM's CPU count — fewer CPUs, fewer concurrent Lean
# processes. 8 CPUs / 24 GB builds it; raise both if you have the RAM.
BUILDER_CPUS="${BUILDER_CPUS:-8}"
BUILDER_MEMORY="${BUILDER_MEMORY:-24G}"

ensure_runtime() {
  if [ "$RUNTIME" = container ]; then
    container system status >/dev/null 2>&1 || container system start >/dev/null \
      || die "could not start Apple container services"
  fi
}

ensure_builder() {
  [ "$RUNTIME" = container ] || return 0
  # Parse e.g. 24G / 24576M / 24Gi into MiB without GNU coreutils (`numfmt` is
  # not on a stock macOS, and silently skipping the resize is worse than noisy).
  local want_mb
  want_mb=$(printf '%s' "$BUILDER_MEMORY" | awk '
    { n = $0; sub(/[KkMmGgTt][Ii]?[Bb]?$/, "", n)
      u = toupper(substr($0, length(n) + 1, 1))
      if (u == "G") n *= 1024; else if (u == "K") n /= 1024
      else if (u == "T") n *= 1048576
      else if (u != "M" && u != "") n /= 1048576   # anything else: bytes
      # a bare number is read as MiB, which is how these get written by hand
      printf "%d", n }')
  [ -n "$want_mb" ] || die "could not parse BUILDER_MEMORY=$BUILDER_MEMORY"
  local have_mb; have_mb=$(container builder status 2>/dev/null | awk 'NR==2 {print $(NF-1)}')
  if [ -z "${have_mb:-}" ] || [ "${have_mb:-0}" -lt "$want_mb" ]; then
    echo "==> sizing the image builder to ${BUILDER_CPUS} CPUs / ${BUILDER_MEMORY}" \
         "(was ${have_mb:-none} MB; the 2 GB default cannot build this image)"
    container builder stop >/dev/null 2>&1
    container builder start --cpus "$BUILDER_CPUS" --memory "$BUILDER_MEMORY" >/dev/null \
      || die "could not start the image builder"
  fi
}

ensure_volume() {
  if [ "$RUNTIME" = container ]; then
    container volume inspect "$VOLUME" >/dev/null 2>&1 \
      || container volume create -s "$VOLUME_SIZE" "$VOLUME" >/dev/null
  else
    "$RUNTIME" volume inspect "$VOLUME" >/dev/null 2>&1 \
      || "$RUNTIME" volume create "$VOLUME" >/dev/null
  fi
}

# Pull the published image behind a local tag (cadence-<name>) and retag it.
# `image pull` / `image tag` are the spellings all three runtimes share.
try_pull() {
  [ "$PULL" = never ] && return 1
  local ref="${IMAGE_REPO}-${1#cadence-}:latest"
  echo "==> pulling $ref (a first pull is ~4 GiB; refreshes fetch only changed layers)"
  "$RUNTIME" image pull "$ref" || return 1
  "$RUNTIME" image tag "$ref" "$1"
}

ensure_image() {
  "$RUNTIME" image inspect "$IMAGE" >/dev/null 2>&1 && return 0
  # Prefer the published image: nobody should have to build the dependency
  # tree to check a proof.
  try_pull "$IMAGE" && return 0
  case "$IMAGE" in
    cadence-verified)
      die "image $IMAGE is not present and could not be pulled from
    ${IMAGE_REPO}-verified:latest
  (offline, PULL=never, or a registry problem — try '$RUNTIME login ghcr.io').
  To build it locally instead (docs/Images.md):
    RUNTIME=$RUNTIME scripts/container.sh build verified
  That builds this project inside the image: ~15 min with a proof-cache seed,
  ~90 min without. Point VEILCACHE=<dir> at an existing cache to seed it." ;;
    *)
      echo "==> could not pull; building $IMAGE locally (slow the first time)"
      do_build dev ;;
  esac
}

do_build() {
  # Apple's container cannot build the large layers on a machine this size; the
  # builder VM OOMs holding the layer plus the elaboration. Warn, don't block —
  # the smaller stages do build, and someone with more RAM may get further.
  if [ "$RUNTIME" = container ] && [ "${1:-dev}" != toolchain ]; then
    echo "warning: building '${1:-dev}' with Apple container is not expected to" >&2
    echo "         succeed (its builder VM OOMs on the ~13 GB deps layer)." >&2
    echo "         Use RUNTIME=podman or RUNTIME=docker to build; either" >&2
    echo "         runtime's images run under Apple container afterwards." >&2
  fi
  ensure_builder
  local target="${1:-dev}"
  # Tag by target. $IMAGE is a per-command *run* default (see the dispatch at
  # the bottom) and is empty here unless the caller set it explicitly, so it
  # must not be used unguarded — doing so produced an untagged image.
  local tag="${IMAGE:-cadence-${target}}"
  local extra=()
  # An optional proof-cache seed makes the `verified` image ~15 min instead of
  # ~90: without it every verification condition is re-solved from scratch.
  # The `build` stage reads .veilcache-seed from the build context as a
  # build-time bind mount (it never enters a layer); `verified-cache` ships
  # the cache that stage *produced* — the seed plus everything solved fresh —
  # so the published cache stays current rather than frozen at the seed.
  # Seeding turns ~90 minutes of cvc5 into ~11 minutes of kernel-checked
  # replay. A tracked .keep keeps the unseeded path working, so this is an
  # optimisation, never a requirement.
  local seed="${VEILCACHE:-$REPO/.lake/build/veilcache}"
  case "$target" in verified|verified-cache)
    if [ -d "$seed" ] && [ -n "$(ls -A "$seed" 2>/dev/null)" ]; then
      echo "==> seeding the proof cache from $seed ($(ls "$seed" | wc -l | tr -d ' ') entries)"
      find "$REPO/.veilcache-seed" -mindepth 1 ! -name .keep -delete 2>/dev/null
      cp -a "$seed"/. "$REPO/.veilcache-seed"/
      # Leave the context clean afterwards, whatever happens.
      trap 'find "$REPO/.veilcache-seed" -mindepth 1 ! -name .keep -delete 2>/dev/null' EXIT
    else
      echo "==> no proof cache at $seed — the build will solve every VC (~90 min)"
    fi ;;
  esac
  # `--file` spelled out because only podman looks for a `Containerfile` on its
  # own — docker (and Apple's container) look for `Dockerfile` and fail.
  ( cd "$REPO" && "$RUNTIME" build --file Containerfile \
      --target "$target" --tag "$tag" "${extra[@]}" . )
}

# Run a script inside the workspace.
#
# The payload is written to a file and bind-mounted, NOT interpolated into the
# runtime's command line: embedding it in a double-quoted string would have the
# HOST shell expand every $VAR and $(...) in it before the container ever saw it.
# Sources are copied from the read-only mount so the checkout is never written
# to; `.lake` is the persistent volume, which the runtime initialises from the
# image the first time it is used.
run_in_container() {
  # One volume PER IMAGE. A named volume is initialised from whichever image
  # first mounts it and is sticky afterwards, so sharing one between `dev`
  # (dependencies only) and `verified` (dependencies + this project's oleans)
  # produces confusing results — `check` would find no proofs to check.
  VOLUME="${VOLUME:-cadence-lake-${IMAGE#cadence-}}"
  ensure_runtime; ensure_image; ensure_volume
  local payload_dir payload
  payload_dir="$(mktemp -d)"
  payload="$payload_dir/run.sh"
  trap 'rm -rf "$payload_dir"' RETURN
  {
    printf '%s\n' '#!/usr/bin/env bash'
    printf '%s\n' 'set -uo pipefail'
    printf 'WORKSPACE=%q\n' "$WORKSPACE"
    [ -n "${LEAN_NUM_THREADS:-}" ] && printf 'export LEAN_NUM_THREADS=%q\n' "$LEAN_NUM_THREADS"
    # Proof-file batch width for scripts/revalidate.sh (see its header);
    # BATCH=1 avoids spurious discharger-contention timeouts on few cores.
    [ -n "${BATCH:-}" ] && printf 'export BATCH=%q\n' "$BATCH"
    cat <<'PREAMBLE'
# Docker and podman initialise a fresh named volume from the image's content at
# the mount point, so the prebuilt dependency tree arrives by itself. If it did
# not, say so loudly rather than silently rebuilding the world for an hour.
if [ ! -d "$WORKSPACE/.lake/packages" ]; then
  echo 'warning: .lake/packages is missing — this runtime did not initialise' >&2
  echo '         the volume from the image, so everything will be rebuilt' >&2
  echo '         (~1 h). Use podman or docker, or populate the volume.' >&2
fi
cd "$WORKSPACE" || exit 2
# Sources come from the read-only mount; .lake is the volume and must survive.
find /src -maxdepth 1 -mindepth 1 ! -name .lake ! -name .git \
     ! -name .veilcache-seed -exec cp -a {} "$WORKSPACE/" \;
PREAMBLE
    cat            # the caller's payload, verbatim, from stdin
  } > "$payload"
  chmod +x "$payload"

  "$RUNTIME" run --rm -i \
    --cpus "$CPUS" --memory "$MEMORY" \
    --mount "type=bind,source=$REPO,target=/src,$RO" \
    --mount "type=bind,source=$payload_dir,target=/payload,$RO" \
    -v "$VOLUME:$WORKSPACE/.lake" \
    "$IMAGE" bash /payload/run.sh
}

case "${1:-verify}" in
  build)  ensure_runtime; do_build "${2:-dev}" ;;
  pull)
    ensure_runtime
    shift
    [ "$#" -gt 0 ] || set -- verified
    for t in "$@"; do
      case "$t" in
        toolchain|deps|dev|verified|verified-cache) ;;
        *) die "unknown image: $t (toolchain|deps|dev|verified|verified-cache)" ;;
      esac
      PULL=auto try_pull "cadence-$t" \
        || die "could not pull ${IMAGE_REPO}-$t:latest"
    done ;;
  verify)
    # Runs against the `verified` image, so the dependency tree AND the proof
    # cache are already there: this is a re-validation of the project against
    # your sources (tier 2), not a build of the world. For a genuinely cold
    # project build that re-solves every verification condition with cvc5, use
    #   IMAGE=cadence-dev scripts/container.sh verify      (~90 min)
    IMAGE="${IMAGE:-cadence-verified}"
    run_in_container <<'PAYLOAD' ;;
bash scripts/revalidate.sh /tmp
PAYLOAD
  monitor)
    # Run the model-conformance monitor suites (docs/Monitor.md): every trace
    # fixture through both the hand-written and the generated monitor (they
    # must agree with the expectation and each other), then the divergence
    # harness (every TraceMutate mutation must be rejected). The monitor runs
    # on the interpreter over the project's OWN oleans, so this needs the
    # `verified` image — and, after an edit, a `verify` run first so the
    # oleans in the volume match the sources.
    IMAGE="${IMAGE:-cadence-verified}"
    run_in_container <<'PAYLOAD' ;;
fail=0
bash scripts/test-chorus-monitor.sh        || fail=1
bash scripts/test-monitor-divergence.sh    || fail=1
bash scripts/test-single-node-monitor.sh   || fail=1
if [ "$fail" -eq 0 ]; then echo "=== MONITOR SUITES GREEN"; else echo "=== MONITOR SUITES FAILED" >&2; fi
exit "$fail"
PAYLOAD
  check)
    # Kernel-re-check every stored proof: no solver, no tactic execution, no
    # elaboration. This needs the project's OWN oleans, so it runs against the
    # `verified` image. See docs/Container.md §3-§4 for what it establishes.
    IMAGE="${IMAGE:-cadence-verified}"
    run_in_container <<'PAYLOAD' ;;
MODS=$( { echo Cadence; find Cadence -name '*.lean' | sed 's|\.lean$||; s|/|.|g'; } \
        | grep -v '^Cadence\.Monitor' | sort -u )
# leanchecker replays STORED proofs, so the module list is the intersection of
# the checked-out sources with the oleans actually present in the volume. A
# source module with no stored olean (added or renamed since the volume's
# oleans were built) has nothing to re-check: skip it LOUDLY rather than fail.
# Locally, a `verify` run first brings the volume up to date; in CI the check
# job runs against the published image while the verify job elaborates — and
# thereby kernel-checks — exactly the modules skipped here (verify.yml has the
# composition argument).
PRESENT="" MISSING=""
for m in $MODS; do
  if [ -f ".lake/build/lib/lean/${m//.//}.olean" ]; then
    PRESENT="$PRESENT $m"
  else
    MISSING="$MISSING $m"
  fi
done
if [ -n "$MISSING" ]; then
  echo "==> skipping (source module with no stored olean — not part of what this run can re-check):"
  for m in $MISSING; do echo "      $m"; done
fi
if [ -z "$PRESENT" ]; then
  echo "FAILED — no stored oleans found; wrong volume, or run 'verify' first" >&2; exit 1
fi
# Cap Lean's worker threads. leanchecker allocates aggressively per thread and
# at the default (one per core) it needs ~19 GB and gets OOM-killed inside a
# 20 GB container 11 seconds in. Measured on all 66 modules: 4 threads =>
# 4 min 12 s and a 12.9 GB peak; 2 threads => 4.8 GB but 226 s for the Chorus
# model alone. Four is the sweet spot; lower it if you have less memory.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
echo "==> leanchecker over $(echo $PRESENT | wc -w) modules (LEAN_NUM_THREADS=$LEAN_NUM_THREADS)"
if time lake env leanchecker $PRESENT; then
  echo "OK — every stored declaration re-checked by the kernel"
  [ -n "$MISSING" ] && echo "    (skipped modules above were NOT covered by this run)"
  exit 0
else
  echo "FAILED — leanchecker rejected something" >&2; exit 1
fi
PAYLOAD
  shell)  IMAGE="${IMAGE:-cadence-dev}"
          run_in_container <<'PAYLOAD' ;;
exec bash
PAYLOAD
  -h|--help|help)
    awk 'NR>1 && /^#/ {sub(/^# ?/,""); print; next} NR>1 {exit}' "${BASH_SOURCE[0]}" ;;
  *) die "unknown command: $1 (try --help)" ;;
esac
