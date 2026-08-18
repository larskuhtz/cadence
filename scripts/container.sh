#!/usr/bin/env bash
# Build and verify Cadence inside a Linux container.
#
# This script only dispatches to a container runtime; the image itself is a
# plain multi-stage OCI build (../Containerfile) with no runtime assumptions.
#
#   scripts/container.sh build [toolchain|deps|dev|verified|verified-cache]
#   scripts/container.sh verify        staged verification against your sources
#                                     (tier 2, ~9 min; IMAGE=cadence-dev for a
#                                     cold build that re-solves everything)
#   scripts/container.sh check         kernel-re-check every proof (~4 min, no solver)
#   scripts/container.sh shell         interactive shell in the workspace
#
# Runtime selection, in order: $RUNTIME, then whichever of container / podman /
# docker is found first.
#   RUNTIME=podman scripts/container.sh verify
#
# Resources:  CPUS (default 12)   MEMORY (default 20G)
# Persistence: a named volume ($VOLUME, default cadence-lake) holds .lake —
# oleans, the dependency tree and the proof cache. Sources are bind-mounted
# read-only and copied in, so the container never writes to your checkout.
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

ensure_image() {
  "$RUNTIME" image inspect "$IMAGE" >/dev/null 2>&1 && return 0
  case "$IMAGE" in
    cadence-verified)
      die "image $IMAGE not present. Build it first:
    RUNTIME=$RUNTIME scripts/container.sh build verified
  That builds this project inside the image: ~15 min with a proof-cache seed,
  ~90 min without. Point VEILCACHE=<dir> at an existing cache to seed it." ;;
    *)
      echo "==> image $IMAGE not present; building it (slow the first time)"
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
  local tag="cadence-${target}"
  [ "$target" = dev ] && tag="$IMAGE"
  local extra=()
  # An optional proof-cache seed makes the `verified` image ~15 min instead of
  # ~90: without it every verification condition is re-solved from scratch.
  # The verified* stages read .veilcache-seed from the build context: as a
  # build-time mount (`verified`, so it never enters a layer) and as a COPY
  # (`verified-cache`, where it is the point). Seeding it turns ~90 minutes of
  # cvc5 into ~11 minutes of kernel-checked replay. A tracked .keep keeps the
  # unseeded path working, so this is an optimisation, never a requirement.
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
  ( cd "$REPO" && "$RUNTIME" build --target "$target" --tag "$tag" "${extra[@]}" . )
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
  check)
    # Kernel-re-check every stored proof: no solver, no tactic execution, no
    # elaboration. This needs the project's OWN oleans, so it runs against the
    # `verified` image. See docs/Container.md §3-§4 for what it establishes.
    IMAGE="${IMAGE:-cadence-verified}"
    run_in_container <<'PAYLOAD' ;;
MODS=$( { echo Cadence; find Cadence -name '*.lean' | sed 's|\.lean$||; s|/|.|g'; } \
        | grep -v '^Cadence\.Monitor' | sort -u | tr '\n' ' ' )
# Cap Lean's worker threads. leanchecker allocates aggressively per thread and
# at the default (one per core) it needs ~19 GB and gets OOM-killed inside a
# 20 GB container 11 seconds in. Measured on all 66 modules: 4 threads =>
# 4 min 12 s and a 12.9 GB peak; 2 threads => 4.8 GB but 226 s for the Chorus
# model alone. Four is the sweet spot; lower it if you have less memory.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
echo "==> leanchecker over $(echo "$MODS" | wc -w) modules (LEAN_NUM_THREADS=$LEAN_NUM_THREADS)"
if time lake env leanchecker $MODS; then
  echo "OK — every declaration re-checked by the kernel"
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
