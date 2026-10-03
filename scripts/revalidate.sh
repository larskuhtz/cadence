#!/usr/bin/env bash
# Re-validation of the whole Cadence suite, with a bounded number of
# concurrent `lean` processes.
#
#   scripts/revalidate.sh [logdir]      # one `lake build`, JOBS-wide
#   JOBS=6 scripts/revalidate.sh        # ... with an explicit cap (CI: 2)
#   BATCH=1 scripts/revalidate.sh       # the staged build (image build)
#
# Writes an RSS sample log (total resident memory of all `lean` processes,
# every 15 s) to $logdir. Both modes build the same targets and do the same
# verification work.
#
# JOBS (the default): a single `lake build` under LEAN_NUM_THREADS=$JOBS.
# Lake runs each module build on a thread of that pool, so the variable caps
# how many `lean` processes run at once (unset, it is the core count). Lake
# then schedules by dependency, with no barriers: `Mvba/NoLock.lean` (a ~1 min
# single-core model check) runs alongside the Chorus model instead of last,
# the three family models build side by side, and a slow proof file holds up
# no batch. The default JOBS comes from the memory actually available (the
# cgroup limit in a container, else physical RAM) at ~4 GB per slot, capped
# at the core count. Measured 2026-09-29, 14 cores / 36 GB, every project
# olean deleted:
#
#   mode             cache   wall     peak RSS   mean cores busy
#   BATCH=6 staged   warm    13m16s   14.9 GB    4.8
#   JOBS=8           warm     7m10s   19.2 GB    7.6
#   JOBS=12          warm     7m14s   29.3 GB    8.1
#   JOBS=8           cold    10m49s   25.5 GB    9.0
#
# JOBS=12 buys nothing over 8: the build is then bound by its critical path
# (the Chorus model, then its proof files), not by slots. In the cold run the
# slowest cell took 88 s of its 180 s budget, with no retries. Per-process
# peaks, cold: most proof files 2–4 GB, Chorus/Proofs/Vote.lean 9.2 GB (it
# opts out of foldBoolAtoms), the Chorus model 11.7 GB.
#
# CI's verify job uses JOBS=2 on its 4-core / 16 GB arm64 runner (13 GB
# container limit). Measured 2026-10-03, cold, all runs against one image
# digest: an olean-changing edit to Chorus.lean re-solved the Chorus model
# and its 49 proof files with no proof cache (and the Conductor and glue
# models, which that image lagged):
#
#   mode      verify step         slowest cell (of 180 s)   ⏱ / OOM
#   BATCH=1   66m38s, 63m09s      56.2 s, 54.6 s            none
#   BATCH=2   68m51s              69.2 s                    none
#   JOBS=2    61m24s, 59m36s      48.5 s, 48.9 s            none
#
# BATCH=2 is slower than BATCH=1 and its slowest cell rises by a quarter:
# each process of a staged build sizes its own thread pool to all four
# cores. LEAN_NUM_THREADS=2 caps both the slots and each process's pool, so
# per-file times rise (Vote 211 s → 415 s) but the slowest cell does not,
# and with no barriers the build is still faster overall. A JOBS=2 run that
# rebuilt the Chorus model next to the whole Mvba family and
# `Mvba/NoLock.lean` stayed inside the 13 GB limit.
#
# BATCH (setting it selects this mode): the staged build — the model files
# one at a time, then the proof families in batches of $BATCH (capped at 5 for
# the two smaller families), each stage a separate `lake build` that must
# finish before the next starts. Exits non-zero on the first failed stage.
# The image build still uses BATCH=1 (its width is a Containerfile ARG, and
# an edit to the Containerfile rebuilds the deps image); CI's verify job did
# until 2026-10-03 (table above). A wide batch on few cores makes concurrent
# dischargers contend for wall-clock, and a near-limit VC that passes
# comfortably alone then times out (the 2026-08 external audit measured 21 s
# alone vs > 60 s in a batch of 6 on 8 cores, at the then 60 s budget).
#
# When reading the output, count all four verification markers — ✅ proven,
# ❌ counterexample, 💥 solver crash, ⏱ timeout — plus ♻ (proof-cache
# replay, kernel-checked). A healthy run has only ✅ and ♻. In the staged
# mode every `lake build` re-prints the stored log of each already-built
# module it passes through, so marker counts there are inflated several-fold;
# count markers from a JOBS-mode log.
set -u
cd "$(dirname "$0")/.." || exit 1

# Point the dynamic loader at the toolchain that is actually in use, not at
# whichever one an image happened to be built with. `lean-smt` ships
# precompiled plugins that record a DT_NEEDED on the toolchain's own
# libLake_shared.so without an RPATH, so on Linux the loader has to be told
# where to look. Deriving the path here rather than baking it into an image
# keeps it correct when the two disagree: a container built for one toolchain
# and a checkout whose lean-toolchain names another makes `lake` load a
# mismatched libleanshared.so and die with
# `undefined symbol: runtime_initialize_Init_System_IO`.
TC="$(lean --print-prefix 2>/dev/null || true)"
if [ -n "$TC" ]; then
  export LD_LIBRARY_PATH="$TC/lib/lean:$TC/lib:${LD_LIBRARY_PATH:-}"
fi

LOGDIR=${1:-/tmp}
RSSLOG="$LOGDIR/cadence_revalidate_rss.log"
: > "$RSSLOG"

( while true; do
    total=$(ps -Ao rss=,comm= | awk '$2 ~ /\/lean$/ {s+=$1} END {printf "%.1f", s/1048576}')
    echo "$(date +%T) ${total:-0} GB" >> "$RSSLOG"
    sleep 15
  done ) &
SAMPLER=$!
trap 'kill $SAMPLER 2>/dev/null' EXIT

if [ -z "${BATCH:-}" ]; then
  if [ -z "${JOBS:-}" ]; then
    cores=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)
    mem=$(cat /sys/fs/cgroup/memory.max 2>/dev/null || true)
    case "$mem" in (''|*[!0-9]*)
      mem=$(sysctl -n hw.memsize 2>/dev/null \
            || awk '/^MemTotal:/ {print $2 * 1024}' /proc/meminfo) ;;
    esac
    JOBS=$(( mem / 4294967296 - 1 ))
    [ "$JOBS" -gt "$cores" ] && JOBS=$cores
    [ "$JOBS" -ge 1 ] || JOBS=1
  fi
  case "$JOBS" in (*[!0-9]*|'') echo "JOBS must be a positive integer" >&2; exit 2 ;; esac
  [ "$JOBS" -ge 1 ] || { echo "JOBS must be ≥ 1" >&2; exit 2; }
  echo "=== lake build, LEAN_NUM_THREADS=$JOBS — start $(date +%T)"
  t0=$SECONDS
  if LEAN_NUM_THREADS=$JOBS lake build; then
    # The staged mode's marker, which CI asserts; here there is one stage.
    echo "=== ALL STAGES GREEN (one lake build, $(( SECONDS - t0 )) s) $(date +%T)"
    exit 0
  fi
  echo "=== BUILD FAILED ($(( SECONDS - t0 )) s)"
  exit 1
fi

case "$BATCH" in (*[!0-9]*|'') echo "BATCH must be a positive integer" >&2; exit 2 ;; esac
[ "$BATCH" -ge 1 ] || { echo "BATCH must be ≥ 1" >&2; exit 2; }
FB_BATCH=$(( BATCH < 5 ? BATCH : 5 ))

stage() {
  echo ""
  echo "=== STAGE: $* — start $(date +%T)"
  local t0=$SECONDS
  if lake build "$@"; then
    echo "=== STAGE OK ($(( SECONDS - t0 )) s): $*"
  else
    echo "=== STAGE FAILED ($(( SECONDS - t0 )) s): $*"
    exit 1
  fi
}

# Composition-layer models: small, and they run their invariant sweeps in-file.
stage Cadence.Cadence Cadence.Conductor

# Model files of the three proof families: VC registry only, no sweep.
stage Cadence.Chorus
stage Cadence.FallbackReceipt
stage Cadence.Mvba

# Per-action proof files, batched (the memory rule above).
PROOFS=()
for f in Cadence/Chorus/Proofs/*.lean; do
  PROOFS+=("Cadence.Chorus.Proofs.$(basename "$f" .lean)")
done
echo "=== ${#PROOFS[@]} Chorus proof files, batches of $BATCH"
i=0
while [ $i -lt ${#PROOFS[@]} ]; do
  stage "${PROOFS[@]:$i:$BATCH}"
  i=$(( i + BATCH ))
done

FPROOFS=()
for f in Cadence/FallbackReceipt/Proofs/*.lean; do
  FPROOFS+=("Cadence.FallbackReceipt.Proofs.$(basename "$f" .lean)")
done
echo "=== ${#FPROOFS[@]} FallbackReceipt proof files, batches of $FB_BATCH"
i=0
while [ $i -lt ${#FPROOFS[@]} ]; do
  stage "${FPROOFS[@]:$i:$FB_BATCH}"
  i=$(( i + FB_BATCH ))
done

MPROOFS=()
for f in Cadence/Mvba/Proofs/*.lean; do
  MPROOFS+=("Cadence.Mvba.Proofs.$(basename "$f" .lean)")
done
echo "=== ${#MPROOFS[@]} Mvba proof files, batches of $FB_BATCH"
i=0
while [ $i -lt ${#MPROOFS[@]} ]; do
  stage "${MPROOFS[@]:$i:$FB_BATCH}"
  i=$(( i + FB_BATCH ))
done

# Composition certificates (#gen_composition + the #veil_status audit pins).
stage Cadence.Chorus.Certify Cadence.FallbackReceipt.Certify Cadence.Mvba.Certify

# End theorems and the monitor.
stage Cadence.Chorus.Compose Cadence.Chorus.Pigeonhole \
      Cadence.Chorus.Counting Cadence.Chorus.Progress \
      Cadence.Chorus.Liveness Cadence.Chorus.Termination \
      Cadence.Mvba.BoundedTermination \
      Cadence.Composition \
      Cadence.FallbackReceipt.Totality
# The composed system: the glue's end theorem at the Conductor and Chorus
# instances (imports both composition files).
stage Cadence.System

# The root audit module (re-derives every end theorem's axiom footprint) and
# everything else the default target covers, including the monitor.
stage Cadence

echo ""
echo "=== ALL STAGES GREEN $(date +%T)"
