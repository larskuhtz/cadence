#!/usr/bin/env bash
# Staged re-validation of the whole Cadence suite.
#
# `lake build` alone verifies everything, but it schedules the 39 + 10
# per-action proof files all at once, and a *cold* proof file peaks around
# 5 GB of resident memory (lake has no job cap). This script builds the same
# targets in dependency order with the proof families batched, which bounds a
# cold run's footprint — see BATCH below for the measured figures. On a machine
# with plenty of RAM, plain `lake build` is equivalent and faster.
#
#   scripts/revalidate.sh [logdir]
#
# Writes an RSS sample log (total resident memory of all `lean` processes,
# every 15 s) to $logdir. Exits non-zero on the first failed stage.
#
# BATCH controls how many proof files build concurrently per stage (default
# 6 for the Chorus family, capped at 5 for FallbackReceipt). The default is
# tuned for a large workstation with a WARM proof cache.
#
# Lower it for a cold run, or on a core-poor machine. Concurrent dischargers
# contend for wall-clock, and a near-limit VC that passes comfortably alone
# then times out — measured by the 2026-08 external audit at 21 s alone vs
# > 60 s in a batch of 6 on 8 cores, and again on a cold 4.32 run where
# `fb_sign_neg × inclusion_no_honest_fb_neg` (10.5 s alone, 60 s budget)
# missed its budget in a batch of 6. A cold run is also memory-bound: 32.0 GB
# peak at BATCH=6 against 20.7 GB at BATCH=3, on 14 cores / 36 GB.
#
# So: BATCH=3 for a cold run on a 36 GB machine, BATCH=1 on ≤ 8 cores.
#
# When reading the output, count all four verification markers — ✅ proven,
# ❌ counterexample, 💥 solver crash, ⏱ timeout — plus ♻ (proof-cache
# replay, kernel-checked). A healthy run has only ✅ and ♻.
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
BATCH="${BATCH:-6}"
case "$BATCH" in (*[!0-9]*|'') echo "BATCH must be a positive integer" >&2; exit 2 ;; esac
[ "$BATCH" -ge 1 ] || { echo "BATCH must be ≥ 1" >&2; exit 2; }
FB_BATCH=$(( BATCH < 5 ? BATCH : 5 ))
RSSLOG="$LOGDIR/cadence_revalidate_rss.log"
: > "$RSSLOG"

( while true; do
    total=$(ps -Ao rss=,comm= | awk '$2 ~ /\/lean$/ {s+=$1} END {printf "%.1f", s/1048576}')
    echo "$(date +%T) ${total:-0} GB" >> "$RSSLOG"
    sleep 15
  done ) &
SAMPLER=$!
trap 'kill $SAMPLER 2>/dev/null' EXIT

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

# Model files of the two proof families: VC registry only, no sweep.
stage Cadence.Chorus
stage Cadence.FallbackReceipt

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

# Composition certificates (#gen_composition + the #veil_status audit pins).
stage Cadence.Chorus.Certify Cadence.FallbackReceipt.Certify

# End theorems, the pre-fix refutation, and the monitor.
stage Cadence.Chorus.Compose Cadence.Chorus.Pigeonhole \
      Cadence.Chorus.Counting Cadence.Chorus.Progress \
      Cadence.Composition \
      Cadence.FallbackReceipt.Totality \
      Cadence.FallbackReceipt.PreFix
# The composed system: the glue's end theorem at the Conductor and Chorus
# instances (imports both composition files).
stage Cadence.System

# The root audit module (re-derives every end theorem's axiom footprint) and
# everything else the default target covers, including the monitor.
stage Cadence

echo ""
echo "=== ALL STAGES GREEN $(date +%T)"
