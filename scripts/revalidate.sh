#!/usr/bin/env bash
# Staged re-validation of the whole Cadence suite.
#
# `lake build` alone verifies everything, but it schedules the 39 + 10
# per-action proof files all at once, and a *cold* proof file peaks around
# 5 GB of resident memory (lake has no job cap). This script builds the same
# targets in dependency order with the proof families batched, which keeps a
# cold run inside ~30 GB. On a machine with plenty of RAM, plain `lake build`
# is equivalent and faster.
#
#   scripts/revalidate.sh [logdir]
#
# Writes an RSS sample log (total resident memory of all `lean` processes,
# every 15 s) to $logdir. Exits non-zero on the first failed stage.
#
# When reading the output, count all four verification markers — ✅ proven,
# ❌ counterexample, 💥 solver crash, ⏱ timeout — plus ♻ (proof-cache
# replay, kernel-checked). A healthy run has only ✅ and ♻.
set -u
cd "$(dirname "$0")/.." || exit 1
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
echo "=== ${#PROOFS[@]} Chorus proof files, batches of 6"
i=0
while [ $i -lt ${#PROOFS[@]} ]; do
  stage "${PROOFS[@]:$i:6}"
  i=$(( i + 6 ))
done

FPROOFS=()
for f in Cadence/FallbackReceipt/Proofs/*.lean; do
  FPROOFS+=("Cadence.FallbackReceipt.Proofs.$(basename "$f" .lean)")
done
echo "=== ${#FPROOFS[@]} FallbackReceipt proof files, batches of 5"
i=0
while [ $i -lt ${#FPROOFS[@]} ]; do
  stage "${FPROOFS[@]:$i:5}"
  i=$(( i + 5 ))
done

# Composition certificates (#gen_composition + the #veil_status audit pins).
stage Cadence.Chorus.Certify Cadence.FallbackReceipt.Certify

# End theorems, the pre-fix refutation, and the monitor.
stage Cadence.Chorus.Compose Cadence.Chorus.Pigeonhole \
      Cadence.Composition \
      Cadence.FallbackReceipt.Totality \
      Cadence.FallbackReceipt.PreFix

# The root audit module (re-derives every end theorem's axiom footprint) and
# everything else the default target covers, including the monitor.
stage Cadence

echo ""
echo "=== ALL STAGES GREEN $(date +%T)"
