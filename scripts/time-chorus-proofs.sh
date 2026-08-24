#!/usr/bin/env bash
# Build the Chorus per-action proof family and report per-file wall time.
#
#   scripts/time-chorus-proofs.sh [batch-size]
#
# Builds one action's proof file per `lake build` invocation (batch size 1 by
# default) so the reported time is that file's alone: elaboration of the model
# is shared, but the discharger runs per file. Use a larger batch size to
# measure throughput instead of per-file cost. Mind that a warm proof cache
# measures kernel replay, not solving — delete `.lake/build/veilcache/` first
# to time the real thing.
set -u
cd "$(dirname "$0")/.." || exit 1
BATCH=${1:-1}
LOG=$(mktemp -t chorus-stage)
trap 'rm -f "$LOG"' EXIT

PROOFS=()
for f in Cadence/Chorus/Proofs/*.lean; do
  PROOFS+=("Cadence.Chorus.Proofs.$(basename "$f" .lean)")
done

total0=$SECONDS
i=0
while [ $i -lt ${#PROOFS[@]} ]; do
  batch=("${PROOFS[@]:$i:$BATCH}")
  t0=$SECONDS
  if lake build "${batch[@]}" > "$LOG" 2>&1; then
    status=OK
  else
    status=FAILED
  fi
  echo "$(( SECONDS - t0 )) s  $status  ${batch[*]}"
  grep -E "❌|💥|⏱|error:" "$LOG" | head -5
  [ "$status" = FAILED ] && { cat "$LOG"; exit 1; }
  i=$(( i + BATCH ))
done
echo "TOTAL $(( SECONDS - total0 )) s"
