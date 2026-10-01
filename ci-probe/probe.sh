#!/usr/bin/env bash
# TEMPORARY CI instrumentation (PR #54): name the phase of the Chorus model
# build that peaks under the runner's memory cap. Reverted before the PR is
# ready. Changes no limits.
CG=/sys/fs/cgroup
gb() { awk -v b="${1:-0}" 'BEGIN{printf "%.2f", b/1073741824}'; }
probe() {  # probe <label> <file>
  local label=$1 file=$2 t0=$SECONDS
  echo "=== PROBE $label: $file — start $(date +%T); memory.max=$(cat $CG/memory.max 2>/dev/null)"
  ( while true; do
      cur=$(cat $CG/memory.current 2>/dev/null)
      anon=$(awk '$1=="anon"{print $2}' $CG/memory.stat 2>/dev/null)
      fil=$(awk '$1=="file"{print $2}' $CG/memory.stat 2>/dev/null)
      rss=$(ps -eo rss=,comm= | awk '$2=="lean"{s+=$1} END{printf "%.2f", s/1048576}')
      echo "PROBE-MEM $label t=$(( SECONDS - t0 ))s cur=$(gb "$cur")G anon=$(gb "$anon")G file=$(gb "$fil")G leanRSS=${rss}G"
      sleep 10
    done ) &
  local S=$!
  bash scripts/scratch.sh "$file" 2>&1 | while IFS= read -r l; do
    echo "PROBE-OUT $label t=$(( SECONDS - t0 ))s ${l:0:300}"; done
  local rc=${PIPESTATUS[0]}
  kill $S 2>/dev/null
  echo "=== PROBE $label: exit $rc after $(( SECONDS - t0 )) s; memory.peak=$(gb "$(cat $CG/memory.peak 2>/dev/null)")G; events: $(tr '\n' ' ' < $CG/memory.events 2>/dev/null)"
}
# 1. master's model against the image's oleans (master, old Veil): the baseline.
probe master ci-probe/ChorusMaster.lean
# 2. this branch's model: build its imports on the new Veil first.
lake build Cadence.Interfaces Cadence.Primitives Cadence.QuorumCounting Cadence.Tooling 2>&1 | tail -3
probe branch Cadence/Chorus.lean
