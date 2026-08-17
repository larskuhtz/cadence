#!/usr/bin/env bash
# Negative-regression harness for the Chorus model-conformance monitor.
#
# Confirms the monitor has teeth: starting from a model-ACCEPTED trace (by
# default the one emitted from a real n=4 implementation run), apply each
# mutation in Cadence/Monitor/TraceMutate.lean -- every mutation models a class of
# implementation divergence -- and assert the monitor REJECTS the result.
#
# Usage:  scripts/test-monitor-divergence.sh [base-trace.jsonl]
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
TC="$HOME/.elan/toolchains/leanprover--lean4---v4.28.0"
export LD_LIBRARY_PATH="$TC/lib/lean:$TC/lib:${LD_LIBRARY_PATH:-}"
cd "$REPO"

BASE="${1:-traces/fast_path_negative.jsonl}"
MUT=Cadence/Monitor/TraceMutate.lean
MON="${CHORUS_MONITOR:-Cadence/Monitor/ChorusMonitor.lean}"
fail=0

# Mutation → the implementation-bug class it models (for the report).
declare -A WHAT=(
  [shrink-quorum]="accepts an undersized (<2f+1) quorum certificate"
  [forge-quorum]="counts a non-voter toward a quorum"
  [drop-commitqc]="finalizes without a commit certificate"
  [drop-fastqc]="casts a fast-commit vote with no FastQC behind it"
  [swap-verdict]="commits the opposite verdict (pos vs neg)"
  [reorder-vote]="uses a quorum before its evidence exists"
  [dup-finalize]="finalizes the same slot twice"
)

# Sanity: the base trace must be ACCEPTED.
base_out=$(lake env lean --run "$MON" < "$BASE" 2>/dev/null); base_rc=$?
if [[ "$base_out" == *ACCEPTED* && "$base_rc" == 0 ]]; then
  echo "BASE  $(basename "$BASE") → $base_out"
else
  echo "FAIL  base trace not accepted: $base_out (exit $base_rc)"; exit 1
fi
echo

reject() { # mutation
  local mut="$1" out rc
  out=$(MUTATION="$mut" lake env lean --run "$MUT" < "$BASE" 2>/dev/null \
          | lake env lean --run "$MON" 2>/dev/null); rc=$?
  if [[ "$out" == *"NOT ACCEPTED"* && "$rc" != 0 ]]; then
    printf "PASS  %-14s (%s)\n" "$mut" "${WHAT[$mut]}"
    echo "        → $out"
  else
    printf "FAIL  %-14s not rejected: %s (exit %s)\n" "$mut" "$out" "$rc"
    fail=1
  fi
}

for m in shrink-quorum forge-quorum drop-commitqc drop-fastqc swap-verdict reorder-vote dup-finalize; do
  reject "$m"
done

echo
if [[ $fail == 0 ]]; then echo "ALL PASS (monitor rejected every divergence)"; else echo "SOME FAILED"; fi
exit $fail
