#!/usr/bin/env bash
# Regression harness for the Chorus model-conformance monitor.
# Runs the happy-path trace (must be ACCEPTED) plus negative fixtures (must be
# rejected), checking both the verdict string and the process exit code.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUN="$HERE/run-chorus-monitor.sh"
TRACES="$HERE/../traces"
fail=0

check() { # name trace_file want_substr want_exit
  local name="$1" trace="$2" want="$3" wantrc="$4"
  # Run BOTH the hand-written monitor and the #gen_monitor-generated variant;
  # they must agree with each other and with the expectation.
  local outH rcH outG rcG
  outH="$("$RUN" < "$trace" 2>/dev/null)"; rcH=$?
  outG="$(CHORUS_MONITOR=Cadence/Monitor/ChorusMonitorGen.lean "$RUN" < "$trace" 2>/dev/null)"; rcG=$?
  if [[ "$outH" == *"$want"* && "$rcH" == "$wantrc" && "$outH" == "$outG" && "$rcH" == "$rcG" ]]; then
    echo "PASS  $name"
    echo "        → $outH (exit $rcH) [hand-written == generated]"
  else
    echo "FAIL  $name"
    echo "        hand-written: $outH (exit $rcH)"
    echo "        generated:    $outG (exit $rcG)"
    echo "        want:         substring '$want', exit $wantrc"
    fail=1
  fi
}

check "positive fast-path is ACCEPTED"     "$TRACES/fast_path_positive.jsonl"       "ACCEPTED"     0
check "negative fast-path (impl) ACCEPTED"  "$TRACES/fast_path_negative.jsonl"       "ACCEPTED"     0
check "vote before deadline rejected"       "$TRACES/reject_early_vote.jsonl"        "NOT ACCEPTED" 1
check "premature finalize rejected"         "$TRACES/reject_premature_finalize.jsonl" "NOT ACCEPTED" 1

echo
if [[ "$fail" == 0 ]]; then echo "ALL PASS"; else echo "SOME FAILED"; fi
exit $fail
