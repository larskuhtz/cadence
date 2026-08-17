#!/usr/bin/env bash
# Regression for the single-node monitor mode (`--node I`).
#
# From the real whole-system emitted trace, the model must simulate EACH honest
# node in isolation (validate that node's actions, admit the rest), and must
# REJECT when a member of a node's admitted quorum is missing.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUN="$HERE/run-chorus-monitor.sh"
T="$HERE/../traces/fast_path_negative.jsonl"
fail=0

check() { # name  input-cmd  node  want_substr  want_exit
  local name="$1" incmd="$2" node="$3" want="$4" wantrc="$5" out rc
  out="$(eval "$incmd" | "$RUN" --node "$node" 2>/dev/null)"; rc=$?
  if [[ "$out" == *"$want"* && "$rc" == "$wantrc" ]]; then
    echo "PASS  $name"
    echo "        → $out (exit $rc)"
  else
    echo "FAIL  $name"
    echo "        → $out (exit $rc); want substring '$want', exit $wantrc"
    fail=1
  fi
}

check "node 0 simulated in isolation"  "cat '$T'"  0  "ACCEPTED"      0
check "node 1 simulated in isolation"  "cat '$T'"  1  "ACCEPTED"      0
check "node 0 rejects unbacked quorum (node-1 vote dropped from the trace)" \
      "grep -v '\"vote\", \"args\": \[1\]' '$T'"   0  "NOT ACCEPTED"  1

echo
if [[ $fail == 0 ]]; then echo "ALL PASS"; else echo "SOME FAILED"; fi
exit $fail
