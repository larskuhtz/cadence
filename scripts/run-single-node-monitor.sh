#!/usr/bin/env bash
# Single-node Chorus model-conformance monitor.
#
# Checks whether the Veil Chorus model simulates ONE selected node in isolation,
# given a whole-system observable trace on stdin: the node's own actions are
# validated under the all-honest instance, and every other node's message is
# admitted from the trace (consumer-side projection). `n = 3f+1` is then the
# quorum universe, not the number of monitored nodes.
#
# Usage:  scripts/run-single-node-monitor.sh <node-id> < whole_system_trace.jsonl
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NODE="${1:?usage: scripts/run-single-node-monitor.sh <node-id 0..3> < trace.jsonl}"
exec "$HERE/run-chorus-monitor.sh" --node "$NODE"
