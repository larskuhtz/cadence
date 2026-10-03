#!/usr/bin/env bash
# Chorus model-conformance monitor runner.
#
# Reads a JSONL trace from stdin (one label per line) and prints whether the
# Veil Chorus model ACCEPTS (simulates) it.
#   → Cadence/Monitor/ChorusMonitor.lean   (the monitor and its CLI)
#   → docs/Monitor.md                      (what acceptance does and does not mean)
#
# Runs the built monitor module on the Lean interpreter (`lean --run`, through
# a driver in scripts/monitor/) rather than as a compiled `lake exe`: the
# monitor needs no native build of its import closure. The module is
# `lake build`-ed first (a no-op when current), so the monitor is usable
# straight after `lake build` and never runs a stale olean; scripts/monitor/env.sh
# has the mechanism.
#
# Usage:  scripts/run-chorus-monitor.sh [monitor flags] < trace.jsonl
#         scripts/run-chorus-monitor.sh --help
# Env:    CHORUS_MONITOR  which monitor: ChorusMonitor (default, the hand-written
#                         test oracle) or ChorusMonitorGen (the #gen_monitor-
#                         generated one); the module name or the source path
#                         (Cadence/Monitor/ChorusMonitorGen.lean) also work.
# Exit:   0 accepted/ok · 1 model rejection · 2 usage/IO · 3 alphabet mismatch
set -euo pipefail
. "$(dirname "${BASH_SOURCE[0]}")/monitor/env.sh"
MON="${CHORUS_MONITOR:-ChorusMonitor}"
MON="$(basename "${MON%.lean}")"
MON="${MON#Cadence.Monitor.}"
case "$MON" in
  ChorusMonitor|ChorusMonitorGen) ;;
  *) echo "error: CHORUS_MONITOR='${CHORUS_MONITOR}' is not ChorusMonitor or ChorusMonitorGen" >&2
     exit 2 ;;
esac
monitor_build "$MON" || exit 2
monitor_run "$MON" "$@"
