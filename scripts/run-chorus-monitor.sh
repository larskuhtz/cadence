#!/usr/bin/env bash
# Chorus model-conformance monitor runner.
#
# Reads a JSONL trace from stdin (one label per line) and prints whether the
# Veil Chorus model ACCEPTS (simulates) it.
#   → Cadence/Monitor/ChorusMonitor.lean   (the monitor and its CLI)
#   → docs/Monitor.md                      (what acceptance does and does not mean)
#
# Runs on the Lean interpreter (`lean --run`) rather than as a compiled
# `lake exe`: the monitor needs no native build of its import closure, and the
# interpreter keeps it usable straight after `lake build`.
#
# Usage:  scripts/run-chorus-monitor.sh [monitor flags] < trace.jsonl
#         scripts/run-chorus-monitor.sh --help
# Exit:   0 accepted/ok · 1 model rejection · 2 usage/IO · 3 alphabet mismatch
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
TC="$HOME/.elan/toolchains/leanprover--lean4---v4.28.0"
export LD_LIBRARY_PATH="$TC/lib/lean:$TC/lib:${LD_LIBRARY_PATH:-}"
cd "$REPO"
# Default to the hand-written monitor (the test oracle); set CHORUS_MONITOR to
# Cadence/Monitor/ChorusMonitorGen.lean to run the #gen_monitor-generated one.
MON="${CHORUS_MONITOR:-Cadence/Monitor/ChorusMonitor.lean}"
exec lake env lean --run "$MON" "$@"
