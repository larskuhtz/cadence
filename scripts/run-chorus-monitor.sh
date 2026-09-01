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
cd "$REPO"
# Resolve the toolchain root wherever it lives (elan on a host, a plain
# toolchain inside the container image) and point the loader at its
# libraries — without this, `lean --run` can fail to load
# libLake_shared.so (docs/Container.md §4).
TC="$(lean --print-prefix 2>/dev/null || true)"
# Fallback: derive the elan directory name from lean-toolchain, so this never
# drifts from the pinned toolchain.
[ -n "$TC" ] || TC="$HOME/.elan/toolchains/$(tr -d '[:space:]' < lean-toolchain | sed 's|/|--|g; s|:|---|g')"
export LD_LIBRARY_PATH="$TC/lib/lean:$TC/lib:${LD_LIBRARY_PATH:-}"
# Default to the hand-written monitor (the test oracle); set CHORUS_MONITOR to
# Cadence/Monitor/ChorusMonitorGen.lean to run the #gen_monitor-generated one.
MON="${CHORUS_MONITOR:-Cadence/Monitor/ChorusMonitor.lean}"
exec lake env lean --run "$MON" "$@"
