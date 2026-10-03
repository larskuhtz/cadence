# Shared setup for the model-conformance monitor scripts (docs/Monitor.md);
# sourced, not run.
#
# A monitor runs on the Lean interpreter: `lake env lean --run` on a driver
# in this directory, which imports one built module of Cadence/Monitor and
# runs its `main`. Only the import is elaborated, so a run costs loading the
# olean, not elaborating the monitor's source. Because the driver runs the
# *built* olean, `monitor_build` first brings the module up to date with
# `lake build` — a no-op when it is current, a rebuild after a source edit —
# so a run never executes stale code, and the monitor is usable straight
# after `lake build` or a source edit alike.

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
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

# monitor_build MODULE... — `lake build` the named modules of Cadence/Monitor
# (short names, e.g. ChorusMonitor), with lake's output on stderr so the
# monitor's stdout stays clean. The up-to-date check costs about half a
# monitor run, so a suite calls this once for every module it runs and then
# exports CADENCE_MONITOR_BUILT=1, which makes later calls no-ops.
monitor_build() {
  [ -n "${CADENCE_MONITOR_BUILT:-}" ] && return 0
  local mods=() m
  for m in "$@"; do mods+=("Cadence.Monitor.$m"); done
  if ! lake build -q "${mods[@]}" >&2; then
    echo "error: lake build ${mods[*]} failed; refusing to run a stale or missing olean" >&2
    return 2
  fi
}

# monitor_run MODULE [ARGS...] — run the `main` of Cadence/Monitor/MODULE
# through its driver; stdin, stdout and the exit code pass through.
monitor_run() {
  local m="$1"; shift
  lake env lean --run "scripts/monitor/$m.lean" "$@"
}
