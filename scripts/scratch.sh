#!/usr/bin/env bash
# Run a scratch Lean file with the solver available.
#
#   scripts/scratch.sh /path/to/scratch.lean
#
# `lake env lean <file>` is not enough: the cvc5 bindings, lean-smt, lean-auto
# and Qq are loaded as native plugins, and lake passes those only for modules it
# builds itself. Without them a file containing `#check_vc` / `#prove_vc` dies
# with "Could not find native implementation of external declaration
# 'cvc5.TermManager.new'" — an abort, with no Lean diagnostic.
#
# The plugin list is read out of a real module's build setup, so it cannot
# drift from what `lake build` uses.
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO"
[ $# -ge 1 ] || { echo "usage: scripts/scratch.sh <file.lean> [lean args...]" >&2; exit 2; }

SETUP="$(find .lake/build/ir -name '*.setup.json' -print -quit 2>/dev/null || true)"
if [ -z "$SETUP" ]; then
  echo "no build setup under .lake/build/ir — run 'lake build Cadence.Chorus' first" >&2
  exit 2
fi

PLUGINS=()
while IFS= read -r line; do PLUGINS+=("$line"); done < <(
  python3 -c "
import json
for p in json.load(open('$SETUP'))['plugins']:
    print('--plugin=' + p['path'])
"
)

exec lake env lean "${PLUGINS[@]}" "$@"
