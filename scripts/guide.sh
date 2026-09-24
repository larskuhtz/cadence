#!/usr/bin/env bash
# Build the guide — the authored walk-through for auditors — into the site.
#
#   scripts/guide.sh [outdir]      # default outdir: site/guide
#
# Normally run by `scripts/docs.sh` as one of its stages. Running it alone is
# the fast loop for editing the guide, and needs a previous `scripts/docs.sh`
# run: the guide quotes Veil model declarations from the literate renderer's
# JSON (`.lake/build/literate/json/`), and links into the rendered sources,
# which it expects at `../sources/` from its own page.
#
# The guide is a Verso document (`docs/guide/`), which is to say a Lean
# program: every statement it shows is the real declaration, every model
# quotation is the real source, and every status box is computed from the
# compiled development while it builds (`docs/guide/CadenceGuide/Audit.lean`).
# A renamed declaration, a vanished model property or an axiom beyond Lean's
# standard three therefore fails this build.
set -euo pipefail

cd "$(dirname "$0")/.."
OUT="${1:-site/guide}"
WORK=".lake/build/guide"

if [ ! -d .lake/build/literate/json ]; then
  echo "error: no literate JSON — run scripts/docs.sh first; the guide quotes" >&2
  echo "       the models from what its rendering stage wrote" >&2
  exit 1
fi

echo "=== building the guide (Verso)"
# The model quotations are read while the guide elaborates, from files lake
# does not track, so a re-render of the sources would not by itself rebuild
# the guide. Dropping the guide's own olean forces that one module to
# re-elaborate — seconds — and nothing else.
rm -f .lake/build/lib/lean/CadenceGuide.olean
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" lake -Kenv=dev build CadenceGuide

echo "=== rendering to $OUT"
rm -rf "$WORK" "$OUT"
mkdir -p "$WORK" "$(dirname "$OUT")"
# On the interpreter, like the conformance monitor: building an executable
# would link the whole import closure and force native compilation of Mathlib.
#
# One page. The guide is short, a single page opens from disk as well as over
# a server, and — the reason that decides it — its links into the sources are
# relative, so every guide page has to sit at the same depth.
lake -Kenv=dev env lean --run docs/guide/GuideMain.lean \
  --output "$WORK" --with-html-single --without-html-multi
mv "$WORK/html-single" "$OUT"

if [ ! -s "$OUT/index.html" ]; then
  echo "error: the guide produced no index.html in $OUT" >&2
  exit 1
fi

# The palette override (docs/guide/theme.css) is appended to Verso's own
# variables file, so it wins without patching anything Verso generated.
cat docs/guide/theme.css >> "$OUT/verso-vars.css"

echo "=== guide rendered into $OUT ($(du -sh "$OUT" | cut -f1))"
