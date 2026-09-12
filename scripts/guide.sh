#!/usr/bin/env bash
# Build the guide — the short, authored introduction to reading this
# development's sources.
#
#   scripts/guide.sh [outdir]      # default outdir: site/guide
#
# The guide is a Verso document (`docs/guide/`), which is to say a Lean
# program: its references to this development's declarations are resolved when
# it builds, and its embedded docstrings are the real ones from the source. A
# renamed declaration therefore breaks this build rather than rotting a link.
#
# It is not the documentation of record. `docs/` is comprehensive and the
# sources are authoritative; the guide exists to make them approachable, and
# deliberately states no facts of its own — no counts, no measurements, no
# status claims — so that there is nothing in it to drift.
#
# Behind `-Kenv=dev`, like the documentation generator, so a normal
# `lake build` neither resolves nor builds Verso.
set -euo pipefail

cd "$(dirname "$0")/.."
OUT="${1:-site/guide}"

echo "=== building the guide (Verso)"
# Elaborating the document imports the development, because that is what makes
# the cross-references checked; expect it to take about as long as any other
# consumer of the full import closure.
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" lake -R -Kenv=dev build CadenceGuide

echo "=== rendering to $OUT"
mkdir -p "$OUT"
# On the interpreter, like the conformance monitor: building an executable
# would link the whole import closure and force native compilation of Mathlib.
lake -R -Kenv=dev env lean --run docs/guide/GuideMain.lean --output "$OUT"

# Verso emits a multi-page site under html-multi/ (and a single-page variant
# when asked). Surface it at the top so a link to the guide's directory works.
if [ ! -s "$OUT/html-multi/index.html" ]; then
  echo "error: the guide produced no html-multi/index.html in $OUT" >&2
  exit 1
fi
cat > "$OUT/index.html" <<'REDIRECT'
<!DOCTYPE html><meta charset="utf-8">
<meta http-equiv="refresh" content="0; url=html-multi/index.html">
<title>Reading the Cadence formalization</title>
<p><a href="html-multi/index.html">Reading the Cadence formalization</a></p>
REDIRECT

echo
echo "=== guide rendered into $OUT ($(du -sh "$OUT" | cut -f1))"
echo "    open $OUT/index.html"
