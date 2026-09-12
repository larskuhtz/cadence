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
# Clean first: renaming a section leaves its old directory behind otherwise.
rm -rf "$OUT"
mkdir -p "$OUT"
# On the interpreter, like the conformance monitor: building an executable
# would link the whole import closure and force native compilation of Mathlib.
#
# --depth 1 keeps a page per top-level section rather than splitting at every
# subheading. --with-html-single additionally emits the whole guide as one
# page, which is what works when the output is opened from the filesystem:
# Verso's multi-page links are directory-style and need a server to resolve.
lake -R -Kenv=dev env lean --run docs/guide/GuideMain.lean \
  --output "$OUT" --depth 1 --with-html-single

if [ ! -s "$OUT/html-multi/index.html" ]; then
  echo "error: the guide produced no html-multi/index.html in $OUT" >&2
  exit 1
fi

# The palette override (docs/guide/theme.css) is appended to Verso's own
# variables file, so it wins without patching anything Verso generated.
for d in "$OUT"/html-multi "$OUT"/html-single; do
  [ -d "$d" ] || continue
  [ -f "$d/verso-vars.css" ] && cat docs/guide/theme.css >> "$d/verso-vars.css"
done

# Landing page. The multi-page version needs a web server, so the
# single-page one is the sensible default when opening files directly.
cat > "$OUT/index.html" <<'REDIRECT'
<!DOCTYPE html><meta charset="utf-8">
<meta http-equiv="refresh" content="0; url=html-single/index.html">
<title>Reading the Cadence formalization</title>
<p><a href="html-single/index.html">Reading the Cadence formalization</a>
   (one page) &middot;
   <a href="html-multi/index.html">by section</a> — needs a web server.</p>
REDIRECT

echo
echo "=== guide rendered into $OUT ($(du -sh "$OUT" | cut -f1))"
echo "    open $OUT/index.html                 (single page, works from disk)"
echo "    python3 -m http.server -d $OUT       (then browse the sectioned version)"
