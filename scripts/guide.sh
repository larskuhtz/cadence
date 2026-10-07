#!/usr/bin/env bash
# Build the guide — "Cadence Verification", the site's entry point — into the
# site: one page for the front matter and one per chapter.
#
#   scripts/guide.sh [outdir]      # default outdir: site/guide
#
# Normally run by `scripts/docs.sh` as one of its stages. Running it alone is
# the fast loop for editing the guide, and needs a previous `scripts/docs.sh`
# run: the guide quotes Veil model declarations from the literate renderer's
# JSON (`.lake/build/literate/json/`), and links into the rendered sources,
# which it expects at `../sources/` from the guide's root.
#
# The guide is a Verso document (`docs/guide/`), which is to say a Lean
# program: every statement it shows is the real declaration, every model
# quotation is the real source, and every status box is computed from the
# compiled development while it builds (`docs/guide/CadenceGuide/Elements.lean`
# lists the elements). A renamed declaration, a vanished model property, an
# axiom beyond Lean's standard three, a diagram naming a declaration that is
# gone or an audit table that no longer matches its model therefore fails this
# build.
set -euo pipefail

cd "$(dirname "$0")/.."
OUT="${1:-site/guide}"
WORK=".lake/build/guide"

if [ ! -d .lake/build/literate/json ] || [ ! -f .lake/build/literate/site-links.js ]; then
  echo "error: no literate JSON or link table — run scripts/docs.sh first; the" >&2
  echo "       guide quotes the models from what its rendering stage wrote, and" >&2
  echo "       resolves its links through the table that stage generates" >&2
  exit 1
fi

echo "=== building the guide (Verso)"
# The chapters read files lake does not track while they elaborate — the
# model quotations' JSON, the anchors, the diagrams, the audit tables' data —
# so a change to one of those would not by itself rebuild the guide. Dropping
# the oleans of the root and of the chapters forces those modules to
# re-elaborate, seconds each, and nothing else: the elements' own modules read
# no file while they build.
rm -f .lake/build/lib/lean/CadenceGuide.olean
rm -f .lake/build/lib/lean/CadenceGuide/Chapters/*.olean
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" lake -Kenv=dev build CadenceGuide

echo "=== rendering to $OUT"
rm -rf "$WORK" "$OUT"
mkdir -p "$WORK" "$(dirname "$OUT")"
# On the interpreter, like the conformance monitor: building an executable
# would link the whole import closure and force native compilation of Mathlib.
#
# One page per chapter (`--depth 1`: the root's parts are pages, their
# sections stay on them). Verso gives every page a `<base href>` at the
# guide's root, so a relative link means the same on every page whatever its
# depth: the elements write their links into the sources as `../sources/…`,
# and the rewriting below produces the same form.
lake -Kenv=dev env lean --run docs/guide/GuideMain.lean \
  --output "$WORK" --depth 1
mv "$WORK/html-multi" "$OUT"

if [ ! -s "$OUT/index.html" ]; then
  echo "error: the guide produced no index.html in $OUT" >&2
  exit 1
fi

# The guide's own links, resolved statically. Each source file writes them
# relative to itself, and the link table (scripts/site-links.sh, via
# scripts/docs.sh) says where each goes; a site target is relative to the
# site root, which is `../` from the guide's root. A page does not record
# which file wrote it, so every page is rewritten from the table of all the
# guide's files at once. That is sound only while no href means two
# different things in two of them, so that is checked: the root and the
# chapters sit in different directories, and the same relative path could
# name different files from each. Quotations and embedded docstrings were
# written in other files; their links are resolved in the browser
# (docs/site-comments.js).
jq -r 'to_entries[] | select(.key | startswith("docs/guide/")) | .value | to_entries[]
       | "\(.key)\t\(.value | if startswith("sources/") then "../" + . else . end)"' \
  .lake/build/literate/links.json | sort -u > "$WORK/guide-links.tsv"
if ! awk -F'\t' '($1 in t) && t[$1] != $2 {
        print "error: the guide link (" $1 ") goes to " t[$1] " from one file and to " $2 \
              " from another; write it so that it names one file" > "/dev/stderr"; bad = 1 }
      { t[$1] = $2 } END { exit bad }' "$WORK/guide-links.tsv"; then
  exit 1
fi
while IFS= read -r page; do
  awk -F'\t' 'NR == FNR { map["href=\"" $1 "\""] = "href=\"" $2 "\""; next }
    { for (k in map) { while ((i = index($0, k)) > 0)
        $0 = substr($0, 1, i - 1) map[k] substr($0, i + length(k)) }
      print }' "$WORK/guide-links.tsv" "$page" > "$page.tmp"
  mv "$page.tmp" "$page"
done < <(find "$OUT" -name '*.html')

# The palette override (docs/guide/theme.css) is appended to Verso's own
# variables file, so it wins without patching anything Verso generated.
cat docs/guide/theme.css >> "$OUT/verso-vars.css"

echo "=== guide rendered into $OUT ($(du -sh "$OUT" | cut -f1))"
