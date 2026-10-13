#!/usr/bin/env bash
# Check the guide and the living documents for the style slips that keep
# coming back after a read-through.
#
#   scripts/doc-style.sh [FILE...]   (default: the guide's sources, the living
#                                     documents under docs/, and README.md)
#
# Four rules, each a short list of patterns
# (docs/Documentation.md, "The style check"):
#
#   history  words that tell how the text came to be rather than what is the
#            case: "no longer", "today", "retired", "when it lands",
#            "decided <year>", "since R<n>", and "now" next to a verb
#   correct  "honest" for a validator that follows the protocol: the
#            documents say "correct", as the paper does
#   count    a pin or finding count outside its home: "N/N real" (the
#            #veil_status pins), "P1–P<n>" and "<n> findings"; their homes,
#            docs/Architecture.md and docs/PaperAlignment.md, are exempt
#   lineref  a Lean file cited by line number ("Chorus.lean, lines 10–20",
#            "Chorus.lean:10"): cite the declaration by name
#
# Only prose is read: inline code spans and fenced code blocks are dropped
# first, so a Lean name such as `all_honest_recorded` or the clock `now` is
# not a hit.
#
# Records keep their history and are not read: History.md, AuditReport.md
# and MvbaPlan.md (a decision record). CLAUDE.md is the developers' file,
# with dated measurements, and is not read either.
#
# A justified use carries the marker `style-allow` on the same line or the
# line before, in a comment (`<!-- style-allow: why -->` in Markdown,
# `-- style-allow: why` in Lean).
#
# POSIX tools only (sh, awk, find, sort), like scripts/paper-cites.sh, so it
# runs wherever the docs build does. Exit status 1 on any hit.
set -eu
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
if [ "$#" -eq 0 ]; then
  files="$( { find docs/guide -name '*.lean' -type f
              find docs -name '*.md' -type f
              echo README.md; } | LC_ALL=C sort)"
  set -- $files
fi

LC_ALL=C exec awk '
function base(p,    n, a) { n = split(p, a, "/"); return a[n] }
function hit(rule, why) {
  if (allow) return
  printf "%s:%d: [%s] %s: %s\n", FILENAME, FNR, rule, why, orig
  bad++
}
FNR == 1 {
  b = base(FILENAME)
  skip = (b == "History.md" || b == "AuditReport.md" || b == "MvbaPlan.md" || b == "CLAUDE.md")
  home = (b == "Architecture.md" || b == "PaperAlignment.md")
  fence = 0; prevallow = 0
}
skip { next }
{
  orig = $0
  allow = prevallow || index($0, "style-allow") > 0
  prevallow = index($0, "style-allow") > 0
  if ($0 ~ /^[ \t]*```/) { fence = !fence; next }
  if (fence) next
  line = tolower($0)
  gsub(/`[^`]*`/, "", line)          # inline code spans
  gsub(/\]\([^)]*\)/, "]", line)     # link targets
  w = " " line " "
  gsub(/[^a-z0-9_ ]/, " & ", w)      # pad punctuation so words are delimited
  gsub(/[ \t]+/, " ", w)
  w = " " w " "

  # history
  if (w ~ / no longer /)                  hit("history", "\"no longer\"")
  if (w ~ / today /)                      hit("history", "\"today\"")
  if (w ~ / retired /)                    hit("history", "\"retired\"")
  if (w ~ / when it lands /)              hit("history", "\"when it lands\"")
  if (w ~ / decided 20[0-9][0-9]/)        hit("history", "\"decided <year>\"")
  if (w ~ / since r[0-9]/)                hit("history", "\"since R<n>\"")
  if (w ~ / (is|are|was|were|has|have|had|it|they|this|that|which) now / ||
      w ~ / now (is|are|has|have|uses|takes|reads|carries|lives|holds|says|states|covers|names|runs|derived|proven|derives|proves|the|a|an) /)
                                          hit("history", "\"now\"")
  # correct
  if (w ~ / honest /)                     hit("correct", "\"honest\" where \"correct\" is meant")
  # count
  if (!home) {
    if (w ~ / [0-9]+ \/ ?[0-9]+ real /)   hit("count", "a pin count; its home is the #veil_status pin")
    if (w ~ / p1 [-–]+ ?p[0-9]+ / || line ~ /p1(–|-)p[0-9]+/)
                                          hit("count", "a findings range; its home is PaperAlignment.md §6")
    if (w ~ / [0-9]+ findings /)          hit("count", "a findings count; its home is PaperAlignment.md §6")
  }
  # lineref
  if (line ~ /\.lean[^ ]*,? *lines? [0-9]/ || line ~ /\.lean:[0-9]/)
                                          hit("lineref", "a Lean file cited by line number")
}
END {
  if (bad) {
    printf "doc-style: %d hit(s); fix them, or mark a justified use with style-allow\n", bad > "/dev/stderr"
    exit 1
  }
  print "doc-style: clean"
}' "$@"
