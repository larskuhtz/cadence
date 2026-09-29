#!/usr/bin/env bash
# Resolve the relative Markdown links written in this repository's sources.
#
#   scripts/site-links.sh check [FILE...]    # default: every Lean and Markdown file
#   scripts/site-links.sh table MODULES FILE...
#   scripts/site-links.sh base               # the repository base URL (below)
#
# A reference to a file is written as a Markdown link relative to the file it
# appears in — GitHub's convention, and the one `CLAUDE.md` asks for:
# `[Interfaces.lean](Interfaces.lean)` from `Cadence/`,
# `[ChorusDesign.md](../docs/ChorusDesign.md)` from there. GitHub resolves
# those natively. The rendered site cannot: its pages sit at other paths, and
# most targets are not on the site at all. This script is the one place that
# says where each link goes, for every consumer (`scripts/docs.sh`).
#
# `check` reads every link in the given files and fails, naming file and
# line, on any whose target does not exist in the repository.
#
# `table` does the same check and prints one row per distinct link,
#
#     <file> TAB <href> TAB <target>
#
# where <target> is `sources/<module path>/[#fragment]` — relative to the
# site root — for a Lean module the site renders (one per line of MODULES,
# the renderer's plan), and otherwise the file on the repository's web view at
# the commit being rendered. That base comes from `SITE_SOURCE_URL`
# (…/blob/<commit>, no trailing slash); `scripts/container.sh docs` sets it
# from the host, where the checkout's history is. Without it the base is
# derived from this checkout's `origin` and `HEAD`.
#
# What counts as a link: `[text](target)` outside code spans and fenced code
# blocks, whose target has no scheme and does not start with `#`. Reference-
# style links are not used in this repository and are not read.
set -euo pipefail

cd "$(dirname "$0")/.."

mode="${1:-}"; shift || true
case "$mode" in
  check) modules=/dev/null ;;
  table) modules="${1:?usage: site-links.sh table MODULES FILE...}"; shift ;;
  base) ;;
  *) echo "usage: scripts/site-links.sh {check [FILE...]|table MODULES FILE...|base}" >&2; exit 2 ;;
esac
if [ $# -eq 0 ] && [ "$mode" != base ]; then
  [ "$mode" = check ] || { echo "site-links.sh: no files given" >&2; exit 2; }
  # Everything that carries prose: the Lean sources, the guide, the docs.
  files=()
  while IFS= read -r f; do files+=("$f"); done < <(
    { find Cadence scripts docs .claude/skills -type f \( -name '*.lean' -o -name '*.md' \)
      printf '%s\n' Cadence.lean README.md CLAUDE.md; } | sort -u)
  set -- "${files[@]}"
fi

base=""
if [ "$mode" != check ]; then
  base="${SITE_SOURCE_URL:-}"
  if [ -z "$base" ]; then
    origin="$(git remote get-url origin 2>/dev/null || true)"
    rev="$(git rev-parse HEAD 2>/dev/null || true)"
    if [ -z "$origin" ] || [ -z "$rev" ]; then
      echo "error: SITE_SOURCE_URL is unset and this is not a git checkout;" >&2
      echo "       set it to the repository's web view at the rendered commit" >&2
      echo "       (https://github.com/<owner>/<repo>/blob/<commit>)" >&2
      exit 1
    fi
    # git@github.com:owner/repo.git and https://github.com/owner/repo(.git)
    web="$(printf '%s' "$origin" | sed -E 's#^git@([^:]+):#https://\1/#; s#\.git$##')"
    base="$web/blob/$rev"
  fi
  [ "$mode" = base ] && { printf '%s\n' "$base"; exit 0; }
fi

# Extract: file TAB line TAB href TAB repo-path, one per link occurrence.
# The path is the target resolved against the linking file's directory and
# normalised; "!" in the path column marks one that climbs out of the
# repository.
extract() {
  awk '
    function norm(p,    n, i, parts, out, k) {
      n = split(p, parts, "/"); k = 0
      for (i = 1; i <= n; i++) {
        if (parts[i] == "" || parts[i] == ".") continue
        if (parts[i] == "..") { if (k == 0) return "!"; k--; continue }
        out[++k] = parts[i]
      }
      p = ""
      for (i = 1; i <= k; i++) p = p (i > 1 ? "/" : "") out[i]
      return p
    }
    FNR == 1 { fence = 0; dir = FILENAME; sub(/[^\/]*$/, "", dir) }
    /^[[:space:]]*```/ { fence = !fence; next }
    fence { next }
    {
      line = $0
      gsub(/`[^`]*`/, "", line)            # code spans on one line
      while (match(line, /\]\([^()[:space:]]+\)/)) {
        href = substr(line, RSTART + 2, RLENGTH - 3)
        line = substr(line, RSTART + RLENGTH)
        if (href ~ /^[a-zA-Z][a-zA-Z0-9+.-]*:/ || href ~ /^#/) continue
        # The guide is a page of the site, and the trust boundary is a page
        # the site generates: the one link written in site layout.
        if (FILENAME ~ /^docs\/guide\// && href == "../trust-boundary.html") continue
        path = href; sub(/#.*/, "", path)
        print FILENAME "\t" FNR "\t" href "\t" norm(dir path)
      }
    }' "$@"
}

rows="$(extract "$@")"
[ -n "$rows" ] || exit 0

dead=0
while IFS=$'\t' read -r file line href path; do
  if [ "$path" = "!" ] || [ -z "$path" ] || [ ! -e "$path" ]; then
    echo "dead link: $file:$line: ($href)" >&2
    dead=$((dead + 1))
  fi
done <<< "$rows"
if [ "$dead" -ne 0 ]; then
  echo "error: $dead relative link(s) point at nothing in the repository" >&2
  exit 1
fi
[ "$mode" = check ] && exit 0

# Table: one row per (file, href).
printf '%s\n' "$rows" | cut -f1,3,4 | sort -u \
| while IFS=$'\t' read -r file href path; do
    frag=""; case "$href" in *'#'*) frag="#${href#*#}" ;; esac
    target=""
    case "$path" in
      *.lean)
        mod="${path%.lean}"; mod="${mod//\//.}"
        if grep -qxF "$mod" "$modules"; then
          target="sources/${path%.lean}/$frag"
        fi ;;
    esac
    if [ -z "$target" ]; then
      if [ -d "$path" ]; then target="${base/\/blob\//\/tree\/}/$path$frag"
      else target="$base/$path$frag"; fi
    fi
    printf '%s\t%s\t%s\n' "$file" "$href" "$target"
  done
