#!/usr/bin/env bash
# Regenerate docs/paper-labels.tsv: every LaTeX label of the target paper
# revision, with the reference a reader sees for it in the rendered PDF.
#
#   scripts/paper-labels.sh [PAPER_REPO] [REV]
#
# PAPER_REPO defaults to ../../papers/cadence (relative to the main checkout),
# REV to the target named in the map's own header (docs/PaperAlignment.md §0).
# The paper checkout is only read: the revision is exported with `git archive`
# into a temporary directory, built there with tectonic (the main body first,
# then the supplement, which cross-references the main body's .aux through
# `xr`), and every `\newlabel` of the two .aux files is read back.
#
# The map is the authority for citations: a citation reads
# "<reference> (`label`)", with "Supplement, " in front for the supplement,
# and scripts/paper-cites.sh checks every citation against the map.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
out="$root/docs/paper-labels.tsv"
# The default is relative to the main checkout, so it also holds in a worktree.
main="$(cd "$(git -C "$root" rev-parse --path-format=absolute --git-common-dir)/.." && pwd)"
repo="${1:-$main/../../papers/cadence}"
rev="${2:-$( (sed -n 's/^# rev: //p' "$out" 2>/dev/null || true) | head -1)}"
rev="${rev:-48cac9a}"
command -v tectonic >/dev/null || { echo "tectonic not found" >&2; exit 1; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
git -C "$repo" archive --format=tar "$rev" | tar -x -C "$work"
full="$(git -C "$repo" rev-parse "$rev^{commit}")"

# Never trust a committed .aux: build from the sources.
rm -f "$work"/*.aux
(cd "$work" && mkdir -p out-main out-supp \
  && tectonic --keep-intermediates -o out-main main.tex >out-main/build.log 2>&1) \
  || { echo "main.tex failed to build; log: $work/out-main/build.log" >&2; trap - EXIT; exit 1; }
cp "$work/out-main/main.aux" "$work/main.aux"
(cd "$work" && tectonic --keep-intermediates -o out-supp supplementary-internal.tex \
  >out-supp/build.log 2>&1) \
  || { echo "supplementary-internal.tex failed to build; log: $work/out-supp/build.log" >&2; trap - EXIT; exit 1; }

python3 - "$work/out-main/main.aux" "$work/out-supp/supplementary-internal.aux" \
  "$full" >"$out.tmp" <<'EOF'
import re, sys

def groups(s, i):
    """Yield the top-level brace groups of s starting at index i."""
    out = []
    while i < len(s) and s[i] == '{':
        depth, j = 0, i
        while True:
            c = s[j]
            if c == '\\':
                j += 2
                continue
            if c == '{':
                depth += 1
            elif c == '}':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        out.append(s[i + 1:j])
        i = j + 1
    return out

NAMES = {
    'section': 'Section', 'subsection': 'Section', 'subsubsection': 'Section',
    'appendix': 'Appendix', 'subappendix': 'Appendix', 'subsubappendix': 'Appendix',
    'algorithm': 'Algorithm', 'lemma': 'Lemma', 'theorem': 'Theorem',
    'corollary': 'Corollary', 'proposition': 'Proposition',
    'definition': 'Definition', 'remark': 'Remark', 'module': 'Module',
    'figure': 'Figure', 'assumption': 'Assumption', 'table': 'Table',
}

def read(path, doc):
    plain, kind, order = {}, {}, []
    for line in open(path, encoding='utf-8', errors='replace'):
        if not line.startswith('\\newlabel{'):
            continue
        g = groups(line, len('\\newlabel'))
        if len(g) < 2:
            continue
        label, body = g[0], g[1]
        if label.endswith('@cref'):
            m = re.match(r'\{\[([^\]]*)\]', body)
            kind[label[:-5]] = m.group(1) if m else ''
            continue
        sub = groups(body, 0)
        if len(sub) < 3:
            continue
        plain[label] = (sub[0], sub[1], sub[2])
        order.append(label)
    rows, alg = [], None
    for label in order:
        num, page, name = plain[label]
        k = kind.get(label)
        if k is None:
            continue  # not a cleveref-visible label (e.g. the xr prefix machinery)
        if k == 'algorithm':
            alg, last = (num, name, page), 0
        if k == 'line':
            # A line belongs to the most recent algorithm label. Inside a
            # float the line's name is the caption; after a \captionof it is
            # the section title, so then the first line must be on the
            # label's page or the next, and the numbering must keep rising
            # (a reset without a new label is an unlabelled algorithm).
            near = alg is not None and page.isdigit() and alg[2].isdigit() \
                and 0 <= int(page) - int(alg[2]) <= 1
            ok = alg is not None and (alg[1] == name or
                                      (num.isdigit() and int(num) > last and (near or last > 0)))
            if not ok:
                sys.exit(f'{doc}: line label {label} is not inside a labelled algorithm')
            last = int(num) if num.isdigit() else last
            ref = f'Algorithm {alg[0]}, line {num}'
        elif k == 'equation':
            ref = f'Equation ({num})'
        elif k in NAMES:
            ref = f'{NAMES[k]} {num}'
        else:
            sys.exit(f'{doc}: label {label} has an unknown kind {k!r}')
        if not num:
            sys.exit(f'{doc}: label {label} has no rendered number')
        rows.append((label, doc, ref, page))
    return rows

main_aux, supp_aux, rev = sys.argv[1:4]
print(f'# Generated by scripts/paper-labels.sh; do not edit.')
print(f'# rev: {rev[:7]}')
print(f'# commit: {rev}')
print('# label\tdocument\treference\tpage')
for row in read(main_aux, 'main') + read(supp_aux, 'supplement'):
    print('\t'.join(row))
EOF
mv "$out.tmp" "$out"
echo "wrote $out: $(grep -vc '^#' "$out") labels at ${full:0:7}"
