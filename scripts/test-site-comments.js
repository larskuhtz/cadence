#!/usr/bin/env node
// Tests for `docs/site-comments.js`, the comment-markup renderer of the
// documentation site.
//
//   node scripts/test-site-comments.js [site/sources]
//
// Always runs the fixed cases below. Given the `sources/` directory of a
// rendered site (`scripts/docs.sh`), it also parses every comment on every
// page and checks that each rendering keeps the source text exactly — the
// delimiters are hidden, not deleted, which is what keeps the copy button
// copying the source.
"use strict";
const fs = require("fs");
const path = require("path");
const { parse } = require(path.join(__dirname, "..", "docs", "site-comments.js"));

// The source text a rendering stands for: delimiters included.
function source(tree) {
  return tree.map((a) => {
    if (typeof a === "string") return a;
    if ("code" in a) return a.open + a.code + a.close;
    if ("link" in a) return "[" + source(a.body) + a.close;
    const k = "strong" in a ? "strong" : "em";
    return a.delim + source(a[k]) + a.delim;
  }).join("");
}

// A compact view of a rendering, for the expectations below.
function view(tree) {
  return tree.map((a) => {
    if (typeof a === "string") return a;
    if ("code" in a) return "<c>" + a.code + "</c>";
    if ("link" in a) return "<a " + a.link + ">" + view(a.body) + "</a>";
    const k = "strong" in a ? "strong" : "em";
    return "<" + k + ">" + view(a[k]) + "</" + k + ">";
  }).join("");
}

let failures = 0;
function check(input, block, expected) {
  const tree = parse(input, block);
  const got = tree ? view(tree) : null;
  if (got !== expected) {
    failures++;
    console.log("FAIL", JSON.stringify(input));
    console.log("  got ", JSON.stringify(got));
    console.log("  want", JSON.stringify(expected));
  }
  if (tree && source(tree) !== input) {
    failures++;
    console.log("SOURCE CHANGED", JSON.stringify(input));
  }
}

// `null`: the comment is left exactly as it is.
check(" plain text only", false, null);
check(" a `code` span", false, " a <c>code</c> span");
check(" unpaired ` backtick", false, null);
check(" `code", false, null);
check(" ``a ` b`` double", false, " <c>a ` b</c> double");
check(" `` `x` `` padded", false, " <c>`x`</c> padded");
check(" *every* proposer", false, " <em>every</em> proposer");
check(" (*parenthesised*)", false, " (<em>parenthesised</em>)");
check(" **The mutation.** `x`", false, " <strong>The mutation.</strong> <c>x</c>");
check(" **bold with *em* inside**", false, " <strong>bold with <em>em</em> inside</strong>");
check(" *see `x`* here", false, " <em>see <c>x</c></em> here");
check(" *unclosed and `x`", false, " *unclosed and <c>x</c>");
// Asterisks that are not emphasis.
check(" a*b*c intraword", false, null);
check(" 2 * 3 * 4", false, null);
check(" ***triple*** stays", false, null);
check(" msg_* is a glob", false, null);
check(" `commit_assign_*` and *x*", false, " <c>commit_assign_*</c> and <em>x</em>");
// Underscores are identifiers here, never emphasis.
check(" _under_ stays", false, null);
// Line breaks: only a code span in a block comment may cross one.
check(" *open\nclose* no", true, null);
check(" `code\nacross` block", true, " <c>code\nacross</c> block");
// Links: absolute http(s) targets only.
check(" [`Cadence.lean`](./Cadence.lean)", false, " [<c>Cadence.lean</c>](./Cadence.lean)");
check(" [paper](https://arxiv.org/abs/2607.02275) link", false,
  " <a https://arxiv.org/abs/2607.02275>paper</a> link");
// Layout: a comment in columns is left alone; code spans and two spaces
// after a full stop do not count as columns.
check(" a | b | c with `x`", false, null);
check(" col1  col2 `x`", false, null);
check(" at `|M_i| ≥ 2f+1`, once", false, " at <c>|M_i| ≥ 2f+1</c>, once");
check(" root.  Then `x`", false, " root.  Then <c>x</c>");

const siteDir = process.argv[2];
if (siteDir) {
  const pages = [];
  (function walk(d) {
    for (const e of fs.readdirSync(d, { withFileTypes: true })) {
      const p = path.join(d, e.name);
      if (e.isDirectory()) walk(p);
      else if (e.name.endsWith(".html")) pages.push(p);
    }
  })(siteDir);
  const unescape = (s) => s.replace(/&lt;/g, "<").replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"').replace(/&#39;/g, "'").replace(/&amp;/g, "&");
  let comments = 0, rendered = 0;
  for (const page of pages) {
    const html = fs.readFileSync(page, "utf8");
    for (const m of html.matchAll(/<span class="comment (line|block) token"[^>]*>([^<]*)<\/span>/g)) {
      comments++;
      const text = unescape(m[2]);
      const tree = parse(text, m[1] === "block");
      if (!tree) continue;
      rendered++;
      if (source(tree) !== text) {
        failures++;
        console.log("SOURCE CHANGED", path.relative(siteDir, page), JSON.stringify(text.slice(0, 80)));
      }
    }
  }
  console.log(`${comments} comments on ${pages.length} pages, ${rendered} with markup rendered`);
}

console.log(failures ? `${failures} failure(s)` : "ok");
process.exit(failures ? 1 : 0);
