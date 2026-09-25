// Inline Markdown in plain comments (`--` and `/- … -/`) on the rendered
// sources. Loaded through `extra_js` in `literate.toml`; the styles are
// `docs/site-overrides.css` §5, and why this exists at all is
// `docs/VersoIssues.md` §6.
//
// Verso renders a doc comment's Markdown but prints a plain comment as one
// text token, so the markup this development writes in its comments —
// `code`, *emphasis*, **strong**, the occasional link — shows up literally.
// This script renders that inline subset, in place, and deliberately nothing
// more:
//
// * Inline only. A comment stays where it is in the code, in the code font;
//   there is no block structure (paragraphs, lists, headings).
// * The source text is kept. Delimiters are wrapped in hidden spans rather
//   than deleted, so `textContent` — what the copy button copies — is the
//   source exactly as written.
// * Conservative. Whatever could be misread is left as written: a backtick
//   without a partner, `***`, intraword `*` (as in `a*b`), emphasis across a
//   line break, `_underscores_` (they are nearly always part of an
//   identifier here), and every link whose target is not an absolute
//   http(s) URL (the relative ones point into the repository, not the site).
// * Layout-preserving. Hiding delimiters shortens a line, which is harmless
//   in prose and wrong in a comment laid out in columns; a comment with an
//   aligned run of spaces or a `|` is left untouched.
//
// A `--` comment is one token per line, so markup cannot span two of them;
// a `/- … -/` comment is one token, and a code span may cross a line break
// inside it.

(function () {
  "use strict";

  // --- parsing: text -> nodes, or null to leave the comment as it is ------

  // A line with an internal run of two or more spaces, or with a `|`, is
  // aligned rather than prose. Only the text outside code spans counts
  // (`|M_i|` in a code span is a cardinality, not a column), and two spaces
  // after a full stop are a typing habit, not a column.
  function looksLaidOut(atoms) {
    var text = atoms.map(function (a) { return typeof a === "string" ? a : "x"; }).join("");
    return text.split("\n").some(function (line) {
      return /[^\s.!?:;] {2,}\S/.test(line) || line.indexOf("|") !== -1;
    });
  }

  // Code spans first: CommonMark's rule, a run of n backticks closed by the
  // next run of exactly n. Returns atoms: single characters, or code atoms.
  function codeAtoms(text, allowNewline) {
    var atoms = [];
    var i = 0;
    while (i < text.length) {
      if (text[i] !== "`") { atoms.push(text[i]); i++; continue; }
      var n = 0;
      while (text[i + n] === "`") n++;
      var close = -1;
      for (var j = i + n; j < text.length; j++) {
        if (text[j] === "\n" && !allowNewline) break;
        if (text[j] !== "`") continue;
        var m = 0;
        while (text[j + m] === "`") m++;
        if (m === n) { close = j; break; }
        j += m - 1;
      }
      if (close === -1) {
        for (var k = 0; k < n; k++) atoms.push("`");
        i += n;
        continue;
      }
      var body = text.slice(i + n, close);
      // One space of padding on each side is stripped, as in CommonMark.
      var lead = "", trail = "";
      if (body.length > 2 && body[0] === " " && body[body.length - 1] === " " && /\S/.test(body)) {
        lead = " "; trail = " "; body = body.slice(1, -1);
      }
      atoms.push({ code: body, open: "`".repeat(n) + lead, close: trail + "`".repeat(n) });
      i = close + n;
    }
    return atoms;
  }

  function isSpace(a) { return a === undefined || (typeof a === "string" && /\s/.test(a)); }
  function isWordChar(a) { return typeof a === "string" && /[\p{L}\p{N}]/u.test(a); }

  // `[text](https://…)` with no line break in the text; the text may hold
  // code atoms. Anything else stays as characters.
  function linkAtoms(atoms) {
    var out = [];
    for (var i = 0; i < atoms.length; i++) {
      if (atoms[i] === "[") {
        var j = i + 1;
        while (j < atoms.length && atoms[j] !== "]" && atoms[j] !== "\n" && atoms[j] !== "[") j++;
        if (atoms[j] === "]" && atoms[j + 1] === "(" && j > i + 1) {
          var k = j + 2, url = "";
          while (k < atoms.length && typeof atoms[k] === "string" && atoms[k] !== ")" && !/\s/.test(atoms[k])) {
            url += atoms[k]; k++;
          }
          if (atoms[k] === ")" && /^https?:\/\/\S+$/.test(url)) {
            out.push({ link: url, body: atoms.slice(i + 1, j), close: "](" + url + ")" });
            i = k;
            continue;
          }
        }
      }
      out.push(atoms[i]);
    }
    return out;
  }

  // Emphasis over the atoms: runs of one `*` (em) or two (strong); longer
  // runs stay literal. An opener is followed by a non-space and not preceded
  // by a word character; a closer mirrors it. Pairs never cross a line
  // break. Returns the tree: strings, code/link atoms, {em|strong: [...]}.
  function emphasis(atoms) {
    var delims = [];
    for (var i = 0; i < atoms.length; i++) {
      if (atoms[i] !== "*") continue;
      var n = 0;
      while (atoms[i + n] === "*") n++;
      if (n <= 2) {
        var before = atoms[i - 1], after = atoms[i + n];
        delims.push({
          at: i, n: n,
          canOpen: !isSpace(after) && !isWordChar(before),
          canClose: !isSpace(before) && !isWordChar(after),
        });
      }
      i += n - 1;
    }
    var pairs = [];
    var stack = [];
    var d = 0;
    for (var p = 0; p < atoms.length; p++) {
      if (atoms[p] === "\n") stack = [];
      if (d < delims.length && delims[d].at === p) {
        var cur = delims[d++];
        var matched = false;
        if (cur.canClose) {
          for (var s = stack.length - 1; s >= 0; s--) {
            if (stack[s].n === cur.n) {
              pairs.push({ open: stack[s], close: cur });
              stack.length = s;
              matched = true;
              break;
            }
          }
        }
        if (!matched && cur.canOpen) stack.push(cur);
        p += cur.n - 1;
      }
    }
    if (pairs.length === 0) return atoms.slice();
    var starts = {}, ends = {};
    pairs.forEach(function (pr) { starts[pr.open.at] = pr; ends[pr.close.at] = pr; });
    function build(from, to) {
      var out = [];
      for (var q = from; q < to; q++) {
        if (starts[q]) {
          var pr = starts[q];
          var kind = pr.open.n === 2 ? "strong" : "em";
          var node = {};
          node[kind] = build(q + pr.open.n, pr.close.at);
          node.delim = "*".repeat(pr.open.n);
          out.push(node);
          q = pr.close.at + pr.close.n - 1;
        } else {
          out.push(atoms[q]);
        }
      }
      return out;
    }
    return build(0, atoms.length);
  }

  function hasMarkup(tree) {
    return tree.some(function (a) { return typeof a !== "string"; });
  }

  function parse(text, block) {
    var atoms = codeAtoms(text, block);
    if (looksLaidOut(atoms)) return null;
    var tree = emphasis(linkAtoms(atoms));
    return hasMarkup(tree) ? tree : null;
  }

  // --- rendering: nodes -> DOM ---------------------------------------------

  function delim(doc, s) {
    var span = doc.createElement("span");
    span.className = "md-delim";
    span.textContent = s;
    return span;
  }

  function render(doc, tree, parent) {
    var text = "";
    function flush() {
      if (text) { parent.appendChild(doc.createTextNode(text)); text = ""; }
    }
    tree.forEach(function (a) {
      if (typeof a === "string") { text += a; return; }
      flush();
      if ("code" in a) {
        var code = doc.createElement("code");
        code.className = "comment-code";
        code.appendChild(delim(doc, a.open));
        code.appendChild(doc.createTextNode(a.code));
        code.appendChild(delim(doc, a.close));
        parent.appendChild(code);
      } else if ("link" in a) {
        var link = doc.createElement("a");
        link.href = a.link;
        link.appendChild(delim(doc, "["));
        render(doc, a.body, link);
        link.appendChild(delim(doc, a.close));
        parent.appendChild(link);
      } else {
        var kind = "strong" in a ? "strong" : "em";
        var el = doc.createElement(kind);
        el.appendChild(delim(doc, a.delim));
        render(doc, a[kind], el);
        el.appendChild(delim(doc, a.delim));
        parent.appendChild(el);
      }
    });
    flush();
  }

  function renderAll(doc) {
    var spans = doc.querySelectorAll(".hl.lean .comment.line, .hl.lean .comment.block");
    spans.forEach(function (span) {
      if (span.children.length > 0) return;
      var tree = parse(span.textContent, span.classList.contains("block"));
      if (!tree) return;
      var frag = doc.createDocumentFragment();
      render(doc, tree, frag);
      span.textContent = "";
      span.appendChild(frag);
    });
  }

  if (typeof module !== "undefined" && module.exports) {
    module.exports = { parse: parse, render: render, renderAll: renderAll };
  } else if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", function () { renderAll(document); });
  } else {
    renderAll(document);
  }
})();
