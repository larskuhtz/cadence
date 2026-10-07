# Diagrams

The guide's diagrams, one hand-written SVG file per diagram. The guide
inlines a file into its page; on GitHub, a Markdown page shows the same file
as an image, `![…](diagrams/modules-contracts.svg)` from `docs/`.

| File | Shows | Used in |
|---|---|---|
| [modules-contracts.svg](modules-contracts.svg) | the composed claims on top; the glue and the two contracts it consumes; the Conductor and Chorus, each with the contract it meets; the MVBA under Chorus; the assumed ACS under the Conductor, with its ideal model named as a consistency witness; the receipt layer beside Chorus | guide chapters 0 and 1; the README's landing section; [Architecture.md](../Architecture.md) §1.1 |
| [claim-premise-witness.svg](claim-premise-witness.svg) | one claim, `Composed.liveness`, with its premises, the proof step that uses each, the witness model that meets all of them, and plausibility as the part no tool checks | guide chapter 2; the opener of [Premises.md](../Premises.md) |
| [model-to-theorem.svg](model-to-theorem.svg) | the pipeline for Chorus, from the model to the axiom pin, with what is trusted at each step | guide chapter 7; the README's "How the proof fits together" |
| [chorus-slot.svg](chorus-slot.svg) | one slot of Chorus on its `phase` axis: the proposal, the vote, the fast path and the fallback path, and the adversary, with the actions the guide quotes | guide chapter 3 |

## What the diagrams cite

The diagrams name declarations exactly as the sources do, and cite the
paper by its rendered numbers. The labels behind those numbers:

* Definition 1 (`def:safety`), MCP Safety;
  Definition 2 (`def:liveness`) and Lemma 2 (`lemma:cadence-liveness`),
  𝓡-Liveness; Definition 3 (`def:censorship-resistance`);
  Corollary 4 (`cor:chorus-correctness-within-cadence`);
  Lemma 5 (`lemma:cadence-bounded-concurrency`).
* Algorithm 1 (`algorithm:cadence`), the glue;
  Module 1 (`mod:slotconsensus`), met by Chorus;
  Module 2 (`mod:orchestrator_2`), met by the Conductor, which is
  Algorithm 7 (`algorithm:conductor`);
  Module 3 (`mod:mvba`), met by the supplement's MVBA;
  Module 4 (`mod:acs`), the ACS;
  Algorithm 5 (`alg:fallback`), the receipt layer's rules.

The facts come from [Cadence.lean](../../Cadence.lean),
[Interfaces.lean](../../Cadence/Interfaces.lean),
[CompositionContracts.md](../CompositionContracts.md) §3–§7,
[Premises.md](../Premises.md) §0 and
[Architecture.md](../Architecture.md) §2. When a declaration they name is
renamed, the diagram changes with it.

## Conventions

* **One file per diagram, written by hand.** No editor output, no embedded
  images; text is SVG text, so it stays searchable and sharp.
* **The page's palette.** The colours are those of the guide's
  [theme.css](../guide/theme.css): body text, the code-constant blue for
  declaration names, the link blue for claims and kernel-checked steps, and
  the keyword purple for what is assumed or judged by a human. Fonts are
  the page's stacks: the text stack for prose, the monospace stack for
  declarations. A diagram is 760 units wide, the guide's column width, and
  scales down with it.
* **A style means the same in every diagram.** Blue is a claim or a
  kernel-checked result; dashed purple is an assumed module, a trusted
  tool, or a judgement only a human makes; dotted is a consistency witness,
  or (in [chorus-slot.svg](chorus-slot.svg)) a step summarised in words;
  grey is everything else: models, pipeline steps, actions.
* **Light by default, dark for GitHub.** The light rules come first; the
  dark ones sit in exactly one `@media (prefers-color-scheme: dark)` block,
  which the guide drops when it inlines a file, because the site is
  light-only.
* **Every class starts with `dg-`**, and every file carries the same
  `<style>` block, so several diagrams inlined on one page agree with each
  other and leave the page's own styles alone. An `id` starts with the
  file's own prefix (`dg-mc-`, `dg-cpw-`, `dg-mt-`, `dg-cs-`), so ids stay
  unique on a page.
* **A `<title>` and a `<desc>`** in every file: the title is the diagram's
  name, the description says in prose everything the diagram shows, for a
  screen reader and for GitHub's image text.
