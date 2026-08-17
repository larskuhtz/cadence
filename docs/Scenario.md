# The scenario this project is built for

*Why the repository is arranged the way it is: who edits what, who maintains
the proofs, and what an auditor is being asked to trust. This is a statement of
intent and of the target workflow — some of it is realised today (the model /
proof-file split, the machine-derived audit pins), some is the direction of
travel. For what is actually proven, read [`../README.md`](../README.md).*

## TL;DR

1. Model and top level properties must be human comprehensible and editable.
2. After the initial setup, users are more likely to change the model than the properties.
3. Proofs are created and maintained by AI agents behind the scenes.
4. Properties are Lean theorems. Users trust the work of the AI agent, because
   they trust the Lean kernel.
5. The workflow and proof system scales to large models.

## Scenario

The most common usage scenario is the following:

Human users care about
1. the model and
2. the top level properties.

This is what a human user will edit, read, and reason about. When they see a
theorem in the Lean code, they expect that it holds unconditionally subject to
the soundness of the Lean kernel, the axioms the theorem uses, and nothing
else.

Typically, while working on a project, human users will make changes to the
model. Properties can be expected to be relatively stable once they got
established.

Proof creation and maintenance is typically delegated to AI agents, which are
more efficient for these tasks.

Users expect fast feedback for the part of the protocol that they are working
on. Mechanical propagation of those changes throughout the overall system can
happen asynchronously and usually is not on the critical path of the user
experience. This is supported by the fact that AI agents typically can identify
reliably which parts of the system are affected by a change and what work can
be considered mechanical.

## Workflow

A common workflow is as follows:

1. Initial setup:
    1. The human user provides the basic protocol. Examples for how this can
       be done include referencing a description in a paper, providing a
       prototype or pseudo code, pointing at some production implementation,
       or creating a first (possibly simplified) model manually.

       The human user also provides the properties of the model in some formal
       or informal way.
    2. An AI agent takes the basic model and turns it into a concrete formal
       Lean model.

       The AI agent also provides a formal version of the properties as Lean
       theorems that matches the formal model.
    3. The human user and the AI agent collaborate on iteratively refining the
       model and the properties.
    4. The AI agent creates proofs for the properties and maintains them as the
       model evolves.

2. Ongoing maintenance:
    1. The human user makes changes to the model (possibly in collaboration
       with the AI agent).
    2. The AI agent updates the properties as needed to align with the changes.
    3. The AI agent re-creates the proofs and provides prompt feedback whether
       the properties still hold or not.
    4. Based on the feedback the human user continues to adjust the model
       (looping back to step 1).
    5. In the background, the AI agent propagates the changes throughout the
       overall system updating all proofs as needed, and providing feedback in
       case there are unforeseen issues.

3. Audit:
   1. Auditors need to read only
       - concise top-level documentation (`README.md`, `docs/Architecture.md`,
         or anything else that helps understand the model and properties) —
         including the inventory of meta-assumptions that live outside Lean
         (modelling contracts, fairness axioms),
       - the model and the properties in Lean code, and
       - the theorem statements in the Lean code.
   2. A theorem *is* the Lean expression of a property. Properties are
      declared exactly once (as constants/defs) in the declaration files; a
      theorem states a property by importing and referencing that
      declaration — its body is that precise term. There is no
      copy-and-pasting and no correspondence check by any tool other than
      Lean itself: auditors verify that the declared property says what they
      mean, and the kernel checks the rest.
   3. Completeness is obtained by internalization, not by tooling: the top
      level property is one declared proposition (e.g. `model ⊨ properties`),
      so a single theorem stating it forces every lower-level obligation to
      exist — a missing case is a type error, not a silent gap. The same
      argument applies one level down (e.g. one theorem per invariant):
      auditors never need to inspect the lower-level proof mechanics to
      understand or trust the statement of a theorem. They do need to
      confirm the theorem's file is part of the build.
   4. Auditors do not need to read the proofs: a theorem holds when the Lean
      kernel type-checks it — relative to the axioms it uses. The axiom set is
      therefore part of the audit surface and should be pinned mechanically
      (e.g. a build-failing audit command that reports, per property, its
      proof status and exact axioms).

One important thing to notice is that the loop in 2.1 -> 2.4 is the critical
path for protocol development. This is where the user experiments with new
ideas, features, and optimizations. The proof system should be optimized for
providing prompt and accurate feedback in this loop by automating this step as
much as possible, deferring tasks that are not relevant for the iteration to
the background. During this loop it is much more likely that the user changes
the protocol behavior than the properties. Hence, the proof system should be
optimized for this scenario.

## Scaling

### Modular Reasoning

In order for the system to be scalable, modular reasoning should be supported
when monolithic proofs are expensive or not feasible. A common approach is to
abstract/axiomatize sub-protocols and primitives via type classes and to prove
instances of these classes separately. Components can then establish theorems
relative to these abstractions. Top level properties are established by
composing theorems about concrete instantiations of all components.

### Asynchronous Proofs

For models with very large monolithic components that cannot be abstracted into
sub-protocols it is acceptable to separate the declaration of the model and the
properties from the theorems and the proofs:

* Declaration Files:
    - Model code
    - Property statements (e.g. as constants/defs, not theorems)
* Proof Files:
    - Theorems, stating the declared properties by reference — their bodies
      *are* the imported statements
    - Proofs

The Proof files depend on the declaration files but not the other way around.

Building the declaration files only validates the coherence of the model and
the property statements.

Building the proof files establishes the properties as theorems.

The same discipline applies to mechanically generated obligations: generated
proof obligations (e.g. per-action verification conditions) are emitted as
named declarations in the declaration files and referenced by the proof files
the same way — identity by reference, checked by Lean, at every level.

This supports a workflow where a human user can edit declaration files with the
support of a language server without having to wait for proofs being
re-established on each edit. Re-establishing proofs on large models can be very
costly both in terms of time and memory consumption. Proof creation is only
triggered when the user explicitly opens and/or builds a file that states the
respective theorem.
