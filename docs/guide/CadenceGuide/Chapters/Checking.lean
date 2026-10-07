/-
Chapter 7 of the guide: How the proofs are checked.
-/
import CadenceGuide.Elements
import CadenceGuide.ChapterList
import CadenceGuide.Pin

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "How the proofs are checked" =>
%%%
file := "checking"
%%%

_What the machine checks and how, what is trusted, and how to re-check it yourself._

A theorem in Lean holds once Lean's kernel, a small type checker, accepts its
proof, relative to the axioms the proof uses. Everything this development
proves reaches the kernel in that form, including what an SMT solver found.
This chapter follows a property from the model it is stated in to the pinned
theorem, says what is trusted along the way, and ends with the commands that
re-run the checks.

Building the project is the check. A Veil model is a Lean file, and
elaborating it runs its verification; `lake build` elaborates every file, and
any failed step fails the build.

# From model to pinned theorem

{figure "docs/diagrams/model-to-theorem.svg" (caption := "From model to pinned theorem: the pipeline for Chorus, with what is trusted at each step.")}

The steps, for the three large models (Chorus, the MVBA and the receipt
layer):

1. *The model* declares the state, the actions, and the properties: the
   safety properties the paper claims and the invariants that make them
   provable by induction.
2. *The verification conditions.* Veil turns the model into a transition
   system and states one condition per action and property: if every
   invariant holds and the action fires, the property still holds. It also
   states one for the initial state, and one per action saying that the
   action does not fail. The statements are persisted with the model, as its
   VC registry.
3. *The proof files*, one per action, prove that action's conditions. Each
   condition's statement is read from the registry, never written out by
   hand, so a proof cannot be a proof of something else.
4. *The composition* is an induction over the actions: every reachable state
   satisfies every invariant. It ends in a named theorem per property, such
   as `Mvba.reachable_agreement`, and in the status pin of the next sections.
5. *The contract instances and the theorems over runs* are plain Lean: the
   instances are built from the reachable-state theorems, and the liveness and
   timing claims are proven over runs of the generated transition system, with
   their premises as hypotheses.
6. *The axiom pins* check that every end result depends on Lean's three
   standard axioms and nothing else.

The two small models, the glue and the Conductor, prove all their conditions
in the model file itself and persist the proofs as theorems there; the
induction over them is in [Composition.lean](../../../../Cadence/Composition.lean).
The large models split the proofs over one file per action because a
module's proofs otherwise have to be held in one process, which does not fit
in memory at Chorus's size.

The commands that do this work, as they appear in the files:

:::table +header
*
  * Command
  * Where
  * What it does
*
  * `#gen_spec`
  * the model
  * builds the transition system and states the verification conditions
*
  * `#prove_action M a`
  * a proof file per action
  * proves every condition of action `a` of model `M`, and persists the proofs
*
  * `#prove_vc M a p by …`
  * a proof file
  * a hand-written tactic for one condition, whose statement still comes from the registry
*
  * `#check_invariants`, `#gen_theorems`
  * the two small models
  * prove every condition in the file, and persist the proofs as theorems
*
  * `#gen_composition M`
  * a `Certify.lean`, or `Composition.lean`
  * the induction: `M.invariants_of_reachable`, and one theorem per property
*
  * `#veil_status M`
  * a `Certify.lean`
  * checks that every registered condition has a real proof of exactly its statement
*
  * `#guard_msgs in #print axioms X`
  * [Cadence.lean](../../../../Cadence.lean), and at each result
  * fails the build unless `X` depends on exactly the expected axioms
*
  * `#model_check`
  * the mutation test, the receipt layer
  * explores a small concrete instance exhaustively
:::

# Solver discharge and kernel reconstruction

Most conditions are frame obligations: the action writes nothing the property
reads. Veil closes those with a short Lean proof and no solver. The others go
to the SMT solver cvc5.

Every model elaborates with `veil.smt.trust false`. With that setting a
solver verdict is not accepted as a proof: cvc5 produces a proof certificate,
Veil's solver bridge rebuilds it as a Lean proof term, and the kernel checks
that term like any other. A condition whose proof cannot be rebuilt fails the
build. So cvc5 is a search procedure here: it finds proofs, and the kernel
decides whether they are proofs.

A few conditions are beyond the solver's search, typically ones that need a
quorum-intersection argument the solver does not find. Those carry a
hand-written tactic in the action's proof file. Their statement comes from
the registry like every other, and the kernel checks the result like every
other. The per-model counts are in [Architecture.md](../../../Architecture.md) §2.

Two tools stay trusted. Lean's kernel checks every proof. Veil's translation
of a model into its transition system and verification conditions is trusted:
whether those conditions say what the model means is a property of the tool,
not of any one proof. [Architecture.md](../../../Architecture.md) §4 item 7
states this, and [Dependencies.md](../../../Dependencies.md) § "Trusted
computing base" says what is inside that surface.

# The axiom pins and the status pins

*Axiom pins.* Lean can list every axiom a proof depends on, by walking the
proof term. A pin wraps that listing in `#guard_msgs`, which fails the build
unless the output is exactly the expected text. Every end result is pinned in
the audit root, [Cadence.lean](../../../../Cadence.lean), at Lean's three
standard axioms; one of them:

{pin "Cadence.lean" "#print axioms Cadence.system_positional_log_safety"}

An unfinished proof (`sorry`) shows up as the extra axiom `sorryAx`, and a
project-specific axiom shows up under its own name, so either fails the pin.
The guide repeats the check: every result embedded on these pages carries a status box computed while the guide builds, and the guide's
build fails on any axiom beyond the three. The site's
[trust boundary](../trust-boundary.html) page lists the axiom footprint of
every end result at once, derived from the compiled development.

*Status pins.* An axiom pin says a proof is complete. It does not say that
every condition the model states has one. `#veil_status` checks that: it walks
the model's registry and reports, per condition, whether a theorem with
exactly that statement is in scope and checked, and over which axioms. Its
output is pinned for each of the three large models:

{pin "Cadence/Chorus/Certify.lean" "#veil_status Chorus"}

{pin "Cadence/Mvba/Certify.lean" "#veil_status Mvba"}

{pin "Cadence/FallbackReceipt/Certify.lean" "#veil_status FallbackReceipt"}

"Real" means a kernel-checked theorem of the registered statement, so a pin at
every condition real is the claim "nothing is stubbed", as a build check.
Adding a property to a model changes its number of conditions, and the pin
fails until it is updated.

*What the pins do not say.* They say the proofs are complete and rest on
Lean's axioms. Whether the statements are the right ones, that the model is
the paper's protocol and its premises are plausible, is the reader's part:
{chapter Claims}[chapter 2], {chapter ModelIdioms}[chapter 4] and
{chapter Contracts}[chapter 5].

# The proof cache

Solving the conditions is the slow part of a build, so Veil keeps a proof
cache, keyed by each condition's statement, that stores the proof terms the
solver path produced. On a hit, the stored proof term is checked by the kernel
against the current condition before anything uses it. The cache saves the
search, not the check.

Two consequences matter for a reader of the evidence:

* A hit does not re-run a hand-written tactic, because it replays the proof
  the tactic once produced. A changed tactic is tested only by solving its
  condition without the cache. The image CI verifies against ships no cache,
  so a commit that touches a model or a proof file solves the affected
  conditions from scratch.
* The kernel check of a hit happens when the module is built. Whoever
  receives the built files (`.olean`) did not see it; the audit ladder below
  closes that gap.

# The mutation test

A proof shows the invariants are true. The mutation test shows they are
needed. [NoLock.lean](../../../../Cadence/Mvba/NoLock.lean) takes the MVBA
model with one guard removed, the lock check of {cite}`line:mvba:pp-guard`,
and runs the model checker on it. The checker finds a reachable state in
which two correct validators decide different vectors, which is what the
lock check exists to prevent.

The check runs on a restriction of the mutant, with some steps bundled, a
fixed scheduler and fewer actions, built so that every run of the restriction
is a run of the mutant; a violation found there is a violation of the mutant.
The counterexample is pinned verbatim with `#guard_msgs`, so a green build
requires the violation: if a change repaired the mutant, the build would
fail. The file's header gives the argument for the restriction step by step.

# The monitor

The model-conformance monitor answers a different question: does a recorded
run of the Rust implementation behave as the Chorus model allows? It replays
the trace through the model's own action bodies, one step at a time, and
reports whether every step's guards held. It is a test oracle for the
implementation, and it is outside every theorem's trust base: no proof
depends on it.

Its accepted fixture also shows that the model's fast path reaches
finalization, so Chorus's safety properties are not true merely because
nothing is reachable. A mutation suite checks that corrupted traces are
rejected at the right guard. The monitor stands in for the MVBA with a stub
that never decides, so no fallback-path trace can be checked yet.
[Monitor.md](../../../Monitor.md) has the design, the scope and the commands.

# The documentation checks

The documentation is checked too, so that what it says about the development
cannot silently drift:

* *Links.* Every relative link in the sources, the documents and this guide
  is resolved against the repository, and a link to a file that does not
  exist fails the check ([site-links.sh](../../../../scripts/site-links.sh)).
  The site build also checks every link into the rendered sources.
* *Paper citations.* Every citation names a label of the paper's target
  revision and the reference the rendered PDF shows for it; a label not in
  the label map, or a reference that is not the map's, fails the check
  ([paper-cites.sh](../../../../scripts/paper-cites.sh)).
* *The guide's elements.* This guide states no fact of its own: each
  statement, quotation, status box, diagram name and table is read from the
  compiled development or a checked file while the guide builds, and fails
  the build when it is stale. A renamed declaration, a vanished model
  property, an axiom beyond the three, or an audit table that no longer
  matches its model's actions each stop it.
  [Documentation.md](../../../Documentation.md) § "The guide" lists each
  element and when it fails.
* *The trust boundary page* is generated from the compiled development, and
  the site build fails if any end result's axiom footprint has drifted.

# Continuous integration

Three workflows run on GitHub:

* *verify*, on every pull request and every push to the default branch. Two jobs in parallel. The
  first re-verifies the sources against the published `verified` image,
  re-elaborating every module whose source changed, then runs the monitor's
  suites; it fails on any failed, crashed or timed-out condition and on any
  `sorry`. The second replays every proof stored in that image through the
  kernel. Together they cover every declaration the commit relies on: the
  unchanged modules by the replay, the changed ones by the re-elaboration.
* *publish-images*, on every push to the default branch. It builds the
  `verified` image by running the full verification inside it, so a published
  image is always one whose verification passed.
* *docs*, after the images are published. It renders the site from that
  image's build; the documentation checks above run as part of it. The site
  is documentation, not evidence: the gates are the two jobs of *verify*.

# Re-checking it yourself

The published images hold the toolchain, every dependency, and this project
already built and verified, so a reader can re-check the proofs without
building anything. [container.sh](../../../../scripts/container.sh) pulls an
image on first use; `RUNTIME` selects podman, docker or Apple's `container`:

```
RUNTIME=podman scripts/container.sh check    # every stored proof through the kernel
RUNTIME=podman scripts/container.sh verify   # the build files against these sources
```

What each establishes depends on one fact about Lean. Importing a built file
(`.olean`) does not re-check it: the declarations are loaded as they are.
Elaborating a module from source does check it. So a prebuilt image is
trusted until something re-checks it, and the audit ladder says what each
tier re-checks:

:::table +header
*
  * Tier
  * What you check
  * How
*
  * 0
  * nothing: you read the sources and trust the image
  * —
*
  * 1
  * every stored proof is well-typed, and every axiom footprint is as claimed
  * `scripts/container.sh check`: Lean's `leanchecker` replays every declaration through the kernel, with no solver and no elaboration
*
  * 2a
  * tier 1, and the image's built files correspond to these sources, by the build tool's source hashes
  * `scripts/container.sh verify`
*
  * 2b
  * as 2a, with the elaborator redoing the project from source rather than trusting the hashes
  * delete the project's built files in the `verified-cache` image, then re-verify
*
  * 3
  * as 2b, with no cached proof reused: every condition solved again by cvc5 and rebuilt for the kernel
  * as 2b, from the `verified` image, which ships no cache
:::

Tier 1 shows that the proofs in the image are complete and rest on the
claimed axioms. Only a rebuild, tier 2, shows they were produced from the
sources you are reading. Every tier also runs natively on Linux and macOS;
the container fixes the environment. [Container.md](../../../Container.md)
§3–§4 has the argument, the commands for each tier and the measured times.
