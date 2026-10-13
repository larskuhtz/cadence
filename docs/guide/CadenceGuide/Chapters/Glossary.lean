/-
Chapter 9 of the guide: Terms and codes.

One sentence per term, and a key to the codes the guide and the documents
use. The chapters link here at a term's first use.
-/
import CadenceGuide.Elements
import CadenceGuide.ChapterList

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "Terms and codes" =>
%%%
file := "terms"
%%%

_One sentence per term the guide uses, and a key to the codes in it and in the documents; read on demand._

# Tools and proofs

: Veil

  A language for writing a distributed protocol as a state machine inside
  the Lean proof assistant. It turns each model into the conditions that
  prove its properties, and proves them.

: Kernel

  The small type checker at the core of Lean that accepts or rejects every
  proof. It is the part of Lean an auditor trusts.

: Pin

  A build check that fails unless a command prints exactly the recorded
  text: the axioms a theorem rests on (`#print axioms`), or the proof status
  of every condition of a model (`#veil_status`).

: Verification condition (VC)

  One proof obligation Veil states for a model: the initial state satisfies
  a property, or one action preserves it.

: Frame obligation

  A verification condition whose action writes nothing the property reads.
  Veil closes it with a short proof and no solver.

: Witness

  A concrete model and run in which all of a claim's premises hold at once,
  which shows that the premises are consistent.

# Models

: Reachable state

  A state that some run of the model reaches from an initial state.

: Inductive invariant

  A property that holds in the initial states and that every action
  preserves, so it holds in every reachable state.

: Admissible run

  A run that meets a module's scheduling and timing premises. Each contract
  instance defines its own `Admissible`, and its timed properties hold in
  those runs.

: Positive position

  A read of the network that can require a message to exist, never that one
  is absent. Correct validators read other validators' messages only this
  way ({chapter ModelIdioms}[chapter 4]).

# Contracts

: Class, instance, contract

  A class is a Lean list of operations and properties over an abstract type,
  and an instance is a value that provides all of them, with their proofs.
  A contract is a class that states one of the paper's modules
  ({chapter Contracts}[chapter 5]).

# Chorus and the MVBA

: FastQC

  A supermajority, `2f + 1`, of matching vote signatures on one proposer's
  entry: the fast path's certificate.

: FallbackQC

  `f + 1` matching fallback signatures on one proposer's entry: the fallback
  path's certificate for that entry.

: CommitQC

  A supermajority of matching commit votes: the certificate on which a
  validator finalizes. The fast path, the fallback path and the MVBA each
  produce one.

: Meta-block

  The value the MVBA agrees on: for each proposer, a root or no entry,
  each with the certificate that backs it.

: Entry vector

  A meta-block with its certificates dropped: for each proposer, a root or
  no entry. The MVBA's agreement is over entry vectors.

# Codes

: P1, P2, …

  A finding for the paper's authors. Each is listed in
  {chapter Claims}[chapter 2], and stated with the paper's text in
  [PaperAlignment.md](../../../PaperAlignment.md#6-findings-for-the-papers-authors) §6.

: Premise tags

  A tag in parentheses names a premise of a timed or untimed claim:
  (F-…) a fairness premise, such as (F-justice); (Δδ-justice) and
  (Δ-justice) the timing bounds on owed steps; (P-phase), (P-open) and
  (T-timer) timers that fire on time; (P-incl) the inclusive deadline;
  (A-…) a named assumption, such as (A-leader-rotation-k). C1 and C2 are
  Chorus's two conditions on its caller. Each is defined in
  [Premises.md](../../../Premises.md).

: R1–R6, W1–W3, B1–B4

  The locality rules of [Locality.md](../../../Locality.md): what a correct
  validator may read (R) and write (W), and what a Byzantine validator must
  not do (B). {chapter ModelIdioms}[Chapter 4] explains them.

: The V line and the A line

  Two lines of further work. The V line builds a checker that applies the
  locality rules to every action; the A line builds a reference ACS from
  the MVBA ({chapter OpenIssues}[chapter 8]).
