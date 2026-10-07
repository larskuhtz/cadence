/-
Chapter 8 of the guide: Open issues and further work.
-/
import CadenceGuide.Elements

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "Open issues and further work" =>
%%%
file := "open-issues"
%%%

_What is open, and what is planned._

Everything this development claims is proven and axiom-pinned, and the
premises of every claim are shown to hold together in one model. The open
items are places where the development could go further. Their one home is
[TODO.md](../../../TODO.md); this chapter summarises them by kind, and the
list there is the current one.

# Open issues

*The paper.* The review of the paper produced findings for its authors,
grouped and listed in [PaperAlignment.md](../../../PaperAlignment.md) §6;
sending them is open, and each stays open on the paper side until the authors
resolve it. Two further items keep the development tied to the paper: a
re-check at each new paper commit, by the procedure of
[PaperAlignment.md](../../../PaperAlignment.md) §1, before that commit can
become the target; and, once it stabilises, a check that the supplement's
practical Conductor behaves as the verified Conductor's contract allows.

*Soundness instruments.* Checks a human makes today that a machine could
make:

* the monotone-network discipline: that a model reads network relations only
  positively is audited by hand, and a violation would not fail the build; a
  meta-program classifying every read would make it a machine check;
* a model of the threshold-encryption class, the one primitive class without
  an instance, to show its assumptions are consistent;
* a Chorus run through the MVBA path, so the certificate bridge between Chorus
  and the MVBA is shown satisfiable at the composed instance;
* an in-build reachability trace for Chorus, which today the monitor's fixture
  stands in for.

[ChorusDesign.md](../../../ChorusDesign.md) §9 keeps the list specific to
Chorus.

# The external audit

An external audit of the development, created by
[Aristotle (Harmonic)](https://aristotle.harmonic.fun), checked three
questions: whether the model implements the protocol faithfully, whether the
paper's claims are covered, and whether the proofs and the documented
arguments are sound. It audited revision `bfeee8c` of this repository in
August 2026, against version 2 of the paper on arXiv. The report is frozen at that revision; notes under its
findings record what has been closed since, and by which commit:
[AuditReport.md](../../../AuditReport.md).

# History

How the verification reached its current state, build by build, with the
decisions and the failures that shaped it, is
[History.md](../../../History.md). It is a ledger of past states: for the
current state, read this guide.

# Further work

[TODO.md](../../../TODO.md) lists the directions it would be worth taking,
each with the reason:

* *in the Veil tool*: liveness checked inside the models, as safety is, and
  the cause of a solver divergence seen with withheld contract fields;
* *in the monitor*: an MVBA leg, so fallback-path traces can be checked, and
  wider trace coverage;
* *in scope*: Chorus over many slots, epochs with rotating proposers, and a
  latency bound through the commit-certificate route;
* *in the models' hygiene*: candidates for merging actions, clearer names, and
  consistent formatting.
