/-
The guide to the Cadence verification: the front page, and the chapters in
reading order.

A Verso document, and so a Lean program. It carries no facts of its own:

* every statement is the real declaration, embedded from the compiled
  development (`{claim}`), and every Veil model declaration is quoted from the
  rendered sources (`{model}`) — so a renamed or removed declaration fails
  this build rather than leaving a stale quotation;
* every status box, checklist and table is computed when the guide is built
  ([Elements.lean](CadenceGuide/Elements.lean) lists the elements): the
  kernel's axiom footprint, the module contracts a result is conditional on,
  and which declarations discharge them.

The one kind of hand-written code is an *outline*, marked as such and always
followed by the real declaration.

Each chapter is a file of its own under [Chapters](CadenceGuide/Chapters) and
a page of its own on the site, so the chapters can be written independently.
This file holds the front page and the order of the chapters.
-/
import CadenceGuide.Elements
import CadenceGuide.Chapters.Approach
import CadenceGuide.Chapters.Claims
import CadenceGuide.Chapters.ReadingModel
import CadenceGuide.Chapters.ModelIdioms
import CadenceGuide.Chapters.Contracts
import CadenceGuide.Chapters.Components
import CadenceGuide.Chapters.Checking
import CadenceGuide.Chapters.OpenIssues
import CadenceGuide.Chapters.EarlierWalkthrough
import CadenceGuide.Chapters.Specimen

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "Cadence Verification" =>

%%%
shortTitle := "Cadence Verification"
%%%

_What is proven about the Cadence protocol, and what it rests on._

{include 1 CadenceGuide.Chapters.Approach}

{include 1 CadenceGuide.Chapters.Claims}

{include 1 CadenceGuide.Chapters.ReadingModel}

{include 1 CadenceGuide.Chapters.ModelIdioms}

{include 1 CadenceGuide.Chapters.Contracts}

{include 1 CadenceGuide.Chapters.Components}

{include 1 CadenceGuide.Chapters.Checking}

{include 1 CadenceGuide.Chapters.OpenIssues}

{include 1 CadenceGuide.Chapters.EarlierWalkthrough}

{include 1 CadenceGuide.Chapters.Specimen}
