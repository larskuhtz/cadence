import Cadence.Mvba.Rank
import Cadence.Mvba.Compose
import Cadence.Fairness

/-! # Mvba.Liveness — the run-level target, and the assumptions it rests on

[`docs/MvbaPlan.md`](../../docs/MvbaPlan.md) §3.4 and §3.5 step 4. This file
**states** the bound-erased termination claim and every premise it takes. It
does not prove it: `TerminationClaim` below is a `Prop`-valued *definition*,
so the file is green without a `sorry` and the target is citable, greppable
and type-checked from the day it is written rather than existing as prose.

Everything a human has to believe is therefore a named `Prop` in this file,
each with a docstring and each appearing as an explicit hypothesis of the
claim — never a side condition discovered by reading a proof.
`grep -n '^def [A-Z]' Cadence/Mvba/Liveness.lean` prints the whole list: the
four label classes, the six premises, the target and the claim, and nothing
else.

## The fairness classification, and a correction to §3.2

`MvbaPlan.md` §3.2 fixed **two** scheduling classes: unfair for the `byz_*`
family (F-byz), weakly fair for the honest actions (F-justice). Writing the
run-level statement down shows that two is not enough, and that the natural
reading of the pair is **inconsistent**.

`timeout_qc` and `timeout_noqc` are honest actions, so §3.2 puts them under
(F-justice). But the model abstracts the *timing* of a timeout away (§3.6:
"`timeout i v` is enabled, not timed"), so in the current view a correct
validator holding a lock has `timeout_qc` **continuously enabled**. Weak
fairness then forces it to fire — in every view, including the good one —
and the obvious form of (A-viewsync), "no correct validator times out in the
good view", contradicts it outright. A contradictory premise set does not
make a theorem hard to prove; it makes it vacuous, which is the one outcome
worth engineering against.

So the timers are their **own class**, and the timing assumption is split
into the two halves it always had:

| class | labels | what is assumed |
|---|---|---|
| unfair | `ByzLabel` | nothing — (F-byz) |
| weakly fair | `JusticeLabel` | (F-justice) |
| timer | `TimerLabel` | (F-timeout) *and* (A-viewsync) |
| input | `Label.isInput` | nothing here — a premise of the claim, not fairness |

(F-timeout) is "the timeout is finite": a correct validator that has not
decided eventually times out of every view it enters, which is what closes a
view a faulty leader has stalled. (A-viewsync) is "the timeout is long
enough": in the good view no correct validator times out *before it has
decided*. Stated that way the two are compatible — a validator may time out
of the good view, just not before deciding, and `decide`'s own guard
(`∀ E, ¬ decided i E`) is what makes that a stable situation rather than a
race. Together they are the untimed content of the supplement's
"the view timeout exceeds `Δ_R + 3Δ + max(Δ, Δ_sync)`".

The inputs `propose` and `abandon` are the *caller's*, not the scheduler's
(`Mvba/Compose.lean`'s `Label.isInput`), so no fairness is assumed of them.
That every correct validator proposes is `AllPropose`, a premise of the
claim exactly as it is in `thm:termination` ("once every correct validator
has invoked propose").

## What the claim does not mention

`ByzNodeSetEnum` and `ByzNodeSetHonestQuorum` are absent from the statement
and will appear as hypotheses of the eventual *theorem*. That split is the
point: enumerability and a constructive quorum of correct validators are
what a **proof** needs to assemble certificates
([`ByzQuorum.lean`](../ByzQuorum.lean)), not part of what is being claimed.

## Open: non-vacuity of the premise set

The classification above removes the one contradiction found so far, but
"these six premises are jointly satisfiable" is not yet proven. It needs a
run exhibited, which is step 4's work and beyond it; the model's `sat trace`
blocks witness the protocol half (a decision is reachable) and no more.
Until then the premise set is checked for consistency by argument, not by
machine, and this paragraph is the record of that. -/

namespace Mvba

open Cadence

/-! ## The four label classes

Each is a `match` listing its actions by name, so the classification is
checkable by reading twenty-four lines rather than by trusting a sentence.
Adding an action to the model and forgetting it here is a non-exhaustive
match — an error, not a silent misclassification.

This section carries **no** instances: a label is a syntactic object, and
classifying it needs neither the quorum interface nor the view order. -/

section Labels

variable {node nodeset value view : Type}

/-- **(F-byz).** The labels the adversary controls. No definition in this
file requires anything of them, which *is* the assumption: progress never
relies on adversarial help. `not_justice_of_byz` pins the disjointness. -/
def ByzLabel : Mvba.Label node nodeset value view → Prop
  | .byz_preprepare .. => True
  | .byz_prepare .. => True
  | .byz_commit .. => True
  | .byz_timeout_qc .. => True
  | .byz_timeout_noqc .. => True
  | _ => False

/-- The two timer labels. They are honest actions, but the model abstracts
away *when* they fire, so they carry no weak-fairness hypothesis and are
governed by (F-timeout) and (A-viewsync) instead — the header says why weak
fairness on them would make the claim vacuous. -/
def TimerLabel : Mvba.Label node nodeset value view → Prop
  | .timeout_qc .. => True
  | .timeout_noqc .. => True
  | _ => False

/-- The labels (F-justice) covers: the honest message handlers, the
certificate assemblies, the view changes and the environment's availability
action — everything that is neither the adversary's, nor a timer, nor the
caller's input. -/
def JusticeLabel (l : Mvba.Label node nodeset value view) : Prop :=
  ¬ ByzLabel l ∧ ¬ TimerLabel l ∧ ¬ Label.isInput l

/-- **(F-byz), machine-checked at the only level it can be**: no label the
adversary controls is subject to a fairness hypothesis. -/
theorem not_justice_of_byz (l : Mvba.Label node nodeset value view)
    (h : ByzLabel l) : ¬ JusticeLabel l := fun hj => hj.1 h

/-- Likewise for the timers: (F-justice) does not reach them. -/
theorem not_justice_of_timer (l : Mvba.Label node nodeset value view)
    (h : TimerLabel l) : ¬ JusticeLabel l := fun hj => hj.2.1 h

/-- And the caller's inputs are not scheduled here either. -/
theorem not_justice_of_input (l : Mvba.Label node nodeset value view)
    (h : Label.isInput l) : ¬ JusticeLabel l := fun hj => hj.2.2 h

/-- The classification is exhaustive: every label is scheduled by exactly one
of the four disciplines. Proven by cases over the model's own label type, so
it cannot drift from the action list. -/
theorem label_classified (l : Mvba.Label node nodeset value view) :
    JusticeLabel l ∨ ByzLabel l ∨ TimerLabel l ∨ Label.isInput l := by
  cases l <;> simp [JusticeLabel, ByzLabel, TimerLabel, Label.isInput]

end Labels

/-! ## The premises, one named `Prop` each

From here on the full instance set is in scope: the premises talk about
states, and a state's type is the model's. -/

section Runs

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}

/-- A labelled run of the MVBA: the object every premise below is about. -/
abbrev MvbaRun (th : Theory node nodeset value view) :=
  LRun (Mvba.relationalTransitionSystem node nodeset value view) th

/-- **(F-justice)** — weak fairness of every honest, non-timer, non-input
action. The one scheduling assumption of the ordinary kind. -/
def FJustice (r : MvbaRun th) : Prop :=
  ∀ l, JusticeLabel l → WeaklyFair r l

/-- **(F-timeout)** — *the timeout is finite.* A correct validator that never
decides eventually times out of every view it enters. This is what closes a
view whose leader is faulty or silent, and so what lets the view counter
advance at all; without it a run may stall in view 1 forever. -/
def FTimeout (r : MvbaRun th) : Prop :=
  ∀ (i : node) (V : view) (n : Nat), ¬ nset.is_byz i = true →
    (r.at' n).entered i V = true →
    (∀ m E, ¬ (r.at' m).decided i E = true) →
      ∃ m, (r.at' m).timed_out i V = true

/-- **(A-viewsync)** — *the timeout is long enough.* There is an honest-led
view that every correct validator enters, and in which no correct validator
times out before it has decided.

This is the untimed stand-in for `thm:termination`'s after-GST Δ-synchrony
together with its view-timeout bound. The "before it has decided" is
load-bearing and is the correction §3.2 needed: the flat form ("no correct
validator times out in the good view") contradicts weak fairness of
`timeout_qc`, and the claim would hold vacuously. -/
def AViewSync (r : MvbaRun th) : Prop :=
  ∃ (W : view) (L : node),
    th.leader W L = true ∧ ¬ nset.is_byz L = true ∧
    (∀ i, ¬ nset.is_byz i = true → ∃ n, (r.at' n).entered i W = true) ∧
    (∀ i n, ¬ nset.is_byz i = true → (r.at' n).timed_out i W = true →
      ∃ E, (r.at' n).decided i E = true)

/-- **(F-avail)** — the availability shares arrive. A correct validator that
accepted a vector eventually has `avail_ready` for it, which is
`send_commit`'s environment precondition. The supplement's `Δ_sync`
(`lem:avail-progress`), with the bound erased. -/
def FAvail (r : MvbaRun th) : Prop :=
  ∀ (i : node) (n : Nat) (V : view) (E : value), ¬ nset.is_byz i = true →
    (r.at' n).accepted i V E = true → ∃ m, (r.at' m).avail_ready i E = true

/-- **The caller's premise**, not a fairness assumption: every correct
validator invokes `propose`. `thm:termination` says "once every correct
validator has invoked propose", and this is that. -/
def AllPropose (r : MvbaRun th) : Prop :=
  ∀ i, ¬ nset.is_byz i = true → ∃ (n : Nat) (E : value), (r.at' n).input i E = true

/-- **The caller's second premise**: no correct validator is abandoned before
it decides. `thm:termination`'s "if no correct validator is externally
abandoned before deciding"; `abandon` is a contract *input*, so this is a
condition on the consumer, not on the scheduler. -/
def NoEarlyAbandon (r : MvbaRun th) : Prop :=
  ∀ (i : node) (n : Nat), ¬ nset.is_byz i = true →
    (r.at' n).abandoned i = true → ∃ E, (r.at' n).decided i E = true

/-! ## The target -/

/-- **Bound-erased termination**: every correct validator decides. The
`O(fΔ)`-free skeleton of `thm:termination`, and the untimed sibling of
`MVBATemporal.termination` (`Cadence/Interfaces.lean`), whose timed form
this development still has no instance of. -/
def Terminates (r : MvbaRun th) : Prop :=
  ∀ i, ¬ nset.is_byz i = true → ∃ (n : Nat) (E : value), (r.at' n).decided i E = true

/-- **The step-4 target, stated.** Not a theorem and not asserted anywhere:
this is the `Prop` that §3.5 step 4 has to prove, written down so that its
premises are fixed, type-checked and citable before the proof exists.

The six premises are exactly the file's named definitions, in the order the
header's table lists them. What is deliberately *absent* is any quorum
machinery: `ByzNodeSetEnum` and `ByzNodeSetHonestQuorum` are what a proof
needs, not part of the claim. -/
def TerminationClaim (th : Theory node nodeset value view) : Prop :=
  ∀ r : MvbaRun th,
    FJustice r → FTimeout r → AViewSync r → FAvail r →
    AllPropose r → NoEarlyAbandon r →
      Terminates r

/-- A decided validator stays decided, so `Terminates` is equivalent to the
`Eventually` form of the run vocabulary — the shape a future
`response [termination] … ↝ …` would generate. -/
theorem terminates_iff_eventually (r : MvbaRun th) :
    Terminates r ↔ ∀ i, ¬ nset.is_byz i = true →
      r.Eventually (fun st => ∃ E, st.decided i E = true) := by
  constructor
  · rintro h i hi
    obtain ⟨n, E, hE⟩ := h i hi
    exact ⟨n, E, hE⟩
  · rintro h i hi
    obtain ⟨n, E, hE⟩ := h i hi
    exact ⟨n, E, hE⟩

end Runs

end Mvba

/-! ## The pinned trust base

Definitions and four facts about the label classification; the target itself
is a definition, so nothing here asserts termination. -/

/-- info: 'Mvba.label_classified' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Mvba.label_classified

/-- info: 'Mvba.not_justice_of_byz' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Mvba.not_justice_of_byz

/--
info: 'Mvba.terminates_iff_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.terminates_iff_eventually
