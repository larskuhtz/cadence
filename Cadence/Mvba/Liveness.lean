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
`timeout_qc`, and the claim would hold vacuously.

The entry clause is conditioned on the validator having *participated*. A
correct validator that never calls `propose` never enters any view, so
without that condition this premise would quietly entail `AllPropose`, and
two premises that look independent would not be. Each of the six is meant to
be readable on its own. -/
def AViewSync (r : MvbaRun th) : Prop :=
  ∃ (W : view) (L : node),
    th.leader W L = true ∧ ¬ nset.is_byz L = true ∧
    (∀ i, ¬ nset.is_byz i = true → (∃ (n : Nat) (E : value), (r.at' n).input i E = true) →
      ∃ n, (r.at' n).entered i W = true) ∧
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

/-! ## The last link of the chain

The first piece of the proof, and the one that fixes the shape of all the
others: **once a commit certificate exists, a correct participating
validator decides.** It reduces the whole claim to "a commit certificate
eventually exists", and it is where the three mechanics the rest will reuse
are worked out — how an action's enabledness is discharged from its guards,
how a firing's effect is read off, and how (F-justice) is consumed.

Nothing here needs an invariant. That is itself information for §3.5 step 3:
this link adds nothing to the sweep, and the cells will be bought by the
links that cannot say the same. -/

/-- Expose an action's transition body in `h` — `Mvba/Compose.lean`'s
`mvba_tr`, repeated here rather than exported because it is a two-line local
tactic and the two files have no other reason to depend on each other. -/
local macro "mvba_tr" h:ident : tactic =>
  `(tactic| (simp only [Mvba.relationalTransitionSystem, Mvba.Next, Mvba.NextAct] at $h:ident
             simp only [trSimp] at $h:ident))

/-- Turn an enabledness goal into the action's guards: the same unfolding as
`mvba_tr`, on the goal. What is left is `∃ st', <guards> ∧ <update> = st'`,
so the guards *are* enabledness and the post-state is determined. -/
local macro "mvba_enabled" : tactic =>
  `(tactic| simp only [Enabled, Mvba.relationalTransitionSystem, Mvba.Next,
      Mvba.NextAct, trSimp])

/-- Evaluate the field-representation `set`/`get` pair at the canonical
representation, to read a firing's effect off the post-state. -/
local macro "mvba_effect" : tactic =>
  `(tactic| simp +unfoldPartialApp [Veil.FieldRepresentation.set,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id])

variable {st st' : Mvba.State (Mvba.FieldAbstractType node nodeset value view)}

/-- **`decide`'s guards are its enabledness.** Stated in the plain accessor
spelling the rest of the development uses, so it composes with the generated
`<relation>.mono` lemmas without a translation step. -/
theorem enabled_decide {i : node} {v : view} {e : value}
    (hi : ¬ nset.is_byz i = true)
    (hin : ∃ E, st.input i E = true)
    (hab : ¬ st.abandoned i = true)
    (hqc : st.msg_commitqc v e = true)
    (hnd : ∀ E, ¬ st.decided i E = true) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.decide i v e) := by
  mvba_enabled
  exact ⟨_, hi, hin, hab, hqc, hnd, rfl⟩

/-- **`decide`'s effect.** A `decide i v e` step leaves `i` deciding `e`. -/
theorem decide_effect {i : node} {v : view} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.decide i v e) st') : st'.decided i e = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, rfl⟩ := htr
  mvba_effect

/-- **The last link.** A correct validator that has proposed, is never
abandoned before deciding, and for which *some* commit certificate exists at
*some* point, decides.

Only (F-justice) is used: no timer assumption, no view synchronisation, no
quorum machinery. `decide` accepts a certificate of any view, so the leader
schedule plays no part either — which is why this link is the one that can
be proven before the others exist. -/
theorem eventually_decided_of_commitqc
    (r : MvbaRun th) (hfj : FJustice r) (hna : NoEarlyAbandon r)
    {i : node} (hi : ¬ nset.is_byz i = true)
    {N : Nat} {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    {v : view} {e : value} (hqc : (r.at' N).msg_commitqc v e = true) :
    ∃ (n : Nat) (E : value), (r.at' n).decided i E = true := by
  by_contra hcon
  push Not at hcon
  -- `i` never decides — hence, by the caller's premise, is never abandoned.
  have hab : ∀ n, ¬ (r.at' n).abandoned i = true := by
    intro n habn
    obtain ⟨E, hE⟩ := hna i n hi habn
    exact hcon n E hE
  -- The input and the certificate persist, by the generated monotonicity.
  have hin' : ∀ n, N ≤ n → (r.at' n).input i E₀ = true :=
    r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin
  have hqc' : ∀ n, N ≤ n → (r.at' n).msg_commitqc v e = true :=
    r.mono (P := fun s => s.msg_commitqc v e = true)
      (fun m hm => Mvba.msg_commitqc.mono (r.steps m) v e hm) hqc
  -- So `decide i v e` is enabled from `N` on, and weak fairness fires it.
  obtain ⟨n, hn, hfire⟩ :=
    hfj (.decide i v e) (by simp [JusticeLabel, ByzLabel, TimerLabel, Label.isInput]) N
      (fun n hn => enabled_decide hi ⟨E₀, hin' n hn⟩ (hab n) (hqc' n hn) (fun E => hcon n E))
  exact hcon (n + 1) e (decide_effect (hfire ▸ r.steps n))

/-! ## The link before it, and the first use of the rank

`form_commitqc` is the assembly that produces the certificate the last link
consumes. Its guard is exactly the second summand of `Rank.lean`'s
`assemblyGap` reaching zero — so the two compose into a statement with no
mention of certificates at all: **if the commit dimension of the rank ever
bottoms out on a supermajority, every correct participating validator
decides.**

That is the rank being *used*, not merely defined, and it is the shape every
remaining link will have: a residual reaches zero, an assembly becomes
enabled, weak fairness fires it, and the next residual is one step closer.
Like the last link, neither of these needs an invariant. -/

/-- **`form_commitqc`'s guards are its enabledness.** -/
theorem enabled_form_commitqc {v : view} {e : value} {q : nodeset}
    (hsm : nset.supermajority q)
    (hall : ∀ p, nset.member p q = true → st.msg_commit p v e = true) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.form_commitqc v e q) := by
  mvba_enabled
  exact ⟨_, hsm, hall, rfl⟩

/-- **`form_commitqc`'s effect**: the certificate is on the network. -/
theorem form_commitqc_effect {v : view} {e : value} {q : nodeset}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.form_commitqc v e q) st') : st'.msg_commitqc v e = true := by
  mvba_tr htr
  obtain ⟨-, -, rfl⟩ := htr
  mvba_effect

/-- **The assembly link.** A supermajority all of whose members have sent
their `Commit` on `(v, e)` yields a commit certificate. The index is
reported so that the links compose: the certificate appears at or after the
point the commits were observed, which is what lets the next link's
premises be transported to it. -/
theorem eventually_commitqc_of_commit_quorum
    (r : MvbaRun th) (hfj : FJustice r)
    {N : Nat} {v : view} {e : value} {q : nodeset} (hsm : nset.supermajority q)
    (hall : ∀ p, nset.member p q = true → (r.at' N).msg_commit p v e = true) :
    ∃ n, N ≤ n ∧ (r.at' n).msg_commitqc v e = true := by
  by_contra hcon
  push Not at hcon
  have hall' : ∀ n, N ≤ n → ∀ p, nset.member p q = true →
      (r.at' n).msg_commit p v e = true := by
    intro n hn p hp
    exact r.mono (P := fun s => s.msg_commit p v e = true)
      (fun m hm => Mvba.msg_commit.mono (r.steps m) p v e hm) (hall p hp) n hn
  obtain ⟨n, hn, hfire⟩ :=
    hfj (.form_commitqc v e q)
      (by simp [JusticeLabel, ByzLabel, TimerLabel, Label.isInput]) N
      (fun n hn => enabled_form_commitqc hsm (hall' n hn))
  exact hcon (n + 1) (by omega) (form_commitqc_effect (hfire ▸ r.steps n))

/-- **The rank's commit dimension bottoming out entails termination for one
validator.** The composition of the two links above with
`Rank.lean`'s `commit_quorum_of_assemblyGap_zero`: no certificate is
mentioned, only the residual.

`enum` appears because `assemblyGap` is defined over an enumerated quorum —
the proof-side requirement of [`ByzQuorum.lean`](../ByzQuorum.lean), carried
as a visible hypothesis exactly as intended. -/
theorem eventually_decided_of_assemblyGap_zero
    (r : MvbaRun th) (hfj : FJustice r) (hna : NoEarlyAbandon r)
    (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    {q : nodeset} (hsm : nset.supermajority q)
    {N : Nat} {v : view} {e : value}
    (hz : assemblyGap enum q v e (r.at' N) = 0)
    {i : node} (hi : ¬ nset.is_byz i = true)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true) :
    ∃ (n : Nat) (E : value), (r.at' n).decided i E = true := by
  obtain ⟨m, hm, hqc⟩ := eventually_commitqc_of_commit_quorum r hfj hsm
    (fun p hp => commit_quorum_of_assemblyGap_zero hz p hp)
  exact eventually_decided_of_commitqc r hfj hna hi
    (r.mono (P := fun s => s.input i E₀ = true)
      (fun k hk => Mvba.input.mono (r.steps k) i E₀ hk) hin m hm) hqc

/-! ## The link before *that*: a validator sends its `Commit`

Here the shape changes, and the change is the whole content of §3.1(a).
Every guard of the two links above was monotone, so "enabled once" meant
"enabled ever after" and weak fairness applied directly. `send_commit` has
three guards that are **anti-monotone** — `in_view i v`, `¬ timed_out i v`,
`¬ commit_sent i v` — and each has to be handled differently:

* `in_view` and `¬ timed_out` are assumed, as `SettledIn`. They are what
  (A-viewsync) exists to discharge for the good view, and they cannot be
  proven here because a validator may legitimately sync past a view.
* `¬ commit_sent i v` is **not** assumed, because it is the one whose
  falsification is the goal. Keeping it analysable is what the two new
  invariants in the model are for: if the guard dies, the validator has
  already sent the `Commit` this link was waiting for, so the conclusion
  holds anyway. That is `commit_sent_backed`, and
  `commit_sent_implies_voted` is what makes it inductive — a validator that
  has sent its `Commit` in `v` cannot accept a different vector in `v`,
  because both `Pre-Prepare` handlers require `∀ W, voted i W → W < v`.

Those two invariants are the first cells §3.5 step 3 buys, and they were
found by writing this proof rather than guessed. -/

/-- `i` is **settled in view `v` from `N` on**: at every index from `N` it is
in view `v`, has not timed out there, and has not been abandoned.

These are exactly the anti-monotone guards the honest per-validator actions
of a view share — `Progress.lean`'s table of §3.1(a) — so the links take one
named hypothesis rather than three unnamed ones, and discharging it for the
good view is precisely what (A-viewsync) and `NoEarlyAbandon` are for. -/
def SettledIn (r : MvbaRun th) (i : node) (v : view) (N : Nat) : Prop :=
  ∀ n, N ≤ n →
    InView (r.at' n) i v ∧ ¬ (r.at' n).timed_out i v = true ∧
      ¬ (r.at' n).abandoned i = true

/-- **`send_commit`'s guards are its enabledness.** -/
theorem enabled_send_commit {i : node} {v : view} {e : value}
    (hi : ¬ nset.is_byz i = true)
    (hin : ∃ E, st.input i E = true)
    (hab : ¬ st.abandoned i = true)
    (hview : InView st i v)
    (hacc : st.accepted i v e = true)
    (hloc : st.local_prepqc i v e = true)
    (hnto : ¬ st.timed_out i v = true)
    (hncs : ¬ st.commit_sent i v = true)
    (hav : st.avail_ready i e = true) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.send_commit i v e) := by
  mvba_enabled
  exact ⟨_, hi, hin, hab, hview.1, hview.2, hacc, hloc, hnto, hncs, hav, rfl⟩

/-- **`send_commit`'s effect**: the flag is set and the `Commit` is sent, in
the same step — which is what `commit_sent_backed` lifts to an invariant. -/
theorem send_commit_effect {i : node} {v : view} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.send_commit i v e) st') :
    st'.commit_sent i v = true ∧ st'.msg_commit i v e = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, rfl⟩ := htr
  constructor <;> mvba_effect

/-- **The `send_commit` link.** A correct validator settled in view `v` that
has accepted `e` there, holds the view's certificate on it and has its
availability shares, sends its `Commit` on `(v, e)`.

The `commit_sent` guard is discharged rather than assumed: if it dies, the
model's `commit_sent_backed` says the `Commit` is already on the network, so
the conclusion holds either way. -/
theorem eventually_msg_commit_of_settled
    (r : MvbaRun th) (hfj : FJustice r)
    {i : node} (hi : ¬ nset.is_byz i = true) {v : view} {e : value} {N : Nat}
    (hs : SettledIn r i v N)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hacc : (r.at' N).accepted i v e = true)
    (hloc : (r.at' N).local_prepqc i v e = true)
    (hav : (r.at' N).avail_ready i e = true) :
    ∃ n, N ≤ n ∧ (r.at' n).msg_commit i v e = true := by
  by_contra hcon
  push Not at hcon
  have hin' : ∀ n, N ≤ n → (r.at' n).input i E₀ = true :=
    r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin
  have hacc' : ∀ n, N ≤ n → (r.at' n).accepted i v e = true :=
    r.mono (P := fun s => s.accepted i v e = true)
      (fun m hm => Mvba.accepted.mono (r.steps m) i v e hm) hacc
  have hloc' : ∀ n, N ≤ n → (r.at' n).local_prepqc i v e = true :=
    r.mono (P := fun s => s.local_prepqc i v e = true)
      (fun m hm => Mvba.local_prepqc.mono (r.steps m) i v e hm) hloc
  have hav' : ∀ n, N ≤ n → (r.at' n).avail_ready i e = true :=
    r.mono (P := fun s => s.avail_ready i e = true)
      (fun m hm => Mvba.avail_ready.mono (r.steps m) i e hm) hav
  -- The one anti-monotone guard that is not assumed: if it dies, we are done.
  have hncs : ∀ n, N ≤ n → ¬ (r.at' n).commit_sent i v = true := by
    intro n hn hcs
    exact hcon n hn
      (Mvba.reachable_commit_sent_backed (r.reachable n) i v e hi hcs (hacc' n hn))
  obtain ⟨n, hn, hfire⟩ :=
    hfj (.send_commit i v e)
      (by simp [JusticeLabel, ByzLabel, TimerLabel, Label.isInput]) N
      (fun n hn =>
        enabled_send_commit hi ⟨E₀, hin' n hn⟩ (hs n hn).2.2 (hs n hn).1
          (hacc' n hn) (hloc' n hn) (hs n hn).2.1 (hncs n hn) (hav' n hn))
  exact hcon (n + 1) (by omega) (send_commit_effect (hfire ▸ r.steps n)).2

/-! ## And the link before that: a validator adopts the view's certificate

`adopt_prepqc` has the same three anti-monotone guards as `send_commit`, two
of them again covered by `SettledIn`. The third is the lock-view bound
`∀ W E, local_prepqc i W E → W < v`, and it is handled the same way — not
assumed, because its failure is the goal — but the argument that its failure
*is* the goal takes three of the model's invariants rather than one:

* `local_prepqc_within_entered` (new, and the third cell liveness buys) pins
  the offending certificate's view to at most `v`;
* the guard's failure gives "not below `v`", so the view is `v` exactly;
* `local_prepqc_backed` sends it to `msg_prepqc v E`, and `prepqc_unique`
  — all prepare certificates of a view are on one vector — identifies `E`
  with the `e` the link is about.

So a validator in view `v` whose lock-view guard has lapsed is holding the
very certificate the argument was waiting for. -/

/-- **`adopt_prepqc`'s guards are its enabledness.** -/
theorem enabled_adopt_prepqc {i : node} {v : view} {e : value}
    (hi : ¬ nset.is_byz i = true)
    (hin : ∃ E, st.input i E = true)
    (hab : ¬ st.abandoned i = true)
    (hview : InView st i v)
    (hqc : st.msg_prepqc v e = true)
    (hacc : st.accepted i v e = true)
    (hlow : ∀ W E, st.local_prepqc i W E = true → vord.lt W v)
    (hnto : ¬ st.timed_out i v = true) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.adopt_prepqc i v e) := by
  mvba_enabled
  exact ⟨_, hi, hin, hab, hview.1, hview.2, hqc, hacc, hlow, hnto, rfl⟩

/-- **`adopt_prepqc`'s effect**: the certificate is held. -/
theorem adopt_prepqc_effect {i : node} {v : view} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.adopt_prepqc i v e) st') : st'.local_prepqc i v e = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := htr
  mvba_effect

/-- **A lapsed lock-view guard is the adoption itself.** At a reachable state
where `i` is in view `v` and a prepare certificate of `v` on `e` exists, the
guard `∀ W E, local_prepqc i W E → W < v` can fail only by `i` holding that
very certificate. This is where the three invariants are used. -/
theorem local_prepqc_of_guard_lapsed
    (hr : (Mvba.relationalTransitionSystem node nodeset value view).reachable th st)
    {i : node} (hi : ¬ nset.is_byz i = true) {v : view} {e : value}
    (hview : InView st i v) (hqc : st.msg_prepqc v e = true)
    (hlapse : ¬ ∀ W E, st.local_prepqc i W E = true → vord.lt W v) :
    st.local_prepqc i v e = true := by
  -- Some held certificate is not below `v` …
  obtain ⟨W, E, hWE, hnlt⟩ : ∃ W E, st.local_prepqc i W E = true ∧ ¬ vord.lt W v := by
    by_contra hc
    exact hlapse (fun W E h => by
      by_contra hlt
      exact hc ⟨W, E, h, hlt⟩)
  -- … and none is above it, so it is at `v`.
  have hle : vord.le W v :=
    Mvba.reachable_local_prepqc_within_entered hr i W E v hi hWE hview.2
  have hWv : W = v := by
    rcases (vord.le_lt W v) with ⟨_, hmk⟩
    by_contra hne
    exact hnlt (hmk ⟨hle, hne⟩)
  subst hWv
  -- All prepare certificates of a view are on one vector.
  have hbacked := Mvba.reachable_local_prepqc_backed hr i W E hi hWE
  have := Mvba.reachable_prepqc_unique hr W E e hbacked hqc
  subst this
  exact hWE

/-- **The `adopt_prepqc` link.** A correct validator settled in view `v` that
has accepted `e` there, with a prepare certificate of `v` on `e` on the
network, holds that certificate. -/
theorem eventually_local_prepqc_of_settled
    (r : MvbaRun th) (hfj : FJustice r)
    {i : node} (hi : ¬ nset.is_byz i = true) {v : view} {e : value} {N : Nat}
    (hs : SettledIn r i v N)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hqc : (r.at' N).msg_prepqc v e = true)
    (hacc : (r.at' N).accepted i v e = true) :
    ∃ n, N ≤ n ∧ (r.at' n).local_prepqc i v e = true := by
  by_contra hcon
  push Not at hcon
  have hin' : ∀ n, N ≤ n → (r.at' n).input i E₀ = true :=
    r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin
  have hqc' : ∀ n, N ≤ n → (r.at' n).msg_prepqc v e = true :=
    r.mono (P := fun s => s.msg_prepqc v e = true)
      (fun m hm => Mvba.msg_prepqc.mono (r.steps m) v e hm) hqc
  have hacc' : ∀ n, N ≤ n → (r.at' n).accepted i v e = true :=
    r.mono (P := fun s => s.accepted i v e = true)
      (fun m hm => Mvba.accepted.mono (r.steps m) i v e hm) hacc
  -- The anti-monotone guard: if it lapses, the adoption has happened.
  have hlow : ∀ n, N ≤ n →
      ∀ W E, (r.at' n).local_prepqc i W E = true → vord.lt W v := by
    intro n hn
    by_contra hlapse
    exact hcon n hn
      (local_prepqc_of_guard_lapsed (r.reachable n) hi (hs n hn).1 (hqc' n hn) hlapse)
  obtain ⟨n, hn, hfire⟩ :=
    hfj (.adopt_prepqc i v e)
      (by simp [JusticeLabel, ByzLabel, TimerLabel, Label.isInput]) N
      (fun n hn =>
        enabled_adopt_prepqc hi ⟨E₀, hin' n hn⟩ (hs n hn).2.2 (hs n hn).1
          (hqc' n hn) (hacc' n hn) (hlow n hn) (hs n hn).2.1)
  exact hcon (n + 1) (by omega) (adopt_prepqc_effect (hfire ▸ r.steps n))

/-! ## The prepare assembly, and the per-validator chain closed

`form_prepqc` is the commit assembly's twin — both guards monotone, so the
proof is the one from `eventually_commitqc_of_commit_quorum` with the
relation changed. With it the whole **per-validator** half of a view's work
composes into one statement: from a prepare quorum to that validator's
`Commit`, through adoption and the availability premise.

What is left after this is the quorum-wide half (every correct validator
doing the same, so that the *commit* quorum assembles), the acceptance that
puts `accepted i v e` in place, and discharging `SettledIn`. -/

/-- **`form_prepqc`'s guards are its enabledness.** -/
theorem enabled_form_prepqc {v : view} {e : value} {q : nodeset}
    (hsm : nset.supermajority q)
    (hall : ∀ p, nset.member p q = true → st.msg_prepare p v e = true) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.form_prepqc v e q) := by
  mvba_enabled
  exact ⟨_, hsm, hall, rfl⟩

/-- **`form_prepqc`'s effect**: the prepare certificate is on the network. -/
theorem form_prepqc_effect {v : view} {e : value} {q : nodeset}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.form_prepqc v e q) st') : st'.msg_prepqc v e = true := by
  mvba_tr htr
  obtain ⟨-, -, rfl⟩ := htr
  mvba_effect

/-- **The prepare-assembly link.** A supermajority all of whose members have
sent their `Prepare` on `(v, e)` yields a prepare certificate. -/
theorem eventually_prepqc_of_prepare_quorum
    (r : MvbaRun th) (hfj : FJustice r)
    {N : Nat} {v : view} {e : value} {q : nodeset} (hsm : nset.supermajority q)
    (hall : ∀ p, nset.member p q = true → (r.at' N).msg_prepare p v e = true) :
    ∃ n, N ≤ n ∧ (r.at' n).msg_prepqc v e = true := by
  by_contra hcon
  push Not at hcon
  have hall' : ∀ n, N ≤ n → ∀ p, nset.member p q = true →
      (r.at' n).msg_prepare p v e = true := by
    intro n hn p hp
    exact r.mono (P := fun s => s.msg_prepare p v e = true)
      (fun m hm => Mvba.msg_prepare.mono (r.steps m) p v e hm) (hall p hp) n hn
  obtain ⟨n, hn, hfire⟩ :=
    hfj (.form_prepqc v e q)
      (by simp [JusticeLabel, ByzLabel, TimerLabel, Label.isInput]) N
      (fun n hn => enabled_form_prepqc hsm (hall' n hn))
  exact hcon (n + 1) (by omega) (form_prepqc_effect (hfire ▸ r.steps n))

/-- Being settled from `N` on is being settled from any later point on. -/
theorem SettledIn.later {r : MvbaRun th} {i : node} {v : view} {N M : Nat}
    (hs : SettledIn r i v N) (h : N ≤ M) : SettledIn r i v M :=
  fun n hn => hs n (Nat.le_trans h hn)

/-- **The per-validator chain, closed.** A correct validator settled in view
`v` that has accepted `e` there sends its `Commit` on `(v, e)`, given only a
prepare certificate of that view — which a prepare quorum produces.

This composes three links and the availability premise: adopt the
certificate, wait for the shares, send. The index juggling is the only
fiddly part, and it is only that `FAvail` reports no ordering: availability
may arrive before or after the adoption, so the two are brought to a common
index by monotonicity. -/
theorem eventually_msg_commit_of_prepqc
    (r : MvbaRun th) (hfj : FJustice r) (hav : FAvail r)
    {i : node} (hi : ¬ nset.is_byz i = true) {v : view} {e : value} {N : Nat}
    (hs : SettledIn r i v N)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hqc : (r.at' N).msg_prepqc v e = true)
    (hacc : (r.at' N).accepted i v e = true) :
    ∃ n, N ≤ n ∧ (r.at' n).msg_commit i v e = true := by
  -- Adopt the certificate.
  obtain ⟨n₁, hn₁, hloc⟩ := eventually_local_prepqc_of_settled r hfj hi hs hin hqc hacc
  -- The availability shares arrive, at an index `FAvail` does not order.
  obtain ⟨m, hm⟩ := hav i N v e hi hacc
  -- Bring both to a common point, monotonically.
  have h₁ : n₁ ≤ max n₁ m := Nat.le_max_left n₁ m
  have h₂ : m ≤ max n₁ m := Nat.le_max_right n₁ m
  have hN : N ≤ max n₁ m := Nat.le_trans hn₁ h₁
  obtain ⟨k, hk, hres⟩ :=
    eventually_msg_commit_of_settled r hfj hi (hs.later hN)
      (r.mono (P := fun s => s.input i E₀ = true)
        (fun j hj => Mvba.input.mono (r.steps j) i E₀ hj) hin _ hN)
      (r.mono (P := fun s => s.accepted i v e = true)
        (fun j hj => Mvba.accepted.mono (r.steps j) i v e hj) hacc _ hN)
      (r.mono (P := fun s => s.local_prepqc i v e = true)
        (fun j hj => Mvba.local_prepqc.mono (r.steps j) i v e hj) hloc _ h₁)
      (r.mono (P := fun s => s.avail_ready i e = true)
        (fun j hj => Mvba.avail_ready.mono (r.steps j) i e hj) hm _ h₂)
  exact ⟨k, Nat.le_trans hN hk, hres⟩

/-! ## The acceptance, and the whole per-validator chain

`handle_preprepare` is the last per-validator link, and the most expensive:
its vote guard `∀ W, voted i W → W < v` is anti-monotone like the two
before it, but showing that its failure *is* the goal takes five invariants
rather than one, because a vote is a weaker thing than a lock. The chain is:

* `voted_within_entered` pins a lapse to view `v` rather than one above it,
  exactly as `local_prepqc_within_entered` did for the lock;
* at `v`, the validator is not timed out (`SettledIn`), and voting without
  timing out is accepting — `voted_implies_accepted_proposal`;
* what it accepted is what the leader proposed, because an honest leader
  proposes once per view (`honest_preprepare_unique`, with
  `honest_preprepare_proposed` and `voted_implies_leader_proposed` making
  that inductive).

The honest leader is where this link differs from every earlier one: it is
the first that does not hold for an arbitrary view. That is not an artefact
— under a Byzantine leader two correct validators really can accept
different vectors, which is why the protocol needs an honest-led view at
all, and why (A-viewsync) produces one. -/

/-- **`handle_preprepare`'s guards are its enabledness.** -/
theorem enabled_handle_preprepare {i l : node} {pv v : view} {e : value}
    (hi : ¬ nset.is_byz i = true)
    (hin : ∃ E, st.input i E = true)
    (hab : ¬ st.abandoned i = true)
    (hview : InView st i v)
    (hnext : vord.next pv v)
    (hlead : th.leader v l = true)
    (hpp : st.msg_preprepare l v e = true)
    (hvalid : th.valid e = true)
    (hjust : (∃ w, st.tc_lock pv w e = true) ∨ st.tc_nolock pv = true)
    (hvote : ∀ W, st.voted i W = true → vord.lt W v) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.handle_preprepare i l pv v e) := by
  mvba_enabled
  exact ⟨_, hi, hin, hab, hview.1, hview.2, hnext, hlead, hpp, hvalid, hjust, hvote, rfl⟩

/-- **`handle_preprepare`'s effect**: the vector is accepted and the
`Prepare` is sent. -/
theorem handle_preprepare_effect {i l : node} {pv v : view} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.handle_preprepare i l pv v e) st') :
    st'.accepted i v e = true ∧ st'.msg_prepare i v e = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := htr
  constructor <;> mvba_effect

/-- **A lapsed vote guard is the acceptance itself**, under an honest
leader. At a reachable state where `i` is settled in view `v` and the
honest leader of `v` has proposed `e`, the guard
`∀ W, voted i W → W < v` can fail only by `i` having accepted `e`. -/
theorem accepted_of_vote_guard_lapsed
    (hr : (Mvba.relationalTransitionSystem node nodeset value view).reachable th st)
    {i l : node} (hi : ¬ nset.is_byz i = true) {v : view} {e : value}
    (hview : InView st i v) (hnto : ¬ st.timed_out i v = true)
    (hlead : th.leader v l = true) (hl : ¬ nset.is_byz l = true)
    (hpp : st.msg_preprepare l v e = true)
    (hlapse : ¬ ∀ W, st.voted i W = true → vord.lt W v) :
    st.accepted i v e = true := by
  obtain ⟨W, hW, hnlt⟩ : ∃ W, st.voted i W = true ∧ ¬ vord.lt W v := by
    by_contra hc
    exact hlapse (fun W h => by
      by_contra hlt
      exact hc ⟨W, h, hlt⟩)
  have hle : vord.le W v := Mvba.reachable_voted_within_entered hr i W v hi hW hview.2
  have hWv : W = v := by
    rcases (vord.le_lt W v) with ⟨_, hmk⟩
    by_contra hne
    exact hnlt (hmk ⟨hle, hne⟩)
  subst hWv
  exact Mvba.reachable_voted_implies_accepted_proposal hr i W l e hi hW hnto hlead hl hpp

/-- **The acceptance link.** A correct validator settled in view `v`, with
the honest leader of `v` having proposed a valid `e` justified by the
previous view's timeout certificate, accepts `e` and sends its `Prepare`. -/
theorem eventually_accepted_of_settled
    (r : MvbaRun th) (hfj : FJustice r)
    {i l : node} (hi : ¬ nset.is_byz i = true) {pv v : view} {e : value} {N : Nat}
    (hs : SettledIn r i v N)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (hnext : vord.next pv v)
    (hlead : th.leader v l = true) (hl : ¬ nset.is_byz l = true)
    (hpp : (r.at' N).msg_preprepare l v e = true)
    (hvalid : th.valid e = true)
    (hjust : (∃ w, (r.at' N).tc_lock pv w e = true) ∨ (r.at' N).tc_nolock pv = true) :
    ∃ n, N ≤ n ∧ (r.at' n).accepted i v e = true ∧ (r.at' n).msg_prepare i v e = true := by
  by_contra hcon
  push Not at hcon
  have hin' : ∀ n, N ≤ n → (r.at' n).input i E₀ = true :=
    r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin
  have hpp' : ∀ n, N ≤ n → (r.at' n).msg_preprepare l v e = true :=
    r.mono (P := fun s => s.msg_preprepare l v e = true)
      (fun m hm => Mvba.msg_preprepare.mono (r.steps m) l v e hm) hpp
  have hjust' : ∀ n, N ≤ n →
      (∃ w, (r.at' n).tc_lock pv w e = true) ∨ (r.at' n).tc_nolock pv = true := by
    rcases hjust with ⟨w, hw⟩ | hnl
    · exact fun n hn => Or.inl ⟨w, r.mono (P := fun s => s.tc_lock pv w e = true)
        (fun m hm => Mvba.tc_lock.mono (r.steps m) pv w e hm) hw n hn⟩
    · exact fun n hn => Or.inr (r.mono (P := fun s => s.tc_nolock pv = true)
        (fun m hm => Mvba.tc_nolock.mono (r.steps m) pv hm) hnl n hn)
  -- The anti-monotone guard: if it lapses, the acceptance has happened, and
  -- the `Prepare` goes with it (`honest_prepare_accepted`'s converse is the
  -- action's own effect, so the two arrive together or not at all).
  have hvote : ∀ n, N ≤ n → ∀ W, (r.at' n).voted i W = true → vord.lt W v := by
    intro n hn
    by_contra hlapse
    have hacc := accepted_of_vote_guard_lapsed (r.reachable n) hi (hs n hn).1
      (hs n hn).2.1 hlead hl (hpp' n hn) hlapse
    exact hcon n hn hacc
      (Mvba.reachable_accepted_implies_prepare (r.reachable n) i v e hi hacc)
  obtain ⟨n, hn, hfire⟩ :=
    hfj (.handle_preprepare i l pv v e)
      (by simp [JusticeLabel, ByzLabel, TimerLabel, Label.isInput]) N
      (fun n hn =>
        enabled_handle_preprepare hi ⟨E₀, hin' n hn⟩ (hs n hn).2.2 (hs n hn).1
          hnext hlead (hpp' n hn) hvalid (hjust' n hn) (hvote n hn))
  obtain ⟨ha, hp⟩ := handle_preprepare_effect (hfire ▸ r.steps n)
  exact hcon (n + 1) (by omega) ha hp

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

/--
info: 'Mvba.eventually_decided_of_commitqc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_decided_of_commitqc

/--
info: 'Mvba.eventually_decided_of_assemblyGap_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_decided_of_assemblyGap_zero

/--
info: 'Mvba.eventually_msg_commit_of_settled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_msg_commit_of_settled

/--
info: 'Mvba.eventually_local_prepqc_of_settled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_local_prepqc_of_settled

/--
info: 'Mvba.eventually_msg_commit_of_prepqc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_msg_commit_of_prepqc

/--
info: 'Mvba.eventually_accepted_of_settled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_accepted_of_settled
