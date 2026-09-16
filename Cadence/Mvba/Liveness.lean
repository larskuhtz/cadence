import Cadence.Mvba.Rank
import Cadence.Mvba.Compose
import Cadence.Fairness
import Cadence.ViewOrder

/-! # Mvba.Liveness — the run-level target, and the assumptions it rests on

[`docs/MvbaPlan.md`](../../docs/MvbaPlan.md) §3.4 and §3.5 step 4. This file
states the bound-erased termination claim, every premise it takes, **and its
proof**: `Mvba.termination : TerminationClaim th`.

`TerminationClaim` is a `Prop`-valued *definition*, written down before any
of the proof existed. That was the point of the ordering: the target and its
premises were fixed, type-checked and citable in advance rather than
accumulating as a proof went along, so nothing could quietly become a
hypothesis because a proof turned out to need it. The list moved twice afterwards and both moves are recorded. A
(F-timeout) premise was added when §3.2's two fairness classes turned out
not to work, and removed again once the model carried a timer and the proof
was seen never to use it. Validity of the callers' inputs went the other
way: it is part of the contract with the consumer, so it became
`MVBASafety.propose_valid` and a guard of `Mvba.propose` (the supplement's
own precondition) rather than a premise here.

Everything a human has to believe is therefore a named `Prop` in this file,
each with a docstring and each appearing as an explicit hypothesis of the
claim — never a side condition discovered by reading a proof.
`grep -n '^def [A-Z]' Cadence/Mvba/Liveness.lean` prints the whole list: the
four label classes, the five premises, the target and the claim, and
nothing else.

## The fairness classification, and a correction to §3.2

`MvbaPlan.md` §3.2 fixed **two** scheduling classes: unfair for the `byz_*`
family (F-byz), weakly fair for the honest actions (F-justice). Writing the
run-level statement down shows that two is not enough, and that the natural
reading of the pair is **inconsistent**.

The reason is the timeout. `timeout_qc` and `timeout_noqc` are honest
actions, so §3.2 puts them under (F-justice); but if their guards say
nothing about time, a correct validator in a view has one of them
continuously enabled, weak fairness forces it to fire in *every* view
including the good one, and any assumption that the good view survives its
timeout contradicts that outright. A contradictory premise set does not make
a theorem hard to prove; it makes it vacuous, which is the one outcome worth
engineering against.

The fix was to put the timing back into the model, as little of it as the
claim needs: `expire_timer i v` is an **abstract phase marker**, a clock with
exactly one tick, from before the timeout to after it, and both timeout
actions are guarded on it. With that the timeouts can be weakly fair like
every other honest action; what they may no longer do is fire before the
timer has run out. So there are three scheduling classes, not two, and the
whole of the timing assumption sits on the extra one:

| class | labels | what is assumed |
|---|---|---|
| unfair | `ByzLabel` | nothing — (F-byz) |
| weakly fair | `JusticeLabel`, the two `timeout_*` among them | (F-justice) |
| timer | `TimerLabel`, i.e. `expire_timer` | (A-viewsync), both clauses |
| input | `InputLabel` | nothing here — a premise of the claim, not fairness |

**The timer is not weakly fair, and must not be.** Both halves of the
supplement's timeout discipline are statements about *when* it may tick —
finite in every view, and in the good view not before the chain has produced
a certificate — and (A-viewsync) is exactly that pair. Handing the marker to
weak fairness instead would force a tick in the good view, and with the
second clause that yields a commit certificate with no protocol reasoning at
all: the chain of links below would become dead code, proved past rather
than used. It is the same trivialisation the first clause is scoped away
from the good view to avoid, and the argument is written out at
`AViewSync`.

**There is no premise saying views eventually close, and none saying
validators reach the good view.** Both were once on the list. The first
— (F-timeout) — was dropped when the timer arrived and the proof turned out
not to use it. The second was (A-viewsync)'s entry clause, and it is now a
**theorem** (`eventually_entered_good`): the longest argument in the file,
and the reason [`ViewOrder.lean`](../ViewOrder.lean) exists.

The inputs `propose` and `abandon` are the *caller's*, not the scheduler's
(`Mvba/Compose.lean`'s `Label.isInput`), so no fairness is assumed of them.
That every correct validator proposes is `AllPropose`, a premise of the
claim exactly as it is in `thm:termination` ("once every correct validator
has invoked propose").

## What the claim does not mention

`ByzNodeSetEnum`, `ByzNodeSetHonestQuorum` and `ViewOrderEnum` are absent
from the statement and appear as hypotheses of the *theorem*. That split is
the point: enumerability, a constructive quorum of correct validators
([`ByzQuorum.lean`](../ByzQuorum.lean)) and a discrete, finitely-generated
view order ([`ViewOrder.lean`](../ViewOrder.lean)) are what a **proof** needs
to assemble certificates and to count, not part of what is being claimed.

## Open: non-vacuity of the premise set

The classification above removes the one contradiction found so far, but
"these five premises are jointly satisfiable" is not yet proven. It needs a
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

/-- The timer label. Just `expire_timer`, the environment action that marks
a validator's view timer as run out.

The two `timeout_*` actions used to be here. They are ordinary honest
actions again now that the model carries the marker: they are guarded on it,
so they are not perpetually enabled, and weak fairness on them is sound —
see the header. What carries no fairness hypothesis is the *marker*, because
when a timer expires is the one piece of timing an untimed model cannot
derive. -/
def TimerLabel : Mvba.Label node nodeset value view → Prop
  | .expire_timer .. => True
  | _ => False

/-- The two contract inputs. This restates `Mvba/Compose.lean`'s
`Label.isInput` rather than using it, and the reason is mechanical, not a
disagreement about what an input is: since the label type reached
twenty-five constructors that definition's `match` no longer reduces outside
its own module, so `¬ Label.isInput (.decide …)` cannot be discharged here.
The two are tied together by `not_justice_of_input` below, through
`Label.isInput_cases`, so a drift between them is caught rather than
silent. -/
def InputLabel : Mvba.Label node nodeset value view → Prop
  | .propose .. => True
  | .abandon .. => True
  | _ => False

/-- The labels (F-justice) covers: the honest message handlers, the
certificate assemblies, the view changes, the timeouts and the environment's
availability action — everything that is neither the adversary's, nor the
timer, nor the caller's input. -/
def JusticeLabel (l : Mvba.Label node nodeset value view) : Prop :=
  ¬ ByzLabel l ∧ ¬ TimerLabel l ∧ ¬ InputLabel l

/-- **(F-byz), machine-checked at the only level it can be**: no label the
adversary controls is subject to a fairness hypothesis. -/
theorem not_justice_of_byz (l : Mvba.Label node nodeset value view)
    (h : ByzLabel l) : ¬ JusticeLabel l := fun hj => hj.1 h

/-- Likewise for the timers: (F-justice) does not reach them. -/
theorem not_justice_of_timer (l : Mvba.Label node nodeset value view)
    (h : TimerLabel l) : ¬ JusticeLabel l := fun hj => hj.2.1 h

/-- And the caller's inputs are not scheduled here either — stated against
`Mvba/Compose.lean`'s `Label.isInput`, which is what ties `InputLabel` to the
module's own notion of an input. -/
theorem not_justice_of_input (l : Mvba.Label node nodeset value view)
    (h : Label.isInput l) : ¬ JusticeLabel l := by
  rcases Label.isInput_cases h with ⟨i, e, rfl⟩ | ⟨i, rfl⟩
  · exact fun hj => hj.2.2 trivial
  · exact fun hj => hj.2.2 trivial

/-- The classification is exhaustive: every label falls under one of the four
disciplines.

Exhaustiveness is *by construction* — `JusticeLabel` is defined as the
negation of the other three — so this is a classical case split and checks
nothing about the action list. What does the checking is the two `match`
definitions above, which are non-exhaustive matches over the model's own
label type: adding an action and forgetting it lands it in `JusticeLabel`
silently, and the guard against that is reading them, not this lemma.
(A `cases l` proof used to stand here and verified no more; it stopped
elaborating when the twenty-fifth action pushed `Label.isInput`'s match past
the point where Lean generates its equation lemmas.) -/
theorem label_classified (l : Mvba.Label node nodeset value view) :
    JusticeLabel l ∨ ByzLabel l ∨ TimerLabel l ∨ InputLabel l := by
  classical
  by_cases hb : ByzLabel l
  · exact Or.inr (Or.inl hb)
  by_cases ht : TimerLabel l
  · exact Or.inr (Or.inr (Or.inl ht))
  by_cases hi : InputLabel l
  · exact Or.inr (Or.inr (Or.inr hi))
  exact Or.inl ⟨hb, ht, hi⟩

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

/-- **(A-viewsync)** — *the good view, and what its timer may do.* There is
an honest-led view `W`, above the first, such that

* in every view **below** `W` a correct validator's timer eventually runs
  out, and
* in `W` no correct validator's timer runs out before a commit certificate
  exists.

Untimed, that is the whole of the supplement's timeout discipline: the first
clause is "every view's timeout is finite", the second is "the good view's
timeout exceeds the chain's latency after GST". Both speak only about the
environment's timer — `expire_timer`, the model's phase marker — and neither
mentions the protocol's outcome.

**What is no longer here.** This premise used to also assert that every
correct validator *enters* `W`, which is the strong, protocol-specific half:
view synchronisation, assumed. It is now derived
(`eventually_entered_good`), and what is left is a statement about when a
timer may fire.

**Why the first clause stops below `W`.** In the timed protocol the two
clauses are about one object: every view's timeout is finite, and `W`'s
exceeds the latency. Untimed, "exceeds the latency" can only be said as "not
before the certificate" — and a finiteness clause covering `W` would then,
together with it, hand over a commit certificate outright, which is the
thing the decision chain is there to prove. So the good view has to be
excluded, and it costs nothing: it is the view in which the protocol
succeeds, so the second clause's conditional is never triggered. The views
*above* `W` are excluded for a different and duller reason — the proof does
not use them, and a premise should assume no more than it needs.

**Why the consequent is a certificate.** It is weaker than the paper's
sentence, which speaks of the decision, and enough, because
`eventually_decided_of_commitqc` turns a certificate into every correct
validator deciding using (F-justice) alone. So the premise mentions neither
`decided` nor `timed_out`: it relates two events, a timer running out and a
certificate existing. And the "before …" is load-bearing — a flat "the timer
never runs out in `W`" would be unsatisfiable the moment anything forced
timers to expire.

The good view is required to be **above the first**, by naming its
predecessor `PV`. That is not a convenience: `thm:termination`'s proof makes
the same restriction in as many words — "View 1 is exceptional because
validators enter it when their local `propose` call occurs, and those calls
need not be Δ-synchronized … We therefore analyze below a later view entered
through a timeout certificate", the exceptional case contributing only a
further `O(Δ)`. It costs nothing, because (A-leader-rotation) puts an
honest-led view above *every* view, view 1 included. -/
def AViewSync (r : MvbaRun th) : Prop :=
  ∃ (W PV : view) (L : node),
    vord.next PV W ∧
    th.leader W L = true ∧ ¬ nset.is_byz L = true ∧
    (∀ (i : node) (V : view), ¬ nset.is_byz i = true → vord.lt V W →
      (∃ n, (r.at' n).entered i V = true) →
        ∃ n, (r.at' n).timer_expired i V = true) ∧
    (∀ (i : node) (n : Nat), ¬ nset.is_byz i = true →
      (r.at' n).timer_expired i W = true →
        ∃ (V : view) (E : value), (r.at' n).msg_commitqc V E = true)

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

The five premises are exactly the file's named definitions. Input validity
is **not** among them, and deliberately: it is part of the contract between
the consumer and this module, so it lives in `Mvba.propose`'s guard where
Chorus's `mvba_propose` already meets it, rather than being restated here as
a premise of every liveness theorem. What is also deliberately *absent* is
any quorum machinery: `ByzNodeSetEnum` and
`ByzNodeSetHonestQuorum` are what a **proof** needs to assemble certificates,
not part of what is claimed, and they appear as hypotheses of `termination`
below rather than here. -/
def TerminationClaim (th : Theory node nodeset value view) : Prop :=
  ∀ r : MvbaRun th,
    FJustice r → AViewSync r → FAvail r →
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
    hfj (.decide i v e) (⟨fun h => h, fun h => h, fun h => h⟩) N
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
      (⟨fun h => h, fun h => h, fun h => h⟩) N
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
      (⟨fun h => h, fun h => h, fun h => h⟩) N
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
      (⟨fun h => h, fun h => h, fun h => h⟩) N
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
      (⟨fun h => h, fun h => h, fun h => h⟩) N
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
      (⟨fun h => h, fun h => h, fun h => h⟩) N
      (fun n hn =>
        enabled_handle_preprepare hi ⟨E₀, hin' n hn⟩ (hs n hn).2.2 (hs n hn).1
          hnext hlead (hpp' n hn) hvalid (hjust' n hn) (hvote n hn))
  obtain ⟨ha, hp⟩ := handle_preprepare_effect (hfire ▸ r.steps n)
  exact hcon (n + 1) (by omega) ha hp

/-! ## The quorum-wide lift, and a view that decides

Everything so far has been about one validator. A certificate needs a
*quorum* of them to have acted **at the same state**, and that is a
different kind of step: weak fairness gives each member's message
eventually, at its own index, and the assembly guard needs one index where
all of them have arrived.

`Fairness.lean`'s `eventually_forall` is that step, and it is where
finiteness is finally consumed: monotone predicates over a **finite list**
collapse a family of eventualities into one. `ByzNodeSetEnum` supplies the
list, and `ByzNodeSetHonestQuorum` supplies a quorum whose members are all
correct — which matters because under (F-byz) no progress may rest on a
Byzantine member sending anything. Both are hypotheses of the theorems
below and of nothing else in the development. -/

/-- **Lift a per-member eventuality to the whole quorum.** -/
theorem eventually_quorum (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (r : MvbaRun th) {q : nodeset} {N : Nat}
    (P : node → Mvba.State (Mvba.FieldAbstractType node nodeset value view) → Prop)
    (hmono : ∀ p n, P p (r.at' n) → P p (r.at' (n + 1)))
    (h : ∀ p, nset.member p q = true → ∃ n, N ≤ n ∧ P p (r.at' n)) :
    ∃ n, N ≤ n ∧ ∀ p, nset.member p q = true → P p (r.at' n) := by
  obtain ⟨n, hn, hall⟩ :=
    r.eventually_forall P hmono N (enum.members q)
      (fun p hp => h p ((enum.mem_members p q).mpr hp))
  exact ⟨n, hn, fun p hp => hall p ((enum.mem_members p q).mp hp)⟩

/-- **A view with an honest leader decides**, given that its correct quorum
is settled there and the leader has proposed.

This is the whole of `thm:termination`'s "correct-leader view" paragraph,
bound erased: every member of the honest quorum accepts the proposal and
prepares, the prepare certificate forms, each of them adopts it and
commits, the commit certificate forms, and then *every* correct validator
that has proposed decides — not only the quorum's members, because `decide`
accepts a certificate of any view and needs nothing local.

The hypotheses are the six premises' content specialised to one view, plus
the two quorum classes. `SettledIn` is still assumed rather than derived;
discharging it for the view (A-viewsync) produces is what remains. -/
theorem terminates_of_settled_honest_view
    (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (r : MvbaRun th) (hfj : FJustice r) (hav : FAvail r) (hna : NoEarlyAbandon r)
    (hq : Cadence.ByzNodeSetHonestQuorum node nodeset nset)
    (hap : AllPropose r)
    {l : node} (hl : ¬ nset.is_byz l = true) {pv v : view} {e : value} {N : Nat}
    (hnext : vord.next pv v)
    (hlead : th.leader v l = true)
    (hpp : (r.at' N).msg_preprepare l v e = true)
    (hvalid : th.valid e = true)
    (hjust : (∃ w, (r.at' N).tc_lock pv w e = true) ∨ (r.at' N).tc_nolock pv = true)
    (hs : ∀ p, nset.member p hq.honestQuorum = true → SettledIn r p v N) :
    Terminates r := by
  have hcorrect : ∀ p, nset.member p hq.honestQuorum = true → ¬ nset.is_byz p = true :=
    hq.honestQuorum_correct
  -- (1) Every member accepts and prepares — at its own index …
  have hstep1 : ∀ p, nset.member p hq.honestQuorum = true →
      ∃ n, N ≤ n ∧ ((r.at' n).accepted p v e = true ∧
        (r.at' n).msg_prepare p v e = true) := by
    intro p hp
    obtain ⟨E₀, hE₀⟩ :=
      Mvba.reachable_entered_implies_input (r.reachable N) p v (hcorrect p hp)
        ((hs p hp N (Nat.le_refl N)).1).1
    obtain ⟨n, hn, ha, hpr⟩ :=
      eventually_accepted_of_settled r hfj (hcorrect p hp) (hs p hp) hE₀ hnext hlead hl
        hpp hvalid hjust
    exact ⟨n, hn, ha, hpr⟩
  -- … and, being finitely many, at one index.
  obtain ⟨n₁, hn₁, hall₁⟩ :=
    eventually_quorum enum r
      (fun p s => s.accepted p v e = true ∧ s.msg_prepare p v e = true)
      (fun p m hm => ⟨Mvba.accepted.mono (r.steps m) p v e hm.1,
        Mvba.msg_prepare.mono (r.steps m) p v e hm.2⟩)
      hstep1
  -- (2) The prepare certificate forms.
  obtain ⟨n₂, hn₂, hqc⟩ :=
    eventually_prepqc_of_prepare_quorum r hfj hq.honestQuorum_supermajority
      (fun p hp => (hall₁ p hp).2)
  -- (3) Every member commits — again at its own index, then at one.
  have hstep3 : ∀ p, nset.member p hq.honestQuorum = true →
      ∃ n, n₂ ≤ n ∧ (r.at' n).msg_commit p v e = true := by
    intro p hp
    obtain ⟨E₀, hE₀⟩ :=
      Mvba.reachable_entered_implies_input (r.reachable n₂) p v (hcorrect p hp)
        ((hs p hp n₂ (Nat.le_trans hn₁ hn₂)).1).1
    exact eventually_msg_commit_of_prepqc r hfj hav (hcorrect p hp)
      ((hs p hp).later (Nat.le_trans hn₁ hn₂)) hE₀ hqc
      (r.mono (P := fun s => s.accepted p v e = true)
        (fun m hm => Mvba.accepted.mono (r.steps m) p v e hm) (hall₁ p hp).1 _ hn₂)
  obtain ⟨n₃, hn₃, hall₃⟩ :=
    eventually_quorum enum r (fun p s => s.msg_commit p v e = true)
      (fun p m hm => Mvba.msg_commit.mono (r.steps m) p v e hm) hstep3
  -- (4) The commit certificate forms …
  obtain ⟨n₄, hn₄, hcqc⟩ :=
    eventually_commitqc_of_commit_quorum r hfj hq.honestQuorum_supermajority hall₃
  -- … and every correct validator that has proposed decides on it.
  intro i hi
  obtain ⟨m, E, hm⟩ := hap i hi
  exact eventually_decided_of_commitqc r hfj hna hi
    (r.mono (P := fun s => s.input i E = true)
      (fun j hj => Mvba.input.mono (r.steps j) i E hj) hm _ (Nat.le_max_left m n₄))
    (r.mono (P := fun s => s.msg_commitqc v e = true)
      (fun j hj => Mvba.msg_commitqc.mono (r.steps j) v e hj) hcqc _
      (Nat.le_max_right m n₄))

/-! ## The leader proposes

The last link, and the first at the *leader's* end rather than a follower's.
Its anti-monotone guard is `¬ proposed_in l v`, handled exactly as
`¬ commit_sent i v` was: not assumed, because its falsification is the goal,
with `proposed_in_backed` saying the guard can only die by the proposal the
argument was waiting for.

Both ways of proposing above the first view are covered, and which applies is
decided by the previous view's timeout certificate, as the protocol decides
it: with a lock, `leader_repropose` re-offers the locked vector; without one,
`leader_propose_fresh` offers the leader's own input.

**What this link deliberately does not claim.** It gives a proposal, not a
*valid* one. For a re-proposal validity is a theorem — `prepqc_valid` on the
lock the certificate carries — but for a fresh proposal it is not available
at all: `leader_propose_fresh` requires `input l e` and nothing more, and
`propose` does not check validity either, the model's header being explicit
that "`Valid B_i` is the caller's obligation". So an honest leader really can
propose an invalid vector, no correct validator will accept it
(`handle_preprepare` requires `valid e`), and its view is wasted. That is a
genuine premise of `thm:termination` rather than a gap here, and it belongs
with the other caller premises (`AllPropose`, `NoEarlyAbandon`) when the
composition needs it. -/

/-- **`leader_repropose`'s guards are its enabledness.** -/
theorem enabled_leader_repropose {l : node} {pv v w : view} {e : value}
    (hl : ¬ nset.is_byz l = true)
    (hin : ∃ E, st.input l E = true)
    (hab : ¬ st.abandoned l = true)
    (hnext : vord.next pv v)
    (hlead : th.leader v l = true)
    (hview : InView st l v)
    (hlock : st.tc_lock pv w e = true)
    (hnp : ¬ st.proposed_in l v = true) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.leader_repropose l pv v w e) := by
  mvba_enabled
  exact ⟨_, hl, hin, hab, hnext, hlead, hview.1, hview.2, hlock, hnp, rfl⟩

/-- **`leader_propose_fresh`'s guards are its enabledness.** -/
theorem enabled_leader_propose_fresh {l : node} {pv v : view} {e : value}
    (hl : ¬ nset.is_byz l = true)
    (hab : ¬ st.abandoned l = true)
    (hnext : vord.next pv v)
    (hlead : th.leader v l = true)
    (hview : InView st l v)
    (hnl : st.tc_nolock pv = true)
    (hinp : st.input l e = true)
    (hnp : ¬ st.proposed_in l v = true) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.leader_propose_fresh l pv v e) := by
  mvba_enabled
  exact ⟨_, hl, hab, hnext, hlead, hview.1, hview.2, hnl, hinp, hnp, rfl⟩

theorem leader_repropose_effect {l : node} {pv v w : view} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.leader_repropose l pv v w e) st') : st'.msg_preprepare l v e = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := htr
  mvba_effect

theorem leader_propose_fresh_effect {l : node} {pv v : view} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.leader_propose_fresh l pv v e) st') : st'.msg_preprepare l v e = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := htr
  mvba_effect

/-- **The leader link.** An honest leader settled in a view above the first,
whose previous view carries a timeout certificate, proposes. -/
theorem eventually_preprepare_of_settled_leader
    (r : MvbaRun th) (hfj : FJustice r)
    {l : node} (hl : ¬ nset.is_byz l = true) {pv v : view} {N : Nat}
    (hs : SettledIn r l v N)
    (hnext : vord.next pv v)
    (hlead : th.leader v l = true)
    (hjust : (∃ w e, (r.at' N).tc_lock pv w e = true) ∨ (r.at' N).tc_nolock pv = true) :
    ∃ (n : Nat) (E : value), N ≤ n ∧ (r.at' n).msg_preprepare l v E = true := by
  -- The leader has an input, because it is in a view.
  obtain ⟨E₀, hE₀⟩ :=
    Mvba.reachable_entered_implies_input (r.reachable N) l v hl
      ((hs N (Nat.le_refl N)).1).1
  have hin' : ∀ n, N ≤ n → (r.at' n).input l E₀ = true :=
    r.mono (P := fun s => s.input l E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) l E₀ hm) hE₀
  by_contra hcon
  push Not at hcon
  -- The anti-monotone guard: if it lapses, the leader has already proposed.
  have hnp : ∀ n, N ≤ n → ¬ (r.at' n).proposed_in l v = true := by
    intro n hn hp
    obtain ⟨E', hE'⟩ := Mvba.reachable_proposed_in_backed (r.reachable n) l v hl hp
    exact hcon n E' hn hE'
  rcases hjust with ⟨w, e, hw⟩ | hnl
  · have hw' : ∀ n, N ≤ n → (r.at' n).tc_lock pv w e = true :=
      r.mono (P := fun s => s.tc_lock pv w e = true)
        (fun m hm => Mvba.tc_lock.mono (r.steps m) pv w e hm) hw
    obtain ⟨n, hn, hfire⟩ :=
      hfj (.leader_repropose l pv v w e)
        (⟨fun h => h, fun h => h, fun h => h⟩) N
        (fun n hn =>
          enabled_leader_repropose hl ⟨E₀, hin' n hn⟩ (hs n hn).2.2 hnext hlead
            (hs n hn).1 (hw' n hn) (hnp n hn))
    exact hcon (n + 1) e (by omega) (leader_repropose_effect (hfire ▸ r.steps n))
  · have hnl' : ∀ n, N ≤ n → (r.at' n).tc_nolock pv = true :=
      r.mono (P := fun s => s.tc_nolock pv = true)
        (fun m hm => Mvba.tc_nolock.mono (r.steps m) pv hm) hnl
    obtain ⟨n, hn, hfire⟩ :=
      hfj (.leader_propose_fresh l pv v E₀)
        (⟨fun h => h, fun h => h, fun h => h⟩) N
        (fun n hn =>
          enabled_leader_propose_fresh hl (hs n hn).2.2 hnext hlead (hs n hn).1
            (hnl' n hn) (hin' n hn) (hnp n hn))
    exact hcon (n + 1) E₀ (by omega) (leader_propose_fresh_effect (hfire ▸ r.steps n))

/-! ## The view change

The other half of liveness, and the one the decision chain cannot supply:
what carries a run *out of* a view whose leader is silent or faulty, and so
towards the honest-led view (A-leader-rotation) promises.

Three steps. What makes the *first* one fire — a validator's timer running
out — is not a link but the assumption (A-viewsync)'s first clause, and
"Reaching the good view" below is where it is consumed. Given that, the rest
is the familiar shape: a quorum of timeouts assembles a certificate, and the
certificate lets a validator advance.

Neither step costs a new invariant. `sync_view`'s guard
`∀ V, entered i V → V ≤ pv` is anti-monotone, but its failure is the goal
outright — a validator whose views are no longer all below `pv` has already
advanced past `pv`, which is what the step was for. That is the cleanest
instance of the pattern in the file: no invariant is needed because the
guard's negation *is* the conclusion. -/

/-- **`form_tc_nolock`'s guards are its enabledness.** -/
theorem enabled_form_tc_nolock {v : view} {q : nodeset}
    (hsm : nset.supermajority q)
    (hall : ∀ p, nset.member p q = true → st.msg_timeout_noqc p v = true) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.form_tc_nolock v q) := by
  mvba_enabled
  exact ⟨_, hsm, hall, rfl⟩

/-- **`form_tc_nolock`'s effect**: the view is closed by a certificate. -/
theorem form_tc_nolock_effect {v : view} {q : nodeset}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.form_tc_nolock v q) st') : st'.msg_tc v = true := by
  mvba_tr htr
  obtain ⟨-, -, rfl⟩ := htr
  mvba_effect

/-- **The timeout-certificate link.** A supermajority all of whose members
have sent their lock-free `Timeout` for `v` closes the view. -/
theorem eventually_tc_of_timeout_quorum
    (r : MvbaRun th) (hfj : FJustice r)
    {N : Nat} {v : view} {q : nodeset} (hsm : nset.supermajority q)
    (hall : ∀ p, nset.member p q = true → (r.at' N).msg_timeout_noqc p v = true) :
    ∃ n, N ≤ n ∧ (r.at' n).msg_tc v = true := by
  by_contra hcon
  push Not at hcon
  have hall' : ∀ n, N ≤ n → ∀ p, nset.member p q = true →
      (r.at' n).msg_timeout_noqc p v = true := by
    intro n hn p hp
    exact r.mono (P := fun s => s.msg_timeout_noqc p v = true)
      (fun m hm => Mvba.msg_timeout_noqc.mono (r.steps m) p v hm) (hall p hp) n hn
  obtain ⟨n, hn, hfire⟩ :=
    hfj (.form_tc_nolock v q)
      (⟨fun h => h, fun h => h, fun h => h⟩) N
      (fun n hn => enabled_form_tc_nolock hsm (hall' n hn))
  exact hcon (n + 1) (by omega) (form_tc_nolock_effect (hfire ▸ r.steps n))

/-- **`sync_view`'s guards are its enabledness.** -/
theorem enabled_sync_view {i : node} {pv v : view}
    (hi : ¬ nset.is_byz i = true)
    (hin : ∃ E, st.input i E = true)
    (hab : ¬ st.abandoned i = true)
    (hnext : vord.next pv v)
    (htc : st.msg_tc pv = true)
    (hbelow : ∀ V, st.entered i V = true → vord.le V pv) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.sync_view i pv v) := by
  mvba_enabled
  exact ⟨_, hi, hin, hab, hnext, htc, hbelow, rfl⟩

/-- **`sync_view`'s effect**: the next view is entered. -/
theorem sync_view_effect {i : node} {pv v : view}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.sync_view i pv v) st') : st'.entered i v = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  mvba_effect

/-- **The view-advance link.** Given a timeout certificate for `pv`, a
correct validator that has proposed and is not abandoned ends up having
entered some view strictly above `pv`.

The conclusion is stated that way — "some view above `pv`" rather than
"`pv + 1`" — because both outcomes are progress and the guard's failure
gives the first directly: either the validator syncs into `pv + 1`, or it
was already past `pv`, in which case there is nothing to do. -/
theorem eventually_entered_above_of_tc
    (r : MvbaRun th) (hfj : FJustice r)
    {i : node} (hi : ¬ nset.is_byz i = true) {pv v : view} {N : Nat}
    (hnext : vord.next pv v)
    (hnab : ∀ n, N ≤ n → ¬ (r.at' n).abandoned i = true)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (htc : (r.at' N).msg_tc pv = true) :
    ∃ (n : Nat) (V : view), N ≤ n ∧ (r.at' n).entered i V = true ∧ vord.lt pv V := by
  have hlt : vord.lt pv v := ((vord.next_def pv v).mp hnext).1
  by_contra hcon
  push Not at hcon
  have hin' : ∀ n, N ≤ n → (r.at' n).input i E₀ = true :=
    r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin
  have htc' : ∀ n, N ≤ n → (r.at' n).msg_tc pv = true :=
    r.mono (P := fun s => s.msg_tc pv = true)
      (fun m hm => Mvba.msg_tc.mono (r.steps m) pv hm) htc
  -- The anti-monotone guard, and the cleanest case of the pattern: its
  -- failure *is* the conclusion.
  have hbelow : ∀ n, N ≤ n → ∀ V, (r.at' n).entered i V = true → vord.le V pv := by
    intro n hn V hV
    by_contra hnle
    exact hcon n V hn hV (lt_of_not_le hnle)
  obtain ⟨n, hn, hfire⟩ :=
    hfj (.sync_view i pv v)
      (⟨fun h => h, fun h => h, fun h => h⟩) N
      (fun n hn =>
        enabled_sync_view hi ⟨E₀, hin' n hn⟩ (hnab n hn) hnext (htc' n hn) (hbelow n hn))
  exact hcon (n + 1) v (by omega) (sync_view_effect (hfire ▸ r.steps n)) hlt

/-! ## A view is closed only by a correct validator

The fact that makes the honest-led view unskippable, and the one place the
quorum *intersection* axioms are used on the liveness side rather than the
assembly ones. Everything else here assembles quorums; this consumes one.

A timeout certificate for `V` is backed by a `2f+1` quorum of `Timeout`
messages (`msg_tc_backed`, then `tc_nolock_backed` or `tc_lock_backed`).
Every such quorum contains a correct member
(`supermajority_contains_honest_greater_than_third` followed by
`greater_than_third_one_honest`), and a correct validator's `Timeout` for
`V` means it timed out there (`honest_timeout_noqc_timed_out`,
`honest_timeout_qc_timed_out`). So a view cannot be closed behind the
correct validators' backs — which is exactly what lets (A-viewsync) keep a
run inside the good view: it forbids a correct validator timing out there
before deciding, and without one no certificate for that view can exist. -/

/-- **A timeout certificate implies a correct validator timed out.** -/
theorem exists_honest_timed_out_of_tc
    (hr : (Mvba.relationalTransitionSystem node nodeset value view).reachable th st)
    {V : view} (htc : st.msg_tc V = true) :
    ∃ R, ¬ nset.is_byz R = true ∧ st.timed_out R V = true := by
  -- The certificate is one of the two the assemblies build …
  have hq : ∃ q, nset.supermajority q ∧ ∀ p, nset.member p q = true →
      (st.msg_timeout_noqc p V = true ∨ ∃ W' E', st.msg_timeout_qc p V W' E' = true) := by
    rcases Mvba.reachable_msg_tc_backed hr V htc with hnl | ⟨W, E, hlock⟩
    · obtain ⟨q, hsm, hall⟩ := Mvba.reachable_tc_nolock_backed hr V hnl
      exact ⟨q, hsm, fun p hp => Or.inl (hall p hp)⟩
    · obtain ⟨-, -, q, hsm, hall⟩ := Mvba.reachable_tc_lock_backed hr V W E hlock
      refine ⟨q, hsm, fun p hp => ?_⟩
      rcases hall p hp with h | ⟨W', E', h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨W', E', h⟩
  obtain ⟨q, hsm, hall⟩ := hq
  -- … and every `2f+1` quorum contains a correct member.
  obtain ⟨t, hgt, hsub⟩ := nset.supermajority_contains_honest_greater_than_third q hsm
  obtain ⟨R, hRt, hRhon⟩ := nset.greater_than_third_one_honest t hgt
  obtain ⟨hRq, -⟩ := hsub R hRt
  refine ⟨R, (hsub R hRt).2, ?_⟩
  rcases hall R hRq with h | ⟨W', E', h⟩
  · exact Mvba.reachable_honest_timeout_noqc_timed_out hr R V (hsub R hRt).2 h
  · exact Mvba.reachable_honest_timeout_qc_timed_out hr R V W' E' (hsub R hRt).2 h

/-- The same for a lock-carrying certificate, which `sync_view_adopt` reads
instead of `msg_tc`. -/
theorem exists_honest_timed_out_of_tc_lock
    (hr : (Mvba.relationalTransitionSystem node nodeset value view).reachable th st)
    {V W : view} {E : value} (hlock : st.tc_lock V W E = true) :
    ∃ R, ¬ nset.is_byz R = true ∧ st.timed_out R V = true := by
  obtain ⟨-, -, q, hsm, hall⟩ := Mvba.reachable_tc_lock_backed hr V W E hlock
  obtain ⟨t, hgt, hsub⟩ := nset.supermajority_contains_honest_greater_than_third q hsm
  obtain ⟨R, hRt, hRhon⟩ := nset.greater_than_third_one_honest t hgt
  refine ⟨R, (hsub R hRt).2, ?_⟩
  rcases hall R (hsub R hRt).1 with h | ⟨W', E', h, -⟩
  · exact Mvba.reachable_honest_timeout_noqc_timed_out hr R V (hsub R hRt).2 h
  · exact Mvba.reachable_honest_timeout_qc_timed_out hr R V W' E' (hsub R hRt).2 h

/-! ## The good view is not skipped

The induction the two previous sections were for, and the last structural
step before `SettledIn` can be discharged.

**While no correct validator has decided, no correct validator can be in a
view above the honest-led one.** Climbing past a view needs a certificate
for it (`entered_needs_certificate`, the model's one step property), a
certificate needs a correct validator to have timed out there
(`exists_honest_timed_out_of_tc`), and a correct validator timing out in the
good view has, by (A-viewsync), already decided. The induction closes
because a validator only ever times out in a view it has entered
(`timed_out_entered`), so the certificate's view is itself covered by the
induction hypothesis.

Note what this does *not* assume: nothing about how many views there are,
and no ranking. It is a plain induction on the run index. `Rank.lean`'s view
component measures *progress toward* the good view; this says the run cannot
overshoot it, which is the other half and the one (A-viewsync) is for. -/

/-- The initializer enters no view. -/
theorem init_not_entered
    (hinit : (Mvba.relationalTransitionSystem node nodeset value view).init th st)
    (i : node) (V : view) : ¬ st.entered i V = true := by
  simp only [Mvba.relationalTransitionSystem, Mvba.Init] at hinit
  simp only [Mvba.initializer.ext.tr] at hinit
  (repeat (obtain ⟨-, hinit⟩ := hinit))
  mvba_effect

/-- **The good view is not overshot.** If no correct validator ever times
out in `W`, none is ever in a view above it.

The hypothesis used to be "no correct validator ever decides"; weakening
(A-viewsync) to speak of certificates moved that condition into the caller,
and this induction turned out not to need it at all — only that the good
view is never abandoned. -/
theorem entered_le_of_no_timeout
    (r : MvbaRun th) {W : view}
    (hvs : ∀ i n, ¬ nset.is_byz i = true → (r.at' n).timed_out i W = true → False) :
    ∀ (n : Nat) (j : node) (V : view), ¬ nset.is_byz j = true →
      (r.at' n).entered j V = true → vord.le V W := by
  intro n
  induction n with
  | zero => exact fun j V _ hV => absurd hV (init_not_entered r.starts j V)
  | succ n ih =>
    intro j V hj hV
    -- Either the view was already entered — the induction hypothesis — …
    by_cases hprev : (r.at' n).entered j V = true
    · exact ih j V hj hprev
    -- … or this step entered it, and then a certificate for the view below
    -- existed, hence a correct validator had timed out there.
    rcases Mvba.reachable_entered_needs_certificate_step (r.reachable n) (r.steps n)
      j V ⟨hj, hprev, hV⟩ with rfl | ⟨PV, hnext, hcert⟩
    · exact vord.zero_lt W
    have hto : ∃ R, ¬ nset.is_byz R = true ∧ (r.at' n).timed_out R PV = true := by
      rcases hcert with htc | ⟨Wc, Ec, hlock⟩
      · exact exists_honest_timed_out_of_tc (r.reachable n) htc
      · exact exists_honest_timed_out_of_tc_lock (r.reachable n) hlock
    obtain ⟨R, hR, hRto⟩ := hto
    -- That validator had entered `PV`, so `PV ≤ W` by the induction hypothesis …
    have hPV : vord.le PV W :=
      ih R PV hR (Mvba.reachable_timed_out_entered (r.reachable n) R PV hR hRto)
    -- … and `PV = W` is impossible, because it would mean a correct validator
    -- timed out in the good view, which (A-viewsync) allows only after a
    -- decision.
    have hPVne : ¬ PV = W := by
      rintro rfl
      exact hvs R n hR hRto
    -- So `PV < W`, and `V` is the least view above `PV`.
    exact ((vord.next_def PV V).mp hnext).2 W ((vord.le_lt PV W).mpr ⟨hPV, hPVne⟩)

/-! ## `SettledIn`, discharged

Every link above assumed `SettledIn`. Here it is *derived*, and the three
conjuncts come from three different places, which is worth seeing laid out
because it is the whole role of (A-viewsync):

* `¬ abandoned` — from `NoEarlyAbandon`, a caller premise;
* `¬ timed_out i W` — from (A-viewsync)'s second clause. The lemma takes
  that already reduced to "no correct validator times out in `W`", because
  which form the premise has is the caller's business: with the certificate
  form it is the first link that closes the gap, and stating it this way
  keeps the two independent;
* `InView i W` — the hard one, and the only one needing a run-level
  argument. `entered i W` is monotone, so it holds ever after; that *no
  higher view* is entered is `entered_le_of_no_timeout`.

All three are conditioned on the same thing: that no correct validator ever
decides. That is not a limitation but the shape of the eventual proof — the
run-level theorem splits on exactly that, and in the other branch there is a
decision already and nothing to settle. -/

/-- **`SettledIn` from (A-viewsync), while nobody has decided.** -/
theorem settledIn_of_no_decision
    (r : MvbaRun th) {W : view}
    (hvs : ∀ i n, ¬ nset.is_byz i = true → (r.at' n).timed_out i W = true → False)
    (hna : NoEarlyAbandon r)
    (hnodec : ∀ j n E, ¬ nset.is_byz j = true → ¬ (r.at' n).decided j E = true)
    {i : node} (hi : ¬ nset.is_byz i = true) {N : Nat}
    (hentered : (r.at' N).entered i W = true) :
    SettledIn r i W N := by
  have hent : ∀ n, N ≤ n → (r.at' n).entered i W = true :=
    r.mono (P := fun s => s.entered i W = true)
      (fun m hm => Mvba.entered.mono (r.steps m) i W hm) hentered
  refine fun n hn => ⟨⟨hent n hn, ?_⟩, ?_, ?_⟩
  · exact fun V hV => entered_le_of_no_timeout r hvs n i V hi hV
  · exact fun hto => hvs i n hi hto
  · intro hab
    obtain ⟨E, hE⟩ := hna i n hi hab
    exact hnodec i n E hi hE

/-- **The whole honest quorum settled, at one index.** The finite-family lift
once more: each member enters the good view at its own point, and
`eventually_quorum` brings them to a common one — which the view-level
theorem needs, since it starts every member's chain from the same `N`. -/
theorem exists_settled_quorum_of_no_decision
    (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (r : MvbaRun th) {W : view} {q : nodeset}
    (hvs : ∀ i n, ¬ nset.is_byz i = true → (r.at' n).timed_out i W = true → False)
    (hna : NoEarlyAbandon r)
    (hnodec : ∀ j n E, ¬ nset.is_byz j = true → ¬ (r.at' n).decided j E = true)
    (hcorrect : ∀ p, nset.member p q = true → ¬ nset.is_byz p = true)
    (henter : ∀ p, nset.member p q = true → ∃ n, (r.at' n).entered p W = true) :
    ∃ N, ∀ p, nset.member p q = true → SettledIn r p W N := by
  obtain ⟨N, -, hall⟩ :=
    eventually_quorum enum r (fun p s => s.entered p W = true)
      (fun p m hm => Mvba.entered.mono (r.steps m) p W hm)
      (fun p hp => by
        obtain ⟨n, hn⟩ := henter p hp
        exact ⟨max 0 n, Nat.zero_le _,
          r.mono (P := fun s => s.entered p W = true)
            (fun j hj => Mvba.entered.mono (r.steps j) p W hj) hn _
            (Nat.le_max_right 0 n)⟩)
  exact ⟨N, fun p hp => settledIn_of_no_decision r hvs hna hnodec (hcorrect p hp) (hall p hp)⟩

/-! ## Entering a view is evidence that the one below was closed

`terminates_of_good_view` below asked for a timeout certificate under the
good view. It turns out not to need one as a *hypothesis*: (A-viewsync)
already says every correct validator enters the good view, and entering a
view above the first is only possible through `sync_view` or
`sync_view_adopt`, whose guards read that certificate at the pre-state. So
the certificate is a **consequence** of the entry, not a further assumption.

The argument needs the first moment the view was entered — `entered` is
monotone and empty initially, so a least index exists — and there the step
property `entered_needs_certificate` applies.

The same step property, read at the first entry, is what the **climb** uses
in the other direction: `exists_tc_below_of_entered` keeps the certificate in
the shape `sync_view` asks for rather than resolving it into a lock. Those
two lemmas differ only in which of `msg_tc_backed` and `tc_lock_implies_tc`
they apply, and they are stated separately because a reader of either
should not have to carry the other. -/

section Predecessor

variable {view : Type} [vord : TotalOrderWithMinimum view]

/-- A view has at most one immediate predecessor. -/
theorem next_unique {a b c : view} (hab : vord.next a c) (hbc : vord.next b c) :
    a = b := by
  have ha := (vord.next_def a c).mp hab
  have hb := (vord.next_def b c).mp hbc
  have hac := (vord.le_lt a c).mp ha.1
  have hbc' := (vord.le_lt b c).mp hb.1
  rcases vord.le_total a b with hle | hle
  · by_contra hne
    have hlt : vord.lt a b := (vord.le_lt a b).mpr ⟨hle, hne⟩
    exact hbc'.2 (vord.le_antisymm b c hbc'.1 (ha.2 b hlt))
  · by_contra hne
    have hlt : vord.lt b a := (vord.le_lt b a).mpr ⟨hle, fun h => hne h.symm⟩
    exact hac.2 (vord.le_antisymm a c hac.1 (hb.2 a hlt))

/-- Nothing is the immediate predecessor of the least view. -/
theorem not_next_zero {a : view} (h : vord.next a vord.zero) : False := by
  have h1 := (vord.le_lt a vord.zero).mp ((vord.next_def a vord.zero).mp h).1
  exact h1.2 (vord.le_antisymm a vord.zero h1.1 (vord.zero_lt a))

end Predecessor

section Entry

variable {node nodeset value view : Type}
  [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view]
  [nset : ByzNodeSet node nodeset] [vord : TotalOrderWithMinimum view]
  {th : Theory node nodeset value view}

/-- The first moment a view was entered. `entered` is monotone and empty at
the initial state, so a least index exists and has a predecessor. -/
theorem exists_first_entry (r : MvbaRun th) {i : node} {W : view} {n : Nat}
    (hent : (r.at' n).entered i W = true) :
    ∃ m, (r.at' m).entered i W = false ∧ (r.at' (m + 1)).entered i W = true := by
  classical
  have h : ∃ k, (r.at' k).entered i W = true := ⟨n, hent⟩
  have hk := Nat.find_spec h
  rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
  · rw [h0] at hk
    exact absurd hk (init_not_entered r.starts i W)
  · obtain ⟨m, hm⟩ : ∃ m, Nat.find h = m + 1 := ⟨Nat.find h - 1, by omega⟩
    refine ⟨m, ?_, by rw [← hm]; exact hk⟩
    have hmin := Nat.find_min h (m := m) (by omega)
    cases hb : (r.at' m).entered i W with
    | false => rfl
    | true => exact absurd hb hmin

/-- **Entering a view above the first means the one below it was closed**, in
exactly the form the leader link reads: a lock of that view, or a lock-free
certificate for it. -/
theorem exists_justification_below_of_entered
    (r : MvbaRun th) {i : node} (hi : ¬ nset.is_byz i = true) {pv W : view}
    (hnext : vord.next pv W) {n : Nat} (hent : (r.at' n).entered i W = true) :
    ∃ m, (∃ w e, (r.at' m).tc_lock pv w e = true) ∨
      (r.at' m).tc_nolock pv = true := by
  obtain ⟨m, hfalse, htrue⟩ := exists_first_entry r hent
  have hfalse' : ¬ (r.at' m).entered i W = true := by simp [hfalse]
  rcases Mvba.reachable_entered_needs_certificate_step (r.reachable m) (r.steps m)
    i W ⟨hi, hfalse', htrue⟩ with rfl | ⟨PV, hPV, hcert⟩
  · exact absurd hnext not_next_zero
  · have hPVpv : PV = pv := next_unique hPV hnext
    subst hPVpv
    rcases hcert with htc | ⟨w, e, hlock⟩
    · rcases Mvba.reachable_msg_tc_backed (r.reachable m) PV htc with hn | ⟨w, e, h⟩
      · exact ⟨m, Or.inr hn⟩
      · exact ⟨m, Or.inl ⟨w, e, h⟩⟩
    · exact ⟨m, Or.inl ⟨w, e, hlock⟩⟩

/-- **… and in the shape the climb wants**: the bare timeout certificate,
which is what `sync_view` is guarded on.

`exists_justification_below_of_entered` resolves the certificate into its two
shapes because the leader link needs the lock; here the opposite is wanted,
and `tc_lock_implies_tc` — a lock is also a timeout certificate, both set by
the one step of `form_tc_lock` — is what makes the two interchangeable. -/
theorem exists_tc_below_of_entered
    (r : MvbaRun th) {i : node} (hi : ¬ nset.is_byz i = true) {pv W : view}
    (hnext : vord.next pv W) {n : Nat} (hent : (r.at' n).entered i W = true) :
    ∃ m, (r.at' m).msg_tc pv = true := by
  obtain ⟨m, hfalse, htrue⟩ := exists_first_entry r hent
  have hfalse' : ¬ (r.at' m).entered i W = true := by simp [hfalse]
  rcases Mvba.reachable_entered_needs_certificate_step (r.reachable m) (r.steps m)
    i W ⟨hi, hfalse', htrue⟩ with rfl | ⟨PV, hPV, hcert⟩
  · exact absurd hnext not_next_zero
  · have hPVpv : PV = pv := next_unique hPV hnext
    subst hPVpv
    rcases hcert with h | ⟨w, e, h⟩
    · exact ⟨m, h⟩
    · exact ⟨m, Mvba.reachable_tc_lock_implies_tc (r.reachable m) PV w e h⟩

end Entry

/-! ## Monotone growth over a finite list stops

The third use of the covering list, after counting (`residual`) and
maximising (`exists_greatest`), and the one that makes weak fairness usable
where a guard mentions a maximum.

Weak fairness needs a *fixed* label to be continuously enabled. A validator's
`timeout_qc i v w e` names its highest held certificate, so the label moves
whenever a higher one is adopted, and no single label is continuously
enabled while that keeps happening. It cannot keep happening: held
certificates only accumulate, they all lie in the covering list, and a
monotone family over a finite list stops growing. After it stops, the
maximum is fixed and one label stays enabled.

The proof is the `residual` measure again — growth strictly lowers it, so it
can only happen finitely often — and nothing about the protocol enters. -/

/-- **A monotone family over a finite list acquires no new members after
some point.** -/
theorem eventually_no_new (r : MvbaRun th) {α : Type}
    (P : α → Mvba.State (Mvba.FieldAbstractType node nodeset value view) → Prop)
    (hmono : ∀ a n, P a (r.at' n) → P a (r.at' (n + 1))) (Vs : List α) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ m, n ≤ m → ∀ a, a ∈ Vs → P a (r.at' m) → P a (r.at' n) := by
  classical
  intro N
  generalize hk : residual Vs (fun a => P a (r.at' N)) = k
  induction k using Nat.strong_induction_on generalizing N with
  | _ k ih =>
    by_cases hstable : ∀ m, N ≤ m → ∀ a, a ∈ Vs → P a (r.at' m) → P a (r.at' N)
    · exact ⟨N, Nat.le_refl N, hstable⟩
    · push Not at hstable
      obtain ⟨m, hm, a, ha, hPm, hPN⟩ := hstable
      have hlt : residual Vs (fun a => P a (r.at' m)) <
          residual Vs (fun a => P a (r.at' N)) :=
        residual_lt_of_new
          (fun b hb => r.mono (P := fun s => P b s) (fun j hj => hmono b j hj) hb m hm)
          ha hPN hPm
      obtain ⟨n, hn, hstab⟩ := ih (residual Vs (fun a => P a (r.at' m))) (by omega) m rfl
      exact ⟨n, Nat.le_trans hm hn, hstab⟩

/-! ## An expired timer produces a `Timeout`

The step that makes the timer marker pay off, and the first use of both
`exists_greatest` and `eventually_no_new`.

A validator that stays in a view with its timer run out will time out. Which
of the two actions fires depends on whether it holds a certificate, and the
awkward case is that it does: `timeout_qc` names the *highest* one, so the
label moves as certificates are adopted and weak fairness has nothing fixed
to bite on. Both halves of the fix come from the covering list — adoption
stops (`eventually_no_new`, since held certificates accumulate and all lie
below the current view), and once it has, a highest one exists
(`exists_greatest`). From there a single label is continuously enabled and
(F-justice) does the rest. -/

/-- **`timeout_noqc`'s guards are its enabledness.** -/
theorem enabled_timeout_noqc {i : node} {v : view}
    (hi : ¬ nset.is_byz i = true)
    (hin : ∃ E, st.input i E = true)
    (hab : ¬ st.abandoned i = true)
    (hview : InView st i v)
    (htimer : st.timer_expired i v = true)
    (hnto : ¬ st.timed_out i v = true)
    (hno : ∀ W E, ¬ st.local_prepqc i W E = true) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.timeout_noqc i v) := by
  mvba_enabled
  exact ⟨_, hi, hin, hab, hview.1, hview.2, htimer, hnto, hno, rfl⟩

/-- **`timeout_qc`'s guards are its enabledness.** -/
theorem enabled_timeout_qc {i : node} {v w : view} {e : value}
    (hi : ¬ nset.is_byz i = true)
    (hin : ∃ E, st.input i E = true)
    (hab : ¬ st.abandoned i = true)
    (hview : InView st i v)
    (htimer : st.timer_expired i v = true)
    (hnto : ¬ st.timed_out i v = true)
    (hloc : st.local_prepqc i w e = true)
    (hmax : ∀ W E, st.local_prepqc i W E = true → vord.le W w) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.timeout_qc i v w e) := by
  mvba_enabled
  exact ⟨_, hi, hin, hab, hview.1, hview.2, htimer, hnto, hloc, hmax, rfl⟩

theorem timeout_noqc_effect {i : node} {v : view}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.timeout_noqc i v) st') : st'.timed_out i v = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := htr
  mvba_effect

theorem timeout_qc_effect {i : node} {v w : view} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.timeout_qc i v w e) st') : st'.timed_out i v = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := htr
  mvba_effect

/-- **An expired timer produces a `Timeout`.** A correct validator that stays
in view `v`, is not abandoned, and whose timer for `v` has run out, times
out — given a list covering the views at or below `v`, which is what bounds
its held certificates. -/
theorem eventually_timed_out_of_timer
    (r : MvbaRun th) (hfj : FJustice r)
    {i : node} (hi : ¬ nset.is_byz i = true) {v : view} {N : Nat}
    (Vs : List view) (hcov : ∀ V, vord.le V v → V ∈ Vs)
    (hview : ∀ n, N ≤ n → InView (r.at' n) i v)
    (hnab : ∀ n, N ≤ n → ¬ (r.at' n).abandoned i = true)
    {E₀ : value} (hin : (r.at' N).input i E₀ = true)
    (htimer : (r.at' N).timer_expired i v = true) :
    ∃ n, N ≤ n ∧ (r.at' n).timed_out i v = true := by
  classical
  by_contra hcon
  push Not at hcon
  have hin' : ∀ n, N ≤ n → (r.at' n).input i E₀ = true :=
    r.mono (P := fun s => s.input i E₀ = true)
      (fun m hm => Mvba.input.mono (r.steps m) i E₀ hm) hin
  have htimer' : ∀ n, N ≤ n → (r.at' n).timer_expired i v = true :=
    r.mono (P := fun s => s.timer_expired i v = true)
      (fun m hm => Mvba.timer_expired.mono (r.steps m) i v hm) htimer
  -- Every certificate this validator holds is of a view at or below `v`,
  -- hence in the covering list.
  have hheld : ∀ n, N ≤ n → ∀ W E, (r.at' n).local_prepqc i W E = true → W ∈ Vs :=
    fun n hn W E hW => hcov W
      (Mvba.reachable_local_prepqc_within_entered (r.reachable n) i W E v hi hW
        (hview n hn).2)
  -- Adoption stops.
  obtain ⟨n₀, hn₀, hstab⟩ :=
    eventually_no_new r (fun W s => ∃ E, s.local_prepqc i W E = true)
      (fun W m ⟨E, hE⟩ => ⟨E, Mvba.local_prepqc.mono (r.steps m) i W E hE⟩) Vs N
  by_cases hany : ∃ W E, (r.at' n₀).local_prepqc i W E = true
  -- It holds one, so it holds a highest one, and that label stays enabled.
  · obtain ⟨W₀, E₀', hW₀⟩ := hany
    obtain ⟨w, -, ⟨e, he⟩, hmax⟩ :=
      exists_greatest vord.le vord.le_total (fun a b c => vord.le_trans a b c)
        (fun W => ∃ E, (r.at' n₀).local_prepqc i W E = true) Vs W₀
        (hheld n₀ hn₀ W₀ E₀' hW₀) ⟨E₀', hW₀⟩
    obtain ⟨n, hn, hfire⟩ :=
      hfj (.timeout_qc i v w e) ⟨fun h => h, fun h => h, fun h => h⟩ n₀
        (fun n hn =>
          enabled_timeout_qc hi ⟨E₀, hin' n (Nat.le_trans hn₀ hn)⟩
            (hnab n (Nat.le_trans hn₀ hn)) (hview n (Nat.le_trans hn₀ hn))
            (htimer' n (Nat.le_trans hn₀ hn)) (hcon n (Nat.le_trans hn₀ hn))
            (r.mono (P := fun s => s.local_prepqc i w e = true)
              (fun j hj => Mvba.local_prepqc.mono (r.steps j) i w e hj) he n hn)
            (fun W E hWE => hmax W (hheld n (Nat.le_trans hn₀ hn) W E hWE)
              (hstab n hn W (hheld n (Nat.le_trans hn₀ hn) W E hWE) ⟨E, hWE⟩)))
    exact hcon (n + 1) (by omega) (timeout_qc_effect (hfire ▸ r.steps n))
  -- It holds none, and by stability never will.
  · push Not at hany
    obtain ⟨n, hn, hfire⟩ :=
      hfj (.timeout_noqc i v) ⟨fun h => h, fun h => h, fun h => h⟩ n₀
        (fun n hn =>
          enabled_timeout_noqc hi ⟨E₀, hin' n (Nat.le_trans hn₀ hn)⟩
            (hnab n (Nat.le_trans hn₀ hn)) (hview n (Nat.le_trans hn₀ hn))
            (htimer' n (Nat.le_trans hn₀ hn)) (hcon n (Nat.le_trans hn₀ hn))
            (fun W E hWE => by
              obtain ⟨E', hE'⟩ :=
                hstab n hn W (hheld n (Nat.le_trans hn₀ hn) W E hWE) ⟨E, hWE⟩
              exact hany W E' hE'))
    exact hcon (n + 1) (by omega) (timeout_noqc_effect (hfire ▸ r.steps n))

/-! ## Closing a view

The half of the climb that was still open. `eventually_entered_above_of_tc`
advances a validator once a certificate exists; this produces one.

The obstacle is `form_tc_lock`, whose guard names the member carrying the
**highest** certificate — a maximum, where every other assembly in this file
needed only a conjunction. It looked at first as though the maximum might
not exist, since `byz_timeout_qc` lets a Byzantine member carry unboundedly
many certificates and the monotone relations record no bound. That was
wrong, and the reason is worth stating because it is what makes the whole
step cheap: the guard asks each member for *some* carried certificate below
the chosen one, so it is enough to pick **one per member** and maximise over
those. The list of members is finite by `ByzNodeSetEnum`; nothing else needs
to be.

So the selection is an ordinary fold over a list, using only totality and
transitivity of the view order, and it needs no invariant and no
correctness assumption on the members. -/

omit [Inhabited node] [Inhabited nodeset] [Inhabited value] [Inhabited view] nset in
/-- **Either every member sent the lock-free `Timeout`, or one of them
carries a certificate that dominates a choice from every other.** An
induction over the member list; the four cases are the two for the head
crossed with the two for the tail, and the only order reasoning is
`le_total` and `le_trans`. -/
theorem exists_dominating_timeout
    {st : Mvba.State (Mvba.FieldAbstractType node nodeset value view)} {v : view} :
    ∀ (ms : List node), (∀ p ∈ ms, SentTimeout st p v) →
      (∀ p ∈ ms, st.msg_timeout_noqc p v = true) ∨
      ∃ (r₀ : node) (w : view) (e : value), r₀ ∈ ms ∧
        st.msg_timeout_qc r₀ v w e = true ∧
        ∀ p ∈ ms, st.msg_timeout_noqc p v = true ∨
          ∃ W E, st.msg_timeout_qc p v W E = true ∧ vord.le W w
  | [], _ => Or.inl (by simp)
  | a :: ms, h => by
    have htail := exists_dominating_timeout ms (fun p hp => h p (by simp [hp]))
    rcases h a (by simp) with hna | ⟨wa, ea, hqa⟩
    · rcases htail with hall | ⟨r₀, w, e, hr₀, hq₀, hdom⟩
      · exact Or.inl (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp' <;> [exact hna; exact hall p hp'])
      · refine Or.inr ⟨r₀, w, e, by simp [hr₀], hq₀, fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp' <;> [exact Or.inl hna; exact hdom p hp']
    · rcases htail with hall | ⟨r₀, w, e, hr₀, hq₀, hdom⟩
      · refine Or.inr ⟨a, wa, ea, by simp, hqa, fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact Or.inr ⟨wa, ea, hqa, vord.le_refl wa⟩
        · exact Or.inl (hall p hp')
      · rcases vord.le_total wa w with hle | hle
        · refine Or.inr ⟨r₀, w, e, by simp [hr₀], hq₀, fun p hp => ?_⟩
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact Or.inr ⟨wa, ea, hqa, hle⟩
          · exact hdom p hp'
        · refine Or.inr ⟨a, wa, ea, by simp, hqa, fun p hp => ?_⟩
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact Or.inr ⟨wa, ea, hqa, vord.le_refl wa⟩
          · rcases hdom p hp' with hn | ⟨W, E, hW, hWle⟩
            · exact Or.inl hn
            · exact Or.inr ⟨W, E, hW, vord.le_trans W w wa hWle hle⟩

/-- **`form_tc_lock`'s guards are its enabledness.** -/
theorem enabled_form_tc_lock {v : view} {q : nodeset} {r₀ : node} {w : view} {e : value}
    (hsm : nset.supermajority q) (hmem : nset.member r₀ q = true)
    (hqc : st.msg_timeout_qc r₀ v w e = true)
    (hpq : st.msg_prepqc w e = true) (hle : vord.le w v)
    (hdom : ∀ p, nset.member p q = true → st.msg_timeout_noqc p v = true ∨
      ∃ W E, st.msg_timeout_qc p v W E = true ∧ vord.le W w) :
    Enabled (Mvba.relationalTransitionSystem node nodeset value view) th st
      (.form_tc_lock v q r₀ w e) := by
  mvba_enabled
  exact ⟨_, hsm, hmem, hqc, hpq, hle, hdom, rfl⟩

theorem form_tc_lock_effect {v : view} {q : nodeset} {r₀ : node} {w : view} {e : value}
    (htr : (Mvba.relationalTransitionSystem node nodeset value view).tr th st
      (.form_tc_lock v q r₀ w e) st') : st'.msg_tc v = true := by
  mvba_tr htr
  obtain ⟨-, -, -, -, -, -, rfl⟩ := htr
  mvba_effect

/-- **A view all of whose quorum members have timed out gets closed.** The
two assemblies together: whichever of them the timeouts allow, weak fairness
fires it. This is the missing half of the climb — `eventually_entered_above_of_tc`
supplies the other. -/
theorem eventually_tc_of_timed_out_quorum
    (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (r : MvbaRun th) (hfj : FJustice r)
    {N : Nat} {v : view} {q : nodeset} (hsm : nset.supermajority q)
    (hto : ∀ p, nset.member p q = true → SentTimeout (r.at' N) p v) :
    ∃ n, N ≤ n ∧ (r.at' n).msg_tc v = true := by
  rcases exists_dominating_timeout (enum.members q)
      (fun p hp => hto p ((enum.mem_members p q).mpr hp)) with hall | ⟨r₀, w, e, hr₀, hq₀, hdom⟩
  -- No lock anywhere: the lock-free assembly applies.
  · exact eventually_tc_of_timeout_quorum r hfj hsm
      (fun p hp => hall p ((enum.mem_members p q).mp hp))
  -- Otherwise the dominating member is `form_tc_lock`'s `r₀`.
  · by_contra hcon
    push Not at hcon
    have hmono : ∀ (P : Mvba.State (Mvba.FieldAbstractType node nodeset value view) → Prop),
        (∀ m, P (r.at' m) → P (r.at' (m + 1))) → P (r.at' N) → ∀ n, N ≤ n → P (r.at' n) :=
      fun P hp hPN n hn => r.mono (P := P) hp hPN n hn
    have hq₀' := hmono (fun s => s.msg_timeout_qc r₀ v w e = true)
      (fun m hm => Mvba.msg_timeout_qc.mono (r.steps m) r₀ v w e hm) hq₀
    have hpq : (r.at' N).msg_prepqc w e = true :=
      Mvba.reachable_timeout_qc_backed (r.reachable N) r₀ v w e hq₀
    have hpq' := hmono (fun s => s.msg_prepqc w e = true)
      (fun m hm => Mvba.msg_prepqc.mono (r.steps m) w e hm) hpq
    have hle : vord.le w v :=
      Mvba.reachable_timeout_qc_view_le (r.reachable N) r₀ v w e hq₀
    obtain ⟨n, hn, hfire⟩ :=
      hfj (.form_tc_lock v q r₀ w e)
        (⟨fun h => h, fun h => h, fun h => h⟩) N
        (fun n hn =>
          enabled_form_tc_lock hsm ((enum.mem_members r₀ q).mpr hr₀) (hq₀' n hn)
            (hpq' n hn) hle (fun p hp => by
              rcases hdom p ((enum.mem_members p q).mp hp) with hnq | ⟨W, E, hW, hWle⟩
              · exact Or.inl (hmono (fun s => s.msg_timeout_noqc p v = true)
                  (fun m hm => Mvba.msg_timeout_noqc.mono (r.steps m) p v hm) hnq n hn)
              · exact Or.inr ⟨W, E, hmono (fun s => s.msg_timeout_qc p v W E = true)
                  (fun m hm => Mvba.msg_timeout_qc.mono (r.steps m) p v W E hm) hW n hn,
                  hWle⟩))
    exact hcon (n + 1) (by omega) (form_tc_lock_effect (hfire ▸ r.steps n))

/-! ## Reaching the good view

The longest argument in the file, and what turns (A-viewsync) from a
synchronisation assumption into a statement about timers. Everything above
either fixed the good view or assumed it had been entered; this derives the
entry.

**Why it is not one more eventuality.** Nothing moves a validator forward
except a timeout certificate for the view below it, and a certificate needs
a *quorum* to have timed out in **one common view**. So the argument is
about the honest quorum as a body, and it runs on a measure — how many of
the covered views the quorum has entered, which only grows and is bounded:

1. every member has entered view 1 (`input_implies_entered`, from the
   participation premise: having proposed *is* being in view 1);
2. let `M` be the highest view any member has reached — `exists_greatest`
   over the covering list, since a total order gives no maximum by itself;
3. if `M` is the good view, the certificate below it already exists
   (`exists_tc_below_of_entered`) and there is nothing left to do;
4. otherwise either some member reaches a view no member had reached, which
   **lowers the measure**, or no member ever does — in which case the quorum
   is pinned at `M` for ever, and that is refuted: everyone catches up to `M`
   through the certificate that opened it, their timers run out (the first
   clause of (A-viewsync), available because `M` is strictly *below* the
   good view), they all time out, the view closes, and somebody leaves it.

The good view's own clause enters upstream of all of this, as `hto`: no
correct validator ever times out in `W`. That is what bounds the whole run
at or below `W` (`entered_le_of_no_timeout`) and so keeps `M` inside the
covering list — and it is also why nobody can *skip* the good view on the
way past.

**What the view order has to supply** is
[`ViewOrder.lean`](../ViewOrder.lean): successors exist, and the views below
one are finitely many. Neither is in `TotalOrderWithMinimum`. The first is
not a proof convenience — `sync_view` is guarded on `vord.next pv v`, so a
view with nothing directly above it is a view no validator can leave. -/

/-- **A measure that can always be lowered while the goal is unmet reaches
it.** Pure arithmetic on a sequence of naturals: no run and no protocol,
which is the point — the climbing argument stays separate from whatever
makes each individual step possible. -/
theorem eventually_of_measure (μ : Nat → Nat) (G : Nat → Prop)
    (hstep : ∀ N, ∃ n, N ≤ n ∧ (G n ∨ μ n < μ N)) : ∀ N, ∃ n, N ≤ n ∧ G n := by
  intro N
  generalize hk : μ N = k
  induction k using Nat.strong_induction_on generalizing N with
  | _ k ih =>
    obtain ⟨n, hn, h⟩ := hstep N
    rcases h with hG | hlt
    · exact ⟨n, hn, hG⟩
    · obtain ⟨m, hm, hG⟩ := ih (μ n) (by omega) n rfl
      exact ⟨m, Nat.le_trans hn hm, hG⟩

/-- **The view below the good one gets a timeout certificate.** The climb
itself, by the measure described above. -/
theorem eventually_tc_below_good
    (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (hqe : Cadence.ByzNodeSetHonestQuorum node nodeset nset)
    (vfin : Cadence.ViewOrderEnum view vord)
    (r : MvbaRun th) (hfj : FJustice r) (hap : AllPropose r)
    {W PV : view} (hnext : vord.next PV W)
    (hnab : ∀ (i : node) (n : Nat), ¬ nset.is_byz i = true →
      ¬ (r.at' n).abandoned i = true)
    (hto : ∀ (i : node) (n : Nat), ¬ nset.is_byz i = true →
      (r.at' n).timed_out i W = true → False)
    (hftimer : ∀ (i : node) (V : view), ¬ nset.is_byz i = true → vord.lt V W →
      (∃ n, (r.at' n).entered i V = true) →
        ∃ n, (r.at' n).timer_expired i V = true) :
    ∃ n, (r.at' n).msg_tc PV = true := by
  classical
  have hQc := hqe.honestQuorum_correct
  have hQs := hqe.honestQuorum_supermajority
  have hcov : ∀ V, vord.le V W → V ∈ vfin.below W := vfin.mem_below W
  have hle : ∀ (n : Nat) (j : node) (V : view), ¬ nset.is_byz j = true →
      (r.at' n).entered j V = true → vord.le V W := entered_le_of_no_timeout r hto
  obtain ⟨R₀, hR₀⟩ :=
    nset.greater_than_third_one_honest hqe.honestQuorum
      (nset.supermajority_greater_than_third _ hQs)
  -- The measure: covered views no member of the honest quorum has entered.
  set P : Nat → view → Prop :=
    fun n U => ∃ p, nset.member p hqe.honestQuorum = true ∧ (r.at' n).entered p U = true
    with hP
  have hPmono : ∀ {m n : Nat}, m ≤ n → ∀ U, P m U → P n U := by
    rintro m n hmn U ⟨p, hp, hU⟩
    exact ⟨p, hp, r.mono (P := fun s => s.entered p U = true)
      (fun j hj => Mvba.entered.mono (r.steps j) p U hj) hU n hmn⟩
  have hstep : ∀ N, ∃ n, N ≤ n ∧ ((r.at' n).msg_tc PV = true ∨
      residual (vfin.below W) (P n) < residual (vfin.below W) (P N)) := by
    intro N
    -- Every member has entered view 1, at one index.
    obtain ⟨N₁, hN₁, hzero⟩ :=
      eventually_quorum enum r (N := N) (fun p s => s.entered p vord.zero = true)
        (fun p m hm => Mvba.entered.mono (r.steps m) p vord.zero hm)
        (fun p hp => by
          obtain ⟨m, E, hm⟩ := hap p (hQc p hp)
          exact ⟨max N m, Nat.le_max_left N m,
            Mvba.reachable_input_implies_entered (r.reachable _) p E (hQc p hp)
              (r.mono (P := fun s => s.input p E = true)
                (fun j hj => Mvba.input.mono (r.steps j) p E hj) hm _
                (Nat.le_max_right N m))⟩)
    -- The greatest view any member has entered there.
    obtain ⟨M, hMmem, hMent, hMmax⟩ :=
      exists_greatest vord.le vord.le_total (fun a b c => vord.le_trans a b c)
        (P N₁) (vfin.below W) vord.zero (hcov vord.zero (vord.zero_lt W))
        ⟨R₀, hR₀.1, hzero R₀ hR₀.1⟩
    obtain ⟨pM, hpMq, hpM⟩ := hMent
    by_cases hMW : M = W
    -- A member is already in the good view: the certificate below it exists.
    · subst hMW
      obtain ⟨m, hm⟩ := exists_tc_below_of_entered r (hQc pM hpMq) hnext hpM
      exact ⟨max N₁ m, Nat.le_trans hN₁ (Nat.le_max_left _ _),
        Or.inl (r.mono (P := fun s => s.msg_tc PV = true)
          (fun j hj => Mvba.msg_tc.mono (r.steps j) PV hj) hm _
          (Nat.le_max_right _ _))⟩
    · have hMltW : vord.lt M W :=
        (vord.le_lt M W).mpr ⟨hle N₁ pM M (hQc pM hpMq) hpM, hMW⟩
      by_cases hup : ∃ (n : Nat) (U : view) (p : node), N₁ ≤ n ∧ U ∈ vfin.below W ∧
          nset.member p hqe.honestQuorum = true ∧ (r.at' n).entered p U = true ∧
          ∀ p', nset.member p' hqe.honestQuorum = true →
            ¬ (r.at' N₁).entered p' U = true
      -- Someone reached a view no member had: the measure fell.
      · obtain ⟨n, U, p, hn, hU, hp, hent, hnew⟩ := hup
        refine ⟨n, Nat.le_trans hN₁ hn, Or.inr ?_⟩
        exact Nat.lt_of_lt_of_le
          (residual_lt_of_new (hPmono hn) hU (fun ⟨p', hp', h'⟩ => hnew p' hp' h')
            ⟨p, hp, hent⟩)
          (residual_le (hPmono hN₁) (vfin.below W))
      -- Nobody ever does — which the rest of this branch refutes.
      · push Not at hup
        exfalso
        have hbound : ∀ n, N₁ ≤ n → ∀ p, nset.member p hqe.honestQuorum = true →
            ∀ U, (r.at' n).entered p U = true → vord.le U M := by
          intro n hn p hp U hU
          have hUVs : U ∈ vfin.below W := hcov U (hle n p U (hQc p hp) hU)
          obtain ⟨p', hp', h'⟩ := hup n U p hn hUVs hp hU
          exact hMmax U hUVs ⟨p', hp', h'⟩
        -- Every member catches up to `M`, through the certificate that
        -- opened it.
        have hcatch : ∃ N₂, N₁ ≤ N₂ ∧
            ∀ p, nset.member p hqe.honestQuorum = true →
              (r.at' N₂).entered p M = true := by
          obtain ⟨m₀, hm₀f, hm₀t⟩ := exists_first_entry r hpM
          have hm₀f' : ¬ (r.at' m₀).entered pM M = true := by simp [hm₀f]
          rcases Mvba.reachable_entered_needs_certificate_step (r.reachable m₀)
              (r.steps m₀) pM M ⟨hQc pM hpMq, hm₀f', hm₀t⟩ with rfl | ⟨PM, hPM, hc⟩
          · exact ⟨N₁, Nat.le_refl _, hzero⟩
          · have htc : (r.at' m₀).msg_tc PM = true := by
              rcases hc with h | ⟨w, e, h⟩
              · exact h
              · exact Mvba.reachable_tc_lock_implies_tc (r.reachable m₀) PM w e h
            refine eventually_quorum enum r (N := N₁)
              (fun p s => s.entered p M = true)
              (fun p m hm => Mvba.entered.mono (r.steps m) p M hm) (fun p hp => ?_)
            obtain ⟨mp, Ep, hmp⟩ := hap p (hQc p hp)
            obtain ⟨n, V, hn, hV, hlt⟩ :=
              eventually_entered_above_of_tc r hfj (hQc p hp)
                (N := max (max N₁ m₀) mp) hPM
                (fun n _ => hnab p n (hQc p hp))
                (r.mono (P := fun s => s.input p Ep = true)
                  (fun j hj => Mvba.input.mono (r.steps j) p Ep hj) hmp _
                  (Nat.le_max_right _ _))
                (r.mono (P := fun s => s.msg_tc PM = true)
                  (fun j hj => Mvba.msg_tc.mono (r.steps j) PM hj) htc _
                  (Nat.le_trans (Nat.le_max_right N₁ m₀) (Nat.le_max_left _ _)))
            have hNn : N₁ ≤ n :=
              Nat.le_trans (Nat.le_trans (Nat.le_max_left N₁ m₀) (Nat.le_max_left _ _)) hn
            exact ⟨n, hNn, vord.le_antisymm V M (hbound n hNn p hp V hV)
              (((vord.next_def PM M).mp hPM).2 V hlt) ▸ hV⟩
        obtain ⟨N₂, hN₂, hentM⟩ := hcatch
        -- `M` is their current view from then on.
        have hview : ∀ p, nset.member p hqe.honestQuorum = true →
            ∀ n, N₂ ≤ n → InView (r.at' n) p M := by
          intro p hp n hn
          exact ⟨r.mono (P := fun s => s.entered p M = true)
            (fun j hj => Mvba.entered.mono (r.steps j) p M hj) (hentM p hp) n hn,
            fun V hV => hbound n (Nat.le_trans hN₂ hn) p hp V hV⟩
        -- Their timers run out — the clause of (A-viewsync) that covers
        -- the views below the good one, and `M` is one of them.
        obtain ⟨N₃, hN₃, htimer⟩ :=
          eventually_quorum enum r (N := N₂) (fun p s => s.timer_expired p M = true)
            (fun p m hm => Mvba.timer_expired.mono (r.steps m) p M hm)
            (fun p hp => by
              obtain ⟨n, hn⟩ := hftimer p M (hQc p hp) hMltW ⟨N₂, hentM p hp⟩
              exact ⟨max N₂ n, Nat.le_max_left _ _,
                r.mono (P := fun s => s.timer_expired p M = true)
                  (fun j hj => Mvba.timer_expired.mono (r.steps j) p M hj) hn _
                  (Nat.le_max_right _ _)⟩)
        -- … so they all time out …
        obtain ⟨N₄, hN₄, hsent⟩ :=
          eventually_quorum enum r (N := N₃) (fun p s => SentTimeout s p M)
            (fun p m hm => by
              rcases hm with h | ⟨w, e, h⟩
              · exact Or.inl (Mvba.msg_timeout_noqc.mono (r.steps m) p M h)
              · exact Or.inr ⟨w, e, Mvba.msg_timeout_qc.mono (r.steps m) p M w e h⟩)
            (fun p hp => by
              obtain ⟨mp, Ep, hmp⟩ := hap p (hQc p hp)
              obtain ⟨n, hn, hti⟩ :=
                eventually_timed_out_of_timer r hfj (hQc p hp) (N := max N₃ mp)
                  (vfin.below W)
                  (fun V hV => hcov V (vord.le_trans V M W hV
                    ((vord.le_lt M W).mp hMltW).1))
                  (fun n hn => hview p hp n
                    (Nat.le_trans hN₃ (Nat.le_trans (Nat.le_max_left _ _) hn)))
                  (fun n _ => hnab p n (hQc p hp))
                  (r.mono (P := fun s => s.input p Ep = true)
                    (fun j hj => Mvba.input.mono (r.steps j) p Ep hj) hmp _
                    (Nat.le_max_right _ _))
                  (r.mono (P := fun s => s.timer_expired p M = true)
                    (fun j hj => Mvba.timer_expired.mono (r.steps j) p M hj)
                    (htimer p hp) _ (Nat.le_max_left _ _))
              exact ⟨n, Nat.le_trans (Nat.le_max_left _ _) hn,
                Mvba.reachable_timed_out_implies_message (r.reachable n) p M
                  (hQc p hp) hti⟩)
        -- … the view closes …
        obtain ⟨N₅, hN₅, htc⟩ :=
          eventually_tc_of_timed_out_quorum enum r hfj hQs hsent
        -- … and somebody leaves it, which the bound forbids.
        obtain ⟨mp, Ep, hmp⟩ := hap R₀ hR₀.2
        obtain ⟨n, V, hn, hV, hlt⟩ :=
          eventually_entered_above_of_tc r hfj hR₀.2 (N := max N₅ mp)
            (vfin.next_succ M)
            (fun n _ => hnab R₀ n hR₀.2)
            (r.mono (P := fun s => s.input R₀ Ep = true)
              (fun j hj => Mvba.input.mono (r.steps j) R₀ Ep hj) hmp _
              (Nat.le_max_right _ _))
            (r.mono (P := fun s => s.msg_tc M = true)
              (fun j hj => Mvba.msg_tc.mono (r.steps j) M hj) htc _
              (Nat.le_max_left _ _))
        have hNn : N₁ ≤ n :=
          Nat.le_trans hN₂ (Nat.le_trans hN₃ (Nat.le_trans hN₄ (Nat.le_trans hN₅
            (Nat.le_trans (Nat.le_max_left _ _) hn))))
        exact ((vord.le_lt M V).mp hlt).2
          (vord.le_antisymm M V ((vord.le_lt M V).mp hlt).1
            (hbound n hNn R₀ hR₀.1 V hV))
  obtain ⟨n, -, hn⟩ :=
    eventually_of_measure (fun n => residual (vfin.below W) (P n))
      (fun n => (r.at' n).msg_tc PV = true) hstep 0
  exact ⟨n, hn⟩

/-- **Every correct validator enters the good view.** What (A-viewsync) used
to assume, in one step from the certificate below it: a validator that has
proposed advances past `PV`, and it cannot advance further than `W`, because
that would need a correct validator to have timed out there. -/
theorem eventually_entered_good
    (r : MvbaRun th) (hfj : FJustice r) (hap : AllPropose r)
    {W PV : view} (hnext : vord.next PV W)
    (hnab : ∀ (i : node) (n : Nat), ¬ nset.is_byz i = true →
      ¬ (r.at' n).abandoned i = true)
    (hto : ∀ (i : node) (n : Nat), ¬ nset.is_byz i = true →
      (r.at' n).timed_out i W = true → False)
    (htc : ∃ n, (r.at' n).msg_tc PV = true) :
    ∀ i, ¬ nset.is_byz i = true → ∃ n, (r.at' n).entered i W = true := by
  intro i hi
  obtain ⟨m, hm⟩ := htc
  obtain ⟨mp, E, hmp⟩ := hap i hi
  obtain ⟨n, V, hn, hV, hlt⟩ :=
    eventually_entered_above_of_tc r hfj hi (N := max m mp) hnext
      (fun n _ => hnab i n hi)
      (r.mono (P := fun s => s.input i E = true)
        (fun j hj => Mvba.input.mono (r.steps j) i E hj) hmp _ (Nat.le_max_right _ _))
      (r.mono (P := fun s => s.msg_tc PV = true)
        (fun j hj => Mvba.msg_tc.mono (r.steps j) PV hj) hm _ (Nat.le_max_left _ _))
  exact ⟨n, vord.le_antisymm V W (entered_le_of_no_timeout r hto n i V hi hV)
    (((vord.next_def PV W).mp hnext).2 V hlt) ▸ hV⟩

/-! ## The assembly

Everything above, in one theorem: **if a run reaches an honest-led view with
a timeout certificate below it, every correct validator decides.**

The proof is a dichotomy, and both branches are already built.

* *Some correct validator has decided.* Then `decided_backed` turns that into
  a commit certificate, and the very first link —
  `eventually_decided_of_commitqc` — carries it to every correct validator.
  No view reasoning at all.
* *None has.* Then `SettledIn` is available for the honest quorum and for
  the leader, the leader proposes, its proposal is one the handlers accept
  (`honest_preprepare_valid`, `honest_preprepare_justified`), and
  `terminates_of_settled_honest_view` concludes — which contradicts the
  branch's own assumption, since the honest quorum is non-empty. So this
  branch is vacuous, which is the right outcome: a run that reaches a good
  view cannot fail to decide.

Neither the entry into the good view nor the certificate below it is a
hypothesis. The entry is `eventually_entered_good`, the section above; the
certificate follows from it, because entering `W` is only possible through
one (`exists_justification_below_of_entered`). What separates this from
`TerminationClaim` is therefore only the shape of (A-viewsync) itself — the
claim quantifies over runs and this theorem takes the good view and its
leader as arguments. -/

theorem terminates_of_good_view
    (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (hqe : Cadence.ByzNodeSetHonestQuorum node nodeset nset)
    (vfin : Cadence.ViewOrderEnum view vord)
    (r : MvbaRun th) (hfj : FJustice r) (hav : FAvail r) (hna : NoEarlyAbandon r)
    (hap : AllPropose r)
    {W : view} {l : node} {pv : view}
    (hlead : th.leader W l = true) (hl : ¬ nset.is_byz l = true)
    (hnext : vord.next pv W)
    (hftimer : ∀ (i : node) (V : view), ¬ nset.is_byz i = true → vord.lt V W →
      (∃ n, (r.at' n).entered i V = true) →
        ∃ n, (r.at' n).timer_expired i V = true)
    (hnto : ∀ i n, ¬ nset.is_byz i = true → (r.at' n).timer_expired i W = true →
      ∃ (V : view) (E : value), (r.at' n).msg_commitqc V E = true) :
    Terminates r := by
  by_cases hdec : ∃ (j : node) (n : Nat) (E : value),
      ¬ nset.is_byz j = true ∧ (r.at' n).decided j E = true
  -- Branch one: a decision already exists, so a certificate does.
  · obtain ⟨j, nj, Ej, hj, hEj⟩ := hdec
    obtain ⟨V, hV⟩ := Mvba.reachable_decided_backed (r.reachable nj) j Ej hj hEj
    intro i hi
    obtain ⟨m, E, hm⟩ := hap i hi
    exact eventually_decided_of_commitqc r hfj hna hi
      (r.mono (P := fun s => s.input i E = true)
        (fun k hk => Mvba.input.mono (r.steps k) i E hk) hm _ (Nat.le_max_left m nj))
      (r.mono (P := fun s => s.msg_commitqc V Ej = true)
        (fun k hk => Mvba.msg_commitqc.mono (r.steps k) V Ej hk) hV _
        (Nat.le_max_right m nj))
  -- Branch two: nobody has decided — which the good view makes impossible.
  · push Not at hdec
    have hnodec : ∀ j n E, ¬ nset.is_byz j = true → ¬ (r.at' n).decided j E = true :=
      fun j n E hj => hdec j n E hj
    -- (A-viewsync) gives a *certificate* where the argument below wants a
    -- contradiction; the first link bridges the two, and needs only
    -- (F-justice). This is the whole reason the premise can be the weaker
    -- of the two forms.
    have hto : ∀ i n, ¬ nset.is_byz i = true →
        (r.at' n).timed_out i W = true → False := by
      intro i n hi hti
      -- The premise speaks of the timer; the model says a validator that has
      -- timed out had one that ran out.
      obtain ⟨V, E, hV⟩ :=
        hnto i n hi (Mvba.reachable_timed_out_implies_timer (r.reachable n) i W hi hti)
      obtain ⟨m, E₀, hm⟩ := hap i hi
      obtain ⟨k, Ek, hk⟩ :=
        eventually_decided_of_commitqc r hfj hna hi
          (r.mono (P := fun s => s.input i E₀ = true)
            (fun j hj => Mvba.input.mono (r.steps j) i E₀ hj) hm _ (Nat.le_max_left m n))
          (r.mono (P := fun s => s.msg_commitqc V E = true)
            (fun j hj => Mvba.msg_commitqc.mono (r.steps j) V E hj) hV _
            (Nat.le_max_right m n))
      exact hnodec i k Ek hi hk
    -- Nobody is abandoned either, for the same reason.
    have hnab : ∀ (i : node) (n : Nat), ¬ nset.is_byz i = true →
        ¬ (r.at' n).abandoned i = true := by
      intro i n hi hab
      obtain ⟨E, hE⟩ := hna i n hi hab
      exact hnodec i n E hi hE
    -- The good view is *reached*, not assumed.
    have henter : ∀ i, ¬ nset.is_byz i = true →
        ∃ n, (r.at' n).entered i W = true :=
      eventually_entered_good r hfj hap hnext hnab hto
        (eventually_tc_below_good enum hqe vfin r hfj hap hnext hnab hto hftimer)
    -- The honest quorum, settled at one index.
    obtain ⟨Nq, hq⟩ :=
      exists_settled_quorum_of_no_decision enum r hto hna hnodec
        hqe.honestQuorum_correct
        (fun p hp => henter p (hqe.honestQuorum_correct p hp))
    -- The leader, settled at its own.
    obtain ⟨Nl, hNl⟩ := henter l hl
    -- The certificate below the good view is not assumed: entering `W` is
    -- only possible through it.
    obtain ⟨Nt, hNt⟩ := exists_justification_below_of_entered r hl hnext hNl
    -- One index for all three.
    have h1 : Nq ≤ max Nq (max Nl Nt) := Nat.le_max_left _ _
    have h2 : Nl ≤ max Nq (max Nl Nt) :=
      Nat.le_trans (Nat.le_max_left Nl Nt) (Nat.le_max_right _ _)
    have h3 : Nt ≤ max Nq (max Nl Nt) :=
      Nat.le_trans (Nat.le_max_right Nl Nt) (Nat.le_max_right _ _)
    have hsl : SettledIn r l W (max Nq (max Nl Nt)) :=
      settledIn_of_no_decision r hto hna hnodec hl
        (r.mono (P := fun s => s.entered l W = true)
          (fun k hk => Mvba.entered.mono (r.steps k) l W hk) hNl _ h2)
    -- Carried forward to the common index, monotonically.
    have hjust : (∃ w e, (r.at' (max Nq (max Nl Nt))).tc_lock pv w e = true) ∨
        (r.at' (max Nq (max Nl Nt))).tc_nolock pv = true := by
      rcases hNt with ⟨w, e, h⟩ | h
      · exact Or.inl ⟨w, e, r.mono (P := fun s => s.tc_lock pv w e = true)
          (fun k hk => Mvba.tc_lock.mono (r.steps k) pv w e hk) h _ h3⟩
      · exact Or.inr (r.mono (P := fun s => s.tc_nolock pv = true)
          (fun k hk => Mvba.tc_nolock.mono (r.steps k) pv hk) h _ h3)
    -- The leader proposes, and what it proposes the handlers accept.
    obtain ⟨n₀, E₀, hn₀, hpp⟩ :=
      eventually_preprepare_of_settled_leader r hfj hl hsl hnext hlead hjust
    have hvalid : th.valid E₀ = true :=
      Mvba.reachable_honest_preprepare_valid (r.reachable n₀) l W E₀ hl hpp
    have hjust₀ : (∃ w, (r.at' n₀).tc_lock pv w E₀ = true) ∨
        (r.at' n₀).tc_nolock pv = true :=
      Mvba.reachable_honest_preprepare_justified (r.reachable n₀) l W E₀ pv hl hpp hnext
    -- The view decides — contradicting this branch.
    have hterm : Terminates r :=
      terminates_of_settled_honest_view enum r hfj hav hna hqe hap hl hnext hlead hpp
        hvalid hjust₀
        (fun p hp => (hq p hp).later (Nat.le_trans h1 hn₀))
    obtain ⟨R, hRq⟩ :=
      nset.greater_than_third_one_honest hqe.honestQuorum
        (nset.supermajority_greater_than_third _ hqe.honestQuorum_supermajority)
    obtain ⟨nR, ER, hR⟩ := hterm R hRq.2
    exact absurd hR (hnodec R nR ER hRq.2)

/-! ## The claim, proven

`TerminationClaim` was written down before any of its proof existed, so that
its premises were fixed in advance rather than discovered. Here it is
discharged.

Everything it needs is above, and what this adds is only the unpacking —
which is now literal, every clause of (A-viewsync) going straight to the
argument of the same name. The three hypotheses the claim does not mention
are the two quorum classes and the view order's, exactly as the header
says. -/

theorem termination
    (enum : Cadence.ByzNodeSetEnum node nodeset nset)
    (hqe : Cadence.ByzNodeSetHonestQuorum node nodeset nset)
    (vfin : Cadence.ViewOrderEnum view vord) :
    TerminationClaim th := by
  rintro r hfj ⟨W, PV, l, hnext, hlead, hl, hftimer, hnto⟩ hav hap hna
  exact terminates_of_good_view enum hqe vfin r hfj hav hna hap hlead hl hnext
    hftimer hnto

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

/--
info: 'Mvba.label_classified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
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

/--
info: 'Mvba.terminates_of_settled_honest_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.terminates_of_settled_honest_view

/--
info: 'Mvba.eventually_preprepare_of_settled_leader' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_preprepare_of_settled_leader

/--
info: 'Mvba.eventually_entered_above_of_tc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_entered_above_of_tc

/--
info: 'Mvba.entered_le_of_no_timeout' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.entered_le_of_no_timeout

/--
info: 'Mvba.exists_settled_quorum_of_no_decision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.exists_settled_quorum_of_no_decision

/--
info: 'Mvba.terminates_of_good_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.terminates_of_good_view

/--
info: 'Mvba.termination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.termination

/--
info: 'Mvba.eventually_of_measure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_of_measure

/--
info: 'Mvba.exists_tc_below_of_entered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.exists_tc_below_of_entered

/--
info: 'Mvba.eventually_tc_below_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_tc_below_good

/--
info: 'Mvba.eventually_entered_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_entered_good

/--
info: 'Mvba.eventually_tc_of_timed_out_quorum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.eventually_tc_of_timed_out_quorum
