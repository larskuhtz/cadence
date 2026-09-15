import Cadence.Mvba.Proofs.Init
import Cadence.Mvba.Proofs.Propose
import Cadence.Mvba.Proofs.Abandon
import Cadence.Mvba.Proofs.LeaderProposeFirst
import Cadence.Mvba.Proofs.LeaderRepropose
import Cadence.Mvba.Proofs.LeaderProposeFresh
import Cadence.Mvba.Proofs.HandlePreprepareFirst
import Cadence.Mvba.Proofs.HandlePreprepare
import Cadence.Mvba.Proofs.FormPrepqc
import Cadence.Mvba.Proofs.AdoptPrepqc
import Cadence.Mvba.Proofs.BecomeAvailReady
import Cadence.Mvba.Proofs.SendCommit
import Cadence.Mvba.Proofs.FormCommitqc
import Cadence.Mvba.Proofs.Decide
import Cadence.Mvba.Proofs.TimeoutQc
import Cadence.Mvba.Proofs.TimeoutNoqc
import Cadence.Mvba.Proofs.FormTcLock
import Cadence.Mvba.Proofs.FormTcNolock
import Cadence.Mvba.Proofs.SyncView
import Cadence.Mvba.Proofs.SyncViewAdopt
import Cadence.Mvba.Proofs.ByzPreprepare
import Cadence.Mvba.Proofs.ByzPrepare
import Cadence.Mvba.Proofs.ByzCommit
import Cadence.Mvba.Proofs.ByzTimeoutQc
import Cadence.Mvba.Proofs.ByzTimeoutNoqc

/-! # `Mvba` certificate

Scaffolded by `#gen_proof_files Mvba`; yours to edit. Imports the
per-action proof files and composes their preservation lemmas into
`Mvba.invariants_of_reachable` (+ named `reachable_<property>`
projections). Downstream consumers import this file and nothing heavier. -/

open Veil Mvba

namespace Mvba

#gen_composition Mvba

end Mvba

/--
info: 'Mvba.invariants_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mvba.invariants_of_reachable

/- `#veil_status`: the machine-checked trust table — every registry cell
has a real, statement-matching, kernel-checked theorem in the import
closure, over exactly the standard axioms. Run `#veil_status Mvba table`
interactively for the per-cell table (theorem, defining file, per-cell
axiom set). The count is (3 `safety` + 38 `invariant` + the per-action
`doesNotThrow` cell) × (24 actions + the initializer), plus one
`step_property` × 24 actions — a step relates two states, so unlike an
invariant it has no cell at the initializer.

**Thirteen of the invariants are there for liveness rather than safety**
(`docs/MvbaPlan.md` §3.5 step 3, `Mvba/Liveness.lean`). Every one of them
exists to make an *anti-monotone* guard analysable: a fairness argument has
to know that such a guard can only die by the progress it was waiting for,
and the model's safety proof never had to ask where a guard's failure came
from. By guard:

* `send_commit`'s `¬ commit_sent i v` — `commit_sent_backed`, with
  `commit_sent_implies_voted` to make it inductive;
* `adopt_prepqc`'s `∀ W E, local_prepqc i W E → W < v` —
  `local_prepqc_within_entered`;
* `handle_preprepare`'s `∀ W, voted i W → W < v` —
  `voted_implies_accepted_proposal`, resting on `voted_within_entered`,
  `voted_implies_leader_proposed`, `honest_preprepare_unique` and
  `honest_preprepare_proposed`. Those last two are the formal content of
  `thm:termination`'s "the correct leader broadcasts a single valid
  proposal".

`accepted_implies_prepare` is the ninth, and the one exception to the
pattern: it is not about a guard but about a *conclusion* — the acceptance
link's guard analysis yields `accepted`, while the prepare quorum needs
`msg_prepare`, and the two handlers set them in the same step.
`entered_implies_input` is likewise not about a guard: it lets a liveness
theorem read the participation premise off a validator's being in a view,
rather than carry it separately. `proposed_in_backed` is the leader's
counterpart of `commit_sent_backed`, for the three leader actions'
anti-monotone `¬ proposed_in l v`. And `prepqc_valid` is needed where safety
never was: `leader_repropose` re-proposes a lock **without** re-checking
validity (the supplement's `Recover`), while `handle_preprepare` requires
`valid e`, so the re-proposal is accepted only because the lock was valid all
along. `msg_tc_backed` is the thirteenth: it gets from `sync_view`'s guard to
the timeout quorum behind the certificate, and so to a *correct* validator
that timed out in the view — the step that shows a run cannot advance past
the honest-led view without doing what (A-viewsync) forbids.

The module's one `step_property`, `entered_needs_certificate`, is liveness's
too: a newly entered view is view 1 or the successor of one that already has
a timeout certificate. It has to be a *step* property rather than an
invariant because it relates the two states. Adding it is also what pushed
this family past the default elaboration budgets — the proof files now carry
`veil_large_clump_budgets`, as the Chorus family always has. -/

/-- info: #veil_status Mvba: 1074/1074 real; axioms: propext, Classical.choice, Quot.sound -/
#guard_msgs in
#veil_status Mvba
