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
axiom set). The count is (3 `safety` + 25 `invariant` + the per-action
`doesNotThrow` cell) × (24 actions + the initializer). -/

/-- info: #veil_status Mvba: 725/725 real; axioms: propext, Classical.choice, Quot.sound -/
#guard_msgs in
#veil_status Mvba
