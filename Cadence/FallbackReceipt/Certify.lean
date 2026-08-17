import Cadence.FallbackReceipt.Proofs.Init
import Cadence.FallbackReceipt.Proofs.DeliverEntryFastqc
import Cadence.FallbackReceipt.Proofs.DeliverEntryPos
import Cadence.FallbackReceipt.Proofs.DeliverEntryNeg
import Cadence.FallbackReceipt.Proofs.AcceptVote
import Cadence.FallbackReceipt.Proofs.BuildEntryFastqc
import Cadence.FallbackReceipt.Proofs.BuildEntryEquiv
import Cadence.FallbackReceipt.Proofs.BuildEntryFbqcPos
import Cadence.FallbackReceipt.Proofs.BuildEntryFbqcNeg
import Cadence.FallbackReceipt.Proofs.Propose

/-! # `FallbackReceipt` certificate

Scaffolded by `#gen_proof_files FallbackReceipt`; yours to edit. Imports the
per-action proof files and composes their preservation lemmas into
`FallbackReceipt.invariants_of_reachable` (+ named `reachable_<property>`
projections). Downstream consumers import this file and nothing heavier. -/

open Veil FallbackReceipt

namespace FallbackReceipt

#gen_composition FallbackReceipt

end FallbackReceipt

/--
info: 'FallbackReceipt.invariants_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FallbackReceipt.invariants_of_reachable

/- `#veil_status` (M7): the machine-checked trust table — every registry
cell has a real, statement-matching, kernel-checked theorem in the import
closure, over exactly the standard axioms. Run
`#veil_status FallbackReceipt table` interactively for the per-cell table
(theorem, defining file, per-cell axiom set). -/

/-- info: #veil_status FallbackReceipt: 220/220 real; axioms: propext, Classical.choice, Quot.sound -/
#guard_msgs in
#veil_status FallbackReceipt
