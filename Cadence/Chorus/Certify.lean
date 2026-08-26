import Cadence.Chorus.Proofs.Init
import Cadence.Chorus.Proofs.AdvanceToDeadline
import Cadence.Chorus.Proofs.AdvanceToFbArm
import Cadence.Chorus.Proofs.AdvanceToMvbaArm
import Cadence.Chorus.Proofs.Propose
import Cadence.Chorus.Proofs.DeliverChunkAssigned
import Cadence.Chorus.Proofs.RecordChunk
import Cadence.Chorus.Proofs.Vote
import Cadence.Chorus.Proofs.AggregateFastqcPos
import Cadence.Chorus.Proofs.AggregateFastqcNeg
import Cadence.Chorus.Proofs.CommitSignPos
import Cadence.Chorus.Proofs.CommitSignNeg
import Cadence.Chorus.Proofs.CastFastCommit
import Cadence.Chorus.Proofs.BroadcastCommitqcPos
import Cadence.Chorus.Proofs.BroadcastCommitqcNeg
import Cadence.Chorus.Proofs.FbSignPos
import Cadence.Chorus.Proofs.FbSignNeg
import Cadence.Chorus.Proofs.CastFallbackVote
import Cadence.Chorus.Proofs.MvbaDecidePos
import Cadence.Chorus.Proofs.MvbaDecideNeg
import Cadence.Chorus.Proofs.MvbaTerminate
import Cadence.Chorus.Proofs.RedisseminateChunk
import Cadence.Chorus.Proofs.CastFbCommit
import Cadence.Chorus.Proofs.CommitAssignPos
import Cadence.Chorus.Proofs.CommitAssignNeg
import Cadence.Chorus.Proofs.FinalizeCommit
import Cadence.Chorus.Proofs.ByzSignProposer
import Cadence.Chorus.Proofs.ByzDeliverChunk
import Cadence.Chorus.Proofs.ByzSignVotePos
import Cadence.Chorus.Proofs.ByzSignVoteNeg
import Cadence.Chorus.Proofs.ByzCastVote
import Cadence.Chorus.Proofs.ByzSignFbPos
import Cadence.Chorus.Proofs.ByzSignFbNeg
import Cadence.Chorus.Proofs.ByzSignFallback
import Cadence.Chorus.Proofs.ByzSignCommitPos
import Cadence.Chorus.Proofs.ByzSignCommitNeg
import Cadence.Chorus.Proofs.ByzCastCommit
import Cadence.Chorus.Proofs.ByzSignFbcommit
import Cadence.Chorus.Proofs.ByzReleaseMsgDecryptShare

/-! # `Chorus` certificate

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Imports the
per-action proof files and composes their preservation lemmas into
`Chorus.invariants_of_reachable` (+ named `reachable_<property>`
projections). Downstream consumers import this file and nothing heavier. -/

open Veil Chorus

namespace Chorus

#gen_composition Chorus

end Chorus

/--
info: 'Chorus.invariants_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Chorus.invariants_of_reachable

/- `#veil_status` (M7): the machine-checked trust table — every registry
cell (3 822 action × invariant obligations + 39 doesNotThrow) has a real,
statement-matching, kernel-checked theorem in the import closure, over
exactly the standard axioms. Run `#veil_status Chorus table`
interactively for the per-cell table (theorem, defining file, per-cell
axiom set; expect minutes at this scale). -/

/-- info: #veil_status Chorus: 3861/3861 real; axioms: propext, Classical.choice, Quot.sound -/
#guard_msgs in
#veil_status Chorus
