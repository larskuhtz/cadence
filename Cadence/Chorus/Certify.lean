import Cadence.Chorus.Proofs.Init
import Cadence.Chorus.Proofs.AdvanceToDeadline
import Cadence.Chorus.Proofs.AdvanceToFbArm
import Cadence.Chorus.Proofs.AdvanceToMvbaArm
import Cadence.Chorus.Proofs.Participate
import Cadence.Chorus.Proofs.Abandon
import Cadence.Chorus.Proofs.Propose
import Cadence.Chorus.Proofs.RecordChunk
import Cadence.Chorus.Proofs.Vote
import Cadence.Chorus.Proofs.AggregateFastqcPos
import Cadence.Chorus.Proofs.AggregateFastqcNeg
import Cadence.Chorus.Proofs.CommitSignPos
import Cadence.Chorus.Proofs.CommitSignNeg
import Cadence.Chorus.Proofs.CastFastCommit
import Cadence.Chorus.Proofs.BroadcastCommitqcPos
import Cadence.Chorus.Proofs.BroadcastCommitqcNeg
import Cadence.Chorus.Proofs.ReceiveVotePos
import Cadence.Chorus.Proofs.ReceiveVoteNeg
import Cadence.Chorus.Proofs.FbSignPos
import Cadence.Chorus.Proofs.FbSignNeg
import Cadence.Chorus.Proofs.CastFallbackVote
import Cadence.Chorus.Proofs.MvbaStep
import Cadence.Chorus.Proofs.MvbaPropose
import Cadence.Chorus.Proofs.SendMvbaCert
import Cadence.Chorus.Proofs.AcceptMvbaCommitqc
import Cadence.Chorus.Proofs.MvbaAvailReady
import Cadence.Chorus.Proofs.OnMvbaDecidePos
import Cadence.Chorus.Proofs.OnMvbaDecideNeg
import Cadence.Chorus.Proofs.MvbaTerminate
import Cadence.Chorus.Proofs.CastFbCommit
import Cadence.Chorus.Proofs.BroadcastFbcommitqc
import Cadence.Chorus.Proofs.CommitAssignPosFast
import Cadence.Chorus.Proofs.CommitAssignPosFb
import Cadence.Chorus.Proofs.CommitAssignPosMvba
import Cadence.Chorus.Proofs.CommitAssignNegFast
import Cadence.Chorus.Proofs.CommitAssignNegFb
import Cadence.Chorus.Proofs.CommitAssignNegMvba
import Cadence.Chorus.Proofs.FinalizeCommit
import Cadence.Chorus.Proofs.ByzSignProposer
import Cadence.Chorus.Proofs.ByzSendChunk
import Cadence.Chorus.Proofs.ByzRedisseminateChunk
import Cadence.Chorus.Proofs.ByzSignVotePos
import Cadence.Chorus.Proofs.ByzSignVoteNeg
import Cadence.Chorus.Proofs.ByzCastVote
import Cadence.Chorus.Proofs.ByzSignFbPos
import Cadence.Chorus.Proofs.ByzSignFbNeg
import Cadence.Chorus.Proofs.ByzSignFallback
import Cadence.Chorus.Proofs.ByzSignCommitPos
import Cadence.Chorus.Proofs.ByzSignCommitNeg
import Cadence.Chorus.Proofs.ByzCastCommit
import Cadence.Chorus.Proofs.ByzBroadcastCommitqcPos
import Cadence.Chorus.Proofs.ByzBroadcastCommitqcNeg
import Cadence.Chorus.Proofs.ByzSignFbcommit
import Cadence.Chorus.Proofs.ByzBroadcastFbcommitqc
import Cadence.Chorus.Proofs.ByzSendMvbaCert
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

/- `#veil_status`: the machine-checked trust table — every registry
cell (the action × property obligations, the step-property cells and one
doesNotThrow per action) has a real, statement-matching, kernel-checked
theorem in the import closure, over exactly the standard axioms. Run `#veil_status Chorus table`
interactively for the per-cell table (theorem, defining file, per-cell
axiom set; expect minutes at this scale). -/

/-- info: #veil_status Chorus: 6215/6215 real; axioms: propext, Classical.choice, Quot.sound -/
#guard_msgs in
#veil_status Chorus
