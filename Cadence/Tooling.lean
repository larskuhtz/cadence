import Veil

/-! # Targeted invariant-checking commands for Veil

User-side additions that complement Veil's built-in `#check_invariants`
and `#check_action`. They give tighter inner-loop iteration when
debugging a single invariant or a single (action × invariant) pair —
useful when the full sweep over `actions × invariants` is expensive.

* `#check_invariant <name>` — check the named invariant against every
  action (the dual of `#check_action`).
* `#check_vc <action> <invariant>` — check a single (action × invariant)
  pair.

Both commands reuse Veil's existing `Verifier.runFilteredAsync` /
`displayStreamingResults` pipeline (`Veil/Core/Tools/Verifier/Server.lean`,
`Veil/Core/UI/Verifier/VerificationResults.lean`); they differ from the
built-ins only in the `VCMetadata → Bool` filter passed in. The
underlying VC-manager only schedules dischargers whose metadata
matches, so the SMT cost is exactly the cost of the targeted VCs.

These commands rely on Veil's `VCMetadata.induction` carrying both
`.action` and `.property` fields (see
`Veil/Frontend/DSL/Infra/Metadata.lean`).

Eventually it would be nice to upstream these to Veil itself — the
implementations are tiny and orthogonal to the rest of the framework.
-/

namespace Veil

open Lean Elab Command Meta

/-! ### `#check_invariant <name>` -/

scoped syntax (name := checkInvariant) "#check_invariant" ident : command

/-- Filter: induction VCs whose property name equals `invName`. -/
private def isInductionForInvariant (invName : Name) : VCMetadata → Bool
  | .induction m => m.property == invName
  | .trace _ => false

@[command_elab Veil.checkInvariant]
def elabCheckInvariant : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.checkInvariant (fun _ => return "#check_invariant") do
    if ← isModelCheckCompileMode then return
    if ← isNoVerifyMode then
      logWarningAt stx m!"⏭ skipped (veil.noVerify): no VCs were solved"
      return
    let mod ← getCurrentModule (errMsg := "You cannot #check_invariant outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    unless stx.getKind == `Veil.checkInvariant do
      throwUnsupportedSyntax
    let invName := stx[1].getId
    let filter := isInductionForInvariant invName
    Verifier.runFilteredAsync filter (logVerificationResults stx)
    Verifier.displayStreamingResults stx
      (Verifier.vcManager.atomically fun ref => do
        let mgr ← ref.get
        let results ← mgr.toResults filter
        pure (results, if mgr.isDoneFiltered filter then .done else .running))
      mod.specFinalizedAtStx

/-! ### `#check_vc <action> <invariant>` -/

scoped syntax (name := checkVC) "#check_vc" ident ident : command

/-- Filter: the single induction VC for the given (action, property). -/
private def isInductionForVC (actionName invName : Name) : VCMetadata → Bool
  | .induction m => m.action == actionName ∧ m.property == invName
  | .trace _ => false

@[command_elab Veil.checkVC]
def elabCheckVC : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.checkVC (fun _ => return "#check_vc") do
    if ← isModelCheckCompileMode then return
    if ← isNoVerifyMode then
      logWarningAt stx m!"⏭ skipped (veil.noVerify): no VCs were solved"
      return
    let mod ← getCurrentModule (errMsg := "You cannot #check_vc outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    unless stx.getKind == `Veil.checkVC do
      throwUnsupportedSyntax
    let actionName := stx[1].getId
    let invName := stx[2].getId
    let filter := isInductionForVC actionName invName
    Verifier.runFilteredAsync filter (logVerificationResults stx)
    Verifier.displayStreamingResults stx
      (Verifier.vcManager.atomically fun ref => do
        let mgr ← ref.get
        let results ← mgr.toResults filter
        pure (results, if mgr.isDoneFiltered filter then .done else .running))
      mod.specFinalizedAtStx

end Veil
