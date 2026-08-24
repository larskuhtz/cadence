import Veil

/-! # Shared prelude for the per-action proof files

The verified-module file family (`docs/Architecture.md` §6) puts one
`<Model>/Proofs/<Action>.lean` file per action next to the model. Those
files are generated from a common scaffold and are, apart from the action
name and the occasional manual cell, identical. This module carries the
parts that were previously copy-pasted into every one of them, plus the
two tactics the manual cells use:

* **`veil_proof_options`** and **`veil_large_clump_budgets`** — the
  option blocks each proof file must set, together with the reasoning for
  each option, stated once instead of once per file. One option is
  deliberately *not* here: `veil.smt.trust false` stays written out in
  every proof file, so the repository's no-trusted-solver rule remains
  checkable by grepping the files that rely on it rather than by reading
  this macro.
* **`unveil_local`** — the cheap counterpart of `unveil` for a manual
  cell: same goal shape, but it does not simplify the invariant clump.
* **`inv% h <name>`** / **`inv_have h := <name>`** — projection of a
  single conjunct out of the invariant clump *by invariant name* rather
  than by a hand-counted chain of `.2`s.

Nothing here is part of any theorem's trust base: the option commands only
set options, `inv%` elaborates to an ordinary `And.left`/`And.right`
projection chain, and `unveil_local` is a macro over Veil's own tactics —
all of it kernel-checked like any other proof term. -/

open Lean Elab Command Term Meta

/-- The option block every Veil proof file in this development sets — except
`veil.smt.trust false`, which each file writes out itself: the
no-trusted-solver rule is the repository's headline claim (`README.md`),
and keeping the literal in every file keeps it greppable.

* `veil.cache.proofs true` — consume the proof-cache entries earlier
  solves stored and store fresh ones. Every hit is kernel-replayed
  (`veil.cache.kernelReplay`), so the cache skips *search*, not checking.
* `linter.unreachableTactic` / `linter.unusedTactic` off — a kernel-replay
  hit consumes a manual `#prove_vc … by <tac>` cell at the command level
  and never elaborates the `by` suffix, which those two linters would
  otherwise flag. That is by design here — and it also means a warm cache
  green-lights a cell without exercising its tactic script, so an edited
  cell must be solved cold once (the cache discipline in `CLAUDE.md`
  § Build). -/
elab "veil_proof_options" : command => do
  for stx in #[← `(command| set_option veil.cache.proofs true),
               ← `(command| set_option linter.unreachableTactic false),
               ← `(command| set_option linter.unusedTactic false)] do
    elabCommand stx

/-- The elaboration budgets a model with a large invariant clump needs.

These mirror the budgets the defining model file sets before `#gen_spec`:
on the cross-file path the VC statements are re-created in *this* file, so
this file has to afford the same instance search and recursion depth. Too
small a budget shows up as an elaboration failure, not as an unsound
proof. -/
elab "veil_large_clump_budgets" : command => do
  for stx in #[← `(command| set_option synthInstance.maxHeartbeats 2000000),
               ← `(command| set_option synthInstance.maxSize 4096),
               ← `(command| set_option maxRecDepth 8192),
               ← `(command| set_option maxHeartbeats 1000000)] do
    elabCommand stx

namespace Veil.InvProjection

open Veil

/-- The conjuncts of a right-nested `∧`-spine, outermost first.

The spine is read syntactically; only a tail that is not already an `And`
application is weak-head normalised, and then only once. Normalising
eagerly would be wrong here: the conjuncts are applications of *reducible*
invariant abbreviations, and `whnfR` would unfold them. -/
private partial def andSpine (e : Expr) : MetaM (Array Expr) :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | .app (.app (.const ``And _) a) b => go b (acc.push a)
    | _ =>
      match ← whnfR e with
      | .app (.app (.const ``And _) a) b => go b (acc.push a)
      | _ => return acc.push e

/-- The invariant names of a Veil module, in declaration order, read off
the assembled `Invariants` definition (whose body is literally the
conjunction `@inv₁ … ∧ @inv₂ … ∧ …`). -/
private def invariantNames (invariantsName : Name) : MetaM (Array Name) := do
  let some (.defnInfo di) := (← getEnv).find? invariantsName
    | throwError "`{invariantsName}` is not a definition — is the Veil module \
        with the invariant clump imported?"
  lambdaTelescope di.value fun _ body => do
    (← andSpine body).mapM fun c => do
      let some n := c.getAppFn.constName?
        | throwError "`{invariantsName}` has a conjunct that is not an \
            application of a named invariant: {c}"
      return n

/-- `inv% h <invariant>` — the conjunct of the invariant clump `h` that
belongs to the named `invariant`/`safety` declaration.

In a Veil inductiveness goal the induction hypothesis `hinv` is the whole
invariant clump: one right-nested conjunction with a conjunct per
`safety`/`invariant` declaration, in declaration order. Written out by
hand a conjunct is `hinv.2.2.….2.1` with up to eighty `.2`s — unreadable,
and silently wrong as soon as a declaration is added or reordered.

`inv% hinv fb_neg_qv_no_pos_quorum` builds that projection chain from the
module's own `Invariants` definition instead, so the index can never drift
from the model. Two things are checked at elaboration time: the name must
be one of the clump's conjuncts, and the clump in the goal must have
exactly as many conjuncts as the module has invariants — if a future model
change makes the pre-simplified clump shape diverge from the declaration
list, this fails loudly rather than projecting the wrong conjunct. -/
scoped syntax (name := invProjection) "inv% " term:max ident : term

@[term_elab invProjection]
def elabInvProjection : TermElab := fun stx _ => do
  let h ← elabTerm stx[1] none
  let ty ← instantiateMVars (← inferType h)
  let invName ← resolveGlobalConstNoOverload stx[2]
  let invariantsName := invName.getPrefix ++ `Invariants
  let names ← invariantNames invariantsName
  let some idx := names.findIdx? (· == invName)
    | throwError "`{invName}` is not a conjunct of `{invariantsName}`"
  let conjuncts ← andSpine ty
  unless conjuncts.size == names.size do
    throwError "the invariant clump in the goal has {conjuncts.size} conjuncts \
      but `{invariantsName}` has {names.size} — the clump shape no longer \
      matches the declaration list, so projection by name is not sound here"
  let mut e := h
  for _ in [0:idx] do
    e ← mkAppM ``And.right #[e]
  if idx + 1 < names.size then
    e ← mkAppM ``And.left #[e]
  return e

/-- `unveil_local` — the manual-cell counterpart of `unveil`.

`unveil` massages a Veil VC into readable form with
`veil_intros; veil_wp; …; veil_concretize_wp; veil_clear; veil_simp at *`.
On a model with a ninety-seven-conjunct invariant clump the last step
dominates: it simplifies *every* hypothesis, and the clump is the biggest
one by far. Measured on Chorus, `unveil` costs ~22 s per manual cell, of
which ~14 s is that `at *`.

`unveil_local` takes the same route the automatic discharger takes — the
generated local-WP bridge theorem — and then simplifies the *goal* only,
which leaves it in exactly the shape `unveil` produces. The invariant
clump stays as it is; project the conjuncts a proof needs with `inv_have`,
which normalises them one at a time. Measured on the same cells: ~0.4 s
instead of ~22 s.

If a cell's VC is not in the local-WP form (`veil_apply_local_wp` fails),
fall back to `unveil`. -/
scoped syntax (name := unveilLocal) "unveil_local" : tactic

/-- `inv_have h := <invariant>` — bind the named conjunct of the invariant
clump `hinv` as `h`, normalised the way `unveil` would have normalised it
(curried implications, `… = false` rather than `¬ … = true`). The
companion of `unveil_local`, which leaves the clump untouched. -/
scoped syntax (name := invHave) "inv_have " ident " := " ident : tactic

macro_rules
  | `(tactic| unveil_local) =>
    `(tactic| (veil_apply_local_wp
               open Classical in veil_simp only [smtSimp]
               veil_intro_ho
               veil_simp))
  | `(tactic| inv_have $h:ident := $name:ident) => do
    -- `hinv` is introduced unhygienically by Veil's WP tactics, so the
    -- reference to it has to be unhygienic too.
    let hinv := Lean.mkIdent `hinv
    `(tactic| (have $h := inv% $hinv $name
               veil_simp at $h:ident))

end Veil.InvProjection
