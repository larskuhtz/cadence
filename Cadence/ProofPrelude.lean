import Veil

/-! # Shared prelude for the per-action proof files

The verified-module file family (`docs/Architecture.md` §6) puts one
`<Model>/Proofs/<Action>.lean` file per action next to the model. Those
files are generated from a common scaffold and are, apart from the action
name and the occasional manual cell, identical. This module carries the
parts that were previously copy-pasted into every one of them:

* **`veil_proof_options`** and **`veil_large_clump_budgets`** — the
  option blocks each proof file must set, together with the reasoning for
  each option, stated once instead of once per file. One option is
  deliberately *not* here: `veil.smt.trust false` stays written out in
  every proof file, so the repository's no-trusted-solver rule remains
  checkable by grepping the files that rely on it rather than by reading
  this macro.

The two tactics the manual cells use — `unveil_local`, the cheap
counterpart of `unveil` that leaves the invariant clump unsimplified, and
`veil_inv_have h := <invariant>`, which projects a single conjunct out of
that clump *by invariant name* rather than by a hand-counted chain of
`.2`s — were defined here until 2026-09-10 and are now **Veil's own**
(`Veil/Frontend/DSL/Tactic.lean`), where they are also the two halves of
the discharger's cheap first rung `veil_solve_frame`
(`docs/Dependencies.md`). They need no `open` beyond `Veil`.

Nothing here is part of any theorem's trust base: these commands only set
options. -/

open Lean Elab Command

/-- The option block every Veil proof file in this development sets — except
`veil.smt.trust false`, which each file writes out itself: the
no-trusted-solver rule is the repository's headline claim (`README.md`),
and keeping the literal in every file keeps it greppable.

* `veil.smt.timeout 180` — three times Veil's 60 s default. Not because
  any cell needs 180 s to solve, but because the budget has to be sized for
  the *slowest machine that runs the family cold*, and that is CI (a 4-core
  `ubuntu-24.04-arm` runner at `BATCH=1`, with no proof cache), not a
  workstation. Measured on the same file and runner:
  `fb_sign_neg × inclusion_no_honest_fb_neg` takes 6.2–17.0 s here, 52.8 s
  on CI before the step properties landed (88% of the old budget) and
  62.5 s after them — a *completed* solve that overran, with its TR retry
  at 63.3 s, so the build failed on a cell cvc5 can discharge. Raising the
  budget is close to free: a timeout bounds a **failing** search only, so a
  green run costs the same wall clock either way. It is not a licence to
  ignore a slow cell — a cell that starts needing minutes is diverging, and
  the remedy for that is a manual proof, not a bigger number (`CLAUDE.md`
  § Build, "Distinguish *slow* from *divergent*").
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
  for stx in #[← `(command| set_option veil.smt.timeout 180),
               ← `(command| set_option veil.cache.proofs true),
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
