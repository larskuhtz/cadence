---
name: cadence-verification
description: Working guide for the Cadence/Chorus/Conductor Veil models — how the proof families are laid out, the verification commands, the fast iteration loop, and the model-specific traps. Read before modifying any .lean model, adding an invariant, writing a manual proof cell, or running a verification sweep.
---

# Working on the Cadence Veil models

[CLAUDE.md](../../../CLAUDE.md) has the orientation, the build commands and
the hard rules; this guide is the next level down — the mechanics of the proof
families and the traps that only show up once you are inside a cell.

## 1. How a verified module is laid out

Both large models use the same three-layer shape. `Chorus` is the reference;
`FallbackReceipt` is the same thing at 1/17 the scale, which makes it the
right place to try anything structural first.

```
Cadence/Chorus.lean            MODEL — state, actions, invariants.
   │                           Elaborating it persists every VC *statement*
   │                           in the module's registry. No sweep, no proofs.
   ▼ imported by
Cadence/Chorus/Proofs/*.lean   ONE FILE PER ACTION (39, incl. Init.lean).
   │                           `#prove_action Chorus <action>` re-creates that
   │                           action's registered VCs, discharges them with
   │                           reconstruction, persists real kernel-checked
   │                           theorems, and emits the preservation lemma
   │                           `Chorus.Proofs.step_<action>` / `init_case`.
   ▼ imported by
Cadence/Chorus/Certify.lean    `#gen_composition Chorus` → the reachability
   │                           induction (`invariants_of_reachable`) + one
   │                           named `reachable_<property>` per property.
   │                           Ends in its axiom pin and `#veil_status` pin.
   ▼ imported by
Cadence/Chorus/Compose.lean        hand-written end theorems, each with its
Cadence/Chorus/Pigeonhole.lean     own axiom pin.
```

Why the per-action layer exists: persisting a module's reconstructed proofs
requires holding them all in one process's environment, which exceeds 32 GB at
Chorus's scale. One small file per action bounds each process (~5 GB cold),
and the composition only needs one lemma per action. The files were scaffolded
once by `#gen_proof_files Chorus` and are hand-owned since.

**Statement identity is structural, not conventional**: the proof files read
their VC statements out of the registry the model wrote, so they cannot drift
from what the model declares. Never restate a VC by hand.

`Cadence/Cadence.lean` and `Cadence/Conductor.lean` are small enough to sweep
in-file (`#check_invariants`) and persist their real proofs directly with
`#gen_theorems`; `Cadence/Composition.lean` consumes those theorems.

## 2. The commands

| Command | Use |
|---|---|
| `#check_invariants` / `#check_action <a>` | in-file sweep (the small models only) |
| `#check_invariant <name>` | one invariant × all actions — from `Cadence/Tooling.lean` |
| `#check_vc <action> <invariant>` | one cell — from `Cadence/Tooling.lean` |
| `#check_invariants <Module>`, `#check_action <Module> <a>`, `#check_vc <Module> <a> <p>` | the **cross-file** forms, in any file importing the model |
| `#prove_vc <Module> <a> <p> by <tac>` | prove one cell for real, cross-file. A later `#prove_action` consumes it after a statement check instead of re-solving |
| `#prove_action <Module> <a>` | the proof files' workhorse |
| `#gen_composition <Module>` | the certificate |
| `#veil_status <Module> [table]` | the audit: per registry cell, is there a real, statement-matching, kernel-checked theorem in scope? |

Run **one** check command at a time — several concurrent ones contend for the
same discharger scheduler and slow each other down.

**Solver options are read in different places depending on the path.** For an
in-file sweep they are captured when the module elaborates its spec, so a
`set_option … in #check_invariants` is *inert* (this project shipped an inert
900 s timeout for weeks — see [History](../../../docs/History.md) Build #12).
On the cross-file path they are read at tactic runtime, in the *consuming*
file. That is why every proof file sets its own `veil.smt.trust false` and
cache options at the top.

## 3. The fast loop

1. Build the model: `lake build Cadence.Chorus` (~90 s — it runs no sweep).
2. Open a scratch file mirroring a proof file's head: `import Cadence.Chorus`,
   `import Cadence.ProofPrelude`, `open Veil Chorus Veil.InvProjection`,
   `set_option veil.smt.trust false`, `veil_proof_options`,
   `veil_large_clump_budgets`.
3. Put `#prove_vc Chorus <action> <property> by <tac>` cells in it and run
   `lake env lean <scratch>`. Seconds per cell.
4. To see what you are proving, end the tactic after the `obtain`s and read
   the unsolved-goals dump.
5. Move the finished cell into the action's proof file, **before** that
   file's `#prove_action`.

Cells proven in scratch land in the proof cache, so the real proof file
replays them instead of re-solving. The flip side: a warm entry consumes a
cell *without elaborating its tactic* (entries are keyed by VC statement,
not proof script), so after editing a committed cell, solve it cold once —
a scratch run with `set_option veil.cache.proofs false`, or delete its
entry — before trusting the script.

## 4. Manual cells

A few Chorus cells (the quorum-intersection ones) cannot be found by the solver
and are `#prove_vc Chorus <action> <property> by <tac>` lines in their
actions' proof files, before the `#prove_action` that consumes them after a
statement check. The statement always comes from the model's registry —
never write one by hand.

* Open a cell with `unveil_local` (`Cadence/ProofPrelude.lean`), not
  `unveil`: same goal shape, ~0.4 s instead of ~22 s, because it leaves the
  invariant clump unsimplified. Project the conjuncts the proof needs with
  `inv_have h := <invariant>` — by name, no `.2` chains; a model change
  that invalidates the lookup fails loudly at elaboration. If a cell's VC
  is not in local-WP form (`veil_apply_local_wp` fails), fall back to
  `unveil`.
* A failing cell in a proof file already retries through the built-in ladder
  (perturbed solver seeds, then the alternative two-state encoding) before it
  is reported. Only write a manual proof once that ladder has genuinely failed
  — and check it is divergence, not slowness (see CLAUDE.md).

## 5. Adding or changing an invariant

1. Put it where it reads best — position in the model is thematic, not
   load-bearing: the manual cells project conjuncts by name (`inv_have`),
   so inserting or reordering re-indexes nothing, and any change to the
   clump changes every VC statement either way.
2. Rebuild the model, then the proof family. Statement-changing edits
   re-solve honestly — the cache gives no hits on changed statements.
3. Expect the clump to get harder: growing it has previously tipped
   *formerly green* cells into e-matching divergence (History, Build #11).
   Make the broken ones manual, mirroring their neighbours.
4. Update the `#veil_status` pins in the `Certify.lean` files — the counts
   change — and sanity-check that the new counts are what you expect
   (actions × properties + one does-not-throw per action).
5. Any edit to a model file — **even a comment** — rebuilds its proof family.
   Budget the staged build before touching it.

## 6. Model-specific traps

### Chorus

* **Avoid `∃`-quorum ghosts in action preconditions** that downstream VCs must
  re-derive: they push quorum reasoning into every consumer and diverge the
  solver's e-matching. Materialise certificates as network relations with an
  explicit assembly action (the `msg_commitqc_*` / `broadcast_commitqc_*`
  pattern), or record witnesses in auxiliary history relations (the
  `local_fb_neg_qv` pattern).
* One cell (`vote × fastqc_complete_implies_mvba_evidence`) turns
  `veil.smt.foldBoolAtoms` off file-locally in `Proofs/Vote.lean`. The
  reasoning is in that file's header; the option is tactic-side, so statements
  and cache keys are unaffected.

### Cadence and Conductor

* **Oracle actions carry the contract's `require`s; protocol actions are
  local.** Only oracle actions (`orch_open`, `sc_finalize`, `acs_decide`) may
  read other validators' rows — they model distributed services. Honest
  protocol actions read and write only the acting validator's rows.
* When a solver search diverges at an oracle action, materialise the missing
  fact as an explicit witness parameter or a derivable `require` on the oracle
  (see `acs_decide`'s decision-precedes-entry require) instead of hoping
  e-matching finds the invariant chain.
* `Conductor.lean` needs the raised `synthInstance` budgets that precede its
  `#gen_spec` even at 10 action parameters.

### FallbackReceipt

* `PreFix.lean`'s model-check **violation is the expected result** and is
  `#guard_msgs`-pinned. A green build requires it.
* The layer's `#model_check` (23 975 states at `n = 4, f = 1`) is a redundant,
  solver-free regression over properties that also have unbounded proofs — and
  a non-vacuity witness, since the explored graph is checked to contain
  proposing runs. Keep both.

## 7. What not to break

The list of verification-status invariants in
[CLAUDE.md](../../../CLAUDE.md) — no trusted solver step, no `sorryAx`,
complete `#veil_status` pins, the pre-fix refutation still failing. Each is
build-checked, so you will find out; the point of the list is that "fixing"
the build by weakening one of them changes what the project claims.
