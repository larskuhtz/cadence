# Cadence verification — architecture

*Top-level design document for this formalisation. For orientation, build
instructions, and the evidence-auditing guide, start at
[README.md](../README.md); for the end theorems and their trust base on
one page, [`Cadence.lean`](../Cadence.lean). This file explains how the
formalisation is structured, what each part establishes and by what
method, and exactly where its trust boundaries and meta-theoretic seams
lie — **§4 is the audit checklist**: everything the machine does not
establish, in one place. The per-model design rationale lives one level
down: [ChorusDesign.md](./ChorusDesign.md) for the Chorus model, and
[ConductorDesign.md](./ConductorDesign.md) plus the module headers of
[Cadence/Cadence.lean](../Cadence/Cadence.lean) and
[Cadence/Conductor.lean](../Cadence/Conductor.lean) for the
composition-layer models.*

## 1. What is being verified

[Cadence](https://www.category.xyz/cadence) (`arXiv:2607.02275v2`; see the
root [README.md](../README.md) for the citation and how to resolve the label
names used here) is a BFT consensus design with three layers, and the
formalisation mirrors that decomposition one-to-one:

* **Chorus** (`p2_chorus.tex`, `alg_*.tex`) — the per-slot one-shot
  consensus: `k` concurrent proposers, a two-round fast path, and a
  fallback path (fallback voting → MVBA → a final commit round).
  Modelled in [Cadence/Chorus.lean](../Cadence/Chorus.lean).
* **Conductor** (`p2_conductor_proofs.tex`, the ACS version) — the
  window-based orchestrator that schedules slots. Modelled in
  [Cadence/Conductor.lean](../Cadence/Conductor.lean).
* **Cadence** (`p2_framework.tex`) — the extreme-pipelining glue that
  runs one slot-consensus instance per slot under the orchestrator and
  assembles the MCP log. Modelled in [Cadence/Cadence.lean](../Cadence/Cadence.lean).

Two auxiliary models cover the layer where the protocol's per-validator
reasoning is most intricate: the **fallback receipt/propose layer**
([Cadence/FallbackReceipt.lean](../Cadence/FallbackReceipt.lean) and companions), which
mechanises the per-validator layer where a real liveness bug was found
and fixed (see §5), and the *pre-fix* variant — the paper's receipt
rules as they stood **before** that bug fix, i.e. as published in
`arXiv:2607.02275v1` (§5; "pre-fix" is used in this sense throughout) —
kept as a machine-checked refutation.

## 2. The methods

Four verification methods are combined — the numbering is a catalogue,
**not** a ranking of strength or soundness; every claim is checked by
at least one machine, and the trust base of each artefact is stated
(and, where possible, pinned in CI by `#guard_msgs`).

**Method 1 — inductive invariants, SMT-discharged** (labelled "sweep"
in the tables below). Each protocol model declares its safety
properties and helper invariants; Veil generates one verification
condition per (action × property) pair and discharges them with cvc5.
Current state, all green:

| Module | Actions | Declarations | VCs | Discharge |
|---|---|---|---|---|
| `Cadence/Chorus.lean` | 38 | 9 safety + 88 invariants | 3 822 | cvc5, **proof-reconstructed** (kernel-checked), + 11 manual Lean proofs for e-matching-divergent cells |
| `Cadence/Cadence.lean` | 4 | 4 safety + 18 invariants | 115 | cvc5, **proof-reconstructed** (kernel-checked) |
| `Cadence/Conductor.lean` | 7 | 5 safety + 14 invariants | 160 | cvc5, **proof-reconstructed** (kernel-checked; one encoding-divergent attempt covered by its alternative form) |
| `Cadence/FallbackReceipt.lean` | 9 | 1 safety + 20 invariants | 220 | cvc5, **proof-reconstructed** (kernel-checked, no trusted step) |

**All four modules run with proof reconstruction** (`veil.smt.trust
false`): every ✅ is a proof re-checked by Lean's kernel, not a trusted
solver verdict. Where the VCs are discharged differs by module size:
`Cadence/Cadence.lean`/`Conductor.lean` run an in-file sweep
(`#check_invariants`); `Cadence/Chorus.lean`/`FallbackReceipt.lean` only *state*
their VCs (a persistent registry) and the per-action proof files
discharge them (§6). A per-cell fallback ladder (seed retries → the
alternative two-state encoding → manual Lean proofs) absorbs
reconstruction-resistant cells; no trusted islands are needed.

**Method 2 — exhaustive model checking (concrete instances).** Used
only where it is a *complete* method or strictly redundant — **no claim
about the final protocol rests on a bounded-instance check**:

* the **refutation** of the pre-fix receipt rules (§5) — exhibiting a
  reachable counterexample is complete evidence of a bug regardless of
  instance size; the found trace (`n = 3f+1`, `f = 1`) is pinned
  verbatim in the build;
* a **redundant regression check** over the receipt layer's structural
  invariants (23 975 states) — defense in depth alongside their
  unbounded SMT proofs, and a non-vacuity witness (the explored graph
  contains proposing runs).

**Method 3 — plain-Lean composition over reachable states.** Every
discharged VC is persisted as a named, kernel-checked theorem
(`#gen_theorems` in the small modules, `#prove_action` in the
proof-file families), and inductions over the generated `reachable`
relation assemble them into "every reachable state satisfies the
invariant clump" (`invariants_of_reachable` — emitted by
`#gen_composition` in the families' `Certify.lean` files, hand-written
in `Cadence/Composition.lean` for the small modules), from which the paper's
*module contracts* ([Cadence/Interfaces.lean](../Cadence/Interfaces.lean)) are
instantiated:

* `Conductor ⊨ Orchestrator` and the paper's **positional MCP Safety**
  (`def:safety` over ordered logs) — [Cadence/Composition.lean](../Cadence/Composition.lean);
* `Chorus ⊨ SlotConsensus` —
  [Cadence/Chorus/Compose.lean](../Cadence/Chorus/Compose.lean), over the composed
  certificate and named per-property projections of
  [Cadence/Chorus/Certify.lean](../Cadence/Chorus/Certify.lean);
* build totality of the receipt layer for **every** `n = 3f+1` —
  [Cadence/FallbackReceipt/Totality.lean](../Cadence/FallbackReceipt/Totality.lean),
  kernel-checked end-to-end;
* the **evidence pigeonhole** of Chorus's fair-progress argument, for
  every `n = 3f+1` — [Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean)
  (`evidence_pigeonhole_of_reachable`): a supermajority of honest
  fallback entries always yields certified per-proposer evidence
  (FallbackQC or EquivCert). This is the counting step at the centre of
  the fair-progress argument, and it is a theorem rather than an
  assumption.

**Method 4 — documented meta-theory.** What is deliberately *not*
inside Lean is stated as named assumptions and audited by hand (§4).
This is the one method that is weaker than the others — which is
exactly why §4 exists as its complete, auditable inventory.

## 3. Property coverage (what is proven, where)

The paper's headline properties and their formal counterparts:

| Paper claim | Formal artefact | Method |
|---|---|---|
| Chorus Agreement (`lemma:chorus-agreement`) | `safety [agreement_pos]`, `[agreement_pos_neg]`; instance field `agreement` in `Cadence/Chorus/Compose.lean` | sweep + composition |
| Chorus integrity | `safety [integrity_pos]`, `[integrity_pos_neg]` | sweep |
| Proposal inclusion / censorship resistance (`lemma:chorus-proposal-inclusion`) | `safety [proposal_inclusion]`, `[proposal_inclusion_no_neg]` (premise `all_honest_recorded`); instance field `proposal_inclusion` | sweep + composition |
| Hiding until the deadline (`lemma:chorus-hiding`) | protocol half: `safety [hiding_until_deadline]`; crypto half axiomatised (`ThresholdIBE`, [Cadence/Primitives.lean](../Cadence/Primitives.lean)) | sweep + axiom |
| Speculative-finality revertibility claim | `safety [speculative_agreement_pos]`, `[..._pos_neg]` (conditional on `no_equivocation` and `no_invalid_encoding`) | sweep |
| Chorus termination (`lemma:chorus-termination`) | fair-progress invariant layer + (F-\*)/(A-mvba) meta-axioms; untimed (no `ℓ` bound) | sweep + meta (§4) |
| "Fallback meta-block valid by construction" (`alg:fallback` build rule) | `certified_propose` (all `n`, SMT) + `build_totality_of_reachable` (all `n = 3f+1`, kernel-checked) | sweep + Lean |
| Evidence pigeonhole (per-proposer evidence always forms from `2f+1` honest fallback entries — the counting step of `lemma:chorus-termination`'s fallback branch) | `evidence_pigeonhole_of_reachable` ([Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean)), all `n = 3f+1` | sweep + Lean |
| The pre-fix receipt rules are broken (the §7.2 finding) | pinned model-checker violation, [Cadence/FallbackReceipt/PreFix.lean](../Cadence/FallbackReceipt/PreFix.lean) | model check |
| Conductor open-prefix agreement, boundedness residues | Conductor sweep + `orchestrator_instance` | sweep + composition |
| MCP Safety, positional form (`def:safety`) | `positional_log_safety` in `Cadence/Composition.lean` | composition |
| Conductor/Cadence temporal claims (totality, ℓ-liveness, recovery) | documented obligations in `Cadence/Interfaces.lean` tables | meta (§4) |

## 4. The meta-assumption inventory

**This is the audit checklist.** Everything the Lean artefacts do *not*
establish, in one place; each item names where it is stated and why it is
believed sound. Nothing else in this repository requires a leap of faith —
the rest is re-derived by the machine on every build (see §6 and the pins
in [`Cadence.lean`](../Cadence.lean)).

The list is meant to be *checkable for completeness* rather than taken on
trust. Every assumption below has a **name**, and the named fairness and
oracle axioms — (F-justice), (F-byz), (A-mvba), (A-sc-termination),
(A-sc-totality) — appear verbatim in the Lean sources at the points where
they are consumed, so `grep -rn '(A-' Cadence/` enumerates the consumers
and would expose an axiom that had crept in without being listed here. The
network contract (item 1) is the exception and the reason item 1 comes
first: its names live in [ChorusDesign.md](./ChorusDesign.md) §3.1.1 rather
than in the code, and no tool checks it — the sources speak of "monotone"
relations, and it takes a human to confirm each use is positive.

1. **The monotone-network contract (M-update)+(M-frame)**
   ([ChorusDesign.md](./ChorusDesign.md) §3.1–§3.3): safety in the
   monotone model implies safety under asynchrony only if network
   relations are consulted positively. Veil does not enforce (M-frame);
   it is audited by hand, with three documented scoped exception
   categories (`fb_sign_neg`'s witnessed quorum; `cast_fb_commit`'s
   frozen decided-vector read; and seven *self-row* reads — a guard
   consulting a row of `msg_proposer_signed`/`msg_commit_cast`
   negatively, where the row is indexed by, and writable only by, the
   acting validator itself — enumerated in ChorusDesign.md §3.1).
2. **Fairness and oracle-termination axioms** (Chorus liveness section;
   [ChorusDesign.md](./ChorusDesign.md) §7): (F-justice), (F-byz),
   (A-mvba). The SMT-discharged fair-progress invariants carry the
   safety content; the temporal glue (fair scheduling → eventual
   firing) is not encoded. (A-mvba)'s per-validator implementability
   premise is discharged by the receipt-layer models (§5) at the same
   meta seam. The argument's one counting step — the *evidence
   pigeonhole* (`ChorusDesign.md` §7, x = 0 branch) — is **not on this
   list**: `Chorus.evidence_pigeonhole_of_reachable`
   ([Cadence/Chorus/Pigeonhole.lean](../Cadence/Chorus/Pigeonhole.lean)) proves it over
   reachable states for every `n = 3f+1`, from the `two_cover`
   pigeonhole and the named reachability projections.
3. **Primitive contracts as axioms**: `ThresholdIBE` (cryptographic
   hiding — genuinely an assumption, as for any crypto primitive) and
   the `MVBA` / `ACS` module contracts
   ([Cadence/Primitives.lean](../Cadence/Primitives.lean),
   [Cadence/Interfaces.lean](../Cadence/Interfaces.lean)) — standard primitives whose
   implementations are out of scope. Note what is *not* on this list:
   the `ByzNodeSet` quorum/counting interface is **not** an assumption
   gap — its axioms are Lean-proven for the concrete `byzNodeSetFin`
   instance family, which covers every deployment size `n = 3f+1` with
   any Byzantine set of size `≤ f`. An end-to-end example instantiation
   of the remaining class stack (an `MVBA`/`ThresholdIBE` model
   instance) is open work ([ChorusDesign.md](./ChorusDesign.md) §9).
4. **Temporal/quantitative module obligations**: ℓ-termination,
   `d_tot`-totality, Quiescence, boundedness cardinalities, recovery —
   documented rows of the `Cadence/Interfaces.lean` obligation tables with
   named meta-axiom labels ((A-sc-termination), (A-sc-totality), …).
   The models are untimed; no formal artefact claims a latency bound.
5. **Scope**: single slot for Chorus (slot independence is argued, not
   modelled), no epochs/proposer rotation, chunk indices and
   erasure-code arithmetic abstracted
   ([ChorusDesign.md](./ChorusDesign.md) §3.4, §8), payload bytes not
   modelled.
6. **Trusted tooling**: Veil's VC generation and the concrete model
   checker are part of the trusted computing base everywhere (as is
   Lean's kernel). cvc5's `unsat` verdicts are *not* trusted — every
   sweep reconstructs its proofs kernel-checked (§6) — but its `sat`
   verdicts on the `sat trace` reachability sanity checks are (a wrong
   model there could only make a non-vacuity check vacuous, never a
   safety claim wrong).

## 5. The receipt layer: why the auxiliary models exist

A liveness bug in the paper's fallback receipt rules (an accepted
EquivCert was never harvested, so a validator could propose an invalid
meta-block and never retry — breaking the termination proof's premise)
was found by a **parallel formal-verification effort using Rocq**
(an external report, 2026-07-06), independently confirmed against the
paper sources here, and fixed upstream on 2026-07-07 (receipt
restriction + atomic build; full record:
[ChorusDesign.md](./ChorusDesign.md) §7.2).

Both sides of that are now citable against public artefacts: the buggy
rules are those published in **`arXiv:2607.02275v1`** and the corrected
design is **v2**, so "pre-fix" and "fixed" name immutable documents
rather than an internal commit range. The episode drove two permanent
artefacts in *this* formalisation:

* the **fallback commit round** and the tightened wire format are
  modelled faithfully in `Cadence/Chorus.lean` rather than documented away, and
* the receipt/propose layer itself is mechanised both ways:
  the *shipped* design verified (including the counting argument, for
  every `n = 3f+1`, kernel-checked), and the *pre-fix* design refuted
  by exhaustive model checking, with the found counterexample — which
  is exactly the reported scenario — pinned in the build.

This is the concrete sense in which the formalisation "provides
evidence the paper has no bugs": the one bug found so far was found by
exactly this kind of formal scrutiny (by the Rocq effort), and this
project's contribution is to keep both directions machine-checked
permanently — the fixed design verified at full generality, and the
bug's presence-before-fix reproducible in every build.

## 6. Trust base: cvc5 out, kernel in

Current bases, per artefact (each pinned by `#guard_msgs` where marked;
how the project got here is history — [History.md](./History.md)). Every
axiom pin below is *also* re-derived in the audit root
[`Cadence.lean`](../Cadence.lean), so the whole table can be read off one
file:

| Artefact | Axioms | Pinned |
|---|---|---|
| `Cadence.positional_log_safety`, `Conductor.orchestrator_instance` (`Cadence/Composition.lean`) | `propext, Classical.choice, Quot.sound` | ✓ |
| `Chorus.invariants_of_reachable` + per-property projections (`Cadence/Chorus/Certify.lean`) | same | ✓ + `#veil_status`: 3822/3822 real |
| `FallbackReceipt.invariants_of_reachable` (`Cadence/FallbackReceipt/Certify.lean`) | same | ✓ + `#veil_status`: 220/220 real |
| `FallbackReceipt.build_totality_of_reachable` (`Cadence/FallbackReceipt/Totality.lean`) | same | ✓ |
| `Chorus.slotConsensus_instance` (`Cadence/Chorus/Compose.lean`) | same | ✓ |
| `Chorus.evidence_pigeonhole_of_reachable` (`Cadence/Chorus/Pigeonhole.lean`) | same | ✓ |
| the `FallbackReceiptPreFix` refutation (`Cadence/FallbackReceipt/PreFix.lean`) | expected model-checker violation (trace) | ✓ |

**cvc5's unsat verdicts are trusted nowhere**: every discharge runs
with proof reconstruction (`veil.smt.trust false`) — every proof is
re-checked by Lean's kernel. **And no composition consumes a stub**:
every pinned artefact rests on real, persisted, kernel-checked proof
terms.

The mechanism that makes this fit on a 32 GB machine is the
**verified-module file family**. A model file (`Cadence/Chorus.lean`,
`Cadence/FallbackReceipt.lean`) elaborates the transition system and persists
its VC *statements* in an olean-carried registry — it runs no solver
and persists no proofs. One proof file per action
(`<Model>/Proofs/<Action>.lean`) re-creates that action's VCs from the
registry — statements identical to what the model declares, by
construction — discharges them (cvc5 + reconstruction), persists every
proof as a kernel-checked theorem in its own small olean, and exports
one "this action preserves the invariants" lemma; keeping each action's
proofs in their own process/olean is what bounds memory (~5 GB per file
cold). The 11 quorum-intersection cells that SMT cannot find are manual
`#prove_vc … by <tactic>` cells in their actions' proof files, consumed
after a statement check — the statement itself always comes from the
registry, and the tactics project invariant conjuncts by name
(`Cadence/ProofPrelude.lean`), so nothing in a proof file restates or
hand-indexes what the model declares. `<Model>/Certify.lean` composes the per-action lemmas
(`#gen_composition`) into `invariants_of_reachable` plus named
per-property projections, pins the axiom base, and re-audits the whole
set with a pinned `#veil_status` line — per VC, a real,
statement-matching, kernel-checked theorem must be in scope, or the
build fails.

What remains trusted is inventoried in §4 item 6 — Lean's kernel,
Veil's VC generation, the model checker where used, and the solver's
`sat` verdicts on non-load-bearing `sat trace` checks.

## 7. The verification pipeline this rests on

Making the above affordable took real work on the verification tool
itself. That work is **not** documented here: it lives in the public Veil
fork this project pins, one branch per change, with its own rationale.
What this repository records is only *which* capabilities it depends on
and why — [Dependencies.md](./Dependencies.md).

The short version, since it explains the shape of the file tree: a
persistent registry of VC statements plus cross-file proving commands
(so the proofs of one model can be spread over many small files, §6); a
kernel-replaying proof cache (so re-validation costs minutes, and is
deterministic rather than solver-seed-dependent); composition emission
and the `#veil_status` audit command (so the certificates and the
"nothing is stubbed" claim are machine-derived); and a handful of
scaling fixes without which a 3 822-VC module does not elaborate at all.

The one measurement worth keeping in this document, because it bounds
what a future scaling effort can win: reconstruction proof terms of the
same action share 65–92 % of their term mass, and 65–72 % of a single
term was the SMT pipeline re-deriving the `Bool → Prop` embedding of the
whole hypothesis context. The fork removes that part; hoisting the
remaining shared hypothesis processing into named, once-checked lemmas is
the next structural lever.

## 8. History

Decision history and per-build records intentionally live outside this
document: [History.md](./History.md) (build history, per-module status) and
the git log. [ChorusDesign.md](./ChorusDesign.md) §7.2 carries the one
protocol bug found so far, because that record is a result rather than a
build log.
