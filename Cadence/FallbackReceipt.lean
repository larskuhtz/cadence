import Veil
import Cadence.Tooling

/-! # FallbackReceipt — the fallback receipt/propose layer (shipped design)

*This is a **model file** of the verified-module file family
(`docs/Architecture.md` §6): it elaborates the transition system and
persists the VC registry, but runs **no invariant sweep** — the proofs
live in the per-action files under
[`FallbackReceipt/Proofs/`](./FallbackReceipt/Proofs), composed into the
reachability certificate by
[`FallbackReceipt/Certify.lean`](./FallbackReceipt/Certify.lean). Opening
this file in an editor costs the model elaboration plus the (cheap)
background `doesNotThrow` checks and the bounded model check.*

Mechanization of the layer behind the §7.2 finding (`docs/ChorusDesign.md` §7.2, §9
item 6): the per-validator receipt of `FallbackVote`s and the once-only
MVBA propose with the atomic per-proposer build, exactly as the paper
*shipped* it on 2026-07-07 (`alg:fallback`) — the receipt restriction at
`line:fb-accept` (a vote is accepted only if every entry is a valid
FastQC or the sender's *own* valid fallback signed entry), FastQC
harvesting at `line:fb-harvest`, and the atomic build at
`line:fb-build-entry`–`line:fb-formqc`. The companion module
`FallbackReceipt/PreFix.lean` models the
*pre-fix* rules and mechanically refutes them.

This module is deliberately *per-validator*: it models one (correct)
receiving validator `i` — its `M_i`, its `Ev` harvest, its build. The
network enters only as the nondeterministic arrival of receiver-verified
vote content.

## Verified claims

* **`certified_propose` (safety, SMT, all `n`)** — whenever the propose
  fires, every proposer's built entry is certificate-backed: a harvested
  FastQC, an EquivCert assembled from two conflicting positive signed
  entries in `M_i`, or a FallbackQC from `f+1` matching signed entries
  in `M_i`. This is the paper's "`B` is valid by construction".
* **Build totality (the per-validator pigeonhole, proven for all `n` in
  `FallbackReceipt/Totality.lean`)** —
  once `|M_i| ≥ 2f+1`, one of the three build cases applies for *every*
  proposer (`line:fb-build-entry`, "one of the three cases always
  applies, by counting"): if no FastQC was harvested and no two positive
  entries conflict, the `2f+1` entries for the proposer span at most two
  values (one root and ⊥), so one value has `f+1` matching copies.
  **The two-class counting step is not SMT-dischargeable at the abstract
  `ByzNodeSet` level** — partitioning a quorum by the value its members
  signed requires set comprehension, which is outside the class's
  first-order language (`docs/ChorusDesign.md` §7, "Evidence pigeonhole"; the same
  crux as Chorus's meta-level step), a module-level `assumption` cannot
  mention mutable relations, and the statement is not even *true* in
  every model of the axioms — so it is deliberately **not** a declared
  invariant of this module (its abstract VCs would be unprovable, which
  would poison the proof-file family). It is instead proven as a
  plain-Lean theorem over the concrete instance *family*
  `byzNodeSetFin n f` — every `n = 3f+1`, arbitrary proposer and root
  types — in `FallbackReceipt/Totality.lean`, from a single SMT-proven
  structural invariant (`accepted_entries_complete`), and lifted to all
  reachable states there via the `#gen_composition` certificate
  (`FallbackReceipt/Certify.lean`).
  That is strictly stronger than the earlier bounded `#model_check`
  argument at `n = 4`; the model check below remains as a fast
  exhaustive regression over the structural invariants.

Note the counting needs **no honesty split**: any `2f+1` *accepted*
votes suffice, Byzantine senders included — the receipt restriction
alone pins each accepted vote to FastQC-or-own-entry, and FallbackQCs
aggregate any `f+1` matching signatures. (Contrast the paper's §7
*global* pigeonhole over honest entries; the per-validator argument is
what the §7.2 fix made work.)

## Integration seam (the (A-mvba) implementability leg)

This module discharges the per-validator implementability of (A-mvba)'s
premise (`docs/ChorusDesign.md` §7, `Chorus.lean` liveness section): network-global
evidence → every correct validator proposes a *valid* meta-block.
*Assumed* from Chorus (facts proven there over the shared vocabulary):

| here | Chorus / paper |
|---|---|
| `carried_fastqc r P m` arrival | a valid FastQC for `(P, m)` on the wire — Chorus ghost `vote_quorum_pos`; validity receiver-verified |
| `carried_pos r P m` arrival | `r`'s own positive fallback signed entry — Chorus `msg_fb_pos_sig r P m`; its `σ_p` verifies, so `msg_proposer_signed P m` holds |
| `carried_neg r P` arrival | Chorus `msg_fb_neg_sig r P` |
| eventually `2f+1` accepted | `progress_fallback_signing` + the honest supermajority casts fallback votes (Chorus liveness case split, `x = 0`/mixed branches) |

*Guaranteed*: `certified_propose` + build totality
(`FallbackReceipt/Totality.lean`) + (F-justice) on the build/propose
actions ⇒ every correct validator that receives `2f+1` fallback votes
proposes a valid meta-block. The seam is meta-level (documented, not a
Lean composition) pending VC persistence for *Chorus*
(`docs/Architecture.md` §6) — within *this* module the chain is closed
in Lean end-to-end (`build_totality_of_reachable` in the totality
file), matching the integration mode pinned in `docs/ChorusDesign.md` §9 item 6.

## Locality regime — deliberately different from `Chorus.lean`

All mutable state here is *local to the receiving validator* (its
`M_i`, its harvest, its build state) — category (L) of `docs/ChorusDesign.md`
§3.5. The monotone-network contract (`docs/ChorusDesign.md` §3.1.1) is therefore
**not invoked**: negative guards over this state are sound (a validator
observes its own receipt state exactly), including the build rule's
faithful `else if` precedence guards. Asynchrony enters solely through
arbitrary interleavings of the delivery/acceptance actions.

## Modelling notes / deviations

* `proposer` is a separate index type (in Chorus, `Ps ⊆ Π`): the receipt
  layer never uses a proposer's node identity, only its entry slot.
* The paper's atomic build-and-propose is decomposed into per-proposer
  `build_entry_*` actions plus a `propose` umbrella (the standard Veil
  idiom, cf. `Chorus.lean` §"Per-proposer signing decomposed"). Entries
  may thus be selected against a *growing* `M_i` rather than the exact
  trigger-time snapshot — an over-approximation of schedules that
  affects neither certification (backing is monotone) nor totality.
* The build cases carry the paper's `if / else if / else` precedence as
  explicit negative guards (sound here, see the locality regime).
* Entries are frozen per sender at acceptance (`first` message only,
  the receive handler's guard).
* Carried FallbackQCs are not modelled: on the shipped wire a fallback
  vote carries only FastQCs or own entries (`line:fb-accept`), so the
  kind does not exist. -/

veil module FallbackReceipt

type node
type nodeset
type proposer
type merkle_root

instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet

/-! ## Wire state — receiver-verified `FallbackVote` content

`carried_* r P …` is the entry for proposer `P` in the (unique, per
sender `r`) fallback vote that has reached the receiving validator, and
it exists only in receiver-verified form: a `carried_fastqc` is a FastQC
whose `2f+1` signatures verified; a `carried_pos` carries `r`'s own
signature and a verifying proposer signature `σ_p`. Exactly one entry
kind per proposer per vote (the delivery guards). -/

relation carried_fastqc (r : node) (p : proposer) (m : merkle_root)
relation carried_pos (r : node) (p : proposer) (m : merkle_root)
relation carried_neg (r : node) (p : proposer)

-- `r`'s vote passed the `line:fb-accept` receipt restriction: membership
-- of `M_i`.
relation accepted (r : node)

/-! ## Build state — the assembled meta-block entries -/

relation built_fastqc (p : proposer) (m : merkle_root)
relation built_equiv (p : proposer)
relation built_fbqc_pos (p : proposer) (m : merkle_root)
relation built_fbqc_neg (p : proposer)
-- `MVBA[s].propose(B)` has fired (`line:fb-mvba-propose`); once-only
-- (`mvbaInvoked`).
individual proposed : Bool

#gen_state

/-! ## Derived state (ghosts) -/

-- `Ev(p)` holds a harvested FastQC (`line:fb-harvest`; harvesting is
-- atomic with receipt, so it is derived state).
ghost relation ev_fastqc (p : proposer) (m : merkle_root) :=
  ∃ r, accepted r ∧ carried_fastqc r p m

-- `|M_i| ≥ 2f+1` — the propose trigger (`line:fb-build-entry` guard).
ghost relation received_supermajority :=
  ∃ q, nset.supermajority q ∧ ∀ r, nset.member r q → accepted r

-- Two conflicting positive signed entries in `M_i`: the EquivCert build
-- case (`line:fb-build-equiv`). The two entries carry verifying `σ_p`s
-- on distinct roots — the certificate's content. (Distinct senders are
-- implied: one sender has at most one entry per proposer.)
ghost relation equiv_available (p : proposer) :=
  ∃ r1 r2 m1 m2, m1 ≠ m2 ∧
    accepted r1 ∧ carried_pos r1 p m1 ∧
    accepted r2 ∧ carried_pos r2 p m2

-- `f+1` matching positive signed entries in `M_i`: a positive FallbackQC
-- is formable (`line:fb-formqc`).
ghost relation fbqc_pos_available (p : proposer) (m : merkle_root) :=
  ∃ q, nset.greater_than_third q ∧
    ∀ r, nset.member r q → accepted r ∧ carried_pos r p m

-- The negative counterpart (`f+1` matching `⟨s, p, ⊥⟩` entries).
ghost relation fbqc_neg_available (p : proposer) :=
  ∃ q, nset.greater_than_third q ∧
    ∀ r, nset.member r q → accepted r ∧ carried_neg r p

-- The build produced an entry for `p` (of whichever kind).
ghost relation entry_built (p : proposer) :=
  (∃ m, built_fastqc p m) ∨ built_equiv p ∨
  (∃ m, built_fbqc_pos p m) ∨ built_fbqc_neg p

/-! ## Initial state -/

after_init {
  carried_fastqc R P M := false
  carried_pos R P M := false
  carried_neg R P := false
  accepted R := false
  built_fastqc P M := false
  built_equiv P := false
  built_fbqc_pos P M := false
  built_fbqc_neg P := false
  proposed := false
}

/-! ## Delivery — the environment presents vote content

Sender-nondeterministic (honest or Byzantine — on the shipped wire both
are confined to the same entry kinds), receiver-verified. One entry kind
per proposer per vote; entries freeze once the vote is accepted. -/

action deliver_entry_fastqc (r : node) (p : proposer) (m : merkle_root) {
  require ¬ accepted r
  require ∀ M, ¬ carried_fastqc r p M
  require ∀ M, ¬ carried_pos r p M
  require ¬ carried_neg r p
  carried_fastqc r p m := true
}

action deliver_entry_pos (r : node) (p : proposer) (m : merkle_root) {
  require ¬ accepted r
  require ∀ M, ¬ carried_fastqc r p M
  require ∀ M, ¬ carried_pos r p M
  require ¬ carried_neg r p
  carried_pos r p m := true
}

action deliver_entry_neg (r : node) (p : proposer) {
  require ¬ accepted r
  require ∀ M, ¬ carried_fastqc r p M
  require ∀ M, ¬ carried_pos r p M
  require ¬ carried_neg r p
  carried_neg r p := true
}

/- Receipt (`line:fb-accept`, the 2026-07-07 restriction): the first
`FallbackVote` from `r` joins `M_i` iff it carries, for every proposer,
a valid FastQC or `r`'s own valid signed entry. (Votes carrying anything
else — e.g. an EquivCert, cf. the pre-fix module — are rejected; in this
module's vocabulary such votes cannot even be expressed, which *is* the
restriction.) -/
action accept_vote (r : node) {
  require ¬ accepted r
  require ∀ P, (∃ M, carried_fastqc r P M) ∨ (∃ M, carried_pos r P M) ∨
    carried_neg r P
  accepted r := true
}

/-! ## The atomic build (`line:fb-build-entry`–`line:fb-formqc`)

Fires at the propose trigger (`|M_i| ≥ 2f+1`, once-only), one case per
proposer with the paper's `if / else if / else` precedence as explicit
guards. -/

action build_entry_fastqc (p : proposer) (m : merkle_root) {
  require ¬ proposed
  require received_supermajority
  require ¬ entry_built p
  -- `line:fb-build-fast`
  require ev_fastqc p m
  built_fastqc p m := true
}

action build_entry_equiv (p : proposer) {
  require ¬ proposed
  require received_supermajority
  require ¬ entry_built p
  -- else: no FastQC harvested …
  require ∀ M, ¬ ev_fastqc p M
  -- `line:fb-build-equiv`
  require equiv_available p
  built_equiv p := true
}

action build_entry_fbqc_pos (p : proposer) (m : merkle_root) (q : nodeset) {
  require ¬ proposed
  require received_supermajority
  require ¬ entry_built p
  -- else: neither of the first two cases …
  require ∀ M, ¬ ev_fastqc p M
  require ¬ equiv_available p
  -- `line:fb-formqc`: f+1 matching positive signed entries.
  require nset.greater_than_third q
  require ∀ r, nset.member r q → accepted r ∧ carried_pos r p m
  built_fbqc_pos p m := true
}

action build_entry_fbqc_neg (p : proposer) (q : nodeset) {
  require ¬ proposed
  require received_supermajority
  require ¬ entry_built p
  require ∀ M, ¬ ev_fastqc p M
  require ¬ equiv_available p
  require nset.greater_than_third q
  require ∀ r, nset.member r q → accepted r ∧ carried_neg r p
  built_fbqc_neg p := true
}

/- `MVBA[s].propose(B)` (`line:fb-mvba-propose`): once-only, at the
trigger, with the meta-block complete. -/
action propose (q : nodeset) {
  require ¬ proposed
  require nset.supermajority q
  require ∀ r, nset.member r q → accepted r
  require ∀ P, entry_built P
  proposed := true
}

/-! ## Safety — "B is valid by construction" -/

safety [certified_propose]
  proposed →
    ∀ (P : proposer),
      (∃ M, ev_fastqc P M) ∨ equiv_available P ∨
      (∃ M, fbqc_pos_available P M) ∨ fbqc_neg_available P

/-! ## Structural invariants (wire discipline, backing, build sanity) -/

/- Lifted `accept_vote` guard: every member of `M_i` carries an entry for
every proposer. The pigeonhole's "at least one" leg. -/
invariant [accepted_entries_complete]
  ∀ (R : node) (P : proposer),
    accepted R →
      (∃ M, carried_fastqc R P M) ∨ (∃ M, carried_pos R P M) ∨
      carried_neg R P

/- Lifted delivery guards: exactly-one entry kind per (sender, proposer). -/
invariant [carried_fastqc_unique]
  ∀ (R : node) (P : proposer) (M M2 : merkle_root),
    carried_fastqc R P M ∧ carried_fastqc R P M2 → M = M2

invariant [carried_pos_unique]
  ∀ (R : node) (P : proposer) (M M2 : merkle_root),
    carried_pos R P M ∧ carried_pos R P M2 → M = M2

invariant [carried_fastqc_pos_excl]
  ∀ (R : node) (P : proposer) (M M2 : merkle_root),
    ¬ (carried_fastqc R P M ∧ carried_pos R P M2)

invariant [carried_fastqc_neg_excl]
  ∀ (R : node) (P : proposer) (M : merkle_root),
    ¬ (carried_fastqc R P M ∧ carried_neg R P)

invariant [carried_pos_neg_excl]
  ∀ (R : node) (P : proposer) (M : merkle_root),
    ¬ (carried_pos R P M ∧ carried_neg R P)

/- Certificate backing of the built entries (`certified_propose`'s
per-kind content; each is the lifted build guard, stable because
`accepted`/`carried_*` are monotone). -/
invariant [built_fastqc_backed]
  ∀ (P : proposer) (M : merkle_root), built_fastqc P M → ev_fastqc P M

invariant [built_equiv_backed]
  ∀ (P : proposer), built_equiv P → equiv_available P

invariant [built_fbqc_pos_backed]
  ∀ (P : proposer) (M : merkle_root),
    built_fbqc_pos P M → fbqc_pos_available P M

invariant [built_fbqc_neg_backed]
  ∀ (P : proposer), built_fbqc_neg P → fbqc_neg_available P

/- One built entry per proposer (lifted `¬ entry_built` guards): the
meta-block is a per-proposer map. -/
invariant [built_fastqc_unique]
  ∀ (P : proposer) (M M2 : merkle_root),
    built_fastqc P M ∧ built_fastqc P M2 → M = M2

invariant [built_fbqc_pos_unique]
  ∀ (P : proposer) (M M2 : merkle_root),
    built_fbqc_pos P M ∧ built_fbqc_pos P M2 → M = M2

invariant [built_fastqc_equiv_excl]
  ∀ (P : proposer) (M : merkle_root), ¬ (built_fastqc P M ∧ built_equiv P)

invariant [built_fastqc_fbqc_pos_excl]
  ∀ (P : proposer) (M M2 : merkle_root),
    ¬ (built_fastqc P M ∧ built_fbqc_pos P M2)

invariant [built_fastqc_fbqc_neg_excl]
  ∀ (P : proposer) (M : merkle_root),
    ¬ (built_fastqc P M ∧ built_fbqc_neg P)

invariant [built_equiv_fbqc_pos_excl]
  ∀ (P : proposer) (M : merkle_root),
    ¬ (built_equiv P ∧ built_fbqc_pos P M)

invariant [built_equiv_fbqc_neg_excl]
  ∀ (P : proposer), ¬ (built_equiv P ∧ built_fbqc_neg P)

invariant [built_fbqc_pos_neg_excl]
  ∀ (P : proposer) (M : merkle_root),
    ¬ (built_fbqc_pos P M ∧ built_fbqc_neg P)

/- Lifted `propose` guards: the propose is trigger-gated and complete. -/
invariant [proposed_supermajority]
  proposed → received_supermajority

invariant [proposed_entries_built]
  proposed → ∀ (P : proposer), entry_built P

/- NOTE: the per-validator pigeonhole ("build totality" — at the
trigger, one build case applies for every proposer) is deliberately
NOT a declared invariant: its abstract VCs are unprovable (the
two-class counting is outside the abstract `ByzNodeSet` language and
fails in non-standard models of the axioms), which would poison both
`#check_invariants` and `#gen_theorems`. It is stated and proven for
all `n = 3f+1` over the concrete instance family in
`FallbackReceipt/Totality.lean`,
using only `accepted_entries_complete` from the clump above. -/

/- Proof reconstruction ON (this module only): captured at `#gen_spec`,
so it governs the background `doesNotThrow` dischargers this file still
runs. The invariant proofs live in the proof-file family, which sets the
option itself (read at tactic runtime on the cross-file path) — every
persisted theorem carries **no** `sorryAx`, and the totality file's
`build_totality_of_reachable` is kernel-checked end-to-end (its
`#print axioms` is the standard `propext`/`Classical.choice`/`Quot.sound`
trio). -/
set_option veil.smt.trust false

/- VC registry (`docs/Dependencies.md` §1): `#gen_spec`
persists every VC's statement (as an `Expr`) plus its action/property/
style metadata into the olean. This is the model file's entire proof
interface: the family's `#prove_action`/`#prove_vc` commands re-create
the VCs from these statements — identical to what any in-file sweep
would check, by construction. Solve-free; costs one statement
elaboration per VC here and ~2 KB/VC of olean. -/
set_option veil.gen.vcRegistry true

/- Proof cache (`docs/Dependencies.md` §2): consult the
content-addressed cache (`.lake/build/veilcache/`) for the `doesNotThrow`
dischargers, and store their proofs. The family's proof files enable the
cache themselves. File-level so the dischargers capture it at `#gen_spec`
(solver options are captured there, not at the command). -/
set_option veil.cache.proofs true

#gen_spec

/-! ## Verification

Three legs (see the module header):

1. **Abstract (all `n`), SMT — in the proof-file family, not here**: one
   `#prove_action` per action under
   [`FallbackReceipt/Proofs/`](./FallbackReceipt/Proofs) proves every
   registered VC cross-file and persists it as a kernel-checked theorem;
   [`FallbackReceipt/Certify.lean`](./FallbackReceipt/Certify.lean)
   composes the per-action preservation lemmas into
   `FallbackReceipt.invariants_of_reachable` (+ named `reachable_*`
   projections) via `#gen_composition`. This file itself only starts the
   (cheap) background `doesNotThrow` checks at `#gen_spec`.
2. **Concrete (`n = 4, f = 1`, one proposer, two roots), exhaustive**:
   `#model_check` over the `insByzNodeSetFinSimple` instance — a fast
   full-reachability regression over the same declarations (and a
   non-vacuity witness: the explored graph contains proposing runs).
3. **The totality closure**: `FallbackReceipt/Totality.lean` consumes the
   certificate to lift the pigeonhole theorem to every reachable state. -/

#model_check interpreted
  { node := Fin (3 * 1 + 1), nodeset := ByzNSet (3 * 1 + 1),
    proposer := Fin 1, merkle_root := Fin 2 } {}

end FallbackReceipt
