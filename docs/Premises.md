# The premises

*The page to read first. Every liveness claim of this development is
conditional: it holds in every run that meets its premises. The premises
play the role of the claim's axioms, so they are what an auditor has to
believe. This page lists each one once, says what it is for and why it is
plausible, and points to the evidence for the two properties the machine
can check.*

**What is machine-checked about the premises, and what is not.**

* **Consistency.** All premises of a claim hold together in one model: a
  *witness theorem* exhibits an instance and a run meeting every one of
  them at once. A claim whose premises could never hold together would be
  vacuous. Every claim below has its witness.
* **Each premise is used.** Every premise is consumed by some step of the
  claim's proof, so none of them can be dropped without a replacement.
  This is the best-effort half of independence (§7 says how it was
  checked).
* **Completeness** comes from the proofs: the claims are proven from
  exactly the premises listed, kernel-checked, with no further axiom
  ([Cadence.lean](../Cadence.lean) pins every axiom footprint).
* **Plausibility is the auditor's judgement.** No tool can check that a
  premise describes the runs a real network and a real implementation
  produce. Each entry below therefore says, in one line, why it is
  plausible on its own, and names the paper's sentence it formalises, or
  says that it is a modelling choice and where the choice is justified.

**How an entry reads.** The heading is the premise's Lean name and, where
it has one, its tag. Then, one line each:

* **Role** — what the premise is for, in plain words.
* **Plausible** — why a real environment or implementation meets it.
* **Satisfiable** — "obvious", or the witness theorem that shows it.
* **Used in** — the proof step that consumes it.
* **Paper** — the paper's statement it formalises, or "modelling choice"
  with a pointer to the justification.

The premises' definitions are in
[Chorus/Liveness.lean](../Cadence/Chorus/Liveness.lean),
[Chorus/Schedule.lean](../Cadence/Chorus/Schedule.lean),
[Mvba/Liveness.lean](../Cadence/Mvba/Liveness.lean) and
[Mvba/Schedule.lean](../Cadence/Mvba/Schedule.lean); each docstring starts
with the role line of this page.

## Contents

1. [The claims and their premises](#1-the-claims-and-their-premises)
2. [The setting: hypotheses on the instance](#2-the-setting-hypotheses-on-the-instance)
3. [Scheduling: the untimed premises](#3-scheduling-the-untimed-premises)
4. [Timing: the timed premises](#4-timing-the-timed-premises)
5. [The seam between Chorus and the MVBA](#5-the-seam-between-chorus-and-the-mvba)
6. [The caller's conditions](#6-the-callers-conditions)
7. [Independence: every premise is used](#7-independence-every-premise-is-used)
8. [What is not a premise](#8-what-is-not-a-premise)

## 1. The claims and their premises

Each row is a headline claim, the premises it takes (by the section of this
page that has them), and its witness. The safety claims take no run
premise; their hypotheses are §2's and the trust items of
[Architecture.md](Architecture.md) §4.

| Claim | Premises | Witness |
|---|---|---|
| `Chorus.termination` — every correct validator finalizes the slot | §2.1, §2.3, §2.4; `FJustice` §3.1, `MvbaAdmissible` §3.2; `ValidBridge` §5.1; `AllParticipate` §6.1, C1 §6.2 | `Chorus.termination_premises_satisfiable` |
| `Chorus.timed_termination_atMvba`, `…_tight_atMvba` — every correct validator finalizes by `max(t, GST) + 5Δ + ℓ_MVBA + 9δ` (tight: `4Δ + ℓ_MVBA + 8δ`) | §2.1–§2.8; `TimedJustice` §4.1, `PhasePunctual` §4.2, `MvbaOwnTiming` §4.3; `ValidBridge` §5.1; `AllParticipateBy t` §6.1, C1 §6.2, C2 §6.3, `SyncParticipationWithin Δ` §6.4 | `Chorus.timedTermination_premises_satisfiable` |
| `Chorus.timed_termination`, `…_tight` — the same, for any MVBA contract `T` | as above, with `TimedMvbaAdmissible T` §4.3 in place of `MvbaOwnTiming`, and `0 ≤ ℓ_MVBA` §2.9 in place of the MVBA instance's §2.2 and §2.5–§2.7 | through the row above (at the system's MVBA, `0 ≤ ℓ_MVBA` is a theorem) |
| `Chorus.totality` — once one correct validator finalizes at `c`, all do by `max(c, GST) + max(Δ, d) + 2δ` | §2.1 (finitely many validators), §2.8; `TimedJustice` §4.1; C1 §6.2, `SyncParticipationWithin d` §6.4 | `Chorus.totality_premises_satisfiable` |
| `Chorus.chorusTemporal`, `Chorus.chorusWithTotality`, `Chorus.slotConsensusFull` — Chorus ⊨ the full `SlotConsensus` contract | the three rows above (`Admissible` names their run premises), and the non-empty proposer set §2.10 | `Chorus.admissible_exists` (every initial state) |
| `Mvba.termination` — every correct validator decides | §2.1, §2.2, §2.3, §2.4; `Mvba.FJustice` §3.3, (A-viewsync) §3.4, (F-avail) §3.5; `AllPropose`, `NoEarlyAbandon`, (F-relay) §6.5 | `Mvba.termination_premises_satisfiable` |
| `Mvba.bounded_termination`, `Mvba.timed_termination` — every correct validator decides by `max(t, GST) + ℓ_MVBA` | §2.1–§2.7; `Mvba.Sync` §4.4–§4.7; the timed caller conditions §6.5 | `Mvba.timedTermination_premises_satisfiable` |
| `Mvba.mvbaTemporal`, `Mvba.mvbaFull` — Mvba ⊨ the full `MVBA` contract | the row above (`Admissible` is `Mvba.Sync`) | `Mvba.admissible_exists` (every initial state) |
| `Cadence.system_positional_log_safety` — two correct validators never disagree on a log position, in the composed system | `ACSSafety` (the ACS primitive, assumed: [Architecture.md](Architecture.md) §4 item 3); the quorum classes of §2.1; the three modules' configurations, with the models' assumptions of §2.4; that the Conductor and Chorus agree on who is Byzantine (`hbyz`, [CompositionContracts.md](CompositionContracts.md) §7) | — (a safety claim: it holds in every reachable state) |

"Finitely many validators" in the Chorus rows is `Fin n`; the timed claims
need it through the totality step, and `Chorus.totality` takes it as
`Fintype node` at any quorum system.

## 2. The setting: hypotheses on the instance

Hypotheses about the validators, the quorum system, the views, time and the
schedule. They constrain the *instance*, not the run, so every run of the
instance shares them. All of them are obvious; the witnesses meet them
with four validators, one Byzantine, views and clock `ℕ`, and `Δ = 1`.

### 2.1 Validators and faults

`n = 3f + 1` validators, `Fin n`, at most `f` of them Byzantine
(`byzNodeSetFin n f`, the Chorus claims); for the MVBA, any quorum system
satisfying `ByzNodeSet`'s axioms over finitely many validators
(`Fintype node`).

* **Role:** the fault threshold: any two supermajorities share a correct
  validator, and the correct validators are a supermajority.
* **Plausible:** the standard Byzantine setting; a deployment fixes `n`
  and tolerates `f` faults.
* **Satisfiable:** obvious; `ByzNodeSet`'s axioms are proven for every
  `n ≥ 3f + 1` and every Byzantine set of size at most `f`
  (`byzNodeSetFinGen`, [ByzQuorum.lean](../Cadence/ByzQuorum.lean)).
* **Used in:** Chorus: `honest_supermajority` (`saturation_fin`,
  `mvba_evidence_of_saturation`) and the counting class (the FallbackQC's
  correct signer, `eventually_fbcommit_sig`); timed: `honest_quorum_fin`
  (`within_all_saturated`). MVBA: finiteness gives the quorum enumeration
  (`ByzNodeSetEnum.ofFintype`) both termination proofs assemble
  certificates with, and the common deadline of `Mvba.aViewSync_of_sync`.
* **Paper:** Section 2 (`subsection:mcp-overview`): "`n = 3f + 1`
  validators, of which up to `f > 0` may be faulty".

### 2.2 A correct supermajority: `ByzNodeSetHonestQuorum`

* **Role:** some supermajority consists of correct validators only.
* **Plausible:** at most `f` of `3f + 1` are Byzantine, so the other
  `2f + 1` are such a set.
* **Satisfiable:** obvious; proven for every `n ≥ 3f + 1`
  ([ByzQuorum.lean](../Cadence/ByzQuorum.lean)), and at the Chorus family
  it is a theorem (`Chorus.hqeFin`).
* **Used in:** `Mvba.termination` (`eventually_tc_below_good`,
  `terminates_of_settled_honest_view`), `Mvba.bounded_termination`
  (`within_tc`, `exists_good_view`).
* **Paper:** a consequence of §2.1; modelling choice to state it apart
  ([Architecture.md](Architecture.md) §4 item 3: the intersection axioms
  do not give it).

### 2.3 Views: `ViewOrderEnum`

* **Role:** every view has a next one, and finitely many lie below each.
* **Plausible:** views are a counter.
* **Satisfiable:** obvious; `ℕ` (`natViewOrderEnum`).
* **Used in:** the MVBA's view change: `eventually_tc_below_good` (an
  induction over the views below the good one), `Mvba.bounded_termination`
  (`ℓ_MVBA` counts `|below v_L|` views); Chorus reaches it only through
  `Mvba.termination` (`all_decided_of_all_input`).
* **Paper:** modelling choice; a view with nothing directly above it is a
  view no validator can leave ([Architecture.md](Architecture.md) §4
  item 3).

### 2.4 The models' assumptions

`Chorus.lean`'s `mvba_init` (the MVBA starts in an initial state),
`mval_pos_functional` and `mval_pos_neg_excl` (theorems at the system's
configuration, `chorusTheory_assumptions`); `Mvba.lean`'s
`leader_functional` (one leader per view) and `leader_honest_cofinal`
(above every view there is a correct-led one). The system's configurations
fix the rest: `Cadence.chorusTheory`, and `Cadence.mvbaTheory`, whose
entry vector of a meta-block is its own entries (`ent :=
MetaBlock.entries`); the validity predicate and the leader schedule stay
arbitrary.

* **Role:** the configuration the claims are about: an MVBA that has not
  started, and a leader schedule.
* **Plausible:** a slot's MVBA instance starts fresh; a leader schedule
  is a function, and round-robin reaches every validator.
* **Satisfiable:** obvious; the witnesses use the MVBA's initial state and
  validator 0 as every view's leader.
* **Used in:** `abandoned_of_mvba_abandoned` and `eventually_mvba_complete`
  (`mvba_init`: the MVBA's records start empty and its reachability holds),
  `certified_certifiedVector` (`ent`), and the MVBA's safety invariants
  (`leader_functional`: one `Pre-Prepare` per view's leader).
  `leader_honest_cofinal` is used by no claim's proof (§7).
* **Paper:** Supplement, Section 1.2 (`subsec:mvba-protocol`) (the leader
  schedule); `ent` is the paper's `entries(B)`. These are Veil model
  `assumption`s: their comments are in [Chorus.lean](../Cadence/Chorus.lean)
  and [Mvba.lean](../Cadence/Mvba.lean) and do not carry this page's role
  line, since a comment edit in a model file rebuilds its proof family.

### 2.5 A correct leader in every `k` views: `LeaderRotation`, (A-leader-rotation-k)

* **Role:** among any `k` consecutive views one has a correct leader.
* **Plausible:** round-robin over `n = 3f + 1` validators gives
  `k = f + 1`.
* **Satisfiable:** obvious; the witnesses take `k = 1`.
* **Used in:** `Mvba.bounded_termination` (`exists_good_view`: the good
  view is reached after fewer than `k` burnt views) and
  `Mvba.aViewSync_of_sync`; `Chorus.admissible_exists` takes the good view
  from it (`goodView_of_rotation`).
* **Paper:** Supplement, Section 1.2 (`subsec:mvba-protocol`): "every
  `f+1` consecutive views contain a correct leader".

### 2.6 Time

A cancellative, Archimedean, linearly ordered additive monoid.

* **Role:** clock readings can be added, compared and cancelled, and no
  time is beyond every multiple of a delay.
* **Plausible:** real time, or `ℕ` ticks.
* **Satisfiable:** obvious; `ℕ`.
* **Used in:** cancellation by `Mvba.bounded_termination`'s deadline
  arithmetic ([Bounds.md](Bounds.md) §6.2.8); the Archimedean property by
  `Mvba.admissible_exists` (a run's clock must be unbounded, the
  contract's non-Zeno field) and so by the two contract instances.
* **Paper:** Section 2 (`subsection:mcp-overview`) (synchronized clocks,
  a global notion of time); the algebra is a modelling choice
  ([Bounds.md](Bounds.md) §6.2.2).

### 2.7 The MVBA's schedule: `Mvba.Schedule`

`Δ` (network bound after GST), `δ` (local step), `ρ` (retransmission
interval), `Δ_sync` (availability), the view timeout `τ`, with `0 < Δ`,
the rest non-negative, (S-cap) `τ v ≤ τ_max`, and (S-ramp) from some view
`v_L` on every timeout exceeds the chain's latency `L_cert`.

* **Role:** the constants the bound is stated in, and a view timeout long
  enough for a view to decide.
* **Plausible:** the supplement's fixed timeout `T` is the case `τ`
  constant, `v_L` the first view; capped backoff also qualifies.
* **Satisfiable:** obvious; `Schedule.fixedNat`, the paper's fixed
  timeout.
* **Used in:** (S-ramp) by `good_view_decides` (the good view's budget
  covers its chain); (S-cap) by `synced_succ` (a burnt view costs at most
  `burn`); the non-negativity fields by `mvbaSchedule_ℓ_nonneg`, `Δ_pos`
  and `δ_nonneg` by `Chorus.totality` and every timeline milestone, and
  `ρ_nonneg` by `relayed_of_timedJustice`.
* **Paper:** Supplement, Section 1.2 (`subsec:mvba-protocol`), "Views,
  leaders, and timing parameters" (the fixed `T`); why a cap is needed is
  [Bounds.md](Bounds.md) §6.2.3, Finding 1.

### 2.8 The Chorus schedule: `Chorus.Schedule`

The MVBA's schedule, the slot's deadline `D`, and two inequalities.

* **`δ_le_Δ`** — *Role:* a local step is no slower than a network hop.
  *Plausible:* true at the paper's `δ = 0`, and for any implementation
  whose computation is faster than its network. *Used in:* every `Δ`-row
  milestone (`within_fb_sig`, `within_complete_fast_metablock`,
  `within_input_of_fbcert`, `within_chunk_delivered`,
  `within_finalized_late`), and the handoff's `δ ≤ Δ + ρ` in
  `timedMvbaAdmissible_of_rows`. *Paper:* modelling choice, F10
  ([Bounds.md](Bounds.md) §6.4.2).
* **`Δ_le_Δsync`** — *Role:* the MVBA's availability window covers one
  Chorus network hop. *Plausible:* the chunks the MVBA waits for are sent
  one hop earlier, by the FallbackQC's correct signer; true whenever the
  layers share `Δ`. *Used in:* `availWithin_of_timedJustice`, which
  derives the MVBA's (Δ-avail). *Paper:* modelling choice, F15
  ([Bounds.md](Bounds.md) §6.4.2), over Algorithm 5, line 12
  (`line:fb-redisseminate`) and the supplement's
  availability-synchronization assumption.
* **`D`** — the deadline, any value; its relation to the participation
  times is C2 (§6.3). *Used in:* `deadline_le_of_start` and the window
  arithmetic.
* **Satisfiable:** obvious; the witness takes `Δ = 1`, `δ = 0`, `D = 1`,
  `Δ_sync = 1`.

### 2.9 `0 ≤ ℓ_MVBA` (the generic timed claims only)

* **Role:** the MVBA contract's latency is not negative.
* **Plausible:** it is a latency.
* **Satisfiable:** obvious; at the system's MVBA it is a theorem
  (`mvbaSchedule_ℓ_nonneg`), so the `…_atMvba` forms do not take it.
* **Used in:** `within_finalized_late` (the MVBA's decision deadline comes
  after the proposals').
* **Paper:** modelling choice: an abstract contract's `ℓ` is any element
  of `time`.

### 2.10 The slot has a proposer (the contract instance only)

`∃ J, is_proposer J = true`, a hypothesis of `Chorus.chorusTemporal`,
`Chorus.chorusWithTotality` and `Chorus.slotConsensusFull`.

* **Role:** some validator is the slot's proposer; nobody has to propose.
* **Plausible:** a slot exists to carry proposals.
* **Satisfiable:** obvious; the witness has one proposer, validator 0.
* **Used in:** `Chorus.admissible_exists` only (`not_certified_of_idle`):
  with a proposer, nothing is certified before anybody signs, so
  `ValidBridge` holds with nothing to say in the idle run. With none, the
  empty meta-block would be certified everywhere.
* **Paper:** Appendix A.1 (`subsection:mcp-preliminaries`) allows an empty
  proposer set; finding P14 ([PaperAlignment.md](PaperAlignment.md) §6).

## 3. Scheduling: the untimed premises

The untimed claims say *given enough time, it terminates*. Their
scheduling premises are weak fairness: an action that stays enabled
eventually fires. Weak fairness over plain enabledness is the same premise
as weak fairness over state-changing steps here, because every fair action
fires once (`Chorus.justice_enabledMove`, `Mvba.enabledMove_of_enabled`).
Nothing is asked of a Byzantine validator's actions (F-byz).

### 3.1 `FJustice`, (F-justice) for Chorus

* **Role:** a correct validator's enabled step happens, for messages
  from correct senders.
* **Plausible:** messages between correct validators are delivered
  eventually, and a correct validator processes what it has received.
  Nothing is owed on a Byzantine validator's message, which may reach
  only some validators. The three inputs (`participate`, `abandon`,
  `propose`) are the caller's and carry no fairness.
* **Satisfiable:** obvious alone (a fair action disables itself when it
  fires); jointly with the families over every value,
  `Chorus.termination_premises_satisfiable`.
* **Used in:** every `eventually_*` step of `Chorus.termination`
  (`eventually_voted`, `eventually_saturated`, `eventually_mvba_complete`,
  `eventually_fbcommit_sig`, `eventually_committed_of_assignable`, …); the
  proposal family by `eventually_input`; the handoff family by
  `fRelay_of_fJustice`; the availability family by `fAvail_of_fJustice`.
* **Paper:** the untimed shadow of Lemma 11 (`lemma:chorus-termination`)'s
  setting, "every message between correct validators is delivered within
  `Δ`"; weak fairness is a modelling choice ([Liveness.md](Liveness.md)
  §2).

### 3.2 `MvbaAdmissible`

* **Role:** the MVBA's steps inside a Chorus run are scheduled as the
  MVBA's own termination theorem asks (§3.3 and §3.4 on the projection).
* **Plausible:** it is the MVBA's own scheduling premise, read on the
  MVBA's share of the run; the MVBA's caller premises are derived (§8).
* **Satisfiable:** `Chorus.termination_premises_satisfiable`.
* **Used in:** `all_decided_of_all_input`, which hands the projection to
  `Mvba.termination`.
* **Paper:** modelling choice: the composition of the two layers
  ([Liveness.md](Liveness.md) §2).

### 3.3 `Mvba.FJustice`, (F-justice) for the MVBA

* **Role:** a correct validator's enabled MVBA step happens, for a correct
  leader's proposal and correct quorums' votes.
* **Plausible:** as §3.1, for the MVBA's messages.
* **Satisfiable:** obvious alone; `Mvba.termination_premises_satisfiable`.
* **Used in:** every link of `Mvba.termination`'s decision chain
  (`eventually_preprepare_of_settled_leader`, `eventually_accepted_of_settled`,
  `eventually_msg_commit_of_prepare_quorum`, `eventually_tc_of_timed_out_quorum`,
  …).
* **Paper:** the untimed shadow of Supplement, Section 1.3
  (`subsec:mvba-correctness`)'s network; weak fairness is a modelling
  choice ([MvbaPlan.md](MvbaPlan.md) §3.1–§3.2).

### 3.4 `AViewSync`, (A-viewsync)

* **Role:** the view timer, as ordering constraints: timers below some
  correct-led view do fire, and that view's timer waits for a correct
  validator's decision.
* **Plausible:** it is what a timeout above the chain's latency gives
  after GST; the timed premises imply it (`Mvba.aViewSync_of_sync`).
* **Satisfiable:** a corollary of the timed premises, so it inherits their
  witness; `Mvba.termination_premises_satisfiable` checks it directly.
* **Used in:** "not too late" by `eventually_tc_below_good`; "not too
  early" by `terminates_of_good_view`.
* **Paper:** the untimed form of Supplement, Section 1.2
  (`subsec:mvba-protocol`)'s fixed timeout and Supplement, Theorem 2
  (`thm:termination`)'s good view; modelling choice for the untimed
  model ([Liveness.md](Liveness.md) §2.1).

### 3.5 `FAvail`, (F-avail)

* **Role:** a correct validator that accepted a value eventually has the
  value's availability shares.
* **Plausible:** the dissemination layer delivers the chunks.
* **Satisfiable:** obvious; `Mvba.termination_premises_satisfiable`.
* **Used in:** `eventually_msg_commit_of_prepare_quorum` (`Commit` waits
  for availability).
* **Paper:** Supplement, Lemma 5 (`lem:avail-progress`) and the
  supplement's availability-synchronization assumption, with the bound
  erased. Inside Cadence it is derived (§8).

## 4. Timing: the timed premises

The timed claims bound the latency. Their premises say that, after GST,
every step a correct validator owes happens within its bound. A window
opens at `max(clk, GST)`, so an obligation pending at GST is due a bound
after GST.

### 4.1 `TimedJustice`, (Δδ-justice)

* **Role:** each owed Chorus step happens within its hop's bound: `Δ` for
  a step that receives a message, `δ` for a local one.
* **Plausible:** after GST the network delivers within `Δ` and a correct
  validator computes within `δ`; the rows are owed only for correct
  senders, as in §3.1.
* **Satisfiable:** each row obvious alone; jointly (one clock, families
  over every value) `Chorus.timedTermination_premises_satisfiable` and
  `Chorus.totality_premises_satisfiable`.
* **Used in:** `Chorus.totality` (`within_assigned`, `within_finalized`),
  the timeline (`within_voted`, `within_fb_sig`, `within_cast`, the two
  proposal families in `within_input_of_*`), the round
  (`within_recorded`, `within_fbcommit_sig`, `within_finalized_late`), and
  the derivations of the MVBA's caller clauses (`relayed_of_timedJustice`,
  `availWithin_of_timedJustice`). The fast commit path's rows are used by
  no termination proof; they stay because the premise is "every step
  within its bound" ([Bounds.md](Bounds.md) §6.4.5).
* **Paper:** Lemma 11 (`lemma:chorus-termination`)'s setting, "after time
  `M`, every message between correct validators is delivered within `Δ`",
  and Proposition 4 (`prop:chorus-totality`).

### 4.2 `PhasePunctual`, (P-phase)

* **Role:** the slot's phase timers fire on time: not before their
  landmark (`D`, `D + Δ`, `D + 2Δ`), and by it.
* **Plausible:** validators have synchronized clocks, and a timer is a
  clock comparison.
* **Satisfiable:** obvious; the witness's markers fire at their
  landmarks.
* **Used in:** "by it" by `reached_within`, behind every milestone that
  waits for a phase; "not before" by `phase_pre_of_lt`
  (`within_entry_recorded`).
* **Paper:** the deadline timers of Appendix C.3
  (`subsection:chorus-protocol-overview`); the markers are a modelling
  choice ([Bounds.md](Bounds.md) §6.4.2).

### 4.3 `MvbaOwnTiming` (at the system's MVBA), `TimedMvbaAdmissible T` (generic)

* **Role:** the MVBA's steps inside the run meet the MVBA's own timing
  model: §4.4 and §4.5 on the projection (generic: the contract's
  `T.Admissible`).
* **Plausible:** it is the MVBA's own premise; the MVBA's two clauses on
  its caller (§4.6, §4.7) are derived from Chorus's rows (§8).
* **Satisfiable:** `Chorus.timedTermination_premises_satisfiable`.
* **Used in:** `within_all_decided`, the MVBA tail, through
  `T.termination`.
* **Paper:** modelling choice: the composition of the two layers
  ([Bounds.md](Bounds.md) §6.4.2).

### 4.4 `BoundedJustice`, (Δ-justice)

* **Role:** each owed MVBA step happens within its bound: `δ` local, `Δ`
  for a message sent at or after GST by correct senders and retained,
  `Δ + ρ` for a retransmitted timeout or timeout certificate.
* **Plausible:** it is the supplement's network clause by clause:
  delivery after GST, retransmission every `ρ`, one-view retention.
* **Satisfiable:** `Mvba.admissible_exists`, and with the rest
  `Mvba.timedTermination_premises_satisfiable`.
* **Used in:** the good view's chain (`good_view_decides`) and the view
  change (`within_tc`, `within_entered_above_of_tc`, `synced_succ`).
* **Paper:** Supplement, Section 1.3 (`subsec:mvba-correctness`)'s
  termination setting and Supplement, Section 10.3
  (`sec:reliable-delivery`) ([Bounds.md](Bounds.md) §6.2.4).

### 4.5 `TimerPunctual`, (T-timer)

* **Role:** a view timer fires exactly when the clock reaches entry plus
  timeout.
* **Plausible:** a timer is a clock comparison.
* **Satisfiable:** as §4.4.
* **Used in:** `synced_succ` and `good_view_decides` (a view lasts its
  budget, no less), `aViewSync_of_decision`.
* **Paper:** the view timer of Supplement, Section 1.2
  (`subsec:mvba-protocol`).

### 4.6 `AvailWithin`, (Δ-avail)

* **Role:** a correct validator holding a value has its availability
  shares within `Δ_sync`.
* **Plausible:** the availability layer's bound after GST.
* **Satisfiable:** as §4.4.
* **Used in:** `good_view_decides` (the `Commit` of the good view's
  chain). Inside Cadence it is derived (§8).
* **Paper:** Supplement, Section 1.2 (`subsec:mvba-protocol`),
  "Availability-synchronization assumption"; Supplement, Lemma 5
  (`lem:avail-progress`).

### 4.7 `Relayed`, (Δ-relay)

* **Role:** a decided commit certificate reaches every undecided correct
  validator within `Δ + ρ`.
* **Plausible:** the composing layer broadcasts the certificate a decision
  outputs and serves it again every `ρ`.
* **Satisfiable:** as §4.4.
* **Used in:** `within_decided_ref` (the last `Δ + ρ` of `ℓ_MVBA`). Inside
  Cadence it is derived (§8).
* **Paper:** Supplement, Lemma 13 (`lem:decision-propagation`).

## 5. The seam between Chorus and the MVBA

### 5.1 `ValidBridge`

* **Role:** the MVBA's validity check is Chorus's certificate check: a
  certified meta-block is `Valid`, and one a correct validator decided or
  accepted is certified.
* **Plausible:** certificates cannot be forged and are publicly
  verifiable, so validity *is* carrying genuine certificates. It is the
  cryptographic seam, not a scheduling assumption.
* **Satisfiable:** not obvious (it relates two sub-states);
  `Chorus.termination_premises_satisfiable` and
  `Chorus.timedTermination_premises_satisfiable`, with `valid := (· = v⋆)`
  ([Bounds.md](Bounds.md) §6.4.5).
* **Used in:** soundness by `eventually_committed_of_mvba_arm` and
  `within_finalized_late` (a correct validator can propose); completeness
  by `eventually_mvba_complete`, `within_recorded` (the decision handlers'
  check) and `eventually_fbcommit_sig` (a FallbackQC entry has a correct
  signer); the held-value clause by `fAvail_of_fJustice` and
  `availWithin_of_timedJustice`.
* **Paper:** Module 3 (`mod:mvba`)'s external validity, with `Valid` read
  as certificate verification; modelling choice for the composition
  ([CompositionContracts.md](CompositionContracts.md) §7 item 1). The
  accepted-value clause reads the MVBA's internal state: P12
  ([PaperAlignment.md](PaperAlignment.md) §6).

## 6. The caller's conditions

The module's caller controls these, not the scheduler. They are the
contract's own antecedents, and within Cadence the composition meets them.
All of them hold together in a run where everyone participates at `D − Δ`
and abandons only after finalizing, the Conductor's steady state.
C1 and C2 also appear, unnamed, as antecedents of the contract fields in
[Interfaces.lean](../Cadence/Interfaces.lean); their comments there do not
carry this page's role line, since Chorus.lean imports that file and a
comment edit would rebuild the Chorus family.

### 6.1 `AllParticipate`, `AllParticipateBy t`

* **Role:** every correct validator invokes `participate()` (by `t`).
* **Plausible:** the glue participates when it opens the slot.
* **Satisfiable:** obvious; the two termination witnesses.
* **Used in:** `eventually_committed_of_finalized`,
  `activeFrom_of_never_finalized`; timed, `exists_start`.
* **Paper:** Algorithm 1, line 17 (`line:participate`); Module 1
  (`mod:slotconsensus`)'s Termination.

### 6.2 `NoAbandonBeforeFinalizing`, C1

* **Role:** no correct validator invokes `abandon()` before it has
  finalized.
* **Plausible:** the glue abandons a slot only once it has finalized it.
  Without it the claim is false: finalizing is a gated rule.
* **Satisfiable:** obvious; all three Chorus witnesses.
* **Used in:** `activeFrom_of_never_finalized`,
  `eventually_committed_of_assignable`, totality's `within_assigned` and
  `within_finalized`, `activeUntil_of_not_finalized`, and
  `within_finalized_late`'s MVBA tail.
* **Paper:** Algorithm 1, line 23 (`line:abandon`); Module 1 does not
  state it, P13 ([PaperAlignment.md](PaperAlignment.md) §6).

### 6.3 `NoEarlyStart`, C2

* **Role:** no correct validator participates before `D − Δ`.
* **Plausible:** the Conductor opens a slot at its start time.
* **Satisfiable:** obvious; `Chorus.timedTermination_premises_satisfiable`.
* **Used in:** `deadline_le_of_start` (`D ≤ t + Δ`, in
  `within_finalized_late`).
* **Paper:** Lemma 12 (`lemma:conductor-integrity`); Module 1 does not
  state it, P13.

### 6.4 `SyncParticipationWithin d`

* **Role:** once one correct validator participates at `c`, all do by
  `max(c, GST) + d`; the contract's case is `d = Δ`.
* **Plausible:** the Conductor opens a slot at every correct validator
  within `Δ` of the first after GST.
* **Satisfiable:** obvious; `Chorus.totality_premises_satisfiable` and
  `Chorus.timedTermination_premises_satisfiable`.
* **Used in:** `Chorus.totality` (the finalizer's peers participate in
  time); the timed claims through totality, on the early-finalization
  branch.
* **Paper:** Definition 5 (`def:delta-synchronized-participation`),
  supplied by Lemma 15 (`lemma:conductor-totality`).

### 6.5 The MVBA's caller: `AllPropose`, `NoEarlyAbandon`, `FRelay` (F-relay)

Untimed: every correct validator invokes `propose`; none is abandoned
before deciding; a correct validator's decided certificate is handed on to
whoever can take it. Timed (the fields of `MVBATemporal.termination`):
every correct validator proposes by `t`, proposes a `Valid` value, and is
not abandoned before `max(t, GST) + ℓ_MVBA`.

* **Role:** the MVBA is started everywhere, left running until it
  decides, and its decisions are passed on.
* **Plausible:** Chorus proposes on its fallback trigger, abandons only
  after finalizing, and broadcasts the certificate a decision outputs.
* **Satisfiable:** obvious alone; with the scheduling premises,
  `Mvba.termination_premises_satisfiable` and
  `Mvba.timedTermination_premises_satisfiable` (the model halts a
  validator after it decides, [Bounds.md](Bounds.md) §6.3.2).
* **Used in:** `AllPropose` by `eventually_tc_below_good` and
  `eventually_entered_good` (timed: `exists_good_view`); `NoEarlyAbandon`
  by `settledIn_of_no_decision` and `eventually_decided_of_decision`;
  (F-relay) by `eventually_decided_of_decision`. The timed `Valid`
  antecedent is not used (§7).
* **Paper:** Supplement, Theorem 2 (`thm:termination`): "once every
  correct validator has invoked propose", "if no correct validator is
  externally abandoned before deciding"; Supplement, Lemma 13
  (`lem:decision-propagation`) for the handoff. Inside Cadence all of them
  are derived (§8).

## 7. Independence: every premise is used

Every premise in §2–§6 is consumed by a step of its claim's proof, with
the exceptions below. The check was a transitive analysis of the proof
terms, run over every claim of §1: a hypothesis counts as used when the
proof mentions it in a position that is not discarded, where passing it to
a lemma that does not use it is not a use, and an argument of a case split
is a use only if a branch uses it. Anything the analysis cannot see
through (the generated proof families, library lemmas) counts as a use, so
it can miss an unused premise but not invent one. It finds the one
antecedent a proof discards by name (the first exception below), and the
proof steps named in the "Used in" lines were read besides.

**Result (R21).** Every premise of every claim in §1 is used, with three
exceptions, none of them removed here (removing a premise changes a
claim's statement):

* **Unused: the timed MVBA claim's `Valid` antecedent.**
  `Mvba.timed_termination` (and so `Mvba.mvbaTemporal`'s `termination`)
  does not use "every correct validator proposes a `Valid` value": the
  model's `propose` checks validity itself. The antecedent is part of the
  contract field `MVBATemporal.termination`, Module 3 (`mod:mvba`)'s
  caller condition, which another implementation may need. *Proposal:*
  keep it in the contract; this page records that the instance does not
  use it.
* **Implied: `ByzNodeSetHonestQuorum` in the timed Chorus claims at the
  system's MVBA.** `Chorus.timed_termination_atMvba` and
  `Chorus.timed_termination_tight_atMvba` take it as a hypothesis (`hqe`)
  and use it, but at the family they are stated at it is a theorem
  (`Chorus.hqeFin`), which the contract instance already uses. *Proposal:*
  derive it inside the two theorems and drop the hypothesis (a plain-Lean
  statement change in
  [Chorus/TimedTermination.lean](../Cadence/Chorus/TimedTermination.lean)
  and its two callers).
* **Unused and implied: the model assumption `leader_honest_cofinal`**
  (§2.4). No proof of a claim in §1 reads it: its one reader,
  `Mvba.exists_honest_leader_above` in
  [Mvba/Rank.lean](../Cadence/Mvba/Rank.lean), is used nowhere, and the
  liveness claims take their correct-led view from (A-viewsync) or from
  `LeaderRotation`, which implies it. As a model `assumption` it is a
  conjunct of every reachable state's premises, so the MVBA's safety
  claims are stated for leader schedules with cofinally many correct
  leaders rather than for every schedule
  ([Architecture.md](Architecture.md) §4 item 2). *Proposal:* remove it
  from [Mvba.lean](../Cadence/Mvba.lean), with the unused lemma; that
  widens the MVBA's safety claims to every leader schedule. It is a model
  change: every Mvba VC statement changes and the family re-solves cold
  (the cell counts do not move).

Where a premise is a conjunction, the analysis sees the whole. The parts
are accounted for in the "Used in" lines; the one part no termination
proof uses is `TimedJustice`'s fast commit path rows (§4.1), kept because
the premise is the paper's "every step within its bound", and dropping a
row would admit runs the paper's network does not produce.

## 8. What is not a premise

Things an auditor might expect to be assumed, and which are proven
instead.

* **The MVBA's termination.** Chorus's claims apply `Mvba.termination`
  and `T.termination` to the run's MVBA steps; the former assumption
  (A-mvba) is retired.
* **The MVBA's caller conditions, inside Cadence.** Chorus is the MVBA's
  caller, so its proofs derive them: every correct validator proposes
  (`eventually_input`), none abandons before deciding
  (`abandoned_of_mvba_abandoned`), (F-relay) (`fRelay_of_fJustice`) and
  (Δ-relay) (`relayed_of_timedJustice`), (F-avail) (`fAvail_of_fJustice`)
  and (Δ-avail) (`availWithin_of_timedJustice`).
* **(A-viewsync) under the timed premises** (`Mvba.aViewSync_of_sync`).
* **A correct supermajority at the Chorus family** (`Chorus.hqeFin`), and
  the quorum counting facts (`Cadence.byzNodeSetFin_counting`).
* **(F-byz)** is the absence of a premise: no fairness is asked of
  Byzantine actions, so no progress relies on adversarial help.

The rest of what the machine does not establish (the monotone-network
contract, the primitive contracts, the trusted tooling, the scope) is
[Architecture.md](Architecture.md) §4. The detail behind the witnesses is
[Bounds.md](Bounds.md) §6.3.1–§6.3.2 (the MVBA's model) and §6.4.5 (the
Chorus model); the reasons for the fairness classes are
[Liveness.md](Liveness.md) §2.
