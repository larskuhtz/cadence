# Spikes — the evidence behind the contract redesign

Runnable experiments, kept because they are the evidence for
[`../docs/CompositionContracts.md`](../docs/CompositionContracts.md) and
because re-deriving them costs an afternoon. **Not part of the build**: the
library's globs cover `Cadence` and its submodules only, so nothing here is
compiled by `lake build`.

Run one with:

```bash
scripts/scratch.sh spikes/01_state_explicit_contract_ok.lean
```

That script (not bare `lake env lean`) is required — the solver bindings load
as native plugins. It needs at least one real module built first, so run
`lake build Cadence.Interfaces` once in a fresh checkout.

**Read the exit code from `scratch.sh` itself.** Three of these are *supposed*
to fail; a wrapper like `cmd > log; echo $?` reports the wrapper, not the
tool.

| File | Expected | What it establishes |
|---|---|---|
| `01_state_explicit_contract_ok.lean` | `exit 0`, all `✅` | A contract stated over an **explicit state type** is consumable by a Veil module as an ordinary `instantiate` constraint, and Veil hands the instantiated class's axioms to the solver — so the consumer *discharges* the contract property instead of restating it. Also: the consumer's `appended_opened` holds only because `opened_monotone` is a formal field, so formalising Monotonicity is load-bearing. |
| `02_negative_control_axiom_removed.lean` | `exit 1`, `prefix_agreement_usable ... ❌` | The same module with `open_prefix_agreement` deleted from the class and nothing else changed. The invariant fails with a counterexample while every other one still passes, so 01's discharge is not vacuous. |
| `03_nonfirstorder_field_breaks_smt.lean` | `exit 1`, one error naming `MiniOrchLive.totality` | Adding a `totality` field quantifying over a run (`run : Nat → state`) to the *instantiated* class is fatal: Veil emits all class axioms verbatim and cvc5 has no function sorts. This is why the contract must be split. Originally every VC came back `💥` with `cvc5.Error.error "Symbol '->' not declared as a type"`, naming neither class nor field; since the 2026-09 Veil bump the check command reports it once, before any solver starts, and names `attribute [veil_smt_ignore] MiniOrchLive.totality` as the escape hatch. The spike is kept as the reproduction of that check. |
| `04_two_level_split_ok.lean` | `exit 0`, all `✅` | The split works: `OrchSafety` (first-order, `instantiate`d by the module) plus `Orch extends OrchSafety` carrying Totality over an explicit `OrchRun` and `B`-boundedness with the bound as data. Ends with an `example` showing `F.toOrchSafety` hands the composition exactly what it assumes, so nothing is dropped from the interface. |
| `05_shared_fault_model_and_family_ok.lean` | `exit 0`, all `✅` | The remaining mechanics of the implemented design: a later `instantiate` can take an *earlier* instantiated parameter's projection as a class argument (one `FaultModel` shared by every contract a module consumes) and resolve an inst-implicit `TotalOrder`; a per-slot abstract state `function sc_state (s : slot) : scstate` with class-field applications translates; and the consumer's agreement and prefix invariants are discharged from the class axioms at the reachable abstract state. |
| `06_dependent_temporal_parent.lean` | `exit 0`, no errors | The temporal level of a contract can be a class **over the safety instance** (`XTemporal … [S : XSafety …]`, every field stated over `S.init`/`S.trans`), and `class X extends XSafety, XTemporal` takes the dependent parent: `#check` shows `X.toXTemporal`'s instance argument printing as `X.toXSafety self`, so the two levels cannot be about different transition systems. Ends by joining a proven fragment with an assumed temporal instance — the shape that replaces the residual structures, with the fragment recoverable by `rfl`. The plain-field fallback (`toTemporal : XTemporal … (S := toXSafety)`) is kept alongside and also works. Pure Lean; nothing here reaches SMT. |
| `07_sc_state_tag_ok.lean` | `exit 0`, all `✅` | `SlotConsensusSafety` can drop its **slot index** and carry the instance's slot as a state observable (`tag : state → slot` with `tag_frame`), so all four contracts extend one *unindexed* skeleton. The consumer keeps one abstract state per slot, and `[sc_tagged]` (slot `s`'s state is tagged `s`) is inductive from one added assumption `[sc_tag_init]` plus `tag_frame`; `[appended_slot]` then recovers what the indexed `slot_safety` gave directly. The measured cost of the encoding is that one assumption line. |
| `08_sc_tag_frame_removed.lean` | `exit 1`, exactly one `❌`: `sc_tagged` under `sc_step` | The negative control for 07: the same module with `tag_frame` deleted and nothing else. `sc_tagged` stops being inductive at exactly the action that moves a slot-consensus state, so 07's encoding is not proving itself for some other reason. Every other cell still passes — each assumes the clump at the pre-state — which is what an inductive counterexample looks like. |

**A note on 07's skeleton.** Spikes 07 and 08 give their contracts a shared
`TSS` transition-system skeleton, which is the shape `Interfaces.lean` now
has. When they were written it was not: a Veil module that `instantiate`s a
class with an `extends` parent verified (the sweeps here were the evidence)
but its `sat trace` failed — fork bug L17, found by exactly this work and
fixed in the fork on 2026-09-10. The spikes passed even then, because they
run no trace; they now match the shipped shape as well.

These use throwaway names (`MiniOrch`, `OrchSafety`, `Orch`, `OrchS`,
`ScS`) and a toy consumer. They are shape experiments, not drafts of the real
contracts — the real contracts are [`../Cadence/Interfaces.lean`](../Cadence/Interfaces.lean).

**Two further experiments graduated into the code base rather than staying
here.** Proving the *step-level* contract fields (monotonicity of the
observables, the frames, the paper's Monotonicity) for an implementation
means reasoning about two consecutive states of a Veil-generated transition
system, which no `#check_invariants` cell can do. The technique — expose the
action's pre-computed body `<action>.ext.tr` through its
`<action>.ext.derived_eq` bridge (Veil's `trSimp` simp set is exactly those
two per action), destructure, substitute the post-state, evaluate the
field-representation `get`/`set` pair at the canonical representation — is
the `StepFacts` section of
[`../Cadence/Composition.lean`](../Cadence/Composition.lean) (7 Conductor
actions) and of [`../Cadence/Chorus/Compose.lean`](../Cadence/Chorus/Compose.lean)
(all 38 Chorus actions, one uniform tactic, seconds). That those files build
is the evidence.
