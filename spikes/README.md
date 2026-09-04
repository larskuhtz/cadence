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

**Read the exit code from `scratch.sh` itself.** Two of these are *supposed*
to fail; a wrapper like `cmd > log; echo $?` reports the wrapper, not the
tool.

| File | Expected | What it establishes |
|---|---|---|
| `01_state_explicit_contract_ok.lean` | `exit 0`, all `✅` | A contract stated over an **explicit state type** is consumable by a Veil module as an ordinary `instantiate` constraint, and Veil hands the instantiated class's axioms to the solver — so the consumer *discharges* the contract property instead of restating it. Also: the consumer's `appended_opened` holds only because `opened_monotone` is a formal field, so formalising Monotonicity is load-bearing. |
| `02_negative_control_axiom_removed.lean` | `exit 1`, `prefix_agreement_usable ... ❌` | The same module with `open_prefix_agreement` deleted from the class and nothing else changed. The invariant fails with a counterexample while every other one still passes, so 01's discharge is not vacuous. |
| `03_nonfirstorder_field_breaks_smt.lean` | `exit 1`, **all** VCs `💥` | Adding a `totality` field quantifying over a run (`run : Nat → state`) to the *instantiated* class crashes every VC with `cvc5.Error.error "Symbol '->' not declared as a type"`. Veil emits all class axioms verbatim and cvc5 has no function sorts. This is why the contract must be split. |
| `04_two_level_split_ok.lean` | `exit 0`, all `✅` | The split works: `OrchSafety` (first-order, `instantiate`d by the module) plus `Orch extends OrchSafety` carrying Totality over an explicit `OrchRun` and `B`-boundedness with the bound as data. Ends with an `example` showing `F.toOrchSafety` hands the composition exactly what it assumes, so nothing is dropped from the interface. |

These use throwaway names (`MiniOrch`, `OrchSafety`, `Orch`) and a toy
consumer. They are shape experiments, not drafts of the real contracts — the
target shape is `docs/CompositionContracts.md` §6 "The uniform target".
