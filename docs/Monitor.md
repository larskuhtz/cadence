# The model-conformance monitor

The proofs in this repository establish Chorus's safety invariants over *all*
reachable states of the **model**. That leaves a complementary question, and
it is the one an auditor of a running system asks next:

> Does an execution of the real implementation refine the model?

The monitor answers it for a concrete recorded execution. It replays a
projected implementation trace against the model and reports whether the model
**accepts** (simulates) it.

It is **not** model checking — there is no state-space
exploration — and it is not a re-proof. It runs the model's *own* action
bodies, one trace label at a time, and a failed `require` (guard) means the
implementation diverged from the model at that step.

## 1. What it establishes, and what it does not

* **Establishes**: this recorded run is a behaviour of the model. Every safety
  property proven of the model therefore holds along this run.
* **Does not establish**: that *all* runs of the implementation are behaviours
  of the model (that would be a refinement proof, not a check), nor anything
  about liveness. The monitor is a refinement/**safety** check.

Its practical value is as a *test oracle*: because the acceptance criterion is
the model's own guards, it catches ordering and prerequisite bugs that
hand-written assertions in an implementation test suite would not, and it
reports them in the vocabulary of the proven properties.

It carries one further load since the 2026-08 external audit (its
Finding 4): the fixture run is the build's **non-vacuity witness for
Chorus**. `Cadence.lean` and `Conductor.lean` carry in-build `sat trace`
witnesses; Chorus cannot ([`TODO.md`](./TODO.md) § Soundness has the two
blockers), so `traces/fast_path_positive.jsonl` — which drives three honest
validators through the full fast path to `finalize_commit`, executed
against the model's extracted actions — is what shows the Chorus safety
properties are not vacuously true. CI runs the monitor suites on every
commit (`scripts/container.sh monitor`, in
[`.github/workflows/verify.yml`](../.github/workflows/verify.yml)); an edit
that made finalization unreachable turns that step red.

## 2. How the pieces fit together

```
   Rust sim run (n = 3f+1 = 4)                Veil Chorus model
   ────────────────────────────               ─────────────────
   the implementation's sim harness            veil.gen.executableActions
     feature `trace-emit`                        emits  Chorus.NextAct.extracted
        │  emits JSONL in the                          │  (per-label executor,
        │  model's Label alphabet                      │   no O(nᵏ) enumeration)
        ▼                                              ▼
   chorus_*.jsonl  ─────────────▶  step : Label → State → outcome
                                   (run the model's action body for the label)
                                         │
                                         ▼
                             ACCEPTED  /  NOT ACCEPTED (guard failed)
```

The model side needs no new trust: `veil.gen.executableActions` emits an
*executable* form of the same action bodies the verification conditions are
generated from (see [Dependencies.md](./Dependencies.md) §5).

## 3. Two stages: observable emission, then model-side bridging

To keep the emitter model-unaware — and to make acceptance *witnessed* rather
than *reconstructed* — emission and projection are split.

* **Stage A — observable emission** (implementation side). The emitter emits
  only the model actions it can *witness* in a run: `vote`,
  `aggregate_fastqc_*`, `cast_fast_commit`, `broadcast_commitqc_*`,
  `finalize_commit`, `advance_*`. It observes them at two composition
  surfaces — the **network** (each node's outbound votes and casts, via a
  generic egress observer) and the **`SlotConsensus` interface**
  (finalization). It does not emit, or need to know about, the model's
  internal steps.
* **Stage B — internal-step bridging** (monitor side). Some model actions are
  purely internal — `commit_sign_*` (implicit in casting a fast-commit vote)
  and `commit_assign_*` (implicit in finalizing) — and have no observable
  event. Before each observed label the monitor applies every *enabled*
  internal action to a fixpoint: the ε-closure of the model's silent
  transitions.

### 3.1 Why Stage B is sound

The saturation only ever applies actions the model itself **enables**, so it
cannot manufacture unjustified state. A `cast_fast_commit` with no preceding
FastQC still fails, because `commit_sign` is not enabled in that state — the
bridge cannot invent the missing prerequisite. Termination is likewise
structural: the internal actions are monotone and range over the small
node/root domains of the concrete instance.

This is exactly why the two-stage design catches bugs that an
emitter which *reconstructed* the schedule would have masked: see the
`drop-fastqc` row in §6.

## 4. The pieces, in this repository

| File | Role |
|---|---|
| [`Cadence/Monitor/ChorusMonitor.lean`](../Cadence/Monitor/ChorusMonitor.lean) | the hand-written monitor: instantiation, a JSONL→`Label` decoder with one arm per constructor, the trace fold, and a `main` reading JSONL from stdin. **The test oracle.** |
| [`Cadence/Monitor/MvbaStub.lean`](../Cadence/Monitor/MvbaStub.lean) | the stand-in for Chorus's MVBA class constraint (since 2026-09-10 Chorus `instantiate`s `MVBASafety` over three abstract sorts): state and message `Unit`, the value a finite entry-vector record with the two projections Chorus's `Theory` needs, and a *silent* instance of the class that never decides — a consistent model of `MVBASafety` under which every guard reading it is decidable. Shared by both monitors; its coverage consequence is §8. |
| [`Cadence/Monitor/ChorusMonitorGen.lean`](../Cadence/Monitor/ChorusMonitorGen.lean) | the same monitor with its instantiation produced by Veil's `#gen_monitor` instead of hand-written. Must agree with the oracle on every fixture. |
| [`Cadence/Monitor/Alphabet.lean`](../Cadence/Monitor/Alphabet.lean) | the published alphabet: the monitor's alphabet **is** the constructors of `Chorus.Label`, reflected mechanically so it cannot drift from the model. Each action is tagged **observable** (Stage A emits it) or **internal** (Stage B inserts it). |
| [`Cadence/Monitor/TraceMutate.lean`](../Cadence/Monitor/TraceMutate.lean) | the trace-mutation tool: corrupt a valid trace in a way that models a class of implementation bug. |

The monitor runs on the Lean **interpreter** (`lean --run`); it needs no
compiled binary.

## 5. Usage

```bash
# Check a JSONL trace (read from stdin) against the model:
scripts/run-chorus-monitor.sh < traces/fast_path_negative.jsonl
#   → ACCEPTED — 18 step(s) simulated by the model ✓        (exit 0)

# Run the #gen_monitor-generated variant instead of the hand-written oracle:
CHORUS_MONITOR=Cadence/Monitor/ChorusMonitorGen.lean \
  scripts/run-chorus-monitor.sh < traces/fast_path_negative.jsonl
```

The monitor binary also *serves the emitter contract*, so an emitter author
never has to read the Lean (flags are forwarded by the runner script):

```bash
scripts/run-chorus-monitor.sh --alphabet             # the action alphabet, as JSON
scripts/run-chorus-monitor.sh --rust-emitter-stub    # a Rust trait skeleton to implement
scripts/run-chorus-monitor.sh --check-trace-alphabet < trace.jsonl   # syntactic check only
scripts/run-chorus-monitor.sh --node 0 < trace.jsonl # single-node projection (§7)
scripts/run-chorus-monitor.sh --help
scripts/run-chorus-monitor.sh --version
```

Exit codes: `0` accepted / ok · `1` model rejection (semantic) · `2` usage or
I/O error · `3` alphabet mismatch (syntactic). Keeping `1` and `3` distinct is
deliberate: a trace the monitor cannot *decode* is an emitter/alphabet
problem, and reporting it as a model rejection would be misleading.

### Trace format

One JSON object per line, positional arguments:

```json
{"action": "vote", "args": [0]}
{"action": "aggregate_fastqc_pos", "args": [0, 0, 1, [0,1,2]]}
{"action": "advance_to_deadline"}
```

`args` may be omitted when empty. Node and merkle-root arguments are integers
(`Fin 4` / `Fin 2`); a node set is a JSON array of integers; an MVBA value
(the entry vector) is a JSON array of four entries, each a root index or
`null`; the MVBA's abstract state is not observable and is written `null`
(`mvba_step` takes exactly `[null]`). Blank lines and lines starting with
`//` or `#` are ignored. The alphabet the emitter must follow is served by
`--alphabet` and changed on 2026-09-10 with the MVBA's consumption as a
class constraint: the oracle actions `mvba_decide_pos`/`mvba_decide_neg`
and the nullary `mvba_terminate` are gone, replaced by `mvba_step`,
`mvba_propose`, `on_mvba_decide_pos`, `on_mvba_decide_neg` and a binary
`mvba_terminate`.

## 6. Validation: mutation testing

`scripts/test-monitor-divergence.sh` starts from a model-ACCEPTED trace (by
default the one emitted from a real run), applies each mutation in
`TraceMutate.lean`, and asserts the monitor **rejects** the result at the guard
that should fail:

```
shrink-quorum  → NOT ACCEPTED at aggregate_fastqc_neg  (undersized <2f+1 QC)
forge-quorum   → NOT ACCEPTED at aggregate_fastqc_neg  (non-voter in a QC)
drop-commitqc  → NOT ACCEPTED at finalize_commit       (no commit certificate)
drop-fastqc    → NOT ACCEPTED at cast_fast_commit      (cast with no FastQC — unbridgeable)
swap-verdict   → NOT ACCEPTED at aggregate_fastqc_pos  (wrong pos/neg verdict)
reorder-vote   → NOT ACCEPTED at aggregate_fastqc_neg  (QC before its evidence)
dup-finalize   → NOT ACCEPTED at finalize_commit       (double finalization)
```

Each mutation models a class of implementation divergence and names the guard
that rejects it, so a mutation that passed silently would itself be a failure
signal. Because
the mutations operate on the trace rather than on the model or the
implementation, this suite keeps working, and grows in coverage, as the
implementation lands more behaviour and the emitted traces get richer.

The two regression suites:

```bash
scripts/test-chorus-monitor.sh       # acceptance: both monitors on every fixture, must agree
scripts/test-monitor-divergence.sh   # negative: every mutated trace must be REJECTED
scripts/test-single-node-monitor.sh  # the single-node projection mode of §7
```

All three run on every commit via `scripts/container.sh monitor` (the
`verify` workflow's monitor step) — against the `verified` image, over
oleans the verification stage has just rebuilt from the same sources.

## 7. Single-node projection mode (`--node i`)

`--node i` monitors one selected node in isolation, given a whole-system
observable trace: node `i`'s own actions are **validated** under the
all-honest instance (so the `2f+1` thresholds are the real ones), while every
other node's message is **admitted** from the trace by writing its facts
through the model's own `byz_*` actions under that sender's own
single-Byzantine instance — each a valid `|byz| ≤ f` instance.

The per-instance cap does not bound the number of distinct senders admitted:
`State` is independent of the Byzantine instance, so admitted facts accumulate
in one threaded state while node `i`'s guards read them under the all-honest
instance. That makes `n = 3f+1` a pure quorum-threshold parameter, decoupled
from the number of monitored nodes.

Soundness rests on the same property as the network abstraction: the model
reads environment facts only in guards, in positive position — the monotone
contract of [ChorusDesign.md](./ChorusDesign.md) §3.1–§3.3. As everywhere in
this document, it is a refinement/safety check, not liveness.

Current coverage: the negative fast path with proposer = node 0, matching the
current emitter. The positive path and the fallback path are more admit rules
on the same mechanism.

## 8. Instance and scope of the current cut

`n = 3f+1 = 4`, `f = 1`, a single slot, **empty** Byzantine set (all four
nodes honest — the deployment the all-honest sim exercises), proposal index 0
mapped to model proposer node 0, and every root well-encoded
(`well_encoded := fun _ => true` in the `Theory` instantiation — the
fixtures' proposals are honestly encoded; an invalid-encoding trace would
instantiate it `false` at the offending root). The sim's data-availability layer is stubbed,
so every node votes negative and finalization runs the **negative fast path**;
the emitter emits the observable actions of that path.
`traces/fast_path_positive.jsonl` additionally exercises the positive guards
by hand.

Why a concrete instance is not a soundness compromise: the model's safety
theorems are proven **universally** (every `n = 3f+1`, every Byzantine set of
size ≤ f), so no instantiation is required for the properties to transfer —
the instance only fixes which run is being checked. The trace additionally
pins the nondeterminism at the monitored components' boundary. See
[ChorusDesign.md](./ChorusDesign.md) §3 and
[Architecture.md](./Architecture.md) §4.

**The MVBA leg is a coverage gap.** Since 2026-09-10 Chorus consumes the
MVBA as the class constraint `MVBASafety` over three abstract sorts
(`docs/MvbaPlan.md` §6), and no implementation event corresponds to them:
the MVBA's internal state and messages are not observable at the Chorus
trace boundary, and the emitter does not emit decisions. The monitor
therefore instantiates the constraint with the **silent stub** of
[`Cadence/Monitor/MvbaStub.lean`](../Cadence/Monitor/MvbaStub.lean) —
state and message `Unit`, a `decided` relation that never holds — under
which the oracle step `mvba_step` is a silent no-op (tagged *internal*, so
Stage B absorbs it) and the decision handlers `on_mvba_decide_*` and
`mvba_terminate` can **never be enabled**: a trace carrying a fallback-path
decision is rejected at the first handler. That is a limit of the monitor,
not of the model — the model's MVBA is the verified `Mvba` instance
(`Cadence/System.lean`) — and closing it means giving the monitor a real
MVBA leg: either a concrete executable `MVBASafety` instance driven by
MVBA-level trace events (the `Mvba` model's own extracted actions would
do), or an emitter that observes decisions at the `MVBA.decide` interface
so that a decision event can seed a `decided`-true stub state. The fixtures
under `traces/` are fast-path only and never reach the MVBA, so they are
unaffected.

Future scope, in rough order: positive-path emission; finer per-message
emission (individual votes and casts observed at the network boundary rather
than derived from the certificates); the MVBA leg above; multi-slot
(Conductor) traces; and Byzantine validate-vs-admit tagging.

## 9. Where the emitter lives

The Rust emitter is part of the implementation repository, not this one: a
`trace-emit` feature on the Chorus sim crate that observes each node's actual
network egress (which nodes broadcast votes and fast-commit votes) plus the
finalization interface, and emits the **observable** actions in the model's
`Label` alphabet. Quorum arguments come from the certificates' verified signer
sets, so a node that broadcast a vote but never made it into a QC is still
recorded as a voter — the trace reflects what happened on the wire, not just
what the certificates imply.

Everything the emitter needs from this repository is served by the monitor
binary itself (`--alphabet`, `--rust-emitter-stub`, `--check-trace-alphabet`),
which is what keeps the two sides from drifting.
