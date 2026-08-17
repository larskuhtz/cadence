/-
Chorus model-conformance monitor (hand-written cut).

Reads a JSONL trace from stdin (one label per line) and checks whether the
model ACCEPTS it: each label is run through the Veil Chorus model's own
extracted action body at a concrete instance (n = 3f+1 = 4, f = 1, node 0 the
sole proposer, empty Byzantine set).  A failed `require` (assertionFailure) or a
disabled action means the trace is NOT accepted — i.e. the implementation run
diverges from the model.

This is a trace-directed acceptance/simulation check, NOT model checking.

JSONL line format (positional args):
  {"action": "vote", "args": [0]}
  {"action": "aggregate_fastqc_pos", "args": [0, 0, 1, [0,1,2]]}
  {"action": "advance_to_deadline"}                 -- args optional when empty
Args: node/merkle_root are ints (Fin 4 / Fin 2); a nodeset is a JSON array of
ints (subset of {0,1,2,3}).  Blank lines and lines beginning with `//` or `#`
are ignored.
-/
import Cadence.Chorus
import Cadence.Monitor.Alphabet
import Cadence.ByzQuorum
open Veil Veil.Extract
open scoped Chorus
open Lean (Json fromJson? ToJson FromJson)

-- Modest budgets suffice once the state is seeded via the explicit instance.
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
-- `String.trim` is deprecated but still returns `String`; silence the linter so
-- `lean --run` output stays clean (the replacement returns `String.Slice`).
set_option linter.deprecated false

namespace ChorusMonitor

/-! ## Concrete instance -/

abbrev SL := Fin 1
abbrev ND := Fin (3 * 1 + 1)
abbrev NS := ByzNSet (3 * 1 + 1)
abbrev MR := Fin 2
abbrev PH := Chorus.Phase_IndT
abbrev PC := Chorus.PathChoice_IndT

abbrev Th  := Chorus.Theory SL ND NS MR PH PC
abbrev St  := Chorus.State (Chorus.FieldConcreteType SL ND NS MR PH PC)
abbrev Lbl := Chorus.Label SL ND NS MR PH PC

/-- Empty Byzantine set at n = 3f+1 = 4, f = 1: all four nodes honest.  A valid
    ≤f instantiation (the model's safety theorem is universal over ≤f Byzantine,
    including none), and the one that matches the all-honest Rust sim run — so
    the monitor validates every node's action.  Overrides the default
    `insByzNodeSetFinSimple` (which would make node 0 Byzantine). -/
def emptyByz4 : ByzNodeSet ND NS :=
  Cadence.byzNodeSetFinGen (3 * 1 + 1) 1 (by decide) (fun _ => False) (by decide)

/-- Node 0 is the sole proposer.  Proposal index 0 in the implementation maps to
    model proposer node 0 (the impl indexes proposals `0..num_proposals`,
    decoupled from node identity; here `num_proposals = 1`). -/
def chThy : Th := Chorus.Theory.mk (fun j => j == 0)

/-- Explicit specialized Inhabited seed — avoids the pathological `Inhabited St`
    search (this is what `#model_check` does via `inhabσ`). -/
def stInhab : Inhabited St := Chorus.instInhabitedStateFieldConcreteType

/-- The extracted per-label executable step at this concrete instance. -/
def cnext (lbl : Lbl) : VeilMultiExecM Std.Format ℤ Th St Unit :=
  Chorus.NextAct.extracted (ρ := Th) (σ := St) (nset := emptyByz4)
    (slot := SL) (node := ND) (nodeset := NS) (merkle_root := MR) (Phase := PH) (PathChoice := PC) lbl

/-- The extracted initializer at this instance. -/
def cinit : VeilMultiExecM Std.Format ℤ Th St Unit :=
  Chorus.initializer.ext.extracted (ρ := Th) (σ := St) (nset := emptyByz4)
    (slot := SL) (node := ND) (nodeset := NS) (merkle_root := MR) (Phase := PH) (PathChoice := PC)

def initState : Option St :=
  (extractValidStates cinit chThy stInhab.default).filterMap id |>.head?

/-! ## Monitor step -/

inductive StepResult where
  | ok (st : St)
  | notAccepted (why : String)
  | ambiguous (n : Nat)

/-- Run the model action named by the label on the current state.  A failed
    `require` (assertionFailure) or no outcome means NOT accepted. -/
def step (st : St) (lbl : Lbl) : StepResult :=
  match extractAllOutcomes (cnext lbl) chThy st with
  | []                      => .notAccepted "action not enabled (no outcome)"
  | [.success st']          => .ok st'
  | [.assertionFailure _ _] => .notAccepted "require failed (label not enabled in model)"
  | [.divergence]           => .notAccepted "divergence"
  | outs                    => .ambiguous outs.length

/-! ## Internal-action saturation (Stage B)

The emitter (Stage A) emits only the model actions it can *witness* in the
implementation. The model's purely-internal steps — `commit_sign_*` (implicit in
casting a fast-commit vote) and `commit_assign_*` (implicit in finalizing) — have
no observable event, so the monitor inserts them: before each observed label it
applies every *enabled* internal action to a fixpoint (the ε-closure of the
model's silent transitions). This is bounded — internal actions are monotone and
range over the small node/root domains — and sound: it only ever applies actions
the model *enables*, so it cannot manufacture unjustified state (a cast with no
prior FastQC still fails, because `commit_sign` is not enabled). See
`docs/Monitor.md` §3–§3.1. -/

/-- Internal actions the emitter does not emit; the monitor bridges them. -/
def internalCandidates : List Lbl :=
  (List.finRange (3 * 1 + 1)).flatMap fun i =>
  (List.finRange (3 * 1 + 1)).flatMap fun j =>
    [Chorus.Label.commit_sign_neg i j, Chorus.Label.commit_assign_neg i j]
    ++ (List.finRange 2).flatMap fun m =>
       [Chorus.Label.commit_sign_pos i j m, Chorus.Label.commit_assign_pos i j m]

/-- Apply the first enabled internal action that changes the state (`none` when
    no internal action is enabled or all are idempotent). -/
def applyEnabledInternal (st : St) : Option St :=
  internalCandidates.findSome? fun lbl =>
    match extractAllOutcomes (cnext lbl) chThy st with
    | [.success st'] => if st' == st then none else some st'
    | _              => none

/-- Saturate internal actions to a fixpoint. Terminates: each application
    strictly grows the (monotone) state relations. -/
partial def saturate (st : St) : St :=
  match applyEnabledInternal st with
  | some st' => saturate st'
  | none     => st

/-! ## Label decoding (JSON → Lbl) -/

/-- Decode a `Nat` into `Fin bound`.  Term-level `if` (not inside a Veil `do`). -/
private def toFin (bound : Nat) (k : Nat) : Except String (Fin bound) :=
  if h : k < bound then .ok ⟨k, h⟩ else .error s!"index {k} out of range (≥ {bound})"

/-- Build a `ByzNSet` from a strictly-sorted, deduplicated node list. -/
private def mkNSet (sorted : List ND) : Except String NS :=
  if h : sorted.Pairwise (· < ·) then .ok ⟨sorted, h⟩
  else .error s!"nodeset {sorted.map (·.val)} not strictly sortable"

private def dNode (j : Json) : Except String ND := j.getNat? >>= toFin (3 * 1 + 1)
private def dRoot (j : Json) : Except String MR := j.getNat? >>= toFin 2

private def dNSet (j : Json) : Except String NS := do
  let arr ← j.getArr?
  let fins ← arr.toList.mapM fun e => e.getNat? >>= toFin (3 * 1 + 1)
  mkNSet ((fins.dedup).mergeSort (fun a b => decide (a ≤ b)))

/-- Decode one `(act, args)` pair into a concrete `Lbl`. -/
def decodeLabel (act : String) (args : List Json) : Except String Lbl :=
  match act, args with
  -- phase advance (nullary)
  | "advance_to_deadline", []        => pure .advance_to_deadline
  | "advance_to_fb_arm", []          => pure .advance_to_fb_arm
  | "advance_to_mvba_arm", []        => pure .advance_to_mvba_arm
  | "mvba_terminate", []             => pure .mvba_terminate
  -- honest fast / propose path
  | "propose", [a, b]                => do pure (.propose (← dNode a) (← dRoot b))
  | "deliver_chunk_assigned", [a,b,c]=> do pure (.deliver_chunk_assigned (← dNode a) (← dNode b) (← dRoot c))
  | "record_chunk", [a,b,c]          => do pure (.record_chunk (← dNode a) (← dNode b) (← dRoot c))
  | "vote", [a]                      => do pure (.vote (← dNode a))
  | "aggregate_fastqc_pos", [a,b,c,d]=> do pure (.aggregate_fastqc_pos (← dNode a) (← dNode b) (← dRoot c) (← dNSet d))
  | "aggregate_fastqc_neg", [a,b,c]  => do pure (.aggregate_fastqc_neg (← dNode a) (← dNode b) (← dNSet c))
  | "commit_sign_pos", [a,b,c]       => do pure (.commit_sign_pos (← dNode a) (← dNode b) (← dRoot c))
  | "commit_sign_neg", [a,b]         => do pure (.commit_sign_neg (← dNode a) (← dNode b))
  | "cast_fast_commit", [a]          => do pure (.cast_fast_commit (← dNode a))
  | "broadcast_commitqc_pos", [a,b,c]=> do pure (.broadcast_commitqc_pos (← dNode a) (← dRoot b) (← dNSet c))
  | "broadcast_commitqc_neg", [a,b]  => do pure (.broadcast_commitqc_neg (← dNode a) (← dNSet b))
  -- fallback path
  | "fb_sign_pos", [a,b,c,d,e]       => do pure (.fb_sign_pos (← dNode a) (← dNode b) (← dRoot c) (← dNSet d) (← dNSet e))
  | "fb_sign_neg", [a,b,c]           => do pure (.fb_sign_neg (← dNode a) (← dNode b) (← dNSet c))
  | "cast_fallback_vote", [a]        => do pure (.cast_fallback_vote (← dNode a))
  | "mvba_decide_pos", [a,b]         => do pure (.mvba_decide_pos (← dNode a) (← dRoot b))
  | "mvba_decide_neg", [a]           => do pure (.mvba_decide_neg (← dNode a))
  | "redisseminate_chunk", [a,b,c]   => do pure (.redisseminate_chunk (← dNode a) (← dNode b) (← dRoot c))
  | "cast_fb_commit", [a]            => do pure (.cast_fb_commit (← dNode a))
  | "commit_assign_pos", [a,b,c]     => do pure (.commit_assign_pos (← dNode a) (← dNode b) (← dRoot c))
  | "commit_assign_neg", [a,b]       => do pure (.commit_assign_neg (← dNode a) (← dNode b))
  | "finalize_commit", [a]           => do pure (.finalize_commit (← dNode a))
  -- byzantine capability actions
  | "byz_sign_proposer", [a,b]       => do pure (.byz_sign_proposer (← dNode a) (← dRoot b))
  | "byz_deliver_chunk", [a,b,c]     => do pure (.byz_deliver_chunk (← dNode a) (← dNode b) (← dRoot c))
  | "byz_sign_vote_pos", [a,b,c]     => do pure (.byz_sign_vote_pos (← dNode a) (← dNode b) (← dRoot c))
  | "byz_sign_vote_neg", [a,b]       => do pure (.byz_sign_vote_neg (← dNode a) (← dNode b))
  | "byz_cast_vote", [a]             => do pure (.byz_cast_vote (← dNode a))
  | "byz_sign_fb_pos", [a,b,c]       => do pure (.byz_sign_fb_pos (← dNode a) (← dNode b) (← dRoot c))
  | "byz_sign_fb_neg", [a,b]         => do pure (.byz_sign_fb_neg (← dNode a) (← dNode b))
  | "byz_sign_fallback", [a]         => do pure (.byz_sign_fallback (← dNode a))
  | "byz_sign_commit_pos", [a,b,c]   => do pure (.byz_sign_commit_pos (← dNode a) (← dNode b) (← dRoot c))
  | "byz_sign_commit_neg", [a,b]     => do pure (.byz_sign_commit_neg (← dNode a) (← dNode b))
  | "byz_cast_commit", [a]           => do pure (.byz_cast_commit (← dNode a))
  | "byz_sign_fbcommit", [a]         => do pure (.byz_sign_fbcommit (← dNode a))
  | "byz_release_msg_decrypt_share", [a] => do pure (.byz_release_msg_decrypt_share (← dNode a))
  | _, _ => throw s!"unknown action or wrong arity: '{act}' with {args.length} arg(s)"

/-- Best-effort action-name extraction, for diagnostics. -/
def actionOf (j : Json) : String :=
  (j.getObjVal? "action" |>.bind (·.getStr?)).toOption.getD "?"

/-- Parse one JSON object into a concrete `Lbl`. -/
def parseLine (j : Json) : Except String Lbl := do
  let act ← (← j.getObjVal? "action").getStr?
  let argsJson := (j.getObjVal? "args").toOption.getD (Json.arr #[])
  let args ← argsJson.getArr?
  decodeLabel act args.toList

/-! ## Trace folding -/

inductive Verdict where
  | accepted (nSteps : Nat)
  | rejected (atStep : Nat) (act : String) (why : String)
  | decodeError (atStep : Nat) (line : String) (msg : String)
  | noInitState

def Verdict.render : Verdict → String
  | .accepted n            => s!"ACCEPTED — {n} step(s) simulated by the model ✓"
  | .rejected i act why    => s!"NOT ACCEPTED — step {i} ({act}): {why}"
  | .decodeError i ln msg  => s!"DECODE ERROR — step {i}: {msg}\n  line: {ln}"
  | .noInitState           => "MONITOR ERROR — model produced no initial state"

/-- Fold the monitor `step` over a decoded trace, short-circuiting on the first
    non-acceptance.  `lines` pairs each raw line with its parsed JSON. -/
def runTrace (lines : List (String × Json)) : Verdict :=
  match initState with
  | none => .noInitState
  | some s0 => go lines s0 1
where
  go : List (String × Json) → St → Nat → Verdict
  | [], _, i => .accepted (i - 1)
  | (raw, j) :: rest, st, i =>
    match parseLine j with
    | .error msg => .decodeError i raw msg
    | .ok lbl =>
      -- Stage B: bridge the model's internal steps before the observed label.
      match step (saturate st) lbl with
      | .ok st'          => go rest st' (i + 1)
      | .notAccepted why => .rejected i (actionOf j) why
      | .ambiguous n     => .rejected i (actionOf j)
                              s!"ambiguous: {n} distinct model outcomes (trace under-determines args)"

/-! ## Entry point -/

/-- Split stdin into (rawLine, parsedJson) pairs, skipping blanks and comments. -/
def parseInput (input : String) : Except String (List (String × Json)) := do
  let mut acc := #[]
  for ln in input.splitOn "\n" do
    let t := ln.trim
    if t.isEmpty || "//".isPrefixOf t || "#".isPrefixOf t then continue
    match Json.parse ln with
    | .ok j => acc := acc.push (t, j)
    | .error e => throw s!"JSON parse error on line: {t}\n  {e}"
  pure acc.toList

/-! ## Single-node mode (consumer-side projection)

Monitor one selected node `i` in isolation. Node `i`'s own actions are VALIDATED
under the all-honest instance (so the `2f+1` thresholds are the real ones); every
other node's message is ADMITTED by writing its facts via the model's own `byz_*`
actions under that sender's OWN single-Byzantine instance — each a valid
`|byz| ≤ f = 1` instance. The per-instance cap does not bound the number of
distinct senders admitted: `State` is independent of the Byzantine instance, so
the facts accumulate in one threaded state while node `i`'s guards read them under
the all-honest instance. This makes `n = 3f+1` a pure quorum-threshold parameter,
decoupled from the number of monitored nodes. Sound because the model reads
environment facts only in guards (monotone / positive-use — see
`docs/Monitor.md` §7 and `docs/ChorusDesign.md` §3.1); it is a refinement/safety check, not liveness.

v1 coverage: the negative fast path with proposer = node 0 (matching the current
emitter). Positive path / fallback are more admit rules on the same mechanism. -/

def byz0 : ByzNodeSet ND NS := Cadence.byzNodeSetFinGen (3 * 1 + 1) 1 (by decide) (fun x => x = 0) (by decide)
def byz1 : ByzNodeSet ND NS := Cadence.byzNodeSetFinGen (3 * 1 + 1) 1 (by decide) (fun x => x = 1) (by decide)
def byz2 : ByzNodeSet ND NS := Cadence.byzNodeSetFinGen (3 * 1 + 1) 1 (by decide) (fun x => x = 2) (by decide)
def byz3 : ByzNodeSet ND NS := Cadence.byzNodeSetFinGen (3 * 1 + 1) 1 (by decide) (fun x => x = 3) (by decide)

-- Per-instance executors: the guard `Decidable`s need the instance fixed, so
-- these cannot be one function polymorphic over the instance.
def cnextB0 (lbl : Lbl) : VeilMultiExecM Std.Format ℤ Th St Unit :=
  Chorus.NextAct.extracted (ρ := Th) (σ := St) (nset := byz0)
    (slot := SL) (node := ND) (nodeset := NS) (merkle_root := MR) (Phase := PH) (PathChoice := PC) lbl
def cnextB1 (lbl : Lbl) : VeilMultiExecM Std.Format ℤ Th St Unit :=
  Chorus.NextAct.extracted (ρ := Th) (σ := St) (nset := byz1)
    (slot := SL) (node := ND) (nodeset := NS) (merkle_root := MR) (Phase := PH) (PathChoice := PC) lbl
def cnextB2 (lbl : Lbl) : VeilMultiExecM Std.Format ℤ Th St Unit :=
  Chorus.NextAct.extracted (ρ := Th) (σ := St) (nset := byz2)
    (slot := SL) (node := ND) (nodeset := NS) (merkle_root := MR) (Phase := PH) (PathChoice := PC) lbl
def cnextB3 (lbl : Lbl) : VeilMultiExecM Std.Format ℤ Th St Unit :=
  Chorus.NextAct.extracted (ρ := Th) (σ := St) (nset := byz3)
    (slot := SL) (node := ND) (nodeset := NS) (merkle_root := MR) (Phase := PH) (PathChoice := PC) lbl

def runExec (prog : VeilMultiExecM Std.Format ℤ Th St Unit) (st : St) : StepResult :=
  match extractAllOutcomes prog chThy st with
  | []                      => .notAccepted "action not enabled (no outcome)"
  | [.success st']          => .ok st'
  | [.assertionFailure _ _] => .notAccepted "require failed (label not enabled in model)"
  | [.divergence]           => .notAccepted "divergence"
  | outs                    => .ambiguous outs.length

/-- A projected micro-step: validate/assemble run under all-honest; admit runs
    under sender `r`'s single-Byzantine instance. -/
inductive NodeStep where
  | validate (lbl : Lbl)
  | assemble (lbl : Lbl)
  | admit (r : ND) (lbl : Lbl)

def execNodeStep : NodeStep → St → StepResult
  | .validate lbl, st => runExec (cnext lbl) st
  | .assemble lbl, st => runExec (cnext lbl) st
  | .admit r lbl, st =>
    match r.val with
    | 0 => runExec (cnextB0 lbl) st
    | 1 => runExec (cnextB1 lbl) st
    | 2 => runExec (cnextB2 lbl) st
    | 3 => runExec (cnextB3 lbl) st
    | _ => .notAccepted s!"no admit instance for sender {r.val}"

-- Saturate only node `i`'s internal steps (proposer 0, negative path).
def internalCandidatesNode (i : ND) : List Lbl :=
  [Chorus.Label.commit_sign_neg i 0, Chorus.Label.commit_assign_neg i 0]

def applyEnabledInternalNode (i : ND) (st : St) : Option St :=
  (internalCandidatesNode i).findSome? fun lbl =>
    match extractAllOutcomes (cnext lbl) chThy st with
    | [.success st'] => if st' == st then none else some st'
    | _              => none

partial def saturateNode (i : ND) (st : St) : St :=
  match applyEnabledInternalNode i st with
  | some st' => saturateNode i st'
  | none     => st

/-- Project one whole-system label onto monitored node `i`. `.ok []` = drop;
    `.error` = a label outside v1's single-node coverage (reported as exit 3). -/
def projectLbl (i : ND) : Lbl → Except String (List NodeStep)
  | .advance_to_deadline           => .ok [.validate .advance_to_deadline]
  | .vote r                        => .ok (if r = i then [.validate (.vote r)]
                                           else [.admit r (.byz_sign_vote_neg r 0)])
  | .aggregate_fastqc_neg r j q     => .ok (if r = i then [.validate (.aggregate_fastqc_neg r j q)] else [])
  | .cast_fast_commit r            => .ok (if r = i then [.validate (.cast_fast_commit r)]
                                           else [.admit r (.byz_sign_commit_neg r 0),
                                                 .admit r (.byz_cast_commit r)])
  | .broadcast_commitqc_neg j q     => .ok [.assemble (.broadcast_commitqc_neg j q)]
  | .finalize_commit r             => .ok (if r = i then [.validate (.finalize_commit r)] else [])
  | _ => .error "label outside single-node v1 coverage (negative fast path, proposer 0)"

/-- Fold the projected micro-steps, saturating node `i`'s internal steps before
    each. Returns the same `Verdict` type as the whole-system fold. -/
def runProjectedNode (i : ND) (lines : List (String × Json)) : Verdict := Id.run do
  match initState with
  | none => return .noInitState
  | some s0 => do
    let mut st := s0
    let mut nVal := 0
    let mut idx := 1
    for (raw, j) in lines do
      match parseLine j with
      | .error msg => return .decodeError idx raw msg
      | .ok lbl =>
        match projectLbl i lbl with
        | .error e => return .decodeError idx raw e
        | .ok steps =>
          for stp in steps do
            match execNodeStep stp (saturateNode i st) with
            | .ok st' =>
                st := st'
                if (match stp with | .validate _ => true | _ => false) then nVal := nVal + 1
            | .notAccepted why => return .rejected idx (actionOf j) why
            | .ambiguous n     => return .rejected idx (actionOf j) s!"ambiguous: {n} outcomes"
      idx := idx + 1
    return .accepted nVal

/-- CLI: `--node i` — monitor node `i` against a whole-system trace on stdin. -/
-- Term-level dependent `if` (not a `do`-element — avoids Veil's `ifSomeDo`).
private def nodeOfNat (k : Nat) : Option ND := if h : k < 3 * 1 + 1 then some ⟨k, h⟩ else none

def runNodeMonitor (nStr : String) : IO UInt8 := do
  match nStr.toNat? >>= nodeOfNat with
  | none =>
    IO.eprintln s!"--node expects a node index 0..3, got '{nStr}'"; return 2
  | some i =>
    let input ← (← IO.getStdin).readToEnd
    match parseInput input with
    | .error e => IO.eprintln s!"input error: {e}"; return 2
    | .ok lines =>
      let v := runProjectedNode i lines
      IO.println s!"[node {i.val}] {v.render}"
      return (match v with
        | .accepted _     => 0
        | .rejected ..    => 1
        | .decodeError .. => 3
        | .noInitState    => 2)

/-! ## CLI

Exit codes: `0` accepted / OK; `1` model rejection (semantic — the trace is a
real divergence); `2` usage / I/O error; `3` alphabet mismatch (syntactic — the
trace does not decode against the model alphabet). The 1-vs-3 split keeps "the
implementation diverged from the model" distinct from "the emitter and the model
disagree on the alphabet". -/

def versionText : String :=
  "chorus-monitor 0.1 — Chorus model-conformance monitor (instance n = 3f+1 = 4, f = 1)"

def usageText : String :=
  "chorus-monitor — check whether the Veil Chorus model accepts a trace.\n\n" ++
  "USAGE:\n" ++
  "  chorus-monitor [FLAG] < trace.jsonl\n\n" ++
  "With no flag, reads a JSONL trace from stdin and prints ACCEPTED / NOT ACCEPTED.\n\n" ++
  "FLAGS:\n" ++
  "  --help, -h              show this help\n" ++
  "  --node I                monitor only node I (0..3) in isolation against a whole-system\n" ++
  "                          trace on stdin (consumer-side projection: validate I's actions,\n" ++
  "                          admit the rest). n=3f+1 is then the quorum universe, not #nodes.\n" ++
  "  --version               show version\n" ++
  "  --alphabet              print the model's action alphabet (JSON) — the emitter contract\n" ++
  "  --check-trace-alphabet  read stdin; check only that every line decodes against the\n" ++
  "                          alphabet (no model run). Reports ALPHABET MISMATCH on failure.\n" ++
  "  --rust-emitter-stub     print a Rust trait skeleton to implement a trace emitter\n\n" ++
  "EXIT CODES: 0 accepted/ok · 1 model rejection · 2 usage/IO · 3 alphabet mismatch"

/-- Run the monitor over stdin; returns the process exit code. -/
def runMonitor : IO UInt8 := do
  let input ← (← IO.getStdin).readToEnd
  match parseInput input with
  | .error e => IO.eprintln s!"input error: {e}"; return 2
  | .ok lines =>
    let verdict := runTrace lines
    IO.println verdict.render
    return (match verdict with
      | .accepted _     => 0
      | .rejected ..    => 1
      | .decodeError .. => 3
      | .noInitState    => 2)

/-- Syntactic-only check: does every line decode against the alphabet? -/
def checkAlphabet : IO UInt8 := do
  let input ← (← IO.getStdin).readToEnd
  match parseInput input with
  | .error e => IO.eprintln s!"ALPHABET MISMATCH — {e}"; return 3
  | .ok lines => do
    let mut i := 1
    for (raw, j) in lines do
      match parseLine j with
      | .error msg =>
        IO.eprintln s!"ALPHABET MISMATCH — line {i} ({actionOf j}): {msg}\n  {raw}"
        return 3
      | .ok _ => pure ()
      i := i + 1
    IO.println s!"TRACE ALPHABET OK — {lines.length} label(s) decode against the Chorus alphabet"
    return 0

end ChorusMonitor

/-- Top-level entry point for `lean --run`. -/
def main (args : List String) : IO Unit := do
  let code : UInt8 ← match args with
    | []                        => ChorusMonitor.runMonitor
    | ["--help"] | ["-h"]       => do IO.println ChorusMonitor.usageText; pure 0
    | ["--version"]             => do IO.println ChorusMonitor.versionText; pure 0
    | ["--alphabet"]            => do IO.println chorusAlphabetJson; pure 0
    | ["--rust-emitter-stub"]   => do IO.println chorusRustStub; pure 0
    | ["--check-trace-alphabet"]=> ChorusMonitor.checkAlphabet
    | ["--node", n]             => ChorusMonitor.runNodeMonitor n
    | _                         => do
        IO.eprintln s!"unknown arguments: {args}\n"; IO.eprintln ChorusMonitor.usageText; pure 2
  if code ≠ 0 then IO.Process.exit code
