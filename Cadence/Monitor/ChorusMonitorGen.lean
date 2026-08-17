/-
Chorus model-conformance monitor — GENERATED instantiation variant.

Identical in behaviour to `Monitor/ChorusMonitor.lean`, but the error-prone
instantiation block (Th/St/Lbl, chThy, the specialized Inhabited seed, and the
`NextAct.extracted`/`initializer.ext.extracted` applications) is produced by
Veil's `#gen_monitor` command instead of hand-written. `Monitor/ChorusMonitor.lean` is
the test oracle: `scripts/test-chorus-monitor.sh` runs both on the same trace
fixtures and they must agree.

`#gen_monitor` lives in the Veil fork this project depends on
(`Veil/Frontend/DSL/Module/GenMonitor.lean`); its argument keywords are
`scoped`, so the command has to be activated with `open scoped
Veil.GenMonitor`.
-/
import Cadence.Chorus
open Veil Veil.Extract
open scoped Veil.GenMonitor
open scoped Chorus
open Lean (Json)

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
set_option linter.deprecated false

/-- Empty Byzantine set at n = 3f+1 = 4, f = 1 (see `Monitor/ChorusMonitor.lean`). -/
def emptyByz4 : ByzNodeSet (Fin (3 * 1 + 1)) (ByzNSet (3 * 1 + 1)) :=
  byzNodeSetFin (3 * 1 + 1) 1 rfl (fun _ => False) (by decide)

-- ▼▼▼ the entire instantiation, generated ▼▼▼
#gen_monitor Chorus into ChorusGen
  sorts (Fin 1), (Fin (3 * 1 + 1)), (ByzNSet (3 * 1 + 1)), (Fin 2),
        Chorus.Phase_IndT, Chorus.PathChoice_IndT
  theory (Chorus.Theory.mk (fun j => j == 0))
  byz emptyByz4
-- ▲▲▲ emits ChorusGen.{Th,St,Lbl,chThy,stInhab,cnext,cinit,initStates,step} ▲▲▲

namespace ChorusMonitorGen

abbrev ND := Fin (3 * 1 + 1)
abbrev NS := ByzNSet (3 * 1 + 1)
abbrev MR := Fin 2
abbrev Lbl := ChorusGen.Lbl
abbrev St := ChorusGen.St

/-- Interpret the generated raw-outcome `step` into an acceptance verdict. -/
inductive StepResult where
  | ok (st : St)
  | notAccepted (why : String)
  | ambiguous (n : Nat)

def step (st : St) (lbl : Lbl) : StepResult :=
  match ChorusGen.step st lbl with
  | []                      => .notAccepted "action not enabled (no outcome)"
  | [.success st']          => .ok st'
  | [.assertionFailure _ _] => .notAccepted "require failed (label not enabled in model)"
  | [.divergence]           => .notAccepted "divergence"
  | outs                    => .ambiguous outs.length

def initState : Option St := ChorusGen.initStates.head?

/-- Stage B: internal-action saturation (see `Monitor/ChorusMonitor.lean`). The emitter
    emits only observable actions; the monitor bridges `commit_sign_*` /
    `commit_assign_*` by applying every enabled internal action to a fixpoint. -/
def internalCandidates : List Lbl :=
  (List.finRange (3 * 1 + 1)).flatMap fun i =>
  (List.finRange (3 * 1 + 1)).flatMap fun j =>
    [Chorus.Label.commit_sign_neg i j, Chorus.Label.commit_assign_neg i j]
    ++ (List.finRange 2).flatMap fun m =>
       [Chorus.Label.commit_sign_pos i j m, Chorus.Label.commit_assign_pos i j m]

def applyEnabledInternal (st : St) : Option St :=
  internalCandidates.findSome? fun lbl =>
    match ChorusGen.step st lbl with
    | [.success st'] => if st' == st then none else some st'
    | _              => none

partial def saturate (st : St) : St :=
  match applyEnabledInternal st with
  | some st' => saturate st'
  | none     => st

/-! ## Label decoding (JSON → Lbl) — identical to the hand-written monitor -/

private def toFin (bound : Nat) (k : Nat) : Except String (Fin bound) :=
  if h : k < bound then .ok ⟨k, h⟩ else .error s!"index {k} out of range (≥ {bound})"

private def mkNSet (sorted : List ND) : Except String NS :=
  if h : sorted.Pairwise (· < ·) then .ok ⟨sorted, h⟩
  else .error s!"nodeset {sorted.map (·.val)} not strictly sortable"

private def dNode (j : Json) : Except String ND := j.getNat? >>= toFin (3 * 1 + 1)
private def dRoot (j : Json) : Except String MR := j.getNat? >>= toFin 2

private def dNSet (j : Json) : Except String NS := do
  let arr ← j.getArr?
  let fins ← arr.toList.mapM fun e => e.getNat? >>= toFin (3 * 1 + 1)
  mkNSet ((fins.dedup).mergeSort (fun a b => decide (a ≤ b)))

def decodeLabel (act : String) (args : List Json) : Except String Lbl :=
  match act, args with
  | "advance_to_deadline", []        => pure .advance_to_deadline
  | "advance_to_fb_arm", []          => pure .advance_to_fb_arm
  | "advance_to_mvba_arm", []        => pure .advance_to_mvba_arm
  | "mvba_terminate", []             => pure .mvba_terminate
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

def actionOf (j : Json) : String :=
  (j.getObjVal? "action" |>.bind (·.getStr?)).toOption.getD "?"

def parseLine (j : Json) : Except String Lbl := do
  let act ← (← j.getObjVal? "action").getStr?
  let argsJson := (j.getObjVal? "args").toOption.getD (Json.arr #[])
  let args ← argsJson.getArr?
  decodeLabel act args.toList

/-! ## Trace folding + entry point -/

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
      match step (saturate st) lbl with
      | .ok st'          => go rest st' (i + 1)
      | .notAccepted why => .rejected i (actionOf j) why
      | .ambiguous n     => .rejected i (actionOf j)
                              s!"ambiguous: {n} distinct model outcomes (trace under-determines args)"

def parseInput (input : String) : Except String (List (String × Json)) := do
  let mut acc := #[]
  for ln in input.splitOn "\n" do
    let t := ln.trim
    if t.isEmpty || "//".isPrefixOf t || "#".isPrefixOf t then continue
    match Json.parse ln with
    | .ok j => acc := acc.push (t, j)
    | .error e => throw s!"JSON parse error on line: {t}\n  {e}"
  pure acc.toList

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match parseInput input with
  | .error e => IO.eprintln s!"input error: {e}"; IO.Process.exit 1
  | .ok lines =>
    let verdict := runTrace lines
    IO.println verdict.render
    match verdict with
    | .accepted _ => pure ()
    | _           => IO.Process.exit 1

end ChorusMonitorGen

/-- Top-level entry point for `lean --run`. -/
def main : IO Unit := ChorusMonitorGen.main
