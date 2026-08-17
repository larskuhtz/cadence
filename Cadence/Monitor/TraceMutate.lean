/-
Trace mutation tool for the Chorus model-conformance monitor.

Reads a JSONL trace from stdin, applies the named mutation from the `MUTATION`
environment variable, and writes the mutated JSONL to stdout (one compact JSON
object per line; comments are dropped).

Each mutation turns a model-ACCEPTED trace into one that models a *class of
implementation divergence*, which the monitor must then REJECT.  This is the
negative half of the conformance framework: it confirms the monitor has teeth
against realistic bugs, using the trace the implementation already emits — no
protocol-implementation changes required.

  MUTATION            models the bug…                          monitor rejects via
  ─────────           ───────────────                          ───────────────────
  shrink-quorum       accepting an undersized (<2f+1) QC       require supermajority
  forge-quorum        counting a non-voter in a QC             require ∀r∈q, r voted
  drop-commitqc       finalizing with no commit certificate    require msg_commitqc_*
  drop-fastqc         casting a fast-commit with no FastQC     unbridgeable commit_sign
  swap-verdict        committing the wrong verdict (pos/neg)   require matching vote sigs
  reorder-vote        using a QC before its evidence exists    require voter sig present
  dup-finalize        finalizing the same slot twice           require ¬ already committed

Usage:  MUTATION=shrink-quorum ./TraceMutate < trace.jsonl | ./monitor
-/
import Lean
open Lean

set_option linter.deprecated false

namespace TraceMutate

def getArgs (j : Json) : Array Json :=
  ((j.getObjVal? "args").toOption.getD (Json.arr #[])).getArr?.toOption.getD #[]

def getAct (j : Json) : String :=
  ((j.getObjVal? "action").bind (·.getStr?)).toOption.getD ""

def mkLine (act : String) (args : Array Json) : Json :=
  Json.mkObj [("action", Json.str act), ("args", Json.arr args)]

def isArr : Json → Bool
  | .arr _ => true
  | _      => false

def innerArr (j : Json) : Array Json := j.getArr?.toOption.getD #[]

/-- Array with element `idx` removed. -/
def removeIdx (objs : Array Json) (idx : Nat) : Array Json := Id.run do
  let mut out := #[]
  for i in [0:objs.size] do
    if i ≠ idx then out := out.push objs[i]!
  return out

/-- Drop the last element of the first nodeset argument found (undersized QC). -/
def shrinkQuorum (objs : Array Json) : Array Json := Id.run do
  for i in [0:objs.size] do
    let args := getArgs objs[i]!
    if let some k := args.findIdx? isArr then
      let inner := innerArr args[k]!
      if inner.size > 0 then
        return objs.set! i (mkLine (getAct objs[i]!) (args.set! k (Json.arr inner.pop)))
  return objs

/-- Make a quorum count a node that never voted: drop the vote of a node that
    is a member of the first quorum, leaving the quorum unchanged. The QC then
    references a signer whose vote is absent, so aggregation's
    `∀ r ∈ q, r voted` guard fails. (Robust however many nodes vote — unlike
    injecting a "non-voter", which does not exist when the whole set votes.) -/
def forgeQuorum (objs : Array Json) : Array Json := Id.run do
  -- x := first member of the first quorum nodeset.
  let mut member : Option Nat := none
  for j in objs do
    if let some k := (getArgs j).findIdx? isArr then
      if let some e0 := (innerArr (getArgs j)[k]!)[0]? then
        member := e0.getNat?.toOption
        break
  match member with
  | none => return objs
  | some x =>
    for i in [0:objs.size] do
      if getAct objs[i]! == "vote" && ((getArgs objs[i]!)[0]? >>= (·.getNat?.toOption)) == some x then
        return removeIdx objs i
    return objs

/-- Remove the first `broadcast_commitqc_*` (finalize with no certificate). -/
def dropCommitQc (objs : Array Json) : Array Json := Id.run do
  for i in [0:objs.size] do
    if (getAct objs[i]!).startsWith "broadcast_commitqc" then
      return removeIdx objs i
  return objs

/-- Remove the first `aggregate_fastqc_*` (a node casts a fast-commit vote with
    no FastQC behind it). The monitor cannot bridge the missing `commit_sign`
    (its guard `local_fastqc_*` is unmet), so the later cast is rejected. -/
def dropFastqc (objs : Array Json) : Array Json := Id.run do
  for i in [0:objs.size] do
    if (getAct objs[i]!).startsWith "aggregate_fastqc" then
      return removeIdx objs i
  return objs

/-- Flip the first `aggregate_fastqc_neg (i j q)` to `_pos (i j root q)`
    (commit the wrong verdict). -/
def swapVerdict (objs : Array Json) : Array Json := Id.run do
  for i in [0:objs.size] do
    if getAct objs[i]! == "aggregate_fastqc_neg" then
      let a := getArgs objs[i]!
      if a.size == 3 then
        let newArgs := #[a[0]!, a[1]!, toJson (0 : Nat), a[2]!]
        return objs.set! i (mkLine "aggregate_fastqc_pos" newArgs)
  return objs

/-- Move the first `vote` to the end (QC used before its evidence exists). -/
def reorderVote (objs : Array Json) : Array Json := Id.run do
  for i in [0:objs.size] do
    if getAct objs[i]! == "vote" then
      return (removeIdx objs i).push objs[i]!
  return objs

/-- Append a copy of the last `finalize_commit` (double finalization). -/
def dupFinalize (objs : Array Json) : Array Json := Id.run do
  let mut last : Option Json := none
  for j in objs do
    if getAct j == "finalize_commit" then last := some j
  match last with
  | some j => return objs.push j
  | none   => return objs

def apply (name : String) (objs : Array Json) : Except String (Array Json) :=
  match name with
  | "shrink-quorum" => .ok (shrinkQuorum objs)
  | "forge-quorum"  => .ok (forgeQuorum objs)
  | "drop-commitqc" => .ok (dropCommitQc objs)
  | "drop-fastqc"   => .ok (dropFastqc objs)
  | "swap-verdict"  => .ok (swapVerdict objs)
  | "reorder-vote"  => .ok (reorderVote objs)
  | "dup-finalize"  => .ok (dupFinalize objs)
  | "identity"      => .ok objs
  | other           => .error s!"unknown mutation '{other}'"

def parseObjs (input : String) : Except String (Array Json) := do
  let mut acc := #[]
  for ln in input.splitOn "\n" do
    let t := ln.trim
    if t.isEmpty || "//".isPrefixOf t || "#".isPrefixOf t then continue
    match Json.parse t with
    | .ok j    => acc := acc.push j
    | .error e => throw s!"JSON parse error: {e} on line: {t}"
  pure acc

end TraceMutate

def main : IO Unit := do
  let name := (← IO.getEnv "MUTATION").getD "identity"
  let input ← (← IO.getStdin).readToEnd
  match TraceMutate.parseObjs input with
  | .error e => IO.eprintln s!"mutate: {e}"; IO.Process.exit 2
  | .ok objs =>
    match TraceMutate.apply name objs with
    | .error e => IO.eprintln s!"mutate: {e}"; IO.Process.exit 2
    | .ok out  => for j in out do IO.println j.compress
