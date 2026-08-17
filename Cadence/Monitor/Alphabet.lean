/-
Model alphabet, derived mechanically from the `Chorus.Label` inductive.

The monitor's alphabet is exactly the constructors of the model's action `Label`
type. Reflecting on the inductive at elaboration time keeps the published
alphabet — and the generated Rust emitter stub — in lock-step with the model:
they cannot drift, because there is no hand-maintained copy.

Produces two string defs consumed by the monitor CLI (`Monitor/ChorusMonitor.lean`):
* `chorusAlphabetJson` — a language-neutral description of the alphabet
  (`--alphabet`);
* `chorusRustStub`     — a Rust trait skeleton an emitter author implements
  (`--rust-emitter-stub`).

Instance encoded here: n = 3f+1 = 4, f = 1, roots = 2, slots = 1 (matches
`Monitor/ChorusMonitor.lean`). Only `node`, `merkle_root`, `nodeset` occur as argument
sorts (no action takes a `slot`/`Phase`/`PathChoice` argument), and all are
small bounded non-negative integers / sets of them — no floats, strings, or
wide arithmetic — so the value encoding is unambiguous.
-/
import Cadence.Chorus
open Lean Lean.Meta Lean.Elab.Command

namespace Chorus.MonitorAlphabet

/-- Reflect an action `Label` inductive into `(actionName, argSorts)` pairs.
    The first `numParams` binders of each constructor are the sort type
    parameters; each remaining (explicit) argument's type is one of those
    parameters, whose user-name is the sort. -/
def reflectActions (labelName : Name) : MetaM (Array (String × Array String)) := do
  let ind ← getConstInfoInduct labelName
  let nParams := ind.numParams
  let mut out := #[]
  for ctorName in ind.ctors do
    let ci ← getConstInfoCtor ctorName
    let sorts ← forallTelescopeReducing ci.type fun binders _ => do
      let params := binders.extract 0 nParams
      let args := binders.extract nParams binders.size
      let mut pmap : Std.HashMap FVarId String := {}
      for p in params do
        pmap := pmap.insert p.fvarId! (← p.fvarId!.getUserName).toString
      let mut ss := #[]
      for a in args do
        let ty ← a.fvarId!.getType
        ss := ss.push (match ty with | .fvar fid => pmap.getD fid "?" | _ => "?")
      return ss
    out := out.push (ctorName.getString!, sorts)
  return out

/-! ### Serializers (pure; used at elaboration time to bake the string defs).
    Built with plain string concatenation so literal `{`/`}` are not mistaken
    for `s!` interpolation. -/

private def q (s : String) : String := "\"" ++ s ++ "\""

/-- Actions the emitter does NOT emit — the monitor inserts them (Stage B). Kept
    in step with `internalCandidates` in `Monitor/ChorusMonitor.lean`. -/
def internalActionNames : List String :=
  ["commit_sign_pos", "commit_sign_neg", "commit_assign_pos", "commit_assign_neg"]

def isInternal (a : String) : Bool := internalActionNames.contains a

/-- Neutral JSON description of the alphabet. Each action is tagged `observable`
    (the emitter emits it) or `internal` (the monitor inserts it). -/
def alphabetJsonOf (acts : Array (String × Array String)) : String :=
  let actLine := fun (a : String) (ss : Array String) =>
    "    {" ++ q "action" ++ ": " ++ q a ++ ", " ++ q "args" ++ ": ["
      ++ ", ".intercalate (ss.toList.map q) ++ "], "
      ++ q "role" ++ ": " ++ q (if isInternal a then "internal" else "observable") ++ "}"
  let actLines := acts.toList.map (fun (a, ss) => actLine a ss)
  "{\n"
    ++ "  " ++ q "model" ++ ": " ++ q "Chorus" ++ ",\n"
    ++ "  " ++ q "instance" ++ ": {" ++ q "n" ++ ": 4, " ++ q "f" ++ ": 1, "
      ++ q "num_roots" ++ ": 2, " ++ q "num_slots" ++ ": 1},\n"
    ++ "  " ++ q "sorts" ++ ": {\n"
    ++ "    " ++ q "node" ++ ": {" ++ q "encoding" ++ ": " ++ q "uint" ++ ", "
      ++ q "domain" ++ ": " ++ q "0..3" ++ "},\n"
    ++ "    " ++ q "merkle_root" ++ ": {" ++ q "encoding" ++ ": " ++ q "uint" ++ ", "
      ++ q "domain" ++ ": " ++ q "0..1" ++ "},\n"
    ++ "    " ++ q "nodeset" ++ ": {" ++ q "encoding" ++ ": " ++ q "array<uint>" ++ ", "
      ++ q "element" ++ ": " ++ q "node" ++ ", "
      ++ q "note" ++ ": " ++ q "strictly ascending; a subset of node" ++ "}\n"
    ++ "  },\n"
    ++ "  " ++ q "actions" ++ ": [\n"
    ++ ",\n".intercalate actLines ++ "\n"
    ++ "  ]\n"
    ++ "}"

/-- Rust type + per-argument formatting for a sort. -/
private def sortRust (s : String) : String × Bool :=  -- (rustType, isNodeset)
  match s with
  | "nodeset" => ("&[u64]", true)
  | _         => ("u64", false)   -- node, merkle_root

/-- `(paramDecls, placeholders, formatArgs)` for a constructor's argument sorts,
    naming each argument `<sort><k>` (k = index among same-sort arguments). -/
private def rustArgs (sorts : Array String) : String × String × String := Id.run do
  let mut counts : Std.HashMap String Nat := {}
  let mut params : List String := []
  let mut phs : List String := []
  let mut fas : List String := []
  for s in sorts do
    let k := counts.getD s 0
    counts := counts.insert s (k + 1)
    let nm := s ++ toString k
    let (ty, isNs) := sortRust s
    params := params ++ [nm ++ ": " ++ ty]
    phs := phs ++ ["{}"]
    fas := fas ++ [if isNs then "fmt_nodeset(" ++ nm ++ ")" else nm]
  return (", ".intercalate params, ", ".intercalate phs, ", ".intercalate fas)

private def rustMethod (name : String) (sorts : Array String) : String :=
  let (params, phs, fas) := rustArgs sorts
  let sep := if params.isEmpty then "" else ", "
  -- format!(r#"{"action": "NAME", "args": [PH]}"#, FAS)  (braces doubled for format!)
  let fmtStr := "{{" ++ q "action" ++ ": " ++ q name ++ ", " ++ q "args" ++ ": [" ++ phs ++ "]}}"
  let call :=
    if fas.isEmpty
    then "self.emit(format!(r#" ++ q fmtStr ++ "#));"
    else "self.emit(format!(r#" ++ q fmtStr ++ "#, " ++ fas ++ "));"
  "    fn " ++ name ++ "(&mut self" ++ sep ++ params ++ ") {\n        " ++ call ++ "\n    }"

/-- Rust trait skeleton: implement `emit`, then call the per-action methods at
    the corresponding points in the simulation. -/
def rustStubOf (acts : Array (String × Array String)) : String :=
  -- Only OBSERVABLE actions get a method; the monitor inserts the internal ones.
  let observable := acts.toList.filter (fun (a, _) => ¬ isInternal a)
  let methodDefs := "\n\n".intercalate (observable.map (fun (a, ss) => rustMethod a ss))
  "// GENERATED from the Chorus model's action `Label` by\n"
    ++ "//   chorus-monitor --rust-emitter-stub\n"
    ++ "// Do not edit by hand; regenerate when the model's action alphabet changes.\n"
    ++ "//\n"
    ++ "// This trait covers only the OBSERVABLE actions. The model's internal\n"
    ++ "// steps (" ++ ", ".intercalate internalActionNames ++ ") are\n"
    ++ "// NOT emitted — the monitor inserts them — so you never call them here.\n"
    ++ "//\n"
    ++ "// Instance: n = 3f+1 = 4, f = 1, roots = 2, slots = 1.\n"
    ++ "// Sort encodings:  node, merkle_root : u64 (node in 0..3, root in 0..1);\n"
    ++ "//                  nodeset : &[u64], strictly ascending, a subset of node.\n"
    ++ "// All values are small bounded non-negative integers / sets of them — no\n"
    ++ "// floats, strings, or wide arithmetic, so encoding is unambiguous. The\n"
    ++ "// monitor validates domains and reports any out-of-range value as an\n"
    ++ "// ALPHABET MISMATCH (distinct from a model rejection).\n"
    ++ "//\n"
    ++ "// Usage: implement `emit` (append the line to your trace sink), then call\n"
    ++ "// e.g. `self.vote(i)` / `self.aggregate_fastqc_neg(i, j, &q)` at the\n"
    ++ "// matching points in your simulation.\n\n"
    ++ "fn fmt_nodeset(xs: &[u64]) -> String {\n"
    ++ "    let inner = xs.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(\", \");\n"
    ++ "    format!(\"[{}]\", inner)\n"
    ++ "}\n\n"
    ++ "pub trait ChorusTrace {\n"
    ++ "    /// The only method you implement: record one JSONL trace line.\n"
    ++ "    fn emit(&mut self, line: String);\n\n"
    ++ methodDefs ++ "\n"
    ++ "}\n"

end Chorus.MonitorAlphabet

-- Bake the reflected alphabet into string defs usable at runtime.
run_cmd do
  let acts ← liftTermElabM (Chorus.MonitorAlphabet.reflectActions `Chorus.Label)
  elabCommand (← `(def $(mkIdent `chorusAlphabetJson) : String := $(quote (Chorus.MonitorAlphabet.alphabetJsonOf acts))))
  elabCommand (← `(def $(mkIdent `chorusRustStub) : String := $(quote (Chorus.MonitorAlphabet.rustStubOf acts))))
