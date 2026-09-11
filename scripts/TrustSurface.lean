/-
Emit the trust boundary of the development as a standalone HTML page,
**derived from the compiled environment** rather than written by hand.

Run by `scripts/docs.sh`, which redirects stdout to `trust-boundary.html`
next to the generated documentation, so the page inherits its stylesheet and
can link straight into the rendered source of every declaration it names.

Four questions are answered mechanically:

1. What does each end result rest on?     (its axiom footprint, per Lean's kernel)
2. Does this development declare an axiom? (it must not)
3. Which module contracts have no instance? (exactly what is left unproven)
4. What does no machine check at all?      (stated, since it cannot be derived)

Nothing here is a restatement: every row is computed from the `.olean`s that
`lake build` produced, so a claim that has drifted from the code cannot
survive a rebuild of this page.
-/
import Cadence

open Lean Meta Elab Command

/-- Lean's three standard classical axioms — the expected footprint. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The end results, in the order `Cadence.lean` pins them. -/
def endResults : List Name :=
  [``Chorus.invariants_of_reachable,
   ``Chorus.slotConsensusSafety,
   ``Chorus.slotConsensus_of_temporal,
   ``Chorus.evidence_pigeonhole_of_reachable,
   ``Chorus.fbcert_of_honest_fallback_votes,
   ``Chorus.fbcommitqc_of_honest_commit_votes,
   ``Chorus.commitqc_of_honest_fast_dominant,
   ``Chorus.progress_dichotomy_of_saturation,
   ``Chorus.build_totality_of_reachable,
   ``Conductor.orchestratorSafety,
   ``Conductor.orchestrator_of_temporal,
   ``Cadence.positional_log_safety,
   ``Cadence.system_positional_log_safety,
   ``FallbackReceipt.invariants_of_reachable,
   ``FallbackReceipt.build_totality_of_reachable,
   ``Mvba.invariants_of_reachable,
   ``Mvba.reachable_agreement,
   ``Mvba.reachable_integrity,
   ``Mvba.reachable_external_validity,
   ``Mvba.mvbaSafety,
   ``Mvba.mvba_of_temporal]

/-- Contract classes to report on: the state-level fragment and the temporal
level of each paper module. -/
def contractClasses : List Name :=
  [``SlotConsensusSafety, ``SlotConsensusTemporal,
   ``OrchestratorSafety, ``OrchestratorTemporal,
   ``MVBASafety, ``MVBATemporal,
   ``ACSSafety, ``ACSTemporal]

def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

/-- Is `m` one of this development's own modules? -/
def isOwnModule (m : Name) : Bool := m == `Cadence || (`Cadence).isPrefixOf m

/-- The module a declaration was introduced in. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => some env.header.moduleNames[idx.toNat]!
  | none => none

/-- A link into the generated documentation: module `Cadence.Chorus.Compose`
becomes `Cadence/Chorus/Compose.html#<decl>`. This is what turns the page
into a navigation hub rather than a second inventory. -/
def declLink (env : Environment) (n : Name) : String :=
  match moduleOf env n with
  | some m =>
    let path := String.intercalate "/" (m.components.map toString)
    s!"<a href=\"{path}.html#{n}\"><code>{esc n.toString}</code></a>"
  | none => s!"<code>{esc n.toString}</code>"

/-- Head constant of a type, after stripping `∀` binders **syntactically**.
Deliberately no `whnf`: this runs over every declaration of the development,
and reducing proof-sized types there costs minutes and overruns the heartbeat
budget. An instance's type always mentions its class at the head already. -/
partial def headSymbol : Expr → Option Name
  | .forallE _ _ b _ => headSymbol b
  | e => e.getAppFn.constName?

/-- The head symbol of every `∀`-binder's type, syntactically. Used to see
whether a declaration that produces a contract instance *consumes* one — i.e.
whether it is an unconditional witness or a conditional join. -/
partial def binderHeads : Expr → List Name
  | .forallE _ t b _ => (match headSymbol t with | some n => [n] | none => []) ++ binderHeads b
  | _ => []

/-- A declaration of this development producing a contract instance, together
with the contract classes it *requires* in order to do so. An empty
requirement list is an unconditional witness; a non-empty one is a join, which
proves nothing on its own. -/
structure Provider where
  name : Name
  requires : List Name

/-- One pass over this development's declarations, grouping those that produce
a contract instance by the class they produce.

Two exclusions matter, and getting them wrong inverts the page's conclusion:

* **Parent projections.** `extends` generates `X.toXSafety`, whose type has
  `XSafety` at the head for *every* `X`. It witnesses nothing, so projections
  are dropped (`getProjectionFnInfo?`).
* **Conditional joins.** `Chorus.slotConsensus_of_temporal` produces a full
  `SlotConsensus` — but only when handed a `SlotConsensusTemporal`, of which
  this development has no instance. Recorded separately rather than counted
  as a proof. -/
def providerMap (env : Environment) : Std.HashMap Name (Array Provider) := Id.run do
  let mut m : Std.HashMap Name (Array Provider) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail then continue
    if (env.getProjectionFnInfo? n).isSome then continue
    match moduleOf env n with
    | some mod =>
      if isOwnModule mod then
        match ci with
        | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
          match headSymbol ci.type with
          | some cls =>
            if contractClasses.contains cls then
              let reqs := (binderHeads ci.type).filter contractClasses.contains
              m := m.insert cls ((m.getD cls #[]).push ⟨n, reqs.eraseDups⟩)
          | none => pure ()
        | _ => pure ()
    | none => pure ()
  return m

set_option maxHeartbeats 1000000 in
run_cmd liftTermElabM do
  let env ← getEnv
  let provMap := providerMap env
  let mut o : Array String := #[]
  let p (s : String) : Array String → Array String := fun a => a.push s
  o := p "<!DOCTYPE html><html lang=\"en\"><head><meta charset=\"utf-8\">" o
  o := p "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">" o
  o := p "<title>The trust boundary — Cadence</title>" o
  o := p "<link rel=\"stylesheet\" href=\"style.css\">" o
  o := p "<style>
    body{max-width:62rem;margin:0 auto;padding:2rem 1.25rem;line-height:1.55}
    table{border-collapse:collapse;width:100%;margin:1rem 0}
    th,td{text-align:left;padding:.4rem .6rem;border-bottom:1px solid #8884;vertical-align:top}
    th{font-weight:600}
    code{font-size:.92em}
    .ok{color:#137333}.bad{color:#b3261e;font-weight:700}
    .note{opacity:.8;font-size:.94em}
  </style></head><body>" o

  o := p "<h1>The trust boundary</h1>" o
  o := p "<p class=\"note\">Generated from the compiled development by
    <code>scripts/TrustSurface.lean</code>. Every row below is computed from the
    <code>.olean</code>s that <code>lake build</code> produced, not written by
    hand, so a claim that has drifted from the code cannot survive a rebuild of
    this page. Declaration names link into the rendered source.</p>" o

  -- 1. Axiom footprint of every end result.
  o := p "<h2>1. What each end result rests on</h2>" o
  o := p "<p>Lean's kernel records, for every theorem, the complete set of axioms
    its proof term uses. The expected set is Lean's three standard classical
    axioms and nothing else — in particular no <code>sorryAx</code>, which is
    what an admitted or stubbed proof shows up as.</p>" o
  o := p "<table><tr><th>Result</th><th>Module</th><th>Axiom footprint</th></tr>" o
  let mut drift := 0
  for r in endResults do
    let axs ← collectAxioms r
    let extra := axs.filter (fun a => !standardAxioms.contains a)
    let cell :=
      if extra.isEmpty then "<span class=\"ok\">the three standard axioms</span>"
      else
        let names := String.intercalate ", " (extra.toList.map (fun a => esc a.toString))
        s!"<span class=\"bad\">UNEXPECTED: {names}</span>"
    if !extra.isEmpty then drift := drift + 1
    let m := (moduleOf env r).map toString |>.getD "—"
    o := p s!"<tr><td>{declLink env r}</td><td><code>{esc m}</code></td><td>{cell}</td></tr>" o
  o := p "</table>" o
  o := p (if drift == 0 then
      s!"<p>All {endResults.length} results depend on exactly <code>propext</code>,
         <code>Classical.choice</code> and <code>Quot.sound</code>. The SMT solver
         is not among them: every discharge is reconstructed as a proof term and
         re-checked by the kernel.</p>"
    else s!"<p class=\"bad\">{drift} result(s) carry an unexpected axiom.</p>") o

  -- 2. Axioms this development declares itself.
  o := p "<h2>2. Axioms declared by this development</h2>" o
  let mut own : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail then continue
    if ci matches .axiomInfo _ then
      match moduleOf env n with
      | some m => if isOwnModule m then own := own.push n
      | none => pure ()
  o := p (if own.isEmpty then
      "<p><span class=\"ok\">None.</span> No <code>Cadence.*</code> module declares
       an axiom, so nothing in §1 is satisfied by an assumption introduced here.</p>"
    else
      let names := String.intercalate ", " (own.toList.map (fun n => s!"<code>{esc n.toString}</code>"))
      s!"<p class=\"bad\">{own.size} declared:</p><p>{names}</p>") o

  -- 3. Contracts with and without an instance.
  o := p "<h2>3. Module contracts, and which have no instance</h2>" o
  o := p "<p>Three states are distinguished, and the difference between the last
    two is the point of this table.
    <strong>Proven</strong>: some declaration of this development produces the
    contract outright.
    <strong>Proven relative to …</strong>: it is produced only when another
    contract is supplied — sound, but it inherits whatever that one assumes.
    <strong>No instance</strong>: nothing produces it, which is exactly what
    &ldquo;unproven&rdquo; means here. Because every field of a temporal class is
    stated over the proven fragment's own transitions, that absence is the
    complete statement of what is owed; there is no second place where these
    obligations are written down.</p>" o
  o := p "<table><tr><th>Contract</th><th>Unconditional instance</th>\
    <th>Conditional join</th><th>Status</th></tr>" o
  for cls in contractClasses do
    if env.contains cls then
      let provs := provMap.getD cls #[]
      let witnesses := provs.filter (·.requires.isEmpty)
      let joins := provs.filter (!·.requires.isEmpty)
      -- Three states, and the difference between the last two is the whole
      -- point of the page: a contract can be proven outright, proven only
      -- relative to another contract that is itself assumed, or not provided
      -- at all — which is what "unproven" means here.
      let status :=
        if !witnesses.isEmpty then "<span class=\"ok\">proven</span>"
        else if !joins.isEmpty then
          let deps := (joins.toList.flatMap (·.requires)).eraseDups
          s!"proven relative to {String.intercalate ", " (deps.map (fun r => s!"<code>{esc r.toString}</code>"))}"
        else "<span class=\"bad\">no instance — assumed</span>"
      let fmt (a : Array Provider) (withReqs : Bool) : String :=
        if a.isEmpty then "—"
        else String.intercalate ", " (a.toList.map fun pr =>
          if withReqs && !pr.requires.isEmpty then
            s!"{declLink env pr.name} <span class=\"note\">(given \
              {String.intercalate ", " (pr.requires.map (fun r => s!"<code>{esc r.toString}</code>"))})</span>"
          else declLink env pr.name)
      o := p s!"<tr><td>{declLink env cls}</td><td>{fmt witnesses false}</td>\
        <td>{fmt joins true}</td><td>{status}</td></tr>" o
  o := p "</table>" o
  o := p "<p>The <code>…Temporal</code> rows without an instance are the timing and
    liveness obligations. <code>ACSSafety</code> has none because the ACS is a
    standard primitive whose implementation is out of scope.</p>" o

  -- 4. What no machine checks.
  o := p "<h2>4. What no machine checks</h2>" o
  o := p "<p>Three things sit above the kernel and are believed rather than
    derived. This page cannot certify them; they are listed so that the boundary
    is complete.</p>
    <ol>
    <li><strong>The monotone-network contract.</strong> Network relations may be
      consulted in positive position only. Veil does not enforce this, and a
      violation would not fail the build — it is audited by hand
      (<code>docs/ChorusDesign.md</code> §3.1.1).</li>
    <li><strong>The two stated bridges</strong> — the ACS median range and the
      MVBA decision's certificate check — each interpreting a class parameter in
      the consumer's own vocabulary
      (<code>docs/CompositionContracts.md</code> §7).</li>
    <li><strong>The tooling</strong>: Lean's kernel, Veil's verification-condition
      generation, the model checker where it is used, and the solver's
      <code>sat</code> verdicts on non-load-bearing reachability witnesses
      (<code>docs/Architecture.md</code> §4 item 7).</li>
    </ol>" o

  o := p "</body></html>" o
  IO.println (String.intercalate "\n" o.toList)
