/-
An appendix of the guide: one specimen of each element the chapters write
with, for the chapters' authors and for review. The session that has moved
every element into its chapter removes this page, its `include` in
[CadenceGuide.lean](../../CadenceGuide.lean), and the specimen files under
[specimen](../../specimen).
-/
import CadenceGuide.Elements

open Verso.Genre Manual
open CadenceGuide

set_option pp.rawOnError true

#doc (Manual) "Appendix: the guide's elements" =>
%%%
file := "elements"
%%%

_One specimen of each element the chapters are written with. Each one reads
the compiled development or a checked file while the guide builds, and fails
the build when what it shows has gone stale._

# A paper citation

`{cite}` takes a label of the paper's target revision and renders the
reference a reader finds in the PDF: {cite}`lemma:chorus-agreement`, and in
the supplement {cite}`lem:decision-propagation`. A label that is not in the
label map fails the build.

# A claims box

`:::claims` sets its contents off from the text around it, for the front
page's claims and for the "what you check" boxes.

:::claims (title := "What this project claims")
*MCP Safety*, {cite}`def:safety`: two correct validators never hold different
entries at the same position of their logs. {decl}`Cadence.system_positional_log_safety`
:::

# A figure

`{figure}` inlines an SVG file from the repository, without its dark-scheme
rules. A file that is missing, has no `<title>`, or uses a class or id
without the `dg-` prefix fails the build.

{figure "docs/guide/specimen/placeholder.svg" (caption := "A placeholder, until the diagrams exist.")}

# A contract's checklist

`{contractFields}` lists a contract class field by field, from the compiled
class: what each field says (its docstring), its level, and what proves it.
A field without a docstring fails the build, as does a field that no
instance provides when its class is not an assumed contract.

{contractFields OrchestratorWithTotality}

# An audit table

`{auditTable}` renders a model's audit table from its data file, and checks
every action name against the model's actions and every relation named in
the derived columns against the model's declarations. This one shows the
stub's two rows, marked as a selection.

{auditTable Chorus "docs/guide/audit/Chorus.tsv" +sample}
