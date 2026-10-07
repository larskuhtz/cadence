/-
Everything a chapter of the guide needs, in one import: the elements, and the
development they talk about.

A chapter resolves its references — `{decl}`, `{claim}`, `{contractFields}` —
in its own environment, so the development is imported here, once. An element
a chapter session adds is a module of its own, imported by the chapter that
uses it, not added here: this file and the elements below belong to no
chapter.

The elements, by module:

* [Audit.lean](Audit.lean) — `{decl}`, `{claim}`, `{model}`, `{contracts}`,
  and the shared vocabulary (the contract classes, the witness modules, the
  assumed contracts);
* [Cite.lean](Cite.lean) — `{cite}`, a paper citation from the label map;
* [Figure.lean](Figure.lean) — `{figure}`, an SVG diagram inlined;
* [ClaimsBox.lean](ClaimsBox.lean) — `:::claims`, a set-off box;
* [ContractFields.lean](ContractFields.lean) — `{contractFields}`, a
  contract's checklist;
* [AuditTable.lean](AuditTable.lean) — `{auditTable}`, a model's audit table.
-/
import CadenceGuide.Audit
import CadenceGuide.Cite
import CadenceGuide.Figure
import CadenceGuide.ClaimsBox
import CadenceGuide.ContractFields
import CadenceGuide.AuditTable
import Cadence
