/-
`{pin "file" "command"}` — a `#guard_msgs` pin, quoted from the source file
that carries it.

A pin is a command with its expected output written above it as a doc
comment; `#guard_msgs` fails the build unless the command prints exactly that
text. So the doc comment *is* the evidence, and `{model}`, which shows a
declaration's code without its doc comment, would quote the command and leave
the result out. This element quotes the three parts as written — the expected
output, `#guard_msgs in`, the command — and links the module's rendered page.

It fails the guide's build when the file has no pin of that command, or more
than one, or when the file is not a module of the development the guide
imports. What it quotes is the text the development's own build checks.

    {pin "Cadence/Chorus/Certify.lean" "#veil_status Chorus"}
-/
import CadenceGuide.Audit

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CadenceGuide

structure PinConfig where
  file : String
  command : String

instance : FromArgs PinConfig DocElabM :=
  ⟨PinConfig.mk <$> .positional `file .string <*> .positional `command .string⟩

/-- The pin of `command` in `lines`: the expected-output doc comment, the
`#guard_msgs in` line and the command, as written. One pin, or an error. -/
def findPin (lines : Array String) (command : String) : Except String String := do
  let trim (s : String) : String := s.trimAscii.toString
  let mut found : Array String := #[]
  for k in [2:lines.size] do
    unless trim lines[k]! == command && trim lines[k-1]! == "#guard_msgs in" do continue
    -- Walk back from the end of the doc comment to its opening `/--`.
    let mut j := k - 2
    unless trim lines[j]! |>.endsWith "-/" do
      throw s!"`{command}` has `#guard_msgs in` above it but no expected output"
    while j > 0 && !(trim lines[j]! |>.startsWith "/--") do j := j - 1
    unless trim lines[j]! |>.startsWith "/--" do
      throw s!"`{command}`: no opening `/--` above its `#guard_msgs in`"
    found := found.push ("\n".intercalate (lines.extract j (k + 1)).toList)
  match found with
  | #[p] => pure p
  | #[] => throw s!"no `#guard_msgs` pin of `{command}`"
  | ps => throw s!"{ps.size} pins of `{command}`; expected one"

/-- `{pin "file" "command"}` — the `#guard_msgs` pin of `command` in `file`,
quoted as written. -/
@[block_command]
def pin : BlockCommandOf PinConfig
  | ⟨file, command⟩ => do
    let path : System.FilePath := file
    unless file.endsWith ".lean" && (← path.pathExists) do
      throwError "{file} is not a Lean file of the repository"
    let mod := ((file.dropEnd 5).toString.splitOn "/").foldl Name.str .anonymous
    unless (← getEnv).header.moduleNames.contains mod do
      throwError "{mod} is not a module the guide imports, so its pins are not checked by \
        the build this guide describes"
    let text ← match findPin (← IO.FS.lines path) command with
      | .ok t => pure t
      | .error e => throwError "{file}: {e}"
    let html := s!"<div class=\"cg-status cg-plain\"><dl><dt>Pinned in</dt><dd>\
      <a href=\"{moduleUrl mod}\"><code>{esc file}</code></a> — the build fails unless \
      the command prints exactly the text above it</dd></dl></div>"
    ``(Verso.Doc.Block.concat #[
        Verso.Doc.Block.code $(quote text),
        Verso.Doc.Block.other (CadenceGuide.Block.status $(quote html)) #[]])

end CadenceGuide
