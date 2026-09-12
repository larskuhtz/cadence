/-
Entry point for the guide. `scripts/guide.sh` runs this with `--output`.
-/
import VersoManual
import CadenceGuide

open Verso.Genre.Manual

def main := manualMain (%doc CadenceGuide)
