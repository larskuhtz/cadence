import Cadence.Monitor.TraceMutate

/-!
Entry point for `lake env lean --run`: runs the `main` of
[TraceMutate.lean](../../Cadence/Monitor/TraceMutate.lean) from its built
olean, so a run elaborates one import instead of the tool's source.
[env.sh](env.sh) builds the module before running it.
-/
