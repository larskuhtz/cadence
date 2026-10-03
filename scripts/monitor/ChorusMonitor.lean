import Cadence.Monitor.ChorusMonitor

/-!
Entry point for `lake env lean --run`: runs the `main` of
[ChorusMonitor.lean](../../Cadence/Monitor/ChorusMonitor.lean) from its built
olean, so a run elaborates one import instead of the monitor's source.
[env.sh](env.sh) builds the module before running it.
-/
