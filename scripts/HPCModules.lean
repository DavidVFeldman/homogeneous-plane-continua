import HPC

/-!
The modules of the environment that imports `HPC`, one per line (batch 204, commission
section 1, check 2 of `scripts/split.py`). Run from the repository root:
  lake env lean scripts/HPCModules.lean > /tmp/hpc-env-modules.txt
  python3 scripts/split.py --no-write --env /tmp/hpc-env-modules.txt
-/

open Lean in
#eval show CoreM Unit from do
  for m in (← getEnv).header.moduleNames do
    IO.println m
