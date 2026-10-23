import HPC.Moore.M19CD2

/-! `#print axioms` for every theorem declared in the batch-142 files (`HPC/Moore/M19D*.lean`
except `M19D.lean`, and `HPC/Moore/M19CD2.lean`). Output: `axioms-batch142.txt`. -/

open Lean Elab Command in
elab "#audit_batch142" : command => do
  let env ← getEnv
  let mods := [`HPC.Moore.M19DGlue, `HPC.Moore.M19DDefs, `HPC.Moore.M19DPocket,
    `HPC.Moore.M19DOuter, `HPC.Moore.M19DWeight, `HPC.Moore.M19DCorner, `HPC.Moore.M19DChords,
    `HPC.Moore.M19DInside, `HPC.Moore.M19DExtract, `HPC.Moore.M19DLens, `HPC.Moore.M19DNice,
    `HPC.Moore.M19DThm, `HPC.Moore.M19CD2]
  for m in mods do
    let some idx := env.getModuleIdx? m | logInfo m!"missing module {m}"
    let mut names : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx then
        if let .thmInfo _ := ci then
          if !n.isInternal then names := names.push n
    names := names.qsort (fun a b => a.toString < b.toString)
    logInfo m!"-- {m}: {names.size} theorems"
    for n in names do
      let axs ← liftCoreM <| collectAxioms n
      logInfo m!"{n}: {axs.toList}"

#audit_batch142
