import HPC.Moore.M19EF

/-! `#print axioms` for every theorem declared in the batch-143 files (`HPC/Moore/GridSquare.lean`,
`HPC/Moore/GridMesh.lean`, `HPC/Moore/M19F.lean`, `HPC/Moore/M19E*.lean` and `HPC/Moore/M19EF.lean`).
Output: `axioms-batch143.txt`. -/

open Lean Elab Command in
elab "#audit_batch143" : command => do
  let env ← getEnv
  let mods := [`HPC.Moore.GridSquare, `HPC.Moore.GridMesh, `HPC.Moore.M19F,
    `HPC.Moore.M19ESeq, `HPC.Moore.M19ELines, `HPC.Moore.M19EFamily, `HPC.Moore.M19EGrid,
    `HPC.Moore.M19EMesh, `HPC.Moore.M19ESchoenflies, `HPC.Moore.M19EThm, `HPC.Moore.M19EF]
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

#audit_batch143
