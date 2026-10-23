import HPC.Moore.M19G

/-! `#print axioms` for every theorem declared in the batch-144 files (`HPC/Moore/M19GSquare.lean`,
`HPC/Moore/M19GPaste.lean`, `HPC/Moore/M19GBoundary.lean`, `HPC/Moore/M19GCuts.lean`,
`HPC/Moore/M19GSplit.lean`, `HPC/Moore/M19GCollar.lean`, `HPC/Moore/M19GPlane.lean`,
`HPC/Moore/M19GCor.lean` and `HPC/Moore/M19G.lean`). Output: `axioms-batch144.txt`. -/

open Lean Elab Command in
elab "#audit_batch144" : command => do
  let env ← getEnv
  let mods := [`HPC.Moore.M19GSquare, `HPC.Moore.M19GPaste, `HPC.Moore.M19GBoundary,
    `HPC.Moore.M19GCuts, `HPC.Moore.M19GSplit, `HPC.Moore.M19GCollar, `HPC.Moore.M19GPlane,
    `HPC.Moore.M19GCor, `HPC.Moore.M19G]
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

#audit_batch144
