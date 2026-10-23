import HPC.Jones.Jones55T2

/-! `#print axioms` for every theorem declared in the batch-148 files (`HPC/Jones/Jones55T2A.lean`,
`HPC/Jones/Jones55T2D.lean` and `HPC/Jones/Jones55T2.lean`). Output: `axioms-batch148.txt`. -/

open Lean Elab Command in
elab "#audit_batch148" : command => do
  let env ← getEnv
  let mods := [`HPC.Jones.Jones55T2A, `HPC.Jones.Jones55T2D, `HPC.Jones.Jones55T2]
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

#audit_batch148
