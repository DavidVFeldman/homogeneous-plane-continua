import HPC.Moore.M25A

/-! `#print axioms` for every theorem declared in the batch-145 files (`HPC/Moore/M25Defs.lean`,
`HPC/Moore/M25Plane.lean`, `HPC/Moore/M25Quot.lean`, `HPC/Moore/M25Thm.lean`,
`HPC/Moore/M25Thm2.lean`, `HPC/Moore/M25Ax.lean`, `HPC/Moore/M25FA.lean` and
`HPC/Moore/M25A.lean`). Output: `axioms-batch145.txt`. -/

open Lean Elab Command in
elab "#audit_batch145" : command => do
  let env ← getEnv
  let mods := [`HPC.Moore.M25Defs, `HPC.Moore.M25Plane, `HPC.Moore.M25Quot, `HPC.Moore.M25Thm,
    `HPC.Moore.M25Thm2, `HPC.Moore.M25Ax, `HPC.Moore.M25FA, `HPC.Moore.M25A]
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

#audit_batch145
