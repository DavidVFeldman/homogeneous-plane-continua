import HPC.Moore.M25C

/-! `#print axioms` for every theorem declared in the batch-147 files (`HPC/Moore/TSCCCut.lean`,
`HPC/Moore/M25CDefs.lean`, `HPC/Moore/M25CInt.lean`, `HPC/Moore/M25C13.lean`,
`HPC/Moore/M25C15.lean`, `HPC/Moore/M25C19.lean`, `HPC/Moore/M25C20.lean`, `HPC/Moore/M25C6.lean`
and `HPC/Moore/M25C.lean`). Output: `axioms-batch147.txt`. -/

open Lean Elab Command in
elab "#audit_batch147" : command => do
  let env ← getEnv
  let mods := [`HPC.Moore.TSCCCut, `HPC.Moore.M25CDefs, `HPC.Moore.M25CInt, `HPC.Moore.M25C13,
    `HPC.Moore.M25C15, `HPC.Moore.M25C19, `HPC.Moore.M25C20, `HPC.Moore.M25C6, `HPC.Moore.M25C]
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

#audit_batch147
