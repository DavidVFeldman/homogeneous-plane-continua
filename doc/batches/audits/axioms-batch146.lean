import HPC.Moore.M25B

/-! `#print axioms` for every theorem declared in the batch-146 files (`HPC/Moore/CutArc.lean`,
`HPC/Moore/Borsuk.lean`, `HPC/Moore/Mullikin.lean`, `HPC/Moore/Mullikin4.lean`,
`HPC/Moore/M25BDefs.lean`, `HPC/Moore/M25B5.lean`, `HPC/Moore/M25B9.lean`, `HPC/Moore/M25B11.lean`,
`HPC/Moore/M25BPts.lean`, `HPC/Moore/M25BRefute.lean` and `HPC/Moore/M25B.lean`). Output:
`axioms-batch146.txt`. -/

open Lean Elab Command in
elab "#audit_batch146" : command => do
  let env ← getEnv
  let mods := [`HPC.Moore.CutArc, `HPC.Moore.Borsuk, `HPC.Moore.Mullikin, `HPC.Moore.Mullikin4,
    `HPC.Moore.M25BDefs, `HPC.Moore.M25B5, `HPC.Moore.M25B9, `HPC.Moore.M25B11, `HPC.Moore.M25BPts,
    `HPC.Moore.M25BRefute, `HPC.Moore.M25B]
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

#audit_batch146
