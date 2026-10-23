import HPC.Jones.Jones49B

/-! `#print axioms` for every theorem declared in the batch-150 files (`HPC/Jones/Jones49Chain.lean`,
`HPC/Jones/Jones49Sep.lean`, `HPC/Jones/Jones49B.lean`, `HPC/Jones/Moore22.lean` and
`HPC/Jones/Moore22T4.lean`). Output: `axioms-batch150.txt`. -/

open Lean Elab Command in
elab "#audit_batch150" : command => do
  let env ← getEnv
  let mods := [`HPC.Jones.Jones49Chain, `HPC.Jones.Jones49Sep, `HPC.Jones.Jones49B,
    `HPC.Jones.Moore22, `HPC.Jones.Moore22T4]
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

#audit_batch150
