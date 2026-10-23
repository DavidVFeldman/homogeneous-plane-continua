import HPC.Jones.Jones49A

/-! `#print axioms` for every theorem declared in the batch-149 files (`HPC/Jones/Jones49Order.lean`,
`HPC/Jones/Jones49Circle.lean`, `HPC/Jones/Jones49Menger.lean`, `HPC/Jones/Jones49Why.lean` and
`HPC/Jones/Jones49A.lean`). Output: `axioms-batch149.txt`. -/

open Lean Elab Command in
elab "#audit_batch149" : command => do
  let env ← getEnv
  let mods := [`HPC.Jones.Jones49Order, `HPC.Jones.Jones49Circle, `HPC.Jones.Jones49Menger,
    `HPC.Jones.Jones49Why, `HPC.Jones.Jones49A]
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

#audit_batch149
