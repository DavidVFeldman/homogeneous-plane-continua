import HPC
import HPC.Archive.Most51Geom
open Lean Elab Command

def touchedModules : List Name :=
  [`HPC.Plane.BandN, `HPC.Plane.Most51, `HPC.Archive.Most51Geom,
   `HPC.PseudoArc.Theorem14, `HPC.PseudoArc.Recon86]

run_cmd do
  let env ← getEnv
  for m in touchedModules do
    let some idx := env.getModuleIdx? m | logInfo m!"missing module {m}"
    let mut names : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx && !n.isInternalDetail then
        match ci with
        | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => names := names.push n
        | _ => pure ()
    let sorted := names.qsort (fun a b => a.toString < b.toString)
    IO.println s!"-- module {m}: {sorted.size} declarations"
    for n in sorted do
      let axs ← liftCoreM (Lean.collectAxioms n)
      let axs := axs.qsort (fun a b => a.toString < b.toString)
      IO.println s!"'{n}' depends on axioms: {axs.toList}"
