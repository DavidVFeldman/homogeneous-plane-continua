import Audit76Long.P13861Data

/-! The extension law at `witness-batch75-span12-k4.txt`, basepoint 343, put to the kernel. The arms here run to
13518 links, past the default thread stack of the kernel's recursion, which is
why this module is in the library `Audit76Long` (built with a larger thread stack) rather than in
`HPC`. -/

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

namespace HPC.Fold.Audit76.P13861

/-- The basepoint 343. -/
def basept_343 : Fin 13861 := ⟨343, by omega⟩

/-- **The extension law at basepoint 343** (band `[0, 12]`, least leg count 4). Source: `witness-batch75-span12-k4.txt`.
The witness: `L' = 0`, `H' = 7`, `w'` from `4` through `[2, 7, 0]`, the appended leg to
`11`. -/
theorem extendsSubBand_343 : ExtendsSubBand rho basept_343 0 12 4 :=
  extendsSubBand_of_witness 0 7 4 11 [2, 7, 0] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end HPC.Fold.Audit76.P13861
