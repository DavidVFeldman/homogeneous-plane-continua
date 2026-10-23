import Audit76Long.P5742bData

/-! The extension law at `witness-batch75-span11-k5.txt`, basepoint 5099, put to the kernel. The arms here run to
5100 links, past the default thread stack of the kernel's recursion, which is
why this module is in the library `Audit76Long` (built with a larger thread stack) rather than in
`HPC`. -/

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

namespace HPC.Fold.Audit76.P5742b

/-- The basepoint 5099. -/
def basept_5099 : Fin 5742 := ⟨5099, by omega⟩

/-- **The extension law at basepoint 5099** (band `[0, 11]`, least leg count 5). Source: `witness-batch75-span11-k5.txt`.
The witness: `L' = 2`, `H' = 10`, `w'` from `6` through `[4, 9, 2, 10]`, the appended leg to
`1`. -/
theorem extendsSubBand_5099 : ExtendsSubBand rho basept_5099 0 11 5 :=
  extendsSubBand_of_witness 2 10 6 1 [4, 9, 2, 10] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end HPC.Fold.Audit76.P5742b
