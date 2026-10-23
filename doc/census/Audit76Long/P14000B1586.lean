import Audit76Long.P14000Data

/-! The extension law at `witness-batch75-span12-k6.txt`, basepoint 1586, put to the kernel. The arms here run to
12414 links, past the default thread stack of the kernel's recursion, which is
why this module is in the library `Audit76Long` (built with a larger thread stack) rather than in
`HPC`. -/

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

namespace HPC.Fold.Audit76.P14000

/-- The basepoint 1586. -/
def basept_1586 : Fin 14000 := ⟨1586, by omega⟩

/-- **The extension law at basepoint 1586** (band `[0, 12]`, least leg count 6). Source: `witness-batch75-span12-k6.txt`.
The witness: `L' = 2`, `H' = 11`, `w'` from `6` through `[9, 4, 10, 2, 11]`, the appended leg to
`1`. -/
theorem extendsSubBand_1586 : ExtendsSubBand rho basept_1586 0 12 6 :=
  extendsSubBand_of_witness 2 11 6 1 [9, 4, 10, 2, 11] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end HPC.Fold.Audit76.P14000
