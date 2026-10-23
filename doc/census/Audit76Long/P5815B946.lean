import Audit76Long.P5815Data

/-! The extension law at `witness-batch74-span11.txt`, basepoint 946, put to the kernel. The arms here run to
4869 links, past the default thread stack of the kernel's recursion, which is
why this module is in the library `Audit76Long` (built with a larger thread stack) rather than in
`HPC`. -/

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

namespace HPC.Fold.Audit76.P5815

/-- The basepoint 946. -/
def basept_946 : Fin 5815 := ⟨946, by omega⟩

/-- **The extension law at basepoint 946** (band `[0, 11]`, least leg count 5). Source: `witness-batch74-span11.txt`.
The witness: `L' = 0`, `H' = 8`, `w'` from `4` through `[7, 2, 8, 0]`, the appended leg to
`10`. -/
theorem extendsSubBand_946 : ExtendsSubBand rho basept_946 0 11 5 :=
  extendsSubBand_of_witness 0 8 4 10 [7, 2, 8, 0] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end HPC.Fold.Audit76.P5815
