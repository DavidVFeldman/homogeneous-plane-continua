import Audit76Long.P13861Data

/-! The extension law at `witness-batch74-span12.txt`, basepoint 2027, put to the kernel. The arms here run to
11834 links, past the default thread stack of the kernel's recursion, which is
why this module is in the library `Audit76Long` (built with a larger thread stack) rather than in
`HPC`. -/

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

namespace HPC.Fold.Audit76.P13861

/-- The basepoint 2027. -/
def basept_2027 : Fin 13861 := ⟨2027, by omega⟩

/-- **The extension law at basepoint 2027** (band `[0, 12]`, least leg count 5). Source: `witness-batch74-span12.txt`.
The witness: `L' = 0`, `H' = 9`, `w'` from `4` through `[7, 2, 9, 0]`, the appended leg to
`11`. -/
theorem extendsSubBand_2027 : ExtendsSubBand rho basept_2027 0 12 5 :=
  extendsSubBand_of_witness 0 9 4 11 [7, 2, 9, 0] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end HPC.Fold.Audit76.P13861
