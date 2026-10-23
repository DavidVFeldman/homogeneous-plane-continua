import HPC.Moore.M19A
import HPC.Moore.M19Bstep
import HPC.Moore.M19B
import HPC.Moore.M19D
import HPC.Moore.M41
import HPC.Moore.M43

/-!
# Batch 140: F.A. Theorems 41–43 completed; Moore 1919, Theorems A and B

R. L. Moore, *On the foundations of plane analysis situs*, Trans. AMS 17 (1916), 131–164
(`doc/sources/moore1916.pdf`), pp. 155–156; and R. L. Moore, *Concerning a set of postulates for
plane analysis situs*, Trans. AMS 20 (1919), 169–178 (`doc/sources/moore1919.pdf`), pp. 170–174.

The batch-140 skeleton (kept verbatim at `doc/batches/skeletons/Moore1919AB.lean`) is split as
follows. Each change of shape is recorded at the statement and in `doc/batches/REPORT-batch140.md`.

| skeleton item | file | declarations | outcome |
|---|---|---|---|
| `Space.IsSegmentOf`, `Space.ShareSegment` | `M19Defs.lean` | the same | verbatim |
| `fa_theorem41` | `M41Replace`, `M41Geom`, `M41Side`, `M41Half`, `M41.lean` | `fa_theorem41_caseII`, `fa_theorem41` | proved |
| `fa_theorem42` | `M41.lean` | `fa_theorem42` | proved |
| `fa_theorem43` (corrected, `G` nonempty) | `M43Pocket`, `M43Dual`, `M43Comp`, `M43.lean` | `dual_step`, `iterate_inner`, `fa_theorem43` | proved |
| `m19_theoremA` | `M19A.lean` | `Gen.crossing`, `m19_theoremA` | proved (injectivity hypothesis dropped) |
| `m19_B_step` | `M19Bstep.lean` | `m19_B_step` | proved (without Theorem 43) |
| footnote * of p. 174 (commission item B) | `M19D.lean` | `hair_isPreconnected`, `m19_D_arc` | proved (shape chosen) |
| `m19_theoremB` | `M19B.lean` | `m19_theoremB` | proved |

Each statement carries only the axioms its proof uses (the skeleton's section assumes Axioms 1–8).
This file only collects the imports; it contains no declarations.
-/
