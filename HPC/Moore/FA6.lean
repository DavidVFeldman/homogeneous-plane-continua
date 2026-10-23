import HPC.Moore.Sec6Defs
import HPC.Moore.Sec6A
import HPC.Moore.Sec6B
import HPC.Moore.Sec6Th28
import HPC.Moore.Sec6Th29
import HPC.Moore.Sec6Th31
import HPC.Moore.Sec6Lim
import HPC.Moore.Sec6Th32
import HPC.Moore.Sec6Th33

/-!
# Moore, *On the foundations of plane analysis situs* (F.A., 1916), §6 (batch 138)

R. L. Moore, Trans. AMS 17 (1916), 131–164, pp. 140–150: Theorems 20–34. The batch-138 skeleton
(kept verbatim at `doc/batches/skeletons/MooreFA6.lean`) is split as follows; every `sorry` of the
skeleton is discharged or refuted, with each change of shape recorded at the statement and in
`doc/batches/REPORT-batch138.md`.

| skeleton | file | declarations |
|---|---|---|
| §1 definitions (item A) | `Sec6Defs.lean` | `openArc`, `IsInteriorOf`, `SeparatesOn`, `InOrder` (verbatim) |
| arcs and closed curves, topologically | `Sec6Arc.lean`, `Sec6Plane.lean` | `Gen.TArc`, `Gen.TSCC`, first points, gluing, `Gen.exists_access`, `Gen.exists_cross` |
| the bridge; Theorems 20–23; interior of `J` | `Sec6A.lean` | `fa_theorem20` … `fa_theorem23`, `not_fa_theorem23_printed`, `existsUnique_interior` |
| Theorems 24–27 | `Sec6Th24.lean` … `Sec6Th27.lean`, `Sec6B.lean` | `fa_theorem24` … `fa_theorem27` |
| Theorem 28 | `Sec6Th28.lean` | `fa_theorem28` |
| Theorems 29, 30 | `Sec6Th29.lean` | `fa_theorem29`, `fa_theorem30` |
| Theorem 31 | `Sec6Th31.lean` | `fa_theorem31`, `th31_pocket` |
| limit arcs | `Sec6Lim.lean` | `Gen.tarc_of_seq`, `Gen.exists_tarc_of_seq` |
| Theorem 32 | `Sec6Th32.lean` | `fa_theorem32` (via `sides`, `side_propagate`, `accessible`) |
| Theorems 33, 34 | `Sec6Th33.lean` | `fa_theorem33`, `fa_theorem34`, `fa_theorem34_region` |

Each statement carries only the axioms its proof uses (the skeleton's section assumes Axioms
1–8); the axioms used by each theorem are listed in its docstring and in the report.
-/
