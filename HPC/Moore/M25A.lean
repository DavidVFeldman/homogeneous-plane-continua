import HPC.Moore.M25Defs
import HPC.Moore.M25Plane
import HPC.Moore.M25Quot
import HPC.Moore.M25Thm
import HPC.Moore.M25Thm2
import HPC.Moore.M25Ax
import HPC.Moore.M25FA

/-!
# Batch 145: Moore 1925 §I, Theorems 1–4 and the p. 420 claim

The batch 145 skeleton (`doc/batches/skeletons/Moore1925I.lean`), split under `HPC/Moore/`:

* `M25Defs`: the skeleton's definitions, verbatim (`elt`, `ptsOf`, `MooreDecomp`, `IsLimitElt`,
  `mooreRegion`, `spaceOfElts`).
* `M25Plane`: the plane facts `brouwer_boundary` and `janiszewski_compact` (item C).
* `M25Quot`: the quotient (item A) and Theorem 1 (item B).
* `M25Thm`: Theorems 3 and 4, `spaceOfElts_topology`, `m25_unbounded_unique` (items E, F).
* `M25Thm2`: Theorem 2 (item D).
* `M25Ax`, `M25FA`: the p. 420 claim `m25_axioms1245` and the corollary `m25_FA_1_15` (item G).
-/
