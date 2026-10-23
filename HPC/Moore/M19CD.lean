import HPC.Moore.M19CDMain
import HPC.Moore.M19CRefute
import HPC.Moore.M19CDRegion

/-!
# Batch 141: Moore 1919, double rulings; Theorems C and D (pp. 172–176)

R. L. Moore, *Concerning a set of postulates for plane analysis situs*, Trans. AMS 20 (1919),
169–178 (`doc/sources/moore1919.pdf`), pp. 172–176.

The batch-141 skeleton (kept verbatim at `doc/batches/skeletons/Moore1919CD.lean`) is split as
follows. Each change of shape is recorded at the statement and in `doc/batches/REPORT-batch141.md`.

| skeleton item | file | declarations | outcome |
|---|---|---|---|
| `Space.Quad`, `Space.DoubleRuling`, `carrier`, `cells` | `M19CDDefs.lean` | the same | verbatim |
| `doubleRuling_cell`, `doubleRuling_cells_ncard` | `M19CDTile.lean`, `M19CDCells.lean` | the same (`Space.DoubleRuling.tiling`) | proved |
| `m19_theoremC` | `M19CRefute.lean` | `no_ruling_of_two_branches`, `tangent_configuration`, `not_m19_theoremC_printed` | refuted as printed |
| `m19_theoremD` | `M19DThm.lean` (batch 142) | `m19_theoremD` | proved in batch 142 (`M19CD2.lean`) |
| `doubleRuling_refine` (shape free) | `M19CDSplit`, `M19CDRuling`, `M19CDCut`, `M19CDGlue`, `M19CDExt`, `M19CDRefine`, `M19CDOrder`, `M19CDMain.lean` | `Space.ArcRuling.extendY`, `Space.ArcRuling.refine`, `Space.ArcRuling.toDoubleRuling`, `doubleRuling_refine` | proved |
| item A, padding | `M19CDMain.lean` | `doubleRuling_pad` | proved |
| check 5, region form of Theorem D | `M19CDRegion.lean` | `m19_theoremD_regions_of_curves` | proved (relative to the curve form) |

Each statement carries only the axioms its proof uses (the skeleton's section assumes Axioms 1–8).

**Theorem D** was left open in this batch. It is proved in batch 142 (`m19_theoremD`,
`HPC/Moore/M19DThm.lean`, collected in `HPC/Moore/M19CD2.lean`), through a corrected Theorem C for
curves touching `ABCDA` from within nowhere; the commented-out statement formerly kept here is
removed.

This file only collects the imports; it contains no declarations.
-/
