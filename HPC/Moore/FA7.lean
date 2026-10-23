import HPC.Moore.Sec7A
import HPC.Moore.Sec7B
import HPC.Moore.Sec7Chord
import HPC.Moore.Sec7Th37
import HPC.Moore.Sec7Th38
import HPC.Moore.Sec7Th42
import HPC.Moore.Sec7Th41

/-!
# Moore, *On the foundations of plane analysis situs* (F.A., 1916), §7 (batch 139)

R. L. Moore, Trans. AMS 17 (1916), 131–164, pp. 150–157: Theorems 35–43. The batch-139 skeleton
(kept verbatim at `doc/batches/skeletons/MooreFA7.lean`) is split as follows. Each change of shape
is recorded at the statement and in `doc/batches/REPORT-batch139.md`.

| skeleton item | file | declarations | outcome |
|---|---|---|---|
| Jordan structure of `J`, `I`, `S − I'` | `Sec7A.lean` | `jordan`, `component_eq`, `access` | proved |
| `fa_theorem35` | `Sec7A.lean` | `fa_theorem35`, `not_fa_theorem35_printed` | proved (`R ≠ ∅`); printed form refuted |
| `fa_theorem36` | `Sec7B.lean` | `fa_theorem36` | proved (one step of Moore's proof corrected) |
| `fa_theorem36_interior_subset` | `Sec7B.lean` | `fa_theorem36_interior_subset` | proved |
| `fa_arcs_of_scc_meet` | `Sec7A.lean` | `fa_arcs_of_scc_meet` | proved |
| chords (for 37, 38) | `Sec7Chord.lean` | `param_chords_finite`, `exists_maximal_chord` | proved |
| `fa_theorem37` | `Sec7Th37.lean` | `fa_theorem37` | proved |
| `fa_theorem38` (`True` placeholder) | `Sec7Th38.lean` | `fa_theorem38` | shape chosen, proved |
| `fa_theorem39` | `Sec7A.lean` | `fa_theorem39` | proved (Moore's argument replaced) |
| `fa_theorem40` | `Sec7A.lean` | `fa_theorem40`, `exists_arc_through` | proved |
| `fa_theorem41` | `Sec7Th41.lean` | `fa_theorem41_caseI_nested`, `fa_theorem41_caseI`, `fa_theorem41_of_subset` | Case I and the first sub-case of Case II proved; Case II closed in batch 140 (`M41.lean`: `fa_theorem41_caseII`, `fa_theorem41`) — **closed** |
| `fa_theorem42` | `Sec7Th42.lean` | `fa_theorem42_of_41` | proved from Theorem 41; unconditional form closed in batch 140 (`M41.lean`: `fa_theorem42`) — **closed** |
| `fa_theorem43` | `Sec7Th42.lean` | `not_fa_theorem43_printed` | printed form refuted (`G = ∅`); corrected form (`G` nonempty) closed in batch 140 (`M43.lean`: `fa_theorem43`) — **closed** |

Theorems 41–43 were left open in batch 139 and closed in batch 140 (`M41.lean`, `M43.lean`); this
table was updated in batch 141. Nothing in it is open.

Each statement carries only the axioms its proof uses (the skeleton's section assumes Axioms 1–8).
-/
