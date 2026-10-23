import HPC.Moore.Defs
import HPC.Moore.Basic
import HPC.Moore.Chains
import HPC.Moore.Bridge
import HPC.Moore.Sec4
import HPC.Moore.ArcChar
import HPC.Moore.Thm15
import HPC.Moore.Arcs
import HPC.Moore.Refute

/-!
# Moore, *On the foundations of plane analysis situs* (F.A., 1916), §§2–5 (batch 137)

R. L. Moore, Trans. AMS 17 (1916), 131–164. The batch-137 skeleton (kept verbatim at
`doc/batches/skeletons/MooreFA.lean`) is split as follows; every `sorry` of the skeleton is
discharged, refuted, or reshaped as recorded at the statement and in `REPORT-batch137.md`.

| skeleton | file | declarations |
|---|---|---|
| §1 definitions, Axioms 1–8, 5₁ (item A) | `Defs.lean` | verbatim |
| §2 Theorems 1–9, `M'` closed (item B) | `Basic.lean` | `fa_theorem1` … `fa_theorem9`, `fa_cl_isClosed` |
| §2 Theorem 10 (item B) | `Chains.lean` | `fa_theorem10`, `exists_simpleChain_sublist` |
| §4 the bridge (item D) | `Bridge.lean` | `isTopologicalBasis_region`, `isLimitPt_iff`, `isClosedM_iff`, `isConn_iff`, `heineBorel_iff`, `metrizable`, `cl_eq_closure` |
| §3 Theorems 11–14 (item C) | `Sec4.lean` | `fa_theorem11` … `fa_theorem14`, `not_fa_theorem14_printed` |
| §3 Theorems 15, 16 (item C) | `Thm15.lean` | `fa_theorem15`, `fa_theorem16` (Moore's nested chains: `exists_irreducible`) |
| §5 arc characterization (item E) | `ArcChar.lean` | `isIrreducibleConnected_iff_arc` |
| §5 arcs, pp. 139–140 (item E) | `Arcs.lean` | `isArc_iff`, `fa_sec5_arc_split`, `fa_sec5_interval_unique`, `fa_sec5_first_point`, `fa_sec5_last_point`, `fa_sec5_limitPt_iff`, `not_fa_sec5_limitPt_printed`, `fa_scc_two_arcs` |
| §5 Theorems 17–19 (item E) | `Sec4.lean` | `fa_theorem17`, `fa_theorem18`, `fa_theorem19` |
| printed Theorems 4, 19 | `Refute.lean` | `not_fa_theorem4_printed`, `not_fa_theorem19_printed` |

Each statement carries only the axioms its proof uses (the skeleton's section headings assume
more); the table of axioms used per theorem is in `REPORT-batch137.md`.
-/
