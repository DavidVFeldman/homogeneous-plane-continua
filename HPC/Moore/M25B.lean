import HPC.Moore.M25B11
import HPC.Moore.M25BRefute
import HPC.Moore.Mullikin4

/-!
# Batch 146: Moore 1925 §I, part 2 (Theorems 5–12; Mullikin 1922 Theorem 5)

Delivery of the skeleton `doc/batches/skeletons/Moore1925II.lean` (commission
`doc/batches/COMMISSION-batch146.md`, report `doc/batches/REPORT-batch146.md`). The skeleton is split:

* `CutArc.lean`: cut-point arcs and the circle characterization (Moore 1920 Theorem 4), for compact
  metrizable spaces;
* `M25BDefs.lean`: the skeleton's definitions, verbatim;
* `M25B5.lean`: `not_separatesPlane_ptsOf`, Theorems 5–8;
* `M25B9.lean`: Theorems 9, 10, 12;
* `Borsuk.lean`: Borsuk's theorem for the plane (direction used);
* `Mullikin.lean`: Mullikin's Theorem 5, corrected;
* `Mullikin4.lean`: Mullikin's Theorem 4 at `M₁ ∩ M₂ = ∅`, against her convention for "connected";
* `M25B11.lean`: Theorem 11;
* `M25BPts.lean`, `M25BRefute.lean`: the decomposition into points, and the refutations of the
  printed Theorems 2, 7, 10, 11 and of Mullikin's printed Theorem 5.
-/
