import HPC.HO16.StairDefs
import HPC.HO16.PLLib2
import HPC.HO16.SidesLib
import HPC.HO16.Sides
import HPC.HO16.StairLib
import HPC.HO16.Stairwell
import HPC.HO16.Lemma18
import HPC.HO16.StairExample

/-!
# Batch 195: Hoehn–Oversteegen Theorem 1, III — sides, straight sets, stairwells

The batch-195 skeleton (`doc/batches/skeletons/HO16C.lean`), split under `HPC/HO16/`:

* `StairDefs`: the definitions of commission §§3–6 (`HasConsCompl`, `sideOf`, `IsOrdinaryPt`,
  `IsGeneric`, `IsStraight`, `endSet`, `IsStairwellStr`, `HasStairwell`,
  `IsBrokenStairwellStr`, `HasBrokenStairwell`, `phiStar`, `foldPre`);
* `PLLib2` (§2): components of `G \ (K ∪ P)`, ordinary points, intersections;
* `SidesLib`, `Sides` (§3): the observations after Definition 9, Propositions 10 and 11;
* `StairLib`, `Stairwell` (§§4–6, §8): Definition 12's observation, the remarks on stairwells,
  Claim 14.1, Proposition 17, the fold of Proposition 19;
* `Lemma18` (§7): Lemma 18;
* `StairExample` (§5, §9): the certificate for p. 193 and a stairwell structure of height 3.

Source: Hoehn–Oversteegen 2016 (`doc/sources/hoehn-oversteegen2016.pdf`). Route: commission 195.
-/
