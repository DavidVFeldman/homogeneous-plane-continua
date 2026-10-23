import HPC.Jones.Defs
import HPC.Jones.Basic
import HPC.Jones.Theorem6
import HPC.Jones.Theorem13Aux
import HPC.Jones.Theorem13
import HPC.Jones.CutPoints
import HPC.Jones.Jones51

/-!
# Batch 135: Jones 1948 (non-aposyndetic continua), complete; Jones 1951, the Lemma

Umbrella module for `HPC/Jones/`. Sources: F. B. Jones, *Concerning non-aposyndetic continua*,
Amer. J. Math. 70 (1948), 403–413; F. B. Jones, *Certain homogeneous unicoherent indecomposable
continua*, Proc. AMS 2 (1951), 855–859 (`doc/sources/`).

Convention: Jones's `M` is the whole space `X`, a compact connected metric space.

* `Defs`: the definitions of §1 (`AposAt`, …, `IsDecomposableSpace`) and general lemmas.
* `Basic`: equivalences with the repository (`isDecomposableSpace_iff_not_isIndecomposable`,
  `composant_eq_composant_univ`); Theorems 0–5, 7–10; Theorem 10 as printed is false
  (`theorem10_printed_iff`, `not_theorem10_printed_unitInterval`).
* `Theorem6`: Theorem 6, and Theorem 6 as printed is false (`not_theorem6_printed`).
* `Theorem13Aux`, `Theorem13`: Theorem 13.
* `CutPoints`: Theorems 11, 12, 14–19 and the three Corollaries.
* `Jones51`: `aposSet`, `isOpen_aposSet`, `IsHomogeneous`, `jones51_lemma`.

Jones 1951, Theorem 1, left open in batch 135, is proved in batch 136 (`jones51_theorem1`,
`HPC/Jones/Jones51Thm1.lean`, imported through `HPC/Jones/Jones55.lean`).
-/
