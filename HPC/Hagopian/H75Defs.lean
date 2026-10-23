import HPC.Jones.Jones49F
import HPC.Effros.Effros
import HPC.Plane.Atriodic51Defs
import HPC.Plane.EndPoints51
import HPC.PseudoArc.Theorem14
import HPC.Moore.M25Plane

/-!
# Batch 155: the definitions of the skeleton `Hagopian75.lean` (§§2–3)

The `Defs` section of the batch-155 skeleton, verbatim, split off so that the supporting files
(`H75Basic`, `H75Kur*`, `H75Triod`, `H75Lemma1`, `H75Thm1*`, …) can use it. The theorem
`admissible_quotient_homeomorph` of that section is in `Hagopian75.lean`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Defs

variable {X : Type*} [MetricSpace X]

/-- A *triod* in an arbitrary metric space: the definition of `HPC.Plane.IsTriod` (Bing 1951 §1)
without the ambient compactness. Hagopian (p. 35): "a continuum `T` … contains a subcontinuum `Z`
such that `T − Z` is the union of three nonempty disjoint open sets". -/
def IsTriodSet (T : Set X) : Prop :=
  Fold.Q78.IsContinuum T ∧ ∃ Z : Set X, Fold.Q78.IsContinuum Z ∧ Z ⊆ T ∧
    ∃ A B C : Set X, A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧ T \ Z = A ∪ B ∪ C ∧
      Disjoint (closure A) B ∧ Disjoint A (closure B) ∧ Disjoint (closure A) C ∧
      Disjoint A (closure C) ∧ Disjoint (closure B) C ∧ Disjoint B (closure C)

/-- The quotient map of an *admissible decomposition* (p. 36), in map form: a continuous map of `E`
onto `[0, 1]` with connected fibres. (Hagopian: "an upper semi-continuous decomposition whose
elements are connected sets and whose quotient space is the unit interval".) -/
def IsAdmissibleMap (E : Set X) (k : E → unitInterval) : Prop :=
  Continuous k ∧ Function.Surjective k ∧ ∀ t, IsConnected (k ⁻¹' {t})

/-- **Type A** (Thomas, via Hagopian p. 36): irreducible between two of its points, with an
admissible decomposition. -/
def IsTypeA (E : Set X) : Prop :=
  (∃ a b, IsIrreducibleBetween E a b) ∧ ∃ k : E → unitInterval, IsAdmissibleMap E k

/-- **Type A′** (p. 36): type A, with an admissible decomposition each of whose elements has void
interior relative to `E`. -/
def IsTypeA' (E : Set X) : Prop :=
  (∃ a b, IsIrreducibleBetween E a b) ∧
    ∃ k : E → unitInterval, IsAdmissibleMap E k ∧ ∀ t, interior (k ⁻¹' {t}) = ∅

/-- The layer `k⁻¹(s)`, as a subset of the ambient space. -/
def layer {E : Set X} (k : E → unitInterval) (s : unitInterval) : Set X :=
  Subtype.val '' (k ⁻¹' {s})

end Defs

end HPC.Hagopian
