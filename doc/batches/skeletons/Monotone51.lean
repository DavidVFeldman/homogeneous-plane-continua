import HPC.Plane.PseudoArc51

/-!
# Bing, *Concerning hereditarily indecomposable continua*, §4: monotone decompositions

Skeleton for batch 89 (save as `HPC/Plane/Monotone51.lean`; add `import HPC.Plane.Monotone51` to
the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted
with the change recorded; `theorem3_HIC` and `theorem4_HIC` keep their conclusions.

A monotone decomposition of `M` is given by a continuous surjection with connected fibres
(COMMISSION-batch89.md §3.1). `IsSnakeLike`, `IsHereditarilyIndecomposable`, `IsPseudoArc` are
from `Snake51.lean`, `EndPoints51.lean`, `PseudoArc51.lean`.
-/

namespace HPC.Plane

open Set

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `f` is a **monotone map** of `M` onto `M'`: continuous on `M`, with image `M'`, and with every
fibre `M ∩ f ⁻¹' {y}` (for `y ∈ M'`) connected. Bing's "upper semi-continuous collection of
continua filling `M`" is the collection of fibres. -/
def IsMonotoneMap (f : X → Y) (M : Set X) (M' : Set Y) : Prop :=
  ContinuousOn f M ∧ f '' M = M' ∧ ∀ y ∈ M', IsConnected (M ∩ f ⁻¹' {y})

/-- **Bing 1951 (Pacific J. Math.), Theorem 3.** The monotone image of a chainable (compact)
continuum is chainable. (Bing's chain of `D(n_{3k+1}, n_{3k+5})`'s; COMMISSION-batch89.md §3.4 asks
whether consecutive links meet as he has them.) -/
theorem theorem3_HIC {f : X → Y} {M : Set X} {M' : Set Y} (hM : IsSnakeLike M)
    (hf : IsMonotoneMap f M M') : IsSnakeLike M' := by
  sorry

/-- The monotone image of a hereditarily indecomposable continuum is hereditarily
indecomposable. -/
theorem isHereditarilyIndecomposable_image {f : X → Y} {M : Set X} {M' : Set Y}
    (hM : Fold.Q78.IsContinuum M) (hHI : IsHereditarilyIndecomposable M)
    (hf : IsMonotoneMap f M M') : IsHereditarilyIndecomposable M' := by
  sorry

/-- The monotone image of a chainable continuum is a (compact) continuum and chainable; recorded
separately from `theorem3_HIC` only to name the continuum part. -/
theorem isContinuum_image {f : X → Y} {M : Set X} {M' : Set Y} (hM : Fold.Q78.IsContinuum M)
    (hf : IsMonotoneMap f M M') : Fold.Q78.IsContinuum M' := by
  sorry

/-- **Bing 1951 (Pacific J. Math.), Theorem 4.** If `M` is a pseudo-arc and every fibre of the
monotone map `f` is a proper subcontinuum of `M`, the image `M'` is a pseudo-arc, hence
homeomorphic to `M`. -/
theorem theorem4_HIC {f : X → Y} {M : Set X} {M' : Set Y} (hM : IsPseudoArc M)
    (hf : IsMonotoneMap f M M') (hproper : ∀ y ∈ M', M ∩ f ⁻¹' {y} ≠ M) :
    IsPseudoArc M' ∧ Nonempty (M ≃ₜ M') := by
  sorry

end HPC.Plane
