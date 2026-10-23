import HPC.Plane.Layers51

/-!
# Batch 98: the Cantor organ as a test of Theorem 11

Skeleton (save as `HPC/Plane/Organ98.lean`; add `import HPC.Plane.Organ98` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded. Nothing in an existing file is to be edited.

The Cantor organ `Org.Organ` (batch 97) satisfies `BingS` and has no degenerate element. Bing's
Theorem 11 asserts that every `BingS` space is snake-like. The organ is therefore either a
counterexample to Theorem 11 or a space whose chainability Bing's proof cannot reach.
-/

namespace HPC.Plane

open Set Topology Metric Org

/-! ## §1. Is the organ snake-like? -/

/-- **Decisive question.** Prove or refute. -/
theorem organ_isSnakeLike : IsSnakeLike (univ : Set Organ) := by
  sorry

/-! ## §2. Bing's nondegenerate branch on the organ -/

/-- In the organ, at a good non-dyadic layer `g' = layer (lam goodC)`: the top point of the
strand satisfies condition A for `M = g'` (the layer is an arc; its end points satisfy A). -/
theorem organ_condA_layer :
    CondA (layer (lam goodC)) (pt goodC 1) := by
  sorry

/-- **Bing's claim "`p'` satisfies condition A for `M` equal to either `H` or `K`"**, tested on the
organ at the good layer with `p'` the top point: `H = F⁻¹[0, lam goodC]`, `K = F⁻¹[lam goodC, 1]`.
State for each side whether condition A holds (prove the true ones, refute the false ones). -/
theorem organ_condA_H_or_K :
    CondA (F ⁻¹' Icc 0 (lam goodC)) (pt goodC 1) ∨ CondA (F ⁻¹' Icc (lam goodC) 1) (pt goodC 1) := by
  sorry

/-! ## §3. What gluing along a nondegenerate layer requires -/

/-- **Terminal subcontinuum.** `T ⊆ M` is terminal in `M` when every subcontinuum of `M` meeting
`T` lies in `T` or contains `T`. -/
def IsTerminalIn (M T : Set Organ) : Prop :=
  ∀ L : Set Organ, Fold.Q78.IsContinuum L → L ⊆ M → (L ∩ T).Nonempty → L ⊆ T ∨ T ⊆ L

/-- The good layer is terminal in both sides. -/
theorem organ_layer_terminal :
    IsTerminalIn (F ⁻¹' Icc 0 (lam goodC)) (layer (lam goodC)) ∧
    IsTerminalIn (F ⁻¹' Icc (lam goodC) 1) (layer (lam goodC)) := by
  sorry

/-- **Gluing question (general, in a compact metric space).** If `H`, `K` are snake-like continua
with `H ∩ K = T` terminal in both and `H ∪ K` is a continuum, is `H ∪ K` snake-like? Prove, or
refute (a refutation would have to be a space in which the two chains run through `T` in
incompatible ways). Stated over a general compact metric space `X`. -/
theorem isSnakeLike_union_of_terminal {X : Type*} [MetricSpace X] [CompactSpace X]
    {H K T : Set X} (hH : IsSnakeLike H) (hK : IsSnakeLike K) (hHK : H ∩ K = T)
    (hTH : ∀ L : Set X, Fold.Q78.IsContinuum L → L ⊆ H → (L ∩ T).Nonempty → L ⊆ T ∨ T ⊆ L)
    (hTK : ∀ L : Set X, Fold.Q78.IsContinuum L → L ⊆ K → (L ∩ T).Nonempty → L ⊆ T ∨ T ⊆ L)
    (hT : T.Nonempty) : IsSnakeLike (H ∪ K) := by
  sorry

end HPC.Plane
