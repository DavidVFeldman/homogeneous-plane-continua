import HPC.Plane.Theorem11

/-!
# Batch 97: degenerate elements of Bing's decomposition (Q-deg)

Skeleton (save as `HPC/Plane/Layers51.lean`; add `import HPC.Plane.Layers51` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded. Target: `exists_degenerate_interior_elt` (`Theorem11.lean`, the last `sorry` of
Theorem 11 apart from Theorem 10); if it closes, replace that `sorry` by a reference (the one
permitted edit to an existing file) and record it.

Hausdorff distance is Mathlib's `Metric.hausdorffDist`; for the nonempty compact sets involved it
is a metric. "Element" means `bingElt`.
-/

namespace HPC.Plane

open Set Topology Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Continuity point of the element map.** `x` is a continuity point when every element near
`x` is Hausdorff-close to `bingElt x`: for every `ε > 0` there is an open `W ∋ x` such that every
`y ∈ W` has `hausdorffDist (bingElt y) (bingElt x) < ε`. (Upper semicontinuity gives one half
automatically; the content is lower semicontinuity.) -/
def IsContPt (x : S) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ W : Set S, IsOpen W ∧ x ∈ W ∧
    ∀ y ∈ W, hausdorffDist (bingElt y) (bingElt x) < ε

/-- Continuity is a property of the element: if `y ∈ bingElt x` then `x` and `y` are continuity
points together. -/
theorem isContPt_congr (hS : BingS S) {x y : S} (hy : y ∈ bingElt x) : IsContPt x ↔ IsContPt y := by
  sorry

/-- **Fort's theorem for the element map** (M. K. Fort, Jr., *Points of continuity of
semi-continuous functions*, Publ. Math. Debrecen 2 (1951), 100–102): the continuity points of an
upper semicontinuous compact-valued map on a Baire space are residual. Here: the set of
non-continuity points is meagre in `S`. -/
theorem isMeagre_not_isContPt (hS : BingS S) : IsMeagre {x : S | ¬ IsContPt x} := by
  sorry

/-- A continuity point outside both end elements exists (Baire: `S` is a complete metric space,
the two end elements are closed with empty interior, so their union is meagre). -/
theorem exists_contPt_not_endElt (hS : BingS S) : ∃ x : S, IsContPt x ∧ ¬ IsEndElt x := by
  sorry

/-- **Q-deg core (open question).** At a continuity point that is not an end element, the element
is degenerate. Prove, or refute by a `BingS` space with a nondegenerate element that is a
Hausdorff limit of the elements on both sides. (Batch 96 derived, at such a point with element
`T`: every subcontinuum meeting `T` lies in `T` or contains `T`.) -/
theorem bingElt_degenerate_of_isContPt (hS : BingS S) {x : S} (hx : IsContPt x)
    (hxe : ¬ IsEndElt x) : bingElt x = {x} := by
  sorry

/-- The batch-96 fact, recorded as a statement: at a continuity point, a subcontinuum meeting the
element lies in it or contains it. -/
theorem subcontinuum_of_isContPt (hS : BingS S) {x : S} (hx : IsContPt x) (hxe : ¬ IsEndElt x)
    {L : Set S} (hL : Fold.Q78.IsContinuum L) (hmeet : (L ∩ bingElt x).Nonempty) :
    L ⊆ bingElt x ∨ bingElt x ⊆ L := by
  sorry

/-- **Q-deg** (`exists_degenerate_interior_elt`): assembly of the above. -/
theorem exists_degenerate_interior_elt' (hS : BingS S) :
    ∃ p : S, bingElt p = {p} ∧ ¬ IsEndElt p := by
  sorry

/-- **Theorem 11, conditional on Theorem 10 only**, once Q-deg closes. -/
theorem theorem11_1951_of_T10'
    (hT10 : ∀ {M : Set S}, Fold.Q78.IsContinuum M → ∀ {m : ℕ} (D : Chain S m), M ⊆ D.union →
      ∀ {p : S}, CondA M p →
      ∃ (n : ℕ) (E : Chain S n) (hn : 0 < n), M ⊆ E.union ∧ E.Refines D ∧
        p ∈ E.link ⟨0, hn⟩ ∧ ∀ j : Fin n, j.val ≠ 0 → p ∉ closure (E.link j))
    (hS : BingS S) : IsSnakeLike (univ : Set S) := by
  sorry

end HPC.Plane
