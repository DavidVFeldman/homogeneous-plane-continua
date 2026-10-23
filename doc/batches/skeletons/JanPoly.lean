import HPC.Plane.Cyc2

/-!
# Batch 129: polygonal Janiszewski, part III — polygonal sets, the field change, the two uses

Skeleton for the NEW material. Save as `HPC/Plane/JanPoly.lean`, add `import HPC.Plane.JanPoly`
at the end of the root `HPC.lean`. The edits to existing files (the field of `PlaneFacts`; the
re-proofs of `crosscut'` and `exists_theta_point`; the re-basing of Theorem 6 on Theorem 7) are
described in COMMISSION-batch129.md §2 and are NOT in this file. Every `sorry` is a work item;
shapes may be adjusted with the change recorded.
-/

namespace HPC.Plane

open Set Metric

/-! ### Polygonal sets -/

/-- A **polygonal set**: a finite union of closed segments, degenerate segments (points) allowed.
Compact; closed under finite unions; every simple closed polygon and every `graphSet` is one. -/
def IsPolygonal (A : Set Pt) : Prop := ∃ S : Finset Seg, A = graphSet S

theorem IsPolygonal.isCompact {A : Set Pt} (h : IsPolygonal A) : IsCompact A := by
  sorry

theorem IsPolygonal.union {A B : Set Pt} (hA : IsPolygonal A) (hB : IsPolygonal B) :
    IsPolygonal (A ∪ B) := by
  sorry

theorem isPolygonal_empty : IsPolygonal (∅ : Set Pt) := by
  sorry

theorem isPolygonal_segment (a b : Pt) : IsPolygonal (segment ℝ a b) := by
  sorry

theorem isPolygonal_singleton (a : Pt) : IsPolygonal ({a} : Set Pt) := by
  sorry

theorem IsSimpleClosedPolygon.isPolygonal {J : Set Pt} (hJ : IsSimpleClosedPolygon J) :
    IsPolygonal J := by
  sorry

/-- A finite union of polygonal sets is polygonal. -/
theorem isPolygonal_biUnion {ι : Type*} (s : Finset ι) {A : ι → Set Pt}
    (h : ∀ i ∈ s, IsPolygonal (A i)) : IsPolygonal (⋃ i ∈ s, A i) := by
  sorry

/-! ### Isolated points do not separate -/

/-- An open connected subset of the plane minus a point is connected (the plane has rank `2`;
Mathlib: `Set.Countable.isConnected_compl_of_one_lt_rank` for the whole space, and for an open
connected set either a local path-connectedness argument or the corresponding Mathlib lemma if one
exists — search for `isPreconnected_compl_singleton`, `IsOpen.isConnected_diff_countable`,
`Convex.isPathConnected` and relatives). -/
theorem isConnected_diff_singleton_of_isOpen {U : Set Pt} (hU : IsOpen U) (hc : IsConnected U)
    (q : Pt) : IsConnected (U \ {q}) := by
  sorry

/-- Adding a point to a closed set does not change which pairs of other points it separates. -/
theorem separatesPts_insert_iff {A : Set Pt} (hA : IsClosed A) {q x y : Pt} (hqx : q ≠ x)
    (hqy : q ≠ y) : SeparatesPts (insert q A) x y ↔ SeparatesPts A x y := by
  sorry

/-- **Janiszewski for polygonal sets** (degenerate segments allowed), from `janiszewskiPoly_holds`:
drop the degenerate segments whose point lies on a nondegenerate one, and add the genuinely
isolated points back one at a time with `separatesPts_insert_iff` (an isolated point of `A` not in
`B` changes neither `A ∩ B`'s connectedness — check: `A ∩ B` may gain the point if it is in `B`; then
it is an isolated point of `A ∩ B`, which is then not connected unless it is the single point —
handle: if `A ∩ B` is a single point the hypothesis is `IsConnected {q}`, and the nondegenerate
parts of `A`, `B` have empty intersection or meet exactly in `{q}`… state and prove the reduction
you find cleanest; the statement below is the target). -/
theorem janiszewski_polygonal {A B : Set Pt} (hA : IsPolygonal A) (hB : IsPolygonal B)
    (hAB : IsConnected (A ∩ B) ∨ A ∩ B = ∅) {x y : Pt} (hx : ¬ SeparatesPts A x y)
    (hy : ¬ SeparatesPts B x y) : ¬ SeparatesPts (A ∪ B) x y := by
  sorry

/-! ### Polygonality of the sets of `exists_theta_point` -/

/-- At a non-vertex point `p` of an edge of a simple closed polygon `Γ`, the interior
`polyInterior Γ` meets a small ball in exactly one of the two half-disks (`ball_diff_chord`,
`parity_flip_edge`, `jct_polygon`'s identification of `polyInterior Γ` with the odd parity set). -/
theorem polyInterior_local_halfDisk {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n)
    {p : Pt} (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) :
    ∃ ρ > 0, ∃ s : Bool, ∀ ρ', 0 < ρ' → ρ' ≤ ρ →
      ball p ρ' ∩ polyInterior (polygonOf v) =
        halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ' s := by
  sorry

/-- A segment `e` and a simple closed polygon `Γ₂` meet in a finite union of segments and points
(pairwise intersections of segments are segments or points or empty). -/
theorem isPolygonal_segment_inter_polygon {a b : Pt} {Γ₂ : Set Pt} (hΓ₂ : IsSimpleClosedPolygon Γ₂) :
    IsPolygonal (segment ℝ a b ∩ Γ₂) := by
  sorry

/-- `e ∖ Γ₂` is a finite union of open subsegments, each inside `polyInterior Γ₂` or inside its
exterior; so `e ∩ polyInterior Γ₂` is a finite union of open subsegments. -/
theorem exists_open_pieces {a b : Pt} {Γ₂ : Set Pt} (hΓ₂ : IsSimpleClosedPolygon Γ₂) :
    ∃ P : Finset (Pt × Pt), (∀ q ∈ P, q.1 ∈ segment ℝ a b ∧ q.2 ∈ segment ℝ a b) ∧
      segment ℝ a b ∩ polyInterior Γ₂ = ⋃ q ∈ P, openSegment ℝ q.1 q.2 := by
  sorry

/-- **The key polygonality lemma.** For simple closed polygons `Γ₁`, `Γ₂` with interiors `h₁`, `h₂`,
the set `Γ₁ ∩ closure (h₁ ∩ h₂)` is polygonal. Per edge `e` of `Γ₁`:
* the open pieces of `e ∩ h₂` lie in `closure (h₁ ∩ h₂)` (a point of `Γ₁` is in `closure h₁`, and
  `h₂` is an open neighbourhood of it), so their closures do;
* on `e ∩ Γ₂`, a finite union of segments and points: at an interior point `p` of such a segment
  `τ` that is a vertex of neither polygon, `h₁` and `h₂` are half-disks of `ball p ρ` on sides of
  the common line (`polyInterior_local_halfDisk`), and `p ∈ closure (h₁ ∩ h₂)` iff the sides agree;
  the side of `hᵢ` is constant along the interior of `τ` (the half-disks at nearby points overlap,
  or: the side strip of batch 128), so `τ`'s interior is inside or outside `closure (h₁ ∩ h₂)` as a
  whole; its ends and the finitely many vertices and isolated points of `e ∩ Γ₂` are single points;
* `e ∩ closure (h₁ ∩ h₂) ⊆ e ∩ closure h₂ = (e ∩ h₂) ∪ (e ∩ Γ₂)`, which lists all the points.
So `e ∩ closure (h₁ ∩ h₂)` = (closures of the open pieces) ∪ (the shared segments whose interiors
are in it) ∪ (finitely many points) — polygonal. -/
theorem isPolygonal_frontier_inter_closure {Γ₁ Γ₂ : Set Pt} (h₁ : IsSimpleClosedPolygon Γ₁)
    (h₂ : IsSimpleClosedPolygon Γ₂) :
    IsPolygonal (Γ₁ ∩ closure (polyInterior Γ₁ ∩ polyInterior Γ₂)) := by
  sorry

end HPC.Plane
