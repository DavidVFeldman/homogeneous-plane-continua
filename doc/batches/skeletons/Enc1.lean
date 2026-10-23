import HPC.Plane.JanPoly

/-!
# Batch 130: `enclose`, part I — the grid union, its boundary graph, simple cycles, and the
# polygon interior as the odd parity set

Skeleton. Every `sorry` is a work item; shapes may be adjusted with the change recorded. Save as
`HPC/Plane/Enc1.lean`, add `import HPC.Plane.Enc1` at the end of the root `HPC.lean`.

## The plan for `enclose` (batches 130–131)

The field: `M` a compact continuum not separating the plane, `G ⊇ M` open ⇒ a simple closed
polygon `J` with `J ∩ M = ∅`, `M ⊆ polyInterior J ⊆ G`. The construction avoids the classification
of polyomino boundaries:

1. **The grid union.** With mesh `δ` and offset `0`, `Q :=` the union of the closed grid squares
   meeting `cthickening δ M`. Then `M ∩ frontier Q = ∅` (every square containing a point of `M` is
   in `Q`, and the squares containing a point cover a neighbourhood of it), `Q ⊆ cthickening (2δ) M`,
   and `frontier Q` is the union of the **boundary edges**: the grid edges of the squares of `Q`
   that belong to exactly one square of `Q`. These form a proper graph `G₀` of segments.
2. **The outer cycle.** Let `y` be a far point and `K := connectedComponentIn (graphSet G₀)ᶜ y` (the
   unbounded component). By batch 128, `Z := oddSet G₀ y` is a cycle and
   `gFun G₀ y = [· ∈ K] + cycParity Z` is constant off `graphSet G₀`. A point `x ∈ M` lies in
   `interior Q`, hence not in `K` (`K` cannot cross `frontier Q ⊆ graphSet G₀`), so
   `cycParity Z x = 1 + cycParity Z y = 1` (`cycParity_far`).
3. **Simple cycles.** `Z` is an edge-disjoint union of cycles `J₁, …, J_m` whose point sets are
   simple closed polygons (every even-degree graph decomposes into closed trails; a closed trail
   with a repeated vertex splits at it). Parity is additive, so `∑ cycParity Jᵢ x = 1` for
   `x ∈ M`; each `cycParity Jᵢ` is constant on the connected `M` (which misses `graphSet G₀`), so
   some `Jᵢ` has parity `1` on all of `M`, i.e. `M ⊆ polyInterior Jᵢ` (the odd parity set *is*
   the interior: `polyInterior_eq_oddSet`).
4. **Inside `G`** (batch 131). `K` is connected, unbounded and misses `Jᵢ`, so
   `polyInterior Jᵢ ⊆ Kᶜ`; and `Kᶜ ⊆ G` once the mesh is small: every point of `Gᶜ` inside a large
   ball is joined to a far point by a polygonal path in `Mᶜ` (connected, since `M` does not
   separate), finitely many such paths and balls cover the compact `Gᶜ ∩ closedBall`, their union
   `P` is compact at positive distance `d` from `M`, and with `2δ < d` the set `Q` misses `P`, so
   all of `P` lies in `K`.

This batch: 1, 2, 3 and the parity identification; batch 131: 4, the assembly `enclose_holds`,
`planeFacts_holds : PlaneFacts`, and the retirement of the interface.
-/

namespace HPC.Plane

open Set Metric

/-! ### The polygon interior is the odd parity set -/

/-- For a simple closed polygon `polygonOf v`, `polyInterior (polygonOf v)` is the set of points
off the polygon with crossing parity `1` (from the proof of `jct_polygon`:
`polyInterior_eq_of_split` with the two parity classes). -/
theorem polyInterior_eq_oddSet {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) :
    polyInterior (polygonOf v) = {x | x ∉ polygonOf v ∧ parity v x = 1} := by
  sorry

/-- The parity of a simple closed polygon as a cycle of segments equals its `parity` as a vertex
list: with `edges v := Finset.univ.image (fun i => (v i, v (i+1)))`, `cycParity (edges v) x =
parity v x` (the edge map is injective for simple `v`, so the sums agree term by term). -/
noncomputable def polyEdges {n : ℕ} (v : Fin n → Pt) : Finset Seg :=
  Finset.univ.image fun i : Fin n => (v i, v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)

theorem cycParity_polyEdges {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (x : Pt) :
    cycParity (polyEdges v) x = parity v x := by
  sorry

theorem graphSet_polyEdges {n : ℕ} (v : Fin n → Pt) : graphSet (polyEdges v) = polygonOf v := by
  sorry

/-! ### Simple cycles in a proper graph -/

/-- A finite set of segments `C` is a **simple cycle** if its point set is a simple closed polygon
with the segments of `C` as its edges: there are `n ≥ 3` and simple vertices `v : Fin n → Pt` with
`C = polyEdges v` (up to orientation of the segments: state it as `graphSet C = polygonOf v` and
`∀ s ∈ C, ∃ i, segSet s = polyEdge v i` with the map a bijection, or whichever form the
decomposition below produces most easily; what later steps need is `IsSimpleClosedPolygon
(graphSet C)` and `cycParity C = parity v`). -/
def IsSimpleCycle (C : Finset Seg) : Prop :=
  ∃ (n : ℕ) (v : Fin n → Pt), IsSimpleVertices v ∧ graphSet C = polygonOf v ∧
    ∀ x, cycParity C x = parity v x

/-- **Every cycle is an edge-disjoint union of simple cycles.** (Strong induction on the number of
edges: a nonempty even-degree proper graph contains a closed trail — walk along unused edges from a
vertex of positive degree; by evenness one never gets stuck before returning; a closed trail with
a repeated vertex contains a shorter one; a closed trail without repeated vertices is a simple
cycle, since in a proper graph distinct edges meet only at common ends; remove it and recurse.) -/
theorem exists_simpleCycle_decomposition {Z : Finset Seg} (hZ : IsCycle Z) :
    ∃ L : List (Finset Seg), (∀ C ∈ L, IsSimpleCycle C) ∧ (∀ C ∈ L, C ⊆ Z) ∧
      L.Pairwise Disjoint ∧ Z = L.foldr (· ∪ ·) ∅ := by
  sorry

/-- Parity of an edge-disjoint union is the sum of the parities. -/
theorem cycParity_foldr {L : List (Finset Seg)} (hL : L.Pairwise Disjoint) (x : Pt) :
    cycParity (L.foldr (· ∪ ·) ∅) x = (L.map fun C => cycParity C x).sum := by
  sorry

/-! ### The grid union and its boundary graph -/

/-- The closed grid square of index `(a, b)` and mesh `δ` (offset `0`): `gridSq 0 δ a b`. -/
abbrev gsq (δ : ℝ) (a b : ℤ) : Set Pt := gridSq 0 δ a b

/-- The index set of the squares meeting `cthickening δ M` (finite for bounded `M`). -/
noncomputable def sqIdx (M : Set Pt) (δ : ℝ) : Finset (ℤ × ℤ) :=
  sorry

/-- The grid union. -/
def gridUnion (M : Set Pt) (δ : ℝ) : Set Pt := ⋃ ab ∈ sqIdx M δ, gsq δ ab.1 ab.2

theorem mem_sqIdx_iff {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) (ab : ℤ × ℤ) :
    ab ∈ sqIdx M δ ↔ (gsq δ ab.1 ab.2 ∩ cthickening δ M).Nonempty := by
  sorry

theorem gridUnion_subset_cthickening {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ}
    (hδ : 0 < δ) : gridUnion M δ ⊆ cthickening (2 * δ) M := by
  sorry

theorem isCompact_gridUnion (M : Set Pt) (δ : ℝ) : IsCompact (gridUnion M δ) := by
  sorry

/-- **`M` misses the frontier of the grid union**: a point of `M` lies in every square containing
it, all of which are in `sqIdx` (they meet `M ⊆ cthickening δ M`), and those squares cover a
neighbourhood of the point (the four squares around a vertex, the two along an edge, the one for
an interior point). -/
theorem disjoint_frontier_gridUnion {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ}
    (hδ : 0 < δ) : Disjoint M (frontier (gridUnion M δ)) := by
  sorry

/-- The four edges of a grid square, as segments (oriented lexicographically or in any fixed
way). -/
noncomputable def sqEdges (δ : ℝ) (a b : ℤ) : Finset Seg :=
  sorry

/-- **The boundary graph**: the edges of the squares of `sqIdx` that belong to exactly one
square of `sqIdx`. -/
noncomputable def bdryGraph (M : Set Pt) (δ : ℝ) : Finset Seg :=
  sorry

/-- The boundary graph is a proper graph (grid segments of one mesh meet only at grid vertices,
which are their ends; distinct segments have distinct point sets). -/
theorem isProper_bdryGraph {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) :
    IsProper (bdryGraph M δ) := by
  sorry

/-- **The frontier of the grid union is the boundary graph.** (A point of a grid edge shared by two
squares of `Q` is interior to `Q`; a point of an edge of exactly one square of `Q` is a frontier
point; grid vertices are handled by the squares around them — a vertex all of whose squares are in
`Q` is interior, otherwise it is an end of a boundary edge; points inside a square of `Q` are
interior, points in no square of `Q` are outside `Q`, which is closed.) -/
theorem frontier_gridUnion {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) :
    frontier (gridUnion M δ) = graphSet (bdryGraph M δ) := by
  sorry

/-- The boundary graph lies in the grid union. -/
theorem graphSet_bdryGraph_subset {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) :
    graphSet (bdryGraph M δ) ⊆ gridUnion M δ := by
  sorry

/-! ### The outer cycle and the enclosing polygon -/

/-- A far point: beyond everything, east. -/
noncomputable def farPt (M : Set Pt) (δ : ℝ) : Pt :=
  sorry

theorem farPt_not_mem {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) :
    farPt M δ ∉ gridUnion M δ := by
  sorry

/-- **The interior of the grid union lies outside the unbounded component**: the component `K` of
the far point in `(graphSet G₀)ᶜ` does not meet `interior Q` (it is connected, misses
`frontier Q`, and contains a point outside `Q`). -/
theorem interior_gridUnion_disjoint_component {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ}
    (hδ : 0 < δ) :
    Disjoint (interior (gridUnion M δ))
      (connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)) := by
  sorry

/-- **Points of `M` have odd parity for the outer cycle.** With `Z := oddSet (bdryGraph M δ) (farPt
M δ)`: `gFun` is constant off the graph (`gFun_const`), equals `1 + cycParity Z (farPt)` at the far
point and `0 + cycParity Z x` at `x ∈ M ⊆ interior Q`; `cycParity Z (farPt) = 0` (`cycParity_far`,
the far point is east of everything). -/
theorem cycParity_oddSet_eq_one_on {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ)
    {x : Pt} (hx : x ∈ M) :
    cycParity (oddSet (bdryGraph M δ) (farPt M δ)) x = 1 := by
  sorry

/-- **The enclosing polygon, inside the complement of the unbounded component.** For a compact
connected `M` and mesh `δ > 0`: a simple closed polygon `J ⊆ graphSet (bdryGraph M δ)` with
`J ∩ M = ∅`, `M ⊆ polyInterior J`, and `polyInterior J` disjoint from the component `K` of the far
point. (Decompose the outer cycle into simple cycles; parities add to `1` on `M`; each is constant
on the connected `M`, which misses the graph; pick one with parity `1`; `polyInterior_eq_oddSet`;
`K` is connected, unbounded and misses `J`, so lies in the exterior — `polyInterior_disjoint_of_
unbounded`.) -/
theorem exists_enclosing_polygon {M : Set Pt} (hM : Fold.Q78.IsContinuum M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ J ⊆ graphSet (bdryGraph M δ) ∧ Disjoint J M ∧
      M ⊆ polyInterior J ∧
      Disjoint (polyInterior J) (connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)) := by
  sorry

end HPC.Plane
