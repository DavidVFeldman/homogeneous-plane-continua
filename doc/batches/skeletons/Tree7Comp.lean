import HPC.Plane.Tree7

/-!
# Batch 120: Bing 1951 (Duke), Theorem 7 — the components are polygon interiors; `theorem7_1951`

Skeleton. Every `sorry` is a work item; shapes may be adjusted with the change recorded. Save as
`HPC/Plane/Tree7Comp.lean`, add `import HPC.Plane.Tree7Comp` at the end of the root `HPC.lean`. No
existing file is to be edited except `Axioms.lean`/`axioms.txt`.

**Theorem 7 (p. 657).** *If `M` is a tree-like plane continuum and `ε` is a positive number, there is
a tree-chain covering `M` whose links are the interiors of simple closed curves of diameters less
than `ε`.* Stated here with the hypothesis the proof of Theorem 6 uses (no subcontinuum of `M`
separates the plane); the implication from "tree-like" is open relative to `PlaneFacts`
(batch 119, item 5).

**The main theorem of this batch** (`PlaneFacts.component_inter_eq_polyInterior`): if `J` and `P` are
simple closed polygons whose intersection is **finite**, every component of
`polyInterior J ∩ polyInterior P` is the interior of a simple closed polygon. Transversality is not
used; general position (batch 119) enters only through `finite_inter_of_gp`. Plan:

1. **Cross-cut families and the induction.** A cross-cut family of `J` is a finite set of cross-cuts
   (as in `PlaneFacts.crosscut`) any two of which meet only in points of `J`, i.e. only at common
   ends. Splitting `polyInterior J` along one of them (`crosscut`) and distributing the others to
   the two sides, induction on the number of cross-cuts shows that every component of
   `polyInterior J \ ⋃ C` is a polygon interior.
2. **Decomposing `P` at a finite set of its points** into simple arcs meeting only at those points
   (`split_two` at two of them, then `IsSimplePolyArc.split` at the rest, by induction).
3. **The cross-cut family of `P` in `J`**: the pieces of `P` between consecutive points of
   `X = P ∩ J` which run inside `polyInterior J`; `polyInterior J \ P = polyInterior J \ ⋃ C`.
4. **Identification**: a component of `U ∩ N` (`U = polyInterior J`, `N = polyInterior P`) is a
   component of `U \ P` (a connected set missing `frontier N = P` and meeting `N` lies in `N`).
   The degenerate cases (`P ∩ U = ∅`; `P ∩ J = ∅`; `P ∩ J` a single point) give `U ∩ N ∈ {∅, U, N}`
   by connectedness alone.
5. **Theorem 7** from `exists_gp_cover`, `treeChain_of_cover`, `notched_eq_polyInterior`.
-/

namespace HPC.Plane

open Set Metric

open scoped Classical

/-! ### 1. Cross-cut families and the induction -/

/-- A **cross-cut** of the simple closed polygon `J`: a simple polygonal arc meeting `J` exactly in
its two (distinct) ends, with its interior inside `polyInterior J`. -/
def IsCrosscut (J c : Set Pt) : Prop :=
  ∃ a b : Pt, a ≠ b ∧ IsSimplePolyArc c a b ∧ c ∩ J = {a, b} ∧ c \ {a, b} ⊆ polyInterior J

/-- A **cross-cut family** of `J`: finitely many cross-cuts, any two of which meet only in `J`
(hence only at common ends). -/
def IsCrosscutFamily (J : Set Pt) (C : Finset (Set Pt)) : Prop :=
  (∀ c ∈ C, IsCrosscut J c) ∧ ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → c ∩ c' ⊆ J

/-- The component of a point of `A` in the union of two disjoint open sets `A`, `B` is its
component in `A`. -/
theorem connectedComponentIn_union_of_disjoint_open {A B : Set Pt} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : Disjoint A B) {x : Pt} (hx : x ∈ A) :
    connectedComponentIn (A ∪ B) x = connectedComponentIn A x := by
  sorry

/-- A cross-cut of `J` whose interior lies in `polyInterior (αᵢ ∪ c)` (one side of the cross-cut `c`,
`crosscut`) and which meets `c` only in `J` is a cross-cut of `αᵢ ∪ c`. (Its ends are in
`closure (polyInterior (αᵢ ∪ c)) ∩ J = αᵢ`, the closure clause of `crosscut`; it meets `c` only in
its ends, as `c' ∩ c ⊆ J ∩ c' = ends`.) -/
theorem IsCrosscut.of_side {J c c' α : Set Pt} (hc' : IsCrosscut J c')
    (hΓ : IsSimpleClosedPolygon (α ∪ c)) (hα : α ⊆ J)
    (hcl : closure (polyInterior (α ∪ c)) ∩ J = α) (hcc : c' ∩ c ⊆ J)
    (hside : ∀ a b : Pt, IsSimplePolyArc c' a b → c' \ {a, b} ⊆ polyInterior (α ∪ c)) :
    IsCrosscut (α ∪ c) c' := by
  sorry

/-- **The cross-cut induction.** For a cross-cut family `C` of `J`, every component of
`polyInterior J \ ⋃ C` is the interior of a simple closed polygon contained in `J ∪ ⋃ C`.

Induction on `C.card`. `C = ∅`: the component is `polyInterior J` (connected, `polyInterior_eq`).
Otherwise pick `c ∈ C`, `crosscut` gives `α₁`, `α₂`, `Γᵢ = αᵢ ∪ c`, `Uᵢ = polyInterior Γᵢ` with
`polyInterior J \ c = U₁ ⊔ U₂`. For `c' ∈ C.erase c`, `c' \ ends` is connected
(`isConnected_diff_ends`), lies in `polyInterior J \ c` (`c' ∩ c ⊆ J` and the interior misses `J`),
so lies in `U₁` or in `U₂`; let `Cᵢ` be those in `Uᵢ`. Each `Cᵢ` is a cross-cut family of `Γᵢ`
(`IsCrosscut.of_side`; pairwise: `c' ∩ c'' ⊆ J ∩ c' = ends c' ⊆ Γᵢ`). Then
`polyInterior J \ ⋃ C = (U₁ \ ⋃ C₁) ⊔ (U₂ \ ⋃ C₂)` — a cross-cut of `C₂` lies in `closure U₂`,
which misses the open `U₁` — both pieces open, so the component of `x ∈ U₁ \ ⋃ C₁` in the union is
its component in `U₁ \ ⋃ C₁` (`connectedComponentIn_union_of_disjoint_open`), a polygon interior by
induction (`C₁.card < C.card`), with polygon `⊆ Γ₁ ∪ ⋃ C₁ ⊆ J ∪ ⋃ C`. -/
theorem PlaneFacts.components_of_crosscuts (hPF : PlaneFacts) {J : Set Pt}
    (hJ : IsSimpleClosedPolygon J) {C : Finset (Set Pt)} (hC : IsCrosscutFamily J C) {x : Pt}
    (hx : x ∈ polyInterior J \ ⋃ c ∈ C, c) :
    ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧ Γ ⊆ J ∪ ⋃ c ∈ C, c ∧
      connectedComponentIn (polyInterior J \ ⋃ c ∈ C, c) x = polyInterior Γ := by
  sorry

/-! ### 2. Decomposing an arc and a polygon at finitely many points -/

/-- **Decomposing a simple arc at a finite set `X` of interior points**: finitely many simple
sub-arcs with ends in `X ∪ {p, q}`, covering the arc, meeting each other and `X ∪ {p, q}` only at
their ends. Induction on `X` (`Finset.induction`): remove `x ∈ X`, decompose, and split the piece
containing `x` at `x` (`IsSimplePolyArc.split`). -/
theorem exists_arc_decomposition {β : Set Pt} {p q : Pt} (hβ : IsSimplePolyArc β p q)
    (X : Finset Pt) (hX : ∀ x ∈ X, x ∈ β ∧ x ≠ p ∧ x ≠ q) :
    ∃ A : Finset (Set Pt), (⋃ γ ∈ A, γ) = β ∧
      (∀ γ ∈ A, ∃ s t : Pt, IsSimplePolyArc γ s t ∧ s ∈ insert p (insert q (X : Set Pt)) ∧
        t ∈ insert p (insert q (X : Set Pt)) ∧ γ ∩ insert p (insert q (X : Set Pt)) = {s, t}) ∧
      ∀ γ ∈ A, ∀ γ' ∈ A, γ ≠ γ' → γ ∩ γ' ⊆ insert p (insert q (X : Set Pt)) := by
  sorry

/-- **Decomposing a simple closed polygon at a finite set `X ⊆ P` with at least two points** into
simple arcs with ends in `X`, covering `P`, meeting each other and `X` only at their ends.
(`split_two` at two points of `X`, then `exists_arc_decomposition` on each arc with the remaining
points of `X` on it.) -/
theorem exists_polygon_decomposition {P : Set Pt} (hP : IsSimpleClosedPolygon P) (X : Finset Pt)
    (hXP : (X : Set Pt) ⊆ P) (hX2 : 2 ≤ X.card) :
    ∃ A : Finset (Set Pt), (⋃ γ ∈ A, γ) = P ∧
      (∀ γ ∈ A, ∃ s t : Pt, IsSimplePolyArc γ s t ∧ s ∈ X ∧ t ∈ X ∧ γ ∩ X = {s, t}) ∧
      ∀ γ ∈ A, ∀ γ' ∈ A, γ ≠ γ' → γ ∩ γ' ⊆ X := by
  sorry

/-! ### 3. The cross-cut family of `P` in `J` -/

/-- **The pieces of `P` inside `polyInterior J`.** If `J`, `P` are simple closed polygons with
`X = J ∩ P` finite of cardinality `≥ 2`, the pieces of `P` between consecutive points of `X`
(`exists_polygon_decomposition`) whose interiors lie in `polyInterior J` form a cross-cut family
`C` of `J` with `polyInterior J \ P = polyInterior J \ ⋃ C`. (A piece minus its ends is connected
and misses `J` — `γ ∩ J = γ ∩ P ∩ J = γ ∩ X = ends` — so it lies in `polyInterior J` or in the
exterior; the pieces in the exterior do not meet `polyInterior J` at all, since their ends are on
`J`; pairwise `γ ∩ γ' ⊆ X ⊆ J`.) -/
theorem PlaneFacts.exists_crosscutFamily (hPF : PlaneFacts) {J P : Set Pt}
    (hJ : IsSimpleClosedPolygon J) (hP : IsSimpleClosedPolygon P) (hfin : (J ∩ P).Finite)
    (h2 : 2 ≤ hfin.toFinset.card) :
    ∃ C : Finset (Set Pt), IsCrosscutFamily J C ∧ (∀ c ∈ C, c ⊆ P) ∧
      polyInterior J \ P = polyInterior J \ ⋃ c ∈ C, c := by
  sorry

/-! ### 4. Identification of the components; the degenerate cases -/

/-- A connected set missing the frontier of `S` and meeting `S` lies in `S`. -/
theorem subset_of_isConnected_of_disjoint_frontier {S T : Set Pt} (hT : IsConnected T)
    (hfr : Disjoint T (frontier S)) (hne : (T ∩ S).Nonempty) : T ⊆ S := by
  sorry

/-- The component of `x ∈ U ∩ N` in `U ∩ N` is its component in `U \ P`, where
`N = polyInterior P` and `P = frontier N` (`PlaneFacts.split`). -/
theorem PlaneFacts.connectedComponentIn_inter_eq (hPF : PlaneFacts) {P : Set Pt}
    (hP : IsSimpleClosedPolygon P) {U : Set Pt} (hU : IsOpen U) {x : Pt}
    (hx : x ∈ U ∩ polyInterior P) :
    connectedComponentIn (U ∩ polyInterior P) x = connectedComponentIn (U \ P) x := by
  sorry

/-- **The main theorem: components of the intersection of two polygon interiors whose boundaries
meet in finitely many points are polygon interiors.** With `U = polyInterior J`, `N = polyInterior
P`, `X = J ∩ P`:
* `P ∩ U = ∅`: `U` is connected and misses `P = frontier N`, so `U ⊆ N` (then `U ∩ N = U`) or
  `U ∩ N = ∅` (no `x`).
* `P ∩ U ≠ ∅`, `X = ∅`: `P` is connected and misses `J`, so `P ⊆ U`. `J ∩ N = ∅`: otherwise `J`
  (connected, missing `P`) lies in `N`, then `closure U = U ∪ J` (connected, missing `P`, meeting
  `N`) lies in `N`, so `P ⊆ U ⊆ N`, against `P ∩ N = ∅` (`P = frontier N`, `N` open, `P ≠ ∅`). So
  `closure N = N ∪ P` is connected, misses `J`, meets `U`: `N ⊆ U`, and `U ∩ N = N = polyInterior P`.
* `P ∩ U ≠ ∅`, `X = {a}`: `P \ {a}` is connected (split `P` at `a` and a second point; an arc minus
  one end is connected) and misses `J`, so `P \ {a} ⊆ U`. `J \ {a}` is connected and misses `P`, so
  `J \ {a} ⊆ N` or `J \ {a} ⊆ (closure N)ᶜ`. In the first case `U ∪ (J \ {a})` is connected, misses
  `P`, meets `N`, so `U ⊆ N` and `U ∩ N = U`. In the second `N ∪ (P \ {a})` is connected, misses `J`,
  meets `U`, so `N ⊆ U` and `U ∩ N = N`.
* `2 ≤ |X|`: `exists_crosscutFamily`, `connectedComponentIn_inter_eq`, `components_of_crosscuts`. -/
theorem PlaneFacts.component_inter_eq_polyInterior (hPF : PlaneFacts) {J P : Set Pt}
    (hJ : IsSimpleClosedPolygon J) (hP : IsSimpleClosedPolygon P) (hfin : (J ∩ P).Finite)
    {x : Pt} (hx : x ∈ polyInterior J ∩ polyInterior P) :
    ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧
      connectedComponentIn (polyInterior J ∩ polyInterior P) x = polyInterior Γ := by
  sorry

/-! ### 5. Theorem 7 -/

/-- The vertex function of the 20-gon satisfies the vertex-level predicate (the content of
`isSimpleClosedPolygon_notchedPoly`, batch 119). -/
theorem isSimpleVertices_notchedVertices (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) : IsSimpleVertices (notchedVertices o δ η r a b) := by
  sorry

/-- In general position the boundaries of the polygon `polygonOf v` and of a notched square meet
in a finite set (`finite_inter_of_gp`, `notchedPoly = polygonOf notchedVertices`). -/
theorem finite_inter_notchedPoly_of_gp {n : ℕ} {v : Fin n → Pt} (o : Pt) (δ η r : ℝ) (a b : ℤ)
    (hgp : InGeneralPosition v (notchedVertices o δ η r a b)) :
    (polygonOf v ∩ notchedPoly o δ η r a b).Finite := by
  sorry

/-- **Theorem 7 (Bing 1951, Duke, p. 657)**, with the hypothesis its proof uses: a bounded plane
continuum no subcontinuum of which separates the plane is covered, for every `ε > 0`, by a tree
chain whose links are interiors of simple closed polygons of diameter `< ε`. (`exists_gp_cover`
gives `v`, `o δ η r I`; `J = polygonOf v`; `treeChain_of_cover` gives `G ⊆ compFamily (polyInterior J)
(notchedFamily o δ η r I)`; a member is `connectedComponentIn (polyInterior J ∩ notched …) x`, and
`notched … = polyInterior (notchedPoly …)` (`notched_eq_polyInterior`) with `notchedPoly` simple
and `J ∩ notchedPoly` finite (`finite_inter_notchedPoly_of_gp`), so
`component_inter_eq_polyInterior` applies.) -/
theorem theorem7_1951 (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧
      (∀ h ∈ G, ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ) ∧
      (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h := by
  sorry

end HPC.Plane
