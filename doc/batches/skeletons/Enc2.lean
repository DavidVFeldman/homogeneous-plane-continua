import HPC.Plane.Enc1
import HPC.Plane.JanPoly

/-!
# Batch 131: `enclose`, part II — the uniform path argument, `enclose_holds`, `planeFacts_holds`,
# Theorems 6 and 7 of Bing 1951 (Duke) unconditional

Skeleton. Save as `HPC/Plane/Enc2.lean`, add `import HPC.Plane.Enc2` at the end of the root
`HPC.lean`. Every `sorry` is a work item; shapes may be adjusted with the change recorded. The
edits to existing files (the renaming of the three relative theorems of `Tree7Comp.lean`, the
audit, `OPEN.md`, `README.md`) are described in COMMISSION-batch131.md §2 and are NOT in this file.

## The argument

Fix a continuum `M` that does not separate the plane, an open `G ⊇ M`, and `R` with
`M ⊆ ball 0 R`. Write `K δ := connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)`.
`exists_enclosing_polygon` (batch 130) gives, for every mesh `δ > 0`, a simple closed polygon `J`
with `M ⊆ polyInterior J` and `polyInterior J ∩ K δ = ∅`. So `polyInterior J ⊆ (K δ)ᶜ`, and
`enclose` follows once `(K δ)ᶜ ⊆ G`, i.e. `Gᶜ ⊆ K δ`, for one `δ`.

Membership in `K δ`, uniformly: a preconnected set `S` all of whose points are at distance
`> 2δ` from `M` misses `cthickening (2δ) M ⊇ gridUnion M δ ⊇ graphSet (bdryGraph M δ)`, so if `S`
meets `K δ` then `S ⊆ K δ` (`subset_component_of_far`). The eastern half-plane
`Ioi (gridR M δ) ×ˢ univ` lies in `K δ` (`halfPlane_subset_component`, batch 130).

The far point `f₀ := (R + 1, 0)` and the ray `Ray R := {(t, 0) | R + 1 ≤ t}` are at distance
`≥ 1` from `M` (sup metric: `dist (t, 0) m ≥ t - m.1 > t - R`). The ray is preconnected and meets
the eastern half-plane, so `Ray R ⊆ K δ` whenever `2δ < 1`.

`Mᶜ` is open and connected (`¬ SeparatesPlane M`), hence path-connected
(`IsOpen.isConnected_iff_isPathConnected`). For `x ∈ Gᶜ ∩ closedBall 0 (R + 1)` (compact, inside
`Mᶜ` since `M ⊆ G`) choose a path `γₓ` in `Mᶜ` from `x` to `f₀`; its range is compact and disjoint
from the compact `M`, so `dₓ := infDist`-gap `> 0`; put `rₓ := dₓ / 2`. The set
`Pₓ := closedBall x rₓ ∪ range γₓ` is compact, preconnected, contains `f₀`, and every point of it
is at distance `≥ rₓ` from `M` (triangle inequality on the ball). The balls `ball x rₓ` cover the
compact `Gᶜ ∩ closedBall 0 (R + 1)`; take a finite subcover `x₁, …, xₙ`, and
`d := min (1, r₁, …, rₙ) > 0`, `δ := d / 3`. Then `2δ < d`, so each `Pᵢ` and the ray lie in
`K δ`; hence `Gᶜ ∩ closedBall 0 (R + 1) ⊆ ⋃ ball xᵢ rᵢ ⊆ K δ`.

Points `x` with `‖x‖ > R + 1` (sup norm) are at distance `> 1` from `M` and lie in one of the four
open half-planes `{x.1 > R + 1}`, `{x.1 < -(R + 1)}`, `{x.2 > R + 1}`, `{x.2 < -(R + 1)}`, each
preconnected and at distance `> 1` from `M`; the first meets the eastern half-plane, and each of
the others meets the first at a corner `(T, ±T)` / `(±T, T)` with `T > R + 1`. So all four are in
`K δ` (`compl_closedBall_subset_component`). Hence `Gᶜ ⊆ K δ`.

Non-separation is used once: for the paths `γₓ`. `IsContinuum M` gives `M` compact, connected,
nonempty (`exists_enclosing_polygon` needs it; `infDist` to `M` needs nonemptiness).
-/

namespace HPC.Plane

open Set Metric

/-- The outer component of mesh `δ`, abbreviated. -/
def outerComp (M : Set Pt) (δ : ℝ) : Set Pt :=
  connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)

/-! ### Uniform membership in the outer component -/

/-- A point at distance `> 2δ` from `M` is off the boundary graph of mesh `δ`
(`graphSet_bdryGraph_subset`, `gridUnion_subset_cthickening`; `cthickening (2δ) M` is
`{p | infEdist p M ≤ 2δ}`). -/
theorem not_mem_graphSet_bdryGraph_of_far {M : Set Pt} (hM : Bornology.IsBounded M)
    (hMne : M.Nonempty) {δ : ℝ} (hδ : 0 < δ) {p : Pt} (hp : 2 * δ < infDist p M) :
    p ∉ graphSet (bdryGraph M δ) := by
  sorry

/-- A preconnected set at distance `> 2δ` from `M` that meets the outer component lies in it. -/
theorem subset_component_of_far {M : Set Pt} (hM : Bornology.IsBounded M) (hMne : M.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) {S : Set Pt} (hS : IsPreconnected S)
    (hfar : ∀ p ∈ S, 2 * δ < infDist p M) (hmeet : (S ∩ outerComp M δ).Nonempty) :
    S ⊆ outerComp M δ := by
  sorry

/-- The eastern ray from `(R + 1, 0)`. -/
def eastRay (R : ℝ) : Set Pt := (fun t : ℝ => ((t, 0) : Pt)) '' Ici (R + 1)

theorem isPreconnected_eastRay (R : ℝ) : IsPreconnected (eastRay R) := by
  sorry

/-- Points of the ray are at distance `> R' ` from `M` whenever … — the form used: if `M ⊆ ball 0 R`
then every point of `eastRay R` is at distance `≥ 1` from `M` (sup metric, first coordinates). -/
theorem one_le_infDist_eastRay {M : Set Pt} (hMne : M.Nonempty) {R : ℝ} (hMR : M ⊆ ball 0 R)
    {p : Pt} (hp : p ∈ eastRay R) : 1 ≤ infDist p M := by
  sorry

/-- The ray meets the eastern half-plane `Ioi (gridR M δ) ×ˢ univ ⊆ outerComp M δ`
(`halfPlane_subset_component`), so it lies in the outer component for `2δ < 1`. -/
theorem eastRay_subset_component {M : Set Pt} (hM : Bornology.IsBounded M) (hMne : M.Nonempty)
    {R : ℝ} (hMR : M ⊆ ball 0 R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : 2 * δ < 1) :
    eastRay R ⊆ outerComp M δ := by
  sorry

/-- The outside of the closed sup-norm ball of radius `R + 1` lies in the outer component for
`2δ < 1` (four open half-planes, each preconnected, each at distance `> 1` from `M`; the eastern
one meets `Ioi (gridR M δ) ×ˢ univ`; the others meet it at corners). -/
theorem compl_closedBall_subset_component {M : Set Pt} (hM : Bornology.IsBounded M)
    (hMne : M.Nonempty) {R : ℝ} (hMR : M ⊆ ball 0 R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : 2 * δ < 1) :
    (closedBall (0 : Pt) (R + 1))ᶜ ⊆ outerComp M δ := by
  sorry

/-! ### Paths in `Mᶜ` and their distance from `M` -/

/-- An open connected set in the plane is path-connected
(`IsOpen.isConnected_iff_isPathConnected`; `ℝ × ℝ` is a `LocPathConnectedSpace` as a normed
space — check the instance; otherwise `Convex.isPathConnected` on balls and the open-set argument). -/
theorem joinedIn_compl_of_not_separates {M : Set Pt} (hMc : IsClosed M) (hns : ¬ SeparatesPlane M)
    {x y : Pt} (hx : x ∉ M) (hy : y ∉ M) : JoinedIn Mᶜ x y := by
  sorry

/-- A compact set disjoint from the compact nonempty `M` is at positive distance from it:
there is `d > 0` with `d ≤ infDist p M` for all its points. -/
theorem exists_pos_infDist_le_of_disjoint {M P : Set Pt} (hM : IsCompact M) (hMne : M.Nonempty)
    (hP : IsCompact P) (hPM : Disjoint P M) : ∃ d > 0, ∀ p ∈ P, d ≤ infDist p M := by
  sorry

/-- **The local piece.** For `x ∉ M` and `f₀ ∉ M`, with `Mᶜ` connected: a radius `r > 0` and a
preconnected set `P ∋ x, f₀` containing `closedBall x r`, every point of which is at distance
`≥ r` from `M`. (`P := closedBall x r ∪ range γ` with `γ` a path in `Mᶜ` from `x` to `f₀` and
`r := d / 2`, `d` the gap of `range γ`; on the ball, `infDist p M ≥ infDist x M - dist p x ≥ d - r`.) -/
theorem exists_far_piece {M : Set Pt} (hM : IsCompact M) (hMne : M.Nonempty)
    (hns : ¬ SeparatesPlane M) {x f₀ : Pt} (hx : x ∉ M) (hf : f₀ ∉ M) :
    ∃ r > 0, ∃ P : Set Pt, IsPreconnected P ∧ x ∈ P ∧ f₀ ∈ P ∧ closedBall x r ⊆ P ∧
      ∀ p ∈ P, r ≤ infDist p M := by
  sorry

/-- **The uniform constant.** For a compact `C ⊆ Mᶜ` and `f₀ ∉ M`: a `d > 0` and finitely many
pieces `Pᵢ` (preconnected, containing `f₀`, at distance `≥ d` from `M`) whose interiors cover `C`
(finite subcover of `C` by the balls `ball xᵢ rᵢ`, `exists_far_piece`; `d := min rᵢ`, or `1` if
there are none). -/
theorem exists_uniform_pieces {M : Set Pt} (hM : IsCompact M) (hMne : M.Nonempty)
    (hns : ¬ SeparatesPlane M) {C : Set Pt} (hC : IsCompact C) (hCM : Disjoint C M) {f₀ : Pt}
    (hf : f₀ ∉ M) :
    ∃ d > 0, ∃ F : Finset (Set Pt), (∀ P ∈ F, IsPreconnected P ∧ f₀ ∈ P ∧
      ∀ p ∈ P, d ≤ infDist p M) ∧ C ⊆ ⋃ P ∈ F, P := by
  sorry

/-! ### `enclose` -/

/-- **The complement of `G` lies in the outer component for small mesh.** `R` with `M ⊆ ball 0 R`;
`C := Gᶜ ∩ closedBall 0 (R + 1)`; `f₀ := (R + 1, 0) ∈ eastRay R`; `exists_uniform_pieces` gives `d`
and `F`; `δ := min d 1 / 3`. Each `P ∈ F` meets `outerComp M δ` at `f₀` (`eastRay_subset_component`)
and is at distance `≥ d > 2δ` from `M`, so `P ⊆ outerComp M δ` (`subset_component_of_far`); the
outside of the closed ball by `compl_closedBall_subset_component`. -/
theorem exists_mesh_compl_subset {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ¬ SeparatesPlane M) {G : Set Pt} (hG : IsOpen G) (hMG : M ⊆ G) :
    ∃ δ > 0, Gᶜ ⊆ outerComp M δ := by
  sorry

/-- **The field `enclose` of `PlaneFacts` holds**: a continuum that does not separate the plane,
inside an open set `G`, is enclosed by a simple closed polygon whose interior lies in `G`
(`exists_mesh_compl_subset` and `exists_enclosing_polygon`: `polyInterior J ⊆ (outerComp M δ)ᶜ ⊆ G`). -/
theorem enclose_holds : ∀ M : Set Pt, Fold.Q78.IsContinuum M → ¬ SeparatesPlane M →
    ∀ G : Set Pt, IsOpen G → M ⊆ G →
      ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ Disjoint J M ∧ M ⊆ polyInterior J ∧
        polyInterior J ⊆ G := by
  sorry

/-- **`PlaneFacts` holds.** All three fields proved: `jct_polygon` (batch 126),
`enclose_holds` (batches 130–131), `janiszewski_polygonal` (batches 127–129). -/
theorem planeFacts_holds : PlaneFacts := planeFacts_of_enclose enclose_holds

/-! ### Bing 1951 (Duke), Theorems 6 and 7, unconditional

The relative forms (`theorem7_1951_rel`, `theorem6_1951_rel`, `theorem7_weak_rel` after the
renaming of COMMISSION-batch131.md §2) are specialised at `planeFacts_holds`. Statements otherwise
verbatim. -/

/-- **Bing 1951 (Duke), Theorem 7** (with the hypothesis "no subcontinuum of `M` separates the
plane" in place of "tree-like", as in batches 120–130): a bounded plane continuum no subcontinuum
of which separates the plane is covered, for every `ε > 0`, by a tree chain whose links are
interiors of simple closed polygons of diameter `< ε`. No interface, no hypothesis beyond the
theorem's own. -/
theorem theorem7_1951 {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧
      (∀ h ∈ G, ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ) ∧
      (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h :=
  theorem7_1951_rel planeFacts_holds hM hns hε

/-- **Bing 1951 (Duke), Theorem 6**: a bounded plane continuum containing no continuum that
separates the plane is tree-like. No interface. -/
theorem theorem6_1951 {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) : IsTreeLike M :=
  theorem6_1951_rel planeFacts_holds hM hns

/-- **Theorem 7, weak form**, unconditional. -/
theorem theorem7_weak {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧ (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h ∧
      ∀ h ∈ G, IsOpen h ∧ IsConnected h ∧ Bornology.IsBounded h ∧
        interior (closure h) = h ∧ ¬ SeparatesPlane h :=
  theorem7_weak_rel planeFacts_holds hM hns hε

end HPC.Plane
