import HPC.Plane.Arcs48

/-!
# Batch 109: threaded chains, and the band around a self-avoiding lattice path

Skeleton (save as `HPC/Plane/Band.lean`; add `import HPC.Plane.Band` to the root `HPC.lean`).
Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the change
recorded. No existing file is to be edited, except the audit.

Purpose: the first half of a proof of the density lemma of Bing 1951 (Pacific) §3 in the plane,
replacing the open `exists_tame_chain_near` (a chain of links that are images of the standard boxes
under a *homeomorphism of `E`*) by what `exists_pseudoArc_in_tameChain` actually uses — a map of
the open standard strip into `E`, continuous and injective on the strip, carrying each standard
rectangle into the corresponding link (`IsThreadedChain`). Such a map is built here as a *band*
around a self-avoiding lattice path whose corners are rounded by quarter circles: no
homeomorphism of the plane, no bending of the complement. The second half (batch 110) is the
combinatorial lemma — a self-avoiding lattice cycle inside the squares meeting a plane continuum,
through every one of them — and the assembly.

Conventions. `E` is a real inner product space; `e₁, e₂` an orthonormal pair; `δ > 0` the lattice
mesh; the lattice point `(a, b) : ℤ × ℤ` sits at `δ • (a • e₁ + b • e₂)`. A self-avoiding lattice
path with `n` steps is `c 0, …, c n`, pairwise distinct, consecutive ones a unit step apart. Its
*stretches* are indexed by `k = 0, …, n`: stretch `k` runs from the midpoint of step `k-1` to the
midpoint of step `k` (half-steps at the two ends), straight if steps `k-1` and `k` have the same
direction, and otherwise the quarter circle of radius `δ/2` centred at `c k - u/2 + u'/2`
(`u, u'` the two step directions) from the one midpoint to the other. The *rounded path* `Γ` is
parametrised by `τ ∈ [0, n]`, stretch `k` on `[k - 1/2, k + 1/2]` (clipped to `[0, n]`), and `ν`
is its left unit normal; the *band* is `(τ, t) ↦ Γ τ + (t * δ) • ν τ`, `|t| < 1/8`. The strip
`(0, 2m+1) × (0, 1)` is threaded through the band by `(x, y) ↦ band (λ x) ((y - 1/2)/4)` with
`λ = n / (2m+1) ∈ [3, 4)`, so that the `τ`-ranges of nonadjacent links are at least `λ ≥ 3`
apart, hence lie in nonadjacent stretches, whose *stretch triangles* (the convex hull of `c k` and
the two midpoints) are at distance `≥ (√2/2) δ > 2 · (δ/8)`.
-/

namespace HPC.Plane

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Threaded chains -/

/-- The open strip `(0, 2m+1) × (0, 1)`: the union of the first `m` standard rectangles. -/
def stripSet (m : ℕ) : Set Pt := ⋃ j : Fin m, stdRect j

theorem stripSet_eq (m : ℕ) : stripSet m = Ioo (0 : ℝ) (2 * m + 1) ×ˢ Ioo (0 : ℝ) 1 := by
  sorry

/-- **A threaded chain** in `E`: a map of the plane, continuous and injective on the open strip,
carrying each standard rectangle into the corresponding link. Weaker than `IsTameChain` (no
homeomorphism of `E`, no openness, links need not be images); it is exactly what
`exists_pseudoArc_in_tameChain` uses. -/
def IsThreadedChain {m : ℕ} (D : Chain E m) : Prop :=
  ∃ f : Pt → E, ContinuousOn f (stripSet m) ∧ InjOn f (stripSet m) ∧
    ∀ j : Fin m, f '' stdRect j ⊆ D.link j

theorem isThreadedChain_of_isTameChain {m : ℕ} {D : Chain E m} (hD : IsTameChain D) :
    IsThreadedChain D := by
  sorry

/-- **A pseudo-arc inside a threaded chain** (the proof of `exists_pseudoArc_in_tameChain`,
verbatim: batch 84's planar pseudo-arc in the standard rectangles, carried by `f`; Pacific
Theorem 4 for the continuous injective image). -/
theorem exists_pseudoArc_in_threadedChain {m : ℕ} (hm : 3 ≤ m) (D : Chain E m)
    (hD : IsThreadedChain D) :
    ∃ h : Set E, IsPseudoArc h ∧ h ⊆ D.union ∧ ∀ j, (h ∩ D.link j).Nonempty := by
  sorry

/-- The geometric lemma with threaded chains in place of tame chains, as a hypothesis. -/
def GeomLemma' (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Prop :=
  ∀ g : Set E, Fold.Q78.IsContinuum g → ∀ ε : ℝ, 0 < ε →
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsThreadedChain D ∧ (∀ j, diam (D.link j) < ε) ∧
      D.union ⊆ thickening ε g ∧ g ⊆ thickening ε D.union

theorem geomLemma'_of_geomLemma (h : GeomLemma E) : GeomLemma' E := by
  sorry

/-- Density from the threaded form (the proof of `dense_pseudoArcs_of`, verbatim). -/
theorem dense_pseudoArcs_of' (hgeo : GeomLemma' E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} := by
  sorry

theorem theorem2_HIC_of' (hgeo : GeomLemma' E) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsPseudoArc (K.1 : Set E)} := by
  sorry

/-! ### Lattice paths -/

/-- A unit step of the integer lattice. -/
def IsUnitStep (p q : ℤ × ℤ) : Prop := |q.1 - p.1| + |q.2 - p.2| = 1

/-- **A self-avoiding lattice path** with `n` steps: `c 0, …, c n` pairwise distinct, consecutive
points a unit step apart. (Values of `c` beyond `n` are irrelevant.) -/
structure LatticePath (n : ℕ) where
  c : ℕ → ℤ × ℤ
  injOn : InjOn c (Iic n)
  step : ∀ i, i < n → IsUnitStep (c i) (c (i + 1))

/-- The lattice point `(a, b)` placed in `E` at mesh `δ`. -/
def latticePt (e₁ e₂ : E) (δ : ℝ) (p : ℤ × ℤ) : E := δ • ((p.1 : ℝ) • e₁ + (p.2 : ℝ) • e₂)

/-- The midpoint of step `i` of the path. -/
def stepMid (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (i : ℕ) : E :=
  midpoint ℝ (latticePt e₁ e₂ δ (P.c i)) (latticePt e₁ e₂ δ (P.c (i + 1)))

/-- **The stretch triangle** of index `k`: the convex hull of `c k` and the midpoints of steps
`k - 1` and `k` (only the one midpoint at `k = 0` and `k = n`). -/
def stretchTri (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (k : ℕ) : Set E :=
  convexHull ℝ ({latticePt e₁ e₂ δ (P.c k)} ∪
    (if 0 < k then {stepMid e₁ e₂ δ P (k - 1)} else ∅) ∪
    (if k < n then {stepMid e₁ e₂ δ P k} else ∅))

/-- The polygonal path: the union of the steps as segments of `E`. -/
def polyPath (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) : Set E :=
  ⋃ i ∈ Iio n, segment ℝ (latticePt e₁ e₂ δ (P.c i)) (latticePt e₁ e₂ δ (P.c (i + 1)))

/-- Each stretch triangle lies in the closed `ℓ¹`-ball of radius `δ/2` about its lattice point;
in particular within `δ/2` of it. -/
theorem stretchTri_subset_ball {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) (k : ℕ) :
    stretchTri e₁ e₂ δ P k ⊆ closedBall (latticePt e₁ e₂ δ (P.c k)) (δ / 2) := by
  sorry

/-- Each stretch triangle lies within `δ/2` of the polygonal path. -/
theorem stretchTri_subset_thickening {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePath n) {k : ℕ} (hk : k ≤ n) :
    stretchTri e₁ e₂ δ P k ⊆ cthickening (δ / 2) (polyPath e₁ e₂ δ P) := by
  sorry

/-- **Separation of nonadjacent stretches.** For `k' ≥ k + 2` (both `≤ n`) the stretch triangles
are at distance at least `(√2/2) δ`. Two cases: the lattice points `c k`, `c k'` at `ℓ¹`-distance
`≥ 2` (then the `ℓ¹`-balls of radius `δ/2` are at `ℓ¹`-distance `≥ δ`, hence Euclidean `≥ δ/√2`);
or lattice-adjacent, `c k' = c k + e` — then neither path-neighbour of `c k` is `c k'` (the path is
self-avoiding and `|k - k'| ≥ 2`), so stretch `k` lies in the half-plane `⟪· - c k, e⟫ ≤ 0`, and
symmetrically stretch `k'` in `⟪· - c k, e⟫ ≥ δ`: distance `≥ δ`. -/
theorem stretchTri_separated {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {k k' : ℕ} (hk' : k' ≤ n) (h : k + 2 ≤ k') :
    ∀ p ∈ stretchTri e₁ e₂ δ P k, ∀ q ∈ stretchTri e₁ e₂ δ P k',
      Real.sqrt 2 / 2 * δ ≤ dist p q := by
  sorry

/-! ### The rounded path and its band -/

/-- **The rounded path** `Γ : ℝ → E`, parametrised by `τ ∈ [0, n]`: stretch `k` on
`[k - 1/2, k + 1/2]` — the straight segment from the midpoint of step `k-1` to the midpoint of
step `k` when the two steps have the same direction, the quarter circle of radius `δ/2` (centre
`c k - u/2 + u'/2` in lattice units) between the same two midpoints otherwise, both traversed at
constant speed in `τ`; the half-steps from `c 0` and to `c n` at the ends. (Definition is a work
item; any parametrisation with the properties below is acceptable, recorded.) -/
noncomputable def roundedPath (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) : ℝ → E := sorry

/-- **The left unit normal** `ν : ℝ → E` of the rounded path: the left normal `(a, b) ↦ (-b, a)`
of the step direction on straight stretches; on a quarter circle the radial unit vector, towards
the centre on a left turn and away from it on a right turn (so again the left normal of the
direction of motion); continuous on `[0, n]`, agreeing from both sides at the stretch boundaries
`k + 1/2`. -/
noncomputable def roundedNormal (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) : ℝ → E := sorry

theorem roundedPath_continuousOn {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) : ContinuousOn (roundedPath e₁ e₂ δ P) (Icc 0 n) := by
  sorry

theorem roundedNormal_continuousOn {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePath n) :
    ContinuousOn (roundedNormal e₁ e₂ δ P) (Icc 0 n) := by
  sorry

theorem norm_roundedNormal {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) n) :
    ‖roundedNormal e₁ e₂ δ P τ‖ = 1 := by
  sorry

/-- Stretch `k` of the rounded path lies in the stretch triangle `k`. -/
theorem roundedPath_mem_stretchTri {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePath n) {k : ℕ} (hk : k ≤ n) {τ : ℝ}
    (hτ : τ ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) (hτn : τ ∈ Icc (0 : ℝ) n) :
    roundedPath e₁ e₂ δ P τ ∈ stretchTri e₁ e₂ δ P k := by
  sorry

/-- **The band**: `(τ, t) ↦ Γ τ + (t δ) • ν τ`. -/
noncomputable def band (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (q : ℝ × ℝ) : E :=
  roundedPath e₁ e₂ δ P q.1 + (q.2 * δ) • roundedNormal e₁ e₂ δ P q.1

/-- **Injectivity of the band** on `[0, n] × (-1/8, 1/8)`. Within one stretch: an affine map on a
straight stretch; polar coordinates about the centre, radii in `(3δ/8, 5δ/8)`, angles in a
quarter turn, on a quarter circle. Adjacent stretches `k, k+1`: the band over stretch `k` lies in
the closed half-plane `⟪· - m_k, u_k⟫ ≤ 0` and that over stretch `k+1` in `⟪· - m_k, u_k⟫ ≥ 0`
(`m_k` the midpoint of step `k`, `u_k` its direction), and on the common line both are
`m_k + (t δ) • ν(k + 1/2)`. Nonadjacent stretches: `stretchTri_separated`, since each band point
is within `δ/8` of its stretch. -/
theorem band_injOn {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (P : LatticePath n) :
    InjOn (band e₁ e₂ δ P) (Icc (0 : ℝ) n ×ˢ Ioo (-1 / 8 : ℝ) (1 / 8)) := by
  sorry

theorem band_continuousOn {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) :
    ContinuousOn (band e₁ e₂ δ P) (Icc (0 : ℝ) n ×ˢ Ioo (-1 / 8 : ℝ) (1 / 8)) := by
  sorry

/-! ### The chain of a lattice path -/

/-- The threading map of the strip: `(x, y) ↦ band (λ x) ((y - 1/2)/4)`, `λ = n/(2m+1)`. -/
noncomputable def threadMap (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (m : ℕ) (p : Pt) :
    E :=
  band e₁ e₂ δ P ((n : ℝ) / (2 * m + 1) * p.1, (p.2 - 1 / 2) / 4)

/-- The link `j`: the open `δ/8`-neighbourhood of the rounded path over `τ ∈ [2λj, λ(2j+3)]`. -/
noncomputable def latticeLink (e₁ e₂ : E) (δ : ℝ) {n : ℕ} (P : LatticePath n) (m : ℕ) (j : ℕ) :
    Set E :=
  thickening (δ / 8) (roundedPath e₁ e₂ δ P ''
    Icc ((n : ℝ) / (2 * m + 1) * (2 * j)) ((n : ℝ) / (2 * m + 1) * (2 * j + 3)))

/-- **The chain of a lattice path** with `n` steps, `6m + 3 ≤ n < 6m + 9` (so `λ ∈ [3, 4)`):
links `latticeLink`; adjacent links share `Γ (λ (2j + 5/2))`; nonadjacent links have `τ`-ranges
`≥ λ ≥ 3` apart, hence meet only nonadjacent stretches, at distance `≥ (√2/2) δ > δ/4`. -/
noncomputable def latticeChain {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {m : ℕ} (h₁ : 6 * m + 3 ≤ n) (h₂ : n < 6 * m + 9) :
    Chain E m := sorry

theorem latticeChain_link {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (P : LatticePath n) {m : ℕ} (h₁ : 6 * m + 3 ≤ n) (h₂ : n < 6 * m + 9) (j : Fin m) :
    (latticeChain hon hδ P h₁ h₂).link j = latticeLink e₁ e₂ δ P m j := by
  sorry

theorem isThreadedChain_latticeChain {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (P : LatticePath n) {m : ℕ} (h₁ : 6 * m + 3 ≤ n) (h₂ : n < 6 * m + 9) :
    IsThreadedChain (latticeChain hon hδ P h₁ h₂) := by
  sorry

/-- **The band theorem.** A self-avoiding lattice path with `n ≥ 21` steps at mesh `δ` carries a
threaded chain of at least three links, each of diameter `≤ 16 δ`, whose union lies within `δ` of
the polygonal path and comes within `δ` of every lattice point of the path. -/
theorem exists_threadedChain_of_latticePath {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (hn : 21 ≤ n) (P : LatticePath n) :
    ∃ (m : ℕ) (D : Chain E m), 3 ≤ m ∧ IsThreadedChain D ∧
      (∀ j, diam (D.link j) ≤ 16 * δ) ∧
      D.union ⊆ thickening δ (polyPath e₁ e₂ δ P) ∧
      ∀ i, i ≤ n → ∃ x ∈ D.union, dist x (latticePt e₁ e₂ δ (P.c i)) ≤ δ := by
  sorry

end HPC.Plane
