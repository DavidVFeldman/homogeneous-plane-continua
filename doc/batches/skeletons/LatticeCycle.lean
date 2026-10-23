import HPC.Plane.BandChain

/-!
# Batch 110: a self-avoiding lattice cycle through the squares meeting a plane continuum, and the
# density lemma in the plane

Skeleton (save as `HPC/Plane/LatticeCycle.lean`; add `import HPC.Plane.LatticeCycle` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded. No existing file is to be edited, except the audit.

Second half of the density lemma (first half: batch 109, `Band.lean`, `BandChain.lean`).

Conventions. Squares are indexed by `s : ℤ × ℤ`; square `s` is `[s.1, s.1 + 1] × [s.2, s.2 + 1]` in
units of the side `δ`. The fine lattice has mesh `δ/8`, so in fine coordinates square `s` is
`[8 s.1, 8 s.1 + 8] × [8 s.2, 8 s.2 + 8]` and its *depth-1 points* are those with both coordinates
strictly inside. Two squares are *adjacent* when their indices differ by a unit step (they share a
side). A finite set of squares is *connected* when it has no nonempty proper subset closed under
adjacency within the set.

The cycle (item 2). Enumerate a connected finite set `T` as `s₁, …, s_N` with each `s_k` (`k ≥ 2`)
adjacent to an earlier one. Start with the depth-1 loop of `s₁` (`24` steps: the boundary of
`[1, 7]²` inside the square in fine coordinates). Invariant for the current set `T_k`: (a) for every
`s ∈ T_k` and every side `σ` of `s` not shared with a square of `T_k`, the seven depth-1 points of
`s` along `σ` (the row at distance `1` from `σ`, between the two depth-1 corners) are consecutive on
the cycle; (b) every cycle point is a depth-1 point of some square of `T_k`, or lies on a side shared
by two squares of `T_k` at offset `1` or `7` from a corner; (c) the four depth-1 corners of every
square of `T_k` are on the cycle. Step: `s_{k+1} = ℓ` is adjacent to some `s ∈ T_k` across the side
`σ`, which is not shared within `T_k`; by (a) the row of `s` along `σ` is consecutive; replace its
five interior points by the detour: the point of `σ` at offset `1`, the depth-1 point of `ℓ` beyond
it, the depth-1 loop of `ℓ` minus its own `σ`-row (from that point around to the point at offset
`7`), the point of `σ` at offset `7`, and back to the row's last point. The new points are depth-1
points of `ℓ` or on `σ`; by (b) no old point is one of these (interiors of distinct squares are
disjoint; sides meet only at corners, which are never cycle points), so the cycle stays
self-avoiding; (a)–(c) hold for `T_{k+1}` (`σ` is no longer free; the rows of `ℓ` along its other
sides are consecutive in the detour). The cycle grows by `16` steps per square.
-/

namespace HPC.Plane

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Polyominoes and the cycle -/

/-- A finite set of squares is **connected** (edge-adjacency: indices a unit step apart). -/
def PolyConnected (T : Finset (ℤ × ℤ)) : Prop :=
  ∀ A : Finset (ℤ × ℤ), A ⊆ T → A.Nonempty →
    (∀ s ∈ A, ∀ s' ∈ T, IsUnitStep s s' → s' ∈ A) → A = T

/-- The fine lattice point `p` lies in the closed square `s` (fine coordinates, mesh `1/8`). -/
def InSq (s p : ℤ × ℤ) : Prop :=
  8 * s.1 ≤ p.1 ∧ p.1 ≤ 8 * s.1 + 8 ∧ 8 * s.2 ≤ p.2 ∧ p.2 ≤ 8 * s.2 + 8

/-- The fine lattice point `p` is a depth-1 point of the square `s` (strictly inside). -/
def InSqInt (s p : ℤ × ℤ) : Prop :=
  8 * s.1 < p.1 ∧ p.1 < 8 * s.1 + 8 ∧ 8 * s.2 < p.2 ∧ p.2 < 8 * s.2 + 8

/-- A connected finite set of squares has a connected enumeration: a bijection `Fin N → T` in which
every square after the first is adjacent to an earlier one. -/
theorem exists_connected_enumeration (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (hc : PolyConnected T) :
    ∃ (N : ℕ) (e : ℕ → ℤ × ℤ), N = T.card ∧ InjOn e (Iio N) ∧ (∀ i < N, e i ∈ T) ∧
      ∀ k, 0 < k → k < N → ∃ j < k, IsUnitStep (e j) (e k) := by
  sorry

/-- **The self-avoiding lattice cycle.** For a nonempty connected finite set `T` of squares there
is a self-avoiding closed lattice path on the fine lattice, of length `L ≥ 24`, inside the union of
the closed squares, with a depth-1 point in every square. (`c i` for `i ≥ L` is irrelevant.) -/
theorem exists_latticeCycle (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (hc : PolyConnected T) :
    ∃ (L : ℕ) (c : ℕ → ℤ × ℤ), 24 ≤ L ∧ InjOn c (Iio L) ∧
      (∀ i, i + 1 < L → IsUnitStep (c i) (c (i + 1))) ∧ IsUnitStep (c (L - 1)) (c 0) ∧
      (∀ i < L, ∃ s ∈ T, InSq s (c i)) ∧
      ∀ s ∈ T, ∃ i < L, InSqInt s (c i) := by
  sorry

/-- The cycle minus its closing step: a `LatticePath` with `n = L - 1 ≥ 23` steps. -/
theorem exists_latticePath_of_polyomino (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (hc : PolyConnected T) :
    ∃ (n : ℕ) (P : LatticePath n), 23 ≤ n ∧
      (∀ i ≤ n, ∃ s ∈ T, InSq s (P.c i)) ∧
      ∀ s ∈ T, ∃ i ≤ n, InSqInt s (P.c i) := by
  sorry

/-! ### The squares meeting a plane continuum -/

/-- The closed square `s` of side `δ` in the `(e₁, e₂)`-plane. -/
def sqSet (e₁ e₂ : E) (δ : ℝ) (s : ℤ × ℤ) : Set E :=
  {x | δ * s.1 ≤ inner ℝ x e₁ ∧ inner ℝ x e₁ ≤ δ * (s.1 + 1) ∧
    δ * s.2 ≤ inner ℝ x e₂ ∧ inner ℝ x e₂ ≤ δ * (s.2 + 1)}

/-- The squares meeting `g`. -/
def squaresMeeting (e₁ e₂ : E) (δ : ℝ) (g : Set E) : Set (ℤ × ℤ) :=
  {s | (sqSet e₁ e₂ δ s ∩ g).Nonempty}

/-- A two-dimensional real inner product space has an orthonormal pair spanning it. -/
theorem exists_orthonormal_pair_span [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    ∃ e₁ e₂ : E, Orthonormal ℝ ![e₁, e₂] ∧
      ∀ x : E, x = (inner ℝ x e₁) • e₁ + (inner ℝ x e₂) • e₂ := by
  sorry

/-- In the plane, a bounded set meets finitely many squares. -/
theorem squaresMeeting_finite {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {g : Set E} (hg : Bornology.IsBounded g) : (squaresMeeting e₁ e₂ δ g).Finite := by
  sorry

/-- In the plane, every point lies in some square. -/
theorem exists_sq_mem {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂])
    (hspan : ∀ x : E, x = (inner ℝ x e₁) • e₁ + (inner ℝ x e₂) • e₂) {δ : ℝ} (hδ : 0 < δ)
    (x : E) : ∃ s, x ∈ sqSet e₁ e₂ δ s := by
  sorry

/-- A square of side `δ` has diameter `δ √2` (in the plane; `≤ 2 δ` is enough). -/
theorem diam_sqSet_le {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂])
    (hspan : ∀ x : E, x = (inner ℝ x e₁) • e₁ + (inner ℝ x e₂) • e₂) {δ : ℝ} (hδ : 0 < δ)
    (s : ℤ × ℤ) : ∀ x ∈ sqSet e₁ e₂ δ s, ∀ y ∈ sqSet e₁ e₂ δ s, dist x y ≤ 2 * δ := by
  sorry

/-- A fine lattice point in the closed square `s` (fine coordinates) is in `sqSet s`, and a
depth-1 point is in it too. -/
theorem latticePt_mem_sqSet {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂]) {δ : ℝ} (hδ : 0 < δ)
    {s p : ℤ × ℤ} (h : InSq s p) : latticePt e₁ e₂ (δ / 8) p ∈ sqSet e₁ e₂ δ s := by
  sorry

/-- **The squares meeting a connected set are connected.** If `T = A ⊔ B` with no adjacency
between `A` and `B`, then `g ∩ ⋃ A` and `g ∩ ⋃ B` are closed, cover `g`, and are nonempty, so
they share a point `x ∈ g` lying in some `s_A ∈ A` and `s_B ∈ B`; `s_A ∩ s_B` is a side (then they
are adjacent) or a single corner `x`; in the latter case the other two squares at that corner
contain `x ∈ g`, so lie in `T`, and each is adjacent to both `s_A` and `s_B`. -/
theorem squaresMeeting_connected {e₁ e₂ : E} (hon : Orthonormal ℝ ![e₁, e₂])
    (hspan : ∀ x : E, x = (inner ℝ x e₁) • e₁ + (inner ℝ x e₂) • e₂) {δ : ℝ} (hδ : 0 < δ)
    {g : Set E} (hg : IsConnected g) (hfin : (squaresMeeting e₁ e₂ δ g).Finite) :
    PolyConnected hfin.toFinset := by
  sorry

/-! ### Assembly -/

/-- **The density lemma in the plane** (threaded form). Take `δ = ε/4`; the squares of side `δ`
meeting `g`; the lattice path of `exists_latticePath_of_polyomino` at fine mesh `δ/8`; the chain
of `exists_threadedChain_of_latticePath`. Links have diameter `≤ 16 (δ/8) = ε/2`; the union is
within `δ/8` of the polygonal path, which lies in the union of the closed squares, each meeting `g`
and of diameter `≤ 2δ`; every `x ∈ g` lies in a square, which has a depth-1 point of the path,
within `δ/8` of the union. -/
theorem geomLemma'_of_finrank_two [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    GeomLemma' E := by
  sorry

/-- **Density of pseudo-arcs in the plane.** -/
theorem dense_pseudoArcs_plane [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} := by
  sorry

/-- **Bing 1951 (Pacific), Theorem 2, in the plane**: the pseudo-arcs form a dense `G_δ` in the
space of compact continua of a two-dimensional real inner product space. -/
theorem theorem2_HIC_plane [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    Dense {K : Cont E | IsPseudoArc (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsPseudoArc (K.1 : Set E)} := by
  sorry

/-- The snake-like continua form a `G_δ` in `C(S)` (complement of the union of the closed sets
`isClosed_notCoverable i`, via `Most.isSnakeLike_iff`). -/
theorem isGδ_snakeLike {S : Type*} [MetricSpace S] :
    IsGδ {K : Cont S | IsSnakeLike (K.1 : Set S)} := by
  sorry

/-- Density of snake-like continua in the plane (pseudo-arcs are snake-like). -/
theorem dense_snakeLike_plane [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    Dense {K : Cont E | IsSnakeLike (K.1 : Set E)} := by
  sorry

/-- **Bing 1951 (Duke), Theorem 2, in the plane**: "most" compact continua are snake-like — the
snake-like continua form a dense `G_δ` in the space of compact continua. -/
theorem theorem2_1951_plane [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 2) :
    Dense {K : Cont E | IsSnakeLike (K.1 : Set E)} ∧
      IsGδ {K : Cont E | IsSnakeLike (K.1 : Set E)} := by
  sorry

end HPC.Plane
