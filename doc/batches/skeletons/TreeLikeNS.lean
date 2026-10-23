import HPC.Plane.Enc2
import HPC.Plane.Enc1Cyc
import HPC.Plane.Cyc2Circle
import HPC.Plane.Ingram68

/-!
# Batch 133: tree-like plane continua contain no separating continuum; Bing 1951 (Duke)
# Theorem 7 as printed

Skeleton. Save as `HPC/Plane/TreeLikeNS.lean` and add `import HPC.Plane.TreeLikeNS` at the end of
the root `HPC.lean`. Every `sorry` is a work item. Shapes may be adjusted, with the change
recorded. Fix the imports to what is needed.

## Why

Bing states Theorem 7 for a *tree-like* plane continuum ("In the proof of Theorem 6 we establish
the following result"). The proof of Theorem 6 uses the hypothesis "M contains no continuum which
separates the plane". So Bing's Theorem 7 rests on an unstated step: a tree-like plane continuum
contains no continuum that separates the plane. That step is `treeLike_nonseparating`. It is
classical (tree-like continua are acyclic, and Borsuk's separation theorem applies), but neither
Bing nor the repository proves it. With it, Theorem 7 holds as printed (`theorem7_1951_treeLike`),
and Theorem 6 becomes an equivalence (`isTreeLike_iff_nonseparating`).

## The argument (no Borsuk, no Brouwer: logarithms and the crossing parity of batch 125)

Identify `Pt` with `ℂ` (`toCpx`).

1. **A logarithm on a fine tree cover.** Let `G` be a tree chain, all of whose links have
   diameter `< ε` and lie at distance `> 8ε` from `p`. Then `z ↦ z − p` has a continuous logarithm
   on `⋃ G` (`exists_log_on_treeChain`).
   * Each link `A` lies in a ball `D_A = ball c_A (3ε)` (sup metric) that misses `p`. A convex set
     missing `p` carries a continuous branch of `log (z − p)`.
   * Induct by removing a leaf. A leaf link `A` meets exactly one other link `B`. The ball
     branches on `D_A` and `D_B` differ by a constant on the convex set `D_A ∩ D_B ⊇ A ∩ B`.
     Shift the branch on `A` by that constant.
   * Invariant: on each link `A`, the logarithm is the restriction of a branch defined on all of
     `D_A`. This handles disconnected links and disconnected `A ∩ B`.
   * Graph theory needed: the nerve of a tree chain is a tree (no circular subcollection, so no
     chordless cycle, so no cycle; coherent, so connected). A tree with at least two vertices has a
     leaf whose removal leaves a tree chain.
2. **No logarithm on a polygon around `p`** (`no_log_on_polygon`). Suppose `J = polygonOf v` is
   simple, `p ∈ polyInterior J`, and `L` is continuous on `J` with `exp (L z) = z − p`.
   * Along each edge `[vᵢ, vᵢ₊₁]` (which misses `p`), `Im (L vᵢ₊₁ − L vᵢ) = αᵢ`, the signed angle
     subtended at `p`, with `αᵢ ∈ (−π, π)`.
   * Telescoping around the closed polygon gives `Σ αᵢ = 0`.
   * With `θ(z) = arg (p − z)`, whose cut is the *east* ray from `p`, `αᵢ = θ(vᵢ₊₁) − θ(vᵢ) + 2π jᵢ`
     with `jᵢ ∈ {−1, 0, 1}`. Also `jᵢ` is odd exactly when the edge crosses the east ray in the
     half-open sense of `CrossesEast`.
   * So `0 = Σ jᵢ ≡ crossCount ≡ parity v p = 1 (mod 2)` (`polyInterior_eq_oddSet`). Contradiction.
3. **A polygon in `W` around `p`** (`exists_polygon_around`). Let `W` be open, `p ∉ W`, with the
   component of `p` in `Wᶜ` bounded.
   * Cut-wire theorem (`exists_split_of_no_continuum`, batch 132, in a compact subspace) on
     `F = Wᶜ ∩ closedBall 0 R`: `F = F₁ ⊔ F₂` with `p ∈ F₁` and `F₁ ⊆ ball 0 R`.
   * Grid at mesh `δ` well below the distance from `F₁` to `F₂ ∪ (ball 0 R)ᶜ`: the frontier of the
     grid union of `F₁` lies in `W`.
   * The batch-130 odd-set argument for a *point* `x ∈ M` of a bounded `M` gives a simple closed
     polygon `J` on the boundary graph with `x ∈ polyInterior J`
     (`exists_enclosing_polygon_pt`). This is the proof of `exists_enclosing_polygon` with
     `x₀ := x`, needing only that `M` is bounded.
4. **Assembly** (`treeLike_nonseparating`).
   * Suppose `K ⊆ M` separates the plane. Take `p` in a bounded component of `Kᶜ`, and put
     `d = infDist p K`.
   * Take a tree chain for `M` of mesh `ε < d / 16`. The links meeting `K` form a tree chain `G'`;
     it is coherent because `K` is connected.
   * `W = ⋃ G'` contains `K`, lies within `ε` of `K`, and misses `p`.
   * The component of `p` in `Wᶜ` lies in that of `p` in `Kᶜ`, so it is bounded.
   * Step 3 gives a polygon `J ⊆ W` around `p`. Step 1 gives a logarithm on `W`. Restricting it
     to `J` contradicts step 2.
-/

namespace HPC.Plane

open Set Metric

/-! ### 0. The definition of tree-like (edit to `Tree67.lean`, COMMISSION-batch133.md §1)

`IsTreeLike` as defined up to batch 132 asks `diam A < ε` of the links but not boundedness.
Mathlib's `diam` of an unbounded set is `0`, so `{univ}` is a tree chain of every mesh, and every
continuum, a circle included, is "tree-like". The old definition is kept here under a new name,
and its triviality is proved. `Tree67.lean`'s `IsTreeLike` gets `Bornology.IsBounded A`, as
`IsEpsChain` (snake-like) has. -/

/-- The definition of `IsTreeLike` up to batch 132 (links not required to be bounded). -/
def IsTreeLikeOld (M : Set Pt) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∀ ε : ℝ, 0 < ε → ∃ G : Finset (Set Pt), IsTreeChain G ∧
    (∀ A ∈ G, diam A < ε) ∧ M ⊆ ⋃ A ∈ G, A

/-- **The old definition is trivial**: every continuum satisfies it (`G = {univ}`; `univ` is
unbounded, so `diam univ = 0`). Hence `treeLike_nonseparating` was false for it (a circle). -/
theorem isTreeLikeOld_of_isContinuum {M : Set Pt} (hM : Fold.Q78.IsContinuum M) :
    IsTreeLikeOld M := by
  sorry

/-- `Pt = ℝ × ℝ` as complex numbers. -/
def toCpx (z : Pt) : ℂ := ⟨z.1, z.2⟩

theorem continuous_toCpx : Continuous toCpx := by
  sorry

/-! ### 1. A logarithm on a fine tree cover -/

/-- On a convex set missing `p` there is a continuous branch of `log (z − p)`. (For instance,
`Complex.log ((z − p) / (c − p)) + Complex.log (c − p)` on a ball around `c` small enough that
`(z − p) / (c − p)` stays in the right half-plane.) State it for the balls you use. -/
theorem exists_log_on_ball {p c : Pt} {r : ℝ} (hr : 0 < r) (hp : 4 * r < dist c p) :
    ∃ L : Pt → ℂ, ContinuousOn L (ball c r) ∧
      ∀ z ∈ ball c r, Complex.exp (L z) = toCpx z - toCpx p := by
  sorry

/-- The nerve of a tree chain is a tree. The form needed: a tree chain with at least two links has
a link `A` meeting exactly one other link `B`, such that `G.erase A` is again a tree chain. -/
theorem exists_leaf {G : Finset (Set Pt)} (hG : IsTreeChain G) (h2 : 2 ≤ G.card) :
    ∃ A ∈ G, ∃ B ∈ G, A ≠ B ∧ (A ∩ B).Nonempty ∧
      (∀ C ∈ G, C ≠ A → C ≠ B → Disjoint A C) ∧ IsTreeChain (G.erase A) := by
  sorry

/-- **A logarithm on a fine tree cover.** Suppose `G` is a tree chain, each link of `G` has
diameter `< ε`, and every point of every link is at distance `> 8 ε` from `p`. Then `z − p` has a
continuous logarithm on `⋃ G`. (Induction on `G.card` with the ball invariant of the header.) -/
theorem exists_log_on_treeChain {G : Finset (Set Pt)} (hG : IsTreeChain G) {ε : ℝ} (hε : 0 < ε)
    (hdiam : ∀ A ∈ G, Bornology.IsBounded A ∧ diam A < ε) {p : Pt}
    (hfar : ∀ A ∈ G, ∀ z ∈ A, 8 * ε < dist z p) :
    ∃ L : Pt → ℂ, ContinuousOn L (⋃ A ∈ G, A) ∧
      ∀ z ∈ ⋃ A ∈ G, A, Complex.exp (L z) = toCpx z - toCpx p := by
  sorry

/-! ### 2. No logarithm on a polygon around `p` -/

/-- **No logarithm on a simple closed polygon around `p`.** The angle sum is `0` by telescoping
and odd by the crossing parity (header, step 2; `parity`, `CrossesEast`, `polyInterior_eq_oddSet`).
-/
theorem no_log_on_polygon {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) {p : Pt}
    (hp : p ∈ polyInterior (polygonOf v)) :
    ¬ ∃ L : Pt → ℂ, ContinuousOn L (polygonOf v) ∧
      ∀ z ∈ polygonOf v, Complex.exp (L z) = toCpx z - toCpx p := by
  sorry

/-! ### 3. A polygon in an open set around a point -/

/-- **Batch 130 for a point.** For bounded `M`, `x ∈ M` and `δ > 0`, some simple closed polygon on
the boundary graph of the grid union has `x` in its interior. (The proof of
`exists_enclosing_polygon`, with `x₀ := x`.) -/
theorem exists_enclosing_polygon_pt {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ}
    (hδ : 0 < δ) {x : Pt} (hx : x ∈ M) :
    ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ J ⊆ graphSet (bdryGraph M δ) ∧ x ∈ polyInterior J := by
  sorry

/-- **A polygon in `W` around `p`.** Suppose `W` is open, `p ∉ W`, and the component of `p` in
`Wᶜ` is bounded. Then some simple closed polygon `J ⊆ W` has `p` in its interior. (Cut-wire, then
`exists_enclosing_polygon_pt` and `frontier_gridUnion`.) -/
theorem exists_polygon_around {W : Set Pt} (hW : IsOpen W) {p : Pt} (hp : p ∉ W)
    (hb : Bornology.IsBounded (connectedComponentIn Wᶜ p)) :
    ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ J ⊆ W ∧ p ∈ polyInterior J := by
  sorry

/-! ### 4. Assembly -/

/-- If a compact `K` separates the plane, some point off `K` has a bounded component in `Kᶜ`.
(The complement of a large closed ball is connected and lies in one component of `Kᶜ`.) -/
theorem exists_bounded_component_of_separates {K : Set Pt} (hK : IsCompact K)
    (hs : SeparatesPlane K) :
    ∃ p, p ∉ K ∧ Bornology.IsBounded (connectedComponentIn Kᶜ p) := by
  sorry

/-- The links of a tree chain that meet a continuum `K` form a tree chain (coherence: `K` is
connected, and two subcollections with no meeting links would split `K`). -/
theorem isTreeChain_filter_meet {G : Finset (Set Pt)} (hG : IsTreeChain G) {K : Set Pt}
    (hK : IsConnected K) (hKG : K ⊆ ⋃ A ∈ G, A) :
    IsTreeChain (G.filter fun A => (A ∩ K).Nonempty) := by
  sorry

/-- **A tree-like plane continuum contains no continuum that separates the plane.** The unstated
step of Bing 1951 (Duke), Theorem 7 (header). -/
theorem treeLike_nonseparating {M : Set Pt} (hM : IsTreeLike M) :
    ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K := by
  sorry

/-- **Bing 1951 (Duke), Theorem 7, as printed.** If `M` is a tree-like plane continuum and
`ε > 0`, there is a tree chain covering `M` whose links are the interiors of simple closed curves
(here: polygons) of diameters less than `ε`. -/
theorem theorem7_1951_treeLike {M : Set Pt} (hM : IsTreeLike M) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧
      (∀ h ∈ G, ∃ Γ : Set Pt, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ) ∧
      (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h :=
  theorem7_1951 hM.1 (treeLike_nonseparating hM) hε

/-- **Theorem 6 and its converse.** A bounded plane continuum is tree-like iff it contains no
continuum that separates the plane. -/
theorem isTreeLike_iff_nonseparating {M : Set Pt} (hM : Fold.Q78.IsContinuum M) :
    IsTreeLike M ↔ ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K :=
  ⟨fun h => treeLike_nonseparating h, fun h => theorem6_1951 hM h⟩

end HPC.Plane
