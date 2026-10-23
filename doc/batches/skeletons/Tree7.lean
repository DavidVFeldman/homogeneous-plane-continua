import HPC.Plane.Tree6

/-!
# Batch 119: Bing 1951 (Duke), Theorem 7 — the links as interiors of simple closed polygons (I)

Skeleton. Every `sorry` is a work item; shapes may be adjusted with the change recorded. Save as
`HPC/Plane/Tree7.lean`, add `import HPC.Plane.Tree7` at the end of the root `HPC.lean`. No existing
file is to be edited except `Axioms.lean`/`axioms.txt`.

**Theorem 7 (p. 657).** *If `M` is a tree-like plane continuum and `ε` is a positive number, there is
a tree-chain covering `M` whose links are the interiors of simple closed curves of diameters less
than `ε`.* Bing: "In the proof of Theorem 6 we establish the following result." The two sentences
of that proof which carry Theorem 7 are

> "Let `H` be the collection of all interiors `h` of simple closed curves such that `h` is a
> component of the intersection of `d_0` and one of the `d_i`'s"

(that the components ARE interiors of simple closed curves is asserted, not argued; it is true, but
its proof needs either the classification of compact polygonal 1-manifolds or a general-position
argument — the second is what this file and batch 120 do), and the hypothesis "tree-like", where
the proof of Theorem 6 uses "contains no continuum separating the plane" (item 5).

Plan of this batch:

1. **The links of Theorem 6, elementary properties, and Theorem 7 in weak form.** The members of
   `compFamily (polyInterior J) D` are bounded, open, connected, regular open (the interior of their
   closure), and have connected complement (they do not separate the plane). `theorem7_weak`.
   The proof of `theorem6_1951` is refactored into `treeChain_of_cover` (any simple closed polygon
   `J ⊇ M` and any no-triple bounded open cover `D` of `polyInterior J`) so that batch 120 can feed
   it the general-position cover.
2. **The notched square is the interior of an explicit 20-gon** `notchedPoly` (unconditional:
   `polyInterior_eq_of_split`).
3. **General position by translation.** Once `J` is chosen (`enclose`), the whole notched cover is
   translated by a small `t`; the covering of `closure (polyInterior J)` survives (Lebesgue number),
   and the bad `t` form a finite union of closed nowhere dense sets.
4. **Cross-cuts.** Splitting a simple closed polygon at two points, joining two arcs into a simple
   closed polygon, and the **cross-cut theorem** `PlaneFacts.crosscut`: a simple polygonal arc `c`
   inside `polyInterior J` with its two ends on `J` splits `polyInterior J` into the interiors of
   the two simple closed polygons `α₁ ∪ c`, `α₂ ∪ c` (`J = α₁ ∪ α₂`).
5. **The hypothesis** (reconnaissance, no `sorry`): see the commission.

Batch 120: the cross-cut induction (components of `polyInterior J ∖ ⋃ c̄_j` are polygon interiors),
the crossing structure of `notchedPoly` against `J` in general position (the components of
`notchedPoly ∩ polyInterior J` are pairwise disjoint cross-cuts), the identification of the
components of `polyInterior J ∩ notched` with the components of `polyInterior J ∖ notchedPoly` lying
in `notched`, and `theorem7_1951`.

The plane is `Pt = ℝ × ℝ` with the sup metric, as in `Tree67`/`Tree6`.
-/

namespace HPC.Plane

open Set Metric

open scoped Classical

/-! ### 1. The links of Theorem 6 -/

/-- The notched squares of the index set `I`. -/
def notchedFamily (o : Pt) (δ η r : ℝ) (I : Finset (ℤ × ℤ)) : Finset (Set Pt) :=
  I.image fun ab => notched o δ η r ab.1 ab.2

/-- `exists_notched_cover_bdd` (batch 118) with the parameters exposed: the cover is
`notchedFamily o δ η r I` with `0 < η < r`, `4 r ≤ δ ≤ ε / 2`. (The constants of
`exists_notched_cover`: `δ = ε/2`, `r = min (r₀/2) (δ/4)`, `η = r/2`; `I` = the indices of the grid
squares meeting `M`. Same proof; state the constants actually obtained if they differ.) -/
theorem exists_notched_cover_param {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (o : Pt) (δ η r : ℝ) (I : Finset (ℤ × ℤ)), 0 < η ∧ η < r ∧ 4 * r ≤ δ ∧ δ ≤ ε / 2 ∧
      (∀ d ∈ notchedFamily o δ η r I, diam d < ε) ∧
      M ⊆ ⋃ d ∈ notchedFamily o δ η r I, d ∧
      ∀ d₁ ∈ notchedFamily o δ η r I, ∀ d₂ ∈ notchedFamily o δ η r I,
        ∀ d₃ ∈ notchedFamily o δ η r I, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅ := by
  sorry

/-- A notched square is bounded (`notched_subset_box`). -/
theorem isBounded_notched (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r) (a b : ℤ) :
    Bornology.IsBounded (notched o δ η r a b) := by
  sorry

/-- A notched square is connected: it is star-shaped with respect to the centre of the square
(each of its three open rectangles is convex and contains the centre). -/
theorem isConnected_notched (o : Pt) {δ η r : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) : IsConnected (notched o δ η r a b) := by
  sorry

/-- The complement of a notched square is connected and unbounded. (Star-shapedness again: if
`x ∉ N` and `y` lies on the ray from the centre `c` through `x` beyond `x`, then `y ∉ N`, since
`y ∈ N` would put the segment `[c, y] ∋ x` in `N`. So every point of `Nᶜ` is joined inside `Nᶜ` by a
ray to the complement of a large box, which is connected.) -/
theorem isConnected_compl_notched (o : Pt) {δ η r : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) :
    IsConnected (notched o δ η r a b)ᶜ ∧ ¬ Bornology.IsBounded (notched o δ η r a b)ᶜ := by
  sorry

/-- A notched square is regular open: `interior (closure N) = N`. (Every boundary point of `N` is
a limit of points of the interior of `Nᶜ`: on the sides of the square within `r` of a corner, the
points just outside; on the ends of the strips, the points just beyond the end; the `r`-corners
`(x₀ + r, y₀)` etc. are limits of points below-left.) -/
theorem regular_notched (o : Pt) {δ η r : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hηr : η < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) :
    interior (closure (notched o δ η r a b)) = notched o δ η r a b := by
  sorry

/-- The interior of a simple closed polygon is regular open (`jct`: `closure U = U ∪ J`, and a
point of `J` is in the closure of the exterior `V`, which is open and misses `U ∪ J`). -/
theorem PlaneFacts.polyInterior_regular (hPF : PlaneFacts) {J : Set Pt}
    (hJ : IsSimpleClosedPolygon J) :
    interior (closure (polyInterior J)) = polyInterior J := by
  sorry

/-- Members of `compFamily` are bounded when `d₀` is. -/
theorem compFamily_isBounded {d₀ : Set Pt} {D : Finset (Set Pt)} (hd₀ : Bornology.IsBounded d₀)
    {h : Set Pt} (hh : h ∈ compFamily d₀ D) : Bornology.IsBounded h := by
  sorry

/-- **Members of `compFamily` are regular open** when `d₀` and the members of `D` are.
(`interior (closure h) ⊆ interior (closure (d₀ ∩ d)) ⊆ interior (closure d₀) ∩ interior (closure d)
= d₀ ∩ d`; a point of `d₀ ∩ d` in the closure of the component `h` lies in `h`, since its own
component is open — `mem_connectedComponentIn_of_mem_closure`, batch 118.) -/
theorem compFamily_regular {d₀ : Set Pt} {D : Finset (Set Pt)} (hd₀ : IsOpen d₀)
    (hopen : ∀ d ∈ D, IsOpen d) (hreg₀ : interior (closure d₀) = d₀)
    (hreg : ∀ d ∈ D, interior (closure d) = d) {h : Set Pt} (hh : h ∈ compFamily d₀ D) :
    interior (closure h) = h := by
  sorry

/-- **Members of `compFamily` do not separate the plane.** With `O = d₀ ∩ d`: `Oᶜ = d₀ᶜ ∪ dᶜ` is
connected (both connected and unbounded; `d₀` bounded, so they meet). Every other component `C` of
`O` is a nonempty bounded open set, so its frontier is nonempty, and `frontier C ⊆ Oᶜ` (a point of
`O` in `closure C` lies in `C`, components of open sets being open); hence `closure C ∪ Oᶜ` is
connected, and `hᶜ = Oᶜ ∪ ⋃ (closure C)` over the other components is connected. -/
theorem compFamily_compl_connected {d₀ : Set Pt} {D : Finset (Set Pt)} (hd₀ : IsOpen d₀)
    (hd₀b : Bornology.IsBounded d₀) (hopen : ∀ d ∈ D, IsOpen d)
    (hc₀ : IsConnected d₀ᶜ) (hu₀ : ¬ Bornology.IsBounded d₀ᶜ)
    (hc : ∀ d ∈ D, IsConnected dᶜ ∧ ¬ Bornology.IsBounded dᶜ)
    {h : Set Pt} (hh : h ∈ compFamily d₀ D) : ¬ SeparatesPlane h := by
  sorry

/-- **The tail of the proof of Theorem 6, factored out**: for any simple closed polygon `J` with
`M ⊆ polyInterior J` and any bounded open no-triple cover `D` of `polyInterior J` with links of
diameter `< ε`, a finite family of members of `compFamily (polyInterior J) D` is a tree chain of
mesh `< ε` covering `M`, each member containing a point of `M`. (The proof of `theorem6_1951` from
"`set d₀ := polyInterior J`" on, verbatim; `theorem6_1951` itself is not to be edited.) -/
theorem treeChain_of_cover (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    {J : Set Pt} (hJ : IsSimpleClosedPolygon J) (hMJ : M ⊆ polyInterior J)
    {D : Finset (Set Pt)} (hopen : ∀ d ∈ D, IsOpen d) (hbdd : ∀ d ∈ D, Bornology.IsBounded d)
    {ε : ℝ} (hdiam : ∀ d ∈ D, diam d < ε) (hcov : polyInterior J ⊆ ⋃ d ∈ D, d)
    (htriple : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅) :
    ∃ G : Finset (Set Pt), (∀ h ∈ G, h ∈ compFamily (polyInterior J) D) ∧ IsTreeChain G ∧
      (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h ∧ ∀ h ∈ G, (h ∩ M).Nonempty := by
  sorry

/-- **Theorem 7, weak form**: the links of the tree chain of Theorem 6 are bounded, open,
connected, regular open, and do not separate the plane. (`exists_notched_cover_param`, `enclose`
with `G = ⋃ D`, `treeChain_of_cover`, and the properties above with `compFamily_props`;
`isConnected_compl_notched`, `regular_notched`, `compl_polyInterior`, `polyInterior_regular`.) -/
theorem theorem7_weak (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Set Pt), IsTreeChain G ∧ (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h ∧
      ∀ h ∈ G, IsOpen h ∧ IsConnected h ∧ Bornology.IsBounded h ∧
        interior (closure h) = h ∧ ¬ SeparatesPlane h := by
  sorry

/-! ### 2. The notched square as the interior of a 20-gon -/

/-- The twenty vertices of the boundary of `notched o δ η r a b`, counterclockwise from the
bottom-left corner `(x₀, y₀)` of the square, `x₀ = o.1 + δ a`, `x₁ = x₀ + δ`, `y₀ = o.2 + δ b`,
`y₁ = y₀ + δ`:

    (x₀,y₀) (x₀+r,y₀) (x₀+r,y₀−η) (x₁−r,y₀−η) (x₁−r,y₀) (x₁,y₀)        -- bottom side, strip below
    (x₁,y₀+r) (x₁+η,y₀+r) (x₁+η,y₁−r) (x₁,y₁−r) (x₁,y₁)                 -- right side, strip right
    (x₁−r,y₁) (x₁−r,y₁+η) (x₀+r,y₁+η) (x₀+r,y₁) (x₀,y₁)                 -- top side, strip above
    (x₀,y₁−r) (x₀−η,y₁−r) (x₀−η,y₀+r) (x₀,y₀+r)                         -- left side, strip left

(Requires `0 < η`, `0 < r`, `2 r < δ` for the vertices to be distinct and the polygon simple.) -/
def notchedVertices (o : Pt) (δ η r : ℝ) (a b : ℤ) : Fin 20 → Pt :=
  let x₀ : ℝ := o.1 + δ * a
  let x₁ : ℝ := o.1 + δ * (a + 1)
  let y₀ : ℝ := o.2 + δ * b
  let y₁ : ℝ := o.2 + δ * (b + 1)
  ![(x₀, y₀), (x₀ + r, y₀), (x₀ + r, y₀ - η), (x₁ - r, y₀ - η), (x₁ - r, y₀), (x₁, y₀),
    (x₁, y₀ + r), (x₁ + η, y₀ + r), (x₁ + η, y₁ - r), (x₁, y₁ - r), (x₁, y₁),
    (x₁ - r, y₁), (x₁ - r, y₁ + η), (x₀ + r, y₁ + η), (x₀ + r, y₁), (x₀, y₁),
    (x₀, y₁ - r), (x₀ - η, y₁ - r), (x₀ - η, y₀ + r), (x₀, y₀ + r)]

/-- The boundary polygon of a notched square. -/
def notchedPoly (o : Pt) (δ η r : ℝ) (a b : ℤ) : Set Pt :=
  polygonOf (notchedVertices o δ η r a b)

/-- The 20-gon is a simple closed polygon (its edges are axis-parallel; a finite check). -/
theorem isSimpleClosedPolygon_notchedPoly (o : Pt) {δ η r : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hr : 0 < r) (h4 : 4 * r ≤ δ) (a b : ℤ) : IsSimpleClosedPolygon (notchedPoly o δ η r a b) := by
  sorry

/-- The frontier of a notched square is its boundary polygon. -/
theorem frontier_notched (o : Pt) {δ η r : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) : frontier (notched o δ η r a b) = notchedPoly o δ η r a b := by
  sorry

/-- **The notched square is the interior of its boundary polygon** — unconditional, by
`polyInterior_eq_of_split` with `U = notched`, `V = (closure notched)ᶜ` (`V` connected and unbounded
by the star-shapedness of `closure notched`; `Pᶜ = U ∪ V` by `frontier_notched`). -/
theorem notched_eq_polyInterior (o : Pt) {δ η r : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) :
    notched o δ η r a b = polyInterior (notchedPoly o δ η r a b) := by
  sorry

/-! ### 3. General position by translation -/

/-- Edge `i` of the closed polygon with vertices `v` (indices mod `n`). -/
def polyEdge {n : ℕ} (v : Fin n → Pt) (i : Fin n) : Set Pt :=
  segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)

/-- The vertex-level form of `IsSimpleClosedPolygon` (its body): at least three distinct vertices,
adjacent edges meeting only at their common vertex, non-adjacent edges disjoint. -/
def IsSimpleVertices {n : ℕ} (v : Fin n → Pt) : Prop :=
  3 ≤ n ∧ Function.Injective v ∧
    ∀ i j : Fin n, i ≠ j →
      (((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) →
        polyEdge v i ∩ polyEdge v j ⊆ {v i, v j, v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩}) ∧
      (¬ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) →
        Disjoint (polyEdge v i) (polyEdge v j))

theorem isSimpleClosedPolygon_iff {J : Set Pt} :
    IsSimpleClosedPolygon J ↔ ∃ (n : ℕ) (v : Fin n → Pt), IsSimpleVertices v ∧ J = polygonOf v := by
  sorry

/-- **General position** of two closed polygons given by their vertices: no vertex of either lies
on the other, and two edges that meet are not parallel. (Then two meeting edges cross in exactly one
point, interior to both, and `polygonOf v ∩ polygonOf w` is finite.) -/
def InGeneralPosition {n k : ℕ} (v : Fin n → Pt) (w : Fin k → Pt) : Prop :=
  (∀ i, v i ∉ polygonOf w) ∧ (∀ j, w j ∉ polygonOf v) ∧
    ∀ i j, (polyEdge v i ∩ polyEdge w j).Nonempty →
      ¬ ∃ c : ℝ, v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i =
        c • (w ⟨(j.val + 1) % k, Nat.mod_lt _ (Fin.pos j)⟩ - w j)

/-- In general position two polygons meet in a finite set. -/
theorem finite_inter_of_gp {n k : ℕ} {v : Fin n → Pt} {w : Fin k → Pt}
    (hgp : InGeneralPosition v w) : (polygonOf v ∩ polygonOf w).Finite := by
  sorry

/-- Translating a notched square translates its vertices. -/
theorem notched_translate (o t : Pt) (δ η r : ℝ) (a b : ℤ) :
    notched (o + t) δ η r a b = (fun p => p + t) '' notched o δ η r a b := by
  sorry

theorem notchedVertices_translate (o t : Pt) (δ η r : ℝ) (a b : ℤ) :
    notchedVertices (o + t) δ η r a b = fun i => notchedVertices o δ η r a b i + t := by
  sorry

/-- **Lebesgue number for translation**: a compact `K` inside an open `G` stays inside every
translate of `G` by a small vector. (`IsCompact.exists_thickening_subset_open`: `thickening λ K ⊆ G`;
then `p ∈ K`, `dist t 0 < λ` give `p - t ∈ G`.) -/
theorem subset_translate_of_compact {K G : Set Pt} (hK : IsCompact K) (hG : IsOpen G)
    (hKG : K ⊆ G) : ∃ l > 0, ∀ t : Pt, dist t 0 < l → K ⊆ (fun p => p + t) '' G := by
  sorry

/-- **A small translation puts the notched squares in general position with a given polygon.**
The bad translations `t` are: (i) a vertex `v i` on a translated boundary line of some notched
square — the boundary lines are `x = o.1 + δ a + s + t.1` and `y = o.2 + δ b + s' + t.2` with
`s, s' ∈ {-η, 0, r, δ - r, δ, δ + η}`, so finitely many values of `t.1` or `t.2` are excluded, i.e.
finitely many lines in the `t`-plane; (ii) a translated vertex `w j + t` of a notched square on
`polygonOf v`, i.e. `t ∈ polygonOf v - w j`: finitely many translates of a nowhere dense closed set;
(iii) an edge of `v` parallel to (hence, if they meet, collinear with) a boundary line: for an
axis-parallel edge of `v` finitely many values of `t.1` or `t.2` are excluded; a non-axis-parallel
edge is never parallel to an axis-parallel one. The union of finitely many closed nowhere dense sets
is closed nowhere dense, so the open disk `ball 0 l` is not contained in it. -/
theorem exists_gp_translation {n : ℕ} (v : Fin n → Pt) (o : Pt) {δ η r : ℝ} (hδ : 0 < δ)
    (hη : 0 < η) (hr : 0 < r) (h4 : 4 * r ≤ δ) (I : Finset (ℤ × ℤ)) {l : ℝ} (hl : 0 < l) :
    ∃ t : Pt, dist t 0 < l ∧
      ∀ ab ∈ I, InGeneralPosition v (notchedVertices (o + t) δ η r ab.1 ab.2) := by
  sorry

/-- **The general-position cover** (the input of batch 120): a simple closed polygon `J =
polygonOf v` around `M`, missing `M`, and a notched cover `notchedFamily o δ η r I` of
`polyInterior J` with links of diameter `< ε`, no triple points, every notched square in general
position with `v`. (Proof: `exists_notched_cover_param` gives `o₀ δ η r I`; `enclose` with
`G = ⋃ notchedFamily o₀ …` gives `J`; `closure (polyInterior J) = polyInterior J ∪ J` is compact in
`G` (`PlaneFacts.split`), so `subset_translate_of_compact` gives `l`; `exists_gp_translation` gives
`t`, and `o := o₀ + t`. Diameters, boundedness and no-triple are translation invariant
(`notched_translate`); `M ⊆ polyInterior J ⊆ ⋃ (translated family)`.) -/
theorem PlaneFacts.exists_gp_cover (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (v : Fin n → Pt) (o : Pt) (δ η r : ℝ) (I : Finset (ℤ × ℤ)),
      IsSimpleVertices v ∧ M ⊆ polyInterior (polygonOf v) ∧ Disjoint (polygonOf v) M ∧
      0 < η ∧ η < r ∧ 4 * r ≤ δ ∧ δ ≤ ε / 2 ∧
      polyInterior (polygonOf v) ⊆ ⋃ d ∈ notchedFamily o δ η r I, d ∧
      (∀ d ∈ notchedFamily o δ η r I, diam d < ε) ∧
      (∀ d₁ ∈ notchedFamily o δ η r I, ∀ d₂ ∈ notchedFamily o δ η r I,
        ∀ d₃ ∈ notchedFamily o δ η r I, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅) ∧
      ∀ ab ∈ I, InGeneralPosition v (notchedVertices o δ η r ab.1 ab.2) := by
  sorry

/-! ### 4. Cross-cuts -/

/-- **Splitting a simple closed polygon at two of its points** into two simple polygonal arcs
from `a` to `b` meeting only at `a` and `b`. (The points may be vertices or interior to edges; the
vertex lists are the vertices of `J` between `a` and `b` in each direction, with `a`, `b` adjoined.) -/
theorem IsSimpleClosedPolygon.split_two {J : Set Pt} (hJ : IsSimpleClosedPolygon J) {a b : Pt}
    (ha : a ∈ J) (hb : b ∈ J) (hab : a ≠ b) :
    ∃ α₁ α₂ : Set Pt, IsSimplePolyArc α₁ a b ∧ IsSimplePolyArc α₂ a b ∧ α₁ ∪ α₂ = J ∧
      α₁ ∩ α₂ = {a, b} := by
  sorry

/-- **Joining two simple polygonal arcs** with the same ends, meeting only at the ends, gives a
simple closed polygon. (Concatenate the vertex list of `α` with the reversed interior of the list of
`β`; `α ∩ β = {a, b}` gives the disjointness of non-adjacent edges and excludes an overlap of the
two edges at `a` or at `b`; a straight angle at `a` or `b` is allowed by `IsSimpleClosedPolygon`.) -/
theorem isSimpleClosedPolygon_of_arcs {α β : Set Pt} {a b : Pt} (hα : IsSimplePolyArc α a b)
    (hβ : IsSimplePolyArc β a b) (hαβ : α ∩ β = {a, b}) : IsSimpleClosedPolygon (α ∪ β) := by
  sorry

/-- An arc minus its ends is connected (a polygonal path is the continuous image of an interval;
the open path is the image of the open interval). -/
theorem IsSimplePolyArc.isConnected_diff_ends {α : Set Pt} {a b : Pt}
    (hα : IsSimplePolyArc α a b) : IsConnected (α \ {a, b}) := by
  sorry

/-- **The cross-cut theorem.** A simple polygonal arc `c` from `a` to `b` (`a ≠ b`) meeting `J`
exactly in `{a, b}`, with its interior inside `polyInterior J`, splits `polyInterior J` into the
interiors of the two simple closed polygons `α₁ ∪ c` and `α₂ ∪ c`, where `J = α₁ ∪ α₂` is the split
of `J` at `a`, `b`:

    polyInterior J \ c = polyInterior (α₁ ∪ c) ∪ polyInterior (α₂ ∪ c),   disjoint,

and `closure (polyInterior (αᵢ ∪ c)) ∩ J = αᵢ`.

Proof (`U = polyInterior J`, `V` its exterior, `Γᵢ = αᵢ ∪ c`, `Uᵢ = polyInterior Γᵢ`, `Vᵢ` its
exterior, all from `PlaneFacts.split`):
* `V ⊆ V₁`: `V` is connected, unbounded, misses `Γ₁ ⊆ closure U`.
* `α₂ \ {a, b} ⊆ V₁`: it is connected (`isConnected_diff_ends`), misses `Γ₁` (`α₁ ∩ α₂ = {a, b}`,
  `c ∩ J = {a, b}`), and each of its points is a limit of points of `V ⊆ V₁` (`PlaneFacts.split`:
  `w ∈ closure V` for `w ∈ J`), while `Γ₁ᶜ` is locally `U₁` or `V₁` near such a point
  (`local_side`): so it lies in `V₁`. Hence `U₁ ∩ J = ∅`.
* `U₁ ⊆ U`: `U₁` is connected and misses `J`; near an interior point `w` of `c`, `c ⊆ Γ₁` is
  two-sided for `Γ₁` (`local_side`), both sides lie in `U` (`w ∈ U` open), and one side is in `U₁`:
  so `U₁` meets `U`. Likewise `U₂ ⊆ U`.
* `U₁ ∩ U₂ = ∅`: `Γ₁ ∩ U₂ = ∅` (`c ⊆ Γ₂ = frontier U₂`; `α₁ \ {a, b} ⊆ V₂` as above), so the connected
  `U₂` lies in `U₁` or in `V₁`; if `U₂ ⊆ U₁` then by symmetry `U₁ ⊆ U₂`, so `U₁ = U₂`, `Γ₁ = Γ₂`
  (frontiers), `α₁ = α₂` — but `α₁ \ {a, b} ⊆ V₂` misses `Γ₂ ⊇ α₂`. So `U₂ ⊆ V₁`.
* `U \ c ⊆ U₁ ∪ U₂`: for `x ∈ U \ c` and `y ∈ V`, the compact set `Γ₁ ∪ Γ₂ = J ∪ c` separates `x`
  from `y` (the component of `x` in `(J ∪ c)ᶜ` lies in the component of `x` in `Jᶜ`, which is `U`,
  and `y ∉ U`); `Γ₁ ∩ Γ₂ = c` is connected (`IsSimplePolyArc.isContinuum`); so by `janiszewski`
  one of `Γ₁`, `Γ₂` separates `x` from `y`; `y ∈ V ⊆ V₁ ∩ V₂`, so `x ∉ V₁` or `x ∉ V₂`, i.e.
  `x ∈ U₁` or `x ∈ U₂` (`x ∉ Γᵢ`).
* `Uᵢ ⊆ U \ c`: `c ⊆ Γᵢ` misses `Uᵢ`.
* `closure U₁ ∩ J = (U₁ ∪ Γ₁) ∩ J = Γ₁ ∩ J = α₁` (`c ∩ J = {a, b} ⊆ α₁`). -/
theorem PlaneFacts.crosscut (hPF : PlaneFacts) {J : Set Pt} (hJ : IsSimpleClosedPolygon J)
    {c : Set Pt} {a b : Pt} (hab : a ≠ b) (hc : IsSimplePolyArc c a b)
    (hcJ : c ∩ J = {a, b}) (hcU : c \ {a, b} ⊆ polyInterior J) :
    ∃ α₁ α₂ : Set Pt, IsSimplePolyArc α₁ a b ∧ IsSimplePolyArc α₂ a b ∧ α₁ ∪ α₂ = J ∧
      α₁ ∩ α₂ = {a, b} ∧
      IsSimpleClosedPolygon (α₁ ∪ c) ∧ IsSimpleClosedPolygon (α₂ ∪ c) ∧
      polyInterior J \ c = polyInterior (α₁ ∪ c) ∪ polyInterior (α₂ ∪ c) ∧
      Disjoint (polyInterior (α₁ ∪ c)) (polyInterior (α₂ ∪ c)) ∧
      closure (polyInterior (α₁ ∪ c)) ∩ J = α₁ ∧ closure (polyInterior (α₂ ∪ c)) ∩ J = α₂ := by
  sorry

/-! ### 5. The hypothesis of Theorem 7 (reconnaissance — no `sorry`)

Bing states Theorem 7 for a *tree-like* plane continuum; the proof he points to (Theorem 6) uses
"contains no continuum which separates the plane". The repository will state `theorem7_1951`
(batch 120) with the latter hypothesis. The implication

    theorem treeLike_nonseparating (hPF : PlaneFacts) {M : Set Pt} (hM : IsTreeLike M) :
        ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K

is the question of item 5 of the commission: proved, refuted (not expected: it is a classical
theorem), or open with the obstruction stated. It is NOT to be added as a `sorry`, nor as a field
of `PlaneFacts`, in this batch. -/

end HPC.Plane
