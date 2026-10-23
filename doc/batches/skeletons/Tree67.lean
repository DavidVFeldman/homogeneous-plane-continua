import HPC.PseudoArc.Thm14

/-!
# Batch 117: Bing 1951 (Duke) §3, Theorems 6 and 7 — definitions, the plane-topology interface,
# and the grid cover

Skeleton (save as `HPC/Plane/Tree67.lean`; add `import HPC.Plane.Tree67` at the end of the root
`HPC.lean`). Statements only; every proof is a `sorry` work item, except the fields of
`PlaneFacts`, which are *hypotheses* and stay hypotheses in this batch. Shapes may be adjusted
with the change recorded. No existing file is to be edited, except the audit.

**Bing's definitions (p. 653).** A chain is a finite collection of open sets `d_1, …, d_j` with
`d_i ∩ d_j ≠ ∅ iff |i − j| ≤ 1`, links not required connected. A *circular chain* has more than
two links and its first and last links intersect. A finite *coherent* collection `G` of open sets
is a *tree chain* if no three of the open sets have a point in common and no subcollection of `G`
is a circular chain. (`G` is coherent if for each proper subcollection `G'` of it, an element of
`G'` intersects an element of `G − G'`.) A compact continuum is *tree-like* if for each `ε > 0`
there is a tree chain covering it with links of diameter `< ε`.

**Theorem 6 (p. 656).** *Each bounded plane continuum which does not contain a continuum which
separates the plane is tree-like.* **Theorem 7 (p. 657).** *If `M` is a tree-like plane continuum
and `ε` a positive number, there is a tree-chain covering `M` whose links are the interiors of
simple closed curves of diameters less than `ε`.* ("In the proof of Theorem 6 we establish the
following result.")

**The interface.** Bing's proof uses three facts of plane topology that the repository does not
have and that are not to be proved here: the Jordan curve theorem for simple closed polygons; a
simple closed curve around a non-separating continuum inside any neighbourhood of it ("there is
an unbounded continuum `W` which does not intersect `M` such that the complement of `W` is the
interior `d_0` of a simple closed curve and `d_1, …, d_n` covers `d_0`"); and Janiszewski's
theorem, from which the point `q` of the circular-chain contradiction will be derived in batch
118. They are bundled as the hypotheses `PlaneFacts`; every theorem of §3 is proved relative to
it. (David: "treated as a hypothesis, albeit known actually to be a theorem".) Two more facts enter
for Theorem 7 and are recorded in the ledger when they are reached (batch 119): components of the
intersection of two polygon interiors are polygon interiors; a tree-like plane continuum contains
no continuum separating the plane.

The plane is `Pt = ℝ × ℝ` with its product (sup) metric, as everywhere in `HPC/Plane`; "diameter
less than `ε`" is in that metric, which only changes constants.
-/

namespace HPC.Plane

open Set Metric

/-! ### Polygons, interiors, separation -/

/-- A closed polygon with `n ≥ 3` vertices: the union of the segments `v i — v (i+1)` (indices
mod `n`). -/
def polygonOf {n : ℕ} (v : Fin n → Pt) : Set Pt :=
  ⋃ i : Fin n, segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩)

/-- A **simple closed polygon**: a closed polygon whose vertices are distinct, non-adjacent edges
are disjoint and adjacent edges meet only at their common vertex. -/
def IsSimpleClosedPolygon (J : Set Pt) : Prop :=
  ∃ (n : ℕ) (hn : 3 ≤ n) (v : Fin n → Pt), J = polygonOf v ∧ Function.Injective v ∧
    ∀ i j : Fin n, i ≠ j →
      (((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) →
        segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩) ∩
          segment ℝ (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩) ⊆
            {v i, v j, v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩}) ∧
      (¬ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) →
        Disjoint (segment ℝ (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩))
          (segment ℝ (v j) (v ⟨(j.val + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩)))

/-- The **interior** of a compact set `J` of the plane: the union of the bounded components of
its complement. (No Jordan curve theorem is needed to define it.) -/
def polyInterior (J : Set Pt) : Set Pt :=
  {x | x ∉ J ∧ Bornology.IsBounded (connectedComponentIn Jᶜ x)}

/-- `A` **separates the plane** (Bing: "separates the plane"): its complement is not connected. -/
def SeparatesPlane (A : Set Pt) : Prop := ¬ IsConnected Aᶜ

/-- `A` separates `x` from `y`: they lie in different components of `Aᶜ`. -/
def SeparatesPts (A : Set Pt) (x y : Pt) : Prop :=
  x ∉ A ∧ y ∉ A ∧ y ∉ connectedComponentIn Aᶜ x

/-! ### Tree chains -/

/-- A finite collection `G` of open sets is **coherent** (Bing): every nonempty proper
subcollection has an element meeting an element of the rest. -/
def IsCoherent (G : Finset (Set Pt)) : Prop :=
  ∀ G' ⊂ G, G'.Nonempty → ∃ A ∈ G', ∃ B ∈ G \ G', (A ∩ B).Nonempty

/-- A **circular chain** of open sets: `m > 2` sets `d 0, …, d (m-1)`, `d i ∩ d j ≠ ∅ iff
`|i − j| ≤ 1` *or* `{i, j} = {0, m-1}`. -/
def IsCircularChain (G : Finset (Set Pt)) : Prop :=
  ∃ (m : ℕ) (hm : 2 < m) (d : Fin m → Set Pt), Function.Injective d ∧ G = Finset.univ.image d ∧
    ∀ i j : Fin m, (d i ∩ d j).Nonempty ↔
      (((i : ℤ) - j).natAbs ≤ 1 ∨ (i.val = 0 ∧ j.val = m - 1) ∨ (j.val = 0 ∧ i.val = m - 1))

/-- A **tree chain** (Bing, p. 653): a finite coherent collection of open sets, no three with a
common point, no subcollection a circular chain. -/
def IsTreeChain (G : Finset (Set Pt)) : Prop :=
  (∀ A ∈ G, IsOpen A) ∧ IsCoherent G ∧
    (∀ A ∈ G, ∀ B ∈ G, ∀ C ∈ G, A ≠ B → B ≠ C → A ≠ C → A ∩ B ∩ C = ∅) ∧
    ∀ G' ⊆ G, ¬ IsCircularChain G'

/-- A compact continuum is **tree-like** if for every `ε > 0` some tree chain of links of
diameter `< ε` covers it. -/
def IsTreeLike (M : Set Pt) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∀ ε : ℝ, 0 < ε → ∃ G : Finset (Set Pt), IsTreeChain G ∧
    (∀ A ∈ G, diam A < ε) ∧ M ⊆ ⋃ A ∈ G, A

/-! ### The interface -/

/-- **The plane-topology facts used by Bing's proof of Theorem 6, as hypotheses.**
* `jct`: the Jordan curve theorem for simple closed polygons — the complement has exactly two
  components, one bounded and one unbounded, and the polygon is the frontier of each;
* `enclose`: around a compact continuum `M` that does not separate the plane, inside any open
  `G ⊇ M`, there is a simple closed polygon `J` missing `M` with `M ⊆ polyInterior J ⊆ G`
  (Bing's `W = ℝ² ∖ d_0`, "unbounded continuum which does not intersect `M`, the complement of
  `W` is the interior `d_0` of a simple closed curve and `d_1, …, d_n` covers `d_0`");
* `janiszewski`: if `A`, `B` are closed, `A ∩ B` is connected or empty, and neither separates `x`
  from `y`, then `A ∪ B` does not separate `x` from `y`. -/
structure PlaneFacts : Prop where
  jct : ∀ J : Set Pt, IsSimpleClosedPolygon J →
    ∃ U V : Set Pt, IsOpen U ∧ IsOpen V ∧ Jᶜ = U ∪ V ∧ Disjoint U V ∧
      IsConnected U ∧ IsConnected V ∧ Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      frontier U = J ∧ frontier V = J
  enclose : ∀ M : Set Pt, Fold.Q78.IsContinuum M → ¬ SeparatesPlane M →
    ∀ G : Set Pt, IsOpen G → M ⊆ G →
      ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ Disjoint J M ∧ M ⊆ polyInterior J ∧
        polyInterior J ⊆ G
  janiszewski : ∀ A B : Set Pt, IsClosed A → IsClosed B → (IsConnected (A ∩ B) ∨ A ∩ B = ∅) →
    ∀ x y : Pt, ¬ SeparatesPts A x y → ¬ SeparatesPts B x y → ¬ SeparatesPts (A ∪ B) x y

/-- Under `jct`, `polyInterior J` is the bounded component `U`, and the frontier facts transfer. -/
theorem PlaneFacts.polyInterior_eq (h : PlaneFacts) {J : Set Pt} (hJ : IsSimpleClosedPolygon J) :
    IsOpen (polyInterior J) ∧ IsConnected (polyInterior J) ∧
      Bornology.IsBounded (polyInterior J) ∧ frontier (polyInterior J) = J ∧
      IsConnected (J ∪ polyInterior J)ᶜ := by
  sorry

/-! ### The grid cover (Bing, first paragraph of the proof of Theorem 6) -/

/-- A bounded plane continuum containing no continuum that separates the plane is nowhere
dense: a closed square inside it would contain the boundary of the square, which separates
(its complement is the disjoint union of the open square and the open exterior). -/
theorem interior_eq_empty_of_noSeparating {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) : interior M = ∅ := by
  sorry

/-- The closed grid square of side `ε` with lower-left corner `o + ε • (a, b)`. -/
def gridSq (o : Pt) (ε : ℝ) (a b : ℤ) : Set Pt :=
  Icc (o.1 + ε * a) (o.1 + ε * (a + 1)) ×ˢ Icc (o.2 + ε * b) (o.2 + ε * (b + 1))

/-- The vertices of the grid with offset `o`. -/
def gridVertices (o : Pt) (ε : ℝ) : Set Pt :=
  {p | ∃ a b : ℤ, p = (o.1 + ε * a, o.2 + ε * b)}

/-- **An offset with no grid vertex on `M`** (Bing: "no point of `M` is on the vertex of any of
the quadrilaterals"): `M` bounded and nowhere dense, finitely many vertices matter, and a finite
union of translates of a nowhere dense closed set is nowhere dense. -/
theorem exists_grid_offset {M : Set Pt} (hM : IsClosed M) (hb : Bornology.IsBounded M)
    (hnd : interior M = ∅) {ε : ℝ} (hε : 0 < ε) :
    ∃ o : Pt, Disjoint (gridVertices o ε) M := by
  sorry

/-- The finitely many grid squares meeting `M`, as a finset of index pairs. -/
theorem finite_gridSq_meeting {M : Set Pt} (hb : Bornology.IsBounded M) (o : Pt) {ε : ℝ}
    (hε : 0 < ε) : {ab : ℤ × ℤ | (gridSq o ε ab.1 ab.2 ∩ M).Nonempty}.Finite := by
  sorry

/-- **The notched enlargement** of a grid square: the open square, together with open strips of
width `η` along its four sides, each strip stopped at distance `r` from the two ends of its side.
(`r > η`; the square's corners and `r`-neighbourhoods of them are not enlarged.) -/
def notched (o : Pt) (ε η r : ℝ) (a b : ℤ) : Set Pt :=
  Ioo (o.1 + ε * a) (o.1 + ε * (a + 1)) ×ˢ Ioo (o.2 + ε * b) (o.2 + ε * (b + 1)) ∪
  Ioo (o.1 + ε * a + r) (o.1 + ε * (a + 1) - r) ×ˢ
    Ioo (o.2 + ε * b - η) (o.2 + ε * (b + 1) + η) ∪
  Ioo (o.1 + ε * a - η) (o.1 + ε * (a + 1) + η) ×ˢ
    Ioo (o.2 + ε * b + r) (o.2 + ε * (b + 1) - r)

theorem isOpen_notched (o : Pt) (ε η r : ℝ) (a b : ℤ) : IsOpen (notched o ε η r a b) := by
  sorry

theorem diam_notched_le (o : Pt) {ε η r : ℝ} (hε : 0 < ε) (hη : 0 < η) (hr : 0 < r)
    (a b : ℤ) : diam (notched o ε η r a b) ≤ ε + 2 * η := by
  sorry

/-- **`M ∩ q̄ ⊆ d`**: if `M` keeps distance `≥ r` from every grid vertex, every point of `M` in
the closed square lies in its notched enlargement. -/
theorem inter_gridSq_subset_notched {M : Set Pt} (o : Pt) {ε η r : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hr : 0 < r) (hrε : 2 * r < ε)
    (hfar : ∀ p ∈ M, ∀ v ∈ gridVertices o ε, r ≤ dist p v) (a b : ℤ) :
    M ∩ gridSq o ε a b ⊆ notched o ε η r a b := by
  sorry

/-- **No three notched squares share a point** (`η < r`, `2 r < ε`): two notched squares meet
only if the squares share a side, and then only in the strip along that side away from its
ends; three distinct squares cannot pairwise share sides. -/
theorem notched_no_triple (o : Pt) {ε η r : ℝ} (hε : 0 < ε) (hη : 0 < η) (hηr : η < r)
    (hrε : 2 * r < ε) {a b a' b' a'' b'' : ℤ}
    (h1 : (a, b) ≠ (a', b')) (h2 : (a', b') ≠ (a'', b'')) (h3 : (a, b) ≠ (a'', b'')) :
    notched o ε η r a b ∩ notched o ε η r a' b' ∩ notched o ε η r a'' b'' = ∅ := by
  sorry

/-- **The cover** (Bing: "There is an `ε` collection `d_1, …, d_n` of interiors of simple closed
curves such that `d_i` contains `M · q̄_i` and no point belongs to three of the `d_i`'s"): a finite
family of notched squares, open, of diameter `< ε`, covering `M`, with no triple intersections. The
polygon property of the `d_i` is not stated here (batch 119). -/
theorem exists_notched_cover {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hb : Bornology.IsBounded M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Finset (Set Pt), (∀ d ∈ D, IsOpen d) ∧ (∀ d ∈ D, diam d < ε) ∧ M ⊆ ⋃ d ∈ D, d ∧
      (∀ d ∈ D, (d ∩ M).Nonempty) ∧
      ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅ := by
  sorry

/-! ### Two lemmas for batch 118 -/

/-- Components of open subsets of the plane are open. -/
theorem isOpen_connectedComponentIn_of_isOpen {U : Set Pt} (hU : IsOpen U) (x : Pt) :
    IsOpen (connectedComponentIn U x) := by
  sorry

/-- A minimal finite open cover of a connected set is coherent (every element meets the set;
a split of the cover into two subfamilies with no intersections across would split the set). Bing
does not argue the coherence of `H'`; this supplies it. -/
theorem isCoherent_of_minimal_cover {M : Set Pt} (hM : IsConnected M) (G : Finset (Set Pt))
    (hopen : ∀ A ∈ G, IsOpen A) (hcov : M ⊆ ⋃ A ∈ G, A) (hmin : ∀ A ∈ G, (A ∩ M).Nonempty)
    (hmin' : ∀ A ∈ G, ¬ M ⊆ ⋃ B ∈ G.erase A, B) : IsCoherent G := by
  sorry

end HPC.Plane
