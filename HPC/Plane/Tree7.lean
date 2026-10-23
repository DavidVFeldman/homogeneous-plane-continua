import HPC.Plane.Tree7Star
import HPC.Plane.Tree7GP
import HPC.Plane.Tree7Notched

/-!
# Batch 119: Bing 1951 (Duke), Theorem 7 — the links as interiors of simple closed polygons (I)

Batch 119 delivery of the skeleton (original: `doc/batches/skeletons/Tree7.lean`). Every item is
proved; no `sorry` remains. The shape changes (all of them drop hypotheses the proofs do not use, so
each new statement implies the commissioned one, except the move of two definitions) are recorded in
the docstrings and in `doc/batches/REPORT-batch119.md`. Auxiliary files: `Tree7Star` (strongly
star-shaped sets, the notched square), `Tree7Arcs` (arcs of a simple closed polygon), `Tree7Cross`
(the cross-cut theorem), `Tree7GP` (lines, non-parallel segments), `Tree7Notched` (the 20-gon, finite
checks).

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
noncomputable def notchedFamily (o : Pt) (δ η r : ℝ) (I : Finset (ℤ × ℤ)) : Finset (Set Pt) :=
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
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨o, ho⟩ := exists_grid_offset hM.1.isClosed (interior_eq_empty_of_noSeparating hns) δ
  obtain ⟨r0, hr0, hfar0⟩ := exists_far hM.1 hM.2.nonempty (isClosed_gridVertices o hδ0.ne')
    ⟨_, 0, 0, rfl⟩ ho
  set r := min (r0 / 2) (δ / 4) with hr
  have hr0' : 0 < r := lt_min (by positivity) (by positivity)
  have hrr0 : r < r0 := (min_le_left _ _).trans_lt (by linarith)
  have hr4 : 4 * r ≤ δ := by have := min_le_right (r0 / 2) (δ / 4); linarith
  have hrδ : 2 * r < δ := by have := min_le_right (r0 / 2) (δ / 4); linarith
  set η := r / 2 with hη
  have hη0 : 0 < η := by positivity
  have hηr : η < r := by linarith
  have hfar : ∀ p ∈ M, ∀ v ∈ gridVertices o δ, r < dist p v := fun p hp v hv =>
    hrr0.trans_le (hfar0 p hp v hv)
  have hS := finite_gridSq_meeting hM.1.isBounded o hδ0
  refine ⟨o, δ, η, r, hS.toFinset, hη0, hηr, hr4, le_rfl, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 hd
    refine (diam_notched_le o hδ0 hη0 hr0' _ _).trans_lt ?_
    have := min_le_right (r0 / 2) (δ / 4)
    linarith
  · intro p hp
    have hsq := mem_gridSq_floor o p hδ0
    refine mem_iUnion₂.2 ⟨_, Finset.mem_image.2 ⟨(⌊(p.1 - o.1) / δ⌋, ⌊(p.2 - o.2) / δ⌋),
      hS.mem_toFinset.2 ⟨p, hsq, hp⟩, rfl⟩, ?_⟩
    exact inter_gridSq_subset_notched o hη0 hfar _ _ ⟨hp, hsq⟩
  · intro d₁ h₁ d₂ h₂ d₃ h₃ n12 n23 n13
    obtain ⟨⟨a₁, b₁⟩, -, rfl⟩ := Finset.mem_image.1 h₁
    obtain ⟨⟨a₂, b₂⟩, -, rfl⟩ := Finset.mem_image.1 h₂
    obtain ⟨⟨a₃, b₃⟩, -, rfl⟩ := Finset.mem_image.1 h₃
    exact notched_no_triple o hδ0 hη0 hηr hrδ
      (fun h => n12 (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))
      (fun h => n23 (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))
      (fun h => n13 (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))

/-- A notched square is bounded (`notched_subset_box`). -/
theorem isBounded_notched (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r) (a b : ℤ) :
    Bornology.IsBounded (notched o δ η r a b) :=
  (Metric.isBounded_Icc _ _ |>.prod (Metric.isBounded_Icc _ _)).subset
    (notched_subset_box o hη hr _ _)

/-- A notched square is connected: it is star-shaped with respect to the centre of the square
(each of its three open rectangles is convex and contains the centre). The skeleton's `hδ` (implied
by `hr` and `h4`) was dropped here, in `isConnected_compl_notched`, `regular_notched` and
`notched_eq_polyInterior`. -/
theorem isConnected_notched (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) : IsConnected (notched o δ η r a b) :=
  (strongStar_notched o hη hr h4 a b).1.isConnected (strongStar_notched o hη hr h4 a b).2

/-- The complement of a notched square is connected and unbounded. (Star-shapedness again: if
`x ∉ N` and `y` lies on the ray from the centre `c` through `x` beyond `x`, then `y ∉ N`, since
`y ∈ N` would put the segment `[c, y] ∋ x` in `N`. So every point of `Nᶜ` is joined inside `Nᶜ` by a
ray to the complement of a large box, which is connected.) -/
theorem isConnected_compl_notched (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) :
    IsConnected (notched o δ η r a b)ᶜ ∧ ¬ Bornology.IsBounded (notched o δ η r a b)ᶜ :=
  (strongStar_notched o hη hr h4 a b).1.compl_connected (strongStar_notched o hη hr h4 a b).2
    (isBounded_notched o hη hr a b)

/-- A notched square is regular open: `interior (closure N) = N`. (Every boundary point of `N` is
a limit of points of the interior of `Nᶜ`: on the sides of the square within `r` of a corner, the
points just outside; on the ends of the strips, the points just beyond the end; the `r`-corners
`(x₀ + r, y₀)` etc. are limits of points below-left.) -/
theorem regular_notched (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hηr : η < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) :
    interior (closure (notched o δ η r a b)) = notched o δ η r a b :=
  (strongStar_notched o hη (hη.trans hηr) h4 a b).1.regular (isOpen_notched _ _ _ _ _ _)

/-- The interior of a simple closed polygon is regular open (`jct`: `closure U = U ∪ J`, and a
point of `J` is in the closure of the exterior `V`, which is open and misses `U ∪ J`). -/
theorem PlaneFacts.polyInterior_regular (hPF : PlaneFacts) {J : Set Pt}
    (hJ : IsSimpleClosedPolygon J) :
    interior (closure (polyInterior J)) = polyInterior J := by
  obtain ⟨V, hU, hV, hJV, hd, -, hfr, -, hfV, -⟩ := hPF.split hJ
  refine subset_antisymm (fun p hp => ?_) (hU.subset_interior_iff.2 subset_closure)
  have hpcl : p ∈ closure (polyInterior J) := interior_subset hp
  rw [closure_eq_self_union_frontier, hfr] at hpcl
  rcases hpcl with h | h
  · exact h
  · exfalso
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 (hfV p h) _ isOpen_interior hp
    have hycl : y ∈ closure (polyInterior J) := interior_subset hy1
    exact (hd.symm.closure_right hV).notMem_of_mem_left hy2 hycl

/-- Members of `compFamily` are bounded when `d₀` is. -/
theorem compFamily_isBounded {d₀ : Set Pt} {D : Finset (Set Pt)} (hd₀ : Bornology.IsBounded d₀)
    {h : Set Pt} (hh : h ∈ compFamily d₀ D) : Bornology.IsBounded h := by
  obtain ⟨d, -, x, -, rfl⟩ := hh
  exact hd₀.subset ((connectedComponentIn_subset _ _).trans inter_subset_left)

/-- **Members of `compFamily` are regular open** when `d₀` and the members of `D` are.
(`interior (closure h) ⊆ interior (closure (d₀ ∩ d)) ⊆ interior (closure d₀) ∩ interior (closure d)
= d₀ ∩ d`; a point of `d₀ ∩ d` in the closure of the component `h` lies in `h`, since its own
component is open — `mem_connectedComponentIn_of_mem_closure`, batch 118.) -/
theorem compFamily_regular {d₀ : Set Pt} {D : Finset (Set Pt)} (hd₀ : IsOpen d₀)
    (hopen : ∀ d ∈ D, IsOpen d) (hreg₀ : interior (closure d₀) = d₀)
    (hreg : ∀ d ∈ D, interior (closure d) = d) {h : Set Pt} (hh : h ∈ compFamily d₀ D) :
    interior (closure h) = h := by
  obtain ⟨d, hd, x, -, rfl⟩ := hh
  have hO : IsOpen (d₀ ∩ d) := hd₀.inter (hopen d hd)
  refine subset_antisymm (fun p hp => ?_)
    (hO.connectedComponentIn.subset_interior_iff.2 subset_closure)
  have hsub : closure (connectedComponentIn (d₀ ∩ d) x) ⊆ closure d₀ ∩ closure d :=
    subset_inter (closure_mono ((connectedComponentIn_subset _ _).trans inter_subset_left))
      (closure_mono ((connectedComponentIn_subset _ _).trans inter_subset_right))
  have h₀ : p ∈ interior (closure d₀) := interior_mono (hsub.trans inter_subset_left) hp
  have h₁ : p ∈ interior (closure d) := interior_mono (hsub.trans inter_subset_right) hp
  rw [hreg₀] at h₀
  rw [hreg d hd] at h₁
  exact mem_connectedComponentIn_of_mem_closure hO ⟨h₀, h₁⟩ (interior_subset hp)

/-- **Members of `compFamily` do not separate the plane.** With `O = d₀ ∩ d`: `Oᶜ = d₀ᶜ ∪ dᶜ` is
connected (both connected and unbounded; `d₀` bounded, so they meet). Every other component `C` of
`O` is a nonempty bounded open set, so its frontier is nonempty, and `frontier C ⊆ Oᶜ` (a point of
`O` in `closure C` lies in `C`, components of open sets being open); hence `closure C ∪ Oᶜ` is
connected, and `hᶜ = Oᶜ ∪ ⋃ (closure C)` over the other components is connected. The skeleton's
`hu₀ : ¬ Bornology.IsBounded d₀ᶜ` is not needed (the meeting point of `d₀ᶜ` and `dᶜ` comes from `dᶜ`
being unbounded and `d₀` bounded) and was dropped. -/
theorem compFamily_compl_connected {d₀ : Set Pt} {D : Finset (Set Pt)} (hd₀ : IsOpen d₀)
    (hd₀b : Bornology.IsBounded d₀) (hopen : ∀ d ∈ D, IsOpen d)
    (hc₀ : IsConnected d₀ᶜ) (hc : ∀ d ∈ D, IsConnected dᶜ ∧ ¬ Bornology.IsBounded dᶜ)
    {h : Set Pt} (hh : h ∈ compFamily d₀ D) : ¬ SeparatesPlane h := by
  obtain ⟨d, hd, x, -, rfl⟩ := hh
  set O := d₀ ∩ d with hOdef
  have hO : IsOpen O := hd₀.inter (hopen d hd)
  obtain ⟨hdc, hdu⟩ := hc d hd
  -- `Oᶜ` is connected
  have hmeet : (d₀ᶜ ∩ dᶜ).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    exact hdu (hd₀b.subset fun z hz => by
      by_contra hz'
      have : z ∈ d₀ᶜ ∩ dᶜ := ⟨hz', hz⟩
      rw [hne] at this; exact this)
  have hOc : IsConnected Oᶜ := by
    rw [hOdef, compl_inter]
    obtain ⟨z, hz⟩ := hmeet
    exact hc₀.union ⟨z, hz⟩ hdc
  set h := connectedComponentIn O x with hh
  have hho : IsOpen h := hO.connectedComponentIn
  have hhO : h ⊆ O := connectedComponentIn_subset _ _
  intro hsep
  apply hsep
  obtain ⟨z₀, hz₀⟩ := hOc.nonempty
  refine ⟨⟨z₀, fun h' => hz₀ (hhO h')⟩, isPreconnected_of_forall z₀ fun y hy => ?_⟩
  by_cases hyO : y ∈ O
  · set C := connectedComponentIn O y with hC
    have hCh : Disjoint C h := by
      rw [Set.disjoint_left]
      intro u hu hu'
      apply hy
      rw [hh, ← connectedComponentIn_eq_of_meet ⟨u, hu, hu'⟩]
      exact mem_connectedComponentIn hyO
    have hclh : Disjoint (closure C) h := (hCh.symm.closure_right hho).symm
    have hCb : Bornology.IsBounded C :=
      hd₀b.subset ((connectedComponentIn_subset _ _).trans inter_subset_left)
    have hCne : C.Nonempty := ⟨y, mem_connectedComponentIn hyO⟩
    have hfr : (frontier C).Nonempty := by
      by_contra hfe
      rw [not_nonempty_iff_eq_empty, frontier_eq_empty_iff] at hfe
      rcases hfe with he | he
      · exact hCne.ne_empty he
      · exact NormedSpace.unbounded_univ ℝ Pt (he ▸ hCb)
    obtain ⟨w, hw⟩ := hfr
    have hwO : w ∈ Oᶜ := by
      intro hwO
      have hwC := mem_connectedComponentIn_of_mem_closure hO hwO (frontier_subset_closure hw)
      rw [hO.connectedComponentIn.frontier_eq] at hw
      exact hw.2 hwC
    refine ⟨Oᶜ ∪ closure C, union_subset (compl_subset_compl.2 hhO) ?_, Or.inl hz₀,
      Or.inr (subset_closure (mem_connectedComponentIn hyO)),
      hOc.isPreconnected.union w hwO (frontier_subset_closure hw)
        (isPreconnected_connectedComponentIn.closure)⟩
    intro u hu hu'
    exact hclh.notMem_of_mem_left hu hu'
  · exact ⟨Oᶜ, compl_subset_compl.2 hhO, hz₀, hyO, hOc.isPreconnected⟩

/-- **The tail of the proof of Theorem 6, factored out**: for any simple closed polygon `J` with
`M ⊆ polyInterior J` and any bounded open no-triple cover `D` of `polyInterior J` with links of
diameter `< ε`, a finite family of members of `compFamily (polyInterior J) D` is a tree chain of
mesh `< ε` covering `M`, each member containing a point of `M`. (The proof of `theorem6_1951` from
"`set d₀ := polyInterior J`" on, verbatim; `theorem6_1951` itself is not to be edited.) -/
theorem treeChain_of_cover (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    {J : Set Pt} (hJ : IsSimpleClosedPolygon J) (hMJ : M ⊆ polyInterior J)
    {D : Finset (Set Pt)} (hopen : ∀ d ∈ D, IsOpen d) (hbdd : ∀ d ∈ D, Bornology.IsBounded d)
    {ε : ℝ} (hdiam : ∀ d ∈ D, diam d < ε) (hcov : polyInterior J ⊆ ⋃ d ∈ D, d)
    (htriple : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅)
    (hpoly : ∀ h ∈ compFamily (polyInterior J) D,
      ∃ Γ, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ) :
    ∃ G : Finset (Set Pt), (∀ h ∈ G, h ∈ compFamily (polyInterior J) D) ∧ IsTreeChain G ∧
      (∀ h ∈ G, diam h < ε) ∧ M ⊆ ⋃ h ∈ G, h ∧ ∀ h ∈ G, (h ∩ M).Nonempty := by
  set d₀ := polyInterior J with hd₀
  have hd₀o : IsOpen d₀ := (hPF.polyInterior_eq hJ).1
  have hx : ∀ x ∈ M, ∃ d ∈ D, x ∈ d := fun x hx => by
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.1 (hcov (hMJ hx)); exact ⟨d, hd, hxd⟩
  choose! dx hdxD hxdx using hx
  set c : Pt → Set Pt := fun x => connectedComponentIn (d₀ ∩ dx x) x with hc
  have hcmem : ∀ x ∈ M, c x ∈ compFamily d₀ D := fun x hx =>
    ⟨dx x, hdxD x hx, x, ⟨hMJ hx, hxdx x hx⟩, rfl⟩
  obtain ⟨t, htM, htfin, htcov⟩ := hM.1.elim_finite_subcover_image (b := M) (c := c)
    (fun x hx => (compFamily_props hd₀o hopen (hcmem x hx)).1)
    (fun x hx => mem_iUnion₂.2 ⟨x, hx, mem_connectedComponentIn ⟨hMJ hx, hxdx x hx⟩⟩)
  set H := htfin.toFinset.image c with hH
  have hHmem : ∀ h ∈ H, ∃ x ∈ M, h = c x := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
    exact ⟨x, htM (htfin.mem_toFinset.1 hx), rfl⟩
  have hHc : ∀ h ∈ H, h ∈ compFamily d₀ D := by
    intro h hh; obtain ⟨x, hx, rfl⟩ := hHmem h hh; exact hcmem x hx
  have hHo : ∀ h ∈ H, IsOpen h := fun h hh => (compFamily_props hd₀o hopen (hHc h hh)).1
  have hHcov : M ⊆ ⋃ h ∈ H, h := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (htcov hy)
    exact mem_iUnion₂.2 ⟨c x, Finset.mem_image.2 ⟨x, htfin.mem_toFinset.2 hx, rfl⟩, hyx⟩
  have hHM : ∀ h ∈ H, (h ∩ M).Nonempty := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := hHmem h hh
    exact ⟨x, mem_connectedComponentIn ⟨hMJ hx, hxdx x hx⟩, hx⟩
  refine ⟨H, hHc, ⟨hHo, ?_, ?_, ?_⟩, ?_, hHcov, hHM⟩
  · exact isCoherent_of_minimal_cover hM.2 H hHo hHcov fun h hh => hHM h hh
  · intro A hA B hB C hC hAB hBC hAC
    exact compFamily_no_triple htriple (hHc A hA) (hHc B hB) (hHc C hC) hAB hBC hAC
  · intro G' hG'
    exact compFamily_no_circular hPF hJ hopen htriple hcov hpoly G' fun h hh => hHc h (hG' hh)
  · intro h hh
    obtain ⟨x, hx, rfl⟩ := hHmem h hh
    refine lt_of_le_of_lt (diam_mono ?_ (hbdd _ (hdxD x hx))) (hdiam _ (hdxD x hx))
    exact (connectedComponentIn_subset _ _).trans inter_subset_right

/- `theorem7_weak` was moved to `HPC/Plane/Tree7Comp.lean` in batch 129 and re-proved there from
`theorem7_1951` (its links are polygon interiors, which have all the listed properties):
`treeChain_of_cover` now asks the components to be polygon interiors, which the plain
notched-square cover used by its old proof does not guarantee. -/

/-! ### 2. The notched square as the interior of a 20-gon -/

/-! The twenty vertices of the boundary of `notched o δ η r a b`, counterclockwise from the
bottom-left corner `(x₀, y₀)` of the square, `x₀ = o.1 + δ a`, `x₁ = x₀ + δ`, `y₀ = o.2 + δ b`,
`y₁ = y₀ + δ`:

    (x₀,y₀) (x₀+r,y₀) (x₀+r,y₀−η) (x₁−r,y₀−η) (x₁−r,y₀) (x₁,y₀)        -- bottom side, strip below
    (x₁,y₀+r) (x₁+η,y₀+r) (x₁+η,y₁−r) (x₁,y₁−r) (x₁,y₁)                 -- right side, strip right
    (x₁−r,y₁) (x₁−r,y₁+η) (x₀+r,y₁+η) (x₀+r,y₁) (x₀,y₁)                 -- top side, strip above
    (x₀,y₁−r) (x₀−η,y₁−r) (x₀−η,y₀+r) (x₀,y₀+r)                         -- left side, strip left

The definitions `notchedVertices` (this list, unchanged from the skeleton) and `notchedPoly`
(`polygonOf notchedVertices`) were moved verbatim to `HPC/Plane/Tree7Notched.lean`, together with
the finite checks, so that those checks (about seven minutes of elaboration) are compiled once.
The vertex list was checked against `notched` and needed no change: the frontier of the notched
square is exactly this 20-gon (`frontier_notched`). -/

/-- The 20-gon is a simple closed polygon (its edges are axis-parallel; a finite check:
`notchedVertices_injective`, and `notchedVertices_edges` for the 400 ordered pairs of edges, each
reduced to linear arithmetic by `segment_vert`/`segment_horiz`). The skeleton's `hδ : 0 < δ` is
implied by `hr` and `h4` and was dropped. -/
theorem isSimpleClosedPolygon_notchedPoly (o : Pt) {δ η r : ℝ} (hη : 0 < η)
    (hr : 0 < r) (h4 : 4 * r ≤ δ) (a b : ℤ) : IsSimpleClosedPolygon (notchedPoly o δ η r a b) :=
  ⟨20, by norm_num, notchedVertices o δ η r a b, rfl, notchedVertices_injective o hη hr h4 a b,
    notchedVertices_edges o hη hr h4 a b⟩

/-- The frontier of a notched square is its boundary polygon. (`closure notched` is the union
of the three closed rectangles; a point of it outside `notched` lies on one of the twenty edges,
by a case analysis on which rectangle and which side; conversely each edge lies in a closed
rectangle and outside the three open ones.) The skeleton's `hδ` was dropped (implied by `hr`,
`h4`). -/
theorem frontier_notched (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) : frontier (notched o δ η r a b) = notchedPoly o δ η r a b :=
  frontier_notched' o hη hr h4 a b

/-- **The notched square is the interior of its boundary polygon** — unconditional, by
`polyInterior_eq_of_split` with `U = notched`, `V = (closure notched)ᶜ` (`V` connected and unbounded
by the star-shapedness of `closure notched`; `Pᶜ = U ∪ V` by `frontier_notched`). -/
theorem notched_eq_polyInterior (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) :
    notched o δ η r a b = polyInterior (notchedPoly o δ η r a b) := by
  obtain ⟨hst, hc⟩ := strongStar_notched o hη hr h4 a b
  set N := notched o δ η r a b with hN
  have hNo : IsOpen N := isOpen_notched _ _ _ _ _ _
  obtain ⟨hVc, hVb⟩ := hst.compl_closure_connected hc (isBounded_notched o hη hr a b)
  have hP : (notchedPoly o δ η r a b)ᶜ = N ∪ (closure N)ᶜ := by
    rw [← frontier_notched o hη hr h4 a b, hNo.frontier_eq]
    ext x
    simp only [mem_compl_iff, mem_diff, mem_union, not_and, not_not]
    constructor
    · intro h
      by_cases hx : x ∈ closure N
      · exact Or.inl (h hx)
      · exact Or.inr hx
    · rintro (h | h) h'
      · exact h
      · exact absurd h' h
  exact (polyInterior_eq_of_split hNo isClosed_closure.isOpen_compl hP
    (Set.disjoint_compl_right_iff_subset.2 subset_closure) (isConnected_notched o hη hr h4 a b)
    hVc (isBounded_notched o hη hr a b) hVb).symm

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
    IsSimpleClosedPolygon J ↔ ∃ (n : ℕ) (v : Fin n → Pt), IsSimpleVertices v ∧ J = polygonOf v :=
  ⟨fun ⟨n, hn, v, hJ, hinj, h⟩ => ⟨n, v, ⟨hn, hinj, h⟩, hJ⟩,
    fun ⟨n, v, ⟨hn, hinj, h⟩, hJ⟩ => ⟨n, hn, v, hJ, hinj, h⟩⟩

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
  have hsub : polygonOf v ∩ polygonOf w ⊆ ⋃ (i : Fin n) (j : Fin k), polyEdge v i ∩ polyEdge w j := by
    rintro z ⟨hz1, hz2⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz1
    obtain ⟨j, hj⟩ := mem_iUnion.1 hz2
    exact mem_iUnion₂.2 ⟨i, j, hi, hj⟩
  refine Set.Finite.subset (Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_) hsub
  by_cases hne : (polyEdge v i ∩ polyEdge w j).Nonempty
  · exact (segment_inter_subsingleton (hgp.2.2 i j hne)).finite
  · rw [not_nonempty_iff_eq_empty.1 hne]; exact finite_empty

/-- Translating a notched square translates its vertices. -/
theorem notched_translate (o t : Pt) (δ η r : ℝ) (a b : ℤ) :
    notched (o + t) δ η r a b = (fun p => p + t) '' notched o δ η r a b := by
  ext p
  simp only [mem_image]
  constructor
  · intro h
    refine ⟨p - t, ?_, by simp⟩
    simp only [notched, mem_union, mem_prod, mem_Ioo, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub] at h ⊢
    rcases h with (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) | ⟨⟨h1, h2⟩, h3, h4⟩
    · left; left; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · left; right; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · right; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨q, h, rfl⟩
    simp only [notched, mem_union, mem_prod, mem_Ioo, Prod.fst_add, Prod.snd_add] at h ⊢
    rcases h with (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) | ⟨⟨h1, h2⟩, h3, h4⟩
    · left; left; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · left; right; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · right; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem notchedVertices_translate (o t : Pt) (δ η r : ℝ) (a b : ℤ) :
    notchedVertices (o + t) δ η r a b = fun i => notchedVertices o δ η r a b i + t := by
  funext i
  fin_cases i <;> simp [notchedVertices, Prod.ext_iff] <;> constructor <;> ring

/-- Consecutive vertices of the 20-gon are distinct. -/
theorem notched_edge_ne (o : Pt) {δ η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (h4 : 4 * r ≤ δ) (a b : ℤ) (j : Fin 20) :
    notchedVertices o δ η r a b ⟨(j.val + 1) % 20, Nat.mod_lt _ (Fin.pos j)⟩ -
      notchedVertices o δ η r a b j ≠ 0 := by
  fin_cases j <;> simp [notchedVertices, Prod.ext_iff] <;> nlinarith

/-- **Lebesgue number for translation**: a compact `K` inside an open `G` stays inside every
translate of `G` by a small vector. (`IsCompact.exists_thickening_subset_open`: `thickening λ K ⊆ G`;
then `p ∈ K`, `dist t 0 < λ` give `p - t ∈ G`.) -/
theorem subset_translate_of_compact {K G : Set Pt} (hK : IsCompact K) (hG : IsOpen G)
    (hKG : K ⊆ G) : ∃ l > 0, ∀ t : Pt, dist t 0 < l → K ⊆ (fun p => p + t) '' G := by
  obtain ⟨l, hl, hthick⟩ := hK.exists_thickening_subset_open hG hKG
  refine ⟨l, hl, fun t ht p hp => ⟨p - t, hthick ?_, by simp⟩⟩
  rw [mem_thickening_iff]
  exact ⟨p, hp, by rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, ← dist_zero_right]; exact ht⟩

/-- **A small translation puts the notched squares in general position with a given polygon.**
The bad translations `t` are: (i) a vertex `v i` on a translated boundary line of some notched
square — the boundary lines are `x = o.1 + δ a + s + t.1` and `y = o.2 + δ b + s' + t.2` with
`s, s' ∈ {-η, 0, r, δ - r, δ, δ + η}`, so finitely many values of `t.1` or `t.2` are excluded, i.e.
finitely many lines in the `t`-plane; (ii) a translated vertex `w j + t` of a notched square on
`polygonOf v`, i.e. `t ∈ polygonOf v - w j`: finitely many translates of a nowhere dense closed set;
(iii) an edge of `v` parallel to (hence, if they meet, collinear with) a boundary line: for an
axis-parallel edge of `v` finitely many values of `t.1` or `t.2` are excluded; a non-axis-parallel
edge is never parallel to an axis-parallel one. The union of finitely many closed nowhere dense sets
is closed nowhere dense, so the open disk `ball 0 l` is not contained in it.

Proved with all three kinds of bad translation put on lines (`lineSet`, `HPC/Plane/Tree7GP.lean`):
for every `ab ∈ I`, `i`, `j`, the line through `v i - w j` in the direction of edge `j` of the
notched square (kinds (i) and (iii)), and the line through `v i - w j` in the direction of edge `i`
of `v` (kind (ii); any direction if that edge is degenerate). The edges of the 20-gon are nonzero
(`notched_edge_ne`); a finite union of lines has empty interior. The skeleton's `hδ` was dropped
(implied by `hr`, `h4`). -/
theorem exists_gp_translation {n : ℕ} (v : Fin n → Pt) (o : Pt) {δ η r : ℝ}
    (hη : 0 < η) (hr : 0 < r) (h4 : 4 * r ≤ δ) (I : Finset (ℤ × ℤ)) {l : ℝ} (hl : 0 < l) :
    ∃ t : Pt, dist t 0 < l ∧
      ∀ ab ∈ I, InGeneralPosition v (notchedVertices (o + t) δ η r ab.1 ab.2) := by
  classical
  set W : ℤ × ℤ → Fin 20 → Pt := fun ab => notchedVertices o δ η r ab.1 ab.2 with hW
  set nx : Fin 20 → Fin 20 := fun j => ⟨(j.val + 1) % 20, Nat.mod_lt _ (Fin.pos j)⟩ with hnx
  set mx : Fin n → Fin n := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ with hmx
  set E : ℤ × ℤ → Fin 20 → Pt := fun ab j => W ab (nx j) - W ab j with hE
  set Dv : Fin n → Pt := fun i => if v (mx i) - v i = 0 then (1, 0) else v (mx i) - v i with hDv
  have hE0 : ∀ ab j, E ab j ≠ 0 := fun ab j => notched_edge_ne o hη hr h4 ab.1 ab.2 j
  have hDv0 : ∀ i, Dv i ≠ 0 := by
    intro i
    simp only [hDv]
    split_ifs with h
    · simp [Prod.ext_iff]
    · exact h
  set S : Finset ((ℤ × ℤ) × Fin n × Fin 20 × Bool) :=
    I ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ)) with hS
  obtain ⟨t, ht, htS⟩ := exists_mem_ball_notMem_lines S (fun k => v k.2.1 - W k.1 k.2.2.1)
    (fun k => if k.2.2.2 then E k.1 k.2.2.1 else Dv k.2.1)
    (fun k _ => by dsimp only; split_ifs; exacts [hE0 _ _, hDv0 _]) 0 hl
  refine ⟨t, mem_ball.1 ht, fun ab hab => ?_⟩
  have hnot : ∀ i j (b : Bool), t ∉ lineSet (v i - W ab j) (if b then E ab j else Dv i) := by
    intro i j b h
    exact htS (mem_iUnion₂.2 ⟨(ab, i, j, b), by simp [hS, hab], h⟩)
  rw [notchedVertices_translate]
  refine ⟨fun i hi => ?_, fun j hj => ?_, fun i j hne hpar => ?_⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.1 hi
    exact hnot i j true (lineSet_of_mem_segment_translate hj)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hj
    exact hnot i j false (lineSet_of_translate_mem_segment hi)
  · obtain ⟨c, hc⟩ := hpar
    rw [add_sub_add_right_eq_sub] at hc
    exact hnot i j true (lineSet_of_parallel hc hne)

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
  obtain ⟨o₀, δ, η, r, I, hη, hηr, h4, hδε, -, hMcov, -⟩ := exists_notched_cover_param hM hns hε
  have hr : 0 < r := hη.trans hηr
  have hδ : 0 < δ := by linarith
  set G := ⋃ d ∈ notchedFamily o₀ δ η r I, d with hG
  have hGo : IsOpen G := isOpen_biUnion fun d hd => by
    obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 hd; exact isOpen_notched _ _ _ _ _ _
  obtain ⟨l₀, hl₀, hthick⟩ := hM.1.exists_thickening_subset_open hGo hMcov
  obtain ⟨J, hJ, hJM, hMJ, hJG⟩ := hPF.enclose M hM (hns M subset_rfl hM) (thickening (l₀ / 2) M)
    isOpen_thickening (self_subset_thickening (by positivity) M)
  have hKG : closure (polyInterior J) ⊆ G :=
    (closure_mono hJG).trans ((closure_thickening_subset_cthickening _ _).trans
      ((cthickening_subset_thickening' hl₀ (by linarith) M).trans hthick))
  have hKc : IsCompact (closure (polyInterior J)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hPF.polyInterior_eq hJ).2.2.1.closure
  obtain ⟨l, hl, htr⟩ := subset_translate_of_compact hKc hGo hKG
  obtain ⟨n, v, hv, rfl⟩ := isSimpleClosedPolygon_iff.1 hJ
  obtain ⟨t, ht, hgp⟩ := exists_gp_translation v o₀ hη hr h4 I hl
  refine ⟨n, v, o₀ + t, δ, η, r, I, hv, hMJ, hJM, hη, hηr, h4, hδε, ?_, ?_, ?_, hgp⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := htr t ht (subset_closure hx)
    obtain ⟨d, hd, hyd⟩ := mem_iUnion₂.1 hy
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 hd
    refine mem_iUnion₂.2 ⟨_, Finset.mem_image.2 ⟨ab, hab, rfl⟩, ?_⟩
    rw [notched_translate]
    exact ⟨y, hyd, rfl⟩
  · intro d hd
    obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 hd
    refine (diam_notched_le (o₀ + t) hδ hη hr _ _).trans_lt ?_
    linarith
  · intro d₁ h₁ d₂ h₂ d₃ h₃ n12 n23 n13
    obtain ⟨⟨a₁, b₁⟩, -, rfl⟩ := Finset.mem_image.1 h₁
    obtain ⟨⟨a₂, b₂⟩, -, rfl⟩ := Finset.mem_image.1 h₂
    obtain ⟨⟨a₃, b₃⟩, -, rfl⟩ := Finset.mem_image.1 h₃
    exact notched_no_triple (o₀ + t) hδ hη hηr (by linarith)
      (fun h => n12 (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))
      (fun h => n23 (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))
      (fun h => n13 (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))

/-! ### 4. Cross-cuts -/

/-- **Splitting a simple closed polygon at two of its points** into two simple polygonal arcs
from `a` to `b` meeting only at `a` and `b`. (The points may be vertices or interior to edges; the
vertex lists are the vertices of `J` between `a` and `b` in each direction, with `a`, `b` adjoined.) -/
theorem IsSimpleClosedPolygon.split_two {J : Set Pt} (hJ : IsSimpleClosedPolygon J) {a b : Pt}
    (ha : a ∈ J) (hb : b ∈ J) (hab : a ≠ b) :
    ∃ α₁ α₂ : Set Pt, IsSimplePolyArc α₁ a b ∧ IsSimplePolyArc α₂ a b ∧ α₁ ∪ α₂ = J ∧
      α₁ ∩ α₂ = {a, b} :=
  hJ.split_two' ha hb hab

/-- **Joining two simple polygonal arcs** with the same ends, meeting only at the ends, gives a
simple closed polygon. (Concatenate the vertex list of `α` with the reversed interior of the list of
`β`; `α ∩ β = {a, b}` gives the disjointness of non-adjacent edges and excludes an overlap of the
two edges at `a` or at `b`; a straight angle at `a` or `b` is allowed by `IsSimpleClosedPolygon`.) -/
theorem isSimpleClosedPolygon_of_arcs {α β : Set Pt} {a b : Pt} (hα : IsSimplePolyArc α a b)
    (hβ : IsSimplePolyArc β a b) (hαβ : α ∩ β = {a, b}) : IsSimpleClosedPolygon (α ∪ β) :=
  isSimpleClosedPolygon_of_arcs' hα hβ hαβ

/-- An arc minus its ends is connected (a polygonal path is the continuous image of an interval;
the open path is the image of the open interval). -/
theorem IsSimplePolyArc.isConnected_diff_ends {α : Set Pt} {a b : Pt}
    (hα : IsSimplePolyArc α a b) : IsConnected (α \ {a, b}) :=
  hα.isConnected_diff_ends'

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
* `closure U₁ ∩ J = (U₁ ∪ Γ₁) ∩ J = Γ₁ ∩ J = α₁` (`c ∩ J = {a, b} ⊆ α₁`).

Proved as outlined (`crosscut'`, `HPC/Plane/Tree7Cross.lean`), except that `local_side` is not
needed: a point `w ∈ α₂ \ {a, b}` lies in `closure V` (`PlaneFacts.split`), so if the connected set
`α₂ \ {a, b}` were inside the open set `U₁`, then `U₁` would meet `V ⊆ V₁`; and `U₁ ⊆ U` follows
because `U₁` is connected, misses `J`, and cannot lie in `V ⊆ V₁`. The hypothesis `hcU` is needed
(an arc outside `J` with its ends on `J` satisfies `hcJ`, and then one of the two new interiors
contains `polyInterior J`); `hab` is implied by `hc` and is kept. -/
theorem PlaneFacts.crosscut (hPF : PlaneFacts) {J : Set Pt} (hJ : IsSimpleClosedPolygon J)
    {c : Set Pt} {a b : Pt} (hab : a ≠ b) (hc : IsSimplePolyArc c a b)
    (hcJ : c ∩ J = {a, b}) (hcU : c \ {a, b} ⊆ polyInterior J) :
    ∃ α₁ α₂ : Set Pt, IsSimplePolyArc α₁ a b ∧ IsSimplePolyArc α₂ a b ∧ α₁ ∪ α₂ = J ∧
      α₁ ∩ α₂ = {a, b} ∧
      IsSimpleClosedPolygon (α₁ ∪ c) ∧ IsSimpleClosedPolygon (α₂ ∪ c) ∧
      polyInterior J \ c = polyInterior (α₁ ∪ c) ∪ polyInterior (α₂ ∪ c) ∧
      Disjoint (polyInterior (α₁ ∪ c)) (polyInterior (α₂ ∪ c)) ∧
      closure (polyInterior (α₁ ∪ c)) ∩ J = α₁ ∧ closure (polyInterior (α₂ ∪ c)) ∩ J = α₂ :=
  hPF.crosscut' hJ hab hc hcJ hcU

/-! ### 5. The hypothesis of Theorem 7 (reconnaissance — no `sorry`)

Bing states Theorem 7 for a *tree-like* plane continuum; the proof he points to (Theorem 6) uses
"contains no continuum which separates the plane". The repository will state `theorem7_1951`
(batch 120) with the latter hypothesis. The implication

    theorem treeLike_nonseparating (hPF : PlaneFacts) {M : Set Pt} (hM : IsTreeLike M) :
        ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K

is the question of item 5 of the commission: proved, refuted (not expected: it is a classical
theorem), or open with the obstruction stated. It is NOT to be added as a `sorry`, nor as a field
of `PlaneFacts`, in this batch.

Batch 131: `PlaneFacts` is now proved (`planeFacts_holds`, `HPC/Plane/Enc2.lean`), so the
question is unconditional (the hypothesis `hPF` above can be dropped).

Batch 133: closed. Under the definition of `IsTreeLike` up to batch 132 (links not required to be
bounded) the statement was false: every continuum satisfied that definition
(`isTreeLikeOld_of_isContinuum`). With bounded links (`Tree67.lean`, repaired in batch 133) it is
proved: `HPC.Plane.treeLike_nonseparating` in `TreeLikeNS.lean`, which also gives Theorem 7 as
printed (`theorem7_1951_treeLike`) and Theorem 6 with its converse
(`isTreeLike_iff_nonseparating`). -/

end HPC.Plane
