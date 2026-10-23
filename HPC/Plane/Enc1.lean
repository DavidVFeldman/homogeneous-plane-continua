import HPC.Plane.Enc1Cyc
import HPC.Plane.Enc1Grid

/-!
# Batch 130: `enclose`, part I — the grid union, its boundary graph, simple cycles, and the
# polygon interior as the odd parity set

COMMISSION-batch130.md. The skeleton of the commission with every `sorry` replaced by a proof. The
material is spread over three files:

* `HPC/Plane/Enc1Cyc.lean`: the polygon interior as the odd parity set (`polyInterior_eq_oddSet`,
  `polyEdges`, `cycParity_polyEdges`, `graphSet_polyEdges`), simple cycles (`IsSimpleCycle`,
  `exists_simpleCycle_decomposition`, `cycParity_foldr`);
* `HPC/Plane/Enc1Grid.lean`: unions of grid squares for an arbitrary finite index set
  (`sqUnion`), their boundary edges (`bdryOf`), properness and the frontier;
* this file: the grid union of `M` (`sqIdx`, `gridUnion`, `bdryGraph`), the far point, the outer
  cycle and the enclosing polygon.

## The plan for `enclose` (batches 130–131)

The field: `M` a compact continuum not separating the plane, `G ⊇ M` open ⇒ a simple closed
polygon `J` with `J ∩ M = ∅`, `M ⊆ polyInterior J ⊆ G`. The construction avoids the classification
of polyomino boundaries:

1. **The grid union.** With mesh `δ` and offset `0`, `Q :=` the union of the closed grid squares
   meeting `cthickening δ M`. Then `M ∩ frontier Q = ∅`, `Q ⊆ cthickening (2δ) M`, and
   `frontier Q` is the union of the **boundary edges**: the grid edges of the squares of `Q`
   that belong to exactly one square of `Q`. These form a proper graph `G₀` of segments.
2. **The outer cycle.** Let `y` be a far point and `K := connectedComponentIn (graphSet G₀)ᶜ y`.
   By batch 128, `Z := oddSet G₀ y` is a cycle and `gFun G₀ y = [· ∈ K] + cycParity Z` is constant
   off `graphSet G₀`. A point `x ∈ M` lies in `interior Q`, hence not in `K`, so
   `cycParity Z x = 1`.
3. **Simple cycles.** `Z` is an edge-disjoint union of simple cycles; parity is additive, and
   each parity is constant on the connected `M`, so one simple cycle `J` has parity `1` on `M`,
   i.e. `M ⊆ polyInterior J`.
4. **Inside `G`** (batch 131).

Changes of shape (recorded in REPORT-batch130):

* `bdryGraph M δ` is defined as `bdryOf δ (sqIdx M δ)`, indexing boundary edges directly by the
  "exclusive or" of the two squares an edge belongs to; `mem_bdryGraph_iff_card` proves it is the
  set of edges of squares of `sqIdx` belonging to exactly one square of `sqIdx`, the docstring of
  the skeleton.
* Unused hypotheses are dropped: `hM` from `isProper_bdryGraph`, `frontier_gridUnion`,
  `graphSet_bdryGraph_subset`, `interior_gridUnion_disjoint_component`; `hM`, `hδ` from
  `isCompact_gridUnion` (none there already) and `farPt_not_mem`.
-/

namespace HPC.Plane

open Set Metric

/-! ### The grid union -/

/-- The index set of the squares meeting `cthickening δ M` (finite for bounded `M`, `δ > 0`;
empty by convention otherwise). -/
noncomputable def sqIdx (M : Set Pt) (δ : ℝ) : Finset (ℤ × ℤ) :=
  open Classical in
  if h : {ab : ℤ × ℤ | (gsq δ ab.1 ab.2 ∩ cthickening δ M).Nonempty}.Finite then h.toFinset else ∅

/-- The grid union. -/
def gridUnion (M : Set Pt) (δ : ℝ) : Set Pt := ⋃ ab ∈ sqIdx M δ, gsq δ ab.1 ab.2

theorem gridUnion_eq (M : Set Pt) (δ : ℝ) : gridUnion M δ = sqUnion δ (sqIdx M δ) := rfl

theorem finite_sqIdx_set {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) :
    {ab : ℤ × ℤ | (gsq δ ab.1 ab.2 ∩ cthickening δ M).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := (hM.cthickening (δ := δ)).subset_closedBall 0
  set N : ℤ := ⌈R / δ⌉ + 1 with hN_def
  have hN : R + δ ≤ δ * (N : ℝ) := by
    have h1 : R / δ + 1 ≤ (N : ℝ) := by
      rw [hN_def]; push_cast; linarith [Int.le_ceil (R / δ)]
    calc R + δ = δ * (R / δ + 1) := by field_simp
      _ ≤ δ * N := by gcongr
  have key : ∀ (a : ℤ) (t : ℝ), |t| ≤ R → δ * a ≤ t → t ≤ δ * (a + 1) → a ∈ Icc (-N) N := by
    intro a t ht h1 h2
    rw [abs_le] at ht
    exact ⟨int_le_of_mul_le hδ (by push_cast; linarith),
      (int_lt_of_mul_lt hδ (by linarith)).le⟩
  refine ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset ?_
  rintro ⟨a, b⟩ ⟨z, hz, hzM⟩
  have hzR := hR hzM
  rw [mem_closedBall, dist_zero_right] at hzR
  have h1 : |z.1| ≤ R := by
    have := norm_fst_le z
    rw [Real.norm_eq_abs] at this
    linarith
  have h2 : |z.2| ≤ R := by
    have := norm_snd_le z
    rw [Real.norm_eq_abs] at this
    linarith
  rw [mem_gsq] at hz
  exact ⟨key a z.1 h1 hz.1.1 hz.1.2, key b z.2 h2 hz.2.1 hz.2.2⟩

theorem mem_sqIdx_iff {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) (ab : ℤ × ℤ) :
    ab ∈ sqIdx M δ ↔ (gsq δ ab.1 ab.2 ∩ cthickening δ M).Nonempty := by
  unfold sqIdx
  rw [dif_pos (finite_sqIdx_set hM hδ), Set.Finite.mem_toFinset]
  rfl

theorem gridUnion_subset_cthickening {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ}
    (hδ : 0 < δ) : gridUnion M δ ⊆ cthickening (2 * δ) M := by
  intro x hx
  rw [gridUnion_eq, mem_sqUnion] at hx
  obtain ⟨a, b, hab, hx⟩ := hx
  obtain ⟨y, hy, hyM⟩ := (mem_sqIdx_iff hM hδ _).1 hab
  have hd : dist x y ≤ δ := by
    rw [mem_gsq] at hx hy
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
    constructor <;> rw [abs_le] <;> constructor <;> push_cast at * <;> linarith
  have := Metric.mem_cthickening_of_dist_le x y δ _ hyM hd
  rw [two_mul]
  exact cthickening_cthickening_subset hδ.le hδ.le M this

theorem isCompact_gridUnion (M : Set Pt) (δ : ℝ) : IsCompact (gridUnion M δ) :=
  isCompact_sqUnion δ _

/-- **`M` misses the frontier of the grid union**: a point of `M` lies in every square containing
it, all of which are in `sqIdx`; and a frontier point lies in a square not in `sqIdx`
(`mem_frontier_sqUnion_iff`). -/
theorem disjoint_frontier_gridUnion {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ}
    (hδ : 0 < δ) : Disjoint M (frontier (gridUnion M δ)) := by
  rw [Set.disjoint_left]
  intro z hzM hzF
  rw [gridUnion_eq, mem_frontier_sqUnion_iff hδ] at hzF
  obtain ⟨a, b, a', b', -, hab', -, hz'⟩ := hzF
  exact hab' ((mem_sqIdx_iff hM hδ _).2 ⟨z, hz', self_subset_cthickening M hzM⟩)

/-- Points of `M` are interior to the grid union. -/
theorem subset_interior_gridUnion {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ}
    (hδ : 0 < δ) : M ⊆ interior (gridUnion M δ) := fun x hx =>
  mem_interior_sqUnion hδ fun _ _ hz =>
    (mem_sqIdx_iff hM hδ _).2 ⟨x, hz, self_subset_cthickening M hx⟩

open Classical in
/-- The four edges of a grid square, as lexicographically oriented segments. -/
noncomputable def sqEdges (δ : ℝ) (a b : ℤ) : Finset Seg :=
  {hseg δ a b, hseg δ a (b + 1), vseg δ a b, vseg δ (a + 1) b}

/-- **The boundary graph**: the edges of the squares of `sqIdx` that belong to exactly one
square of `sqIdx` (`mem_bdryGraph_iff_card`). -/
noncomputable def bdryGraph (M : Set Pt) (δ : ℝ) : Finset Seg := bdryOf δ (sqIdx M δ)

/-- The boundary graph is a proper graph. (Hypothesis `hM` of the skeleton dropped.) -/
theorem isProper_bdryGraph (M : Set Pt) {δ : ℝ} (hδ : 0 < δ) : IsProper (bdryGraph M δ) :=
  isProper_bdryOf hδ _

/-- **The frontier of the grid union is the boundary graph.** (Hypothesis `hM` of the skeleton
dropped.) -/
theorem frontier_gridUnion (M : Set Pt) {δ : ℝ} (hδ : 0 < δ) :
    frontier (gridUnion M δ) = graphSet (bdryGraph M δ) :=
  frontier_sqUnion hδ _

/-- The boundary graph lies in the grid union. (Hypothesis `hM` of the skeleton dropped.) -/
theorem graphSet_bdryGraph_subset (M : Set Pt) {δ : ℝ} (hδ : 0 < δ) :
    graphSet (bdryGraph M δ) ⊆ gridUnion M δ := by
  rw [← frontier_gridUnion M hδ]
  exact frontier_subset_closure.trans (isCompact_gridUnion M δ).isClosed.closure_eq.subset

theorem mem_sqEdges {δ : ℝ} {a b : ℤ} {s : Seg} : s ∈ sqEdges δ a b ↔
    s = hseg δ a b ∨ s = hseg δ a (b + 1) ∨ s = vseg δ a b ∨ s = vseg δ (a + 1) b := by
  classical
  simp [sqEdges]

theorem hseg_inj {δ : ℝ} (hδ : δ ≠ 0) {a b a' b' : ℤ} :
    hseg δ a b = hseg δ a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    simp only [hseg, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, -⟩ := h
    exact ⟨by exact_mod_cast mul_left_cancel₀ hδ h1, by exact_mod_cast mul_left_cancel₀ hδ h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem vseg_inj {δ : ℝ} (hδ : δ ≠ 0) {a b a' b' : ℤ} :
    vseg δ a b = vseg δ a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    simp only [vseg, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, -⟩ := h
    exact ⟨by exact_mod_cast mul_left_cancel₀ hδ h1, by exact_mod_cast mul_left_cancel₀ hδ h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem hseg_ne_vseg {δ : ℝ} (hδ : δ ≠ 0) (a b a' b' : ℤ) : hseg δ a b ≠ vseg δ a' b' := by
  intro h
  simp only [hseg, vseg, Prod.mk.injEq] at h
  obtain ⟨⟨h1, -⟩, h3, -⟩ := h
  have := mul_left_cancel₀ hδ (h3.trans h1.symm)
  linarith

theorem card_filter_eq_one_iff_xor {S : Finset (ℤ × ℤ)} {p q : ℤ × ℤ} (hpq : p ≠ q)
    {P : ℤ × ℤ → Prop} [DecidablePred P] (hP : ∀ x, P x ↔ x = p ∨ x = q) :
    (S.filter P).card = 1 ↔ Xor' (p ∈ S) (q ∈ S) := by
  classical
  have hS : S.filter P = (S.filter (· = p)) ∪ (S.filter (· = q)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, hP]
    tauto
  have hd : Disjoint (S.filter (· = p)) (S.filter (· = q)) :=
    Finset.disjoint_filter.2 fun x _ h1 h2 => hpq (h1.symm.trans h2)
  have hc : ∀ r, (S.filter (· = r)).card = if r ∈ S then 1 else 0 := by
    intro r
    split_ifs with hr
    · rw [Finset.card_eq_one]
      exact ⟨r, by ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor <;>
        [exact fun h => h.2; exact fun h => ⟨h ▸ hr, h⟩]⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun x hx h => hr (h ▸ hx)
  rw [hS, Finset.card_union_of_disjoint hd, hc, hc]
  by_cases hp : p ∈ S <;> by_cases hq : q ∈ S <;> simp [hp, hq]

/-- **The boundary graph is the set of edges of squares of `sqIdx` belonging to exactly one square
of `sqIdx`** (the skeleton's description of `bdryGraph`). -/
theorem mem_bdryGraph_iff_card (M : Set Pt) {δ : ℝ} (hδ : 0 < δ) (s : Seg) :
    s ∈ bdryGraph M δ ↔
      ((sqIdx M δ).filter fun ab => s ∈ sqEdges δ ab.1 ab.2).card = 1 := by
  classical
  have hδ0 : δ ≠ 0 := hδ.ne'
  unfold bdryGraph
  rw [mem_bdryOf]
  by_cases hs : ∃ a b, s = hseg δ a b
  · obtain ⟨a, b, rfl⟩ := hs
    rw [card_filter_eq_one_iff_xor (p := (a, b)) (q := (a, b - 1))
      (fun h => by simp only [Prod.mk.injEq] at h; omega) fun x => ?_]
    · constructor
      · rintro (⟨a', b', hx, h⟩ | ⟨a', b', hx, h⟩)
        · obtain ⟨rfl, rfl⟩ := (hseg_inj hδ0).1 h
          exact hx
        · exact absurd h (hseg_ne_vseg hδ0 _ _ _ _)
      · exact fun hx => Or.inl ⟨a, b, hx, rfl⟩
    · obtain ⟨a', b'⟩ := x
      have h1 := hseg_ne_vseg hδ0 a b a' b'
      have h2 := hseg_ne_vseg hδ0 a b (a' + 1) b'
      simp only [mem_sqEdges, hseg_inj hδ0, h1, h2, or_false, Prod.mk.injEq]
      omega
  by_cases hv : ∃ a b, s = vseg δ a b
  · obtain ⟨a, b, rfl⟩ := hv
    rw [card_filter_eq_one_iff_xor (p := (a, b)) (q := (a - 1, b))
      (fun h => by simp only [Prod.mk.injEq] at h; omega) fun x => ?_]
    · constructor
      · rintro (⟨a', b', hx, h⟩ | ⟨a', b', hx, h⟩)
        · exact absurd h.symm (hseg_ne_vseg hδ0 _ _ _ _)
        · obtain ⟨rfl, rfl⟩ := (vseg_inj hδ0).1 h
          exact hx
      · exact fun hx => Or.inr ⟨a, b, hx, rfl⟩
    · obtain ⟨a', b'⟩ := x
      have h1 := hseg_ne_vseg hδ0 a' b' a b
      have h2 := hseg_ne_vseg hδ0 a' (b' + 1) a b
      simp only [mem_sqEdges, vseg_inj hδ0, Ne.symm h1, Ne.symm h2, false_or, Prod.mk.injEq]
      omega
  · push_neg at hs hv
    have : (sqIdx M δ).filter (fun ab => s ∈ sqEdges δ ab.1 ab.2) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro ab _ h
      rcases mem_sqEdges.1 h with h | h | h | h
      · exact hs _ _ h
      · exact hs _ _ h
      · exact hv _ _ h
      · exact hv _ _ h
    rw [this, Finset.card_empty]
    simp only [zero_ne_one, iff_false, not_or, not_exists, not_and]
    exact ⟨fun a b _ h => hs a b h, fun a b _ h => hv a b h⟩

/-! ### The outer cycle and the enclosing polygon -/

/-- The largest abscissa of the grid union (`0` if it is empty). -/
noncomputable def gridR (M : Set Pt) (δ : ℝ) : ℝ := sSup (Prod.fst '' gridUnion M δ)

/-- A far point: beyond everything, east. -/
noncomputable def farPt (M : Set Pt) (δ : ℝ) : Pt := (gridR M δ + 1, 0)

theorem fst_le_gridR {M : Set Pt} {δ : ℝ} {x : Pt} (hx : x ∈ gridUnion M δ) : x.1 ≤ gridR M δ :=
  le_csSup ((isCompact_gridUnion M δ).bddAbove_image continuous_fst.continuousOn)
    (mem_image_of_mem _ hx)

/-- The far point is outside the grid union. (No hypotheses needed.) -/
theorem farPt_not_mem (M : Set Pt) (δ : ℝ) : farPt M δ ∉ gridUnion M δ := fun h => by
  have := fst_le_gridR h
  simp only [farPt] at this
  linarith

/-- The half-plane east of the grid union lies in the component of the far point. -/
theorem halfPlane_subset_component (M : Set Pt) {δ : ℝ} (hδ : 0 < δ) :
    Ioi (gridR M δ) ×ˢ (univ : Set ℝ) ⊆
      connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ) := by
  refine (isPreconnected_Ioi.prod isPreconnected_univ).subset_connectedComponentIn
    ⟨by simp [farPt], mem_univ _⟩ fun z hz hzG => ?_
  have := fst_le_gridR (graphSet_bdryGraph_subset M hδ hzG)
  exact absurd hz.1 (not_lt.2 this)

theorem farPt_not_mem_graphSet (M : Set Pt) {δ : ℝ} (hδ : 0 < δ) :
    farPt M δ ∉ graphSet (bdryGraph M δ) := fun h =>
  farPt_not_mem M δ (graphSet_bdryGraph_subset M hδ h)

theorem not_isBounded_component (M : Set Pt) {δ : ℝ} (hδ : 0 < δ) :
    ¬ Bornology.IsBounded (connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)) := by
  intro hb
  obtain ⟨r, hr⟩ := (hb.subset (halfPlane_subset_component M hδ)).subset_closedBall 0
  set t : ℝ := max (gridR M δ) r + 1
  have hmem : ((t, 0) : Pt) ∈ Ioi (gridR M δ) ×ˢ (univ : Set ℝ) :=
    ⟨by simp only [mem_Ioi, t]; linarith [le_max_left (gridR M δ) r], mem_univ _⟩
  have := hr hmem
  rw [mem_closedBall, dist_zero_right] at this
  have h1 := norm_fst_le ((t, 0) : Pt)
  simp only [Real.norm_eq_abs] at h1
  have h2 : t ≤ |t| := le_abs_self t
  linarith [le_max_right (gridR M δ) r]

/-- **The interior of the grid union lies outside the unbounded component**. (Hypothesis `hM` of
the skeleton dropped.) -/
theorem interior_gridUnion_disjoint_component (M : Set Pt) {δ : ℝ} (hδ : 0 < δ) :
    Disjoint (interior (gridUnion M δ))
      (connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)) := by
  set Q := gridUnion M δ
  set K := connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)
  have hQc : IsClosed Q := (isCompact_gridUnion M δ).isClosed
  have hsub : K ⊆ Qᶜ ∪ interior Q := by
    intro z hz
    have hzF : z ∉ frontier Q := by
      rw [frontier_gridUnion M hδ]
      exact connectedComponentIn_subset _ _ hz
    by_cases hzQ : z ∈ Q
    · right
      by_contra hi
      exact hzF ⟨subset_closure hzQ, hi⟩
    · exact Or.inl hzQ
  have hKQ : K ⊆ Qᶜ :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hQc.isOpen_compl
      isOpen_interior (disjoint_compl_left.mono_right interior_subset) hsub
      ⟨farPt M δ, mem_connectedComponentIn (farPt_not_mem_graphSet M hδ), farPt_not_mem M δ⟩
  exact (disjoint_compl_left.mono_right interior_subset).symm.mono_right hKQ

/-- **Points of `M` have odd parity for the outer cycle.** -/
theorem cycParity_oddSet_eq_one_on {M : Set Pt} (hM : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ)
    {x : Pt} (hx : x ∈ M) :
    cycParity (oddSet (bdryGraph M δ) (farPt M δ)) x = 1 := by
  classical
  set G := bdryGraph M δ
  set K := connectedComponentIn (graphSet G)ᶜ (farPt M δ)
  have hxG : x ∉ graphSet G := by
    rw [← frontier_gridUnion M hδ]
    exact Set.disjoint_left.1 (disjoint_frontier_gridUnion hM hδ) hx
  have hxK : x ∉ K := Set.disjoint_left.1 (interior_gridUnion_disjoint_component M hδ)
    (subset_interior_gridUnion hM hδ hx)
  obtain ⟨R, hR⟩ := cycParity_far (oddSet G (farPt M δ))
  set y : Pt := (max R (gridR M δ) + 1, 0)
  have hyH : y ∈ Ioi (gridR M δ) ×ˢ (univ : Set ℝ) :=
    ⟨by simp only [mem_Ioi, y]; linarith [le_max_right R (gridR M δ)], mem_univ _⟩
  have hyK : y ∈ K := halfPlane_subset_component M hδ hyH
  have hyG : y ∉ graphSet G := connectedComponentIn_subset _ _ hyK
  have h := gFun_const (isProper_bdryGraph M hδ) (farPt M δ) hxG hyG
  unfold gFun at h
  rw [if_neg hxK, if_pos hyK, hR y (by simp only [y]; linarith [le_max_left R (gridR M δ)]),
    zero_add, add_zero] at h
  exact h

/-- **The enclosing polygon, inside the complement of the unbounded component.** -/
theorem exists_enclosing_polygon {M : Set Pt} (hM : Fold.Q78.IsContinuum M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ J ⊆ graphSet (bdryGraph M δ) ∧ Disjoint J M ∧
      M ⊆ polyInterior J ∧
      Disjoint (polyInterior J) (connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)) := by
  have hMb : Bornology.IsBounded M := hM.1.isBounded
  set G := bdryGraph M δ
  obtain ⟨L, hLs, hLZ, hLd, hZL⟩ :=
    exists_simpleCycle_decomposition (isCycle_oddSet (isProper_bdryGraph M hδ) (farPt M δ))
  obtain ⟨x0, hx0⟩ := hM.2.nonempty
  have hsum : (L.map fun C => cycParity C x0).sum = 1 := by
    rw [← cycParity_foldr hLd, ← hZL]
    exact cycParity_oddSet_eq_one_on hMb hδ hx0
  obtain ⟨C, hCL, hC1⟩ : ∃ C ∈ L, cycParity C x0 = 1 := by
    by_contra hcon
    push_neg at hcon
    have : (L.map fun C => cycParity C x0).sum = 0 := by
      refine List.sum_eq_zero fun a ha => ?_
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 ha
      rcases zmod2_cases (cycParity C x0) 0 with h | h
      · exact h
      · exact absurd (by simpa using h) (hcon C hC)
    rw [this] at hsum
    exact zero_ne_one hsum
  obtain ⟨n, v, hv, hgC, hpar⟩ := hLs C hCL
  have hJG : polygonOf v ⊆ graphSet G :=
    hgC ▸ graphSet_mono ((hLZ C hCL).trans (oddSet_subset _ _))
  have hMJ : Disjoint (polygonOf v) M := by
    have := disjoint_frontier_gridUnion hMb hδ
    rw [frontier_gridUnion M hδ] at this
    exact (this.mono_right hJG).symm
  refine ⟨polygonOf v, isSimpleClosedPolygon_iff.2 ⟨n, v, hv, rfl⟩, hJG, hMJ, ?_, ?_⟩
  · intro x hx
    rw [polyInterior_eq_oddSet hv]
    refine ⟨Set.disjoint_right.1 hMJ hx, ?_⟩
    rw [parity_eq_of_isPreconnected hM.2.isPreconnected hMJ.symm.subset_compl_right hx hx0,
      ← hpar, hC1]
  · set K := connectedComponentIn (graphSet G)ᶜ (farPt M δ)
    have hK : IsConnected K :=
      isConnected_connectedComponentIn_iff.2 (farPt_not_mem_graphSet M hδ)
    have hKJ : Disjoint K (polygonOf v) :=
      Set.disjoint_left.2 fun z hz hzJ => connectedComponentIn_subset _ _ hz (hJG hzJ)
    exact (polyInterior_disjoint_of_unbounded hK (not_isBounded_component M hδ) hKJ).symm

end HPC.Plane
