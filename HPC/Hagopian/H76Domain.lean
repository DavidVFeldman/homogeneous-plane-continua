import HPC.Hagopian.H76T9Full

/-!
# Batch 166, item A: the domain under a crossing arc (collar coordinates)

`rect_domain_aux`: for an arc `I` from the left edge to the right edge of the rectangle
`[a, b] × [0, c]`, above the bottom edge and meeting the side edges only at its ends, the curve
`I ∪ (bottom edge) ∪ (left edge up to r) ∪ (right edge up to s)` is a simple closed curve; its bounded
complementary domain (`jordan_curve_theorem`) lies in the open rectangle.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- The complement of a closed rectangle in the plane is connected and unbounded. -/
theorem isConnected_compl_rect (a b c d : ℝ) :
    IsConnected (Icc a b ×ˢ Icc c d : Set (ℝ × ℝ))ᶜ ∧
      ¬ Bornology.IsBounded (Icc a b ×ˢ Icc c d : Set (ℝ × ℝ))ᶜ := by
  set H1 : Set (ℝ × ℝ) := {p | b < p.1}
  set H2 : Set (ℝ × ℝ) := {p | p.1 < a}
  set H3 : Set (ℝ × ℝ) := {p | d < p.2}
  set H4 : Set (ℝ × ℝ) := {p | p.2 < c}
  have hcv : ∀ (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (e : ℝ), IsPreconnected {p : ℝ × ℝ | e < f p} ∧
      IsPreconnected {p : ℝ × ℝ | f p < e} := fun f e =>
    ⟨(convex_halfSpace_gt f.isLinear e).isPreconnected,
      (convex_halfSpace_lt f.isLinear e).isPreconnected⟩
  have p1 : IsPreconnected H1 := (hcv (LinearMap.fst ℝ ℝ ℝ) _).1
  have p2 : IsPreconnected H2 := (hcv (LinearMap.fst ℝ ℝ ℝ) _).2
  have p3 : IsPreconnected H3 := (hcv (LinearMap.snd ℝ ℝ ℝ) _).1
  have p4 : IsPreconnected H4 := (hcv (LinearMap.snd ℝ ℝ ℝ) _).2
  have heq : (Icc a b ×ˢ Icc c d : Set (ℝ × ℝ))ᶜ = H1 ∪ H3 ∪ H2 ∪ H4 := by
    ext p
    simp only [mem_compl_iff, mem_prod, mem_Icc, H1, H2, H3, H4, mem_union, mem_setOf_eq]
    constructor
    · intro h
      by_contra h'
      simp only [not_or, not_lt] at h'
      exact h ⟨⟨h'.1.2, h'.1.1.1⟩, h'.2, h'.1.1.2⟩
    · rintro (((h | h) | h) | h) ⟨⟨h1, h2⟩, h3, h4⟩ <;> linarith
  have e1 : ((b + 1, d + 1) : ℝ × ℝ) ∈ H1 := show b < b + 1 by linarith
  have e3 : ((b + 1, d + 1) : ℝ × ℝ) ∈ H3 := show d < d + 1 by linarith
  have f3 : ((a - 1, d + 1) : ℝ × ℝ) ∈ H3 := show d < d + 1 by linarith
  have f2 : ((a - 1, d + 1) : ℝ × ℝ) ∈ H2 := show a - 1 < a by linarith
  have g1 : ((b + 1, c - 1) : ℝ × ℝ) ∈ H1 := show b < b + 1 by linarith
  have g4 : ((b + 1, c - 1) : ℝ × ℝ) ∈ H4 := show c - 1 < c by linarith
  have q13 : IsPreconnected (H1 ∪ H3) := p1.union _ e1 e3 p3
  have q132 : IsPreconnected (H1 ∪ H3 ∪ H2) := q13.union _ (Or.inr f3) f2 p2
  have q : IsPreconnected (H1 ∪ H3 ∪ H2 ∪ H4) := q132.union _ (Or.inl (Or.inl g1)) g4 p4
  have hne : (H1 ∪ H3 ∪ H2 ∪ H4).Nonempty := ⟨_, Or.inl (Or.inl (Or.inl e1))⟩
  refine ⟨heq ▸ ⟨hne, q⟩, fun hb => ?_⟩
  have hR : Bornology.IsBounded (Icc a b ×ˢ Icc c d : Set (ℝ × ℝ)) :=
    (isCompact_Icc.prod isCompact_Icc).isBounded
  have : Bornology.IsBounded (univ : Set (ℝ × ℝ)) := by
    rw [← compl_union_self (Icc a b ×ˢ Icc c d : Set (ℝ × ℝ))]; exact hb.union hR
  exact NormedSpace.unbounded_univ ℝ (ℝ × ℝ) this

/-- The `U`-shaped frame `{a} × [0, r₂] ∪ [a, b] × {0} ∪ {b} × [0, s₂]` is an arc from `(a, r₂)` to
`(b, s₂)` when `a < b`, `0 < r₂`, `0 < s₂`. -/
theorem tarc_frame {a b r₂ s₂ : ℝ} (hab : a < b) (hr : 0 < r₂) (hs : 0 < s₂) :
    TArc ((a, r₂) : Pt) (b, s₂)
      (({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ Icc a b ×ˢ {0} ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂) := by
  have h1 := tarc_vseg a hr.ne'
  have h2 := tarc_hseg 0 hab.ne
  have h3 := tarc_vseg b hs.ne
  rw [uIcc_of_ge hr.le] at h1
  rw [uIcc_of_le hab.le] at h2
  rw [uIcc_of_le hs.le] at h3
  have h12 : ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∩ Icc a b ×ˢ {0} = {((a, 0) : Pt)} := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨rfl, -⟩, -, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, le_rfl, hr.le⟩, ⟨le_rfl, hab.le⟩, rfl⟩
  have h123 : (({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ Icc a b ×ˢ {0}) ∩ ({b} : Set ℝ) ×ˢ Icc 0 s₂ =
      {((b, 0) : Pt)} := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_union, mem_prod, mem_singleton_iff, mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨(⟨rfl, -⟩ | ⟨-, rfl⟩), rfl, -⟩
      · exact absurd hab (lt_irrefl _)
      · exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨Or.inr ⟨⟨hab.le, le_rfl⟩, rfl⟩, rfl, le_rfl, hs.le⟩
  exact (h1.union h2 h12).union h3 h123

/-- **The domain under a crossing arc** (statement of `rect_domain`). -/
theorem rect_domain_aux {a b c : ℝ} (hab : a < b) (hc : 0 < c) {r s : ℝ × ℝ} {I : Set (ℝ × ℝ)}
    (hI : TArc r s I) (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hr : r.1 = a) (hs : s.1 = b)
    (hIs : I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s}) :
    ∃ D : Set (ℝ × ℝ), IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
      D ⊆ Ioo a b ×ˢ Ioo 0 c ∧
      frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
        ({b} : Set ℝ) ×ˢ Icc 0 s.2 := by
  have hrI := hIR hI.left_mem
  have hsI := hIR hI.right_mem
  have hr2 : 0 < r.2 := hrI.2.1
  have hs2 : 0 < s.2 := hsI.2.1
  set U : Set (ℝ × ℝ) :=
    ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪ Icc a b ×ˢ {0} ∪ ({b} : Set ℝ) ×ˢ Icc 0 s.2 with hUdef
  have hU : TArc r s U := by
    have h := tarc_frame hab hr2 hs2
    rwa [show ((a, r.2) : Pt) = r from Prod.ext hr.symm rfl,
      show ((b, s.2) : Pt) = s from Prod.ext hs.symm rfl] at h
  have hUR : U ⊆ Icc a b ×ˢ Icc 0 c := by
    rintro ⟨x, y⟩ ((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩)
    · simp only [mem_singleton_iff] at hx; subst hx
      exact ⟨⟨le_rfl, hab.le⟩, hy.1, hy.2.trans hrI.2.2⟩
    · simp only [mem_singleton_iff] at hy; subst hy
      exact ⟨hx, le_rfl, hc.le⟩
    · simp only [mem_singleton_iff] at hx; subst hx
      exact ⟨⟨hab.le, le_rfl⟩, hy.1, hy.2.trans hsI.2.2⟩
  have hIU : I ∩ U = {r, s} := by
    apply subset_antisymm
    · rintro p ⟨hpI, hpU⟩
      rw [← hIs]
      refine ⟨hpI, ?_⟩
      have hpR := hIR hpI
      obtain ⟨x, y⟩ := p
      rcases hpU with ((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩)
      · simp only [mem_singleton_iff] at hx; subst hx
        exact ⟨Or.inl rfl, hpR.2.1.le, hpR.2.2⟩
      · simp only [mem_singleton_iff] at hy; subst hy
        exact absurd hpR.2.1 (lt_irrefl _)
      · simp only [mem_singleton_iff] at hx; subst hx
        exact ⟨Or.inr rfl, hpR.2.1.le, hpR.2.2⟩
    · rintro p (rfl | rfl)
      · exact ⟨hI.left_mem, hU.left_mem⟩
      · exact ⟨hI.right_mem, hU.right_mem⟩
  have hJ : TSCC (I ∪ U) := ⟨r, s, I, U, hI, hU, hIU, rfl⟩
  obtain ⟨D, O, hDo, hDc, hOo, hOc, hDO, hDOu, hDb, hOb, hDf, -⟩ :=
    jordan_curve_theorem (tscc_homeomorph_circle hJ)
  have hJR : I ∪ U ⊆ Icc a b ×ˢ Icc 0 c :=
    union_subset (hIR.trans (prod_mono subset_rfl Ioc_subset_Icc_self)) hUR
  obtain ⟨hCc, hCb⟩ := isConnected_compl_rect a b 0 c
  have hCsub : (Icc a b ×ˢ Icc 0 c : Set (ℝ × ℝ))ᶜ ⊆ D ∪ O := by
    rw [hDOu]; exact compl_subset_compl.2 hJR
  have hDR : D ⊆ Icc a b ×ˢ Icc 0 c := by
    rcases hCc.isPreconnected.subset_or_subset hDo hOo hDO hCsub with h | h
    · exact absurd (hDb.subset h) hCb
    · intro p hp
      by_contra hpR
      exact disjoint_left.1 hDO hp (h hpR)
  refine ⟨D, hDo, hDc, hDb, ?_, ?_⟩
  · have := interior_maximal hDR hDo
    rwa [interior_prod_eq, interior_Icc, interior_Icc] at this
  · rw [hDf, hUdef]
    ext p
    simp only [mem_union]
    tauto

/-- **The low strip lies in the domain.** If `D` is open, lies in the open rectangle and has the
frame curve as frontier, and `I` stays at height `≥ c₀ > 0`, then `(a, b) × (0, c₀) ⊆ D`. (The middle
of the bottom edge is a frontier point of `D`; the strip is connected and misses the frontier.) -/
theorem rect_domain_low {a b c : ℝ} (hab : a < b) {r s : ℝ × ℝ} {I D : Set (ℝ × ℝ)}
    (hDR : D ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
      ({b} : Set ℝ) ×ˢ Icc 0 s.2) {c₀ : ℝ} (hc₀ : 0 < c₀) (hIc : ∀ z ∈ I, c₀ ≤ z.2) :
    Ioo a b ×ˢ Ioo 0 c₀ ⊆ D := by
  set m : ℝ × ℝ := ((a + b) / 2, 0)
  have hm : m ∈ closure D := by
    apply frontier_subset_closure
    rw [hDf]
    exact Or.inl (Or.inl (Or.inr ⟨⟨show a ≤ (a + b) / 2 by linarith,
      show (a + b) / 2 ≤ b by linarith⟩, rfl⟩))
  obtain ⟨z, hzD, hzm⟩ := Metric.mem_closure_iff.1 hm (min c₀ ((b - a) / 2))
    (lt_min hc₀ (by linarith))
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, lt_min_iff, lt_min_iff] at hzm
  obtain ⟨-, h2, -⟩ := hzm
  have hz := hDR hzD
  have hzS : z ∈ Ioo a b ×ˢ Ioo 0 c₀ := by
    refine ⟨hz.1, hz.2.1, ?_⟩
    have := (abs_lt.1 h2).1
    simp only [m] at this
    linarith
  have hS : IsPreconnected (Ioo a b ×ˢ Ioo 0 c₀) :=
    ((convex_Ioo a b).prod (convex_Ioo 0 c₀)).isPreconnected
  refine conn_sub_of_frontier hS ?_ ⟨z, hzS, hzD⟩
  rw [hDf, disjoint_left]
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, hy1, hy2⟩ (((hI | ⟨-, hy⟩) | ⟨hx, -⟩) | ⟨hx, -⟩)
  · have := hIc _ hI; simp only at this; linarith
  · simp only [mem_singleton_iff] at hy; linarith
  · simp only [mem_singleton_iff] at hx; linarith
  · simp only [mem_singleton_iff] at hx; linarith

/-- **A vertical segment from the bottom edge up to its first point on `I` lies in the domain.** -/
theorem rect_domain_vert {a b c : ℝ} (hab : a < b) {r s : ℝ × ℝ} {I D : Set (ℝ × ℝ)}
    (hI : IsCompact I) (hI0 : ∀ z ∈ I, 0 < z.2) (hDR : D ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
      ({b} : Set ℝ) ×ˢ Icc 0 s.2) {x w : ℝ} (hx : x ∈ Ioo a b) (hw : 0 < w)
    (hxI : Disjoint (({x} : Set ℝ) ×ˢ Ioo 0 w) I) :
    ({x} : Set ℝ) ×ˢ Ioo 0 w ⊆ D := by
  obtain ⟨c₀, hc₀, -, hc₀I⟩ := exists_height_below hI hI0
  have hlow := rect_domain_low hab hDR hDf hc₀ fun z hz => (hc₀I z hz).le
  have hpt : ((x, min w c₀ / 2) : ℝ × ℝ) ∈ ({x} : Set ℝ) ×ˢ Ioo 0 w := by
    refine ⟨rfl, by positivity, ?_⟩
    have := min_le_left w c₀; show min w c₀ / 2 < w; linarith
  have hptD : ((x, min w c₀ / 2) : ℝ × ℝ) ∈ D := by
    apply hlow
    refine ⟨hx, by positivity, ?_⟩
    have := min_le_right w c₀; show min w c₀ / 2 < c₀; linarith
  have hS : IsPreconnected (({x} : Set ℝ) ×ˢ Ioo 0 w) :=
    ((convex_singleton x).prod (convex_Ioo 0 w)).isPreconnected
  refine conn_sub_of_frontier hS ?_ ⟨_, hpt, hptD⟩
  rw [hDf, disjoint_left]
  rintro ⟨x', y⟩ ⟨hx', hy1, hy2⟩ (((hI' | ⟨-, hy⟩) | ⟨hx'', -⟩) | ⟨hx'', -⟩)
  · exact disjoint_left.1 hxI ⟨hx', hy1, hy2⟩ hI'
  · simp only [mem_singleton_iff] at hy; linarith
  · simp only [mem_singleton_iff] at hx' hx''; linarith [hx.1]
  · simp only [mem_singleton_iff] at hx' hx''; linarith [hx.2]

end HPC.Hagopian
