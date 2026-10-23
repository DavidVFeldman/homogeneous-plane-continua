import HPC.Hagopian.H76Adapt

/-!
# Batch 163, item A: the rectangle `(0, 1) × (-1, 0)` cut at `(y, 0)` and `(x₀, -1)`

Elementary facts about the two boundary arcs of the lower unit rectangle between a point of its
top edge and a point of its bottom edge.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- The left boundary arc of `[0, 1] × [-1, 0]` from `(y, 0)` to `(x₀, -1)`. -/
def rectC₁ (y x₀ : ℝ) : Set Pt :=
  (Icc 0 y ×ˢ {(0 : ℝ)}) ∪ ({(0 : ℝ)} ×ˢ Icc (-1) 0) ∪ (Icc 0 x₀ ×ˢ {(-1 : ℝ)})

/-- The right boundary arc of `[0, 1] × [-1, 0]` from `(y, 0)` to `(x₀, -1)`. -/
def rectC₂ (y x₀ : ℝ) : Set Pt :=
  (Icc y 1 ×ˢ {(0 : ℝ)}) ∪ ({(1 : ℝ)} ×ˢ Icc (-1) 0) ∪ (Icc x₀ 1 ×ˢ {(-1 : ℝ)})

theorem rect_frontier {y x₀ : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hx0 : 0 < x₀) (hx1 : x₀ < 1) :
    frontier (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0) = rectC₁ y x₀ ∪ rectC₂ y x₀ := by
  rw [frontier_prod_eq, closure_Ioo (by norm_num), closure_Ioo (by norm_num),
    frontier_Ioo (by norm_num), frontier_Ioo (by norm_num)]
  ext ⟨p, q⟩
  simp only [rectC₁, rectC₂, mem_union, mem_prod, mem_Icc, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (⟨⟨h1, h2⟩, rfl | rfl⟩ | ⟨rfl | rfl, h3, h4⟩)
    · rcases le_total p x₀ with h | h
      · exact Or.inl (Or.inr ⟨⟨h1, h⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨⟨h, h2⟩, rfl⟩)
    · rcases le_total p y with h | h
      · exact Or.inl (Or.inl (Or.inl ⟨⟨h1, h⟩, rfl⟩))
      · exact Or.inr (Or.inl (Or.inl ⟨⟨h, h2⟩, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨rfl, h3, h4⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, h3, h4⟩))
  · rintro (((⟨⟨h1, h2⟩, rfl⟩ | ⟨rfl, h3, h4⟩) | ⟨⟨h1, h2⟩, rfl⟩) |
      ((⟨⟨h1, h2⟩, rfl⟩ | ⟨rfl, h3, h4⟩) | ⟨⟨h1, h2⟩, rfl⟩))
    · exact Or.inl ⟨⟨h1, by linarith⟩, Or.inr rfl⟩
    · exact Or.inr ⟨Or.inl rfl, h3, h4⟩
    · exact Or.inl ⟨⟨h1, by linarith⟩, Or.inl rfl⟩
    · exact Or.inl ⟨⟨by linarith, h2⟩, Or.inr rfl⟩
    · exact Or.inr ⟨Or.inr rfl, h3, h4⟩
    · exact Or.inl ⟨⟨by linarith, h2⟩, Or.inl rfl⟩

theorem rect_tarc₁ {y x₀ : ℝ} (hy0 : 0 < y) (hx0 : 0 < x₀) :
    TArc ((y, 0) : Pt) (x₀, -1) (rectC₁ y x₀) := by
  have s1 := tarc_hseg (0 : ℝ) hy0.ne'
  have s2 := tarc_vseg (0 : ℝ) (by norm_num : (0 : ℝ) ≠ -1)
  have s3 := tarc_hseg (-1 : ℝ) hx0.ne
  rw [uIcc_of_ge hy0.le] at s1
  rw [uIcc_of_ge (by norm_num : (-1 : ℝ) ≤ 0)] at s2
  rw [uIcc_of_le hx0.le] at s3
  have s12 := TArc.union s1 s2 (by
    ext ⟨p, q⟩
    simp only [mem_inter_iff, mem_prod, mem_Icc, mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨-, rfl⟩, rfl, -⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨⟨le_rfl, hy0.le⟩, rfl⟩, rfl, by norm_num, le_rfl⟩)
  exact TArc.union s12 s3 (by
    ext ⟨p, q⟩
    simp only [mem_inter_iff, mem_union, mem_prod, mem_Icc, mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨(⟨-, rfl⟩ | ⟨rfl, -⟩), -, h⟩
      · norm_num at h
      · exact ⟨rfl, h⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨Or.inr ⟨rfl, le_rfl, by norm_num⟩, ⟨le_rfl, hx0.le⟩, rfl⟩)

theorem rect_tarc₂ {y x₀ : ℝ} (hy1 : y < 1) (hx1 : x₀ < 1) :
    TArc ((y, 0) : Pt) (x₀, -1) (rectC₂ y x₀) := by
  have s1 := tarc_hseg (0 : ℝ) hy1.ne
  have s2 := tarc_vseg (1 : ℝ) (by norm_num : (0 : ℝ) ≠ -1)
  have s3 := tarc_hseg (-1 : ℝ) hx1.ne'
  rw [uIcc_of_le hy1.le] at s1
  rw [uIcc_of_ge (by norm_num : (-1 : ℝ) ≤ 0)] at s2
  rw [uIcc_of_ge hx1.le] at s3
  have s12 := TArc.union s1 s2 (by
    ext ⟨p, q⟩
    simp only [mem_inter_iff, mem_prod, mem_Icc, mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨-, rfl⟩, rfl, -⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨⟨hy1.le, le_rfl⟩, rfl⟩, rfl, by norm_num, le_rfl⟩)
  exact TArc.union s12 s3 (by
    ext ⟨p, q⟩
    simp only [mem_inter_iff, mem_union, mem_prod, mem_Icc, mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨(⟨-, rfl⟩ | ⟨rfl, -⟩), -, h⟩
      · norm_num at h
      · exact ⟨rfl, h⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨Or.inr ⟨rfl, le_rfl, by norm_num⟩, ⟨hx1.le, le_rfl⟩, rfl⟩)

theorem rect_inter {y x₀ : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hx0 : 0 < x₀) (hx1 : x₀ < 1) :
    rectC₁ y x₀ ∩ rectC₂ y x₀ = {((y, 0) : Pt), (x₀, -1)} := by
  ext ⟨p, q⟩
  simp only [rectC₁, rectC₂, mem_inter_iff, mem_union, mem_prod, mem_Icc, mem_singleton_iff,
    mem_insert_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨((⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2, h3⟩) | ⟨⟨h1, h2⟩, h3⟩),
      ((⟨⟨h4, h5⟩, h6⟩ | ⟨h4, h5, h6⟩) | ⟨⟨h4, h5⟩, h6⟩)⟩ <;>
      first
      | exact Or.inl ⟨by linarith, by linarith⟩
      | exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl (Or.inl ⟨⟨hy0.le, le_rfl⟩, rfl⟩), Or.inl (Or.inl ⟨⟨le_rfl, hy1.le⟩, rfl⟩)⟩
    · exact ⟨Or.inr ⟨⟨hx0.le, le_rfl⟩, rfl⟩, Or.inr ⟨⟨le_rfl, hx1.le⟩, rfl⟩⟩

theorem rectC₁_axis {y x₀ : ℝ} (hy0 : 0 < y) :
    ∀ z ∈ rectC₁ y x₀, z.2 = 0 → ∃ t : unitInterval, (((1 - (t : ℝ)) * y, 0) : Pt) = z := by
  rintro ⟨p, q⟩ hz hq
  simp only [rectC₁, mem_union, mem_prod, mem_Icc, mem_singleton_iff] at hz hq
  subst hq
  rcases hz with (⟨⟨h1, h2⟩, -⟩ | ⟨rfl, -⟩) | ⟨-, h⟩
  · have hu : 1 - p / y ∈ Icc (0 : ℝ) 1 := by
      constructor
      · rw [sub_nonneg, div_le_one hy0]; exact h2
      · have := div_nonneg h1 hy0.le; linarith
    refine ⟨⟨_, hu⟩, Prod.ext ?_ rfl⟩
    simp only
    field_simp
    ring
  · exact ⟨1, by simp⟩
  · norm_num at h

theorem rectC₂_axis {y x₀ : ℝ} (hy1 : y < 1) :
    ∀ z ∈ rectC₂ y x₀, z.2 = 0 → ∃ t : unitInterval, ((y + (t : ℝ) * (1 - y), 0) : Pt) = z := by
  rintro ⟨p, q⟩ hz hq
  simp only [rectC₂, mem_union, mem_prod, mem_Icc, mem_singleton_iff] at hz hq
  subst hq
  have h1y : (1 - y) ≠ 0 := by linarith
  rcases hz with (⟨⟨h1, h2⟩, -⟩ | ⟨rfl, -⟩) | ⟨-, h⟩
  · have hu : (p - y) / (1 - y) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
    refine ⟨⟨_, hu⟩, Prod.ext ?_ rfl⟩
    simp only
    field_simp
    ring
  · exact ⟨1, by simp⟩
  · norm_num at h

end HPC.Hagopian
