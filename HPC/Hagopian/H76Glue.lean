import HPC.Hagopian.H76Rect

/-!
# Batch 163, item A: gluing two half-squares along a vertical

`glueMap y fL fR` puts the square map `fL` (reflected) on `[0, y] × [0, 1]` and `fR` on
`[y, 1] × [0, 1]`; the two agree along the vertical `x = y` when `fL (0, t) = fR (0, t)`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- Clamp a real number into the unit interval. -/
noncomputable abbrev clampI : ℝ → unitInterval := projIcc (0 : ℝ) 1 zero_le_one

/-- Glue `fL` (on `[0, y]`, reflected) and `fR` (on `[y, 1]`) along `x = y`. -/
noncomputable def glueMap (y : ℝ) (fL fR : unitInterval × unitInterval → Pt) (p : ℝ × ℝ) : Pt :=
  if p.1 ≤ y then fL (clampI ((y - p.1) / y), clampI p.2)
  else fR (clampI ((p.1 - y) / (1 - y)), clampI p.2)

theorem clampI_val {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : (clampI x : ℝ) = x := by
  rw [clampI, projIcc_of_mem _ hx]

theorem clampI_zero : clampI 0 = 0 := Subtype.ext (clampI_val ⟨le_rfl, zero_le_one⟩)

theorem clampI_coe (u : unitInterval) : clampI u = u := Subtype.ext (clampI_val u.2)

theorem clampI_inj {x x' : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hx' : x' ∈ Icc (0 : ℝ) 1)
    (e : clampI x = clampI x') : x = x' := by
  rw [← clampI_val hx, ← clampI_val hx', e]

theorem glue_memL {y x : ℝ} (hy0 : 0 < y) (hx : x ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    (y - x) / y ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (by linarith) hy0.le, by rw [div_le_one hy0]; linarith [hx.1]⟩

theorem glue_memR {y x : ℝ} (hy1 : y < 1) (hx : x ∈ Icc (0 : ℝ) 1) (hxy : y ≤ x) :
    (x - y) / (1 - y) ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith [hx.2]⟩

variable {y : ℝ} {fL fR : unitInterval × unitInterval → Pt}

theorem glueMap_L {p : ℝ × ℝ} (h : p.1 ≤ y) :
    glueMap y fL fR p = fL (clampI ((y - p.1) / y), clampI p.2) := if_pos h

theorem glueMap_R {p : ℝ × ℝ} (h : ¬ p.1 ≤ y) :
    glueMap y fL fR p = fR (clampI ((p.1 - y) / (1 - y)), clampI p.2) := if_neg h

theorem glueMap_vert (s : ℝ) : glueMap y fL fR (y, s) = fL (0, clampI s) := by
  rw [glueMap_L (p := (y, s)) le_rfl]
  simp only [sub_self, zero_div, clampI_zero]

theorem glueMap_continuous (hL : Continuous fL) (hR : Continuous fR)
    (hLR : ∀ t, fL (0, t) = fR (0, t)) : Continuous (glueMap y fL fR) := by
  have e : glueMap y fL fR = fun p => if p.1 ≤ y then fL (clampI ((y - p.1) / y), clampI p.2)
      else fR (clampI ((p.1 - y) / (1 - y)), clampI p.2) := rfl
  rw [e]
  refine Continuous.if_le ?_ ?_ continuous_fst continuous_const ?_
  · exact hL.comp ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp continuous_snd))
  · exact hR.comp ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp continuous_snd))
  · intro p hp
    simp only [hp, sub_self, zero_div, clampI_zero, hLR]

theorem glueMap_top (hy0 : 0 < y) (hy1 : y < 1)
    (hfL0 : ∀ t, fL (t, 0) = ((1 - (t : ℝ)) * y, 0))
    (hfR0 : ∀ t, fR (t, 0) = (y + (t : ℝ) * (1 - y), 0)) :
    ∀ x ∈ Icc (0 : ℝ) 1, glueMap y fL fR (x, 0) = (x, 0) := by
  intro x hx
  by_cases h : x ≤ y
  · rw [glueMap_L h, clampI_zero, hfL0, clampI_val (glue_memL hy0 hx h)]
    refine Prod.ext ?_ rfl
    simp only
    field_simp
    ring
  · rw [glueMap_R h, clampI_zero, hfR0, clampI_val (glue_memR hy1 hx (not_le.1 h).le)]
    refine Prod.ext ?_ rfl
    have : (1 - y) ≠ 0 := by linarith
    simp only
    field_simp
    ring

theorem glueMap_injOn (hy0 : 0 < y) (hy1 : y < 1) (hfL : Function.Injective fL)
    (hfR : Function.Injective fR) (hRβ : ∀ p q, fL p = fR q → q.1 = 0) :
    InjOn (glueMap y fL fR) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hy1' : (1 - y) ≠ 0 := by linarith
  rintro ⟨x, s⟩ ⟨hx, hs⟩ ⟨x', s'⟩ ⟨hx', hs'⟩ e
  simp only at hx hs hx' hs'
  by_cases h1 : x ≤ y <;> by_cases h2 : x' ≤ y
  · rw [glueMap_L h1, glueMap_L h2] at e
    have := hfL e
    simp only [Prod.mk.injEq] at this
    have e1 := clampI_inj (glue_memL hy0 hx h1) (glue_memL hy0 hx' h2) this.1
    have e2 := clampI_inj hs hs' this.2
    refine Prod.ext ?_ e2
    simp only
    rw [div_left_inj' hy0.ne'] at e1
    linarith
  · exfalso
    rw [glueMap_L h1, glueMap_R h2] at e
    have h0 := hRβ _ _ e
    simp only at h0
    have := clampI_inj (glue_memR hy1 hx' (not_le.1 h2).le) ⟨le_rfl, zero_le_one⟩
      (h0.trans clampI_zero.symm)
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact h2 (by linarith)
    · exact hy1' h
  · exfalso
    rw [glueMap_R h1, glueMap_L h2] at e
    have h0 := hRβ _ _ e.symm
    simp only at h0
    have := clampI_inj (glue_memR hy1 hx (not_le.1 h1).le) ⟨le_rfl, zero_le_one⟩
      (h0.trans clampI_zero.symm)
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact h1 (by linarith)
    · exact hy1' h
  · rw [glueMap_R h1, glueMap_R h2] at e
    have := hfR e
    simp only [Prod.mk.injEq] at this
    have e1 := clampI_inj (glue_memR hy1 hx (not_le.1 h1).le)
      (glue_memR hy1 hx' (not_le.1 h2).le) this.1
    have e2 := clampI_inj hs hs' this.2
    refine Prod.ext ?_ e2
    simp only
    rw [div_left_inj' hy1'] at e1
    linarith

theorem glueMap_mapsTo {S : Set Pt} (hLr : range fL ⊆ S) (hRr : range fR ⊆ S) (p : ℝ × ℝ) :
    glueMap y fL fR p ∈ S := by
  by_cases h : p.1 ≤ y
  · rw [glueMap_L h]; exact hLr (mem_range_self _)
  · rw [glueMap_R h]; exact hRr (mem_range_self _)

theorem glueMap_snd (hL2 : ∀ p, (fL p).2 = 0 → p.2 = 0) (hR2 : ∀ p, (fR p).2 = 0 → p.2 = 0) :
    ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (glueMap y fL fR p).2 = 0 → p.2 = 0 := by
  rintro ⟨x, s⟩ ⟨-, hs⟩ h
  simp only at hs ⊢
  have key : clampI s = 0 := by
    by_cases h1 : x ≤ y
    · rw [glueMap_L h1] at h; exact hL2 _ h
    · rw [glueMap_R h1] at h; exact hR2 _ h
  rw [← clampI_val hs, key]; rfl

/-- The open square `(0, 1)²` as a subset of `unitInterval × unitInterval`. -/
def openSqI : Set (unitInterval × unitInterval) := {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1}

theorem glueMap_image_sub (hy0 : 0 < y) (hy1 : y < 1) {R₁ R₂ V : Set Pt}
    (hfLo : fL '' openSqI = R₁) (hfRo : fR '' openSqI = R₂) (hR₁ : R₁ ⊆ V) (hR₂ : R₂ ⊆ V)
    (hvert : ∀ s ∈ Ioo (0 : ℝ) 1, fL (0, clampI s) ∈ V) :
    glueMap y fL fR '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ⊆ V := by
  rintro _ ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hsI : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
  have hs0 : (0 : unitInterval) < clampI s := by
    show (0 : ℝ) < clampI s
    rw [clampI_val hsI]; exact hs.1
  have hs1 : clampI s < (1 : unitInterval) := by
    show (clampI s : ℝ) < 1
    rw [clampI_val hsI]; exact hs.2
  rcases lt_trichotomy x y with h | rfl | h
  · rw [glueMap_L h.le]
    refine hR₁ (hfLo ▸ ⟨_, ⟨?_, ?_, hs0, hs1⟩, rfl⟩)
    · show (0 : ℝ) < clampI ((y - x) / y)
      rw [clampI_val (glue_memL hy0 hxI h.le)]; exact div_pos (by linarith) hy0
    · show (clampI ((y - x) / y) : ℝ) < 1
      rw [clampI_val (glue_memL hy0 hxI h.le), div_lt_one hy0]; linarith [hx.1]
  · rw [glueMap_vert]; exact hvert s hs
  · rw [glueMap_R (not_le.2 h)]
    refine hR₂ (hfRo ▸ ⟨_, ⟨?_, ?_, hs0, hs1⟩, rfl⟩)
    · show (0 : ℝ) < clampI ((x - y) / (1 - y))
      rw [clampI_val (glue_memR hy1 hxI h.le)]; exact div_pos (by linarith) (by linarith)
    · show (clampI ((x - y) / (1 - y)) : ℝ) < 1
      rw [clampI_val (glue_memR hy1 hxI h.le), div_lt_one (by linarith)]; linarith [hx.2]

theorem glueMap_image_sup (hy0 : 0 < y) (hy1 : y < 1) {R₁ R₂ : Set Pt}
    (hfLo : fL '' openSqI = R₁) (hfRo : fR '' openSqI = R₂) :
    R₁ ∪ R₂ ⊆ glueMap y fL fR '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rintro z (h | h)
  · rw [← hfLo] at h
    obtain ⟨⟨u, r⟩, ⟨hu0, hu1, hr0, hr1⟩, rfl⟩ := h
    have hu0' : (0 : ℝ) < u := hu0
    have hu1' : (u : ℝ) < 1 := hu1
    have hr0' : (0 : ℝ) < r := hr0
    have hr1' : (r : ℝ) < 1 := hr1
    have hm : (y - (y - u * y)) / y = u := by field_simp; ring
    refine ⟨(y - u * y, r), ⟨⟨by nlinarith, by nlinarith⟩, hr0', hr1'⟩, ?_⟩
    rw [glueMap_L (by simp only; nlinarith)]
    simp only [hm, clampI_coe]
  · rw [← hfRo] at h
    obtain ⟨⟨u, r⟩, ⟨hu0, hu1, hr0, hr1⟩, rfl⟩ := h
    have hu0' : (0 : ℝ) < u := hu0
    have hu1' : (u : ℝ) < 1 := hu1
    have hr0' : (0 : ℝ) < r := hr0
    have hr1' : (r : ℝ) < 1 := hr1
    have h1y : 0 < 1 - y := by linarith
    have hm : (y + u * (1 - y) - y) / (1 - y) = u := by field_simp; ring
    refine ⟨(y + u * (1 - y), r), ⟨⟨by nlinarith, by nlinarith⟩, hr0', hr1'⟩, ?_⟩
    rw [glueMap_R (by simp only; nlinarith)]
    simp only [hm, clampI_coe]

end HPC.Hagopian
