import HPC.Chains.Basic

/-!
# T3: the 1951 notion does not imply the 1948 notion

A chain `D` of four vertical strips and a chain `E` of six rectangles in `ℝ × ℝ` (sup metric)
with `E.IsCrookedIn D` and `¬ E.IsCrookedIn' D`. See COMMISSION.md §3, T3, for the
numerical verification in English.
-/

namespace HPC

open Set

/-- Open rectangle `(a,b) × (c,d)` in `ℝ × ℝ`. -/
def rect (a b c d : ℝ) : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo c d

theorem isOpen_rect (a b c d : ℝ) : IsOpen (rect a b c d) :=
  isOpen_Ioo.prod isOpen_Ioo

/-- Two open rectangles meet exactly when their `x`-intervals and their `y`-intervals both
meet.  This packages the witness needed for all the adjacency checks below. -/
theorem rect_inter_nonempty_iff (a b c d a' b' c' d' : ℝ) :
    (rect a b c d ∩ rect a' b' c' d').Nonempty ↔
      (max a a' < min b b' ∧ max c c' < min d d') := by
  constructor
  · rintro ⟨⟨x, y⟩, ⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩
    exact ⟨(max_lt h1 h5).trans (lt_min h2 h6), (max_lt h3 h7).trans (lt_min h4 h8)⟩
  · rintro ⟨hx, hy⟩
    refine ⟨((max a a' + min b b') / 2, (max c c' + min d d') / 2),
      ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
      [ have := le_max_left a a'; have := min_le_left b b'; have := le_max_left c c';
        have := min_le_left d d'; have := le_max_right a a'; have := min_le_right b b';
        have := le_max_right c c'; have := min_le_right d d'] <;> linarith

theorem rect_nonempty_iff (a b c d : ℝ) : (rect a b c d).Nonempty ↔ (a < b ∧ c < d) := by
  simp [rect, Set.prod_nonempty_iff]

/-- Containment of rectangles from containment of the defining intervals. -/
theorem rect_subset {a b c d a' b' c' d' : ℝ} (h1 : a' ≤ a) (h2 : b ≤ b') (h3 : c' ≤ c)
    (h4 : d ≤ d') : rect a b c d ⊆ rect a' b' c' d' := by
  rintro ⟨x, y⟩ ⟨⟨g1, g2⟩, g3, g4⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The four strips. -/
def Dlink : Fin 4 → Set (ℝ × ℝ) :=
  ![rect 0 2 0 10, rect 1 4 0 10, rect 3 6 0 10, rect 5 7 0 10]

/-- The six rectangles. -/
def Elink : Fin 6 → Set (ℝ × ℝ) :=
  ![rect 0.5 1.5 1 2,
    rect 1.2 3.5 1.5 2.5,
    rect 3.2 5.8 2 3,
    rect 1.5 3.8 2.7 3.7,
    rect 3.2 5.5 3.5 4.5,
    rect 5.2 6.8 4.2 5.2]

/-- `D` is a chain: consecutive strips overlap, non-consecutive ones are disjoint. -/
def Dchain : Chain (ℝ × ℝ) 4 where
  link := Dlink
  isOpen i := by
    fin_cases i <;> exact isOpen_rect _ _ _ _
  adjacent := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Dlink, rect_inter_nonempty_iff, rect_nonempty_iff]

/-- `E` is a chain: consecutive rectangles overlap, non-consecutive ones are disjoint. -/
def Echain : Chain (ℝ × ℝ) 6 where
  link := Elink
  isOpen i := by
    fin_cases i <;> exact isOpen_rect _ _ _ _
  adjacent := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Elink, rect_inter_nonempty_iff, rect_nonempty_iff]

/-- `E` refines `D`, with links landing in strips `0, 1, 2, 1, 2, 3` respectively. -/
theorem Echain_refines_Dchain : Echain.Refines Dchain := by
  intro i
  fin_cases i
  · exact ⟨0, rect_subset (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · exact ⟨1, rect_subset (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · exact ⟨2, rect_subset (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · exact ⟨1, rect_subset (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · exact ⟨2, rect_subset (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · exact ⟨3, rect_subset (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

/-- The only link of `E` contained in strip `0` of `D` is `E.link 0`: each other rectangle
carries a point with `x ≥ 2`. -/
theorem eq_zero_of_subset_Dchain_zero (t : Fin 6) (ht : Echain.link t ⊆ Dchain.link 0) :
    t = 0 := by
  fin_cases t
  · rfl
  · exact absurd (ht (show ((3 : ℝ), (2 : ℝ)) ∈ rect 1.2 3.5 1.5 2.5 by norm_num [rect]))
      (by show ((3 : ℝ), (2 : ℝ)) ∉ rect 0 2 0 10; norm_num [rect])
  · exact absurd (ht (show ((4 : ℝ), (2.5 : ℝ)) ∈ rect 3.2 5.8 2 3 by norm_num [rect]))
      (by show ((4 : ℝ), (2.5 : ℝ)) ∉ rect 0 2 0 10; norm_num [rect])
  · exact absurd (ht (show ((3 : ℝ), (3 : ℝ)) ∈ rect 1.5 3.8 2.7 3.7 by norm_num [rect]))
      (by show ((3 : ℝ), (3 : ℝ)) ∉ rect 0 2 0 10; norm_num [rect])
  · exact absurd (ht (show ((4 : ℝ), (4 : ℝ)) ∈ rect 3.2 5.5 3.5 4.5 by norm_num [rect]))
      (by show ((4 : ℝ), (4 : ℝ)) ∉ rect 0 2 0 10; norm_num [rect])
  · exact absurd (ht (show ((6 : ℝ), (5 : ℝ)) ∈ rect 5.2 6.8 4.2 5.2 by norm_num [rect]))
      (by show ((6 : ℝ), (5 : ℝ)) ∉ rect 0 2 0 10; norm_num [rect])

/-- The only link of `E` contained in strip `3` of `D` is `E.link 5`: each other rectangle
carries a point with `x ≤ 5`. -/
theorem eq_five_of_subset_Dchain_three (t : Fin 6) (ht : Echain.link t ⊆ Dchain.link 3) :
    t = 5 := by
  fin_cases t
  · exact absurd (ht (show ((1 : ℝ), (1.5 : ℝ)) ∈ rect 0.5 1.5 1 2 by norm_num [rect]))
      (by show ((1 : ℝ), (1.5 : ℝ)) ∉ rect 5 7 0 10; norm_num [rect])
  · exact absurd (ht (show ((3 : ℝ), (2 : ℝ)) ∈ rect 1.2 3.5 1.5 2.5 by norm_num [rect]))
      (by show ((3 : ℝ), (2 : ℝ)) ∉ rect 5 7 0 10; norm_num [rect])
  · exact absurd (ht (show ((4 : ℝ), (2.5 : ℝ)) ∈ rect 3.2 5.8 2 3 by norm_num [rect]))
      (by show ((4 : ℝ), (2.5 : ℝ)) ∉ rect 5 7 0 10; norm_num [rect])
  · exact absurd (ht (show ((3 : ℝ), (3 : ℝ)) ∈ rect 1.5 3.8 2.7 3.7 by norm_num [rect]))
      (by show ((3 : ℝ), (3 : ℝ)) ∉ rect 5 7 0 10; norm_num [rect])
  · exact absurd (ht (show ((4 : ℝ), (4 : ℝ)) ∈ rect 3.2 5.5 3.5 4.5 by norm_num [rect]))
      (by show ((4 : ℝ), (4 : ℝ)) ∉ rect 5 7 0 10; norm_num [rect])
  · rfl

/-- **T3, first half.** `E` is crooked in `D` in the 1951 sense. The only pair of strip indices
with gap `> 2` is `(0, 3)`; the only rectangle inside strip `0` is `E.link 0` and the only one
inside strip `3` is `E.link 5`; the witnesses are `r = 2, s = 3` (or `r = 3, s = 2` for the
reversed orientation). -/
theorem Echain_isCrookedIn_Dchain : Echain.IsCrookedIn Dchain := by
  refine ⟨Echain_refines_Dchain, ?_⟩
  intro h k hk i j hi hj
  have hh : h = 0 := Fin.ext (by have := h.isLt; have := k.isLt; omega)
  have hkk : k = 3 := Fin.ext (by have := h.isLt; have := k.isLt; omega)
  subst hh
  subst hkk
  have hi0 : i = 0 := eq_zero_of_subset_Dchain_zero i hi
  have hj5 : j = 5 := eq_five_of_subset_Dchain_three j hj
  subst hi0
  subst hj5
  refine ⟨2, 3, Or.inl ⟨by decide, by decide, by decide⟩, ?_, ?_⟩
  · show rect 3.2 5.8 2 3 ⊆ rect 3 6 0 10
    exact rect_subset (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · show rect 1.5 3.8 2.7 3.7 ⊆ rect 1 4 0 10
    exact rect_subset (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **T3, second half.** `E` is not crooked in `D` in the 1948 sense: `E.link 1` meets strip
`0` at `(1.3, 1.8)`, `E.link 2` meets strip `3` at `(5.5, 2.5)`, and no index lies strictly
between `1` and `2`. -/
theorem Echain_not_isCrookedIn'_Dchain : ¬ Echain.IsCrookedIn' Dchain := by
  rintro ⟨-, hC⟩
  have hmem1 : ((1.3 : ℝ), (1.8 : ℝ)) ∈ Echain.link 1 ∩ Dchain.link 0 := by
    show ((1.3 : ℝ), (1.8 : ℝ)) ∈ rect 1.2 3.5 1.5 2.5 ∩ rect 0 2 0 10
    constructor <;> norm_num [rect]
  have hmem2 : ((5.5 : ℝ), (2.5 : ℝ)) ∈ Echain.link 2 ∩ Dchain.link 3 := by
    show ((5.5 : ℝ), (2.5 : ℝ)) ∈ rect 3.2 5.8 2 3 ∩ rect 5 7 0 10
    constructor <;> norm_num [rect]
  obtain ⟨r, s, hb, -, -⟩ :=
    hC 0 3 (by norm_num) 1 2 ⟨_, hmem1⟩ ⟨_, hmem2⟩
  rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    · simp only [gt_iff_lt, Fin.lt_def] at h1 h2 h3
      omega

/-- **T3.** The two notions differ. -/
theorem isCrookedIn_ne_isCrookedIn' :
    ∃ (D : Chain (ℝ × ℝ) 4) (E : Chain (ℝ × ℝ) 6), E.IsCrookedIn D ∧ ¬ E.IsCrookedIn' D :=
  ⟨Dchain, Echain, Echain_isCrookedIn_Dchain, Echain_not_isCrookedIn'_Dchain⟩

end HPC
