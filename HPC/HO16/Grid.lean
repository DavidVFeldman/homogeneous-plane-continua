import HPC.HO16.Defs
import HPC.Span.OT82Strip

/-!
# Batch 193, §6.2: grid graphs and radial projections

Commission 193, §6.2. Radial projection of a rectangle from an inner point onto its frontier
(`radProj`), the edges of the grid of mesh `η` (`gridH`, `gridV`), and the PL graph formed by the
edges of the grid squares meeting a compact set.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane

/-! ### Radial projection in a rectangle -/

/-- The closed rectangle `[p.1, q.1] × [p.2, q.2]`. -/
def rect (p q : Pt) : Set Pt := {x | p.1 ≤ x.1 ∧ x.1 ≤ q.1 ∧ p.2 ≤ x.2 ∧ x.2 ≤ q.2}

/-- `x` lies on one of the four lines bounding the rectangle `[p, q]`. -/
def OnBdry (p q : Pt) (x : Pt) : Prop := x.1 = p.1 ∨ x.1 = q.1 ∨ x.2 = p.2 ∨ x.2 = q.2

/-- The gauge of the rectangle `[p, q]` centred at `c`. -/
noncomputable def rectGauge (p q c : Pt) (v : Pt) : ℝ :=
  max (max (v.1 / (q.1 - c.1)) (-v.1 / (c.1 - p.1))) (max (v.2 / (q.2 - c.2)) (-v.2 / (c.2 - p.2)))

/-- Radial projection from `c` onto the frontier of the rectangle `[p, q]`. -/
noncomputable def radProj (p q c : Pt) (x : Pt) : Pt := c + (rectGauge p q c (x - c))⁻¹ • (x - c)

section Rad

variable {p q c : Pt}

/-- `c` is an inner point of the rectangle. -/
def IsInner (p q c : Pt) : Prop := p.1 < c.1 ∧ c.1 < q.1 ∧ p.2 < c.2 ∧ c.2 < q.2

theorem rectGauge_pos (hc : IsInner p q c) {v : Pt} (hv : v ≠ 0) : 0 < rectGauge p q c v := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have a1 : 0 < q.1 - c.1 := by linarith
  have a2 : 0 < c.1 - p.1 := by linarith
  have a3 : 0 < q.2 - c.2 := by linarith
  have a4 : 0 < c.2 - p.2 := by linarith
  unfold rectGauge
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := fun h => hv (Prod.ext hv1 h)
    rcases lt_or_gt_of_ne hv2 with h | h
    · exact lt_max_of_lt_right (lt_max_of_lt_right (div_pos (by linarith) a4))
    · exact lt_max_of_lt_right (lt_max_of_lt_left (div_pos h a3))
  · rcases lt_or_gt_of_ne hv1 with h | h
    · exact lt_max_of_lt_left (lt_max_of_lt_right (div_pos (by linarith) a2))
    · exact lt_max_of_lt_left (lt_max_of_lt_left (div_pos h a1))

theorem rectGauge_smul {t : ℝ} (ht : 0 ≤ t) (v : Pt) :
    rectGauge p q c (t • v) = t * rectGauge p q c v := by
  unfold rectGauge
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [mul_max_of_nonneg _ _ ht, mul_max_of_nonneg _ _ ht, mul_max_of_nonneg _ _ ht]
  congr 2 <;> ring

theorem continuous_rectGauge : Continuous (rectGauge p q c) := by
  unfold rectGauge
  fun_prop

theorem rectGauge_le_one_iff (hc : IsInner p q c) {x : Pt} :
    rectGauge p q c (x - c) ≤ 1 ↔ x ∈ rect p q := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have a1 : 0 < q.1 - c.1 := by linarith
  have a2 : 0 < c.1 - p.1 := by linarith
  have a3 : 0 < q.2 - c.2 := by linarith
  have a4 : 0 < c.2 - p.2 := by linarith
  simp only [rectGauge, max_le_iff, Prod.fst_sub, Prod.snd_sub, div_le_one a1, div_le_one a2,
    div_le_one a3, div_le_one a4, rect, mem_setOf_eq]
  constructor
  · rintro ⟨⟨b1, b2⟩, b3, b4⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨b1, b2, b3, b4⟩
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem rectGauge_eq_one_iff (hc : IsInner p q c) {x : Pt} (hx : x ∈ rect p q) :
    rectGauge p q c (x - c) = 1 ↔ OnBdry p q x := by
  have hle := (rectGauge_le_one_iff hc).2 hx
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have a1 : 0 < q.1 - c.1 := by linarith
  have a2 : 0 < c.1 - p.1 := by linarith
  have a3 : 0 < q.2 - c.2 := by linarith
  have a4 : 0 < c.2 - p.2 := by linarith
  constructor
  · intro h
    unfold rectGauge at h
    simp only [Prod.fst_sub, Prod.snd_sub] at h
    rcases max_choice (max ((x.1 - c.1) / (q.1 - c.1)) (-(x.1 - c.1) / (c.1 - p.1)))
      (max ((x.2 - c.2) / (q.2 - c.2)) (-(x.2 - c.2) / (c.2 - p.2))) with h' | h' <;>
      rw [h'] at h
    · rcases max_choice ((x.1 - c.1) / (q.1 - c.1)) (-(x.1 - c.1) / (c.1 - p.1)) with h'' | h'' <;>
        rw [h''] at h <;> rw [div_eq_one_iff_eq (by linarith)] at h
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inl (by linarith)
    · rcases max_choice ((x.2 - c.2) / (q.2 - c.2)) (-(x.2 - c.2) / (c.2 - p.2)) with h'' | h'' <;>
        rw [h''] at h <;> rw [div_eq_one_iff_eq (by linarith)] at h
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · intro hb
    refine le_antisymm hle ?_
    unfold rectGauge
    simp only [Prod.fst_sub, Prod.snd_sub]
    rcases hb with hb | hb | hb | hb
    · refine le_max_of_le_left (le_max_of_le_right (le_of_eq ?_))
      rw [hb, eq_div_iff (by linarith)]; ring
    · refine le_max_of_le_left (le_max_of_le_left (le_of_eq ?_))
      rw [hb, eq_div_iff (by linarith)]; ring
    · refine le_max_of_le_right (le_max_of_le_right (le_of_eq ?_))
      rw [hb, eq_div_iff (by linarith)]; ring
    · refine le_max_of_le_right (le_max_of_le_left (le_of_eq ?_))
      rw [hb, eq_div_iff (by linarith)]; ring

/-- The radial projection is the identity on the frontier. -/
theorem radProj_of_onBdry (hc : IsInner p q c) {x : Pt} (hx : x ∈ rect p q) (hb : OnBdry p q x) :
    radProj p q c x = x := by
  rw [radProj, (rectGauge_eq_one_iff hc hx).2 hb, inv_one, one_smul, add_sub_cancel]

/-- The radial projection maps into the frontier. -/
theorem radProj_mem (hc : IsInner p q c) {x : Pt} (hx : x ≠ c) :
    radProj p q c x ∈ rect p q ∧ OnBdry p q (radProj p q c x) := by
  have hv : x - c ≠ 0 := sub_ne_zero.2 hx
  have hg := rectGauge_pos hc hv
  have h1 : rectGauge p q c (radProj p q c x - c) = 1 := by
    rw [radProj, add_sub_cancel_left, rectGauge_smul (inv_nonneg.2 hg.le), inv_mul_cancel₀ hg.ne']
  have hr : radProj p q c x ∈ rect p q := (rectGauge_le_one_iff hc).1 h1.le
  exact ⟨hr, (rectGauge_eq_one_iff hc hr).1 h1⟩

theorem continuousOn_radProj (hc : IsInner p q c) :
    ContinuousOn (radProj p q c) {x | x ≠ c} := by
  intro x hx
  have hv : x - c ≠ 0 := sub_ne_zero.2 hx
  have h1 : ContinuousAt (fun y : Pt => rectGauge p q c (y - c)) x :=
    (continuous_rectGauge.comp (continuous_id.sub continuous_const)).continuousAt
  exact (continuousAt_const.add ((h1.inv₀ (rectGauge_pos hc hv).ne').smul
    (continuousAt_id.sub continuousAt_const))).continuousWithinAt

theorem dist_le_of_mem_rect {x y : Pt} (hx : x ∈ rect p q) (hy : y ∈ rect p q) :
    dist x y ≤ max (q.1 - p.1) (q.2 - p.2) := by
  obtain ⟨a1, a2, a3, a4⟩ := hx
  obtain ⟨b1, b2, b3, b4⟩ := hy
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  refine max_le_max ?_ ?_ <;> rw [abs_le] <;> constructor <;> linarith

end Rad

/-! ### The grid of mesh `η` -/

section GridDefs

variable (η : ℝ)

/-- The grid point `(iη, jη)`. -/
def gridP (i j : ℤ) : Pt := ((i : ℝ) * η, (j : ℝ) * η)

/-- The horizontal grid edge from `(iη, jη)` to `((i+1)η, jη)`. -/
def gridH (i j : ℤ) : Pt × Pt := (gridP η i j, gridP η (i + 1) j)

/-- The vertical grid edge from `(iη, jη)` to `(iη, (j+1)η)`. -/
def gridV (i j : ℤ) : Pt × Pt := (gridP η i j, gridP η i (j + 1))

/-- The grid square `[iη, (i+1)η] × [jη, (j+1)η]`. -/
def gridSq (i j : ℤ) : Set Pt := rect (gridP η i j) (gridP η (i + 1) (j + 1))

/-- A grid edge. -/
def IsGridEdge (s : Pt × Pt) : Prop := (∃ i j, s = gridH η i j) ∨ (∃ i j, s = gridV η i j)

end GridDefs

section Grid

variable {η : ℝ}

theorem mem_segment_gridH (hη : 0 < η) {i j : ℤ} {x : Pt} :
    x ∈ segment ℝ (gridH η i j).1 (gridH η i j).2 ↔
      x.2 = j * η ∧ i * η ≤ x.1 ∧ x.1 ≤ (i + 1) * η := by
  simp only [gridH, gridP, Int.cast_add, Int.cast_one]
  rw [← Prod.image_mk_segment_left, segment_eq_Icc (by nlinarith)]
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
    exact ⟨rfl, ht1, ht2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨x.1, ⟨h2, h3⟩, Prod.ext rfl h1.symm⟩

theorem mem_segment_gridV (hη : 0 < η) {i j : ℤ} {x : Pt} :
    x ∈ segment ℝ (gridV η i j).1 (gridV η i j).2 ↔
      x.1 = i * η ∧ j * η ≤ x.2 ∧ x.2 ≤ (j + 1) * η := by
  simp only [gridV, gridP, Int.cast_add, Int.cast_one]
  rw [← Prod.image_mk_segment_right, segment_eq_Icc (by nlinarith)]
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
    exact ⟨rfl, ht1, ht2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨x.2, ⟨h2, h3⟩, Prod.ext h1.symm rfl⟩

theorem int_eq_of_mul_eq (hη : 0 < η) {a b : ℤ} (h : (a : ℝ) * η = b * η) : a = b := by
  have := mul_right_cancel₀ hη.ne' h
  exact_mod_cast this

theorem int_le_of_mul_le (hη : 0 < η) {a b : ℤ} (h : (a : ℝ) * η ≤ b * η) : a ≤ b := by
  have := le_of_mul_le_mul_right h hη
  exact_mod_cast this

theorem int_le_succ_of_mul_le (hη : 0 < η) {a b : ℤ} (h : (a : ℝ) * η ≤ (b + 1) * η) :
    a ≤ b + 1 := by
  have := le_of_mul_le_mul_right h hη
  exact_mod_cast this

/-- A grid point on a grid edge is one of its ends. -/
theorem gridP_mem_edge (hη : 0 < η) {s : Pt × Pt} (hs : IsGridEdge η s) {a b : ℤ}
    (h : gridP η a b ∈ segment ℝ s.1 s.2) : gridP η a b = s.1 ∨ gridP η a b = s.2 := by
  rcases hs with ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := (mem_segment_gridH hη).1 h
    simp only [gridP] at h1 h2 h3
    have hb := int_eq_of_mul_eq hη h1
    have ha1 := int_le_of_mul_le hη h2
    have ha2 := int_le_succ_of_mul_le hη h3
    subst hb
    rcases (show a = i ∨ a = i + 1 by omega) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · obtain ⟨h1, h2, h3⟩ := (mem_segment_gridV hη).1 h
    simp only [gridP] at h1 h2 h3
    have ha := int_eq_of_mul_eq hη h1
    have hb1 := int_le_of_mul_le hη h2
    have hb2 := int_le_succ_of_mul_le hη h3
    subst ha
    rcases (show b = j ∨ b = j + 1 by omega) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Two different grid edges meet only in grid points. -/
theorem exists_gridP_of_mem_two_edges (hη : 0 < η) {s s' : Pt × Pt} (hs : IsGridEdge η s)
    (hs' : IsGridEdge η s') (hne : s ≠ s') {x : Pt} (hx : x ∈ segment ℝ s.1 s.2)
    (hx' : x ∈ segment ℝ s'.1 s'.2) : ∃ a b : ℤ, x = gridP η a b := by
  rcases hs with ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩ <;> rcases hs' with ⟨i', j', rfl⟩ | ⟨i', j', rfl⟩
  · obtain ⟨h1, h2, h3⟩ := (mem_segment_gridH hη).1 hx
    obtain ⟨h1', h2', h3'⟩ := (mem_segment_gridH hη).1 hx'
    have hj : j = j' := int_eq_of_mul_eq hη (h1.symm.trans h1')
    subst hj
    have hi : i ≠ i' := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hi with h | h
    · have hle : ((i : ℝ) + 1) * η ≤ i' * η := by
        have : ((i : ℝ) + 1) ≤ i' := by exact_mod_cast h
        nlinarith
      exact ⟨i', j, Prod.ext (by simp only [gridP]; linarith) (by simp only [gridP]; exact h1)⟩
    · have hle : ((i' : ℝ) + 1) * η ≤ i * η := by
        have : ((i' : ℝ) + 1) ≤ i := by exact_mod_cast h
        nlinarith
      exact ⟨i, j, Prod.ext (by simp only [gridP]; linarith) (by simp only [gridP]; exact h1)⟩
  · obtain ⟨h1, -, -⟩ := (mem_segment_gridH hη).1 hx
    obtain ⟨h1', -, -⟩ := (mem_segment_gridV hη).1 hx'
    exact ⟨i', j, Prod.ext h1' h1⟩
  · obtain ⟨h1, -, -⟩ := (mem_segment_gridV hη).1 hx
    obtain ⟨h1', -, -⟩ := (mem_segment_gridH hη).1 hx'
    exact ⟨i, j', Prod.ext h1 h1'⟩
  · obtain ⟨h1, h2, h3⟩ := (mem_segment_gridV hη).1 hx
    obtain ⟨h1', h2', h3'⟩ := (mem_segment_gridV hη).1 hx'
    have hi : i = i' := int_eq_of_mul_eq hη (h1.symm.trans h1')
    subst hi
    have hj : j ≠ j' := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hj with h | h
    · have hle : ((j : ℝ) + 1) * η ≤ j' * η := by
        have : ((j : ℝ) + 1) ≤ j' := by exact_mod_cast h
        nlinarith
      exact ⟨i, j', Prod.ext (by simp only [gridP]; exact h1) (by simp only [gridP]; linarith)⟩
    · have hle : ((j' : ℝ) + 1) * η ≤ j * η := by
        have : ((j' : ℝ) + 1) ≤ j := by exact_mod_cast h
        nlinarith
      exact ⟨i, j, Prod.ext (by simp only [gridP]; exact h1) (by simp only [gridP]; linarith)⟩

/-- Two different grid edges meet at most in common ends. -/
theorem gridEdge_inter_subset (hη : 0 < η) {s s' : Pt × Pt} (hs : IsGridEdge η s)
    (hs' : IsGridEdge η s') (hne : s ≠ s') :
    segment ℝ s.1 s.2 ∩ segment ℝ s'.1 s'.2 ⊆ ({s.1, s.2} : Set Pt) ∩ {s'.1, s'.2} := by
  rintro x ⟨hx, hx'⟩
  obtain ⟨a, b, rfl⟩ := exists_gridP_of_mem_two_edges hη hs hs' hne hx hx'
  exact ⟨gridP_mem_edge hη hs hx, gridP_mem_edge hη hs' hx'⟩

theorem gridEdge_ne (hη : 0 < η) {s : Pt × Pt} (hs : IsGridEdge η s) : s.1 ≠ s.2 := by
  rcases hs with ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩
  · intro h
    have := congrArg Prod.fst h
    simp only [gridH, gridP, Int.cast_add, Int.cast_one] at this
    nlinarith
  · intro h
    have := congrArg Prod.snd h
    simp only [gridV, gridP, Int.cast_add, Int.cast_one] at this
    nlinarith

theorem isInner_gridSq_iff {i j : ℤ} {c : Pt} :
    IsInner (gridP η i j) (gridP η (i + 1) (j + 1)) c ↔
      c ∈ Ioo ((i : ℝ) * η) ((i + 1) * η) ×ˢ Ioo ((j : ℝ) * η) ((j + 1) * η) := by
  simp only [IsInner, gridP, Int.cast_add, Int.cast_one, mem_prod, mem_Ioo]
  tauto

theorem mem_gridSq_iff {i j : ℤ} {x : Pt} :
    x ∈ gridSq η i j ↔ (i : ℝ) * η ≤ x.1 ∧ x.1 ≤ (i + 1) * η ∧ (j : ℝ) * η ≤ x.2 ∧
      x.2 ≤ (j + 1) * η := by
  simp only [gridSq, rect, gridP, Int.cast_add, Int.cast_one, mem_setOf_eq]

/-- The frontier of a grid square lies in its four edges. -/
theorem onBdry_gridSq (hη : 0 < η) {i j : ℤ} {x : Pt} (hx : x ∈ gridSq η i j)
    (hb : OnBdry (gridP η i j) (gridP η (i + 1) (j + 1)) x) :
    x ∈ segment ℝ (gridH η i j).1 (gridH η i j).2 ∨
      x ∈ segment ℝ (gridH η i (j + 1)).1 (gridH η i (j + 1)).2 ∨
      x ∈ segment ℝ (gridV η i j).1 (gridV η i j).2 ∨
      x ∈ segment ℝ (gridV η (i + 1) j).1 (gridV η (i + 1) j).2 := by
  rw [mem_gridSq_iff] at hx
  obtain ⟨h1, h2, h3, h4⟩ := hx
  simp only [OnBdry, gridP, Int.cast_add, Int.cast_one] at hb
  simp only [mem_segment_gridH hη, mem_segment_gridV hη, Int.cast_add, Int.cast_one]
  rcases hb with hb | hb | hb | hb
  · exact Or.inr (Or.inr (Or.inl ⟨hb, h3, h4⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb, h3, h4⟩))
  · exact Or.inl ⟨hb, h1, h2⟩
  · exact Or.inr (Or.inl ⟨hb, h1, h2⟩)

/-- The edges of a grid square lie in it. -/
theorem edges_subset_gridSq (hη : 0 < η) {i j : ℤ} {x : Pt}
    (hx : x ∈ segment ℝ (gridH η i j).1 (gridH η i j).2 ∨
      x ∈ segment ℝ (gridH η i (j + 1)).1 (gridH η i (j + 1)).2 ∨
      x ∈ segment ℝ (gridV η i j).1 (gridV η i j).2 ∨
      x ∈ segment ℝ (gridV η (i + 1) j).1 (gridV η (i + 1) j).2) : x ∈ gridSq η i j := by
  rw [mem_gridSq_iff]
  simp only [mem_segment_gridH hη, mem_segment_gridV hη, Int.cast_add, Int.cast_one] at hx
  rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨h2, h3, ?_, ?_⟩ <;> nlinarith
  · refine ⟨h2, h3, ?_, ?_⟩ <;> nlinarith
  · refine ⟨?_, ?_, h2, h3⟩ <;> nlinarith
  · refine ⟨?_, ?_, h2, h3⟩ <;> nlinarith

/-- A point of two different grid squares lies on the frontier of both. -/
theorem onBdry_of_mem_two_gridSq (hη : 0 < η) {i j i' j' : ℤ} {x : Pt} (hx : x ∈ gridSq η i j)
    (hx' : x ∈ gridSq η i' j') (hne : (i, j) ≠ (i', j')) :
    OnBdry (gridP η i j) (gridP η (i + 1) (j + 1)) x := by
  rw [mem_gridSq_iff] at hx hx'
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨h1', h2', h3', h4'⟩ := hx'
  simp only [OnBdry, gridP, Int.cast_add, Int.cast_one]
  by_cases hi : i = i'
  · subst hi
    have hj : j ≠ j' := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hj with h | h
    · have : ((j : ℝ) + 1) ≤ j' := by exact_mod_cast h
      right; right; right; nlinarith
    · have : ((j' : ℝ) + 1) ≤ j := by exact_mod_cast h
      right; right; left; nlinarith
  · rcases lt_or_gt_of_ne hi with h | h
    · have : ((i : ℝ) + 1) ≤ i' := by exact_mod_cast h
      right; left; nlinarith
    · have : ((i' : ℝ) + 1) ≤ i := by exact_mod_cast h
      left; nlinarith

theorem mem_gridSq_floor (hη : 0 < η) (x : Pt) :
    x ∈ gridSq η ⌊x.1 / η⌋ ⌊x.2 / η⌋ := by
  rw [mem_gridSq_iff]
  have k1 := Int.floor_le (x.1 / η)
  have k2 := Int.lt_floor_add_one (x.1 / η)
  have k3 := Int.floor_le (x.2 / η)
  have k4 := Int.lt_floor_add_one (x.2 / η)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rwa [le_div_iff₀ hη] at k1
  · rw [div_lt_iff₀ hη] at k2; linarith
  · rwa [le_div_iff₀ hη] at k3
  · rw [div_lt_iff₀ hη] at k4; linarith

end Grid

/-- Continuity on a finite union of closed sets. -/
theorem continuousOn_biUnion_finset {α β ι : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (I : Finset ι) {s : ι → Set α} (hs : ∀ i ∈ I, IsClosed (s i))
    (hf : ∀ i ∈ I, ContinuousOn f (s i)) : ContinuousOn f (⋃ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I haI ih =>
    rw [Finset.set_biUnion_insert]
    exact (hf a (Finset.mem_insert_self a I)).union_of_isClosed
      (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
        (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      (hs a (Finset.mem_insert_self a I))
      (isClosed_biUnion_finset fun i hi => hs i (Finset.mem_insert_of_mem hi))

/-- **§6.2, grid graphs**: radial projections in the squares of a fine grid map a compact plane
set with empty interior into a nearby PL graph. -/
theorem exists_plGraph_approx {X : Set Pt} (hX : IsCompact X) (hint : interior X = ∅) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ G : Set Pt, IsPLGraph G ∧ G ⊆ thickening δ X ∧
      ∃ f : Pt → Pt, ContinuousOn f X ∧ ∀ x ∈ X, f x ∈ G ∧ dist (f x) x < δ := by
  classical
  set η := δ / 2 with hηdef
  have hη : 0 < η := half_pos hδ
  -- centres
  have hdense : Dense Xᶜ := interior_eq_empty_iff_dense_compl.1 hint
  have hcen : ∀ ij : ℤ × ℤ, ∃ c : Pt,
      IsInner (gridP η ij.1 ij.2) (gridP η (ij.1 + 1) (ij.2 + 1)) c ∧ c ∉ X := by
    intro ij
    obtain ⟨c, hc1, hc2⟩ := hdense.inter_open_nonempty
      (Ioo ((ij.1 : ℝ) * η) ((ij.1 + 1) * η) ×ˢ Ioo ((ij.2 : ℝ) * η) ((ij.2 + 1) * η))
      (isOpen_Ioo.prod isOpen_Ioo)
      ⟨(((ij.1 : ℝ) + 1 / 2) * η, ((ij.2 : ℝ) + 1 / 2) * η),
        ⟨by constructor <;> nlinarith, by constructor <;> nlinarith⟩⟩
    exact ⟨c, isInner_gridSq_iff.2 hc1, hc2⟩
  choose cen hcenI hcenX using hcen
  -- bounds
  obtain ⟨R, hR⟩ := hX.isBounded.subset_closedBall (0 : Pt)
  set N : ℤ := ⌈R / η⌉ with hN
  have hbound : ∀ i j : ℤ, (gridSq η i j ∩ X).Nonempty → i ∈ Finset.Icc (-N - 1) N ∧
      j ∈ Finset.Icc (-N - 1) N := by
    rintro i j ⟨x, hxQ, hxX⟩
    rw [mem_gridSq_iff] at hxQ
    obtain ⟨h1, h2, h3, h4⟩ := hxQ
    have hx := hR hxX
    rw [mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
      max_le_iff, abs_le, abs_le] at hx
    obtain ⟨⟨k1, k2⟩, k3, k4⟩ := hx
    have hRN : R / η ≤ N := Int.le_ceil _
    have hRN' : R ≤ N * η := by rwa [div_le_iff₀ hη] at hRN
    simp only [Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have : ((-N - 1 : ℤ) : ℝ) * η ≤ i * η := by push_cast; nlinarith
      exact int_le_of_mul_le hη this
    · exact int_le_of_mul_le hη (by linarith)
    · have : ((-N - 1 : ℤ) : ℝ) * η ≤ j * η := by push_cast; nlinarith
      exact int_le_of_mul_le hη this
    · exact int_le_of_mul_le hη (by linarith)
  set I : Finset (ℤ × ℤ) := (Finset.Icc (-N - 1) N ×ˢ Finset.Icc (-N - 1) N).filter
    (fun ij => (gridSq η ij.1 ij.2 ∩ X).Nonempty) with hIdef
  have hmemI : ∀ ij : ℤ × ℤ, ij ∈ I ↔ (gridSq η ij.1 ij.2 ∩ X).Nonempty := by
    intro ij
    rw [hIdef, Finset.mem_filter, Finset.mem_product]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hbound ij.1 ij.2 h, h⟩
  set S : Finset (Pt × Pt) := I.biUnion fun ij =>
    {gridH η ij.1 ij.2, gridH η ij.1 (ij.2 + 1), gridV η ij.1 ij.2, gridV η (ij.1 + 1) ij.2}
    with hSdef
  have hSedge : ∀ s ∈ S, IsGridEdge η s := by
    intro s hs
    obtain ⟨ij, -, hs⟩ := Finset.mem_biUnion.1 hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
  have hSsq : ∀ s ∈ S, ∀ y ∈ segment ℝ s.1 s.2, ∃ x ∈ X, dist y x ≤ η := by
    intro s hs y hy
    obtain ⟨ij, hij, hs⟩ := Finset.mem_biUnion.1 hs
    obtain ⟨x, hxQ, hxX⟩ := (hmemI ij).1 hij
    have hyQ : y ∈ gridSq η ij.1 ij.2 := by
      apply edges_subset_gridSq hη
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (Or.inl hy))
      · exact Or.inr (Or.inr (Or.inr hy))
    refine ⟨x, hxX, (dist_le_of_mem_rect hyQ hxQ).trans (le_of_eq ?_)⟩
    simp only [gridP, Int.cast_add, Int.cast_one]
    rw [max_eq_left (by ring_nf; rfl)]
    ring
  set G : Set Pt := ⋃ s ∈ S, segment ℝ s.1 s.2 with hGdef
  -- the map
  set fl : Pt → ℤ × ℤ := fun x => (⌊x.1 / η⌋, ⌊x.2 / η⌋) with hfl
  set f : Pt → Pt := fun x => radProj (gridP η (fl x).1 (fl x).2)
    (gridP η ((fl x).1 + 1) ((fl x).2 + 1)) (cen (fl x)) x with hfdef
  have hfl_mem : ∀ x, x ∈ gridSq η (fl x).1 (fl x).2 := fun x => mem_gridSq_floor hη x
  have hf_eq : ∀ (ij : ℤ × ℤ) (x : Pt), x ∈ gridSq η ij.1 ij.2 →
      f x = radProj (gridP η ij.1 ij.2) (gridP η (ij.1 + 1) (ij.2 + 1)) (cen ij) x := by
    intro ij x hx
    by_cases h : fl x = ij
    · simp only [hfdef, h]
    · have h' : ((fl x).1, (fl x).2) ≠ (ij.1, ij.2) := h
      rw [hfdef]
      dsimp only
      rw [radProj_of_onBdry (hcenI _) (hfl_mem x) (onBdry_of_mem_two_gridSq hη (hfl_mem x) hx h'),
        radProj_of_onBdry (hcenI _) hx (onBdry_of_mem_two_gridSq hη hx (hfl_mem x) h'.symm)]
  have hflI : ∀ x ∈ X, fl x ∈ I := fun x hx => (hmemI _).2 ⟨x, hfl_mem x, hx⟩
  refine ⟨G, ⟨S, fun s hs => gridEdge_ne hη (hSedge s hs), rfl,
    fun s hs s' hs' hne => gridEdge_inter_subset hη (hSedge s hs) (hSedge s' hs') hne⟩, ?_, f, ?_,
    fun x hx => ?_⟩
  · intro y hy
    obtain ⟨s, hs, hy⟩ := mem_iUnion₂.1 hy
    obtain ⟨x, hxX, hxy⟩ := hSsq s hs y hy
    exact mem_thickening_iff.2 ⟨x, hxX, by linarith⟩
  · have hcov : X ⊆ ⋃ ij ∈ I, X ∩ gridSq η ij.1 ij.2 := fun x hx =>
      mem_iUnion₂.2 ⟨fl x, hflI x hx, hx, hfl_mem x⟩
    refine ContinuousOn.mono (continuousOn_biUnion_finset I (fun ij _ => ?_) (fun ij _ => ?_)) hcov
    · exact hX.isClosed.inter (by
        rw [show gridSq η ij.1 ij.2 = {x : Pt | (ij.1 : ℝ) * η ≤ x.1 ∧ x.1 ≤ (ij.1 + 1) * η ∧
          (ij.2 : ℝ) * η ≤ x.2 ∧ x.2 ≤ (ij.2 + 1) * η} from Set.ext fun x => mem_gridSq_iff]
        exact (isClosed_le continuous_const continuous_fst).inter
          ((isClosed_le continuous_fst continuous_const).inter
          ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd continuous_const))))
    · refine ((continuousOn_radProj (hcenI ij)).mono fun x hx => ?_).congr
        fun x hx => hf_eq ij x hx.2
      exact fun h => hcenX ij (h ▸ hx.1)
  · have hxc : x ≠ cen (fl x) := fun h => hcenX (fl x) (h ▸ hx)
    obtain ⟨hr1, hr2⟩ := radProj_mem (hcenI (fl x)) hxc
    refine ⟨?_, ?_⟩
    · refine mem_iUnion₂.2 ?_
      rcases onBdry_gridSq hη hr1 hr2 with h | h | h | h
      · exact ⟨_, Finset.mem_biUnion.2 ⟨fl x, hflI x hx, by simp⟩, h⟩
      · exact ⟨_, Finset.mem_biUnion.2 ⟨fl x, hflI x hx, by simp⟩, h⟩
      · exact ⟨_, Finset.mem_biUnion.2 ⟨fl x, hflI x hx, by simp⟩, h⟩
      · exact ⟨_, Finset.mem_biUnion.2 ⟨fl x, hflI x hx, by simp⟩, h⟩
    · have := dist_le_of_mem_rect hr1 (hfl_mem x)
      have e1 : (gridP η ((fl x).1 + 1) ((fl x).2 + 1)).1 - (gridP η (fl x).1 (fl x).2).1 = η := by
        simp only [gridP, Int.cast_add, Int.cast_one]; ring
      have e2 : (gridP η ((fl x).1 + 1) ((fl x).2 + 1)).2 - (gridP η (fl x).1 (fl x).2).2 = η := by
        simp only [gridP, Int.cast_add, Int.cast_one]; ring
      rw [e1, e2, max_self] at this
      exact this.trans_lt (half_lt_self hδ)

end HPC.HO16
