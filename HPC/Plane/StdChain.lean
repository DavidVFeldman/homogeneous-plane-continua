import HPC.Chains.Basic

/-!
# The standard chain of rectangles, and its images under plane homeomorphisms

Batch 84. The standard chain with `m` links is the row of open rectangles
`(2j, 2j+3) × (0, 1)`, `j < m`: consecutive links overlap in `(2j+2, 2j+3) × (0,1)`, links two
apart are disjoint. A *tame* chain is the image of a standard chain under a homeomorphism of the
plane; every planar chain built in this batch is tame.
-/

namespace HPC.Plane

open Set

/-- The plane (sup metric of the product). -/
abbrev Pt := ℝ × ℝ

/-- The `j`-th standard rectangle `(2j, 2j+3) × (0,1)`. -/
def stdRect (j : ℕ) : Set Pt := Ioo (2 * (j : ℝ)) (2 * j + 3) ×ˢ Ioo 0 1

/-- The closed *overlap zone* around the overlap of standard links `j` and `j+1`. -/
def zone (j : ℕ) : Set Pt := Icc (2 * (j : ℝ) + 8 / 5) (2 * j + 17 / 5) ×ˢ Icc 0 1

/-- A closed box in the private part of the first standard link. -/
def boxA : Set Pt := Icc (9 / 8 : ℝ) (15 / 8) ×ˢ Icc (1 / 4) (3 / 4)

/-- A closed box in the private part of the last standard link of a chain with `m` links. -/
def boxB (m : ℕ) : Set Pt := Icc (2 * (m : ℝ) - 7 / 8) (2 * m - 1 / 8) ×ˢ Icc (1 / 4) (3 / 4)

/-- The compact region containing the closures of all standard links `j < m`. -/
def region (m : ℕ) : Set Pt := Icc (0 : ℝ) (2 * m + 1) ×ˢ Icc 0 1

theorem isOpen_stdRect (j : ℕ) : IsOpen (stdRect j) := isOpen_Ioo.prod isOpen_Ioo

theorem closure_stdRect (j : ℕ) : closure (stdRect j) = Icc (2 * (j : ℝ)) (2 * j + 3) ×ˢ Icc 0 1 := by
  rw [stdRect, closure_prod_eq, closure_Ioo (by linarith), closure_Ioo (by norm_num)]

theorem isCompact_region (m : ℕ) : IsCompact (region m) := isCompact_Icc.prod isCompact_Icc

theorem isCompact_boxA : IsCompact boxA := isCompact_Icc.prod isCompact_Icc

theorem isCompact_boxB (m : ℕ) : IsCompact (boxB m) := isCompact_Icc.prod isCompact_Icc

theorem boxA_nonempty : boxA.Nonempty := ⟨(3 / 2, 1 / 2), by simp [boxA]; norm_num⟩

theorem boxB_nonempty (m : ℕ) : (boxB m).Nonempty :=
  ⟨(2 * m - 1 / 2, 1 / 2), by
    simp only [boxB, mem_prod, mem_Icc]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith⟩

theorem stdRect_inter_nonempty_iff (i j : ℕ) :
    (stdRect i ∩ stdRect j).Nonempty ↔ (i ≤ j + 1 ∧ j ≤ i + 1) := by
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨h1, h2⟩, -⟩, ⟨h3, h4⟩, -⟩
    have e1 : (i : ℝ) < j + 2 := by linarith
    have e2 : (j : ℝ) < i + 2 := by linarith
    have e1' : i < j + 2 := by exact_mod_cast e1
    have e2' : j < i + 2 := by exact_mod_cast e2
    omega
  · rintro ⟨h1, h2⟩
    have e1 : (i : ℝ) ≤ j + 1 := by exact_mod_cast h1
    have e2 : (j : ℝ) ≤ i + 1 := by exact_mod_cast h2
    refine ⟨(max (2 * (i : ℝ)) (2 * j) + 1 / 2, 1 / 2), ⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · have := le_max_left (2 * (i : ℝ)) (2 * j); linarith
    · rcases le_total (2 * (i : ℝ)) (2 * j) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    · norm_num
    · have := le_max_right (2 * (i : ℝ)) (2 * j); linarith
    · rcases le_total (2 * (i : ℝ)) (2 * j) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    · norm_num

/-- The chain of the images under `Φ` of the first `m` standard rectangles. -/
def tameChain (Φ : Pt ≃ₜ Pt) (m : ℕ) : Chain Pt m where
  link j := Φ '' stdRect j
  isOpen j := Φ.isOpenMap _ (isOpen_stdRect j)
  adjacent i j := by
    rw [← image_inter Φ.injective, image_nonempty, stdRect_inter_nonempty_iff]
    omega

@[simp] theorem tameChain_link (Φ : Pt ≃ₜ Pt) (m : ℕ) (j : Fin m) :
    (tameChain Φ m).link j = Φ '' stdRect j := rfl

theorem closure_tameChain_link (Φ : Pt ≃ₜ Pt) (m : ℕ) (j : Fin m) :
    closure ((tameChain Φ m).link j) = Φ '' closure (stdRect j) := by
  rw [tameChain_link, Φ.image_closure]

/-- A chain is *tame* if it is the image of a standard chain under a plane homeomorphism. -/
def IsTame {m : ℕ} (D : Chain Pt m) : Prop := ∃ Φ : Pt ≃ₜ Pt, ∀ j, D.link j = Φ '' stdRect j

theorem tameChain_isTame (Φ : Pt ≃ₜ Pt) (m : ℕ) : IsTame (tameChain Φ m) := ⟨Φ, fun _ => rfl⟩

theorem closure_stdRect_subset_region {m : ℕ} (j : Fin m) : closure (stdRect j) ⊆ region m := by
  rw [closure_stdRect]
  intro p hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j := by positivity
  exact ⟨⟨by linarith, by linarith⟩, h3⟩

theorem boxA_subset_stdRect : boxA ⊆ stdRect 0 := by
  rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3, h4⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith

theorem boxA_disjoint {j : ℕ} (hj : j ≠ 0) : Disjoint boxA (stdRect j) := by
  rw [Set.disjoint_left]
  rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, -⟩ ⟨⟨h3, -⟩, -⟩
  have : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
  simp only at h2 h3; linarith

theorem boxB_subset_stdRect {m : ℕ} (hm : 0 < m) : boxB m ⊆ stdRect (m - 1) := by
  rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3, h4⟩
  have e : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm]; simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [e] at * <;> linarith

theorem boxB_disjoint {m j : ℕ} (hj : j + 1 < m) : Disjoint (boxB m) (stdRect j) := by
  rw [Set.disjoint_left]
  rintro ⟨a, b⟩ ⟨⟨h1, -⟩, -⟩ ⟨⟨-, h4⟩, -⟩
  have : (j : ℝ) + 2 ≤ m := by exact_mod_cast hj
  simp only at h1 h4; linarith

end HPC.Plane
