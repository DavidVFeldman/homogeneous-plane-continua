import HPC.Fold.Pair79Ends

/-!
# Batch 79: the folds with a fake end link, some start

The crookedness clause of the extended sequences (`lowExt`, `highExt`) as standalone lemmas, and
with them the folds of `Pair79Ends` in which the start of the walk is whichever
`first_direction` allows.
-/

namespace HPC.Fold.B79

open Z77

theorem crkOn_lowExt (S : ℤ → ℤ) (p q : ℕ)
    (hcr : CrkOn S (-(p : ℤ)) q)
    (hnn : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → 0 ≤ S x) (hend : S q ≤ 1)
    (hmeet : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → 3 ≤ S x →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ S y ≤ 1 ∧ S x - 2 ≤ S y' ∧ S y' ≤ S x - 1) :
    CrkOn (lowExt S q) (1 - extM p q false) (extM p q true - 1) := by
  set S' : ℤ → ℤ := lowExt S q with hS'
  have hS'eq : ∀ x : ℤ, x ≤ q → S' x = S x := by
    intro x hx; simp only [hS', lowExt]; rw [if_neg (by omega)]
  have hS'q1 : S' ((q : ℤ) + 1) = 0 := by simp [hS', lowExt]
  have e1 : (1 : ℤ) - ((extM p q false : ℕ) : ℤ) = -(p : ℤ) := by simp [extM]
  have e2 : ((extM p q true : ℕ) : ℤ) - 1 = (q : ℤ) + 1 := by simp [extM]; ring
  rw [e1, e2]
  intro s t hs hst ht
  rcases lt_or_eq_of_le ht with ht' | ht'
  · have ht'' : t ≤ q := by omega
    obtain ⟨h1, h2⟩ := hcr s t hs hst ht''
    rw [hS'eq s (by omega), hS'eq t ht'']
    constructor
    · intro h
      obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h1 h
      exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
        by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
        by rw [hS'eq r' (by omega)]; exact a7⟩
    · intro h
      obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h2 h
      exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
        by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
        by rw [hS'eq r' (by omega)]; exact a7⟩
  · subst ht'
    rw [hS'eq s (by omega), hS'q1]
    have hs0 := hnn s hs (by omega)
    constructor
    · intro h; omega
    · intro h
      have hsq : s < q := by
        rcases lt_or_eq_of_le (show s ≤ q by omega) with h' | h'
        · exact h'
        · subst h'; omega
      obtain ⟨y, y', a1, a2, a3, a4, a5, a6⟩ := hmeet s hs hsq (by omega)
      have hy0 := hnn y (by omega) (by omega)
      refine ⟨y, y', a1, a2, by omega, ?_, ?_, ?_, ?_⟩
      · rw [hS'eq y (by omega)]; exact hy0
      · rw [hS'eq y (by omega)]; omega
      · rw [hS'eq y' (by omega)]; exact a5
      · rw [hS'eq y' (by omega)]; exact a6

theorem crkOn_highExt (S : ℤ → ℤ) (p q : ℕ) (Hb : ℤ)
    (hcr : CrkOn S (-(p : ℤ)) q)
    (hH : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → S x ≤ Hb) (hend : Hb - 1 ≤ S q)
    (hmeet : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → S x + 3 ≤ Hb →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ Hb - 2 ≤ S y ∧ S y ≤ Hb - 1 ∧ S x ≤ S y' ∧
        S y' ≤ S x + 1) :
    CrkOn (highExt S q Hb) (1 - extM p q false) (extM p q true - 1) := by
  set S' : ℤ → ℤ := highExt S q Hb with hS'
  have hS'eq : ∀ x : ℤ, x ≤ q → S' x = S x := by
    intro x hx; simp only [hS', highExt]; rw [if_neg (by omega)]
  have hS'q1 : S' ((q : ℤ) + 1) = Hb := by simp [hS', highExt]
  have e1 : (1 : ℤ) - ((extM p q false : ℕ) : ℤ) = -(p : ℤ) := by simp [extM]
  have e2 : ((extM p q true : ℕ) : ℤ) - 1 = (q : ℤ) + 1 := by simp [extM]; ring
  rw [e1, e2]
  intro s t hs hst ht
  rcases lt_or_eq_of_le ht with ht' | ht'
  · have ht'' : t ≤ q := by omega
    obtain ⟨h1, h2⟩ := hcr s t hs hst ht''
    rw [hS'eq s (by omega), hS'eq t ht'']
    constructor
    · intro h
      obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h1 h
      exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
        by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
        by rw [hS'eq r' (by omega)]; exact a7⟩
    · intro h
      obtain ⟨r, r', a1, a2, a3, a4, a5, a6, a7⟩ := h2 h
      exact ⟨r, r', a1, a2, a3, by rw [hS'eq r (by omega)]; exact a4,
        by rw [hS'eq r (by omega)]; exact a5, by rw [hS'eq r' (by omega)]; exact a6,
        by rw [hS'eq r' (by omega)]; exact a7⟩
  · subst ht'
    rw [hS'eq s (by omega), hS'q1]
    have hsH := hH s hs (by omega)
    constructor
    · intro h
      have hsq : s < q := by
        rcases lt_or_eq_of_le (show s ≤ q by omega) with h' | h'
        · exact h'
        · subst h'; omega
      obtain ⟨y, y', a1, a2, a3, a4, a5, a6, a7⟩ := hmeet s hs hsq h
      refine ⟨y, y', a1, a2, by omega, ?_, ?_, ?_, ?_⟩
      · rw [hS'eq y (by omega)]; exact a4
      · rw [hS'eq y (by omega)]; exact a5
      · rw [hS'eq y' (by omega)]; exact a6
      · rw [hS'eq y' (by omega)]; exact a7
    · intro h; omega

/-- Either first direction is available for the extended sequence. -/
theorem ok_lowExt (S : ℤ → ℤ) (p q : ℕ)
    (hcr : CrkOn S (-(p : ℤ)) q)
    (hnn : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → 0 ≤ S x) (hend : S q ≤ 1)
    (hmeet : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → 3 ≤ S x →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ S y ≤ 1 ∧ S x - 2 ≤ S y' ∧ S y' ≤ S x - 1) :
    ∃ above : Bool, if above then OKAbove (lowExt S q) (extM p q)
      else OKBelow (lowExt S q) (extM p q) := by
  rcases first_direction (crkOn_lowExt S p q hcr hnn hend hmeet) with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

theorem ok_highExt (S : ℤ → ℤ) (p q : ℕ) (Hb : ℤ)
    (hcr : CrkOn S (-(p : ℤ)) q)
    (hH : ∀ x : ℤ, -(p : ℤ) ≤ x → x ≤ q → S x ≤ Hb) (hend : Hb - 1 ≤ S q)
    (hmeet : ∀ x : ℤ, -(p : ℤ) ≤ x → x < q → S x + 3 ≤ Hb →
      ∃ y y', x < y ∧ y < y' ∧ y' < q ∧ Hb - 2 ≤ S y ∧ S y ≤ Hb - 1 ∧ S x ≤ S y' ∧
        S y' ≤ S x + 1) :
    ∃ above : Bool, if above then OKAbove (highExt S q Hb) (extM p q)
      else OKBelow (highExt S q Hb) (extM p q) := by
  rcases first_direction (crkOn_highExt S p q Hb hcr hH hend hmeet) with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

end HPC.Fold.B79
