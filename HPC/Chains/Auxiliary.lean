import Mathlib

/-!
# Auxiliary arithmetic: a discrete intermediate value theorem

This file is not part of the commissioned statement list; it holds the index combinatorics
used in the proofs of T4 and T5.  A function on ℕ whose consecutive values differ by at most
one attains, between two indices, every value strictly between the two endpoint values, and
attains two such values *in order*.  See `HPC.exists_step_between`.
-/

namespace HPC

/-- Discrete intermediate value theorem, two values at once and in order.

If `g` changes by at most one at each step, `g i < p < q < g j` and `i < j`, then there are
`i < x < y < j` with `g x = p` and `g y = q`. -/
theorem exists_step_between {g : ℕ → ℤ} (hstep : ∀ t, |g (t + 1) - g t| ≤ 1)
    {i j : ℕ} (hij : i < j) {p q : ℤ} (h1 : g i < p) (h2 : p < q) (h3 : q < g j) :
    ∃ x y : ℕ, i < x ∧ x < y ∧ y < j ∧ g x = p ∧ g y = q := by
  classical
  have hstep' : ∀ t, g (t + 1) - g t ≤ 1 ∧ -(1 : ℤ) ≤ g (t + 1) - g t := fun t =>
    ⟨(abs_le.mp (hstep t)).2, (abs_le.mp (hstep t)).1⟩
  -- `y` : the first index at or after `i` where `g` reaches `q`.
  have hex : ∃ t, i ≤ t ∧ q ≤ g t := ⟨j, hij.le, h3.le⟩
  set y := Nat.find hex with hy
  obtain ⟨hiy, hqy⟩ : i ≤ y ∧ q ≤ g y := Nat.find_spec hex
  have hmin : ∀ t, t < y → ¬(i ≤ t ∧ q ≤ g t) := fun t ht => Nat.find_min hex ht
  have hiy' : i < y := by
    rcases hiy.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hqy) (by omega)
  have hyj : y ≤ j := Nat.find_le ⟨hij.le, h3.le⟩
  have hgy : g y = q := by
    have hlt : g (y - 1) < q := by
      have h := hmin (y - 1) (by omega)
      rw [not_and_or] at h
      rcases h with h | h
      · omega
      · omega
    have h5 := hstep' (y - 1)
    have hy1 : y - 1 + 1 = y := by omega
    rw [hy1] at h5
    omega
  have hyj' : y < j := by
    rcases hyj.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hgy) (by omega)
  -- `x` : the last index at or before `y` where `g` is still at most `p`.
  set P : ℕ → Prop := fun t => i ≤ t ∧ g t ≤ p with hP
  set x := Nat.findGreatest P y with hx
  have hPi : P i := ⟨le_rfl, h1.le⟩
  have hPx : P x := Nat.findGreatest_spec (m := i) (by omega) hPi
  have hxy : x ≤ y := Nat.findGreatest_le y
  have hxy' : x < y := by
    rcases hxy.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hPx.2) (by omega)
  have hix : i ≤ x := hPx.1
  have hgx1 : p < g (x + 1) := by
    have hnot : ¬P (x + 1) :=
      Nat.findGreatest_is_greatest (P := P) (n := y) (k := x + 1) (by omega) (by omega)
    rw [hP, not_and_or] at hnot
    rcases hnot with h | h
    · omega
    · omega
  have hgx : g x = p := by
    have h5 := hstep' x
    omega
  have hix' : i < x := by
    rcases hix.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hgx) (by omega)
  exact ⟨x, y, hix', hxy', hyj', hgx, hgy⟩

/-- Same as `exists_step_between`, for a decreasing pair of target values. -/
theorem exists_step_between_anti {g : ℕ → ℤ} (hstep : ∀ t, |g (t + 1) - g t| ≤ 1)
    {i j : ℕ} (hij : i < j) {p q : ℤ} (h1 : p < g i) (h2 : q < p) (h3 : g j < q) :
    ∃ x y : ℕ, i < x ∧ x < y ∧ y < j ∧ g x = p ∧ g y = q := by
  have hstep' : ∀ t, |(-g) (t + 1) - (-g) t| ≤ 1 := by
    intro t
    have h := hstep t
    rw [abs_sub_comm] at h
    simpa [show -g (t + 1) + g t = g t - g (t + 1) by ring] using h
  obtain ⟨x, y, h4, h5, h6, h7, h8⟩ :=
    exists_step_between hstep' hij (p := -p) (q := -q) (by simpa using h1)
      (by simpa using h2) (by simpa using h3)
  exact ⟨x, y, h4, h5, h6, by simpa [neg_eq_iff_eq_neg] using h7,
    by simpa [neg_eq_iff_eq_neg] using h8⟩

/-- `x` and `y` lie strictly between `i` and `j`, with `x` on the side of `i`. -/
def BetweenN (i x y j : ℕ) : Prop := (i < x ∧ x < y ∧ y < j) ∨ (j < y ∧ y < x ∧ x < i)

/-- Discrete intermediate value theorem in its unoriented form: if `p` and `q` lie strictly
between `g i` and `g j`, with `p` on the side of `g i`, then `g` takes the values `p` and `q`
at two indices strictly between `i` and `j`, the first on the side of `i`. -/
theorem exists_step_between_gen {g : ℕ → ℤ} (hstep : ∀ t, |g (t + 1) - g t| ≤ 1) {i j : ℕ}
    {p q : ℤ} (hb : (g i < p ∧ p < q ∧ q < g j) ∨ (g j < q ∧ q < p ∧ p < g i)) :
    ∃ x y : ℕ, BetweenN i x y j ∧ g x = p ∧ g y = q := by
  have hne : g i ≠ g j := by rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
  have hij : i ≠ j := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · obtain ⟨x, y, h4, h5, h6, h7, h8⟩ := exists_step_between hstep hlt h1 h2 h3
      exact ⟨x, y, Or.inl ⟨h4, h5, h6⟩, h7, h8⟩
    · obtain ⟨x, y, h4, h5, h6, h7, h8⟩ := exists_step_between_anti hstep hlt h3 h2 h1
      exact ⟨x, y, Or.inl ⟨h4, h5, h6⟩, h7, h8⟩
  -- reflect the index line so that the two indices are again in increasing order
  · set G : ℕ → ℤ := fun t => g (i + j - t) with hG
    have hGstep : ∀ t, |G (t + 1) - G t| ≤ 1 := by
      intro t
      by_cases ht : t < i + j
      · have h1 : i + j - t = (i + j - (t + 1)) + 1 := by omega
        have := hstep (i + j - (t + 1))
        rw [hG]
        simp only
        rw [h1]
        rwa [abs_sub_comm] at this
      · have h1 : i + j - t = 0 := by omega
        have h2 : i + j - (t + 1) = 0 := by omega
        simp [hG, h1, h2]
    have hGi : G j = g i := by simp [hG, show i + j - j = i by omega]
    have hGj : G i = g j := by simp [hG, show i + j - i = j by omega]
    have key : ∃ x y : ℕ, j < x ∧ x < y ∧ y < i ∧ G x = p ∧ G y = q := by
      rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact exists_step_between hGstep hgt (by rw [hGi]; exact h1) h2 (by rw [hGj]; exact h3)
      · exact exists_step_between_anti hGstep hgt (by rw [hGi]; exact h3) h2
          (by rw [hGj]; exact h1)
    obtain ⟨x, y, h4, h5, h6, h7, h8⟩ := key
    refine ⟨i + j - x, i + j - y, Or.inr ⟨by omega, by omega, by omega⟩, ?_, ?_⟩
    · simpa [hG] using h7
    · simpa [hG] using h8

/-- A one-sided discrete intermediate value theorem: if `g` changes by at most one at each
step, `g i` is at least `p`, `g j` is at most `q < p`, and `i ≤ j`, then `g` takes the value
`p` and then the value `q` at indices in `[i, j]`. -/
theorem exists_step_le_between {g : ℕ → ℤ} (hstep : ∀ t, |g (t + 1) - g t| ≤ 1) {i j : ℕ}
    (hij : i ≤ j) {p q : ℤ} (hqp : q < p) (h1 : p ≤ g i) (h2 : g j ≤ q) :
    ∃ x y : ℕ, i ≤ x ∧ x < y ∧ y ≤ j ∧ g x = p ∧ g y = q := by
  classical
  have hstep' : ∀ t, g (t + 1) - g t ≤ 1 ∧ -(1 : ℤ) ≤ g (t + 1) - g t := fun t =>
    ⟨(abs_le.mp (hstep t)).2, (abs_le.mp (hstep t)).1⟩
  -- the first index at or after `i` where `g` has come down to `p`
  have hex1 : ∃ t, i ≤ t ∧ g t ≤ p := ⟨j, hij, by omega⟩
  set x := Nat.find hex1 with hxdef
  obtain ⟨hix, hgx⟩ : i ≤ x ∧ g x ≤ p := Nat.find_spec hex1
  have hxj : x ≤ j := Nat.find_le ⟨hij, by omega⟩
  have hgxp : g x = p := by
    rcases hix.lt_or_eq with hlt | heq
    · have hmin := Nat.find_min hex1 (m := x - 1) (by omega)
      rw [not_and_or] at hmin
      have hs := hstep' (x - 1)
      have hx1 : x - 1 + 1 = x := by omega
      rw [hx1] at hs
      rcases hmin with hmin | hmin <;> omega
    · rw [← heq] at hgx ⊢
      omega
  -- the first index at or after `x` where `g` has come down to `q`
  have hex2 : ∃ t, x ≤ t ∧ g t ≤ q := ⟨j, hxj, h2⟩
  set y := Nat.find hex2 with hydef
  obtain ⟨hxy, hgy⟩ : x ≤ y ∧ g y ≤ q := Nat.find_spec hex2
  have hyj : y ≤ j := Nat.find_le ⟨hxj, h2⟩
  have hxy' : x < y := by
    rcases hxy.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq] at hgy
      omega
  have hgyq : g y = q := by
    have hmin := Nat.find_min hex2 (m := y - 1) (by omega)
    rw [not_and_or] at hmin
    have hs := hstep' (y - 1)
    have hy1 : y - 1 + 1 = y := by omega
    rw [hy1] at hs
    rcases hmin with hmin | hmin <;> omega
  exact ⟨x, y, hix, hxy', hyj, hgxp, hgyq⟩

/-- The unoriented form of `exists_step_le_between`. -/
theorem exists_step_le_between_gen {g : ℕ → ℤ} (hstep : ∀ t, |g (t + 1) - g t| ≤ 1) {i j : ℕ}
    {p q : ℤ} (hqp : q < p) (h1 : p ≤ g i) (h2 : g j ≤ q) :
    ∃ x y : ℕ, ((i ≤ x ∧ x < y ∧ y ≤ j) ∨ (j ≤ y ∧ y < x ∧ x ≤ i)) ∧ g x = p ∧ g y = q := by
  rcases le_or_gt i j with hij | hij
  · obtain ⟨x, y, h3, h4, h5, h6, h7⟩ := exists_step_le_between hstep hij hqp h1 h2
    exact ⟨x, y, Or.inl ⟨h3, h4, h5⟩, h6, h7⟩
  · set G : ℕ → ℤ := fun t => g (i + j - t) with hG
    have hGstep : ∀ t, |G (t + 1) - G t| ≤ 1 := by
      intro t
      by_cases ht : t < i + j
      · have h3 : i + j - t = (i + j - (t + 1)) + 1 := by omega
        have h4 := hstep (i + j - (t + 1))
        rw [hG]
        simp only
        rw [h3]
        rwa [abs_sub_comm] at h4
      · have h3 : i + j - t = 0 := by omega
        have h4 : i + j - (t + 1) = 0 := by omega
        simp [hG, h3, h4]
    have hGj : G j = g i := by simp [hG, show i + j - j = i by omega]
    have hGi : G i = g j := by simp [hG, show i + j - i = j by omega]
    obtain ⟨x, y, h3, h4, h5, h6, h7⟩ :=
      exists_step_le_between hGstep hij.le hqp (by rw [hGj]; exact h1) (by rw [hGi]; exact h2)
    refine ⟨i + j - x, i + j - y, Or.inr ⟨by omega, by omega, by omega⟩, ?_, ?_⟩
    · simpa [hG] using h6
    · simpa [hG] using h7

end HPC
