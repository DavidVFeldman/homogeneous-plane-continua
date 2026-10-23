import HPC.Fold.Pair79Fin

/-!
# Batch 79: the exclusion behind two-link basepoints

For adjacent links `lo`, `hi` with `ρ hi = σ hi = ρ lo + 1`, a fold on the least levels started
just above `ρ lo` from `lo` and a fold on the greatest levels started just below `σ hi` from `hi`
cannot both be forbidden: the two events together contradict the crookedness clause.
-/

namespace HPC.Fold.B79

variable {n : ℕ}

theorem pair_exclusion (ρ σ : Fin n → ℤ) (hcr : IsCrookedIvF ρ σ) (lo hi a : Fin n)
    (hadj : lo.val = hi.val + 1 ∨ hi.val = lo.val + 1) (hloa : lo ≤ a)
    (hρ : ρ hi = ρ lo + 1) (hσ : σ hi = ρ lo + 1) (hnn : ∀ t, 0 ≤ ρ t)
    (hmeetA : ∀ t : Fin n, t < a → 3 ≤ ρ t → ∃ y y' : Fin n, t < y ∧ y < y' ∧ y' < a ∧
      ρ y ≤ 1 ∧ ρ t - 1 ≤ σ y')
    (hup : EvUp ρ lo a 0) (hdown : EvDown σ hi a 0) : False := by
  set x := ρ lo with hx
  have hle := hcr.le
  rw [Fin.le_def] at hloa
  have hσlo : x ≤ σ lo := hle lo
  rcases hup with ⟨t, hta, hρt, hT⟩ | ⟨h0, -⟩
  swap
  · have := hnn lo; omega
  have hT' : ∀ w : Fin n, (lo.val < w.val ∧ w.val < t.val) ∨ (t.val < w.val ∧ w.val < lo.val) →
      x ≤ ρ w := fun w hw => hT w hw
  rw [Fin.le_def] at hta
  have htlo : t.val ≠ lo.val := fun h => by
    have : t = lo := Fin.ext h
    rw [this] at hρt; omega
  have hthi : t.val ≠ hi.val := fun h => by
    have : t = hi := Fin.ext h
    rw [this] at hρt; omega
  have hσt : x + 3 ≤ σ t := by have := hle t; omega
  rcases hdown with ⟨u, hua, hσu, hU⟩ | ⟨h0, hU⟩
  · have hU' : ∀ w : Fin n, (hi.val < w.val ∧ w.val < u.val) ∨ (u.val < w.val ∧ w.val < hi.val) →
        σ w ≤ x + 1 := fun w hw => by have := hU w hw; omega
    rw [Fin.le_def] at hua
    have hρu : ρ u ≤ x - 2 := by have := hle u; omega
    have hulo : u.val ≠ lo.val := fun h => by
      have : u = lo := Fin.ext h
      rw [this] at hσu; omega
    have huhi : u.val ≠ hi.val := fun h => by
      have : u = hi := Fin.ext h
      rw [this] at hσu; omega
    rcases lt_or_gt_of_ne htlo with htl | htl <;> rcases lt_or_gt_of_ne huhi with huh | huh
    · -- both below the pair
      rcases lt_or_gt_of_ne (show t.val ≠ u.val by
        intro h; have : t = u := Fin.ext h; rw [this] at hρt; omega) with h | h
      · have := hT' u (Or.inr ⟨h, by omega⟩); omega
      · have := hU' t (Or.inr ⟨h, by omega⟩); omega
    · -- `t` below, `u` above
      have hsu : t < u := by rw [Fin.lt_def]; omega
      obtain ⟨w, w', h1, h2, h3, -, h5⟩ := hcr.crooked t u hsu (x + 3) (x - 2)
        ⟨t, by simp, by omega, hσt⟩ ⟨u, by simp, hρu, by omega⟩ (by rw [abs_of_nonneg] <;> omega)
      obtain ⟨⟨k1, k2⟩, ⟨k3, k4⟩⟩ := h5 (by omega)
      rw [Fin.lt_def] at h1 h2 h3
      have hwlo : lo.val < w.val := by
        rcases lt_trichotomy w.val lo.val with h | h | h
        · have := hT' w (Or.inr ⟨h1, h⟩); omega
        · have : w = lo := Fin.ext h
          rw [this] at k1; omega
        · exact h
      have hw'hi : w'.val ≠ hi.val := fun h => by
        have : w' = hi := Fin.ext h
        rw [this] at k4; omega
      have := hU' w' (Or.inl ⟨by omega, h3⟩); omega
    · -- `t` above, `u` below
      have hsu : u < t := by rw [Fin.lt_def]; omega
      obtain ⟨w, w', h1, h2, h3, h5, -⟩ := hcr.crooked u t hsu (x - 2) (x + 3)
        ⟨u, by simp, hρu, by omega⟩ ⟨t, by simp, by omega, hσt⟩ (by rw [abs_of_nonpos] <;> omega)
      obtain ⟨⟨k1, k2⟩, ⟨k3, k4⟩⟩ := h5 (by omega)
      rw [Fin.lt_def] at h1 h2 h3
      have hwhi : hi.val < w.val := by
        rcases lt_trichotomy w.val hi.val with h | h | h
        · have := hU' w (Or.inr ⟨h1, h⟩); omega
        · have : w = hi := Fin.ext h
          rw [this] at k2; omega
        · exact h
      have hw'lo : w'.val ≠ lo.val := fun h => by
        have : w' = lo := Fin.ext h
        rw [this] at k3; omega
      have := hT' w' (Or.inl ⟨by omega, h3⟩); omega
    · -- both above the pair
      rcases lt_or_gt_of_ne (show t.val ≠ u.val by
        intro h; have : t = u := Fin.ext h; rw [this] at hρt; omega) with h | h
      · have := hU' t (Or.inl ⟨by omega, h⟩); omega
      · have := hT' u (Or.inl ⟨by omega, h⟩); omega
  · -- the fake low link: `x = 2` and `σ ≤ 3` from `hi` to `a`
    have hU' : ∀ w : Fin n, hi.val ≤ w.val → w.val ≤ a.val → σ w ≤ x + 1 := fun w h1 h2 => by
      have := hU w h1 h2; omega
    rcases lt_or_gt_of_ne htlo with htl | htl
    · obtain ⟨y, y', h1, h2, h3, k1, k2⟩ := hmeetA t (by rw [Fin.lt_def]; omega) (by omega)
      rw [Fin.lt_def] at h1 h2 h3
      have hylo : lo.val < y.val := by
        rcases lt_trichotomy y.val lo.val with h | h | h
        · have := hT' y (Or.inr ⟨h1, h⟩); omega
        · have : y = lo := Fin.ext h
          rw [this] at k1; omega
        · exact h
      have := hU' y' (by omega) (by omega); omega
    · have := hU' t (by omega) hta; omega

end HPC.Fold.B79
