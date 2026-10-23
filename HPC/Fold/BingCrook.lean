import HPC.Fold.BingF

/-!
# Bing's pattern is crooked

Batch 82. The pattern `bingF d` is crooked in the strong (level) sense: between an index at level
`≤ h` and an index at level `≥ k`, `k ≥ h + 3`, there are indices at levels `k − 1` and `h + 1`, in
that order starting from the low one. Proof by induction on `d` through the three pieces.
-/

namespace HPC.Fold

/-- `r` and `s` lie strictly between `i` and `j`, `r` nearer to `i`. -/
def NBetween (i r s j : ℕ) : Prop := (i < r ∧ r < s ∧ s < j) ∨ (j < s ∧ s < r ∧ r < i)

theorem NBetween.symm {i r s j : ℕ} (h : NBetween i r s j) : NBetween j s r i := by
  unfold NBetween at *; omega

/-- A discrete intermediate value theorem. -/
theorem exists_eq_of_lip (g : ℕ → ℤ) (hg : ∀ u, |g (u + 1) - g u| ≤ 1) :
    ∀ (len lo : ℕ) (v : ℤ), (g lo ≤ v ∧ v ≤ g (lo + len)) ∨ (g (lo + len) ≤ v ∧ v ≤ g lo) →
      ∃ s, lo ≤ s ∧ s ≤ lo + len ∧ g s = v
  | 0, lo, v, h => ⟨lo, le_rfl, le_rfl, by simp at h; omega⟩
  | len + 1, lo, v, h => by
      by_cases hv : g lo = v
      · exact ⟨lo, le_rfl, by omega, hv⟩
      · have h1 := hg lo
        rw [abs_le] at h1
        obtain ⟨s, hs1, hs2, hs3⟩ := exists_eq_of_lip g hg len (lo + 1) v (by
          rw [show lo + 1 + len = lo + (len + 1) by ring]; omega)
        exact ⟨s, by omega, by omega, hs3⟩

/-- Crookedness of a level sequence on the index window `[lo, hi]`. -/
def PatCrookedOn (g : ℕ → ℤ) (lo hi : ℕ) : Prop :=
  ∀ i j, lo ≤ i → i ≤ hi → lo ≤ j → j ≤ hi → ∀ h k : ℤ, g i ≤ h → k ≤ g j → h + 3 ≤ k →
    ∃ r s, NBetween i r s j ∧ g r = k - 1 ∧ g s = h + 1

/-- Crookedness is local to the window. -/
theorem PatCrookedOn.congr {g g' : ℕ → ℤ} {lo hi : ℕ} (hc : PatCrookedOn g lo hi)
    (he : ∀ u, lo ≤ u → u ≤ hi → g' u = g u) : PatCrookedOn g' lo hi := by
  intro i j hi1 hi2 hj1 hj2 h k hgi hgj hhk
  rw [he i hi1 hi2] at hgi
  rw [he j hj1 hj2] at hgj
  obtain ⟨r, s, hb, hr, hs⟩ := hc i j hi1 hi2 hj1 hj2 h k hgi hgj hhk
  refine ⟨r, s, hb, ?_, ?_⟩
  · rw [he r (by unfold NBetween at hb; omega) (by unfold NBetween at hb; omega)]; exact hr
  · rw [he s (by unfold NBetween at hb; omega) (by unfold NBetween at hb; omega)]; exact hs

/-- Shifting indices by `o` and levels by `c`. -/
theorem PatCrookedOn.shift {g : ℕ → ℤ} {lo hi : ℕ} (hc : PatCrookedOn g lo hi) (o : ℕ) (c : ℤ) :
    PatCrookedOn (fun u => c + g (u - o)) (lo + o) (hi + o) := by
  intro i j hi1 hi2 hj1 hj2 h k hgi hgj hhk
  obtain ⟨r, s, hb, hr, hs⟩ := hc (i - o) (j - o) (by omega) (by omega) (by omega) (by omega)
    (h - c) (k - c) (by simp only at hgi; linarith) (by simp only at hgj; linarith) (by linarith)
  refine ⟨r + o, s + o, by unfold NBetween at *; omega, ?_, ?_⟩
  · simp only [Nat.add_sub_cancel]; linarith
  · simp only [Nat.add_sub_cancel]; linarith

/-- Reflecting levels. -/
theorem PatCrookedOn.neg {g : ℕ → ℤ} {lo hi : ℕ} (hc : PatCrookedOn g lo hi) (c : ℤ) :
    PatCrookedOn (fun u => c - g u) lo hi := by
  intro i j hi1 hi2 hj1 hj2 h k hgi hgj hhk
  obtain ⟨r, s, hb, hr, hs⟩ := hc j i hj1 hj2 hi1 hi2 (c - k) (c - h)
    (by simp only at hgj; linarith) (by simp only at hgi; linarith) (by linarith)
  exact ⟨s, r, hb.symm, by simp only; linarith, by simp only; linarith⟩

theorem bingF_ge_one (d u : ℕ) (hu0 : 0 < u) (hu : u < z d) : 1 ≤ bingF d u := by
  have h0 := bingF_nonneg d u
  have : bingF d u ≠ 0 := fun h => by have := bingF_eq_zero d u hu h; omega
  omega

/-- **Bing's pattern is crooked.** -/
theorem bingF_crooked : ∀ d : ℕ, PatCrookedOn (bingF d) 0 (z d - 1)
  | 0 => by
      intro i j _ _ _ _ h k hi hj hhk
      have := bingF_nonneg 0 i; have := bingF_le 0 j; push_cast at *; omega
  | 1 => by
      intro i j _ _ _ _ h k hi hj hhk
      have := bingF_nonneg 1 i; have := bingF_le 1 j; push_cast at *; omega
  | 2 => by
      intro i j _ _ _ _ h k hi hj hhk
      have := bingF_nonneg 2 i; have := bingF_le 2 j; push_cast at *; omega
  | d + 3 => by
      have hA3 := z_three_le (d + 2) (by omega)
      have hB2 := z_two_le (d + 1) (by omega)
      have hz := z_succ3 d
      set zA := z (d + 2) with hzA
      set zB := z (d + 1) with hzB
      -- the three windows
      have cA : PatCrookedOn (bingF (d + 3)) 0 (zA - 1) :=
        (bingF_crooked (d + 2)).congr (fun u _ hu => bingF_A d u (by omega))
      have cB : PatCrookedOn (bingF (d + 3)) (zA - 1) (zA + zB - 2) := by
        have := (((bingF_crooked (d + 1)).neg ((d : ℤ) + 2)).shift (zA - 1) 0)
        rw [show 0 + (zA - 1) = zA - 1 by omega,
          show z (d + 1) - 1 + (zA - 1) = zA + zB - 2 by omega] at this
        refine this.congr (fun u hu1 hu2 => ?_)
        rw [bingF_B d u hu1 (by omega)]; ring
      have cC : PatCrookedOn (bingF (d + 3)) (zA + zB - 2) (z (d + 3) - 1) := by
        have := ((bingF_crooked (d + 2)).shift (zA + zB - 2) 1)
        rw [show 0 + (zA + zB - 2) = zA + zB - 2 by omega,
          show z (d + 2) - 1 + (zA + zB - 2) = z (d + 3) - 1 by omega] at this
        refine this.congr (fun u hu1 _ => ?_)
        rw [bingF_C d u hu1]
      -- levels at the junctions and bounds
      have lp1 : bingF (d + 3) (zA - 1) = (d : ℤ) + 2 := by
        rw [bingF_A d _ (by omega), bingF_top (d + 2) _ le_rfl]; push_cast; ring
      have lp2 : bingF (d + 3) (zA + zB - 2) = 1 := by
        rw [bingF_C d _ le_rfl, Nat.sub_self, bingF_zero]; ring
      have hlip := bingF_lip (d + 3)
      have hle : ∀ u, bingF (d + 3) u ≤ (d : ℤ) + 3 := fun u => by
        have := bingF_le (d + 3) u; push_cast at this; exact this
      have hB_le : ∀ u, u ≤ zA + zB - 2 → bingF (d + 3) u ≤ (d : ℤ) + 2 := by
        intro u hu
        rcases Nat.lt_or_ge u zA with h | h
        · rw [bingF_A d u h]; have := bingF_le (d + 2) u; push_cast at this; exact this
        · rw [bingF_B d u (by omega) (by omega)]
          have := bingF_nonneg (d + 1) (u - (zA - 1)); linarith
      have htop : ∀ u, u < z (d + 3) → bingF (d + 3) u = (d : ℤ) + 3 → u = z (d + 3) - 1 := by
        intro u hu h
        have := bingF_eq_top (d + 3) u (by rw [h]; push_cast; ring)
        omega
      have hpos : ∀ u, 0 < u → u < z (d + 3) → 1 ≤ bingF (d + 3) u :=
        fun u h1 h2 => bingF_ge_one (d + 3) u h1 h2
      intro i j _ hi2 _ hj2 h k hgi hgj hhk
      have hilt : i < z (d + 3) := by omega
      have hjlt : j < z (d + 3) := by omega
      -- both in one window
      by_cases hAA : i ≤ zA - 1 ∧ j ≤ zA - 1
      · exact cA i j (by omega) hAA.1 (by omega) hAA.2 h k hgi hgj hhk
      by_cases hBB : zA - 1 ≤ i ∧ i ≤ zA + zB - 2 ∧ zA - 1 ≤ j ∧ j ≤ zA + zB - 2
      · exact cB i j hBB.1 hBB.2.1 hBB.2.2.1 hBB.2.2.2 h k hgi hgj hhk
      by_cases hCC : zA + zB - 2 ≤ i ∧ zA + zB - 2 ≤ j
      · exact cC i j hCC.1 hi2 hCC.2 hj2 h k hgi hgj hhk
      rcases Nat.lt_or_ge i j with hij | hij
      · -- the low index comes first
        by_cases hiA : i < zA - 1
        · by_cases hk : k ≤ (d : ℤ) + 2
          · obtain ⟨r, s, hb, hr, hs⟩ :=
              cA i (zA - 1) (by omega) (by omega) (by omega) le_rfl h k hgi (by rw [lp1]; exact hk)
                hhk
            exact ⟨r, s, by unfold NBetween at *; omega, hr, hs⟩
          · -- `j` is the last index
            have hj : j = z (d + 3) - 1 := htop j hjlt (by have := hle j; linarith)
            have hh : h ≤ d := by linarith [hle j]
            obtain ⟨s, hs1, hs2, hs3⟩ :=
              exists_eq_of_lip (bingF (d + 3)) hlip (zB - 1) (zA - 1) (h + 1)
                (Or.inr ⟨by rw [show zA - 1 + (zB - 1) = zA + zB - 2 by omega, lp2]
                            have := bingF_nonneg (d + 3) i; linarith,
                          by rw [lp1]; linarith⟩)
            refine ⟨zA - 1, s, Or.inl ⟨hiA, ?_, by omega⟩, by rw [lp1]; linarith [hle j], hs3⟩
            rcases Nat.lt_or_ge (zA - 1) s with h1 | h1
            · exact h1
            · exfalso; have : s = zA - 1 := by omega
              rw [this, lp1] at hs3; linarith
        · -- `i` in the middle piece, `j` in the last
          have hi1 : 1 ≤ bingF (d + 3) i := hpos i (by omega) hilt
          obtain ⟨r, s, hb, hr, hs⟩ :=
            cC (zA + zB - 2) j le_rfl (by omega) (by omega) hj2 h k (by rw [lp2]; linarith) hgj
              hhk
          exact ⟨r, s, by unfold NBetween at *; omega, hr, hs⟩
      · -- the low index comes last
        have hij' : j < i := by
          rcases Nat.lt_or_ge j i with h1 | h1
          · exact h1
          · exfalso; have : i = j := by omega
            subst this; linarith
        have hi1 : 1 ≤ bingF (d + 3) i := hpos i (by omega) hilt
        by_cases hjA : j < zA - 1
        · by_cases hiB : i ≤ zA + zB - 2
          · obtain ⟨r, s, hb, hr, hs⟩ :=
              cB i (zA - 1) (by omega) hiB le_rfl (by omega) h k hgi
                (by rw [lp1]; linarith [hB_le j (by omega)]) hhk
            exact ⟨r, s, by unfold NBetween at *; omega, hr, hs⟩
          · obtain ⟨r, s, hb, hr, hs⟩ :=
              cB (zA + zB - 2) (zA - 1) (by omega) le_rfl le_rfl (by omega) h k
                (by rw [lp2]; linarith) (by rw [lp1]; linarith [hB_le j (by omega)]) hhk
            exact ⟨r, s, by unfold NBetween at *; omega, hr, hs⟩
        · -- `j` in the middle piece, `i` in the last
          have hjB : j ≤ zA + zB - 2 := by omega
          obtain ⟨r, s, hb, hr, hs⟩ :=
            cB (zA + zB - 2) j (by omega) le_rfl (by omega) hjB h k (by rw [lp2]; linarith) hgj hhk
          exact ⟨r, s, by unfold NBetween at *; omega, hr, hs⟩

end HPC.Fold
