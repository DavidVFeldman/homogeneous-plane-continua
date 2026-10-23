import HPC.Fold.Profile
import HPC.Fold.Span9Mid5

/-!
# Span nine: the open branch, cut by the ascent and descent profiles

After batch 41 the span-nine basepoints are settled except two branches (`s3_span_nine_except`):
`ρ i = L + 4` with both arms `HighAt (L + 1) (L + 8)`, and its mirror at `L + 5`. This file cuts
the first of them with the profile engine of `HPC/Fold/Profile.lean`, and the second by the same
argument read upside down.

The two walks are the ones the census of this batch found serving every actual pair of the
branch: the Λ-walk based at `L + 3` with peak `L + 8`, and the V-walk based at `L + 5` through
the valley `L + 1`. What each of them needs of an arm is a single announcement, with no index
attached, because crookedness supplies the index:

* Λ: before the arm ever drops to `L + 1` it has been at `L + 8`;
* V: before the arm ever rises to `L + 7` it has been at `L + 1`.

An arm of the branch falls under the first when it meets the ceiling first, and under the second
when it meets the floor first, so what is left open is only a basepoint whose two arms meet
different ends first, or an arm whose highest level before the floor is exactly `L + 7`.
-/

namespace HPC.Fold

/-- **Span nine, the branch at `L + 4`, Λ.** The exact criterion for the Λ-walk based at
`L + 3` with peak `L + 8`: before an arm ever drops to `L + 1` it stands at `L + 7`, at an index
at least five. No crookedness is needed — this is the criterion itself, and it is exact. -/
theorem s3_span_nine_mid_low_of_lamProfile {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hH : H = L + 9) (hp : ρ i = L + 4)
    (hG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ j : Fin (n - i.val), j.val < d.val ∧ 5 ≤ j.val ∧ L + 7 ≤ armG ρ i j)
    (hT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ j : Fin (i.val + 1), j.val < d.val ∧ 5 ≤ j.val ∧ L + 7 ≤ armT ρ i j) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hk : κ (L + 3) H = L + 8 := by simp only [κ]; omega
  refine exists_folds_of_profile ρ i H L (L + 3) hlip (by omega) (by rw [hp]; rw [abs_le]; omega)
    hLb hHb ?_ ?_
  · rw [critLamProfile_iff_of_isLip (armG_isLip hlip i), hk]
    intro d hd
    obtain ⟨j, hj1, hj2, hj3⟩ := hG d (by omega)
    exact ⟨j, hj1, by omega, by omega⟩
  · rw [critLamProfile_iff_of_isLip (armT_isLip hlip i), hk]
    intro d hd
    obtain ⟨j, hj1, hj2, hj3⟩ := hT d (by omega)
    exact ⟨j, hj1, by omega, by omega⟩

/-- **Span nine, the branch at `L + 4`, V.** The exact criterion for the V-walk based at `L + 5`
through the valley `L + 1`: before an arm ever rises to `L + 7` it stands at `L + 2` or below, at
an index at least four. -/
theorem s3_span_nine_mid_low_of_veeProfile {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hH : H = L + 9) (hp : ρ i = L + 4)
    (hG : ∀ d : Fin (n - i.val), L + 7 ≤ armG ρ i d →
      ∃ j : Fin (n - i.val), j.val < d.val ∧ 4 ≤ j.val ∧ armG ρ i j ≤ L + 2)
    (hT : ∀ d : Fin (i.val + 1), L + 7 ≤ armT ρ i d →
      ∃ j : Fin (i.val + 1), j.val < d.val ∧ 4 ≤ j.val ∧ armT ρ i j ≤ L + 2) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  refine exists_folds_of_veeProfile ρ i H L (L + 5) hlip (by omega)
    (by rw [hp]; rw [abs_le]; omega) hLb hHb ?_ ?_
  · rw [critVeeProfile_iff_of_isLip (armG_isLip hlip i) _ _ (by omega)]
    intro d hd
    obtain ⟨j, hj1, hj2, hj3⟩ := hG d (by omega)
    exact ⟨j, hj1, by omega, by omega⟩
  · rw [critVeeProfile_iff_of_isLip (armT_isLip hlip i) _ _ (by omega)]
    intro d hd
    obtain ⟨j, hj1, hj2, hj3⟩ := hT d (by omega)
    exact ⟨j, hj1, by omega, by omega⟩

/-- **Span nine, the branch at `L + 4`, ceiling first.** If each arm has been at the ceiling
`L + 8` before it ever drops to `L + 1`, the basepoint is served: both arms fold onto the Λ-walk
based at `L + 3`. -/
theorem s3_span_nine_mid_low_of_top {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hH : H = L + 9) (hp : ρ i = L + 4)
    (hG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ j : Fin (n - i.val), j.val < d.val ∧ L + 8 ≤ armG ρ i j)
    (hT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ j : Fin (i.val + 1), j.val < d.val ∧ L + 8 ≤ armT ρ i j) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by simp [armG]
  have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by simp [armT]
  refine exists_folds_of_profile ρ i H L (L + 3) hlip (by omega) (by rw [hp]; rw [abs_le]; omega)
    hLb hHb ?_ ?_
  · refine critLamProfile_of_top_before hmG (armG_isLip hlip i) (crookUp_armG hcr i) (L + 3) H
      (by omega) (by rw [hG0, hp]; omega) ?_
    intro d hd
    obtain ⟨j, hj1, hj2⟩ := hG d (by omega)
    exact ⟨j, hj1, by omega⟩
  · refine critLamProfile_of_top_before hmT (armT_isLip hlip i) (crookUp_armT hcr i) (L + 3) H
      (by omega) (by rw [hT0, hp]; omega) ?_
    intro d hd
    obtain ⟨j, hj1, hj2⟩ := hT d (by omega)
    exact ⟨j, hj1, by omega⟩

/-- **Span nine, the branch at `L + 4`, floor first.** If each arm has been at the floor level
`L + 1` before it ever rises to `L + 7`, the basepoint is served: both arms fold onto the V-walk
based at `L + 5`. -/
theorem s3_span_nine_mid_low_of_floor {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hH : H = L + 9) (hp : ρ i = L + 4)
    (hG : ∀ d : Fin (n - i.val), L + 7 ≤ armG ρ i d →
      ∃ j : Fin (n - i.val), j.val < d.val ∧ armG ρ i j ≤ L + 1)
    (hT : ∀ d : Fin (i.val + 1), L + 7 ≤ armT ρ i d →
      ∃ j : Fin (i.val + 1), j.val < d.val ∧ armT ρ i j ≤ L + 1) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by simp [armG]
  have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by simp [armT]
  refine exists_folds_of_veeProfile ρ i H L (L + 5) hlip (by omega)
    (by rw [hp]; rw [abs_le]; omega) hLb hHb ?_ ?_
  · refine critVeeProfile_of_floor_before hmG (armG_isLip hlip i) (crookDown_armG hcr i) (L + 5) L
      rfl (by rw [hG0, hp]; omega) ?_
    intro d hd
    exact hG d (by omega)
  · refine critVeeProfile_of_floor_before hmT (armT_isLip hlip i) (crookDown_armT hcr i) (L + 5) L
      rfl (by rw [hT0, hp]; omega) ?_
    intro d hd
    exact hT d (by omega)

/-! ## The mirror branch at `L + 5`

The reflection `x ↦ 2L + 9 - x` carries the branch at `L + 5` to the branch at `L + 4`, the
ceiling announcement to the floor announcement, and the Λ-walk based at `L + 3` to the V-walk
based at `L + 6`. The two statements below are the images of the two above; they are proved the
same way, from the profile engine and the timing law, with the two announcements exchanged. -/

/-- **Span nine, the branch at `L + 5`, V.** The exact criterion for the V-walk based at `L + 6`
through the valley `L + 1`. -/
theorem s3_span_nine_mid_high_of_veeProfile {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hH : H = L + 9) (hp : ρ i = L + 5)
    (hG : ∀ d : Fin (n - i.val), L + 8 ≤ armG ρ i d →
      ∃ j : Fin (n - i.val), j.val < d.val ∧ 5 ≤ j.val ∧ armG ρ i j ≤ L + 2)
    (hT : ∀ d : Fin (i.val + 1), L + 8 ≤ armT ρ i d →
      ∃ j : Fin (i.val + 1), j.val < d.val ∧ 5 ≤ j.val ∧ armT ρ i j ≤ L + 2) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  refine exists_folds_of_veeProfile ρ i H L (L + 6) hlip (by omega)
    (by rw [hp]; rw [abs_le]; omega) hLb hHb ?_ ?_
  · rw [critVeeProfile_iff_of_isLip (armG_isLip hlip i) _ _ (by omega)]
    intro d hd
    obtain ⟨j, hj1, hj2, hj3⟩ := hG d (by omega)
    exact ⟨j, hj1, by omega, by omega⟩
  · rw [critVeeProfile_iff_of_isLip (armT_isLip hlip i) _ _ (by omega)]
    intro d hd
    obtain ⟨j, hj1, hj2, hj3⟩ := hT d (by omega)
    exact ⟨j, hj1, by omega, by omega⟩

/-- **Span nine, the branch at `L + 5`, Λ.** The exact criterion for the Λ-walk based at `L + 4`
with peak `L + 8`. -/
theorem s3_span_nine_mid_high_of_lamProfile {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hH : H = L + 9) (hp : ρ i = L + 5)
    (hG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 2 →
      ∃ j : Fin (n - i.val), j.val < d.val ∧ 4 ≤ j.val ∧ L + 7 ≤ armG ρ i j)
    (hT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 2 →
      ∃ j : Fin (i.val + 1), j.val < d.val ∧ 4 ≤ j.val ∧ L + 7 ≤ armT ρ i j) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hk : κ (L + 4) H = L + 8 := by simp only [κ]; omega
  refine exists_folds_of_profile ρ i H L (L + 4) hlip (by omega) (by rw [hp]; rw [abs_le]; omega)
    hLb hHb ?_ ?_
  · rw [critLamProfile_iff_of_isLip (armG_isLip hlip i), hk]
    intro d hd
    obtain ⟨j, hj1, hj2, hj3⟩ := hG d (by omega)
    exact ⟨j, hj1, by omega, by omega⟩
  · rw [critLamProfile_iff_of_isLip (armT_isLip hlip i), hk]
    intro d hd
    obtain ⟨j, hj1, hj2, hj3⟩ := hT d (by omega)
    exact ⟨j, hj1, by omega, by omega⟩

/-- **Span nine, the branch at `L + 5`, floor first.** -/
theorem s3_span_nine_mid_high_of_floor {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hH : H = L + 9) (hp : ρ i = L + 5)
    (hG : ∀ d : Fin (n - i.val), L + 8 ≤ armG ρ i d →
      ∃ j : Fin (n - i.val), j.val < d.val ∧ armG ρ i j ≤ L + 1)
    (hT : ∀ d : Fin (i.val + 1), L + 8 ≤ armT ρ i d →
      ∃ j : Fin (i.val + 1), j.val < d.val ∧ armT ρ i j ≤ L + 1) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by simp [armG]
  have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by simp [armT]
  refine exists_folds_of_veeProfile ρ i H L (L + 6) hlip (by omega)
    (by rw [hp]; rw [abs_le]; omega) hLb hHb ?_ ?_
  · refine critVeeProfile_of_floor_before' hmG (armG_isLip hlip i) (crookDown_armG hcr i)
      (L + 6) L rfl (by rw [hG0, hp]; omega) ?_
    intro d hd
    exact hG d (by omega)
  · refine critVeeProfile_of_floor_before' hmT (armT_isLip hlip i) (crookDown_armT hcr i)
      (L + 6) L rfl (by rw [hT0, hp]; omega) ?_
    intro d hd
    exact hT d (by omega)

/-- **Span nine, the branch at `L + 5`, ceiling first.** -/
theorem s3_span_nine_mid_high_of_top {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hH : H = L + 9) (hp : ρ i = L + 5)
    (hG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 2 →
      ∃ j : Fin (n - i.val), j.val < d.val ∧ L + 8 ≤ armG ρ i j)
    (hT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 2 →
      ∃ j : Fin (i.val + 1), j.val < d.val ∧ L + 8 ≤ armT ρ i j) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by simp [armG]
  have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by simp [armT]
  refine exists_folds_of_profile ρ i H L (L + 4) hlip (by omega)
    (by rw [hp]; rw [abs_le]; omega) hLb hHb ?_ ?_
  · refine critLamProfile_of_top_before' hmG (armG_isLip hlip i) (crookUp_armG hcr i) (L + 4) H
      (by omega) (by rw [hG0, hp]; omega) ?_
    intro d hd
    obtain ⟨j, hj1, hj2⟩ := hG d (by omega)
    exact ⟨j, hj1, by omega⟩
  · refine critLamProfile_of_top_before' hmT (armT_isLip hlip i) (crookUp_armT hcr i) (L + 4) H
      (by omega) (by rw [hT0, hp]; omega) ?_
    intro d hd
    obtain ⟨j, hj1, hj2⟩ := hT d (by omega)
    exact ⟨j, hj1, by omega⟩

end HPC.Fold
