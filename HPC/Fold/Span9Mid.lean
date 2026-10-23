import HPC.Fold.Span9

/-!
# Span nine at the basepoint `L + 4`: the `LowAt (L + 1) (L + 8)` half

`HPC/Fold/Span9.lean` settles span nine at the basepoints `L + 3` and `L + 6`, and leaves the two
middle heights `L + 4` and `L + 5` open.  This file settles one half of the height `L + 4`: the
basepoint is served unless both arms are `HighAt (L + 1) (L + 8)`.

The leaf at that height is: both arms `HighAt (L + 1) (L + 9)` and both arms `LowAt L (L + 7)`.
One application of `dichotomy_at` at the level pair `(L + 1, L + 8)` splits it in two; on the
`LowAt` side a second application at `(L, L + 9)` splits it again, and the two resulting branches
are served:

* `LowAt (L + 1) (L + 8)` and `LowAt L (L + 9)`: the four-leg walk of `HPC/Fold/Leg4.lean` with
  peak `K = L + 7` and valley `M = L + 2`, that is
  `L+3, …, L+7, …, L+2, …, L+8, …, L+1`.  Its floor announcement is the branch
  `LowAt (L + 1) (L + 8)`, its deep-floor announcement the branch `LowAt L (L + 9)`, and its
  ceiling announcement the leaf `HighAt (L + 1) (L + 9)` followed by one application of
  `CrookUp.levels` at the levels `(L + 2, L + 9)`.
* `LowAt (L + 1) (L + 8)` and `HighAt L (L + 9)`: the three-leg walk of `HPC/Fold/Leg3Mid.lean`
  with peak `K = L + 7`, that is `L+3, …, L+7, …, L+1, …, L+8`.  Its floor announcement is again
  the branch `LowAt (L + 1) (L + 8)`, and its ceiling announcement is the branch
  `HighAt L (L + 9)` read verbatim.

What is left open at this height is therefore the basepoint `L + 4` with both arms
`HighAt (L + 1) (L + 8)`; `HPC/Fold/Span9Mid5.lean` does the mirror job at `L + 5` and assembles
everything proved about span nine.
-/

namespace HPC.Fold

/-! ## The two branches -/

/-- **The `L + 4` leaf at span nine, `LowAt (L + 1) (L + 8)` and `LowAt L (L + 9)` branch.**
Four legs, with peak `K = L + 7` and valley `M = L + 2`. -/
theorem foldsOnto_span9_mid_low_low {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (hcu : CrookUp f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hhigh : HighAt f (L + 1) (L + 9))
    (hlow8 : LowAt f (L + 1) (L + 8)) (hlow9 : LowAt f L (L + 9)) :
    FoldsOnto f (leg4Len L (L + 9) (L + 7) (L + 2) (L + 4))
      (leg4Walk L (L + 9) (L + 7) (L + 2) (L + 4)) := by
  refine foldsOnto_leg4 hm f hf L (L + 9) (L + 7) (L + 2) (L + 4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h0 hL hH ?_ ?_ ?_
  -- floor: from `LowAt f (L + 1) (L + 8)`
  · intro d hd
    rcases hlow8 d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr ⟨j, j', hjj', hj', by omega, by omega⟩
  -- deep floor: from `LowAt f L (L + 9)`
  · intro d hd
    rcases hlow9 d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by omega, by omega⟩)
  -- ceiling: the leaf condition and one crookedness clause
  · intro d hd
    obtain ⟨j, hj, hjf⟩ := hhigh d (by omega)
    obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
      hcu.levels (L + 2) (L + 9) (by omega) j d hj (by omega) (by omega)
    exact Or.inr (Or.inr ⟨j, u, u', h1, h2, h3, by omega, by omega, by omega⟩)

/-- **The `L + 4` leaf at span nine, `LowAt (L + 1) (L + 8)` and `HighAt L (L + 9)` branch.**
Three legs, with peak `K = L + 7`; no crookedness clause is needed. -/
theorem foldsOnto_span9_mid_low_high {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow8 : LowAt f (L + 1) (L + 8)) (hhigh9 : HighAt f L (L + 9)) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk L (L + 9) (L + 7) (L + 4)) := by
  refine foldsOnto_leg3M hm f hf L (L + 9) (L + 7) (L + 4) (by omega) (by omega) (by omega)
    (by omega) h0 hL hH ?_ ?_
  -- floor: from `LowAt f (L + 1) (L + 8)`
  · intro d hd
    rcases hlow8 d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr ⟨j, j', hjj', hj', by omega, by omega⟩
  -- ceiling: from `HighAt f L (L + 9)`
  · intro d hd
    obtain ⟨j, hj, hjf⟩ := hhigh9 d (by omega)
    exact Or.inl ⟨j, hj, by omega⟩

/-! ## The basepoint `L + 4`, off the `HighAt (L + 1) (L + 8)` branch -/

/-- **`S3` at span nine, at the basepoint `L + 4`, unless both arms are `HighAt (L + 1) (L + 8)`.**
This is one half of the first of the two heights left open by `s3_span_nine_off_center`. -/
theorem s3_span_nine_mid_low {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hp : ρ i = L + 4)
    (hnh : ¬ (HighAt (armG ρ i) (L + 1) (L + 8) ∧ HighAt (armT ρ i) (L + 1) (L + 8))) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hh : HighAt (armG ρ i) (ρ i - 3) (L + 9) ∧ HighAt (armT ρ i) (ρ i - 3) (L + 9)
  · by_cases hl : LowAt (armG ρ i) L (ρ i + 3) ∧ LowAt (armT ρ i) L (ρ i + 3)
    · obtain ⟨hhG, hhT⟩ := hh
      have e1 : ρ i - 3 = L + 1 := by omega
      rw [e1] at hhG hhT
      have hi := i.isLt
      have hmG : 0 < n - i.val := by omega
      have hmT : 0 < i.val + 1 := by omega
      have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
        show ρ ⟨i.val + 0, _⟩ = L + 4
        rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp), hp]
      have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
        show ρ ⟨i.val - 0, _⟩ = L + 4
        rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp), hp]
      have hGL : ∀ j, L ≤ armG ρ i j := fun j => hLb _
      have hGH : ∀ j, armG ρ i j ≤ L + 9 := fun j => hHb _
      have hTL : ∀ j, L ≤ armT ρ i j := fun j => hLb _
      have hTH : ∀ j, armT ρ i j ≤ L + 9 := fun j => hHb _
      rcases dichotomy_at hcr i (L + 1) (L + 8) (by omega) with ⟨hg8, ht8⟩ | ⟨hg8, ht8⟩
      · rcases dichotomy_at hcr i L (L + 9) (by omega) with ⟨hg9, ht9⟩ | ⟨hg9, ht9⟩
        · exact ⟨_, _,
            foldsOnto_span9_mid_low_low hmG _ (armG_isLip hlip i) (crookUp_armG hcr i) L
              hG0 hGL hGH hhG hg8 hg9,
            foldsOnto_span9_mid_low_low hmT _ (armT_isLip hlip i) (crookUp_armT hcr i) L
              hT0 hTL hTH hhT ht8 ht9⟩
        · exact ⟨_, _,
            foldsOnto_span9_mid_low_high hmG _ (armG_isLip hlip i) L hG0 hGL hGH hg8 hg9,
            foldsOnto_span9_mid_low_high hmT _ (armT_isLip hlip i) L hT0 hTL hTH ht8 ht9⟩
      · exact absurd ⟨hg8, ht8⟩ hnh
    · exact s3_of_not_lowAt ρ σ i (L + 9) L hlip hcr hLb hHb (by omega) hl
  · exact s3_of_not_highAt ρ σ i (L + 9) L hlip hcr hLb hHb (by omega) hh

end HPC.Fold
