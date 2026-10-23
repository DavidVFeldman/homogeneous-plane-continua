import HPC.Fold.Span8Full

/-!
# Span nine, at the two outer interior basepoints

`HPC/Fold/Span8Full.lean` settles span eight at every basepoint.  At span nine the interior
basepoints stand at `L + 3`, `L + 4`, `L + 5` and `L + 6` (`s3_near_extreme` serves the rest),
and `s3_span_seven_of_cases` leaves a basepoint open only when both arms are `HighAt (ρ i - 3) H`
and both arms are `LowAt L (ρ i + 3)`.  This file settles the two outer ones, `L + 3` and `L + 6`,
with the three-leg fold of `HPC/Fold/Leg3.lean` and its reflection `foldsOnto_leg3'`.

At each of the two heights two applications of `dichotomy_at` split the leaf into three branches,
and each branch names a peak `K` for which the two announcements of the engine are available.
Levels are written as offsets from `L`, and `H = L + 9`.

* `ρ i = L + 3`, split first at `(L, L + 7)`, and on its `LowAt` side again at `(L, L + 8)`.
  * `HighAt L (L + 7)`: peak `K = L + 5`, the walk `L+2, …, L+5, …, L+1, …, L+8`.
  * `LowAt L (L + 7)` and `LowAt L (L + 8)`: peak `K = L + 7`.
  * `LowAt L (L + 7)` and `HighAt L (L + 8)`: peak `K = L + 6`.
  In each branch the floor announcement is a `LowAt` condition read verbatim, and the ceiling
  announcement is a `HighAt` condition followed by one instance of the crookedness clause
  `CrookUp` (`HPC/Fold/Crook.lean`).

* `ρ i = L + 6`, split first at `(L + 1, L + 9)`, and on its `LowAt` side again at
  `(L + 2, L + 9)`.  Here the arm is reflected, `g = L + H - f`, so that the engine sees the
  basepoint `L + 3` again, and the fold is onto the reflected walk `leg3Walk'`.
  * `HighAt (L + 1) (L + 9)`: peak `K = L + 7`.
  * `LowAt (L + 1) (L + 9)` and `LowAt (L + 2) (L + 9)`: peak `K = L + 5`.
  * `LowAt (L + 1) (L + 9)` and `HighAt (L + 2) (L + 9)`: peak `K = L + 6`.
  No crookedness clause is needed at this height: the two announcements are exactly the leaf
  conditions and the branch conditions, read through the reflection.

What comes out is `s3_span_nine_off_center`: at span nine every basepoint except those standing
exactly four or exactly five levels above the floor is served, and its chain-level reading
`theorem3_span_nine_off_center`.  The two middle basepoints at span exactly nine remain open.
-/

namespace HPC.Fold

/-! ## The leaf at height `L + 3` -/

/-- **The `L + 3` leaf at span nine, `HighAt L (L + 7)` branch.**  Peak `K = L + 5`.  The floor
announcement is the leaf `LowAt L (L + 6)`; the ceiling announcement is the branch
`HighAt L (L + 7)` followed by one instance of the crookedness clause. -/
theorem foldsOnto_span9_low_high {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 3) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f L (L + 6)) (hhigh : HighAt f L (L + 7)) (hcu : CrookUp f) :
    FoldsOnto f (leg3Len L (L + 9) (L + 5) (L + 3)) (leg3Walk L (L + 9) (L + 5) (L + 3)) := by
  refine foldsOnto_leg3 hm f hf L (L + 9) (L + 5) (L + 3) (by omega) (by omega) (by omega)
    (by omega) h0 hL hH ?_ ?_
  · intro d hd
    rcases hlow d hd with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr ⟨j, j', hjj', hj', hjf, by omega⟩
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
      hcu.levels (L + 1) (L + 7) (by omega) k d hk (by omega) (by omega)
    exact Or.inr (Or.inr ⟨k, u, u', h1, h2, h3, hkf, by omega, by omega⟩)

/-- **The `L + 3` leaf at span nine, `LowAt L (L + 7)` and `LowAt L (L + 8)` branch.**  Peak
`K = L + 7`.  The floor announcement is the branch `LowAt L (L + 8)`; the ceiling announcement is
the leaf `HighAt L (L + 9)` followed by one instance of the crookedness clause. -/
theorem foldsOnto_span9_low_low {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 3) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f L (L + 8)) (hhigh : HighAt f L (L + 9)) (hcu : CrookUp f) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 3)) (leg3Walk L (L + 9) (L + 7) (L + 3)) := by
  refine foldsOnto_leg3 hm f hf L (L + 9) (L + 7) (L + 3) (by omega) (by omega) (by omega)
    (by omega) h0 hL hH ?_ ?_
  · intro d hd
    rcases hlow d hd with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr ⟨j, j', hjj', hj', hjf, by omega⟩
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
      hcu.levels (L + 1) (L + 9) (by omega) k d hk (by omega) (by omega)
    exact Or.inr (Or.inr ⟨k, u, u', h1, h2, h3, hkf, by omega, by omega⟩)

/-- **The `L + 3` leaf at span nine, `LowAt L (L + 7)` and `HighAt L (L + 8)` branch.**  Peak
`K = L + 6`.  The floor announcement is the branch `LowAt L (L + 7)`; the ceiling announcement is
the branch `HighAt L (L + 8)` followed by one instance of the crookedness clause. -/
theorem foldsOnto_span9_low_mid {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 3) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f L (L + 7)) (hhigh : HighAt f L (L + 8)) (hcu : CrookUp f) :
    FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 3)) (leg3Walk L (L + 9) (L + 6) (L + 3)) := by
  refine foldsOnto_leg3 hm f hf L (L + 9) (L + 6) (L + 3) (by omega) (by omega) (by omega)
    (by omega) h0 hL hH ?_ ?_
  · intro d hd
    rcases hlow d hd with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr ⟨j, j', hjj', hj', hjf, by omega⟩
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
      hcu.levels (L + 1) (L + 8) (by omega) k d hk (by omega) (by omega)
    exact Or.inr (Or.inr ⟨k, u, u', h1, h2, h3, hkf, by omega, by omega⟩)

/-! ## The leaf at height `L + 6` -/

/-- **The `L + 6` leaf at span nine, `HighAt (L + 1) (L + 9)` branch.**  Peak `K = L + 7` for the
reflected arm.  The ceiling of the arm is the branch `HighAt (L + 1) (L + 9)` and its floor the
leaf `LowAt L (L + 9)`, both read verbatim. -/
theorem foldsOnto_span9_high_high {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 6) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f L (L + 9)) (hhigh : HighAt f (L + 1) (L + 9)) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 3)) (leg3Walk' L (L + 9) (L + 7) (L + 6)) := by
  have e : L + (L + 9) - (L + 6) = L + 3 := by ring
  have hfold := foldsOnto_leg3' hm f hf L (L + 9) (L + 7) (L + 6) (by omega) (by omega)
    (by omega) (by omega) h0 hL hH ?_ ?_
  · rw [e] at hfold; exact hfold
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    exact Or.inl ⟨k, hk, by omega⟩
  · intro d hd
    rcases hlow d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by omega, by omega⟩)

/-- **The `L + 6` leaf at span nine, `LowAt (L + 1) (L + 9)` and `LowAt (L + 2) (L + 9)`
branch.**  Peak `K = L + 5` for the reflected arm; the ceiling of the arm is the leaf
`HighAt (L + 3) (L + 9)` and its floor the branch `LowAt (L + 2) (L + 9)`. -/
theorem foldsOnto_span9_high_low {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 6) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f (L + 2) (L + 9)) (hhigh : HighAt f (L + 3) (L + 9)) :
    FoldsOnto f (leg3Len L (L + 9) (L + 5) (L + 3)) (leg3Walk' L (L + 9) (L + 5) (L + 6)) := by
  have e : L + (L + 9) - (L + 6) = L + 3 := by ring
  have hfold := foldsOnto_leg3' hm f hf L (L + 9) (L + 5) (L + 6) (by omega) (by omega)
    (by omega) (by omega) h0 hL hH ?_ ?_
  · rw [e] at hfold; exact hfold
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    exact Or.inl ⟨k, hk, by omega⟩
  · intro d hd
    rcases hlow d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by omega, by omega⟩)

/-- **The `L + 6` leaf at span nine, `LowAt (L + 1) (L + 9)` and `HighAt (L + 2) (L + 9)`
branch.**  Peak `K = L + 6` for the reflected arm; the ceiling of the arm is the branch
`HighAt (L + 2) (L + 9)` and its floor the branch `LowAt (L + 1) (L + 9)`. -/
theorem foldsOnto_span9_high_mid {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 6) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f (L + 1) (L + 9)) (hhigh : HighAt f (L + 2) (L + 9)) :
    FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 3)) (leg3Walk' L (L + 9) (L + 6) (L + 6)) := by
  have e : L + (L + 9) - (L + 6) = L + 3 := by ring
  have hfold := foldsOnto_leg3' hm f hf L (L + 9) (L + 6) (L + 6) (by omega) (by omega)
    (by omega) (by omega) h0 hL hH ?_ ?_
  · rw [e] at hfold; exact hfold
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    exact Or.inl ⟨k, hk, by omega⟩
  · intro d hd
    rcases hlow d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by omega, by omega⟩)

/-! ## Span nine away from the two middle levels -/

/-- **`S3` at span nine, off the two middle levels.**  Every basepoint of a faithful crooked
sequence of span at most nine is served, except possibly one standing exactly four or exactly
five levels above the floor when the span is exactly nine. -/
theorem s3_span_nine_off_center {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 9) (hoff : H ≤ L + 8 ∨ (ρ i ≠ L + 4 ∧ ρ i ≠ L + 5)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases h8 : H ≤ L + 8
  · exact s3_span_eight ρ σ i H L hlip hcr hLb hHb hLH h8
  · have hH9 : H = L + 9 := by omega
    have hmid : ρ i ≠ L + 4 ∧ ρ i ≠ L + 5 := by
      rcases hoff with h | h
      · omega
      · exact h
    by_cases hnear : ρ i ≤ L + 2 ∨ H - 2 ≤ ρ i
    · exact s3_near_extreme ρ i H L hlip hLb hHb hLH hnear
    · push_neg at hnear
      obtain ⟨hlow, hhigh⟩ := hnear
      by_cases hh : HighAt (armG ρ i) (ρ i - 3) H ∧ HighAt (armT ρ i) (ρ i - 3) H
      · by_cases hl : LowAt (armG ρ i) L (ρ i + 3) ∧ LowAt (armT ρ i) L (ρ i + 3)
        · -- the leaf: both arms `HighAt (ρ i - 3) H` and both arms `LowAt L (ρ i + 3)`
          obtain ⟨hhG, hhT⟩ := hh
          obtain ⟨hlG, hlT⟩ := hl
          have hi := i.isLt
          have hmG : 0 < n - i.val := by omega
          have hmT : 0 < i.val + 1 := by omega
          have hG0 : armG ρ i ⟨0, hmG⟩ = ρ i := by
            show ρ ⟨i.val + 0, _⟩ = ρ i
            rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
          have hT0 : armT ρ i ⟨0, hmT⟩ = ρ i := by
            show ρ ⟨i.val - 0, _⟩ = ρ i
            rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
          have hGL : ∀ j, L ≤ armG ρ i j := fun j => hLb _
          have hGH : ∀ j, armG ρ i j ≤ L + 9 := by
            intro j
            have hj := j.isLt
            have h := hHb (⟨i.val + j.val, by omega⟩ : Fin n)
            have e : armG ρ i j = ρ (⟨i.val + j.val, by omega⟩ : Fin n) := rfl
            omega
          have hTL : ∀ j, L ≤ armT ρ i j := fun j => hLb _
          have hTH : ∀ j, armT ρ i j ≤ L + 9 := by
            intro j
            have hj := j.isLt
            have h := hHb (⟨i.val - j.val, by omega⟩ : Fin n)
            have e : armT ρ i j = ρ (⟨i.val - j.val, by omega⟩ : Fin n) := rfl
            omega
          rcases (show ρ i = L + 3 ∨ ρ i = L + 6 by omega) with hp | hp
          · -- the basepoint stands at `L + 3`
            have e1 : ρ i - 3 = L := by omega
            have e2 : ρ i + 3 = L + 6 := by omega
            rw [e1, hH9] at hhG hhT
            rw [e2] at hlG hlT
            rcases dichotomy_at hcr i L (L + 7) (by omega) with ⟨hgb, htb⟩ | ⟨hgb, htb⟩
            · rcases dichotomy_at hcr i L (L + 8) (by omega) with ⟨hgb2, htb2⟩ | ⟨hgb2, htb2⟩
              · exact ⟨_, _,
                  foldsOnto_span9_low_low hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                    hgb2 hhG (crookUp_armG hcr i),
                  foldsOnto_span9_low_low hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                    htb2 hhT (crookUp_armT hcr i)⟩
              · exact ⟨_, _,
                  foldsOnto_span9_low_mid hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                    hgb hgb2 (crookUp_armG hcr i),
                  foldsOnto_span9_low_mid hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                    htb htb2 (crookUp_armT hcr i)⟩
            · exact ⟨_, _,
                foldsOnto_span9_low_high hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                  hlG hgb (crookUp_armG hcr i),
                foldsOnto_span9_low_high hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                  hlT htb (crookUp_armT hcr i)⟩
          · -- the basepoint stands at `L + 6`
            have e1 : ρ i - 3 = L + 3 := by omega
            have e2 : ρ i + 3 = L + 9 := by omega
            rw [e1, hH9] at hhG hhT
            rw [e2] at hlG hlT
            rcases dichotomy_at hcr i (L + 1) (L + 9) (by omega) with ⟨hgb, htb⟩ | ⟨hgb, htb⟩
            · rcases dichotomy_at hcr i (L + 2) (L + 9) (by omega) with ⟨hgb2, htb2⟩ | ⟨hgb2, htb2⟩
              · exact ⟨_, _,
                  foldsOnto_span9_high_low hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                    hgb2 hhG,
                  foldsOnto_span9_high_low hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                    htb2 hhT⟩
              · exact ⟨_, _,
                  foldsOnto_span9_high_mid hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                    hgb hgb2,
                  foldsOnto_span9_high_mid hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                    htb htb2⟩
            · exact ⟨_, _,
                foldsOnto_span9_high_high hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                  hlG hgb,
                foldsOnto_span9_high_high hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                  hlT htb⟩
        · exact s3_of_not_lowAt ρ σ i H L hlip hcr hLb hHb hLH hl
      · exact s3_of_not_highAt ρ σ i H L hlip hcr hLb hHb hLH hh

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, for a crooked chain whose
minimal-index range is at most nine, at a basepoint that is neither exactly four nor exactly five
above the range's floor. -/
theorem theorem3_span_nine_off_center {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n)
    (hspan : ∀ s t : Fin n, (hcr.1.minIdx t : ℤ) ≤ (hcr.1.minIdx s : ℤ) + 9)
    (hoff : ∀ s : Fin n, (hcr.1.minIdx i : ℤ) ≠ (hcr.1.minIdx s : ℤ) + 4 ∧
      (hcr.1.minIdx i : ℤ) ≠ (hcr.1.minIdx s : ℤ) + 5) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have href : E.Refines D := hcr.1
  set ρ : Fin n → ℤ := fun t => ((href.minIdx t : ℕ) : ℤ) with hρ
  set σ : Fin n → ℤ := fun t => ((href.maxIdx t : ℕ) : ℤ) with hσ
  obtain ⟨tL, -, htL⟩ := Finset.exists_min_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  obtain ⟨tH, -, htH⟩ := Finset.exists_max_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  set L : ℤ := ρ tL with hL
  set H : ℤ := ρ tH with hH
  have hLf : ∀ t, L ≤ ρ t := fun t => htL t (Finset.mem_univ t)
  have hHf : ∀ t, ρ t ≤ H := fun t => htH t (Finset.mem_univ t)
  by_cases hdeg : H ≤ L + 2
  · refine exists_blocks_first_of_range_le_two hn href i (href.minIdx tL).val (fun t => ?_)
    have h1 := hLf t
    have h2 := hHf t
    simp only [hρ, hL, hH] at h1 h2 hdeg
    omega
  · have hcase : L + 3 ≤ H := by omega
    have height : H ≤ L + 9 := hspan tL tH
    have hlip : IsLip ρ := by
      intro t t' htt'
      have := minIdx_lip href t t' htt'
      simp only [hρ]
      rw [abs_le]
      omega
    have hcrook : IsCrookedIvF ρ σ := isCrookedIvF_minIdx_maxIdx hcr
    obtain ⟨len, c, hG, hT⟩ :=
      s3_span_nine_off_center ρ σ i H L hlip hcrook hLf hHf hcase height (Or.inr (hoff tL))
    exact exists_blocks_first_of_folds href i _ _ hG hT

end HPC.Fold
