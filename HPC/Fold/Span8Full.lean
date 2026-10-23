import HPC.Fold.Span8Mid4

/-!
# Span eight, every basepoint

`HPC/Fold/Span8.lean` proves `S3` at span eight at every basepoint except one standing exactly
four levels above the floor of a band of width exactly eight; `HPC/Fold/Span8Mid.lean` and
`HPC/Fold/Span8Mid4.lean` serve the four branches of that remaining leaf.  This file puts the
pieces together: `s3_span_eight` drops the off-centre hypothesis of `s3_span_eight_off_center`,
and `theorem3_span_eight` is the chain-level reading.

At the middle basepoint `ρ i = L + 4` of a band `[L, L + 8]` the leaf is: both arms
`HighAt (L + 1) (L + 8)` and both arms `LowAt L (L + 7)`.  Two applications of `dichotomy_at`,
at the level pairs `(L, L + 8)` and `(L + 1, L + 7)`, split it into four branches, each of which
is served by one of

```
foldsOnto_span8_mid_low_low     foldsOnto_span8_mid_low_high
foldsOnto_span8_mid_high_low    foldsOnto_span8_mid_high_high
```

the first and the last onto four-leg walks, the two mixed ones onto three-leg walks.
-/

namespace HPC.Fold

/-- **`S3` at span eight, at the middle basepoint.**  The band is `[L, L + 8]` and the basepoint
stands at `L + 4`; the four branches of the leaf are served by the four middle-basepoint folds. -/
theorem s3_span_eight_middle {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 8)
    (hp : ρ i = L + 4) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hh : HighAt (armG ρ i) (ρ i - 3) (L + 8) ∧ HighAt (armT ρ i) (ρ i - 3) (L + 8)
  · by_cases hl : LowAt (armG ρ i) L (ρ i + 3) ∧ LowAt (armT ρ i) L (ρ i + 3)
    · obtain ⟨hhG, hhT⟩ := hh
      obtain ⟨hlG, hlT⟩ := hl
      have e1 : ρ i - 3 = L + 1 := by omega
      have e2 : ρ i + 3 = L + 7 := by omega
      rw [e1] at hhG hhT
      rw [e2] at hlG hlT
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
      have hGH : ∀ j, armG ρ i j ≤ L + 8 := fun j => hHb _
      have hTL : ∀ j, L ≤ armT ρ i j := fun j => hLb _
      have hTH : ∀ j, armT ρ i j ≤ L + 8 := fun j => hHb _
      rcases dichotomy_at hcr i L (L + 8) (by omega) with ⟨hg8, ht8⟩ | ⟨hg8, ht8⟩
      · rcases dichotomy_at hcr i (L + 1) (L + 7) (by omega) with ⟨hg7, ht7⟩ | ⟨hg7, ht7⟩
        · exact ⟨_, _,
            foldsOnto_span8_mid_low_low hmG _ (armG_isLip hlip i) (crookUp_armG hcr i) L
              hG0 hGL hGH hhG hg8 hg7,
            foldsOnto_span8_mid_low_low hmT _ (armT_isLip hlip i) (crookUp_armT hcr i) L
              hT0 hTL hTH hhT ht8 ht7⟩
        · exact ⟨_, _,
            foldsOnto_span8_mid_low_high hmG _ (armG_isLip hlip i) L hG0 hGL hGH hg8 hg7,
            foldsOnto_span8_mid_low_high hmT _ (armT_isLip hlip i) L hT0 hTL hTH ht8 ht7⟩
      · rcases dichotomy_at hcr i (L + 1) (L + 7) (by omega) with ⟨hg7, ht7⟩ | ⟨hg7, ht7⟩
        · exact ⟨_, _,
            foldsOnto_span8_mid_high_low hmG _ (armG_isLip hlip i) L hG0 hGL hGH hg7 hg8,
            foldsOnto_span8_mid_high_low hmT _ (armT_isLip hlip i) L hT0 hTL hTH ht7 ht8⟩
        · exact ⟨_, _,
            foldsOnto_span8_mid_high_high hmG _ (armG_isLip hlip i) (crookUp_armG hcr i) L
              hG0 hGL hGH hlG hg8 hg7,
            foldsOnto_span8_mid_high_high hmT _ (armT_isLip hlip i) (crookUp_armT hcr i) L
              hT0 hTL hTH hlT ht8 ht7⟩
    · exact s3_of_not_lowAt ρ σ i (L + 8) L hlip hcr hLb hHb (by omega) hl
  · exact s3_of_not_highAt ρ σ i (L + 8) L hlip hcr hLb hHb (by omega) hh

/-- **`S3` at span eight.**  Every basepoint of a faithful crooked sequence of span at most eight
is served: both arms fold onto one common walk. -/
theorem s3_span_eight {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 8) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hoff : H ≤ L + 7 ∨ ρ i ≠ L + 4
  · exact s3_span_eight_off_center ρ σ i H L hlip hcr hLb hHb hLH hspan hoff
  · push_neg at hoff
    obtain ⟨h8, hp⟩ := hoff
    have hH8 : H = L + 8 := by omega
    subst hH8
    exact s3_span_eight_middle ρ σ i L hlip hcr hLb hHb hp

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, for a crooked chain whose
minimal-index range is at most eight, at every basepoint. -/
theorem theorem3_span_eight {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n)
    (hspan : ∀ s t : Fin n, (hcr.1.minIdx t : ℤ) ≤ (hcr.1.minIdx s : ℤ) + 8) :
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
    have height : H ≤ L + 8 := hspan tL tH
    have hlip : IsLip ρ := by
      intro t t' htt'
      have := minIdx_lip href t t' htt'
      simp only [hρ]
      rw [abs_le]
      omega
    have hcrook : IsCrookedIvF ρ σ := isCrookedIvF_minIdx_maxIdx hcr
    obtain ⟨len, c, hG, hT⟩ := s3_span_eight ρ σ i H L hlip hcrook hLf hHf hcase height
    exact exists_blocks_first_of_folds href i _ _ hG hT

end HPC.Fold
