import HPC.Fold.Leg3

/-!
# Span eight, away from the middle level

At span eight the two halves of `HPC/Fold/Span7.lean` leave three basepoints open, at heights
`L + 3`, `L + 4` and `L + 5` (`s3_span_seven_of_cases`: a basepoint survives only if both arms
are `HighAt (ρ i - 3) H` and both arms are `LowAt L (ρ i + 3)`).  This file settles the two outer
ones, `L + 3` and `L + 5`, with the three-leg fold of `HPC/Fold/Leg3.lean`.

The pattern is the same at both heights: one further application of `dichotomy_at` splits the
leaf into two branches, and each branch names a peak `K` for which the two announcements of
`foldsOnto_leg3` are available.

* `ρ i = L + 3`, split at `(L, L + 7)`.
  * `HighAt L (L + 7)`: peak `K = L + 5`, the walk `L+2, …, L+5, …, L+1, …, L+7`.
  * `LowAt L (L + 7)`: peak `K = L + 6`, the walk `L+2, …, L+6, …, L+1, …, L+7`.
  In both branches the floor announcement is the leaf `LowAt`, and the ceiling announcement is
  the leaf or branch `HighAt` followed by one instance of the crookedness clause `CrookUp`
  (`HPC/Fold/Crook.lean`).

* `ρ i = L + 5`, split at `(L + 1, L + 8)`.  Here the arm is reflected, `g = L + H - f`, so that
  the engine sees the basepoint `L + 3` again, and the fold is onto the reflected walk
  `leg3Walk'`.
  * `LowAt (L + 1) (L + 8)`: peak `K = L + 5`.
  * `HighAt (L + 1) (L + 8)`: peak `K = L + 6`.
  No crookedness clause is needed at this height: the two announcements are exactly the leaf
  `HighAt` and the branch conditions, read through the reflection.  The ceiling announcement used
  is the two-time form of `foldsOnto_leg3` (a time at `K + 1` or above followed by one at
  `L + 2` or below).

What comes out is `s3_span_eight_off_center`: at span eight every basepoint except one exactly
four levels above the floor is served, and `theorem3_span_eight_off_center`, its reading for
crooked chains.  The middle basepoint `L + 4` at span exactly eight remains open.
-/

namespace HPC.Fold

/-! ## The reflected three-leg fold -/

/-- The reflection of the three-leg walk: from `p + 1` down to the valley `L + H - K`, up to
`H - 1`, and down to `L + 1`. -/
def leg3Walk' (L H K p : ℤ) (u : ℕ) : ℤ := L + H - leg3Walk L H K (L + H - p) u

/-- **The reflected three-leg fold.**  The mirror of `foldsOnto_leg3`: no crookedness hypothesis
lies beneath the engine, so reflecting the arm is legitimate. -/
theorem foldsOnto_leg3' {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L H K p : ℤ)
    (hLP : L + 2 ≤ L + H - p) (hPL : L + H - p ≤ L + 3) (hPK : L + H - p + 1 ≤ K)
    (hKH : K ≤ H - 1) (h0 : f ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hceilf : ∀ d : Fin m, H ≤ f d →
      (∃ k : Fin m, k.val < d.val ∧ f k ≤ L + H - K) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ H - 1 ≤ f k ∧ f k' ≤ L + H - K + 1))
    (hfloorf : ∀ d : Fin m, f d ≤ L + H - K - 2 →
      (∃ k : Fin m, k.val < d.val ∧ H ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + H - K - 1 ∧ H - 2 ≤ f k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        H - 1 ≤ f k ∧ f k' ≤ L + H - K ∧ H - 2 ≤ f k'')) :
    FoldsOnto f (leg3Len L H K (L + H - p)) (leg3Walk' L H K p) := by
  set g : Fin m → ℤ := fun j => L + H - f j with hg
  have hglip : IsLip g := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [hg]
    rw [abs_le] at this ⊢
    omega
  have hg0 : g ⟨0, hm⟩ = L + H - p := by simp only [hg, h0]
  have hgL : ∀ j, L ≤ g j := fun j => by have := hH j; simp only [hg]; omega
  have hgH : ∀ j, g j ≤ H := fun j => by have := hL j; simp only [hg]; omega
  have hgfloor : ∀ d : Fin m, g d ≤ L →
      (∃ k : Fin m, k.val < d.val ∧ K ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ g k ≤ L + 1 ∧ K - 1 ≤ g k') := by
    intro d hd
    have hfd : H ≤ f d := by simp only [hg] at hd; omega
    rcases hceilf d hfd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, hk, by simp only [hg]; omega⟩
    · exact Or.inr ⟨k, k', hkk', hk', by simp only [hg]; omega, by simp only [hg]; omega⟩
  have hgceil : ∀ d : Fin m, K + 2 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ K + 1 ≤ g k ∧ g k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        g k ≤ L + 1 ∧ K ≤ g k' ∧ g k'' ≤ L + 2) := by
    intro d hd
    have hfd : f d ≤ L + H - K - 2 := by simp only [hg] at hd; omega
    rcases hfloorf d hfd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by simp only [hg]; omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by simp only [hg]; omega, by simp only [hg]; omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by simp only [hg]; omega,
        by simp only [hg]; omega, by simp only [hg]; omega⟩)
  obtain ⟨β, h1, h2, h3, h4⟩ :=
    foldsOnto_leg3 hm g hglip L H K (L + H - p) hLP hPL hPK hKH hg0 hgL hgH hgfloor hgceil
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have := h4 j
  simp only [hg] at this
  simp only [leg3Walk']
  rw [abs_le] at this ⊢
  omega

/-! ## The leaf at height `L + 3` -/

/-- **The `L + 3` leaf, `HighAt` branch.**  Peak `K = L + 5`.  The floor announcement is the leaf
`LowAt L (L + 6)`; the ceiling announcement is the branch `HighAt L (L + 7)` followed by one
instance of the crookedness clause. -/
theorem foldsOnto_span8_low_high {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 3) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 8)
    (hlow : LowAt f L (L + 6)) (hhigh : HighAt f L (L + 7)) (hcu : CrookUp f) :
    FoldsOnto f (leg3Len L (L + 8) (L + 5) (L + 3)) (leg3Walk L (L + 8) (L + 5) (L + 3)) := by
  refine foldsOnto_leg3 hm f hf L (L + 8) (L + 5) (L + 3) (by omega) (by omega) (by omega)
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

/-- **The `L + 3` leaf, `LowAt` branch.**  Peak `K = L + 6`.  The floor announcement is the branch
`LowAt L (L + 7)`; the ceiling announcement is the leaf `HighAt L (L + 8)` followed by one
instance of the crookedness clause. -/
theorem foldsOnto_span8_low_low {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 3) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 8)
    (hlow : LowAt f L (L + 7)) (hhigh : HighAt f L (L + 8)) (hcu : CrookUp f) :
    FoldsOnto f (leg3Len L (L + 8) (L + 6) (L + 3)) (leg3Walk L (L + 8) (L + 6) (L + 3)) := by
  refine foldsOnto_leg3 hm f hf L (L + 8) (L + 6) (L + 3) (by omega) (by omega) (by omega)
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

/-! ## The leaf at height `L + 5` -/

/-- **The `L + 5` leaf, `LowAt` branch.**  Peak `K = L + 5` for the reflected arm.  Both
announcements are read off the conditions directly: the leaf `HighAt (L + 2) (L + 8)` is the
ceiling of the arm, and the branch `LowAt (L + 1) (L + 8)` its floor, in the two-time form. -/
theorem foldsOnto_span8_high_low {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 8)
    (hlow : LowAt f (L + 1) (L + 8)) (hhigh : HighAt f (L + 2) (L + 8)) :
    FoldsOnto f (leg3Len L (L + 8) (L + 5) (L + 3)) (leg3Walk' L (L + 8) (L + 5) (L + 5)) := by
  have e : L + (L + 8) - (L + 5) = L + 3 := by ring
  have hfold := foldsOnto_leg3' hm f hf L (L + 8) (L + 5) (L + 5) (by omega) (by omega)
    (by omega) (by omega) h0 hL hH ?_ ?_
  · rw [e] at hfold; exact hfold
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    exact Or.inl ⟨k, hk, by omega⟩
  · intro d hd
    rcases hlow d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by omega, by omega⟩)

/-- **The `L + 5` leaf, `HighAt` branch.**  Peak `K = L + 6` for the reflected arm; the branch
`HighAt (L + 1) (L + 8)` is the ceiling of the arm and the leaf `LowAt L (L + 8)` its floor. -/
theorem foldsOnto_span8_high_high {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 8)
    (hlow : LowAt f L (L + 8)) (hhigh : HighAt f (L + 1) (L + 8)) :
    FoldsOnto f (leg3Len L (L + 8) (L + 6) (L + 3)) (leg3Walk' L (L + 8) (L + 6) (L + 5)) := by
  have e : L + (L + 8) - (L + 5) = L + 3 := by ring
  have hfold := foldsOnto_leg3' hm f hf L (L + 8) (L + 6) (L + 5) (by omega) (by omega)
    (by omega) (by omega) h0 hL hH ?_ ?_
  · rw [e] at hfold; exact hfold
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    exact Or.inl ⟨k, hk, by omega⟩
  · intro d hd
    rcases hlow d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by omega, by omega⟩)

/-! ## Span eight away from the middle -/

/-- **`S3` at span eight, off the middle level.**  Every basepoint of a faithful crooked sequence
of span at most eight is served, except possibly one standing exactly four levels above the floor
when the span is exactly eight. -/
theorem s3_span_eight_off_center {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 8) (hoff : H ≤ L + 7 ∨ ρ i ≠ L + 4) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases h7 : H ≤ L + 7
  · exact s3_span_seven ρ σ i H L hlip hcr hLb hHb hLH h7
  · have hH8 : H = L + 8 := by omega
    have hmid : ρ i ≠ L + 4 := by
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
          have hGH : ∀ j, armG ρ i j ≤ L + 8 := by
            intro j
            have hj := j.isLt
            have h := hHb (⟨i.val + j.val, by omega⟩ : Fin n)
            have e : armG ρ i j = ρ (⟨i.val + j.val, by omega⟩ : Fin n) := rfl
            omega
          have hTL : ∀ j, L ≤ armT ρ i j := fun j => hLb _
          have hTH : ∀ j, armT ρ i j ≤ L + 8 := by
            intro j
            have hj := j.isLt
            have h := hHb (⟨i.val - j.val, by omega⟩ : Fin n)
            have e : armT ρ i j = ρ (⟨i.val - j.val, by omega⟩ : Fin n) := rfl
            omega
          rcases (show ρ i = L + 3 ∨ ρ i = L + 5 by omega) with hp | hp
          · -- the basepoint stands at `L + 3`
            have e1 : ρ i - 3 = L := by omega
            have e2 : ρ i + 3 = L + 6 := by omega
            rw [e1, hH8] at hhG hhT
            rw [e2] at hlG hlT
            rcases dichotomy_at hcr i L (L + 7) (by omega) with ⟨hgb, htb⟩ | ⟨hgb, htb⟩
            · exact ⟨_, _,
                foldsOnto_span8_low_low hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                  hgb hhG (crookUp_armG hcr i),
                foldsOnto_span8_low_low hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                  htb hhT (crookUp_armT hcr i)⟩
            · exact ⟨_, _,
                foldsOnto_span8_low_high hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                  hlG hgb (crookUp_armG hcr i),
                foldsOnto_span8_low_high hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                  hlT htb (crookUp_armT hcr i)⟩
          · -- the basepoint stands at `L + 5`
            have e1 : ρ i - 3 = L + 2 := by omega
            have e2 : ρ i + 3 = L + 8 := by omega
            rw [e1, hH8] at hhG hhT
            rw [e2] at hlG hlT
            rcases dichotomy_at hcr i (L + 1) (L + 8) (by omega) with ⟨hgb, htb⟩ | ⟨hgb, htb⟩
            · exact ⟨_, _,
                foldsOnto_span8_high_low hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                  hgb hhG,
                foldsOnto_span8_high_low hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                  htb hhT⟩
            · exact ⟨_, _,
                foldsOnto_span8_high_high hmG _ (armG_isLip hlip i) L (by rw [hG0, hp]) hGL hGH
                  hlG hgb,
                foldsOnto_span8_high_high hmT _ (armT_isLip hlip i) L (by rw [hT0, hp]) hTL hTH
                  hlT htb⟩
        · exact s3_of_not_lowAt ρ σ i H L hlip hcr hLb hHb hLH hl
      · exact s3_of_not_highAt ρ σ i H L hlip hcr hLb hHb hLH hh

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, for a crooked chain whose
minimal-index range is at most eight, at a basepoint that is not exactly four above the range's
floor. -/
theorem theorem3_span_eight_off_center {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n)
    (hspan : ∀ s t : Fin n, (hcr.1.minIdx t : ℤ) ≤ (hcr.1.minIdx s : ℤ) + 8)
    (hoff : ∀ s : Fin n, (hcr.1.minIdx i : ℤ) ≠ (hcr.1.minIdx s : ℤ) + 4) :
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
    have hmid : ρ i ≠ L + 4 := hoff tL
    obtain ⟨len, c, hG, hT⟩ :=
      s3_span_eight_off_center ρ σ i H L hlip hcrook hLf hHf hcase height (Or.inr hmid)
    exact exists_blocks_first_of_folds href i _ _ hG hT

end HPC.Fold
