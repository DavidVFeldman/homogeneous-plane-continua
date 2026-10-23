import HPC.Fold.Span9Mid

/-!
# Span nine at the basepoint `L + 5`: the `HighAt (L + 1) (L + 8)` half, and the assembly

`HPC/Fold/Span9Mid.lean` settles the basepoint `L + 4` at span nine unless both arms are
`HighAt (L + 1) (L + 8)`.  This file does the mirror job at the basepoint `L + 5`: it is settled
unless both arms are `LowAt (L + 1) (L + 8)`.

The leaf at that height is: both arms `HighAt (L + 2) (L + 9)` and both arms `LowAt L (L + 8)`.
One application of `dichotomy_at` at `(L + 1, L + 8)` splits it in two; on the `HighAt` side a
second application at `(L, L + 9)` splits it again, and the two branches are served by the
reflected walks — the arm is read upside down, `g = L + H - f`, so that the engines see the
basepoint `L + 4`:

* `HighAt (L + 1) (L + 8)` and `LowAt L (L + 9)`: three legs, peak `K = L + 7` for the reflected
  arm, the walk `L+6, …, L+2, …, L+8, …, L+1`.  Both announcements are the branch conditions read
  through the reflection, and no crookedness clause is needed.
* `HighAt (L + 1) (L + 8)` and `HighAt L (L + 9)`: four legs, peak `K = L + 7` and valley
  `M = L + 2` for the reflected arm.  The floor announcement is the branch
  `HighAt (L + 1) (L + 8)`, the ceiling announcement the leaf `LowAt L (L + 8)`, and the
  deep-floor announcement is the engine's three-time clause, supplied by the branch
  `HighAt L (L + 9)` together with one application of `CrookUp.levels` at the levels
  `(L + 1, L + 9)`.

`s3_span_nine_except` then assembles everything proved about span nine: the only basepoints left
open are one at `L + 4` whose two arms are both `HighAt (L + 1) (L + 8)`, and one at `L + 5` whose
two arms are both `LowAt (L + 1) (L + 8)`.
-/

namespace HPC.Fold

/-! ## The two branches at height `L + 5` -/

/-- **The `L + 5` leaf at span nine, `HighAt (L + 1) (L + 8)` and `LowAt L (L + 9)` branch.**
Three legs for the reflected arm, with peak `K = L + 7`. -/
theorem foldsOnto_span9_mid5_high_low {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hhigh8 : HighAt f (L + 1) (L + 8)) (hlow9 : LowAt f L (L + 9)) :
    FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4)) (leg3Walk' L (L + 9) (L + 7) (L + 5)) := by
  set g : Fin m → ℤ := fun j => L + (L + 9) - f j with hgdef
  have hglip : IsLip g := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [hgdef]
    rw [abs_le] at this ⊢
    omega
  have hg0 : g ⟨0, hm⟩ = L + 4 := by simp only [hgdef, h0]; ring
  have hgL : ∀ j, L ≤ g j := fun j => by have := hH j; simp only [hgdef]; omega
  have hgH : ∀ j, g j ≤ L + 9 := fun j => by have := hL j; simp only [hgdef]; omega
  -- floor: from `HighAt f (L + 1) (L + 8)`
  have hgfloor : ∀ d : Fin m, g d ≤ L + 4 - 3 →
      (∃ k : Fin m, k.val < d.val ∧ L + 7 ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧
        g k ≤ L + 4 - 2 ∧ L + 7 - 1 ≤ g k') := by
    intro d hd
    have hfd : L + 8 ≤ f d := by simp only [hgdef] at hd; omega
    obtain ⟨j, hj, hjf⟩ := hhigh8 d hfd
    exact Or.inl ⟨j, hj, by simp only [hgdef]; omega⟩
  -- ceiling: from `LowAt f L (L + 9)`
  have hgceil : ∀ d : Fin m, L + 7 + 2 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + 4 - 3) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 7 + 1 ≤ g k ∧ g k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        g k ≤ L + 4 - 2 ∧ L + 7 ≤ g k' ∧ g k'' ≤ L + 2) := by
    intro d hd
    have hfd : f d ≤ L := by simp only [hgdef] at hd; omega
    rcases hlow9 d hfd with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by simp only [hgdef]; omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by simp only [hgdef]; omega,
        by simp only [hgdef]; omega⟩)
  obtain ⟨β, h1, h2, h3, h4⟩ :=
    foldsOnto_leg3M hm g hglip L (L + 9) (L + 7) (L + 4) (by omega) (by omega) (by omega)
      (by omega) hg0 hgL hgH hgfloor hgceil
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have := h4 j
  simp only [hgdef] at this
  have e : L + (L + 9) - (L + 5) = L + 4 := by ring
  simp only [leg3Walk', e]
  rw [abs_le] at this ⊢
  omega

/-- **The `L + 5` leaf at span nine, `HighAt (L + 1) (L + 8)` and `HighAt L (L + 9)` branch.**
Four legs for the reflected arm, with peak `K = L + 7` and valley `M = L + 2`; the deep-floor
announcement is the engine's three-time clause. -/
theorem foldsOnto_span9_mid5_high_high {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (hcu : CrookUp f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow8 : LowAt f L (L + 8))
    (hhigh8 : HighAt f (L + 1) (L + 8)) (hhigh9 : HighAt f L (L + 9)) :
    FoldsOnto f (leg4Len L (L + 9) (L + 7) (L + 2) (L + 4))
      (leg4Walk' L (L + 9) (L + 7) (L + 2) (L + 4)) := by
  set g : Fin m → ℤ := fun j => L + (L + 9) - f j with hgdef
  have hglip : IsLip g := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [hgdef]
    rw [abs_le] at this ⊢
    omega
  have hg0 : g ⟨0, hm⟩ = L + 4 := by simp only [hgdef, h0]; ring
  have hgL : ∀ j, L ≤ g j := fun j => by have := hH j; simp only [hgdef]; omega
  have hgH : ∀ j, g j ≤ L + 9 := fun j => by have := hL j; simp only [hgdef]; omega
  -- floor: from `HighAt f (L + 1) (L + 8)`
  have hgfloor : ∀ d : Fin m, g d ≤ L + 2 - 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 7 ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧
        g k ≤ L + 4 - 2 ∧ L + 7 - 1 ≤ g k') := by
    intro d hd
    have hfd : L + 8 ≤ f d := by simp only [hgdef] at hd; omega
    obtain ⟨j, hj, hjf⟩ := hhigh8 d hfd
    exact Or.inl ⟨j, hj, by simp only [hgdef]; omega⟩
  -- deep floor: from `HighAt f L (L + 9)` and one crookedness clause
  have hgdeep : ∀ d : Fin m, g d ≤ L + 2 - 2 →
      (∃ k : Fin m, k.val < d.val ∧ L + 7 + 2 ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧
        g k ≤ L + 2 - 1 ∧ L + 9 - 2 ≤ g k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        L + 7 + 1 ≤ g k ∧ g k' ≤ L + 2 ∧ L + 9 - 2 ≤ g k'') := by
    intro d hd
    have hfd : L + 9 ≤ f d := by simp only [hgdef] at hd; omega
    obtain ⟨j, hj, hjf⟩ := hhigh9 d hfd
    obtain ⟨u, u', p1, p2, p3, p4, p5⟩ :=
      hcu.levels (L + 1) (L + 9) (by omega) j d hj (by omega) (by omega)
    exact Or.inr (Or.inr ⟨j, u, u', p1, p2, p3, by simp only [hgdef]; omega,
      by simp only [hgdef]; omega, by simp only [hgdef]; omega⟩)
  -- ceiling: from the leaf `LowAt f L (L + 8)`
  have hgceil : ∀ d : Fin m, L + 7 + 2 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + 2 - 1) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧
        L + 7 + 1 ≤ g k ∧ g k' ≤ L + 2 + 1) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        g k ≤ L + 4 - 2 ∧ L + 7 ≤ g k' ∧ g k'' ≤ L + 2 + 1) := by
    intro d hd
    have hfd : f d ≤ L := by simp only [hgdef] at hd; omega
    rcases hlow8 d hfd with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by simp only [hgdef]; omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by simp only [hgdef]; omega,
        by simp only [hgdef]; omega⟩)
  obtain ⟨β, h1, h2, h3, h4⟩ :=
    foldsOnto_leg4 hm g hglip L (L + 9) (L + 7) (L + 2) (L + 4) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hg0 hgL hgH
      hgfloor hgdeep hgceil
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have := h4 j
  simp only [hgdef] at this
  simp only [leg4Walk']
  rw [abs_le] at this ⊢
  omega

/-! ## The basepoint `L + 5`, off the `LowAt (L + 1) (L + 8)` branch -/

/-- **`S3` at span nine, at the basepoint `L + 5`, unless both arms are `LowAt (L + 1) (L + 8)`.**
The mirror of `s3_span_nine_mid_low`. -/
theorem s3_span_nine_mid_high {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hp : ρ i = L + 5)
    (hnl : ¬ (LowAt (armG ρ i) (L + 1) (L + 8) ∧ LowAt (armT ρ i) (L + 1) (L + 8))) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hh : HighAt (armG ρ i) (ρ i - 3) (L + 9) ∧ HighAt (armT ρ i) (ρ i - 3) (L + 9)
  · by_cases hl : LowAt (armG ρ i) L (ρ i + 3) ∧ LowAt (armT ρ i) L (ρ i + 3)
    · obtain ⟨hlG, hlT⟩ := hl
      have e2 : ρ i + 3 = L + 8 := by omega
      rw [e2] at hlG hlT
      have hi := i.isLt
      have hmG : 0 < n - i.val := by omega
      have hmT : 0 < i.val + 1 := by omega
      have hG0 : armG ρ i ⟨0, hmG⟩ = L + 5 := by
        show ρ ⟨i.val + 0, _⟩ = L + 5
        rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp), hp]
      have hT0 : armT ρ i ⟨0, hmT⟩ = L + 5 := by
        show ρ ⟨i.val - 0, _⟩ = L + 5
        rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp), hp]
      have hGL : ∀ j, L ≤ armG ρ i j := fun j => hLb _
      have hGH : ∀ j, armG ρ i j ≤ L + 9 := fun j => hHb _
      have hTL : ∀ j, L ≤ armT ρ i j := fun j => hLb _
      have hTH : ∀ j, armT ρ i j ≤ L + 9 := fun j => hHb _
      rcases dichotomy_at hcr i (L + 1) (L + 8) (by omega) with ⟨hg8, ht8⟩ | ⟨hg8, ht8⟩
      · exact absurd ⟨hg8, ht8⟩ hnl
      · rcases dichotomy_at hcr i L (L + 9) (by omega) with ⟨hg9, ht9⟩ | ⟨hg9, ht9⟩
        · exact ⟨_, _,
            foldsOnto_span9_mid5_high_low hmG _ (armG_isLip hlip i) L hG0 hGL hGH hg8 hg9,
            foldsOnto_span9_mid5_high_low hmT _ (armT_isLip hlip i) L hT0 hTL hTH ht8 ht9⟩
        · exact ⟨_, _,
            foldsOnto_span9_mid5_high_high hmG _ (armG_isLip hlip i) (crookUp_armG hcr i) L
              hG0 hGL hGH hlG hg8 hg9,
            foldsOnto_span9_mid5_high_high hmT _ (armT_isLip hlip i) (crookUp_armT hcr i) L
              hT0 hTL hTH hlT ht8 ht9⟩
    · exact s3_of_not_lowAt ρ σ i (L + 9) L hlip hcr hLb hHb (by omega) hl
  · exact s3_of_not_highAt ρ σ i (L + 9) L hlip hcr hLb hHb (by omega) hh

/-! ## Everything proved about span nine -/

/-- **`S3` at span nine, as far as it is proved.**  Every basepoint of a faithful crooked sequence
of span at most nine is served, except possibly one standing exactly four levels above the floor
whose two arms are both `HighAt (L + 1) (L + 8)`, or one standing exactly five levels above the
floor whose two arms are both `LowAt (L + 1) (L + 8)`. -/
theorem s3_span_nine_except {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 9)
    (hoff : H ≤ L + 8 ∨
      ((ρ i = L + 4 →
        ¬ (HighAt (armG ρ i) (L + 1) (L + 8) ∧ HighAt (armT ρ i) (L + 1) (L + 8))) ∧
       (ρ i = L + 5 →
        ¬ (LowAt (armG ρ i) (L + 1) (L + 8) ∧ LowAt (armT ρ i) (L + 1) (L + 8))))) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases h8 : H ≤ L + 8
  · exact s3_span_eight ρ σ i H L hlip hcr hLb hHb hLH h8
  · have hH9 : H = L + 9 := by omega
    subst hH9
    rcases hoff with h | ⟨h4, h5⟩
    · omega
    · by_cases hp4 : ρ i = L + 4
      · exact s3_span_nine_mid_low ρ σ i L hlip hcr hLb hHb hp4 (h4 hp4)
      · by_cases hp5 : ρ i = L + 5
        · exact s3_span_nine_mid_high ρ σ i L hlip hcr hLb hHb hp5 (h5 hp5)
        · exact s3_span_nine_off_center ρ σ i (L + 9) L hlip hcr hLb hHb hLH hspan
            (Or.inr ⟨hp4, hp5⟩)

end HPC.Fold
