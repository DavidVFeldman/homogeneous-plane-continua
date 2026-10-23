import HPC.Fold.Leg3Mid
import HPC.Fold.Span8

/-!
# Span eight at the middle basepoint: the two three-leg branches

`HPC/Fold/Span8.lean` settles span eight at every basepoint except one standing exactly four
levels above the floor.  At that middle basepoint the leaf is: both arms `HighAt (L + 1) H` and
both arms `LowAt L (L + 7)`, with `H = L + 8` and `ρ i = L + 4`.

Two applications of `dichotomy_at`, at the level pairs `(L, H)` and `(L + 1, H - 1)`, split the
leaf into four branches.  This file serves the two mixed branches with the middle-basepoint
three-leg engine of `HPC/Fold/Leg3Mid.lean`:

* `HighAt L H` and `LowAt (L + 1) (H - 1)`: the walk `leg3Walk L H (L + 6) (L + 4)`, i.e.
  `L+3, L+4, L+5, L+6, L+5, L+4, L+3, L+2, L+1, L+2, L+3, L+4, L+5, L+6, L+7`;
* `LowAt L H` and `HighAt (L + 1) (H - 1)`: its reflection, served through `foldsOnto_leg3M'`.

Neither branch needs a crookedness clause: the two announcements of the engine are read directly
off the branch conditions.  The two remaining branches — both arms `LowAt` at both level pairs,
and both arms `HighAt` at both level pairs — are not served by any three-leg walk and are left to
`HPC/Fold/Leg4.lean`.
-/

namespace HPC.Fold

/-! ## The reflected middle-basepoint fold -/

/-- **The reflected three-leg fold at a middle basepoint.**  The mirror of `foldsOnto_leg3M`;
as with `foldsOnto_leg3'`, no crookedness lies beneath the engine, so reflecting the arm is
legitimate. -/
theorem foldsOnto_leg3M' {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L H K p : ℤ)
    (hLP : L + 2 ≤ L + H - p) (hPL : L + H - p ≤ L + 4) (hPK : L + H - p + 1 ≤ K)
    (hKH : K ≤ H - 1) (h0 : f ⟨0, hm⟩ = p) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ H)
    (hceilf : ∀ d : Fin m, p + 3 ≤ f d →
      (∃ k : Fin m, k.val < d.val ∧ f k ≤ L + H - K) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ p + 2 ≤ f k ∧ f k' ≤ L + H - K + 1))
    (hfloorf : ∀ d : Fin m, f d ≤ L + H - K - 2 →
      (∃ k : Fin m, k.val < d.val ∧ p + 3 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + H - K - 1 ∧ H - 2 ≤ f k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        p + 2 ≤ f k ∧ f k' ≤ L + H - K ∧ H - 2 ≤ f k'')) :
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
  have hgfloor : ∀ d : Fin m, g d ≤ L + H - p - 3 →
      (∃ k : Fin m, k.val < d.val ∧ K ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ g k ≤ L + H - p - 2 ∧ K - 1 ≤ g k') := by
    intro d hd
    have hfd : p + 3 ≤ f d := by simp only [hg] at hd; omega
    rcases hceilf d hfd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, hk, by simp only [hg]; omega⟩
    · exact Or.inr ⟨k, k', hkk', hk', by simp only [hg]; omega, by simp only [hg]; omega⟩
  have hgceil : ∀ d : Fin m, K + 2 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + H - p - 3) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ K + 1 ≤ g k ∧ g k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        g k ≤ L + H - p - 2 ∧ K ≤ g k' ∧ g k'' ≤ L + 2) := by
    intro d hd
    have hfd : f d ≤ L + H - K - 2 := by simp only [hg] at hd; omega
    rcases hfloorf d hfd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by simp only [hg]; omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by simp only [hg]; omega, by simp only [hg]; omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by simp only [hg]; omega,
        by simp only [hg]; omega, by simp only [hg]; omega⟩)
  obtain ⟨β, h1, h2, h3, h4⟩ :=
    foldsOnto_leg3M hm g hglip L H K (L + H - p) hLP hPL hPK hKH hg0 hgL hgH hgfloor hgceil
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have := h4 j
  simp only [hg] at this
  simp only [leg3Walk']
  rw [abs_le] at this ⊢
  omega

/-! ## The two mixed branches -/

/-- **The middle basepoint, `HighAt L H` and `LowAt (L + 1) (H - 1)`.**  Peak `K = L + 6`.  The
floor announcement is the branch `LowAt (L + 1) (L + 7)`, the ceiling announcement the branch
`HighAt L (L + 8)`; no crookedness clause is needed. -/
theorem foldsOnto_span8_mid_high_low {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 8)
    (hlow : LowAt f (L + 1) (L + 7)) (hhigh : HighAt f L (L + 8)) :
    FoldsOnto f (leg3Len L (L + 8) (L + 6) (L + 4)) (leg3Walk L (L + 8) (L + 6) (L + 4)) := by
  refine foldsOnto_leg3M hm f hf L (L + 8) (L + 6) (L + 4) (by omega) (by omega) (by omega)
    (by omega) h0 hL hH ?_ ?_
  · intro d hd
    rcases hlow d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr ⟨j, j', hjj', hj', by omega, by omega⟩
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    exact Or.inl ⟨k, hk, by omega⟩

/-- **The middle basepoint, `LowAt L H` and `HighAt (L + 1) (H - 1)`.**  The reflection of
`foldsOnto_span8_mid_high_low`: the arm is read upside down and folded onto the reflected walk. -/
theorem foldsOnto_span8_mid_low_high {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 8)
    (hlow : LowAt f L (L + 8)) (hhigh : HighAt f (L + 1) (L + 7)) :
    FoldsOnto f (leg3Len L (L + 8) (L + 6) (L + 4)) (leg3Walk' L (L + 8) (L + 6) (L + 4)) := by
  have e : L + (L + 8) - (L + 4) = L + 4 := by ring
  have hfold := foldsOnto_leg3M' hm f hf L (L + 8) (L + 6) (L + 4) (by omega) (by omega)
    (by omega) (by omega) h0 hL hH ?_ ?_
  · rw [e] at hfold; exact hfold
  · intro d hd
    obtain ⟨k, hk, hkf⟩ := hhigh d (by omega)
    exact Or.inl ⟨k, hk, by omega⟩
  · intro d hd
    rcases hlow d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by omega, by omega⟩)

end HPC.Fold
