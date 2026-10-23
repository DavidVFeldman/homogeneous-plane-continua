import HPC.Fold.Leg4
import HPC.Fold.Span8Mid

/-!
# Span eight at the middle basepoint: the two four-leg branches

`HPC/Fold/Span8Mid.lean` serves the two mixed branches of the middle-basepoint leaf with the
three-leg engine.  The two remaining branches — both arms `LowAt` at both level pairs, and both
arms `HighAt` at both level pairs — are served by no three-leg walk at all.  This file serves them
with the four-leg engine of `HPC/Fold/Leg4.lean`, at the parameters

```
H = L + 8,  K = L + 6,  M = L + 2,  P = L + 4,
```

so that `leg4Walk L (L+8) (L+6) (L+2) (L+4)` is

```
L+3, L+4, L+5, L+6, L+5, L+4, L+3, L+2, L+3, L+4, L+5, L+6, L+7, L+6, L+5, L+4, L+3, L+2, L+1.
```

* `LowAt L H` and `LowAt (L + 1) (H - 1)`: the floor announcement is read off
  `LowAt f (L+1) (L+7)`, the deep-floor announcement off `LowAt f L (L+8)`, and the ceiling
  announcement off the leaf condition `HighAt f (L+1) (L+8)` together with one application of
  `CrookUp.levels` at the levels `(L + 2, L + 8)`.
* `HighAt L H` and `HighAt (L + 1) (H - 1)`: the arm is read upside down and folded onto the
  reflected walk `leg4Walk'`.  The floor announcement comes from `HighAt f (L+1) (L+7)`, the
  ceiling announcement from the leaf condition `LowAt f L (L+7)`, and the deep-floor announcement
  from `HighAt f L (L+8)` together with one application of `CrookUp.levels` at the levels
  `(L + 1, L + 8)` — this is the three-time clause of the engine's deep-floor announcement.
-/

namespace HPC.Fold

/-! ## The reflected four-leg walk -/

/-- The reflection of `leg4Walk`: down from `H - P + L + 1` to `L + H - K`, up to `L + H - M`,
down to `L + 1`, up to `H - 1`. -/
def leg4Walk' (L H K M P : ℤ) (u : ℕ) : ℤ := L + H - leg4Walk L H K M P u

/-! ## The branch with both arms low -/

/-- **The middle basepoint, `LowAt L H` and `LowAt (L + 1) (H - 1)`.**  Four legs, with peak
`K = L + 6` and valley `M = L + 2`. -/
theorem foldsOnto_span8_mid_low_low {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (hcr : CrookUp f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 8)
    (hhigh : HighAt f (L + 1) (L + 8))
    (hlow8 : LowAt f L (L + 8)) (hlow7 : LowAt f (L + 1) (L + 7)) :
    FoldsOnto f (leg4Len L (L + 8) (L + 6) (L + 2) (L + 4))
      (leg4Walk L (L + 8) (L + 6) (L + 2) (L + 4)) := by
  refine foldsOnto_leg4 hm f hf L (L + 8) (L + 6) (L + 2) (L + 4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h0 hL hH ?_ ?_ ?_
  -- floor: from `LowAt f (L + 1) (L + 7)`
  · intro d hd
    rcases hlow7 d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr ⟨j, j', hjj', hj', by omega, by omega⟩
  -- deep floor: from `LowAt f L (L + 8)`
  · intro d hd
    rcases hlow8 d (by omega) with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by omega, by omega⟩)
  -- ceiling: the leaf condition and one crookedness clause
  · intro d hd
    obtain ⟨j, hj, hjf⟩ := hhigh d (by omega)
    obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
      hcr.levels (L + 2) (L + 8) (by omega) j d hj (by omega) (by omega)
    exact Or.inr (Or.inr ⟨j, u, u', h1, h2, h3, by omega, by omega, by omega⟩)

/-! ## The branch with both arms high -/

/-- **The middle basepoint, `HighAt L H` and `HighAt (L + 1) (H - 1)`.**  The reflection of
`foldsOnto_span8_mid_low_low`: the arm is read upside down and folded onto `leg4Walk'`.  The
deep-floor announcement of the reflected arm is the engine's three-time clause. -/
theorem foldsOnto_span8_mid_high_high {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (hcr : CrookUp f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 8)
    (hlow : LowAt f L (L + 7))
    (hhigh8 : HighAt f L (L + 8)) (hhigh7 : HighAt f (L + 1) (L + 7)) :
    FoldsOnto f (leg4Len L (L + 8) (L + 6) (L + 2) (L + 4))
      (leg4Walk' L (L + 8) (L + 6) (L + 2) (L + 4)) := by
  set g : Fin m → ℤ := fun j => L + (L + 8) - f j with hgdef
  have hglip : IsLip g := by
    intro j j' hjj'
    have := hf j j' hjj'
    simp only [hgdef]
    rw [abs_le] at this ⊢
    omega
  have hg0 : g ⟨0, hm⟩ = L + 4 := by simp only [hgdef, h0]; ring
  have hgL : ∀ j, L ≤ g j := fun j => by have := hH j; simp only [hgdef]; omega
  have hgH : ∀ j, g j ≤ L + 8 := fun j => by have := hL j; simp only [hgdef]; omega
  -- floor: from `HighAt f (L + 1) (L + 7)`
  have hgfloor : ∀ d : Fin m, g d ≤ L + 2 - 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 6 ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧
        g k ≤ L + 4 - 2 ∧ L + 6 - 1 ≤ g k') := by
    intro d hd
    have hfd : L + 7 ≤ f d := by simp only [hgdef] at hd; omega
    obtain ⟨j, hj, hjf⟩ := hhigh7 d hfd
    exact Or.inl ⟨j, hj, by simp only [hgdef]; omega⟩
  -- deep floor: from `HighAt f L (L + 8)` and one crookedness clause
  have hgdeep : ∀ d : Fin m, g d ≤ L + 2 - 2 →
      (∃ k : Fin m, k.val < d.val ∧ L + 6 + 2 ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧
        g k ≤ L + 2 - 1 ∧ L + 8 - 2 ≤ g k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        L + 6 + 1 ≤ g k ∧ g k' ≤ L + 2 ∧ L + 8 - 2 ≤ g k'') := by
    intro d hd
    have hfd : L + 8 ≤ f d := by simp only [hgdef] at hd; omega
    obtain ⟨j, hj, hjf⟩ := hhigh8 d hfd
    obtain ⟨u, u', p1, p2, p3, p4, p5⟩ :=
      hcr.levels (L + 1) (L + 8) (by omega) j d hj (by omega) (by omega)
    exact Or.inr (Or.inr ⟨j, u, u', p1, p2, p3, by simp only [hgdef]; omega,
      by simp only [hgdef]; omega, by simp only [hgdef]; omega⟩)
  -- ceiling: from `LowAt f L (L + 7)`
  have hgceil : ∀ d : Fin m, L + 6 + 2 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + 2 - 1) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧
        L + 6 + 1 ≤ g k ∧ g k' ≤ L + 2 + 1) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        g k ≤ L + 4 - 2 ∧ L + 6 ≤ g k' ∧ g k'' ≤ L + 2 + 1) := by
    intro d hd
    have hfd : f d ≤ L := by simp only [hgdef] at hd; omega
    rcases hlow d hfd with ⟨j, hj, hjf⟩ | ⟨j, j', hjj', hj', hjf, hj'f⟩
    · exact Or.inl ⟨j, hj, by simp only [hgdef]; omega⟩
    · exact Or.inr (Or.inl ⟨j, j', hjj', hj', by simp only [hgdef]; omega,
        by simp only [hgdef]; omega⟩)
  obtain ⟨β, h1, h2, h3, h4⟩ :=
    foldsOnto_leg4 hm g hglip L (L + 8) (L + 6) (L + 2) (L + 4) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hg0 hgL hgH
      hgfloor hgdeep hgceil
  refine ⟨β, h1, h2, h3, fun j => ?_⟩
  have := h4 j
  simp only [hgdef] at this
  simp only [leg4Walk']
  rw [abs_le] at this ⊢
  omega

end HPC.Fold
