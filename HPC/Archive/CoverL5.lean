import HPC.Fold.Leg4Wide

/-!
# Three four-leg walks for the branch `L + 5`

The census `census-batch56.c` measures what the branch `L + 5` still needs. Over the corpus (4 566
faithful pairs, 1 464 514 basepoints of the branch) the three reflected three-turn walks serve all
but **917** basepoints, and every one of those 917 is served by a walk of the window of the wide
four-leg engine `foldsOnto_leg4W` (`HPC/Fold/Leg4Wide.lean`). A greedy cover of the 917 needs
**three** walks, and they are the three proved here:

| walk | engine parameters | serves |
|---|---|---|
| `L+4 → L+7 → L+1 → L+8 → L+1` | `leg4Walk L (L+9) (L+7) (L+1) (L+5)` | 701 of 917 |
| `L+4 → L+7 → L+2 → L+8 → L+1` | `leg4Walk L (L+9) (L+7) (L+2) (L+5)` | 611 of 917 |
| `L+6 → L+3 → L+7 → L+1 → L+8` | the reflection of `leg4Walk L (L+9) (L+6) (L+2) (L+4)` | 528 of 917 |

Each is an instance of the engine, so each comes with a criterion of the same shape as
`foldsOnto_walk5738`: three announcements — the descents to `P − 3`, the descents to `P − 4` and
the ascents to `K + 2`, read at the walk's own levels — suffice for the fold. That is the answer
to question 4 of the commission on the corpus: the walks of the four-leg table each have a
criterion, and a list of three of them covers every basepoint of the branch that the three-turn
walks miss. It is a statement about the corpus, not a theorem about the branch: what is proved
here is the criterion for each walk, not that the three walks exhaust the branch.
-/

namespace HPC.Fold

/-- **The walk `L+4 → L+7 → L+1 → L+8 → L+1`.** The widest single walk of the branch-`L + 5`
residue: the engine at `P = L + 5`, `K = L + 7`, `M = L + 1`. An arm based at `L + 4` or `L + 5`
inside the band `[L, L + 9]` folds onto it as soon as its descents to `L + 2`, its descents to
`L + 1` and its ascents to `L + 9` are announced. -/
theorem foldsOnto_walk47181 {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0lo : L + 4 ≤ f ⟨0, hm⟩) (h0hi : f ⟨0, hm⟩ ≤ L + 5)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hfloor : ∀ d : Fin m, f d ≤ L + 2 →
      (∃ k : Fin m, k.val < d.val ∧ L + 7 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 3 ∧ L + 6 ≤ f k'))
    (hdeep : ∀ d : Fin m, f d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 9 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L ∧ L + 7 ≤ f k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        L + 8 ≤ f k ∧ f k' ≤ L + 1 ∧ L + 7 ≤ f k''))
    (hceil : ∀ d : Fin m, L + 9 ≤ f d →
      (∃ k : Fin m, k.val < d.val ∧ f k ≤ L) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 8 ≤ f k ∧ f k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        f k ≤ L + 3 ∧ L + 7 ≤ f k' ∧ f k'' ≤ L + 2)) :
    FoldsOnto f (leg4Len L (L + 9) (L + 7) (L + 1) (L + 5))
      (leg4Walk L (L + 9) (L + 7) (L + 1) (L + 5)) := by
  refine foldsOnto_leg4W hm f hf L (L + 9) (L + 7) (L + 1) (L + 5) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hL hH ?_ ?_ ?_
  · intro d hd
    rcases hfloor d (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr ⟨k, k', hkk', hk', by omega, by omega⟩
  · intro d hd
    rcases hdeep d (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by omega, by omega, by omega⟩)
  · intro d hd
    rcases hceil d (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by omega, by omega, by omega⟩)

/-- **The walk `L+4 → L+7 → L+2 → L+8 → L+1`.** The engine at `P = L + 5`, `K = L + 7`,
`M = L + 2`: the same shape with the valley one level higher. -/
theorem foldsOnto_walk47281 {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (L : ℤ)
    (h0lo : L + 4 ≤ f ⟨0, hm⟩) (h0hi : f ⟨0, hm⟩ ≤ L + 5)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hfloor : ∀ d : Fin m, f d ≤ L + 2 →
      (∃ k : Fin m, k.val < d.val ∧ L + 7 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 3 ∧ L + 6 ≤ f k'))
    (hdeep : ∀ d : Fin m, f d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 9 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 1 ∧ L + 7 ≤ f k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        L + 8 ≤ f k ∧ f k' ≤ L + 2 ∧ L + 7 ≤ f k''))
    (hceil : ∀ d : Fin m, L + 9 ≤ f d →
      (∃ k : Fin m, k.val < d.val ∧ f k ≤ L + 1) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 8 ≤ f k ∧ f k' ≤ L + 3) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        f k ≤ L + 3 ∧ L + 7 ≤ f k' ∧ f k'' ≤ L + 3)) :
    FoldsOnto f (leg4Len L (L + 9) (L + 7) (L + 2) (L + 5))
      (leg4Walk L (L + 9) (L + 7) (L + 2) (L + 5)) := by
  refine foldsOnto_leg4W hm f hf L (L + 9) (L + 7) (L + 2) (L + 5) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hL hH ?_ ?_ ?_
  · intro d hd
    rcases hfloor d (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr ⟨k, k', hkk', hk', by omega, by omega⟩
  · intro d hd
    rcases hdeep d (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by omega, by omega, by omega⟩)
  · intro d hd
    rcases hceil d (by omega) with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by omega, by omega, by omega⟩)

/-- **The walk `L+6 → L+3 → L+7 → L+1 → L+8`.** The reflection of the engine at `P = L + 4`,
`K = L + 6`, `M = L + 2`. An arm based at `L + 5` or `L + 6` inside the band `[L, L + 9]` folds
onto it as soon as its ascents to `L + 8`, its ascents to `L + 9` and its descents to `L + 1` are
announced — the reflections of the engine's three announcements. -/
theorem foldsOnto_walk63718 {m : ℕ} (hm : 0 < m) (g : Fin m → ℤ) (hg : IsLip g) (L : ℤ)
    (h0lo : L + 5 ≤ g ⟨0, hm⟩) (h0hi : g ⟨0, hm⟩ ≤ L + 6)
    (hL : ∀ j, L ≤ g j) (hH : ∀ j, g j ≤ L + 9)
    (hup8 : ∀ d : Fin m, L + 8 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + 3) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 7 ≤ g k ∧ g k' ≤ L + 4))
    (hup9 : ∀ d : Fin m, L + 9 ≤ g d →
      (∃ k : Fin m, k.val < d.val ∧ g k ≤ L + 1) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ L + 8 ≤ g k ∧ g k' ≤ L + 2) ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        g k ≤ L + 2 ∧ L + 7 ≤ g k' ∧ g k'' ≤ L + 2))
    (hdown1 : ∀ d : Fin m, g d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 8 ≤ g k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ g k ≤ L + 2 ∧ L + 6 ≤ g k') ∨
      (∃ k k' k'' : Fin m, k.val < k'.val ∧ k'.val < k''.val ∧ k''.val < d.val ∧
        L + 7 ≤ g k ∧ g k' ≤ L + 3 ∧ L + 6 ≤ g k'')) :
    FoldsOnto g (leg4Len L (L + 9) (L + 6) (L + 2) (L + 4))
      (leg4Walk' L (L + 9) (L + 6) (L + 2) (L + 4)) := by
  set f : Fin m → ℤ := fun j => L + (L + 9) - g j with hfdef
  have hflip : IsLip f := by
    intro j j' hjj'
    have := hg j j' hjj'
    simp only [hfdef]
    rw [abs_le] at this ⊢
    omega
  refine foldsOnto_leg4W_refl g L (L + 9) (L + 6) (L + 2) (L + 4) ?_
  refine foldsOnto_leg4W hm f hflip L (L + 9) (L + 6) (L + 2) (L + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [hfdef]; omega) (by simp only [hfdef]; omega)
    (by simp only [hfdef]; omega)
    (fun j => by have := hH j; simp only [hfdef]; omega)
    (fun j => by have := hL j; simp only [hfdef]; omega) ?_ ?_ ?_
  -- floor, read at `P - 3 = L + 1`: the reflection of the ascents to `L + 8`
  · intro d hd
    have hgd : L + 8 ≤ g d := by simp only [hfdef] at hd; omega
    rcases hup8 d hgd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩
    · exact Or.inl ⟨k, hk, by simp only [hfdef]; omega⟩
    · exact Or.inr ⟨k, k', hkk', hk', by simp only [hfdef]; omega, by simp only [hfdef]; omega⟩
  -- deep floor, read at `P - 4 = L`: the reflection of the ascents to `L + 9`
  · intro d hd
    have hgd : L + 9 ≤ g d := by simp only [hfdef] at hd; omega
    rcases hup9 d hgd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by simp only [hfdef]; omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by simp only [hfdef]; omega,
        by simp only [hfdef]; omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by simp only [hfdef]; omega,
        by simp only [hfdef]; omega, by simp only [hfdef]; omega⟩)
  -- ceiling, read at `K + 2 = L + 8` on the reflection: the descents of `g` to `L + 1`
  · intro d hd
    have hgd : g d ≤ L + 1 := by simp only [hfdef] at hd; omega
    rcases hdown1 d hgd with ⟨k, hk, hkf⟩ | ⟨k, k', hkk', hk', hkf, hk'f⟩ |
      ⟨k, k', k'', hkk', hk'k'', hk'', hkf, hk'f, hk''f⟩
    · exact Or.inl ⟨k, hk, by simp only [hfdef]; omega⟩
    · exact Or.inr (Or.inl ⟨k, k', hkk', hk', by simp only [hfdef]; omega,
        by simp only [hfdef]; omega⟩)
    · exact Or.inr (Or.inr ⟨k, k', k'', hkk', hk'k'', hk'', by simp only [hfdef]; omega,
        by simp only [hfdef]; omega, by simp only [hfdef]; omega⟩)

end HPC.Fold
