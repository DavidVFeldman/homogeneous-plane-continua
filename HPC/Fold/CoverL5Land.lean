import HPC.Fold.Leg4Land
import HPC.Fold.Leg4Crit
import HPC.Fold.ArmReflect
import HPC.Fold.Leaf

/-!
# Exhaustiveness at the branch `L + 5`, in the form the exact criterion allows

Batch 58 §2.2 says what exhaustiveness at `L + 5` would have to look like: *every arm of the
branch either meets the criterion of one of a finite list of walks, or fails a clause the partner
arm's criterion consumes* — and it refuted the first half for the criteria of the engine
(`not_leg4CritClosesL5`), because those criteria are sound and far from necessary. With the exact
criterion of `HPC/Fold/Leg4Land.lean` the obstruction is gone: the landmark sentence of a walk
holds on an arm **iff** the arm folds onto that walk, so "the list of walks is exhaustive" and
"the list of criteria is exhaustive" are the same statement, and the statement is a decidable
property of each arm separately.

This file writes it down. `Leg4LandClosesL5` is exhaustiveness in that arm-only form, and
`s3_span_nine_mid5_of_leg4LandClosesL5` is the reduction: it implies the branch. The two
orientations are carried because the reflection of an arm of the branch is based at `L + 4`, and
the census finds both orientations used.

`census-batch59.c` evaluates `Leg4LandClosesL5` over the corpus arm by arm: at every one of the
basepoints of the branch it records, some parameter set of the window has its landmark sentence on
both arms, and a greedy cover of the recorded basepoints needs four walks —

```
reflected (P, K, M) = (L+4, L+6, L+2)      L+6 → L+3 → L+7 → L+1 → L+8
direct    (P, K, M) = (L+5, L+7, L+3)      L+4 → L+7 → L+3 → L+8 → L+1
reflected (P, K, M) = (L+4, L+6, L+1)      L+6 → L+3 → L+8 → L+1 → L+8
direct    (P, K, M) = (L+5, L+8, L+1)      L+4 → L+8 → L+1 → L+8 → L+1
```

— the first of which is the walk whose descent announcement *is* the branch hypothesis
(`HPC/Fold/CoverL5Low.lean`). This is a measurement, not a theorem; what is a theorem is that the
measurement is of the right statement.
-/

namespace HPC.Fold

/-- **A basepoint of the branch served by a walk of the family, read on the arms.** If both arms
satisfy the landmark sentence of one parameter set of the window, whose walk their common base
level `L + 5` fits, the pair folds onto that walk. -/
theorem s3_span_nine_mid5_of_leg4Land_direct {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L K M P : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5)
    (hw : Leg4Window L (L + 9) K M P) (hPlo : L + 5 ≤ P) (hPhi : P ≤ L + 7)
    (hG : Leg4Land (armG ρ i) (L + 9) K M P) (hT : Leg4Land (armT ρ i) (L + 9) K M P) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  obtain ⟨hLP, hPL, hPK, hKH, hLM, hMP, hMK, hHK⟩ := hw
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  refine ⟨leg4Len L (L + 9) K M P, leg4Walk L (L + 9) K M P, ?_, ?_⟩
  · exact foldsOnto_leg4_of_leg4Land hmG (armG ρ i) (armG_isLip hlip i) L (L + 9) K M P
      hLP hPL hPK hKH hLM hMP hMK hHK (by rw [h0G]; omega) (by rw [h0G]; omega)
      (fun j => hLb _) (fun j => hHb _) hG
  · exact foldsOnto_leg4_of_leg4Land hmT (armT ρ i) (armT_isLip hlip i) L (L + 9) K M P
      hLP hPL hPK hKH hLM hMP hMK hHK (by rw [h0T]; omega) (by rw [h0T]; omega)
      (fun j => hLb _) (fun j => hHb _) hT

/-- **The same, read through the reflection of each arm.** The reflected arms are based at
`L + 4`, and the pair folds onto the reflected walk. -/
theorem s3_span_nine_mid5_of_leg4Land_refl {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L K M P : ℤ)
    (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5)
    (hw : Leg4Window L (L + 9) K M P) (hPlo : L + 4 ≤ P) (hPhi : P ≤ L + 6)
    (hG : Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) K M P)
    (hT : Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) K M P) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  obtain ⟨hLP, hPL, hPK, hKH, hLM, hMP, hMK, hHK⟩ := hw
  have hmG : 0 < n - i.val := by have := i.isLt; omega
  have hmT : 0 < i.val + 1 := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have hGb : ∀ j, L ≤ armG ρ i j ∧ armG ρ i j ≤ L + 9 := fun j => ⟨hLb _, hHb _⟩
  have hTb : ∀ j, L ≤ armT ρ i j ∧ armT ρ i j ≤ L + 9 := fun j => ⟨hLb _, hHb _⟩
  refine ⟨leg4Len L (L + 9) K M P, leg4Walk' L (L + 9) K M P, ?_, ?_⟩
  · refine foldsOnto_leg4W_refl (armG ρ i) L (L + 9) K M P ?_
    exact foldsOnto_leg4_of_leg4Land hmG (armRefl (L + (L + 9)) (armG ρ i))
      (armRefl_isLip (armG_isLip hlip i) _) L (L + 9) K M P
      hLP hPL hPK hKH hLM hMP hMK hHK
      (by simp only [armRefl_apply]; rw [h0G]; omega)
      (by simp only [armRefl_apply]; rw [h0G]; omega)
      (fun j => by simp only [armRefl_apply]; have := hGb j; omega)
      (fun j => by simp only [armRefl_apply]; have := hGb j; omega) hG
  · refine foldsOnto_leg4W_refl (armT ρ i) L (L + 9) K M P ?_
    exact foldsOnto_leg4_of_leg4Land hmT (armRefl (L + (L + 9)) (armT ρ i))
      (armRefl_isLip (armT_isLip hlip i) _) L (L + 9) K M P
      hLP hPL hPK hKH hLM hMP hMK hHK
      (by simp only [armRefl_apply]; rw [h0T]; omega)
      (by simp only [armRefl_apply]; rw [h0T]; omega)
      (fun j => by simp only [armRefl_apply]; have := hTb j; omega)
      (fun j => by simp only [armRefl_apply]; have := hTb j; omega) hT

/-- **Exhaustiveness at the branch `L + 5`, in arm-only form.** At every basepoint of the branch
some parameter set of the window has its *landmark sentence* — the exact criterion of its walk —
on both arms, read either on the arms or on their reflections in the level `L + (L + 9)`.

Unlike `Leg4CritClosesL5` (`HPC/Fold/Audit58.lean`), which is false, this is a statement about the
folds themselves: `foldsOnto_leg4_iff_leg4Land` makes each clause of it equivalent to "the arm
folds onto the walk". -/
def Leg4LandClosesL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    ∃ K M P : ℤ, Leg4Window L (L + 9) K M P ∧
      ((L + 5 ≤ P ∧ P ≤ L + 7 ∧
          Leg4Land (armG ρ i) (L + 9) K M P ∧ Leg4Land (armT ρ i) (L + 9) K M P) ∨
       (L + 4 ≤ P ∧ P ≤ L + 6 ∧
          Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) K M P ∧
          Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) K M P))

/-- **Exhaustiveness in that form closes the branch.** -/
theorem s3_span_nine_mid5_of_leg4LandClosesL5 (h : Leg4LandClosesL5) {n : ℕ} (ρ σ : Fin n → ℤ)
    (i : Fin n) (L : ℤ) (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  obtain ⟨K, M, P, hw, hcase⟩ := h n ρ σ i L hlip hcr hLb hHb hp hG hT
  rcases hcase with ⟨hPlo, hPhi, hlG, hlT⟩ | ⟨hPlo, hPhi, hlG, hlT⟩
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L K M P hlip hLb hHb hp hw hPlo hPhi hlG hlT
  · exact s3_span_nine_mid5_of_leg4Land_refl ρ i L K M P hlip hLb hHb hp hw hPlo hPhi hlG hlT

end HPC.Fold
