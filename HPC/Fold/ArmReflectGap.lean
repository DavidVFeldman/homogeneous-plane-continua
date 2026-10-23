import HPC.Fold.ArmReflect

/-!
# What the arm reflection does not transport

`HPC/Fold/ArmReflect.lean` transports every statement whose hypotheses are `IsLip`, the band, the
basepoint level and the landmark clauses: the three criteria of batch 51 and the sentence of the
three walks all have exact mirrors at the basepoint `L + 5`. The dichotomies `valley4_or_vee` and
`leg3Ceil_or_lam` are not of that kind — they consume the crookedness of the arm — and this file
shows that the obstruction is real and not an artefact of the proofs: the clauses the model
delivers, `CrookUp` and `CrookDown`, do **not** imply their own reflections.

`CrookUp` asks, between a time and a later time three or more levels above it, for a time inside
`[f t - 2, f t - 1]` and then one inside `[f s, f s + 1]`. Its reflection `CrookUpR` asks for
`[f t - 1, f t]` and then `[f s + 1, f s + 2]` — both windows one level higher. The two arms below
are 1-Lipschitz, stay in the band `[0, 9]` and start at `5` (so they are admissible arms of the
branch `L + 5` with `L = 0`), satisfy both clauses of the model and fail the reflected ones. Every
verdict is decided in the kernel.

The censuses of batch 52 say the same thing about the arms of the model itself: over the corpus of
`census-batch52.c`, `CrookUpR` fails on 950 and `CrookDownR` on 527 of the 43 404 arms of the
branch `L + 5` on which the clauses were tested, while `CrookUp` and `CrookDown` — theorems — fail
on none.
-/

set_option maxRecDepth 4000000

namespace HPC.Fold

/-! ## The clauses, made decidable

Each is a bounded quantifier over the steps of the arm, so the instances only have to unfold the
definition. -/

instance (m : ℕ) (f : Fin m → ℤ) : Decidable (IsLip f) := by unfold IsLip; infer_instance

instance (m : ℕ) (f : Fin m → ℤ) : Decidable (CrookUp f) := by unfold CrookUp; infer_instance

instance (m : ℕ) (f : Fin m → ℤ) : Decidable (CrookDown f) := by unfold CrookDown; infer_instance

instance (m : ℕ) (f : Fin m → ℤ) : Decidable (CrookUpR f) := by unfold CrookUpR; infer_instance

instance (m : ℕ) (f : Fin m → ℤ) : Decidable (CrookDownR f) := by
  unfold CrookDownR; infer_instance

/-- An arm of the band `[0, 9]` based at `5`: it satisfies `CrookUp` and `CrookDown` and fails
`CrookUpR`. -/
def gapArmUp : Fin 16 → ℤ := ![5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 4, 5]

/-- An arm of the band `[0, 9]` based at `5`: it satisfies `CrookUp` and `CrookDown` and fails
`CrookDownR`. -/
def gapArmDown : Fin 5 → ℤ := ![5, 4, 3, 3, 2]

theorem gapArmUp_isLip : IsLip gapArmUp := by decide

theorem gapArmUp_band : (∀ j, (0 : ℤ) ≤ gapArmUp j) ∧ (∀ j, gapArmUp j ≤ 0 + 9) := by decide

theorem gapArmUp_base : gapArmUp ⟨0, by norm_num⟩ = 0 + 5 := by decide

theorem gapArmUp_crookUp : CrookUp gapArmUp := by decide

theorem gapArmUp_crookDown : CrookDown gapArmUp := by decide

theorem gapArmUp_not_crookUpR : ¬ CrookUpR gapArmUp := by decide

theorem gapArmDown_isLip : IsLip gapArmDown := by decide

theorem gapArmDown_band : (∀ j, (0 : ℤ) ≤ gapArmDown j) ∧ (∀ j, gapArmDown j ≤ 0 + 9) := by decide

theorem gapArmDown_base : gapArmDown ⟨0, by norm_num⟩ = 0 + 5 := by decide

theorem gapArmDown_crookUp : CrookUp gapArmDown := by decide

theorem gapArmDown_crookDown : CrookDown gapArmDown := by decide

theorem gapArmDown_not_crookDownR : ¬ CrookDownR gapArmDown := by decide

/-- **`CrookUp` and `CrookDown` do not imply `CrookUpR`.** There is a 1-Lipschitz arm of the band
`[0, 9]` based at `0 + 5` satisfying both clauses of the model whose reflection fails `CrookDown` —
so the hypothesis of `ceil4R_or_lam` is not one the model supplies. -/
theorem crookUpR_not_of_model :
    ∃ (m : ℕ) (hm : 0 < m) (f : Fin m → ℤ), IsLip f ∧ (∀ j, (0 : ℤ) ≤ f j) ∧
      (∀ j, f j ≤ 0 + 9) ∧ f ⟨0, hm⟩ = 0 + 5 ∧ CrookUp f ∧ CrookDown f ∧ ¬ CrookUpR f :=
  ⟨16, by norm_num, gapArmUp, gapArmUp_isLip, gapArmUp_band.1, gapArmUp_band.2, gapArmUp_base,
    gapArmUp_crookUp, gapArmUp_crookDown, gapArmUp_not_crookUpR⟩

/-- **`CrookUp` and `CrookDown` do not imply `CrookDownR`** either, and here five steps suffice. -/
theorem crookDownR_not_of_model :
    ∃ (m : ℕ) (hm : 0 < m) (f : Fin m → ℤ), IsLip f ∧ (∀ j, (0 : ℤ) ≤ f j) ∧
      (∀ j, f j ≤ 0 + 9) ∧ f ⟨0, hm⟩ = 0 + 5 ∧ CrookUp f ∧ CrookDown f ∧ ¬ CrookDownR f :=
  ⟨5, by norm_num, gapArmDown, gapArmDown_isLip, gapArmDown_band.1, gapArmDown_band.2,
    gapArmDown_base, gapArmDown_crookUp, gapArmDown_crookDown, gapArmDown_not_crookDownR⟩

end HPC.Fold
