import HPC.Fold.Mid2MixedG67

/-!
# The index of slack is not closed by the timing law

`crossMid2_relaxed` proves the residue of the branch at `L + 5` for the **relaxed** clause
`Mid2Floor2`, whose landmark is allowed at arm index two. The consumers of the residue — `w71` and
`w72`, whose floor clause asks for `K - P + 1 = 3` — want `Mid2Floor`, with the landmark at arm
index three. One index separates them.

This file shows that the separation is real as far as the arm is concerned: an arm of the band
based at `L + 5`, 1-Lipschitz, and obeying the timing law in the form `ArmSep` — `k` levels cost
`z k - 1` steps — can satisfy `Mid2Floor2` and fail `Mid2Floor`. The witness is

```
cex67 :  5 6 6 5 5 5 5 5 5 4 4 4 3 3 2
index :  0 1 2 3 4 5 6 7 8 9 ...     14
```

Its only time at `L + 2` is its index fourteen, and its only time at `L + 6` or above is its index
one and two: the clause is met at index two and nowhere at index three or more. The descent obeys
the law — four levels are fourteen steps apart where twelve are asked, three levels six where five
are asked, two levels two where two are asked — so no sharpening of the law on a single arm can
recover the missing index. Anything that closes the gap must read the pairing between the two arms,
exactly as `not_armCrossMid2L5` of batch 66 says of the residue itself.
-/

namespace HPC.Fold

/-- The arm of the counterexample: it touches `L + 6` at its index two and never again, and
descends to `L + 2` at its index fourteen. -/
def cex67 : Fin 15 → ℤ := ![5, 6, 6, 5, 5, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2]

theorem cex67_isLip : IsLip cex67 := by unfold IsLip cex67; decide

theorem cex67_lb : ∀ j, (0 : ℤ) ≤ cex67 j := by unfold cex67; decide

theorem cex67_ub : ∀ j, cex67 j ≤ 0 + 9 := by unfold cex67; decide

theorem cex67_base : cex67 ⟨0, by norm_num⟩ = 0 + 5 := by decide

/-- **The witness obeys the timing law.** Its levels span four, so only `k ≤ 4` can be asked, and
for each of those the index gaps are met: `z 4 - 1 = 12` steps for four levels and the arm takes
fourteen, `z 3 - 1 = 5` for three and it takes six, `z 2 - 1 = 2` for two and it takes two. -/
theorem cex67_span : ∀ p q : Fin 15, cex67 q - cex67 p ≤ 4 := by unfold cex67; decide

theorem cex67_armSep : ArmSep cex67 := by
  intro k p q hk hne
  have hk4 : k ≤ 4 := by have := cex67_span p q; omega
  revert hk hne
  revert p q
  interval_cases k <;> decide

/-- **The witness satisfies the relaxed clause**, at its index two. -/
theorem mid2Floor2_cex67 : Mid2Floor2 cex67 0 := by
  unfold Mid2Floor2 cex67
  decide

/-- **And it fails the clause itself**: at its index three and beyond it never reaches `L + 6`. -/
theorem not_mid2Floor_cex67 : ¬ Mid2Floor cex67 0 := by
  unfold Mid2Floor cex67
  decide

/-- **The index of slack is not an arm-only fact.** An arm of the band `[L, L + 9]` based at
`L + 5`, 1-Lipschitz and obeying the timing law, can satisfy `Mid2Floor2` and fail `Mid2Floor`. -/
theorem not_mid2Floor_of_mid2Floor2_arm :
    ¬ (∀ (m : ℕ) (f : Fin m → ℤ) (L : ℤ) (hm : 0 < m), IsLip f → ArmSep f →
        f ⟨0, hm⟩ = L + 5 → (∀ j, L ≤ f j) → (∀ j, f j ≤ L + 9) →
        Mid2Floor2 f L → Mid2Floor f L) := by
  intro h
  exact not_mid2Floor_cex67
    (h 15 cex67 0 (by norm_num) cex67_isLip cex67_armSep cex67_base cex67_lb cex67_ub
      mid2Floor2_cex67)

end HPC.Fold
