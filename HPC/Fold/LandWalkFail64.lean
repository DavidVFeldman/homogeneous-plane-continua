import HPC.Fold.LandWalkBase64

/-!
# `LandWalkPSuffices` is false

Question 4 of batch 64 asks for the induction that would prove `LandWalkPSuffices`
(`HPC/Fold/LandWalkFail.lean`): for a walk with **no unit leg**, the corrected landmark sentence
`LandWalkP` implies folding. **The statement is false.** The induction cannot be carried out.

The search of `probe64.c` (log `probe64b.log`) runs the implication over all walks of at most four
turns with levels in `[0, 6]`, restricted to walks with no unit leg, and all arms of at most
thirteen times; it finds 64 walks with a counterexample, and every one of them has a leg of
length **two**. The batch-63 search missed them because its arms had at most twelve times and its
levels at most five.

The smallest witness is the walk of the turning levels `[3, 1, 4]` from `0`:

```
walkList 0 [3,1,4] :  0  1  2  3  2  1  2  3  4      (nine times)
turn times         :  0        3     5        8
turning levels     :  0        3     1        4
legs               :     3        2       3
```

and the thirteen-time arm

```
cexArm3 :  -1  0  1  2  1  0  -1  0  1  2  3  4  5
```

* It satisfies `LandWalkP` (`landWalkP_cex3`), with the single chain `(0, 3, 8, 11)`: the arm's
  time `0` at the level `-1` for the walk's start, its time `3` at `2` for the turning level `3`,
  its time `8` at `1` for the turning level `1`, and its time `11` at `4` for the last turning
  level `4`. Every gap the walk asks for — three, two, three — is met with room to spare.
* It does not fold (`not_foldsOnto_cex3`). Its two times at the level `-1`, at the arm's times `0`
  and `6`, are served by the walk's time `0` alone, so the fold stands at the walk's time `0` at
  the arm's time `6`; from there the arm's last level `5`, which only the walk's time `8` serves,
  is six steps away and the arm has only six times left — but the fold would have to be at the
  walk's time `8` at the arm's time `12`, and `0 + 6 < 8`.

**What the counterexample says.** The landmark sentence reads each landmark *within one* of the
walk's turning level. That is enough to place the landmarks in the right order, and it is
necessary for a fold; it is not enough to force the fold to *be* at the turn, and where a leg is
only two steps long the one level of slack lets the chain be met by an arm that has to repeat a
level the walk passes only once. A leg of three steps leaves no such room on the search:

```
                        walks    walks with a counterexample to sufficiency
                                 LandWalkP, arms of at most thirteen times
  shortest leg  2        1120      64
  shortest leg  3         500       0
  shortest leg  4         184       0
  shortest leg  5          50       0
  shortest leg  6           8       0
```

so the statement `LandWalkP3Suffices` below — the same with `NoShortLeg`, every leg at least three
steps long — is what the measurement leaves standing. The four-leg window of
`HPC/Fold/Leg4Land.lean` gives legs `K - P + 1 ≥ 3`, `K - M ≥ 3`, `H - 1 - M ≥ 3` and
`H - 2 - (L + 1) ≥ 3`, so the engine of that file is inside `NoShortLeg` and is untouched by the
refutation, exactly as it was untouched by the batch-63 one.
-/

namespace HPC.Fold

/-! ## The witness -/

/-- The arm of the batch-64 counterexample: thirteen times, at the levels
`-1 0 1 2 1 0 -1 0 1 2 3 4 5`. -/
def cexArm3 : Fin 13 → ℤ := ![-1, 0, 1, 2, 1, 0, -1, 0, 1, 2, 3, 4, 5]

theorem cex3_walkLen : walkLen 0 [3, 1, 4] = 9 := rfl

theorem cex3_walkList_zero : walkList 0 [3, 1, 4] 0 = 0 := rfl
theorem cex3_walkList_one : walkList 0 [3, 1, 4] 1 = 1 := rfl
theorem cex3_walkList_two : walkList 0 [3, 1, 4] 2 = 2 := rfl
theorem cex3_walkList_three : walkList 0 [3, 1, 4] 3 = 3 := rfl
theorem cex3_walkList_four : walkList 0 [3, 1, 4] 4 = 2 := rfl
theorem cex3_walkList_five : walkList 0 [3, 1, 4] 5 = 1 := rfl
theorem cex3_walkList_six : walkList 0 [3, 1, 4] 6 = 2 := rfl
theorem cex3_walkList_seven : walkList 0 [3, 1, 4] 7 = 3 := rfl
theorem cex3_walkList_eight : walkList 0 [3, 1, 4] 8 = 4 := rfl

theorem cex3_walkStop_one : walkStop 0 [3, 1, 4] 1 = 3 := rfl
theorem cex3_walkStop_two : walkStop 0 [3, 1, 4] 2 = 5 := rfl
theorem cex3_walkStop_three : walkStop 0 [3, 1, 4] 3 = 8 := rfl

/-- Beyond the third turn the walk stands still, at its time `8`. -/
theorem cex3_walkStop_ge (k : ℕ) : walkStop 0 [3, 1, 4] (k + 3) = 8 := by
  simp [walkStop]

/-- Beyond the third turn the walk is at the level `4`. -/
theorem cex3_walkLevel_ge (k : ℕ) : walkLevel 0 [3, 1, 4] (k + 3) = 4 := by
  simp [walkLevel]

/-- The walk has no unit leg: its legs are three, two and three steps long. -/
theorem cex3_noUnitLeg : NoUnitLeg 0 [3, 1, 4] := by
  refine ⟨by decide, by decide, by decide, trivial⟩

/-- Every level of the arm is served by the walk. -/
theorem cex3_band (j : Fin 13) : ∃ p : ℕ, p < walkLen 0 [3, 1, 4] ∧
    |cexArm3 j - walkList 0 [3, 1, 4] p| ≤ 1 := by
  fin_cases j
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨8, by decide, by decide⟩

/-- The arm is 1-Lipschitz. -/
theorem cex3_isLip : IsLip cexArm3 := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [cexArm3]

/-! ## The arm satisfies the corrected sentence -/

/-- **Where the trigger can sit.** For every time `d` of the arm, a position `P` that no serving
time of the walk precedes is at most `3`, and at most the arm's own time, unless `d` is the arm's
last time — where the only serving position is the walk's time `8`. -/
theorem cex3_trigger_bound {d : Fin 13} {P : ℕ}
    (hd : ∀ p : ℕ, p < walkLen 0 [3, 1, 4] → |cexArm3 d - walkList 0 [3, 1, 4] p| ≤ 1 → P ≤ p) :
    (d.val = 12 ∧ P ≤ 8) ∨ (P ≤ 3 ∧ P ≤ d.val) := by
  fin_cases d
  · exact Or.inr ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); omega⟩
  · exact Or.inr ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); omega⟩
  · exact Or.inr ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); omega⟩
  · exact Or.inr ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 3; omega⟩
  · exact Or.inr ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 4; omega⟩
  · exact Or.inr ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 5; omega⟩
  · exact Or.inr ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 6; omega⟩
  · exact Or.inr ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 7; omega⟩
  · exact Or.inr ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 8; omega⟩
  · exact Or.inr ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 9; omega⟩
  · exact Or.inr ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 10; omega⟩
  · exact Or.inr ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 11; omega⟩
  · exact Or.inl ⟨rfl, by have := hd 8 (by decide) (by decide); omega⟩

/-- **The arm satisfies the corrected sentence**, with the single chain `(0, 3, 8, 11)`. -/
theorem landWalkP_cex3 : LandWalkP cexArm3 0 [3, 1, 4] := by
  intro r d P hrP hd
  have hkey := cex3_trigger_bound hd
  refine ⟨fun u => if u = 0 then (0 : Fin 13) else if u = 1 then (3 : Fin 13)
    else if u = 2 then (8 : Fin 13) else (11 : Fin 13), Nat.le_refl 0, ?_, ?_, ?_⟩
  · -- the gaps of the chain are the walk's own
    intro u _
    match u with
    | 0 => show (0 : ℕ) + (3 - 0) ≤ 3; omega
    | 1 => show (3 : ℕ) + (5 - 3) ≤ 8; omega
    | 2 => show (8 : ℕ) + (8 - 5) ≤ 11; omega
    | (k + 3) =>
        show (11 : ℕ) + (walkStop 0 [3, 1, 4] (k + 3 + 1) - walkStop 0 [3, 1, 4] (k + 3)) ≤ 11
        rw [show k + 3 + 1 = (k + 1) + 3 by omega, cex3_walkStop_ge, cex3_walkStop_ge]
  · -- the last landmark is far enough before the time `d`
    match r with
    | 0 =>
        show (0 : ℕ) + (P - 0) ≤ d.val
        have hd12 : d.val ≤ 12 := by omega
        omega
    | 1 =>
        have h3 : 3 ≤ P := by rw [cex3_walkStop_one] at hrP; exact hrP
        show (3 : ℕ) + (P - walkStop 0 [3, 1, 4] 1) ≤ d.val
        rw [cex3_walkStop_one]
        omega
    | 2 =>
        have h5 : 5 ≤ P := by rw [cex3_walkStop_two] at hrP; exact hrP
        show (8 : ℕ) + (P - walkStop 0 [3, 1, 4] 2) ≤ d.val
        rw [cex3_walkStop_two]
        omega
    | (k + 3) =>
        have h8 : 8 ≤ P := by rw [cex3_walkStop_ge] at hrP; exact hrP
        show (11 : ℕ) + (P - walkStop 0 [3, 1, 4] (k + 3)) ≤ d.val
        rw [cex3_walkStop_ge]
        omega
  · -- the chain's levels are the walk's turning levels
    intro u _
    match u with
    | 0 => show |(-1 : ℤ) - 0| ≤ 1; decide
    | 1 => show |(2 : ℤ) - 3| ≤ 1; decide
    | 2 => show |(1 : ℤ) - 1| ≤ 1; decide
    | (k + 3) =>
        show |(4 : ℤ) - walkLevel 0 [3, 1, 4] (k + 3)| ≤ 1
        rw [cex3_walkLevel_ge]
        decide

/-! ## The arm does not fold -/

/-- **The arm does not fold onto the walk.** -/
theorem not_foldsOnto_cex3 :
    ¬ FoldsOnto cexArm3 (walkLen 0 [3, 1, 4]) (walkList 0 [3, 1, 4]) := by
  rintro ⟨β, hlen, hstep, hz, hval⟩
  have h0 : β (0 : Fin 13) = 0 := hz _ rfl
  have s01 := hstep (0 : Fin 13) (1 : Fin 13) rfl
  have s12 := hstep (1 : Fin 13) (2 : Fin 13) rfl
  have s23 := hstep (2 : Fin 13) (3 : Fin 13) rfl
  have s34 := hstep (3 : Fin 13) (4 : Fin 13) rfl
  have s45 := hstep (4 : Fin 13) (5 : Fin 13) rfl
  have s56 := hstep (5 : Fin 13) (6 : Fin 13) rfl
  have s67 := hstep (6 : Fin 13) (7 : Fin 13) rfl
  have s78 := hstep (7 : Fin 13) (8 : Fin 13) rfl
  have s89 := hstep (8 : Fin 13) (9 : Fin 13) rfl
  have s9a := hstep (9 : Fin 13) (10 : Fin 13) rfl
  have sab := hstep (10 : Fin 13) (11 : Fin 13) rfl
  have sbc := hstep (11 : Fin 13) (12 : Fin 13) rfl
  rw [abs_le] at s01 s12 s23 s34 s45 s56 s67 s78 s89 s9a sab sbc
  -- the arm's second time at the level `-1` pins the fold to the walk's time `0`
  have hb6 : β (6 : Fin 13) = 0 := by
    have hle : β (6 : Fin 13) ≤ 6 := by omega
    have hv : |(-1 : ℤ) - walkList 0 [3, 1, 4] (β (6 : Fin 13))| ≤ 1 := hval (6 : Fin 13)
    rcases (show β (6 : Fin 13) = 0 ∨ β (6 : Fin 13) = 1 ∨ β (6 : Fin 13) = 2 ∨
        β (6 : Fin 13) = 3 ∨ β (6 : Fin 13) = 4 ∨ β (6 : Fin 13) = 5 ∨
        β (6 : Fin 13) = 6 by omega) with h | h | h | h | h | h | h
    · exact h
    · rw [h, cex3_walkList_one] at hv; norm_num at hv
    · rw [h, cex3_walkList_two] at hv; norm_num at hv
    · rw [h, cex3_walkList_three] at hv; norm_num at hv
    · rw [h, cex3_walkList_four] at hv; norm_num at hv
    · rw [h, cex3_walkList_five] at hv; norm_num at hv
    · rw [h, cex3_walkList_six] at hv; norm_num at hv
  -- and the last level is served only by the walk's last time, which is now out of reach
  have hv12 : |(5 : ℤ) - walkList 0 [3, 1, 4] (β (12 : Fin 13))| ≤ 1 := hval (12 : Fin 13)
  rcases (show β (12 : Fin 13) = 0 ∨ β (12 : Fin 13) = 1 ∨ β (12 : Fin 13) = 2 ∨
      β (12 : Fin 13) = 3 ∨ β (12 : Fin 13) = 4 ∨ β (12 : Fin 13) = 5 ∨
      β (12 : Fin 13) = 6 by omega) with h | h | h | h | h | h | h
  · rw [h, cex3_walkList_zero] at hv12; norm_num at hv12
  · rw [h, cex3_walkList_one] at hv12; norm_num at hv12
  · rw [h, cex3_walkList_two] at hv12; norm_num at hv12
  · rw [h, cex3_walkList_three] at hv12; norm_num at hv12
  · rw [h, cex3_walkList_four] at hv12; norm_num at hv12
  · rw [h, cex3_walkList_five] at hv12; norm_num at hv12
  · rw [h, cex3_walkList_six] at hv12; norm_num at hv12

/-- **`LandWalkPSuffices` is false.** The corrected landmark sentence is not sufficient for a walk
with no unit leg either: the thirteen-time arm `cexArm3` satisfies `LandWalkP` on the walk of the
turning levels `[3, 1, 4]` from `0`, whose legs are three, two and three steps long, and does not
fold onto it. -/
theorem not_landWalkPSuffices : ¬ LandWalkPSuffices := by
  intro h
  exact not_foldsOnto_cex3
    (h 13 (by omega) cexArm3 0 [3, 1, 4] cex3_isLip (by decide) cex3_noUnitLeg cex3_band
      landWalkP_cex3)

/-! ## The statement the measurement leaves standing -/

/-- Every leg of the walk is at least three times long. This is what the four-leg window of
`HPC/Fold/Leg4Land.lean` gives — `K - P + 1 ≥ 3`, `K - M ≥ 3`, `H - 1 - M ≥ 3`,
`H - 2 - (L + 1) ≥ 3` — and `probe64.c` finds no counterexample to sufficiency under it. -/
def NoShortLeg : ℤ → List ℤ → Prop
  | _, [] => True
  | s, t :: ts => 3 ≤ (t - s).natAbs ∧ NoShortLeg t ts

/-- A walk with no short leg has no unit leg. -/
theorem noUnitLeg_of_noShortLeg : ∀ (s : ℤ) (ts : List ℤ), NoShortLeg s ts → NoUnitLeg s ts
  | _, [], _ => trivial
  | s, t :: ts, h => ⟨by have := h.1; omega, noUnitLeg_of_noShortLeg t ts h.2⟩

/-- **The corrected sufficiency statement, corrected again.** `LandWalkPSuffices` with `NoUnitLeg`
replaced by `NoShortLeg`; `not_landWalkPSuffices` refutes the weaker hypothesis, and the search of
`probe64.c` finds no counterexample to this one. Its proof is not in this batch; its base cases
are `landWalkP_suffices_of_length_le_one`.

**Batch 65 refutes this statement too** (`not_landWalkP3Suffices`, `HPC/Fold/LandWalkFail65.lean`):
the search behind it was exhaustive only to arms of fourteen times, and a randomised deep search to
arms of thirty times (`probe65b.c`) finds counterexamples at walks whose shortest leg is three and
at walks whose shortest leg is four. The statement is kept as batch 64 delivered it; the witness is
`cexArm65` on the walk of the turning levels `[5, 2, 6]` from `1`. -/
def LandWalkP3Suffices : Prop :=
  ∀ (m : ℕ) (hm : 0 < m) (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ),
    IsLip f →
    |f ⟨0, hm⟩ - s| ≤ 1 →
    NoShortLeg s ts →
    (∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) →
    LandWalkP f s ts →
    FoldsOnto f (walkLen s ts) (walkList s ts)

/-- **With it the corrected sentence is folding**, for a walk with no short leg. -/
theorem landWalkP_iff_foldsOnto_of_suffices3 (h : LandWalkP3Suffices) {m : ℕ} (hm : 0 < m)
    (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) (hlip : IsLip f) (h0 : |f ⟨0, hm⟩ - s| ≤ 1)
    (hleg : NoShortLeg s ts)
    (hband : ∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) :
    LandWalkP f s ts ↔ FoldsOnto f (walkLen s ts) (walkList s ts) :=
  ⟨fun hl => h m hm f s ts hlip h0 hleg hband hl, landWalkP_of_foldsOnto⟩

end HPC.Fold
