import HPC.Fold.LandWalkSuff

/-!
# The general landmark sentence is *not* sufficient, and the trigger is why

Batch 62 stated the sufficiency half of the general engine as `LandWalkSuffices`
(`HPC/Fold/LandWalkSuff.lean`): for a walk of **any** shape, the landmark sentence `LandWalk`
implies folding. Question 4 of batch 63 asks for its proof. This file refutes it.

## The counterexample

Take the walk of the three turning levels `[1, 0, 3]` from `0`,

```
walkList 0 [1,0,3] :   0  1  0  1  2  3          (six times)
turns              :   0  1  2        5
turning levels     :   0  1  0        3
```

and the three-time arm `f = (1, 2, 3)`. It is 1-Lipschitz, starts within one of the walk's first
level, and every one of its levels is served by the walk's time `4` alone if need be. It satisfies
`LandWalk f 0 [1,0,3]` — `landWalk_cex` — and it does **not** fold onto the walk
(`not_foldsOnto_cex`): the fold must start at the walk's time `0`, so after two steps it can be at
the walk's time `2` at the latest, and the walk's levels there are `0, 1, 0`, none of which serves
the arm's level `3`. Hence `not_landWalkSuffices`.

## Where the sentence leaks

`LandWalk`'s clause `r` fires at a time `d` only when **every** time of the walk that serves `f d`
is the `r`-th turn time or later, and the chain it then returns ends at `d` itself with the walk's
own turn-to-turn gap. Both halves of that are weaker than what the four-leg sentence `Leg4Land`
asks: there the trigger is read at the *level* (`leg4Walk_floor_pos` and its two companions give
the earliest serving time `2K - P - v` of a level `v`, which is not a turn time), and the last gap
of the chain (`K - 1 - f d`, `H - 2 - f d`, `f d - M - 1`) is the distance from the last landmark
to *that* time, not to the next turn. In the counterexample the arm's level `3` is served earliest
at time `4`, which is not a turn time and lies strictly before the last turn `5`, so no clause of
`LandWalk` fires at the arm's last time at all.

`LandWalkP` repairs exactly this: the trigger is any position `P` at or after the `r`-th turn that
no serving time precedes, and the chain's last landmark is a time of the arm at `walkLevel r`, at
least `P - walkStop r` before `d`. It is still necessary for folding — `landWalkP_of_foldsOnto`,
one application of `foldsOnto_landmarkN` to the chain `walkStop 0 ≤ ⋯ ≤ walkStop r ≤ P` — and it
excludes the counterexample above (`not_landWalkP_cex`).

The search that found the counterexample (`probe63.c`, logs `probe63.log`, `probe63b.log`) reports
that the repair is neither cosmetic nor complete. Over the same range — all 1862 walks of at most
four turns with levels in `[0,5]`, and all arms of at most twelve times —

```
                        walks    with a counterexample to sufficiency
                                 LandWalk        LandWalkP
  shortest leg  1        1120      510               30
  shortest leg  2         500      162                0
  shortest leg  3         184       30                0
  shortest leg  4          50        0                0
  shortest leg  5           8        0                0
```

so the sentence as stated fails at walks whose every leg is three long, while the corrected
sentence fails only at walks with a leg of length **one**. A unit leg is excluded by the four-leg
window (`M + 3 ≤ K`, `P ≤ K`, `M ≤ P - 2`, `K ≤ H - 1`), which is why the engine of
`HPC/Fold/Leg4Land.lean` is unaffected. The unit-leg case is a refutation in its own right and is
proved here as well (`not_landWalkP_suffices_without_noUnitLeg`, with the ten-time arm
`0 1 2 1 0 1 2 1 0 -1` on the walk `1 2 3 2 3 2 1 0`). `LandWalkPSuffices` is the corrected
statement, carrying that hypothesis, and is not proved here.
-/

namespace HPC.Fold

/-! ## The counterexample arm and its walk -/

/-- The arm of the counterexample: three times at the levels `1, 2, 3`. -/
def cexArm : Fin 3 → ℤ := ![1, 2, 3]

@[simp] theorem cexArm_zero : cexArm 0 = 1 := rfl
@[simp] theorem cexArm_one : cexArm 1 = 2 := rfl
@[simp] theorem cexArm_two : cexArm 2 = 3 := rfl

/-- The walk of the counterexample has six times. -/
theorem cex_walkLen : walkLen 0 [1, 0, 3] = 6 := rfl

theorem cex_walkList_zero : walkList 0 [1, 0, 3] 0 = 0 := rfl
theorem cex_walkList_one : walkList 0 [1, 0, 3] 1 = 1 := rfl
theorem cex_walkList_two : walkList 0 [1, 0, 3] 2 = 0 := rfl
theorem cex_walkList_three : walkList 0 [1, 0, 3] 3 = 1 := rfl
theorem cex_walkList_four : walkList 0 [1, 0, 3] 4 = 2 := rfl
theorem cex_walkList_five : walkList 0 [1, 0, 3] 5 = 3 := rfl

theorem cex_walkStop_zero : walkStop 0 [1, 0, 3] 0 = 0 := rfl
theorem cex_walkStop_one : walkStop 0 [1, 0, 3] 1 = 1 := rfl
theorem cex_walkStop_two : walkStop 0 [1, 0, 3] 2 = 2 := rfl

/-- Beyond the third turn the walk stands still, at time `5`. -/
theorem cex_walkStop_ge (k : ℕ) : walkStop 0 [1, 0, 3] (k + 3) = 5 := by
  simp [walkStop]

theorem cex_walkLevel_zero : walkLevel 0 [1, 0, 3] 0 = 0 := rfl
theorem cex_walkLevel_one : walkLevel 0 [1, 0, 3] 1 = 1 := rfl

/-- Every level of the arm is served by the walk's time `4`. -/
theorem cex_band (j : Fin 3) : ∃ p : ℕ, p < walkLen 0 [1, 0, 3] ∧
    |cexArm j - walkList 0 [1, 0, 3] p| ≤ 1 := by
  refine ⟨4, by norm_num [cex_walkLen], ?_⟩
  rw [cex_walkList_four]
  fin_cases j <;> decide

/-- The arm is 1-Lipschitz. -/
theorem cex_isLip : IsLip cexArm := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [cexArm]

/-! ## The arm satisfies the landmark sentence -/

/-- **The counterexample arm satisfies `LandWalk`.** -/
theorem landWalk_cex : LandWalk cexArm 0 [1, 0, 3] := by
  intro r d hd
  -- beyond the third turn no clause fires: the walk's time `4` serves every level of the arm
  have hfar : ∀ k : ℕ, r = k + 3 → False := by
    intro k hk
    have h4 : |cexArm d - walkList 0 [1, 0, 3] 4| ≤ 1 := by
      rw [cex_walkList_four]
      fin_cases d <;> decide
    have := hd 4 (by norm_num [cex_walkLen]) h4
    rw [hk, cex_walkStop_ge] at this
    omega
  match r with
  | 0 =>
      exact ⟨fun _ => d, rfl, by simp [cex_walkStop_zero], fun u hu => absurd hu (by omega),
        fun u hu => absurd hu (by omega)⟩
  | 1 =>
      -- the trigger forces `d ≥ 1`: the arm's first level is served by the walk's time `0`
      have hd1 : 1 ≤ d.val := by
        by_contra hcon
        have hd0 : d = (0 : Fin 3) := Fin.ext (show d.val = 0 by omega)
        have h0 : |cexArm d - walkList 0 [1, 0, 3] 0| ≤ 1 := by rw [hd0]; decide
        have := hd 0 (by norm_num [cex_walkLen]) h0
        rw [cex_walkStop_one] at this
        omega
      refine ⟨fun u => if u = 0 then (0 : Fin 3) else d, by norm_num, by
        simp [cex_walkStop_zero], ?_, ?_⟩
      · intro u hu
        have hu0 : u = 0 := by omega
        subst hu0
        show (0 : ℕ) + (1 - 0) ≤ d.val
        omega
      · intro u hu
        have hu0 : u = 0 := by omega
        subst hu0
        show |(1 : ℤ) - 0| ≤ 1
        decide
  | 2 =>
      -- the trigger forces `d = 2`
      have hd2 : d = (2 : Fin 3) := by
        have hlt := d.isLt
        rcases (show d.val = 0 ∨ d.val = 1 ∨ d.val = 2 by omega) with h | h | h
        · exfalso
          have hd0 : d = (0 : Fin 3) := Fin.ext h
          have h0 : |cexArm d - walkList 0 [1, 0, 3] 0| ≤ 1 := by rw [hd0]; decide
          have := hd 0 (by norm_num [cex_walkLen]) h0
          rw [cex_walkStop_two] at this
          omega
        · exfalso
          have hd1 : d = (1 : Fin 3) := Fin.ext h
          have h1 : |cexArm d - walkList 0 [1, 0, 3] 1| ≤ 1 := by rw [hd1]; decide
          have := hd 1 (by norm_num [cex_walkLen]) h1
          rw [cex_walkStop_two] at this
          omega
        · exact Fin.ext h
      subst hd2
      refine ⟨fun u => if u = 0 then (0 : Fin 3) else if u = 1 then (1 : Fin 3) else (2 : Fin 3),
        by norm_num, by simp [cex_walkStop_zero], ?_, ?_⟩
      · intro u hu
        rcases (show u = 0 ∨ u = 1 by omega) with h | h <;> subst h
        · show (0 : ℕ) + (1 - 0) ≤ 1
          omega
        · show (1 : ℕ) + (2 - 1) ≤ 2
          omega
      · intro u hu
        rcases (show u = 0 ∨ u = 1 by omega) with h | h <;> subst h
        · show |(1 : ℤ) - 0| ≤ 1
          decide
        · show |(2 : ℤ) - 1| ≤ 1
          decide
  | (k + 3) => exact absurd rfl (fun h => hfar k h)

/-! ## The arm does not fold -/

/-- **The counterexample arm does not fold onto the walk.** -/
theorem not_foldsOnto_cex :
    ¬ FoldsOnto cexArm (walkLen 0 [1, 0, 3]) (walkList 0 [1, 0, 3]) := by
  rintro ⟨β, hlen, hstep, hz, hval⟩
  have h0 : β (0 : Fin 3) = 0 := hz _ rfl
  have h01 := hstep (0 : Fin 3) (1 : Fin 3) rfl
  have h12 := hstep (1 : Fin 3) (2 : Fin 3) rfl
  rw [abs_le] at h01 h12
  rw [h0] at h01
  have hb2 : β (2 : Fin 3) ≤ 2 := by
    have h1 : (β (1 : Fin 3) : ℤ) ≤ 1 := by push_cast at h01 ⊢; omega
    have h2 := h12.2
    push_cast at h2 ⊢
    omega
  have hv : |(3 : ℤ) - walkList 0 [1, 0, 3] (β (2 : Fin 3))| ≤ 1 := hval (2 : Fin 3)
  rcases (show β (2 : Fin 3) = 0 ∨ β (2 : Fin 3) = 1 ∨ β (2 : Fin 3) = 2 by omega)
    with h | h | h <;> rw [h] at hv
  · rw [cex_walkList_zero] at hv; norm_num at hv
  · rw [cex_walkList_one] at hv; norm_num at hv
  · rw [cex_walkList_two] at hv; norm_num at hv

/-- **The sufficiency statement of batch 62 is false.** The landmark sentence of a walk of
arbitrary shape does not imply folding. -/
theorem not_landWalkSuffices : ¬ LandWalkSuffices := by
  intro h
  exact not_foldsOnto_cex
    (h 3 (by omega) cexArm 0 [1, 0, 3] cex_isLip (by decide) cex_band landWalk_cex)

/-! ## The corrected sentence -/

/-- **The landmark sentence with the trigger read at the level.** For every turn `r` of the walk
and every position `P` at or after the `r`-th turn that no time serving `f d` precedes, the arm has
a landmark chain ending at a time at the level `walkLevel r`, itself at least `P - walkStop r`
before `d`.

This is `LandWalk` with the two weaknesses the counterexample exploits removed: the trigger is a
position of the walk, not a turn time, and the last gap of the chain is measured to that
position. -/
def LandWalkP {m : ℕ} (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) : Prop :=
  ∀ (r : ℕ) (d : Fin m) (P : ℕ), walkStop s ts r ≤ P →
    (∀ p : ℕ, p < walkLen s ts → |f d - walkList s ts p| ≤ 1 → P ≤ p) →
    ∃ j : ℕ → Fin m, walkStop s ts 0 ≤ (j 0).val ∧
      (∀ u, u < r → (j u).val + (walkStop s ts (u + 1) - walkStop s ts u) ≤ (j (u + 1)).val) ∧
      (j r).val + (P - walkStop s ts r) ≤ d.val ∧
      (∀ u, u ≤ r → |f (j u) - walkLevel s ts u| ≤ 1)

/-- **The corrected sentence is still necessary**, for a walk of any shape: one application of
`foldsOnto_landmarkN` to the chain `walkStop 0 ≤ ⋯ ≤ walkStop r ≤ P`. -/
theorem landWalkP_of_foldsOnto {m : ℕ} {f : Fin m → ℤ} {s : ℤ} {ts : List ℤ}
    (h : FoldsOnto f (walkLen s ts) (walkList s ts)) : LandWalkP f s ts := by
  intro r d P hrP hd
  set q : ℕ → ℕ := fun u => if u ≤ r then walkStop s ts u else P with hq
  have hmono : ∀ u, q u ≤ q (u + 1) := by
    intro u
    by_cases hu' : u ≤ r
    · by_cases hu : u + 1 ≤ r
      · simp only [hq, if_pos hu', if_pos hu]
        exact walkStop_mono s ts u
      · have hur : u = r := by omega
        subst hur
        simp only [hq, if_pos (le_refl u), if_neg hu]
        exact hrP
    · have hu : ¬ u + 1 ≤ r := by omega
      simp only [hq, if_neg hu', if_neg hu]
      exact le_refl P
  have hqr1 : q (r + 1) = P := by simp [hq]
  obtain ⟨j, hjr, hj0, hjgap, hjval⟩ :=
    foldsOnto_landmarkN h d (r + 1) q hmono (by rw [hqr1]; exact hd)
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · simpa [hq] using hj0
  · intro u hu
    have := hjgap u (by omega)
    simpa [hq, if_pos (show u ≤ r by omega), if_pos (show u + 1 ≤ r by omega)] using this
  · have := hjgap r (by omega)
    rw [hjr] at this
    simpa [hq, if_pos (show r ≤ r by omega), if_neg (show ¬ r + 1 ≤ r by omega)] using this
  · intro u hu
    have := hjval u (by omega)
    rw [hq] at this
    simp only [if_pos hu] at this
    rwa [walkList_walkStop] at this

/-- **The corrected sentence excludes the counterexample.** -/
theorem not_landWalkP_cex : ¬ LandWalkP cexArm 0 [1, 0, 3] := by
  intro h
  -- the arm's last level, `3`, is served earliest by the walk's time `4`
  have htrig : ∀ p : ℕ, p < walkLen 0 [1, 0, 3] →
      |cexArm (2 : Fin 3) - walkList 0 [1, 0, 3] p| ≤ 1 → 4 ≤ p := by
    intro p hp hv
    rw [cex_walkLen] at hp
    rw [cexArm_two] at hv
    interval_cases p
    · rw [cex_walkList_zero] at hv; norm_num at hv
    · rw [cex_walkList_one] at hv; norm_num at hv
    · rw [cex_walkList_two] at hv; norm_num at hv
    · rw [cex_walkList_three] at hv; norm_num at hv
    · omega
    · omega
  obtain ⟨j, hj0, hjgap, hjlast, hjval⟩ :=
    h 2 (2 : Fin 3) 4 (by rw [cex_walkStop_two]; omega) htrig
  -- the chain must reach the walk's second turning level two steps before time `2`
  have hgap1 := hjgap 1 (by omega)
  simp only [show (1 : ℕ) + 1 = 2 from rfl, cex_walkStop_one, cex_walkStop_two] at hgap1
  rw [cex_walkStop_two] at hjlast
  have h2 : ((2 : Fin 3) : Fin 3).val = 2 := rfl
  omega


/-! ## The unit leg is needed as well

The corrected sentence is not sufficient for *every* walk either. The witness is a walk with two
unit legs and a ten-time arm, the smallest the search of `probe63.c` finds:

```
walkList 1 [3,2,3,0] :  1  2  3  2  3  2  1  0        (eight times)
turn times           :  0     2  3  4        7
turning levels       :  1     3  2  3        0
arm                  :  0  1  2  1  0  1  2  1  0  -1
```

The arm satisfies `LandWalkP` — one chain, `(0, 2, 3, 6, 9)`, serves every clause — and does not
fold, because each of its three visits to the level `0` pins the fold to the walk's time `0`, and
from there the last level `-1`, which only the walk's time `7` serves, is out of reach.
-/

/-- The arm of the second counterexample: ten times, at the levels `0 1 2 1 0 1 2 1 0 -1`. -/
def cexArm2 : Fin 10 → ℤ := ![0, 1, 2, 1, 0, 1, 2, 1, 0, -1]

theorem cex2_walkLen : walkLen 1 [3, 2, 3, 0] = 8 := rfl

theorem cex2_walkList_zero : walkList 1 [3, 2, 3, 0] 0 = 1 := rfl
theorem cex2_walkList_one : walkList 1 [3, 2, 3, 0] 1 = 2 := rfl
theorem cex2_walkList_two : walkList 1 [3, 2, 3, 0] 2 = 3 := rfl
theorem cex2_walkList_three : walkList 1 [3, 2, 3, 0] 3 = 2 := rfl
theorem cex2_walkList_four : walkList 1 [3, 2, 3, 0] 4 = 3 := rfl
theorem cex2_walkList_seven : walkList 1 [3, 2, 3, 0] 7 = 0 := rfl

theorem cex2_walkStop_one : walkStop 1 [3, 2, 3, 0] 1 = 2 := rfl
theorem cex2_walkStop_two : walkStop 1 [3, 2, 3, 0] 2 = 3 := rfl
theorem cex2_walkStop_three : walkStop 1 [3, 2, 3, 0] 3 = 4 := rfl

/-- Beyond the fourth turn the walk stands still, at its time `7`. -/
theorem cex2_walkStop_ge (k : ℕ) : walkStop 1 [3, 2, 3, 0] (k + 4) = 7 := by
  simp [walkStop]

/-- Beyond the fourth turn the walk is at the level `0`. -/
theorem cex2_walkLevel_ge (k : ℕ) : walkLevel 1 [3, 2, 3, 0] (k + 4) = 0 := by
  simp [walkLevel]

/-- Every turn after the first is at the walk's time two or later. -/
theorem cex2_walkStop_ge_two (r : ℕ) (hr : 1 ≤ r) : 2 ≤ walkStop 1 [3, 2, 3, 0] r := by
  match r with
  | 1 => exact le_of_eq cex2_walkStop_one.symm
  | 2 => rw [cex2_walkStop_two]; omega
  | 3 => rw [cex2_walkStop_three]; omega
  | (k + 4) => rw [cex2_walkStop_ge]; omega

/-- Every level of the second arm is served by the walk. -/
theorem cex2_band (j : Fin 10) : ∃ p : ℕ, p < walkLen 1 [3, 2, 3, 0] ∧
    |cexArm2 j - walkList 1 [3, 2, 3, 0] p| ≤ 1 := by
  by_cases h9 : cexArm2 j = -1
  · exact ⟨7, by norm_num [cex2_walkLen], by rw [h9, cex2_walkList_seven]; decide⟩
  · refine ⟨0, by norm_num [cex2_walkLen], ?_⟩
    rw [cex2_walkList_zero]
    fin_cases j <;> revert h9 <;> decide

/-- The second arm is 1-Lipschitz. -/
theorem cex2_isLip : IsLip cexArm2 := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [cexArm2]

/-- **The second arm satisfies the corrected sentence.** -/
theorem landWalkP_cex2 : LandWalkP cexArm2 1 [3, 2, 3, 0] := by
  intro r d P hrP hd
  refine ⟨fun u => if u = 0 then (0 : Fin 10) else if u = 1 then (2 : Fin 10)
    else if u = 2 then (3 : Fin 10) else if u = 3 then (6 : Fin 10) else (9 : Fin 10),
    Nat.le_refl 0, ?_, ?_, ?_⟩
  · -- the gaps of the chain are the walk's own
    intro u _
    match u with
    | 0 => show (0 : ℕ) + (2 - 0) ≤ 2; omega
    | 1 => show (2 : ℕ) + (3 - 2) ≤ 3; omega
    | 2 => show (3 : ℕ) + (4 - 3) ≤ 6; omega
    | 3 => show (6 : ℕ) + (7 - 4) ≤ 9; omega
    | (k + 4) =>
        show (9 : ℕ) + (walkStop 1 [3, 2, 3, 0] (k + 4 + 1) - walkStop 1 [3, 2, 3, 0] (k + 4)) ≤ 9
        rw [show k + 4 + 1 = (k + 1) + 4 by omega, cex2_walkStop_ge, cex2_walkStop_ge]
  · -- the last landmark is far enough before the time `d`
    by_cases h9 : cexArm2 d = -1
    · have hdv : d.val = 9 := by fin_cases d <;> revert h9 <;> decide
      have hP7 : P ≤ 7 := hd 7 (by norm_num [cex2_walkLen]) (by rw [h9, cex2_walkList_seven]; decide)
      rw [hdv]
      match r with
      | 0 => show (0 : ℕ) + (P - 0) ≤ 9; omega
      | 1 =>
          have := hrP
          rw [cex2_walkStop_one] at this ⊢
          show (2 : ℕ) + (P - 2) ≤ 9
          omega
      | 2 =>
          have := hrP
          rw [cex2_walkStop_two] at this ⊢
          show (3 : ℕ) + (P - 3) ≤ 9
          omega
      | 3 =>
          have := hrP
          rw [cex2_walkStop_three] at this ⊢
          show (6 : ℕ) + (P - 4) ≤ 9
          omega
      | (k + 4) =>
          show (9 : ℕ) + (P - walkStop 1 [3, 2, 3, 0] (k + 4)) ≤ 9
          rw [cex2_walkStop_ge]
          omega
    · -- every other level of the arm is served by the walk's own first time, so `P = 0`
      have hP0 : P = 0 := by
        have := hd 0 (by norm_num [cex2_walkLen])
          (by rw [cex2_walkList_zero]; fin_cases d <;> revert h9 <;> decide)
        omega
      have hr0 : r = 0 := by
        by_contra hc
        have := cex2_walkStop_ge_two r (by omega)
        omega
      subst hr0
      show (0 : ℕ) + (P - 0) ≤ d.val
      omega
  · -- the chain's levels are the walk's turning levels
    intro u _
    match u with
    | 0 => show |(0 : ℤ) - 1| ≤ 1; decide
    | 1 => show |(2 : ℤ) - 3| ≤ 1; decide
    | 2 => show |(1 : ℤ) - 2| ≤ 1; decide
    | 3 => show |(2 : ℤ) - 3| ≤ 1; decide
    | (k + 4) =>
        show |(-1 : ℤ) - walkLevel 1 [3, 2, 3, 0] (k + 4)| ≤ 1
        rw [cex2_walkLevel_ge]
        decide

/-- **The second arm does not fold.** -/
theorem not_foldsOnto_cex2 :
    ¬ FoldsOnto cexArm2 (walkLen 1 [3, 2, 3, 0]) (walkList 1 [3, 2, 3, 0]) := by
  rintro ⟨β, hlen, hstep, hz, hval⟩
  have h0 : β (0 : Fin 10) = 0 := hz _ rfl
  have s01 := hstep (0 : Fin 10) (1 : Fin 10) rfl
  have s12 := hstep (1 : Fin 10) (2 : Fin 10) rfl
  have s23 := hstep (2 : Fin 10) (3 : Fin 10) rfl
  have s34 := hstep (3 : Fin 10) (4 : Fin 10) rfl
  have s45 := hstep (4 : Fin 10) (5 : Fin 10) rfl
  have s56 := hstep (5 : Fin 10) (6 : Fin 10) rfl
  have s67 := hstep (6 : Fin 10) (7 : Fin 10) rfl
  have s78 := hstep (7 : Fin 10) (8 : Fin 10) rfl
  have s89 := hstep (8 : Fin 10) (9 : Fin 10) rfl
  rw [abs_le] at s01 s12 s23 s34 s45 s56 s67 s78 s89
  -- the arm's third time at the level `0` pins the fold to the walk's time `0`
  have hb4 : β (4 : Fin 10) = 0 := by
    have hle : β (4 : Fin 10) ≤ 4 := by omega
    have hv : |(0 : ℤ) - walkList 1 [3, 2, 3, 0] (β (4 : Fin 10))| ≤ 1 := hval (4 : Fin 10)
    rcases (show β (4 : Fin 10) = 0 ∨ β (4 : Fin 10) = 1 ∨ β (4 : Fin 10) = 2 ∨
        β (4 : Fin 10) = 3 ∨ β (4 : Fin 10) = 4 by omega) with h | h | h | h | h
    · exact h
    · rw [h, cex2_walkList_one] at hv; norm_num at hv
    · rw [h, cex2_walkList_two] at hv; norm_num at hv
    · rw [h, cex2_walkList_three] at hv; norm_num at hv
    · rw [h, cex2_walkList_four] at hv; norm_num at hv
  have hb8 : β (8 : Fin 10) = 0 := by
    have hle : β (8 : Fin 10) ≤ 4 := by omega
    have hv : |(0 : ℤ) - walkList 1 [3, 2, 3, 0] (β (8 : Fin 10))| ≤ 1 := hval (8 : Fin 10)
    rcases (show β (8 : Fin 10) = 0 ∨ β (8 : Fin 10) = 1 ∨ β (8 : Fin 10) = 2 ∨
        β (8 : Fin 10) = 3 ∨ β (8 : Fin 10) = 4 by omega) with h | h | h | h | h
    · exact h
    · rw [h, cex2_walkList_one] at hv; norm_num at hv
    · rw [h, cex2_walkList_two] at hv; norm_num at hv
    · rw [h, cex2_walkList_three] at hv; norm_num at hv
    · rw [h, cex2_walkList_four] at hv; norm_num at hv
  -- and the last level is served only by the walk's last time
  have hv9 : |(-1 : ℤ) - walkList 1 [3, 2, 3, 0] (β (9 : Fin 10))| ≤ 1 := hval (9 : Fin 10)
  rcases (show β (9 : Fin 10) = 0 ∨ β (9 : Fin 10) = 1 by omega) with h | h
  · rw [h, cex2_walkList_zero] at hv9; norm_num at hv9
  · rw [h, cex2_walkList_one] at hv9; norm_num at hv9

/-- **The unit-leg hypothesis of `LandWalkPSuffices` cannot be dropped.** Without it the corrected
sentence is not sufficient either: the ten-time arm `cexArm2` satisfies `LandWalkP` on the walk of
the turning levels `[3, 2, 3, 0]` from `1`, whose second and third legs are one step long, and does
not fold onto it. -/
theorem not_landWalkP_suffices_without_noUnitLeg :
    ¬ (∀ (m : ℕ) (hm : 0 < m) (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ),
        IsLip f → |f ⟨0, hm⟩ - s| ≤ 1 →
        (∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) →
        LandWalkP f s ts →
        FoldsOnto f (walkLen s ts) (walkList s ts)) := by
  intro h
  exact not_foldsOnto_cex2
    (h 10 (by omega) cexArm2 1 [3, 2, 3, 0] cex2_isLip (by decide) cex2_band landWalkP_cex2)

/-! ## The corrected sufficiency, stated -/

/-- Every leg of the walk is at least two times long: no turning level of `ts` is one step from
its predecessor. This is what the four-leg window `M + 3 ≤ K`, `M ≤ P - 2`, `K ≤ H - 1` gives the
engine of `HPC/Fold/Leg4Land.lean`, and the search of `probe63.c` finds no counterexample to the
corrected sentence's sufficiency under it. -/
def NoUnitLeg : ℤ → List ℤ → Prop
  | _, [] => True
  | s, t :: ts => 2 ≤ (t - s).natAbs ∧ NoUnitLeg t ts

/-- **The corrected sufficiency statement.** For a walk with no unit leg, the corrected landmark
sentence `LandWalkP` implies folding.

This is what `LandWalkSuffices` should have said; `not_landWalkSuffices` refutes the version
without either repair, and `probe63.c` finds a counterexample to it when the unit-leg hypothesis is
dropped. Its proof — the induction of `gseq4_invLand` carried over `walkList s ts` — is not in this
batch.

**Batch 64 refutes this statement too** (`not_landWalkPSuffices`, `HPC/Fold/LandWalkFail64.lean`):
a thirteen-time arm on the walk of the turning levels `[3, 1, 4]` from `0`, whose legs are three,
two and three steps long, satisfies `LandWalkP` and does not fold. The statement is kept as the
batch-63 delivery states it; what the wider search of `probe64.c` leaves standing is
`LandWalkP3Suffices`, the same with every leg at least three steps long. -/
def LandWalkPSuffices : Prop :=
  ∀ (m : ℕ) (hm : 0 < m) (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ),
    IsLip f →
    |f ⟨0, hm⟩ - s| ≤ 1 →
    NoUnitLeg s ts →
    (∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) →
    LandWalkP f s ts →
    FoldsOnto f (walkLen s ts) (walkList s ts)

/-- **With the corrected sufficiency the corrected sentence is folding**, for a walk of any shape
with no unit leg; necessity is `landWalkP_of_foldsOnto`. -/
theorem landWalkP_iff_foldsOnto_of_suffices (h : LandWalkPSuffices) {m : ℕ} (hm : 0 < m)
    (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) (hlip : IsLip f) (h0 : |f ⟨0, hm⟩ - s| ≤ 1)
    (hleg : NoUnitLeg s ts)
    (hband : ∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) :
    LandWalkP f s ts ↔ FoldsOnto f (walkLen s ts) (walkList s ts) :=
  ⟨fun hl => h m hm f s ts hlip h0 hleg hband hl, landWalkP_of_foldsOnto⟩

end HPC.Fold
