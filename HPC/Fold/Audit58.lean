import HPC.Fold.PairCheck
import HPC.Fold.Leg4Scan
import HPC.Fold.Decide
import HPC.Fold.ArmReflect
import HPC.Fold.Leaf

/-!
# The criteria of the four-leg engine do not close the branch `L + 5`

Batch 56 gave the branch `L + 5` of span nine a list of walks — the four-leg family of
`foldsOnto_leg4W` (`HPC/Fold/Leg4Wide.lean`) — every member of which comes with a *criterion*:
a base condition and three announcements about the arm, sufficient for the fold. Batch 57 refuted
the route through the reflected valley crossing and named, as the next candidate, the walk
`L+4 → L+7 → L+1 → L+8 → L+1`, whose floor announcement is met by exactly the pair of links the
crookedness clause returns. Question 1 of COMMISSION.md asks whether the branch hypothesis
`LowAt (L + 1) (L + 8)` and `ivSep` supply that walk's other two announcements; question 3 asks
whether the criteria may be read on the interval `[ρ, σ]` of a link rather than on its point `ρ`.

This file answers both with theorems, at two explicit faithful witnesses.

**Question 1: no, and not for any walk of the family.** `Leg4CritClosesL5` is the statement that
at every basepoint of the branch *some* parameter set of the engine's window has its criterion on
both arms, read either directly or through the reflection of each arm. It is false
(`not_leg4CritClosesL5`). The witness is the window of Bing's chain `bing 0 9` (986 links)
beginning at its link 811 and 175 links long, whose first link stands at `L + 5`: its forward arm
fails the criterion of **all twenty-nine** parameter sets of the window, in both orientations.
Its backward arm is the basepoint alone, so nothing is hidden there. In particular the walk
question 1 names fails too (`not_walk47181CritL5`), and the clause of it that fails at this arm
is the floor announcement, at the arm's index five.

**Question 3: the interval reading is not sufficient.** `Leg4CritIvSufficient` is the engine with
every landmark "at `l` or above" read on `σ` and every landmark "at `l` or below" read on `ρ`,
the triggers left on `ρ`. It is false (`not_leg4CritIvSufficient`), and the witness is small: the
nine-link faithful arm

```
ρ = 5 4 5 5 5 4 5 4 3        σ = 5 4 5 6 5 4 5 4 3
```

meets the interval criterion of the parameter set `(P, K, M) = (L + 6, L + 7, L + 4)` — its floor
announcement is served by the link at index three, whose interval reaches `L + 6` although its
`ρ` sits at `L + 5` — and does not fold onto the walk `L+5 → L+7 → L+4 → L+8 → L+1`. So the one
level the model reads from below is not bookkeeping: the engine consumes the point, not the
interval.

Every verdict is put to the kernel. Faithfulness is proved, not assumed, by the search of
`HPC/Fold/PairCheck.lean`; the twenty-nine refutations are the linear scans of
`HPC/Fold/Leg4Scan.lean`, which is what makes a 175-link arm affordable.
-/

set_option maxRecDepth 20000000

namespace HPC.Fold

/-- **The criteria of the wide four-leg engine, offered as a closure of the branch `L + 5`.**
At every basepoint of the branch some parameter set of the engine's window has its criterion on
both arms, read either on the arms or on their reflections in the level `L + (L + 9)`. Refuted by
`not_leg4CritClosesL5`. -/
def Leg4CritClosesL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    ∃ K M P : ℤ, Leg4Window L (L + 9) K M P ∧
      ((Leg4Crit (armG ρ i) (L + 9) K M P ∧ Leg4Crit (armT ρ i) (L + 9) K M P) ∨
        (Leg4Crit (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) K M P ∧
          Leg4Crit (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) K M P))

/-- **The walk question 1 names**, `L+4 → L+7 → L+1 → L+8 → L+1`, which is the engine at
`(P, K, M) = (L + 5, L + 7, L + 1)`: its criterion holds on both arms at every basepoint of the
branch. Refuted by `not_walk47181CritL5`. -/
def Walk47181CritL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    Leg4Crit (armG ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ∧
      Leg4Crit (armT ρ i) (L + 9) (L + 7) (L + 1) (L + 5)

/-- **The engine, read on the interval.** The criterion with its high landmarks read on the upper
end `σ` of a link and its low landmarks on the lower end `ρ`, the triggers left on `ρ`, is still
sufficient for the fold. Refuted by `not_leg4CritIvSufficient`. -/
def Leg4CritIvSufficient : Prop :=
  ∀ (m : ℕ) (ρ σ : Fin m → ℤ) (L Hh K M P : ℤ), 0 < m → IsCrookedIvF ρ σ → IsLip ρ →
    Leg4Window L Hh K M P → (∀ j, L ≤ ρ j) → (∀ j, ρ j ≤ Hh) →
    Leg4CritG ρ ρ σ Hh K M P →
    FoldsOnto ρ (leg4Len L Hh K M P) (leg4Walk L Hh K M P)

namespace Audit58

/-! ## The arm that meets no criterion

The window of Bing's chain `bing 0 9` beginning at its link 811, 175 links long. The chain is thin,
so `σ = ρ`; both are carried as one natural number in base sixteen, the link `i` being the `i`-th
digit.

`ρ`: `5 4 3 4 3 2 3 4 3 4 5 4 3 4 5 4 5 6 5 4 5 4 3 4 5 4 5 6 5 4 5 6 5 6 7 6 5 6 5 4 5 6 5 4 5 4 3 4 5 4 5 6 5 4 5 6 5 6 7 6 5 6 5 4 5 6 5 6 7 6 5 6 7 6 7 8 7 6 7 6 5 6 7 6 5 6 5 4 5 6 5 6 7 6 5 6 5 4 5 6 5 4 5 4 3 4 5 4 5 6 5 4 5 6 5 6 7 6 5 6 5 4 5 6 5 6 7 6 5 6 7 6 7 8 7 6 7 6 5 6 7 6 5 6 5 4 5 6 5 6 7 6 5 6 7 6 7 8 7 6 7 6 5 6 7 6 7 8 7 6 7 8 7 8 9`.
-/

/-- The 175 links of the window, as a base-sixteen numeral. -/
def rhoNat : ℕ := 0x9878767876765676787676567656545656765676787676567656545656765654565454345456545656765654565676567678767656765654565676565456545434545654565676565456545434545654543454343234345

/-- Reading a link off the numeral. -/
def rhoD (i : ℕ) : ℕ := (rhoNat >>> (4 * i)) &&& 15

/-- The point sequence of the pair. -/
def rho175 : Fin 175 → ℤ := PairCheck.rhoOf 175 rhoD

/-- The pair is thin: the upper end of each link is its point. -/
def sig175 : Fin 175 → ℤ := PairCheck.sigOf 175 rhoD

/-- The basepoint: the first link, where `ρ` stands at `L + 5` with `L = 0`. -/
def basept : Fin 175 := ⟨0, by omega⟩

/-- The forward arm at the basepoint: the whole window. -/
abbrev armF : Fin (175 - basept.val) → ℤ := armG rho175 basept

/-- Its reflection in the level `L + (L + 9)`. -/
abbrev armFR : Fin (175 - basept.val) → ℤ := armRefl (0 + (0 + 9)) (armG rho175 basept)

/-! ## The pair is faithful -/

/-- `IsCrookedIvF rho175 sig175`, by the search of `HPC/Fold/PairCheck.lean`. -/
theorem faithful : IsCrookedIvF rho175 sig175 :=
  PairCheck.isCrookedIvF_of_search (n := 175) (lev := 10) (rd := rhoD) (sd := rhoD)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

/-! ## The branch hypotheses -/

theorem band_lo : ∀ t, (0 : ℤ) ≤ rho175 t := by decide

theorem band_hi : ∀ t, rho175 t ≤ 0 + 9 := by decide

theorem base_level : rho175 basept = 0 + 5 := by decide

theorem lowAt_armG : LowAt (armG rho175 basept) (0 + 1) (0 + 8) := by unfold LowAt; decide

theorem lowAt_armT : LowAt (armT rho175 basept) (0 + 1) (0 + 8) := by unfold LowAt; decide

/-! ## No parameter set of the window has its criterion

For each of the twenty-nine parameter sets `(P, K, M)` of the window, and for each of the two
orientations, the clause of the criterion that fails is named, together with the index at which it
fails; the scans of `HPC/Fold/Leg4Scan.lean` do the rest. -/

/-- `(P, K, M) = (3, 6, 1)`: the base clause fails at the index 0. -/
theorem no_dir_3_6_1 : ¬ Leg4Crit armF (0 + 9) 6 1 3 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (3, 6, 1)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_3_6_1 : ¬ Leg4Crit armFR (0 + 9) 6 1 3 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (3, 7, 1)`: the base clause fails at the index 0. -/
theorem no_dir_3_7_1 : ¬ Leg4Crit armF (0 + 9) 7 1 3 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (3, 7, 1)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_3_7_1 : ¬ Leg4Crit armFR (0 + 9) 7 1 3 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (3, 8, 1)`: the base clause fails at the index 0. -/
theorem no_dir_3_8_1 : ¬ Leg4Crit armF (0 + 9) 8 1 3 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (3, 8, 1)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_3_8_1 : ¬ Leg4Crit armFR (0 + 9) 8 1 3 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (4, 6, 1)`: the base clause fails at the index 0. -/
theorem no_dir_4_6_1 : ¬ Leg4Crit armF (0 + 9) 6 1 4 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (4, 6, 1)`, reflected: the deep clause fails at the index 174. -/
theorem no_refl_4_6_1 : ¬ Leg4Crit armFR (0 + 9) 6 1 4 :=
  not_leg4CritG_of_deep ⟨174, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (4, 6, 2)`: the base clause fails at the index 0. -/
theorem no_dir_4_6_2 : ¬ Leg4Crit armF (0 + 9) 6 2 4 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (4, 6, 2)`, reflected: the deep clause fails at the index 174. -/
theorem no_refl_4_6_2 : ¬ Leg4Crit armFR (0 + 9) 6 2 4 :=
  not_leg4CritG_of_deep ⟨174, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (4, 7, 1)`: the base clause fails at the index 0. -/
theorem no_dir_4_7_1 : ¬ Leg4Crit armF (0 + 9) 7 1 4 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (4, 7, 1)`, reflected: the deep clause fails at the index 174. -/
theorem no_refl_4_7_1 : ¬ Leg4Crit armFR (0 + 9) 7 1 4 :=
  not_leg4CritG_of_deep ⟨174, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (4, 7, 2)`: the base clause fails at the index 0. -/
theorem no_dir_4_7_2 : ¬ Leg4Crit armF (0 + 9) 7 2 4 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (4, 7, 2)`, reflected: the deep clause fails at the index 174. -/
theorem no_refl_4_7_2 : ¬ Leg4Crit armFR (0 + 9) 7 2 4 :=
  not_leg4CritG_of_deep ⟨174, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (4, 8, 1)`: the base clause fails at the index 0. -/
theorem no_dir_4_8_1 : ¬ Leg4Crit armF (0 + 9) 8 1 4 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (4, 8, 1)`, reflected: the floor clause fails at the index 75. -/
theorem no_refl_4_8_1 : ¬ Leg4Crit armFR (0 + 9) 8 1 4 :=
  not_leg4CritG_of_floor ⟨75, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (4, 8, 2)`: the base clause fails at the index 0. -/
theorem no_dir_4_8_2 : ¬ Leg4Crit armF (0 + 9) 8 2 4 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (4, 8, 2)`, reflected: the floor clause fails at the index 75. -/
theorem no_refl_4_8_2 : ¬ Leg4Crit armFR (0 + 9) 8 2 4 :=
  not_leg4CritG_of_floor ⟨75, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 6, 1)`: the floor clause fails at the index 5. -/
theorem no_dir_5_6_1 : ¬ Leg4Crit armF (0 + 9) 6 1 5 :=
  not_leg4CritG_of_floor ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 6, 1)`, reflected: the deep clause fails at the index 75. -/
theorem no_refl_5_6_1 : ¬ Leg4Crit armFR (0 + 9) 6 1 5 :=
  not_leg4CritG_of_deep ⟨75, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 6, 2)`: the floor clause fails at the index 5. -/
theorem no_dir_5_6_2 : ¬ Leg4Crit armF (0 + 9) 6 2 5 :=
  not_leg4CritG_of_floor ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 6, 2)`, reflected: the deep clause fails at the index 75. -/
theorem no_refl_5_6_2 : ¬ Leg4Crit armFR (0 + 9) 6 2 5 :=
  not_leg4CritG_of_deep ⟨75, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 6, 3)`: the floor clause fails at the index 5. -/
theorem no_dir_5_6_3 : ¬ Leg4Crit armF (0 + 9) 6 3 5 :=
  not_leg4CritG_of_floor ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 6, 3)`, reflected: the deep clause fails at the index 75. -/
theorem no_refl_5_6_3 : ¬ Leg4Crit armFR (0 + 9) 6 3 5 :=
  not_leg4CritG_of_deep ⟨75, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 7, 1)`: the floor clause fails at the index 5. -/
theorem no_dir_5_7_1 : ¬ Leg4Crit armF (0 + 9) 7 1 5 :=
  not_leg4CritG_of_floor ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 7, 1)`, reflected: the deep clause fails at the index 75. -/
theorem no_refl_5_7_1 : ¬ Leg4Crit armFR (0 + 9) 7 1 5 :=
  not_leg4CritG_of_deep ⟨75, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 7, 2)`: the floor clause fails at the index 5. -/
theorem no_dir_5_7_2 : ¬ Leg4Crit armF (0 + 9) 7 2 5 :=
  not_leg4CritG_of_floor ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 7, 2)`, reflected: the deep clause fails at the index 75. -/
theorem no_refl_5_7_2 : ¬ Leg4Crit armFR (0 + 9) 7 2 5 :=
  not_leg4CritG_of_deep ⟨75, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 7, 3)`: the floor clause fails at the index 5. -/
theorem no_dir_5_7_3 : ¬ Leg4Crit armF (0 + 9) 7 3 5 :=
  not_leg4CritG_of_floor ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 7, 3)`, reflected: the deep clause fails at the index 75. -/
theorem no_refl_5_7_3 : ¬ Leg4Crit armFR (0 + 9) 7 3 5 :=
  not_leg4CritG_of_deep ⟨75, by decide⟩ (by decide) (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 8, 1)`: the floor clause fails at the index 5. -/
theorem no_dir_5_8_1 : ¬ Leg4Crit armF (0 + 9) 8 1 5 :=
  not_leg4CritG_of_floor ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 8, 1)`, reflected: the floor clause fails at the index 34. -/
theorem no_refl_5_8_1 : ¬ Leg4Crit armFR (0 + 9) 8 1 5 :=
  not_leg4CritG_of_floor ⟨34, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 8, 2)`: the floor clause fails at the index 5. -/
theorem no_dir_5_8_2 : ¬ Leg4Crit armF (0 + 9) 8 2 5 :=
  not_leg4CritG_of_floor ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 8, 2)`, reflected: the floor clause fails at the index 34. -/
theorem no_refl_5_8_2 : ¬ Leg4Crit armFR (0 + 9) 8 2 5 :=
  not_leg4CritG_of_floor ⟨34, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 8, 3)`: the floor clause fails at the index 5. -/
theorem no_dir_5_8_3 : ¬ Leg4Crit armF (0 + 9) 8 3 5 :=
  not_leg4CritG_of_floor ⟨5, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (5, 8, 3)`, reflected: the floor clause fails at the index 34. -/
theorem no_refl_5_8_3 : ¬ Leg4Crit armFR (0 + 9) 8 3 5 :=
  not_leg4CritG_of_floor ⟨34, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 6, 1)`: the floor clause fails at the index 2. -/
theorem no_dir_6_6_1 : ¬ Leg4Crit armF (0 + 9) 6 1 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 6, 1)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_6_1 : ¬ Leg4Crit armFR (0 + 9) 6 1 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 6, 2)`: the floor clause fails at the index 2. -/
theorem no_dir_6_6_2 : ¬ Leg4Crit armF (0 + 9) 6 2 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 6, 2)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_6_2 : ¬ Leg4Crit armFR (0 + 9) 6 2 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 6, 3)`: the floor clause fails at the index 2. -/
theorem no_dir_6_6_3 : ¬ Leg4Crit armF (0 + 9) 6 3 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 6, 3)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_6_3 : ¬ Leg4Crit armFR (0 + 9) 6 3 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 7, 1)`: the floor clause fails at the index 2. -/
theorem no_dir_6_7_1 : ¬ Leg4Crit armF (0 + 9) 7 1 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 7, 1)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_7_1 : ¬ Leg4Crit armFR (0 + 9) 7 1 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 7, 2)`: the floor clause fails at the index 2. -/
theorem no_dir_6_7_2 : ¬ Leg4Crit armF (0 + 9) 7 2 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 7, 2)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_7_2 : ¬ Leg4Crit armFR (0 + 9) 7 2 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 7, 3)`: the floor clause fails at the index 2. -/
theorem no_dir_6_7_3 : ¬ Leg4Crit armF (0 + 9) 7 3 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 7, 3)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_7_3 : ¬ Leg4Crit armFR (0 + 9) 7 3 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 7, 4)`: the floor clause fails at the index 2. -/
theorem no_dir_6_7_4 : ¬ Leg4Crit armF (0 + 9) 7 4 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 7, 4)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_7_4 : ¬ Leg4Crit armFR (0 + 9) 7 4 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 8, 1)`: the floor clause fails at the index 2. -/
theorem no_dir_6_8_1 : ¬ Leg4Crit armF (0 + 9) 8 1 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 8, 1)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_8_1 : ¬ Leg4Crit armFR (0 + 9) 8 1 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 8, 2)`: the floor clause fails at the index 2. -/
theorem no_dir_6_8_2 : ¬ Leg4Crit armF (0 + 9) 8 2 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 8, 2)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_8_2 : ¬ Leg4Crit armFR (0 + 9) 8 2 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 8, 3)`: the floor clause fails at the index 2. -/
theorem no_dir_6_8_3 : ¬ Leg4Crit armF (0 + 9) 8 3 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 8, 3)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_8_3 : ¬ Leg4Crit armFR (0 + 9) 8 3 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- `(P, K, M) = (6, 8, 4)`: the floor clause fails at the index 2. -/
theorem no_dir_6_8_4 : ¬ Leg4Crit armF (0 + 9) 8 4 6 :=
  not_leg4CritG_of_floor ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- `(P, K, M) = (6, 8, 4)`, reflected: the base clause fails at the index 0. -/
theorem no_refl_6_8_4 : ¬ Leg4Crit armFR (0 + 9) 8 4 6 :=
  not_leg4CritG_of_base ⟨0, by decide⟩ rfl (by decide)

/-- **No parameter set of the window** has its criterion on the forward arm. -/
theorem no_crit_dir (K M P : ℤ) (hw : Leg4Window 0 (0 + 9) K M P) :
    ¬ Leg4Crit armF (0 + 9) K M P := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hw
  interval_cases P <;> interval_cases K <;> interval_cases M <;>
    first
      | omega
      | exact no_dir_3_6_1
      | exact no_dir_3_7_1
      | exact no_dir_3_8_1
      | exact no_dir_4_6_1
      | exact no_dir_4_6_2
      | exact no_dir_4_7_1
      | exact no_dir_4_7_2
      | exact no_dir_4_8_1
      | exact no_dir_4_8_2
      | exact no_dir_5_6_1
      | exact no_dir_5_6_2
      | exact no_dir_5_6_3
      | exact no_dir_5_7_1
      | exact no_dir_5_7_2
      | exact no_dir_5_7_3
      | exact no_dir_5_8_1
      | exact no_dir_5_8_2
      | exact no_dir_5_8_3
      | exact no_dir_6_6_1
      | exact no_dir_6_6_2
      | exact no_dir_6_6_3
      | exact no_dir_6_7_1
      | exact no_dir_6_7_2
      | exact no_dir_6_7_3
      | exact no_dir_6_7_4
      | exact no_dir_6_8_1
      | exact no_dir_6_8_2
      | exact no_dir_6_8_3
      | exact no_dir_6_8_4

/-- **No parameter set of the window** has its criterion on the reflected arm. -/
theorem no_crit_refl (K M P : ℤ) (hw : Leg4Window 0 (0 + 9) K M P) :
    ¬ Leg4Crit armFR (0 + 9) K M P := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hw
  interval_cases P <;> interval_cases K <;> interval_cases M <;>
    first
      | omega
      | exact no_refl_3_6_1
      | exact no_refl_3_7_1
      | exact no_refl_3_8_1
      | exact no_refl_4_6_1
      | exact no_refl_4_6_2
      | exact no_refl_4_7_1
      | exact no_refl_4_7_2
      | exact no_refl_4_8_1
      | exact no_refl_4_8_2
      | exact no_refl_5_6_1
      | exact no_refl_5_6_2
      | exact no_refl_5_6_3
      | exact no_refl_5_7_1
      | exact no_refl_5_7_2
      | exact no_refl_5_7_3
      | exact no_refl_5_8_1
      | exact no_refl_5_8_2
      | exact no_refl_5_8_3
      | exact no_refl_6_6_1
      | exact no_refl_6_6_2
      | exact no_refl_6_6_3
      | exact no_refl_6_7_1
      | exact no_refl_6_7_2
      | exact no_refl_6_7_3
      | exact no_refl_6_7_4
      | exact no_refl_6_8_1
      | exact no_refl_6_8_2
      | exact no_refl_6_8_3
      | exact no_refl_6_8_4

end Audit58

/-- **The criteria of the four-leg engine do not close the branch `L + 5`.** At the basepoint of
the 175-link faithful window of `Audit58` the forward arm fails the criterion of every parameter
set of the engine's window, in both orientations. -/
theorem not_leg4CritClosesL5 : ¬ Leg4CritClosesL5 := by
  intro h
  obtain ⟨K, M, P, hw, hc⟩ :=
    h 175 Audit58.rho175 Audit58.sig175 Audit58.basept 0 Audit58.faithful Audit58.band_lo
      Audit58.band_hi Audit58.base_level Audit58.lowAt_armG Audit58.lowAt_armT
  rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Audit58.no_crit_dir K M P hw h1
  · exact Audit58.no_crit_refl K M P hw h1

/-- **The walk question 1 names does not have a criterion the branch meets.** Its parameter set is
`(P, K, M) = (L + 5, L + 7, L + 1)`, and at the arm of `Audit58` its floor announcement already
fails. -/
theorem not_walk47181CritL5 : ¬ Walk47181CritL5 := by
  intro h
  exact Audit58.no_dir_5_7_1
    (h 175 Audit58.rho175 Audit58.sig175 Audit58.basept 0 Audit58.faithful Audit58.band_lo
      Audit58.band_hi Audit58.base_level Audit58.lowAt_armG Audit58.lowAt_armT).1

namespace Audit58Iv

/-! ## The arm that meets the interval criterion and does not fold

`ρ`: `5 4 5 5 5 4 5 4 3`; `σ`: `5 4 5 6 5 4 5 4 3`. -/

/-- The nine links of `ρ`. -/
def rhoNat : ℕ := 0x345455545

/-- The nine links of `σ`. -/
def sigNat : ℕ := 0x345456545

def rhoD (i : ℕ) : ℕ := (rhoNat >>> (4 * i)) &&& 15

def sigD (i : ℕ) : ℕ := (sigNat >>> (4 * i)) &&& 15

/-- The point sequence. -/
def rho9 : Fin 9 → ℤ := PairCheck.rhoOf 9 rhoD

/-- The upper end of each link. -/
def sig9 : Fin 9 → ℤ := PairCheck.sigOf 9 sigD

theorem faithful : IsCrookedIvF rho9 sig9 :=
  PairCheck.isCrookedIvF_of_search (n := 9) (lev := 10) (rd := rhoD) (sd := sigD)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

theorem lip : IsLip rho9 := by unfold IsLip; decide

theorem band_lo : ∀ j, (0 : ℤ) ≤ rho9 j := by decide

theorem band_hi : ∀ j, rho9 j ≤ 9 := by decide

theorem window : Leg4Window 0 9 7 4 6 := by decide

/-- The criterion holds with the landmarks read on the interval. -/
theorem crit_interval : Leg4CritG rho9 rho9 sig9 9 7 4 6 := by decide

/-- It fails with the landmarks read on the point: the floor announcement asks for a link at
`L + 6`, and the arm never rises above `L + 5`. -/
theorem not_crit_point : ¬ Leg4Crit rho9 9 7 4 6 := by decide

/-- And the arm does not fold onto the walk. -/
theorem not_folds : ¬ FoldsOnto rho9 (leg4Len 0 9 7 4 6) (leg4Walk 0 9 7 4 6) :=
  not_foldsOnto_of_foldsB (by decide)

end Audit58Iv

/-- **The interval reading of the engine is not sufficient.** The nine-link faithful arm of
`Audit58Iv` meets the criterion of `(P, K, M) = (L + 6, L + 7, L + 4)` with its landmarks read on
the intervals of its links, and does not fold onto the walk that criterion is for. -/
theorem not_leg4CritIvSufficient : ¬ Leg4CritIvSufficient := fun h =>
  Audit58Iv.not_folds
    (h 9 Audit58Iv.rho9 Audit58Iv.sig9 0 9 7 4 6 (by omega) Audit58Iv.faithful Audit58Iv.lip
      Audit58Iv.window Audit58Iv.band_lo Audit58Iv.band_hi Audit58Iv.crit_interval)

end HPC.Fold
