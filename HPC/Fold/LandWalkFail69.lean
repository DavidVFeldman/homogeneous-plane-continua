import HPC.Fold.LandWalkFail65
import HPC.Fold.Decide

/-!
# The clause of batch 66 §2.3 does not restore sufficiency either

Batch 68 ran the engine probe to arms of **forty** times — twice the length of the walks it ranges
over, which is what the batch-64 rule asks — against the corrected landmark sentence `LandWalkP`
**with the clause of batch 66 §2.3 added**: at the clause of the turn `r`, the `r`-th landmark of
the chain comes after every time of the arm whose level is served only by walk positions before the
`r`-th turn. The sweep (`probe68c.log`) found twelve counterexamples, four of which were re-checked
independently by `check68.py`; batch 69 §2.5 asks for one of the four in Lean.

This file writes the clause out (`BeforeClause`, `LandWalkPB`), states the sufficiency of the
strengthened sentence for a walk with no short leg (`LandWalkPB3Suffices`) and for a walk all of
whose legs are at least `k` steps (`LandWalkPBLegSuffices`), and refutes both at the fourth
counterexample of `check68.log`, whose shortest leg is **four**:

```
walkList 0 [5,1,6,0] : 0 1 2 3 4 5 4 3 2 1 2 3 4 5 6 5 4 3 2 1 0    (twenty-one times)
turn times           : 0         5       9         14          20
turning levels       : 0         5       1          6           0
legs                 :    5         4        5            6
cexArm69 (forty times):
  -1 0 -1 0 0 -1 0 0 1 2 2 2 3 2 3 2 3 2 1 2 1 2 2 2 3 4 4 3 2 1 0 -1 0 1 2 3 4 5 6 7
```

* The arm satisfies the strengthened sentence (`landWalkPB_cex69`), with the single chain
  `(0, 25, 29, 38)`: its time `0` at the level `-1` for the walk's start `0`, its time `25` at `4`
  for the turning level `5`, its time `29` at `1` for the turning level `1`, and its time `38` at
  `6` for the turning level `6`. Only the turns `r ≤ 3` have a clause at all here: the walk's fourth
  turn is its time `20`, and no level of the arm is first served that late, so the trigger of the
  clause `r ≥ 4` is never met (`cex69_no_trigger_ge_four`). The added clause of batch 66 is met
  wherever it is asked, and for a blunt reason: **every** level of this arm is served by some walk
  position at or after the walk's third turn (`cex69_served_late`), so no time of the arm is one the
  clause speaks about (`cex69_beforeClause`).
* It does not fold (`not_foldsOnto_cex69`), by the dynamic program of `HPC/Fold/Decide.lean`, which
  decides `FoldsOnto` and is proved to be the definition (`foldsB_iff`); the kernel evaluates it.

So `LandWalkPB3Suffices` and `LandWalkPBLegSuffices 4` are false, and with them
`LandWalkPBLegSuffices k` for every `k ≤ 4`. Together with batch 65 this closes the question the
batch-64 rule left open: the landmark sentence is not made sufficient by the level-aware trigger, by
longer legs, or by the batch-66 clause, and no sufficiency statement is written. Nothing in the
development depends on one — every fold it produces comes from `foldsOnto_leg4_iff_leg4Land`, whose
criterion is exact, and the landmark sentence is used only in its necessary direction.
-/

namespace HPC.Fold

/-! ## The sentence with the clause of batch 66 §2.3 -/

/-- **The clause of batch 66 §2.3**, at the turn `r` and the landmark `jr`: every time of the arm
whose level is served by some position of the walk, but by none at or after the `r`-th turn, comes
before `jr`. -/
def BeforeClause {m : ℕ} (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) (r : ℕ) (jr : Fin m) : Prop :=
  ∀ e : Fin m, (∃ p : ℕ, p < walkLen s ts ∧ |f e - walkList s ts p| ≤ 1) →
    (∀ p : ℕ, p < walkLen s ts → |f e - walkList s ts p| ≤ 1 → p < walkStop s ts r) →
    e.val < jr.val

/-- **The corrected landmark sentence with the clause of batch 66 §2.3 added.** This is `LandWalkP`
with `BeforeClause` asked of the last landmark of the chain — the sentence `probe68.c` tests. -/
def LandWalkPB {m : ℕ} (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ) : Prop :=
  ∀ (r : ℕ) (d : Fin m) (P : ℕ), walkStop s ts r ≤ P →
    (∀ p : ℕ, p < walkLen s ts → |f d - walkList s ts p| ≤ 1 → P ≤ p) →
    ∃ j : ℕ → Fin m, walkStop s ts 0 ≤ (j 0).val ∧
      (∀ u, u < r → (j u).val + (walkStop s ts (u + 1) - walkStop s ts u) ≤ (j (u + 1)).val) ∧
      (j r).val + (P - walkStop s ts r) ≤ d.val ∧
      (∀ u, u ≤ r → |f (j u) - walkLevel s ts u| ≤ 1) ∧
      BeforeClause f s ts r (j r)

/-- The strengthened sentence implies the corrected one: it is the corrected one with a clause
added. -/
theorem landWalkP_of_landWalkPB {m : ℕ} {f : Fin m → ℤ} {s : ℤ} {ts : List ℤ}
    (h : LandWalkPB f s ts) : LandWalkP f s ts := by
  intro r d P hrP hd
  obtain ⟨j, h0, hgap, hlast, hlev, -⟩ := h r d P hrP hd
  exact ⟨j, h0, hgap, hlast, hlev⟩

/-- **Sufficiency of the strengthened sentence, for a walk with no short leg.** This is
`LandWalkP3Suffices` with the batch-66 clause added to its hypothesis; it is what the batch-68
probe tested and is refuted below. -/
def LandWalkPB3Suffices : Prop :=
  ∀ (m : ℕ) (hm : 0 < m) (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ),
    IsLip f →
    |f ⟨0, hm⟩ - s| ≤ 1 →
    NoShortLeg s ts →
    (∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) →
    LandWalkPB f s ts →
    FoldsOnto f (walkLen s ts) (walkList s ts)

/-- **The same with the leg bound raised to `k`.** -/
def LandWalkPBLegSuffices (k : ℕ) : Prop :=
  ∀ (m : ℕ) (hm : 0 < m) (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ),
    IsLip f →
    |f ⟨0, hm⟩ - s| ≤ 1 →
    LegAtLeast k s ts →
    (∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) →
    LandWalkPB f s ts →
    FoldsOnto f (walkLen s ts) (walkList s ts)

/-! ## The witness -/

/-- The arm of the fourth counterexample of `check68.log`: forty times, at the levels
`-1 0 -1 0 0 -1 0 0 1 2 2 2 3 2 3 2 3 2 1 2 1 2 2 2 3 4 4 3 2 1 0 -1 0 1 2 3 4 5 6 7`. -/
def cexArm69 : Fin 40 → ℤ :=
  ![-1, 0, -1, 0, 0, -1, 0, 0, 1, 2, 2, 2, 3, 2, 3, 2, 3, 2, 1, 2,
    1, 2, 2, 2, 3, 4, 4, 3, 2, 1, 0, -1, 0, 1, 2, 3, 4, 5, 6, 7]

theorem cex69_walkLen : walkLen 0 [5, 1, 6, 0] = 21 := rfl

theorem cex69_walkStop_one : walkStop 0 [5, 1, 6, 0] 1 = 5 := rfl
theorem cex69_walkStop_two : walkStop 0 [5, 1, 6, 0] 2 = 9 := rfl
theorem cex69_walkStop_three : walkStop 0 [5, 1, 6, 0] 3 = 14 := rfl

/-- Beyond the fourth turn the walk stands still, at its time `20`. -/
theorem cex69_walkStop_ge (k : ℕ) : walkStop 0 [5, 1, 6, 0] (k + 4) = 20 := by
  simp [walkStop]

theorem cex69_walkStop_of_ge {r : ℕ} (h : 4 ≤ r) : walkStop 0 [5, 1, 6, 0] r = 20 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 4 := ⟨r - 4, by omega⟩
  exact cex69_walkStop_ge k

theorem cex69_walkLevel_zero : walkLevel 0 [5, 1, 6, 0] 0 = 0 := rfl
theorem cex69_walkLevel_one : walkLevel 0 [5, 1, 6, 0] 1 = 5 := rfl
theorem cex69_walkLevel_two : walkLevel 0 [5, 1, 6, 0] 2 = 1 := rfl
theorem cex69_walkLevel_three : walkLevel 0 [5, 1, 6, 0] 3 = 6 := rfl

/-- **Every leg of the walk is at least four times long**: its legs are five, four, five and six. -/
theorem cex69_legAtLeast_four : LegAtLeast 4 0 [5, 1, 6, 0] := by
  refine ⟨by decide, by decide, by decide, by decide, trivial⟩

/-- The walk has no short leg. -/
theorem cex69_noShortLeg : NoShortLeg 0 [5, 1, 6, 0] :=
  (legAtLeast_three_iff_noShortLeg 0 [5, 1, 6, 0]).1
    (legAtLeast_mono (by omega) 0 [5, 1, 6, 0] cex69_legAtLeast_four)

/-- The arm is 1-Lipschitz. -/
theorem cex69_isLip : IsLip cexArm69 := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [cexArm69]

/-- **Every level of the arm is served late**: by a walk position at or after the walk's third
turn, the time `14`. This is what makes the batch-66 clause vacuous here. -/
theorem cex69_served_late (e : Fin 40) :
    ∃ p : ℕ, p < walkLen 0 [5, 1, 6, 0] ∧ 14 ≤ p ∧ |cexArm69 e - walkList 0 [5, 1, 6, 0] p| ≤ 1 := by
  fin_cases e
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨18, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨18, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨18, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨18, by decide, by decide, by decide⟩
  · exact ⟨17, by decide, by decide, by decide⟩
  · exact ⟨17, by decide, by decide, by decide⟩
  · exact ⟨18, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨18, by decide, by decide, by decide⟩
  · exact ⟨17, by decide, by decide, by decide⟩
  · exact ⟨16, by decide, by decide, by decide⟩
  · exact ⟨15, by decide, by decide, by decide⟩
  · exact ⟨14, by decide, by decide, by decide⟩

/-- Every level of the arm is served by the walk. -/
theorem cex69_band (j : Fin 40) : ∃ p : ℕ, p < walkLen 0 [5, 1, 6, 0] ∧
    |cexArm69 j - walkList 0 [5, 1, 6, 0] p| ≤ 1 := by
  obtain ⟨p, h1, -, h3⟩ := cex69_served_late j
  exact ⟨p, h1, h3⟩

/-- **The batch-66 clause holds at every turn `r ≤ 3` and every landmark**, vacuously: no level of
the arm is served only by positions before the walk's `r`-th turn. -/
theorem cex69_beforeClause {r : ℕ} (hr : r ≤ 3) (jr : Fin 40) :
    BeforeClause cexArm69 0 [5, 1, 6, 0] r jr := by
  intro e _ hlate
  obtain ⟨p, hp, hp14, hval⟩ := cex69_served_late e
  have hstop : walkStop 0 [5, 1, 6, 0] r ≤ 14 := by
    interval_cases r
    · exact Nat.zero_le _
    · rw [cex69_walkStop_one]; omega
    · rw [cex69_walkStop_two]; omega
    · rw [cex69_walkStop_three]
  exact absurd (hlate p hp hval) (by omega)

/-! ## The arm satisfies the strengthened sentence -/

/-- **Where the trigger can sit.** For every time `d` of the arm, a position `P` that no serving
position of the walk precedes is at most the first position serving the arm's level there. The
arm's levels and their first serving positions are: `-1, 0, 1` at `0`, `2` at `1`, `3` at `2`,
`4` at `3`, `5` at `4`, `6` at `5` and `7` at `14`; the last of these occurs at the arm's time `39`
alone. -/
theorem cex69_trigger_bound {d : Fin 40} {P : ℕ}
    (hd : ∀ p : ℕ, p < walkLen 0 [5, 1, 6, 0] → |cexArm69 d - walkList 0 [5, 1, 6, 0] p| ≤ 1 →
      P ≤ p) :
    (P ≤ 4 ∧ P ≤ d.val) ∨ (P ≤ 5 ∧ d.val = 38) ∨ (P ≤ 14 ∧ d.val = 39) := by
  fin_cases d
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 0; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 1; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 2; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 3; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 4; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 5; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 6; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 7; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 8; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 9; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 10; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 11; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 12; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 13; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 14; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 15; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 16; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 17; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 18; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 19; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 20; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 21; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 22; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 23; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 24; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 25; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 26; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 27; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 28; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 29; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 30; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 31; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 32; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 33; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 34; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 35; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 36; omega⟩
  · exact Or.inl ⟨by have := hd 4 (by decide) (by decide); omega,
      by have := hd 4 (by decide) (by decide); show P ≤ 37; omega⟩
  · exact Or.inr (Or.inl ⟨by have := hd 5 (by decide) (by decide); omega, rfl⟩)
  · exact Or.inr (Or.inr ⟨by have := hd 14 (by decide) (by decide); omega, rfl⟩)

/-- **No clause beyond the third turn is ever triggered.** The walk's fourth turn is its time `20`,
and every level of the arm is served by its time `14` or earlier. -/
theorem cex69_no_trigger_ge_four {r : ℕ} (hr : 4 ≤ r) (d : Fin 40) (P : ℕ)
    (hrP : walkStop 0 [5, 1, 6, 0] r ≤ P)
    (hd : ∀ p : ℕ, p < walkLen 0 [5, 1, 6, 0] → |cexArm69 d - walkList 0 [5, 1, 6, 0] p| ≤ 1 →
      P ≤ p) : False := by
  rw [cex69_walkStop_of_ge hr] at hrP
  rcases cex69_trigger_bound hd with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

/-- The chain of the counterexample: the arm's times `0`, `25`, `29` and `38`. -/
def cexChain69 : ℕ → Fin 40
  | 0 => 0
  | 1 => 25
  | 2 => 29
  | _ => 38

theorem cex69_chain_level_zero :
    |cexArm69 (cexChain69 0) - walkLevel 0 [5, 1, 6, 0] 0| ≤ 1 := by decide

theorem cex69_chain_level_one :
    |cexArm69 (cexChain69 1) - walkLevel 0 [5, 1, 6, 0] 1| ≤ 1 := by decide

theorem cex69_chain_level_two :
    |cexArm69 (cexChain69 2) - walkLevel 0 [5, 1, 6, 0] 2| ≤ 1 := by decide

theorem cex69_chain_level_three :
    |cexArm69 (cexChain69 3) - walkLevel 0 [5, 1, 6, 0] 3| ≤ 1 := by decide

/-- **The arm satisfies the sentence with the batch-66 clause**, with the single chain
`(0, 25, 29, 38)`. -/
theorem landWalkPB_cex69 : LandWalkPB cexArm69 0 [5, 1, 6, 0] := by
  intro r d P hrP hd
  by_cases hr4 : 4 ≤ r
  · exact absurd (cex69_no_trigger_ge_four hr4 d P hrP hd) (fun h => h.elim)
  have hr : r ≤ 3 := by omega
  have hkey := cex69_trigger_bound hd
  refine ⟨cexChain69, Nat.zero_le _, ?_, ?_, ?_, cex69_beforeClause hr _⟩
  · -- the gaps of the chain are the walk's own
    intro u hu
    interval_cases r
    · omega
    · interval_cases u
      · show (0 : ℕ) + (5 - 0) ≤ 25; omega
    · interval_cases u
      · show (0 : ℕ) + (5 - 0) ≤ 25; omega
      · show (25 : ℕ) + (9 - 5) ≤ 29; omega
    · interval_cases u
      · show (0 : ℕ) + (5 - 0) ≤ 25; omega
      · show (25 : ℕ) + (9 - 5) ≤ 29; omega
      · show (29 : ℕ) + (14 - 9) ≤ 38; omega
  · -- the last landmark is far enough before the time `d`
    interval_cases r
    · show (0 : ℕ) + (P - 0) ≤ d.val
      rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · show (25 : ℕ) + (P - walkStop 0 [5, 1, 6, 0] 1) ≤ d.val
      rw [cex69_walkStop_one] at hrP ⊢
      rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · show (29 : ℕ) + (P - walkStop 0 [5, 1, 6, 0] 2) ≤ d.val
      rw [cex69_walkStop_two] at hrP ⊢
      rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · show (38 : ℕ) + (P - walkStop 0 [5, 1, 6, 0] 3) ≤ d.val
      rw [cex69_walkStop_three] at hrP ⊢
      rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · -- the chain's levels are the walk's turning levels
    intro u hu
    have hu3 : u ≤ 3 := by omega
    interval_cases u
    · exact cex69_chain_level_zero
    · exact cex69_chain_level_one
    · exact cex69_chain_level_two
    · exact cex69_chain_level_three

/-! ## The arm does not fold -/

set_option maxRecDepth 100000 in
/-- **The arm does not fold onto the walk**, by the dynamic program of `HPC/Fold/Decide.lean`,
which decides `FoldsOnto` by its own definition (`foldsB_iff`). -/
theorem not_foldsOnto_cex69 :
    ¬ FoldsOnto cexArm69 (walkLen 0 [5, 1, 6, 0]) (walkList 0 [5, 1, 6, 0]) :=
  not_foldsOnto_of_foldsB (by decide)

/-! ## The refutations -/

/-- **`LandWalkPB3Suffices` is false.** The corrected landmark sentence with the clause of batch 66
§2.3 added is still not sufficient for a walk with no short leg: the forty-time arm `cexArm69`
satisfies it on the walk of the turning levels `[5, 1, 6, 0]` from `0` and does not fold onto it. -/
theorem not_landWalkPB3Suffices : ¬ LandWalkPB3Suffices := by
  intro h
  exact not_foldsOnto_cex69
    (h 40 (by omega) cexArm69 0 [5, 1, 6, 0] cex69_isLip (by decide) cex69_noShortLeg cex69_band
      landWalkPB_cex69)

/-- **`LandWalkPBLegSuffices 4` is false**: the walk of the witness has legs five, four, five and
six. -/
theorem not_landWalkPBLegSuffices_four : ¬ LandWalkPBLegSuffices 4 := by
  intro h
  exact not_foldsOnto_cex69
    (h 40 (by omega) cexArm69 0 [5, 1, 6, 0] cex69_isLip (by decide) cex69_legAtLeast_four
      cex69_band landWalkPB_cex69)

/-- **Raising the leg bound is not the repair here either**: `LandWalkPBLegSuffices k` is false for
every `k ≤ 4`. -/
theorem not_landWalkPBLegSuffices_le_four {k : ℕ} (hk : k ≤ 4) : ¬ LandWalkPBLegSuffices k := by
  intro h
  exact not_landWalkPBLegSuffices_four (fun m hm f s ts hlip h0 hleg hband hlw =>
    h m hm f s ts hlip h0 (legAtLeast_mono hk s ts hleg) hband hlw)

end HPC.Fold
