import HPC.Fold.LandWalkFail64

/-!
# `LandWalkP3Suffices` is false as well

Question 4 of batch 64 asked for the induction proving `LandWalkPSuffices`; the answer was a
refutation, and the statement left standing was `LandWalkP3Suffices`
(`HPC/Fold/LandWalkFail64.lean`) — the corrected landmark sentence `LandWalkP` implies folding for
a walk **every one of whose legs is at least three steps long**. The batch-64 report fixed the rule
that made this batch look for a counterexample first: *a sufficiency statement is not written until
the arm probe has covered arms at least twice the walk's length.* The batch-64 search was
exhaustive to arms of **fourteen** times; the walks it ranged over are up to twenty times long, so
the rule was not met.

**The statement is false.** `probe65b.c` searches the same implication by randomised depth-first
descents to arms of **thirty** times — a sample, not a sweep, pruned by the two prefix-monotone
conditions (an arm level no time of the walk serves, and a trigger the sentence leaves unmet, are
both permanent) — and finds 43 counterexamples, 41 at walks whose shortest leg is three and **two
at walks whose shortest leg is four**. Both kinds are proved here: the leg-three witness
`cexArm65` refutes `LandWalkP3Suffices`, and the leg-four witness `cexArmB65` refutes
`LandWalkPLegSuffices 4` — and with it `LandWalkPLegSuffices k` for every `k ≤ 4`
(`not_landWalkPLegSuffices_le_four`). So raising the leg bound is not the repair.

The witness proved here is the smallest of them. The walk is the turning levels `[5, 2, 6]` from
`1`:

```
walkList 1 [5,2,6] :  1  2  3  4  5  4  3  2  3  4  5  6     (twelve times)
turn times         :  0           4        7           11
turning levels     :  1           5        2            6
legs               :     4           3           4
```

and the arm is thirty times long:

```
cexArm65 : 0 0 1 2 2 3 2 2 3 4 5 4 3 2 1 2 1 1 1 2 2 1 0 1 2 3 4 5 6 7
```

* It satisfies the corrected sentence (`landWalkP_cex65`), with the single chain
  `(0, 10, 13, 27)`: the arm's time `0` at the level `0` for the walk's start `1`, its time `10` at
  `5` for the turning level `5`, its time `13` at `2` for the turning level `2`, and its time `27`
  at `5` for the last turning level `6`. The gaps the walk asks for — four, three, four — are met
  with room to spare, and the only trigger that reaches past the first turn is the arm's last
  level `7`, which the walk's time `11` alone serves.
* It does not fold (`not_foldsOnto_cex65`). The arm's time `22` is at the level `0`, which only the
  walk's time `0` serves, so the fold stands at the walk's start there; the arm's last level `7`,
  served only by the walk's time `11`, is seven times later, and `0 + 7 < 11`.

**What is left.** The mechanism is the batch-64 one made longer: the sentence pins the landmarks
to within one level of the walk's turns, and an arm may meet every landmark early and then be
dragged back to a level the walk passes once — here the level `0` at the arm's time `22` — after
which the walk's far end is out of reach. Lengthening the legs does not close it, since the return
is to the walk's *start* and not to a turn. A sufficiency statement for the landmark sentence
therefore needs a hypothesis of a different kind, and this batch does not write one; by the rule
of §0 of the batch-64 report, none should be written until a probe has covered arms of at least
twice the walk's length, which for the walks of `probe65b.c` is forty times and has not been done.
-/

namespace HPC.Fold

/-! ## The witness -/

/-- The arm of the batch-65 counterexample: thirty times, at the levels
`0 0 1 2 2 3 2 2 3 4 5 4 3 2 1 2 1 1 1 2 2 1 0 1 2 3 4 5 6 7`. -/
def cexArm65 : Fin 30 → ℤ :=
  ![0, 0, 1, 2, 2, 3, 2, 2, 3, 4, 5, 4, 3, 2, 1, 2, 1, 1, 1, 2, 2, 1, 0, 1, 2, 3, 4, 5, 6, 7]

theorem cex65_walkLen : walkLen 1 [5, 2, 6] = 12 := rfl

theorem cex65_walkList_zero : walkList 1 [5, 2, 6] 0 = 1 := rfl
theorem cex65_walkList_one : walkList 1 [5, 2, 6] 1 = 2 := rfl
theorem cex65_walkList_two : walkList 1 [5, 2, 6] 2 = 3 := rfl
theorem cex65_walkList_three : walkList 1 [5, 2, 6] 3 = 4 := rfl
theorem cex65_walkList_four : walkList 1 [5, 2, 6] 4 = 5 := rfl
theorem cex65_walkList_five : walkList 1 [5, 2, 6] 5 = 4 := rfl
theorem cex65_walkList_six : walkList 1 [5, 2, 6] 6 = 3 := rfl
theorem cex65_walkList_seven : walkList 1 [5, 2, 6] 7 = 2 := rfl
theorem cex65_walkList_eight : walkList 1 [5, 2, 6] 8 = 3 := rfl
theorem cex65_walkList_nine : walkList 1 [5, 2, 6] 9 = 4 := rfl
theorem cex65_walkList_ten : walkList 1 [5, 2, 6] 10 = 5 := rfl
theorem cex65_walkList_eleven : walkList 1 [5, 2, 6] 11 = 6 := rfl

theorem cex65_walkStop_one : walkStop 1 [5, 2, 6] 1 = 4 := rfl
theorem cex65_walkStop_two : walkStop 1 [5, 2, 6] 2 = 7 := rfl
theorem cex65_walkStop_three : walkStop 1 [5, 2, 6] 3 = 11 := rfl

/-- Beyond the third turn the walk stands still, at its time `11`. -/
theorem cex65_walkStop_ge (k : ℕ) : walkStop 1 [5, 2, 6] (k + 3) = 11 := by
  simp [walkStop]

/-- Beyond the third turn the walk is at the level `6`. -/
theorem cex65_walkLevel_ge (k : ℕ) : walkLevel 1 [5, 2, 6] (k + 3) = 6 := by
  simp [walkLevel]

/-- The walk has no short leg: its legs are four, three and four steps long. -/
theorem cex65_noShortLeg : NoShortLeg 1 [5, 2, 6] := by
  refine ⟨by decide, by decide, by decide, trivial⟩

/-- Every level of the arm is served by the walk. -/
theorem cex65_band (j : Fin 30) : ∃ p : ℕ, p < walkLen 1 [5, 2, 6] ∧
    |cexArm65 j - walkList 1 [5, 2, 6] p| ≤ 1 := by
  fin_cases j
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨11, by decide, by decide⟩

/-- The arm is 1-Lipschitz. -/
theorem cex65_isLip : IsLip cexArm65 := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [cexArm65]

/-! ## The arm satisfies the corrected sentence -/

/-- **Where the trigger can sit.** For every time `d` of the arm, a position `P` that no serving
time of the walk precedes is at most `3`, and at most the arm's own time — except at the arm's
time `28`, at the level `6`, where it is at most `4`, and at the arm's last time, at the level `7`,
whose only serving position is the walk's time `11`. -/
theorem cex65_trigger_bound {d : Fin 30} {P : ℕ}
    (hd : ∀ p : ℕ, p < walkLen 1 [5, 2, 6] → |cexArm65 d - walkList 1 [5, 2, 6] p| ≤ 1 → P ≤ p) :
    (P ≤ 3 ∧ P ≤ d.val) ∨ (P ≤ 4 ∧ 28 ≤ d.val) ∨ (d.val = 29 ∧ P ≤ 11) := by
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
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 5; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 6; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 7; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 8; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 9; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 10; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 11; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 12; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 13; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 14; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 15; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 16; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 17; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 18; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 19; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 20; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 21; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 22; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 23; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 24; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 25; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 26; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 27; omega⟩
  · exact Or.inr (Or.inl ⟨by have := hd 4 (by decide) (by decide); omega, by show (28 : ℕ) ≤ 28; omega⟩)
  · exact Or.inr (Or.inr ⟨rfl, by have := hd 11 (by decide) (by decide); omega⟩)

/-- **The arm satisfies the corrected sentence**, with the single chain `(0, 10, 13, 27)`. -/
theorem landWalkP_cex65 : LandWalkP cexArm65 1 [5, 2, 6] := by
  intro r d P hrP hd
  have hkey := cex65_trigger_bound hd
  have hdlt : d.val ≤ 29 := by have := d.isLt; omega
  refine ⟨fun u => if u = 0 then (0 : Fin 30) else if u = 1 then (10 : Fin 30)
    else if u = 2 then (13 : Fin 30) else (27 : Fin 30), Nat.le_refl 0, ?_, ?_, ?_⟩
  · -- the gaps of the chain are the walk's own
    intro u _
    match u with
    | 0 => show (0 : ℕ) + (4 - 0) ≤ 10; omega
    | 1 => show (10 : ℕ) + (7 - 4) ≤ 13; omega
    | 2 => show (13 : ℕ) + (11 - 7) ≤ 27; omega
    | (k + 3) =>
        show (27 : ℕ) + (walkStop 1 [5, 2, 6] (k + 3 + 1) - walkStop 1 [5, 2, 6] (k + 3)) ≤ 27
        rw [show k + 3 + 1 = (k + 1) + 3 by omega, cex65_walkStop_ge, cex65_walkStop_ge]
  · -- the last landmark is far enough before the time `d`
    match r with
    | 0 =>
        show (0 : ℕ) + (P - 0) ≤ d.val
        rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    | 1 =>
        have h4 : 4 ≤ P := by rw [cex65_walkStop_one] at hrP; exact hrP
        show (10 : ℕ) + (P - walkStop 1 [5, 2, 6] 1) ≤ d.val
        rw [cex65_walkStop_one]
        rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    | 2 =>
        have h7 : 7 ≤ P := by rw [cex65_walkStop_two] at hrP; exact hrP
        show (13 : ℕ) + (P - walkStop 1 [5, 2, 6] 2) ≤ d.val
        rw [cex65_walkStop_two]
        rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    | (k + 3) =>
        have h11 : 11 ≤ P := by rw [cex65_walkStop_ge] at hrP; exact hrP
        show (27 : ℕ) + (P - walkStop 1 [5, 2, 6] (k + 3)) ≤ d.val
        rw [cex65_walkStop_ge]
        rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · -- the chain's levels are the walk's turning levels
    intro u _
    match u with
    | 0 => show |(0 : ℤ) - 1| ≤ 1; decide
    | 1 => show |(5 : ℤ) - 5| ≤ 1; decide
    | 2 => show |(2 : ℤ) - 2| ≤ 1; decide
    | (k + 3) =>
        show |(5 : ℤ) - walkLevel 1 [5, 2, 6] (k + 3)| ≤ 1
        rw [cex65_walkLevel_ge]
        decide

/-! ## The arm does not fold -/

/-- **The arm does not fold onto the walk.** Its time `22`, at the level `0`, is served by the
walk's time `0` alone; the arm's last level `7` is served by the walk's time `11` alone, and seven
times are not eleven. -/
theorem not_foldsOnto_cex65 :
    ¬ FoldsOnto cexArm65 (walkLen 1 [5, 2, 6]) (walkList 1 [5, 2, 6]) := by
  rintro ⟨β, hlen, hstep, hz, hval⟩
  have s2223 := hstep (22 : Fin 30) (23 : Fin 30) rfl
  have s2324 := hstep (23 : Fin 30) (24 : Fin 30) rfl
  have s2425 := hstep (24 : Fin 30) (25 : Fin 30) rfl
  have s2526 := hstep (25 : Fin 30) (26 : Fin 30) rfl
  have s2627 := hstep (26 : Fin 30) (27 : Fin 30) rfl
  have s2728 := hstep (27 : Fin 30) (28 : Fin 30) rfl
  have s2829 := hstep (28 : Fin 30) (29 : Fin 30) rfl
  rw [abs_le] at s2223 s2324 s2425 s2526 s2627 s2728 s2829
  -- the arm's time at the level `0` pins the fold to the walk's start
  have hb22 : β (22 : Fin 30) = 0 := by
    have hlt : β (22 : Fin 30) < walkLen 1 [5, 2, 6] := hlen _
    rw [cex65_walkLen] at hlt
    have hv : |(0 : ℤ) - walkList 1 [5, 2, 6] (β (22 : Fin 30))| ≤ 1 := hval (22 : Fin 30)
    rcases (show β (22 : Fin 30) = 0 ∨ β (22 : Fin 30) = 1 ∨ β (22 : Fin 30) = 2 ∨ β (22 : Fin 30) = 3 ∨ β (22 : Fin 30) = 4 ∨ β (22 : Fin 30) = 5 ∨ β (22 : Fin 30) = 6 ∨ β (22 : Fin 30) = 7 ∨ β (22 : Fin 30) = 8 ∨ β (22 : Fin 30) = 9 ∨ β (22 : Fin 30) = 10 ∨ β (22 : Fin 30) = 11 by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
    · exact h0
    · rw [h1, cex65_walkList_one] at hv; norm_num at hv
    · rw [h2, cex65_walkList_two] at hv; norm_num at hv
    · rw [h3, cex65_walkList_three] at hv; norm_num at hv
    · rw [h4, cex65_walkList_four] at hv; norm_num at hv
    · rw [h5, cex65_walkList_five] at hv; norm_num at hv
    · rw [h6, cex65_walkList_six] at hv; norm_num at hv
    · rw [h7, cex65_walkList_seven] at hv; norm_num at hv
    · rw [h8, cex65_walkList_eight] at hv; norm_num at hv
    · rw [h9, cex65_walkList_nine] at hv; norm_num at hv
    · rw [h10, cex65_walkList_ten] at hv; norm_num at hv
    · rw [h11, cex65_walkList_eleven] at hv; norm_num at hv
  -- and the last level is served only by the walk's last time, which is now out of reach
  have hv29 : |(7 : ℤ) - walkList 1 [5, 2, 6] (β (29 : Fin 30))| ≤ 1 := hval (29 : Fin 30)
  rcases (show β (29 : Fin 30) = 0 ∨ β (29 : Fin 30) = 1 ∨ β (29 : Fin 30) = 2 ∨ β (29 : Fin 30) = 3 ∨ β (29 : Fin 30) = 4 ∨ β (29 : Fin 30) = 5 ∨ β (29 : Fin 30) = 6 ∨ β (29 : Fin 30) = 7 by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [h0, cex65_walkList_zero] at hv29; norm_num at hv29
  · rw [h1, cex65_walkList_one] at hv29; norm_num at hv29
  · rw [h2, cex65_walkList_two] at hv29; norm_num at hv29
  · rw [h3, cex65_walkList_three] at hv29; norm_num at hv29
  · rw [h4, cex65_walkList_four] at hv29; norm_num at hv29
  · rw [h5, cex65_walkList_five] at hv29; norm_num at hv29
  · rw [h6, cex65_walkList_six] at hv29; norm_num at hv29
  · rw [h7, cex65_walkList_seven] at hv29; norm_num at hv29

/-- **`LandWalkP3Suffices` is false.** The corrected landmark sentence is not sufficient for a walk
with no short leg either: the thirty-time arm `cexArm65` satisfies `LandWalkP` on the walk of the
turning levels `[5, 2, 6]` from `1`, whose legs are four, three and four steps long, and does not
fold onto it. -/
theorem not_landWalkP3Suffices : ¬ LandWalkP3Suffices := by
  intro h
  exact not_foldsOnto_cex65
    (h 30 (by omega) cexArm65 1 [5, 2, 6] cex65_isLip (by decide) cex65_noShortLeg cex65_band
      landWalkP_cex65)

/-! ## Raising the leg bound is not the repair -/

/-- Every leg of the walk is at least `k` times long. `LegAtLeast 3` is `NoShortLeg`. -/
def LegAtLeast (k : ℕ) : ℤ → List ℤ → Prop
  | _, [] => True
  | s, t :: ts => k ≤ (t - s).natAbs ∧ LegAtLeast k t ts

/-- A longer leg bound implies a shorter one. -/
theorem legAtLeast_mono {k k' : ℕ} (h : k' ≤ k) :
    ∀ (s : ℤ) (ts : List ℤ), LegAtLeast k s ts → LegAtLeast k' s ts
  | _, [], _ => trivial
  | _, t :: ts, hl => ⟨le_trans h hl.1, legAtLeast_mono h t ts hl.2⟩

/-- `LegAtLeast 3` is exactly `NoShortLeg`. -/
theorem legAtLeast_three_iff_noShortLeg :
    ∀ (s : ℤ) (ts : List ℤ), LegAtLeast 3 s ts ↔ NoShortLeg s ts
  | _, [] => Iff.rfl
  | s, t :: ts => by
      simp only [LegAtLeast, NoShortLeg, and_congr_right_iff]
      exact fun _ => legAtLeast_three_iff_noShortLeg t ts

/-- **The sufficiency statement with the leg bound raised to `k`.** `LandWalkP3Suffices` with
`NoShortLeg` replaced by `LegAtLeast k`; `LandWalkPLegSuffices 3` is `LandWalkP3Suffices`. -/
def LandWalkPLegSuffices (k : ℕ) : Prop :=
  ∀ (m : ℕ) (hm : 0 < m) (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ),
    IsLip f →
    |f ⟨0, hm⟩ - s| ≤ 1 →
    LegAtLeast k s ts →
    (∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) →
    LandWalkP f s ts →
    FoldsOnto f (walkLen s ts) (walkList s ts)

/-- `LandWalkPLegSuffices 3` is `LandWalkP3Suffices`. -/
theorem landWalkPLegSuffices_three_iff : LandWalkPLegSuffices 3 ↔ LandWalkP3Suffices := by
  constructor
  · intro h m hm f s ts hlip h0 hleg hband hlw
    exact h m hm f s ts hlip h0 ((legAtLeast_three_iff_noShortLeg s ts).2 hleg) hband hlw
  · intro h m hm f s ts hlip h0 hleg hband hlw
    exact h m hm f s ts hlip h0 ((legAtLeast_three_iff_noShortLeg s ts).1 hleg) hband hlw

/-! ### The four-leg witness

The second witness of `probe65b.c`: the walk is the turning levels `[5, 1, 6, 1]` from `0`, whose
legs are five, four, five and five steps long, and the arm is again thirty times long.

```
walkList 0 [5,1,6,1] :  0 1 2 3 4 5 4 3 2 1 2 3 4 5 6 5 4 3 2 1    (twenty times)
turn times           :  0         5       9         14        19
turning levels       :  0         5       1          6         1
cexArmB65 : -1 0 0 1 1 2 2 2 3 3 4 4 4 4 3 4 3 3 2 1 0 -1 0 1 2 3 4 5 6 7
```

The mechanism is the one of `cexArm65`: the arm's time `21` returns to the level `-1`, which only
the walk's start serves, and its last level `7` is served only by the walk's time `14`, eight times
later than the fold can reach. -/

/-- The arm of the four-leg counterexample, thirty times at the levels
`-1 0 0 1 1 2 2 2 3 3 4 4 4 4 3 4 3 3 2 1 0 -1 0 1 2 3 4 5 6 7`. -/
def cexArmB65 : Fin 30 → ℤ :=
  ![-1, 0, 0, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 4, 3, 4, 3, 3, 2, 1, 0, -1, 0, 1, 2, 3, 4, 5, 6, 7]

theorem cexB65_walkLen : walkLen 0 [5, 1, 6, 1] = 20 := rfl

theorem cexB65_walkStop_one : walkStop 0 [5, 1, 6, 1] 1 = 5 := rfl
theorem cexB65_walkStop_two : walkStop 0 [5, 1, 6, 1] 2 = 9 := rfl
theorem cexB65_walkStop_three : walkStop 0 [5, 1, 6, 1] 3 = 14 := rfl

/-- Beyond the fourth turn the walk stands still, at its time `19`. -/
theorem cexB65_walkStop_ge (k : ℕ) : walkStop 0 [5, 1, 6, 1] (k + 4) = 19 := by
  simp [walkStop]

theorem cexB65_walkStop_of_ge {r : ℕ} (h : 4 ≤ r) : walkStop 0 [5, 1, 6, 1] r = 19 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 4 := ⟨r - 4, by omega⟩
  exact cexB65_walkStop_ge k

/-- Beyond the fourth turn the walk is at the level `1`. -/
theorem cexB65_walkLevel_ge (k : ℕ) : walkLevel 0 [5, 1, 6, 1] (k + 4) = 1 := by
  simp [walkLevel]

/-- **Every leg of the walk is at least four times long.** -/
theorem cexB65_legAtLeast_four : LegAtLeast 4 0 [5, 1, 6, 1] := by
  refine ⟨by decide, by decide, by decide, by decide, trivial⟩

/-- Every level of the arm is served by the walk. -/
theorem cexB65_band (j : Fin 30) : ∃ p : ℕ, p < walkLen 0 [5, 1, 6, 1] ∧
    |cexArmB65 j - walkList 0 [5, 1, 6, 1] p| ≤ 1 := by
  fin_cases j
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨14, by decide, by decide⟩

/-- The arm is 1-Lipschitz. -/
theorem cexB65_isLip : IsLip cexArmB65 := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [cexArmB65]

/-- **Where the trigger can sit.** For every time `d` of the arm, a position `P` that no serving
time of the walk precedes is at most `4`, and at most the arm's own time — except at the arm's
time `28`, at the level `6`, where it is at most `5`, and at the arm's last time, at the level `7`,
whose only serving position is the walk's time `14`. -/
theorem cexB65_trigger_bound {d : Fin 30} {P : ℕ}
    (hd : ∀ p : ℕ, p < walkLen 0 [5, 1, 6, 1] → |cexArmB65 d - walkList 0 [5, 1, 6, 1] p| ≤ 1 →
      P ≤ p) :
    (P ≤ 4 ∧ P ≤ d.val) ∨ (P ≤ 5 ∧ 28 ≤ d.val) ∨ (d.val = 29 ∧ P ≤ 14) := by
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
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 5; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 6; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 7; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 8; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 9; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 10; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 11; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 12; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 13; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 14; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 15; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 16; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 17; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 18; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 19; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 20; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 21; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 22; omega⟩
  · exact Or.inl ⟨by have := hd 0 (by decide) (by decide); omega,
      by have := hd 0 (by decide) (by decide); show P ≤ 23; omega⟩
  · exact Or.inl ⟨by have := hd 1 (by decide) (by decide); omega,
      by have := hd 1 (by decide) (by decide); show P ≤ 24; omega⟩
  · exact Or.inl ⟨by have := hd 2 (by decide) (by decide); omega,
      by have := hd 2 (by decide) (by decide); show P ≤ 25; omega⟩
  · exact Or.inl ⟨by have := hd 3 (by decide) (by decide); omega,
      by have := hd 3 (by decide) (by decide); show P ≤ 26; omega⟩
  · exact Or.inl ⟨by have := hd 4 (by decide) (by decide); omega,
      by have := hd 4 (by decide) (by decide); show P ≤ 27; omega⟩
  · exact Or.inr (Or.inl ⟨by have := hd 5 (by decide) (by decide); omega,
      by show (28 : ℕ) ≤ 28; omega⟩)
  · exact Or.inr (Or.inr ⟨rfl, by have := hd 14 (by decide) (by decide); omega⟩)

/-- **The arm satisfies the corrected sentence**, with the single chain `(0, 10, 18, 27)`. -/
theorem landWalkP_cexB65 : LandWalkP cexArmB65 0 [5, 1, 6, 1] := by
  intro r d P hrP hd
  have hkey := cexB65_trigger_bound hd
  have hP14 : P ≤ 14 := by rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hrlt : r < 4 := by
    by_contra hcon
    rw [cexB65_walkStop_of_ge (by omega)] at hrP
    omega
  refine ⟨fun u => if u = 0 then (0 : Fin 30) else if u = 1 then (10 : Fin 30)
    else if u = 2 then (18 : Fin 30) else (27 : Fin 30), Nat.le_refl 0, ?_, ?_, ?_⟩
  · -- the gaps of the chain are the walk's own
    intro u hu
    match u with
    | 0 => show (0 : ℕ) + (5 - 0) ≤ 10; omega
    | 1 => show (10 : ℕ) + (9 - 5) ≤ 18; omega
    | 2 => show (18 : ℕ) + (14 - 9) ≤ 27; omega
    | (k + 3) => omega
  · -- the last landmark is far enough before the time `d`
    match r with
    | 0 =>
        show (0 : ℕ) + (P - 0) ≤ d.val
        rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    | 1 =>
        have h5 : 5 ≤ P := by rw [cexB65_walkStop_one] at hrP; exact hrP
        show (10 : ℕ) + (P - walkStop 0 [5, 1, 6, 1] 1) ≤ d.val
        rw [cexB65_walkStop_one]
        rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    | 2 =>
        have h9 : 9 ≤ P := by rw [cexB65_walkStop_two] at hrP; exact hrP
        show (18 : ℕ) + (P - walkStop 0 [5, 1, 6, 1] 2) ≤ d.val
        rw [cexB65_walkStop_two]
        rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    | 3 =>
        have h14 : 14 ≤ P := by rw [cexB65_walkStop_three] at hrP; exact hrP
        show (27 : ℕ) + (P - walkStop 0 [5, 1, 6, 1] 3) ≤ d.val
        rw [cexB65_walkStop_three]
        have := d.isLt
        rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    | (k + 4) => omega
  · -- the chain's levels are the walk's turning levels
    intro u hu
    match u with
    | 0 => show |(-1 : ℤ) - 0| ≤ 1; decide
    | 1 => show |(4 : ℤ) - 5| ≤ 1; decide
    | 2 => show |(2 : ℤ) - 1| ≤ 1; decide
    | 3 => show |(5 : ℤ) - 6| ≤ 1; decide
    | (k + 4) => omega

/-- **The four-leg arm does not fold onto the walk.** Its time `21`, at the level `-1`, is served
by the walk's start alone; its last level `7` is served by the walk's time `14` alone, and eight
times are not fourteen. -/
theorem not_foldsOnto_cexB65 :
    ¬ FoldsOnto cexArmB65 (walkLen 0 [5, 1, 6, 1]) (walkList 0 [5, 1, 6, 1]) := by
  rintro ⟨β, hlen, hstep, hz, hval⟩
  have s2122 := hstep (21 : Fin 30) (22 : Fin 30) rfl
  have s2223 := hstep (22 : Fin 30) (23 : Fin 30) rfl
  have s2324 := hstep (23 : Fin 30) (24 : Fin 30) rfl
  have s2425 := hstep (24 : Fin 30) (25 : Fin 30) rfl
  have s2526 := hstep (25 : Fin 30) (26 : Fin 30) rfl
  have s2627 := hstep (26 : Fin 30) (27 : Fin 30) rfl
  have s2728 := hstep (27 : Fin 30) (28 : Fin 30) rfl
  have s2829 := hstep (28 : Fin 30) (29 : Fin 30) rfl
  rw [abs_le] at s2122 s2223 s2324 s2425 s2526 s2627 s2728 s2829
  -- the arm's return to the level `-1` pins the fold to the walk's start
  have hb21 : β (21 : Fin 30) = 0 := by
    have hlt : β (21 : Fin 30) < walkLen 0 [5, 1, 6, 1] := hlen _
    rw [cexB65_walkLen] at hlt
    have hv : |(-1 : ℤ) - walkList 0 [5, 1, 6, 1] (β (21 : Fin 30))| ≤ 1 := hval (21 : Fin 30)
    interval_cases h : β (21 : Fin 30)
    · rfl
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
  -- and the last level is served only by the walk's time `14`, now out of reach
  have hv29 : |(7 : ℤ) - walkList 0 [5, 1, 6, 1] (β (29 : Fin 30))| ≤ 1 := hval (29 : Fin 30)
  have hb29 : β (29 : Fin 30) ≤ 8 := by omega
  interval_cases h : β (29 : Fin 30)
  · exact absurd hv29 (by decide)
  · exact absurd hv29 (by decide)
  · exact absurd hv29 (by decide)
  · exact absurd hv29 (by decide)
  · exact absurd hv29 (by decide)
  · exact absurd hv29 (by decide)
  · exact absurd hv29 (by decide)
  · exact absurd hv29 (by decide)
  · exact absurd hv29 (by decide)

/-- **Raising the leg bound to four does not repair the statement.** `LandWalkPLegSuffices 4` is
false: the thirty-time arm `cexArmB65` satisfies `LandWalkP` on the walk of the turning levels
`[5, 1, 6, 1]` from `0`, whose legs are five, four, five and five steps long, and does not fold
onto it. -/
theorem not_landWalkPLegSuffices_four : ¬ LandWalkPLegSuffices 4 := by
  intro h
  exact not_foldsOnto_cexB65
    (h 30 (by omega) cexArmB65 0 [5, 1, 6, 1] cexB65_isLip (by decide) cexB65_legAtLeast_four
      cexB65_band landWalkP_cexB65)

/-- **No leg bound of four or less repairs the statement**: `LandWalkPLegSuffices k` is false for
every `k ≤ 4`. In particular `LandWalkPLegSuffices 3`, which is `LandWalkP3Suffices`, is false. -/
theorem not_landWalkPLegSuffices_le_four {k : ℕ} (hk : k ≤ 4) : ¬ LandWalkPLegSuffices k := by
  intro h
  exact not_foldsOnto_cexB65
    (h 30 (by omega) cexArmB65 0 [5, 1, 6, 1] cexB65_isLip (by simp [cexArmB65])
      (legAtLeast_mono hk 0 [5, 1, 6, 1] cexB65_legAtLeast_four) cexB65_band landWalkP_cexB65)

end HPC.Fold

