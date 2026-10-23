import HPC.Fold.LandTri

/-!
# The crossing at `L + 5`, and the walk it asks for

Batch 60 proved the arm-only half of exhaustiveness at the branch `L + 5` (`leg4Land_tri`,
`HPC/Fold/LandTri.lean`): every arm of the branch satisfies the exact criterion of one of

```
w8 : direct    (P, K, M) = (L+5, L+8, L+1)     L+4 → L+8 → L+1 → L+8 → L+1
w3 : reflected (P, K, M) = (L+4, L+6, L+1)     L+6 → L+3 → L+8 → L+1 → L+8
wb : reflected (P, K, M) = (L+4, L+6, L+2)     L+6 → L+3 → L+7 → L+1 → L+8
```

and reduced the branch to the *crossings*, the basepoints whose two arms are served by different
walks of the list (`Leg4TriCrossL5`, and against a list of five `Leg4FiveCrossL5`).

The census of batch 61 (`census-batch61.c`) reads the crossings of the corpus and finds that one
further walk serves **both arms of every one of them**:

```
w71 : direct   (P, K, M) = (L+5, L+7, L+1)     L+4 → L+7 → L+1 → L+8 → L+1
```

This file adds it to the list — `Leg4QuadCrossL5` and `s3_span_nine_mid5_of_leg4QuadCrossL5` — and
proves what the two sides of a crossing already owe that walk.

## What `w71` asks, and what each side of a crossing already has

Inside the band `[L, L + 9]` the landmark sentence of `w71` is two clauses (its deep clause
triggers below `L`, so it is vacuous):

* **floor.** Before every descent to `L + 2` or below, a time at `L + 6` or above, at index at
  least `3` and at least `L + 6 - f d` steps earlier.
* **ceiling.** Before every ascent to `L + 9`, a time at `L + 6` or above and, six steps later,
  one at `L + 2` or below, itself `f d - L - 2` steps before the ascent.

* `leg4Land_w71_floor_of_w8`: an arm served by `w8` has the floor clause outright — `w8` asks for
  the same landmark one level higher, one index later and one step earlier. So **the `w8` side of
  a crossing owes `w71` only its ceiling clause** (`leg4Land_w71_of_w8_of_ceil`).
* `land_w71_floor_low1_of_wb`, `land_w71_floor_low1_of_w3`: an arm served by `wb` or by `w3` has
  the floor clause **at its descents to `L + 1`** — the ceiling clause of those walks, read on the
  unreflected arm, is exactly a time at `L + 6` or above the right distance before the descent. So
  the other side of a crossing owes `w71` only its descents to *exactly* `L + 2` and its ascents
  to `L + 9` (`leg4Land_w71_of_wb_of_rest`).

Neither implication is unconditional: the exhaustive arm probe `probe61.c` (log `probe61.log`)
finds 1 590 250 arms of length at most sixteen served by `w8` alone and not by `w71` — all of them
failing its ceiling clause — and 1 034 served by `wb` alone and not by `w71`. What the census says
is that at a *crossing*, where the two arms sit at one basepoint of a faithful pair, the missing
clauses hold; that pairing is what `Leg4QuadCrossL5` still asks for.
-/

namespace HPC.Fold

section Arm

variable {m : ℕ} {f : Fin m → ℤ} {L : ℤ}

/-- **The `w8` side of a crossing already has the floor clause of `w71`.** The floor clause of
`w8` asks for a time at `L + 7` or above at index at least four and at least `L + 7 - f d` steps
before the descent; `w71` asks for one at `L + 6` or above at index at least three and at least
`L + 6 - f d` steps before it. -/
theorem leg4Land_w71_floor_of_w8 (h8 : Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5)) :
    ∀ d : Fin m, f d ≤ L + 2 → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (L + 6 - f d) ≤ (d.val : ℤ) ∧ L + 6 ≤ f j := by
  intro d hd
  obtain ⟨j, h1, h2, h3⟩ := h8.1 d (by omega)
  exact ⟨j, by omega, by omega, by omega⟩

/-- **The `w8` side of a crossing owes `w71` only its ceiling clause.** -/
theorem leg4Land_w71_of_w8_of_ceil (hL : ∀ j, L ≤ f j)
    (h8 : Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5))
    (hceil : ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ f j ∧ f k ≤ L + 2) :
    Leg4Land f (L + 9) (L + 7) (L + 1) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hceil d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **An arm served by `wb` has the floor clause of `w71` at its descents to `L + 1`.** The
ceiling clause of `wb`, read on the unreflected arm, gives a time at `L + 6` or above exactly
`L + 6 - f d` steps or more before the descent, at index at least seven. -/
theorem land_w71_floor_low1_of_wb
    (hb : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4)) :
    ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (L + 6 - f d) ≤ (d.val : ℤ) ∧ L + 6 ≤ f j := by
  intro d hd
  have htrig : L + 6 + 2 ≤ armRefl (L + (L + 9)) f d := by
    simp only [armRefl_apply]
    omega
  obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hb.2.2 d htrig
  simp only [armRefl_apply] at h4 h5 h3
  exact ⟨k, by omega, by omega, by omega⟩

/-- **The same for an arm served by `w3`**, whose ceiling clause asks for a time at `L + 7` or
above. -/
theorem land_w71_floor_low1_of_w3
    (h3 : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 1) (L + 4)) :
    ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (L + 6 - f d) ≤ (d.val : ℤ) ∧ L + 6 ≤ f j := by
  intro d hd
  have htrig : L + 6 + 2 ≤ armRefl (L + (L + 9)) f d := by
    simp only [armRefl_apply]
    omega
  obtain ⟨j, k, h1, h2, h3', h4, h5⟩ := h3.2.2 d htrig
  simp only [armRefl_apply] at h4 h5 h3'
  exact ⟨k, by omega, by omega, by omega⟩

/-- **The `wb` side of a crossing owes `w71` only its descents to exactly `L + 2` and its ascents
to `L + 9`.** -/
theorem leg4Land_w71_of_wb_of_rest (hL : ∀ j, L ≤ f j)
    (hb : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : ∀ d : Fin m, f d = L + 2 → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 4 ≤ (d.val : ℤ) ∧ L + 6 ≤ f j)
    (hceil : ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ f j ∧ f k ≤ L + 2) :
    Leg4Land f (L + 9) (L + 7) (L + 1) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases eq_or_lt_of_le hd with heq | hlt
    · obtain ⟨j, h1, h2, h3⟩ := hmid d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · obtain ⟨j, h1, h2, h3⟩ := land_w71_floor_low1_of_wb hb d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hceil d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

end Arm

/-! ## The list of four -/

/-- The window of `w71`. -/
theorem leg4Window_w71 (L : ℤ) : Leg4Window L (L + 9) (L + 7) (L + 1) (L + 5) := by
  unfold Leg4Window; omega

/-- **The crossings of the list of four.** The three walks of `leg4Land_tri` together with
`w71 = L+4 → L+7 → L+1 → L+8 → L+1`. The census of batch 61 measures this residue on the corpus;
every crossing of the three that the census records is served, on both arms, by `w71`. -/
def Leg4QuadCrossL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 1) (L + 5)) →
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c

/-- **The branch `L + 5` from the crossings of the list of four.** -/
theorem s3_span_nine_mid5_of_leg4QuadCrossL5 (h : Leg4QuadCrossL5) {n : ℕ} (ρ σ : Fin n → ℤ)
    (i : Fin n) (L : ℤ) (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  classical
  refine s3_span_nine_mid5_of_leg4TriCrossL5 ?_ ρ σ i L hlip hcr hLb hHb hp hG hT
  intro n' ρ' σ' i' L' hlip' hcr' hLb' hHb' hp' hG' hT' h8 h3 hb
  by_cases h71 : Leg4Land (armG ρ' i') (L' + 9) (L' + 7) (L' + 1) (L' + 5) ∧
      Leg4Land (armT ρ' i') (L' + 9) (L' + 7) (L' + 1) (L' + 5)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ' i' L' (L' + 7) (L' + 1) (L' + 5) hlip' hLb' hHb'
      hp' (leg4Window_w71 L') (by omega) (by omega) h71.1 h71.2
  exact h n' ρ' σ' i' L' hlip' hcr' hLb' hHb' hp' hG' hT' h8 h3 hb h71

/-! ## A crossing is tight for the timing law

The `w8` side of a crossing climbs to `L + 8`; the other side descends to `L + 2` without an
earlier time at `L + 7` or above. Those two events are six levels apart across the basepoint, so
the timing law of `HPC/Fold/Mixed.lean` — a faithful crooked sequence needs `z 6 = 71` links to
span six levels — puts them at least seventy steps apart in total. The census measures the two
indices at every crossing of the corpus and finds their sum **exactly seventy** each time: the
crossings are the configurations that saturate the law. -/

/-- **A climb to `L + 8` on one arm and a descent to `L + 2` on the other are seventy steps
apart.** -/
theorem cross_high8_low2_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (L : ℤ) (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hT : armT ρ i dT ≤ L + 2) (hG : L + 8 ≤ armG ρ i dG) :
    70 ≤ dT.val + dG.val := by
  have h := cross_gap_ge hcr i dT dG 6 (by omega)
  have hz : z 6 = 71 := by decide
  omega

/-- The mirror of `cross_high8_low2_far`. -/
theorem cross_high8_low2_far' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (L : ℤ) (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hG : armG ρ i dG ≤ L + 2) (hT : L + 8 ≤ armT ρ i dT) :
    70 ≤ dT.val + dG.val := by
  have h := cross_gap_le hcr i dT dG 6 (by omega)
  have hz : z 6 = 71 := by decide
  omega

/-- **The other arm of a crossing stays at `L + 3` or above for seventy steps.** Once the forward
arm has climbed to `L + 8` at its step `dG`, the backward arm cannot descend to `L + 2` before its
step `70 - dG`. -/
theorem cross_no_low2_before {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (L : ℤ) (dG : Fin (n - i.val)) (hG : L + 8 ≤ armG ρ i dG) :
    ∀ dT : Fin (i.val + 1), dT.val + dG.val < 70 → L + 3 ≤ armT ρ i dT := by
  intro dT hlt
  by_contra hc
  exact absurd (cross_high8_low2_far hcr i L dT dG (by omega) hG) (by omega)

/-- The mirror of `cross_no_low2_before`. -/
theorem cross_no_low2_before' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (L : ℤ) (dT : Fin (i.val + 1)) (hT : L + 8 ≤ armT ρ i dT) :
    ∀ dG : Fin (n - i.val), dT.val + dG.val < 70 → L + 3 ≤ armG ρ i dG := by
  intro dG hlt
  by_contra hc
  exact absurd (cross_high8_low2_far' hcr i L dT dG (by omega) hT) (by omega)

/-! ## The list of six

The census measures the crossings of the list of four — the three walks of `leg4Land_tri` with
`w71` — at 0 on most of the corpus's generators but at 51, 65 and 116 on three of them; the two
walks of `Leg4FiveCrossL5`, `w72 = L+4 → L+7 → L+2 → L+8 → L+1` and
`w81 = L+5 → L+8 → L+1 → L+8 → L+1`, serve those. Against the list of six the residue is **0 at
every generator of the corpus**: no basepoint of the branch `L + 5` in the corpus is a crossing of

```
w8, w3, wb, w71, w72, w81.
```
-/

/-- **The crossings of the list of six.** `Leg4FiveCrossL5` (`HPC/Fold/LandTri.lean`) with `w71`
added. The census of batch 61 finds this residue empty over the whole corpus. -/
def Leg4SixCrossL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 1) (L + 5)) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 2) (L + 5)) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 6) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 6)) →
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c

/-- **The branch `L + 5` from the crossings of the list of six.** This is the smallest residue the
census knows: it is empty on every generator of the corpus. -/
theorem s3_span_nine_mid5_of_leg4SixCrossL5 (h : Leg4SixCrossL5) {n : ℕ} (ρ σ : Fin n → ℤ)
    (i : Fin n) (L : ℤ) (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  classical
  refine s3_span_nine_mid5_of_leg4FiveCrossL5 ?_ ρ σ i L hlip hcr hLb hHb hp hG hT
  intro n' ρ' σ' i' L' hlip' hcr' hLb' hHb' hp' hG' hT' h8 h3 hb h72 h81
  by_cases h71 : Leg4Land (armG ρ' i') (L' + 9) (L' + 7) (L' + 1) (L' + 5) ∧
      Leg4Land (armT ρ' i') (L' + 9) (L' + 7) (L' + 1) (L' + 5)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ' i' L' (L' + 7) (L' + 1) (L' + 5) hlip' hLb' hHb'
      hp' (leg4Window_w71 L') (by omega) (by omega) h71.1 h71.2
  exact h n' ρ' σ' i' L' hlip' hcr' hLb' hHb' hp' hG' hT' h8 h3 hb h71 h72 h81

end HPC.Fold
