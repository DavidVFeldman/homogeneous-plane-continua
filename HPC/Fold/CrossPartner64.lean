import HPC.Fold.CrossPair63

/-!
# The partner arm of a crossing: what its own walk gives, and the one clause left

Batch 63 closed the index side of the crossing and reduced the branch `L + 5`, at a crossing whose
band misses the floor, to **the partner's own `w72`** (`s3_span_nine_mid5_of_cross_w72`). Questions
1 and 2 of batch 64 ask where that comes from, and what happens when an arm reaches `L`.

This file answers both, and finds that they have the *same* residue.

## The partner's ceiling clauses are its own

At a crossing one arm is served by `w8` and the other by one of the two reflected walks

```
w3 : reflected (P, K, M) = (L+4, L+6, L+1)     L+6 → L+3 → L+8 → L+1 → L+8
wb : reflected (P, K, M) = (L+4, L+6, L+2)     L+6 → L+3 → L+7 → L+1 → L+8
```

(`leg4Land_tri`). Read on the unreflected arm, the **deep-floor clause of `wb`** fires at exactly
the partner's ascents to `L + 9` and returns, in order, a time at `L + 6` or above and a time at
`L + 2` or below, spaced by six and placed `f d - L - 2` steps before the ascent. That is precisely
the ceiling clause of `w71` — and, a fortiori, of `w72` (`land_w71_ceil_of_wb`,
`land_w72_ceil_of_wb`). So a `wb` partner owes those two walks **no ceiling clause at all**, and by
`land_w71_floor_low1_of_wb` it owes them no floor clause at its descents to `L + 1` either.

What is left is one clause, at one level: the floor clause at the partner's descents to **exactly**
`L + 2`, where no clause of `wb` fires (`g d = L + 7` is below `wb`'s ceiling trigger `L + 8` and
above its floor trigger `L + 1`). `leg4Land_w71_of_wb_of_mid2` and `leg4Land_w72_of_wb_of_mid2`
state the two consequences: with that one clause the `wb` partner satisfies `w71` in full, and —
in a band that misses the floor — `w72` in full.

A `w3` partner is one level away from the same thing: `w3`'s deep-floor clause triggers at
`g d ≤ L - 1`, i.e. at `f d ≥ L + 10`, which is outside the band, so it is vacuous and supplies
nothing; its floor clause at the descents to `L + 1` is all it gives (`land_w71_floor_low1_of_w3`).

## The crossing supplies its own hypothesis

`cross_floor_fail_of_not_w8` records what batch 63 took as an assumption: at a crossing the arm
that is *not* served by `w8` fails `w8`'s **floor** clause at some one descent, because an arm with
that clause is served by `w8` (`leg4Land_w8_of_floor`). One descent serves every ascent of the
other arm, so the hypothesis `hcross` of `leg4Land_w72_of_cross_of_floor_fail` is a consequence of
the crossing and not an extra assumption.

## The mirror, for the crossing whose `w8` side is the backward arm

`cross_peak_valley_core_rev`, `cross_peak_valley_armT'`, `leg4Land_w72_ceil_of_cross_T'` and
`leg4Land_w72_of_cross_of_floor_fail_T` are the batch-63 chain with the two arms exchanged: the
crooked pair is read from the backward arm's ascent to the forward arm's descent, where it comes
out valley-first, which is the order the ceiling clause reads on the backward arm.

## The assembly

`s3_span_nine_mid5_of_cross_offfloor` is the branch at a crossing in a band that misses the floor,
from one named residual fact — `Mid2Floor`, the floor clause at the descents to exactly `L + 2`,
on the partner arm — plus, for a `w3` partner, its ceiling clause. `CrossPartnerRestL5` names the
residue, and `s3_span_nine_mid5_offfloor_of_rest` derives the off-floor half of the branch from it.
-/

namespace HPC.Fold

section Arm

variable {m : ℕ} {f : Fin m → ℤ} {L : ℤ}

/-! ## What a `wb` partner owns -/

/-- **The floor clause at the descents to exactly `L + 2`.** This is the one clause of `w71` and
`w72` that a `wb` arm of the band does not own. -/
def Mid2Floor {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d = L + 2 → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
    (j.val : ℤ) + 4 ≤ (d.val : ℤ) ∧ L + 6 ≤ f j

/-- **The ceiling clause of `w71` is the deep-floor clause of `wb`, read on the unreflected arm.**
`wb`'s deep clause fires at `g d ≤ M - 2`, that is at `f d ≥ L + 9`, and returns three landmarks
`j`, `k`, `l`; its second and third are a time at `L + 6` or above and, six steps later, a time at
`L + 2` or below, placed `f d - L - 2` steps before the ascent — exactly what `w71` asks. -/
theorem land_w71_ceil_of_wb
    (hb : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4)) :
    ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ f j ∧ f k ≤ L + 2 := by
  intro d hd
  have htrig : armRefl (L + (L + 9)) f d ≤ L + 2 - 2 := by
    simp only [armRefl_apply]; omega
  obtain ⟨j, k, l, h1, h2, h3, h4, h5, h6, h7⟩ := hb.2.1 d htrig
  simp only [armRefl_apply] at h4 h5 h6 h7
  exact ⟨k, l, by omega, by omega, by omega, by omega, by omega⟩

/-- **And so the ceiling clause of `w72`**, which asks for the same two landmarks one level
apart. -/
theorem land_w72_ceil_of_wb
    (hb : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4)) :
    ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 3)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ f j ∧ f k ≤ L + 3 := by
  intro d hd
  obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := land_w71_ceil_of_wb hb d hd
  exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **A `wb` arm with the floor clause at `L + 2` satisfies `w71` in full.** -/
theorem leg4Land_w71_of_wb_of_mid2 (hL : ∀ j, L ≤ f j)
    (hb : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor f L) :
    Leg4Land f (L + 9) (L + 7) (L + 1) (L + 5) :=
  leg4Land_w71_of_wb_of_rest hL hb hmid (land_w71_ceil_of_wb hb)

/-- **A `wb` arm of a band that misses the floor, with the floor clause at `L + 2`, satisfies
`w72` in full.** -/
theorem leg4Land_w72_of_wb_of_mid2 (hL : ∀ j, L + 1 ≤ f j)
    (hb : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor f L) :
    Leg4Land f (L + 9) (L + 7) (L + 2) (L + 5) := by
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
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := land_w72_ceil_of_wb hb d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **A `w3` arm with the floor clause at `L + 2` and the ceiling clause satisfies `w71` in
full.** `w3`'s own deep-floor clause triggers at `f d ≥ L + 10` and is vacuous inside the band, so
unlike a `wb` arm it does not own its ceiling. -/
theorem leg4Land_w71_of_w3_of_mid2 (hL : ∀ j, L ≤ f j)
    (h3 : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 1) (L + 4))
    (hmid : Mid2Floor f L)
    (hceil : ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ f j ∧ f k ≤ L + 2) :
    Leg4Land f (L + 9) (L + 7) (L + 1) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases eq_or_lt_of_le hd with heq | hlt
    · obtain ⟨j, h1, h2, h3'⟩ := hmid d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · obtain ⟨j, h1, h2, h3'⟩ := land_w71_floor_low1_of_w3 h3 d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    obtain ⟨j, k, h1, h2, h3', h4, h5⟩ := hceil d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **The same for `w72`**, in a band that misses the floor. -/
theorem leg4Land_w72_of_w3_of_mid2 (hL : ∀ j, L + 1 ≤ f j)
    (h3 : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 1) (L + 4))
    (hmid : Mid2Floor f L)
    (hceil : ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 3)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ f j ∧ f k ≤ L + 3) :
    Leg4Land f (L + 9) (L + 7) (L + 2) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases eq_or_lt_of_le hd with heq | hlt
    · obtain ⟨j, h1, h2, h3'⟩ := hmid d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · obtain ⟨j, h1, h2, h3'⟩ := land_w71_floor_low1_of_w3 h3 d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    obtain ⟨j, k, h1, h2, h3', h4, h5⟩ := hceil d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **What a crossing gives on the arm that `w8` does not serve.** An arm of the band whose every
descent to `L + 2` carries `w8`'s floor landmark *is* served by `w8` (`leg4Land_w8_of_floor`), so
an arm that is not has one descent at which the landmark is missing — and that one descent is what
the pairing argument of batch 63 reads, at every ascent of the other arm. -/
theorem cross_floor_fail_of_not_w8 (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hnot : ¬ Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5)) :
    ∃ d : Fin m, f d ≤ L + 2 ∧
      ¬ ∃ j : Fin m, 4 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + (L + 7 - f d) ≤ (d.val : ℤ) ∧
          L + 7 ≤ f j := by
  classical
  by_contra hc
  push_neg at hc
  exact hnot (leg4Land_w8_of_floor hL hH hc)

/-! ## Every arm of the branch, with the two clauses -/

/-- **The floor clause of `w71` and `w72` at the descents to `L + 1` is free.** Whichever of the
three walks of `leg4Land_tri` serves the arm supplies it: `w8` by `leg4Land_w71_floor_of_w8`,
`w3` and `wb` by their ceiling clauses read on the unreflected arm. -/
theorem land_floor_low1_of_branch (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) (hlow : LowAt f (L + 1) (L + 8)) :
    ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (L + 6 - f d) ≤ (d.val : ℤ) ∧ L + 6 ≤ f j := by
  rcases leg4Land_tri hm hf h0 hL hH hlow with h8 | h3 | hb
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · exact land_w71_floor_low1_of_w3 h3
  · exact land_w71_floor_low1_of_wb hb

/-- **An arm of the branch with the two clauses satisfies `w71` in full.** The floor clause at the
descents to `L + 1` is the trichotomy's, the deep-floor clause triggers below the band, and what
is left is the floor clause at the descents to exactly `L + 2` and the ceiling clause. -/
theorem leg4Land_w71_of_branch_of_mid2_of_ceil (hm : 0 < m) (hf : IsLip f)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f (L + 1) (L + 8)) (hmid : Mid2Floor f L)
    (hceil : ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ f j ∧ f k ≤ L + 2) :
    Leg4Land f (L + 9) (L + 7) (L + 1) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases eq_or_lt_of_le hd with heq | hlt
    · obtain ⟨j, h1, h2, h3⟩ := hmid d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · obtain ⟨j, h1, h2, h3⟩ := land_floor_low1_of_branch hm hf h0 hL hH hlow d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hceil d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **The same for `w72`**, in a band that misses the floor. -/
theorem leg4Land_w72_of_branch_of_mid2_of_ceil (hm : 0 < m) (hf : IsLip f)
    (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L + 1 ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f (L + 1) (L + 8)) (hmid : Mid2Floor f L)
    (hceil : ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 3)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ f j ∧ f k ≤ L + 3) :
    Leg4Land f (L + 9) (L + 7) (L + 2) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases eq_or_lt_of_le hd with heq | hlt
    · obtain ⟨j, h1, h2, h3⟩ := hmid d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · obtain ⟨j, h1, h2, h3⟩ :=
        land_floor_low1_of_branch hm hf h0 (fun j => (hL j).trans' (by omega)) hH hlow d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hceil d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-! ## The deep-floor clause of `w72`, where the band reaches the floor -/

/-- **The deep-floor clause of `w72`**, written out: before every descent to `L`, a time at
`L + 6` or above, five steps later one at `L + 3` or below, six steps after that one at `L + 7` or
above, itself `L + 7 - f d` steps before the descent. Inside a band that misses the floor it is
vacuous; where the band reaches `L` it is the clause `w72` has and `w71` has not. -/
def Deep72 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L → ∃ j k l : Fin m, 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
    (k.val : ℤ) + 6 ≤ (l.val : ℤ) ∧ (l.val : ℤ) + (L + 7 - f d) ≤ (d.val : ℤ) ∧
    L + 6 ≤ f j ∧ f k ≤ L + 3 ∧ L + 7 ≤ f l

/-- **A `wb` arm with the floor clause at `L + 2` and the deep-floor clause satisfies `w72` in
full**, with no hypothesis on the floor of the band. -/
theorem leg4Land_w72_of_wb_of_mid2_of_deep
    (hb : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor f L) (hdeep : Deep72 f L) :
    Leg4Land f (L + 9) (L + 7) (L + 2) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases eq_or_lt_of_le hd with heq | hlt
    · obtain ⟨j, h1, h2, h3⟩ := hmid d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · obtain ⟨j, h1, h2, h3⟩ := land_w71_floor_low1_of_wb hb d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    obtain ⟨j, k, l, h1, h2, h3, h4, h5, h6, h7⟩ := hdeep d (by omega)
    exact ⟨j, k, l, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := land_w72_ceil_of_wb hb d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

end Arm

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## The crooked pair read from a high index to a later low one -/

/-- **`cross_peak_valley_core'` with the two ends exchanged.** From a link at `L + 9` or above and
a *later* link at `L + 2` or below, crookedness puts between them first a **valley** at `ρ a + 1`
or below and then a **peak**, whose interval reaches `L + 8`; the timing law spaces the four
indices exactly as before. Read on the backward arm this is peak-then-valley, which is the order
the ceiling clause asks for. -/
theorem cross_peak_valley_core_rev (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hba : b.val < a.val) (L : ℤ) (ha : ρ a ≤ L + 2) (hb : L + 9 ≤ ρ b) :
    ∃ r r' : Fin n, b.val + 70 ≤ r.val ∧ r.val + 29 ≤ r'.val ∧ r'.val + 70 ≤ a.val ∧
      ρ r ≤ ρ a + 1 ∧ L + 7 ≤ ρ r' ∧ L + 8 ≤ σ r' := by
  obtain ⟨r, r', hbr, hrr', hr'a, -, hcase⟩ :=
    hcr.crooked b a (Fin.lt_def.mpr hba) (ρ b) (ρ a)
      ⟨b, by simp, le_rfl, hcr.le b⟩ ⟨a, by simp, le_rfl, hcr.le a⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hwr' := hcr.width r'
  have hbrv : b.val < r.val := hbr
  have hrr'v : r.val < r'.val := hrr'
  have hr'av : r'.val < a.val := hr'a
  have h1 : b.val + 70 ≤ r.val := by
    have hz : z 6 = 71 := by decide
    rcases ivSep hcr r b (by omega) 6 (ρ a + 1) (ρ b) (by push_cast; omega)
      hr1 hr2 le_rfl (hcr.le b) with h | h
    · omega
    · omega
  have h2 : r.val + 29 ≤ r'.val := by
    have hz : z 5 = 30 := by decide
    rcases ivSep hcr r r' (by omega) 5 (ρ a + 1) (ρ b - 1) (by push_cast; omega)
      hr1 hr2 hr'1 hr'2 with h | h
    · omega
    · omega
  have h3 : r'.val + 70 ≤ a.val := by
    have hz : z 6 = 71 := by decide
    rcases ivSep hcr a r' (by omega) 6 (ρ a) (ρ b - 1) (by push_cast; omega)
      le_rfl (hcr.le a) hr'1 hr'2 with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, h3, by omega, by omega, by omega⟩

/-- **The mirror of `cross_peak_valley_armG'`: the crossing whose `w8` side is the backward arm.**
The forward arm descends to `L + 2` at `dG` with `w8`'s floor clause failing there, the backward
arm ascends to `L + 9` at `dT`, and both witnesses are times of the backward arm — the peak at arm
index five or more, by `base_high_sep`, and the valley `29` steps after it. -/
theorem cross_peak_valley_armT' (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hG : armG ρ i dG ≤ L + 2) (hT : L + 9 ≤ armT ρ i dT)
    (hbad : ∀ j : Fin (n - i.val), 4 ≤ j.val → j.val + 7 ≤ dG.val → armG ρ i j ≤ L + 6) :
    ∃ Rp Rv : Fin (i.val + 1), 5 ≤ Rp.val ∧ Rp.val + 29 ≤ Rv.val ∧ Rv.val + 70 ≤ dT.val ∧
      L + 7 ≤ armT ρ i Rp ∧ armT ρ i Rv ≤ armG ρ i dG + 1 := by
  have hi := i.isLt
  have hdT := dT.isLt
  have hdG := dG.isLt
  set a : Fin n := ⟨i.val + dG.val, by omega⟩ with hadef
  set b : Fin n := ⟨i.val - dT.val, by omega⟩ with hbdef
  have hav : ρ a = armG ρ i dG := rfl
  have hbv : ρ b = armT ρ i dT := rfl
  have hba : b.val < a.val := by
    have hbi : b.val ≤ i.val := by simp only [hbdef]; omega
    rcases Nat.eq_zero_or_pos dT.val with h | h
    · exfalso
      have : b = i := Fin.ext (by simp only [hbdef]; omega)
      rw [this, hp] at hbv
      omega
    · simp only [hadef, hbdef]; omega
  obtain ⟨r, r', h1, h2, h3, hrlev, hr'lev, hr'high⟩ :=
    cross_peak_valley_core_rev hcr a b hba L (by omega) (by omega)
  have hrn := r.isLt
  have hr'n := r'.isLt
  have havl : a.val = i.val + dG.val := rfl
  have hbvl : b.val = i.val - dT.val := rfl
  -- the peak is five steps from the basepoint, on whichever side it falls
  have hfar := base_high_sep hcr i r' L hp hr'high
  -- and it cannot lie on the forward arm at all
  have hr'i : r'.val < i.val := by
    by_contra hc
    push_neg at hc
    have h5 : 5 ≤ r'.val - i.val := by omega
    have hj : r'.val - i.val < n - i.val := by omega
    have hjv : armG ρ i ⟨r'.val - i.val, hj⟩ = ρ r' := by
      show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
    have := hbad ⟨r'.val - i.val, hj⟩ (by simpa using (by omega : 4 ≤ r'.val - i.val))
      (by simp; omega)
    rw [hjv] at this
    omega
  have hri : r.val < i.val := by omega
  refine ⟨⟨i.val - r'.val, by omega⟩, ⟨i.val - r.val, by omega⟩, by simp only []; omega,
    by simp only []; omega, by simp only []; omega, ?_, ?_⟩
  · show L + 7 ≤ ρ ⟨i.val - (i.val - r'.val), _⟩
    rw [show (⟨i.val - (i.val - r'.val), by omega⟩ : Fin n) = r' from Fin.ext (by simp; omega)]
    exact hr'lev
  · show ρ ⟨i.val - (i.val - r.val), _⟩ ≤ armG ρ i dG + 1
    rw [show (⟨i.val - (i.val - r.val), by omega⟩ : Fin n) = r from Fin.ext (by simp; omega)]
    omega

/-- **The ceiling clause of `w72` on the backward arm of a crossing**, the mirror of
`leg4Land_w72_ceil_of_cross'`. -/
theorem leg4Land_w72_ceil_of_cross_T' (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hG : armG ρ i dG ≤ L + 2) (hT : L + 9 ≤ armT ρ i dT)
    (hbad : ∀ j : Fin (n - i.val), 4 ≤ j.val → j.val + 7 ≤ dG.val → armG ρ i j ≤ L + 6) :
    ∃ j k : Fin (i.val + 1), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armT ρ i dT - (L + 3)) ≤ (dT.val : ℤ) ∧
      L + 6 ≤ armT ρ i j ∧ armT ρ i k ≤ L + 3 := by
  obtain ⟨Rp, Rv, hRp, hRpv, hRvd, hRplev, hRvlev⟩ :=
    cross_peak_valley_armT' hcr i L hp dT dG hG hT hbad
  have hd9 : armT ρ i dT ≤ L + 9 :=
    hHb ⟨i.val - dT.val, by have := i.isLt; omega⟩
  exact ⟨Rp, Rv, by exact_mod_cast (by omega : 3 ≤ Rp.val), by omega, by omega, by omega, by omega⟩

/-- **The backward `w8` side of a crossing satisfies `w72` in full, in a band that misses the
floor.** This is `leg4Land_w72_of_cross_of_floor_fail` with the two arms exchanged. -/
theorem leg4Land_w72_of_cross_of_floor_fail_T (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hcross : ∀ dT : Fin (i.val + 1), L + 9 ≤ armT ρ i dT →
      ∃ dG : Fin (n - i.val), armG ρ i dG ≤ L + 2 ∧
        ¬ ∃ j : Fin (n - i.val), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armG ρ i dG) ≤ (dG.val : ℤ) ∧ L + 7 ≤ armG ρ i j) :
    Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 2) (L + 5) := by
  have hi := i.isLt
  have hLarmG : ∀ j : Fin (n - i.val), L ≤ armG ρ i j := by
    intro j
    have := hLb ⟨i.val + j.val, by have := j.isLt; omega⟩
    have he : armG ρ i j = ρ ⟨i.val + j.val, by have := j.isLt; omega⟩ := rfl
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    have := hLb ⟨i.val - d.val, by omega⟩
    have he : armT ρ i d = ρ ⟨i.val - d.val, by omega⟩ := rfl
    omega
  · intro d hd
    obtain ⟨dG, hG, hfail⟩ := hcross d (by omega)
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
      leg4Land_w72_ceil_of_cross_T' hcr i L hp hHb d dG hG (by omega)
        (crossBad_of_floor_fail hLarmG dG hG hfail)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-! ## The assembly, in a band that misses the floor -/

/-- The band's bounds, read on the two arms. -/
theorem armG_lb {i : Fin n} {L : ℤ} (hLb : ∀ t, L ≤ ρ t) : ∀ j, L ≤ armG ρ i j :=
  fun _ => hLb _

theorem armT_lb {i : Fin n} {L : ℤ} (hLb : ∀ t, L ≤ ρ t) : ∀ j, L ≤ armT ρ i j :=
  fun _ => hLb _

/-- **The branch `L + 5` at a crossing whose forward arm is the `w8` side and whose backward arm
is served by `wb`, in a band that misses the floor.** The only residue is the partner's floor
clause at its descents to exactly `L + 2`: its ceiling clause is `wb`'s own deep-floor clause
(`land_w72_ceil_of_wb`), its floor clause at `L + 1` is `wb`'s ceiling clause
(`land_w71_floor_low1_of_wb`), `w72`'s deep-floor clause triggers below the band, and the `w8`
side's own `w72` is the pairing's (`leg4Land_w72_of_cross_of_floor_fail`, batch 63). -/
theorem s3_span_nine_mid5_of_cross_wb_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hb : Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  classical
  have hLb' : ∀ t, L ≤ ρ t := fun t => (hLb t).trans' (by omega)
  by_cases hT8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 8) (L + 1) (L + 5) hlip hLb' hHb hp
      (leg4Window_w8 L) (by omega) (by omega) h8 hT8
  · obtain ⟨d, hd, hfail⟩ :=
      cross_floor_fail_of_not_w8 (armT_lb hLb') (fun j => hHb _) hT8
    exact s3_span_nine_mid5_of_cross_w72 hcr hlip i L hp hHb hLb h8
      (fun _ _ => ⟨d, hd, hfail⟩)
      (leg4Land_w72_of_wb_of_mid2 (fun j => hLb _) hb hmid)

/-- **The mirror: the crossing whose backward arm is the `w8` side and whose forward arm is served
by `wb`.** -/
theorem s3_span_nine_mid5_of_cross_wb_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hb : Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor (armG ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  classical
  have hLb' : ∀ t, L ≤ ρ t := fun t => (hLb t).trans' (by omega)
  by_cases hG8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 8) (L + 1) (L + 5) hlip hLb' hHb hp
      (leg4Window_w8 L) (by omega) (by omega) hG8 h8
  · obtain ⟨d, hd, hfail⟩ :=
      cross_floor_fail_of_not_w8 (armG_lb hLb') (fun j => hHb _) hG8
    exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip hLb' hHb hp
      (leg4Window_w72 L) (by omega) (by omega)
      (leg4Land_w72_of_wb_of_mid2 (fun j => hLb _) hb hmid)
      (leg4Land_w72_of_cross_of_floor_fail_T hcr i L hp hHb hLb h8 (fun _ _ => ⟨d, hd, hfail⟩))

/-- **The off-floor branch, from the two clauses on both arms.** No pairing is used: each arm gets
its floor clause at `L + 1` from the trichotomy and its deep-floor clause from the band. -/
theorem s3_span_nine_mid5_offfloor_of_mid2_of_ceil (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8))
    (hmidG : Mid2Floor (armG ρ i) L) (hmidT : Mid2Floor (armT ρ i) L)
    (hceilG : ∀ d : Fin (n - i.val), L + 9 ≤ armG ρ i d → ∃ j k : Fin (n - i.val),
      3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armG ρ i d - (L + 3)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 3)
    (hceilT : ∀ d : Fin (i.val + 1), L + 9 ≤ armT ρ i d → ∃ j k : Fin (i.val + 1),
      3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armT ρ i d - (L + 3)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armT ρ i j ∧ armT ρ i k ≤ L + 3) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip
    (fun t => (hLb t).trans' (by omega)) hHb hp (leg4Window_w72 L) (by omega) (by omega)
    (leg4Land_w72_of_branch_of_mid2_of_ceil hmG (armG_isLip hlip i) h0G (fun j => hLb _)
      (fun j => hHb _) hG hmidG hceilG)
    (leg4Land_w72_of_branch_of_mid2_of_ceil hmT (armT_isLip hlip i) h0T (fun j => hLb _)
      (fun j => hHb _) hT hmidT hceilT)

/-! ## The crossings that reach the floor: `w71` -/

/-- **The timing law read on the backward arm**, the mirror of `armG_sep`. -/
theorem armT_sep (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (p q : Fin (i.val + 1)) (D : ℕ) (hpq : p.val ≤ q.val)
    (hlev : armT ρ i q + (D : ℤ) ≤ armT ρ i p) :
    p.val + z D ≤ q.val + 1 := by
  have hi := i.isLt
  have hp := p.isLt
  have hq := q.isLt
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    have : z 0 = 1 := rfl
    omega
  set P : Fin n := ⟨i.val - p.val, by omega⟩ with hPdef
  set Q : Fin n := ⟨i.val - q.val, by omega⟩ with hQdef
  have hPv : ρ P = armT ρ i p := rfl
  have hQv : ρ Q = armT ρ i q := rfl
  have hPval : P.val = i.val - p.val := rfl
  have hQval : Q.val = i.val - q.val := rfl
  have hDpos : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hne : Q.val ≠ P.val := by
    intro hc
    have hqp : p = q := Fin.ext (by omega)
    rw [hqp] at hlev
    omega
  rcases ivSep hcr Q P hne D (ρ Q) (ρ P) (by omega) le_rfl (hcr.le Q) le_rfl (hcr.le P) with h | h
  · have hz1 : z 1 = 2 := rfl
    have hzp := z_mono (show 1 ≤ D from hD)
    omega
  · omega

/-- **The index gaps of `Mid2Floor` are free.** At a descent to `L + 2` a time at `L + 6` or above
is four levels up, and the timing law gives twelve steps for four levels, so any such time at arm
index three or more, at any earlier index, already meets the clause's arithmetic. -/
theorem mid2Floor_of_peak_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (h : ∀ d : Fin (i.val + 1), armT ρ i d = L + 2 →
      ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val < d.val ∧ L + 6 ≤ armT ρ i j) :
    Mid2Floor (armT ρ i) L := by
  intro d hd
  obtain ⟨j, h3, hjd, hlev⟩ := h d hd
  have hz : z 4 = 13 := by decide
  have := armT_sep hcr i j d 4 (by omega) (by omega)
  exact ⟨j, by exact_mod_cast h3, by omega, hlev⟩

/-- The same on the forward arm. -/
theorem mid2Floor_of_peak_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (h : ∀ d : Fin (n - i.val), armG ρ i d = L + 2 →
      ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val < d.val ∧ L + 6 ≤ armG ρ i j) :
    Mid2Floor (armG ρ i) L := by
  intro d hd
  obtain ⟨j, h3, hjd, hlev⟩ := h d hd
  have hz : z 4 = 13 := by decide
  have := armG_sep hcr i j d 4 (by omega) (by omega)
  exact ⟨j, by exact_mod_cast h3, by omega, hlev⟩

/-- **The ceiling clause of `w71` from the pairing, at a crossing whose partner descends to
`L + 1`**, with the index-four hypothesis that a crossing supplies (batch 63). -/
theorem leg4Land_w71_ceil_of_cross_low1' (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hT : armT ρ i dT ≤ L + 1) (hG : L + 9 ≤ armG ρ i dG)
    (hbad : ∀ j : Fin (i.val + 1), 4 ≤ j.val → j.val + 7 ≤ dT.val → armT ρ i j ≤ L + 6) :
    ∃ j k : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armG ρ i dG - (L + 2)) ≤ (dG.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 2 := by
  obtain ⟨R, R', hR, hRR', hR'd, hRlev, hR'lev⟩ :=
    cross_peak_valley_armG' hcr i L hp dT dG (by omega) hG hbad
  have hR'2 : armG ρ i R' ≤ L + 2 := by omega
  obtain ⟨j, hj1, hj2, hj3⟩ := h8.1 R' (by omega)
  have hd9 : armG ρ i dG ≤ L + 9 :=
    hHb ⟨i.val + dG.val, by have := dG.isLt; have := i.isLt; omega⟩
  have hgap : j.val + z 5 ≤ R'.val + 1 :=
    armG_sep hcr i j R' 5 (by omega) (by omega)
  have hz : z 5 = 30 := by decide
  exact ⟨j, R', by omega, by omega, by omega, by omega, hR'2⟩

/-- **The forward `w8` side of a crossing whose partner descends to `L + 1` satisfies `w71` in
full.** No hypothesis on the floor of the band is needed: `w71`'s deep-floor clause triggers at
`L - 1`. -/
theorem leg4Land_w71_of_w8_of_cross_low1 (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hcross : ∀ dG : Fin (n - i.val), L + 9 ≤ armG ρ i dG →
      ∃ dT : Fin (i.val + 1), armT ρ i dT ≤ L + 1 ∧
        ¬ ∃ j : Fin (i.val + 1), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armT ρ i dT) ≤ (dT.val : ℤ) ∧ L + 7 ≤ armT ρ i j) :
    Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 1) (L + 5) := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (armG_lb (i := i) hLb d) (by omega)
  · intro d hd
    obtain ⟨dT, hT, hfail⟩ := hcross d (by omega)
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
      leg4Land_w71_ceil_of_cross_low1' hcr i L hp hHb h8 dT d hT (by omega)
        (crossBad_of_floor_fail (armT_lb hLb) dT (by omega) hfail)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **The mirror of `leg4Land_w71_ceil_of_cross_low1'`, for a backward `w8` side.** -/
theorem leg4Land_w71_ceil_of_cross_low1_T' (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hG : armG ρ i dG ≤ L + 1) (hT : L + 9 ≤ armT ρ i dT)
    (hbad : ∀ j : Fin (n - i.val), 4 ≤ j.val → j.val + 7 ≤ dG.val → armG ρ i j ≤ L + 6) :
    ∃ j k : Fin (i.val + 1), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armT ρ i dT - (L + 2)) ≤ (dT.val : ℤ) ∧
      L + 6 ≤ armT ρ i j ∧ armT ρ i k ≤ L + 2 := by
  obtain ⟨Rp, Rv, hRp, hRpv, hRvd, hRplev, hRvlev⟩ :=
    cross_peak_valley_armT' hcr i L hp dT dG (by omega) hT hbad
  have hRv2 : armT ρ i Rv ≤ L + 2 := by omega
  obtain ⟨j, hj1, hj2, hj3⟩ := h8.1 Rv (by omega)
  have hd9 : armT ρ i dT ≤ L + 9 :=
    hHb ⟨i.val - dT.val, by have := i.isLt; omega⟩
  have hgap : j.val + z 5 ≤ Rv.val + 1 :=
    armT_sep hcr i j Rv 5 (by omega) (by omega)
  have hz : z 5 = 30 := by decide
  exact ⟨j, Rv, by omega, by omega, by omega, by omega, hRv2⟩

/-- **The mirror of `leg4Land_w71_of_w8_of_cross_low1`.** -/
theorem leg4Land_w71_of_w8_of_cross_low1_T (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hcross : ∀ dT : Fin (i.val + 1), L + 9 ≤ armT ρ i dT →
      ∃ dG : Fin (n - i.val), armG ρ i dG ≤ L + 1 ∧
        ¬ ∃ j : Fin (n - i.val), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armG ρ i dG) ≤ (dG.val : ℤ) ∧ L + 7 ≤ armG ρ i j) :
    Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 1) (L + 5) := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (armT_lb (i := i) hLb d) (by omega)
  · intro d hd
    obtain ⟨dG, hG, hfail⟩ := hcross d (by omega)
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
      leg4Land_w71_ceil_of_cross_low1_T' hcr i L hp hHb h8 d dG hG (by omega)
        (crossBad_of_floor_fail (armG_lb hLb) dG (by omega) hfail)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **The branch `L + 5` at a crossing whose partner is served by `wb` and descends to `L + 1`,
with no hypothesis on the floor of the band.** Both arms satisfy `w71`: the `w8` side by the
pairing, the partner by `wb` and its floor clause at `L + 2`. This is the configuration of the
crossings that reach the floor. -/
theorem s3_span_nine_mid5_of_cross_low1_wb_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hb : Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor (armT ρ i) L)
    (hcross : ∀ dG : Fin (n - i.val), L + 9 ≤ armG ρ i dG →
      ∃ dT : Fin (i.val + 1), armT ρ i dT ≤ L + 1 ∧
        ¬ ∃ j : Fin (i.val + 1), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armT ρ i dT) ≤ (dT.val : ℤ) ∧ L + 7 ≤ armT ρ i j) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 1) (L + 5) hlip hLb hHb hp
    (leg4Window_w71 L) (by omega) (by omega)
    (leg4Land_w71_of_w8_of_cross_low1 hcr i L hp hHb hLb h8 hcross)
    (leg4Land_w71_of_wb_of_mid2 (armT_lb hLb) hb hmid)

/-! ## The `w72` route where the band reaches the floor -/

/-- **The forward `w8` side of a crossing satisfies `w72` in full**, with its deep-floor clause
assumed instead of a band that misses the floor. This is `leg4Land_w72_of_cross_of_floor_fail`
with the hypothesis that the corpus actually meets: every crossing of the census has an arm that
reaches `L`. -/
theorem leg4Land_w72_of_cross_of_floor_fail_deep (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hdeep : Deep72 (armG ρ i) L)
    (hcross : ∀ dG : Fin (n - i.val), L + 9 ≤ armG ρ i dG →
      ∃ dT : Fin (i.val + 1), armT ρ i dT ≤ L + 2 ∧
        ¬ ∃ j : Fin (i.val + 1), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armT ρ i dT) ≤ (dT.val : ℤ) ∧ L + 7 ≤ armT ρ i j) :
    Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    obtain ⟨j, k, l, h1, h2, h3, h4, h5, h6, h7⟩ := hdeep d (by omega)
    exact ⟨j, k, l, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro d hd
    obtain ⟨dT, hT, hfail⟩ := hcross d (by omega)
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
      leg4Land_w72_ceil_of_cross' hcr i L hp hHb dT d hT (by omega)
        (crossBad_of_floor_fail (armT_lb hLb) dT hT hfail)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **The mirror of `leg4Land_w72_of_cross_of_floor_fail_deep`.** -/
theorem leg4Land_w72_of_cross_of_floor_fail_deep_T (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hdeep : Deep72 (armT ρ i) L)
    (hcross : ∀ dT : Fin (i.val + 1), L + 9 ≤ armT ρ i dT →
      ∃ dG : Fin (n - i.val), armG ρ i dG ≤ L + 2 ∧
        ¬ ∃ j : Fin (n - i.val), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armG ρ i dG) ≤ (dG.val : ℤ) ∧ L + 7 ≤ armG ρ i j) :
    Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 2) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    obtain ⟨j, k, l, h1, h2, h3, h4, h5, h6, h7⟩ := hdeep d (by omega)
    exact ⟨j, k, l, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro d hd
    obtain ⟨dG, hG, hfail⟩ := hcross d (by omega)
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
      leg4Land_w72_ceil_of_cross_T' hcr i L hp hHb d dG hG (by omega)
        (crossBad_of_floor_fail (armG_lb hLb) dG hG hfail)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **The branch `L + 5` at a crossing with a `wb` partner, by `w72`, where the band reaches the
floor.** The two arms' deep-floor clauses replace the off-floor band of batch 63. -/
theorem s3_span_nine_mid5_of_cross_wb_deep_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hb : Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor (armT ρ i) L)
    (hdeepG : Deep72 (armG ρ i) L) (hdeepT : Deep72 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  classical
  by_cases hT8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 8) (L + 1) (L + 5) hlip hLb hHb hp
      (leg4Window_w8 L) (by omega) (by omega) h8 hT8
  · obtain ⟨d, hd, hfail⟩ := cross_floor_fail_of_not_w8 (armT_lb hLb) (fun j => hHb _) hT8
    exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip hLb hHb hp
      (leg4Window_w72 L) (by omega) (by omega)
      (leg4Land_w72_of_cross_of_floor_fail_deep hcr i L hp hHb hLb h8 hdeepG
        (fun _ _ => ⟨d, hd, hfail⟩))
      (leg4Land_w72_of_wb_of_mid2_of_deep hb hmid hdeepT)

/-- **The mirror of `s3_span_nine_mid5_of_cross_wb_deep_armT`.** -/
theorem s3_span_nine_mid5_of_cross_wb_deep_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hb : Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor (armG ρ i) L)
    (hdeepG : Deep72 (armG ρ i) L) (hdeepT : Deep72 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  classical
  by_cases hG8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 8) (L + 1) (L + 5) hlip hLb hHb hp
      (leg4Window_w8 L) (by omega) (by omega) hG8 h8
  · obtain ⟨d, hd, hfail⟩ := cross_floor_fail_of_not_w8 (armG_lb hLb) (fun j => hHb _) hG8
    exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip hLb hHb hp
      (leg4Window_w72 L) (by omega) (by omega)
      (leg4Land_w72_of_wb_of_mid2_of_deep hb hmid hdeepG)
      (leg4Land_w72_of_cross_of_floor_fail_deep_T hcr i L hp hHb hLb h8 hdeepT
        (fun _ _ => ⟨d, hd, hfail⟩))

/-! ## The two walks, one split -/

/-- **The branch `L + 5` at a crossing, from the partner's one clause and whichever of the two
walks serves the `w8` side.** The partner, served by `wb`, satisfies `w71` as soon as it has the
floor clause at its descents to exactly `L + 2`, and `w72` as soon as it has that clause and its
deep-floor clause; so the pair is served as soon as the `w8` side satisfies either walk. This is
the two-walk form of the list of six, with the residue of the branch confined to the partner's one
clause. -/
theorem s3_span_nine_mid5_of_cross_wb_two_walks (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (hb : Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor (armT ρ i) L)
    (hside : Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ∨
      (Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) ∧ Deep72 (armT ρ i) L)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  rcases hside with h71 | ⟨h72, hdeep⟩
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 1) (L + 5) hlip hLb hHb hp
      (leg4Window_w71 L) (by omega) (by omega) h71
      (leg4Land_w71_of_wb_of_mid2 (armT_lb hLb) hb hmid)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip hLb hHb hp
      (leg4Window_w72 L) (by omega) (by omega) h72
      (leg4Land_w72_of_wb_of_mid2_of_deep hb hmid hdeep)

/-- **The mirror of `s3_span_nine_mid5_of_cross_wb_two_walks`**, for a crossing whose partner is
the forward arm. -/
theorem s3_span_nine_mid5_of_cross_wb_two_walks_armG (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (hb : Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hmid : Mid2Floor (armG ρ i) L)
    (hside : Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ∨
      (Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 2) (L + 5) ∧ Deep72 (armG ρ i) L)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  rcases hside with h71 | ⟨h72, hdeep⟩
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 1) (L + 5) hlip hLb hHb hp
      (leg4Window_w71 L) (by omega) (by omega)
      (leg4Land_w71_of_wb_of_mid2 (armG_lb hLb) hb hmid) h71
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip hLb hHb hp
      (leg4Window_w72 L) (by omega) (by omega)
      (leg4Land_w72_of_wb_of_mid2_of_deep hb hmid hdeep) h72

/-! ## The residue, named -/

/-- **What the branch `L + 5` is left owing after this batch.** At a crossing of the trichotomy
the arm that `w8` does not serve has the floor clause at its descents to exactly `L + 2`. The
census of `census-batch64.c` finds this at all 461 crossings of the corpus, and finds it
non-vacuous at all of them (every partner does descend to exactly `L + 2`). -/
def CrossMid2L5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    (¬ Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5) → Mid2Floor (armT ρ i) L) ∧
    (¬ Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) → Mid2Floor (armG ρ i) L)

/-- **The `w71` half of the branch, from the residue and the pairing.** With `CrossMid2L5`, a
basepoint of the branch whose `w8` side owes only the ceiling clause of `w71`, and whose partner
supplies the pairing's valley at `L + 1`, folds. -/
theorem s3_span_nine_mid5_of_crossMid2_of_low1 (hres : CrossMid2L5) {n : ℕ} {ρ σ : Fin n → ℤ}
    (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8))
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hb : Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hnot8 : ¬ Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hcross : ∀ dG : Fin (n - i.val), L + 9 ≤ armG ρ i dG →
      ∃ dT : Fin (i.val + 1), armT ρ i dT ≤ L + 1 ∧
        ¬ ∃ j : Fin (i.val + 1), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armT ρ i dT) ≤ (dT.val : ℤ) ∧ L + 7 ≤ armT ρ i j) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_low1_wb_armT hcr hlip i L hp hHb hLb h8 hb
    ((hres n ρ σ i L hlip hcr hLb hHb hp hG hT).1 hnot8) hcross

end Pair

end HPC.Fold
