import HPC.Fold.LandLowAt

/-!
# The arm-only half of exhaustiveness at the branch `L + 5`

Batch 59 reduced the branch `L + 5` of span nine to an arm-only statement
(`Leg4LandClosesL5`, `HPC/Fold/CoverL5Land.lean`): because the landmark sentence of a four-leg
walk is *exact* (`foldsOnto_leg4_iff_leg4Land`), "the list of walks is exhaustive" is a property
of each arm separately. Batch 60 asks whether an arm that fails a clause of the branch's best walk
folds onto another walk by itself. It does, and this file proves the whole arm-only half:

**every arm of the branch is served by one of three walks.**

## The three walks

With `H = L + 9` and the arm `f` based at `L + 5`, write `g` for the reflection
`armRefl (L + (L + 9)) f`, based at `L + 4`. The three walks are

```
w8 : direct    (P, K, M) = (L+5, L+8, L+1)     L+4 → L+8 → L+1 → L+8 → L+1
w3 : reflected (P, K, M) = (L+4, L+6, L+1)     L+6 → L+3 → L+8 → L+1 → L+8
wb : reflected (P, K, M) = (L+4, L+6, L+2)     L+6 → L+3 → L+7 → L+1 → L+8
```

`wb` is the branch's best walk, the one whose descent clause *is* the branch hypothesis
(`land_down1_of_lowAt_low`, `HPC/Fold/LandLowAt.lean`). Read on `f`, their landmark sentences say:

* `w8` — before every descent to `L + 2` a time at `L + 7` or above, at index at least `4` and at
  least `L + 7 - f d` steps earlier. Its other two clauses are vacuous inside the band.
* `w3` — before every ascent to `L + 8` a time at `L + 4` or below (index at least `3`, gap
  `f d - L - 4`); and before every descent to `L + 1` such a time followed, five steps later, by
  one at `L + 7` or above, itself `L + 7 - f d` steps before the descent.
* `wb` — the same ascent clause; before every descent to `L + 1` a time at `L + 4` or below
  followed four steps later by one at `L + 6` or above; and before every ascent to `L + 9` a time
  at `L + 4` or below, one at `L + 6` or above four steps later, and one at `L + 2` or below six
  steps after that.

## The theorem

`leg4Land_tri`: a 1-Lipschitz arm of the band `[L, L + 9]` based at `L + 5` which satisfies the
branch hypothesis `LowAt (L + 1) (L + 8)` satisfies the landmark sentence of `w8`, of `w3` or of
`wb` — so by `foldsOnto_leg4_of_leg4Land` it folds onto that walk.

The proof is a dichotomy on `w8`. If `w8` fails there is a descent `d₀` to `L + 2` with no earlier
high time, and then (`notW8_hi_after`) *every* time at `L + 8` or above is after `d₀`, which makes
`d₀` itself the ascent clause's landmark for both `w3` and `wb` (`notW8_floor`). What is left is
the descent clause, and there the branch hypothesis decides: where it is met by its first disjunct
— a time at `L + 8` before the descent — the pair `(d₀, that time)` is the stronger chain `w3`
asks for (`notW8_ceil3`); where it is met by its second disjunct — a time at `L + 2` and then one
at `L + 6` — that pair is the chain `wb` asks for (`notW8_ceilWb`). If the first disjunct serves
every descent, `w3` holds; otherwise some descent `d₁` uses the second, and then no ascent to
`L + 9` can precede `d₁`, so the second disjunct's own pair, followed by `d₁`, is the three-link
chain of `wb`'s deep clause (`notW8_deep`).

The census (`census-batch60.c`, log `census-batch60.log`) and the exhaustive arm probes
(`probe60.c`, `probe60b.c`) measured this before it was proved: over every 1-Lipschitz arm of the
band based at `L + 5` with the branch hypothesis, of length at most sixteen, no arm is served by
none of the three, and every arm failing the `L + 8` clause of `wb` is served by `w8`.

## What is left of the branch

`s3_span_nine_mid5` needs one walk serving *both* arms of a basepoint. The trichotomy gives each
arm a walk; the residue is a *crossing*, a basepoint whose two arms are served by different walks
of the three. `Leg4TriCrossL5` states exactly that residue, and
`s3_span_nine_mid5_of_leg4TriCrossL5` shows it is all that remains.
-/

namespace HPC.Fold

section Arm

variable {m : ℕ} {f : Fin m → ℤ} {L : ℤ}

/-! ## `w8` is its floor clause -/

/-- **The landmark sentence of `w8` is its floor clause alone.** Inside the band `[L, L + 9]` the
deep-floor clause of `(P, K, M) = (L+5, L+8, L+1)` triggers only below `L`, and its ceiling clause
only above `L + 9`. -/
theorem leg4Land_w8_of_floor (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hfl : ∀ d : Fin m, f d ≤ L + 2 → ∃ j : Fin m, 4 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (L + 7 - f d) ≤ (d.val : ℤ) ∧ L + 7 ≤ f j) :
    Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := hfl d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    exact absurd (hH d) (by omega)

/-! ## The consequences of a failure of `w8`

Throughout: `d₀` is a time at `L + 2` or below with no time at `L + 7` or above at index at least
`4` and at least `L + 7 - f d₀` steps earlier — the witness that `w8` fails. -/

variable {d₀ : Fin m}

/-- A descent to `L + 2` is at index at least three. -/
theorem notW8_base3 (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5) (hd0 : f d₀ ≤ L + 2) :
    3 ≤ (d₀.val : ℤ) := by
  have := isLip_index_gap' hf (j := ⟨0, hm⟩) (k := d₀) (Nat.zero_le _) 3 (by omega)
  simpa using this

/-- **Every time at `L + 8` or above is after `d₀`.** An earlier one would be the landmark `w8`
asks for. -/
theorem notW8_hi_after (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5) (hd0 : f d₀ ≤ L + 2)
    (hfail : ∀ j : Fin m, 4 ≤ (j.val : ℤ) → (j.val : ℤ) + (L + 7 - f d₀) ≤ (d₀.val : ℤ) →
      f j < L + 7) :
    ∀ d : Fin m, L + 8 ≤ f d → d₀.val < d.val := by
  intro d hd
  by_contra hcon
  push_neg at hcon
  have hgap : (d.val : ℤ) + (f d - f d₀) ≤ (d₀.val : ℤ) :=
    isLip_index_gap' hf hcon (f d - f d₀) (by omega)
  rcases le_or_gt 4 (d.val : ℤ) with h4 | h4
  · exact absurd hd (by have := hfail d h4 (by omega); omega)
  · -- the arm starts at `L + 5`, so a time at `L + 8` before the index four is the index three
    have hstart : ((0 : ℕ) : ℤ) + (f d - f ⟨0, hm⟩) ≤ (d.val : ℤ) :=
      isLip_index_gap hf (j := ⟨0, hm⟩) (k := d) (Nat.zero_le _) (f d - f ⟨0, hm⟩) (by omega)
    have hd3 : d.val = 3 := by
      simp only [Nat.cast_zero, zero_add, h0] at hstart
      omega
    have hd0ge : 4 ≤ d₀.val := by
      rcases Nat.lt_or_ge d₀.val 4 with h | h
      · exfalso
        have : d₀ = d := Fin.ext (by omega)
        rw [this] at hd0
        omega
      · exact h
    have h4m : 4 < m := lt_of_le_of_lt hd0ge d₀.isLt
    have hstep := hf d ⟨4, h4m⟩ (show (⟨4, h4m⟩ : Fin m).val = d.val + 1 by simp [hd3])
    rw [abs_le] at hstep
    have := hfail ⟨4, h4m⟩ (by simp) (by push_cast at hgap ⊢; omega)
    simp only at this
    omega

/-- **The ascent clause of `w3` and of `wb` holds**: `d₀` is its landmark. -/
theorem notW8_floor (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5) (hd0 : f d₀ ≤ L + 2)
    (hfail : ∀ j : Fin m, 4 ≤ (j.val : ℤ) → (j.val : ℤ) + (L + 7 - f d₀) ≤ (d₀.val : ℤ) →
      f j < L + 7) :
    ∀ d : Fin m, L + 8 ≤ f d → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (f d - (L + 4)) ≤ (d.val : ℤ) ∧ f j ≤ L + 4 := by
  intro d hd
  have hlt := notW8_hi_after hm hf h0 hd0 hfail d hd
  have hgap : (d₀.val : ℤ) + (f d - f d₀) ≤ (d.val : ℤ) :=
    isLip_index_gap hf (le_of_lt hlt) (f d - f d₀) (by omega)
  exact ⟨d₀, notW8_base3 hm hf h0 hd0, by omega, by omega⟩

/-- **Where the branch hypothesis is met by its first disjunct, the descent clause of `w3`
holds.** A time `p` at `L + 8` or above before a descent `d` to `L + 1` gives the pair `(d₀, p)`,
which is the stronger chain — a landmark at `L + 4` or below and, five steps later, one at `L + 7`
or above. -/
theorem notW8_ceil3 (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5) (hd0 : f d₀ ≤ L + 2)
    (hfail : ∀ j : Fin m, 4 ≤ (j.val : ℤ) → (j.val : ℤ) + (L + 7 - f d₀) ≤ (d₀.val : ℤ) →
      f j < L + 7)
    (d p : Fin m) (hp : p.val < d.val) (hpv : L + 8 ≤ f p) :
    ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (L + 7 - f d) ≤ (d.val : ℤ) ∧ f j ≤ L + 4 ∧ L + 7 ≤ f k := by
  have hlt := notW8_hi_after hm hf h0 hd0 hfail p hpv
  have hgap1 : (d₀.val : ℤ) + (f p - f d₀) ≤ (p.val : ℤ) :=
    isLip_index_gap hf (le_of_lt hlt) (f p - f d₀) (by omega)
  have hgap2 : (p.val : ℤ) + (f p - f d) ≤ (d.val : ℤ) :=
    isLip_index_gap' hf (le_of_lt hp) (f p - f d) (by omega)
  exact ⟨d₀, p, notW8_base3 hm hf h0 hd0, by omega, by omega, by omega, by omega⟩

/-- **Where the branch hypothesis is met by its second disjunct, the descent clause of `wb`
holds.** A time `p` at `L + 2` or below followed by a time `q` at `L + 6` or above, both before a
descent `d` to `L + 1`, are its two landmarks. -/
theorem notW8_ceilWb (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5)
    (d p q : Fin m) (hpq : p.val < q.val) (hqd : q.val < d.val)
    (hpv : f p ≤ L + 2) (hqv : L + 6 ≤ f q) :
    ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 4 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (L + 6 - f d) ≤ (d.val : ℤ) ∧ f j ≤ L + 4 ∧ L + 6 ≤ f k := by
  have hp3 : 3 ≤ (p.val : ℤ) := by
    have := isLip_index_gap' hf (j := ⟨0, hm⟩) (k := p) (Nat.zero_le _) 3 (by omega)
    simpa using this
  have hgap1 : (p.val : ℤ) + (f q - f p) ≤ (q.val : ℤ) :=
    isLip_index_gap hf (le_of_lt hpq) (f q - f p) (by omega)
  have hgap2 : (q.val : ℤ) + (f q - f d) ≤ (d.val : ℤ) :=
    isLip_index_gap' hf (le_of_lt hqd) (f q - f d) (by omega)
  exact ⟨p, q, hp3, by omega, by omega, by omega, by omega⟩

/-- **The deep clause of `wb` holds once some descent needs the second disjunct.** If a descent
`d₁` to `L + 1` has no chain of the kind `w3` asks for, then no time at `L + 9` precedes it, and
the second disjunct's pair `(p, q)` before `d₁`, followed by `d₁` itself (or by the step after it,
when `q` is as late as the branch hypothesis allows), is the three-link chain. -/
theorem notW8_deep (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5) (hd0 : f d₀ ≤ L + 2)
    (hfail : ∀ j : Fin m, 4 ≤ (j.val : ℤ) → (j.val : ℤ) + (L + 7 - f d₀) ≤ (d₀.val : ℤ) →
      f j < L + 7)
    (d₁ p q : Fin m) (hd1 : f d₁ ≤ L + 1) (hpq : p.val < q.val) (hqd : q.val < d₁.val)
    (hpv : f p ≤ L + 2) (hqv : L + 6 ≤ f q)
    (hno3 : ¬ ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (L + 7 - f d₁) ≤ (d₁.val : ℤ) ∧ f j ≤ L + 4 ∧ L + 7 ≤ f k) :
    ∀ d : Fin m, L + 9 ≤ f d → ∃ j k l : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 4 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + 6 ≤ (l.val : ℤ) ∧
      (l.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧ f j ≤ L + 4 ∧ L + 6 ≤ f k ∧ f l ≤ L + 2 := by
  intro d hd
  -- no ascent to `L + 9` precedes `d₁`: it would give the chain `w3` asks for
  have hafter : d₁.val < d.val := by
    rcases Nat.lt_or_ge d₁.val d.val with h | h
    · exact h
    · exfalso
      have hne : d.val ≠ d₁.val := by
        intro hcon
        have : d = d₁ := Fin.ext hcon
        rw [this] at hd
        omega
      exact hno3 (notW8_ceil3 hm hf h0 hd0 hfail d₁ d (by omega) (by omega))
  have hp3 : 3 ≤ (p.val : ℤ) := by
    have := isLip_index_gap' hf (j := ⟨0, hm⟩) (k := p) (Nat.zero_le _) 3 (by omega)
    simpa using this
  have hpq4 : (p.val : ℤ) + 4 ≤ (q.val : ℤ) := by
    have := isLip_index_gap hf (le_of_lt hpq) (f q - f p) (by omega)
    omega
  have hqd1 : (q.val : ℤ) + 5 ≤ (d₁.val : ℤ) := by
    have := isLip_index_gap' hf (le_of_lt hqd) (f q - f d₁) (by omega)
    omega
  have hd1d : (d₁.val : ℤ) + (f d - f d₁) ≤ (d.val : ℤ) :=
    isLip_index_gap hf (le_of_lt hafter) (f d - f d₁) (by omega)
  rcases le_or_gt ((q.val : ℤ) + 6) (d₁.val : ℤ) with hcase | hcase
  · exact ⟨p, q, d₁, hp3, hpq4, by omega, by omega, by omega, hqv, by omega⟩
  · -- `q` is exactly five steps before `d₁`; the step after `d₁` is still at `L + 2` or below
    have hsucc : d₁.val + 1 < m := by have := d.isLt; omega
    have hstep := hf d₁ ⟨d₁.val + 1, hsucc⟩ rfl
    rw [abs_le] at hstep
    refine ⟨p, q, ⟨d₁.val + 1, hsucc⟩, hp3, hpq4, ?_, ?_, ?_, hqv, ?_⟩
    · push_cast
      omega
    · push_cast
      omega
    · omega
    · omega

/-! ## The trichotomy -/

/-- **Every arm of the branch is served by one of three walks.** A 1-Lipschitz arm of the band
`[L, L + 9]` based at `L + 5` which meets the branch hypothesis satisfies the landmark sentence —
the exact criterion — of

* `w8`, the walk `L+4 → L+8 → L+1 → L+8 → L+1`, or
* `w3`, the walk `L+6 → L+3 → L+8 → L+1 → L+8`, read on the reflected arm, or
* `wb`, the walk `L+6 → L+3 → L+7 → L+1 → L+8`, read on the reflected arm.

This is the arm-only half of exhaustiveness at the branch `L + 5`. -/
theorem leg4Land_tri (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) (hlow : LowAt f (L + 1) (L + 8)) :
    Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5) ∨
      Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 1) (L + 4) ∨
      Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4) := by
  classical
  by_cases h8 : ∀ d : Fin m, f d ≤ L + 2 → ∃ j : Fin m, 4 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (L + 7 - f d) ≤ (d.val : ℤ) ∧ L + 7 ≤ f j
  · exact Or.inl (leg4Land_w8_of_floor hL hH h8)
  push_neg at h8
  obtain ⟨d₀, hd0, hfail⟩ := h8
  have hfail' : ∀ j : Fin m, 4 ≤ (j.val : ℤ) → (j.val : ℤ) + (L + 7 - f d₀) ≤ (d₀.val : ℤ) →
      f j < L + 7 := by
    intro j h1 h2
    have := hfail j h1 h2
    omega
  have hfl := notW8_floor hm hf h0 hd0 hfail'
  -- does every descent to `L + 1` carry the stronger chain?
  by_cases hc3 : ∀ d : Fin m, f d ≤ L + 1 → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (L + 7 - f d) ≤ (d.val : ℤ) ∧
      f j ≤ L + 4 ∧ L + 7 ≤ f k
  · -- yes: `w3` serves the arm
    refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
    · intro d hd
      simp only [armRefl_apply] at hd ⊢
      obtain ⟨j, h1, h2, h3⟩ := hfl d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · intro d hd
      simp only [armRefl_apply] at hd
      exact absurd (hH d) (by omega)
    · intro d hd
      simp only [armRefl_apply] at hd ⊢
      obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hc3 d (by omega)
      exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩
  · -- no: some descent `d₁` needs the second disjunct of the branch hypothesis, and then `wb`
    push_neg at hc3
    obtain ⟨d₁, hd1, hno3⟩ := hc3
    have hno3' : ¬ ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
        (k.val : ℤ) + (L + 7 - f d₁) ≤ (d₁.val : ℤ) ∧ f j ≤ L + 4 ∧ L + 7 ≤ f k := by
      rintro ⟨j, k, h1, h2, h3, h4, h5⟩
      exact absurd h5 (by have := hno3 j k h1 h2 h3 h4; omega)
    -- the branch hypothesis at `d₁` cannot be its first disjunct
    have hd1case : ∃ p q : Fin m, p.val < q.val ∧ q.val < d₁.val ∧ f p ≤ L + 2 ∧ L + 6 ≤ f q := by
      rcases hlow d₁ hd1 with ⟨p, hp, hpv⟩ | ⟨p, q, hpq, hqd, hpv, hqv⟩
      · exact absurd (notW8_ceil3 hm hf h0 hd0 hfail' d₁ p hp hpv) hno3'
      · exact ⟨p, q, hpq, hqd, by omega, by omega⟩
    obtain ⟨p, q, hpq, hqd, hpv, hqv⟩ := hd1case
    refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
    · intro d hd
      simp only [armRefl_apply] at hd ⊢
      obtain ⟨j, h1, h2, h3⟩ := hfl d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · intro d hd
      simp only [armRefl_apply] at hd ⊢
      obtain ⟨j, k, l, h1, h2, h3, h4, h5, h6, h7⟩ :=
        notW8_deep hm hf h0 hd0 hfail' d₁ p q hd1 hpq hqd hpv hqv hno3' d (by omega)
      exact ⟨j, k, l, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · intro d hd
      simp only [armRefl_apply] at hd ⊢
      rcases hlow d (by omega) with ⟨r, hr, hrv⟩ | ⟨r, s, hrs, hsd, hrv, hsv⟩
      · obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
          notW8_ceil3 hm hf h0 hd0 hfail' d r hr (by omega)
        exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩
      · obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
          notW8_ceilWb hm hf h0 d r s hrs hsd (by omega) (by omega)
        exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

end Arm

/-! ## The trichotomy on the arms of a basepoint

Each arm of a basepoint of the branch is served by one of the three walks; a basepoint whose two
arms are served by the *same* walk folds onto it. What is left — the *crossings* — is a basepoint
whose arms are served by different walks. -/

section Pair

variable {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ)

/-- The windows of the three walks. -/
theorem leg4Window_w8 : Leg4Window L (L + 9) (L + 8) (L + 1) (L + 5) := by
  unfold Leg4Window; omega

theorem leg4Window_w3 : Leg4Window L (L + 9) (L + 6) (L + 1) (L + 4) := by
  unfold Leg4Window; omega

theorem leg4Window_wb : Leg4Window L (L + 9) (L + 6) (L + 2) (L + 4) := by
  unfold Leg4Window; omega

/-- **The trichotomy on the forward arm of a basepoint of the branch.** -/
theorem leg4Land_tri_armG (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hp : ρ i = L + 5) (hG : LowAt (armG ρ i) (L + 1) (L + 8)) :
    Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) ∨
      Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∨
      Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) := by
  have hm : 0 < n - i.val := by have := i.isLt; omega
  have h0 : armG ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  exact leg4Land_tri hm (armG_isLip hlip i) h0 (fun j => hLb _) (fun j => hHb _) hG

/-- **The trichotomy on the backward arm of a basepoint of the branch.** -/
theorem leg4Land_tri_armT (hlip : IsLip ρ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hp : ρ i = L + 5) (hT : LowAt (armT ρ i) (L + 1) (L + 8)) :
    Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5) ∨
      Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∨
      Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) := by
  have hm : 0 < i.val + 1 := by omega
  have h0 : armT ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  exact leg4Land_tri hm (armT_isLip hlip i) h0 (fun j => hLb _) (fun j => hHb _) hT

/-- **The crossings the trichotomy leaves at the branch `L + 5`.** A basepoint of the branch at
which no one of the three walks serves both arms: by `leg4Land_tri` each arm is served by one of
them, so the two arms are served by different walks. -/
def Leg4TriCrossL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)) →
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c

end Pair

/-- **The crossings of a longer list.** The census finds the residue of the three walks small but
not empty, and two further walks of the family — `L+4 → L+7 → L+2 → L+8 → L+1` and
`L+5 → L+8 → L+1 → L+8 → L+1` — serve most of what is left. This is the same residue read against
the list of five; it is weaker than `Leg4TriCrossL5`, and by `leg4Land_tri` each arm is still
served by one of the first three. -/
def Leg4FiveCrossL5 : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ), IsLip ρ → IsCrookedIvF ρ σ →
    (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ L + 9) → ρ i = L + 5 →
    LowAt (armG ρ i) (L + 1) (L + 8) → LowAt (armT ρ i) (L + 1) (L + 8) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) →
    ¬ (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 2) (L + 5)) →
    ¬ (Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 6) ∧
        Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 6)) →
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c

/-- The windows of the two further walks. -/
theorem leg4Window_w72 (L : ℤ) : Leg4Window L (L + 9) (L + 7) (L + 2) (L + 5) := by
  unfold Leg4Window; omega

theorem leg4Window_w81 (L : ℤ) : Leg4Window L (L + 9) (L + 8) (L + 1) (L + 6) := by
  unfold Leg4Window; omega

/-- **The branch `L + 5` is exactly its crossings.** With the arm-only half a theorem, the target
`s3_span_nine_mid5` follows from the crossings alone: at a basepoint where one of the three walks
serves both arms the pair folds onto it, and `Leg4TriCrossL5` is the rest. -/
theorem s3_span_nine_mid5_of_leg4TriCrossL5 (h : Leg4TriCrossL5) {n : ℕ} (ρ σ : Fin n → ℤ)
    (i : Fin n) (L : ℤ) (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  classical
  by_cases h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) ∧
      Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 8) (L + 1) (L + 5) hlip hLb hHb hp
      (leg4Window_w8 L) (by omega) (by omega) h8.1 h8.2
  by_cases h3 : Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
      Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)
  · exact s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 1) (L + 4) hlip hLb hHb hp
      (leg4Window_w3 L) (by omega) (by omega) h3.1 h3.2
  by_cases hb : Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
      Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)
  · exact s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 2) (L + 4) hlip hLb hHb hp
      (leg4Window_wb L) (by omega) (by omega) hb.1 hb.2
  exact h n ρ σ i L hlip hcr hLb hHb hp hG hT h8 h3 hb

/-- **The same reduction against the list of five.** The residue is smaller, so the hypothesis is
weaker; the census measures it at 38 of the corpus's 1 745 960 basepoints, against 371 for the
three. -/
theorem s3_span_nine_mid5_of_leg4FiveCrossL5 (h : Leg4FiveCrossL5) {n : ℕ} (ρ σ : Fin n → ℤ)
    (i : Fin n) (L : ℤ) (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5)
    (hG : LowAt (armG ρ i) (L + 1) (L + 8)) (hT : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  classical
  refine s3_span_nine_mid5_of_leg4TriCrossL5 ?_ ρ σ i L hlip hcr hLb hHb hp hG hT
  intro n' ρ' σ' i' L' hlip' hcr' hLb' hHb' hp' hG' hT' h8 h3 hb
  by_cases h72 : Leg4Land (armG ρ' i') (L' + 9) (L' + 7) (L' + 2) (L' + 5) ∧
      Leg4Land (armT ρ' i') (L' + 9) (L' + 7) (L' + 2) (L' + 5)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ' i' L' (L' + 7) (L' + 2) (L' + 5) hlip' hLb' hHb'
      hp' (leg4Window_w72 L') (by omega) (by omega) h72.1 h72.2
  by_cases h81 : Leg4Land (armG ρ' i') (L' + 9) (L' + 8) (L' + 1) (L' + 6) ∧
      Leg4Land (armT ρ' i') (L' + 9) (L' + 8) (L' + 1) (L' + 6)
  · exact s3_span_nine_mid5_of_leg4Land_direct ρ' i' L' (L' + 8) (L' + 1) (L' + 6) hlip' hLb' hHb'
      hp' (leg4Window_w81 L') (by omega) (by omega) h81.1 h81.2
  exact h n' ρ' σ' i' L' hlip' hcr' hLb' hHb' hp' hG' hT' h8 h3 hb h72 h81

end HPC.Fold
