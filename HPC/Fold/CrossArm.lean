import HPC.Fold.Span9Profile

/-!
# The cross-arm clause, and the span-nine reduction

Every fold lemma in the repository so far reads crookedness *inside one arm*: `crookUp_armG`,
`crookDown_armG` and their reflections apply the clause to two times on the same side of the
basepoint. The clause of `IsCrookedIvF` is not restricted in that way — it applies to any two
times of the sequence, and in particular to one time on each arm. This file records that form,

* `crookUp_seq`, `crookDown_seq` — `CrookUp ρ` and `CrookDown ρ` for the whole sequence,

and uses it for the configuration the profile criteria of `HPC/Fold/Profile.lean` leave open at
span nine: a basepoint whose forward arm never meets the floor of the band and whose backward arm
never meets its ceiling. Such a basepoint does not exist (`no_arm_split_high_low`,
`no_arm_split_low_high`): the two ends of the band are then forced onto opposite arms, and the
cross-arm clause between them lands a low time on the high arm or a high time on the low arm.

The second half of the file is bookkeeping that makes the remaining gap at span nine exact:

* `s3_span_nine_of_attained` — the span-nine statement follows from its special case in which
  both ends of the band are attained (if an end is missed the band shrinks and `s3_span_eight`
  applies);
* `s3_span_nine_of_mid` — with that reduction, `s3_span_nine` follows from the two branches of
  `s3_span_nine_except`, now with both ends of the band available as hypotheses.
-/

namespace HPC.Fold

/-! ## The clause across the basepoint -/

/-- **`CrookUp` for the whole sequence.** The crookedness clause of the faithful model applied to
two arbitrary times, which may lie on opposite sides of a basepoint. -/
theorem crookUp_seq {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) : CrookUp ρ := by
  intro s t hst hlev
  obtain ⟨r, r', h1, h2, h3, hcase, -⟩ :=
    hcr.crooked s t (Fin.lt_def.mpr hst) (ρ s) (ρ t)
      ⟨s, by simp, le_refl _, hcr.le _⟩ ⟨t, by simp, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hwr' := hcr.width r'
  exact ⟨r, r', h1, h2, h3, by omega, by omega, by omega, by omega⟩

/-- **`CrookDown` for the whole sequence.** -/
theorem crookDown_seq {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) : CrookDown ρ := by
  intro s t hst hlev
  obtain ⟨r, r', h1, h2, h3, -, hcase⟩ :=
    hcr.crooked s t (Fin.lt_def.mpr hst) (ρ s) (ρ t)
      ⟨s, by simp, le_refl _, hcr.le _⟩ ⟨t, by simp, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hwr' := hcr.width r'
  exact ⟨r, r', h1, h2, h3, by omega, by omega, by omega, by omega⟩

/-! ## Reading an arm at a global time -/

/-- A time at or after the basepoint, read on the forward arm. -/
theorem armG_at {n : ℕ} (ρ : Fin n → ℤ) (i j : Fin n) (h : i.val ≤ j.val) :
    armG ρ i ⟨j.val - i.val, by have := j.isLt; omega⟩ = ρ j := by
  show ρ ⟨i.val + (j.val - i.val), _⟩ = ρ j
  exact congrArg ρ (Fin.ext (by show i.val + (j.val - i.val) = j.val; omega))

/-- A time at or before the basepoint, read on the backward arm. -/
theorem armT_at {n : ℕ} (ρ : Fin n → ℤ) (i j : Fin n) (h : j.val ≤ i.val) :
    armT ρ i ⟨i.val - j.val, by omega⟩ = ρ j := by
  show ρ ⟨i.val - (i.val - j.val), _⟩ = ρ j
  exact congrArg ρ (Fin.ext (by show i.val - (i.val - j.val) = j.val; omega))

/-! ## No basepoint splits the two ends of the band -/

/-- **The cross-arm exclusion, upward form.** If the forward arm never drops to `A + 1` and the
backward arm never rises to `B - 2`, there is no pair of times, one at or before the basepoint at
level `A` or below, one at or after it at level `B` or above. -/
theorem no_split_low_before_high {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (A B : ℤ) (hAB : A + 3 ≤ B) (a b : Fin n) (ha : a.val ≤ i.val) (hb : i.val ≤ b.val)
    (hav : ρ a ≤ A) (hbv : B ≤ ρ b)
    (hG : ∀ j : Fin n, i.val ≤ j.val → A + 2 ≤ ρ j)
    (hT : ∀ j : Fin n, j.val ≤ i.val → ρ j ≤ B - 3) : False := by
  have hab : a.val < b.val := by
    rcases Nat.lt_or_ge a.val b.val with h | h
    · exact h
    · have : a.val = b.val := by omega
      have : ρ a = ρ b := by rw [Fin.ext this]
      omega
  obtain ⟨u, u', h1, h2, h3, h4, h5, h6, h7⟩ := crookUp_seq hcr a b hab (by omega)
  rcases Nat.lt_or_ge i.val u.val with hu | hu
  · exact absurd (hG u' (by omega)) (by omega)
  · exact absurd (hT u hu) (by omega)

/-- **The cross-arm exclusion, downward form.** The reflection of `no_split_low_before_high`: the
high time comes first, on the backward arm, and the low time last, on the forward arm. -/
theorem no_split_high_before_low {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (A B : ℤ) (hAB : A + 3 ≤ B) (a b : Fin n) (ha : a.val ≤ i.val) (hb : i.val ≤ b.val)
    (hav : B ≤ ρ a) (hbv : ρ b ≤ A)
    (hG : ∀ j : Fin n, i.val ≤ j.val → ρ j ≤ B - 3)
    (hT : ∀ j : Fin n, j.val ≤ i.val → A + 2 ≤ ρ j) : False := by
  have hab : a.val < b.val := by
    rcases Nat.lt_or_ge a.val b.val with h | h
    · exact h
    · have : a.val = b.val := by omega
      have : ρ a = ρ b := by rw [Fin.ext this]
      omega
  obtain ⟨u, u', h1, h2, h3, h4, h5, h6, h7⟩ := crookDown_seq hcr a b hab (by omega)
  rcases Nat.lt_or_ge i.val u.val with hu | hu
  · exact absurd (hG u' (by omega)) (by omega)
  · exact absurd (hT u hu) (by omega)

/-- **No basepoint of a span-nine sequence keeps its forward arm off the floor and its backward
arm off the ceiling.** If the forward arm never drops to `L + 1` then the level `L` is attained on
the backward arm, and if the backward arm never rises to `L + 7` then `L + 9` is attained on the
forward arm; the cross-arm clause between those two times then puts a level `L + 7` or above at a
time before the basepoint, or a level `L + 1` or below at a time after it. -/
theorem no_arm_split_high_low {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (L : ℤ) (hL : ∃ t, ρ t = L) (hH : ∃ t, ρ t = L + 9)
    (hGhigh : ∀ d, L + 2 ≤ armG ρ i d) (hTlow : ∀ d, armT ρ i d ≤ L + 6) : False := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨b, hb⟩ := hH
  have hGlev : ∀ j : Fin n, i.val ≤ j.val → L + 2 ≤ ρ j := by
    intro j hj
    have := hGhigh ⟨j.val - i.val, by have := j.isLt; omega⟩
    rwa [armG_at ρ i j hj] at this
  have hTlev : ∀ j : Fin n, j.val ≤ i.val → ρ j ≤ L + 6 := by
    intro j hj
    have := hTlow ⟨i.val - j.val, by omega⟩
    rwa [armT_at ρ i j hj] at this
  have hai : a.val ≤ i.val := by
    by_contra h
    exact absurd (hGlev a (by omega)) (by omega)
  have hbi : i.val ≤ b.val := by
    by_contra h
    exact absurd (hTlev b (by omega)) (by omega)
  exact no_split_low_before_high hcr i L (L + 9) (by omega) a b hai hbi (by omega) (by omega)
    hGlev (fun j hj => by have := hTlev j hj; omega)

/-- The reflection of `no_arm_split_high_low`: the forward arm never rises to `L + 7` and the
backward arm never drops to `L + 1`. -/
theorem no_arm_split_low_high {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (L : ℤ) (hL : ∃ t, ρ t = L) (hH : ∃ t, ρ t = L + 9)
    (hGlow : ∀ d, armG ρ i d ≤ L + 6) (hThigh : ∀ d, L + 2 ≤ armT ρ i d) : False := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨b, hb⟩ := hH
  have hGlev : ∀ j : Fin n, i.val ≤ j.val → ρ j ≤ L + 6 := by
    intro j hj
    have := hGlow ⟨j.val - i.val, by have := j.isLt; omega⟩
    rwa [armG_at ρ i j hj] at this
  have hTlev : ∀ j : Fin n, j.val ≤ i.val → L + 2 ≤ ρ j := by
    intro j hj
    have := hThigh ⟨i.val - j.val, by omega⟩
    rwa [armT_at ρ i j hj] at this
  have hbi : b.val ≤ i.val := by
    by_contra h
    exact absurd (hGlev b (by omega)) (by omega)
  have hai : i.val ≤ a.val := by
    by_contra h
    exact absurd (hTlev a (by omega)) (by omega)
  exact no_split_high_before_low hcr i L (L + 9) (by omega) b a hbi hai (by omega) (by omega)
    (fun j hj => by have := hGlev j hj; omega) hTlev

/-! ## The vacuous mixed case at span nine -/

/-- **Span nine, the mixed case with both criteria vacuous.** At a span-nine basepoint the
Λ-criterion of `HPC/Fold/Profile.lean` holds vacuously for an arm that never drops to `L + 1`,
and the V-criterion holds vacuously for an arm that never rises to `L + 7`; the two together at
one basepoint — the forward arm served only by the Λ-walk, the backward arm served only by the
V-walk — cannot occur. -/
theorem s3_span_nine_no_vacuous_mix {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n)
    (L : ℤ) (hL : ∃ t, ρ t = L) (hH : ∃ t, ρ t = L + 9)
    (hG : ∀ d, L + 2 ≤ armG ρ i d) (hT : ∀ d, armT ρ i d ≤ L + 6) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  absurd (no_arm_split_high_low hcr i L hL hH hG hT) (fun h => h)

/-- The reflection of `s3_span_nine_no_vacuous_mix`. -/
theorem s3_span_nine_no_vacuous_mix' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hL : ∃ t, ρ t = L) (hH : ∃ t, ρ t = L + 9)
    (hG : ∀ d, armG ρ i d ≤ L + 6) (hT : ∀ d, L + 2 ≤ armT ρ i d) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  absurd (no_arm_split_low_high hcr i L hL hH hG hT) (fun h => h)

/-! ## The reduction of span nine to the attained case -/

/-- **Both ends of the band may be assumed attained.** If the sequence misses an end of a
nine-wide band, it lies in an eight-wide band and `s3_span_eight` serves every basepoint. -/
theorem s3_span_nine_of_attained
    (key : ∀ {m : ℕ} (ρ' σ' : Fin m → ℤ) (i' : Fin m) (L' : ℤ), IsLip ρ' → IsCrookedIvF ρ' σ' →
      (∀ t, L' ≤ ρ' t) → (∀ t, ρ' t ≤ L' + 9) → (∃ t, ρ' t = L') → (∃ t, ρ' t = L' + 9) →
      ∃ (len : ℕ) (c : ℕ → ℤ),
        FoldsOnto (armG ρ' i') len c ∧ FoldsOnto (armT ρ' i') len c)
    {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 9) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases h8 : H ≤ L + 8
  · exact s3_span_eight ρ σ i H L hlip hcr hLb hHb hLH h8
  · have hH9 : H = L + 9 := by omega
    subst hH9
    by_cases hLat : ∃ t, ρ t = L
    · by_cases hHat : ∃ t, ρ t = L + 9
      · exact key ρ σ i L hlip hcr hLb hHb hLat hHat
      · push_neg at hHat
        refine s3_span_eight ρ σ i (L + 8) L hlip hcr hLb (fun t => ?_) (by omega) (by omega)
        have := hHb t
        have := hHat t
        omega
    · push_neg at hLat
      refine s3_span_eight ρ σ i (L + 9) (L + 1) hlip hcr (fun t => ?_) hHb (by omega) (by omega)
      have := hLb t
      have := hLat t
      omega

/-- **What is left of span nine.** With both ends attained, the only basepoints not already served
are the two branches of `s3_span_nine_except`; so `s3_span_nine` follows from those two branches,
and this is the exact form in which they may now be attacked — the ends of the band, which the
cross-arm clause needs, are hypotheses. -/
theorem s3_span_nine_of_mid
    (key4 : ∀ {m : ℕ} (ρ' σ' : Fin m → ℤ) (i' : Fin m) (L' : ℤ), IsLip ρ' → IsCrookedIvF ρ' σ' →
      (∀ t, L' ≤ ρ' t) → (∀ t, ρ' t ≤ L' + 9) → (∃ t, ρ' t = L') → (∃ t, ρ' t = L' + 9) →
      ρ' i' = L' + 4 → HighAt (armG ρ' i') (L' + 1) (L' + 8) →
      HighAt (armT ρ' i') (L' + 1) (L' + 8) →
      ∃ (len : ℕ) (c : ℕ → ℤ),
        FoldsOnto (armG ρ' i') len c ∧ FoldsOnto (armT ρ' i') len c)
    (key5 : ∀ {m : ℕ} (ρ' σ' : Fin m → ℤ) (i' : Fin m) (L' : ℤ), IsLip ρ' → IsCrookedIvF ρ' σ' →
      (∀ t, L' ≤ ρ' t) → (∀ t, ρ' t ≤ L' + 9) → (∃ t, ρ' t = L') → (∃ t, ρ' t = L' + 9) →
      ρ' i' = L' + 5 → LowAt (armG ρ' i') (L' + 1) (L' + 8) →
      LowAt (armT ρ' i') (L' + 1) (L' + 8) →
      ∃ (len : ℕ) (c : ℕ → ℤ),
        FoldsOnto (armG ρ' i') len c ∧ FoldsOnto (armT ρ' i') len c)
    {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ H)
    (hLH : L + 3 ≤ H) (hspan : H ≤ L + 9) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  refine s3_span_nine_of_attained ?_ ρ σ i H L hlip hcr hLb hHb hLH hspan
  intro m ρ' σ' i' L' hlip' hcr' hLb' hHb' hLat hHat
  by_cases h4 : ρ' i' = L' + 4 ∧
      HighAt (armG ρ' i') (L' + 1) (L' + 8) ∧ HighAt (armT ρ' i') (L' + 1) (L' + 8)
  · exact key4 ρ' σ' i' L' hlip' hcr' hLb' hHb' hLat hHat h4.1 h4.2.1 h4.2.2
  · by_cases h5 : ρ' i' = L' + 5 ∧
        LowAt (armG ρ' i') (L' + 1) (L' + 8) ∧ LowAt (armT ρ' i') (L' + 1) (L' + 8)
    · exact key5 ρ' σ' i' L' hlip' hcr' hLb' hHb' hLat hHat h5.1 h5.2.1 h5.2.2
    · refine s3_span_nine_except ρ' σ' i' (L' + 9) L' hlip' hcr' hLb' hHb' (by omega) (by omega)
        (Or.inr ⟨fun hp => ?_, fun hp => ?_⟩)
      · exact fun hh => h4 ⟨hp, hh.1, hh.2⟩
      · exact fun hh => h5 ⟨hp, hh.1, hh.2⟩

end HPC.Fold
