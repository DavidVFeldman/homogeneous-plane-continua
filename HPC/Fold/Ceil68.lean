import HPC.Fold.Mid2Index67

/-!
# The ceiling clause of `w71`, read from the pairing the other way

Batch 67 reads the pairing `crooked_peak_valley_high9` between a link at `L + 1` or below and a
link carrying `L + 9` in one direction: from the `w8` side's time at `L + 9` it supplies the
*partner* with `w3`'s ceiling clause. This file reads it the other way, inside a single arm:

> if the arm has been at `L + 1` or below before one of its own times at `L + 9`, then the peak and
> the valley the pairing returns are times of that same arm, and they are exactly the two landmarks
> `w71`'s ceiling clause asks for — a time at `L + 6` or above at arm index three or more, and,
> six steps later, a time at `L + 2` or below, itself seven steps before the ascent.

The levels the pairing returns — `L + 7` for the peak and `L + 2` for the valley — are one better in
each direction than `w71` asks (`L + 6` and `L + 2`), and the spacings it returns — `169` and `70`
and `169` — are far more than the `6` and the `7` of the clause. So the answer to the question is
that the pairing does read the other way, and at the level `w71` asks for.

Reading the same pairing against a link at `L + 2` gives a valley at `L + 3` or below, which is what
`w72`'s ceiling clause asks for instead; that variant is here too.

With the clause in hand the rest of `w71` is already owned by every arm of the branch:

* at a descent to `L + 1` or below the floor clause comes from whichever of `w8`, `w3`, `wb` serves
  the arm (`leg4Land_tri`, and the three floor lemmas of `HPC/Fold/CrossW71.lean`);
* at a descent to exactly `L + 2` it is `Mid2Floor`, which at a crossing of the trichotomy is the
  batch-67 theorem `crossMid2`;
* the deep clause of `w71` triggers at `L - 1` and is vacuous inside the band.

Hence `leg4Land_w71_of_tri_of_mid2_of_ceil`, `w71_armG_of_deepFirst`, and the fold:
`s3_span_nine_mid5_of_deepFirst` — a basepoint of the branch at `L + 5` both of whose arms satisfy
`Mid2Floor` and descend to `L + 1` before each of their own times at `L + 9` folds, onto `w71`
itself — and `s3_span_nine_mid5_of_cross_deepFirst`, where `Mid2Floor` is supplied by `crossMid2`
and only the descents are asked for.
-/

namespace HPC.Fold

/-! ## The two ceiling clauses, named -/

section Arm

variable {m : ℕ} {f : Fin m → ℤ} {L : ℤ}

/-- **The ceiling clause of `w71`**, written out: before every ascent to `L + 9`, a time at `L + 6`
or above at arm index three or more and, six steps later, a time at `L + 2` or below, itself
`f d - (L + 2)` steps before the ascent. This is the third clause of `Leg4Land f (L+9) (L+7) (L+1)
(L+5)`. -/
def Ceil71 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
    (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧
    L + 6 ≤ f j ∧ f k ≤ L + 2

/-- **The ceiling clause of `w72`**, one level lower in its valley and one step shorter in its two
gaps. This is the third clause of `Leg4Land f (L+9) (L+7) (L+2) (L+5)`. -/
def Ceil72 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧
    (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧ (k.val : ℤ) + (f d - (L + 3)) ≤ (d.val : ℤ) ∧
    L + 6 ≤ f j ∧ f k ≤ L + 3

/-- **Deep first at `L + 2`.** Before every ascent to `L + 9` the arm has been at `L + 2` or below.
This is `DeepFirst` with its level raised by one, and it is what the pairing needs to return a
valley at `L + 3` or below. -/
def DeepFirst2 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ e : Fin m, L + 9 ≤ f e → ∃ d : Fin m, d.val < e.val ∧ f d ≤ L + 2

theorem deepFirst2_of_deepFirst (h : DeepFirst f L) : DeepFirst2 f L := by
  intro e he
  obtain ⟨d, h1, h2⟩ := h e he
  exact ⟨d, h1, by omega⟩

/-- **The ceiling clause at one ascent, from a descent to exactly `L + 2` before it.** No pairing is
needed here: `Mid2Floor` supplies the peak, and the timing law supplies both gaps — four levels
between the peak and the descent cost twelve steps (`z 4 = 13`), and seven levels between the
descent and the ascent cost 169 (`z 7 = 170`), where the clause asks for six and seven. -/
theorem ceil71_at_of_mid2_of_sep (hsep : ArmSep f) (hH : ∀ j, f j ≤ L + 9) (hmid : Mid2Floor f L)
    (d e : Fin m) (hed : e.val < d.val) (he : f e = L + 2) (hd : L + 9 ≤ f d) :
    ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (f d - (L + 2)) ≤ (d.val : ℤ) ∧ L + 6 ≤ f j ∧ f k ≤ L + 2 := by
  obtain ⟨j, hj3, hj4, hj6⟩ := hmid e he
  have hz4 : z 4 = 13 := by decide
  have hz7 : z 7 = 170 := by decide
  have h1 : j.val + 12 ≤ e.val := by
    rcases hsep 4 e j (by omega) (by omega) with h | h
    · omega
    · omega
  have h2 : e.val + 169 ≤ d.val := by
    rcases hsep 7 e d (by omega) (by omega) with h | h
    · omega
    · omega
  have hdH := hH d
  exact ⟨j, e, hj3, by omega, by omega, hj6, by omega⟩

/-- **`w71` from the trichotomy, the floor clause at `L + 2`, and the ceiling clause.** An arm of
the band `[L, L + 9]` based at `L + 5` which meets the branch hypothesis owes `w71` nothing but its
descents to exactly `L + 2` and its ascents to `L + 9`: the floor clause at the descents to `L + 1`
or below comes from whichever of the three walks of `leg4Land_tri` serves it, and the deep clause of
`w71` is vacuous inside the band. -/
theorem leg4Land_w71_of_tri_of_mid2_of_ceil (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) (hlow : LowAt f (L + 1) (L + 8))
    (hmid : Mid2Floor f L) (hceil : Ceil71 f L) :
    Leg4Land f (L + 9) (L + 7) (L + 1) (L + 5) := by
  have hfloor : ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (L + 6 - f d) ≤ (d.val : ℤ) ∧ L + 6 ≤ f j := by
    rcases leg4Land_tri hm hf h0 hL hH hlow with h8 | h3 | hb
    · intro d hd
      obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · exact land_w71_floor_low1_of_w3 h3
    · exact land_w71_floor_low1_of_wb hb
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases eq_or_lt_of_le hd with heq | hlt
    · obtain ⟨j, h1, h2, h3⟩ := hmid d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · obtain ⟨j, h1, h2, h3⟩ := hfloor d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hceil d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **`w72` from the trichotomy, the floor clause at `L + 2`, its deep-floor clause and its ceiling
clause.** The same reading for the walk one level lower. -/
theorem leg4Land_w72_of_tri_of_mid2_of_ceil (hm : 0 < m) (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5)
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) (hlow : LowAt f (L + 1) (L + 8))
    (hmid : Mid2Floor f L) (hdeep : Deep72 f L) (hceil : Ceil72 f L) :
    Leg4Land f (L + 9) (L + 7) (L + 2) (L + 5) := by
  have hfloor : ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 3 ≤ (j.val : ℤ) ∧
      (j.val : ℤ) + (L + 6 - f d) ≤ (d.val : ℤ) ∧ L + 6 ≤ f j := by
    rcases leg4Land_tri hm hf h0 hL hH hlow with h8 | h3 | hb
    · intro d hd
      obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · exact land_w71_floor_low1_of_w3 h3
    · exact land_w71_floor_low1_of_wb hb
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases eq_or_lt_of_le hd with heq | hlt
    · obtain ⟨j, h1, h2, h3⟩ := hmid d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
    · obtain ⟨j, h1, h2, h3⟩ := hfloor d (by omega)
      exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    obtain ⟨j, k, l, h1, h2, h3, h4, h5, h6, h7⟩ := hdeep d (by omega)
    exact ⟨j, k, l, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro d hd
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hceil d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

end Arm

/-! ## The pairing, read inside one arm -/

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-- **The pairing against a link at `L + 2` or below.** `crooked_peak_valley_high9` asks for a link
at `L + 1`; one level higher the same reading still returns a peak carrying `L + 8`, and a valley at
`ρ a + 1` or below — now `L + 3` — with the timing law spacing the three `70`, `29`, `70` instead of
`169`, `70`, `169` (six levels and five, rather than seven and six). -/
theorem crooked_peak_valley_high9_mid (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha : ρ a ≤ L + 2)
    (hb1 : ρ b ≤ L + 9) (hb2 : L + 9 ≤ σ b) :
    ∃ r r' : Fin n, a.val + 70 ≤ r.val ∧ r.val + 29 ≤ r'.val ∧ r'.val + 70 ≤ b.val ∧
      L + 7 ≤ ρ r ∧ L + 8 ≤ σ r ∧ ρ r' ≤ ρ a + 1 ∧ ρ a + 1 ≤ σ r' := by
  obtain ⟨r, r', har, hrr', hr'b, hcase, -⟩ :=
    hcr.crooked a b (Fin.lt_def.mpr hab) (ρ a) (L + 9)
      ⟨a, by simp, le_rfl, hcr.le a⟩ ⟨b, by simp, hb1, hb2⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  have hwr := hcr.width r
  have harv : a.val < r.val := har
  have hrr'v : r.val < r'.val := hrr'
  have hr'bv : r'.val < b.val := hr'b
  have hz5 : z 5 = 30 := by decide
  have hz6 : z 6 = 71 := by decide
  have h1 : a.val + 70 ≤ r.val := by
    rcases ivSep hcr a r (by omega) 6 (ρ a) (L + 9 - 1) (by push_cast; omega)
      le_rfl (hcr.le a) hr1 hr2 with h | h
    · omega
    · omega
  have h2 : r.val + 29 ≤ r'.val := by
    rcases ivSep hcr r' r (by omega) 5 (ρ a + 1) (L + 9 - 1) (by push_cast; omega)
      hr'1 hr'2 hr1 hr2 with h | h
    · omega
    · omega
  have h3 : r'.val + 70 ≤ b.val := by
    rcases ivSep hcr r' b (by omega) 6 (ρ a + 1) (L + 9) (by push_cast; omega)
      hr'1 hr'2 hb1 hb2 with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, h3, by omega, by omega, hr'1, hr'2⟩

/-- **The same pair read from the high link.** -/
theorem crooked_valley_peak_high9_mid (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha1 : ρ a ≤ L + 9) (ha2 : L + 9 ≤ σ a)
    (hb : ρ b ≤ L + 2) :
    ∃ r r' : Fin n, a.val + 70 ≤ r.val ∧ r.val + 29 ≤ r'.val ∧ r'.val + 70 ≤ b.val ∧
      ρ r ≤ ρ b + 1 ∧ ρ b + 1 ≤ σ r ∧ L + 7 ≤ ρ r' ∧ L + 8 ≤ σ r' := by
  obtain ⟨r, r', har, hrr', hr'b, -, hcase⟩ :=
    hcr.crooked a b (Fin.lt_def.mpr hab) (L + 9) (ρ b)
      ⟨a, by simp, ha1, ha2⟩ ⟨b, by simp, le_rfl, hcr.le b⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  have hwr' := hcr.width r'
  have harv : a.val < r.val := har
  have hrr'v : r.val < r'.val := hrr'
  have hr'bv : r'.val < b.val := hr'b
  have hz5 : z 5 = 30 := by decide
  have hz6 : z 6 = 71 := by decide
  have h1 : a.val + 70 ≤ r.val := by
    rcases ivSep hcr r a (by omega) 6 (ρ b + 1) (L + 9) (by push_cast; omega)
      hr1 hr2 ha1 ha2 with h | h
    · omega
    · omega
  have h2 : r.val + 29 ≤ r'.val := by
    rcases ivSep hcr r r' (by omega) 5 (ρ b + 1) (L + 9 - 1) (by push_cast; omega)
      hr1 hr2 hr'1 hr'2 with h | h
    · omega
    · omega
  have h3 : r'.val + 70 ≤ b.val := by
    rcases ivSep hcr b r' (by omega) 6 (ρ b) (L + 9 - 1) (by push_cast; omega)
      le_rfl (hcr.le b) hr'1 hr'2 with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, h3, hr1, hr2, by omega, by omega⟩

/-- **The ceiling clause of `w71` on the forward arm, from the pairing.** An arm that has been at
`L + 1` or below before each of its own times at `L + 9` has the clause: the low link and the
ascent are both times of the arm, so the peak and the valley the pairing returns between them are
times of the arm too. -/
theorem ceil71_at_of_low1_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (d e : Fin (n - i.val)) (hed : e.val < d.val)
    (he : armG ρ i e ≤ L + 1) (hd : L + 9 ≤ armG ρ i d) :
    ∃ j k : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armG ρ i d - (L + 2)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 2 := by
  have hi := i.isLt
  have hdn := d.isLt
  have hen := e.isLt
  have hAlt : i.val + e.val < n := by omega
  have hBlt : i.val + d.val < n := by omega
  set A : Fin n := ⟨i.val + e.val, hAlt⟩ with hAdef
  set B : Fin n := ⟨i.val + d.val, hBlt⟩ with hBdef
  have hAv : ρ A = armG ρ i e := rfl
  have hBv : ρ B = armG ρ i d := rfl
  have hab : A.val < B.val := by simp only [hAdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr7, -, hr'1, -⟩ :=
    crooked_peak_valley_high9 hcr A B hab L (by rw [hAv]; omega)
      (by rw [hBv]; exact hHb _) (by have := hcr.le B; rw [hBv] at this; omega)
  have hAval : A.val = i.val + e.val := rfl
  have hBval : B.val = i.val + d.val := rfl
  have hjlt : r.val - i.val < n - i.val := by omega
  have hklt : r'.val - i.val < n - i.val := by omega
  have hjv : armG ρ i ⟨r.val - i.val, hjlt⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
  have hkv : armG ρ i ⟨r'.val - i.val, hklt⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
  have hAle : ρ A ≤ L + 1 := by rw [hAv]; omega
  refine ⟨⟨r.val - i.val, hjlt⟩, ⟨r'.val - i.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    have : armG ρ i d ≤ L + 9 := by rw [← hBv]; exact hHb _
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-- **The mirror, on the backward arm.** The backward arm runs against the chain, so the pairing is
read from the high link: the peak comes first in arm order and the valley after it. -/
theorem ceil71_at_of_low1_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (d e : Fin (i.val + 1)) (hed : e.val < d.val)
    (he : armT ρ i e ≤ L + 1) (hd : L + 9 ≤ armT ρ i d) :
    ∃ j k : Fin (i.val + 1), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 6 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armT ρ i d - (L + 2)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armT ρ i j ∧ armT ρ i k ≤ L + 2 := by
  have hi := i.isLt
  have hdn := d.isLt
  have hen := e.isLt
  have hAlt : i.val - e.val < n := by omega
  have hBlt : i.val - d.val < n := by omega
  set A : Fin n := ⟨i.val - e.val, hAlt⟩ with hAdef
  set B : Fin n := ⟨i.val - d.val, hBlt⟩ with hBdef
  have hAv : ρ A = armT ρ i e := rfl
  have hBv : ρ B = armT ρ i d := rfl
  have hab : B.val < A.val := by simp only [hAdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, -, hr'7, -⟩ :=
    crooked_valley_peak_high9 hcr B A hab L (by rw [hBv]; exact hHb _)
      (by have := hcr.le B; rw [hBv] at this; omega) (by rw [hAv]; omega)
  have hAval : A.val = i.val - e.val := rfl
  have hBval : B.val = i.val - d.val := rfl
  have hjlt : i.val - r'.val < i.val + 1 := by omega
  have hklt : i.val - r.val < i.val + 1 := by omega
  have hjv : armT ρ i ⟨i.val - r'.val, hjlt⟩ = ρ r' := by
    show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)
  have hkv : armT ρ i ⟨i.val - r.val, hklt⟩ = ρ r := by
    show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
  have hAle : ρ A ≤ L + 1 := by rw [hAv]; omega
  refine ⟨⟨i.val - r'.val, hjlt⟩, ⟨i.val - r.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    have : armT ρ i d ≤ L + 9 := by rw [← hBv]; exact hHb _
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-- **The `w72` reading of the same pairing on the forward arm.** Against a link at `L + 2` the
valley comes back at `L + 3` or below, which is the level `w72`'s ceiling clause asks for. -/
theorem ceil72_of_deepFirst2_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hdeep : DeepFirst2 (armG ρ i) L) :
    Ceil72 (armG ρ i) L := by
  intro d hd
  have hi := i.isLt
  have hdn := d.isLt
  obtain ⟨e, hed, he⟩ := hdeep d hd
  have hen := e.isLt
  have hAlt : i.val + e.val < n := by omega
  have hBlt : i.val + d.val < n := by omega
  set A : Fin n := ⟨i.val + e.val, hAlt⟩ with hAdef
  set B : Fin n := ⟨i.val + d.val, hBlt⟩ with hBdef
  have hAv : ρ A = armG ρ i e := rfl
  have hBv : ρ B = armG ρ i d := rfl
  have hab : A.val < B.val := by simp only [hAdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr7, -, hr'1, -⟩ :=
    crooked_peak_valley_high9_mid hcr A B hab L (by rw [hAv]; omega)
      (by rw [hBv]; exact hHb _) (by have := hcr.le B; rw [hBv] at this; omega)
  have hAval : A.val = i.val + e.val := rfl
  have hBval : B.val = i.val + d.val := rfl
  have hjlt : r.val - i.val < n - i.val := by omega
  have hklt : r'.val - i.val < n - i.val := by omega
  have hjv : armG ρ i ⟨r.val - i.val, hjlt⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
  have hkv : armG ρ i ⟨r'.val - i.val, hklt⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
  have hAle : ρ A ≤ L + 2 := by rw [hAv]; omega
  refine ⟨⟨r.val - i.val, hjlt⟩, ⟨r'.val - i.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    have : armG ρ i d ≤ L + 9 := by rw [← hBv]; exact hHb _
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-- **The mirror of the `w72` reading, on the backward arm.** -/
theorem ceil72_of_deepFirst2_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hdeep : DeepFirst2 (armT ρ i) L) :
    Ceil72 (armT ρ i) L := by
  intro d hd
  have hi := i.isLt
  have hdn := d.isLt
  obtain ⟨e, hed, he⟩ := hdeep d hd
  have hen := e.isLt
  have hAlt : i.val - e.val < n := by omega
  have hBlt : i.val - d.val < n := by omega
  set A : Fin n := ⟨i.val - e.val, hAlt⟩ with hAdef
  set B : Fin n := ⟨i.val - d.val, hBlt⟩ with hBdef
  have hAv : ρ A = armT ρ i e := rfl
  have hBv : ρ B = armT ρ i d := rfl
  have hab : B.val < A.val := by simp only [hAdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, -, hr'7, -⟩ :=
    crooked_valley_peak_high9_mid hcr B A hab L (by rw [hBv]; exact hHb _)
      (by have := hcr.le B; rw [hBv] at this; omega) (by rw [hAv]; omega)
  have hAval : A.val = i.val - e.val := rfl
  have hBval : B.val = i.val - d.val := rfl
  have hjlt : i.val - r'.val < i.val + 1 := by omega
  have hklt : i.val - r.val < i.val + 1 := by omega
  have hjv : armT ρ i ⟨i.val - r'.val, hjlt⟩ = ρ r' := by
    show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)
  have hkv : armT ρ i ⟨i.val - r.val, hklt⟩ = ρ r := by
    show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
  have hAle : ρ A ≤ L + 2 := by rw [hAv]; omega
  refine ⟨⟨i.val - r'.val, hjlt⟩, ⟨i.val - r.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    have : armT ρ i d ≤ L + 9 := by rw [← hBv]; exact hHb _
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-! ## The ceiling clause in full -/

/-- **The ceiling clause of `w71` on the forward arm.** An arm that has been at `L + 2` or below
before each of its own times at `L + 9`, and that satisfies `Mid2Floor`, has the clause: where the
earlier time is at `L + 1` or below the pairing gives it, and where it is at exactly `L + 2` the
floor clause and the timing law give it with no pairing at all. -/
theorem ceil71_of_deepFirst2_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hmid : Mid2Floor (armG ρ i) L)
    (hdeep : DeepFirst2 (armG ρ i) L) :
    Ceil71 (armG ρ i) L := by
  intro d hd
  obtain ⟨e, hed, he⟩ := hdeep d hd
  rcases eq_or_lt_of_le he with heq | hlt
  · exact ceil71_at_of_mid2_of_sep (armG_armSep hcr i) (fun _ => hHb _) hmid d e hed heq hd
  · exact ceil71_at_of_low1_armG hcr i L hHb d e hed (by omega) hd

/-- **The mirror, on the backward arm.** -/
theorem ceil71_of_deepFirst2_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hmid : Mid2Floor (armT ρ i) L)
    (hdeep : DeepFirst2 (armT ρ i) L) :
    Ceil71 (armT ρ i) L := by
  intro d hd
  obtain ⟨e, hed, he⟩ := hdeep d hd
  rcases eq_or_lt_of_le he with heq | hlt
  · exact ceil71_at_of_mid2_of_sep (armT_armSep hcr i) (fun _ => hHb _) hmid d e hed heq hd
  · exact ceil71_at_of_low1_armT hcr i L hHb d e hed (by omega) hd

/-- **Deep first is enough on the forward arm**, with no hypothesis on the floor clause: the
pairing alone gives the ceiling clause there. -/
theorem ceil71_of_deepFirst_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hdeep : DeepFirst (armG ρ i) L) :
    Ceil71 (armG ρ i) L := by
  intro d hd
  obtain ⟨e, hed, he⟩ := hdeep d hd
  exact ceil71_at_of_low1_armG hcr i L hHb d e hed he hd

/-- **The mirror.** -/
theorem ceil71_of_deepFirst_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hdeep : DeepFirst (armT ρ i) L) :
    Ceil71 (armT ρ i) L := by
  intro d hd
  obtain ⟨e, hed, he⟩ := hdeep d hd
  exact ceil71_at_of_low1_armT hcr i L hHb d e hed he hd

/-! ## `w71` on an arm of the branch, and the fold -/

/-- **The forward arm of a basepoint of the branch, with `Mid2Floor` and deep first at `L + 2`,
satisfies `w71`.** -/
theorem w71_armG_of_deepFirst2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8))
    (hmid : Mid2Floor (armG ρ i) L) (hdeep : DeepFirst2 (armG ρ i) L) :
    Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 1) (L + 5) := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  exact leg4Land_w71_of_tri_of_mid2_of_ceil hmG (armG_isLip hlip i) h0G (fun j => hLb _)
    (fun j => hHb _) hGlow hmid (ceil71_of_deepFirst2_armG hcr i L hHb hmid hdeep)

/-- **The backward arm, likewise.** -/
theorem w71_armT_of_deepFirst2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hmid : Mid2Floor (armT ρ i) L) (hdeep : DeepFirst2 (armT ρ i) L) :
    Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 1) (L + 5) := by
  have hi := i.isLt
  have hmT : 0 < i.val + 1 := by omega
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  exact leg4Land_w71_of_tri_of_mid2_of_ceil hmT (armT_isLip hlip i) h0T (fun j => hLb _)
    (fun j => hHb _) hTlow hmid (ceil71_of_deepFirst2_armT hcr i L hHb hmid hdeep)

/-- **The pair folds where both arms satisfy `Mid2Floor` and are deep first at `L + 2`.** The walk
is `w71` itself, `L+4 → L+7 → L+1 → L+8 → L+1`. -/
theorem s3_span_nine_mid5_of_deepFirst2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hmidG : Mid2Floor (armG ρ i) L) (hmidT : Mid2Floor (armT ρ i) L)
    (hdeepG : DeepFirst2 (armG ρ i) L) (hdeepT : DeepFirst2 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 1) (L + 5) hlip hLb hHb hp
    (leg4Window_w71 L) (by omega) (by omega)
    (w71_armG_of_deepFirst2 hcr hlip i L hp hLb hHb hGlow hmidG hdeepG)
    (w71_armT_of_deepFirst2 hcr hlip i L hp hLb hHb hTlow hmidT hdeepT)

/-- **At a crossing of the trichotomy, deep first at `L + 2` on both arms is enough.** `Mid2Floor`
is the batch-67 theorem `crossMid2` there, so the only hypothesis left is that each arm descends to
`L + 2` or below before each of its own times at `L + 9` — vacuous on an arm that never reaches
`L + 9`. -/
theorem s3_span_nine_mid5_of_cross_deepFirst2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (hdeepG : DeepFirst2 (armG ρ i) L) (hdeepT : DeepFirst2 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  obtain ⟨hmidT, hmidG⟩ := crossMid2 hcr hlip i L hp hLb hHb hGlow hTlow hcross
  exact s3_span_nine_mid5_of_deepFirst2 hcr hlip i L hp hLb hHb hGlow hTlow hmidG hmidT
    hdeepG hdeepT

/-- **The same with `DeepFirst`**, the form batch 66 uses for `wb`: a descent to `L + 1` before each
ascent to `L + 9`. -/
theorem s3_span_nine_mid5_of_cross_deepFirst (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (hdeepG : DeepFirst (armG ρ i) L) (hdeepT : DeepFirst (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_deepFirst2 hcr hlip i L hp hLb hHb hGlow hTlow hcross
    (deepFirst2_of_deepFirst hdeepG) (deepFirst2_of_deepFirst hdeepT)

/-! ## The high run: where the arm reaches `L + 9` with nothing low before it

The one case the ceiling clause does not reach is an arm with an ascent to `L + 9` before which the
arm has never been at `L + 2` or below. There the pairing still fires, against a link of the
*partner*, and the valley it returns cannot be a time of the ascending arm — it would be the time at
`L + 2` or below that the run excludes. So both the peak and the valley are times of the partner,
and in the partner's own order they read valley, peak, descent: exactly the chain `w3`'s ceiling
clause asks for at that descent. -/

/-- **A high run on the forward arm gives the backward arm `w3`'s ceiling clause.** -/
theorem partner_w3ceil_of_highRun_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (d : Fin (n - i.val)) (hd : L + 9 ≤ armG ρ i d)
    (hrun : ∀ e : Fin (n - i.val), e.val < d.val → L + 3 ≤ armG ρ i e)
    (a : Fin (i.val + 1)) (ha : armT ρ i a ≤ L + 1) :
    ∃ j k : Fin (i.val + 1), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (L + 7 - armT ρ i a) ≤ (a.val : ℤ) ∧
      armT ρ i j ≤ L + 4 ∧ L + 7 ≤ armT ρ i k := by
  have hi := i.isLt
  have hdn := d.isLt
  have han := a.isLt
  have ha0 : 0 < a.val := by
    rcases Nat.eq_zero_or_pos a.val with h | h
    · exfalso
      have : armT ρ i a = ρ i := by
        show ρ ⟨i.val - a.val, _⟩ = ρ i
        congr 1
        exact Fin.ext (by show i.val - a.val = i.val; omega)
      omega
    · exact h
  have hAlt : i.val - a.val < n := by omega
  have hBlt : i.val + d.val < n := by omega
  set A : Fin n := ⟨i.val - a.val, hAlt⟩ with hAdef
  set B : Fin n := ⟨i.val + d.val, hBlt⟩ with hBdef
  have hAv : ρ A = armT ρ i a := rfl
  have hBv : ρ B = armG ρ i d := rfl
  have hAval : A.val = i.val - a.val := rfl
  have hBval : B.val = i.val + d.val := rfl
  have hab : A.val < B.val := by simp only [hAdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr7, -, hr'1, -⟩ :=
    crooked_peak_valley_high9 hcr A B hab L (by rw [hAv]; omega)
      (by rw [hBv]; exact hHb _) (by have := hcr.le B; rw [hBv] at this; omega)
  have hrn := r.isLt
  have hr'n := r'.isLt
  have hAle : ρ A ≤ L + 1 := by rw [hAv]; omega
  -- the valley is not a time of the ascending arm
  have hr'i : r'.val < i.val := by
    by_contra hc
    push_neg at hc
    have hlt : r'.val - i.val < n - i.val := by omega
    have hvv : armG ρ i ⟨r'.val - i.val, hlt⟩ = ρ r' := by
      show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
    have := hrun ⟨r'.val - i.val, hlt⟩ (by simp only []; omega)
    rw [hvv] at this
    omega
  have hjlt : i.val - r'.val < i.val + 1 := by omega
  have hklt : i.val - r.val < i.val + 1 := by omega
  have hjv : armT ρ i ⟨i.val - r'.val, hjlt⟩ = ρ r' := by
    show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)
  have hkv : armT ρ i ⟨i.val - r.val, hklt⟩ = ρ r := by
    show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
  -- the valley is at arm index three or more: the arm is within one of `L + 5` before that
  have hm : 0 < i.val + 1 := by omega
  have h0T : armT ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have hj3 : 3 ≤ i.val - r'.val := by
    have := isLip_index_gap' (armT_isLip hlip i) (j := ⟨0, hm⟩) (k := ⟨i.val - r'.val, hjlt⟩)
      (Nat.zero_le _) 3 (by rw [hjv, h0T]; omega)
    simp only [Nat.cast_zero, zero_add] at this
    omega
  have hLa : L ≤ armT ρ i a := by rw [← hAv]; exact hLb _
  refine ⟨⟨i.val - r'.val, hjlt⟩, ⟨i.val - r.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-- **The mirror: a high run on the backward arm gives the forward arm `w3`'s ceiling clause.** -/
theorem partner_w3ceil_of_highRun_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (d : Fin (i.val + 1)) (hd : L + 9 ≤ armT ρ i d)
    (hrun : ∀ e : Fin (i.val + 1), e.val < d.val → L + 3 ≤ armT ρ i e)
    (a : Fin (n - i.val)) (ha : armG ρ i a ≤ L + 1) :
    ∃ j k : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (L + 7 - armG ρ i a) ≤ (a.val : ℤ) ∧
      armG ρ i j ≤ L + 4 ∧ L + 7 ≤ armG ρ i k := by
  have hi := i.isLt
  have hdn := d.isLt
  have han := a.isLt
  have ha0 : 0 < a.val := by
    rcases Nat.eq_zero_or_pos a.val with h | h
    · exfalso
      have : armG ρ i a = ρ i := by
        show ρ ⟨i.val + a.val, _⟩ = ρ i
        congr 1
        exact Fin.ext (by show i.val + a.val = i.val; omega)
      omega
    · exact h
  have hAlt : i.val + a.val < n := by omega
  have hBlt : i.val - d.val < n := by omega
  set A : Fin n := ⟨i.val + a.val, hAlt⟩ with hAdef
  set B : Fin n := ⟨i.val - d.val, hBlt⟩ with hBdef
  have hAv : ρ A = armG ρ i a := rfl
  have hBv : ρ B = armT ρ i d := rfl
  have hAval : A.val = i.val + a.val := rfl
  have hBval : B.val = i.val - d.val := rfl
  have hab : B.val < A.val := by simp only [hAdef, hBdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, -, hr'7, -⟩ :=
    crooked_valley_peak_high9 hcr B A hab L (by rw [hBv]; exact hHb _)
      (by have := hcr.le B; rw [hBv] at this; omega) (by rw [hAv]; omega)
  have hrn := r.isLt
  have hr'n := r'.isLt
  have hAle : ρ A ≤ L + 1 := by rw [hAv]; omega
  -- the valley is not a time of the ascending arm
  have hri : i.val < r.val := by
    by_contra hc
    push_neg at hc
    have hlt : i.val - r.val < i.val + 1 := by omega
    have hvv : armT ρ i ⟨i.val - r.val, hlt⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    have := hrun ⟨i.val - r.val, hlt⟩ (by simp only []; omega)
    rw [hvv] at this
    omega
  have hjlt : r.val - i.val < n - i.val := by omega
  have hklt : r'.val - i.val < n - i.val := by omega
  have hjv : armG ρ i ⟨r.val - i.val, hjlt⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
  have hkv : armG ρ i ⟨r'.val - i.val, hklt⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
  have hm : 0 < n - i.val := by omega
  have h0G : armG ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have hj3 : 3 ≤ r.val - i.val := by
    have := isLip_index_gap' (armG_isLip hlip i) (j := ⟨0, hm⟩) (k := ⟨r.val - i.val, hjlt⟩)
      (Nat.zero_le _) 3 (by rw [hjv, h0G]; omega)
    simp only [Nat.cast_zero, zero_add] at this
    omega
  have hLa : L ≤ armG ρ i a := by rw [← hAv]; exact hLb _
  refine ⟨⟨r.val - i.val, hjlt⟩, ⟨r'.val - i.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-! ## The clause is exactly deep first at `L + 2` -/

/-- **The ceiling clause returns a time at `L + 2` or below before the ascent**, so it implies deep
first at `L + 2`. Together with `ceil71_of_deepFirst2_armG` this makes the two equivalent on an arm
of the branch that satisfies `Mid2Floor`. -/
theorem deepFirst2_of_ceil71 {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : Ceil71 f L) :
    DeepFirst2 f L := by
  intro e he
  obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := h e he
  exact ⟨k, by omega, h5⟩

/-- **`w71`'s third clause is `Ceil71`.** -/
theorem ceil71_of_w71 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : Leg4Land f (L + 9) (L + 7) (L + 1) (L + 5)) : Ceil71 f L := by
  intro d hd
  obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := h.2.2 d (by omega)
  exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **On the forward arm of a basepoint of the branch satisfying `Mid2Floor`, `w71` is exactly deep
first at `L + 2`.** -/
theorem w71_armG_iff_deepFirst2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hmid : Mid2Floor (armG ρ i) L) :
    Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ↔ DeepFirst2 (armG ρ i) L :=
  ⟨fun h => deepFirst2_of_ceil71 (ceil71_of_w71 h),
    fun h => w71_armG_of_deepFirst2 hcr hlip i L hp hLb hHb hGlow hmid h⟩

/-- **The mirror.** -/
theorem w71_armT_iff_deepFirst2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) (hmid : Mid2Floor (armT ρ i) L) :
    Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ↔ DeepFirst2 (armT ρ i) L :=
  ⟨fun h => deepFirst2_of_ceil71 (ceil71_of_w71 h),
    fun h => w71_armT_of_deepFirst2 hcr hlip i L hp hLb hHb hTlow hmid h⟩

/-! ## What the high run leaves: the partner on `w3` -/

/-- **A failure of `w8` is a failure of its floor clause.** Inside the band the other two clauses of
`w8` are vacuous — the deep clause triggers at `L - 1` and the ceiling clause at `L + 10` — so an
arm of the band that `w8` does not serve has a descent to `L + 2` or below with no time at `L + 7`
or above at index four or more and `L + 7 - f d` steps earlier. -/
theorem w8_floor_fail_of_not_w8 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (h : ¬ Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5)) :
    ∃ d₀ : Fin m, f d₀ ≤ L + 2 ∧
      ∀ j : Fin m, 4 ≤ (j.val : ℤ) → (j.val : ℤ) + (L + 7 - f d₀) ≤ (d₀.val : ℤ) →
        f j < L + 7 := by
  classical
  by_contra hc
  push_neg at hc
  refine h ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := hc d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    exact absurd (hL d) (by omega)
  · intro d hd
    exact absurd (hH d) (by omega)

/-- **At a basepoint whose forward arm has a high run, a backward arm that `w8` does not serve is
served by `w3`.** Its floor clause is the one every arm failing `w8` owns (`notW8_floor`), its deep
clause is vacuous in the band, and its ceiling clause is what the pairing hands it. -/
theorem leg4Land_w3_armT_of_highRun_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (d : Fin (n - i.val)) (hd : L + 9 ≤ armG ρ i d)
    (hrun : ∀ e : Fin (n - i.val), e.val < d.val → L + 3 ≤ armG ρ i e)
    (hnot8 : ¬ Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5)) :
    Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) := by
  have hi := i.isLt
  have hm : 0 < i.val + 1 := by omega
  have h0T : armT ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  obtain ⟨d₀, hd0, hfail⟩ :=
    w8_floor_fail_of_not_w8 (f := armT ρ i) (fun j => hLb _) (fun j => hHb _) hnot8
  have hfl := notW8_floor hm (armT_isLip hlip i) h0T hd0 hfail
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [armRefl_apply] at he ⊢
    obtain ⟨j, h1, h2, h3⟩ := hfl e (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro e he
    simp only [armRefl_apply] at he
    have hub : armT ρ i e ≤ L + 9 := hHb _
    omega
  · intro e he
    simp only [armRefl_apply] at he ⊢
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
      partner_w3ceil_of_highRun_armG hcr hlip i L hp hLb hHb d hd hrun e (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **The mirror.** -/
theorem leg4Land_w3_armG_of_highRun_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (d : Fin (i.val + 1)) (hd : L + 9 ≤ armT ρ i d)
    (hrun : ∀ e : Fin (i.val + 1), e.val < d.val → L + 3 ≤ armT ρ i e)
    (hnot8 : ¬ Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5)) :
    Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) := by
  have hi := i.isLt
  have hm : 0 < n - i.val := by omega
  have h0G : armG ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  obtain ⟨d₀, hd0, hfail⟩ :=
    w8_floor_fail_of_not_w8 (f := armG ρ i) (fun j => hLb _) (fun j => hHb _) hnot8
  have hfl := notW8_floor hm (armG_isLip hlip i) h0G hd0 hfail
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [armRefl_apply] at he ⊢
    obtain ⟨j, h1, h2, h3⟩ := hfl e (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro e he
    simp only [armRefl_apply] at he
    have hub : armG ρ i e ≤ L + 9 := hHb _
    omega
  · intro e he
    simp only [armRefl_apply] at he ⊢
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
      partner_w3ceil_of_highRun_armT hcr hlip i L hp hLb hHb d hd hrun e (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **At a crossing, a high run on one arm puts the other arm on `w3`.** At a crossing no walk of
the trichotomy serves both arms, so the two arms cannot both be served by `w8`; whichever arm has
the high run, its partner then fails `w8` unless it is the `w8` side itself. This is the form the
census measures: where the `w8` side runs high to `L + 9`, the partner is a `w3` arm. -/
theorem cross_partner_w3_of_highRun_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (d : Fin (n - i.val)) (hd : L + 9 ≤ armG ρ i d)
    (hrun : ∀ e : Fin (n - i.val), e.val < d.val → L + 3 ≤ armG ρ i e) :
    Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) :=
  leg4Land_w3_armT_of_highRun_armG hcr hlip i L hp hLb hHb d hd hrun
    (fun hT8 => hcross.1 ⟨h8, hT8⟩)

/-- **The mirror.** -/
theorem cross_partner_w3_of_highRun_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n)
    (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (d : Fin (i.val + 1)) (hd : L + 9 ≤ armT ρ i d)
    (hrun : ∀ e : Fin (i.val + 1), e.val < d.val → L + 3 ≤ armT ρ i e) :
    Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) :=
  leg4Land_w3_armG_of_highRun_armT hcr hlip i L hp hLb hHb d hd hrun
    (fun hG8 => hcross.1 ⟨hG8, h8⟩)

/-! ## The partner's walk, where the partner stops below `L + 9` -/

/-- **`w3` implies `wb` on an arm that never reaches `L + 9`.** The two walks differ in one clause
only — `wb`'s deep clause, whose trigger on the reflected arm is `L`, that is a time of the arm at
`L + 9` — and `w3`'s ceiling clause is the stronger of the two. -/
theorem leg4Land_wb_of_w3_of_no_nine {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h3 : Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 1) (L + 4))
    (hnine : ∀ j, f j ≤ L + 8) :
    Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4) := by
  refine ⟨h3.1, ?_, ?_⟩
  · intro d hd
    simp only [armRefl_apply] at hd
    exact absurd (hnine d) (by omega)
  · intro d hd
    obtain ⟨j, k, h1, h2, h3', h4, h5⟩ := h3.2.2 d (by omega)
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **An arm of the branch that `w8` does not serve and that never reaches `L + 9` is served by
`wb`.** -/
theorem leg4Land_wb_of_not_w8_of_no_nine {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (hm : 0 < m)
    (hf : IsLip f) (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f (L + 1) (L + 8))
    (hnot8 : ¬ Leg4Land f (L + 9) (L + 8) (L + 1) (L + 5)) (hnine : ∀ j, f j ≤ L + 8) :
    Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4) := by
  rcases leg4Land_tri hm hf h0 hL hH hlow with h8 | h3 | hb
  · exact absurd h8 hnot8
  · exact leg4Land_wb_of_w3_of_no_nine h3 hnine
  · exact hb

/-- **At a crossing, a partner that stops below `L + 9` is a `wb` arm.** This is the hypothesis the
batch-64 two-walk assembly carries, proved where the partner does not reach the top of the band —
which over the corpus is every crossing, the `w8` side being the only arm of a crossing that
reaches `L + 9`. -/
theorem cross_partner_wb_of_no_nine_armT (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hnine : ∀ j, armT ρ i j ≤ L + 8) :
    Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) := by
  have hi := i.isLt
  have hm : 0 < i.val + 1 := by omega
  have h0T : armT ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  exact leg4Land_wb_of_not_w8_of_no_nine hm (armT_isLip hlip i) h0T (fun j => hLb _)
    (fun j => hHb _) hTlow (fun hT8 => hcross.1 ⟨h8, hT8⟩) hnine

/-- **The mirror.** -/
theorem cross_partner_wb_of_no_nine_armG (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hnine : ∀ j, armG ρ i j ≤ L + 8) :
    Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) := by
  have hi := i.isLt
  have hm : 0 < n - i.val := by omega
  have h0G : armG ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  exact leg4Land_wb_of_not_w8_of_no_nine hm (armG_isLip hlip i) h0G (fun j => hLb _)
    (fun j => hHb _) hGlow (fun hG8 => hcross.1 ⟨hG8, h8⟩) hnine

/-! ## The high run, assembled on `w72` -/

/-- **The high-run crossing, closed on `w72`.** At a crossing whose `w8` side is the forward arm and
whose partner stops below `L + 9`, the partner is a `wb` arm (`cross_partner_wb_of_no_nine_armT`)
and `crossMid2` gives both arms `Mid2Floor`, so the partner satisfies `w72` as soon as it has the
deep-floor clause, and the `w8` side satisfies `w72` as soon as it has the deep-floor clause and
`w72`'s ceiling clause. Both deep-floor clauses are vacuous in a band that misses the floor. This
is what remains of the branch where the `w8` side runs high to `L + 9`: `w71`'s ceiling clause is
then false on it (`w71_armG_iff_deepFirst2`), and `Ceil72` is the clause that replaces it. -/
theorem s3_span_nine_mid5_of_cross_highRun_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hnineT : ∀ j, armT ρ i j ≤ L + 8)
    (hdeepG : Deep72 (armG ρ i) L) (hdeepT : Deep72 (armT ρ i) L)
    (hceil : Ceil72 (armG ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  obtain ⟨hmidT, hmidG⟩ := crossMid2 hcr hlip i L hp hLb hHb hGlow hTlow hcross
  have hwb := cross_partner_wb_of_no_nine_armT hlip i L hp hLb hHb hTlow hcross h8 hnineT
  have hT72 := leg4Land_w72_of_wb_of_mid2_of_deep hwb hmidT hdeepT
  have hG72 := leg4Land_w72_of_tri_of_mid2_of_ceil hmG (armG_isLip hlip i) h0G (fun j => hLb _)
    (fun j => hHb _) hGlow hmidG hdeepG hceil
  exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip hLb hHb hp
    (leg4Window_w72 L) (by omega) (by omega) hG72 hT72

/-- **The mirror**, with the `w8` side the backward arm. -/
theorem s3_span_nine_mid5_of_cross_highRun_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (h8 : Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hnineG : ∀ j, armG ρ i j ≤ L + 8)
    (hdeepG : Deep72 (armG ρ i) L) (hdeepT : Deep72 (armT ρ i) L)
    (hceil : Ceil72 (armT ρ i) L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hi := i.isLt
  have hmT : 0 < i.val + 1 := by omega
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  obtain ⟨hmidT, hmidG⟩ := crossMid2 hcr hlip i L hp hLb hHb hGlow hTlow hcross
  have hwb := cross_partner_wb_of_no_nine_armG hlip i L hp hLb hHb hGlow hcross h8 hnineG
  have hG72 := leg4Land_w72_of_wb_of_mid2_of_deep hwb hmidG hdeepG
  have hT72 := leg4Land_w72_of_tri_of_mid2_of_ceil hmT (armT_isLip hlip i) h0T (fun j => hLb _)
    (fun j => hHb _) hTlow hmidT hdeepT hceil
  exact s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip hLb hHb hp
    (leg4Window_w72 L) (by omega) (by omega) hG72 hT72

/-- **Where the band misses the floor the two deep-floor clauses are vacuous.** -/
theorem deep72_of_off_floor {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : ∀ j, L + 1 ≤ f j) :
    Deep72 f L := by
  intro d hd
  exact absurd (h d) (by omega)

end Pair

end HPC.Fold
