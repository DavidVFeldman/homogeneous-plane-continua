import HPC.Fold.Deep70

/-!
# Which readings of the pairing are available, and what bound each gives

Batch 70 §2.2 asks whether the `67` of `NearLowT` / `NearLowG` is the pairing's bound or the bound
of the reading chosen. It is the bound of the **reading**, and the reading is fixed by how low the
low time is.

The clause `Ceil72` needs its peak at arm index three or more. The pairing read between a time `a`
of the pair and a link carrying `L + 9` puts that peak `z k − 1` steps after `a`, where `k` is the
number of levels between `ρ a` and the peak's own level `L + 8`, and `z` is the timing law of
Theorem 7 (`z 6 = 71`, `z 7 = 170`, `z 8 = 409`). So the bound on the distance from `a` to the
basepoint is `z k − 1 − 3`:

| the low time is at | the peak is at least | the bound on `i − a` |
| --- | --- | --- |
| `L + 2` or below | `a + 70` | **67** |
| `L + 1` or below | `a + 169` | **166** |
| `L` (the floor) | `a + 408` | **405** |

All three readings return a valley at `ρ a + 1` or below, which is at `L + 3` or below in every
case, and all three place it far enough before the ascent (the clause asks for six steps, the
readings give seventy, one hundred and sixty-nine, and four hundred and eight). So a low time at
`L + 1` within 166 steps of the basepoint, or one at the floor within 405 steps, gives the ceiling
clause just as a low time at `L + 2` within 67 does. This file proves all three, packaged as
`NearLowBandT` / `NearLowBandG`.

**What the corpus says.** The widened census (`census-batch70.log`) measures all three distances at
the 229 high-run crossings: the nearest time at `L + 2` or below is 56 to 65 steps away — inside 67
at every one of them — while the nearest at `L + 1` or below is 295 to 642 steps away and the
nearest at the floor is 872 to 2035. So the two further readings, though they have far more room,
are **not available** on this corpus: the level `L + 2` reading is the only one that fires, and its
two steps of slack are real. That is the answer to the question.
-/

namespace HPC.Fold

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## The pairing read from a time at the floor -/

/-- **The pairing against a link carrying `L + 9`, read from a time at the floor.** The same
reading as `crooked_peak_valley_high9_mid` two levels lower: the peak still carries `L + 8` and the
valley is at `ρ a + 1 ≤ L + 1`, and the timing law now spaces the three `408`, `169`, `408` (eight
levels, seven and eight) instead of `70`, `29`, `70`. -/
theorem crooked_peak_valley_high9_low (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha : ρ a ≤ L)
    (hb1 : ρ b ≤ L + 9) (hb2 : L + 9 ≤ σ b) :
    ∃ r r' : Fin n, a.val + 408 ≤ r.val ∧ r.val + 169 ≤ r'.val ∧ r'.val + 408 ≤ b.val ∧
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
  have hz7 : z 7 = 170 := by decide
  have hz8 : z 8 = 409 := by decide
  have h1 : a.val + 408 ≤ r.val := by
    rcases ivSep hcr a r (by omega) 8 (ρ a) (L + 9 - 1) (by push_cast; omega)
      le_rfl (hcr.le a) hr1 hr2 with h | h
    · omega
    · omega
  have h2 : r.val + 169 ≤ r'.val := by
    rcases ivSep hcr r' r (by omega) 7 (ρ a + 1) (L + 9 - 1) (by push_cast; omega)
      hr'1 hr'2 hr1 hr2 with h | h
    · omega
    · omega
  have h3 : r'.val + 408 ≤ b.val := by
    rcases ivSep hcr r' b (by omega) 8 (ρ a + 1) (L + 9) (by push_cast; omega)
      hr'1 hr'2 hb1 hb2 with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, h3, by omega, by omega, hr'1, hr'2⟩

/-- **The same pair read from the high link.** -/
theorem crooked_valley_peak_high9_low (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha1 : ρ a ≤ L + 9) (ha2 : L + 9 ≤ σ a)
    (hb : ρ b ≤ L) :
    ∃ r r' : Fin n, a.val + 408 ≤ r.val ∧ r.val + 169 ≤ r'.val ∧ r'.val + 408 ≤ b.val ∧
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
  have hz7 : z 7 = 170 := by decide
  have hz8 : z 8 = 409 := by decide
  have h1 : a.val + 408 ≤ r.val := by
    rcases ivSep hcr r a (by omega) 8 (ρ b + 1) (L + 9) (by push_cast; omega)
      hr1 hr2 ha1 ha2 with h | h
    · omega
    · omega
  have h2 : r.val + 169 ≤ r'.val := by
    rcases ivSep hcr r r' (by omega) 7 (ρ b + 1) (L + 9 - 1) (by push_cast; omega)
      hr1 hr2 hr'1 hr'2 with h | h
    · omega
    · omega
  have h3 : r'.val + 408 ≤ b.val := by
    rcases ivSep hcr b r' (by omega) 8 (ρ b) (L + 9 - 1) (by push_cast; omega)
      le_rfl (hcr.le b) hr'1 hr'2 with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, h3, hr1, hr2, by omega, by omega⟩

/-! ## The landmarks, transferred to the arm -/

/-- **Two times of the chain past the basepoint are the two landmarks `Ceil72` asks for**, as soon
as the first is three steps past the basepoint, the second five steps past the first and six steps
before the ascent, and the levels are right. -/
theorem ceil72_at_of_landmarks_armG {i : Fin n} {L : ℤ} (hHb : ∀ t, ρ t ≤ L + 9)
    {d : Fin (n - i.val)} (r r' : Fin n) (hr : i.val + 3 ≤ r.val) (hrr' : r.val + 5 ≤ r'.val)
    (hr'd : r'.val + 6 ≤ i.val + d.val) (hrlev : L + 6 ≤ ρ r) (hr'lev : ρ r' ≤ L + 3) :
    ∃ j k : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armG ρ i d - (L + 3)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 3 := by
  have hi := i.isLt
  have hdn := d.isLt
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
  have hub : armG ρ i d ≤ L + 9 := hHb _
  refine ⟨⟨r.val - i.val, hjlt⟩, ⟨r'.val - i.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-- **The mirror, on the backward arm.** -/
theorem ceil72_at_of_landmarks_armT {i : Fin n} {L : ℤ} (hHb : ∀ t, ρ t ≤ L + 9)
    {d : Fin (i.val + 1)} (r r' : Fin n) (hr : r'.val + 3 ≤ i.val) (hrr' : r.val + 5 ≤ r'.val)
    (hr'd : i.val ≤ r.val + d.val - 6) (hrlev : L + 6 ≤ ρ r')
    (hr'lev : ρ r ≤ L + 3) :
    ∃ j k : Fin (i.val + 1), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armT ρ i d - (L + 3)) ≤ (d.val : ℤ) ∧
      L + 6 ≤ armT ρ i j ∧ armT ρ i k ≤ L + 3 := by
  have hi := i.isLt
  have hdn := d.isLt
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
  have hub : armT ρ i d ≤ L + 9 := hHb _
  refine ⟨⟨i.val - r'.val, hjlt⟩, ⟨i.val - r.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-! ## The three readings, packaged -/

/-- **A low time near the basepoint on the backward side, at any of the three levels the pairing
can be read from**, each with the bound that reading gives. -/
def NearLowBandT {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ a : Fin n, a.val < i.val ∧
    ((ρ a ≤ L + 2 ∧ i.val ≤ a.val + 67) ∨ (ρ a ≤ L + 1 ∧ i.val ≤ a.val + 166) ∨
      (ρ a ≤ L ∧ i.val ≤ a.val + 405))

/-- **The mirror, on the forward side.** -/
def NearLowBandG {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ a : Fin n, i.val < a.val ∧
    ((ρ a ≤ L + 2 ∧ a.val ≤ i.val + 67) ∨ (ρ a ≤ L + 1 ∧ a.val ≤ i.val + 166) ∨
      (ρ a ≤ L ∧ a.val ≤ i.val + 405))

theorem nearLowBandT_of_nearLowT {i : Fin n} {L : ℤ} (h : NearLowT ρ i L) : NearLowBandT ρ i L := by
  obtain ⟨a, h1, h2, h3⟩ := h
  exact ⟨a, h1, Or.inl ⟨h3, h2⟩⟩

theorem nearLowBandG_of_nearLowG {i : Fin n} {L : ℤ} (h : NearLowG ρ i L) : NearLowBandG ρ i L := by
  obtain ⟨a, h1, h2, h3⟩ := h
  exact ⟨a, h1, Or.inl ⟨h3, h2⟩⟩

/-- **Any of the three readings gives the forward arm its ceiling clause.** -/
theorem ceil72_of_nearLowBandT_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (h : NearLowBandT ρ i L) : Ceil72 (armG ρ i) L := by
  obtain ⟨a, hai, hcase⟩ := h
  rcases hcase with ⟨hlev, hnear⟩ | ⟨hlev, hnear⟩ | ⟨hlev, hnear⟩
  · exact ceil72_of_nearLowT_armG hcr i L hHb ⟨a, hai, hnear, hlev⟩
  · intro d hd
    have hi := i.isLt
    have hdn := d.isLt
    have hBlt : i.val + d.val < n := by omega
    set B : Fin n := ⟨i.val + d.val, hBlt⟩ with hBdef
    have hBv : ρ B = armG ρ i d := rfl
    have hab : a.val < B.val := by simp only [hBdef]; omega
    obtain ⟨r, r', h1, h2, h3, hr7, -, hr'1, -⟩ :=
      crooked_peak_valley_high9 hcr a B hab L hlev (by rw [hBv]; exact hHb _)
        (by have := hcr.le B; rw [hBv] at this; omega)
    have hBval : B.val = i.val + d.val := rfl
    exact ceil72_at_of_landmarks_armG hHb r r' (by omega) (by omega) (by omega) (by omega)
      (by omega)
  · intro d hd
    have hi := i.isLt
    have hdn := d.isLt
    have hBlt : i.val + d.val < n := by omega
    set B : Fin n := ⟨i.val + d.val, hBlt⟩ with hBdef
    have hBv : ρ B = armG ρ i d := rfl
    have hab : a.val < B.val := by simp only [hBdef]; omega
    obtain ⟨r, r', h1, h2, h3, hr7, -, hr'1, -⟩ :=
      crooked_peak_valley_high9_low hcr a B hab L hlev (by rw [hBv]; exact hHb _)
        (by have := hcr.le B; rw [hBv] at this; omega)
    have hBval : B.val = i.val + d.val := rfl
    exact ceil72_at_of_landmarks_armG hHb r r' (by omega) (by omega) (by omega) (by omega)
      (by omega)

/-- **The mirror.** -/
theorem ceil72_of_nearLowBandG_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (h : NearLowBandG ρ i L) : Ceil72 (armT ρ i) L := by
  obtain ⟨a, hai, hcase⟩ := h
  rcases hcase with ⟨hlev, hnear⟩ | ⟨hlev, hnear⟩ | ⟨hlev, hnear⟩
  · exact ceil72_of_nearLowG_armT hcr i L hHb ⟨a, hai, hnear, hlev⟩
  · intro d hd
    have hi := i.isLt
    have hdn := d.isLt
    have hBlt : i.val - d.val < n := by omega
    set B : Fin n := ⟨i.val - d.val, hBlt⟩ with hBdef
    have hBv : ρ B = armT ρ i d := rfl
    have hab : B.val < a.val := by simp only [hBdef]; omega
    obtain ⟨r, r', h1, h2, h3, hr1, -, hr'7, -⟩ :=
      crooked_valley_peak_high9 hcr B a hab L (by rw [hBv]; exact hHb _)
        (by have := hcr.le B; rw [hBv] at this; omega) hlev
    have hBval : B.val = i.val - d.val := rfl
    exact ceil72_at_of_landmarks_armT hHb r r' (by omega) (by omega) (by omega) (by omega)
      (by omega)
  · intro d hd
    have hi := i.isLt
    have hdn := d.isLt
    have hBlt : i.val - d.val < n := by omega
    set B : Fin n := ⟨i.val - d.val, hBlt⟩ with hBdef
    have hBv : ρ B = armT ρ i d := rfl
    have hab : B.val < a.val := by simp only [hBdef]; omega
    obtain ⟨r, r', h1, h2, h3, hr1, -, hr'7, -⟩ :=
      crooked_valley_peak_high9_low hcr B a hab L (by rw [hBv]; exact hHb _)
        (by have := hcr.le B; rw [hBv] at this; omega) hlev
    have hBval : B.val = i.val - d.val := rfl
    exact ceil72_at_of_landmarks_armT hHb r r' (by omega) (by omega) (by omega) (by omega)
      (by omega)

/-! ## The branch, on the widest form of the distance hypothesis -/

/-- **The high-run crossing on the widest reading.** `s3_span_nine_mid5_of_cross_highRun_nearLowT_armG`
with the distance hypothesis replaced by the disjunction of the three readings. -/
theorem s3_span_nine_mid5_of_cross_highRun_band_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) (hnl : NearLowBandT ρ i L)
    (hT : (∀ j, armT ρ i j ≤ L + 8) ∨ DeepFirst2 (armT ρ i) L ∨ NearLowBandG ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hceilT : Ceil72 (armT ρ i) L := by
    rcases hT with h | h | h
    · exact ceil72_of_no_nine h
    · exact ceil72_of_deepFirst2_armT hcr i L hHb h
    · exact ceil72_of_nearLowBandG_armT hcr i L hHb h
  exact s3_span_nine_mid5_of_cross_highRun_ceil_armG hcr hlip i L hp hLb hHb hGlow hTlow hcross
    hrun (ceil72_of_nearLowBandT_armG hcr i L hHb hnl) hceilT

/-- **The mirror.** -/
theorem s3_span_nine_mid5_of_cross_highRun_band_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunT ρ i L) (hnl : NearLowBandG ρ i L)
    (hG : (∀ j, armG ρ i j ≤ L + 8) ∨ DeepFirst2 (armG ρ i) L ∨ NearLowBandT ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  have hceilG : Ceil72 (armG ρ i) L := by
    rcases hG with h | h | h
    · exact ceil72_of_no_nine h
    · exact ceil72_of_deepFirst2_armG hcr i L hHb h
    · exact ceil72_of_nearLowBandT_armG hcr i L hHb h
  exact s3_span_nine_mid5_of_cross_highRun_ceil_armT hcr hlip i L hp hLb hHb hGlow hTlow hcross
    hrun hceilG (ceil72_of_nearLowBandG_armT hcr i L hHb hnl)

end Pair

end HPC.Fold
