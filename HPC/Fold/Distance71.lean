import HPC.Fold.Reading70

/-!
# The distance: what the reading needs, and what it can be got from

Batch 70 left the branch `L + 5` owing **one** statement at a high-run crossing: the distance,
`NearLowBandT` / `NearLowBandG` — *a time of the pair at `L + 2` or below within 67 steps before the
basepoint*. Batch 71 asks what produces that time, since nothing proved does.

The census of batch 71 (`census-batch71.c`, log `census-batch71.log`) answers the anatomy question
and hands the proof its shape. At all 229 high-run crossings of the widened corpus the nearest such
time is

* a time of the **partner's** arm, at level exactly `L + 2`, 56 to 65 steps before the basepoint;
* the **valley of one crookedness reading**: the pairing between the nearest time of the pair at
  `L + 1` or below — 295 to 304 steps before the basepoint — and the running arm's link carrying
  `L + 9`.

That reading is a theorem, and this file proves the implication it exhibits. The pairing of
`crooked_peak_valley_high9` between a time `a` at `L + 1` or below and the ascent `b` returns a
valley `r'` at `ρ a + 1 ≤ L + 2` with `a + 239 ≤ r'` and `r' + 169 ≤ b`. The **high run** is what
puts `r'` on the right side of the basepoint: the running arm has nothing at `L + 2` or below
between the basepoint and its ascent, so `r'` — at `L + 2` or below and before the ascent — must lie
before the basepoint. Hence

> `nearLowT_of_nearLow1T_armG`: at a high-run crossing, a time of the pair at `L + 1` or below
> within **306** steps before the basepoint gives one at `L + 2` or below within **67** steps.

The same reading one level lower (`crooked_peak_valley_high9_low`, valley at `ρ a + 1 ≤ L + 1`,
`a + 577 ≤ r'`) gives

> `nearLow1T_of_nearFloorT_armG`: a time at the floor within **883** steps before the basepoint
> gives one at `L + 1` or below within 306,

and the two compose (`nearLowT_of_nearFloorT_armG`). So the distance statement is now a consequence
of the *same* statement two levels lower with a bound thirteen times as large. On the corpus the
`L + 1` hypothesis holds at all 229 crossings (295 to 304, against 306) and the floor hypothesis at
some but not all (872 to 2035, against 883); neither is proved, and the report says so.

The file also fixes what a reading of the ceiling clause has to place (batch 71 §2.3):

* `Valley3BeforeNine` — a peak at `L + 6` or above at arm index three or more and, five steps later,
  a time at `L + 3` or below, six steps before **every** ascent to `L + 9` — is equivalent to
  `Ceil72` on an arm of the band (`ceil72_of_valley3BeforeNine`, `valley3BeforeNine_of_ceil72`), so
  the clause is a statement about the *first* ascent only;
* on a high-running arm that valley is at level **exactly** `L + 3` (`valley_eq_three_of_run`),
  because the run forbids `L + 2` and below before the ascent;
* and `low_nine_sep` records the timing law across the basepoint: a time at `L + 2` or below and a
  link carrying `L + 9` are at least 169 steps apart, so at a high-run crossing the distance to the
  low time and the arm index of the ascent sum to at least 169 (`nearLow_ascent_sep_armG`). The
  census sees that bound attained with **equality** at all 229 crossings, which is why the observed
  distance 56 to 65 is the exact complement of the observed ascent 104 to 113.

Finally, for batch 71 §2.5, `BothHighRunL5` names the configuration where both arms run high, and
`w8_of_cross_of_bothHighRun` shows that at a crossing it cannot happen with both arms failing `w8`:
the two `w3` readings of batch 68 would then serve both arms. The census finds `BothHighRunL5` at
16235 basepoints of the branch but at **none** of the 1351 crossings.
-/

namespace HPC.Fold

section Arm

variable {m : ℕ} {f : Fin m → ℤ} {L : ℤ}

/-! ## What the ceiling clause asks for: one valley before the first ascent -/

/-- **The landmark pair of `Ceil72`, read at the first ascent.** A peak at `L + 6` or above at arm
index three or more, a time at `L + 3` or below five steps later, and every ascent to `L + 9` at
least six steps after that. -/
def Valley3BeforeNine {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∃ j k : Fin m, 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧ L + 6 ≤ f j ∧ f k ≤ L + 3 ∧
    ∀ d : Fin m, L + 9 ≤ f d → (k.val : ℤ) + 6 ≤ (d.val : ℤ)

/-- **The landmark pair gives the clause.** In the band the trigger level `L + 9` is also the arm's
ceiling, so the clause's spacing `k + (f d - (L + 3)) ≤ d` is exactly `k + 6 ≤ d`. -/
theorem ceil72_of_valley3BeforeNine (hHb : ∀ j, f j ≤ L + 9) (h : Valley3BeforeNine f L) :
    Ceil72 f L := by
  obtain ⟨j, k, hj, hjk, hjlev, hklev, hlate⟩ := h
  intro d hd
  have hdle := hHb d
  have := hlate d hd
  exact ⟨j, k, hj, hjk, by omega, hjlev, hklev⟩

/-- **The clause gives the landmark pair**, read at the arm's first ascent: every later ascent is
later still, so the one spacing carries over. -/
theorem valley3BeforeNine_of_ceil72 (hHb : ∀ j, f j ≤ L + 9) (h : Ceil72 f L) (e : Fin m)
    (he : L + 9 ≤ f e) (hfirst : ∀ d : Fin m, L + 9 ≤ f d → e.val ≤ d.val) :
    Valley3BeforeNine f L := by
  obtain ⟨j, k, hj, hjk, hke, hjlev, hklev⟩ := h e he
  have hee : f e = L + 9 := le_antisymm (hHb e) he
  refine ⟨j, k, hj, hjk, hjlev, hklev, fun d hd => ?_⟩
  have hed : (e.val : ℤ) ≤ (d.val : ℤ) := by exact_mod_cast hfirst d hd
  rw [hee] at hke
  omega

/-- **On a running arm the valley is at `L + 3` exactly.** The run forbids `L + 2` and below before
the ascent and the clause asks for `L + 3` or below, so the level is forced: what a reading of the
clause has to place is not a low time but a time at exactly `L + 3`. -/
theorem valley_eq_three_of_run {e k : Fin m}
    (hrun : ∀ d : Fin m, d.val < e.val → L + 3 ≤ f d) (hke : k.val < e.val) (hk : f k ≤ L + 3) :
    f k = L + 3 :=
  le_antisymm hk (hrun k hke)

end Arm

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## The timing law across the basepoint -/

/-- **A time at `L + 2` or below and a link carrying `L + 9` are 169 steps apart**, in either
order: the timing law of Theorem 7 at seven levels (`z 7 = 170`). -/
theorem low_nine_sep (hcr : IsCrookedIvF ρ σ) (a b : Fin n) (L : ℤ) (hne : a.val ≠ b.val)
    (ha : ρ a ≤ L + 2) (hb1 : ρ b ≤ L + 9) (hb2 : L + 9 ≤ σ b) :
    a.val + 169 ≤ b.val ∨ b.val + 169 ≤ a.val := by
  have hz : z 7 = 170 := by decide
  rcases ivSep hcr a b hne 7 (ρ a) (L + 9) (by push_cast; omega) le_rfl (hcr.le a) hb1 hb2 with
    h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- **The distance and the ascent sum to at least 169.** At a high-run crossing the low time `a`
lies before the basepoint and the ascent at arm index `e` after it, so the timing law reads
`(i - a) + e ≥ 169`. The census sees this attained with equality at all 229 high-run crossings:
the distance 56 to 65 is the complement of the ascent 104 to 113. -/
theorem nearLow_ascent_sep_armG (hcr : IsCrookedIvF ρ σ) {i : Fin n} {L : ℤ}
    (hHb : ∀ t, ρ t ≤ L + 9) {a : Fin n} (hai : a.val < i.val) (ha : ρ a ≤ L + 2)
    {e : Fin (n - i.val)} (he : L + 9 ≤ armG ρ i e) :
    169 ≤ (i.val - a.val) + e.val := by
  have hi := i.isLt
  have hel := e.isLt
  have hblt : i.val + e.val < n := by omega
  have hbv : ρ (⟨i.val + e.val, hblt⟩ : Fin n) = armG ρ i e := rfl
  have hb9 : L + 9 ≤ ρ (⟨i.val + e.val, hblt⟩ : Fin n) := by rw [hbv]; exact he
  have hb2 : L + 9 ≤ σ (⟨i.val + e.val, hblt⟩ : Fin n) :=
    le_trans hb9 (hcr.le (⟨i.val + e.val, hblt⟩ : Fin n))
  have hne : a.val ≠ (⟨i.val + e.val, hblt⟩ : Fin n).val := by simp only []; omega
  rcases low_nine_sep hcr a ⟨i.val + e.val, hblt⟩ L hne ha (hHb _) hb2 with h | h
  · simp only [] at h; omega
  · simp only [] at h; omega

/-! ## The two readings that push a low time forward to the basepoint -/

/-- **A time of the pair at `L + 1` or below within 306 steps before the basepoint.** -/
def NearLow1T {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ a : Fin n, a.val < i.val ∧ i.val ≤ a.val + 306 ∧ ρ a ≤ L + 1

/-- **The mirror, on the forward side.** -/
def NearLow1G {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ a : Fin n, i.val < a.val ∧ a.val ≤ i.val + 306 ∧ ρ a ≤ L + 1

/-- **A time of the pair at the floor within 883 steps before the basepoint.** -/
def NearFloorT {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ a : Fin n, a.val < i.val ∧ i.val ≤ a.val + 883 ∧ ρ a ≤ L

/-- **The mirror, on the forward side.** -/
def NearFloorG {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ a : Fin n, i.val < a.val ∧ a.val ≤ i.val + 883 ∧ ρ a ≤ L

/-- **The ascent of a high run of the forward arm, read as a link of the chain**, together with the
run itself: nothing at `L + 2` or below between the basepoint and the ascent. -/
theorem highRunG_link (hcr : IsCrookedIvF ρ σ) {i : Fin n} {L : ℤ} (hp : ρ i = L + 5)
    (h : HighRunG ρ i L) :
    ∃ b : Fin n, i.val < b.val ∧ L + 9 ≤ ρ b ∧ L + 9 ≤ σ b ∧
      ∀ t : Fin n, i.val ≤ t.val → t.val < b.val → L + 3 ≤ ρ t := by
  obtain ⟨e, he, hlow⟩ := h
  have hi := i.isLt
  have hel := e.isLt
  have hblt : i.val + e.val < n := by omega
  have hbv : ρ (⟨i.val + e.val, hblt⟩ : Fin n) = armG ρ i e := rfl
  have hb9 : L + 9 ≤ ρ (⟨i.val + e.val, hblt⟩ : Fin n) := by rw [hbv]; exact he
  have hepos : 0 < e.val := by
    rcases Nat.eq_zero_or_pos e.val with h0 | hpos
    · exfalso
      have : (⟨i.val + e.val, hblt⟩ : Fin n) = i := Fin.ext (by simp only []; omega)
      rw [this, hp] at hb9
      omega
    · exact hpos
  refine ⟨⟨i.val + e.val, hblt⟩, by simp only []; omega, hb9,
    le_trans hb9 (hcr.le _), fun t ht1 ht2 => ?_⟩
  simp only [] at ht2
  have htn := t.isLt
  have hd : t.val - i.val < n - i.val := by omega
  have hval : armG ρ i ⟨t.val - i.val, hd⟩ = ρ t := by
    show ρ ⟨i.val + (t.val - i.val), _⟩ = ρ t
    congr 1
    exact Fin.ext (by show i.val + (t.val - i.val) = t.val; omega)
  have hlt : (⟨t.val - i.val, hd⟩ : Fin (n - i.val)).val < e.val := by simp only []; omega
  have := hlow ⟨t.val - i.val, hd⟩ hlt
  rw [hval] at this
  exact this

/-- **The mirror: the ascent of a high run of the backward arm.** -/
theorem highRunT_link (hcr : IsCrookedIvF ρ σ) {i : Fin n} {L : ℤ} (hp : ρ i = L + 5)
    (h : HighRunT ρ i L) :
    ∃ b : Fin n, b.val < i.val ∧ L + 9 ≤ ρ b ∧ L + 9 ≤ σ b ∧
      ∀ t : Fin n, b.val < t.val → t.val ≤ i.val → L + 3 ≤ ρ t := by
  obtain ⟨e, he, hlow⟩ := h
  have hi := i.isLt
  have hel := e.isLt
  have hblt : i.val - e.val < n := by omega
  have hbv : ρ (⟨i.val - e.val, hblt⟩ : Fin n) = armT ρ i e := rfl
  have hb9 : L + 9 ≤ ρ (⟨i.val - e.val, hblt⟩ : Fin n) := by rw [hbv]; exact he
  have hepos : 0 < e.val := by
    rcases Nat.eq_zero_or_pos e.val with h0 | hpos
    · exfalso
      have : (⟨i.val - e.val, hblt⟩ : Fin n) = i := Fin.ext (by simp only []; omega)
      rw [this, hp] at hb9
      omega
    · exact hpos
  refine ⟨⟨i.val - e.val, hblt⟩, by simp only []; omega, hb9,
    le_trans hb9 (hcr.le _), fun t ht1 ht2 => ?_⟩
  simp only [] at ht1
  have hd : i.val - t.val < i.val + 1 := by omega
  have hval : armT ρ i ⟨i.val - t.val, hd⟩ = ρ t := by
    show ρ ⟨i.val - (i.val - t.val), _⟩ = ρ t
    congr 1
    exact Fin.ext (by show i.val - (i.val - t.val) = t.val; omega)
  have hlt : (⟨i.val - t.val, hd⟩ : Fin (i.val + 1)).val < e.val := by simp only []; omega
  have := hlow ⟨i.val - t.val, hd⟩ hlt
  rw [hval] at this
  exact this

/-- **The distance, from the same statement one level lower.** At a high-run crossing a time of the
pair at `L + 1` or below within 306 steps before the basepoint gives one at `L + 2` or below within
67: the pairing between the two returns a valley at `L + 2` or below, at least 239 steps after the
low time, and the high run forces that valley before the basepoint. -/
theorem nearLowT_of_nearLow1T_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5) (hrun : HighRunG ρ i L) (h : NearLow1T ρ i L) :
    NearLowT ρ i L := by
  obtain ⟨b, hib, hb1, hb2, hnolow⟩ := highRunG_link hcr hp hrun
  obtain ⟨a, hai, hnear, ha⟩ := h
  obtain ⟨r, r', h1, h2, h3, -, -, hr'1, -⟩ :=
    crooked_peak_valley_high9 hcr a b (by omega) L ha (hHb b) hb2
  have hr'lev : ρ r' ≤ L + 2 := by omega
  have hr'i : r'.val < i.val := by
    by_contra hc
    have := hnolow r' (by omega) (by omega)
    omega
  exact ⟨r', hr'i, by omega, hr'lev⟩

/-- **The mirror.** -/
theorem nearLowG_of_nearLow1G_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5) (hrun : HighRunT ρ i L) (h : NearLow1G ρ i L) :
    NearLowG ρ i L := by
  obtain ⟨b, hbi, hb1, hb2, hnolow⟩ := highRunT_link hcr hp hrun
  obtain ⟨a, hia, hnear, ha⟩ := h
  obtain ⟨r, r', h1, h2, h3, hr1, -, -, -⟩ :=
    crooked_valley_peak_high9 hcr b a (by omega) L (hHb b) hb2 ha
  have hrlev : ρ r ≤ L + 2 := by omega
  have hri : i.val < r.val := by
    by_contra hc
    have := hnolow r (by omega) (by omega)
    omega
  exact ⟨r, hri, by omega, hrlev⟩

/-- **One level lower again.** A time of the pair at the floor within 883 steps before the
basepoint gives one at `L + 1` or below within 306: the same reading, with the timing law's
`z 8 = 409` in place of `z 7 = 170`. -/
theorem nearLow1T_of_nearFloorT_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5) (hrun : HighRunG ρ i L) (h : NearFloorT ρ i L) :
    NearLow1T ρ i L := by
  obtain ⟨b, hib, hb1, hb2, hnolow⟩ := highRunG_link hcr hp hrun
  obtain ⟨a, hai, hnear, ha⟩ := h
  obtain ⟨r, r', h1, h2, h3, -, -, hr'1, -⟩ :=
    crooked_peak_valley_high9_low hcr a b (by omega) L ha (hHb b) hb2
  have hr'lev : ρ r' ≤ L + 1 := by omega
  have hr'i : r'.val < i.val := by
    by_contra hc
    have := hnolow r' (by omega) (by omega)
    omega
  exact ⟨r', hr'i, by omega, hr'lev⟩

/-- **The mirror.** -/
theorem nearLow1G_of_nearFloorG_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5) (hrun : HighRunT ρ i L) (h : NearFloorG ρ i L) :
    NearLow1G ρ i L := by
  obtain ⟨b, hbi, hb1, hb2, hnolow⟩ := highRunT_link hcr hp hrun
  obtain ⟨a, hia, hnear, ha⟩ := h
  obtain ⟨r, r', h1, h2, h3, hr1, -, -, -⟩ :=
    crooked_valley_peak_high9_low hcr b a (by omega) L (hHb b) hb2 ha
  have hrlev : ρ r ≤ L + 1 := by omega
  have hri : i.val < r.val := by
    by_contra hc
    have := hnolow r (by omega) (by omega)
    omega
  exact ⟨r, hri, by omega, hrlev⟩

/-- **The two readings composed:** a time at the floor within 883 steps before the basepoint gives
the distance hypothesis outright. -/
theorem nearLowT_of_nearFloorT_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5) (hrun : HighRunG ρ i L) (h : NearFloorT ρ i L) :
    NearLowT ρ i L :=
  nearLowT_of_nearLow1T_armG hcr i L hHb hp hrun
    (nearLow1T_of_nearFloorT_armG hcr i L hHb hp hrun h)

/-- **The mirror.** -/
theorem nearLowG_of_nearFloorG_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 5) (hrun : HighRunT ρ i L) (h : NearFloorG ρ i L) :
    NearLowG ρ i L :=
  nearLowG_of_nearLow1G_armT hcr i L hHb hp hrun
    (nearLow1G_of_nearFloorG_armT hcr i L hHb hp hrun h)

/-! ## The branch, on the `L + 1` reading -/

/-- **The high-run crossing folds on the `L + 1` distance hypothesis.** The assembly of batch 70
with `NearLowBandT` replaced by the weaker hypothesis of `nearLowT_of_nearLow1T_armG`. -/
theorem s3_span_nine_mid5_of_cross_highRun_low1_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) (hnl : NearLow1T ρ i L)
    (hT : (∀ j, armT ρ i j ≤ L + 8) ∨ DeepFirst2 (armT ρ i) L ∨ NearLowBandG ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_highRun_band_armG hcr hlip i L hp hLb hHb hGlow hTlow hcross hrun
    (nearLowBandT_of_nearLowT (nearLowT_of_nearLow1T_armG hcr i L hHb hp hrun hnl)) hT

/-- **The mirror.** -/
theorem s3_span_nine_mid5_of_cross_highRun_low1_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunT ρ i L) (hnl : NearLow1G ρ i L)
    (hG : (∀ j, armG ρ i j ≤ L + 8) ∨ DeepFirst2 (armG ρ i) L ∨ NearLowBandT ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_highRun_band_armT hcr hlip i L hp hLb hHb hGlow hTlow hcross hrun
    (nearLowBandG_of_nearLowG (nearLowG_of_nearLow1G_armT hcr i L hHb hp hrun hnl)) hG

/-! ## Both arms running high -/

/-- **`BothHighRunL5`**: both arms reach `L + 9` with nothing at `L + 2` or below before the
ascent. The census of batch 71 finds this at 16235 basepoints of the branch and at none of the
1351 crossings. -/
def BothHighRunL5 {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  HighRunG ρ i L ∧ HighRunT ρ i L

/-- **At a crossing with both arms running high, one of the arms is a `w8` arm.** If neither were,
the high run of each arm would put the *other* on `w3` (batch 68), and `w3` would serve both arms —
which a crossing forbids. So the configuration `BothHighRunL5` can only occur at a crossing of the
trichotomy in the shape the census measures: with the `w8` side itself running high. -/
theorem w8_of_cross_of_bothHighRun (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) (h : BothHighRunL5 ρ i L) :
    Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) ∨
      Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5) := by
  by_contra hc
  push_neg at hc
  obtain ⟨⟨dG, hdG, hrunG⟩, ⟨dT, hdT, hrunT⟩⟩ := h
  exact hcross.2.1
    ⟨leg4Land_w3_armG_of_highRun_armT hcr hlip i L hp hLb hHb dT hdT hrunT hc.1,
     leg4Land_w3_armT_of_highRun_armG hcr hlip i L hp hLb hHb dG hdG hrunG hc.2⟩

end Pair

end HPC.Fold
