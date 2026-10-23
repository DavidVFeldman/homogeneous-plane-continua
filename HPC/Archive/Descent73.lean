import HPC.Fold.Valley72

/-!
# The `w8`-failing descent places the valley

Batch 72 left the branch at `L + 5` owing exactly one statement: `Ceil72` on the **running** arm of
a high-run crossing (`s3_span_nine_mid5_of_cross_highRun_ceilRun_armG` and its mirror discharge
everything else). Batch 71 read the required pairing from the *nearest* low time across the
basepoint, and that reading is false: the nearest low time may have a time of the partner at
`L + 7` or above before it, and then the pairing's peak is a partner time and the clause gets
nothing (`not_nearLowBandCrossL5`, `HPC/Fold/Audit71.lean`).

This file reads the pairing from a different low time — the one the **failure of `w8`** on the
partner returns. At a high-run crossing the running arm is a `w8` arm (`leg4Land_w8_of_run`), so
the first clause of `TriCrossL5` takes `w8` off the partner, and `w8_floor_fail_of_not_w8` returns
a partner descent `d₀` at `L + 2` or below **together with the sentence that no partner time at
`L + 7` or above sits between arm index four and `d₀`**. That extra sentence is exactly what places
the peak:

* the pairing `crooked_peak_valley_high9_mid` is applied between the chain index `a` of `d₀` and
  the running arm's ascent `b`, and returns a peak `r` (with `L + 7 ≤ ρ r` and `L + 8 ≤ σ r`) and a
  valley `r'` (with `ρ r' ≤ ρ a + 1 ≤ L + 3`), spaced `70`, `29`, `70`;
* `r` cannot lie strictly before the basepoint: there it would be a partner time at arm index five
  or more (`armT_index_of_sig8`, from `L + 8 ≤ σ r`) and at least `70 ≥ L + 7 - ρ a` steps past
  `d₀`'s own index, so the `w8`-failure sentence would force `ρ r < L + 7`;
* `r` is not the basepoint either, which carries `L + 5`;
* so `r` and `r'` are both times of the **running** arm, at arm indices `5 ≤ j` and `k ≥ j + 29`,
  with `k + 70 ≤ d` where `Ceil72` asks for `k + (armG d - (L + 3)) ≤ d` and the band bounds that
  gap by six.

Hence `ceil72_run_of_cross_highRunG` and its mirror, with **no distance hypothesis**, and with them
the high-run crossings fold. The two remaining classes at a crossing are the crossings whose two
arms are both deep first at `L + 2` (`s3_span_nine_mid5_of_cross_deepFirst2`), and
`highRunG_of_not_deepFirst2` makes the split exhaustive, so the residue `Leg4TriCrossL5` of
`HPC/Fold/LandTri.lean` is a theorem (`leg4TriCrossL5_holds`) and the branch at `L + 5` closes
(`s3_span_nine_mid5_holds`, `HPC/Fold/Target73.lean`).
-/

namespace HPC.Fold

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## The running arm's ceiling clause, from the `w8`-failing descent -/

/-- **`Ceil72` on the running arm of a high-run crossing, forward orientation.** No distance
hypothesis: the descent whose failure of `w8` the crossing produces on the partner carries with it
the sentence that no partner time at `L + 7` or above precedes it by four indices or more, and that
sentence forces the pairing's peak past the basepoint. -/
theorem ceil72_run_of_cross_highRunG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) :
    Ceil72 (armG ρ i) L := by
  have hi := i.isLt
  -- the running arm is a `w8` arm, so the crossing takes `w8` off the partner
  have hw8G := leg4Land_w8_armG_of_highRun hcr i L hp hLb hHb hrun
  have hnot : ¬ Leg4Land (armT ρ i) (L + 9) (L + 8) (L + 1) (L + 5) :=
    fun h => hcross.1 ⟨hw8G, h⟩
  obtain ⟨d₀, hd0, hfail⟩ :=
    w8_floor_fail_of_not_w8 (f := armT ρ i) (fun j => hLb _) (fun j => hHb _) hnot
  have hd0pos : 0 < d₀.val := by
    rcases Nat.eq_zero_or_pos d₀.val with h0 | hpos
    · exact absurd hd0 (by rw [armT_zero ρ i d₀ h0, hp]; omega)
    · exact hpos
  have hd0lt := d₀.isLt
  have hAlt : i.val - d₀.val < n := by omega
  set A : Fin n := ⟨i.val - d₀.val, hAlt⟩ with hAdef
  have hAv : ρ A = armT ρ i d₀ := rfl
  have hAval : A.val = i.val - d₀.val := rfl
  have hAle : ρ A ≤ L + 2 := by rw [hAv]; exact hd0
  have hAlo : L ≤ ρ A := hLb A
  intro d hd
  have hdn := d.isLt
  have hBlt : i.val + d.val < n := by omega
  set B : Fin n := ⟨i.val + d.val, hBlt⟩ with hBdef
  have hBv : ρ B = armG ρ i d := rfl
  have hBval : B.val = i.val + d.val := rfl
  have hab : A.val < B.val := by rw [hAval, hBval]; omega
  obtain ⟨r, r', h1, h2, h3, hr7, hr8, hr'1, -⟩ :=
    crooked_peak_valley_high9_mid hcr A B hab L hAle
      (by rw [hBv]; exact hHb _) (by have := hcr.le B; rw [hBv] at this; omega)
  -- the peak is past the basepoint: before it, the `w8`-failure sentence forbids `L + 7`
  have hir : i.val < r.val := by
    rcases lt_trichotomy r.val i.val with hlt | heq | hgt
    · exfalso
      have hqlt : i.val - r.val < i.val + 1 := by omega
      have hqv : armT ρ i ⟨i.val - r.val, hqlt⟩ = ρ r := by
        show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
        congr 1
        exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
      have hq5 : 5 ≤ (⟨i.val - r.val, hqlt⟩ : Fin (i.val + 1)).val :=
        armT_index_of_sig8 hcr i L hp ⟨i.val - r.val, hqlt⟩ r (by simp only []; omega) hr8
      simp only [] at hq5
      have hkey := hfail ⟨i.val - r.val, hqlt⟩ (by simp only []; omega)
        (by simp only [← hAv]; omega)
      rw [hqv] at hkey
      omega
    · exact absurd hr7 (by rw [show r = i from Fin.ext heq, hp]; omega)
    · exact hgt
  have hjlt : r.val - i.val < n - i.val := by have := r.isLt; omega
  have hklt : r'.val - i.val < n - i.val := by have := r'.isLt; omega
  have hjv : armG ρ i ⟨r.val - i.val, hjlt⟩ = ρ r := by
    show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
  have hkv : armG ρ i ⟨r'.val - i.val, hklt⟩ = ρ r' := by
    show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
  have hj5 : 5 ≤ (⟨r.val - i.val, hjlt⟩ : Fin (n - i.val)).val :=
    armG_index_of_sig8 hcr i L hp ⟨r.val - i.val, hjlt⟩ r (by simp only []; omega) hr8
  simp only [] at hj5
  refine ⟨⟨r.val - i.val, hjlt⟩, ⟨r'.val - i.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    have hband : armG ρ i d ≤ L + 9 := by rw [← hBv]; exact hHb _
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-- **The mirror, backward orientation.** -/
theorem ceil72_run_of_cross_highRunT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunT ρ i L) :
    Ceil72 (armT ρ i) L := by
  have hi := i.isLt
  have hw8T := leg4Land_w8_armT_of_highRun hcr i L hp hLb hHb hrun
  have hnot : ¬ Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5) :=
    fun h => hcross.1 ⟨h, hw8T⟩
  obtain ⟨d₀, hd0, hfail⟩ :=
    w8_floor_fail_of_not_w8 (f := armG ρ i) (fun j => hLb _) (fun j => hHb _) hnot
  have hd0pos : 0 < d₀.val := by
    rcases Nat.eq_zero_or_pos d₀.val with h0 | hpos
    · exact absurd hd0 (by rw [armG_zero ρ i d₀ h0, hp]; omega)
    · exact hpos
  have hd0lt := d₀.isLt
  have hAlt : i.val + d₀.val < n := by omega
  set A : Fin n := ⟨i.val + d₀.val, hAlt⟩ with hAdef
  have hAv : ρ A = armG ρ i d₀ := rfl
  have hAval : A.val = i.val + d₀.val := rfl
  have hAle : ρ A ≤ L + 2 := by rw [hAv]; exact hd0
  have hAlo : L ≤ ρ A := hLb A
  intro d hd
  have hdn := d.isLt
  have hBlt : i.val - d.val < n := by omega
  set B : Fin n := ⟨i.val - d.val, hBlt⟩ with hBdef
  have hBv : ρ B = armT ρ i d := rfl
  have hBval : B.val = i.val - d.val := rfl
  have hdpos : 0 < d.val := by
    rcases Nat.eq_zero_or_pos d.val with h0 | hpos
    · exact absurd hd (by rw [armT_zero ρ i d h0, hp]; omega)
    · exact hpos
  have hab : B.val < A.val := by rw [hAval, hBval]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, -, hr'7, hr'8⟩ :=
    crooked_valley_peak_high9_mid hcr B A hab L (by rw [hBv]; exact hHb _)
      (by have := hcr.le B; rw [hBv] at this; omega) hAle
  -- the peak is before the basepoint
  have hr'i : r'.val < i.val := by
    rcases lt_trichotomy r'.val i.val with hlt | heq | hgt
    · exact hlt
    · exact absurd hr'7 (by rw [show r' = i from Fin.ext heq, hp]; omega)
    · exfalso
      have hqlt : r'.val - i.val < n - i.val := by have := r'.isLt; omega
      have hqv : armG ρ i ⟨r'.val - i.val, hqlt⟩ = ρ r' := by
        show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
        congr 1
        exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
      have hq5 : 5 ≤ (⟨r'.val - i.val, hqlt⟩ : Fin (n - i.val)).val :=
        armG_index_of_sig8 hcr i L hp ⟨r'.val - i.val, hqlt⟩ r' (by simp only []; omega) hr'8
      simp only [] at hq5
      have hkey := hfail ⟨r'.val - i.val, hqlt⟩ (by simp only []; omega)
        (by simp only [← hAv]; omega)
      rw [hqv] at hkey
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
  have hj5 : 5 ≤ (⟨i.val - r'.val, hjlt⟩ : Fin (i.val + 1)).val :=
    armT_index_of_sig8 hcr i L hp ⟨i.val - r'.val, hjlt⟩ r' (by simp only []; omega) hr'8
  simp only [] at hj5
  refine ⟨⟨i.val - r'.val, hjlt⟩, ⟨i.val - r.val, hklt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    omega
  · simp only []
    omega
  · simp only []
    have hband : armT ρ i d ≤ L + 9 := by rw [← hBv]; exact hHb _
    omega
  · rw [hjv]; omega
  · rw [hkv]; omega

/-! ## The high-run crossings fold -/

/-- **A high-run crossing folds, forward orientation.** -/
theorem s3_span_nine_mid5_of_cross_highRunG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunG ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_highRun_ceilRun_armG hcr hlip i L hp hLb hHb hGlow hTlow hcross hrun
    (ceil72_run_of_cross_highRunG hcr i L hp hLb hHb hcross hrun)

/-- **The mirror.** -/
theorem s3_span_nine_mid5_of_cross_highRunT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) (hrun : HighRunT ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_highRun_ceilRun_armT hcr hlip i L hp hLb hHb hGlow hTlow hcross hrun
    (ceil72_run_of_cross_highRunT hcr i L hp hLb hHb hcross hrun)

/-- **Every crossing of the trichotomy folds.** Either both arms are deep first at `L + 2`, and the
pair folds onto `w71`, or one of them is not — and then that arm runs high, and the two theorems
above apply. -/
theorem s3_span_nine_mid5_of_cross (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  classical
  by_cases hdG : DeepFirst2 (armG ρ i) L
  · by_cases hdT : DeepFirst2 (armT ρ i) L
    · exact s3_span_nine_mid5_of_cross_deepFirst2 hcr hlip i L hp hLb hHb hGlow hTlow hcross
        hdG hdT
    · exact s3_span_nine_mid5_of_cross_highRunT hcr hlip i L hp hLb hHb hGlow hTlow hcross
        (highRunT_of_not_deepFirst2 i L hdT)
  · exact s3_span_nine_mid5_of_cross_highRunG hcr hlip i L hp hLb hHb hGlow hTlow hcross
      (highRunG_of_not_deepFirst2 i L hdG)

end Pair

/-- **The residue of `HPC/Fold/LandTri.lean`, proved.** `Leg4TriCrossL5` is exactly the statement
that every crossing of the trichotomy folds. -/
theorem leg4TriCrossL5_holds : Leg4TriCrossL5 := by
  intro n ρ σ i L hlip hcr hLb hHb hp hG hT h8 h3 hb
  exact s3_span_nine_mid5_of_cross hcr hlip i L hp hLb hHb hG hT ⟨h8, h3, hb⟩

end HPC.Fold
