import HPC.Fold.Mid2Mixed67

/-!
# The mirror: the forward arm as the failing arm, and the residue closed

`Mid2Mixed67` proves that one of the two reflected walks serves both arms of a basepoint of the
branch, given only the two landmark lemmas in their `σ`-form (`w3_or_wb_of_land`). This file
supplies those two for the case where the arm that fails the relaxed clause is the **forward** one,
and draws the conclusion for both arms at once.

* `land_ascent_armG_sig_of_mid2fail2G`, `land_ascent_armT_sig_of_mid2fail2G` — the `σ`-forms of the
  two landmark lemmas of `Mid2FoldG66`, and `mid2fail2_high_late_G_sig` the `σ`-form of the fact
  they rest on;
* `w3_or_wb_of_mid2failG`, `s3_span_nine_mid5_of_mid2failG`, `not_triCross_of_mid2failG`,
  `crossMid2_relaxed_armG` — the mirror of the four conclusions of `Mid2Mixed67`;
* `crossMid2_relaxed` — **the residue `CrossMid2L5'` for the relaxed clause, in full**: at a
  crossing of the trichotomy in the branch at `L + 5`, *both* arms satisfy `Mid2Floor2`, with no
  condition on how the branch hypothesis is met and no condition on which arm rises first. Batch 66
  proved this at the basepoints whose two arms are both high first and at those whose two arms are
  both deep first; the mixed basepoint, the residue batch 66 left, is what `Mid2Mixed67` adds.
-/

namespace HPC.Fold

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## The landmark lemmas of the mirror, read on the interval -/

/-- **The `σ`-form of `mid2fail2_high_late_G`.** Every link of the failing forward arm whose
interval reaches `L + 8` lies past the failing descent. -/
theorem mid2fail2_high_late_G_sig (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (dG : Fin (n - i.val)) (hdG : armG ρ i dG = L + 2)
    (hwin : ∀ j : Fin (n - i.val), 2 ≤ j.val → j.val + 4 ≤ dG.val → armG ρ i j ≤ L + 5)
    (q : Fin (n - i.val)) (b : Fin n) (hbe : b.val = i.val + q.val) (hq : L + 8 ≤ σ b) :
    dG.val < q.val := by
  have hi := i.isLt
  have hqn := q.isLt
  have hdGn := dG.isLt
  have hm : 0 < n - i.val := by omega
  have hbv : ρ b = armG ρ i q := by
    show ρ b = ρ ⟨i.val + q.val, by omega⟩
    congr 1
    exact Fin.ext (by omega)
  have hw := hcr.width b
  have hq7 : L + 7 ≤ armG ρ i q := by rw [← hbv]; omega
  have h0 : armG ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have hq2 : 2 ≤ q.val := by
    have := isLip_index_gap (armG_isLip hlip i) (j := ⟨0, hm⟩) (k := q) (Nat.zero_le _)
      (armG ρ i q - armG ρ i ⟨0, hm⟩) (by omega)
    simp only [Nat.cast_zero, zero_add] at this
    omega
  rcases Nat.lt_or_ge dG.val q.val with hlt | hge
  · exact hlt
  exfalso
  rcases Nat.lt_or_ge (q.val + 4) (dG.val + 1) with hfar | hnear
  · have := hwin q hq2 (by omega)
    omega
  · have hqne : q.val ≠ dG.val := by
      intro hc
      have : q = dG := Fin.ext hc
      rw [this, hdG] at hq7
      omega
    have hne : (⟨i.val + dG.val, by omega⟩ : Fin n).val ≠ b.val := by
      simp only []
      omega
    have hdv : armG ρ i dG = ρ ⟨i.val + dG.val, by omega⟩ := rfl
    have hz : z 6 = 71 := by decide
    set w : ℤ := max (ρ b) (L + 8) with hwdef
    have hbw : ρ b ≤ w := le_max_left _ _
    have hwb : w ≤ σ b := by
      rcases le_or_gt (ρ b) (L + 8) with h | h
      · simp only [hwdef, max_eq_right h]; exact hq
      · simp only [hwdef, max_eq_left (by omega : L + 8 ≤ ρ b)]; exact hcr.le b
    have hw8 : L + 8 ≤ w := le_max_right _ _
    rcases ivSep hcr ⟨i.val + dG.val, by omega⟩ b hne 6
      (armG ρ i dG) w (by push_cast; omega) (le_of_eq hdv)
      (by rw [hdv]; exact hcr.le _) hbw hwb with hc | hc
    · simp only [] at hc; omega
    · simp only [] at hc; omega

/-- **The `σ`-form of `land_ascent_armG_of_mid2fail2G`.** The failing forward arm has a low
landmark before every link of its own whose interval reaches `L + 8`. -/
theorem land_ascent_armG_sig_of_mid2fail2G (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (q : Fin (n - i.val)) (b : Fin n) (hbe : b.val = i.val + q.val) (hq : L + 8 ≤ σ b) :
    ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hqn := q.isLt
  obtain ⟨dG, hdG, hwin⟩ := mid2Fail2_witness hmid
  have hdGn := dG.isLt
  have hlate := mid2fail2_high_late_G_sig hcr hlip i L hp dG hdG hwin q b hbe hq
  set a : Fin n := ⟨i.val + dG.val, by omega⟩ with hadef
  have hav : ρ a = armG ρ i dG := rfl
  have hab : a.val < b.val := by simp only [hadef]; omega
  obtain ⟨r, r', h1, h2, h3, -, -, hr'1, hr'2⟩ :=
    crooked_peak_valley_high8 hcr a b hab L (by omega) hq
  have havl : a.val = i.val + dG.val := rfl
  have hr'n := r'.isLt
  set R : ℕ := r'.val - i.val with hRdef
  have hRge : dG.val + 41 ≤ R := by omega
  have hRv : armG ρ i ⟨R, by omega⟩ = ρ r' := by
    show ρ ⟨i.val + R, _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + R = r'.val; omega)
  have hgap : R + 29 ≤ q.val := by
    have hne : r'.val ≠ b.val := by omega
    have hz : z 5 = 30 := by decide
    set w : ℤ := max (ρ b) (L + 8) with hwdef
    have hbw : ρ b ≤ w := le_max_left _ _
    have hwb : w ≤ σ b := by
      rcases le_or_gt (ρ b) (L + 8) with hc | hc
      · simp only [hwdef, max_eq_right hc]; exact hq
      · simp only [hwdef, max_eq_left (by omega : L + 8 ≤ ρ b)]; exact hcr.le b
    have hw8 : L + 8 ≤ w := le_max_right _ _
    rcases ivSep hcr r' b hne 5 (ρ a + 1) w (by push_cast; omega)
      hr'1 hr'2 hbw hwb with hc | hc
    · omega
    · omega
  refine ⟨⟨R, by omega⟩, ?_, ?_, ?_⟩
  · show 3 ≤ R
    omega
  · show R + 12 ≤ q.val
    omega
  · rw [hRv]; omega

/-- **The `σ`-form of `land_ascent_armT_of_mid2fail2G`.** When the forward arm fails, the backward
arm has a low landmark before every link of its own whose interval reaches `L + 8`. -/
theorem land_ascent_armT_sig_of_mid2fail2G (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (q : Fin (i.val + 1)) (a : Fin n) (hae : a.val = i.val - q.val) (hq : L + 8 ≤ σ a) :
    ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hqn := q.isLt
  obtain ⟨dG, hdG, hwin⟩ := mid2Fail2_witness hmid
  have hdGn := dG.isLt
  have hdG0 : 0 < dG.val := by
    rcases Nat.eq_zero_or_pos dG.val with h | h
    · exfalso
      have : armG ρ i dG = ρ i := by
        show ρ ⟨i.val + dG.val, _⟩ = ρ i
        congr 1
        exact Fin.ext (by show i.val + dG.val = i.val; omega)
      omega
    · exact h
  set b : Fin n := ⟨i.val + dG.val, by omega⟩ with hbdef
  have hbv : ρ b = armG ρ i dG := rfl
  have hab : a.val < b.val := by simp only [hbdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, hr2, hr'6, hr'7⟩ :=
    crooked_valley_peak_high8 hcr a b hab L hq (by omega)
  have hbvl : b.val = i.val + dG.val := rfl
  have hrn := r.isLt
  have hr'n := r'.isLt
  -- the peak cannot be a time of the failing forward arm
  have hr'i : r'.val < i.val := by
    by_contra hc
    push_neg at hc
    have hne : i.val ≠ r'.val := by
      intro h
      have : i = r' := Fin.ext h
      rw [← this] at hr'6
      omega
    have hsep : i.val + 2 ≤ r'.val ∨ r'.val + 2 ≤ i.val := by
      have hz : z 2 = 3 := by decide
      set v : ℤ := max (ρ r') (L + 7) with hvdef
      have hrv : ρ r' ≤ v := le_max_left _ _
      have hvr : v ≤ σ r' := by
        rcases le_or_gt (ρ r') (L + 7) with h | h
        · simp only [hvdef, max_eq_right h]; exact hr'7
        · simp only [hvdef, max_eq_left (by omega : L + 7 ≤ ρ r')]; exact hcr.le r'
      have hv7 : L + 7 ≤ v := le_max_right _ _
      rcases ivSep hcr i r' hne 2 (L + 5) v (by push_cast; omega)
        (le_of_eq hp) (by have := hcr.le i; omega) hrv hvr with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hfar : r'.val + 29 ≤ b.val := by
      have hne' : r'.val ≠ b.val := by omega
      have hz : z 5 = 30 := by decide
      set v : ℤ := max (ρ r') (L + 7) with hvdef
      have hrv : ρ r' ≤ v := le_max_left _ _
      have hvr : v ≤ σ r' := by
        rcases le_or_gt (ρ r') (L + 7) with h | h
        · simp only [hvdef, max_eq_right h]; exact hr'7
        · simp only [hvdef, max_eq_left (by omega : L + 7 ≤ ρ r')]; exact hcr.le r'
      have hv7 : L + 7 ≤ v := le_max_right _ _
      rcases ivSep hcr b r' (fun hcc => hne' hcc.symm) 5 (ρ b) v (by push_cast; omega)
        le_rfl (hcr.le b) hrv hvr with h | h
      · omega
      · omega
    have hjr : r'.val - i.val < n - i.val := by omega
    have hjv : armG ρ i ⟨r'.val - i.val, hjr⟩ = ρ r' := by
      show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
    have := hwin ⟨r'.val - i.val, hjr⟩ (by simp; omega) (by simp; omega)
    rw [hjv] at this
    omega
  have hri : r.val < i.val := by omega
  set R : ℕ := i.val - r.val with hRdef
  have hRq : R + 29 ≤ q.val := by omega
  have hRv : armT ρ i ⟨R, by omega⟩ = ρ r := by
    show ρ ⟨i.val - R, _⟩ = ρ r
    congr 1
    exact Fin.ext (by show i.val - R = r.val; omega)
  have hlow : ρ r ≤ L + 3 := by omega
  have hR2 : 2 ≤ R := by
    have hne : r.val ≠ i.val := by omega
    have hz : z 2 = 3 := by decide
    rcases ivSep hcr r i hne 2 (ρ b + 1) (L + 5) (by push_cast; omega)
      hr1 hr2 (le_of_eq hp) (by have := hcr.le i; omega) with hc | hc
    · omega
    · omega
  rcases Nat.lt_or_ge R 3 with hR3 | hR3
  · have h3lt : 3 < i.val + 1 := by omega
    refine ⟨⟨3, h3lt⟩, le_rfl, by simp; omega, ?_⟩
    have hstep : |armT ρ i ⟨3, h3lt⟩ - armT ρ i ⟨R, by omega⟩| ≤ 1 :=
      armT_isLip hlip i ⟨R, by omega⟩ ⟨3, h3lt⟩ (by simp; omega)
    rw [hRv] at hstep
    have := abs_le.mp hstep
    omega
  · exact ⟨⟨R, by omega⟩, hR3, by simp; omega, by rw [hRv]; omega⟩

/-! ## The mirror of the four conclusions -/

/-- **One of the two reflected walks serves both arms, when the forward arm fails the relaxed
clause.** -/
theorem w3_or_wb_of_mid2failG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) ∨
      (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)) :=
  w3_or_wb_of_land hcr i L hp hLb hHb
    (fun q b hb hq => land_ascent_armG_sig_of_mid2fail2G hcr hlip i L hp hmid q b hb hq)
    (fun q a ha hq => land_ascent_armT_sig_of_mid2fail2G hcr hlip i L hp hmid q a ha hq)
    hGlow hTlow

/-- **The pair folds.** -/
theorem s3_span_nine_mid5_of_mid2failG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_land hcr hlip i L hp hLb hHb
    (fun q b hb hq => land_ascent_armG_sig_of_mid2fail2G hcr hlip i L hp hmid q b hb hq)
    (fun q a ha hq => land_ascent_armT_sig_of_mid2fail2G hcr hlip i L hp hmid q a ha hq)
    hGlow hTlow

/-- **Such a basepoint is not a crossing of the trichotomy.** -/
theorem not_triCross_of_mid2failG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ¬ TriCrossL5 ρ i L := by
  intro hcross
  rcases w3_or_wb_of_mid2failG hcr hlip i L hp hLb hHb hmid hGlow hTlow with h | h
  · exact hcross.2.1 h
  · exact hcross.2.2 h

/-- **The residue, for the relaxed clause, on the forward arm.** -/
theorem crossMid2_relaxed_armG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) :
    Mid2Floor2 (armG ρ i) L := by
  classical
  by_contra hmid
  exact not_triCross_of_mid2failG hcr hlip i L hp hLb hHb hmid hGlow hTlow hcross

/-! ## The residue, for the relaxed clause, in full -/

/-- **`CrossMid2L5'` for the relaxed clause.** At a crossing of the trichotomy in the branch at
`L + 5` — a basepoint of a 1-Lipschitz crooked chain inside the band `[L, L + 9]`, with the branch
hypothesis on both arms, served by none of the three walk pairs of the trichotomy — **both** arms
satisfy `Mid2Floor2`: at every descent of the arm to exactly `L + 2` there is an earlier time at
`L + 6` or above, at arm index two or more and four steps earlier.

Batch 66 proved this where both arms have a time at `L + 8` before every descent to `L + 1`
(`crossMid2_relaxed_of_highFirst`) and where both arms descend to `L + 1` before they rise to
`L + 9` (`crossMid2_relaxed_of_deepFirst`). What is added here is the mixed basepoint, where one
arm is of each kind, and `highFirst_or_deepFirst` says there is no third kind. The one index of
slack between `Mid2Floor2` and `Mid2Floor` remains. -/
theorem crossMid2_relaxed (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) :
    Mid2Floor2 (armT ρ i) L ∧ Mid2Floor2 (armG ρ i) L :=
  ⟨crossMid2_relaxed_armT hcr hlip i L hp hLb hHb hGlow hTlow hcross,
    crossMid2_relaxed_armG hcr hlip i L hp hLb hHb hGlow hTlow hcross⟩

end Pair

end HPC.Fold
