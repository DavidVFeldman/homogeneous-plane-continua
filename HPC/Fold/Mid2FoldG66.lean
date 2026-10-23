import HPC.Fold.Mid2Fold66

/-!
# The mirror: the forward arm as the failing arm

`Mid2Fold66` proves the residue, for the relaxed clause and under the first disjunct of the branch
hypothesis, when the arm that fails is the **backward** one. This file is the same argument with
the two arms exchanged, and the two together give the residue in the symmetric form
`crossMid2_relaxed_of_highFirst`: at a crossing of the trichotomy both of whose arms have a time at
`L + 8` before every descent to `L + 1`, **both** arms satisfy `Mid2Floor2`.

The mirror is not a corollary of the original — the two arms of a basepoint are read in opposite
directions along the chain, and crookedness is read from the earlier link to the later one — so the
pairing lemma used is the other one of the two: where the original reads
`crooked_peak_valley_high8` from the failing descent forwards, the mirror reads
`crooked_valley_peak_high8` from the high link forwards, and vice versa.
-/

namespace HPC.Fold

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## Where a failing forward arm can be high -/

/-- **A failing forward arm is never high before its failing descent.** -/
theorem mid2fail2_high_late_G (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (dG : Fin (n - i.val)) (hdG : armG ρ i dG = L + 2)
    (hwin : ∀ j : Fin (n - i.val), 2 ≤ j.val → j.val + 4 ≤ dG.val → armG ρ i j ≤ L + 5)
    (q : Fin (n - i.val)) (hq : L + 8 ≤ armG ρ i q) :
    dG.val < q.val := by
  have hi := i.isLt
  have hqn := q.isLt
  have hdGn := dG.isLt
  have hm : 0 < n - i.val := by omega
  have h0 : armG ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have hq3 : 3 ≤ q.val := by
    have := isLip_index_gap (armG_isLip hlip i) (j := ⟨0, hm⟩) (k := q) (Nat.zero_le _)
      (armG ρ i q - armG ρ i ⟨0, hm⟩) (by omega)
    simp only [Nat.cast_zero, zero_add] at this
    omega
  rcases Nat.lt_or_ge dG.val q.val with hlt | hge
  · exact hlt
  exfalso
  rcases Nat.lt_or_ge (q.val + 4) (dG.val + 1) with hfar | hnear
  · have := hwin q (by omega) (by omega)
    omega
  · have hqne : q.val ≠ dG.val := by
      intro hc
      have : q = dG := Fin.ext hc
      rw [this, hdG] at hq
      omega
    have hne : (⟨i.val + dG.val, by omega⟩ : Fin n).val ≠ (⟨i.val + q.val, by omega⟩ : Fin n).val := by
      simp only []
      omega
    have hqv : armG ρ i q = ρ ⟨i.val + q.val, by omega⟩ := rfl
    have hdv : armG ρ i dG = ρ ⟨i.val + dG.val, by omega⟩ := rfl
    have hz : z 6 = 71 := by decide
    rcases ivSep hcr ⟨i.val + dG.val, by omega⟩ ⟨i.val + q.val, by omega⟩ hne 6
      (armG ρ i dG) (armG ρ i q) (by push_cast; omega) (le_of_eq hdv)
      (by rw [hdv]; exact hcr.le _) (le_of_eq hqv) (by rw [hqv]; exact hcr.le _) with hc | hc
    · simp only [] at hc; omega
    · simp only [] at hc; omega

/-! ## The landmark on the failing forward arm -/

/-- **The failing forward arm has a low landmark before each of its own high times.** -/
theorem land_ascent_armG_of_mid2fail2G (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (q : Fin (n - i.val)) (hq : L + 8 ≤ armG ρ i q) :
    ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hqn := q.isLt
  obtain ⟨dG, hdG, hwin⟩ := mid2Fail2_witness hmid
  have hdGn := dG.isLt
  have hlate := mid2fail2_high_late_G hcr hlip i L hp dG hdG hwin q hq
  set a : Fin n := ⟨i.val + dG.val, by omega⟩ with hadef
  set b : Fin n := ⟨i.val + q.val, by omega⟩ with hbdef
  have hav : ρ a = armG ρ i dG := rfl
  have hbv : ρ b = armG ρ i q := rfl
  have hab : a.val < b.val := by simp only [hadef, hbdef]; omega
  obtain ⟨r, r', h1, h2, h3, -, -, hr'1, hr'2⟩ :=
    crooked_peak_valley_high8 hcr a b hab L (by omega) (by have := hcr.le b; omega)
  have havl : a.val = i.val + dG.val := rfl
  have hbvl : b.val = i.val + q.val := rfl
  have hr'n := r'.isLt
  set R : ℕ := r'.val - i.val with hRdef
  have hRge : dG.val + 41 ≤ R := by omega
  have hRv : armG ρ i ⟨R, by omega⟩ = ρ r' := by
    show ρ ⟨i.val + R, _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + R = r'.val; omega)
  -- five levels cost twenty-nine steps
  have hgap : R + 29 ≤ q.val := by
    have hne : r'.val ≠ b.val := by omega
    have hz : z 5 = 30 := by decide
    set w : ℤ := max (ρ b) (L + 8) with hwdef
    have hbw : ρ b ≤ w := le_max_left _ _
    have hwb : w ≤ σ b := by
      rcases le_or_gt (ρ b) (L + 8) with hc | hc
      · simp only [hwdef, max_eq_right hc]; exact by have := hcr.le b; omega
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

/-! ## The landmark on the `w8` side, which is now the backward arm -/

/-- **The mirror of `land_ascent_of_mid2fail2`.** If the forward arm fails the relaxed clause, the
backward arm has, before every one of its times at `L + 8` or above, a time at `L + 4` or below at
arm index three or more and twelve steps earlier. -/
theorem land_ascent_armT_of_mid2fail2G (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (q : Fin (i.val + 1)) (hq : L + 8 ≤ armT ρ i q) :
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
  set a : Fin n := ⟨i.val - q.val, by omega⟩ with hadef
  set b : Fin n := ⟨i.val + dG.val, by omega⟩ with hbdef
  have hav : ρ a = armT ρ i q := rfl
  have hbv : ρ b = armG ρ i dG := rfl
  have hab : a.val < b.val := by simp only [hadef, hbdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, hr2, hr'6, hr'7⟩ :=
    crooked_valley_peak_high8 hcr a b hab L (by have := hcr.le a; omega) (by omega)
  have havl : a.val = i.val - q.val := rfl
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
    -- and it is far from the failing descent, by the law at five levels
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

/-! ## `w3` on both arms, and the fold -/

/-- **`w3` on the failing forward arm.** -/
theorem leg4Land_w3_armG_of_mid2fail2G (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (hA : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ p : Fin (n - i.val), p.val < d.val ∧ L + 8 ≤ armG ρ i p) :
    Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hd8 : L + 8 ≤ armG ρ i d := by omega
    have hd9 : armG ρ i d ≤ L + 9 := hHb ⟨i.val + d.val, by have := d.isLt; omega⟩
    obtain ⟨j, h1, h2, h3⟩ := land_ascent_armG_of_mid2fail2G hcr hlip i L hp hmid d hd8
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    simp only [armRefl_apply] at hd
    have := hHb ⟨i.val + d.val, by have := d.isLt; omega⟩
    have he : armG ρ i d = ρ ⟨i.val + d.val, by have := d.isLt; omega⟩ := rfl
    omega
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hdn := d.isLt
    have hdl : armG ρ i d ≤ L + 1 := by omega
    have hdL : L ≤ armG ρ i d := hLb ⟨i.val + d.val, by omega⟩
    obtain ⟨p, hpd, hp8⟩ := hA d hdl
    have hpn := p.isLt
    obtain ⟨j, hj3, hj12, hjlow⟩ := land_ascent_armG_of_mid2fail2G hcr hlip i L hp hmid p hp8
    have hsep : (p.val : ℤ) + 7 ≤ (d.val : ℤ) := by
      have hz : z 7 = 170 := by decide
      have hne : (⟨i.val + d.val, by omega⟩ : Fin n).val ≠ (⟨i.val + p.val, by omega⟩ : Fin n).val := by
        simp only []
        omega
      have hdv : armG ρ i d = ρ ⟨i.val + d.val, by omega⟩ := rfl
      have hpv : armG ρ i p = ρ ⟨i.val + p.val, by omega⟩ := rfl
      rcases ivSep hcr ⟨i.val + d.val, by omega⟩ ⟨i.val + p.val, by omega⟩ hne 7
        (armG ρ i d) (armG ρ i p) (by push_cast; omega) (le_of_eq hdv)
        (by rw [hdv]; exact hcr.le _) (le_of_eq hpv)
        (by rw [hpv]; exact hcr.le _) with hc | hc
      · simp only [] at hc; omega
      · simp only [] at hc; omega
    exact ⟨j, p, by omega, by omega, by omega, by omega, by omega⟩

/-- **`w3` on the backward arm, when the forward arm is the failing one.** -/
theorem leg4Land_w3_armT_of_mid2fail2G (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (hA : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ p : Fin (i.val + 1), p.val < d.val ∧ L + 8 ≤ armT ρ i p) :
    Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hd8 : L + 8 ≤ armT ρ i d := by omega
    have hd9 : armT ρ i d ≤ L + 9 := hHb ⟨i.val - d.val, by have := d.isLt; omega⟩
    obtain ⟨j, h1, h2, h3⟩ := land_ascent_armT_of_mid2fail2G hcr hlip i L hp hmid d hd8
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    simp only [armRefl_apply] at hd
    have := hHb ⟨i.val - d.val, by have := d.isLt; omega⟩
    have he : armT ρ i d = ρ ⟨i.val - d.val, by have := d.isLt; omega⟩ := rfl
    omega
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hdn := d.isLt
    have hdl : armT ρ i d ≤ L + 1 := by omega
    have hdL : L ≤ armT ρ i d := hLb ⟨i.val - d.val, by omega⟩
    obtain ⟨p, hpd, hp8⟩ := hA d hdl
    have hpn := p.isLt
    obtain ⟨j, hj3, hj12, hjlow⟩ := land_ascent_armT_of_mid2fail2G hcr hlip i L hp hmid p hp8
    have hsep : (p.val : ℤ) + 7 ≤ (d.val : ℤ) := by
      have hz : z 7 = 170 := by decide
      have hne : (⟨i.val - d.val, by omega⟩ : Fin n).val ≠ (⟨i.val - p.val, by omega⟩ : Fin n).val := by
        simp only []
        omega
      have hdv : armT ρ i d = ρ ⟨i.val - d.val, by omega⟩ := rfl
      have hpv : armT ρ i p = ρ ⟨i.val - p.val, by omega⟩ := rfl
      rcases ivSep hcr ⟨i.val - d.val, by omega⟩ ⟨i.val - p.val, by omega⟩ hne 7
        (armT ρ i d) (armT ρ i p) (by push_cast; omega) (le_of_eq hdv)
        (by rw [hdv]; exact hcr.le _) (le_of_eq hpv)
        (by rw [hpv]; exact hcr.le _) with hc | hc
      · simp only [] at hc; omega
      · simp only [] at hc; omega
    exact ⟨j, p, by omega, by omega, by omega, by omega, by omega⟩

/-- **The mirror fold.** -/
theorem s3_span_nine_mid5_of_mid2fail2G (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armG ρ i) L)
    (hAT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ p : Fin (i.val + 1), p.val < d.val ∧ L + 8 ≤ armT ρ i p)
    (hAG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ p : Fin (n - i.val), p.val < d.val ∧ L + 8 ≤ armG ρ i p) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 1) (L + 4) hlip hLb hHb hp
    (leg4Window_w3 L) (by omega) (by omega)
    (leg4Land_w3_armG_of_mid2fail2G hcr hlip i L hp hLb hHb hmid hAG)
    (leg4Land_w3_armT_of_mid2fail2G hcr hlip i L hp hLb hHb hmid hAT)

/-- **The residue at a crossing, in the symmetric form.** At a crossing of the trichotomy at the
branch `L + 5` both of whose arms have a time at `L + 8` before every descent to `L + 1`, **both**
arms satisfy the relaxed clause `Mid2Floor2`. This is what `CrossMid2L5'` asks for on those
basepoints, with the index bound of the clause relaxed from three to two. -/
theorem crossMid2_relaxed_of_highFirst (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hAT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ p : Fin (i.val + 1), p.val < d.val ∧ L + 8 ≤ armT ρ i p)
    (hAG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ p : Fin (n - i.val), p.val < d.val ∧ L + 8 ≤ armG ρ i p)
    (hcross : TriCrossL5 ρ i L) :
    Mid2Floor2 (armT ρ i) L ∧ Mid2Floor2 (armG ρ i) L := by
  classical
  refine ⟨mid2Floor2_of_cross_highFirst hcr hlip i L hp hLb hHb hAT hAG hcross, ?_⟩
  by_contra hmid
  exact hcross.2.1
    ⟨leg4Land_w3_armG_of_mid2fail2G hcr hlip i L hp hLb hHb hmid hAG,
      leg4Land_w3_armT_of_mid2fail2G hcr hlip i L hp hLb hHb hmid hAT⟩

end Pair

end HPC.Fold
