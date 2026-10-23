import HPC.Fold.Mid2MixedG67

/-!
# The index recovered: the residue for `Mid2Floor` itself

`Mid2MixedG67` proves the residue of the branch at `L + 5` for the **relaxed** clause `Mid2Floor2`,
whose landmark is allowed at arm index two, and `Mid2Slack67` shows that the missing index cannot be
recovered from one arm. It can be recovered from the pairing, and that is what this file does.

Everything downstream of the landmark is already generic: `w3_or_wb_of_land` asks only for the two
landmark lemmas, in the form

> before every link of the arm whose interval reaches `L + 8` there is a time of that arm at `L + 4`
> or below, at arm index three or more and twelve steps earlier.

So it is enough to prove those two from a failure of `Mid2Floor` — the weaker hypothesis, since
`Mid2Floor` implies `Mid2Floor2` — rather than from a failure of `Mid2Floor2`. A failure of
`Mid2Floor` at a descent `d` to exactly `L + 2` leaves the window `[3, d - 4]` empty of times at
`L + 6` or above, one index narrower than the window a failure of `Mid2Floor2` leaves. Two places
feel the difference, and both are repaired:

* **the index a high link forces.** A link whose interval reaches `L + 8` sits at arm index five or
  more, not two: three levels above the basepoint cost `z 3 - 1 = 5` steps, and the timing law
  reads intervals, not levels. The batch-66 proofs used the *level* and 1-Lipschitzness, which gives
  only two; reading the interval instead gives five, and the narrower window still applies.
* **the peak of the pairing at index two.** At a descent of the partner the pairing's peak is at
  `L + 6` or above with its interval reaching `L + 7`, which the law puts at arm index two or more
  and no further. Where it is exactly two the window does not exclude it — but then the valley that
  follows it, at `L + 3` or below, would have to sit at arm index one or zero, and the arm is at
  `L + 4` or above there, because it starts at `L + 5` and is 1-Lipschitz. So the valley is a time
  of the *other* arm, which is all the landmark lemma claims.

Hence `land_ascent_sig_of_mid2fail`, `land_ascent_armT_sig_of_mid2fail` and their two mirrors, and
with them

* `crossMid2` — **the residue `CrossMid2L5'` of the branch at `L + 5`, proved**: at a crossing of
  the trichotomy both arms satisfy `Mid2Floor`, the floor clause at the descents to exactly `L + 2`
  that `w71` and `w72` ask for.
-/

namespace HPC.Fold

/-- **The descent at which `Mid2Floor` fails, with its window written out.** One index narrower
than `mid2Fail2_witness`. -/
theorem mid2Fail_witness3 {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : ¬ Mid2Floor f L) :
    ∃ d : Fin m, f d = L + 2 ∧
      ∀ j : Fin m, 3 ≤ j.val → j.val + 4 ≤ d.val → f j ≤ L + 5 := by
  classical
  unfold Mid2Floor at h
  push_neg at h
  obtain ⟨d, hd, hno⟩ := h
  refine ⟨d, hd, fun j h3 h4 => ?_⟩
  have := hno j (by omega) (by omega)
  omega

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## A link whose interval reaches `L + 8` is at arm index five or more -/

/-- **On the forward arm.** Three levels above the basepoint cost `z 3 - 1 = 5` steps, and a link
whose interval reaches `L + 8` is three levels above `L + 5`. -/
theorem armG_index_of_sig8 (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (q : Fin (n - i.val)) (b : Fin n) (hbe : b.val = i.val + q.val) (hq : L + 8 ≤ σ b) :
    5 ≤ q.val := by
  have hi := i.isLt
  have hqn := q.isLt
  have hw := hcr.width b
  have hz : z 3 = 6 := by decide
  set v : ℤ := max (ρ b) (L + 8) with hvdef
  have hbv : ρ b ≤ v := le_max_left _ _
  have hvb : v ≤ σ b := by
    rcases le_or_gt (ρ b) (L + 8) with h | h
    · simp only [hvdef, max_eq_right h]; exact hq
    · simp only [hvdef, max_eq_left (by omega : L + 8 ≤ ρ b)]; exact hcr.le b
  have hv8 : L + 8 ≤ v := le_max_right _ _
  have hne : i.val ≠ b.val := by
    intro hc
    have : i = b := Fin.ext hc
    rw [← this] at hw hq
    omega
  rcases ivSep hcr i b hne 3 (L + 5) v (by push_cast; omega)
    (le_of_eq hp) (by have := hcr.le i; omega) hbv hvb with h | h
  · omega
  · omega

/-- **On the backward arm.** -/
theorem armT_index_of_sig8 (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (q : Fin (i.val + 1)) (a : Fin n) (hae : a.val = i.val - q.val) (hq : L + 8 ≤ σ a) :
    5 ≤ q.val := by
  have hi := i.isLt
  have hqn := q.isLt
  have hw := hcr.width a
  have hz : z 3 = 6 := by decide
  set v : ℤ := max (ρ a) (L + 8) with hvdef
  have hav : ρ a ≤ v := le_max_left _ _
  have hva : v ≤ σ a := by
    rcases le_or_gt (ρ a) (L + 8) with h | h
    · simp only [hvdef, max_eq_right h]; exact hq
    · simp only [hvdef, max_eq_left (by omega : L + 8 ≤ ρ a)]; exact hcr.le a
  have hv8 : L + 8 ≤ v := le_max_right _ _
  have hne : i.val ≠ a.val := by
    intro hc
    have : i = a := Fin.ext hc
    rw [← this] at hw hq
    omega
  rcases ivSep hcr i a hne 3 (L + 5) v (by push_cast; omega)
    (le_of_eq hp) (by have := hcr.le i; omega) hav hva with h | h
  · omega
  · omega

/-! ## Where a failing arm can be high, with the narrower window -/

/-- **The backward arm as the failing one.** Every link of the failing arm whose interval reaches
`L + 8` lies past the failing descent: it is at arm index five or more, the window puts it at
`L + 5` or below if it is four steps or more before the descent, and six levels cost seventy steps
otherwise. -/
theorem mid2fail_high_late_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (dT : Fin (i.val + 1)) (hdT : armT ρ i dT = L + 2)
    (hwin : ∀ j : Fin (i.val + 1), 3 ≤ j.val → j.val + 4 ≤ dT.val → armT ρ i j ≤ L + 5)
    (q : Fin (i.val + 1)) (a : Fin n) (hae : a.val = i.val - q.val) (hq : L + 8 ≤ σ a) :
    dT.val < q.val := by
  have hi := i.isLt
  have hqn := q.isLt
  have hdTn := dT.isLt
  have hav : ρ a = armT ρ i q := by
    show ρ a = ρ ⟨i.val - q.val, by omega⟩
    congr 1
    exact Fin.ext (by omega)
  have hw := hcr.width a
  have hq7 : L + 7 ≤ armT ρ i q := by rw [← hav]; omega
  have hq5 := armT_index_of_sig8 hcr i L hp q a hae hq
  rcases Nat.lt_or_ge dT.val q.val with hlt | hge
  · exact hlt
  exfalso
  rcases Nat.lt_or_ge (q.val + 4) (dT.val + 1) with hfar | hnear
  · have := hwin q (by omega) (by omega)
    omega
  · have hqne : q.val ≠ dT.val := by
      intro hc
      have : q = dT := Fin.ext hc
      rw [this, hdT] at hq7
      omega
    have hne : (⟨i.val - dT.val, by omega⟩ : Fin n).val ≠ a.val := by
      simp only []
      omega
    have hdv : armT ρ i dT = ρ ⟨i.val - dT.val, by omega⟩ := rfl
    have hz : z 6 = 71 := by decide
    set w : ℤ := max (ρ a) (L + 8) with hwdef
    have haw : ρ a ≤ w := le_max_left _ _
    have hwa : w ≤ σ a := by
      rcases le_or_gt (ρ a) (L + 8) with h | h
      · simp only [hwdef, max_eq_right h]; exact hq
      · simp only [hwdef, max_eq_left (by omega : L + 8 ≤ ρ a)]; exact hcr.le a
    have hw8 : L + 8 ≤ w := le_max_right _ _
    rcases ivSep hcr ⟨i.val - dT.val, by omega⟩ a hne 6
      (armT ρ i dT) w (by push_cast; omega) (le_of_eq hdv)
      (by rw [hdv]; exact hcr.le _) haw hwa with hc | hc
    · simp only [] at hc; omega
    · simp only [] at hc; omega

/-- **The forward arm as the failing one.** -/
theorem mid2fail_high_late_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (dG : Fin (n - i.val)) (hdG : armG ρ i dG = L + 2)
    (hwin : ∀ j : Fin (n - i.val), 3 ≤ j.val → j.val + 4 ≤ dG.val → armG ρ i j ≤ L + 5)
    (q : Fin (n - i.val)) (b : Fin n) (hbe : b.val = i.val + q.val) (hq : L + 8 ≤ σ b) :
    dG.val < q.val := by
  have hi := i.isLt
  have hqn := q.isLt
  have hdGn := dG.isLt
  have hbv : ρ b = armG ρ i q := by
    show ρ b = ρ ⟨i.val + q.val, by omega⟩
    congr 1
    exact Fin.ext (by omega)
  have hw := hcr.width b
  have hq7 : L + 7 ≤ armG ρ i q := by rw [← hbv]; omega
  have hq5 := armG_index_of_sig8 hcr i L hp q b hbe hq
  rcases Nat.lt_or_ge dG.val q.val with hlt | hge
  · exact hlt
  exfalso
  rcases Nat.lt_or_ge (q.val + 4) (dG.val + 1) with hfar | hnear
  · have := hwin q (by omega) (by omega)
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

/-! ## The landmark on the arm that does not fail -/

/-- **The forward arm's landmark, when the backward arm fails `Mid2Floor`.** The pairing between
the failing descent and the forward arm's high link returns a peak and, after it, a valley at
`L + 3` or below. The peak is at arm index two or more; where it is three or more the window
excludes it from the failing arm, and where it is exactly two the valley after it would have to sit
at arm index one or zero of the failing arm, where the arm is at `L + 4` or above. So the valley is
a time of the forward arm, and it is the landmark. -/
theorem land_ascent_sig_of_mid2fail (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor (armT ρ i) L)
    (e : Fin (n - i.val)) (b : Fin n) (hbe : b.val = i.val + e.val) (he : L + 8 ≤ σ b) :
    ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ e.val ∧ armG ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hen := e.isLt
  have hmT : 0 < i.val + 1 := by omega
  have h0T : armT ρ i ⟨0, hmT⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  obtain ⟨dT, hdT, hwin⟩ := mid2Fail_witness3 hmid
  have hdTn := dT.isLt
  have hdT0 : 0 < dT.val := by
    rcases Nat.eq_zero_or_pos dT.val with h | h
    · exfalso
      have : armT ρ i dT = ρ i := by
        show ρ ⟨i.val - dT.val, _⟩ = ρ i
        congr 1
        exact Fin.ext (by show i.val - dT.val = i.val; omega)
      omega
    · exact h
  set a : Fin n := ⟨i.val - dT.val, by omega⟩ with hadef
  have hav : ρ a = armT ρ i dT := rfl
  have hab : a.val < b.val := by simp only [hadef]; omega
  obtain ⟨r, r', h1, h2, h3, hr6, hr7, hr'1, hr'2⟩ :=
    crooked_peak_valley_high8 hcr a b hab L (by omega) he
  have havl : a.val = i.val - dT.val := rfl
  have hrn := r.isLt
  have hr'n := r'.isLt
  -- the valley is a time of the forward arm
  have hr'i : i.val < r'.val := by
    by_contra hc
    push_neg at hc
    have hrle : r.val < i.val := by omega
    -- two levels above the basepoint cost two steps
    have hr2 : i.val - r.val ≥ 2 := by
      have hne : i.val ≠ r.val := by
        intro h
        have : i = r := Fin.ext h
        rw [← this] at hr6
        omega
      have hz : z 2 = 3 := by decide
      set v : ℤ := max (ρ r) (L + 7) with hvdef
      have hrv : ρ r ≤ v := le_max_left _ _
      have hvr : v ≤ σ r := by
        rcases le_or_gt (ρ r) (L + 7) with h | h
        · simp only [hvdef, max_eq_right h]; exact hr7
        · simp only [hvdef, max_eq_left (by omega : L + 7 ≤ ρ r)]; exact hcr.le r
      have hv7 : L + 7 ≤ v := le_max_right _ _
      rcases ivSep hcr i r hne 2 (L + 5) v (by push_cast; omega)
        (le_of_eq hp) (by have := hcr.le i; omega) hrv hvr with h | h
      · omega
      · omega
    rcases Nat.lt_or_ge (i.val - r.val) 3 with hlt | hge
    · -- the peak sits at arm index two; the valley would then be at index one or zero
      have hr'two : i.val - r'.val ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos (i.val - r'.val) with hz0 | hz1
      · have hri' : r' = i := Fin.ext (by omega)
        rw [hri'] at hr'1
        omega
      · have hone : i.val - r'.val = 1 := by omega
        have h1lt : 1 < i.val + 1 := by omega
        have hv : armT ρ i ⟨1, h1lt⟩ = ρ r' := by
          show ρ ⟨i.val - 1, _⟩ = ρ r'
          congr 1
          exact Fin.ext (by show i.val - 1 = r'.val; omega)
        have hstep : |armT ρ i ⟨1, h1lt⟩ - armT ρ i ⟨0, hmT⟩| ≤ 1 :=
          armT_isLip hlip i ⟨0, hmT⟩ ⟨1, h1lt⟩ (by simp)
        rw [hv] at hstep
        have := abs_le.mp hstep
        omega
    · -- the peak sits inside the window the failure empties
      have hjr : i.val - r.val < i.val + 1 := by omega
      have hjv : armT ρ i ⟨i.val - r.val, hjr⟩ = ρ r := by
        show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
        congr 1
        exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
      have := hwin ⟨i.val - r.val, hjr⟩ (by simp; omega) (by simp; omega)
      rw [hjv] at this
      omega
  set R : ℕ := r'.val - i.val with hRdef
  have hRlt : R < e.val := by omega
  have hRv : armG ρ i ⟨R, by omega⟩ = ρ r' := by
    show ρ ⟨i.val + R, _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + R = r'.val; omega)
  have hlow : ρ r' ≤ L + 3 := by omega
  have hR2 : 2 ≤ R := by
    have hne : r'.val ≠ i.val := by omega
    have hz : z 2 = 3 := by decide
    rcases ivSep hcr r' i hne 2 (ρ a + 1) (L + 5) (by push_cast; omega)
      hr'1 hr'2 (le_of_eq hp) (by have := hcr.le i; omega) with h | h
    · omega
    · omega
  have hgap : R + 29 ≤ e.val := by
    have hne : r'.val ≠ b.val := by omega
    have hz : z 5 = 30 := by decide
    set w : ℤ := max (ρ b) (L + 8) with hwdef
    have hbw : ρ b ≤ w := le_max_left _ _
    have hwb : w ≤ σ b := by
      rcases le_or_gt (ρ b) (L + 8) with h | h
      · simp only [hwdef, max_eq_right h]; exact he
      · simp only [hwdef, max_eq_left (by omega : L + 8 ≤ ρ b)]; exact hcr.le b
    have hw8 : L + 8 ≤ w := le_max_right _ _
    rcases ivSep hcr r' b hne 5 (ρ a + 1) w (by push_cast; omega)
      hr'1 hr'2 hbw hwb with h | h
    · omega
    · omega
  rcases Nat.lt_or_ge R 3 with hR3 | hR3
  · have h3lt : 3 < n - i.val := by omega
    refine ⟨⟨3, h3lt⟩, le_rfl, by simp; omega, ?_⟩
    have hstep : |armG ρ i ⟨3, h3lt⟩ - armG ρ i ⟨R, by omega⟩| ≤ 1 :=
      armG_isLip hlip i ⟨R, by omega⟩ ⟨3, h3lt⟩ (by simp; omega)
    rw [hRv] at hstep
    have := abs_le.mp hstep
    omega
  · exact ⟨⟨R, by omega⟩, hR3, by simp; omega, by rw [hRv]; omega⟩

/-- **The failing backward arm's own landmark.** Its high links lie past its failing descent, and
crookedness read from such a link towards that descent puts the valley in between, on the same
arm. -/
theorem land_ascent_armT_sig_of_mid2fail (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor (armT ρ i) L)
    (q : Fin (i.val + 1)) (a : Fin n) (hae : a.val = i.val - q.val) (hq : L + 8 ≤ σ a) :
    ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hqn := q.isLt
  obtain ⟨dT, hdT, hwin⟩ := mid2Fail_witness3 hmid
  have hdTn := dT.isLt
  have hlate := mid2fail_high_late_armT hcr i L hp dT hdT hwin q a hae hq
  set b : Fin n := ⟨i.val - dT.val, by omega⟩ with hbdef
  have hbv : ρ b = armT ρ i dT := rfl
  have hab : a.val < b.val := by simp only [hbdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, hr2, -, -⟩ :=
    crooked_valley_peak_high8 hcr a b hab L hq (by omega)
  have hbvl : b.val = i.val - dT.val := rfl
  have hrn := r.isLt
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
    rcases ivSep hcr r i hne 2 (armT ρ i dT + 1) (L + 5) (by push_cast; omega)
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

/-! ## The mirror: the forward arm as the failing one -/

/-- **The failing forward arm's own landmark.** -/
theorem land_ascent_armG_sig_of_mid2failG (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor (armG ρ i) L)
    (q : Fin (n - i.val)) (b : Fin n) (hbe : b.val = i.val + q.val) (hq : L + 8 ≤ σ b) :
    ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hqn := q.isLt
  obtain ⟨dG, hdG, hwin⟩ := mid2Fail_witness3 hmid
  have hdGn := dG.isLt
  have hlate := mid2fail_high_late_armG hcr i L hp dG hdG hwin q b hbe hq
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

/-- **The backward arm's landmark, when the forward arm fails `Mid2Floor`.** -/
theorem land_ascent_armT_sig_of_mid2failG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor (armG ρ i) L)
    (q : Fin (i.val + 1)) (a : Fin n) (hae : a.val = i.val - q.val) (hq : L + 8 ≤ σ a) :
    ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hqn := q.isLt
  have hmG : 0 < n - i.val := by omega
  have h0G : armG ρ i ⟨0, hmG⟩ = L + 5 := by
    show ρ ⟨i.val + 0, _⟩ = L + 5
    rw [show (⟨i.val + 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  obtain ⟨dG, hdG, hwin⟩ := mid2Fail_witness3 hmid
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
  -- the valley is a time of the backward arm
  have hri : r.val < i.val := by
    by_contra hc
    push_neg at hc
    have hr'ge : i.val < r'.val := by omega
    have hs2 : 2 ≤ r'.val - i.val := by
      have hne : i.val ≠ r'.val := by
        intro h
        have : i = r' := Fin.ext h
        rw [← this] at hr'6
        omega
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
      · omega
      · omega
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
    rcases Nat.lt_or_ge (r'.val - i.val) 3 with hlt | hge
    · -- the peak sits at arm index two; the valley would then be at index one or zero
      have hrle : r.val - i.val ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos (r.val - i.val) with hz0 | hz1
      · have hri' : r = i := Fin.ext (by omega)
        rw [hri'] at hr1
        omega
      · have hone : r.val - i.val = 1 := by omega
        have h1lt : 1 < n - i.val := by omega
        have hv : armG ρ i ⟨1, h1lt⟩ = ρ r := by
          show ρ ⟨i.val + 1, _⟩ = ρ r
          congr 1
          exact Fin.ext (by show i.val + 1 = r.val; omega)
        have hstep : |armG ρ i ⟨1, h1lt⟩ - armG ρ i ⟨0, hmG⟩| ≤ 1 :=
          armG_isLip hlip i ⟨0, hmG⟩ ⟨1, h1lt⟩ (by simp)
        rw [hv] at hstep
        have := abs_le.mp hstep
        omega
    · have hjr : r'.val - i.val < n - i.val := by omega
      have hjv : armG ρ i ⟨r'.val - i.val, hjr⟩ = ρ r' := by
        show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
        congr 1
        exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
      have := hwin ⟨r'.val - i.val, hjr⟩ (by simp; omega) (by simp; omega)
      rw [hjv] at this
      omega
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

/-! ## The residue of the branch at `L + 5` -/

/-- **One of the two reflected walks serves both arms, when the backward arm fails `Mid2Floor`.** -/
theorem w3_or_wb_of_mid2floorFailT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor (armT ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) ∨
      (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)) :=
  w3_or_wb_of_land hcr i L hp hLb hHb
    (fun q b hb hq => land_ascent_sig_of_mid2fail hcr hlip i L hp hmid q b hb hq)
    (fun q a ha hq => land_ascent_armT_sig_of_mid2fail hcr hlip i L hp hmid q a ha hq)
    hGlow hTlow

/-- **The mirror.** -/
theorem w3_or_wb_of_mid2floorFailG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor (armG ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) ∨
      (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)) :=
  w3_or_wb_of_land hcr i L hp hLb hHb
    (fun q b hb hq => land_ascent_armG_sig_of_mid2failG hcr i L hp hmid q b hb hq)
    (fun q a ha hq => land_ascent_armT_sig_of_mid2failG hcr hlip i L hp hmid q a ha hq)
    hGlow hTlow

/-- **The pair folds at a basepoint of the branch whose backward arm fails `Mid2Floor`.** -/
theorem s3_span_nine_mid5_of_mid2floorFailT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor (armT ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  rcases w3_or_wb_of_mid2floorFailT hcr hlip i L hp hLb hHb hmid hGlow hTlow with
    ⟨hG, hT⟩ | ⟨hG, hT⟩
  · exact s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 1) (L + 4) hlip hLb hHb hp
      (leg4Window_w3 L) (by omega) (by omega) hG hT
  · exact s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 2) (L + 4) hlip hLb hHb hp
      (leg4Window_wb L) (by omega) (by omega) hG hT

/-- **The mirror fold.** -/
theorem s3_span_nine_mid5_of_mid2floorFailG (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor (armG ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  rcases w3_or_wb_of_mid2floorFailG hcr hlip i L hp hLb hHb hmid hGlow hTlow with
    ⟨hG, hT⟩ | ⟨hG, hT⟩
  · exact s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 1) (L + 4) hlip hLb hHb hp
      (leg4Window_w3 L) (by omega) (by omega) hG hT
  · exact s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 2) (L + 4) hlip hLb hHb hp
      (leg4Window_wb L) (by omega) (by omega) hG hT

/-- **`CrossMid2L5'`, the residue of the branch at `L + 5`, proved.** At a crossing of the
trichotomy — a basepoint of a 1-Lipschitz crooked chain inside the band `[L, L + 9]`, based at
`L + 5`, with the branch hypothesis on both arms, and served by none of the three walk pairs —
**both** arms satisfy `Mid2Floor`: at every descent of the arm to exactly `L + 2` there is an
earlier time at `L + 6` or above, at arm index three or more and four steps earlier.

This is the clause `w71` and `w72` ask for, at the index they ask for it; batch 66 and
`crossMid2_relaxed` proved the form relaxed by one index, and `not_mid2Floor_of_mid2Floor2_arm`
shows the index cannot be recovered from an arm on its own. It is recovered here from the pairing:
a link whose interval reaches `L + 8` is at arm index five or more, and the one place the narrower
window does not reach — the pairing's peak at arm index two — is excluded because the valley that
follows it would have to sit where the arm is still within one of its basepoint. -/
theorem crossMid2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) :
    Mid2Floor (armT ρ i) L ∧ Mid2Floor (armG ρ i) L := by
  classical
  constructor
  · by_contra hmid
    rcases w3_or_wb_of_mid2floorFailT hcr hlip i L hp hLb hHb hmid hGlow hTlow with h | h
    · exact hcross.2.1 h
    · exact hcross.2.2 h
  · by_contra hmid
    rcases w3_or_wb_of_mid2floorFailG hcr hlip i L hp hLb hHb hmid hGlow hTlow with h | h
    · exact hcross.2.1 h
    · exact hcross.2.2 h

/-- **The residue as the batch-65 statement.** `crossMid2` is stronger: `CrossMid2L5'` asks for the
clause only on an arm that `w8` does not serve. -/
theorem crossMid2L5' : CrossMid2L5' := by
  intro n ρ σ i L hlip hcr hLb hHb hp hG hT hcross
  obtain ⟨hT2, hG2⟩ := crossMid2 hcr hlip i L hp hLb hHb hG hT hcross
  exact ⟨fun _ => hT2, fun _ => hG2⟩

/-! ## The batch-64 two-walk assembly, with its residual clause discharged -/

/-- **`s3_span_nine_mid5_of_cross_wb_two_walks` at a crossing, with `Mid2Floor` supplied.** At a
crossing of the trichotomy whose backward arm is served by `wb`, the pair folds as soon as the
forward arm satisfies `w71`, or satisfies `w72` while the backward arm has its deep-floor clause.
The clause the batch-64 statement carried as a hypothesis is now a theorem. -/
theorem s3_span_nine_mid5_of_cross_wb_two_walks_of_cross (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (hb : Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hside : Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ∨
      (Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) ∧ Deep72 (armT ρ i) L)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_wb_two_walks hlip i L hp hHb hLb hb
    (crossMid2 hcr hlip i L hp hLb hHb hGlow hTlow hcross).1 hside

/-- **The mirror**, for a crossing whose partner is the forward arm. -/
theorem s3_span_nine_mid5_of_cross_wb_two_walks_armG_of_cross (hcr : IsCrookedIvF ρ σ)
    (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L ≤ ρ t)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L)
    (hb : Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4))
    (hside : Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 1) (L + 5) ∨
      (Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 2) (L + 5) ∧ Deep72 (armG ρ i) L)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_cross_wb_two_walks_armG hlip i L hp hHb hLb hb
    (crossMid2 hcr hlip i L hp hLb hHb hGlow hTlow hcross).2 hside

end Pair

end HPC.Fold
