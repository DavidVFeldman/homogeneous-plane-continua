import HPC.Fold.Mid2Wb66

/-!
# The mixed basepoint: the two families of batch 66 joined

`Mid2Fold66` gives both arms the reflected walk `w3` when every descent to `L + 1` is preceded by a
time at `L + 8`; `Mid2Wb66` gives both arms `wb` when every ascent to `L + 9` is preceded by a
descent to `L + 1`. This file closes the case the two leave open — the *mixed* basepoint, where one
arm is of the first kind and the other of the second.

Three things do it.

* `highFirst_or_deepFirst` — no arm is of neither kind. If an arm has a descent to `L + 1` with no
  earlier time at `L + 8`, that descent lies before every one of the arm's times at `L + 9`, so the
  arm is deep first. The two families are therefore exhaustive per arm, and the only gap is the
  basepoint whose two arms fall on different sides.
* `crooked_peak_valley_high9` — the pairing read against a link at `L + 1` or below and a link at
  `L + 9`, which is the top of the band. Because the high link carries the level `L + 9` itself,
  the peak the pairing returns carries `L + 8`, so its own level is `L + 7` or above — one level
  higher than `crooked_peak_valley_high8` gives — and the valley is at `L + 2` or below, one level
  lower. Those are exactly the two levels the `L + 2`/`L + 1` seam was short of.
* `mixed_ceilT_or_deepG` — read that pairing between a descent of one arm to `L + 1` and an ascent
  of the other to `L + 9`. The peak lands on one of the two arms. If it lands on the arm with the
  descent, that arm gets the ceiling clause of `w3` at that descent; if it lands on the arm with
  the ascent, that arm gets the deep clause of `wb` at that ascent. Either way the landmark at
  `L + 4` before the peak is free, because the peak's interval reaches `L + 8` and the failure of
  `Mid2Floor2` supplies the landmark before every such link.

So at a basepoint whose backward arm fails `Mid2Floor2`: either every descent of the failing arm
carries `w3`'s ceiling clause — and then, the other arm being high first, both arms are served by
`w3` — or one descent does not, and then every ascent of the other arm carries `wb`'s deep clause,
and both arms are served by `wb`. That is `w3_or_wb_of_mid2fail2`, and with it
`crossMid2_relaxed_of_mid2failT`: at a crossing of the trichotomy the backward arm satisfies
`Mid2Floor2`, with no condition on how the branch hypothesis is met.

The `σ`-forms of the landmark lemmas of batch 66 are proved here as well
(`land_ascent_sig_of_mid2fail2`, `land_ascent_armT_sig_of_mid2fail2`): the pairing hands back a
peak whose *interval* reaches `L + 8` while its own level may be only `L + 7`, and the batch-66
lemmas are stated for the level. Their proofs use the level only through the interval, so the
`σ`-form is the same argument.
-/

namespace HPC.Fold

/-! ## The two kinds of arm -/

/-- **High first.** Before every descent to `L + 1` the arm has been at `L + 8`. This is the first
disjunct of the branch hypothesis, asked at every descent; it is what `w3` needs. -/
def HighFirst {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d ≤ L + 1 → ∃ p : Fin m, p.val < d.val ∧ L + 8 ≤ f p

/-- **Deep first.** Before every ascent to `L + 9` the arm has been at `L + 1`. This is what `wb`
needs; an arm that never reaches `L + 9` satisfies it vacuously. -/
def DeepFirst {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ e : Fin m, L + 9 ≤ f e → ∃ d : Fin m, d.val < e.val ∧ f d ≤ L + 1

/-- **Every arm is of one kind or the other.** If the arm is not high first it has a descent `d` to
`L + 1` with no earlier time at `L + 8`; every time at `L + 9` is then past `d`, since a time at
`L + 9` before `d` would be the missing `L + 8`, so `d` itself witnesses deep first. -/
theorem highFirst_or_deepFirst {m : ℕ} (f : Fin m → ℤ) (L : ℤ) :
    HighFirst f L ∨ DeepFirst f L := by
  classical
  by_cases hA : HighFirst f L
  · exact Or.inl hA
  refine Or.inr ?_
  unfold HighFirst at hA
  push_neg at hA
  obtain ⟨d, hd, hno⟩ := hA
  intro e he
  refine ⟨d, ?_, hd⟩
  rcases Nat.lt_or_ge d.val e.val with h | h
  · exact h
  · exfalso
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · have : e = d := Fin.ext h'
      rw [this] at he; omega
    · exact absurd he (by have := hno e h'; omega)

/-! ## The pairing at the top of the band -/

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-- **The crooked pair read against a link carrying `L + 9`.** From a link at `L + 1` or below and a
later link carrying the top level `L + 9`, crookedness produces a peak carrying `L + 8` — so at
`L + 7` or above itself, since a link is one level wide — and, after it, a valley at `ρ a + 1` or
below. The timing law spaces the three: `169` steps from the low link to the peak (seven levels),
`70` from the peak to the valley (six), and `169` from the valley to the high link (seven). -/
theorem crooked_peak_valley_high9 (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha : ρ a ≤ L + 1)
    (hb1 : ρ b ≤ L + 9) (hb2 : L + 9 ≤ σ b) :
    ∃ r r' : Fin n, a.val + 169 ≤ r.val ∧ r.val + 70 ≤ r'.val ∧ r'.val + 169 ≤ b.val ∧
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
  have hz6 : z 6 = 71 := by decide
  have hz7 : z 7 = 170 := by decide
  have h1 : a.val + 169 ≤ r.val := by
    rcases ivSep hcr a r (by omega) 7 (ρ a) (L + 9 - 1) (by push_cast; omega)
      le_rfl (hcr.le a) hr1 hr2 with h | h
    · omega
    · omega
  have h2 : r.val + 70 ≤ r'.val := by
    rcases ivSep hcr r' r (by omega) 6 (ρ a + 1) (L + 9 - 1) (by push_cast; omega)
      hr'1 hr'2 hr1 hr2 with h | h
    · omega
    · omega
  have h3 : r'.val + 169 ≤ b.val := by
    rcases ivSep hcr r' b (by omega) 7 (ρ a + 1) (L + 9) (by push_cast; omega)
      hr'1 hr'2 hb1 hb2 with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, h3, by omega, by omega, hr'1, hr'2⟩

/-- **The same pair read from the high link.** From a link carrying `L + 9` and a *later* link at
`L + 1` or below, crookedness produces first a valley at `ρ b + 1` or below and then a peak carrying
`L + 8`. -/
theorem crooked_valley_peak_high9 (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha1 : ρ a ≤ L + 9) (ha2 : L + 9 ≤ σ a)
    (hb : ρ b ≤ L + 1) :
    ∃ r r' : Fin n, a.val + 169 ≤ r.val ∧ r.val + 70 ≤ r'.val ∧ r'.val + 169 ≤ b.val ∧
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
  have hz6 : z 6 = 71 := by decide
  have hz7 : z 7 = 170 := by decide
  have h1 : a.val + 169 ≤ r.val := by
    rcases ivSep hcr r a (by omega) 7 (ρ b + 1) (L + 9) (by push_cast; omega)
      hr1 hr2 ha1 ha2 with h | h
    · omega
    · omega
  have h2 : r.val + 70 ≤ r'.val := by
    rcases ivSep hcr r r' (by omega) 6 (ρ b + 1) (L + 9 - 1) (by push_cast; omega)
      hr1 hr2 hr'1 hr'2 with h | h
    · omega
    · omega
  have h3 : r'.val + 169 ≤ b.val := by
    rcases ivSep hcr b r' (by omega) 7 (ρ b) (L + 9 - 1) (by push_cast; omega)
      le_rfl (hcr.le b) hr'1 hr'2 with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, h3, hr1, hr2, by omega, by omega⟩

/-! ## The landmark lemmas, read on the interval -/

/-- **The `σ`-form of `land_ascent_of_mid2fail2`.** A partner that fails the relaxed clause gives
the forward arm a low landmark before every link of that arm whose *interval* reaches `L + 8` —
not only before its times at `L + 8`. The proof of batch 66 uses the level only through the
interval. -/
theorem land_ascent_sig_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (e : Fin (n - i.val)) (b : Fin n) (hbe : b.val = i.val + e.val) (he : L + 8 ≤ σ b) :
    ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ e.val ∧ armG ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hen := e.isLt
  obtain ⟨dT, hdT, hwin⟩ := mid2Fail2_witness hmid
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
  -- the peak cannot be a time of the partner
  have hri : i.val < r.val := by
    by_contra hc
    push_neg at hc
    have hne : i.val ≠ r.val := by
      intro h
      have : i = r := Fin.ext h
      rw [← this] at hr6
      omega
    have hsep : i.val + 2 ≤ r.val ∨ r.val + 2 ≤ i.val := by
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
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hjr : i.val - r.val < i.val + 1 := by omega
    have hjv : armT ρ i ⟨i.val - r.val, hjr⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    have := hwin ⟨i.val - r.val, hjr⟩ (by simp; omega) (by simp; omega)
    rw [hjv] at this
    omega
  have hr'i : i.val < r'.val := by omega
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

/-- **The `σ`-form of `mid2fail2_high_late`.** Every link of the failing arm whose interval reaches
`L + 8` lies past the failing descent. Its own level is then `L + 7` or above, which is still above
the `L + 5` the failure leaves in its window; the index bound the basepoint forces drops from three
to two, which is all the window needs. -/
theorem mid2fail2_high_late_sig (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (dT : Fin (i.val + 1)) (hdT : armT ρ i dT = L + 2)
    (hwin : ∀ j : Fin (i.val + 1), 2 ≤ j.val → j.val + 4 ≤ dT.val → armT ρ i j ≤ L + 5)
    (q : Fin (i.val + 1)) (a : Fin n) (hae : a.val = i.val - q.val) (hq : L + 8 ≤ σ a) :
    dT.val < q.val := by
  have hi := i.isLt
  have hqn := q.isLt
  have hdTn := dT.isLt
  have hm : 0 < i.val + 1 := by omega
  have hav : ρ a = armT ρ i q := by
    show ρ a = ρ ⟨i.val - q.val, by omega⟩
    congr 1
    exact Fin.ext (by omega)
  have hw := hcr.width a
  have hq7 : L + 7 ≤ armT ρ i q := by rw [← hav]; omega
  have h0 : armT ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  have hq2 : 2 ≤ q.val := by
    have := isLip_index_gap (armT_isLip hlip i) (j := ⟨0, hm⟩) (k := q) (Nat.zero_le _)
      (armT ρ i q - armT ρ i ⟨0, hm⟩) (by omega)
    simp only [Nat.cast_zero, zero_add] at this
    omega
  rcases Nat.lt_or_ge dT.val q.val with hlt | hge
  · exact hlt
  exfalso
  rcases Nat.lt_or_ge (q.val + 4) (dT.val + 1) with hfar | hnear
  · have := hwin q hq2 (by omega)
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

/-- **The `σ`-form of `land_ascent_armT_of_mid2fail2`.** The failing arm itself has a low landmark
before every link of its own whose interval reaches `L + 8`. -/
theorem land_ascent_armT_sig_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (q : Fin (i.val + 1)) (a : Fin n) (hae : a.val = i.val - q.val) (hq : L + 8 ≤ σ a) :
    ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hqn := q.isLt
  obtain ⟨dT, hdT, hwin⟩ := mid2Fail2_witness hmid
  have hdTn := dT.isLt
  have hlate := mid2fail2_high_late_sig hcr hlip i L hp dT hdT hwin q a hae hq
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

/-! ## The mixed basepoint: the peak decides which walk

From here on the two landmark lemmas are hypotheses rather than consequences of a particular arm's
failure, so that the mirror — the forward arm as the failing one — can read the same argument.
Both are stated on the interval: a landmark at `L + 4` or below, at arm index three or more and
twelve steps earlier, before every link of the arm whose interval reaches `L + 8`. -/

/-- **At a descent of the backward arm and an ascent of the forward arm, one of the two clauses
holds.** Read the pairing between the backward arm's descent to `L + 1` and the forward arm's time
at `L + 9`. The peak it returns carries `L + 8`, so the landmark hypothesis supplies a time at
`L + 4` or below before it on whichever arm it lies. If the peak lies on the backward arm it is the
`L + 7` that `w3`'s ceiling clause asks for at that descent; if it lies on the forward arm, the
valley that follows it is at `L + 2` or below and the three together are `wb`'s deep clause at that
ascent. -/
theorem mixed_ceilT_or_deepG_of_land (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9)
    (hlandGs : ∀ (q : Fin (n - i.val)) (b : Fin n), b.val = i.val + q.val → L + 8 ≤ σ b →
      ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4)
    (hlandTs : ∀ (q : Fin (i.val + 1)) (a : Fin n), a.val = i.val - q.val → L + 8 ≤ σ a →
      ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4)
    (d : Fin (i.val + 1)) (hd : armT ρ i d ≤ L + 1)
    (e : Fin (n - i.val)) (he : L + 9 ≤ armG ρ i e) :
    (∃ j k : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
        armT ρ i j ≤ L + 4 ∧ L + 7 ≤ armT ρ i k) ∨
      (∃ j k l : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 4 ≤ k.val ∧ k.val + 6 ≤ l.val ∧
        l.val + 7 ≤ e.val ∧ armG ρ i j ≤ L + 4 ∧ L + 6 ≤ armG ρ i k ∧ armG ρ i l ≤ L + 2) := by
  have hi := i.isLt
  have hdn := d.isLt
  have hen := e.isLt
  have he0 : 0 < e.val := by
    rcases Nat.eq_zero_or_pos e.val with h | h
    · exfalso
      have : armG ρ i e = ρ i := by
        show ρ ⟨i.val + e.val, _⟩ = ρ i
        congr 1
        exact Fin.ext (by show i.val + e.val = i.val; omega)
      omega
    · exact h
  set a : Fin n := ⟨i.val - d.val, by omega⟩ with hadef
  set b : Fin n := ⟨i.val + e.val, by omega⟩ with hbdef
  have hav : ρ a = armT ρ i d := rfl
  have hbv : ρ b = armG ρ i e := rfl
  have havl : a.val = i.val - d.val := rfl
  have hbvl : b.val = i.val + e.val := rfl
  have hab : a.val < b.val := by omega
  obtain ⟨r, r', h1, h2, h3, hr7, hr8, hr'1, hr'2⟩ :=
    crooked_peak_valley_high9 hcr a b hab L (by omega) (by rw [hbv]; exact hHb _)
      (by have := hcr.le b; omega)
  have hrn := r.isLt
  have hr'n := r'.isLt
  rcases Nat.lt_or_ge i.val r.val with hri | hri
  · -- the peak is a time of the forward arm: `wb`'s deep clause at the ascent
    refine Or.inr ?_
    have hr'i : i.val < r'.val := by omega
    have hKm : r.val - i.val < n - i.val := by omega
    have hLm : r'.val - i.val < n - i.val := by omega
    have hKv : armG ρ i ⟨r.val - i.val, hKm⟩ = ρ r := by
      show ρ ⟨i.val + (r.val - i.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val + (r.val - i.val) = r.val; omega)
    have hLv : armG ρ i ⟨r'.val - i.val, hLm⟩ = ρ r' := by
      show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
    obtain ⟨j, hj3, hj12, hjlow⟩ :=
      hlandGs ⟨r.val - i.val, hKm⟩ r (by show r.val = i.val + (r.val - i.val); omega) hr8
    have hjv : (⟨r.val - i.val, hKm⟩ : Fin (n - i.val)).val = r.val - i.val := rfl
    have hlv : (⟨r'.val - i.val, hLm⟩ : Fin (n - i.val)).val = r'.val - i.val := rfl
    exact ⟨j, ⟨r.val - i.val, hKm⟩, ⟨r'.val - i.val, hLm⟩, hj3, by omega, by omega, by omega,
      hjlow, by rw [hKv]; omega, by rw [hLv]; omega⟩
  · -- the peak is a time of the backward arm: `w3`'s ceiling clause at the descent
    refine Or.inl ?_
    have htm : i.val - r.val < i.val + 1 := by omega
    have htv : armT ρ i ⟨i.val - r.val, htm⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    obtain ⟨j, hj3, hj12, hjlow⟩ :=
      hlandTs ⟨i.val - r.val, htm⟩ r (by show r.val = i.val - (i.val - r.val); omega) hr8
    have htl : (⟨i.val - r.val, htm⟩ : Fin (i.val + 1)).val = i.val - r.val := rfl
    exact ⟨j, ⟨i.val - r.val, htm⟩, hj3, by omega, by omega, hjlow, by rw [htv]; omega⟩

/-- **The mirror**, with the descent on the forward arm and the ascent on the backward arm. Here
the pairing is read from the high link, so the valley comes first and the peak second; the peak is
still what decides. -/
theorem mixed_ceilG_or_deepT_of_land (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9)
    (hlandGs : ∀ (q : Fin (n - i.val)) (b : Fin n), b.val = i.val + q.val → L + 8 ≤ σ b →
      ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4)
    (hlandTs : ∀ (q : Fin (i.val + 1)) (a : Fin n), a.val = i.val - q.val → L + 8 ≤ σ a →
      ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4)
    (d : Fin (n - i.val)) (hd : armG ρ i d ≤ L + 1)
    (e : Fin (i.val + 1)) (he : L + 9 ≤ armT ρ i e) :
    (∃ j k : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
        armG ρ i j ≤ L + 4 ∧ L + 7 ≤ armG ρ i k) ∨
      (∃ j k l : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 4 ≤ k.val ∧ k.val + 6 ≤ l.val ∧
        l.val + 7 ≤ e.val ∧ armT ρ i j ≤ L + 4 ∧ L + 6 ≤ armT ρ i k ∧ armT ρ i l ≤ L + 2) := by
  have hi := i.isLt
  have hdn := d.isLt
  have hen := e.isLt
  have he0 : 0 < e.val := by
    rcases Nat.eq_zero_or_pos e.val with h | h
    · exfalso
      have : armT ρ i e = ρ i := by
        show ρ ⟨i.val - e.val, _⟩ = ρ i
        congr 1
        exact Fin.ext (by show i.val - e.val = i.val; omega)
      omega
    · exact h
  set a : Fin n := ⟨i.val - e.val, by omega⟩ with hadef
  set b : Fin n := ⟨i.val + d.val, by omega⟩ with hbdef
  have hav : ρ a = armT ρ i e := rfl
  have hbv : ρ b = armG ρ i d := rfl
  have havl : a.val = i.val - e.val := rfl
  have hbvl : b.val = i.val + d.val := rfl
  have hab : a.val < b.val := by omega
  obtain ⟨r, r', h1, h2, h3, hr1, hr2, hr'7, hr'8⟩ :=
    crooked_valley_peak_high9 hcr a b hab L (by rw [hav]; exact hHb _)
      (by have := hcr.le a; omega) (by omega)
  have hrn := r.isLt
  have hr'n := r'.isLt
  rcases Nat.lt_or_ge i.val r'.val with hr'i | hr'i
  · -- the peak is a time of the forward arm: `w3`'s ceiling clause at its descent
    refine Or.inl ?_
    have hKm : r'.val - i.val < n - i.val := by omega
    have hKv : armG ρ i ⟨r'.val - i.val, hKm⟩ = ρ r' := by
      show ρ ⟨i.val + (r'.val - i.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val + (r'.val - i.val) = r'.val; omega)
    obtain ⟨j, hj3, hj12, hjlow⟩ :=
      hlandGs ⟨r'.val - i.val, hKm⟩ r' (by show r'.val = i.val + (r'.val - i.val); omega) hr'8
    have hkl : (⟨r'.val - i.val, hKm⟩ : Fin (n - i.val)).val = r'.val - i.val := rfl
    exact ⟨j, ⟨r'.val - i.val, hKm⟩, hj3, by omega, by omega, hjlow, by rw [hKv]; omega⟩
  · -- the peak is a time of the backward arm: `wb`'s deep clause at its ascent
    refine Or.inr ?_
    have hri : r.val ≤ i.val := by omega
    have hKm : i.val - r'.val < i.val + 1 := by omega
    have hLm : i.val - r.val < i.val + 1 := by omega
    have hKv : armT ρ i ⟨i.val - r'.val, hKm⟩ = ρ r' := by
      show ρ ⟨i.val - (i.val - r'.val), _⟩ = ρ r'
      congr 1
      exact Fin.ext (by show i.val - (i.val - r'.val) = r'.val; omega)
    have hLv : armT ρ i ⟨i.val - r.val, hLm⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    obtain ⟨j, hj3, hj12, hjlow⟩ :=
      hlandTs ⟨i.val - r'.val, hKm⟩ r' (by show r'.val = i.val - (i.val - r'.val); omega) hr'8
    have hkl : (⟨i.val - r'.val, hKm⟩ : Fin (i.val + 1)).val = i.val - r'.val := rfl
    have hll : (⟨i.val - r.val, hLm⟩ : Fin (i.val + 1)).val = i.val - r.val := rfl
    exact ⟨j, ⟨i.val - r'.val, hKm⟩, ⟨i.val - r.val, hLm⟩, hj3, by omega, by omega, by omega,
      hjlow, by rw [hKv]; omega, by rw [hLv]; omega⟩

end Pair

/-! ## The two walks from their clauses -/

/-- **The chain `wb` reads at a descent to `L + 1`.** Either disjunct of the branch hypothesis
supplies it: the first gives a time at `L + 8`, and the landmark before that time is the chain's
first link; the second gives a time at `L + 2` followed by one at `L + 6`, which is the chain
itself. The index gaps are the timing law's. -/
theorem wb_chain_of_land {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (hm : 0 < m)
    (hsep : ArmSep f) (h0 : f ⟨0, hm⟩ = L + 5)
    (hlow : LowAt f (L + 1) (L + 8))
    (hland : ∀ q : Fin m, L + 8 ≤ f q → ∃ j : Fin m, 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧
      f j ≤ L + 4) :
    ∀ d : Fin m, f d ≤ L + 1 → ∃ j k : Fin m, 3 ≤ j.val ∧ j.val + 4 ≤ k.val ∧
      k.val + 6 ≤ d.val ∧ f j ≤ L + 4 ∧ L + 6 ≤ f k := by
  have hz3 : z 3 = 6 := by decide
  have hz4 : z 4 = 13 := by decide
  have hz5 : z 5 = 30 := by decide
  have hz7 : z 7 = 170 := by decide
  have hlowIdx : ∀ j : Fin m, f j ≤ L + 2 → 5 ≤ j.val := by
    intro j hj
    have hne : j.val ≠ (⟨0, hm⟩ : Fin m).val := by
      intro hc
      have : j = ⟨0, hm⟩ := Fin.ext hc
      rw [this, h0] at hj
      omega
    rcases hsep 3 j ⟨0, hm⟩ (by rw [h0]; push_cast; omega) hne with h | h
    · simp only [] at h; omega
    · simp only [] at h; omega
  intro d hd
  rcases hlow d hd with ⟨p, hpd, hp8⟩ | ⟨j, j', hjj', hj'd, hj2, hj'6⟩
  · obtain ⟨j, h1, h2, h3⟩ := hland p hp8
    have hsep7 : p.val + 7 ≤ d.val := by
      have hne : d.val ≠ p.val := by omega
      rcases hsep 7 d p (by omega) hne with h | h
      · omega
      · omega
    exact ⟨j, p, by omega, by omega, by omega, by omega, by omega⟩
  · have h3j : 5 ≤ j.val := hlowIdx j (by omega)
    have hsep4 : j.val + 12 ≤ j'.val := by
      have hne : j.val ≠ j'.val := by omega
      rcases hsep 4 j j' (by omega) hne with h | h
      · omega
      · omega
    have hsep5 : j'.val + 29 ≤ d.val := by
      have hne : d.val ≠ j'.val := by omega
      rcases hsep 5 d j' (by omega) hne with h | h
      · omega
      · omega
    exact ⟨j, j', by omega, by omega, by omega, by omega, by omega⟩

/-- **`wb` from the landmark and the deep chain.** `leg4Land_wb_of_land_of_deepFirst` with the
descent before each ascent replaced by the three landmarks that descent was used to produce, so the
chain may come from anywhere. -/
theorem leg4Land_wb_of_land_of_deepChain {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (hm : 0 < m)
    (hsep : ArmSep f) (h0 : f ⟨0, hm⟩ = L + 5) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9)
    (hlow : LowAt f (L + 1) (L + 8))
    (hland : ∀ q : Fin m, L + 8 ≤ f q → ∃ j : Fin m, 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧
      f j ≤ L + 4)
    (hdeep : ∀ e : Fin m, L + 9 ≤ f e → ∃ j k l : Fin m, 3 ≤ j.val ∧ j.val + 4 ≤ k.val ∧
      k.val + 6 ≤ l.val ∧ l.val + 7 ≤ e.val ∧ f j ≤ L + 4 ∧ L + 6 ≤ f k ∧ f l ≤ L + 2) :
    Leg4Land (armRefl (L + (L + 9)) f) (L + 9) (L + 6) (L + 2) (L + 4) := by
  have hchain := wb_chain_of_land hm hsep h0 hlow hland
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hd8 : L + 8 ≤ f d := by omega
    obtain ⟨j, h1, h2, h3⟩ := hland d hd8
    have := hH d
    exact ⟨j, by omega, by omega, by omega⟩
  · intro e he
    simp only [armRefl_apply] at he ⊢
    have he9 : L + 9 ≤ f e := by omega
    obtain ⟨j, k, l, h1, h2, h3, h4, h5, h6, h7⟩ := hdeep e he9
    have := hH e
    exact ⟨j, k, l, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hdl : f d ≤ L + 1 := by omega
    have hdL : L ≤ f d := hL d
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hchain d hdl
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

section Assemble

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-- **`w3` on the forward arm from its ceiling chain.** The floor clause is the landmark, the deep
clause is vacuous inside the band, and the ceiling clause is the hypothesis. -/
theorem leg4Land_w3_armG_of_ceilChain (i : Fin n) (L : ℤ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hlandG : ∀ q : Fin (n - i.val), L + 8 ≤ armG ρ i q →
      ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4)
    (hceil : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ j k : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
        armG ρ i j ≤ L + 4 ∧ L + 7 ≤ armG ρ i k) :
    Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hd8 : L + 8 ≤ armG ρ i d := by omega
    have hd9 : armG ρ i d ≤ L + 9 := hHb ⟨i.val + d.val, by have := d.isLt; omega⟩
    obtain ⟨j, h1, h2, h3⟩ := hlandG d hd8
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
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hceil d hdl
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **`w3` on the backward arm from its ceiling chain.** -/
theorem leg4Land_w3_armT_of_ceilChain (i : Fin n) (L : ℤ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hlandT : ∀ q : Fin (i.val + 1), L + 8 ≤ armT ρ i q →
      ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4)
    (hceil : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ j k : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
        armT ρ i j ≤ L + 4 ∧ L + 7 ≤ armT ρ i k) :
    Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hd8 : L + 8 ≤ armT ρ i d := by omega
    have hd9 : armT ρ i d ≤ L + 9 := hHb ⟨i.val - d.val, by have := d.isLt; omega⟩
    obtain ⟨j, h1, h2, h3⟩ := hlandT d hd8
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
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ := hceil d hdl
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **A high-first arm has `w3`'s ceiling chain.** The time at `L + 8` the arm has before the
descent is the chain's second link, and the landmark before that time is its first; seven levels
cost seven steps, which is the gap the clause asks for. -/
theorem ceilChain_of_highFirst_armG (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hlandG : ∀ q : Fin (n - i.val), L + 8 ≤ armG ρ i q →
      ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4)
    (hA : HighFirst (armG ρ i) L) :
    ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ j k : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
        armG ρ i j ≤ L + 4 ∧ L + 7 ≤ armG ρ i k := by
  intro d hd
  have hi := i.isLt
  have hdn := d.isLt
  obtain ⟨p, hpd, hp8⟩ := hA d hd
  have hpn := p.isLt
  obtain ⟨j, hj3, hj12, hjlow⟩ := hlandG p hp8
  have hsep : p.val + 7 ≤ d.val := by
    have hz : z 7 = 170 := by decide
    have hne : (⟨i.val + d.val, by omega⟩ : Fin n).val ≠
        (⟨i.val + p.val, by omega⟩ : Fin n).val := by
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
  exact ⟨j, p, hj3, by omega, by omega, hjlow, by omega⟩

/-- **The same on the backward arm.** -/
theorem ceilChain_of_highFirst_armT (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hlandT : ∀ q : Fin (i.val + 1), L + 8 ≤ armT ρ i q →
      ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4)
    (hA : HighFirst (armT ρ i) L) :
    ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ j k : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
        armT ρ i j ≤ L + 4 ∧ L + 7 ≤ armT ρ i k := by
  intro d hd
  have hi := i.isLt
  have hdn := d.isLt
  obtain ⟨p, hpd, hp8⟩ := hA d hd
  have hpn := p.isLt
  obtain ⟨j, hj3, hj12, hjlow⟩ := hlandT p hp8
  have hsep : p.val + 7 ≤ d.val := by
    have hz : z 7 = 170 := by decide
    have hne : (⟨i.val - d.val, by omega⟩ : Fin n).val ≠
        (⟨i.val - p.val, by omega⟩ : Fin n).val := by
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
  exact ⟨j, p, hj3, by omega, by omega, hjlow, by omega⟩

/-! ## One walk for both arms, at every basepoint of the branch -/

/-- **One of the two reflected walks serves both arms.** Every arm is high first or deep first
(`highFirst_or_deepFirst`). Where both are high first, both are served by `w3`; where both are deep
first, both are served by `wb`; and at a mixed basepoint the case split of
`mixed_ceilT_or_deepG_of_land` decides: either every descent of the arm that is deep first carries
`w3`'s ceiling clause, and then `w3` serves both, or one descent does not, and then every ascent of
the other arm carries `wb`'s deep clause, and `wb` serves both. Nothing is assumed about how the
branch hypothesis is met at a descent — the case distinction of batch 66 between its two disjuncts
disappears. -/
theorem w3_or_wb_of_land (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hlandGs : ∀ (q : Fin (n - i.val)) (b : Fin n), b.val = i.val + q.val → L + 8 ≤ σ b →
      ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4)
    (hlandTs : ∀ (q : Fin (i.val + 1)) (a : Fin n), a.val = i.val - q.val → L + 8 ≤ σ a →
      ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) ∨
      (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)) := by
  classical
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
  -- the level form of the two landmark hypotheses
  have hlandG : ∀ q : Fin (n - i.val), L + 8 ≤ armG ρ i q →
      ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4 := by
    intro q hq
    refine hlandGs q ⟨i.val + q.val, by have := q.isLt; omega⟩ rfl ?_
    have hqv : armG ρ i q = ρ ⟨i.val + q.val, by have := q.isLt; omega⟩ := rfl
    have := hcr.le (⟨i.val + q.val, by have := q.isLt; omega⟩ : Fin n)
    omega
  have hlandT : ∀ q : Fin (i.val + 1), L + 8 ≤ armT ρ i q →
      ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4 := by
    intro q hq
    refine hlandTs q ⟨i.val - q.val, by have := q.isLt; omega⟩ rfl ?_
    have hqv : armT ρ i q = ρ ⟨i.val - q.val, by have := q.isLt; omega⟩ := rfl
    have := hcr.le (⟨i.val - q.val, by have := q.isLt; omega⟩ : Fin n)
    omega
  rcases highFirst_or_deepFirst (armG ρ i) L with hAG | hDG
  · rcases highFirst_or_deepFirst (armT ρ i) L with hAT | hDT
    · exact Or.inl
        ⟨leg4Land_w3_armG_of_ceilChain i L hLb hHb hlandG
          (ceilChain_of_highFirst_armG hcr i L hlandG hAG),
        leg4Land_w3_armT_of_ceilChain i L hLb hHb hlandT
          (ceilChain_of_highFirst_armT hcr i L hlandT hAT)⟩
    · by_cases hceil : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
          ∃ j k : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
            armT ρ i j ≤ L + 4 ∧ L + 7 ≤ armT ρ i k
      · exact Or.inl
          ⟨leg4Land_w3_armG_of_ceilChain i L hLb hHb hlandG
            (ceilChain_of_highFirst_armG hcr i L hlandG hAG),
          leg4Land_w3_armT_of_ceilChain i L hLb hHb hlandT hceil⟩
      · have hbad : ∃ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 ∧
            ¬ (∃ j k : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
              armT ρ i j ≤ L + 4 ∧ L + 7 ≤ armT ρ i k) := by
          by_contra hc
          exact hceil (fun d hd => by
            by_contra hq
            exact hc ⟨d, hd, hq⟩)
        obtain ⟨d, hd, hno⟩ := hbad
        refine Or.inr ⟨?_, ?_⟩
        · refine leg4Land_wb_of_land_of_deepChain hmG (armG_armSep hcr i) h0G (fun j => hLb _)
            (fun j => hHb _) hGlow hlandG ?_
          intro e he
          rcases mixed_ceilT_or_deepG_of_land hcr i L hp hHb hlandGs hlandTs d hd e he with hl | hr
          · exact absurd hl hno
          · exact hr
        · exact leg4Land_wb_of_land_of_deepFirst hmT (armT_armSep hcr i) h0T (fun j => hLb _)
            (fun j => hHb _) hTlow hlandT hDT
  · rcases highFirst_or_deepFirst (armT ρ i) L with hAT | hDT
    · by_cases hceil : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
          ∃ j k : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
            armG ρ i j ≤ L + 4 ∧ L + 7 ≤ armG ρ i k
      · exact Or.inl
          ⟨leg4Land_w3_armG_of_ceilChain i L hLb hHb hlandG hceil,
          leg4Land_w3_armT_of_ceilChain i L hLb hHb hlandT
            (ceilChain_of_highFirst_armT hcr i L hlandT hAT)⟩
      · have hbad : ∃ d : Fin (n - i.val), armG ρ i d ≤ L + 1 ∧
            ¬ (∃ j k : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 5 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
              armG ρ i j ≤ L + 4 ∧ L + 7 ≤ armG ρ i k) := by
          by_contra hc
          exact hceil (fun d hd => by
            by_contra hq
            exact hc ⟨d, hd, hq⟩)
        obtain ⟨d, hd, hno⟩ := hbad
        refine Or.inr ⟨?_, ?_⟩
        · exact leg4Land_wb_of_land_of_deepFirst hmG (armG_armSep hcr i) h0G (fun j => hLb _)
            (fun j => hHb _) hGlow hlandG hDG
        · refine leg4Land_wb_of_land_of_deepChain hmT (armT_armSep hcr i) h0T (fun j => hLb _)
            (fun j => hHb _) hTlow hlandT ?_
          intro e he
          rcases mixed_ceilG_or_deepT_of_land hcr i L hp hHb hlandGs hlandTs d hd e he with hl | hr
          · exact absurd hl hno
          · exact hr
    · exact Or.inr ⟨leg4Land_wb_of_land_of_deepFirst hmG (armG_armSep hcr i) h0G (fun j => hLb _)
        (fun j => hHb _) hGlow hlandG hDG,
        leg4Land_wb_of_land_of_deepFirst hmT (armT_armSep hcr i) h0T (fun j => hLb _)
        (fun j => hHb _) hTlow hlandT hDT⟩

/-- **The pair folds.** A walk serving both arms is a fold. -/
theorem s3_span_nine_mid5_of_land (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hlandGs : ∀ (q : Fin (n - i.val)) (b : Fin n), b.val = i.val + q.val → L + 8 ≤ σ b →
      ∃ j : Fin (n - i.val), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armG ρ i j ≤ L + 4)
    (hlandTs : ∀ (q : Fin (i.val + 1)) (a : Fin n), a.val = i.val - q.val → L + 8 ≤ σ a →
      ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  rcases w3_or_wb_of_land hcr i L hp hLb hHb hlandGs hlandTs hGlow hTlow with ⟨hG, hT⟩ | ⟨hG, hT⟩
  · exact s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 1) (L + 4) hlip hLb hHb hp
      (leg4Window_w3 L) (by omega) (by omega) hG hT
  · exact s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 2) (L + 4) hlip hLb hHb hp
      (leg4Window_wb L) (by omega) (by omega) hG hT

/-! ## The residue, for the relaxed clause, on the backward arm -/

/-- **One of the two reflected walks serves both arms, when the backward arm fails the relaxed
clause.** -/
theorem w3_or_wb_of_mid2failT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4)) ∨
      (Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) ∧
        Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4)) :=
  w3_or_wb_of_land hcr i L hp hLb hHb
    (fun q b hb hq => land_ascent_sig_of_mid2fail2 hcr hlip i L hp hmid q b hb hq)
    (fun q a ha hq => land_ascent_armT_sig_of_mid2fail2 hcr hlip i L hp hmid q a ha hq)
    hGlow hTlow

/-- **The pair folds.** -/
theorem s3_span_nine_mid5_of_mid2failT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_land hcr hlip i L hp hLb hHb
    (fun q b hb hq => land_ascent_sig_of_mid2fail2 hcr hlip i L hp hmid q b hb hq)
    (fun q a ha hq => land_ascent_armT_sig_of_mid2fail2 hcr hlip i L hp hmid q a ha hq)
    hGlow hTlow

/-- **Such a basepoint is not a crossing of the trichotomy.** -/
theorem not_triCross_of_mid2failT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8)) :
    ¬ TriCrossL5 ρ i L := by
  intro hcross
  rcases w3_or_wb_of_mid2failT hcr hlip i L hp hLb hHb hmid hGlow hTlow with h | h
  · exact hcross.2.1 h
  · exact hcross.2.2 h

/-- **The residue, for the relaxed clause, on the backward arm.** At a crossing of the trichotomy
in the branch at `L + 5`, the backward arm satisfies `Mid2Floor2`. This is
`crossMid2_relaxed_of_highFirst` and `crossMid2_relaxed_of_deepFirst` with their hypotheses on how
the branch hypothesis is met removed: the mixed basepoint is covered too. -/
theorem crossMid2_relaxed_armT (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hGlow : LowAt (armG ρ i) (L + 1) (L + 8)) (hTlow : LowAt (armT ρ i) (L + 1) (L + 8))
    (hcross : TriCrossL5 ρ i L) :
    Mid2Floor2 (armT ρ i) L := by
  classical
  by_contra hmid
  exact not_triCross_of_mid2failT hcr hlip i L hp hLb hHb hmid hGlow hTlow hcross

end Assemble

end HPC.Fold
