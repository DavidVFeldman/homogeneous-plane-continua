import HPC.Fold.Mid2Cross66

/-!
# What the partner's failure puts on the `w8` side: the ascent clause of `w3` and `wb`

`Mid2Cross66` reads the failure of `Mid2Floor` through the pairing at the partner's *descents*, and
finds the crooked peak on the `w8` side. This file reads it at the `w8` side's own **ascents**, and
finds there the one clause `w3` and `wb` share.

## The relaxed clause

`Mid2Floor2` is `Mid2Floor` with the index bound lowered from three to two: at a descent to exactly
`L + 2` a time at `L + 6` or above at arm index **two** or more and four steps earlier. It is a
weaker demand than `Mid2Floor` (`mid2Floor2_of_mid2Floor`), so its failure is a stronger hypothesis
— and it is the hypothesis the pairing can use, because the timing law only keeps a link whose
interval reaches `L + 7` two steps from the basepoint, not three. The one index of slack is
exactly the difference between the two clauses.

## The theorem

`land_ascent_of_mid2fail2`: at a basepoint of the branch whose backward arm fails `Mid2Floor2`, the
forward arm has, before **every** one of its times at `L + 8` or above, a time at `L + 4` or below
at arm index three or more and twelve steps earlier. That is exactly the floor clause of the
reflected walks `w3` and `wb` read on the forward arm (`land_w3_floor_of_mid2fail2`), the clause
those two walks share.

The proof reads crookedness between the partner's failing descent and the forward arm's high time.
It produces a peak, whose interval reaches `L + 7`, and then a valley at `L + 3` or below. The peak
cannot be a time of the partner: the timing law puts it at arm index two or more (`z 2 = 3`) and
twenty-nine steps from the descent, so it would sit inside the window the failure of `Mid2Floor2`
empties. So the peak — and with it the valley, which comes after it — is a time of the forward arm,
and the valley is the landmark. Its own arm index is two or more by the same law, and where it is
exactly two the next index serves instead, because one step costs one level and `L + 3 + 1 = L + 4`
is still inside the clause. That is the repair the relaxed clause does not need on the partner's
side, where `L + 6` is asked for and a step down from `L + 6` is `L + 5`.

## What it gives

`leg4Land_w3_of_mid2fail2`: if in addition the branch hypothesis is met on the forward arm by its
first disjunct — before every descent of the forward arm to `L + 1` a time at `L + 8` — then the
forward arm is served by `w3` in full. Its deep clause is vacuous inside the band (it triggers at
`L + 10`), its floor clause is the theorem above, and its ceiling clause at the descents to `L + 1`
is that first disjunct with the theorem's landmark placed before it.

`mid2fail2_cross_w3`: hence at a **crossing** whose backward arm fails `Mid2Floor2` and whose
forward arm meets the branch hypothesis that way, the backward arm is served by `wb` and not by
`w3` — the crossing's second clause forces it, since the forward arm now has `w3`. The residue of
the branch at such a basepoint is therefore a `w3`/`wb` crossing and nothing else.
-/

namespace HPC.Fold

/-! ## The relaxed clause -/

/-- **`Mid2Floor` with the index bound lowered to two.** The timing law keeps a link whose interval
reaches `L + 7` two steps from the basepoint, so this is the form of the clause the crooked pairing
can read. -/
def Mid2Floor2 {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  ∀ d : Fin m, f d = L + 2 → ∃ j : Fin m, 2 ≤ (j.val : ℤ) ∧
    (j.val : ℤ) + 4 ≤ (d.val : ℤ) ∧ L + 6 ≤ f j

/-- `Mid2Floor` asks for more, so it implies the relaxed clause. -/
theorem mid2Floor2_of_mid2Floor {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : Mid2Floor f L) :
    Mid2Floor2 f L := by
  intro d hd
  obtain ⟨j, h1, h2, h3⟩ := h d hd
  exact ⟨j, by omega, h2, h3⟩

/-- **The descent at which the relaxed clause fails, with its window written out.** -/
theorem mid2Fail2_witness {m : ℕ} {f : Fin m → ℤ} {L : ℤ} (h : ¬ Mid2Floor2 f L) :
    ∃ d : Fin m, f d = L + 2 ∧
      ∀ j : Fin m, 2 ≤ j.val → j.val + 4 ≤ d.val → f j ≤ L + 5 := by
  classical
  unfold Mid2Floor2 at h
  push_neg at h
  obtain ⟨d, hd, hno⟩ := h
  refine ⟨d, hd, fun j h2 h4 => ?_⟩
  have := hno j (by omega) (by omega)
  omega

/-! ## The crooked pair at a high time of `L + 8` -/

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-- **The crooked pair read against a link whose interval reaches `L + 8`.** From a link at
`L + 2` or below and a later link whose interval reaches `L + 8`, crookedness produces a peak whose
interval reaches `L + 7` and, after it, a valley at `ρ a + 1` or below. The timing law spaces the
peak twenty-nine steps from the low link (`z 5 = 30`) and the valley twelve steps from the peak
(`z 4 = 13`). -/
theorem crooked_peak_valley_high8 (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha : ρ a ≤ L + 2) (hb : L + 8 ≤ σ b) :
    ∃ r r' : Fin n, a.val + 29 ≤ r.val ∧ r.val + 12 ≤ r'.val ∧ r'.val < b.val ∧
      L + 6 ≤ ρ r ∧ L + 7 ≤ σ r ∧ ρ r' ≤ ρ a + 1 ∧ ρ a + 1 ≤ σ r' := by
  set k : ℤ := max (ρ b) (L + 8) with hkdef
  have hbk : ρ b ≤ k := le_max_left _ _
  have hkb : k ≤ σ b := by
    rcases le_or_gt (ρ b) (L + 8) with h | h
    · simp only [hkdef, max_eq_right h]; exact hb
    · simp only [hkdef, max_eq_left (by omega : L + 8 ≤ ρ b)]; exact hcr.le b
  have hk8 : L + 8 ≤ k := le_max_right _ _
  obtain ⟨r, r', har, hrr', hr'b, hcase, -⟩ :=
    hcr.crooked a b (Fin.lt_def.mpr hab) (ρ a) k
      ⟨a, by simp, le_rfl, hcr.le a⟩ ⟨b, by simp, hbk, hkb⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  have hwr := hcr.width r
  have harv : a.val < r.val := har
  have hrr'v : r.val < r'.val := hrr'
  have hr'bv : r'.val < b.val := hr'b
  have h1 : a.val + 29 ≤ r.val := by
    have hz : z 5 = 30 := by decide
    rcases ivSep hcr a r (by omega) 5 (ρ a) (k - 1) (by push_cast; omega)
      le_rfl (hcr.le a) hr1 hr2 with h | h
    · omega
    · omega
  have h2 : r.val + 12 ≤ r'.val := by
    have hz : z 4 = 13 := by decide
    rcases ivSep hcr r' r (by omega) 4 (ρ a + 1) (k - 1) (by push_cast; omega)
      hr'1 hr'2 hr1 hr2 with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, hr'bv, by omega, by omega, hr'1, hr'2⟩

/-! ## The ascent clause on the `w8` side -/

/-- **A partner that fails the relaxed clause gives the forward arm a low landmark before every one
of its high times.** At every time of the forward arm at `L + 8` or above there is an earlier time
of that arm at `L + 4` or below, at arm index three or more and twelve steps earlier. -/
theorem land_ascent_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (e : Fin (n - i.val)) (he : L + 8 ≤ armG ρ i e) :
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
  set b : Fin n := ⟨i.val + e.val, by omega⟩ with hbdef
  have hav : ρ a = armT ρ i dT := rfl
  have hbv : ρ b = armG ρ i e := rfl
  have hab : a.val < b.val := by simp only [hadef, hbdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr6, hr7, hr'1, hr'2⟩ :=
    crooked_peak_valley_high8 hcr a b hab L (by omega) (by have := hcr.le b; omega)
  have havl : a.val = i.val - dT.val := rfl
  have hbvl : b.val = i.val + e.val := rfl
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
    -- two levels above the basepoint costs two steps
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
  -- the valley is a time of the forward arm
  set R : ℕ := r'.val - i.val with hRdef
  have hRlt : R < e.val := by omega
  have hRv : armG ρ i ⟨R, by omega⟩ = ρ r' := by
    show ρ ⟨i.val + R, _⟩ = ρ r'
    congr 1
    exact Fin.ext (by show i.val + R = r'.val; omega)
  have hlow : ρ r' ≤ L + 3 := by omega
  -- and at arm index two or more, by the same law
  have hR2 : 2 ≤ R := by
    have hne : r'.val ≠ i.val := by omega
    have hz : z 2 = 3 := by decide
    rcases ivSep hcr r' i hne 2 (ρ a + 1) (L + 5) (by push_cast; omega)
      hr'1 hr'2 (le_of_eq hp) (by have := hcr.le i; omega) with h | h
    · omega
    · omega
  -- the gap to the high time is twenty-nine steps, by the law at five levels
  have hgap : R + 29 ≤ e.val := by
    have hne : r'.val ≠ b.val := by omega
    have hz : z 5 = 30 := by decide
    set w : ℤ := max (ρ b) (L + 8) with hwdef
    have hbw : ρ b ≤ w := le_max_left _ _
    have hwb : w ≤ σ b := by
      rcases le_or_gt (ρ b) (L + 8) with h | h
      · simp only [hwdef, max_eq_right h]; exact by have := hcr.le b; omega
      · simp only [hwdef, max_eq_left (by omega : L + 8 ≤ ρ b)]; exact hcr.le b
    have hw8 : L + 8 ≤ w := le_max_right _ _
    rcases ivSep hcr r' b hne 5 (ρ a + 1) w (by push_cast; omega)
      hr'1 hr'2 hbw hwb with h | h
    · omega
    · omega
  rcases Nat.lt_or_ge R 3 with hR3 | hR3
  · -- the valley sits at arm index two; the next index is still inside the clause
    have h3lt : 3 < n - i.val := by omega
    refine ⟨⟨3, h3lt⟩, le_rfl, by simp; omega, ?_⟩
    have hR2' : R = 2 := by omega
    have hstep : |armG ρ i ⟨3, h3lt⟩ - armG ρ i ⟨R, by omega⟩| ≤ 1 :=
      armG_isLip hlip i ⟨R, by omega⟩ ⟨3, h3lt⟩ (by simp; omega)
    rw [hRv] at hstep
    have := abs_le.mp hstep
    omega
  · exact ⟨⟨R, by omega⟩, hR3, by simp; omega, by rw [hRv]; omega⟩

/-- **The floor clause of the reflected walks, on the `w8` side.** `w3` and `wb` ask, at every time
of the forward arm at `L + 8` or above, for an earlier time at `L + 4` or below at arm index three
or more; the theorem above supplies it, and the timing law makes the index gap free. -/
theorem land_w3_floor_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L) :
    ∀ d : Fin (n - i.val), armRefl (L + (L + 9)) (armG ρ i) d ≤ (L + 4) - 3 →
      ∃ j : Fin (n - i.val), (L + 6) - (L + 4) + 1 ≤ (j.val : ℤ) ∧
        (j.val : ℤ) + ((L + 6) - 1 - armRefl (L + (L + 9)) (armG ρ i) d) ≤ (d.val : ℤ) ∧
        (L + 6) - 1 ≤ armRefl (L + (L + 9)) (armG ρ i) j := by
  intro d hd
  simp only [armRefl_apply] at hd ⊢
  have hd8 : L + 8 ≤ armG ρ i d := by omega
  have hd9 : armG ρ i d ≤ L + 9 := hHb ⟨i.val + d.val, by have := d.isLt; have := i.isLt; omega⟩
  obtain ⟨j, h1, h2, h3⟩ := land_ascent_of_mid2fail2 hcr hlip i L hp hmid d hd8
  exact ⟨j, by omega, by omega, by omega⟩

/-! ## `w3` in full on the `w8` side -/

/-- **The `w8` side is served by `w3`.** At a basepoint of the branch whose backward arm fails the
relaxed clause, and whose forward arm meets the branch hypothesis by its first disjunct — a time at
`L + 8` before every descent to `L + 1` — the forward arm satisfies the landmark sentence of
`w3 = L+6 → L+3 → L+8 → L+1 → L+8`. The deep clause of `w3` is vacuous inside the band. -/
theorem leg4Land_w3_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (hA : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ p : Fin (n - i.val), p.val < d.val ∧ L + 8 ≤ armG ρ i p) :
    Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) := by
  have hi := i.isLt
  refine ⟨land_w3_floor_of_mid2fail2 hcr hlip i L hp hHb hmid, ?_, ?_⟩
  · -- the deep clause triggers at `L + 10`, outside the band
    intro d hd
    simp only [armRefl_apply] at hd
    have := hHb ⟨i.val + d.val, by have := d.isLt; omega⟩
    have he : armG ρ i d = ρ ⟨i.val + d.val, by have := d.isLt; omega⟩ := rfl
    omega
  · -- the ceiling clause at the descents to `L + 1`
    intro d hd
    simp only [armRefl_apply] at hd ⊢
    have hdl : armG ρ i d ≤ L + 1 := by omega
    have hdL : L ≤ armG ρ i d := hLb ⟨i.val + d.val, by have := d.isLt; have := i.isLt; omega⟩
    obtain ⟨p, hpd, hp8⟩ := hA d hdl
    obtain ⟨j, hj3, hj12, hjlow⟩ := land_ascent_of_mid2fail2 hcr hlip i L hp hmid p hp8
    -- seven levels cost seven steps or more
    have hsep : (p.val : ℤ) + 7 ≤ (d.val : ℤ) := by
      have hz : z 7 = 170 := by decide
      have hpn := p.isLt
      have hdn := d.isLt
      have hne : (⟨i.val + d.val, by omega⟩ : Fin n).val ≠ (⟨i.val + p.val, by omega⟩ : Fin n).val := by
        simp; omega
      have hdv : armG ρ i d = ρ ⟨i.val + d.val, by omega⟩ := rfl
      have hpv : armG ρ i p = ρ ⟨i.val + p.val, by omega⟩ := rfl
      rcases ivSep hcr ⟨i.val + d.val, by omega⟩ ⟨i.val + p.val, by omega⟩ hne 7
        (armG ρ i d) (armG ρ i p) (by push_cast; omega) (le_of_eq hdv)
        (by rw [hdv] at *; exact hcr.le _) (le_of_eq hpv)
        (by rw [hpv] at *; exact hcr.le _) with h | h
      · simp at h; omega
      · simp at h; omega
    exact ⟨j, p, by omega, by omega, by omega, by omega, by omega⟩

/-- **At a crossing the backward arm is then a `wb` arm.** If the forward arm is served by `w3` and
the basepoint is a crossing of the trichotomy, the backward arm is not served by `w3`; by
`mid2Fail_w3_or_wb` it is served by `wb`. -/
theorem mid2fail2_cross_w3 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hT : LowAt (armT ρ i) (L + 1) (L + 8))
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (hA : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ p : Fin (n - i.val), p.val < d.val ∧ L + 8 ≤ armG ρ i p)
    (hcross : TriCrossL5 ρ i L) :
    Leg4Land (armRefl (L + (L + 9)) (armG ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) ∧
      Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 2) (L + 4) := by
  have hG3 := leg4Land_w3_of_mid2fail2 hcr hlip i L hp hLb hHb hmid hA
  have hmid' : ¬ Mid2Floor (armT ρ i) L := fun h => hmid (mid2Floor2_of_mid2Floor h)
  rcases mid2Fail_w3_or_wb i L hlip hLb hHb hp hT hmid' with h3 | hb
  · exact absurd ⟨hG3, h3⟩ hcross.2.1
  · exact ⟨hG3, hb⟩

end Pair

end HPC.Fold
