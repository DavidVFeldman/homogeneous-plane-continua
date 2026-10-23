import HPC.Fold.Mid2Ascent66
import HPC.Fold.CoverL5Land

/-!
# The failing arm gets `w3` too, and the pair folds

`Mid2Ascent66` puts the ascent clause of the reflected walks on the **`w8` side** of a basepoint
whose partner fails the relaxed clause `Mid2Floor2`. This file shows that the *failing arm itself*
gets the same clause, and assembles the two into a fold.

## Where a failing arm can be high

If the backward arm fails `Mid2Floor2` at a descent `dT` to exactly `L + 2`, then **every** time of
that arm at `L + 8` or above lies past `dT` (`mid2fail2_high_late`). Three facts leave no room
anywhere else: a time at `L + 8` is at arm index three or more, because the arm starts at `L + 5`
and is 1-Lipschitz; a time at arm index between two and `dT - 4` is at `L + 5` or below, because
that is what the failure says; and a time at `L + 8` within three steps of a time at `L + 2` is
forbidden by the timing law, which charges seventy steps for six levels.

## The landmark, read backwards

So at a high time `q` of the failing arm the failing descent lies *before* it in the index of the
chain and *after* it along the arm. Crookedness read between them — a link whose interval reaches
`L + 8` and, later in the chain, a link at `L + 2` — produces first a valley at `L + 3` or below
and then a peak (`crooked_valley_peak_high8`). The valley is a time of the same arm, at arm index
between `dT` and `q`, twenty-nine steps from `q` by the timing law, and at arm index two or more;
where it is exactly two the next index serves, one level higher and still inside the clause. That
is the floor clause of `w3` and of `wb`, on the failing arm (`land_w3_floor_armT_of_mid2fail2`).

## The fold

With the branch hypothesis met on both arms by its **first** disjunct — a time at `L + 8` before
every descent to `L + 1`, which is what `LowAt` offers first — both arms are then served by `w3` in
full (`leg4Land_w3_armT_of_mid2fail2` and, from the previous file,
`leg4Land_w3_of_mid2fail2`), and a walk serving both arms is a fold
(`s3_span_nine_mid5_of_leg4Land_refl`). Hence:

* `s3_span_nine_mid5_of_mid2fail2` — at such a basepoint the pair folds;
* `not_triCross_of_mid2fail2` — such a basepoint is not a crossing of the trichotomy;
* `mid2Floor2_of_cross_highFirst` — equivalently, at a crossing whose two arms both meet the branch
  hypothesis by its first disjunct, the partner satisfies `Mid2Floor2`.

The last is the residue `CrossMid2L5'` proved, for the relaxed clause, on the basepoints where the
branch hypothesis is met the first way. What is left of the residue is the second disjunct of
`LowAt`: a descent to `L + 1` whose only warrant is a time at `L + 2` followed by one at `L + 6`,
which is one level short of the `L + 7` that `w3`'s ceiling clause asks for.
-/

namespace HPC.Fold

section Pair

variable {n : ℕ} {ρ σ : Fin n → ℤ}

/-! ## The crooked pair read from the high link -/

/-- **`crooked_peak_valley_high8` with the two ends exchanged.** From a link whose interval reaches
`L + 8` and a *later* link at `L + 2` or below, crookedness produces first a valley at `ρ b + 1` or
below and then a peak whose interval reaches `L + 7`. -/
theorem crooked_valley_peak_high8 (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha : L + 8 ≤ σ a) (hb : ρ b ≤ L + 2) :
    ∃ r r' : Fin n, a.val + 29 ≤ r.val ∧ r.val + 12 ≤ r'.val ∧ r'.val < b.val ∧
      ρ r ≤ ρ b + 1 ∧ ρ b + 1 ≤ σ r ∧ L + 6 ≤ ρ r' ∧ L + 7 ≤ σ r' := by
  set h : ℤ := max (ρ a) (L + 8) with hhdef
  have hah : ρ a ≤ h := le_max_left _ _
  have hha : h ≤ σ a := by
    rcases le_or_gt (ρ a) (L + 8) with hc | hc
    · simp only [hhdef, max_eq_right hc]; exact ha
    · simp only [hhdef, max_eq_left (by omega : L + 8 ≤ ρ a)]; exact hcr.le a
  have hh8 : L + 8 ≤ h := le_max_right _ _
  obtain ⟨r, r', har, hrr', hr'b, -, hcase⟩ :=
    hcr.crooked a b (Fin.lt_def.mpr hab) h (ρ b)
      ⟨a, by simp, hah, hha⟩ ⟨b, by simp, le_rfl, hcr.le b⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  have hwr' := hcr.width r'
  have harv : a.val < r.val := har
  have hrr'v : r.val < r'.val := hrr'
  have hr'bv : r'.val < b.val := hr'b
  have h1 : a.val + 29 ≤ r.val := by
    have hz : z 5 = 30 := by decide
    rcases ivSep hcr r a (by omega) 5 (ρ b + 1) h (by push_cast; omega)
      hr1 hr2 hah hha with hc | hc
    · omega
    · omega
  have h2 : r.val + 12 ≤ r'.val := by
    have hz : z 4 = 13 := by decide
    rcases ivSep hcr r r' (by omega) 4 (ρ b + 1) (h - 1) (by push_cast; omega)
      hr1 hr2 hr'1 hr'2 with hc | hc
    · omega
    · omega
  exact ⟨r, r', h1, h2, hr'bv, hr1, hr2, by omega, by omega⟩

/-! ## Where a failing arm can be high -/

/-- **A failing arm is never high before its failing descent.** If the backward arm fails
`Mid2Floor2` at the descent `dT`, every time of that arm at `L + 8` or above is past `dT`. -/
theorem mid2fail2_high_late (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (dT : Fin (i.val + 1)) (hdT : armT ρ i dT = L + 2)
    (hwin : ∀ j : Fin (i.val + 1), 2 ≤ j.val → j.val + 4 ≤ dT.val → armT ρ i j ≤ L + 5)
    (q : Fin (i.val + 1)) (hq : L + 8 ≤ armT ρ i q) :
    dT.val < q.val := by
  have hi := i.isLt
  have hqn := q.isLt
  have hdTn := dT.isLt
  have hm : 0 < i.val + 1 := by omega
  have h0 : armT ρ i ⟨0, hm⟩ = L + 5 := by
    show ρ ⟨i.val - 0, _⟩ = L + 5
    rw [show (⟨i.val - 0, by omega⟩ : Fin n) = i from Fin.ext (by simp)]
    exact hp
  -- a time at `L + 8` is at arm index three or more
  have hq3 : 3 ≤ q.val := by
    have := isLip_index_gap (armT_isLip hlip i) (j := ⟨0, hm⟩) (k := q) (Nat.zero_le _)
      (armT ρ i q - armT ρ i ⟨0, hm⟩) (by omega)
    simp only [Nat.cast_zero, zero_add] at this
    omega
  rcases Nat.lt_or_ge dT.val q.val with hlt | hge
  · exact hlt
  exfalso
  rcases Nat.lt_or_ge (q.val + 4) (dT.val + 1) with hfar | hnear
  · -- inside the window the failure empties
    have := hwin q (by omega) (by omega)
    omega
  · -- six levels cost seventy steps
    have hqne : q.val ≠ dT.val := by
      intro hc
      have : q = dT := Fin.ext hc
      rw [this, hdT] at hq
      omega
    have hne : (⟨i.val - dT.val, by omega⟩ : Fin n).val ≠ (⟨i.val - q.val, by omega⟩ : Fin n).val := by
      simp only []
      omega
    have hqv : armT ρ i q = ρ ⟨i.val - q.val, by omega⟩ := rfl
    have hdv : armT ρ i dT = ρ ⟨i.val - dT.val, by omega⟩ := rfl
    have hz : z 6 = 71 := by decide
    rcases ivSep hcr ⟨i.val - dT.val, by omega⟩ ⟨i.val - q.val, by omega⟩ hne 6
      (armT ρ i dT) (armT ρ i q) (by push_cast; omega) (le_of_eq hdv)
      (by rw [hdv]; exact hcr.le _) (le_of_eq hqv) (by rw [hqv]; exact hcr.le _) with hc | hc
    · simp only [] at hc; omega
    · simp only [] at hc; omega

/-! ## The floor clause on the failing arm -/

/-- **The failing arm has a low landmark before each of its own high times.** At every time of the
backward arm at `L + 8` or above there is an earlier time of that arm at `L + 4` or below, at arm
index three or more and twelve steps earlier. -/
theorem land_ascent_armT_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (q : Fin (i.val + 1)) (hq : L + 8 ≤ armT ρ i q) :
    ∃ j : Fin (i.val + 1), 3 ≤ j.val ∧ j.val + 12 ≤ q.val ∧ armT ρ i j ≤ L + 4 := by
  have hi := i.isLt
  have hqn := q.isLt
  obtain ⟨dT, hdT, hwin⟩ := mid2Fail2_witness hmid
  have hdTn := dT.isLt
  have hlate := mid2fail2_high_late hcr hlip i L hp dT hdT hwin q hq
  set a : Fin n := ⟨i.val - q.val, by omega⟩ with hadef
  set b : Fin n := ⟨i.val - dT.val, by omega⟩ with hbdef
  have hav : ρ a = armT ρ i q := rfl
  have hbv : ρ b = armT ρ i dT := rfl
  have hab : a.val < b.val := by simp only [hadef, hbdef]; omega
  obtain ⟨r, r', h1, h2, h3, hr1, hr2, -, -⟩ :=
    crooked_valley_peak_high8 hcr a b hab L (by have := hcr.le a; omega) (by omega)
  have havl : a.val = i.val - q.val := rfl
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
  -- two levels below the basepoint costs two steps
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

/-- **The floor clause of the reflected walks, on the failing arm.** -/
theorem land_w3_floor_armT_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L) :
    ∀ d : Fin (i.val + 1), armRefl (L + (L + 9)) (armT ρ i) d ≤ (L + 4) - 3 →
      ∃ j : Fin (i.val + 1), (L + 6) - (L + 4) + 1 ≤ (j.val : ℤ) ∧
        (j.val : ℤ) + ((L + 6) - 1 - armRefl (L + (L + 9)) (armT ρ i) d) ≤ (d.val : ℤ) ∧
        (L + 6) - 1 ≤ armRefl (L + (L + 9)) (armT ρ i) j := by
  intro d hd
  simp only [armRefl_apply] at hd ⊢
  have hi := i.isLt
  have hd8 : L + 8 ≤ armT ρ i d := by omega
  have hd9 : armT ρ i d ≤ L + 9 := hHb ⟨i.val - d.val, by omega⟩
  obtain ⟨j, h1, h2, h3⟩ := land_ascent_armT_of_mid2fail2 hcr hlip i L hp hmid d hd8
  exact ⟨j, by omega, by omega, by omega⟩

/-! ## `w3` in full on the failing arm -/

/-- **The failing arm is served by `w3`**, under the same branch-hypothesis form as the `w8`
side: a time at `L + 8` before every descent of that arm to `L + 1`. -/
theorem leg4Land_w3_armT_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (hA : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ p : Fin (i.val + 1), p.val < d.val ∧ L + 8 ≤ armT ρ i p) :
    Leg4Land (armRefl (L + (L + 9)) (armT ρ i)) (L + 9) (L + 6) (L + 1) (L + 4) := by
  have hi := i.isLt
  refine ⟨land_w3_floor_armT_of_mid2fail2 hcr hlip i L hp hHb hmid, ?_, ?_⟩
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
    obtain ⟨j, hj3, hj12, hjlow⟩ := land_ascent_armT_of_mid2fail2 hcr hlip i L hp hmid p hp8
    have hsep : (p.val : ℤ) + 7 ≤ (d.val : ℤ) := by
      have hz : z 7 = 170 := by decide
      have hne : (⟨i.val - d.val, by omega⟩ : Fin n).val ≠ (⟨i.val - p.val, by omega⟩ : Fin n).val := by
        simp
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

/-! ## The fold -/

/-- **The pair folds.** At a basepoint of the branch whose backward arm fails the relaxed clause,
and where the branch hypothesis is met on both arms by its first disjunct, both arms are served by
`w3` and the pair folds onto that walk. -/
theorem s3_span_nine_mid5_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (hAT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ p : Fin (i.val + 1), p.val < d.val ∧ L + 8 ≤ armT ρ i p)
    (hAG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ p : Fin (n - i.val), p.val < d.val ∧ L + 8 ≤ armG ρ i p) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_leg4Land_refl ρ i L (L + 6) (L + 1) (L + 4) hlip hLb hHb hp
    (leg4Window_w3 L) (by omega) (by omega)
    (leg4Land_w3_of_mid2fail2 hcr hlip i L hp hLb hHb hmid hAG)
    (leg4Land_w3_armT_of_mid2fail2 hcr hlip i L hp hLb hHb hmid hAT)

/-- **Such a basepoint is not a crossing of the trichotomy**: `w3` serves both of its arms. -/
theorem not_triCross_of_mid2fail2 (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hmid : ¬ Mid2Floor2 (armT ρ i) L)
    (hAT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ p : Fin (i.val + 1), p.val < d.val ∧ L + 8 ≤ armT ρ i p)
    (hAG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ p : Fin (n - i.val), p.val < d.val ∧ L + 8 ≤ armG ρ i p) :
    ¬ TriCrossL5 ρ i L := by
  intro hcross
  exact hcross.2.1
    ⟨leg4Land_w3_of_mid2fail2 hcr hlip i L hp hLb hHb hmid hAG,
      leg4Land_w3_armT_of_mid2fail2 hcr hlip i L hp hLb hHb hmid hAT⟩

/-- **The residue, for the relaxed clause, where the branch hypothesis is met the first way.** At a
crossing of the trichotomy both of whose arms have a time at `L + 8` before every descent to
`L + 1`, the backward arm satisfies `Mid2Floor2`. -/
theorem mid2Floor2_of_cross_highFirst (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5) (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9)
    (hAT : ∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      ∃ p : Fin (i.val + 1), p.val < d.val ∧ L + 8 ≤ armT ρ i p)
    (hAG : ∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      ∃ p : Fin (n - i.val), p.val < d.val ∧ L + 8 ≤ armG ρ i p)
    (hcross : TriCrossL5 ρ i L) :
    Mid2Floor2 (armT ρ i) L := by
  classical
  by_contra hmid
  exact not_triCross_of_mid2fail2 hcr hlip i L hp hLb hHb hmid hAT hAG hcross

end Pair

end HPC.Fold
