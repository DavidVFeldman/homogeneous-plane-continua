import HPC.Fold.CrossPair62

/-!
# The two-index slack is closed

Question 3 of batch 63 asks whether the last index question of the crossing — the two-index slack
of `cross_peak_valley_armG` — is settled by the timing law from the basepoint, or has to be
handled by reading the clause from the offending peak.

`cross_peak_valley_armG` (batch 62) needs the partner arm to have no time at `L + 7` or above at
arm index **two** or more before its descent; what a crossing gives, through
`crossBad_of_floor_fail`, is the same from arm index **four**. The gap is a partner peak at
`L + 7` or above at arm index `2` or `3`, and the census of batch 62 found it at 83 of the 461
crossings, so the arms do reach `L + 7` that early: the two-level law is no obstruction, since
`z 2 - 1 = 2` allows exactly that.

The answer is that the slack is closed all the same, by the **three**-level law, and the reason is
that the crooked peak is not merely a time at `L + 7`: its *interval* reaches `L + 8`, one level
higher than its own point value, because the peak of `IsCrookedIvF` is produced at the level
`ρ b - 1 ≥ L + 8` of the high end. Three levels above the basepoint costs `z 3 - 1 = 5` steps
(`base_high_sep`), so the crooked peak lies at arm index five or more on whichever side of the
basepoint it falls — never at index two, three or four.

Hence:

* `cross_peak_valley_armG'` — the batch-62 reading of the pairing with its hypothesis weakened to
  arm index four, which is what the crossing supplies, and its conclusion strengthened from
  `2 ≤ R` to `5 ≤ R`;
* `leg4Land_w72_ceil_of_cross'` and `leg4Land_w72_of_cross_of_floor1'` — the two consequences with
  the same weakening;
* `leg4Land_w72_of_cross_of_floor_fail` — the same with the hypothesis written as what a crossing
  literally is: at every ascent of the `w8` side to `L + 9` the partner arm has a descent to
  `L + 2` at which the floor clause of `w8` fails.

The batch-62 statements are unchanged and remain true; these are the versions whose hypotheses a
crossing supplies.
-/

namespace HPC.Fold

/-! ## The crooked peak, with the level its interval reaches -/

/-- **The crooked pair, with the peak's interval.** This is `cross_peak_valley_core` with the one
extra conclusion the proof already has: the peak's interval reaches `L + 8`, because crookedness
produces it at the level `ρ b - 1`. -/
theorem cross_peak_valley_core' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (a b : Fin n) (hab : a.val < b.val) (L : ℤ) (ha : ρ a ≤ L + 2) (hb : L + 9 ≤ ρ b) :
    ∃ r r' : Fin n, a.val + 70 ≤ r.val ∧ r.val + 29 ≤ r'.val ∧ r'.val + 70 ≤ b.val ∧
      L + 7 ≤ ρ r ∧ L + 8 ≤ σ r ∧ ρ r' ≤ ρ a + 1 := by
  obtain ⟨r, r', har, hrr', hr'b, hcase, -⟩ :=
    hcr.crooked a b (Fin.lt_def.mpr hab) (ρ a) (ρ b)
      ⟨a, by simp, le_rfl, hcr.le a⟩ ⟨b, by simp, le_rfl, hcr.le b⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hcase (by omega)
  have hwr := hcr.width r
  have hwr' := hcr.width r'
  have harv : a.val < r.val := har
  have hrr'v : r.val < r'.val := hrr'
  have hr'bv : r'.val < b.val := hr'b
  have h1 : a.val + 70 ≤ r.val := by
    have hz : z 6 = 71 := by decide
    rcases ivSep hcr a r (by omega) 6 (ρ a) (ρ b - 1) (by push_cast; omega)
      le_rfl (hcr.le a) hr1 hr2 with h | h
    · omega
    · omega
  have h2 : r.val + 29 ≤ r'.val := by
    have hz : z 5 = 30 := by decide
    rcases ivSep hcr r' r (by omega) 5 (ρ a + 1) (ρ b - 1) (by push_cast; omega)
      hr'1 hr'2 hr1 hr2 with h | h
    · omega
    · omega
  have h3 : r'.val + 70 ≤ b.val := by
    have hz : z 6 = 71 := by decide
    rcases ivSep hcr r' b (by omega) 6 (ρ a + 1) (ρ b) (by push_cast; omega)
      hr'1 hr'2 le_rfl (hcr.le b) with h | h
    · omega
    · omega
  exact ⟨r, r', h1, h2, h3, by omega, by omega, by omega⟩

/-- **Three levels above the basepoint costs five steps.** A link whose interval reaches `L + 8`
is at least five steps from a link at the level `L + 5`: the timing law at `z 3 = 6`. -/
theorem base_high_sep {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i r : Fin n) (L : ℤ)
    (hp : ρ i = L + 5) (hr : L + 8 ≤ σ r) :
    i.val + 5 ≤ r.val ∨ r.val + 5 ≤ i.val := by
  have hwr := hcr.width r
  have hne : i.val ≠ r.val := by
    intro hc
    have : i = r := Fin.ext hc
    subst this
    omega
  have hz : z 3 = 6 := by decide
  set b : ℤ := max (ρ r) (L + 8) with hbdef
  have hqb : ρ r ≤ b := le_max_left _ _
  have hbq : b ≤ σ r := by
    rcases le_or_gt (ρ r) (L + 8) with h | h
    · simp only [hbdef, max_eq_right h]; exact hr
    · simp only [hbdef, max_eq_left (by omega : L + 8 ≤ ρ r)]; exact hcr.le r
  have hab : (L + 5) + (3 : ℕ) ≤ b := by
    have : L + 8 ≤ b := le_max_right _ _
    push_cast
    omega
  have hip : L + 5 ≤ σ i := by have := hcr.le i; omega
  rcases ivSep hcr i r hne 3 (L + 5) b hab (by omega) hip hqb hbq with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-! ## The reading of the pairing, with the slack closed -/

/-- **The peak and the valley of the crossing pair are times of the `w8` arm, at arm index five or
more.** The hypothesis on the partner arm is now the one a crossing supplies: no time at `L + 7`
or above at arm index **four** or more before its descent. -/
theorem cross_peak_valley_armG' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hT : armT ρ i dT ≤ L + 2) (hG : L + 9 ≤ armG ρ i dG)
    (hbad : ∀ j : Fin (i.val + 1), 4 ≤ j.val → j.val + 7 ≤ dT.val → armT ρ i j ≤ L + 6) :
    ∃ R R' : Fin (n - i.val), 5 ≤ R.val ∧ R.val + 29 ≤ R'.val ∧ R'.val + 70 ≤ dG.val ∧
      L + 7 ≤ armG ρ i R ∧ armG ρ i R' ≤ armT ρ i dT + 1 := by
  have hi := i.isLt
  have hdT := dT.isLt
  have hdG := dG.isLt
  set a : Fin n := ⟨i.val - dT.val, by omega⟩ with hadef
  set b : Fin n := ⟨i.val + dG.val, by omega⟩ with hbdef
  have hav : ρ a = armT ρ i dT := rfl
  have hbv : ρ b = armG ρ i dG := rfl
  have hab : a.val < b.val := by
    have : a.val ≤ i.val := by simp only [hadef]; omega
    rcases Nat.eq_zero_or_pos dG.val with h | h
    · exfalso
      have : b = i := Fin.ext (by simp only [hbdef]; omega)
      rw [this, hp] at hbv
      omega
    · simp only [hadef, hbdef]; omega
  obtain ⟨r, r', h1, h2, h3, hrlev, hrhigh, hr'lev⟩ :=
    cross_peak_valley_core' hcr a b hab L (by omega) (by omega)
  have hrn := r.isLt
  have hr'n := r'.isLt
  have havl : a.val = i.val - dT.val := rfl
  have hbvl : b.val = i.val + dG.val := rfl
  -- the peak is five steps from the basepoint, on whichever side it falls
  have hfar := base_high_sep hcr i r L hp hrhigh
  -- and it cannot lie on the partner arm at all
  have hri : i.val < r.val := by
    by_contra hc
    push_neg at hc
    have h5 : 5 ≤ i.val - r.val := by omega
    have hj : i.val - r.val < i.val + 1 := by omega
    have hjv : armT ρ i ⟨i.val - r.val, hj⟩ = ρ r := by
      show ρ ⟨i.val - (i.val - r.val), _⟩ = ρ r
      congr 1
      exact Fin.ext (by show i.val - (i.val - r.val) = r.val; omega)
    have := hbad ⟨i.val - r.val, hj⟩ (by simpa using (by omega : 4 ≤ i.val - r.val))
      (by simp; omega)
    rw [hjv] at this
    omega
  have hr'i : i.val < r'.val := by omega
  refine ⟨⟨r.val - i.val, by omega⟩, ⟨r'.val - i.val, by omega⟩, by simp only []; omega,
    by simp; omega, by simp; omega, ?_, ?_⟩
  · show ρ ⟨i.val + (r.val - i.val), _⟩ ≥ L + 7
    rw [show (⟨i.val + (r.val - i.val), by omega⟩ : Fin n) = r from Fin.ext (by simp; omega)]
    exact hrlev
  · show ρ ⟨i.val + (r'.val - i.val), _⟩ ≤ armT ρ i dT + 1
    rw [show (⟨i.val + (r'.val - i.val), by omega⟩ : Fin n) = r' from Fin.ext (by simp; omega)]
    omega

/-! ## The consequences, with the hypothesis a crossing supplies -/

/-- **The ceiling clause of `w72` from the pairing**, with the partner hypothesis at arm index
four. -/
theorem leg4Land_w72_ceil_of_cross' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9)
    (dT : Fin (i.val + 1)) (dG : Fin (n - i.val))
    (hT : armT ρ i dT ≤ L + 2) (hG : L + 9 ≤ armG ρ i dG)
    (hbad : ∀ j : Fin (i.val + 1), 4 ≤ j.val → j.val + 7 ≤ dT.val → armT ρ i j ≤ L + 6) :
    ∃ j k : Fin (n - i.val), 3 ≤ (j.val : ℤ) ∧ (j.val : ℤ) + 5 ≤ (k.val : ℤ) ∧
      (k.val : ℤ) + (armG ρ i dG - (L + 3)) ≤ (dG.val : ℤ) ∧
      L + 6 ≤ armG ρ i j ∧ armG ρ i k ≤ L + 3 := by
  obtain ⟨R, R', hR, hRR', hR'd, hRlev, hR'lev⟩ :=
    cross_peak_valley_armG' hcr i L hp dT dG hT hG hbad
  have hd9 : armG ρ i dG ≤ L + 9 :=
    hHb ⟨i.val + dG.val, by have := dG.isLt; have := i.isLt; omega⟩
  exact ⟨R, R', by exact_mod_cast (by omega : 3 ≤ R.val), by omega, by omega, by omega, by omega⟩

/-- **The `w8` side of a crossing satisfies `w72` in full as soon as it stays at `L + 1` or
above**, with the partner hypothesis at arm index four. -/
theorem leg4Land_w72_of_cross_of_floor1' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hcross : ∀ dG : Fin (n - i.val), L + 9 ≤ armG ρ i dG →
      ∃ dT : Fin (i.val + 1), armT ρ i dT ≤ L + 2 ∧
        (∀ j : Fin (i.val + 1), 4 ≤ j.val → j.val + 7 ≤ dT.val → armT ρ i j ≤ L + 6)) :
    Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) := by
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, h1, h2, h3⟩ := leg4Land_w71_floor_of_w8 h8 d (by omega)
    exact ⟨j, by omega, by omega, by omega⟩
  · intro d hd
    have := hLb ⟨i.val + d.val, by have := d.isLt; omega⟩
    have he : armG ρ i d = ρ ⟨i.val + d.val, by have := d.isLt; omega⟩ := rfl
    omega
  · intro d hd
    obtain ⟨dT, hT, hbad⟩ := hcross d (by omega)
    obtain ⟨j, k, h1, h2, h3, h4, h5⟩ :=
      leg4Land_w72_ceil_of_cross' hcr i L hp hHb dT d hT (by omega) hbad
    exact ⟨j, k, by omega, by omega, by omega, by omega, by omega⟩

/-- **The crossing, written as what it is.** At every ascent of the `w8` side to `L + 9` the
partner arm has a descent to `L + 2` at which the floor clause of `w8` fails — that is what a
crossing of the trichotomy gives — and then the `w8` side satisfies the fifth walk
`w72 = L+4 → L+7 → L+2 → L+8 → L+1` in full.

This is `leg4Land_w72_of_cross_of_floor1` with no residue: the index side of the argument is
closed, and the hypothesis is the failure of `w8`'s own clause on the partner. -/
theorem leg4Land_w72_of_cross_of_floor_fail {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hcross : ∀ dG : Fin (n - i.val), L + 9 ≤ armG ρ i dG →
      ∃ dT : Fin (i.val + 1), armT ρ i dT ≤ L + 2 ∧
        ¬ ∃ j : Fin (i.val + 1), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armT ρ i dT) ≤ (dT.val : ℤ) ∧ L + 7 ≤ armT ρ i j) :
    Leg4Land (armG ρ i) (L + 9) (L + 7) (L + 2) (L + 5) := by
  have hi := i.isLt
  refine leg4Land_w72_of_cross_of_floor1' hcr i L hp hHb hLb h8 ?_
  intro dG hG
  obtain ⟨dT, hT, hfail⟩ := hcross dG hG
  refine ⟨dT, hT, ?_⟩
  have hLarm : ∀ j : Fin (i.val + 1), L ≤ armT ρ i j := by
    intro j
    have := hLb ⟨i.val - j.val, by have := j.isLt; omega⟩
    have he : armT ρ i j = ρ ⟨i.val - j.val, by have := j.isLt; omega⟩ := rfl
    omega
  exact crossBad_of_floor_fail hLarm dT hT hfail


/-! ## What the branch needs, with the crossing's own hypothesis -/

/-- **The branch `L + 5` at a crossing, from the partner's fifth walk alone.** At a basepoint of
the branch whose band misses the floor `L`, if the forward arm satisfies the landmark sentence of
`w8`, if at each of its ascents to `L + 9` the partner arm has a descent to `L + 2` at which the
floor clause of `w8` fails — that is, if the basepoint is a crossing of the trichotomy with the
forward arm on the `w8` side — and if the partner arm satisfies the fifth walk, then both arms fold
onto one walk.

So the crossing's whole remaining obligation is the partner's own `w72` (which the census of batch
62 finds at 431 of the 461 crossings) and the crossings whose `w8` side touches the floor. -/
theorem s3_span_nine_mid5_of_cross_w72 {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (hlip : IsLip ρ) (i : Fin n) (L : ℤ) (hp : ρ i = L + 5)
    (hHb : ∀ t, ρ t ≤ L + 9) (hLb : ∀ t, L + 1 ≤ ρ t)
    (h8 : Leg4Land (armG ρ i) (L + 9) (L + 8) (L + 1) (L + 5))
    (hcross : ∀ dG : Fin (n - i.val), L + 9 ≤ armG ρ i dG →
      ∃ dT : Fin (i.val + 1), armT ρ i dT ≤ L + 2 ∧
        ¬ ∃ j : Fin (i.val + 1), 4 ≤ (j.val : ℤ) ∧
            (j.val : ℤ) + (L + 7 - armT ρ i dT) ≤ (dT.val : ℤ) ∧ L + 7 ≤ armT ρ i j)
    (hT72 : Leg4Land (armT ρ i) (L + 9) (L + 7) (L + 2) (L + 5)) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c :=
  s3_span_nine_mid5_of_leg4Land_direct ρ i L (L + 7) (L + 2) (L + 5) hlip
    (fun t => by have := hLb t; omega) hHb hp (leg4Window_w72 L) (by omega) (by omega)
    (leg4Land_w72_of_cross_of_floor_fail hcr i L hp hHb hLb h8 hcross) hT72

end HPC.Fold
