import HPC.Fold.Mixed

/-!
# The two work items of the branch `L + 4`, settled in the thin form of the model

`HPC/Fold/Mixed.lean` leaves the branch `L + 4` resting on two work items, `unserved_ceiling`
and `unserved_valley`: a pair that folds onto neither canonical walk satisfies the two
hypotheses of the third walk. It also proves the two configurations those items produce to be
impossible on a **thin** sequence — one whose interval sequence `σ` is the point sequence `ρ`
(`cross_ceiling_thin`, `cross_valley_thin`). What was missing was the bookkeeping between the
two: the passage from "the pair folds onto neither canonical walk" to those configurations.

This file supplies it, and so proves both work items, and with them the whole branch `L + 4`,
for thin sequences:

* `ceil_fail_data`, `lam_fail_data`, `vee_fail_data`, `valleyAnn_fail_data` — the four failures
  read as data about one arm: an event, and a window before it;
* `base_window_above` — near the basepoint `L + 4` the sequence stays at `L + 2` or above, three
  steps on either side: falling or rising three levels needs four steps;
* `cross_ceiling_thin'`, `cross_valley_thin'` — the two configurations with the arms exchanged,
  which is a separate statement because the crookedness clause is not symmetric in time;
* `unserved_ceiling_thin`, `unserved_valley_thin` — the two work items, on a thin sequence;
* `s3_span_nine_mid4_thin` — the branch `L + 4` for a thin sequence. Neither `HighAt` hypothesis
  of the commissioned branch statement is needed, nor either end of the band: what the proof
  uses is only that the basepoint stands at `L + 4` in a band of width nine.

**What the thin hypothesis buys.** In the general model the crookedness clause applied between a
time at `L + 1` and a time at `L + 8` returns a *link* meeting the level `L + 7`, that is a time
with `ρ = L + 6` and `σ = L + 7`; on a thin sequence that time stands at `L + 7`, and it is that
one level which contradicts the window of the other arm. The general model is untouched: the two
work items of `Mixed.lean` remain open there.
-/

namespace HPC.Fold

/-! ## Near the basepoint -/

/-- **Three steps either side of the basepoint the sequence is at `L + 2` or above.** A time at
`L + 1` or below is three levels below the basepoint, and a crooked sequence needs four steps to
fall or to climb three levels. -/
theorem base_window_above {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (hlip : IsLip ρ)
    (i : Fin n) (L : ℤ) (hp : ρ i = L + 4) (u : Fin n)
    (hlo : i.val < u.val + 4) (hhi : u.val < i.val + 4) : L + 2 ≤ ρ u := by
  by_contra hcon
  push_neg at hcon
  rcases lt_trichotomy u.val i.val with h | h | h
  · have := crookUp_climb3 hlip (crookUp_seq hcr) u i h (by omega)
    omega
  · rw [show u = i from Fin.ext h, hp] at hcon
    omega
  · have := crookDown_fall3 hlip (crookDown_seq hcr) i u h (by omega)
    omega

/-! ## The four failures, read as data about one arm -/

/-- **An arm that fails the ceiling announcement.** It has a time at `L + 8` or above before
which it never drops to `L + 1` — one application of the clause would otherwise supply the
announcement's third form — and never stands at `L + 7` and afterwards at `L + 2`. -/
theorem ceil_fail_data {m : ℕ} {f : Fin m → ℤ} (hcru : CrookUp f) (L : ℤ) (h : ¬ CeilAnn f L) :
    ∃ d0 : Fin m, L + 8 ≤ f d0 ∧ (∀ k : Fin m, k.val < d0.val → L + 2 ≤ f k) ∧
      (∀ k k' : Fin m, k.val < k'.val → k'.val < d0.val → L + 7 ≤ f k → L + 2 < f k') := by
  unfold CeilAnn at h
  push_neg at h
  obtain ⟨d0, hd0, -, hB, hC⟩ := h
  refine ⟨d0, hd0, fun k hk => ?_, hB⟩
  by_contra hcon
  obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
    hcru.levels (L + 1) (L + 8) (by omega) k d0 hk (by omega) hd0
  exact absurd (hC k u u' h1 h2 h3 (by omega) (by omega)) (by omega)

/-- **An arm that does not fold onto the Λ-walk.** It has a first descent to `L + 1`, and before
that descent it stays in `[L + 2, L + 6]`. The upper end uses the timing law on the arm
(`hidx`): a time at `L + 7` is at step five or later, so the index clause of the Λ-criterion is
free and the failure is a failure of level alone. -/
theorem lam_fail_data {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hlip : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hLb : ∀ j, L ≤ f j) (hHb : ∀ j, f j ≤ L + 9)
    (hidx : ∀ j : Fin m, L + 7 ≤ f j → 5 ≤ j.val)
    (h : ¬ FoldsOnto f (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)) :
    ∃ d : Fin m, 0 < d.val ∧ f d ≤ L + 1 ∧
      (∀ j : Fin m, j.val < d.val → L + 2 ≤ f j) ∧
      (∀ j : Fin m, j.val < d.val → f j ≤ L + 6) := by
  rw [foldsOnto_lam_iff_profile hm f hlip (L + 3) (L + 9) L (by omega)
      (by rw [h0, abs_le]; omega) hLb hHb, critLamProfile_iff_of_isLip hlip,
    show κ (L + 3) (L + 9) = L + 8 from by simp only [κ]; omega] at h
  push_neg at h
  obtain ⟨d0, hd0raw, hd0'⟩ := h
  have hd0 : f d0 ≤ L + 1 := by omega
  obtain ⟨d, hd, hmin⟩ := exists_least_index (fun j => f j ≤ L + 1) ⟨d0, hd0⟩
  have hdd0 : d.val ≤ d0.val := by
    by_contra hc
    exact hmin d0 (by omega) hd0
  refine ⟨d, ?_, hd, fun j hj => ?_, fun j hj => ?_⟩
  · rcases Nat.eq_zero_or_pos d.val with hz | hpz
    · rw [show d = ⟨0, hm⟩ from Fin.ext hz, h0] at hd
      omega
    · exact hpz
  · have := hmin j hj
    omega
  · by_contra hc
    have h7 : L + 7 ≤ f j := by omega
    have h5 : L + 8 - (L + 3) ≤ (j.val : ℤ) := by
      have := hidx j h7
      have : (5 : ℤ) ≤ (j.val : ℤ) := by exact_mod_cast this
      omega
    have := hd0' j (by omega) h5
    omega

/-- **An arm that does not fold onto the V-walk.** It has a time at `L + 7` or above before which
it stays at `L + 3` or above from its step four on. -/
theorem vee_fail_data {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (hlip : IsLip f) (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4) (hLb : ∀ j, L ≤ f j) (hHb : ∀ j, f j ≤ L + 9)
    (h : ¬ FoldsOnto f (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) :
    ∃ e : Fin m, 0 < e.val ∧ L + 7 ≤ f e ∧
      (∀ j : Fin m, j.val < e.val → 4 ≤ j.val → L + 3 ≤ f j) := by
  rw [foldsOnto_vee_iff_profile hm f hlip (L + 5) (L + 9) L (by omega)
      (by rw [h0, abs_le]; omega) hLb hHb,
    critVeeProfile_iff_of_isLip hlip (L + 5) L (by omega)] at h
  push_neg at h
  obtain ⟨e, heraw, he'⟩ := h
  have he : L + 7 ≤ f e := by omega
  refine ⟨e, ?_, he, fun j hj hj4 => ?_⟩
  · rcases Nat.eq_zero_or_pos e.val with hz | hpz
    · rw [show e = ⟨0, hm⟩ from Fin.ext hz, h0] at he
      omega
    · exact hpz
  · have h4 : L + 5 - L - 1 ≤ (j.val : ℤ) := by
      have : (4 : ℤ) ≤ (j.val : ℤ) := by exact_mod_cast hj4
      omega
    have := he' j hj h4
    omega

/-- **An arm that fails the valley announcement of the third walk.** It has a first descent to
`L + 1`, and before that descent it stays in `[L + 2, L + 5]`. -/
theorem valleyAnn_fail_data {m : ℕ} (hm : 0 < m) {f : Fin m → ℤ} (L : ℤ)
    (h0 : f ⟨0, hm⟩ = L + 4)
    (h : ¬ ∀ d : Fin m, f d ≤ L + 1 →
      (∃ k : Fin m, k.val < d.val ∧ L + 6 ≤ f k) ∨
      (∃ k k' : Fin m, k.val < k'.val ∧ k'.val < d.val ∧ f k ≤ L + 1 ∧ L + 5 ≤ f k')) :
    ∃ d : Fin m, 0 < d.val ∧ f d ≤ L + 1 ∧
      (∀ j : Fin m, j.val < d.val → L + 2 ≤ f j) ∧
      (∀ j : Fin m, j.val < d.val → f j ≤ L + 5) := by
  push_neg at h
  obtain ⟨d0, hd0, hA, -⟩ := h
  obtain ⟨d, hd, hmin⟩ := exists_least_index (fun j => f j ≤ L + 1) ⟨d0, hd0⟩
  have hdd0 : d.val ≤ d0.val := by
    by_contra hc
    exact hmin d0 (by omega) hd0
  refine ⟨d, ?_, hd, fun j hj => ?_, fun j hj => ?_⟩
  · rcases Nat.eq_zero_or_pos d.val with hz | hpz
    · rw [show d = ⟨0, hm⟩ from Fin.ext hz, h0] at hd
      omega
    · exact hpz
  · have := hmin j hj
    omega
  · have := hA j (by omega)
    omega

/-! ## The two configurations, with the arms exchanged

`cross_ceiling_thin` and `cross_valley_thin` read the low time before the basepoint and the high
time after it. The crookedness clause is not symmetric in time — between a high time and a later
low time it returns the low link first — so the exchanged configurations are separate
statements, with windows of their own. -/

/-- **The ceiling configuration with the arms exchanged.** `g` before the basepoint `c` at
`L + 8` or above; `t` after it at `L + 1` or below, with the sequence at `L + 2` or above in
between, at `L + 6` or below from the basepoint on, and with no time at `L + 2` or below followed
before the basepoint by one at `L + 7` or above. -/
theorem cross_ceiling_thin' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (hthin : ∀ u, σ u = ρ u) (L : ℤ) (g c t : Fin n)
    (hgc : g.val < c.val) (hct : c.val ≤ t.val)
    (hg : L + 8 ≤ ρ g) (ht : ρ t ≤ L + 1)
    (hmid : ∀ r : Fin n, g.val < r.val → r.val < t.val → L + 2 ≤ ρ r)
    (hGtop : ∀ r : Fin n, c.val ≤ r.val → r.val < t.val → ρ r ≤ L + 6)
    (hnopat : ∀ r r' : Fin n, g.val < r.val → r.val < r'.val → r'.val ≤ c.val →
      L + 7 ≤ ρ r' → L + 2 < ρ r) : False := by
  have hgt : g.val < t.val := by omega
  by_cases hfloor : ρ t ≤ L
  · exact no_low_gap' hcr L g t hgt (by omega) hfloor hmid
  · obtain ⟨r, r', h1, h2, h3, -, hcase⟩ :=
      hcr.crooked g t (Fin.lt_def.mpr hgt) (ρ g) (L + 1)
        ⟨g, by simp, le_rfl, by rw [hthin]⟩
        ⟨t, by simp, by omega, by rw [hthin]; omega⟩
        (by rw [abs_of_nonneg] <;> omega)
    obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
    rw [hthin] at hr2 hr'2
    have hrv : ρ r = L + 2 := by omega
    have hr'v : L + 7 ≤ ρ r' := by omega
    have h1' : g.val < r.val := h1
    have h2' : r.val < r'.val := h2
    have h3' : r'.val < t.val := h3
    rcases lt_or_ge r'.val c.val with hr'c | hr'c
    · exact absurd (hnopat r r' h1' h2' (by omega) hr'v) (by omega)
    · exact absurd (hGtop r' hr'c h3') (by omega)

/-- **The valley configuration with the arms exchanged.** `e` before the basepoint `c` at `L + 7`
or above; `s` after it at `L + 1` or below, with the sequence at `L + 2` or above in between, at
`L + 5` or below from the basepoint on, and at `L + 3` or above up to four steps before the
basepoint. The clause puts a time at `L + 2` and, after it, one at `L + 6`: after the basepoint
the second is too high, and before it the two are four levels apart, hence four steps apart, so
the first of them is early enough to meet the last window. -/
theorem cross_valley_thin' {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ)
    (hthin : ∀ u, σ u = ρ u) (hlip : IsLip ρ) (L : ℤ) (e c s : Fin n)
    (hec : e.val < c.val) (hcs : c.val ≤ s.val)
    (he : L + 7 ≤ ρ e) (hs : ρ s ≤ L + 1)
    (hmid : ∀ r : Fin n, e.val < r.val → r.val < s.val → L + 2 ≤ ρ r)
    (hGtop : ∀ r : Fin n, c.val ≤ r.val → r.val < s.val → ρ r ≤ L + 5)
    (hTno : ∀ r : Fin n, e.val < r.val → r.val + 4 ≤ c.val → L + 3 ≤ ρ r) : False := by
  have hes : e.val < s.val := by omega
  by_cases hfloor : ρ s ≤ L
  · exact no_low_gap' hcr L e s hes (by omega) hfloor hmid
  · obtain ⟨r, r', h1, h2, h3, -, hcase⟩ :=
      hcr.crooked e s (Fin.lt_def.mpr hes) (ρ e) (L + 1)
        ⟨e, by simp, le_rfl, by rw [hthin]⟩
        ⟨s, by simp, by omega, by rw [hthin]; omega⟩
        (by rw [abs_of_nonneg] <;> omega)
    obtain ⟨⟨hr1, hr2⟩, hr'1, hr'2⟩ := hcase (by omega)
    rw [hthin] at hr2 hr'2
    have hrv : ρ r = L + 2 := by omega
    have hr'v : L + 6 ≤ ρ r' := by omega
    have h1' : e.val < r.val := h1
    have h2' : r.val < r'.val := h2
    have h3' : r'.val < s.val := h3
    rcases lt_or_ge r'.val c.val with hr'c | hr'c
    · have hstep := abs_sub_le_of_isLip hlip (r'.val - r.val) r r' (by omega)
      rw [abs_le] at hstep
      have hcast : ((r'.val - r.val : ℕ) : ℤ) = (r'.val : ℤ) - (r.val : ℤ) := by
        push_cast [Nat.cast_sub (le_of_lt h2')]; ring
      exact absurd (hTno r h1' (by omega)) (by omega)
    · exact absurd (hGtop r' hr'c h3') (by omega)

/-! ## The two work items on a thin sequence -/

/-- **The ceiling work item, on a thin sequence.** A pair of the branch `L + 4` that does not
fold onto the Λ-walk on both arms announces, on each arm, its ascents to `L + 8`.

Of the hypotheses of the commissioned `unserved_ceiling` this asks only `hnotLam`: an arm that
fails the announcement folds onto the Λ-walk by itself (`ceiling_or_lam`), so the other arm does
not, and that arm's first descent to `L + 1` meets the failing arm's ascent across the
basepoint. Neither `HighAt` hypothesis, neither end of the band, and `hnotVee` are used. -/
theorem unserved_ceiling_thin {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hthin : ∀ u, σ u = ρ u)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) :
    CeilAnn (armG ρ i) L ∧ CeilAnn (armT ρ i) L := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  constructor
  · by_contra hGfail
    have hGlam : FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L)
        (lamCenter (L + 3) (L + 9) L) := by
      rcases ceiling_or_lam hmG (armG ρ i) (armG_isLip hlip i) (crookUp_armG hcr i) L hG0
        (fun j => hLb _) (fun j => hHb _) with h | h
      · exact absurd h hGfail
      · exact h
    obtain ⟨dT, hdTpos, hdT, hdTmid, hdTtop⟩ :=
      lam_fail_data hmT (armT_isLip hlip i) L hT0 (fun j => hLb _) (fun j => hHb _)
        (fun j hj => armT_three_levels hcr i j (by omega)) (fun h => hnotLam ⟨hGlam, h⟩)
    obtain ⟨d0, hd0, hd0mid, hd0pat⟩ := ceil_fail_data (crookUp_armG hcr i) L hGfail
    have hdTle : dT.val ≤ i.val := by have := dT.isLt; omega
    have hd0lt : i.val + d0.val < n := by have := d0.isLt; omega
    have htv : armT ρ i dT = ρ ⟨i.val - dT.val, by omega⟩ := rfl
    have hgv : armG ρ i d0 = ρ ⟨i.val + d0.val, by omega⟩ := rfl
    refine cross_ceiling_thin hcr hthin L ⟨i.val - dT.val, by omega⟩ i ⟨i.val + d0.val, by omega⟩
      (by show i.val - dT.val < i.val; omega) (by show i.val ≤ i.val + d0.val; omega)
      (by rw [← htv]; exact hdT) (by rw [← hgv]; exact hd0) ?_ ?_ ?_
    · intro r hr1' hr2'
      have hr1 : i.val - dT.val < r.val := hr1'
      have hr2 : r.val < i.val + d0.val := hr2'
      rcases Nat.lt_or_ge i.val r.val with hri | hri
      · have := hd0mid ⟨r.val - i.val, by omega⟩ (show r.val - i.val < d0.val by omega)
        rwa [show armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r from armG_at ρ i r (by omega)] at this
      · have := hdTmid ⟨i.val - r.val, by omega⟩ (show i.val - r.val < dT.val by omega)
        rwa [show armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r from armT_at ρ i r hri] at this
    · intro r hr1' hr2'
      have hr1 : i.val - dT.val < r.val := hr1'
      have hr2 : r.val < i.val := hr2'
      have := hdTtop ⟨i.val - r.val, by omega⟩ (show i.val - r.val < dT.val by omega)
      rwa [show armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r from armT_at ρ i r (by omega)] at this
    · intro r r' hr hrr' hr' h7
      have hri : i.val ≤ r.val := hr
      have hr'lt : r'.val < i.val + d0.val := hr'
      have hgr : armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r := armG_at ρ i r hri
      have hgr' : armG ρ i ⟨r'.val - i.val, by omega⟩ = ρ r' := armG_at ρ i r' (by omega)
      have := hd0pat ⟨r.val - i.val, by omega⟩ ⟨r'.val - i.val, by omega⟩
        (show r.val - i.val < r'.val - i.val by omega)
        (show r'.val - i.val < d0.val by omega) (by rw [hgr]; exact h7)
      rwa [hgr'] at this
  · by_contra hTfail
    have hTlam : FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L)
        (lamCenter (L + 3) (L + 9) L) := by
      rcases ceiling_or_lam hmT (armT ρ i) (armT_isLip hlip i) (crookUp_armT hcr i) L hT0
        (fun j => hLb _) (fun j => hHb _) with h | h
      · exact absurd h hTfail
      · exact h
    obtain ⟨dG, hdGpos, hdG, hdGmid, hdGtop⟩ :=
      lam_fail_data hmG (armG_isLip hlip i) L hG0 (fun j => hLb _) (fun j => hHb _)
        (fun j hj => armG_three_levels hcr i j (by omega)) (fun h => hnotLam ⟨h, hTlam⟩)
    obtain ⟨d0, hd0, hd0mid, hd0pat⟩ := ceil_fail_data (crookUp_armT hcr i) L hTfail
    have hd0le : d0.val ≤ i.val := by have := d0.isLt; omega
    have hd0pos : 0 < d0.val := by
      rcases Nat.eq_zero_or_pos d0.val with hz | hpz
      · rw [show d0 = ⟨0, hmT⟩ from Fin.ext hz, hT0] at hd0
        omega
      · exact hpz
    have hdGlt : i.val + dG.val < n := by have := dG.isLt; omega
    have hgv : armT ρ i d0 = ρ ⟨i.val - d0.val, by omega⟩ := rfl
    have htv : armG ρ i dG = ρ ⟨i.val + dG.val, by omega⟩ := rfl
    refine cross_ceiling_thin' hcr hthin L ⟨i.val - d0.val, by omega⟩ i ⟨i.val + dG.val, by omega⟩
      (by show i.val - d0.val < i.val; omega) (by show i.val ≤ i.val + dG.val; omega)
      (by rw [← hgv]; exact hd0) (by rw [← htv]; exact hdG) ?_ ?_ ?_
    · intro r hr1' hr2'
      have hr1 : i.val - d0.val < r.val := hr1'
      have hr2 : r.val < i.val + dG.val := hr2'
      rcases Nat.lt_or_ge i.val r.val with hri | hri
      · have := hdGmid ⟨r.val - i.val, by omega⟩ (show r.val - i.val < dG.val by omega)
        rwa [show armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r from armG_at ρ i r (by omega)] at this
      · have := hd0mid ⟨i.val - r.val, by omega⟩ (show i.val - r.val < d0.val by omega)
        rwa [show armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r from armT_at ρ i r hri] at this
    · intro r hr1' hr2'
      have hri : i.val ≤ r.val := hr1'
      have hr2 : r.val < i.val + dG.val := hr2'
      have := hdGtop ⟨r.val - i.val, by omega⟩ (show r.val - i.val < dG.val by omega)
      rwa [show armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r from armG_at ρ i r hri] at this
    · intro r r' hr hrr' hr' h7
      have hr1 : i.val - d0.val < r.val := hr
      have hr'le : r'.val ≤ i.val := hr'
      have hter : armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r := armT_at ρ i r (by omega)
      have hter' : armT ρ i ⟨i.val - r'.val, by omega⟩ = ρ r' := armT_at ρ i r' hr'le
      have := hd0pat ⟨i.val - r'.val, by omega⟩ ⟨i.val - r.val, by omega⟩
        (show i.val - r'.val < i.val - r.val by omega)
        (show i.val - r.val < d0.val by omega) (by rw [hter']; exact h7)
      rwa [hter] at this

/-- **The valley work item, on a thin sequence.** A pair of the branch `L + 4` that does not fold
onto the V-walk on both arms announces, on each arm, its descents to `L + 1`.

As with the ceiling item, only `hnotVee` of the commissioned hypotheses is used: an arm failing
the announcement folds onto the V-walk by itself (`valley_or_vee`), so the other arm does not,
and that arm's time at `L + 7` meets the failing arm's descent across the basepoint. -/
theorem unserved_valley_thin {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hthin : ∀ u, σ u = ρ u)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4)
    (hnotVee : ¬ (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L))) :
    (∀ d : Fin (n - i.val), armG ρ i d ≤ L + 1 →
      (∃ k : Fin (n - i.val), k.val < d.val ∧ L + 6 ≤ armG ρ i k) ∨
      (∃ k k' : Fin (n - i.val), k.val < k'.val ∧ k'.val < d.val ∧
        armG ρ i k ≤ L + 1 ∧ L + 5 ≤ armG ρ i k')) ∧
    (∀ d : Fin (i.val + 1), armT ρ i d ≤ L + 1 →
      (∃ k : Fin (i.val + 1), k.val < d.val ∧ L + 6 ≤ armT ρ i k) ∨
      (∃ k k' : Fin (i.val + 1), k.val < k'.val ∧ k'.val < d.val ∧
        armT ρ i k ≤ L + 1 ∧ L + 5 ≤ armT ρ i k')) := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  constructor
  · by_contra hGfail
    have hGvee : FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L)
        (veeCenter (L + 5) (L + 9) L) := by
      rcases valley_or_vee hmG (armG ρ i) (armG_isLip hlip i) (crookDown_armG hcr i) L hG0
        (fun j => hLb _) (fun j => hHb _) with h | h
      · exact absurd h hGfail
      · exact h
    obtain ⟨dG, hdGpos, hdG, hdGmid, hdGtop⟩ := valleyAnn_fail_data hmG L hG0 hGfail
    obtain ⟨eT, heTpos, heT, heTno⟩ :=
      vee_fail_data hmT (armT_isLip hlip i) L hT0 (fun j => hLb _) (fun j => hHb _)
        (fun h => hnotVee ⟨hGvee, h⟩)
    have heTle : eT.val ≤ i.val := by have := eT.isLt; omega
    have hdGlt : i.val + dG.val < n := by have := dG.isLt; omega
    have hev : armT ρ i eT = ρ ⟨i.val - eT.val, by omega⟩ := rfl
    have hsv : armG ρ i dG = ρ ⟨i.val + dG.val, by omega⟩ := rfl
    refine cross_valley_thin' hcr hthin hlip L ⟨i.val - eT.val, by omega⟩ i
      ⟨i.val + dG.val, by omega⟩ (by show i.val - eT.val < i.val; omega)
      (by show i.val ≤ i.val + dG.val; omega)
      (by rw [← hev]; exact heT) (by rw [← hsv]; exact hdG) ?_ ?_ ?_
    · intro r hr1' hr2'
      have hr1 : i.val - eT.val < r.val := hr1'
      have hr2 : r.val < i.val + dG.val := hr2'
      rcases Nat.lt_or_ge i.val r.val with hri | hri
      · have := hdGmid ⟨r.val - i.val, by omega⟩ (show r.val - i.val < dG.val by omega)
        rwa [show armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r from armG_at ρ i r (by omega)] at this
      · rcases Nat.lt_or_ge i.val (r.val + 4) with hnear | hfar
        · exact base_window_above hcr hlip i L hp r (by omega) (by omega)
        · have := heTno ⟨i.val - r.val, by omega⟩ (show i.val - r.val < eT.val by omega)
            (show 4 ≤ i.val - r.val by omega)
          have heq := show armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r from armT_at ρ i r hri
          rw [heq] at this
          omega
    · intro r hr1' hr2'
      have hri : i.val ≤ r.val := hr1'
      have hr2 : r.val < i.val + dG.val := hr2'
      have := hdGtop ⟨r.val - i.val, by omega⟩ (show r.val - i.val < dG.val by omega)
      rwa [show armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r from armG_at ρ i r hri] at this
    · intro r hr1' hr2'
      have hr1 : i.val - eT.val < r.val := hr1'
      have hr2 : r.val + 4 ≤ i.val := hr2'
      have := heTno ⟨i.val - r.val, by omega⟩ (show i.val - r.val < eT.val by omega)
        (show 4 ≤ i.val - r.val by omega)
      rwa [show armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r from armT_at ρ i r (by omega)] at this
  · by_contra hTfail
    have hTvee : FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L)
        (veeCenter (L + 5) (L + 9) L) := by
      rcases valley_or_vee hmT (armT ρ i) (armT_isLip hlip i) (crookDown_armT hcr i) L hT0
        (fun j => hLb _) (fun j => hHb _) with h | h
      · exact absurd h hTfail
      · exact h
    obtain ⟨dT, hdTpos, hdT, hdTmid, hdTtop⟩ := valleyAnn_fail_data hmT L hT0 hTfail
    obtain ⟨eG, heGpos, heG, heGno⟩ :=
      vee_fail_data hmG (armG_isLip hlip i) L hG0 (fun j => hLb _) (fun j => hHb _)
        (fun h => hnotVee ⟨h, hTvee⟩)
    have hdTle : dT.val ≤ i.val := by have := dT.isLt; omega
    have heGlt : i.val + eG.val < n := by have := eG.isLt; omega
    have hsv : armT ρ i dT = ρ ⟨i.val - dT.val, by omega⟩ := rfl
    have hev : armG ρ i eG = ρ ⟨i.val + eG.val, by omega⟩ := rfl
    refine cross_valley_thin hcr hthin hlip L ⟨i.val - dT.val, by omega⟩ i
      ⟨i.val + eG.val, by omega⟩ (by show i.val - dT.val < i.val; omega)
      (by show i.val ≤ i.val + eG.val; omega)
      (by rw [← hsv]; exact hdT) (by rw [← hev]; exact heG) ?_ ?_ ?_
    · intro r hr1' hr2'
      have hr1 : i.val - dT.val < r.val := hr1'
      have hr2 : r.val < i.val + eG.val := hr2'
      rcases Nat.lt_or_ge i.val r.val with hri | hri
      · rcases Nat.lt_or_ge r.val (i.val + 4) with hnear | hfar
        · exact base_window_above hcr hlip i L hp r (by omega) (by omega)
        · have := heGno ⟨r.val - i.val, by omega⟩ (show r.val - i.val < eG.val by omega)
            (show 4 ≤ r.val - i.val by omega)
          have heq := show armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r from armG_at ρ i r (by omega)
          rw [heq] at this
          omega
      · have := hdTmid ⟨i.val - r.val, by omega⟩ (show i.val - r.val < dT.val by omega)
        rwa [show armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r from armT_at ρ i r hri] at this
    · intro r hr1' hr2'
      have hr1 : i.val - dT.val < r.val := hr1'
      have hr2 : r.val < i.val := hr2'
      have := hdTtop ⟨i.val - r.val, by omega⟩ (show i.val - r.val < dT.val by omega)
      rwa [show armT ρ i ⟨i.val - r.val, by omega⟩ = ρ r from armT_at ρ i r (by omega)] at this
    · intro r hr1' hr2'
      have hr1 : i.val + 4 ≤ r.val := hr1'
      have hr2 : r.val < i.val + eG.val := hr2'
      have := heGno ⟨r.val - i.val, by omega⟩ (show r.val - i.val < eG.val by omega)
        (show 4 ≤ r.val - i.val by omega)
      rwa [show armG ρ i ⟨r.val - i.val, by omega⟩ = ρ r from armG_at ρ i r (by omega)] at this

/-! ## The branch `L + 4` on a thin sequence -/

/-- **The branch `L + 4`, on a thin sequence.** Either a canonical walk folds both arms, or the
third walk `L+3 → L+6 → L+1 → L+8` does, by `s3_span_nine_mid4_of_valley` and the two work items
above. The commissioned branch statement `s3_span_nine_mid4` adds both `HighAt` hypotheses and
both ends of the band; none of them is used here. -/
theorem s3_span_nine_mid4_thin {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ) (hthin : ∀ u, σ u = ρ u)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4) :
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c := by
  by_cases hlam : FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)
  · exact ⟨_, _, hlam.1, hlam.2⟩
  · by_cases hvee : FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L)
        (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)
    · exact ⟨_, _, hvee.1, hvee.2⟩
    · obtain ⟨h8G, h8T⟩ := unserved_ceiling_thin ρ σ i L hlip hcr hthin hLb hHb hp hlam
      obtain ⟨hvG, hvT⟩ := unserved_valley_thin ρ σ i L hlip hcr hthin hLb hHb hp hvee
      exact s3_span_nine_mid4_of_valley i L hlip hLb hHb hp hvG hvT h8G h8T

end HPC.Fold
