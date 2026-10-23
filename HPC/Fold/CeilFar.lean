import HPC.Fold.CeilCross
import HPC.Fold.ValleyFar

/-!
# The ceiling crossing, with the timing law: both residues go

`HPC/Fold/CeilCross.lean` proves the two clauses the ceiling case needs — `TopW5` on the arm
failing `Leg3Ceil` and `Valley5` on the other one — outside two configurations local to the
basepoint, `CeilPeakResidual` and `CeilHighResidual`. This file removes both, by the method of
`HPC/Fold/ValleyFar.lean`: read the crookedness clause of the faithful model between the descent
and the ascent, so that the two links it returns carry *intervals* at named levels, and pin them
with the timing law of Theorem 7 (`ivSep`).

Two bounds do all the work, and both are invisible to the one-arm clauses `CrookUp`, `CrookDown`:

* a link whose interval reaches `L + 7` is at least **five** steps from a basepoint at `L + 4`
  (three levels, `z 3 - 1 = 5`), where the Lipschitz bound gives only three — this is what the
  peak residue, which asks for `L + 6` or above two or three steps from the basepoint, cannot
  survive once the clause is read at `L + 7`;
* a link whose interval reaches `L + 8` is at least **twelve** steps from it (four levels,
  `z 4 - 1 = 12`), where `crookUp_climb3` gives four — and the high residue asks for exactly four.

`no_ceilHighResidual` records the second of these on its own: in the faithful model
`CeilHighResidual` never holds at all. The peak residue does occur (the censuses find it), but it
is no longer an obstruction: the clause read at the ascent's own level returns a peak at `L + 7`,
not merely at `L + 6`, and that peak is five steps out.

The conclusion is `cross_ceil_sentence_far`, the work item `cross_ceil_sentence`
(`HPC/Fold/CrossCeil.lean`) with no exceptions, which that file now quotes.
-/

namespace HPC.Fold

/-! ## The high residue is empty -/

/-- **`CeilHighResidual` never holds.** It asks the sequence to stand at `L + 7` or above exactly
four steps from a basepoint at `L + 4`; three levels need five steps. -/
theorem no_ceilHighResidual {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (i : Fin n) (L : ℤ)
    (hp : ρ i = L + 4) : ¬ CeilHighResidual ρ i L := by
  rintro ⟨u, hu, huv⟩
  have hne : i.val ≠ u.val := by omega
  rcases ivSep3 hcr i u hne (L + 4) (ρ u) (by omega) (by omega) (by rw [← hp]; exact hcr.le i)
    le_rfl (hcr.le u) with h | h <;> omega

/-! ## The valley half, with no residue -/

/-- **The valley clause crosses the basepoint, forward form, with no exception.** This is
`ceil_cross_peak_fwd` (`HPC/Fold/CeilCross.lean`) without its residual disjunct: the peak the
clause returns is either five steps or more before the basepoint — where it is the landmark
`Valley5` asks for — or five steps or more after it, where it is the first of the two landmarks
the failure of `Leg3Ceil` forbids. -/
theorem ceil_cross_peak_fwd_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : s.val < i.val) (hsv : ρ s ≤ L + 1)
    (ht : i.val < t.val) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, i.val + 3 ≤ j.val → j.val + 5 ≤ k.val → k.val + 6 ≤ t.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    ∃ v : Fin n, s.val + 12 ≤ v.val ∧ v.val + 4 ≤ i.val ∧ L + 6 ≤ ρ v := by
  have hst : s < t := Fin.lt_def.mpr (by omega)
  obtain ⟨r, r', hsr, hrr', hr't, hup, _hdn⟩ :=
    hcr.crooked s t hst (ρ s) (ρ t) ⟨s, by simp, le_rfl, hcr.le s⟩ ⟨t, by simp, le_rfl, hcr.le t⟩
      (by rw [abs_of_nonpos (by omega : ρ s - ρ t ≤ 0)]; omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hup (by omega)
  have hsr' : s.val < r.val := hsr
  have hrr'' : r.val < r'.val := hrr'
  have hr't' : r'.val < t.val := hr't
  have hwr : σ r ≤ ρ r + 1 := hcr.width r
  have hrhi : L + 6 ≤ ρ r := by omega
  -- the peak is five steps or more from the basepoint
  have hine : i.val ≠ r.val := by
    intro hc
    rw [show r = i from Fin.ext hc.symm] at hrhi
    omega
  have hri : i.val + 5 ≤ r.val ∨ r.val + 5 ≤ i.val :=
    ivSep3 hcr i r hine (L + 4) (ρ t - 1) (by omega) (by omega)
      (by rw [← hp]; exact hcr.le i) hr1 hr2
  -- and far past the descent
  have hsr12 : s.val + 29 ≤ r.val := by
    rcases ivSep5 hcr s r (by omega) (ρ s) (ρ t - 1) (by omega) le_rfl (hcr.le s) hr1 hr2 with
      h | h
    · exact h
    · omega
  rcases hri with hfar | hnear
  · -- the peak lies past the basepoint: the two landmarks are the ones `Leg3Ceil` forbids
    exfalso
    have hrr29 : r.val + 29 ≤ r'.val := by
      rcases ivSep5 hcr r' r (by omega) (ρ s + 1) (ρ t - 1) (by omega) hr'1 hr'2 hr1 hr2 with
        h | h
      · omega
      · exact h
    have hr't29 : r'.val + 29 ≤ t.val := by
      rcases ivSep5 hcr r' t (by omega) (ρ s + 1) (ρ t) (by omega) hr'1 hr'2 le_rfl (hcr.le t) with
        h | h
      · exact h
      · omega
    exact absurd (hnoX r r' (by omega) (by omega) (by omega) (by omega)) (by omega)
  · exact ⟨r, by omega, by omega, hrhi⟩

/-- **The valley clause crosses the basepoint, backward form, with no exception.** -/
theorem ceil_cross_peak_bwd_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : i.val < s.val) (hsv : ρ s ≤ L + 1)
    (ht : t.val < i.val) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, j.val + 3 ≤ i.val → k.val + 5 ≤ j.val → t.val + 6 ≤ k.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    ∃ v : Fin n, i.val + 4 ≤ v.val ∧ v.val + 5 ≤ s.val ∧ L + 6 ≤ ρ v := by
  have hts : t < s := Fin.lt_def.mpr (by omega)
  obtain ⟨r, r', htr, hrr', hr's, _hup, hdn⟩ :=
    hcr.crooked t s hts (ρ t) (ρ s) ⟨t, by simp, le_rfl, hcr.le t⟩ ⟨s, by simp, le_rfl, hcr.le s⟩
      (by rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ ρ t - ρ s)]; omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hdn (by omega)
  have htr' : t.val < r.val := htr
  have hrr'' : r.val < r'.val := hrr'
  have hr's' : r'.val < s.val := hr's
  have hwr' : σ r' ≤ ρ r' + 1 := hcr.width r'
  have hr'hi : L + 6 ≤ ρ r' := by omega
  have hine : i.val ≠ r'.val := by
    intro hc
    rw [show r' = i from Fin.ext hc.symm] at hr'hi
    omega
  have hr'i : i.val + 5 ≤ r'.val ∨ r'.val + 5 ≤ i.val :=
    ivSep3 hcr i r' hine (L + 4) (ρ t - 1) (by omega) (by omega)
      (by rw [← hp]; exact hcr.le i) hr'1 hr'2
  have hr's29 : r'.val + 29 ≤ s.val := by
    rcases ivSep5 hcr s r' (by omega) (ρ s) (ρ t - 1) (by omega) le_rfl (hcr.le s) hr'1 hr'2 with
      h | h
    · omega
    · exact h
  rcases hr'i with hfar | hnear
  · exact ⟨r', by omega, by omega, hr'hi⟩
  · exfalso
    have hrr29 : r.val + 29 ≤ r'.val := by
      rcases ivSep5 hcr r r' (by omega) (ρ s + 1) (ρ t - 1) (by omega) hr1 hr2 hr'1 hr'2 with
        h | h
      · exact h
      · omega
    have htr29 : t.val + 29 ≤ r.val := by
      rcases ivSep5 hcr r t (by omega) (ρ s + 1) (ρ t) (by omega) hr1 hr2 le_rfl (hcr.le t) with
        h | h
      · omega
      · exact h
    exact absurd (hnoX r' r (by omega) (by omega) (by omega) (by omega)) (by omega)

/-! ## The ceiling half, with no residue -/

/-- **The ceiling clause crosses the basepoint, forward form, with no exception.** This is
`ceil_cross_high_fwd` (`HPC/Fold/CeilCross.lean`) without its residual disjunct: the peak the
clause returns reaches `L + 8`, so it is twelve steps or more from the basepoint, and on the
backward side it would then be the peak the failure of the Λ-criterion forbids. -/
theorem ceil_cross_high_fwd_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : s.val < i.val) (hsv : ρ s ≤ L + 1)
    (ht : i.val < t.val) (htv : L + 9 ≤ ρ t)
    (hnoY : ∀ v : Fin n, s.val < v.val → v.val + 5 ≤ i.val → ρ v ≤ L + 6) :
    ∃ j k : Fin n, i.val + 4 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val + 7 ≤ t.val ∧
      L + 6 ≤ ρ j ∧ ρ k ≤ L + 2 := by
  have hst : s < t := Fin.lt_def.mpr (by omega)
  obtain ⟨r, r', hsr, hrr', hr't, hup, _hdn⟩ :=
    hcr.crooked s t hst (ρ s) (ρ t) ⟨s, by simp, le_rfl, hcr.le s⟩ ⟨t, by simp, le_rfl, hcr.le t⟩
      (by rw [abs_of_nonpos (by omega : ρ s - ρ t ≤ 0)]; omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hup (by omega)
  have hsr' : s.val < r.val := hsr
  have hrr'' : r.val < r'.val := hrr'
  have hr't' : r'.val < t.val := hr't
  have hwr : σ r ≤ ρ r + 1 := hcr.width r
  have hrhi : L + 7 ≤ ρ r := by omega
  have hine : i.val ≠ r.val := by
    intro hc
    rw [show r = i from Fin.ext hc.symm] at hrhi
    omega
  have hri : i.val + 12 ≤ r.val ∨ r.val + 12 ≤ i.val :=
    ivSep4 hcr i r hine (L + 4) (ρ t - 1) (by omega) (by omega)
      (by rw [← hp]; exact hcr.le i) hr1 hr2
  rcases hri with hfar | hnear
  · have hrr29 : r.val + 29 ≤ r'.val := by
      rcases ivSep5 hcr r' r (by omega) (ρ s + 1) (ρ t - 1) (by omega) hr'1 hr'2 hr1 hr2 with
        h | h
      · omega
      · exact h
    have hr't29 : r'.val + 29 ≤ t.val := by
      rcases ivSep5 hcr r' t (by omega) (ρ s + 1) (ρ t) (by omega) hr'1 hr'2 le_rfl (hcr.le t) with
        h | h
      · exact h
      · omega
    exact ⟨r, r', by omega, by omega, by omega, by omega, by omega⟩
  · exact absurd (hnoY r hsr (by omega)) (by omega)

/-- **The ceiling clause crosses the basepoint, backward form, with no exception.** -/
theorem ceil_cross_high_bwd_far {n : ℕ} {ρ σ : Fin n → ℤ} (hcr : IsCrookedIvF ρ σ) (L : ℤ)
    (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : i.val < s.val) (hsv : ρ s ≤ L + 1)
    (ht : t.val < i.val) (htv : L + 9 ≤ ρ t)
    (hnoY : ∀ v : Fin n, v.val < s.val → i.val + 5 ≤ v.val → ρ v ≤ L + 6) :
    ∃ j k : Fin n, j.val + 4 ≤ i.val ∧ k.val + 6 ≤ j.val ∧ t.val + 7 ≤ k.val ∧
      L + 6 ≤ ρ j ∧ ρ k ≤ L + 2 := by
  have hts : t < s := Fin.lt_def.mpr (by omega)
  obtain ⟨r, r', htr, hrr', hr's, _hup, hdn⟩ :=
    hcr.crooked t s hts (ρ t) (ρ s) ⟨t, by simp, le_rfl, hcr.le t⟩ ⟨s, by simp, le_rfl, hcr.le s⟩
      (by rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ ρ t - ρ s)]; omega)
  obtain ⟨⟨hr1, hr2⟩, ⟨hr'1, hr'2⟩⟩ := hdn (by omega)
  have htr' : t.val < r.val := htr
  have hrr'' : r.val < r'.val := hrr'
  have hr's' : r'.val < s.val := hr's
  have hwr' : σ r' ≤ ρ r' + 1 := hcr.width r'
  have hr'hi : L + 7 ≤ ρ r' := by omega
  have hine : i.val ≠ r'.val := by
    intro hc
    rw [show r' = i from Fin.ext hc.symm] at hr'hi
    omega
  have hr'i : i.val + 12 ≤ r'.val ∨ r'.val + 12 ≤ i.val :=
    ivSep4 hcr i r' hine (L + 4) (ρ t - 1) (by omega) (by omega)
      (by rw [← hp]; exact hcr.le i) hr'1 hr'2
  rcases hr'i with hfar | hnear
  · exact absurd (hnoY r' hr's (by omega)) (by omega)
  · have hrr29 : r.val + 29 ≤ r'.val := by
      rcases ivSep5 hcr r r' (by omega) (ρ s + 1) (ρ t - 1) (by omega) hr1 hr2 hr'1 hr'2 with
        h | h
      · exact h
      · omega
    have htr29 : t.val + 29 ≤ r.val := by
      rcases ivSep5 hcr r t (by omega) (ρ s + 1) (ρ t) (by omega) hr1 hr2 le_rfl (hcr.le t) with
        h | h
      · omega
      · exact h
    exact ⟨r', r, by omega, by omega, by omega, by omega, by omega⟩

/-! ## The gap on the arms, and the work item -/

/-- **The ceiling crossing on the arms, forward form, with no residue.** If the forward arm fails `Leg3Ceil` and
the pair does not fold onto the Λ-walk, then the
forward arm satisfies `TopW5` and the backward arm satisfies `Valley5`. -/
theorem ceil_gap_fwd_far {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)))
    (hfG : ¬ Leg3Ceil (armG ρ i) L) :
    TopW5 (armG ρ i) L ∧ Valley5 (armT ρ i) L := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  -- the forward arm's unprepared ascent, read globally
  rw [Leg3Ceil] at hfG
  push_neg at hfG
  obtain ⟨D, hD, hDno⟩ := hfG
  have hDm := D.isLt
  have hDpos : 0 < D.val := by
    rcases Nat.eq_zero_or_pos D.val with h | h
    · exact absurd (congrArg (armG ρ i) (Fin.ext h : D = ⟨0, hmG⟩)) (by rw [hG0]; omega)
    · exact h
  set t : Fin n := ⟨i.val + D.val, by omega⟩ with htdef
  have htval : t.val = i.val + D.val := rfl
  have htv : L + 8 ≤ ρ t := hD
  have hnoX : ∀ j k : Fin n, i.val + 3 ≤ j.val → j.val + 5 ≤ k.val → k.val + 6 ≤ t.val →
      L + 5 ≤ ρ j → L + 2 < ρ k := by
    intro j k h1 h2 h3 h4
    have hjn := j.isLt
    have hkn := k.isLt
    have hjb : j.val - i.val < n - i.val := by omega
    have hkb : k.val - i.val < n - i.val := by omega
    have hje : armG ρ i ⟨j.val - i.val, hjb⟩ = ρ j :=
      congrArg ρ (Fin.ext (by show i.val + (j.val - i.val) = j.val; omega))
    have hke : armG ρ i ⟨k.val - i.val, hkb⟩ = ρ k :=
      congrArg ρ (Fin.ext (by show i.val + (k.val - i.val) = k.val; omega))
    have := hDno ⟨j.val - i.val, hjb⟩ ⟨k.val - i.val, hkb⟩ (by simp; omega) (by simp; omega)
      (by simp; omega) (by rw [hje]; exact h4)
    rw [hke] at this
    exact this
  constructor
  · -- the ceiling clause on the forward arm
    intro d hd
    have hdm := d.isLt
    -- the backward arm does not fold onto the Λ-walk
    have hlG : FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
      rcases leg3Ceil_or_lam hmG (armG ρ i) (armG_isLip hlip i) (crookUp_armG hcr i)
        (crookDown_armG hcr i) L hG0 (fun j => hLb _) (fun j => hHb _) with h | h
      · exact absurd h (by rw [Leg3Ceil]; push_neg; exact ⟨D, hD, hDno⟩)
      · exact h
    have hnlT : ¬ FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L)
        (lamCenter (L + 3) (L + 9) L) := fun h => hnotLam ⟨hlG, h⟩
    rw [foldsOnto_lam_iff_profile hmT (armT ρ i) (armT_isLip hlip i) (L + 3) (L + 9) L (by omega)
      (by rw [hT0, abs_le]; omega) (fun j => hLb _) (fun j => hHb _),
      critLamProfile_iff_of_isLip (armT_isLip hlip i), show κ (L + 3) (L + 9) = L + 8 by
        simp only [κ]; omega] at hnlT
    push_neg at hnlT
    obtain ⟨e, he, heno⟩ := hnlT
    have hem := e.isLt
    have hepos : 0 < e.val := by
      rcases Nat.eq_zero_or_pos e.val with h | h
      · exact absurd (congrArg (armT ρ i) (Fin.ext h : e = ⟨0, hmT⟩)) (by rw [hT0]; omega)
      · exact h
    set s : Fin n := ⟨i.val - e.val, by omega⟩ with hsdef
    have hsval : s.val = i.val - e.val := rfl
    have hse : armT ρ i e = ρ s := rfl
    have hsv : ρ s ≤ L + 1 := by rw [← hse]; omega
    have hnoY : ∀ v : Fin n, s.val < v.val → v.val + 5 ≤ i.val → ρ v ≤ L + 6 := by
      intro v h1 h2
      have hvb : i.val - v.val < i.val + 1 := by omega
      have hve : armT ρ i ⟨i.val - v.val, hvb⟩ = ρ v :=
        congrArg ρ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
      have := heno ⟨i.val - v.val, hvb⟩ (by simp; omega)
        (by simp; omega)
      rw [hve] at this
      omega
    set t' : Fin n := ⟨i.val + d.val, by omega⟩ with htdef'
    have htval' : t'.val = i.val + d.val := rfl
    have htv' : L + 9 ≤ ρ t' := hd
    have hdpos : 0 < d.val := by
      rcases Nat.eq_zero_or_pos d.val with h | h
      · exact absurd (congrArg (armG ρ i) (Fin.ext h : d = ⟨0, hmG⟩)) (by rw [hG0]; omega)
      · exact h
    rcases (Or.inl (ceil_cross_high_fwd_far hcr L i s t' hp (by omega) hsv
        (by omega) htv' hnoY) : _ ∨ False) with ⟨j, k, h1, h2, h3, h4, h5⟩ | hbad
    · have hjn := j.isLt
      have hkn := k.isLt
      have hjb : j.val - i.val < n - i.val := by omega
      have hkb : k.val - i.val < n - i.val := by omega
      have hje : armG ρ i ⟨j.val - i.val, hjb⟩ = ρ j :=
        congrArg ρ (Fin.ext (by show i.val + (j.val - i.val) = j.val; omega))
      have hke : armG ρ i ⟨k.val - i.val, hkb⟩ = ρ k :=
        congrArg ρ (Fin.ext (by show i.val + (k.val - i.val) = k.val; omega))
      have h3' : k.val + 7 ≤ i.val + d.val := by omega
      exact ⟨⟨j.val - i.val, hjb⟩, ⟨k.val - i.val, hkb⟩, by simp; omega, by simp; omega,
        by simp; omega, by rw [hje]; exact h4, by rw [hke]; exact h5⟩
    · exact hbad.elim
  · -- the valley clause on the backward arm
    intro d hd
    have hdm := d.isLt
    have hdpos : 0 < d.val := by
      rcases Nat.eq_zero_or_pos d.val with h | h
      · exact absurd (congrArg (armT ρ i) (Fin.ext h : d = ⟨0, hmT⟩)) (by rw [hT0]; omega)
      · exact h
    set s : Fin n := ⟨i.val - d.val, by omega⟩ with hsdef
    have hsval : s.val = i.val - d.val := rfl
    have hsv : ρ s ≤ L + 1 := hd
    rcases (Or.inl (ceil_cross_peak_fwd_far hcr L i s t hp (by omega) hsv
        (by omega) htv hnoX) : _ ∨ False) with ⟨v, h1, h2, h3⟩ | hbad
    · have hvn := v.isLt
      have hvb : i.val - v.val < i.val + 1 := by omega
      have hve : armT ρ i ⟨i.val - v.val, hvb⟩ = ρ v :=
        congrArg ρ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
      have h1' : i.val - d.val + 12 ≤ v.val := by omega
      exact ⟨⟨i.val - v.val, hvb⟩, by simp; omega, by simp; omega, by rw [hve]; exact h3⟩
    · exact hbad.elim

/-- **The ceiling crossing on the arms, backward form**, the mirror of `ceil_gap_fwd_far`. -/
theorem ceil_gap_bwd_far {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)))
    (hfT : ¬ Leg3Ceil (armT ρ i) L) :
    TopW5 (armT ρ i) L ∧ Valley5 (armG ρ i) L := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  rw [Leg3Ceil] at hfT
  push_neg at hfT
  obtain ⟨D, hD, hDno⟩ := hfT
  have hDm := D.isLt
  have hDpos : 0 < D.val := by
    rcases Nat.eq_zero_or_pos D.val with h | h
    · exact absurd (congrArg (armT ρ i) (Fin.ext h : D = ⟨0, hmT⟩)) (by rw [hT0]; omega)
    · exact h
  set t : Fin n := ⟨i.val - D.val, by omega⟩ with htdef
  have htval : t.val = i.val - D.val := rfl
  have htv : L + 8 ≤ ρ t := hD
  have hnoX : ∀ j k : Fin n, j.val + 3 ≤ i.val → k.val + 5 ≤ j.val → t.val + 6 ≤ k.val →
      L + 5 ≤ ρ j → L + 2 < ρ k := by
    intro j k h1 h2 h3 h4
    have hjb : i.val - j.val < i.val + 1 := by omega
    have hkb : i.val - k.val < i.val + 1 := by omega
    have hje : armT ρ i ⟨i.val - j.val, hjb⟩ = ρ j :=
      congrArg ρ (Fin.ext (by show i.val - (i.val - j.val) = j.val; omega))
    have hke : armT ρ i ⟨i.val - k.val, hkb⟩ = ρ k :=
      congrArg ρ (Fin.ext (by show i.val - (i.val - k.val) = k.val; omega))
    have h3' : i.val - D.val + 6 ≤ k.val := by omega
    have := hDno ⟨i.val - j.val, hjb⟩ ⟨i.val - k.val, hkb⟩ (by simp; omega) (by simp; omega)
      (by simp; omega) (by rw [hje]; exact h4)
    rw [hke] at this
    exact this
  constructor
  · intro d hd
    have hdm := d.isLt
    have hlT : FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
      rcases leg3Ceil_or_lam hmT (armT ρ i) (armT_isLip hlip i) (crookUp_armT hcr i)
        (crookDown_armT hcr i) L hT0 (fun j => hLb _) (fun j => hHb _) with h | h
      · exact absurd h (by rw [Leg3Ceil]; push_neg; exact ⟨D, hD, hDno⟩)
      · exact h
    have hnlG : ¬ FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L)
        (lamCenter (L + 3) (L + 9) L) := fun h => hnotLam ⟨h, hlT⟩
    rw [foldsOnto_lam_iff_profile hmG (armG ρ i) (armG_isLip hlip i) (L + 3) (L + 9) L (by omega)
      (by rw [hG0, abs_le]; omega) (fun j => hLb _) (fun j => hHb _),
      critLamProfile_iff_of_isLip (armG_isLip hlip i), show κ (L + 3) (L + 9) = L + 8 by
        simp only [κ]; omega] at hnlG
    push_neg at hnlG
    obtain ⟨e, he, heno⟩ := hnlG
    have hem := e.isLt
    have hepos : 0 < e.val := by
      rcases Nat.eq_zero_or_pos e.val with h | h
      · exact absurd (congrArg (armG ρ i) (Fin.ext h : e = ⟨0, hmG⟩)) (by rw [hG0]; omega)
      · exact h
    set s : Fin n := ⟨i.val + e.val, by omega⟩ with hsdef
    have hsval : s.val = i.val + e.val := rfl
    have hse : armG ρ i e = ρ s := rfl
    have hsv : ρ s ≤ L + 1 := by rw [← hse]; omega
    have hnoY : ∀ v : Fin n, v.val < s.val → i.val + 5 ≤ v.val → ρ v ≤ L + 6 := by
      intro v h1 h2
      have hvn := v.isLt
      have hvb : v.val - i.val < n - i.val := by omega
      have hve : armG ρ i ⟨v.val - i.val, hvb⟩ = ρ v :=
        congrArg ρ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
      have h1' : v.val < i.val + e.val := by omega
      have := heno ⟨v.val - i.val, hvb⟩ (by simp; omega) (by simp; omega)
      rw [hve] at this
      omega
    set t' : Fin n := ⟨i.val - d.val, by omega⟩ with htdef'
    have htval' : t'.val = i.val - d.val := rfl
    have htv' : L + 9 ≤ ρ t' := hd
    have hdpos : 0 < d.val := by
      rcases Nat.eq_zero_or_pos d.val with h | h
      · exact absurd (congrArg (armT ρ i) (Fin.ext h : d = ⟨0, hmT⟩)) (by rw [hT0]; omega)
      · exact h
    rcases (Or.inl (ceil_cross_high_bwd_far hcr L i s t' hp (by omega) hsv
        (by omega) htv' hnoY) : _ ∨ False) with ⟨j, k, h1, h2, h3, h4, h5⟩ | hbad
    · have hjb : i.val - j.val < i.val + 1 := by omega
      have hkb : i.val - k.val < i.val + 1 := by omega
      have hje : armT ρ i ⟨i.val - j.val, hjb⟩ = ρ j :=
        congrArg ρ (Fin.ext (by show i.val - (i.val - j.val) = j.val; omega))
      have hke : armT ρ i ⟨i.val - k.val, hkb⟩ = ρ k :=
        congrArg ρ (Fin.ext (by show i.val - (i.val - k.val) = k.val; omega))
      have h3' : i.val - d.val + 7 ≤ k.val := by omega
      exact ⟨⟨i.val - j.val, hjb⟩, ⟨i.val - k.val, hkb⟩, by simp; omega, by simp; omega,
        by simp; omega, by rw [hje]; exact h4, by rw [hke]; exact h5⟩
    · exact hbad.elim
  · intro d hd
    have hdm := d.isLt
    have hdpos : 0 < d.val := by
      rcases Nat.eq_zero_or_pos d.val with h | h
      · exact absurd (congrArg (armG ρ i) (Fin.ext h : d = ⟨0, hmG⟩)) (by rw [hG0]; omega)
      · exact h
    set s : Fin n := ⟨i.val + d.val, by omega⟩ with hsdef
    have hsval : s.val = i.val + d.val := rfl
    have hsv : ρ s ≤ L + 1 := hd
    rcases (Or.inl (ceil_cross_peak_bwd_far hcr L i s t hp (by omega) hsv
        (by omega) htv hnoX) : _ ∨ False) with ⟨v, h1, h2, h3⟩ | hbad
    · have hvn := v.isLt
      have hvb : v.val - i.val < n - i.val := by omega
      have hve : armG ρ i ⟨v.val - i.val, hvb⟩ = ρ v :=
        congrArg ρ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
      have h2' : v.val + 5 ≤ i.val + d.val := by omega
      exact ⟨⟨v.val - i.val, hvb⟩, by simp; omega, by simp; omega, by rw [hve]; exact h3⟩
    · exact hbad.elim

/-- **The two clauses the ceiling case needs, with no exception.** This is
`ceilCrossGap_of_not_residual` (`HPC/Fold/CeilCross.lean`) with both residual hypotheses
removed. -/
theorem ceilCrossGap_far {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) :
    CeilCrossGap ρ i L :=
  ⟨fun h => ceil_gap_fwd_far ρ σ i L hlip hcr hLb hHb hp hnotLam h,
    fun h => ceil_gap_bwd_far ρ σ i L hlip hcr hLb hHb hp hnotLam h⟩

/-- **The ceiling crossing, with no exception.** This is the work item `cross_ceil_sentence`
(`HPC/Fold/CrossCeil.lean`), with the second disjunct: both arms satisfy the sentence of `w₅`. -/
theorem cross_ceil_sentence_far {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Ceil (armG ρ i) L ∨ ¬ Leg3Ceil (armT ρ i) L)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) :
    ((MidW4 (armG ρ i) L ∧ BottomW4 (armG ρ i) L) ∧
        (MidW4 (armT ρ i) L ∧ BottomW4 (armT ρ i) L)) ∨
      ((Valley5 (armG ρ i) L ∧ TopW5 (armG ρ i) L) ∧
        (Valley5 (armT ρ i) L ∧ TopW5 (armT ρ i) L)) :=
  cross_ceil_sentence_of_gap ρ σ i L hlip hcr hLb hHb hp hfail hnotLam
    (ceilCrossGap_far ρ σ i L hlip hcr hLb hHb hp hnotLam)

end HPC.Fold
