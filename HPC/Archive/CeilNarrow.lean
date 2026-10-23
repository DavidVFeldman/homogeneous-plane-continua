import HPC.Fold.CeilCross

/-!
# Inside the peak residue of the ceiling crossing

`HPC/Fold/CeilCross.lean` proves the two clauses the ceiling case of the work item needs
(`CeilCrossGap`) outside two configurations, `CeilPeakResidual` and `CeilHighResidual`, each a
statement about the four steps either side of the basepoint. This file goes inside the first of
them and asks what else the model says there.

The answer is that the peak residue does not stand alone: it drags a second configuration with it,
and that one is a statement about the *far* arm — the arm that fails `Leg3Ceil`.

> **`ceil_cross_peak_fwd_narrow`.** In the configuration of `ceil_cross_peak_fwd`, either the
> backward arm has the peak `Valley5` asks for, or `CeilPeakResidual` holds **and** the forward arm
> stands at exactly `L + 2` at some time two or more steps past the basepoint at which the interval
> pair meets no level at or below `L + 1`, within one step either way, and stands at `L + 2` or
> above at every time from two steps past the basepoint up to that one (`CeilFarFlatG`).

Two observations carry it, and both are about the failing arm.

* **No low crossing on the far arm** (`ceil_no_low_far_fwd`): before its unprepared ascent the
  failing arm never stands at `L + 1` or below, from two steps past the basepoint on. A time there
  at `L + 1` would let the crookedness clause return, between it and the ascent, exactly the pair
  of landmarks the failure of `Leg3Ceil` forbids.
* **The bottom the clause returns is narrow** (`ceil_flat_narrow_fwd`): the same argument run with
  the *interval* clause of `IsCrookedIvF`, whose trigger level need only be met within one step of
  the anchor, excludes a level at or below `L + 1` at the two neighbours as well. This is the one
  place in the ceiling crossing where the faithful model says more than the two crookedness clauses
  of the sequence do, and it buys exactly the one index that separates `i + 2` from `i + 3`.

With those, the low time the clause returns in the residue is pinned: it cannot lie between the
residual peak and the basepoint (the Lipschitz bound), it cannot be the basepoint, so it lies two
or more steps beyond it — and there it is a flat, narrow bottom at `L + 2`.

The assembled statement is `cross_ceil_sentence_of_not_narrow_residual`: the work item holds unless
`CeilHighResidual` holds, or `CeilPeakResidual` holds *together with* the flat narrow bottom on the
failing arm. It is `cross_ceil_sentence_of_not_residual` with the first residue replaced by a
strictly smaller one.
-/

namespace HPC.Fold

/-! ## The flat narrow bottom on the far arm -/

/-- **A flat narrow bottom on the forward arm**: the sequence stands at exactly `L + 2` at a time
two or more steps past the basepoint, the interval pair meets no level at or below `L + 1` there
or at either neighbour, and the sequence stands at `L + 2` or above at every time between two
steps past the basepoint and that one. -/
def CeilFarFlatG {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ w : Fin n, i.val + 2 ≤ w.val ∧ ρ w = L + 2 ∧
    (∀ y : Fin n, ((y : ℤ) - (w : ℤ)).natAbs ≤ 1 → L + 2 ≤ ρ y) ∧
    (∀ v : Fin n, i.val + 2 ≤ v.val → v.val ≤ w.val → L + 2 ≤ ρ v)

/-- **A flat narrow bottom on the backward arm**, the mirror of `CeilFarFlatG`. -/
def CeilFarFlatT {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ w : Fin n, w.val + 2 ≤ i.val ∧ ρ w = L + 2 ∧
    (∀ y : Fin n, ((y : ℤ) - (w : ℤ)).natAbs ≤ 1 → L + 2 ≤ ρ y) ∧
    (∀ v : Fin n, v.val + 2 ≤ i.val → w.val ≤ v.val → L + 2 ≤ ρ v)

/-! ## The failing arm keeps away from the floor -/

/-- **No low crossing on the far arm, forward form.** With `t` an unprepared ascent to `L + 8` on
the forward arm — `hnoX` is the failure of `Leg3Ceil` read in global indices — the sequence stands
at `L + 2` or above at every time from `i + 2` to `t`. -/
theorem ceil_no_low_far_fwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ) (hcrU : CrookUp ρ)
    (hcrD : CrookDown ρ) (L : ℤ) (i t : Fin n) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, i.val + 3 ≤ j.val → j.val + 5 ≤ k.val → k.val + 6 ≤ t.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    ∀ w : Fin n, i.val + 2 ≤ w.val → w.val < t.val → L + 2 ≤ ρ w := by
  intro w hw hwt
  by_contra hc
  push_neg at hc
  obtain ⟨u, u', hwu, huu', hu't, hu, hu'⟩ :=
    hcrU.levels (L + 1) (L + 8) (by omega) w t hwt (by omega) htv
  have hfall : u.val + 7 ≤ u'.val := crookDown_fall4 hlip hcrD u u' huu' (by omega)
  have hclimb : u'.val + 12 ≤ t.val := crookUp_climb5 hlip hcrU u' t hu't (by omega)
  exact absurd (hnoX u u' (by omega) (by omega) (by omega) (by omega)) (by omega)

/-- **The bottom on the far arm is narrow, forward form.** With the same data, if the interval pair
meets a level at or below `L + 1` within one step of a time `w` past the basepoint, the crookedness
clause of the faithful model returns, between `w` and the ascent, the two landmarks the failure of
`Leg3Ceil` forbids. So no such level is met. -/
theorem ceil_flat_narrow_fwd {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (L : ℤ) (i t : Fin n) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, i.val + 3 ≤ j.val → j.val + 5 ≤ k.val → k.val + 6 ≤ t.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    ∀ w : Fin n, i.val + 2 ≤ w.val → w.val < t.val →
      ∀ y : Fin n, ((y : ℤ) - (w : ℤ)).natAbs ≤ 1 → L + 2 ≤ ρ y := by
  intro w hw hwt y hy
  by_contra hc
  push_neg at hc
  have hcrU := crookUp_seq hcr
  have hcrD := crookDown_seq hcr
  obtain ⟨r, r', hwr, hrr', hr't, hcase, -⟩ :=
    hcr.crooked w t (Fin.lt_def.mpr hwt) (ρ y) (ρ t)
      ⟨y, hy, le_refl _, hcr.le _⟩ ⟨t, by simp, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonpos] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, hr'1, -⟩ := hcase (by omega)
  have hwr' : w.val < r.val := Fin.lt_def.mp hwr
  have hrr'' : r.val < r'.val := Fin.lt_def.mp hrr'
  have hr't' : r'.val < t.val := Fin.lt_def.mp hr't
  have hwidth := hcr.width r
  have hrlow : L + 6 ≤ ρ r := by omega
  have hr'high : ρ r' ≤ L + 2 := by omega
  have hfall : r.val + 7 ≤ r'.val := crookDown_fall4 hlip hcrD r r' hrr'' (by omega)
  have hclimb : r'.val + 12 ≤ t.val := crookUp_climb5 hlip hcrU r' t hr't' (by omega)
  exact absurd (hnoX r r' (by omega) (by omega) (by omega) (by omega)) (by omega)

/-- **No low crossing on the far arm, backward form**, the mirror of `ceil_no_low_far_fwd`. -/
theorem ceil_no_low_far_bwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ) (hcrU : CrookUp ρ)
    (hcrD : CrookDown ρ) (L : ℤ) (i t : Fin n) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, j.val + 3 ≤ i.val → k.val + 5 ≤ j.val → t.val + 6 ≤ k.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    ∀ w : Fin n, w.val + 2 ≤ i.val → t.val < w.val → L + 2 ≤ ρ w := by
  intro w hw hwt
  by_contra hc
  push_neg at hc
  obtain ⟨u, u', htu, huu', hu'w, hu, hu'⟩ :=
    hcrD.levels (L + 1) (L + 8) (by omega) t w hwt htv (by omega)
  have hfall : t.val + 7 ≤ u.val := crookDown_fall4 hlip hcrD t u htu (by omega)
  have hclimb : u.val + 7 ≤ u'.val := crookUp_climb4 hlip hcrU u u' huu' (by omega)
  exact absurd (hnoX u' u (by omega) (by omega) (by omega) (by omega)) (by omega)

/-- **The bottom on the far arm is narrow, backward form**, the mirror of
`ceil_flat_narrow_fwd`. -/
theorem ceil_flat_narrow_bwd {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (L : ℤ) (i t : Fin n) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, j.val + 3 ≤ i.val → k.val + 5 ≤ j.val → t.val + 6 ≤ k.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    ∀ w : Fin n, w.val + 2 ≤ i.val → t.val < w.val →
      ∀ y : Fin n, ((y : ℤ) - (w : ℤ)).natAbs ≤ 1 → L + 2 ≤ ρ y := by
  intro w hw hwt y hy
  by_contra hc
  push_neg at hc
  have hcrU := crookUp_seq hcr
  have hcrD := crookDown_seq hcr
  obtain ⟨r, r', htr, hrr', hr'w, -, hcase⟩ :=
    hcr.crooked t w (Fin.lt_def.mpr hwt) (ρ t) (ρ y)
      ⟨t, by simp, le_refl _, hcr.le _⟩ ⟨y, hy, le_refl _, hcr.le _⟩
      (by rw [abs_of_nonneg] <;> omega)
  obtain ⟨⟨hr1, hr2⟩, hr'1, -⟩ := hcase (by omega)
  have htr' : t.val < r.val := Fin.lt_def.mp htr
  have hrr'' : r.val < r'.val := Fin.lt_def.mp hrr'
  have hr'w' : r'.val < w.val := Fin.lt_def.mp hr'w
  have hwidth := hcr.width r'
  have hrlow : ρ r ≤ L + 2 := by omega
  have hr'high : L + 6 ≤ ρ r' := by omega
  have hfall : t.val + 7 ≤ r.val := crookDown_fall4 hlip hcrD t r htr' (by omega)
  have hclimb : r.val + 7 ≤ r'.val := crookUp_climb4 hlip hcrU r r' hrr'' (by omega)
  exact absurd (hnoX r' r (by omega) (by omega) (by omega) (by omega)) (by omega)

/-! ## The sharpened peak dichotomy -/

/-- **The valley clause crosses the basepoint, forward form, sharpened.** The conclusion of
`ceil_cross_peak_fwd`, with the residual configuration replaced by the conjunction of
`CeilPeakResidual` and a flat narrow bottom at `L + 2` on the failing arm. -/
theorem ceil_cross_peak_fwd_narrow {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : s.val < i.val) (hsv : ρ s ≤ L + 1)
    (ht : i.val < t.val) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, i.val + 3 ≤ j.val → j.val + 5 ≤ k.val → k.val + 6 ≤ t.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    (∃ v : Fin n, s.val + 12 ≤ v.val ∧ v.val + 4 ≤ i.val ∧ L + 6 ≤ ρ v) ∨
      (CeilPeakResidual ρ i L ∧ CeilFarFlatG ρ i L) := by
  have hcrU := crookUp_seq hcr
  have hcrD := crookDown_seq hcr
  obtain ⟨u, u', hsu, huu', hu't, hu, hu'⟩ :=
    hcrU.levels (L + 1) (L + 8) (by omega) s t (by omega) hsv htv
  have hsu12 : s.val + 12 ≤ u.val := crookUp_climb5 hlip hcrU s u hsu (by omega)
  have hfall : u.val + 7 ≤ u'.val := crookDown_fall4 hlip hcrD u u' huu' (by omega)
  have hclimb : u'.val + 12 ≤ t.val := crookUp_climb5 hlip hcrU u' t hu't (by omega)
  -- the peak `u` is at least two steps from the basepoint
  have hnear : u.val + 2 ≤ i.val ∨ i.val + 2 ≤ u.val := by
    rcases lt_trichotomy u.val i.val with h | h | h
    · have hd := abs_sub_le_of_isLip hlip (i.val - u.val) u i (by omega)
      rw [abs_le] at hd
      have hc : ((i.val - u.val : ℕ) : ℤ) = (i.val : ℤ) - (u.val : ℤ) := by
        push_cast [Nat.cast_sub (le_of_lt h)]; ring
      rw [hc] at hd; omega
    · exact absurd (congrArg ρ (Fin.ext h : u = i)) (by omega)
    · have hd := abs_sub_le_of_isLip hlip (u.val - i.val) i u (by omega)
      rw [abs_le] at hd
      have hc : ((u.val - i.val : ℕ) : ℤ) = (u.val : ℤ) - (i.val : ℤ) := by
        push_cast [Nat.cast_sub (le_of_lt h)]; ring
      rw [hc] at hd; omega
  -- if the peak lies past the basepoint, the failure of `Leg3Ceil` is contradicted
  have hulow : u.val + 2 ≤ i.val := by
    rcases hnear with h | h
    · exact h
    · exfalso
      by_cases hthree : i.val + 3 ≤ u.val
      · exact absurd (hnoX u u' hthree (by omega) (by omega) (by omega)) (by omega)
      · have hu2 : u.val = i.val + 2 := by omega
        have hlt : i.val + 3 < n := by omega
        set j : Fin n := ⟨i.val + 3, hlt⟩ with hjdef
        have hju : |ρ j - ρ u| ≤ 1 := by
          have := abs_sub_le_of_isLip hlip 1 u j (by simp [hjdef]; omega)
          simpa using this
        rw [abs_le] at hju
        exact absurd (hnoX j u' (by simp [hjdef]) (by simp [hjdef]; omega) (by omega)
          (by omega)) (by omega)
  by_cases hfar : u.val + 4 ≤ i.val
  · exact Or.inl ⟨u, hsu12, hfar, by omega⟩
  · -- the residue: the peak is two or three steps before the basepoint
    refine Or.inr ⟨⟨u, by omega, by omega⟩, ?_⟩
    -- the low time the clause returns lies two or more steps past the basepoint
    have hu'far : i.val + 2 ≤ u'.val := by
      rcases lt_trichotomy u'.val i.val with h | h | h
      · exfalso
        have hd := abs_sub_le_of_isLip hlip (u'.val - u.val) u u' (by omega)
        rw [abs_le] at hd
        have hc : ((u'.val - u.val : ℕ) : ℤ) = (u'.val : ℤ) - (u.val : ℤ) := by
          push_cast [Nat.cast_sub (le_of_lt (by omega : u.val < u'.val))]; ring
        rw [hc] at hd
        omega
      · exact absurd (congrArg ρ (Fin.ext h : u' = i)) (by omega)
      · by_contra hcon
        have hu'1 : u'.val = i.val + 1 := by omega
        have hd := abs_sub_le_of_isLip hlip 1 i u' (by omega)
        rw [abs_le] at hd
        omega
    refine ⟨u', hu'far, ?_, ?_, ?_⟩
    · have := ceil_no_low_far_fwd hlip hcrU hcrD L i t htv hnoX u' hu'far (by omega)
      omega
    · exact ceil_flat_narrow_fwd hlip hcr L i t htv hnoX u' hu'far (by omega)
    · exact fun v h1 h2 => ceil_no_low_far_fwd hlip hcrU hcrD L i t htv hnoX v h1 (by omega)

/-- **The valley clause crosses the basepoint, backward form, sharpened**, the mirror of
`ceil_cross_peak_fwd_narrow`. -/
theorem ceil_cross_peak_bwd_narrow {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : i.val < s.val) (hsv : ρ s ≤ L + 1)
    (ht : t.val < i.val) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, j.val + 3 ≤ i.val → k.val + 5 ≤ j.val → t.val + 6 ≤ k.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    (∃ v : Fin n, i.val + 4 ≤ v.val ∧ v.val + 5 ≤ s.val ∧ L + 6 ≤ ρ v) ∨
      (CeilPeakResidual ρ i L ∧ CeilFarFlatT ρ i L) := by
  have hcrU := crookUp_seq hcr
  have hcrD := crookDown_seq hcr
  obtain ⟨u, u', htu, huu', hu's, hu, hu'⟩ :=
    hcrD.levels (L + 1) (L + 8) (by omega) t s (by omega) htv hsv
  have hfall : t.val + 7 ≤ u.val := crookDown_fall4 hlip hcrD t u htu (by omega)
  have hclimb : u.val + 7 ≤ u'.val := crookUp_climb4 hlip hcrU u u' huu' (by omega)
  have hfall5 : u'.val + 7 ≤ s.val := crookDown_fall4 hlip hcrD u' s hu's (by omega)
  -- the peak `u'` is at least two steps from the basepoint
  have hnear : u'.val + 2 ≤ i.val ∨ i.val + 2 ≤ u'.val := by
    rcases lt_trichotomy u'.val i.val with h | h | h
    · have hd := abs_sub_le_of_isLip hlip (i.val - u'.val) u' i (by omega)
      rw [abs_le] at hd
      have hc : ((i.val - u'.val : ℕ) : ℤ) = (i.val : ℤ) - (u'.val : ℤ) := by
        push_cast [Nat.cast_sub (le_of_lt h)]; ring
      rw [hc] at hd; omega
    · exact absurd (congrArg ρ (Fin.ext h : u' = i)) (by omega)
    · have hd := abs_sub_le_of_isLip hlip (u'.val - i.val) i u' (by omega)
      rw [abs_le] at hd
      have hc : ((u'.val - i.val : ℕ) : ℤ) = (u'.val : ℤ) - (i.val : ℤ) := by
        push_cast [Nat.cast_sub (le_of_lt h)]; ring
      rw [hc] at hd; omega
  -- if the peak lies before the basepoint, the failure of `Leg3Ceil` is contradicted
  have hupast : i.val + 2 ≤ u'.val := by
    rcases hnear with h | h
    · exfalso
      by_cases hthree : u'.val + 3 ≤ i.val
      · exact absurd (hnoX u' u hthree (by omega) (by omega) (by omega)) (by omega)
      · have hu2 : u'.val + 2 = i.val := by omega
        have hlt : i.val - 3 < n := by omega
        set j : Fin n := ⟨i.val - 3, hlt⟩ with hjdef
        have hju : |ρ j - ρ u'| ≤ 1 := by
          have := abs_sub_le_of_isLip hlip 1 j u' (by simp [hjdef]; omega)
          rw [abs_sub_comm] at this
          simpa using this
        rw [abs_le] at hju
        exact absurd (hnoX j u (by simp [hjdef]; omega) (by simp [hjdef]; omega) (by omega)
          (by omega)) (by omega)
    · exact h
  by_cases hfar : i.val + 4 ≤ u'.val
  · exact Or.inl ⟨u', hfar, by omega, by omega⟩
  · refine Or.inr ⟨⟨u', by omega, by omega⟩, ?_⟩
    have hufar : u.val + 2 ≤ i.val := by
      rcases lt_trichotomy u.val i.val with h | h | h
      · by_contra hcon
        have hu1 : u.val + 1 = i.val := by omega
        have hd := abs_sub_le_of_isLip hlip 1 u i (by omega)
        rw [abs_le] at hd
        omega
      · exact absurd (congrArg ρ (Fin.ext h : u = i)) (by omega)
      · exfalso
        have hd := abs_sub_le_of_isLip hlip (u'.val - u.val) u u' (by omega)
        rw [abs_le] at hd
        have hc : ((u'.val - u.val : ℕ) : ℤ) = (u'.val : ℤ) - (u.val : ℤ) := by
          push_cast [Nat.cast_sub (le_of_lt (by omega : u.val < u'.val))]; ring
        rw [hc] at hd
        omega
    refine ⟨u, hufar, ?_, ?_, ?_⟩
    · have := ceil_no_low_far_bwd hlip hcrU hcrD L i t htv hnoX u hufar (by omega)
      omega
    · exact ceil_flat_narrow_bwd hlip hcr L i t htv hnoX u hufar (by omega)
    · exact fun v h1 h2 => ceil_no_low_far_bwd hlip hcrU hcrD L i t htv hnoX v h1 (by omega)

/-! ## The crossing on the arms, with the sharpened residue -/

/-- **The ceiling crossing on the arms, forward form, sharpened.** `ceil_gap_fwd` with the peak
residue replaced by its conjunction with the flat narrow bottom on the failing arm. -/
theorem ceil_gap_fwd_narrow {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hres1 : ¬ (CeilPeakResidual ρ i L ∧ CeilFarFlatG ρ i L)) (hres2 : ¬ CeilHighResidual ρ i L)
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
  have hcrU := crookUp_seq hcr
  have hcrD := crookDown_seq hcr
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
    rcases ceil_cross_high_fwd hlip hcrU hcrD L i s t' hp (by omega) hsv
        (by omega) htv' hnoY with ⟨j, k, h1, h2, h3, h4, h5⟩ | hbad
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
    · exact absurd hbad hres2
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
    rcases ceil_cross_peak_fwd_narrow hlip hcr L i s t hp (by omega) hsv
        (by omega) htv hnoX with ⟨v, h1, h2, h3⟩ | hbad
    · have hvn := v.isLt
      have hvb : i.val - v.val < i.val + 1 := by omega
      have hve : armT ρ i ⟨i.val - v.val, hvb⟩ = ρ v :=
        congrArg ρ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
      have h1' : i.val - d.val + 12 ≤ v.val := by omega
      exact ⟨⟨i.val - v.val, hvb⟩, by simp; omega, by simp; omega, by rw [hve]; exact h3⟩
    · exact absurd hbad hres1

/-- **The ceiling crossing on the arms, backward form, sharpened**, the mirror of
`ceil_gap_fwd_narrow`. -/
theorem ceil_gap_bwd_narrow {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hres1 : ¬ (CeilPeakResidual ρ i L ∧ CeilFarFlatT ρ i L)) (hres2 : ¬ CeilHighResidual ρ i L)
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
  have hcrU := crookUp_seq hcr
  have hcrD := crookDown_seq hcr
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
    rcases ceil_cross_high_bwd hlip hcrU hcrD L i s t' hp (by omega) hsv
        (by omega) htv' hnoY with ⟨j, k, h1, h2, h3, h4, h5⟩ | hbad
    · have hjb : i.val - j.val < i.val + 1 := by omega
      have hkb : i.val - k.val < i.val + 1 := by omega
      have hje : armT ρ i ⟨i.val - j.val, hjb⟩ = ρ j :=
        congrArg ρ (Fin.ext (by show i.val - (i.val - j.val) = j.val; omega))
      have hke : armT ρ i ⟨i.val - k.val, hkb⟩ = ρ k :=
        congrArg ρ (Fin.ext (by show i.val - (i.val - k.val) = k.val; omega))
      have h3' : i.val - d.val + 7 ≤ k.val := by omega
      exact ⟨⟨i.val - j.val, hjb⟩, ⟨i.val - k.val, hkb⟩, by simp; omega, by simp; omega,
        by simp; omega, by rw [hje]; exact h4, by rw [hke]; exact h5⟩
    · exact absurd hbad hres2
  · intro d hd
    have hdm := d.isLt
    have hdpos : 0 < d.val := by
      rcases Nat.eq_zero_or_pos d.val with h | h
      · exact absurd (congrArg (armG ρ i) (Fin.ext h : d = ⟨0, hmG⟩)) (by rw [hG0]; omega)
      · exact h
    set s : Fin n := ⟨i.val + d.val, by omega⟩ with hsdef
    have hsval : s.val = i.val + d.val := rfl
    have hsv : ρ s ≤ L + 1 := hd
    rcases ceil_cross_peak_bwd_narrow hlip hcr L i s t hp (by omega) hsv
        (by omega) htv hnoX with ⟨v, h1, h2, h3⟩ | hbad
    · have hvn := v.isLt
      have hvb : v.val - i.val < n - i.val := by omega
      have hve : armG ρ i ⟨v.val - i.val, hvb⟩ = ρ v :=
        congrArg ρ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
      have h2' : v.val + 5 ≤ i.val + d.val := by omega
      exact ⟨⟨v.val - i.val, hvb⟩, by simp; omega, by simp; omega, by rw [hve]; exact h3⟩
    · exact absurd hbad hres1

/-- **The two clauses the ceiling case needs, outside the sharpened residues.** -/
theorem ceilCrossGap_of_not_narrow_residual {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hres1 : ¬ (CeilPeakResidual ρ i L ∧ (CeilFarFlatG ρ i L ∨ CeilFarFlatT ρ i L)))
    (hres2 : ¬ CeilHighResidual ρ i L)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) :
    CeilCrossGap ρ i L :=
  ⟨fun h => ceil_gap_fwd_narrow ρ σ i L hlip hcr hLb hHb hp
      (fun hb => hres1 ⟨hb.1, Or.inl hb.2⟩) hres2 hnotLam h,
    fun h => ceil_gap_bwd_narrow ρ σ i L hlip hcr hLb hHb hp
      (fun hb => hres1 ⟨hb.1, Or.inr hb.2⟩) hres2 hnotLam h⟩

/-- **The ceiling crossing, outside the sharpened residues.** This is the work item
`cross_ceil_sentence` (`HPC/Fold/CrossCeil.lean`) for every pair of the branch at which the peak
residue does not come with a flat narrow bottom at `L + 2` on the failing arm, and at which the
high residue does not hold. It is `cross_ceil_sentence_of_not_residual` with the first exclusion
weakened. -/
theorem cross_ceil_sentence_of_not_narrow_residual {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hres1 : ¬ (CeilPeakResidual ρ i L ∧ (CeilFarFlatG ρ i L ∨ CeilFarFlatT ρ i L)))
    (hres2 : ¬ CeilHighResidual ρ i L)
    (hfail : ¬ Leg3Ceil (armG ρ i) L ∨ ¬ Leg3Ceil (armT ρ i) L)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) :
    ((MidW4 (armG ρ i) L ∧ BottomW4 (armG ρ i) L) ∧
        (MidW4 (armT ρ i) L ∧ BottomW4 (armT ρ i) L)) ∨
      ((Valley5 (armG ρ i) L ∧ TopW5 (armG ρ i) L) ∧
        (Valley5 (armT ρ i) L ∧ TopW5 (armT ρ i) L)) :=
  cross_ceil_sentence_of_gap ρ σ i L hlip hcr hLb hHb hp hfail hnotLam
    (ceilCrossGap_of_not_narrow_residual ρ σ i L hlip hcr hLb hHb hp hres1 hres2 hnotLam)

end HPC.Fold
