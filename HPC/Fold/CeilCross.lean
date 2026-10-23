import HPC.Fold.CeilArm

/-!
# The ceiling crossing, and the two configurations it leaves

`HPC/Fold/CeilArm.lean` reduces the work item `cross_ceil_sentence` to `CeilCrossGap`: in the
configuration of the item, with `X` the arm failing `Leg3Ceil` and `Y` the other one, the sentence
of `w₅` needs exactly two more clauses, `TopW5 X` and `Valley5 Y`. This file proves both of them
across the basepoint, except in two configurations, which it names — the ceiling counterpart of
`cross_valley_dichotomy` (`HPC/Fold/CrossValley.lean`).

Writing `i` for the basepoint:

> **`ceil_cross_peak_fwd`, `ceil_cross_peak_bwd`.** `Valley5` holds of the arm that does not fail
> `Leg3Ceil`, unless `ρ` stands at `L + 6` or above two or three steps to one side of the
> basepoint (`CeilPeakResidual`).
>
> **`ceil_cross_high_fwd`, `ceil_cross_high_bwd`.** `TopW5` holds of the arm that fails
> `Leg3Ceil`, unless `ρ` stands at `L + 7` or above exactly four steps to one side of the
> basepoint (`CeilHighResidual`).

Both are one application of `CrookUp` read across the basepoint, between the descent one arm
supplies and the ascent the other one supplies, followed by the timing laws:

* for the valley clause the descent is the failure of `Valley5` on `Y` and the ascent is the
  unprepared `L + 8` of `X`; the clause returns a peak at `L + 6` and a time at `L + 2` after it,
  and on `X`'s side the two are exactly the landmarks `Leg3Ceil` asks for — which `X` does not
  have — so the peak lies on `Y`'s side, where the only thing that can go wrong is that it lies
  too near the basepoint for the index bound of `Valley5`;
* for the ceiling clause the descent is the one at which `Y` fails to fold onto the Λ-walk and the
  ascent is the time at `L + 9` at which `TopW5` fails on `X`; the clause returns a peak at
  `L + 7`, which on `X`'s side is the landmark `TopW5` asks for and on `Y`'s side is the peak the
  Λ-criterion asks for, so again only its index can go wrong, and only at distance exactly four.

With both residues excluded the work item is a theorem:
`cross_ceil_sentence_of_not_residual`.
-/

namespace HPC.Fold

/-! ## The two configurations -/

/-- **The configuration the valley half of the ceiling crossing leaves open**: the sequence stands
at `L + 6` or above two or three steps to one side of the basepoint. It is the only way the peak
the crookedness clause returns can fail to be the peak `Valley5` asks for. -/
def CeilPeakResidual {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ u : Fin n, (u.val + 2 = i.val ∨ u.val + 3 = i.val ∨ u.val = i.val + 2 ∨ u.val = i.val + 3) ∧
    L + 6 ≤ ρ u

/-- **The configuration the ceiling half leaves open**: the sequence stands at `L + 7` or above
exactly four steps to one side of the basepoint. Four steps is the shortest climb of three levels
the clause `CrookUp` allows, and the Λ-criterion asks for five. -/
def CeilHighResidual {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ u : Fin n, (u.val + 4 = i.val ∨ u.val = i.val + 4) ∧ L + 7 ≤ ρ u

/-! ## The valley half, in global indices -/

/-- **The valley clause crosses the basepoint, forward form.** The failing arm is the forward one:
its unprepared ascent is `t`, and `s` is a descent to `L + 1` on the backward arm. Then the
sequence stands at `L + 6` or above at a time at least twelve steps after `s` and at least four
steps before the basepoint — unless the residual configuration holds. -/
theorem ceil_cross_peak_fwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ) (hcrU : CrookUp ρ)
    (hcrD : CrookDown ρ) (L : ℤ) (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : s.val < i.val) (hsv : ρ s ≤ L + 1)
    (ht : i.val < t.val) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, i.val + 3 ≤ j.val → j.val + 5 ≤ k.val → k.val + 6 ≤ t.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    (∃ v : Fin n, s.val + 12 ≤ v.val ∧ v.val + 4 ≤ i.val ∧ L + 6 ≤ ρ v) ∨
      CeilPeakResidual ρ i L := by
  obtain ⟨u, u', hsu, huu', hu't, hu, hu'⟩ :=
    hcrU.levels (L + 1) (L + 8) (by omega) s t (by omega) hsv htv
  have hfall : u.val + 7 ≤ u'.val := crookDown_fall4 hlip hcrD u u' huu' (by omega)
  have hclimb : u'.val + 12 ≤ t.val := crookUp_climb5 hlip hcrU u' t hu't (by omega)
  have hsu12 : s.val + 12 ≤ u.val := crookUp_climb5 hlip hcrU s u hsu (by omega)
  -- the peak is at least two steps from the basepoint
  have hnear : 2 ≤ (i.val : ℤ) - (u.val : ℤ) ∨ 2 ≤ (u.val : ℤ) - (i.val : ℤ) := by
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
  rcases lt_or_ge u.val i.val with hui | hui
  · -- the peak lies on the backward arm
    by_cases hfar : u.val + 4 ≤ i.val
    · exact Or.inl ⟨u, hsu12, hfar, by omega⟩
    · exact Or.inr ⟨u, by omega, by omega⟩
  · -- the peak lies on the forward arm: the two landmarks are the ones `Leg3Ceil` asks for
    exfalso
    by_cases hthree : i.val + 3 ≤ u.val
    · exact absurd (hnoX u u' hthree (by omega) (by omega) (by omega)) (by omega)
    · -- the peak is exactly two steps after the basepoint, and the next step is at `L + 5`
      have hu2 : u.val = i.val + 2 := by omega
      have hlt : i.val + 3 < n := by omega
      set j : Fin n := ⟨i.val + 3, hlt⟩ with hjdef
      have hju : |ρ j - ρ u| ≤ 1 := by
        have := abs_sub_le_of_isLip hlip 1 u j (by simp [hjdef]; omega)
        simpa using this
      rw [abs_le] at hju
      exact absurd (hnoX j u' (by simp [hjdef]) (by simp [hjdef]; omega) (by omega) (by omega))
        (by omega)

/-- **The valley clause crosses the basepoint, backward form**, the mirror of
`ceil_cross_peak_fwd`: the failing arm is the backward one, its unprepared ascent is `t` before
the basepoint and `s` is a descent on the forward arm. -/
theorem ceil_cross_peak_bwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ) (hcrU : CrookUp ρ)
    (hcrD : CrookDown ρ) (L : ℤ) (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : i.val < s.val) (hsv : ρ s ≤ L + 1)
    (ht : t.val < i.val) (htv : L + 8 ≤ ρ t)
    (hnoX : ∀ j k : Fin n, j.val + 3 ≤ i.val → k.val + 5 ≤ j.val → t.val + 6 ≤ k.val →
      L + 5 ≤ ρ j → L + 2 < ρ k) :
    (∃ v : Fin n, i.val + 4 ≤ v.val ∧ v.val + 5 ≤ s.val ∧ L + 6 ≤ ρ v) ∨
      CeilPeakResidual ρ i L := by
  -- the ascent comes first and the descent after it, so the clause read is `CrookDown`
  obtain ⟨u, u', htu, huu', hu's, hu, hu'⟩ :=
    hcrD.levels (L + 1) (L + 8) (by omega) t s (by omega) htv hsv
  have hclimb : u.val + 7 ≤ u'.val := crookUp_climb4 hlip hcrU u u' huu' (by omega)
  have hfall : t.val + 7 ≤ u.val := crookDown_fall4 hlip hcrD t u htu (by omega)
  rcases lt_trichotomy u'.val i.val with hui | hui | hui
  · -- the peak lies on the backward arm: with the low landmark it is what `Leg3Ceil` asks for
    exfalso
    by_cases hthree : u'.val + 3 ≤ i.val
    · exact absurd (hnoX u' u hthree (by omega) (by omega) (by omega)) (by omega)
    · -- the peak is exactly two steps before the basepoint, and the step before it is at `L + 5`
      have hu2 : u'.val + 2 = i.val := by
        have hd := abs_sub_le_of_isLip hlip (i.val - u'.val) u' i (by omega)
        rw [abs_le] at hd
        have hc : ((i.val - u'.val : ℕ) : ℤ) = (i.val : ℤ) - (u'.val : ℤ) := by
          push_cast [Nat.cast_sub (le_of_lt hui)]; ring
        rw [hc] at hd; omega
      have hlt : i.val - 3 < n := by omega
      set j : Fin n := ⟨i.val - 3, hlt⟩ with hjdef
      have hju : |ρ j - ρ u'| ≤ 1 := by
        have := abs_sub_le_of_isLip hlip 1 j u' (by simp [hjdef]; omega)
        rw [abs_sub_comm] at this
        simpa using this
      rw [abs_le] at hju
      exact absurd (hnoX j u (by simp [hjdef]; omega) (by simp [hjdef]; omega) (by omega)
        (by omega)) (by omega)
  · exact absurd (congrArg ρ (Fin.ext hui : u' = i)) (by omega)
  · -- the peak lies on the forward arm
    have hfall5 : u'.val + 7 ≤ s.val := crookDown_fall4 hlip hcrD u' s hu's (by omega)
    by_cases hfar : i.val + 4 ≤ u'.val
    · exact Or.inl ⟨u', hfar, by omega, by omega⟩
    · have hd := abs_sub_le_of_isLip hlip (u'.val - i.val) i u' (by omega)
      rw [abs_le] at hd
      have hc : ((u'.val - i.val : ℕ) : ℤ) = (u'.val : ℤ) - (i.val : ℤ) := by
        push_cast [Nat.cast_sub (le_of_lt hui)]; ring
      rw [hc] at hd
      exact Or.inr ⟨u', by omega, by omega⟩

/-! ## The ceiling half, in global indices -/

/-- **The ceiling clause crosses the basepoint, forward form.** `t` is a time at `L + 9` on the
forward arm and `s` a descent to `L + 1` on the backward arm at which the Λ-criterion fails. Then
the two landmarks `TopW5` asks for lie on the forward arm — unless the sequence stands at `L + 7`
exactly four steps before the basepoint. -/
theorem ceil_cross_high_fwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ) (hcrU : CrookUp ρ)
    (hcrD : CrookDown ρ) (L : ℤ) (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : s.val < i.val) (hsv : ρ s ≤ L + 1)
    (ht : i.val < t.val) (htv : L + 9 ≤ ρ t)
    (hnoY : ∀ v : Fin n, s.val < v.val → v.val + 5 ≤ i.val → ρ v ≤ L + 6) :
    (∃ j k : Fin n, i.val + 4 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val + 7 ≤ t.val ∧
        L + 6 ≤ ρ j ∧ ρ k ≤ L + 2) ∨
      CeilHighResidual ρ i L := by
  obtain ⟨u, u', hsu, huu', hu't, hu, hu'⟩ :=
    hcrU.levels (L + 1) (L + 9) (by omega) s t (by omega) hsv htv
  have hfall : u.val + 7 ≤ u'.val := crookDown_fall4 hlip hcrD u u' huu' (by omega)
  have hclimb : u'.val + 12 ≤ t.val := crookUp_climb5 hlip hcrU u' t hu't (by omega)
  rcases lt_trichotomy u.val i.val with hui | hui | hui
  · -- the peak lies on the backward arm: it is the peak the Λ-criterion asks for
    have hfour : u.val + 4 ≤ i.val := crookDown_fall3 hlip hcrD u i hui (by omega)
    by_cases hfive : u.val + 5 ≤ i.val
    · exact absurd (hnoY u hsu hfive) (by omega)
    · exact Or.inr ⟨u, by omega, by omega⟩
  · exact absurd (congrArg ρ (Fin.ext hui : u = i)) (by omega)
  · -- the peak lies on the forward arm: the two landmarks are the ones `TopW5` asks for
    have hfour : i.val + 4 ≤ u.val := crookUp_climb3 hlip hcrU i u hui (by omega)
    exact Or.inl ⟨u, u', hfour, by omega, by omega, by omega, by omega⟩

/-- **The ceiling clause crosses the basepoint, backward form**, the mirror of
`ceil_cross_high_fwd`: `t` is a time at `L + 9` on the backward arm and `s` a descent to `L + 1`
on the forward arm at which the Λ-criterion fails. -/
theorem ceil_cross_high_bwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ) (hcrU : CrookUp ρ)
    (hcrD : CrookDown ρ) (L : ℤ) (i s t : Fin n) (hp : ρ i = L + 4)
    (hs : i.val < s.val) (hsv : ρ s ≤ L + 1)
    (ht : t.val < i.val) (htv : L + 9 ≤ ρ t)
    (hnoY : ∀ v : Fin n, v.val < s.val → i.val + 5 ≤ v.val → ρ v ≤ L + 6) :
    (∃ j k : Fin n, j.val + 4 ≤ i.val ∧ k.val + 6 ≤ j.val ∧ t.val + 7 ≤ k.val ∧
        L + 6 ≤ ρ j ∧ ρ k ≤ L + 2) ∨
      CeilHighResidual ρ i L := by
  obtain ⟨u, u', htu, huu', hu's, hu, hu'⟩ :=
    hcrD.levels (L + 1) (L + 9) (by omega) t s (by omega) htv hsv
  have hclimb : u.val + 12 ≤ u'.val := crookUp_climb5 hlip hcrU u u' huu' (by omega)
  have hfall : t.val + 7 ≤ u.val := crookDown_fall4 hlip hcrD t u htu (by omega)
  rcases lt_trichotomy u'.val i.val with hui | hui | hui
  · -- the peak lies on the backward arm: the two landmarks are the ones `TopW5` asks for
    have hfour : u'.val + 4 ≤ i.val := crookDown_fall3 hlip hcrD u' i hui (by omega)
    exact Or.inl ⟨u', u, hfour, by omega, by omega, by omega, by omega⟩
  · exact absurd (congrArg ρ (Fin.ext hui : u' = i)) (by omega)
  · -- the peak lies on the forward arm: it is the peak the Λ-criterion asks for
    have hfour : i.val + 4 ≤ u'.val := crookUp_climb3 hlip hcrU i u' hui (by omega)
    by_cases hfive : i.val + 5 ≤ u'.val
    · exact absurd (hnoY u' hu's hfive) (by omega)
    · exact Or.inr ⟨u', by omega, by omega⟩

/-! ## The gap, on the arms -/

/-- **The ceiling crossing on the arms, forward form.** If the forward arm fails `Leg3Ceil` and
the pair does not fold onto the Λ-walk, then — outside the two residual configurations — the
forward arm satisfies `TopW5` and the backward arm satisfies `Valley5`. -/
theorem ceil_gap_fwd {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hres1 : ¬ CeilPeakResidual ρ i L) (hres2 : ¬ CeilHighResidual ρ i L)
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
    rcases ceil_cross_peak_fwd hlip hcrU hcrD L i s t hp (by omega) hsv
        (by omega) htv hnoX with ⟨v, h1, h2, h3⟩ | hbad
    · have hvn := v.isLt
      have hvb : i.val - v.val < i.val + 1 := by omega
      have hve : armT ρ i ⟨i.val - v.val, hvb⟩ = ρ v :=
        congrArg ρ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
      have h1' : i.val - d.val + 12 ≤ v.val := by omega
      exact ⟨⟨i.val - v.val, hvb⟩, by simp; omega, by simp; omega, by rw [hve]; exact h3⟩
    · exact absurd hbad hres1

/-- **The ceiling crossing on the arms, backward form**, the mirror of `ceil_gap_fwd`. -/
theorem ceil_gap_bwd {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hres1 : ¬ CeilPeakResidual ρ i L) (hres2 : ¬ CeilHighResidual ρ i L)
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
    rcases ceil_cross_peak_bwd hlip hcrU hcrD L i s t hp (by omega) hsv
        (by omega) htv hnoX with ⟨v, h1, h2, h3⟩ | hbad
    · have hvn := v.isLt
      have hvb : v.val - i.val < n - i.val := by omega
      have hve : armG ρ i ⟨v.val - i.val, hvb⟩ = ρ v :=
        congrArg ρ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
      have h2' : v.val + 5 ≤ i.val + d.val := by omega
      exact ⟨⟨v.val - i.val, hvb⟩, by simp; omega, by simp; omega, by rw [hve]; exact h3⟩
    · exact absurd hbad hres1

/-- **The two clauses the ceiling case needs, outside the two residual configurations.** -/
theorem ceilCrossGap_of_not_residual {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hres1 : ¬ CeilPeakResidual ρ i L) (hres2 : ¬ CeilHighResidual ρ i L)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) :
    CeilCrossGap ρ i L :=
  ⟨fun h => ceil_gap_fwd ρ σ i L hlip hcr hLb hHb hp hres1 hres2 hnotLam h,
    fun h => ceil_gap_bwd ρ σ i L hlip hcr hLb hHb hp hres1 hres2 hnotLam h⟩

/-- **The ceiling crossing, outside the two residual configurations.** This is the work item
`cross_ceil_sentence` (`HPC/Fold/CrossCeil.lean`) with two hypotheses about the four steps either
side of the basepoint, and with the second disjunct: both arms satisfy the sentence of `w₅`. -/
theorem cross_ceil_sentence_of_not_residual {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hres1 : ¬ CeilPeakResidual ρ i L) (hres2 : ¬ CeilHighResidual ρ i L)
    (hfail : ¬ Leg3Ceil (armG ρ i) L ∨ ¬ Leg3Ceil (armT ρ i) L)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L))) :
    ((MidW4 (armG ρ i) L ∧ BottomW4 (armG ρ i) L) ∧
        (MidW4 (armT ρ i) L ∧ BottomW4 (armT ρ i) L)) ∨
      ((Valley5 (armG ρ i) L ∧ TopW5 (armG ρ i) L) ∧
        (Valley5 (armT ρ i) L ∧ TopW5 (armT ρ i) L)) :=
  cross_ceil_sentence_of_gap ρ σ i L hlip hcr hLb hHb hp hfail hnotLam
    (ceilCrossGap_of_not_residual ρ σ i L hlip hcr hLb hHb hp hres1 hres2 hnotLam)

end HPC.Fold
