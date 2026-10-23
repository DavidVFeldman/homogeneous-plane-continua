import HPC.Archive.CrossValley

/-!
# Inside the valley residue

`cross_valley_dichotomy` (`HPC/Fold/CrossValley.lean`) proves the work item `cross_valley_profile`
except when the sequence stands at `L + 2` two or three steps to one side of the basepoint
(`ValleyResidual`). That residue is where most of the model is: over the corpus of
`census-batch53.c` it is realised at 267 877 branch basepoints, more than half of the cases the
item speaks of. This file asks what the *faithful* model says there, and narrows it.

The crossing needs, on the arm that does not fail, a time at `L + 2` or below at a step at least
four. What the crookedness clause returns is a time within one of the trigger level, so it reaches
`L + 2` only when the trigger is at `L + 1`; in the residue the trigger available is the `L + 2`
near the basepoint, and the clause lands at `L + 3`. That is the one-level shortfall
(`cross_valley_low3_fwd`).

The faithful model, however, fires its clause on levels *met within one step* of the anchor
(`IsCrookedIvF.crooked`), not only on the level at the anchor. So if the interval pair meets any
level at or below `L + 1` at the residual time or at either of its neighbours, the clause anchored
at the residual time returns a time at `L + 2` or below, and — because the witnesses are required
strictly between the anchors — it returns it far enough from the basepoint for the criterion. The
residue therefore only survives where the `L + 2` is *flat and narrow*: the pair meets nothing at
or below `L + 1` there or next door.

> **`cross_valley_dichotomy_narrow`.** Under the hypotheses of the work item, either both arms fold
> onto the V-walk, or `ValleyNarrowResidual` holds: the sequence stands at `L + 2` two or three
> steps to one side of the basepoint, *and* stands at `L + 2` or above at both neighbours of that
> time.

`cross_valley_profile_of_not_narrow_residual` is the work item for every pair avoiding that
configuration. It is `cross_valley_profile_of_not_residual` with a strictly weaker hypothesis:
`ValleyNarrowResidual` implies `ValleyResidual`, and `census-batch54.c` measures the gap between
them.
-/

namespace HPC.Fold

/-- **The configuration the sharpened crossing leaves open**: the sequence stands at `L + 2` two or
three steps to one side of the basepoint, and the interval pair meets no level at or below `L + 1`
there or at either neighbour. -/
def ValleyNarrowResidual {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ u : Fin n, ρ u = L + 2 ∧
    (u.val + 3 = i.val ∨ u.val + 2 = i.val ∨ u.val = i.val + 2 ∨ u.val = i.val + 3) ∧
    ∀ y : Fin n, ((y : ℤ) - (u : ℤ)).natAbs ≤ 1 → L + 2 ≤ ρ y

/-- The narrow residue is a case of the residue. -/
theorem valleyResidual_of_narrow {n : ℕ} {ρ : Fin n → ℤ} {i : Fin n} {L : ℤ}
    (h : ValleyNarrowResidual ρ i L) : ValleyResidual ρ i L := by
  obtain ⟨u, h1, h2, -⟩ := h
  exact ⟨u, h1, h2⟩

/-! ## The crossing, in global indices, sharpened -/

/-- **The crossing when the failing arm is the forward one, sharpened.** `cross_valley_low_fwd`
with the residual configuration replaced by the narrow one: where the residual time has a
neighbour at `L + 1` or below, the interval clause of the faithful model returns the low time the
criterion asks for. -/
theorem cross_valley_low_fwd_narrow {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i s t : Fin n)
    (hp : ρ i = L + 4) (hs : s.val < i.val) (hsv : L + 7 ≤ ρ s)
    (ht : i.val < t.val) (htv : ρ t ≤ L + 1)
    (hfail : ∀ w : Fin n, i.val + 3 ≤ w.val → w.val + 5 ≤ t.val → ρ w ≤ L + 4) :
    (∃ v : Fin n, s.val < v.val ∧ v.val + 4 ≤ i.val ∧ ρ v ≤ L + 2) ∨
      ValleyNarrowResidual ρ i L := by
  have hcrD := crookDown_seq hcr
  obtain ⟨u, u', hsu, huu', hu't, hu1, hu2, hu3, hu4⟩ := hcrD s t (by omega) (by omega)
  have hulow : ρ u ≤ L + 2 := by omega
  have hu'hi : L + 5 ≤ ρ u' := by omega
  have hfall : u'.val + 7 ≤ t.val := crookDown_fall4 hlip hcrD u' t (by omega) (by omega)
  have hu'lt : u'.val < i.val + 3 := by
    by_contra hc
    have := hfail u' (by omega) (by omega)
    omega
  have hult : u.val < i.val := by
    by_contra hc
    have hd := abs_sub_le_of_isLip hlip (u.val - i.val) i u (by omega)
    rw [abs_le] at hd
    have hcast : ((u.val - i.val : ℕ) : ℤ) = (u.val : ℤ) - (i.val : ℤ) := by
      push_cast [Nat.cast_sub (by omega : i.val ≤ u.val)]; ring
    rw [hcast] at hd
    omega
  by_cases hfar : u.val + 4 ≤ i.val
  · exact Or.inl ⟨u, by omega, hfar, hulow⟩
  · have hd := abs_sub_le_of_isLip hlip (i.val - u.val) u i (by omega)
    rw [abs_le] at hd
    have hcast : ((i.val - u.val : ℕ) : ℤ) = (i.val : ℤ) - (u.val : ℤ) := by
      push_cast [Nat.cast_sub (by omega : u.val ≤ i.val)]; ring
    rw [hcast] at hd
    by_cases hu2' : ρ u = L + 2
    · by_cases hnar : ∀ y : Fin n, ((y : ℤ) - (u : ℤ)).natAbs ≤ 1 → L + 2 ≤ ρ y
      · exact Or.inr ⟨u, hu2', by omega, hnar⟩
      · -- a neighbour at `L + 1` or below: the interval clause fires on it
        push_neg at hnar
        obtain ⟨y, hy, hyv⟩ := hnar
        have hsu' : s.val < u.val := hsu
        obtain ⟨r, r', hsr, hrr', hru, -, hcase⟩ :=
          hcr.crooked s u (Fin.lt_def.mpr hsu') (ρ s) (ρ y)
            ⟨s, by simp, le_refl _, hcr.le _⟩ ⟨y, hy, le_refl _, hcr.le _⟩
            (by rw [abs_of_nonneg] <;> omega)
        obtain ⟨⟨hr1, -⟩, -⟩ := hcase (by omega)
        have hsr' : s.val < r.val := Fin.lt_def.mp hsr
        have hrr'' : r.val < r'.val := Fin.lt_def.mp hrr'
        have hru' : r'.val < u.val := Fin.lt_def.mp hru
        exact Or.inl ⟨r, hsr', by omega, by omega⟩
    · -- `ρ u ≤ L + 1`: the clause applied a second time gives a genuine low time
      obtain ⟨v, v', hsv', hvv', hvu, hv1, hv2, hv3, hv4⟩ := hcrD s u (by omega) (by omega)
      exact Or.inl ⟨v, by omega, by omega, by omega⟩

/-- **The crossing when the failing arm is the backward one, sharpened**, the mirror of
`cross_valley_low_fwd_narrow`. -/
theorem cross_valley_low_bwd_narrow {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i s t : Fin n)
    (hp : ρ i = L + 4) (hs : i.val < s.val) (hsv : L + 7 ≤ ρ s)
    (ht : t.val < i.val) (htv : ρ t ≤ L + 1)
    (hfail : ∀ w : Fin n, w.val + 3 ≤ i.val → t.val + 5 ≤ w.val → ρ w ≤ L + 4) :
    (∃ v : Fin n, v.val < s.val ∧ i.val + 4 ≤ v.val ∧ ρ v ≤ L + 2) ∨
      ValleyNarrowResidual ρ i L := by
  have hcrU := crookUp_seq hcr
  obtain ⟨u, u', htu, huu', hu's, hu1, hu2, hu3, hu4⟩ := hcrU t s (by omega) (by omega)
  have huhi : L + 5 ≤ ρ u := by omega
  have hu'low : ρ u' ≤ L + 2 := by omega
  have hclimb : t.val + 7 ≤ u.val := crookUp_climb4 hlip hcrU t u (by omega) (by omega)
  have hugt : i.val < u.val + 3 := by
    by_contra hc
    have := hfail u (by omega) (by omega)
    omega
  have hu'gt : i.val < u'.val := by
    by_contra hc
    have hd := abs_sub_le_of_isLip hlip (i.val - u'.val) u' i (by omega)
    rw [abs_le] at hd
    have hcast : ((i.val - u'.val : ℕ) : ℤ) = (i.val : ℤ) - (u'.val : ℤ) := by
      push_cast [Nat.cast_sub (by omega : u'.val ≤ i.val)]; ring
    rw [hcast] at hd
    omega
  have hd := abs_sub_le_of_isLip hlip (u'.val - i.val) i u' (by omega)
  rw [abs_le] at hd
  have hcast : ((u'.val - i.val : ℕ) : ℤ) = (u'.val : ℤ) - (i.val : ℤ) := by
    push_cast [Nat.cast_sub (by omega : i.val ≤ u'.val)]; ring
  rw [hcast] at hd
  by_cases hfar : i.val + 4 ≤ u'.val
  · exact Or.inl ⟨u', by omega, hfar, hu'low⟩
  · by_cases hu2' : ρ u' = L + 2
    · by_cases hnar : ∀ y : Fin n, ((y : ℤ) - (u' : ℤ)).natAbs ≤ 1 → L + 2 ≤ ρ y
      · exact Or.inr ⟨u', hu2', by omega, hnar⟩
      · push_neg at hnar
        obtain ⟨y, hy, hyv⟩ := hnar
        have hu's' : u'.val < s.val := hu's
        obtain ⟨r, r', hu'r, hrr', hrs, hcase, -⟩ :=
          hcr.crooked u' s (Fin.lt_def.mpr hu's') (ρ y) (ρ s)
            ⟨y, hy, le_refl _, hcr.le _⟩ ⟨s, by simp, le_refl _, hcr.le _⟩
            (by rw [abs_of_nonpos] <;> omega)
        obtain ⟨-, hr'1, -⟩ := hcase (by omega)
        have hu'r' : u'.val < r.val := Fin.lt_def.mp hu'r
        have hrr'' : r.val < r'.val := Fin.lt_def.mp hrr'
        have hrs' : r'.val < s.val := Fin.lt_def.mp hrs
        exact Or.inl ⟨r', hrs', by omega, by omega⟩
    · obtain ⟨w, w', huw, hww', hw's, hw1, hw2, hw3, hw4⟩ := hcrU u' s (by omega) (by omega)
      exact Or.inl ⟨w', by omega, by omega, by omega⟩

/-! ## The criteria on the arms, with the sharpened residue -/

/-- The V-criterion for the backward arm, when the forward arm fails the valley clause, with the
narrow residue excluded. -/
theorem critVee_armT_of_fail_armG_narrow {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i : Fin n) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Valley (armG ρ i) L) (hres : ¬ ValleyNarrowResidual ρ i L) :
    ∀ e : Fin (i.val + 1), L + 7 ≤ armT ρ i e →
      ∃ j : Fin (i.val + 1), j.val < e.val ∧ 4 ≤ j.val ∧ armT ρ i j ≤ L + 2 := by
  have hi := i.isLt
  -- the failing descent, read globally
  rw [Leg3Valley] at hfail
  push_neg at hfail
  obtain ⟨d₀, hd₀v, hd₀no⟩ := hfail
  have hd₀m := d₀.isLt
  set t : Fin n := ⟨i.val + d₀.val, by omega⟩ with htdef
  have htval : t.val = i.val + d₀.val := rfl
  have htv : ρ t ≤ L + 1 := hd₀v
  have hd₀pos : 0 < d₀.val := by
    by_contra hc
    have hti : t = i := Fin.ext (by omega)
    rw [hti, hp] at htv
    omega
  have hfailg : ∀ w : Fin n, i.val + 3 ≤ w.val → w.val + 5 ≤ t.val → ρ w ≤ L + 4 := by
    intro w h1 h2
    have hwn := w.isLt
    have hw : w.val - i.val < n - i.val := by omega
    have := hd₀no ⟨w.val - i.val, hw⟩ (show 3 ≤ w.val - i.val by omega)
      (show w.val - i.val + 5 ≤ d₀.val by omega)
    have heq : armG ρ i ⟨w.val - i.val, hw⟩ = ρ w := by
      show ρ ⟨i.val + (w.val - i.val), _⟩ = ρ w
      exact congrArg ρ (Fin.ext (by show i.val + (w.val - i.val) = w.val; omega))
    rw [heq] at this
    omega
  intro e he
  have hem := e.isLt
  set s : Fin n := ⟨i.val - e.val, by omega⟩ with hsdef
  have hsval : s.val = i.val - e.val := rfl
  have hsv : L + 7 ≤ ρ s := he
  have hepos : 0 < e.val := by
    by_contra hc
    have hsi : s = i := Fin.ext (by omega)
    rw [hsi, hp] at hsv
    omega
  rcases cross_valley_low_fwd_narrow hlip hcr L i s t hp (by omega) hsv (by omega) htv
      hfailg with ⟨v, hv1, hv2, hv3⟩ | hbad
  · have hvn := v.isLt
    refine ⟨⟨i.val - v.val, by omega⟩, by simp; omega, by simp; omega, ?_⟩
    have heq : armT ρ i ⟨i.val - v.val, by omega⟩ = ρ v := by
      show ρ ⟨i.val - (i.val - v.val), _⟩ = ρ v
      exact congrArg ρ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
    rw [heq]; exact hv3
  · exact absurd hbad hres

/-- The V-criterion for the forward arm, when the backward arm fails the valley clause, with the
narrow residue excluded. -/
theorem critVee_armG_of_fail_armT_narrow {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i : Fin n) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Valley (armT ρ i) L) (hres : ¬ ValleyNarrowResidual ρ i L) :
    ∀ e : Fin (n - i.val), L + 7 ≤ armG ρ i e →
      ∃ j : Fin (n - i.val), j.val < e.val ∧ 4 ≤ j.val ∧ armG ρ i j ≤ L + 2 := by
  have hi := i.isLt
  rw [Leg3Valley] at hfail
  push_neg at hfail
  obtain ⟨d₀, hd₀v, hd₀no⟩ := hfail
  have hd₀m := d₀.isLt
  set t : Fin n := ⟨i.val - d₀.val, by omega⟩ with htdef
  have htval : t.val = i.val - d₀.val := rfl
  have htv : ρ t ≤ L + 1 := hd₀v
  have hd₀pos : 0 < d₀.val := by
    by_contra hc
    have hti : t = i := Fin.ext (by omega)
    rw [hti, hp] at htv
    omega
  have hfailg : ∀ w : Fin n, w.val + 3 ≤ i.val → t.val + 5 ≤ w.val → ρ w ≤ L + 4 := by
    intro w h1 h2
    have hwn := w.isLt
    have hw : i.val - w.val < i.val + 1 := by omega
    have := hd₀no ⟨i.val - w.val, hw⟩ (show 3 ≤ i.val - w.val by omega)
      (show i.val - w.val + 5 ≤ d₀.val by omega)
    have heq : armT ρ i ⟨i.val - w.val, hw⟩ = ρ w := by
      show ρ ⟨i.val - (i.val - w.val), _⟩ = ρ w
      exact congrArg ρ (Fin.ext (by show i.val - (i.val - w.val) = w.val; omega))
    rw [heq] at this
    omega
  intro e he
  have hem := e.isLt
  set s : Fin n := ⟨i.val + e.val, by omega⟩ with hsdef
  have hsval : s.val = i.val + e.val := rfl
  have hsv : L + 7 ≤ ρ s := he
  have hepos : 0 < e.val := by
    by_contra hc
    have hsi : s = i := Fin.ext (by omega)
    rw [hsi, hp] at hsv
    omega
  rcases cross_valley_low_bwd_narrow hlip hcr L i s t hp (by omega) hsv (by omega) htv
      hfailg with ⟨v, hv1, hv2, hv3⟩ | hbad
  · have hvn := v.isLt
    refine ⟨⟨v.val - i.val, by omega⟩, by simp; omega, by simp; omega, ?_⟩
    have heq : armG ρ i ⟨v.val - i.val, by omega⟩ = ρ v := by
      show ρ ⟨i.val + (v.val - i.val), _⟩ = ρ v
      exact congrArg ρ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
    rw [heq]; exact hv3
  · exact absurd hbad hres

/-! ## The dichotomy, sharpened -/

/-- **The valley crossing, except in the narrow configuration.** Under the hypotheses of the work
item `cross_valley_profile`, either both arms fold onto the V-walk — its conclusion — or the
sequence stands at `L + 2` two or three steps to one side of the basepoint and at `L + 2` or above
at both neighbours of that time.

Of the work item's hypotheses, the two `HighAt` clauses and both ends of the band are not used. -/
theorem cross_valley_dichotomy_narrow {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Valley (armG ρ i) L ∨ ¬ Leg3Valley (armT ρ i) L) :
    (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
        FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) ∨
      ValleyNarrowResidual ρ i L := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  by_cases hres : ValleyNarrowResidual ρ i L
  · exact Or.inr hres
  refine Or.inl ?_
  rcases hfail with hfG | hfT
  · have hvT : FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
      refine (foldsOnto_vee_iff_profile hmT (armT ρ i) (armT_isLip hlip i) (L + 5) (L + 9) L
        (by omega) (by rw [hT0, abs_le]; omega) (fun j => hLb _) (fun j => hHb _)).mpr ?_
      rw [critVeeProfile_iff_of_isLip (armT_isLip hlip i) (L + 5) L (by omega)]
      intro d hd
      obtain ⟨j, hj1, hj2, hj3⟩ := critVee_armT_of_fail_armG_narrow hlip hcr L i hp hfG hres d (by omega)
      exact ⟨j, hj1, by omega, hj3⟩
    refine ⟨?_, hvT⟩
    rcases leg3Valley_or_vee hmG (armG ρ i) (armG_isLip hlip i) (crookDown_armG hcr i) L hG0
      (fun j => hLb _) (fun j => hHb _) with h | h
    · exact absurd h hfG
    · exact h
  · have hvG : FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
      refine (foldsOnto_vee_iff_profile hmG (armG ρ i) (armG_isLip hlip i) (L + 5) (L + 9) L
        (by omega) (by rw [hG0, abs_le]; omega) (fun j => hLb _) (fun j => hHb _)).mpr ?_
      rw [critVeeProfile_iff_of_isLip (armG_isLip hlip i) (L + 5) L (by omega)]
      intro d hd
      obtain ⟨j, hj1, hj2, hj3⟩ := critVee_armG_of_fail_armT_narrow hlip hcr L i hp hfT hres d (by omega)
      exact ⟨j, hj1, by omega, hj3⟩
    refine ⟨hvG, ?_⟩
    rcases leg3Valley_or_vee hmT (armT ρ i) (armT_isLip hlip i) (crookDown_armT hcr i) L hT0
      (fun j => hLb _) (fun j => hHb _) with h | h
    · exact absurd h hfT
    · exact h

/-- **The work item, for every pair that avoids the narrow configuration.** This is
`cross_valley_profile` with one extra hypothesis, and the hypothesis is strictly weaker than the
one of `cross_valley_profile_of_not_residual`. -/
theorem cross_valley_profile_of_not_narrow_residual {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4)
    (hres : ¬ ValleyNarrowResidual ρ i L)
    (hfail : ¬ Leg3Valley (armG ρ i) L ∨ ¬ Leg3Valley (armT ρ i) L) :
    FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
  rcases cross_valley_dichotomy_narrow ρ σ i L hlip hcr hLb hHb hp hfail with h | h
  · exact h
  · exact absurd h hres

end HPC.Fold
