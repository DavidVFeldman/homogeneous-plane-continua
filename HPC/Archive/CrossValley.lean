import HPC.Fold.Mixed
import HPC.Fold.LandmarkW

/-!
# The valley crossing, and the one case it leaves

`cross_valley_profile` (`HPC/Fold/Mixed.lean`) is the standing work item of the branch `L + 4` that
says a valley failure crosses the basepoint: if either arm of a branch pair fails `Leg3Valley`,
then *both* arms fold onto the V-walk based at `L + 5`. The arm that fails folds onto it by itself
(`leg3Valley_or_vee`, batch 48), so the content is about the other arm, and by the exact criterion
of `HPC/Fold/Profile.lean` what the other arm needs is this: **before every time at `L + 7` or
above it must stand at `L + 2` or below at a step at least four.**

This file proves that it does, except in one configuration, which it names. Writing `i` for the
basepoint:

> **`cross_valley_dichotomy`.** Under the hypotheses of the work item, either both arms fold onto
> the V-walk — the work item's conclusion — or `ρ` takes the value `L + 2` at one of the four times
> `i − 3`, `i − 2`, `i + 2`, `i + 3` (`ValleyResidual`).

So the work item is a theorem for every pair whose sequence avoids `L + 2` at those four times
(`cross_valley_profile_of_not_residual`), and what is left of it is a statement about the three
steps either side of the basepoint. That is the case REPORT-batch49.md §2.2 identified in prose;
here it is identified by a machine-checked theorem, and the analysis behind it is
`cross_valley_low_fwd` and `cross_valley_low_bwd`.

## The argument

Let `X` be the arm that fails `Leg3Valley`, at a descent to `L + 1`, and `Y` the other arm, at an
ascent to `L + 7`. The crookedness clause read across the basepoint (`crookUp_seq`,
`crookDown_seq`) returns, between the ascent and the descent, a time `u` within one of the low
level and a time `u'` within one of the high level.

* If `u` lies four steps or more from the basepoint on `Y`'s side, it is exactly the low time the
  criterion wants, and `Y` folds.
* Otherwise the high time `u'` is pinned: the timing law (`crookDown_fall4`, `crookUp_climb4` — a
  fall or climb of four levels needs seven steps) keeps it away from `X`'s descent, and the failure
  of `Leg3Valley` keeps it out of the window `[3, d₀ − 5]` of `X`. So `u'` sits within two or three
  steps of the basepoint, and `u` within three of it on `Y`'s side.
* Being that close to a basepoint at `L + 4`, `u` is at `L + 1` or `L + 2` by the Lipschitz bound.
  If it is at `L + 1` or below, a *second* application of the clause, between `Y`'s ascent and `u`,
  returns a time at `L + 2` or below far enough back, and `Y` folds after all.
* What is left is `ρ u = L + 2` exactly, with `u` three or two steps before the basepoint (or two
  or three after it, in the mirrored configuration). That is `ValleyResidual`, and there the second
  application returns only a time at `L + 3`: the general model's one-level shortfall, and the
  whole of what the work item still waits on.
-/

namespace HPC.Fold

/-! ## The residual configuration -/

/-- **The configuration the crossing leaves open**: the sequence stands at `L + 2` two or three
steps either side of the basepoint. It is the only way the low time the crookedness clause returns
can fail to be the low time the V-criterion asks for. -/
def ValleyResidual {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  ∃ u : Fin n, ρ u = L + 2 ∧
    (u.val + 3 = i.val ∨ u.val + 2 = i.val ∨ u.val = i.val + 2 ∨ u.val = i.val + 3)

/-! ## The crossing, in global indices -/

/-- **The crossing when the failing arm is the forward one.** Given an ascent `s` before the
basepoint and a descent `t` after it whose valley clause fails, the sequence stands at `L + 2` or
below at a time strictly after `s` and at least four steps before the basepoint — unless the
residual configuration holds. -/
theorem cross_valley_low_fwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcrD : CrookDown ρ) (L : ℤ) (i s t : Fin n)
    (hp : ρ i = L + 4) (hs : s.val < i.val) (hsv : L + 7 ≤ ρ s)
    (ht : i.val < t.val) (htv : ρ t ≤ L + 1)
    (hfail : ∀ w : Fin n, i.val + 3 ≤ w.val → w.val + 5 ≤ t.val → ρ w ≤ L + 4) :
    (∃ v : Fin n, s.val < v.val ∧ v.val + 4 ≤ i.val ∧ ρ v ≤ L + 2) ∨ ValleyResidual ρ i L := by
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
    · exact Or.inr ⟨u, hu2', by omega⟩
    · -- `ρ u ≤ L + 1`: the clause applied a second time gives a genuine low time
      obtain ⟨v, v', hsv', hvv', hvu, hv1, hv2, hv3, hv4⟩ := hcrD s u (by omega) (by omega)
      exact Or.inl ⟨v, by omega, by omega, by omega⟩

/-- **The crossing when the failing arm is the backward one**, the mirror of
`cross_valley_low_fwd`: the ascent `s` is after the basepoint and the failing descent `t` before
it. -/
theorem cross_valley_low_bwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcrU : CrookUp ρ) (L : ℤ) (i s t : Fin n)
    (hp : ρ i = L + 4) (hs : i.val < s.val) (hsv : L + 7 ≤ ρ s)
    (ht : t.val < i.val) (htv : ρ t ≤ L + 1)
    (hfail : ∀ w : Fin n, w.val + 3 ≤ i.val → t.val + 5 ≤ w.val → ρ w ≤ L + 4) :
    (∃ v : Fin n, v.val < s.val ∧ i.val + 4 ≤ v.val ∧ ρ v ≤ L + 2) ∨ ValleyResidual ρ i L := by
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
    · exact Or.inr ⟨u', hu2', by omega⟩
    · obtain ⟨w, w', huw, hww', hw's, hw1, hw2, hw3, hw4⟩ := hcrU u' s (by omega) (by omega)
      exact Or.inl ⟨w', by omega, by omega, by omega⟩

/-! ## The crossing, on the arms -/

/-- The V-criterion for the backward arm, when the forward arm fails the valley clause. -/
theorem critVee_armT_of_fail_armG {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i : Fin n) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Valley (armG ρ i) L) (hres : ¬ ValleyResidual ρ i L) :
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
  rcases cross_valley_low_fwd hlip (crookDown_seq hcr) L i s t hp (by omega) hsv (by omega) htv
      hfailg with ⟨v, hv1, hv2, hv3⟩ | hbad
  · have hvn := v.isLt
    refine ⟨⟨i.val - v.val, by omega⟩, by simp; omega, by simp; omega, ?_⟩
    have heq : armT ρ i ⟨i.val - v.val, by omega⟩ = ρ v := by
      show ρ ⟨i.val - (i.val - v.val), _⟩ = ρ v
      exact congrArg ρ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
    rw [heq]; exact hv3
  · exact absurd hbad hres

/-- The V-criterion for the forward arm, when the backward arm fails the valley clause. -/
theorem critVee_armG_of_fail_armT {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i : Fin n) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Valley (armT ρ i) L) (hres : ¬ ValleyResidual ρ i L) :
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
  rcases cross_valley_low_bwd hlip (crookUp_seq hcr) L i s t hp (by omega) hsv (by omega) htv
      hfailg with ⟨v, hv1, hv2, hv3⟩ | hbad
  · have hvn := v.isLt
    refine ⟨⟨v.val - i.val, by omega⟩, by simp; omega, by simp; omega, ?_⟩
    have heq : armG ρ i ⟨v.val - i.val, by omega⟩ = ρ v := by
      show ρ ⟨i.val + (v.val - i.val), _⟩ = ρ v
      exact congrArg ρ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
    rw [heq]; exact hv3
  · exact absurd hbad hres

/-! ## The dichotomy -/

/-- **The valley crossing, except in one configuration.** Under the hypotheses of the work item
`cross_valley_profile`, either both arms fold onto the V-walk — its conclusion — or the sequence
stands at `L + 2` two or three steps to one side of the basepoint.

Of the work item's hypotheses, the two `HighAt` clauses and both ends of the band are not used. -/
theorem cross_valley_dichotomy {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Valley (armG ρ i) L ∨ ¬ Leg3Valley (armT ρ i) L) :
    (FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
        FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L)) ∨
      ValleyResidual ρ i L := by
  have hi := i.isLt
  have hmG : 0 < n - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  by_cases hres : ValleyResidual ρ i L
  · exact Or.inr hres
  refine Or.inl ?_
  rcases hfail with hfG | hfT
  · have hvT : FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
      refine (foldsOnto_vee_iff_profile hmT (armT ρ i) (armT_isLip hlip i) (L + 5) (L + 9) L
        (by omega) (by rw [hT0, abs_le]; omega) (fun j => hLb _) (fun j => hHb _)).mpr ?_
      rw [critVeeProfile_iff_of_isLip (armT_isLip hlip i) (L + 5) L (by omega)]
      intro d hd
      obtain ⟨j, hj1, hj2, hj3⟩ := critVee_armT_of_fail_armG hlip hcr L i hp hfG hres d (by omega)
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
      obtain ⟨j, hj1, hj2, hj3⟩ := critVee_armG_of_fail_armT hlip hcr L i hp hfT hres d (by omega)
      exact ⟨j, hj1, by omega, hj3⟩
    refine ⟨hvG, ?_⟩
    rcases leg3Valley_or_vee hmT (armT ρ i) (armT_isLip hlip i) (crookDown_armT hcr i) L hT0
      (fun j => hLb _) (fun j => hHb _) with h | h
    · exact absurd h hfT
    · exact h

/-- **The work item, for every pair that avoids the residual configuration.** This is
`cross_valley_profile` with one extra hypothesis, and the hypothesis is about the three steps
either side of the basepoint only. -/
theorem cross_valley_profile_of_not_residual {n : ℕ} (ρ σ : Fin n → ℤ) (i : Fin n) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ t, L ≤ ρ t) (hHb : ∀ t, ρ t ≤ L + 9) (hp : ρ i = L + 4)
    (hres : ¬ ValleyResidual ρ i L)
    (hfail : ¬ Leg3Valley (armG ρ i) L ∨ ¬ Leg3Valley (armT ρ i) L) :
    FoldsOnto (armG ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
  rcases cross_valley_dichotomy ρ σ i L hlip hcr hLb hHb hp hfail with h | h
  · exact h
  · exact absurd h hres


/-! ## How far the crossing gets, without exception

The dichotomy leaves the residual configuration, and the theorems of this section measure exactly
how much is missing there: **one level, and no index**. Unconditionally — in the residual case as
well as outside it — the arm that does not fail the valley clause stands at `L + 3` or below,
before each of its ascents to `L + 7`, at a step at least four. The V-criterion asks for `L + 2`
at such a step; the crookedness clause, applied twice across the basepoint, delivers `L + 3`. -/

/-- **The crossing always reaches `L + 3`, forward form.** The hypotheses are those of
`cross_valley_low_fwd`, and there is no exceptional case: a second application of the crookedness
clause, between the ascent and the low link the first application returns, always lands at `L + 3`
or below at least four steps before the basepoint. -/
theorem cross_valley_low3_fwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcrD : CrookDown ρ) (L : ℤ) (i s t : Fin n)
    (hp : ρ i = L + 4) (hs : s.val < i.val) (hsv : L + 7 ≤ ρ s)
    (ht : i.val < t.val) (htv : ρ t ≤ L + 1)
    (hfail : ∀ w : Fin n, i.val + 3 ≤ w.val → w.val + 5 ≤ t.val → ρ w ≤ L + 4) :
    ∃ v : Fin n, s.val < v.val ∧ v.val + 4 ≤ i.val ∧ ρ v ≤ L + 3 := by
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
  -- the low link is at least two steps before the basepoint, so the second one is at least four
  have hd := abs_sub_le_of_isLip hlip (i.val - u.val) u i (by omega)
  rw [abs_le] at hd
  have hcast : ((i.val - u.val : ℕ) : ℤ) = (i.val : ℤ) - (u.val : ℤ) := by
    push_cast [Nat.cast_sub (by omega : u.val ≤ i.val)]; ring
  rw [hcast] at hd
  obtain ⟨v, v', hsv2, hvv', hvu, hv1, hv2, hv3, hv4⟩ := hcrD s u (by omega) (by omega)
  exact ⟨v, by omega, by omega, by omega⟩

/-- **The crossing always reaches `L + 3`, backward form**, the mirror of
`cross_valley_low3_fwd`. -/
theorem cross_valley_low3_bwd {n : ℕ} {ρ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcrU : CrookUp ρ) (L : ℤ) (i s t : Fin n)
    (hp : ρ i = L + 4) (hs : i.val < s.val) (hsv : L + 7 ≤ ρ s)
    (ht : t.val < i.val) (htv : ρ t ≤ L + 1)
    (hfail : ∀ w : Fin n, w.val + 3 ≤ i.val → t.val + 5 ≤ w.val → ρ w ≤ L + 4) :
    ∃ v : Fin n, v.val < s.val ∧ i.val + 4 ≤ v.val ∧ ρ v ≤ L + 3 := by
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
  obtain ⟨w, w', huw, hww', hw's, hw1, hw2, hw3, hw4⟩ := hcrU u' s (by omega) (by omega)
  exact ⟨w', by omega, by omega, by omega⟩

/-- **The relaxed criterion for the backward arm**, when the forward arm fails the valley clause:
before every ascent to `L + 7` the arm stands at `L + 3` or below at a step at least four. This is
the V-criterion of `critVeeProfile_iff_of_isLip` with `L + 3` where it asks `L + 2`, and unlike
`critVee_armT_of_fail_armG` it has no exceptional case. -/
theorem cross_valley_armT_low3 {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i : Fin n) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Valley (armG ρ i) L) :
    ∀ e : Fin (i.val + 1), L + 7 ≤ armT ρ i e →
      ∃ j : Fin (i.val + 1), j.val < e.val ∧ 4 ≤ j.val ∧ armT ρ i j ≤ L + 3 := by
  have hi := i.isLt
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
  obtain ⟨v, hv1, hv2, hv3⟩ :=
    cross_valley_low3_fwd hlip (crookDown_seq hcr) L i s t hp (by omega) hsv (by omega) htv hfailg
  have hvn := v.isLt
  refine ⟨⟨i.val - v.val, by omega⟩, by simp; omega, by simp; omega, ?_⟩
  have heq : armT ρ i ⟨i.val - v.val, by omega⟩ = ρ v := by
    show ρ ⟨i.val - (i.val - v.val), _⟩ = ρ v
    exact congrArg ρ (Fin.ext (by show i.val - (i.val - v.val) = v.val; omega))
  rw [heq]; exact hv3

/-- **The relaxed criterion for the forward arm**, when the backward arm fails the valley clause;
the mirror of `cross_valley_armT_low3`. -/
theorem cross_valley_armG_low3 {n : ℕ} {ρ σ : Fin n → ℤ} (hlip : IsLip ρ)
    (hcr : IsCrookedIvF ρ σ) (L : ℤ) (i : Fin n) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Valley (armT ρ i) L) :
    ∀ e : Fin (n - i.val), L + 7 ≤ armG ρ i e →
      ∃ j : Fin (n - i.val), j.val < e.val ∧ 4 ≤ j.val ∧ armG ρ i j ≤ L + 3 := by
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
  obtain ⟨v, hv1, hv2, hv3⟩ :=
    cross_valley_low3_bwd hlip (crookUp_seq hcr) L i s t hp (by omega) hsv (by omega) htv hfailg
  have hvn := v.isLt
  refine ⟨⟨v.val - i.val, by omega⟩, by simp; omega, by simp; omega, ?_⟩
  have heq : armG ρ i ⟨v.val - i.val, by omega⟩ = ρ v := by
    show ρ ⟨i.val + (v.val - i.val), _⟩ = ρ v
    exact congrArg ρ (Fin.ext (by show i.val + (v.val - i.val) = v.val; omega))
  rw [heq]; exact hv3

end HPC.Fold
