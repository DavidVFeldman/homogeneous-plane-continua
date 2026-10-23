import HPC.Fold.CrossArm
import HPC.Fold.LandmarkW
import HPC.Fold.Leg3Profile
import HPC.Fold.ProfileP

/-!
# The ceiling case, at the level of arms

`cross_ceil_sentence` (`HPC/Fold/CrossCeil.lean`) asks that a pair of the branch `L + 4` with an
arm failing `Leg3Ceil` and not served by the Λ-walk satisfies the sentence of `w₄` on both arms or
the sentence of `w₅` on both arms. Every census of this repository answers with the *same*
disjunct: at every such configuration both arms satisfy `Valley5` and `TopW5`, the sentence of
`w₅`. This file proves the two halves of that sentence that are statements about arms alone, and
so reduces the work item to two statements across the basepoint and nothing else.

Three theorems about a single 1-Lipschitz arm of the band `[L, L + 9]` based at `L + 4`, with the
two crookedness clauses:

* `valley5_of_not_leg3Ceil` — an arm that **fails** `Leg3Ceil` satisfies `Valley5`. A descent to
  `L + 1` before the unprepared ascent would, by one application of `CrookUp`, produce exactly the
  two landmarks `Leg3Ceil` asks for; so every descent to `L + 1` comes after the ascent, and the
  ascent itself is the peak `Valley5` wants.
* `valley5_or_vee` — an arm that fails `Valley5` folds onto the V-walk based at `L + 5`. This is
  `leg3Valley_or_vee` of batch 48 with the deeper clause: the failing descent is again the witness
  the V-criterion wants, and an ascent to `L + 7` before it is excluded by the timing laws.
* `topW5_or_lam` — an arm that fails `TopW5` folds onto the Λ-walk based at `L + 3`. The time at
  `L + 9` where the clause fails is the peak the Λ-criterion wants, and a descent to `L + 1`
  before it would produce the two landmarks `TopW5` asks for.

What they leave. In the configuration of the work item let `X` be an arm failing `Leg3Ceil` and
`Y` the other one. Then `X` folds onto the Λ-walk (`leg3Ceil_or_lam`), so `Y` does not, and

* `Valley5 X` holds by `valley5_of_not_leg3Ceil`;
* `TopW5 Y` holds by `topW5_or_lam`;

and the sentence of `w₅` needs exactly two more clauses: `TopW5 X` and `Valley5 Y`. That pair is
`CeilCrossGap` below, and `cross_ceil_sentence_of_gap` derives the work item from it.

Where the proof stops one level short. `topW5_low3` measures the first of the two: for an arm of
the branch — one satisfying `HighAt (L + 1) (L + 8)` — the clause `CrookUp`, applied between the
time at `L + 2` the branch hypothesis supplies and the time at `L + 9`, returns the peak `TopW5`
asks for and then a time at `L + 3`, where the clause asks for `L + 2`. It is the general model's
one-level shortfall, in the same place as at the valley (`cross_valley_low3_fwd`,
`HPC/Fold/CrossValley.lean`).
-/

namespace HPC.Fold

/-! ## `Valley5` on an arm that fails the ceiling clause -/

/-- **An arm failing `Leg3Ceil` satisfies `Valley5`.** The two clauses cannot fail together: an
unprepared ascent to `L + 8` forces every descent to `L + 1` to come after it, and then the ascent
itself is the deep peak the valley clause of `w₅` asks for. -/
theorem valley5_of_not_leg3Ceil {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (hcru : CrookUp f) (hcrd : CrookDown f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4)
    (hfail : ¬ Leg3Ceil f L) :
    Valley5 f L := by
  rw [Leg3Ceil] at hfail
  push_neg at hfail
  obtain ⟨D, hD, hno⟩ := hfail
  -- the ascent is late
  have hD0 : 0 < D.val := by
    rcases Nat.eq_zero_or_pos D.val with h | h
    · exact absurd (congrArg f (Fin.ext h : D = ⟨0, hm⟩)) (by omega)
    · exact h
  have hDlate : 0 + 7 ≤ D.val := by
    have := crookUp_climb4 hf hcru ⟨0, hm⟩ D (by simpa using hD0) (by omega)
    simpa using this
  intro d hd
  have hd0 : 0 < d.val := by
    rcases Nat.eq_zero_or_pos d.val with h | h
    · exact absurd (congrArg f (Fin.ext h : d = ⟨0, hm⟩)) (by omega)
    · exact h
  have hdlate : 0 + 4 ≤ d.val := by
    have := crookDown_fall3 hf hcrd ⟨0, hm⟩ d (by simpa using hd0) (by omega)
    simpa using this
  -- the descent cannot precede the ascent
  have hDd : D.val < d.val := by
    rcases lt_trichotomy D.val d.val with h | h | h
    · exact h
    · exact absurd (congrArg f (Fin.ext h : D = d)) (by omega)
    · exfalso
      obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
        hcru.levels (L + 1) (L + 8) (by omega) d D h (by omega) hD
      have hfall : u.val + 7 ≤ u'.val := crookDown_fall4 hf hcrd u u' h2 (by omega)
      have hclimb : u'.val + 12 ≤ D.val := crookUp_climb5 hf hcru u' D h3 (by omega)
      exact absurd (hno u u' (by omega) (by omega) (by omega) (by omega)) (by omega)
  refine ⟨D, by omega, ?_, by omega⟩
  have := crookDown_fall4 hf hcrd D d hDd (by omega)
  omega

/-! ## The two dichotomies of the sentence of `w₅` -/

/-- **An arm that fails `Valley5` folds onto the V-walk.** The step where the clause fails is
itself the low landmark the V-criterion asks for, and an ascent to `L + 7` before it is impossible:
the timing laws would place it inside the window the failure controls. -/
theorem valley5_or_vee {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcru : CrookUp f)
    (hcrd : CrookDown f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j)
    (hH : ∀ j, f j ≤ L + 9) :
    Valley5 f L ∨ FoldsOnto f (veeLen (L + 5) (L + 9) L) (veeCenter (L + 5) (L + 9) L) := by
  by_cases hex : ∃ d : Fin m, f d ≤ L + 1 ∧
      ∀ j : Fin m, 4 ≤ j.val → j.val + 5 ≤ d.val → f j ≤ L + 5
  · obtain ⟨d, hd, hno⟩ := hex
    refine Or.inr ((foldsOnto_vee_iff_profile hm f hf (L + 5) (L + 9) L (by omega)
      (by rw [h0, abs_le]; omega) hL hH).mpr ?_)
    rw [critVeeProfile_iff_of_isLip hf (L + 5) L (by omega)]
    intro e he
    have hd0 : 0 < d.val := by
      rcases Nat.eq_zero_or_pos d.val with h | h
      · exact absurd (congrArg f (Fin.ext h : d = ⟨0, hm⟩)) (by omega)
      · exact h
    have hdlate : 0 + 4 ≤ d.val := by
      have := crookDown_fall3 hf hcrd ⟨0, hm⟩ d (by simpa using hd0) (by omega)
      simpa using this
    refine ⟨d, ?_, by omega, by omega⟩
    rcases lt_trichotomy d.val e.val with h | h | h
    · exact h
    · exact absurd (congrArg f (Fin.ext h : d = e)) (by omega)
    · exfalso
      have he0 : 0 < e.val := by
        rcases Nat.eq_zero_or_pos e.val with h' | h'
        · exact absurd (congrArg f (Fin.ext h' : e = ⟨0, hm⟩)) (by omega)
        · exact h'
      have helate : 0 + 4 ≤ e.val := by
        have := crookUp_climb3 hf hcru ⟨0, hm⟩ e (by simpa using he0) (by omega)
        simpa using this
      have hfall : e.val + 7 ≤ d.val := crookDown_fall4 hf hcrd e d h (by omega)
      exact absurd (hno e (by omega) (by omega)) (by omega)
  · push_neg at hex
    refine Or.inl (fun d hd => ?_)
    obtain ⟨j, hj4, hj5, hjf⟩ := hex d hd
    exact ⟨j, hj4, hj5, by omega⟩

/-- **An arm that fails `TopW5` folds onto the Λ-walk.** The time at `L + 9` where the clause
fails is the peak the Λ-criterion asks for, and a descent to `L + 1` before it would produce, by
one application of `CrookUp`, exactly the two landmarks `TopW5` asks for. -/
theorem topW5_or_lam {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcru : CrookUp f)
    (hcrd : CrookDown f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j)
    (hH : ∀ j, f j ≤ L + 9) :
    TopW5 f L ∨ FoldsOnto f (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
  by_cases hex : ∃ D : Fin m, L + 9 ≤ f D ∧
      ∀ j k : Fin m, 4 ≤ j.val → j.val + 6 ≤ k.val → k.val + 7 ≤ D.val → L + 6 ≤ f j →
        L + 2 < f k
  · obtain ⟨D, hD, hno⟩ := hex
    refine Or.inr (foldsOnto_lam_of_profile hm f hf (L + 3) (L + 9) L (by omega)
      (by rw [h0, abs_le]; omega) hL hH ?_)
    have hk : κ (L + 3) (L + 9) = L + 8 := by simp only [κ]; omega
    rw [critLamProfile_iff_of_isLip hf, hk]
    intro d hd
    have hD0 : 0 < D.val := by
      rcases Nat.eq_zero_or_pos D.val with h | h
      · exact absurd (congrArg f (Fin.ext h : D = ⟨0, hm⟩)) (by omega)
      · exact h
    have hDlate : 0 + 12 ≤ D.val := by
      have := crookUp_climb5 hf hcru ⟨0, hm⟩ D (by simpa using hD0) (by omega)
      simpa using this
    refine ⟨D, ?_, by omega, by omega⟩
    rcases lt_trichotomy D.val d.val with h | h | h
    · exact h
    · exact absurd (congrArg f (Fin.ext h : D = d)) (by omega)
    · exfalso
      have hd0 : 0 < d.val := by
        rcases Nat.eq_zero_or_pos d.val with h' | h'
        · exact absurd (congrArg f (Fin.ext h' : d = ⟨0, hm⟩)) (by omega)
        · exact h'
      have hdlate : 0 + 4 ≤ d.val := by
        have := crookDown_fall3 hf hcrd ⟨0, hm⟩ d (by simpa using hd0) (by omega)
        simpa using this
      obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
        hcru.levels (L + 1) (L + 9) (by omega) d D h (by omega) hD
      have hfall : u.val + 7 ≤ u'.val := crookDown_fall4 hf hcrd u u' h2 (by omega)
      have hclimb : u'.val + 12 ≤ D.val := crookUp_climb5 hf hcru u' D h3 (by omega)
      exact absurd (hno u u' (by omega) (by omega) (by omega) (by omega)) (by omega)
  · push_neg at hex
    refine Or.inl (fun d hd => ?_)
    obtain ⟨j, k, hj4, hjk, hkd, hjf, hkf⟩ := hex d hd
    exact ⟨j, k, hj4, hjk, hkd, hjf, by omega⟩

/-! ## What the ceiling case still needs -/

/-- **The two clauses the ceiling case still needs.** In the configuration of
`cross_ceil_sentence` the arm that fails `Leg3Ceil` satisfies `Valley5` and the other arm
satisfies `TopW5`; what is left is the ceiling clause on the failing arm and the valley clause on
the other one, and this is exactly that statement. Both are statements across the basepoint: each
is about the arm that the hypothesis does *not* speak of. -/
def CeilCrossGap {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (L : ℤ) : Prop :=
  (¬ Leg3Ceil (armG ρ i) L → TopW5 (armG ρ i) L ∧ Valley5 (armT ρ i) L) ∧
    (¬ Leg3Ceil (armT ρ i) L → TopW5 (armT ρ i) L ∧ Valley5 (armG ρ i) L)

/-- **The ceiling crossing, from the two remaining clauses.** With `CeilCrossGap` the work item
`cross_ceil_sentence` holds, and with the second disjunct: both arms satisfy the sentence of `w₅`.
The two halves the file proves — `Valley5` on the failing arm and `TopW5` on the arm that does not
fold onto the Λ-walk — are supplied here. -/
theorem cross_ceil_sentence_of_gap {m : ℕ} (ρ σ : Fin m → ℤ) (i : Fin m) (L : ℤ)
    (hlip : IsLip ρ) (hcr : IsCrookedIvF ρ σ)
    (hLb : ∀ u, L ≤ ρ u) (hHb : ∀ u, ρ u ≤ L + 9) (hp : ρ i = L + 4)
    (hfail : ¬ Leg3Ceil (armG ρ i) L ∨ ¬ Leg3Ceil (armT ρ i) L)
    (hnotLam : ¬ (FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) ∧
      FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L)))
    (hgap : CeilCrossGap ρ i L) :
    ((MidW4 (armG ρ i) L ∧ BottomW4 (armG ρ i) L) ∧
        (MidW4 (armT ρ i) L ∧ BottomW4 (armT ρ i) L)) ∨
      ((Valley5 (armG ρ i) L ∧ TopW5 (armG ρ i) L) ∧
        (Valley5 (armT ρ i) L ∧ TopW5 (armT ρ i) L)) := by
  have hi := i.isLt
  have hmG : 0 < m - i.val := by omega
  have hmT : 0 < i.val + 1 := by omega
  have hG0 : armG ρ i ⟨0, hmG⟩ = L + 4 := by
    rw [show armG ρ i ⟨0, hmG⟩ = ρ i by simp [armG], hp]
  have hT0 : armT ρ i ⟨0, hmT⟩ = L + 4 := by
    rw [show armT ρ i ⟨0, hmT⟩ = ρ i by simp [armT], hp]
  refine Or.inr ?_
  rcases hfail with hfG | hfT
  · -- the forward arm fails the ceiling clause, so it folds onto the Λ-walk
    have hlG : FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
      rcases leg3Ceil_or_lam hmG (armG ρ i) (armG_isLip hlip i) (crookUp_armG hcr i)
        (crookDown_armG hcr i) L hG0 (fun j => hLb _) (fun j => hHb _) with h | h
      · exact absurd h hfG
      · exact h
    have hnlT : ¬ FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L)
        (lamCenter (L + 3) (L + 9) L) := fun h => hnotLam ⟨hlG, h⟩
    have hv5G : Valley5 (armG ρ i) L :=
      valley5_of_not_leg3Ceil hmG (armG ρ i) (armG_isLip hlip i) (crookUp_armG hcr i)
        (crookDown_armG hcr i) L hG0 hfG
    have ht5T : TopW5 (armT ρ i) L := by
      rcases topW5_or_lam hmT (armT ρ i) (armT_isLip hlip i) (crookUp_armT hcr i)
        (crookDown_armT hcr i) L hT0 (fun j => hLb _) (fun j => hHb _) with h | h
      · exact h
      · exact absurd h hnlT
    obtain ⟨ht5G, hv5T⟩ := hgap.1 hfG
    exact ⟨⟨hv5G, ht5G⟩, ⟨hv5T, ht5T⟩⟩
  · have hlT : FoldsOnto (armT ρ i) (lamLen (L + 3) (L + 9) L) (lamCenter (L + 3) (L + 9) L) := by
      rcases leg3Ceil_or_lam hmT (armT ρ i) (armT_isLip hlip i) (crookUp_armT hcr i)
        (crookDown_armT hcr i) L hT0 (fun j => hLb _) (fun j => hHb _) with h | h
      · exact absurd h hfT
      · exact h
    have hnlG : ¬ FoldsOnto (armG ρ i) (lamLen (L + 3) (L + 9) L)
        (lamCenter (L + 3) (L + 9) L) := fun h => hnotLam ⟨h, hlT⟩
    have hv5T : Valley5 (armT ρ i) L :=
      valley5_of_not_leg3Ceil hmT (armT ρ i) (armT_isLip hlip i) (crookUp_armT hcr i)
        (crookDown_armT hcr i) L hT0 hfT
    have ht5G : TopW5 (armG ρ i) L := by
      rcases topW5_or_lam hmG (armG ρ i) (armG_isLip hlip i) (crookUp_armG hcr i)
        (crookDown_armG hcr i) L hG0 (fun j => hLb _) (fun j => hHb _) with h | h
      · exact h
      · exact absurd h hnlG
    obtain ⟨ht5T, hv5G⟩ := hgap.2 hfT
    exact ⟨⟨hv5G, ht5G⟩, ⟨hv5T, ht5T⟩⟩

/-! ## How far the ceiling crossing gets, without exception -/

/-- **The ceiling crossing always reaches `L + 3`.** For an arm of the branch — 1-Lipschitz, in
the band, based at `L + 4` and satisfying the branch hypothesis `HighAt (L + 1) (L + 8)` — before
every time at `L + 9` there are two landmarks with the gaps `TopW5` asks for, the first at `L + 6`
or above and the second at **`L + 3`** or below. `TopW5` asks for `L + 2` at the second, and the
one level between them is the whole of what the work item still waits on at the ceiling.

The proof is one application of `CrookUp` between the time at `L + 2` that the branch hypothesis
supplies and the time at `L + 9`: the clause returns a time within two of the top and then one
within one of the bottom, and the bottom it is measured against is the `L + 2` of the hypothesis,
not the `L + 1` the clause would need. -/
theorem topW5_low3 {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f) (hcru : CrookUp f)
    (hcrd : CrookDown f) (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hhigh : HighAt f (L + 1) (L + 8)) :
    ∀ d : Fin m, L + 9 ≤ f d → ∃ j k : Fin m, 4 ≤ j.val ∧ j.val + 6 ≤ k.val ∧ k.val + 7 ≤ d.val ∧
      L + 6 ≤ f j ∧ f k ≤ L + 3 := by
  intro d hd
  obtain ⟨e, hed, hef⟩ := hhigh d (by omega)
  obtain ⟨u, u', h1, h2, h3, h4, h5⟩ :=
    hcru.levels (L + 2) (L + 9) (by omega) e d hed (by omega) hd
  have hu0 : 0 < u.val := by
    rcases Nat.eq_zero_or_pos u.val with h | h
    · exact absurd (congrArg f (Fin.ext h : u = ⟨0, hm⟩)) (by omega)
    · exact h
  have hulate : 0 + 4 ≤ u.val := by
    have := crookUp_climb3 hf hcru ⟨0, hm⟩ u (by simpa using hu0) (by omega)
    simpa using this
  have hfall : u.val + 7 ≤ u'.val := crookDown_fall4 hf hcrd u u' h2 (by omega)
  have hclimb : u'.val + 12 ≤ d.val := crookUp_climb5 hf hcru u' d h3 (by omega)
  exact ⟨u, u', by omega, by omega, by omega, by omega, by omega⟩

end HPC.Fold
