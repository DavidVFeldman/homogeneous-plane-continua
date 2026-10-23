import HPC.Fold.Leg3Profile

/-!
# The landmark sentence is necessary for a fold

`FoldsOnto f len c` asks for an itinerary `β` — a walk time for each step of the arm, starting at
`0`, moving by at most one position per step, and always within one of the arm's level. Everything
the criteria of this development ask of an arm is a consequence of that, and this file proves the
consequence once and for all.

The observation is the discrete intermediate value theorem for `β`. If the arm's level at a step
`d` can only be served by walk positions `q2` and later, then `β d ≥ q2`, so for every pair of
earlier positions `q0 ≤ q1 ≤ q2` the itinerary passes through `q0` and then through `q1`, at steps
`j ≤ k ≤ d`. Three index bounds come for free, because `β` moves by at most one position per step
and starts at `0`:

* `j ≥ q0`;
* `k ≥ j + (q1 - q0)`;
* `d ≥ k + (q2 - q1)`,

and at those steps the arm is within one of the walk's levels `c q0` and `c q1`. That is the
landmark sentence of REPORT-batch48.md §2.3, in the two-landmark case, and `foldsOnto_landmark1`
and `foldsOnto_landmark2` are it for an arbitrary walk `c`.

## What it gives here

Read on the three-leg walk `L+3 → L+6 → L+1 → L+8` (`leg3Walk L (L+9) (L+6) (L+4)`, whose sixteen
positions carry the levels `3,4,5,6,5,4,3,2,1,2,3,4,5,6,7,8` above `L`):

* an ascent to `L + 8` can only be served by the positions `14` and `15`, and the landmarks `3`
  (level `L + 6`) and `8` (level `L + 1`) before them give exactly `Leg3Ceil`
  (`leg3Ceil_of_foldsOnto_leg3`);
* a descent to `L + 1` can only be served by the positions `7, 8, 9`, and the landmark `3` gives
  a time at `L + 5` or above, at a step at least `3` and at least four steps earlier
  (`leg3Valley4_of_foldsOnto_leg3`).

With the sufficiency proved in batch 48 (`foldsOnto_leg3deep_profile_min`) this closes the
criterion for the third walk: for a 1-Lipschitz arm in the band based at `L + 4`, folding onto the
three-leg walk is **equivalent** to the landmark sentence (`foldsOnto_leg3deep_iff_landmark`), and
the commissioned clauses sit between the two halves. The census of batch 48 reported the sentence
to be equivalent to the fold on its corpus; for this walk that is now a theorem.

The immediate use is negative: an arm that fails `Leg3Ceil` does not fold onto the third walk.
That is what refutes `unserved_leg3deep` and `cross_ceil_profile` in
`HPC/Fold/CrossWitness.lean`.
-/

namespace HPC.Fold

/-! ## The itinerary moves by one position per step -/

section Itin

variable {m : ℕ} {β : Fin m → ℕ}

/-- An itinerary starting at `0` is at position at most `t` at its step `t`. -/
theorem beta_le_val (hz : ∀ j : Fin m, j.val = 0 → β j = 0)
    (hs : ∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) :
    ∀ (n : ℕ) (j : Fin m), j.val = n → β j ≤ n := by
  intro n
  induction n with
  | zero => intro j hj; exact le_of_eq (hz j hj)
  | succ n ih =>
      intro j hj
      have hjm := j.isLt
      have hnm : n < m := by omega
      have hprev := ih ⟨n, hnm⟩ rfl
      have hstep := hs ⟨n, hnm⟩ j (by simp [hj])
      rw [abs_le] at hstep
      omega

/-- Between two steps the itinerary moves by at most their distance. -/
theorem beta_dist (hs : ∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) :
    ∀ (k : ℕ) (a b : Fin m), b.val = a.val + k → (β b : ℤ) - (β a : ℤ) ≤ (k : ℤ) := by
  intro k
  induction k with
  | zero =>
      intro a b hb
      have : b = a := Fin.ext (by omega)
      subst this
      simp
  | succ k ih =>
      intro a b hb
      have hbm := b.isLt
      have hkm : a.val + k < m := by omega
      have hprev := ih a ⟨a.val + k, hkm⟩ rfl
      have hstep := hs ⟨a.val + k, hkm⟩ b (by show b.val = a.val + k + 1; omega)
      rw [abs_le] at hstep
      push_cast at hprev hstep ⊢
      omega

/-- **The discrete intermediate value theorem for an itinerary.** A position between the
itinerary's values at two steps is taken at some step between them. -/
theorem beta_hits (hs : ∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1) :
    ∀ (n : ℕ) (b : Fin m), b.val = n → ∀ (q : ℕ), q ≤ β b → ∀ a : Fin m, a.val ≤ b.val →
      β a ≤ q → ∃ j : Fin m, a.val ≤ j.val ∧ j.val ≤ b.val ∧ β j = q := by
  intro n
  induction n with
  | zero =>
      intro b hb q hq a hab ha
      have : a = b := Fin.ext (by omega)
      subst this
      exact ⟨a, le_rfl, le_rfl, by omega⟩
  | succ n ih =>
      intro b hb q hq a hab ha
      by_cases hbq : β b = q
      · exact ⟨b, hab, le_rfl, hbq⟩
      · have hbm := b.isLt
        have hnm : n < m := by omega
        have hstep := hs ⟨n, hnm⟩ b (by simp [hb])
        rw [abs_le] at hstep
        have hq' : q ≤ β ⟨n, hnm⟩ := by omega
        have han : a.val ≤ n := by
          by_contra hcon
          have hab' : a = b := Fin.ext (by omega)
          subst hab'
          omega
        obtain ⟨j, hj1, hj2, hj3⟩ := ih ⟨n, hnm⟩ rfl q hq' a han ha
        have hj2' : j.val ≤ n := hj2
        exact ⟨j, hj1, by omega, hj3⟩

end Itin

/-! ## The landmark sentence, for an arbitrary walk -/

/-- **One landmark.** If the arm's level at the step `d` is served only by the walk positions
`q1` and later, then at some earlier step `j` the arm is within one of the level `c q0` of the
landmark `q0 ≤ q1`, with `j ≥ q0` and `j + (q1 - q0) ≤ d`. -/
theorem foldsOnto_landmark1 {m len : ℕ} {f : Fin m → ℤ} {c : ℕ → ℤ}
    (h : FoldsOnto f len c) (d : Fin m) (q0 q1 : ℕ) (h01 : q0 ≤ q1)
    (hd : ∀ p : ℕ, p < len → |f d - c p| ≤ 1 → q1 ≤ p) :
    ∃ j : Fin m, q0 ≤ j.val ∧ j.val + (q1 - q0) ≤ d.val ∧ |f j - c q0| ≤ 1 := by
  obtain ⟨β, hlen, hs, hz, hval⟩ := h
  have hdm := d.isLt
  have hzm : 0 < m := by omega
  set z : Fin m := ⟨0, hzm⟩ with hzdef
  have hβz : β z = 0 := hz z rfl
  have hq1 : q1 ≤ β d := hd (β d) (hlen d) (hval d)
  obtain ⟨j, -, hjd, hjβ⟩ :=
    beta_hits hs d.val d rfl q0 (by omega) z (by simp [hzdef]) (by omega)
  refine ⟨j, ?_, ?_, ?_⟩
  · have := beta_le_val hz hs j.val j rfl
    omega
  · have := beta_dist hs (d.val - j.val) j d (by omega)
    push_cast at this
    omega
  · have := hval j
    rwa [hjβ] at this

/-- **Two landmarks.** The same, with two landmarks `q0 ≤ q1` before the position `q2` that the
arm's level at `d` forces: the arm passes within one of `c q0` and then within one of `c q1`, and
the three gaps are at least the walk's own. -/
theorem foldsOnto_landmark2 {m len : ℕ} {f : Fin m → ℤ} {c : ℕ → ℤ}
    (h : FoldsOnto f len c) (d : Fin m) (q0 q1 q2 : ℕ) (h01 : q0 ≤ q1) (h12 : q1 ≤ q2)
    (hd : ∀ p : ℕ, p < len → |f d - c p| ≤ 1 → q2 ≤ p) :
    ∃ j k : Fin m, q0 ≤ j.val ∧ j.val + (q1 - q0) ≤ k.val ∧ k.val + (q2 - q1) ≤ d.val ∧
      |f j - c q0| ≤ 1 ∧ |f k - c q1| ≤ 1 := by
  obtain ⟨β, hlen, hs, hz, hval⟩ := h
  have hdm := d.isLt
  have hzm : 0 < m := by omega
  set z : Fin m := ⟨0, hzm⟩ with hzdef
  have hβz : β z = 0 := hz z rfl
  have hq2 : q2 ≤ β d := hd (β d) (hlen d) (hval d)
  obtain ⟨k, -, hkd, hkβ⟩ :=
    beta_hits hs d.val d rfl q1 (by omega) z (by simp [hzdef]) (by omega)
  obtain ⟨j, -, hjk, hjβ⟩ :=
    beta_hits hs k.val k rfl q0 (by omega) z (by simp [hzdef]) (by omega)
  refine ⟨j, k, ?_, ?_, ?_, ?_, ?_⟩
  · have := beta_le_val hz hs j.val j rfl
    omega
  · have := beta_dist hs (k.val - j.val) j k (by omega)
    push_cast at this
    omega
  · have := beta_dist hs (d.val - k.val) k d (by omega)
    push_cast at this
    omega
  · have := hval j
    rwa [hjβ] at this
  · have := hval k
    rwa [hkβ] at this

/-! ## The three-leg walk, read backwards -/

/-- The three-leg walk of the branch has sixteen positions. -/
theorem leg3Len_branch (L : ℤ) : leg3Len L (L + 9) (L + 6) (L + 4) = 16 := by
  simp only [leg3Len]
  omega

/-- Its levels, position by position. -/
theorem leg3Walk_branch_val (L : ℤ) (u : ℕ) (hu : u < 16) :
    leg3Walk L (L + 9) (L + 6) (L + 4) u =
      L + (if u ≤ 3 then (3 + u : ℤ) else if u ≤ 8 then (9 - u : ℤ) else (u - 7 : ℤ)) := by
  have hcast : ((u : ℤ) ≤ 3 ↔ u ≤ 3) := by exact_mod_cast Iff.rfl
  simp only [leg3Walk]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> omega

/-- The landmark at the peak. -/
theorem leg3Walk_branch_three (L : ℤ) : leg3Walk L (L + 9) (L + 6) (L + 4) 3 = L + 6 := by
  rw [leg3Walk_branch_val L 3 (by norm_num)]
  norm_num

/-- The landmark at the valley. -/
theorem leg3Walk_branch_eight (L : ℤ) : leg3Walk L (L + 9) (L + 6) (L + 4) 8 = L + 1 := by
  rw [leg3Walk_branch_val L 8 (by norm_num)]
  norm_num

/-- An ascent to `L + 8` is served only by the last two positions of the walk. -/
theorem leg3Walk_high_pos {L v : ℤ} {p : ℕ} (hp : p < 16) (hv : L + 8 ≤ v)
    (h : |v - leg3Walk L (L + 9) (L + 6) (L + 4) p| ≤ 1) : 14 ≤ p := by
  rw [leg3Walk_branch_val L p hp, abs_le] at h
  by_contra hc
  interval_cases p <;> simp_all <;> omega

/-- A descent to `L + 1` is served only by the positions `7`, `8`, `9`. -/
theorem leg3Walk_low_pos {L v : ℤ} {p : ℕ} (hp : p < 16) (hv : v ≤ L + 1)
    (h : |v - leg3Walk L (L + 9) (L + 6) (L + 4) p| ≤ 1) : 7 ≤ p := by
  rw [leg3Walk_branch_val L p hp, abs_le] at h
  by_contra hc
  interval_cases p <;> simp_all <;> omega

/-- **`Leg3Ceil` is necessary.** An arm that folds onto the three-leg walk announces every ascent
to `L + 8` exactly as the clause asks: a time at `L + 5` or above at a step at least `3`, a time
at `L + 2` or below five steps later or more, and the ascent six steps after that or later. -/
theorem leg3Ceil_of_foldsOnto_leg3 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4))
      (leg3Walk L (L + 9) (L + 6) (L + 4))) :
    Leg3Ceil f L := by
  intro d hd
  have hpos : ∀ p : ℕ, p < leg3Len L (L + 9) (L + 6) (L + 4) →
      |f d - leg3Walk L (L + 9) (L + 6) (L + 4) p| ≤ 1 → 14 ≤ p := by
    intro p hp hpv
    rw [leg3Len_branch] at hp
    exact leg3Walk_high_pos hp hd hpv
  obtain ⟨j, k, hj0, hjk, hkd, hjv, hkv⟩ :=
    foldsOnto_landmark2 h d 3 8 14 (by norm_num) (by norm_num) hpos
  rw [leg3Walk_branch_three, abs_le] at hjv
  rw [leg3Walk_branch_eight, abs_le] at hkv
  exact ⟨j, k, hj0, by omega, by omega, by omega, by omega⟩

/-- **The valley landmark is necessary.** Every descent to `L + 1` of an arm that folds onto the
three-leg walk is preceded by a time at `L + 5` or above, at a step at least `3` and at least four
steps earlier. (The clause `Leg3Valley` asks five steps; four is what the walk forces, because it
already serves `L + 1` from its position `7`.) -/
theorem leg3Valley4_of_foldsOnto_leg3 {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4))
      (leg3Walk L (L + 9) (L + 6) (L + 4))) :
    ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 3 ≤ j.val ∧ j.val + 4 ≤ d.val ∧ L + 5 ≤ f j := by
  intro d hd
  have hpos : ∀ p : ℕ, p < leg3Len L (L + 9) (L + 6) (L + 4) →
      |f d - leg3Walk L (L + 9) (L + 6) (L + 4) p| ≤ 1 → 7 ≤ p := by
    intro p hp hpv
    rw [leg3Len_branch] at hp
    exact leg3Walk_low_pos hp hd hpv
  obtain ⟨j, hj0, hjd, hjv⟩ := foldsOnto_landmark1 h d 3 7 (by norm_num) hpos
  rw [leg3Walk_branch_three, abs_le] at hjv
  exact ⟨j, hj0, by omega, by omega⟩

/-- **The landmark sentence for the three-leg walk**: the valley landmark with its index four, and
the ceiling clause. -/
def Leg3Land {m : ℕ} (f : Fin m → ℤ) (L : ℤ) : Prop :=
  (∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 3 ≤ j.val ∧ j.val + 4 ≤ d.val ∧ L + 5 ≤ f j) ∧
    Leg3Ceil f L

/-- **The criterion for the third walk is exact.** For a 1-Lipschitz arm of the band based at
`L + 4`, folding onto `L+3 → L+6 → L+1 → L+8` is equivalent to the landmark sentence. Necessity is
the itinerary's intermediate value theorem; sufficiency is `foldsOnto_leg3deep_profile_min`, proved
in batch 48. -/
theorem foldsOnto_leg3deep_iff_landmark {m : ℕ} (hm : 0 < m) (f : Fin m → ℤ) (hf : IsLip f)
    (L : ℤ) (h0 : f ⟨0, hm⟩ = L + 4) (hL : ∀ j, L ≤ f j) (hH : ∀ j, f j ≤ L + 9) :
    FoldsOnto f (leg3Len L (L + 9) (L + 6) (L + 4)) (leg3Walk L (L + 9) (L + 6) (L + 4)) ↔
      Leg3Land f L := by
  constructor
  · intro h
    exact ⟨leg3Valley4_of_foldsOnto_leg3 h, leg3Ceil_of_foldsOnto_leg3 h⟩
  · rintro ⟨hv, hc⟩
    refine foldsOnto_leg3deep_profile_min hm f hf L h0 hL hH ?_ (leg3CeilMin_of_leg3Ceil hc)
    intro d hd
    obtain ⟨j, hj0, hjd, hjv⟩ := hv d hd
    exact ⟨j, hj0, by omega, hjv⟩

/-! ## The deep walk of the re-split branch

`unserved_three_walks` (`HPC/Fold/Mixed.lean`) names two more walks, and the landmark theorem
reads on them exactly as it does on the third one. Here is the valley clause of
`w₅ = L+3 → L+7 → L+1 → L+8`, whose eighteen positions carry
`3,4,5,6,7,6,5,4,3,2,1,2,3,4,5,6,7,8` above `L`: a level `L + 1` is served only by its positions
`9`, `10`, `11`, and the landmark `4` carries the level `L + 7`. -/

/-- The deep walk of the branch has eighteen positions. -/
theorem leg3Len_deep (L : ℤ) : leg3Len L (L + 9) (L + 7) (L + 4) = 18 := by
  simp only [leg3Len]
  omega

/-- Its levels, position by position. -/
theorem leg3Walk_deep_val (L : ℤ) (u : ℕ) (hu : u < 18) :
    leg3Walk L (L + 9) (L + 7) (L + 4) u =
      L + (if u ≤ 4 then (3 + u : ℤ) else if u ≤ 10 then (11 - u : ℤ) else (u - 9 : ℤ)) := by
  simp only [leg3Walk]
  split_ifs <;> omega

/-- The landmark at the peak of the deep walk. -/
theorem leg3Walk_deep_four (L : ℤ) : leg3Walk L (L + 9) (L + 7) (L + 4) 4 = L + 7 := by
  rw [leg3Walk_deep_val L 4 (by norm_num)]
  norm_num

/-- A descent to `L + 1` is served only by the positions `9`, `10`, `11` of the deep walk. -/
theorem leg3Walk_deep_low_pos {L v : ℤ} {p : ℕ} (hp : p < 18) (hv : v ≤ L + 1)
    (h : |v - leg3Walk L (L + 9) (L + 7) (L + 4) p| ≤ 1) : 9 ≤ p := by
  rw [leg3Walk_deep_val L p hp, abs_le] at h
  by_contra hc
  interval_cases p <;> simp_all <;> omega

/-- **The valley clause of the deep walk is necessary.** An arm that folds onto
`L+3 → L+7 → L+1 → L+8` has, before every descent to `L + 1`, a time at `L + 6` or above at a step
at least `4` and at least five steps earlier. -/
theorem deepValley_of_foldsOnto_leg3deep {m : ℕ} {f : Fin m → ℤ} {L : ℤ}
    (h : FoldsOnto f (leg3Len L (L + 9) (L + 7) (L + 4))
      (leg3Walk L (L + 9) (L + 7) (L + 4))) :
    ∀ d : Fin m, f d ≤ L + 1 → ∃ j : Fin m, 4 ≤ j.val ∧ j.val + 5 ≤ d.val ∧ L + 6 ≤ f j := by
  intro d hd
  have hpos : ∀ p : ℕ, p < leg3Len L (L + 9) (L + 7) (L + 4) →
      |f d - leg3Walk L (L + 9) (L + 7) (L + 4) p| ≤ 1 → 9 ≤ p := by
    intro p hp hpv
    rw [leg3Len_deep] at hp
    exact leg3Walk_deep_low_pos hp hd hpv
  obtain ⟨j, hj0, hjd, hjv⟩ := foldsOnto_landmark1 h d 4 9 (by norm_num) hpos
  rw [leg3Walk_deep_four, abs_le] at hjv
  exact ⟨j, hj0, by omega, by omega⟩

end HPC.Fold
