import HPC.Fold.Landmark

/-!
# Landmarks, any number of them

`foldsOnto_landmark1`, `foldsOnto_landmark2` (`HPC/Fold/Landmark.lean`) and
`foldsOnto_landmark3` (`HPC/Fold/Leg4Land.lean`) read one, two and three landmarks off a fold.
Each new leg of a walk has needed a new copy of the same argument, and the four-leg criterion of
batch 59 used all three. This file proves the statement once for a chain of any length, which is
the necessity half of the landmark sentence of a walk with any number of legs — question 3 of the
batch-60 commission, for the half that does not need an engine.

The statement is about an arbitrary walk `c` and an arbitrary increasing list of its positions
`q 0 ≤ q 1 ≤ ⋯ ≤ q r`. If the arm's level at a step `d` can only be served by the walk positions
`q r` and later, then the itinerary passes through every earlier landmark in turn, at steps
`j 0 ≤ j 1 ≤ ⋯ ≤ j r = d`, where

* `j 0 ≥ q 0` — the itinerary starts at the walk position `0` and moves by at most one position
  per step;
* `j (s+1) ≥ j s + (q (s+1) - q s)` — for the same reason;
* and at the step `j s` the arm is within one of the walk's level `c (q s)`.

`foldsOnto_landmarkN` is that, and `foldsOnto_landmark1`, `foldsOnto_landmark2` and
`foldsOnto_landmark3` are its cases `r = 1, 2, 3` (`foldsOnto_landmarkN_one`,
`foldsOnto_landmarkN_two` check the first two against it).
-/

namespace HPC.Fold

section Chain

variable {m : ℕ} {β : Fin m → ℕ}

/-- **The itinerary passes through a chain of positions.** Stated on the itinerary itself: if the
itinerary is at the position `q r` or later at the step `d`, there are steps
`j 0 ≤ ⋯ ≤ j r = d` at which it is at `q 0, …, q r`, with the index gaps the positions dictate. -/
theorem beta_chain (hz : ∀ j : Fin m, j.val = 0 → β j = 0)
    (hs : ∀ j j' : Fin m, j'.val = j.val + 1 → |(β j' : ℤ) - (β j : ℤ)| ≤ 1)
    (q : ℕ → ℕ) (hmono : ∀ s, q s ≤ q (s + 1)) :
    ∀ (r : ℕ) (d : Fin m), q r ≤ β d →
      ∃ j : ℕ → Fin m, j r = d ∧ q 0 ≤ (j 0).val ∧
        (∀ s, s < r → (j s).val + (q (s + 1) - q s) ≤ (j (s + 1)).val) ∧
        (∀ s, s < r → β (j s) = q s) := by
  classical
  intro r
  induction r with
  | zero =>
      intro d hd
      refine ⟨fun _ => d, rfl, ?_, ?_, ?_⟩
      · show q 0 ≤ d.val
        have := beta_le_val hz hs d.val d rfl
        omega
      · intro s hs'
        omega
      · intro s hs'
        omega
  | succ r ih =>
      intro d hd
      have hdm := d.isLt
      have hzm : 0 < m := by omega
      have hqr : q r ≤ β d := le_trans (hmono r) hd
      obtain ⟨k, -, hkd, hkβ⟩ :=
        beta_hits hs d.val d rfl (q r) hqr ⟨0, hzm⟩ (by simp) (by rw [hz ⟨0, hzm⟩ rfl]; omega)
      obtain ⟨j', hj'r, hj'0, hj'gap, hj'β⟩ := ih k (by omega)
      refine ⟨fun s => if s = r + 1 then d else j' s, by simp, ?_, ?_, ?_⟩
      · by_cases h : (0 : ℕ) = r + 1
        · omega
        · simpa [h] using hj'0
      · intro s hsr
        rcases Nat.lt_or_ge s r with hlt | hge
        · show (if s = r + 1 then d else j' s).val + _ ≤
            (if s + 1 = r + 1 then d else j' (s + 1)).val
          rw [if_neg (show s ≠ r + 1 by omega), if_neg (show s + 1 ≠ r + 1 by omega)]
          exact hj'gap s hlt
        · have hsreq : s = r := by omega
          subst hsreq
          show (if s = s + 1 then d else j' s).val + _ ≤
            (if s + 1 = s + 1 then d else j' (s + 1)).val
          rw [if_neg (show s ≠ s + 1 by omega), if_pos rfl, hj'r]
          have hdist := beta_dist hs (d.val - k.val) k d (by omega)
          push_cast at hdist
          omega
      · intro s hsr
        rcases Nat.lt_or_ge s r with hlt | hge
        · show β (if s = r + 1 then d else j' s) = q s
          rw [if_neg (show s ≠ r + 1 by omega)]
          exact hj'β s hlt
        · have hsreq : s = r := by omega
          subst hsreq
          show β (if s = s + 1 then d else j' s) = q s
          rw [if_neg (show s ≠ s + 1 by omega), hj'r]
          exact hkβ

/-- **The landmark sentence for a chain of any length.** If the arm's level at the step `d` is
served only by the walk positions `q r` and later, then for every increasing chain of earlier
positions `q 0 ≤ ⋯ ≤ q r` there are steps `j 0 ≤ ⋯ ≤ j r = d` of the arm at which it is within one
of the walk's levels `c (q s)`, with `j 0 ≥ q 0`, the gaps `j (s+1) - j s ≥ q (s+1) - q s`, and
`d - j (r-1) ≥ q r - q (r-1)`.

This is `foldsOnto_landmark1`, `foldsOnto_landmark2` and `foldsOnto_landmark3` at once, for a walk
with any number of legs. -/
theorem foldsOnto_landmarkN {m len : ℕ} {f : Fin m → ℤ} {c : ℕ → ℤ}
    (h : FoldsOnto f len c) (d : Fin m) (r : ℕ) (q : ℕ → ℕ) (hmono : ∀ s, q s ≤ q (s + 1))
    (hd : ∀ p : ℕ, p < len → |f d - c p| ≤ 1 → q r ≤ p) :
    ∃ j : ℕ → Fin m, j r = d ∧ q 0 ≤ (j 0).val ∧
      (∀ s, s < r → (j s).val + (q (s + 1) - q s) ≤ (j (s + 1)).val) ∧
      (∀ s, s < r → |f (j s) - c (q s)| ≤ 1) := by
  obtain ⟨β, hlen, hs, hz, hval⟩ := h
  obtain ⟨j, hjr, hj0, hjgap, hjβ⟩ :=
    beta_chain hz hs q hmono r d (hd (β d) (hlen d) (hval d))
  refine ⟨j, hjr, hj0, hjgap, ?_⟩
  intro s hsr
  have := hval (j s)
  rwa [hjβ s hsr] at this

/-! ## The one- and two-landmark cases, recovered -/

/-- `foldsOnto_landmark1` is the case `r = 1`. -/
theorem foldsOnto_landmarkN_one {m len : ℕ} {f : Fin m → ℤ} {c : ℕ → ℤ}
    (h : FoldsOnto f len c) (d : Fin m) (q0 q1 : ℕ) (h01 : q0 ≤ q1)
    (hd : ∀ p : ℕ, p < len → |f d - c p| ≤ 1 → q1 ≤ p) :
    ∃ j : Fin m, q0 ≤ j.val ∧ j.val + (q1 - q0) ≤ d.val ∧ |f j - c q0| ≤ 1 := by
  obtain ⟨j, hj1, hj0, hjgap, hjval⟩ :=
    foldsOnto_landmarkN h d 1 (fun s => if s = 0 then q0 else q1)
      (by intro s; by_cases hs : s = 0 <;> simp [hs, h01])
      (by simpa using hd)
  refine ⟨j 0, by simpa using hj0, ?_, by simpa using hjval 0 (by omega)⟩
  have hgap := hjgap 0 (by omega)
  simp only [if_neg (by omega : (0 : ℕ) + 1 ≠ 0)] at hgap
  rw [hj1] at hgap
  exact hgap

/-- `foldsOnto_landmark2` is the case `r = 2`. -/
theorem foldsOnto_landmarkN_two {m len : ℕ} {f : Fin m → ℤ} {c : ℕ → ℤ}
    (h : FoldsOnto f len c) (d : Fin m) (q0 q1 q2 : ℕ) (h01 : q0 ≤ q1) (h12 : q1 ≤ q2)
    (hd : ∀ p : ℕ, p < len → |f d - c p| ≤ 1 → q2 ≤ p) :
    ∃ j k : Fin m, q0 ≤ j.val ∧ j.val + (q1 - q0) ≤ k.val ∧ k.val + (q2 - q1) ≤ d.val ∧
      |f j - c q0| ≤ 1 ∧ |f k - c q1| ≤ 1 :=
  foldsOnto_landmark2 h d q0 q1 q2 h01 h12 hd

end Chain

end HPC.Fold
