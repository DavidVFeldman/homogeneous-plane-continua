import HPC.Fold.LandWalkFail

/-!
# The base of the induction of `LandWalkPSuffices`

Question 4 of batch 64 asks for the induction that proves `LandWalkPSuffices`
(`HPC/Fold/LandWalkFail.lean`): the corrected landmark sentence `LandWalkP` implies folding, for a
walk with no unit leg. This file proves its **base cases**, and they need no landmark sentence at
all:

* `foldsOnto_walk_nil` — a walk with no turn is a single time, and an arm all of whose levels it
  serves folds onto it by the constant itinerary;
* `foldsOnto_walk_one_turn` — a walk with one turn is monotone, and an arm all of whose levels it
  serves folds onto it by the *clamped* itinerary `β j = (min (f j - s - 1) (t - s)).toNat`
  (ascending) or its reflection (descending): the clamp is 1-Lipschitz, it starts at `0` because
  the arm starts within one of `s`, and it serves because the walk covers the whole interval
  between its ends.

So at a walk of at most one turn the sentence is not needed
(`landWalkP_suffices_of_length_le_one`), and the content of `LandWalkPSuffices` is entirely in the
inductive step, where the walk turns and the arm may have to choose a leg.

The measurements behind the statement are `probe64.c` (logs `probe64.log`, `probe64b.log`): over
all walks of at most five turns with levels in `[0, 5]` and all arms of at most twelve times, and
over all walks of at most four turns with levels in `[0, 6]` and arms of at most thirteen times,
no walk without a unit leg has a counterexample to sufficiency.
-/

namespace HPC.Fold

/-! ## The walk of one turn, in closed form -/

theorem walkLen_one (s t : ℤ) : walkLen s [t] = (t - s).natAbs + 1 := by
  simp [walkLen]

/-- **The ascending walk of one turn**: `walkList s [t] p = min (s + p) t`. -/
theorem walkList_one_up {s t : ℤ} (h : s ≤ t) (p : ℕ) :
    walkList s [t] p = min (s + (p : ℤ)) t := by
  rcases Nat.lt_or_ge p (t - s).natAbs with hp | hp
  · rw [walkList_cons_lt hp, if_pos h]
    have : (p : ℤ) < t - s := by
      have : ((t - s).natAbs : ℤ) = t - s := by omega
      omega
    omega
  · rw [walkList_cons_ge hp, walkList_nil]
    have : ((t - s).natAbs : ℤ) = t - s := by omega
    omega

/-- **The descending walk of one turn**: `walkList s [t] p = max (s - p) t`. -/
theorem walkList_one_down {s t : ℤ} (h : t ≤ s) (p : ℕ) :
    walkList s [t] p = max (s - (p : ℤ)) t := by
  rcases Nat.lt_or_ge p (t - s).natAbs with hp | hp
  · rw [walkList_cons_lt hp]
    have hne : ((t - s).natAbs : ℤ) = s - t := by omega
    have hp' : (p : ℤ) < s - t := by omega
    by_cases hst : s ≤ t
    · have : s = t := by omega
      omega
    · rw [if_neg hst]; omega
  · rw [walkList_cons_ge hp, walkList_nil]
    have : ((t - s).natAbs : ℤ) = s - t := by omega
    omega

/-! ## The two base cases -/

/-- **A walk with no turn.** It is the single time `s`, so an arm it serves stands within one of
`s` throughout and folds onto it by the constant itinerary. -/
theorem foldsOnto_walk_nil {m : ℕ} (f : Fin m → ℤ) (s : ℤ)
    (hband : ∀ j : Fin m, ∃ p : ℕ, p < walkLen s ([] : List ℤ) ∧
      |f j - walkList s ([] : List ℤ) p| ≤ 1) :
    FoldsOnto f (walkLen s ([] : List ℤ)) (walkList s ([] : List ℤ)) := by
  refine ⟨fun _ => 0, fun _ => by simp [walkLen], fun j j' _ => by simp, fun _ _ => rfl, ?_⟩
  intro j
  obtain ⟨p, -, hp⟩ := hband j
  simpa using hp

/-- **A walk with one turn.** It is monotone, and the clamped itinerary folds every arm it
serves that starts within one of its first level. -/
theorem foldsOnto_walk_one_turn {m : ℕ} (f : Fin m → ℤ) (s t : ℤ) (hlip : IsLip f)
    (h0 : ∀ j : Fin m, j.val = 0 → |f j - s| ≤ 1)
    (hband : ∀ j : Fin m, ∃ p : ℕ, p < walkLen s [t] ∧ |f j - walkList s [t] p| ≤ 1) :
    FoldsOnto f (walkLen s [t]) (walkList s [t]) := by
  have hlen : walkLen s [t] = (t - s).natAbs + 1 := walkLen_one s t
  rcases le_total s t with hst | hst
  · -- the ascending walk
    have hband' : ∀ j : Fin m, s - 1 ≤ f j ∧ f j ≤ t + 1 := by
      intro j
      obtain ⟨p, -, hp⟩ := hband j
      rw [walkList_one_up hst] at hp
      have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
      rw [abs_le] at hp
      omega
    refine ⟨fun j => (min (f j - s - 1) (t - s)).toNat, ?_, ?_, ?_, ?_⟩
    · intro j
      have := (hband' j).2
      have hn : ((t - s).natAbs : ℤ) = t - s := by omega
      show (min (f j - s - 1) (t - s)).toNat < walkLen s [t]
      rw [hlen]
      omega
    · intro j j' hjj'
      have := hlip j j' hjj'
      rw [abs_le] at this
      show |((min (f j' - s - 1) (t - s)).toNat : ℤ) - ((min (f j - s - 1) (t - s)).toNat : ℤ)| ≤ 1
      rw [abs_le]
      omega
    · intro j hj
      have := h0 j hj
      rw [abs_le] at this
      show (min (f j - s - 1) (t - s)).toNat = 0
      omega
    · intro j
      obtain ⟨hlo, hhi⟩ := hband' j
      show |f j - walkList s [t] (min (f j - s - 1) (t - s)).toNat| ≤ 1
      rw [walkList_one_up hst, abs_le]
      omega
  · -- the descending walk
    have hband' : ∀ j : Fin m, t - 1 ≤ f j ∧ f j ≤ s + 1 := by
      intro j
      obtain ⟨p, -, hp⟩ := hband j
      rw [walkList_one_down hst] at hp
      have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
      rw [abs_le] at hp
      omega
    refine ⟨fun j => (min (s - 1 - f j) (s - t)).toNat, ?_, ?_, ?_, ?_⟩
    · intro j
      have := (hband' j).1
      have hn : ((t - s).natAbs : ℤ) = s - t := by omega
      show (min (s - 1 - f j) (s - t)).toNat < walkLen s [t]
      rw [hlen]
      omega
    · intro j j' hjj'
      have := hlip j j' hjj'
      rw [abs_le] at this
      show |((min (s - 1 - f j') (s - t)).toNat : ℤ) - ((min (s - 1 - f j) (s - t)).toNat : ℤ)| ≤ 1
      rw [abs_le]
      omega
    · intro j hj
      have := h0 j hj
      rw [abs_le] at this
      show (min (s - 1 - f j) (s - t)).toNat = 0
      omega
    · intro j
      obtain ⟨hlo, hhi⟩ := hband' j
      show |f j - walkList s [t] (min (s - 1 - f j) (s - t)).toNat| ≤ 1
      rw [walkList_one_down hst, abs_le]
      omega

/-- **`LandWalkPSuffices` at a walk of at most one turn.** Neither the landmark sentence nor the
hypothesis on the legs is used: the base of the induction is unconditional. -/
theorem landWalkP_suffices_of_length_le_one {m : ℕ} (f : Fin m → ℤ) (s : ℤ) (ts : List ℤ)
    (hts : ts.length ≤ 1) (hlip : IsLip f)
    (h0 : ∀ j : Fin m, j.val = 0 → |f j - s| ≤ 1)
    (hband : ∀ j : Fin m, ∃ p : ℕ, p < walkLen s ts ∧ |f j - walkList s ts p| ≤ 1) :
    FoldsOnto f (walkLen s ts) (walkList s ts) := by
  match ts, hts with
  | [], _ => exact foldsOnto_walk_nil f s hband
  | [t], _ => exact foldsOnto_walk_one_turn f s t hlip h0 hband

end HPC.Fold
