import HPC.Fold.ClosureF

/-!
# The batch-19 mechanism does not suffice over the faithful model

`highExitValleyF_of_attainsMin` reduces `HighExitValleyF` to `AttainsMinBeforeExceedF`: the
claim that an arm which exceeds `hStar + 1` has already attained the ambient minimum `L`.
The sub-claim was refuted in batch 19 by a sequence now known to be no chain; this file
refutes it again by a **member of the faithful model**, so the reduction is not a route to
`HighExitValleyF` and the mechanism of the sketch covers only part of the problem.

The witness is thin — `σ = ρ` — and is the shape produced by iterating Bing's crooked
pattern: the thirty-term chain

    0 1 2 1 2 3 2 1 2 3 2 3 4 3 2 3 2 1 2 3 2 3 4 3 2 3 4 3 4 5

at basepoint `5`, where `p = 3`, `H = 5`, `L = 0` and `hStar = 3`. Its forward arm reaches
`5 = hStar + 2` at its last index and never visits level `0`, the global minimum, which sits
entirely on the backward side. The valley clause itself still holds there — the arm visits
`1 = L + 1` at its second index, and `s = 0` is the only admissible peak index — so this
refutes the sub-claim and not the conjecture.
-/

namespace HPC.Fold

/-- The thirty-term faithful chain. -/
def hevSeq : Fin 30 → ℤ :=
  ![0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 5]

/-- Its basepoint. -/
def hevPt : Fin 30 := ⟨5, by omega⟩

@[simp] theorem hevPt_val : hevPt.val = 5 := rfl

/-- The level at the basepoint. -/
theorem hevSeq_pt : hevSeq hevPt = 3 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem hevSeq_isLip : IsLip hevSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [hevSeq]

set_option maxRecDepth 10000000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- And it is a member of the faithful model, read thin: `σ = ρ`. -/
theorem hevSeq_isCrookedIvF : IsCrookedIvF hevSeq hevSeq :=
  isCrookedIvF_of_check2 (by unfold IsCrookedIvFCheck2 ivEnd clampIdx; decide +kernel)

set_option maxRecDepth 10000 in
/-- The forward arm drops to `1 = p − 2` at its second index, so its peak demand is `3`. -/
theorem hevSeq_hStarArm_G : hStarArm (armG hevSeq hevPt) 3 = 3 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
/-- The backward arm drops at its third index, so its peak demand is `3` as well. -/
theorem hevSeq_hStarArm_T : hStarArm (armT hevSeq hevPt) 3 = 3 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

/-- Hence the bump height is `3`, one below the cap `H − 1 = 4`. -/
theorem hevSeq_hStar : hStar hevSeq hevPt 5 0 = 3 := by
  rw [hStar, hevSeq_pt, hevSeq_hStarArm_G, hevSeq_hStarArm_T]
  norm_num

/-- **The sub-claim of the batch-19 mechanism is false over the faithful model.** -/
theorem not_attainsMinBeforeExceedF : ¬ AttainsMinBeforeExceedF := by
  intro h
  obtain ⟨hG, -⟩ := h 30 hevSeq hevSeq hevPt 5 0 hevSeq_isLip hevSeq_isCrookedIvF
    (by decide) (by decide) (by decide) ⟨0, by decide⟩ ⟨29, by decide⟩
  obtain ⟨l, hl, hlv⟩ := hG ⟨24, by decide⟩ (by rw [hevSeq_hStar]; decide)
  have hlt : l.val < 24 := hl
  have hne : ∀ l : Fin (30 - hevPt.val), l.val < 24 → armG hevSeq hevPt l ≠ 0 := by decide
  exact hne l hlt hlv

end HPC.Fold
