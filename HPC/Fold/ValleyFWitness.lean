import HPC.Fold.ClosureF

/-!
# `HighExitValleyF` and `LowExitPeakF` are false as well

One member of the faithful model refutes both remaining conjectures. It is thin — `σ = ρ` —
and is a concatenation of Bing's crooked patterns, seventy-one links long:

    0 1 2 1 2 3 2 1 2 3 2 3 4 3 2 3 2 1 2 3 2 3 4 3 2 3 4 3 4 5 4 3 4 3 2 3 4 3 2 3 2 1
    2 3 2 3 4 3 2 3 4 3 4 5 4 3 4 3 2 3 4 3 4 5 4 3 4 5 4 5 6

with `H = 6` and `L = 0`, both attained.

* At basepoint `46` the level is `p = 4` and `hStar = 4`. On the forward arm no index reaches
  `hStar` in the phase-adjusted sense before index `0`, so `s = 0` passes the peak-index test
  vacuously, and at the arm's last index the level is `6 > hStar + 1`; but the arm never
  descends to `L + 1 = 1` at all, so the valley clause fails.
* At basepoint `24` the level is `p = 2` and `lStar = 2`. On the backward arm, reflected,
  `s = 0` passes for the same reason, the last index of the arm carries `0 < lStar − 1`, and
  the arm never rises to `H − 1 = 5` in between, so the reflected valley clause fails.

With `not_exitReachF` this settles all three conjectures of the batch in the negative, at
genuine chains.
-/

namespace HPC.Fold

/-- The thin member of the faithful model refuting the two valley conjectures. -/
def hlSeq : Fin 71 → ℤ :=
  ![0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 5,
    4, 3, 4, 3, 2, 3, 4, 3, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 5, 4, 3, 4, 3, 2, 3,
    4, 3, 4, 5, 4, 3, 4, 5, 4, 5, 6]

/-- The basepoint refuting `HighExitValleyF`. -/
def hlPtH : Fin 71 := ⟨46, by omega⟩

/-- The basepoint refuting `LowExitPeakF`. -/
def hlPtL : Fin 71 := ⟨24, by omega⟩

@[simp] theorem hlPtH_val : hlPtH.val = 46 := rfl

@[simp] theorem hlPtL_val : hlPtL.val = 24 := rfl

theorem hlSeq_ptH : hlSeq hlPtH = 4 := by decide

theorem hlSeq_ptL : hlSeq hlPtL = 2 := by decide

set_option maxRecDepth 100000 in
/-- The sequence is 1-Lipschitz. -/
theorem hlSeq_isLip : IsLip hlSeq := by unfold IsLip; decide

set_option maxRecDepth 40000000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 20000000 in
set_option maxHeartbeats 20000000 in
/-- And it is a member of the faithful model, read thin. -/
theorem hlSeq_isCrookedIvF : IsCrookedIvF hlSeq hlSeq :=
  isCrookedIvF_of_check2 (by unfold IsCrookedIvFCheck2 ivEnd clampIdx; decide +kernel)

/-! ## `HighExitValleyF` fails at basepoint `46` -/

set_option maxRecDepth 100000 in
/-- The forward arm at `46` drops to `p − 2` at its third index, so its peak demand is `4`. -/
theorem hlSeq_hStarArm_G : hStarArm (armG hlSeq hlPtH) 4 = 4 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- So does the backward arm. -/
theorem hlSeq_hStarArm_T : hStarArm (armT hlSeq hlPtH) 4 = 4 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

/-- Hence the bump height at `46` is `4`, below the cap `H − 1 = 5`. -/
theorem hlSeq_hStar : hStar hlSeq hlPtH 6 0 = 4 := by
  rw [hStar, hlSeq_ptH, hlSeq_hStarArm_G, hlSeq_hStarArm_T]
  norm_num

set_option maxRecDepth 400000 in
/-- **`HighExitValleyF` is false.** -/
theorem not_highExitValleyF : ¬ HighExitValleyF := by
  intro h
  obtain ⟨hG, -⟩ := h 71 hlSeq hlSeq hlPtH 6 0 hlSeq_isLip hlSeq_isCrookedIvF
    (by decide) (by decide) (by norm_num) ⟨⟨0, by decide⟩, by decide⟩ ⟨⟨70, by decide⟩, by decide⟩
  have hval := hG 0 (fun j hj => absurd hj (by omega))
  obtain ⟨j, -, hj24, hjL⟩ := hval ⟨24, by decide⟩ (Nat.zero_le _)
    (by rw [hlSeq_hStar]; decide)
  have hne : ∀ j : Fin (71 - hlPtH.val), j.val < 24 → ¬ armG hlSeq hlPtH j ≤ 0 + 1 := by decide
  exact hne j hj24 hjL

/-! ## `LowExitPeakF` fails at basepoint `24` -/

set_option maxRecDepth 100000 in
/-- The forward arm at `24`, reflected, leaves its window at its third index, so its valley
demand is `2`. -/
theorem hlSeq_hStarArm_negG : hStarArm (fun j => - armG hlSeq hlPtL j) (-2) = -2 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- And so does the backward arm. -/
theorem hlSeq_hStarArm_negT : hStarArm (fun j => - armT hlSeq hlPtL j) (-2) = -2 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

/-- Hence the valley depth at `24` is `2`. -/
theorem hlSeq_lStar : lStar hlSeq hlPtL 6 0 = 2 := by
  have hG : lStarArm (armG hlSeq hlPtL) 2 = 2 := by
    rw [lStarArm, hlSeq_hStarArm_negG]; omega
  have hT : lStarArm (armT hlSeq hlPtL) 2 = 2 := by
    rw [lStarArm, hlSeq_hStarArm_negT]; omega
  rw [lStar, hlSeq_ptL, hG, hT]
  norm_num

set_option maxRecDepth 400000 in
/-- **`LowExitPeakF` is false.** -/
theorem not_lowExitPeakF : ¬ LowExitPeakF := by
  intro h
  obtain ⟨-, hT⟩ := h 71 hlSeq hlSeq hlPtL 6 0 hlSeq_isLip hlSeq_isCrookedIvF
    (by decide) (by decide) (by norm_num) ⟨⟨0, by decide⟩, by decide⟩ ⟨⟨70, by decide⟩, by decide⟩
  have hval := hT 0 (fun j hj => absurd hj (by omega))
  obtain ⟨j, -, hj24, hjL⟩ := hval ⟨24, by decide⟩ (Nat.zero_le _)
    (by rw [hlSeq_lStar]; decide)
  have hne : ∀ j : Fin (hlPtL.val + 1), j.val < 24 → ¬ - armT hlSeq hlPtL j ≤ -6 + 1 := by decide
  exact hne j hj24 hjL

end HPC.Fold
