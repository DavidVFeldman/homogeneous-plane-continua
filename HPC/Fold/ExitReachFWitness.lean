import HPC.Fold.ClosureF

/-!
# `ExitReachF` is false: a counterexample inside the faithful model

The first of the three conjectures fails over `IsCrookedIvF`. The witness is a forty-two term
member of the model,

    ρ = 4 3 2 3 2 1 2 2 2 1 2 1 0 1 2 1 2 3 2 1 2 2 2 3 4 3 2 3 2 1 2 3 2 3 4 3 2 3 4 3 4 5
    σ = ρ except σ 7 = 3 and σ 21 = 3,

at basepoint `2`, with `p = 2`, `H = 5`, `L = 0`, both extremes attained. The backward arm is
`2, 3, 4`: it never leaves the window below, so its peak demand is `4` and the bump height is
`hStar = 4`, the cap. The forward arm drops to `0` at its eleventh index and before that never
exceeds `3` in the phase-adjusted sense, so `OkLam` fails on it. Dually the forward arm attains
`L = 0`, so the valley depth is the floor `lStar = 1`, while the reflected backward arm leaves
its window at its third index with reflected reach only `−2`, so `OkVee` fails on the backward
arm. Both disjuncts are therefore false at this basepoint.

By `realization` (batch 22) the witness is the `(minIdx, maxIdx)` pair of an explicit chain of
open rectangles crooked in a chain of strips, so this refutes a statement about chains, not
merely about sequences.
-/

namespace HPC.Fold

/-- The refuting member of the faithful model: the lower ends. -/
def exfSeq : Fin 42 → ℤ :=
  ![4, 3, 2, 3, 2, 1, 2, 2, 2, 1, 2, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 3, 4, 3, 2, 3, 2, 1,
    2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 5]

/-- The upper ends: the two links at indices `7` and `21` are the wide ones. -/
def exfSig : Fin 42 → ℤ :=
  ![4, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4, 3, 2, 3, 2, 1,
    2, 3, 2, 3, 4, 3, 2, 3, 4, 3, 4, 5]

/-- Its basepoint. -/
def exfPt : Fin 42 := ⟨2, by omega⟩

@[simp] theorem exfPt_val : exfPt.val = 2 := rfl

/-- The level at the basepoint. -/
theorem exfSeq_pt : exfSeq exfPt = 2 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem exfSeq_isLip : IsLip exfSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [exfSeq]

set_option maxRecDepth 40000000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 20000000 in
set_option maxHeartbeats 20000000 in
/-- And it is a member of the faithful model. -/
theorem exfSeq_isCrookedIvF : IsCrookedIvF exfSeq exfSig :=
  isCrookedIvF_of_check2 (by unfold IsCrookedIvFCheck2 ivEnd clampIdx; decide +kernel)

set_option maxRecDepth 10000 in
/-- The backward arm `2, 3, 4` never leaves the window, so its peak demand is the top level. -/
theorem exfSeq_hStarArm_T : hStarArm (armT exfSeq exfPt) 2 = 4 :=
  hStarArm_eq_of_attained _ _ _ ⟨2, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
/-- The forward arm attains the global minimum before leaving its window, so its valley
demand, in negated form, is `0`. -/
theorem exfSeq_hStarArm_negG : hStarArm (fun j => - armG exfSeq exfPt j) (-2) = 0 :=
  hStarArm_eq_of_attained _ _ _ ⟨10, by decide⟩ (by decide) (by decide) (by decide)

/-- Hence the bump height is the cap `H − 1 = 4`. -/
theorem exfSeq_hStar : (4 : ℤ) ≤ hStar exfSeq exfPt 5 0 := by
  have h := exfSeq_hStarArm_T
  rw [hStar, exfSeq_pt]
  simp only [le_min_iff, le_max_iff]
  omega

/-- And the valley depth is the floor `L + 1 = 1`. -/
theorem exfSeq_lStar : lStar exfSeq exfPt 5 0 ≤ 1 := by
  have h : lStarArm (armG exfSeq exfPt) 2 = 0 := by
    rw [lStarArm, exfSeq_hStarArm_negG]; omega
  rw [lStar, exfSeq_pt]
  simp only [max_le_iff, min_le_iff]
  omega

set_option maxRecDepth 100000 in
/-- Before its first drop the forward arm's phase-adjusted levels never exceed `3`. -/
theorem exfSeq_bound_G (k : Fin (42 - exfPt.val))
    (hk : ∀ k' : Fin (42 - exfPt.val), k' ≤ k → (2 : ℤ) - 1 ≤ armG exfSeq exfPt k') :
    armG exfSeq exfPt k + phase (armG exfSeq exfPt) k ≤ 3 := by
  have hd : ∀ k : Fin (42 - exfPt.val),
      (∀ k' : Fin (42 - exfPt.val), k' ≤ k → (2 : ℤ) - 1 ≤ armG exfSeq exfPt k') →
      k.val ≤ 9 := by decide
  have hk9 := hd k hk
  by_cases hlow : k.val ≤ 1
  · have hno : ∀ k : Fin (42 - exfPt.val), k.val ≤ 1 →
        ¬ ∃ t : Fin (42 - exfPt.val), t.val ≤ k.val ∧ NonAscAt (armG exfSeq exfPt) t := by
      decide
    rw [phase_eq_zero _ _ (hno k hlow)]
    have hb : ∀ k : Fin (42 - exfPt.val), k.val ≤ 1 → armG exfSeq exfPt k ≤ 3 := by decide
    have := hb k hlow
    omega
  · have hb : ∀ k : Fin (42 - exfPt.val), ¬ k.val ≤ 1 → k.val ≤ 9 →
        armG exfSeq exfPt k ≤ 2 := by decide
    have := hb k hlow hk9
    rcases phase_zero_or_one (armG exfSeq exfPt) k with e | e <;> rw [e] <;> omega

/-- So the forward arm's reach falls short of `hStar`. -/
theorem exfSeq_hReach_G : hReach (armG exfSeq exfPt) 2 ≤ 3 :=
  hReach_le_of_pre (by decide) 2 3 (by decide) exfSeq_bound_G

set_option maxRecDepth 10000 in
/-- The reflected backward arm leaves its window at its third index, and before that its
phase-adjusted levels never exceed `−2`. -/
theorem exfSeq_bound_negT (k : Fin (exfPt.val + 1))
    (hk : ∀ k' : Fin (exfPt.val + 1), k' ≤ k → (-2 : ℤ) - 1 ≤ - armT exfSeq exfPt k') :
    (- armT exfSeq exfPt k) + phase (fun j => - armT exfSeq exfPt j) k ≤ -2 := by
  have hd : ∀ k : Fin (exfPt.val + 1),
      (∀ k' : Fin (exfPt.val + 1), k' ≤ k → (-2 : ℤ) - 1 ≤ - armT exfSeq exfPt k') →
      k.val ≤ 1 := by decide
  have hk1 := hd k hk
  rcases Nat.eq_zero_or_pos k.val with h0 | hpos
  · have hke : k = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst hke
    rw [phase_at_zero]
    decide
  · have hb : ∀ k : Fin (exfPt.val + 1), 0 < k.val → k.val ≤ 1 →
        - armT exfSeq exfPt k ≤ -3 := by decide
    have := hb k hpos hk1
    rcases phase_zero_or_one (fun j => - armT exfSeq exfPt j) k with e | e <;> rw [e] <;> omega

/-- And the reflected backward arm's reach falls short of `− lStar`. -/
theorem exfSeq_hReach_negT : hReach (fun j => - armT exfSeq exfPt j) (-2) ≤ -2 :=
  hReach_le_of_pre (by decide) (-2) (-2) (by decide) exfSeq_bound_negT

/-- **`ExitReachF` is false.** The first hypothesis of the batch-16 route fails over the
faithful model, hence at a genuine chain. -/
theorem not_exitReachF : ¬ ExitReachF := by
  intro h
  have key := h 42 exfSeq exfSig exfPt 5 0 exfSeq_isLip exfSeq_isCrookedIvF
    (by decide) (by decide) (by norm_num) ⟨⟨12, by decide⟩, by decide⟩ ⟨⟨41, by decide⟩, by decide⟩
  rw [exfSeq_pt] at key
  have hh := exfSeq_hStar
  have hl := exfSeq_lStar
  rcases key with ⟨hG, -⟩ | ⟨-, hT⟩
  · rcases hG with hnd | hr
    · exact hnd ⟨⟨10, by decide⟩, by decide⟩
    · have := exfSeq_hReach_G
      omega
  · rcases hT with hnd | hr
    · exact hnd ⟨⟨2, by decide⟩, by decide⟩
    · have := exfSeq_hReach_negT
      omega

set_option maxRecDepth 100000 in
/-- Up to its first drop and at it, the forward arm's phase-adjusted level never exceeds `3`;
so no index at or before the drop is a peak index for `hStar = 4`. -/
theorem exfSeq_G_early (s : Fin (42 - exfPt.val)) (hs : s.val ≤ 10) :
    armG exfSeq exfPt s + phase (armG exfSeq exfPt) s ≤ 3 := by
  by_cases hlow : s.val ≤ 1
  · have hno : ∀ k : Fin (42 - exfPt.val), k.val ≤ 1 →
        ¬ ∃ t : Fin (42 - exfPt.val), t.val ≤ k.val ∧ NonAscAt (armG exfSeq exfPt) t := by
      decide
    rw [phase_eq_zero _ _ (hno s hlow)]
    have hb : ∀ k : Fin (42 - exfPt.val), k.val ≤ 1 → armG exfSeq exfPt k ≤ 3 := by decide
    have := hb s hlow
    omega
  · have hb : ∀ k : Fin (42 - exfPt.val), ¬ k.val ≤ 1 → k.val ≤ 10 →
        armG exfSeq exfPt k ≤ 2 := by decide
    have := hb s hlow hs
    rcases phase_zero_or_one (armG exfSeq exfPt) s with e | e <;> rw [e] <;> omega

set_option maxRecDepth 10000 in
/-- The reflected backward arm never reaches `−2` in the phase-adjusted sense. -/
theorem exfSeq_negT_all (s : Fin (exfPt.val + 1)) :
    (- armT exfSeq exfPt s) + phase (fun j => - armT exfSeq exfPt j) s ≤ -2 := by
  rcases Nat.eq_zero_or_pos s.val with h0 | hpos
  · have hse : s = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst hse
    rw [phase_at_zero]
    decide
  · have hb : ∀ s : Fin (exfPt.val + 1), 0 < s.val → - armT exfSeq exfPt s ≤ -3 := by decide
    have := hb s hpos
    rcases phase_zero_or_one (fun j => - armT exfSeq exfPt j) s with e | e <;> rw [e] <;> omega

/-- **`F2PrimeF` is false**, at the same basepoint: neither the Λ nor the V branch folds. -/
theorem not_f2PrimeF : ¬ F2PrimeF := by
  intro h
  have key := h 42 exfSeq exfSig exfPt 5 0 exfSeq_isLip exfSeq_isCrookedIvF
    (by decide) (by decide) (by norm_num) ⟨⟨12, by decide⟩, by decide⟩ ⟨⟨41, by decide⟩, by decide⟩
  rw [exfSeq_pt] at key
  have hh := exfSeq_hStar
  have hl := exfSeq_lStar
  rcases key with ⟨hG, -⟩ | ⟨-, hT⟩
  · refine not_segLam_of_window_or_peak _ 2 5 0 _
      ⟨⟨10, by decide⟩, Or.inl (by decide)⟩ (fun s hs => ?_) hG
    by_cases h11 : 11 ≤ s.val
    · exact ⟨⟨10, by decide⟩, by show (10 : ℕ) < s.val; omega, Or.inl (by decide)⟩
    · exact absurd hs (by have := exfSeq_G_early s (by omega); omega)
  · refine not_segLam_of_window_or_peak _ (-2) 0 (-5) _
      ⟨⟨2, by decide⟩, Or.inl (by decide)⟩ (fun s hs => ?_) hT
    exact absurd hs (by have := exfSeq_negT_all s; omega)

end HPC.Fold
