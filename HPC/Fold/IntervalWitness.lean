import HPC.Fold.Interval

/-!
# The batch-16 route fails over the interval model too

Batch 20's commission expects the interval model to repair the route: the sequence-model
refutations of batch 15 and batch 19 are by sequences that are the minimal-index sequence of no
crooked chain (`badSeq_not_realizable`, `fpSeq_not_realizable`), and the exhaustive census of
short interval chains finds no failure of `ExitReachIv`, `HighExitValleyIv`, `LowExitPeakIv` or
`F2PrimeIv`. It does not. Randomised search over longer interval chains — length 60 on twelve
levels — turns up failures of all of `ExitReachIv`, `LowExitPeakIv` and `F2PrimeIv`, and the
shrunk witnesses are formalised here.

The witness for `ExitReachIv` and `F2PrimeIv` is

    ρ = 9,8,7,8,7,6,7,6,6,5,6,6,7,8,7,6,6,5,6,5,5,4     basepoint 15, p = 6, H = 9, L = 4
    σ = 9,8,7,8,7,6,8,6,7,5,7,6,7,8,7,6,7,5,7,5,6,4

with arms

    G = 6,6,5,6,5,5,4          T = 6,7,8,7,6,6,5,6,6,7,6,7,8,7,8,9

`hStarArm T = 9`, so `hStar = 8` (the cap `max (H − 1) p`), while the forward arm's phase-adjusted
reach is only `7`; and `lStarArm G = 4`, so `lStar = 5`, while the backward arm's reflected reach
is only `−6`. Both arms of both disjuncts therefore fail, for `OkLam`/`OkVee` and for
`SegLam`/`SegVee` alike.

The `LowExitPeakIv` witness is a second sequence of length 24 at basepoint 2.

The interval model is complete only in the negative direction — a sequence carried by no
interval structure is the minimal-index sequence of no chain — so these witnesses refute the
four `…Iv` statements, and say nothing yet about chains.
-/

namespace HPC.Fold

/-! ## A decidable criterion for the interval model

The crookedness clause of `IsCrookedIv` quantifies over integers `h` and `k`; the width clause
pins each of them to one of the two ends of its interval, so the clause is equivalent to a
statement quantified over two Booleans, which `decide` can check on concrete data. -/

/-- The endpoint of the interval at `t` selected by `b`. -/
def ivEnd {n : ℕ} (ρ σ : Fin n → ℤ) (b : Bool) (t : Fin n) : ℤ := if b then σ t else ρ t

/-- The finite (decidable) form of `IsCrookedIv`. -/
def IsCrookedIvCheck {n : ℕ} (ρ σ : Fin n → ℤ) : Prop :=
  (∀ t, ρ t ≤ σ t) ∧ (∀ t, σ t ≤ ρ t + 1) ∧
  (∀ t t' : Fin n, t'.val = t.val + 1 → ρ t' ≤ σ t + 1 ∧ ρ t ≤ σ t' + 1) ∧
  (∀ s t : Fin n, s < t → ∀ b b' : Bool,
    3 ≤ |ivEnd ρ σ b s - ivEnd ρ σ b' t| →
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
      (ivEnd ρ σ b s < ivEnd ρ σ b' t →
        (ρ r ≤ ivEnd ρ σ b' t - 1 ∧ ivEnd ρ σ b' t - 1 ≤ σ r) ∧
        (ρ r' ≤ ivEnd ρ σ b s + 1 ∧ ivEnd ρ σ b s + 1 ≤ σ r')) ∧
      (ivEnd ρ σ b' t < ivEnd ρ σ b s →
        (ρ r ≤ ivEnd ρ σ b' t + 1 ∧ ivEnd ρ σ b' t + 1 ≤ σ r) ∧
        (ρ r' ≤ ivEnd ρ σ b s - 1 ∧ ivEnd ρ σ b s - 1 ≤ σ r')))

/-- The finite criterion suffices. -/
theorem isCrookedIv_of_check {n : ℕ} {ρ σ : Fin n → ℤ} (h : IsCrookedIvCheck ρ σ) :
    IsCrookedIv ρ σ := by
  obtain ⟨hle, hw, hadj, hcr⟩ := h
  refine ⟨hle, hw, hadj, ?_⟩
  intro s t hst hh kk h1 h2 h3 h4 habs
  have hs : hh = ρ s ∨ hh = σ s := by have := hw s; omega
  have ht : kk = ρ t ∨ kk = σ t := by have := hw t; omega
  rcases hs with e | e <;> rcases ht with e' | e' <;> subst e <;> subst e'
  · exact hcr s t hst false false habs
  · exact hcr s t hst false true habs
  · exact hcr s t hst true false habs
  · exact hcr s t hst true true habs

/-! ## Witness 1: `ExitReachIv` and `F2PrimeIv` -/

/-- The refuting interval chain: the level sequence. -/
def ivSeq : Fin 22 → ℤ := ![9, 8, 7, 8, 7, 6, 7, 6, 6, 5, 6, 6, 7, 8, 7, 6, 6, 5, 6, 5, 5, 4]

/-- The refuting interval chain: the upper end of each interval. -/
def ivSig : Fin 22 → ℤ := ![9, 8, 7, 8, 7, 6, 8, 6, 7, 5, 7, 6, 7, 8, 7, 6, 7, 5, 7, 5, 6, 4]

/-- Its basepoint. -/
def ivPt : Fin 22 := ⟨15, by omega⟩

@[simp] theorem ivPt_val : ivPt.val = 15 := rfl

/-- The level at the basepoint. -/
theorem ivSeq_pt : ivSeq ivPt = 6 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem ivSeq_isLip : IsLip ivSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [ivSeq]

set_option maxRecDepth 4000000 in
set_option synthInstance.maxSize 400 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- And it is a genuine interval chain: `(ivSeq, ivSig)` is crooked in the interval model. -/
theorem ivSeq_isCrookedIv : IsCrookedIv ivSeq ivSig :=
  isCrookedIv_of_check (by unfold IsCrookedIvCheck ivEnd; decide)

set_option maxRecDepth 10000 in
/-- The backward arm's peak demand is the top level. -/
theorem ivSeq_hStarArm_T : hStarArm (armT ivSeq ivPt) 6 = 9 :=
  hStarArm_eq_of_attained _ _ _ ⟨15, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
/-- The forward arm's valley demand, in negated form. -/
theorem ivSeq_hStarArm_negG : hStarArm (fun j => - armG ivSeq ivPt j) (-6) = -4 :=
  hStarArm_eq_of_attained _ _ _ ⟨6, by decide⟩ (by decide) (by decide) (by decide)

/-- So the bump height is the cap, `H − 1 = 8`. -/
theorem ivSeq_hStar : (8 : ℤ) ≤ hStar ivSeq ivPt 9 4 := by
  have h := ivSeq_hStarArm_T
  rw [hStar, ivSeq_pt]
  simp only [le_min_iff, le_max_iff]
  omega

/-- And the valley depth is the floor, `L + 1 = 5`. -/
theorem ivSeq_lStar : lStar ivSeq ivPt 9 4 ≤ 5 := by
  have h : lStarArm (armG ivSeq ivPt) 6 = 4 := by
    rw [lStarArm, ivSeq_hStarArm_negG]; omega
  rw [lStar, ivSeq_pt]
  simp only [max_le_iff, min_le_iff]
  omega

/-- The forward arm never exceeds `6`, so its phase-adjusted levels never exceed `7`. -/
theorem ivSeq_bound_G (k : Fin (22 - ivPt.val)) :
    armG ivSeq ivPt k + phase (armG ivSeq ivPt) k ≤ 7 := by
  have hb : ∀ k : Fin (22 - ivPt.val), armG ivSeq ivPt k ≤ 6 := by decide
  have := hb k
  rcases phase_zero_or_one (armG ivSeq ivPt) k with e | e <;> rw [e] <;> omega

/-- The reflected backward arm leaves its window at index `2`, and before that its
phase-adjusted levels never exceed `−6`. -/
theorem ivSeq_bound_negT (k : Fin (ivPt.val + 1))
    (hk : ∀ k' : Fin (ivPt.val + 1), k' ≤ k → (-6 : ℤ) - 1 ≤ - armT ivSeq ivPt k') :
    (- armT ivSeq ivPt k) + phase (fun j => - armT ivSeq ivPt j) k ≤ -6 := by
  have hd : ∀ k : Fin (ivPt.val + 1),
      (∀ k' : Fin (ivPt.val + 1), k' ≤ k → (-6 : ℤ) - 1 ≤ - armT ivSeq ivPt k') →
      k.val ≤ 1 := by decide
  have hk1 := hd k hk
  rcases Nat.eq_zero_or_pos k.val with h0 | hpos
  · have hke : k = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst hke
    rw [phase_at_zero]
    decide
  · have hb : ∀ k : Fin (ivPt.val + 1), 0 < k.val → k.val ≤ 1 →
        - armT ivSeq ivPt k ≤ -7 := by decide
    have := hb k hpos hk1
    rcases phase_zero_or_one (fun j => - armT ivSeq ivPt j) k with e | e <;> rw [e] <;> omega

/-- So the forward arm's reach falls one short of `hStar`. -/
theorem ivSeq_hReach_G : hReach (armG ivSeq ivPt) 6 ≤ 7 :=
  hReach_le_of_all (by decide) 6 7 (by decide) ivSeq_bound_G

/-- And the reflected backward arm's reach falls one short of `− lStar`. -/
theorem ivSeq_hReach_negT : hReach (fun j => - armT ivSeq ivPt j) (-6) ≤ -6 :=
  hReach_le_of_pre (by decide) (-6) (-6) (by decide) ivSeq_bound_negT

/-- **`ExitReachIv` is false**: the route's first hypothesis fails over the interval model. -/
theorem not_exitReachIv : ¬ ExitReachIv := by
  intro h
  have key := h 22 ivSeq ivSig ivPt 9 4 ivSeq_isLip ivSeq_isCrookedIv
    (by decide) (by decide) (by norm_num) ⟨⟨21, by decide⟩, by decide⟩ ⟨⟨0, by decide⟩, by decide⟩
  rw [ivSeq_pt] at key
  have hh := ivSeq_hStar
  have hl := ivSeq_lStar
  rcases key with ⟨hG, -⟩ | ⟨-, hT⟩
  · rcases hG with hnd | hr
    · exact hnd ⟨⟨6, by decide⟩, by decide⟩
    · have := ivSeq_hReach_G
      omega
  · rcases hT with hnd | hr
    · exact hnd ⟨⟨2, by decide⟩, by decide⟩
    · have := ivSeq_hReach_negT
      omega

/-- The reflected backward arm is below `−6` at its first three indices. -/
theorem ivSeq_negT_early (s : Fin (ivPt.val + 1)) (hs : s.val ≤ 2) :
    (- armT ivSeq ivPt s) + phase (fun j => - armT ivSeq ivPt j) s ≤ -6 := by
  rcases Nat.eq_zero_or_pos s.val with h0 | hpos
  · have hse : s = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst hse
    rw [phase_at_zero]
    decide
  · have hb : ∀ s : Fin (ivPt.val + 1), 0 < s.val → s.val ≤ 2 →
        - armT ivSeq ivPt s ≤ -7 := by decide
    have := hb s hpos hs
    rcases phase_zero_or_one (fun j => - armT ivSeq ivPt j) s with e | e <;> rw [e] <;> omega

/-- **`F2PrimeIv` is false**, at the same basepoint: neither the Λ nor the V branch folds. -/
theorem not_f2PrimeIv : ¬ F2PrimeIv := by
  intro h
  have key := h 22 ivSeq ivSig ivPt 9 4 ivSeq_isLip ivSeq_isCrookedIv
    (by decide) (by decide) (by norm_num) ⟨⟨21, by decide⟩, by decide⟩ ⟨⟨0, by decide⟩, by decide⟩
  rw [ivSeq_pt] at key
  have hh := ivSeq_hStar
  have hl := ivSeq_lStar
  rcases key with ⟨hG, -⟩ | ⟨-, hT⟩
  · refine not_segLam_of_window_or_peak _ 6 9 4 _
      ⟨⟨6, by decide⟩, Or.inl (by decide)⟩ (fun s hs => ?_) hG
    exact absurd hs (by have := ivSeq_bound_G s; omega)
  · refine not_segLam_of_window_or_peak _ (-6) (-4) (-9) _
      ⟨⟨2, by decide⟩, Or.inl (by decide)⟩ (fun s hs => ?_) hT
    by_cases h3 : 3 ≤ s.val
    · exact ⟨⟨2, by decide⟩, by show (2 : ℕ) < s.val; omega, Or.inl (by decide)⟩
    · exact absurd hs (by have := ivSeq_negT_early s (by omega); omega)

/-! ## Witness 2: `LowExitPeakIv`

    ρ = 5,6,6,7,8,7,6,6,5,6,5,5,4,5,6,5,6,5,5,4,5,4,4,3      basepoint 2, p = 6, H = 8, L = 3
    σ = 5,7,6,7,8,7,6,7,5,7,5,6,4,5,6,5,7,5,6,4,6,4,5,3

The arms are

    G = 6,7,8,7,6,6,5,6,5,5,4,5,6,5,6,5,5,4,5,4,4,3          T = 6,6,5

with `lStarArm G = 6` and `lStarArm T = 5`, so `lStar = 5`. On the forward arm `s = 4` is
admissible — the first four reflected phase-adjusted levels are `−6, −6, −7, −6`, all below
`− lStar = −5` — and at `u = 21` the reflected arm is at `−3 > − lStar + 1`. The clause then
asks for an index in `[4, 21)` at which the arm is at `H − 1 = 7` or above, and from index `4`
on the arm never again exceeds `6`. -/

def lpivSeq : Fin 24 → ℤ :=
  ![5, 6, 6, 7, 8, 7, 6, 6, 5, 6, 5, 5, 4, 5, 6, 5, 6, 5, 5, 4, 5, 4, 4, 3]

/-- The upper end of each interval. -/
def lpivSig : Fin 24 → ℤ :=
  ![5, 7, 6, 7, 8, 7, 6, 7, 5, 7, 5, 6, 4, 5, 6, 5, 7, 5, 6, 4, 6, 4, 5, 3]

/-- Its basepoint. -/
def lpivPt : Fin 24 := ⟨2, by omega⟩

@[simp] theorem lpivPt_val : lpivPt.val = 2 := rfl

/-- The level at the basepoint. -/
theorem lpivSeq_pt : lpivSeq lpivPt = 6 := by decide

/-- The sequence is 1-Lipschitz. -/
theorem lpivSeq_isLip : IsLip lpivSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [lpivSeq]

set_option maxRecDepth 8000000 in
set_option synthInstance.maxSize 400 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- And it is a genuine interval chain. -/
theorem lpivSeq_isCrookedIv : IsCrookedIv lpivSeq lpivSig :=
  isCrookedIv_of_check (by unfold IsCrookedIvCheck ivEnd; decide)

set_option maxRecDepth 40000 in
/-- The forward arm's valley demand, in negated form. -/
theorem lpivSeq_hStarArm_negG : hStarArm (fun j => - armG lpivSeq lpivPt j) (-6) = -6 :=
  hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 40000 in
/-- The backward arm's valley demand, in negated form. -/
theorem lpivSeq_hStarArm_negT : hStarArm (fun j => - armT lpivSeq lpivPt j) (-6) = -5 :=
  hStarArm_eq_of_attained _ _ _ ⟨2, by decide⟩ (by decide) (by decide) (by decide)

/-- The valley depth, exactly. -/
theorem lpivSeq_lStar : lStar lpivSeq lpivPt 8 3 = 5 := by
  have hG : lStarArm (armG lpivSeq lpivPt) 6 = 6 := by
    rw [lStarArm, lpivSeq_hStarArm_negG]; omega
  have hT : lStarArm (armT lpivSeq lpivPt) 6 = 5 := by
    rw [lStarArm, lpivSeq_hStarArm_negT]; omega
  rw [lStar, lpivSeq_pt, hG, hT]
  decide

/-- Index `4` is an admissible peak index for the reflected forward arm. -/
theorem lpivSeq_admissible (j : Fin (24 - lpivPt.val)) (hj : j.val < 4) :
    (- armG lpivSeq lpivPt j) + phase (fun j' => - armG lpivSeq lpivPt j') j < -5 := by
  rcases phase_zero_or_one (fun j' => - armG lpivSeq lpivPt j') j with e | e
  · have hb : ∀ j : Fin (24 - lpivPt.val), j.val < 4 → - armG lpivSeq lpivPt j ≤ -6 := by decide
    have := hb j hj
    rw [e]; omega
  · have hpos := pos_of_phase_eq_one _ _ e
    have hb : ∀ j : Fin (24 - lpivPt.val), 0 < j.val → j.val < 4 →
        - armG lpivSeq lpivPt j ≤ -7 := by decide
    have := hb j hpos hj
    rw [e]; omega

/-- **`LowExitPeakIv` is false**: the route's third hypothesis fails over the interval model
too. -/
theorem not_lowExitPeakIv : ¬ LowExitPeakIv := by
  intro h
  obtain ⟨hG, -⟩ := h 24 lpivSeq lpivSig lpivPt 8 3 lpivSeq_isLip lpivSeq_isCrookedIv
    (by decide) (by decide) (by norm_num) ⟨⟨23, by decide⟩, by decide⟩ ⟨⟨4, by decide⟩, by decide⟩
  rw [lpivSeq_lStar] at hG
  obtain ⟨j, hj1, hj2, hj3⟩ := hG 4 (fun j hj => lpivSeq_admissible j hj) ⟨21, by decide⟩
    (by decide) (by decide)
  have hb : ∀ j : Fin (24 - lpivPt.val), 4 ≤ j.val → j.val < 21 →
      ¬ (- armG lpivSeq lpivPt j ≤ -8 + 1) := by decide
  exact hb j hj1 hj2 hj3

end HPC.Fold
