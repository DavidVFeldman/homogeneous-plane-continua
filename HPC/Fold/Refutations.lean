import HPC.Fold.Witnesses

/-!
# `MixedGap`, `MixedGapUp` and `Agreement` are false

A single sequence refutes all three. The evidence recorded in their docstrings was gathered
under a crookedness model strictly stronger than either weak form — the model in which both
reversal witnesses sit at exactly the adjacent levels — and no sequence satisfying only a weak
form was ever in the corpus.

    q = 1, 2, 3, 2, 3, 4, 3, 4, 5      basepoint 4,  p = 3

`q` is 1-Lipschitz and satisfies both `IsCrookedSeq` and `IsCrookedSeqUp`. Its arms are
`G = 3, 4, 3, 4, 5` and `T = 3, 2, 3, 2, 1`, with demands

    hStarArm G = 5,  hStarArm T = 3,  lStarArm G = 3,  lStarArm T = 1,

so both gaps are exactly two: the conjunction `MixedGap` forbids holds, and `Agreement` fails.
`q` is not crooked in the exact model, which is why 2 890 280 earlier basepoints showed none.

Nothing proved elsewhere is affected: all three were `def ... : Prop`, never discharged as
hypotheses. `agreement_of_mixedGap` (batch 12) and `mixedGapUp_witnesses` (batch 14) remain
true; the first now has a false antecedent and a false consequent, the second an antecedent
that is satisfiable.

The docstrings of `MixedGap` (`Agree.lean`), `MixedGapUp` (`Symmetry.lean`) and `Agreement`
(`Phase.lean`) cite corpus sizes as evidence; those files are untouched, and the three `not_`
theorems below are the authority.

English proofs: COMMISSION-batch15.md §§2–4.
-/

namespace HPC.Fold

/-- The refuting sequence. -/
def badSeq : Fin 9 → ℤ := ![1, 2, 3, 2, 3, 4, 3, 4, 5]

/-- Its basepoint. -/
def badPt : Fin 9 := ⟨4, by omega⟩

/-- The level at the basepoint: `p = 3`. -/
theorem badSeq_badPt : badSeq badPt = 3 := by decide

theorem badSeq_isLip : IsLip badSeq := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp_all [badSeq]

set_option maxRecDepth 100000 in
theorem badSeq_isCrookedSeq : IsCrookedSeq badSeq := by
  unfold IsCrookedSeq
  decide

set_option maxRecDepth 100000 in
theorem badSeq_isCrookedSeqUp : IsCrookedSeqUp badSeq := by
  unfold IsCrookedSeqUp
  decide

/-- The peak demand of an arm, read off an explicit attaining index together with an upper
bound over all indices whose predecessors stay in the window. -/
theorem hStarArm_eq_of_attained {m : ℕ} (f : Fin m → ℤ) (p c : ℤ) (j : Fin m)
    (hj : f j = c) (hjpre : ∀ j' : Fin m, j' ≤ j → p - 1 ≤ f j')
    (hub : ∀ k : Fin m, (∀ k' : Fin m, k' ≤ k → p - 1 ≤ f k') → f k ≤ c) :
    hStarArm f p = c := by
  classical
  set S : Set ℤ := {v : ℤ | ∃ j : Fin m, f j = v ∧ ∀ j' : Fin m, j' ≤ j → p - 1 ≤ f j'} with hS
  have hmem : c ∈ S := ⟨j, hj, hjpre⟩
  have hne : S.Nonempty := ⟨c, hmem⟩
  have hsub : S ⊆ Set.range f := by rintro v ⟨k, rfl, -⟩; exact ⟨k, rfl⟩
  have hbdd : BddAbove S := ((Set.finite_range f).subset hsub).bddAbove
  refine le_antisymm (csSup_le hne ?_) (le_csSup hbdd hmem)
  rintro v ⟨k, rfl, hk⟩
  exact hub k hk

set_option maxRecDepth 10000 in
theorem badSeq_hStarArm_G : hStarArm (armG badSeq badPt) (badSeq badPt) = 5 := by
  rw [badSeq_badPt]
  exact hStarArm_eq_of_attained _ _ _ ⟨4, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
theorem badSeq_hStarArm_T : hStarArm (armT badSeq badPt) (badSeq badPt) = 3 := by
  rw [badSeq_badPt]
  exact hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
theorem badSeq_lStarArm_G : lStarArm (armG badSeq badPt) (badSeq badPt) = 3 := by
  rw [badSeq_badPt, lStarArm]
  have h : hStarArm (fun j => - armG badSeq badPt j) (-3) = -3 :=
    hStarArm_eq_of_attained _ _ _ ⟨0, by decide⟩ (by decide) (by decide) (by decide)
  omega

set_option maxRecDepth 10000 in
theorem badSeq_lStarArm_T : lStarArm (armT badSeq badPt) (badSeq badPt) = 1 := by
  rw [badSeq_badPt, lStarArm]
  have h : hStarArm (fun j => - armT badSeq badPt j) (-3) = -1 :=
    hStarArm_eq_of_attained _ _ _ ⟨4, by decide⟩ (by decide) (by decide) (by decide)
  omega

/-- **`MixedGap` is false.** -/
theorem not_mixedGap : ¬ MixedGap := by
  intro h
  refine h 9 badSeq badPt badSeq_isLip badSeq_isCrookedSeq ⟨?_, ?_⟩
  · rw [badSeq_hStarArm_G, badSeq_hStarArm_T]
    norm_num
  · rw [badSeq_lStarArm_G, badSeq_lStarArm_T]
    norm_num

/-- **`MixedGapUp` is false**, by the same sequence. -/
theorem not_mixedGapUp : ¬ MixedGapUp := by
  intro h
  refine h 9 badSeq badPt badSeq_isLip badSeq_isCrookedSeqUp ⟨?_, ?_⟩
  · rw [badSeq_hStarArm_G, badSeq_hStarArm_T]
    norm_num
  · rw [badSeq_lStarArm_G, badSeq_lStarArm_T]
    norm_num

/-- **`Agreement` is false.** Both gaps are exactly two. -/
theorem not_agreement : ¬ Agreement := by
  intro h
  rcases h 9 badSeq badPt badSeq_isLip badSeq_isCrookedSeq with hh | hl
  · rw [badSeq_hStarArm_G, badSeq_hStarArm_T] at hh
    norm_num at hh
  · rw [badSeq_lStarArm_G, badSeq_lStarArm_T] at hl
    norm_num at hl

/-- Since `Agreement` is false and batch 12 derives it from `MixedGap`, the derivation is
vacuous; recorded so the chain is not mistaken for a live route. -/
theorem agreement_route_is_dead : ¬ MixedGap ∧ ¬ Agreement :=
  ⟨not_mixedGap, not_agreement⟩

end HPC.Fold
