import HPC.HO16.FoldExists
import HPC.HO16.Prop7

/-!
# Batch 194: non-vacuity of `IsFoldTriple` and `IsSimpleFoldOf`

A concrete triple on the arc `G = [0, 3] ⊆ ℝ`: `G₁ = [0, 2]`, `G₂ = [1, 2]`, `G₃ = [1, 3]`, with
`∂G₁ = {2}` and `∂G₃ = {1}` (the first fold of H–O's Figure 1). By `exists_simpleFold` it carries a
simple fold, and it satisfies every hypothesis of `ho16_prop7` (`G` connected, both frontiers
nonempty). This is the non-vacuity check of the report for the theorems whose hypotheses include
`IsFoldTriple` or `IsSimpleFoldOf`.
-/

namespace HPC.HO16

open Set

/-- A nondegenerate closed interval of `ℝ` is a PL graph (one edge). -/
theorem isPLGraph_Icc {a b : ℝ} (hab : a < b) : IsPLGraph (Icc a b) := by
  refine ⟨{(a, b)}, ?_, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    exact hab.ne
  · simp [segment_eq_Icc hab.le]
  · intro s hs s' hs' hne
    rw [Finset.mem_singleton] at hs hs'
    exact absurd (hs.trans hs'.symm) hne

/-- The triple `([0, 2], [1, 2], [1, 3])` on `[0, 3]` satisfies (F1)–(F3). -/
theorem isFoldTriple_example :
    IsFoldTriple (Icc (0 : ℝ) 3) (Icc 0 2) (Icc 1 2) (Icc 1 3) := by
  refine ⟨nonempty_Icc.2 (by norm_num), nonempty_Icc.2 (by norm_num), nonempty_Icc.2 (by norm_num),
    isPLGraph_Icc (by norm_num), isPLGraph_Icc (by norm_num), isPLGraph_Icc (by norm_num), ?_, ?_,
    ?_⟩
  · rw [Icc_union_Icc' (by norm_num) (by norm_num)]; norm_num
  · rw [Icc_inter_Icc]; norm_num
  · have h1 : Icc (0 : ℝ) 2 \ Icc 1 2 = Ico 0 1 := by
      ext x; simp only [mem_diff, mem_Icc, mem_Ico]; constructor
      · rintro ⟨⟨h0, h2⟩, h⟩; exact ⟨h0, by by_contra h'; exact h ⟨not_lt.1 h', h2⟩⟩
      · rintro ⟨h0, h1⟩; exact ⟨⟨h0, by linarith⟩, fun h => by linarith [h.1]⟩
    have h3 : Icc (1 : ℝ) 3 \ Icc 1 2 = Ioc 2 3 := by
      ext x; simp only [mem_diff, mem_Icc, mem_Ioc]; constructor
      · rintro ⟨⟨h1, h3⟩, h⟩; exact ⟨by by_contra h'; exact h ⟨h1, not_lt.1 h'⟩, h3⟩
      · rintro ⟨h2, h3⟩; exact ⟨⟨by linarith, h3⟩, fun h => by linarith [h.2]⟩
    rw [h1, h3, closure_Ico (by norm_num), closure_Ioc (by norm_num)]
    rw [Set.disjoint_left]
    intro x hx hx'
    linarith [hx.2, hx'.1]

/-- In the example, `∂G₁ = {2}`. -/
theorem relFrontier_example_left :
    relFrontier (Icc (0 : ℝ) 3) (Icc 0 2) = {2} := by
  have h : Icc (0 : ℝ) 3 \ Icc 0 2 = Ioc 2 3 := by
    ext x; simp only [mem_diff, mem_Icc, mem_Ioc]; constructor
    · rintro ⟨⟨h0, h3⟩, h⟩; exact ⟨by by_contra h'; exact h ⟨h0, not_lt.1 h'⟩, h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨⟨by linarith, h3⟩, fun h => by linarith [h.2]⟩
  rw [relFrontier, h, closure_Icc, closure_Ioc (by norm_num)]
  ext x; simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]; constructor
  · rintro ⟨⟨_, h2⟩, ⟨h2', _⟩⟩; linarith
  · rintro rfl; norm_num

/-- In the example, `∂G₃ = {1}`. -/
theorem relFrontier_example_right :
    relFrontier (Icc (0 : ℝ) 3) (Icc 1 3) = {1} := by
  have h : Icc (0 : ℝ) 3 \ Icc 1 3 = Ico 0 1 := by
    ext x; simp only [mem_diff, mem_Icc, mem_Ico]; constructor
    · rintro ⟨⟨h0, h3⟩, h⟩; exact ⟨h0, by by_contra h'; exact h ⟨not_lt.1 h', h3⟩⟩
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0, by linarith⟩, fun h => by linarith [h.1]⟩
  rw [relFrontier, h, closure_Icc, closure_Ico (by norm_num)]
  ext x; simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]; constructor
  · rintro ⟨⟨h1, _⟩, ⟨_, h1'⟩⟩; linarith
  · rintro rfl; norm_num

/-- **Non-vacuity.** The example carries a simple fold, and it meets every hypothesis of
`ho16_prop7`: `G` is connected and both relative frontiers are nonempty. -/
theorem exists_simpleFold_example :
    ∃ F₁ F₂ F₃ : Set (ℝ × ℝ),
      IsSimpleFoldOf (Icc (0 : ℝ) 3) (Icc 0 2) (Icc 1 2) (Icc 1 3) F₁ F₂ F₃ ∧
      IsConnected (Icc (0 : ℝ) 3) ∧ (relFrontier (Icc (0 : ℝ) 3) (Icc 0 2)).Nonempty ∧
      (relFrontier (Icc (0 : ℝ) 3) (Icc 1 3)).Nonempty := by
  obtain ⟨F₁, F₂, F₃, hF⟩ := exists_simpleFold isFoldTriple_example
  refine ⟨F₁, F₂, F₃, hF, isConnected_Icc (by norm_num), ?_, ?_⟩
  · rw [relFrontier_example_left]; exact singleton_nonempty _
  · rw [relFrontier_example_right]; exact singleton_nonempty _

end HPC.HO16
