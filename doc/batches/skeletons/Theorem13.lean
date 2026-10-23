import HPC.PseudoArc.Theorem5

/-!
# Bing 1948, Theorem 13: the described continuum is homogeneous

Skeleton for batch 81 (save as `HPC/PseudoArc/Theorem13.lean`; add `import HPC.PseudoArc.Theorem13`
to the root `HPC.lean`). Statements only; every proof is `sorry` and is a work item. The auxiliary
statements are the claims of Bing's proof (COMMISSION-batch81.md §3) that the repository does not
yet have; their shapes may be adjusted, with the change recorded, provided `theorem13` is reached.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

/-- **Composants are proper.** In an indecomposable continuum `M` the composant of any point is
not all of `M` (Bing uses this at p. 740, "a point belonging to a composant of `M` not containing
`P_n`"). Standard proof: the composant is a countable union of proper subcontinua, each with empty
interior in `M`; Baire. -/
theorem composant_ne_of_indecomposable [CompactSpace X] {M : Set X}
    (hM : Fold.Q78.IsIndecomposable M) (hnd : M.Nontrivial) {p : X} (hp : p ∈ M) :
    composant M p ≠ M := by
  sorry

namespace Description

variable {P Q : X}

/-- **Reaching both ends** (Bing p. 740, first paragraph of the proof). If `R`, `S ∈ M` lie in
different composants, then for every `j` there is `k > j` such that the subchain of `D_k` from `R`
to `S` has a link meeting the first link of `D_j` and a link meeting the last. -/
theorem exists_subchain_meets_ends [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q)
    {R S : X} (hR : R ∈ Δ.M) (hS : S ∈ Δ.M) (hcomp : S ∉ composant Δ.M R) (j : ℕ) :
    ∃ k, j < k ∧ ∃ a b : Fin (Δ.n k), (Δ.D k).IsSubchainFrom a b R S ∧
      (∃ t : Fin (Δ.n k), min a b ≤ t ∧ t ≤ max a b ∧
        ((Δ.D k).link t ∩ (Δ.D j).link ⟨0, by have := Δ.isFrom j; sorry⟩).Nonempty) ∧
      (∃ t : Fin (Δ.n k), min a b ≤ t ∧ t ≤ max a b ∧
        ((Δ.D k).link t ∩ (Δ.D j).link ⟨Δ.n j - 1, by sorry⟩).Nonempty) := by
  sorry

/-- **A description of `M` from `R` to `S`** (Bing p. 740, "we get a sequence `E_1, E_2, …`"):
for `R`, `S ∈ M` in different composants there is a description `Δ'` of the same continuum with
end points `R`, `S`. -/
theorem exists_description_from [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q)
    {R S : X} (hR : R ∈ Δ.M) (hS : S ∈ Δ.M) (hcomp : S ∉ composant Δ.M R) :
    ∃ Δ' : Description X R S, Δ'.M = Δ.M := by
  sorry

/-- **Bing 1948, Theorem 13.** -/
theorem theorem13 [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) :
    Theorem13Statement Δ := by
  sorry

end Description

end HPC
