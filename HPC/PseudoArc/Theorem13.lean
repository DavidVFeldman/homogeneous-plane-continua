import HPC.PseudoArc.Theorem5
import HPC.PseudoArc.T13Step

/-!
# Bing 1948, Theorem 13: the described continuum is homogeneous

Skeleton for batch 81 (save as `HPC/PseudoArc/Theorem13.lean`; add `import HPC.PseudoArc.Theorem13`
to the root `HPC.lean`). Statements only; every proof was a `sorry` work item (batch 81: all filled in). The auxiliary
statements are the claims of Bing's proof (COMMISSION-batch81.md §3) that the repository does not
yet have; their shapes may be adjusted, with the change recorded, provided `theorem13` is reached.

## Batch-81 record

All four statements are proved; no statement was reshaped. The only edits to the skeleton are the
two index-bound placeholders in `exists_subchain_meets_ends` (`0 < Δ.n j`, discharged from
`Δ.isFrom j`) and the import of the supporting files:

* `T13Topo.lean` — limits of finely chained sets are connected; a proper subcontinuum of an
  indecomposable continuum has empty interior (clopen boundary bumping); Baire.
* `T13Chains.lean` — `M` is connected; subchains between two points; the limit argument of
  Bing's first paragraph.
* `T13Step.lean` — Theorem 4 (`Fold.theorem4_pair`) on a subchain from `R` to `S`; one step of
  the sequence `E_1, E_2, …`; the description from `R` to `S`.

The hypothesis `hnd : M.Nontrivial` of `composant_ne_of_indecomposable` turned out to be
unnecessary (for `M` a single point the composant is empty); it is kept because the skeleton has it.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

/-- **Composants are proper.** In an indecomposable continuum `M` the composant of any point is
not all of `M` (Bing uses this at p. 740, "a point belonging to a composant of `M` not containing
`P_n`"). Standard proof: the composant is a countable union of proper subcontinua, each with empty
interior in `M`; Baire.

(Batch 81: the hypothesis `hnd` is not used by the proof.) -/
theorem composant_ne_of_indecomposable [CompactSpace X] {M : Set X}
    (hM : Fold.Q78.IsIndecomposable M) (hnd : M.Nontrivial) {p : X} (hp : p ∈ M) :
    composant M p ≠ M := by
  obtain ⟨y, hyM, hy⟩ := T13.exists_not_mem_proper_subcontinua (M := M) hM hp
  intro heq
  have hyc : y ∈ composant M p := by rw [heq]; exact hyM
  obtain ⟨K, ⟨hK, hKM, hKne, hpK⟩, hyK⟩ := mem_sUnion.mp hyc
  exact hy K hK hKM hKne hpK hyK

namespace Description

variable {P Q : X}

/-- **Reaching both ends** (Bing p. 740, first paragraph of the proof). If `R`, `S ∈ M` lie in
different composants, then for every `j` there is `k > j` such that the subchain of `D_k` from `R`
to `S` has a link meeting the first link of `D_j` and a link meeting the last. -/
theorem exists_subchain_meets_ends [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q)
    {R S : X} (hR : R ∈ Δ.M) (hS : S ∈ Δ.M) (hcomp : S ∉ composant Δ.M R) (j : ℕ) :
    ∃ k, j < k ∧ ∃ a b : Fin (Δ.n k), (Δ.D k).IsSubchainFrom a b R S ∧
      (∃ t : Fin (Δ.n k), min a b ≤ t ∧ t ≤ max a b ∧
        ((Δ.D k).link t ∩ (Δ.D j).link ⟨0, by have := Δ.isFrom j; exact this.1⟩).Nonempty) ∧
      (∃ t : Fin (Δ.n k), min a b ≤ t ∧ t ≤ max a b ∧
        ((Δ.D k).link t ∩ (Δ.D j).link ⟨Δ.n j - 1, by have := (Δ.isFrom j).1; omega⟩).Nonempty) := by
  obtain ⟨k, hjk, a, b, hsub, ⟨t₁, h₁a, h₁b, h₁⟩, ⟨t₂, h₂a, h₂b, h₂⟩⟩ :=
    Δ.exists_subchain_meets_ends' hPQ hR hS hcomp j
  have hab : a ≤ b := hsub.1
  refine ⟨k, hjk, a, b, hsub, ⟨t₁, ?_, ?_, h₁⟩, ⟨t₂, ?_, ?_, h₂⟩⟩ <;>
    simp only [min_eq_left hab, max_eq_right hab] <;> assumption

/-- **A description of `M` from `R` to `S`** (Bing p. 740, "we get a sequence `E_1, E_2, …`"):
for `R`, `S ∈ M` in different composants there is a description `Δ'` of the same continuum with
end points `R`, `S`. -/
theorem exists_description_from [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q)
    {R S : X} (hR : R ∈ Δ.M) (hS : S ∈ Δ.M) (hcomp : S ∉ composant Δ.M R) :
    ∃ Δ' : Description X R S, Δ'.M = Δ.M :=
  Δ.exists_description_from' hPQ hR hS hcomp

/-- **Bing 1948, Theorem 13.** -/
theorem theorem13 [CompactSpace X] (Δ : Description X P Q) (hPQ : P ≠ Q) :
    Theorem13Statement Δ := by
  intro P₁ P₂ h₁ h₂
  have hind : Fold.Q78.IsIndecomposable Δ.M := theorem10 Δ Δ.M subset_rfl Δ.isContinuum_M
  have hnd : Δ.M.Nontrivial := ⟨P, Δ.P_mem_M, Q, Δ.Q_mem_M, hPQ⟩
  have hQ : ∀ p ∈ Δ.M, ∃ q ∈ Δ.M, q ∉ composant Δ.M p := by
    intro p hp
    have hne := composant_ne_of_indecomposable hind hnd hp
    by_contra h
    push_neg at h
    refine hne (Subset.antisymm ?_ h)
    intro z hz
    obtain ⟨K, ⟨-, hKM, -⟩, hzK⟩ := mem_sUnion.mp hz
    exact hKM hzK
  obtain ⟨Q₁, hQ₁, hc₁⟩ := hQ P₁ h₁
  obtain ⟨Q₂, hQ₂, hc₂⟩ := hQ P₂ h₂
  obtain ⟨Δ₁, hΔ₁⟩ := exists_description_from Δ hPQ h₁ hQ₁ hc₁
  obtain ⟨Δ₂, hΔ₂⟩ := exists_description_from Δ hPQ h₂ hQ₂ hc₂
  obtain ⟨T, hT, -⟩ := theorem12 Δ₁ Δ₂ (Δ.ne_of_not_mem_composant h₁ hPQ hc₁)
    (Δ.ne_of_not_mem_composant h₂ hPQ hc₂)
  refine ⟨((Homeomorph.setCongr hΔ₁).symm.trans T).trans (Homeomorph.setCongr hΔ₂), ?_⟩
  have e1 : (Homeomorph.setCongr hΔ₁).symm ⟨P₁, h₁⟩ = ⟨P₁, Δ₁.P_mem_M⟩ := Subtype.ext rfl
  show (Homeomorph.setCongr hΔ₂) (T ((Homeomorph.setCongr hΔ₁).symm ⟨P₁, h₁⟩)) = _
  rw [e1, hT]
  exact Subtype.ext rfl

end Description

end HPC
