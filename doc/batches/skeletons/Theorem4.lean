import HPC.Fold.Open

/-!
# Bing 1948, Theorem 4 (block reading, three-link form), and the end-link clause of Theorem 3

Skeleton for batch 78. Statements only; every proof is `sorry` and is a work item. Names and
hypothesis shapes may be adjusted to fit the repository, provided the mathematical content of
each statement is preserved and any change is recorded in the report.

Conventions: `E` is the fine chain (Bing's `D`), `D` the coarse chain (Bing's `E`); a
consolidation is `E.ofBlocks β hβ`; "in the sum of three consecutive links of `D`" is
`⊆ D.unionRange j 3`.
-/

namespace HPC.Fold

open HPC.Chain

/-- **Bing 1948, Theorem 3 with the end-link clause** (block reading, three-link form). In
addition to the conclusion of `theorem3`: if an end link of `E` meets the first link of `D`,
the block containing it lies in the first three links of `D`; if it meets the last link of `D`,
in the last three. -/
theorem theorem3_end {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n) (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧
      (∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3) ∧
      (∀ t : Fin n, (t.val = 0 ∨ t.val = n - 1) →
        ((E.link t ∩ D.link ⟨0, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange 0 3) ∧
        ((E.link t ∩ D.link ⟨k - 1, by omega⟩).Nonempty →
          (E.ofBlocks β' hβ').link (β' t) ⊆ D.unionRange (k - 3) 3)) := by
  sorry

/-- **Bing 1948, Theorem 4** (block reading, three-link form). If some link of `E` between `r`
and `s` meets the first link of `D` and some link between `r` and `s` meets the last, then `E`
has a block consolidation, every block in three consecutive links of `D`, in which `E.link r`
opens the first block and `E.link s` closes the last. -/
theorem theorem4 {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n) (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r s : Fin n) (hrs : r ≤ s)
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  sorry

end HPC.Fold
