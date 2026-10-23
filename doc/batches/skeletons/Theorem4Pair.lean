import HPC.Fold.Theorem4

/-!
# Bing 1948, Theorem 4 with two-link basepoints

Skeleton for batch 79 (save as `HPC/Fold/Theorem4Pair.lean`; add `import HPC.Fold.Theorem4Pair`
to the root `HPC.lean`). Statements only; the proof is `sorry` and is a work item.

A point of a chain lies in at most two links, and those are adjacent. Theorem 13 needs the chain
`F` of Theorem 4 to be a chain *from `R` to `S`* (Bing p. 729: `R` in the first link and in no
other), which by `Q78.isFrom_ofBlocks_iff` means every fine link containing `R` is in block `0`.
So Theorem 4 is needed with a basepoint that is a pair of adjacent links at each end.
-/

namespace HPC.Fold

open HPC.Chain

/-- **Theorem 4, two-link basepoints.** As `theorem4`, with the first block containing both
`E.link r` and `E.link (r+1)` and the last block containing both `E.link (s-1)` and `E.link s`.
The degenerate single-link cases are `theorem4`. -/
theorem theorem4_pair {X : Type*} [MetricSpace X] {n k : ℕ} (hk : 3 ≤ k)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (r r' s' s : Fin n)
    (hr : r'.val = r.val + 1) (hs : s.val = s'.val + 1) (hmid : r' ≤ s')
    (hlow : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hhigh : ∃ h : Fin n, r ≤ h ∧ h ≤ s ∧ (E.link h ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' r).val = 0 ∧ (β' r').val = 0 ∧ (β' s').val = q - 1 ∧ (β' s).val = q - 1 ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  sorry

end HPC.Fold
