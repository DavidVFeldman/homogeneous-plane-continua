import HPC.Archive.Target73

/-!
# Packaging what is proved: span at most nine, and chains of at most ten links

Batch 73 closed span nine (`s3_span_nine`, `HPC/Fold/Target73.lean`). This file packages that
result in the two forms the commission of batch 74 §2.1 asks for.

* `S3SpanLeNine` / `s3_span_le_nine` — `S3` with the band restricted to `H ≤ L + 9`. The two
  attainment hypotheses of `S3` (`∃ t, ρ t = L` and `∃ t, ρ t = H`) are **not** needed and are
  not carried: what is proved is the stronger statement without them.
* `theorem3_ten_links` — Bing 1948 Theorem 3, in the block reading and three-link form of
  `theorem3_of_S3` (`HPC/Fold/Span.lean`), **unconditional**, for a chain `D` of at most ten
  links.

The bound is exactly ten and the reduction loses nothing. `theorem3_of_S3` runs the fold on
`ρ t = (minIdx t : ℤ)`, the least index of `D` whose link contains the link `E.link t`; its values
lie in `[0, k - 1]`, so the band `[L, H]` of the pair has `H - L ≤ k - 1`. With `k ≤ 10` that is
`H ≤ L + 9`, which is exactly the hypothesis of `s3_span_nine`; and where `H ≤ L + 2` the fold is
not needed at all (`exists_blocks_first_of_range_le_two`). So the ten-link form is the span-nine
theorem read back through the reduction, with no level lost.

`s3_general` — every span — remains open, and so does `theorem3` for an arbitrary chain `D`.
-/

namespace HPC.Fold

/-- **`S3` restricted to spans at most nine.** The statement of `S3` (`HPC/Fold/Span.lean`) with
the band bounded by `H ≤ L + 9`, and with the two attainment hypotheses of `S3` dropped: they are
not needed at this span. -/
def S3SpanLeNine : Prop :=
  ∀ (n : ℕ) (ρ σ : Fin n → ℤ) (i : Fin n) (H L : ℤ),
    IsLip ρ → IsCrookedIvF ρ σ → (∀ t, L ≤ ρ t) → (∀ t, ρ t ≤ H) → L + 3 ≤ H → H ≤ L + 9 →
    ∃ (len : ℕ) (c : ℕ → ℤ),
      FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c

/-- **The milestone of span nine.** `S3` holds at every band of span at most nine. -/
theorem s3_span_le_nine : S3SpanLeNine :=
  fun _ ρ σ i H L hlip hcr hLb hHb hLH hspan =>
    s3_span_nine ρ σ i H L hlip hcr hLb hHb hLH hspan

open HPC.Chain in
/-- **Bing 1948, Theorem 3**, block reading, three-link form, unconditional for a chain `D` of at
most ten links: if `E` is crooked in `D` and `D` has at most ten links, then `E` can be cut into
blocks, with the chosen link `i` opening the first block, so that every block lies in three
consecutive links of `D`.

This is the statement of `theorem3` (`HPC/Fold/Span.lean`) with the hypothesis `k ≤ 10`, and it is
proved from `s3_span_nine`: the span of the pair `(minIdx, maxIdx)` of the refinement is at most
`k - 1 ≤ 9`. -/
theorem theorem3_ten_links {X : Type*} [MetricSpace X] {n k : ℕ} (hn : 0 < n) (hk : k ≤ 10)
    {E : Chain X n} {D : Chain X k} (hcr : E.IsCrookedIn' D) (i : Fin n) :
    ∃ (q : ℕ) (β' : Fin n → Fin q) (hβ' : IsBlockMap β'),
      (β' i).val = 0 ∧ ∀ u, ∃ j : ℕ, (E.ofBlocks β' hβ').link u ⊆ D.unionRange j 3 := by
  classical
  have href : E.Refines D := hcr.1
  set ρ : Fin n → ℤ := fun t => ((href.minIdx t : ℕ) : ℤ) with hρ
  set σ : Fin n → ℤ := fun t => ((href.maxIdx t : ℕ) : ℤ) with hσ
  obtain ⟨tL, -, htL⟩ := Finset.exists_min_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  obtain ⟨tH, -, htH⟩ := Finset.exists_max_image Finset.univ ρ ⟨i, Finset.mem_univ i⟩
  set L : ℤ := ρ tL with hL
  set H : ℤ := ρ tH with hH
  have hLf : ∀ t, L ≤ ρ t := fun t => htL t (Finset.mem_univ t)
  have hHf : ∀ t, ρ t ≤ H := fun t => htH t (Finset.mem_univ t)
  by_cases hdeg : H ≤ L + 2
  · refine exists_blocks_first_of_range_le_two hn href i (href.minIdx tL).val (fun t => ?_)
    have h1 := hLf t
    have h2 := hHf t
    simp only [hρ, hL, hH] at h1 h2 hdeg
    omega
  · have hcase : L + 3 ≤ H := by omega
    have hL0 : (0 : ℤ) ≤ L := by
      simp only [hL, hρ]
      exact Int.natCast_nonneg _
    have hHk : H < (k : ℤ) := by
      simp only [hH, hρ]
      exact_mod_cast (href.minIdx tH).isLt
    have hspan : H ≤ L + 9 := by
      have : (k : ℤ) ≤ 10 := by exact_mod_cast hk
      omega
    have hlip : IsLip ρ := by
      intro t t' htt'
      have := minIdx_lip href t t' htt'
      simp only [hρ]
      rw [abs_le]
      omega
    have hcrook : IsCrookedIvF ρ σ := isCrookedIvF_minIdx_maxIdx hcr
    obtain ⟨len, c, hG, hT⟩ :=
      s3_span_nine ρ σ i H L hlip hcrook hLf hHf hcase hspan
    exact exists_blocks_first_of_folds href i _ _ hG hT

end HPC.Fold
