# Commission: batch 9 — Theorem 3 reduced to one open statement

**Go!** Runs on top of the batch-7/8 delivery. One new file, `HPC/Fold/Reduction.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

After batch 8, one gap separates the machinery from Bing 1948 Theorem 3: that the explicit
bump height serves both arms. This batch makes that gap a single named proposition,
`F2Prime`, proves everything on either side of it, and derives Theorem 3 from it. The result
is that the open problem is one `def ... : Prop` in the repository with no other loose end.

`F2Prime` is **not** to be proved in this batch. It is a hypothesis of the final theorem.

## Protocol

As batches 1–8. Batch-8 results expected: `SegLam`, `SegVee`, `phase`, `phase_add_isLip`,
`segLam_foldsOnto`, `segVee_foldsOnto`, `exists_blocks_first_of_segLam`. Batch-7:
`IsCrookedSeq`, `isCrookedSeq_minIdx`. Batch-6: `IsLip`, `armG`, `armT`. Batch-4/5:
`Chain.Refines.minIdx`, `minIdx_lip`, `minIdx_subset`, `IsBlockMap`, `ofBlocks`, `unionRange`.

## 1. The degenerate branch

**exists_blocks_first_of_range_le_two.** Suppose every `minIdx t` lies in `[c, c+2]`. Take
`q := 1` and `β' t := 0`. `IsBlockMap`: surjective onto `Fin 1`, and the Lipschitz condition is
`0 = 0`. The single block is `⋃ t, E.link t`, which lies in `D.unionRange c 3` because each
`E.link t ⊆ D.link (minIdx t)` (`minIdx_subset`) and `minIdx t ∈ [c, c+2]`. `(β' i).val = 0` by
construction. *(supply: that `ofBlocks` of the constant map has the single link equal to the
union, from `ofBlocks_link`.)*

This is the branch for a constant or near-constant minimal-index sequence, where no one-bump
itinerary exists at all: with `H − L ≤ 2` the hypothesis `L + 1 ≤ h ≤ max (H−1) p` of
`segLam_foldsOnto` is unsatisfiable. It is not a special case to be absorbed into the
itinerary machinery; it is a separate and easier argument.

## 2. The explicit height

`hStarArm f p` is the supremum of the levels `f j` such that every `j' ≤ j` has `f j' ≥ p − 1`
— that is, the greatest level reached strictly before the first drop to `p − 2`, or the
greatest level of the arm if it never drops. The set is nonempty (it contains `p`, witnessed
by `j = 0`) and bounded above (by the arm's maximum), so the supremum is attained.

*(supply: `hStarArm` is written with `sSup` over a set of integers. If a `Finset.max'` over
the image, or a recursive scan, is cleaner in Lean, use it and record the change; what the
rest of the file needs is exactly `hStarArm_mem` and `le_hStarArm`.)*

**hStarArm_mem.** Attainment: the set is a nonempty set of integers bounded above by
`Finset.sup` of the arm's values, so its supremum belongs to it.

**le_hStarArm.** `j = 0` witnesses `p` in the set: `j' ≤ 0` forces `j' = 0` and
`f 0 = p ≥ p − 1`.

`hStar ρ i H L` is `hStarArm` of the two arms, maxed, floored at `max (ρ i) (L+1)` and capped
at `max (H−1) (ρ i)`. `lStar` is the reflection. The floor at `L + 1` and the cap are exactly
the hypotheses `L + 1 ≤ h ≤ max (H−1) p` of `segLam_foldsOnto`.

## 3. Lemma A

**exists_peak_index.** Let `h ≤ hStarArm f p` with `p ≤ h`. By `hStarArm_mem` there is `j₀`
with `f j₀ = hStarArm f p ≥ h` and `f j' ≥ p − 1` for every `j' ≤ j₀`. Since
`f j₀ + phase f j₀ ≥ f j₀ ≥ h` (the phase is `0` or `1`, never negative — batch 8
`phase_zero_or_one`), the set of indices at which the phase-adjusted level reaches `h` is
nonempty; let `s` be its least element, so `s ≤ j₀ < m`.

Clause (2) holds at `s` by choice; clause (3) holds by minimality. For clause (1), let
`j < s ≤ j₀`. Then `f j ≥ p − 1` because `j ≤ j₀`. And `f j + phase f j < h` by minimality, so
`f j < h ≤ h + 1`. *(supply: the `Fin`/`ℕ` index bookkeeping.)*

Note what this does **not** give: for the arm that does *not* attain the maximum, `h` may
exceed its own `hStarArm`, the least peak index may fall after that arm's first drop, and
clause (1) may fail. Closing that is the content of `F2Prime`.

## 4. The open statement

`F2Prime` is the disjunction of "`SegLam` at `hStar` for both arms" and "`SegVee` at `lStar`
for both arms", for every crooked Lipschitz `ρ` with range at least three. Nothing to prove.

The range hypothesis `L + 3 ≤ H` is what makes the itinerary nondegenerate: it gives
`L + 1 ≤ H − 1 ≤ max (H−1) p`, so `hStar` lands in the admissible interval. Sequences of
smaller range go to §1.

## 5. Theorem 3 from F2′

**theorem3_of_F2Prime.** Let `ρ t := (minIdx t : ℤ)`, which is Lipschitz (`minIdx_lip`) and
crooked (`isCrookedSeq_minIdx`). Let `L` and `H` be the least and greatest values of `ρ`
(attained; `Fin n` is nonempty by `hn`).

*Case `H ≤ L + 2`.* Apply §1 with `c := L.toNat`.

*Case `L + 3 ≤ H`.* Apply `hF2` to get the disjunction. In the first case, both arms satisfy
`SegLam` at `hb := hStar ρ i H L`; check the hypotheses of `exists_blocks_first_of_segLam`:
`IsLip` of each arm (batch 6 `armG_isLip`, `armT_isLip`), the bounds `L ≤ ρ t ≤ H`, and
`p ≤ hb ≤ max (H−1) p`, `L ≤ p`, `L + 1 ≤ hb` — all from the definition of `hStar` together
with `le_hStarArm` and `L + 3 ≤ H`. Conclude. In the second case the same with `SegVee`,
`lStar`, and the reflected bridge. *(supply: if `exists_blocks_first_of_segLam` has no
`SegVee` counterpart in batch 8, add one here by the same two-line composition —
`segVee_foldsOnto` on each arm, then batch-6 `exists_blocks_first_of_folds` — and record it.)*

## 6. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: the encoding chosen for `hStarArm`; whether a `SegVee` bridge had to be added; what
   was supplied; any statement that did not go through.

## 7. Not in this batch

`F2Prime` itself. Bing 1948 Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9 gap.
