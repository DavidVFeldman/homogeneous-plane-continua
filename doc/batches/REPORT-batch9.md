# Report — batch 9: Theorem 3 reduced to one open statement

Delivered complete. One new file, `HPC/Fold/Reduction.lean`; the root `HPC.lean` supplied by
the batch was installed unchanged; the commission text is kept as `COMMISSION-batch9.md`.
Nothing else in the project was touched.

`lake build` succeeds on `RequestProject` and `HPC`. The new file contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`, and every theorem of it has axiom
profile exactly `[propext, Classical.choice, Quot.sound]`.

As commissioned, `F2Prime` is **not** proved: it is a `def ... : Prop` and a hypothesis of the
final theorem. Everything on either side of it is proved.

## 1. Census

Definitions (all as commissioned, verbatim):

| name | mathlib dependencies |
| --- | --- |
| `HPC.Fold.hStarArm` | `sSup` on `ℤ` (conditionally complete lattice instance) |
| `HPC.Fold.lStarArm` | — |
| `HPC.Fold.hStar` | `min`, `max` on `ℤ` |
| `HPC.Fold.lStar` | `min`, `max` on `ℤ` |
| `HPC.Fold.F2Prime` | — |

Theorems:

| name | depends on (project) | depends on (mathlib) |
| --- | --- | --- |
| `exists_blocks_first_of_range_le_two` | `IsBlockMap`, `ofBlocks_link`, `minIdx_subset`, `Chain.link_subset_unionRange` | `Subsingleton.elim`, `Set.iUnion₂_subset`, `omega`, `simp` |
| `hStarArm_mem` | `hStarArm` | `Int.csSup_mem`, `Set.finite_range`, `Set.Finite.subset`, `Set.Finite.bddAbove`, `Fin.le_def`, `Fin.ext` |
| `le_hStarArm` | `hStarArm` | `le_csSup`, `Set.finite_range`, `Set.Finite.subset`, `Set.Finite.bddAbove`, `Fin.le_def`, `Fin.ext` |
| `exists_peak_index` | `hStarArm_mem`, `phase`, `phase_zero_or_one`, `exists_least_index`, `IsLip` | `lt_of_not_ge`, `Fin.ext`, `Fin.le_def`, `omega` |
| `exists_blocks_first_of_segVee` (added) | `SegVee`, `segVee_foldsOnto`, `veeBumpLen`, `veeBumpCenter`, `armG`, `armT`, `exists_blocks_first_of_folds`, `Refines.minIdx` | `omega` |
| `theorem3_of_F2Prime` | `F2Prime`, `exists_blocks_first_of_range_le_two`, `exists_blocks_first_of_segLam`, `exists_blocks_first_of_segVee`, `hStar`, `lStar`, `minIdx_lip`, `isCrookedSeq_minIdx`, `armG_isLip`, `armT_isLip` | `Finset.exists_min_image`, `Finset.exists_max_image`, `abs_le`, `omega` |

Axiom profile of each of the six theorems: `[propext, Classical.choice, Quot.sound]`.

## 2. Changes

* **Encoding of `hStarArm`.** No change: the commissioned `sSup` form is kept. The defining
  set is a subset of the range of the arm, hence finite, hence bounded above, and it contains
  `p`; `Int.csSup_mem` then gives `hStarArm_mem` and `le_csSup` gives `le_hStarArm`. Neither a
  `Finset.max'` nor a recursive scan was needed.
* **A `SegVee` bridge had to be added.** Batch 8 delivers `exists_blocks_first_of_segLam` but
  no valley counterpart, so `exists_blocks_first_of_segVee` is added here, by exactly the
  composition the commission describes: `segVee_foldsOnto` on each arm, then batch-6
  `exists_blocks_first_of_folds`. Its numeric hypotheses are those of `segVee_foldsOnto`
  (`lb ≤ p`, `min (L+1) p ≤ lb`, `p ≤ H`, `lb + 1 ≤ H`), all of which `lStar` satisfies under
  `L + 3 ≤ H`.
* **Two commissioned hypotheses are unnecessary** and, following the convention of batches
  1–8, are kept in the statements with a leading underscore:
  * `_hn : 0 < n` in `exists_blocks_first_of_range_le_two` — the basepoint `i : Fin n` already
    makes the index type nonempty, which is all the surjectivity of the constant block map
    needs;
  * `_hf : IsLip f` and `_hph : p ≤ h` in `exists_peak_index` — the three clauses follow from
    `hStarArm_mem`, the minimality of the peak index and the nonnegativity of the phase alone.

  No other hypothesis is idle: in `theorem3_of_F2Prime` all four explicit binders are
  load-bearing.
* No commissioned statement failed, and none was weakened.

## 3. What was supplied

* **§1, degenerate branch.** `q := 1` and the constant block map. Surjectivity is
  `Subsingleton.elim` on `Fin 1` with the witness `i`; the Lipschitz clause is `0 = 0`. The
  single link of `ofBlocks` is the union of all links of `E` by `ofBlocks_link`, and
  `Set.iUnion₂_subset` reduces the containment to one link at a time: `E.link t ⊆ D.link
  (minIdx t)` by `minIdx_subset`, and `D.link (minIdx t) ⊆ D.unionRange c 3` by
  `link_subset_unionRange` since `c ≤ (minIdx t).val ≤ c + 2`.
* **§2, attainment.** The bookkeeping that `{v | ∃ j, f j = v ∧ …} ⊆ Set.range f`, that this
  range is finite, and hence that the set is bounded above; and that `j' ≤ ⟨0, hm⟩` in `Fin m`
  forces `j' = ⟨0, hm⟩` (`Fin.le_def`, then `Fin.ext` with the value equation stated
  explicitly, since the value of the literal `⟨0, hm⟩` is not unfolded by `omega` on its own).
* **§3, Lemma A.** The `Fin`/`ℕ` index bookkeeping: the peak predicate holds at the witness
  `j₀` of `hStarArm_mem` because the phase is `0` or `1`; `exists_least_index` supplies the
  least index `s` at which it holds; minimality forces `s ≤ j₀`, which is what puts every
  `j < s` inside the range `j ≤ j₀` on which `f ≥ p − 1` is known; and the upper bound
  `f j ≤ h + 1` follows from `f j + phase f j < h` with `phase ≥ 0`.
* **§5, Theorem 3.** The extremes `L` and `H` are produced as attained values by
  `Finset.exists_min_image` and `Finset.exists_max_image` over `Finset.univ`, nonempty because
  of the basepoint `i`; `L` is then automatically the cast of a natural number, so the
  degenerate branch can take `c := (minIdx tL).val` with no `toNat` bookkeeping. `IsLip ρ` is
  `minIdx_lip` with the `natAbs`/`|·|` conversion, and crookedness is `isCrookedSeq_minIdx`.
  In the non-degenerate branch all the numeric side conditions of the two bridges
  (`p ≤ hStar ≤ max (H−1) p`, `L + 1 ≤ hStar`, and the four `lStar` bounds) are linear
  consequences of `L ≤ ρ i ≤ H` and `L + 3 ≤ H` once `hStar`/`lStar` are unfolded, the two
  `hStarArm`/`lStarArm` values entering only as atoms.

## 4. Not in this batch

`F2Prime` itself; Bing 1948 Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9 gap.
