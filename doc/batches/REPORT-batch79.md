Commission read: `COMMISSION-batch79.md`, with its `Theorem4Pair.lean`.

# Report — batch 79: Theorem 4 for a chain from `R` to `S`; Theorem 10; statements of Theorems 5, 6, 13

**No counterexample.** I re-read the definitions behind the three targets: `IsCrookedIn'`,
`IsBlockMap`, `ofBlocks`, `unionRange`, `Refines.minIdx/maxIdx`, `Q78.IsContinuum`,
`Q78.IsIndecomposable`, `Q78.Theorem10Statement` and `Description`. None of them makes a statement
vacuous or false. `theorem4_pair` keeps the skeleton's statement **exactly**, with three-link windows
at every block, the two end blocks included. It did not need weakening to four links, and the diff
of the statement against the uploaded `Theorem4Pair.lean` is empty.

| target | status |
|---|---|
| 1. `theorem4_pair` (`HPC/Fold/Theorem4Pair.lean`) | **proved**, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]` |
| 2. `theorem10` (`HPC/PseudoArc/Theorem10.lean`) | **proved**, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]` |
| 3. Theorems 5, 6, 13 (`HPC/PseudoArc/Statements79.lean`) | statements written; they elaborate and add no `sorry` |

`axioms-batch79.txt` is the output of `lake env lean Axioms79.lean`. `lake build HPC` is clean
(8203 jobs). `HPC.lean` now imports `HPC.Fold.Theorem4Pair`, `HPC.Fold.Questions78`,
`HPC.PseudoArc.Theorem10` and `HPC.PseudoArc.Statements79`. As before, the only live `sorry` in the
build is `theorem3_end`, which none of this batch uses.

## 1. Targets

### 1.1 `theorem4_pair`: proved

Statement: as in the skeleton, with `(β' r) = (β' r') = 0`, `(β' s') = (β' s) = q − 1`, and every
block inside `D.unionRange j 3`.

**The idea.** Write `ρ`/`σ` for the least/greatest coarse index of a fine link. The batch-77/78
fold from a basepoint `i` starts its jump walk at `ρ(i) − 1` or at `ρ(i) + 1`. The fold's block 0
consists of the links on the initial stretch whose level stays within one of that start. So block 0
contains a neighbour `i ± 1` of `i` whenever that neighbour's level is within one of the start
(`fold_of_fit_zero`). For a pair `(r, r')`:

* If `ρ(r) = ρ(r')`, either start works, and `first_direction` provides one of them.
* Otherwise call the lower link `lo` (level `x`) and the upper one `hi` (level `x + 1`). The
  adjacency field gives `σ(hi) = x + 1`. There are two candidate folds:
  * **(a)** the fold on `ρ` from `lo`, started *above*, at `x + 1`. Its window `[x, x + 2]` holds
    both links. It is forbidden exactly by the event `EvUp ρ lo`: an arm reaches `x + 3` before
    going below `x`.
  * **(b)** the fold on `σ` from `hi`, started *below*, at `x`. Its window holds `σ(lo) ∈ {x, x+1}`
    and `σ(hi) = x + 1`. It is forbidden exactly by `EvDown σ hi`: an arm's `σ` reaches `x − 2`
    before exceeding `x + 1`, or the fake low link does, when `x = 2`.

  **`pair_exclusion`** shows that the two events cannot both happen:
  * If both arms are on the same side of the pair, the first exit of the common path contradicts
    one of the two events.
  * On opposite sides, the crookedness clause between the two event links gives links at levels
    `x + 2` and `x − 1` in the wrong order. When the fake link is involved, the chain-level clause
    with `D.link 0` (`meet_low_gen`) plays that part.

  The fold on `σ` is the batch-78 fold with a fake *high* end, applied to `N − 1 − σ`
  (`fold_high_end_mode`). Its crookedness comes from `D.reverse`, and its end condition from
  `σ(a) ≤ 1` for the link `a` that meets `D.link 0`.
* If `a = r` (the low meeting link is `r` itself), the fold is on `ρ` from `r`, started below. Then
  `U = 0`, and `r'` goes to block 0 through the middle grouping, because `ρ(r') ≤ 2`.

**The splice.** `splice_schedule_pair` is `B78.splice_schedule` with two changes:
* the prefix and suffix folds may be read on any levels `lP`, `lQ` with `ρ ≤ l ≤ σ`;
* it also reports that links at prefix time 0 (resp. suffix time 0) go to the first (resp. last)
  block, and handles the case `U = 0` (resp. `V = 0`).

The suffix fold is the prefix fold for `E.reverse`, `D.reverse` (`pair_suffix_fold`).

**Assembly (`theorem4_pair`):**
* **`k ≥ 6`:** `theorem4_pair_core` in the orientation where the low link comes first, and
  `D.reverse` otherwise.
* **`k = 4, 5`:** every link lies in the first three or the last three coarse links, and each
  basepoint pair lies wholly in one of the two windows. `pair_windows` gives two or three blocks,
  and the middle block is the high (or low) meeting link. That link lies strictly between the pairs
  whenever it is needed.
* **`k = 3`:** one block.
* **`k ≥ 4` and `r' = s'`:** this is impossible, because the crookedness clause puts two links
  strictly between the low and high meeting links, which lie among three consecutive links.

New files, namespace `HPC.Fold.B79` unless noted, none containing a `sorry`:
* `Pair79Fold.lean` (namespace `Z77`): the greedy fold with its first direction chosen, and
  `fold_of_fit_zero`.
* `Pair79Ends.lean`: the folds with a fake low or high end link and a chosen start.
* `Pair79Any.lean`: crookedness of the extended sequences, and folds whose start is whichever
  direction is available.
* `Pair79Seq.lean`: the events `EvUp`/`EvDown` and their translation to the first-direction
  conditions.
* `Pair79Fin.lean`: the folds on `Fin n` (`finfold_low`, `finfold_low_any`, `finfold_high`).
* `Pair79Excl.lean`: `pair_exclusion`.
* `Pair79Chain.lean`: `pair_prefix_fold`.
* `Pair79Splice.lean`: `splice_schedule_pair`.
* `Pair79Assemble.lean`: `pair_suffix_fold`, `assemble_pair`, `theorem4_pair_core`, `pair_windows`.

### 1.2 Theorem 10: proved

`HPC.Description.theorem10 (Δ : Description X P Q) : Q78.Theorem10Statement Δ`. It uses no
compactness of `X`.

The three missing ingredients named in the commission, and how each was handled:
* **The separation step.** Proved as `Chain.inter_link_nonempty_between`: a preconnected set inside
  the union of a chain, meeting links `a < c`, meets every link `b` between them. The unions of the
  links before `b` and of those after `b` are disjoint open sets.
* **Every link of the subchain meets the continuum.** This is not needed as a separate lemma. It is
  the same separation statement, applied to `K` and to the pieces `A`, `B`.
* **Bing's subchain `D_j(h, k)`.** Also not needed for Theorem 10. The proof works with the two
  links holding `p` and `q` and with the crookedness clause between them (`theorem10_core`).

The mesh step uses `Chain.dist_le_of_mem_link`: points of adjacent links are within `2ε` of each
other. Bing's `2/j` becomes a level whose mesh is less than `δ/3`.

### 1.3 Theorems 5, 6, 13: statements (`HPC/PseudoArc/Statements79.lean`)

Each statement is a `def … : Prop`:
* `Description.Theorem5Statement`
* `Description.Theorem6Statement`, plus `Theorem6PosStatement` (Theorem 6 with `j > 0`)
* `Description.Theorem13Statement`: for all `P₁ P₂ ∈ Δ.M` there is `T : Δ.M ≃ₜ Δ.M` with
  `T P₁ = P₂`

The auxiliary notions are defined in the same file:
* `Description.shift`: the tail `D_i, D_{i+1}, …`, which is again a description.
* `IsPatternFromTo`: Bing's pattern from `h` to `k`.
* `Chain.IsConsolidationOn`: a consolidation of a set of links.
* `composant`: the union of the proper subcontinua containing a point.
* `Chain.IsSubchainFrom`: Bing's `D_i(R, S)`, the subchain whose end links hold `R` and `S` and
  no other link does.

Indexing follows the repository: Bing's `D_1` is `Δ.D 0`.

**`PatternFollowing` versus Theorem 6.** They are the same up to re-indexing, with one difference:
`PatternFollowing` asks for a deeper level `j > i`, while Theorem 6 asks only for "some `j`". Both
directions are proved:
* `theorem6_shift_of_patternFollowing`: `PatternFollowing Δ` gives Theorem 6, with `j > 0`, for
  every tail `Δ.shift i`.
* `patternFollowing_of_theorem6Pos`: Theorem 6 with `j > 0` for every tail gives
  `PatternFollowing Δ`.

Bing's proof of Theorem 6 does produce a deep level. So the hypothesis of Theorem 12 is exactly
"Theorem 6 (with `j > 0`) for every tail".

## 2. The two questions of §2

1. **Merge, then fold.** This route was not used, and whether the merged sequence is
   `IsCrookedIvF` was not settled. The obstacle is the one the commission names. A crookedness
   witness "within one index of `s`" in the merged sequence can sit two original indices away. The
   original clause then yields witnesses that may fall on the merged index itself rather than
   strictly beyond it. So the merged clause does not follow index by index, and I did not look for
   a proof or a counterexample of it.

2. **Start the zigzag from an edge.** A form of this route works, and it needs neither two start
   levels nor a fake basepoint link. The walk starts at a single level: `ρ(lo) + 1 = ρ(hi)` for the
   fold on `ρ` from `lo`, or `σ(hi) − 1` for the fold on `σ` from `hi`. That level is within one of
   both basepoint links, so both land in block 0 and the window stays three links wide. What the
   route needs is the first-direction condition at that start, and it can fail on the `ρ`-reading.
   An exploratory search suggested that this does happen; that search is not formalized and is
   not a verified result. The new fact, proved as
   `pair_exclusion`, is that it then holds on the `σ`-reading from the other link. The batch-78
   fake end link is unchanged: a fake link at level `0` for the `ρ`-fold, and one at the top level
   of `N − 1 − σ` for the `σ`-fold.

No four-link window was needed at either end.
