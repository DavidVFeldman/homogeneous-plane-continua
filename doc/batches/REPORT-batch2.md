# Report — batch 2: matching covers give a homeomorphism (Bing 1948, Theorem 11)

Delivery for the batch-2 commission (`COMMISSION-batch2.md`). One new file,
`HPC/Covers/Matching.lean`; the root `HPC.lean` updated to import it; nothing in `HPC/Chains/`
touched. `lake build` succeeds on `RequestProject` and `HPC`; the file contains no `sorry`,
`admit`, `axiom`, `native_decide` or `implemented_by`.

## 1. Census

All names live in namespace `HPC` (constructions on the data structure in
`HPC.MatchingCovers`). None collides with a mathlib name. The mathlib dependencies listed are
the nontrivial ones; ordinary algebraic/order lemmas and the `linarith`, `simp`, `omega`,
`gcongr`, `ring` tactics are used throughout and not listed.

### From the skeleton (unchanged statements unless noted)

| name | kind | mathlib used |
|---|---|---|
| `tail` | def | `tsum` |
| `rad` | def | — |
| `fat` | def | `Metric.thickening` |
| `rad_eq` | thm | — (via `tail_succ`) |
| `rad_pos` | thm | — |
| `rad_tendsto_zero` | thm | `Summable.tendsto_atTop_zero`, `Filter.tendsto_add_atTop_nat` |
| `subset_fat` | thm | `Metric.self_subset_thickening` |
| `isOpen_fat` | thm | `Metric.isOpen_thickening` |
| `diam_fat_le` | thm | `Metric.diam_thickening_le` |
| `closure_fat_subset_fat` | thm | `Metric.mem_closure_iff`, `Metric.dist_le_diam_of_mem`, `dist_triangle` |
| `MatchingCovers` | structure | `IsOpen`, `Bornology.IsBounded`, `Metric.diam` |
| `MatchingCovers.Tracks₁`, `.Tracks₂` | defs | — |
| `MatchingCovers.exists_homeomorph` | thm | `Continuous.homeoOfEquivCompactToT2`, `Equiv.ofBijective`, `isCompact_iff_compactSpace` |

### Added auxiliaries (agent)

| name | kind | content |
|---|---|---|
| `summable_shift` | thm | `Summable fun l => ε (i + l)` (from `summable_nat_add_iff`) |
| `tail_succ` | thm | `tail ε i = ε i + tail ε (i+1)` (from `Summable.tsum_eq_zero_add`) |
| `tail_nonneg` | thm | `0 ≤ tail ε i` (`tsum_nonneg`) |
| `tail_tendsto_zero` | thm | `tail ε i → 0` (`tendsto_sum_nat_add`) |
| `rad_nonneg` | thm | `0 ≤ rad ε i` |
| `isBounded_fat` | thm | `Bornology.IsBounded.thickening` |
| `mem_fat_iff` | thm | `Metric.mem_thickening_iff` |
| `mesh` | def | `mesh ε i = ε i + 2 * rad ε i`, the Step-3 diameter bound |
| `diam_fat_le_mesh` | thm | `diam (fat S (rad ε i)) ≤ mesh ε i` when `diam S ≤ ε i` |
| `mesh_tendsto_zero` | thm | `mesh ε i → 0` |
| `exists_mesh_lt` | thm | arbitrarily late levels with `mesh ε j < δ` |
| `eq_of_forall_dist_le_mesh` | thm | two points within every mesh are equal |
| `MatchingCovers.swap` | def | exchanges the two sides of the data |
| `MatchingCovers.y₁`, `.y₂` | defs | Bing's `y(n,i)_k = fat (x(n,i)_k) (rad ε i)` |
| `MatchingCovers.x₁_subset_y₁`, `.x₂_subset_y₂` | thms | `x ⊆ y` |
| `MatchingCovers.dist_le_mesh₁`, `.dist_le_mesh₂` | thms | two points of `closure (y i k)` are within `mesh ε i` |
| `MatchingCovers.step1₂`, `.step1₁` | thms | Step 1, nesting across consecutive levels |
| `MatchingCovers.step2₂`, `.step2₁` | thms | Step 2, nesting across any two levels |
| `MatchingCovers.trackSeq`, `.mem_trackSeq` | def/thm | a chosen index sequence tracking a point of `M₁` |
| `MatchingCovers.exists_limit_point` | thm | Step 4, the nested compacta have a common point |
| `MatchingCovers.toFun`, `.toFun_mem`, `.toFun_spec` | def/thms | Bing's `T` on points, and its defining property |
| `MatchingCovers.toFun_mem_y₂` | thm | Step 5, `T p ∈ y(2,j)_r` for *every* `r` with `p ∈ x(1,j)_r` |
| `MatchingCovers.toMap` | def | `T` as a map `M₁ → M₂` of subtypes |
| `MatchingCovers.continuous_toMap` | thm | Step 6 |
| `MatchingCovers.injective_toMap` | thm | Step 8 |
| `MatchingCovers.surjective_toMap` | thm | Step 7 |

## 2. First task: compiling the skeleton

The skeleton compiled as received, with all proofs `sorry`, with **no** changes to syntax or
mathlib names. The suggested mathlib names in §2 of the commission were confirmed:
`Metric.self_subset_thickening`, `Metric.isOpen_thickening`; in addition
`Metric.diam_thickening_le` supplies `diam_fat_le` directly.

## 3. Changes to the commissioned statements

Two hypotheses are not needed and are therefore named with a leading underscore, the statements
being otherwise exactly as commissioned (this is the convention already used in batch 1):

* `rad_pos`: `Summable ε` is not used (positivity of the tail sum needs only `0 < ε i`, since
  `tsum` of a nonnegative sequence is nonnegative even when the sequence is not summable).
* `rad_tendsto_zero`: `∀ i, 0 < ε i` is not used.
* `diam_fat_le`: `Bornology.IsBounded S` is not used, because `Metric.diam_thickening_le`
  holds for arbitrary `S`.
* `closure_fat_subset_fat`: `∀ i, 0 < ε i` is not used; the computation needs only the strict
  inequality `dist p q < ε i` supplied by `hclose` and the identity of `rad_eq`.

No statement failed to go through as written. No statement was weakened, strengthened or
replaced.

## 4. What was supplied at each step

* **`rad_eq`, `rad_pos`, `rad_tendsto_zero`** — as in §2 of the commission. The tail-splitting
  was factored out as `tail_succ`, whose proof needs the summability of the shifted sequence
  (`summable_shift`). `tail ε i → 0` is `tendsto_sum_nat_add` after commuting `i + l` to
  `l + i`.
* **`closure_fat_subset_fat`** — exactly Bing's computation as written in the commission. The
  quantifier over `η` is handled by taking `η := ε i - dist p q`, the slack of `hclose`, once
  and for all rather than "for `η` small enough": with that choice the chain of triangle
  inequalities gives `dist z q < rad ε i` directly.
* **Step 1** (`step1₂`) — `closure_fat_subset_fat` with `A = x₂ i r`, `B = x₂ (i+1) s`,
  `hdiam = diam₂`, `hclose = match₁`.
* **Step 2** (`step2₂`) — induction on the later level `j`. One point of the commission's
  argument needed care and is recorded here as a (small) strengthening of the hypothesis:
  the intermediate levels are chosen by `cover₁`, which covers only `M₁`, so the common point
  of `x(1,i)_r` and `x(1,j)_s` must be assumed to lie in `M₁`. The statement therefore reads
  `(C.x₁ i r ∩ C.x₁ j s ∩ M₁).Nonempty`. This is exactly what is available where Step 2 is
  used (Step 8), because the witness there is produced by `meet₂`, which returns a point of
  `M₂`.
* **Step 3** — `mesh`, `diam_fat_le_mesh`, `mesh_tendsto_zero`, `exists_mesh_lt`. The last is
  stated so as to produce a level *later than a prescribed one*, which Step 8 needs.
* **Steps 4, 5** — `exists_limit_point` uses
  `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` on
  `closure (y₂ i (a i)) ∩ M₂`, nonempty by `meet₂` and `x₂_subset_y₂`, decreasing by Step 1,
  compact because `M₂` is. `toFun` is defined from the chosen tracking sequence `trackSeq`.
  Independence of that choice is packaged as `toFun_mem_y₂`: `T p` lies in `y(2,j)_r` for
  *every* `r` with `p ∈ x(1,j)_r`, proved by applying Step 1 to the pair
  `x(1,j+1)_{trackSeq (j+1)}`, `x(1,j)_r`, both of which contain `p`. Every later step uses
  only `toFun_mem_y₂`, so no separate well-definedness argument is required.
* **Step 6** — `continuous_toMap`, via `Metric.continuous_iff`; the neighbourhood
  `M₁ ∩ x(1,j)_r` of `p` is turned into a metric ball using `open₁`.
* **Step 7** — `surjective_toMap`: the range is dense (`Metric.mem_closure_iff`) and compact
  (continuous image of the compact `M₁`), hence closed, hence everything.
* **Step 8** — `injective_toMap`, exactly as in the commission, with the witness for Step 2
  taken from `meet₂` as explained above.
* **Step 9** — `Continuous.homeoOfEquivCompactToT2` applied to `Equiv.ofBijective`. The
  tracking clause follows from `toFun_mem_y₂` and `eq_of_forall_dist_le_mesh`.

Side-1 versions of the symmetric statements (`step1₁`, `step2₁`, `dist_le_mesh₁`,
`x₁_subset_y₁`) are obtained by applying the side-2 versions to `C.swap`, the same data with
the two sides exchanged, rather than by duplicating the proofs.

## 5. Axiom profiles

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every theorem of the
file, namely: `rad_eq`, `rad_pos`, `rad_tendsto_zero`, `subset_fat`, `isOpen_fat`,
`diam_fat_le`, `closure_fat_subset_fat`, `summable_shift`, `tail_succ`, `tail_nonneg`,
`tail_tendsto_zero`, `rad_nonneg`, `isBounded_fat`, `mem_fat_iff`, `diam_fat_le_mesh`,
`mesh_tendsto_zero`, `exists_mesh_lt`, `eq_of_forall_dist_le_mesh`,
`MatchingCovers.x₁_subset_y₁`, `.x₂_subset_y₂`, `.dist_le_mesh₁`, `.dist_le_mesh₂`, `.step1₁`,
`.step1₂`, `.step2₁`, `.step2₂`, `.mem_trackSeq`, `.exists_limit_point`, `.toFun_mem`,
`.toFun_spec`, `.toFun_mem_y₂`, `.continuous_toMap`, `.injective_toMap`, `.surjective_toMap`,
`.exists_homeomorph`.
