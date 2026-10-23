# Commission: batch 5 — schedules and the range-covering lemma

**Go!** Runs on top of the batch-4 delivery (run ae010870-dfbd-45e9-9fbe-5b8793307372). One
new file, `HPC/Chains/Schedule.lean`; root `HPC.lean` updated. Nothing else touched. Every
`sorry` is a work item; delivery contains none.

## Purpose

Bing 1948 Theorems 3 and 4, in the block reading, are statements about 1-Lipschitz functions
on link indices with a window condition on fibers, and nothing else. This batch proves that
reformulation in both directions, its three-link specialization (the form in which the
theorems will be stated), and the range-covering lemma — the first structural consequence of
crookedness for the two arms of a chain read outward from a link. The remaining content of
Theorems 3–4 (the "Folding Lemma") is not in this batch.

## Protocol

As batches 1–4. Batch-4 results expected to be used: `IsBlockMap`, `ofBlocks`,
`ofBlocks_link`, `Refines.minIdx`, `minIdx_subset`, `minIdx_le`, `minIdx_lip`,
`subset_adjacent_of_subset`, `minIdx_near_of_inter`; batch-1: `link_nonempty`, `Between`,
`IsCrookedIn'`; the discrete intermediate value lemmas of `Aux`, including the
adjacent-crossing form added in batch 4.

## 1. Definitions

- `unionRange D j w = ⋃_{j ≤ j' < j+w, j' < n} D.link j'`.
- `IsSchedule β`: `β : Fin m → ℕ` moves by at most one between adjacent indices and attains
  `0`.

## 2. Proofs

### IsSchedule.exists_blockMap

Let `M := Finset.sup Finset.univ β` (or the maximum over the finite domain; the domain is
nonempty since `β` attains `0`). Put `p := M + 1` and `β' t := ⟨β t, _⟩`, the bound from
`β t ≤ M`. Lipschitz: from `hβ.lip`. Surjective: `β` attains `0` and attains `M` (the sup
over a nonempty finite set is attained), and moves by at most one, so by the discrete
intermediate value theorem it attains every value in `[0, M]`.

### exists_blocks_of_schedule

Take `p, β', hβ'` from `IsSchedule.exists_blockMap`. For a block `u`, pick `t₀` with
`β' t₀ = u` (surjectivity) and let `j` be the least value of `minIdx` over the fiber
`{t | β t = β t₀}` (nonempty finite). Every `t` in the fiber has `minIdx t ≥ j` by minimality
and `minIdx t ≤ minIdx t₀' + (w−1)` for the `t₀'` attaining `j`, by `hwin`; so
`minIdx t ∈ [j, j + w − 1]`. Since `E.link t ⊆ D.link (minIdx t)` (`minIdx_subset`), each link
of the fiber lies in `unionRange j w`, hence so does their union, which is
`(E.ofBlocks β' hβ').link u` by `ofBlocks_link`.

### schedule_of_blocks

*Schedule.* `lip` is `hβ'.lip`. `zero`: `p ≥ 1` since `β'` is surjective from a nonempty type
(`hm`); take `t` with `β' t = 0`.

*Window.* Let `β' t = β' t' = u` and `j` with the block inside `unionRange j w`. Claim:
`minIdx t ∈ [j − 1, j + w − 1]` (with `j − 1` read as `0` when `j = 0`). `E.link t` is nonempty
and lies in `D.link (minIdx t)` and in `unionRange j w`, so `D.link (minIdx t)` meets some
`D.link j'` with `j ≤ j' ≤ j + w − 1`; by adjacency `|minIdx t − j'| ≤ 1`, so
`minIdx t ∈ [j − 1, j + w]`. Exclude `minIdx t = j + w`: then `E.link t ⊆ D.link (j+w)` and
also `⊆ unionRange j w`; the only link of the range meeting `D.link (j+w)` is
`D.link (j+w−1)`, so `E.link t ⊆ D.link (j+w) ∩ D.link (j+w−1) ⊆ D.link (j+w−1)`, whence
`minIdx t ≤ j + w − 1` by `minIdx_le`. Contradiction. So both `minIdx t` and `minIdx t'` lie in
`[j − 1, j + w − 1]`, an interval of length `w`.

(The lower end `j − 1` is not excludable: a link inside `D.link j ∩ D.link (j−1)` has minimal
index `j − 1` and lies in the block's range. This is why the bound is `w` and not `w − 1`.)

### exists_blocks_of_walk

Apply `exists_blocks_of_schedule` with `w := 3`: for `β t = β t'`, both `minIdx t` and
`minIdx t'` are within one of `b (β t)`, hence within two of each other.

### range_covering

Write `ρ := minIdx`, `T := {t | t ≤ i}`, `G := {g | i ≤ g}` (both contain `i`). Let
`lo_T, hi_T, lo_G, hi_G` be the least and greatest values of `ρ` on `T` and on `G`, attained
at `t_lo, t_hi ∈ T` and `g_lo, g_hi ∈ G`. Note `hi_T ≥ ρ i ≥ lo_G` and `hi_G ≥ ρ i ≥ lo_T`.

The statement is: `(lo_G ≤ lo_T + 1 ∧ hi_T ≤ hi_G + 2) ∨ (lo_T ≤ lo_G + 1 ∧ hi_G ≤ hi_T + 2)`,
since e.g. `∀ t ∈ T, ∃ g ∈ G, ρ g ≤ ρ t + 1` is equivalent to `lo_G ≤ lo_T + 1` (take
`g := g_lo`, and conversely apply it to `t := t_lo`), and similarly for the other three
clauses.

**Claim A.** Not (`lo_T + 2 ≤ lo_G` and `hi_T + 3 ≤ hi_G`).

Suppose both. `E.link t_lo ⊆ D.link lo_T` meets `D.link lo_T`; `E.link g_hi` meets
`D.link hi_G`; and `lo_T + 2 < hi_G` since `hi_G ≥ hi_T + 3 ≥ lo_G + 3 ≥ lo_T + 5`. Apply
`h` with `(h, k) := (lo_T, hi_G)`, `(i, j) := (t_lo, g_hi)`: there are `r, s` with
`Between t_lo r s g_hi`, `E.link r ⊆ D.link (hi_G − 1)`, `E.link s ⊆ D.link (lo_T + 1)`. Since
`t_lo ≤ i ≤ g_hi` and `t_lo < g_hi` (as `ρ t_lo ≠ ρ g_hi`), `Between` gives
`t_lo < r < s < g_hi`. From `E.link r ⊆ D.link (hi_G − 1)` and `E.link r ⊆ D.link (ρ r)`,
adjacency gives `ρ r ≥ hi_G − 2 ≥ hi_T + 1 > hi_T`, so `r ∉ T`, i.e. `i < r`, so `r ∈ G` and
hence `s ∈ G` (as `r < s`). But `E.link s ⊆ D.link (lo_T + 1)` gives `ρ s ≤ lo_T + 1 ≤ lo_G − 1`
by `minIdx_le`, contradicting `ρ s ≥ lo_G`.

**Claim B.** Not (`lo_G + 2 ≤ lo_T` and `hi_G + 3 ≤ hi_T`).

Suppose both. Apply `h` with `(h, k) := (lo_G, hi_T)`, `(i, j) := (g_lo, t_hi)`: note
`g_lo ≥ i ≥ t_hi` and they are distinct, so `Between g_lo r s t_hi` gives
`g_lo > r > s > t_hi`. `E.link r ⊆ D.link (hi_T − 1)` gives `ρ r ≥ hi_T − 2 ≥ hi_G + 1 > hi_G`,
so `r ∉ G`, i.e. `r < i`, so `r ∈ T` and hence `s ∈ T` (as `s < r`). But
`E.link s ⊆ D.link (lo_G + 1)` gives `ρ s ≤ lo_G + 1 ≤ lo_T − 1 < lo_T`, contradicting
`ρ s ≥ lo_T`.

**Conclusion.** If `lo_T + 2 ≤ lo_G`, Claim A gives `hi_G ≤ hi_T + 2`, and `lo_T ≤ lo_G + 1`
holds trivially: second disjunct. Otherwise `lo_G ≤ lo_T + 1`; if also `hi_T ≤ hi_G + 2`, first
disjunct; if instead `hi_G + 3 ≤ hi_T`, Claim B gives `lo_T ≤ lo_G + 1`, and `hi_G ≤ hi_T + 2`
holds trivially: second disjunct.

*(supply: the four equivalences between the pointwise clauses and the `lo/hi` inequalities,
and the existence of the four extremal indices — `Finset.exists_min_image` on `Finset.univ.filter`
or the like.)*

## 3. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: what was supplied at each step; any statement that did not go through.

## 4. Not in this batch

The Folding Lemma; Theorems 3, 4, 5, 6; the reduction; the D8/D9 gap.
