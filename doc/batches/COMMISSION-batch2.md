# Commission: batch 2 — matching covers give a homeomorphism (Bing 1948, Theorem 11)

**Go!** Runs on top of the batch-1 delivery (run f8bc1f85-7d33-43c7-816f-8a343b76dfae). One
new file, `HPC/Covers/Matching.lean`; root `HPC.lean` updated to import it; nothing in
`HPC/Chains/` touched. Every `sorry` is a work item; delivery contains none.

## Purpose

Theorem 11 is the engine of Bing's uniqueness theorem: two compacta equipped with sequences
of "matching" finite open covers of summable mesh are homeomorphic. It mentions no chains and
is used verbatim again by Bing–Jones for the circle of pseudo-arcs. It is stated here with the
point-tracking clause that Theorem 12 needs (that a common index sequence forces `T p = q`),
which Bing uses without stating.

## Protocol

As batch 1: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`; `#print axioms`
on every theorem showing only `propext`, `Classical.choice`, `Quot.sound`; census first;
report rather than repair; first task is to make the skeleton compile with proofs still
`sorry`, changing only syntax and mathlib names, recording every change. Toolchain and
mathlib as in the session (v4.28.0).

The auxiliary lemmas in §2 of the skeleton (`rad_eq`, `rad_pos`, `rad_tendsto_zero`,
`subset_fat`, `isOpen_fat`, `diam_fat_le`, `closure_fat_subset_fat`) are a suggested
decomposition, not a requirement: if a different route to the main theorem is cleaner, take
it and report the change; but `closure_fat_subset_fat` is the content of Bing's proof and
should appear in some form.

## 1. Definitions in the skeleton

- `tail ε i = ∑' l, ε (i + l)`, the sum `ε i + ε (i+1) + ⋯`.
- `rad ε i = ε i + 2 · tail ε (i+1)`, Bing's radius `ε_i + 2(ε_{i+1} + ε_{i+2} + ⋯)`.
- `fat S δ = Metric.thickening δ S`, the open `δ`-neighbourhood of `S`; Bing's `y`.
- `MatchingCovers M₁ M₂ ε`: index counts `N : ℕ → ℕ`; on each side a family
  `x_n : (i : ℕ) → Fin (N i) → Set X_n` of open sets; conditions (1) cover, (2) each element
  meets `M_n`, (3) bounded with `diam ≤ ε i`, (4) if the `j`-th element of level `i+1` meets
  the `k`-th of level `i` on one side, there are points of the corresponding two elements on
  the other side at distance `< ε i`; both directions.
- `Tracks_n C a p`: `p ∈ x_n i (a i)` for every `i`.

Condition (4) is phrased with witness points rather than a set-to-set distance, to avoid
needing a mathlib name for `inf { dist p q | p ∈ A, q ∈ B }`. For nonempty sets it is the
same condition.

## 2. Auxiliary statements

**rad_eq.** `rad ε i = ε i + 2 ε (i+1) + 2 · tail ε (i+2)`. Split the first term off the
tail sum; needs summability of the shifted sequence, which follows from `Summable ε`.

**rad_pos, rad_tendsto_zero.** Positivity: each summand positive. Limit: `ε i → 0` because
`ε` is summable, and `tail ε (i+1) → 0` because tails of a convergent series tend to zero.

**subset_fat, isOpen_fat.** Mathlib: `Metric.self_subset_thickening`, `Metric.isOpen_thickening`
(names to be confirmed).

**diam_fat_le.** Two points of the thickening are within `δ` of points of `S`, which are within
`diam S` of each other.

**closure_fat_subset_fat** — the nesting lemma. Let `z` be in the closure of
`fat B (rad ε (i+1))`. Fix any `η > 0`. There is `z'` in `fat B (rad ε (i+1))` with
`dist z z' < η`, hence `b' ∈ B` with `dist z' b' < rad ε (i+1)`. Let `p ∈ B`, `q ∈ A` be the
witnesses of `hclose`, so `dist p q < ε i`. Then
`dist z q ≤ dist z z' + dist z' b' + dist b' p + dist p q
        < η + rad ε (i+1) + ε (i+1) + ε i`.
By `rad_eq`, `rad ε (i+1) = ε (i+1) + 2 ε (i+2) + 2 tail ε (i+3)` and
`rad ε i = ε i + 2 ε (i+1) + 2 tail ε (i+2) = ε i + 2 ε (i+1) + 2 ε (i+2) + 2 tail ε (i+3)`,
so `rad ε (i+1) + ε (i+1) + ε i = rad ε i`. Hence `dist z q < rad ε i + η`. Since
`dist p q < ε i` strictly, the slack `ε i − dist p q > 0` absorbs `η` for `η` small enough,
giving `dist z q < rad ε i` and `z ∈ fat A (rad ε i)`.

## 3. The main theorem — Bing's proof

Write `x(n,i)_k` for `C.x_n i k` and `y(n,i)_k` for `fat (x(n,i)_k) (rad ε i)`.

**Step 1: nesting across consecutive levels.** If `x(n,i)_r` meets `x(n,i+1)_s`, then
`closure y(m,i+1)_s ⊆ y(m,i)_r`, for `m` the other side. This is `closure_fat_subset_fat`
with `A = x(m,i)_r`, `B = x(m,i+1)_s`, `hdiam` from `diam_m`, and `hclose` from `match_n`.

**Step 2: nesting across any levels.** If `i < j` and `x(n,i)_r` meets `x(n,j)_s`, then
`closure y(m,j)_s ⊆ y(m,i)_r`. Pick a common point `c`; by `cover_n` choose at each
intermediate level `l` an element `x(n,l)_{t_l}` containing `c`, with `t_i = r`, `t_j = s`.
Consecutive elements all contain `c`, so they meet; apply Step 1 at each step and chain the
inclusions (closure of a subset of an open set that is itself inside the next … — the
inclusions are `closure y(m,l+1) ⊆ y(m,l)`, and `y(m,l) ⊆ closure y(m,l)`, so they compose).

**Step 3: diameters shrink.** By `diam_fat_le`, `diam y(n,i)_k ≤ ε i + 2 rad ε i`, which tends
to `0` by `rad_tendsto_zero`. Hence for every `δ > 0` there is `j` such that every `y(n,j)_k`
has diameter `< δ`, on both sides.

**Step 4: definition of T on points.** Let `P ∈ M₁`. By `cover₁` there is, for each `i`, an
index `a i` with `P ∈ x(1,i)_{a i}`. Consecutive elements of this sequence meet (both contain
`P`), so by Step 1 the sets `y(2,i)_{a i}` form a sequence whose closures are nested
decreasing, `closure y(2,i+1) ⊆ y(2,i)`. Each closure is closed and, being bounded in the
metric space `X₂`, — note: closedness and nestedness alone do not give a nonempty
intersection in a general metric space; use instead that `y(2,i)_{a i}` meets `M₂` (it
contains `x(2,i)_{a i}` by `subset_fat`, which meets `M₂` by `meet₂`), so the nested sets
`closure y(2,i)_{a i} ∩ M₂` are nonempty compact and decreasing, hence have nonempty
intersection by compactness of `M₂`. Their diameters tend to `0` by Step 3, so the
intersection is a single point. Define `T P` to be it. It lies in `M₂`.

**Step 5: T is well defined.** If `b` is another sequence with `P ∈ x(1,i)_{b i}` for all `i`,
then `x(1,i+1)_{a(i+1)}` meets `x(1,i)_{b i}`, both containing `P`, so by Step 1
`closure y(2,i+1)_{a(i+1)} ⊆ y(2,i)_{b i}` for every `i`. Hence the intersection defining `T P`
via `a` is contained in the intersection via `b`. By symmetry they are equal. (In the
formalization one may instead define `T P` by choosing `a` with `Classical.choice` and prove
that the value is independent of the choice; either way, the point-tracking clause of the
theorem is then immediate: if `a` tracks `P` and `Q`, then `Q ∈ y(2,i)_{a i}` for all `i` by
`subset_fat`, so `Q` is the unique point of the intersection, i.e. `T P = Q`.)

**Step 6: continuity.** Let `P ∈ M₁` and `V` an open neighbourhood of `T P` in `X₂`. Choose a
ball of radius `ρ` about `T P` inside `V`, and by Step 3 choose `j` with every `y(2,j)_k` of
diameter less than `ρ`; then every `y(2,j)_k` containing `T P` lies in `V`. Let `r` be such
that `P ∈ x(1,j)_r`. For any `P' ∈ M₁ ∩ x(1,j)_r`, choose a tracking sequence `a'` for `P'`
with `a' j = r`. Then `x(1,j+1)_{a'(j+1)}` and `x(1,j)_r` both contain `P'`, so by Step 1
`T P' ∈ closure y(2,j+1)_{a'(j+1)} ⊆ y(2,j)_r`. The same argument with `P` gives
`T P ∈ y(2,j)_r`, so `y(2,j)_r ⊆ V`, hence `T P' ∈ V`. Since `M₁ ∩ x(1,j)_r` is a
neighbourhood of `P` in `M₁` (`open₁`), `T` is continuous at `P`.

**Step 7: surjectivity.** Let `Q ∈ M₂` and `V` an open neighbourhood of `Q`. Choose `j` as in
Step 6 so that every `y(2,j)_k` containing `Q` lies in `V`, and `r` with `Q ∈ x(2,j)_r` (by
`cover₂`). By `meet₁`, `M₁ ∩ x(1,j)_r` is nonempty; pick `P'` in it. As in Step 6,
`T P' ∈ y(2,j)_r ⊆ V`. So `T(M₁)` meets every neighbourhood of every point of `M₂`, i.e. is
dense in `M₂`. `T(M₁)` is compact (continuous image of a compact set), hence closed, hence
equals `M₂`.

**Step 8: injectivity.** Suppose `P₁ ≠ P₂` in `M₁` with `T P₁ = T P₂ =: Q`. By Step 3 choose
`k` so that every `y(1,k)_t` has diameter less than `dist P₁ P₂`; then no `y(1,k)_t` contains
both. Let `r` be such that `Q ∈ x(2,k)_r`. Choose `j > k` so that every `y(2,j)_t` containing
`Q` lies in `x(2,k)_r` — possible because `x(2,k)_r` is open and the diameters of the
`y(2,j)_t` tend to `0`. Let `u`, `v` be such that `P₁ ∈ x(1,j)_u`, `P₂ ∈ x(1,j)_v`. By the
definition of `T`, `Q ∈ y(2,j)_u` and `Q ∈ y(2,j)_v`, so both `x(2,j)_u` and `x(2,j)_v` lie
in — in particular meet — `x(2,k)_r`. By Step 2 in the other direction (side 2 meeting
forces side 1 nesting), `closure y(1,j)_u ⊆ y(1,k)_r` and `closure y(1,j)_v ⊆ y(1,k)_r`. But
`P₁ ∈ x(1,j)_u ⊆ y(1,j)_u` and `P₂ ∈ x(1,j)_v ⊆ y(1,j)_v`, so `y(1,k)_r` contains both.
Contradiction.

**Step 9: conclusion.** `T : M₁ → M₂` is a continuous bijection from a compact space to a
Hausdorff space, hence a homeomorphism (`Continuous.homeoOfEquivCompactToT2` or the
equivalent). The tracking clause is Step 5.

## 4. Deliverables

1. Census of every name introduced, with mathlib dependencies.
2. The skeleton compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: what was supplied at each step, any restructuring of the suggested auxiliary
   lemmas, and any statement that did not go through as written, with the point of failure.

## 5. Not in this batch

Bing 1948 Theorems 3, 4, 5, 6, 12; the reduction in Bing 1951; the D8/D9 gap.
