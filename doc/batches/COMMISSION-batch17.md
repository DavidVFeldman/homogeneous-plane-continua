# Commission: batch 17 — shrinking the valley conjectures

**Go!** Runs on top of the batch-16 delivery. One new file, `HPC/Fold/Shrink.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

`F2Prime` rests on `ExitReach`, `HighExitValley` and `LowExitPeak`. The two valley clauses are
vacuous whenever the cap in `hStar` binds, which in the down-form corpus is 99.97 % of
basepoints. This batch proves the vacuity, proves two structural facts about the remaining
case, and restates `HighExitValley` restricted to it. It proves nothing about the restricted
conjecture itself.

Evidence for the restricted form, down-form corpus, all lengths 9–12 on six levels and
selected wider and longer runs: 452 + 84 arm-instances exhaustively and 765 more from random
sequences to length 60 on twelve levels, no failure. The shapes that occur, as
`(hStar − p, H − 1 − hStar, L − (p − 2))`: `(0,1,0)` overwhelmingly, then `(0,1,−1)`, `(0,2,0)`,
`(1,1,0)`. In the first shape the visit is forced by the Lipschitz property alone; the other
three need crookedness.

## Protocol

As batches 1–16. Expected: `ValleyBefore`, `HighExitValley`, `hStar`, `hStarArm`,
`hStarArm_mem`, `le_hStarArm`, `phase`, `armG`, `armT`, `IsLip`, `IsCrookedSeq`.

## 1. Vacuity

**valleyBefore_of_cap.** Unfold `ValleyBefore`: the hypothesis `h + 1 < A u` together with
`A u ≤ H ≤ h + 1` is a contradiction, so the conclusion holds for every `u`.

## 2. Structure of the non-vacuous case

**exists_drop_before_exceed.** `A u > h + 1 > hStarArm A p`. If every `j ≤ u` had
`p − 1 ≤ A j`, then `u` would lie in the set whose supremum is `hStarArm A p`, giving
`A u ≤ hStarArm A p`; so some `j ≤ u` has `A j ≤ p − 2`. Let `d` be the least such. Then `d ≤ u`,
and `d ≠ u` because `A u > h + 1 ≥ p − 1 > p − 2`; every `j < d` has `p − 1 ≤ A j` by
minimality.

**pre_drop_eq.** `A d' ≥ p − 1` by `hpre`, and `A d' ≤ A d + 1 ≤ p − 1` by `IsLip`.

**demands_lt_of_open.** `hStar = min (max (max hG hT) (max p (L+1))) (max (H−1) p)`. If the
minimum is strictly below its second argument, it equals its first, so
`max (max hG hT) (max p (L+1)) < max (H − 1) p`. Since `p ≤ ` that first argument, `p < max (H−1) p`
forces `max (H−1) p = H − 1` and `p < H − 1`; then `hG`, `hT` are each `≤` the first argument
`< H − 1`.

## 3. The restriction

**highExitValley_iff_open.** (⇒) is specialisation. (⇐) Given the hypotheses of
`HighExitValley` at some basepoint: if `hStar < max (H−1) p`, apply the open form; otherwise
`max (H−1) p ≤ hStar`, and since `hStar ≤ max (H−1) p` always, `hStar = max (H−1) p ≥ H − 1`,
so `valleyBefore_of_cap` applies to each arm with `H` the ambient bound.

## 4. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: what was supplied; any statement that did not go through.

## 5. Not in this batch

`HighExitValleyOpen`; the reflected shrinking of `LowExitPeak` (same three statements under
negation — deferred until the open form is worth attacking); `ExitReach`; Bing 1948 Theorems 4,
5, 6; the reduction in Bing 1951; the D8/D9 gap.
