# Commission: batch 16 — `ExitReach`, the corrected dichotomy

**Go!** Runs on top of the batch-15 delivery. One new file, `HPC/Fold/ExitReach.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

`Agreement` is refuted (batch 15). The diagnosis: it compared the two arms' raw demands, while
`hStar` is *capped* at `max (H − 1) p`, so a large demand on one arm does not raise the bar for
the other. In the refuting sequence the demands are `5` and `3` while `hStar` is `4`, and both
arms clear it comfortably.

`ExitReach` is the corrected statement, in terms of first exits and phase-adjusted reach, with
`SegLam` eliminated. This batch states it, proves the branch of it that is elementary, and
derives `F2Prime` from it together with `HighExitValley`.

**On the evidence.** Every corpus cited before batch 15 was filtered with the exact-level
crookedness model and is worthless for the weak forms. The figures below were gathered afresh
under the **down** form, `IsCrookedSeq`, which is what `minIdx` satisfies and what `F2Prime` is
stated over: 1 932 166 basepoints over all down-crooked sequences of lengths 9–12 on six levels
and length 11 on seven. `ExitReach`: no failure. `F2Prime` itself with the `hStar`/`lStar`
witness: no failure. And in every instance `ExitReach` implied the folding condition for both
arms outright, which is the empirical content of §4 below.

## Protocol

As batches 1–15. Expected: `phase`, `phase_zero_or_one`, `hStarArm`, `hStarArm_mem`,
`le_hStarArm`, `hStar`, `lStar`, `SegLam`, `SegVee`, `segLam_of_bounded`,
`segLam_of_peak_before_drop` (batch 10), `HighExitValley`, `ValleyBefore`, `F2Prime`, `armG`,
`armT`.

## 1. Definitions

`DropsBelow A p` is `∃ j, A j ≤ p − 2`. `hReach A p` is the supremum of the phase-adjusted
values `A j + phase A j` over indices whose whole prefix stays at or above `p − 1` — the same
index set as `hStarArm`, with the phase added. `lReach` is the reflection. `OkLam A p h` is
"no drop, or `h ≤ hReach A p`"; `OkVee` is its reflection.

Note `OkLam` is weaker than requiring `h ≤ hStarArm A p`: the phase contributes the spare unit
the Phase Lemma (batch 11) supplies, and the no-drop disjunct covers arms that never leave the
window downward at all — which is exactly what the `Agreement` formulation missed.

## 2. Small lemmas

**hStarArm_le_hReach.** Both suprema are over the same index set, and `phase ≥ 0`
(`phase_zero_or_one`), so each member of `hStarArm`'s set is at most the corresponding member
of `hReach`'s. The set is nonempty (index `0`) and bounded above (by `max A + 1`), so both
suprema exist.

**hReach_mem.** Attainment, as for `hStarArm_mem` in batch 9: a nonempty set of integers
bounded above contains its supremum.

## 3. The no-drop branch

**le_succ_of_no_drop.** Suppose `A` never drops, so `p − 1 ≤ A j` for every `j` and the index
set defining `hStarArm` is everything; hence `A j ≤ hStarArm A p` for every `j` (this is batch
10's `le_hStarArm_of_no_drop`). Two cases on `hdem`. If `hStarArm A p ≤ h`, then
`A j ≤ h ≤ h + 1`. If `H − 1 ≤ h`, then `A j ≤ H ≤ h + 1`. Either way the window holds.

The disjunction `hdem` is exactly what `hStar` delivers: it is the max of the demands, floored
and then capped at `max (H − 1) p`. If the cap does not bind, `hStar` is at least this arm's
demand; if it does, `hStar = max (H − 1) p ≥ H − 1`. *(supply: if it is cleaner to take `hStar`
itself as the hypothesis and derive the disjunction inside, do that and record it.)*

**segLam_of_okLam_no_drop.** By `le_succ_of_no_drop` the arm is confined to `[p − 1, h + 1]`;
apply `segLam_of_bounded` (batch 10), whose remaining hypothesis `∀ j, L ≤ A j` is `hLA`.

## 4. The drop branch

**exists_peak_index_of_hReach.** By `hReach_mem` there is `j₀` with
`A j₀ + phase A j₀ = hReach A p ≥ h` and the prefix condition below `j₀`. The set of indices
where the phase-adjusted value reaches `h` is therefore nonempty; let `s` be its least element,
so `s ≤ j₀`. Clause (2) holds at `s`, clause (3) by minimality, and for `j < s ≤ j₀` the prefix
condition gives `p − 1 ≤ A j`.

This is the hypothesis triple of batch 10's `segLam_of_peak_before_drop`, whose remaining
hypothesis is `hvalley` — the per-arm valley condition, which `HighExitValley` supplies at
`hStar`.

## 5. The assembly

**f2Prime_of_exitReach.** Unfold `F2Prime`. Given the hypotheses, apply `h1` to obtain the
disjunction. In the Λ case, for each arm split on `OkLam`: the no-drop disjunct goes through
§3, and the `hReach` disjunct through §4 combined with `h2` and
`segLam_of_peak_before_drop`. The V case is the same with the reflected lemmas — sound here
because `SegVee`, `OkVee` and `lStar` are all *defined* by negation and no crookedness
hypothesis is involved in the conversion (batch 13 on when reflection is legitimate; batch 14
used it the same way).

## 6. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: whether `hdem` was taken as commissioned or derived from `hStar` inside; how the
   reflection in §5 was handled; what was supplied; any statement that did not go through. **If
   `ExitReach` is refuted while formalizing, report that first** — it is a conjecture, and the
   previous one in this position was false.

## 7. Not in this batch

`ExitReach` itself; `HighExitValley`; `SmallDemandCase`; Bing 1948 Theorems 4, 5, 6; the
reduction in Bing 1951; the D8/D9 gap.
