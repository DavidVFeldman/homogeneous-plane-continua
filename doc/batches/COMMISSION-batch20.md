# Commission: batch 20 — the interval model, and the reinstatement of the batch-16 route

**Go!** Runs on top of the batch-19 delivery. One new file, `HPC/Fold/Interval.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

The sequence model was too weak. `IsCrookedSeq ρ` was proved (batch 7) to hold for the
minimal-index sequence of any chain crooked in the 1948 sense, and every statement from batch
9 on was quantified over it. But it is only necessary. **Neither the batch-15 witness
`1,2,3,2,3,4,3,4,5` nor the batch-19 witness `5,4,3,3,2,3,2,1,2,3,2,1,1,0` is the minimal-index
sequence of any crooked chain**: exhaustive search over every way of letting each link
straddle two adjacent coarse links — 2⁹ and 2¹⁴ patterns — finds none crooked, in the model
that makes crookedness easiest to satisfy. So the refutations of `Agreement`, `MixedGap`,
`F2Prime`, `F2PrimeTight`, `F2PrimeFree` and the three tight conjectures are refutations of
sequence statements by non-chains. They stand as theorems; they say nothing about chains.

Over the faithful model, the batch-16 route is unbroken. On all 19 210 975 basepoints of
genuinely crooked interval chains of length ≤ 8 on five and six levels, and 65 878 more from
random crooked interval chains to length 30 on nine levels: `ExitReach`, `HighExitValley`,
`LowExitPeak`, and `F2Prime` with the `hStar`/`lStar` witness — **no failure**. `Agreement` and
`MixedGap` fail there too (144 instances), so those were genuinely false; the refutations were
right about them and wrong about nothing else.

This batch does four things, all with proofs: defines the model; shows a crooked chain lands in
it; shows the two witnesses do not; and restates the batch-16 route over it, reproving the
assembly and `theorem3` by the existing proofs.

## Protocol

As batches 1–17: complete proofs supplied, no search needed except where §3 says. The two
non-realizability theorems are finite but large; §3 gives the decision tree so that they need
not be brute-forced.

## 1. The model

`IsCrookedIv ρ σ`: `ρ t ≤ σ t ≤ ρ t + 1`; consecutive intervals within distance one; and for
`s < t` and any `h ∈ [ρ s, σ s]`, `k ∈ [ρ t, σ t]` at distance ≥ 3, witnesses `s < r < r' < t`
with the coarse index adjacent to `k` on the side of `h` inside `[ρ r, σ r]` and the index
adjacent to `h` on the side of `k` inside `[ρ r', σ r']`.

This is `IsCrookedIn'` transported literally: a link *lies in* coarse index `j` iff
`j ∈ [minIdx, maxIdx]`, and the hypothesis "meets" is read as "lies in". Real chains may meet
coarse links they do not lie in, which only *adds* hypotheses; so any statement true for all
`IsCrookedIv` sequences is true for all chains, and a sequence with no `σ` making it
`IsCrookedIv` is the minimal-index sequence of no chain.

## 2. The chain lands in the model

**isCrookedIv_minIdx_maxIdx.** `le`: `minIdx_subset` and `le_maxIdx`. `width`:
`subset_adjacent_of_subset` applied to the two containing links. `adj`: `minIdx_lip` and
`maxIdx_lip` (batch 4) give each inequality. `crooked`: let `s < t`, `h ∈ [minIdx s, maxIdx s]`,
`k ∈ [minIdx t, maxIdx t]`, `|h − k| ≥ 3`. Then `E.link s ⊆ D.link h` — every index between
`minIdx` and `maxIdx` contains the link, since a link inside two coarse links is inside every
one between, and here there is at most one between — so `E.link s` meets `D.link h`, and
likewise `E.link t` meets `D.link k`. `IsCrookedIn'` at `(h, k)` gives `r, r'` with
`E.link r ⊆ D.link (k ∓ 1)`, so `k ∓ 1 ∈ [minIdx r, maxIdx r]` by `minIdx_le` and `le_maxIdx`;
same for `r'`. `Between` gives the order. *(supply: the "every index between contains the
link" step; with width ≤ 1 there is no index strictly between, so it is `minIdx_subset` or
`maxIdx_subset` by cases.)*

**IsCrookedIv.isCrookedSeq.** Take `h := ρ s`, `k := ρ t` in `crooked`; the conclusions
`ρ r ≤ k ∓ 1 ≤ σ r ≤ ρ r + 1` give `ρ r ∈ [k ∓ 1 − 1, k ∓ 1]`, which is the down-form window.

## 3. The witnesses are not chains

**badSeq_not_realizable.** `badSeq = 1,2,3,2,3,4,3,4,5`. For any `σ`, `width` forces
`σ t ∈ {ρ t, ρ t + 1}`. Take the pair `s = 0, t = 8`, `h = 1`, `k = 5`, ascending: need `r` with
`4 ∈ [ρ r, σ r]` — so `r ∈ {5, 7}` (`ρ = 4`) or `r ∈ {2, 4, 6}` with `σ r = 4` — and then `r'`
after `r`, before `8`, with `2 ∈ [ρ r', σ r']` — so `ρ r' ∈ {1, 2}`, i.e. `r' ∈ {1, 3}`. But
`r < r'` forces `r ≤ 2`, so `r = 2` with `σ 2 = 4`, `r' = 3`. That handles this pair. Now take
`s = 3, t = 8`, `h = 2`, `k = 5`: need `r ∈ (3, 8)` with `4 ∈ [ρ r, σ r]` — `r ∈ {5, 7}` or
`r ∈ {4, 6}` with `σ = 4` — then `r' ∈ (r, 8)` with `3 ∈ [ρ r', σ r']`, i.e. `ρ r' ∈ {2, 3}`:
`r' ∈ {4, 6}`. `r < r'` gives `r = 4, r' = 6` (needs `σ 4 = 4`) or `r = 5, r' = 6`. Fine. Now
`h = 2, k = 5` at `s = 1, t = 8` similarly. *(supply: the full tree. It is shallow — at most
five pairs decide every pattern — and `decide` on the finite quantification over
`σ ∈ ∏ {ρ t, ρ t + 1}` is an alternative if the kernel can take 512 cases of the crookedness
check. Report which route.)*

**fpSeq_not_realizable.** `fpSeq = 5,4,3,3,2,3,2,1,2,3,2,1,1,0`. The pair `s = 0, t = 4`, `h = 5`,
`k = 2`, descending: need `r ∈ (0,4)` with `3 ∈ [ρ r, σ r]` — `r ∈ {2, 3}` — then `r' ∈ (r, 4)`
with `4 ∈ [ρ r', σ r']` — `r' = 3` with `σ 3 = 4`. So `σ 3 = 4` and `r = 2`. If `σ 0 = 6`, the
pair `s = 0, t = 2`, `h = 6`, `k = 3` needs `r = 1` with `4 ∈ [4, σ 1]` and then `r' ∈ (1, 2)`,
empty: so `σ 0 = 5`. Then the pairs `(0, 7)`, `(0, 13)` and `(5, 7)` dispose of the rest; the
distribution of first-failing pairs over all 16 384 patterns is `(0,2): 8192`, `(0,4): 4096`,
`(0,7): 2048`, `(0,13): 1024`, `(5,7): 1024`, which is exactly a five-level decision tree on
`σ 0, σ 3, …`. *(supply: the tree; or `decide` if 16 384 cases are tractable, which is
doubtful.)*

## 4. The route over the model

The four `…Iv` definitions are the batch-16/18 statements with `IsCrookedSeq ρ` replaced by
`IsCrookedIv ρ σ` and `σ` added to the quantifier prefix; attainment kept from batch 18.

**f2PrimeIv_of_exitReachIv.** Batch 16's `f2Prime_of_exitReach` (with batch-18's third
hypothesis) uses its crookedness hypothesis only to pass it to `h1`, `h2`, `h3`. Copy that
proof; where it passes `IsCrookedSeq ρ`, pass `IsCrookedIv ρ σ`. *(supply: confirm no lemma in
the chain consumes `IsCrookedSeq` directly; if one does, derive it via
`IsCrookedIv.isCrookedSeq`.)*

**theorem3_of_F2PrimeIv.** Batch 9's `theorem3_of_F2Prime` with `isCrookedSeq_minIdx` replaced
by `isCrookedIv_minIdx_maxIdx`, supplying `σ := maxIdx`.

## 5. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: which route the two non-realizability proofs took; whether the batch-16 assembly
   copied over cleanly; what was supplied; any statement that did not go through.

## 6. Not in this batch

`ExitReachIv`, `HighExitValleyIv`, `LowExitPeakIv` — the three conjectures, now over the right
model. They are the next batch, under the relaxed protocol, once this one has landed.
