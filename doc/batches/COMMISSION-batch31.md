# Commission: batch 31 — the interior case of `S3ZigFree`

**Go!** Runs on top of the batch-30 delivery. One new file, `HPC/Fold/Interior.lean`; root
`HPC.lean` updated. Nothing else touched.

## 0. On batch 30

Audited clean: thirty-eight earlier files identical, no forbidden tokens, all four ordinary
items as stated, and `Minimality` **proved**. With `bingPath_length` from batch 24 the bound is
attained, so **Bing 1948 Theorem 7 is now machine-checked in the faithful sequence model,
construction and minimality together.** It is the first of Bing's numbered theorems added to
the verified list in a long while, and it stands whatever happens to the folding programme.

The change that made the induction close is the one worth recording: **measure the gap with the
intervals, not with `ρ`.** In terms of `ρ` alone the first of the three stretches reaches only
`l + d − 2`; in terms of `[ρ u, σ u]` it reaches `l + d − 1`, and then the three stretches
overlap in exactly two links and the recurrence `2z(d−1) + z(d−2) − 2` falls out term for term,
with the `− 2` being the two shared junctions. Batches 20–22 fought to get the interval model
right for reasons of faithfulness; this is the first place its extra content has been used to
prove something, and it is the reason the classical theorem went through.

Three by-products worth noting: `IsCrookedIvF.isLip` — the model forces the Lipschitz condition,
so the many statements carrying `IsLip` as a hypothesis do not need it; `isCrookedIvF_restrict`,
which several censuses had assumed silently since batch 16; and the unconditional forms
`index_gap_of_level_gap'` and `timing_slack'`.

## 1. What is left

`s3ZigFree_of_interior` (batch 29) reduces `S3ZigFree` to interior basepoints,
`L + 3 ≤ ρ i ≤ H − 3`. That is `S3ZigFreeInterior`, and it is the only open statement between
the repository and Bing 1948 Theorem 3 in the block reading.

Evidence: no failure at any basepoint of `bing 0 4` through `bing 0 12`, on 4 000 random and
8 025 grid subchains of `bing 0 12` of span at least nine (batch 29 §1), or on the independent
runs of batches 28–29.

## 2. Ordinary items

**arm_timing, both_arms_timing.** From `timing_slack'` applied to the stretch between `i` and
the index where the arm reaches the extreme, through `isCrookedIvF_restrict`. At an interior
basepoint `ρ i` differs from each extreme by at least three, so `index_gap_of_level_gap'` at that
pair gives `z 3 − 1 = 5` indices, and in particular the `2` of `both_arms_timing`. *(supply: the
arm-index versus sequence-index arithmetic, which `armG`/`armT` make slightly fiddly. State
whatever stronger bound falls out — `z (H − L) − 1` is available and `2` is all the conclusion
asks for.)*

## 3. `s3ZigFreeInterior` — the search item

Search permitted, as batches 18–30. **A counterexample is a success; report it first**, with the
basepoint and the faithful check.

What is new since the last attempt is the timing bound, and the shape of the argument it
suggests is a *greedy* one rather than an induction on the cut:

> Build the walk and the two folds together, one time at a time. Keep the token at each arm's
> own level, clamped into the band, as `foldsOnto_ladderUp` does for the near-extreme case. That
> fold fails only when an arm demands the token be near `L` and near `H` at times too close
> together — which is exactly `no_zigWalk_fold_veeSeq` — and `timing_slack'` says a faithful
> crooked sequence never demands that.

If that closes, it closes without the cut, without `LexCutExists` and without an induction on
the span, and the reversal law is then a consequence rather than a constraint: the walk's turns
are the arms' reversals, and the arms have `⌊span/2⌋ − 1` of them because the levels force it.
**Check that consequence against the census before believing the proof** — a greedy argument
that produced a walk with the wrong number of turns would be wrong somewhere.

Two things the greedy shape must handle, both visible in the data:

* the two arms want the token in different places at the same time. The near-extreme proof has
  only one arm to satisfy at a time, since the other is trapped against the band; in the
  interior both are free. This is where the ten refuted families died, in the form "a shape
  chosen for one arm is a shape imposed on the other".
* the walk must end at `L + 1` and `H − 1` in some order (`IsZigFree.ends`), which is a global
  condition a greedy construction does not obviously meet. `isZigFree_cons` lets a finished walk
  be prefixed, so building backwards from the required ending is available and may be the better
  direction.

If the greedy route fails, the cut route of batch 29 §3 remains, now with `timing_slack'` for
the outer pieces. Report which was attempted and where it stopped.

## 4. Deliverables

1. Census — including, if `s3ZigFreeInterior` is proved, the check that the constructed walk's
   turn count matches the reversal law.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report, in this order: any counterexample; whether `s3ZigFreeInterior` was proved and by
   which route; what was supplied.

## 5. Not in this batch

The linear-time far-index check that would make `¬ F2PrimeOff` unconditional; Bing 1948
Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9 gap.
