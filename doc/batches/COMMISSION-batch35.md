# Commission: batch 35 — the cut route

**Go!** Runs on top of the batch-34 delivery. One new file, `HPC/Fold/CutRoute.lean`; root
`HPC.lean` updated. Nothing else touched.

## 0. On batch 34

Audited clean: forty-two earlier files identical, no forbidden tokens, the gate run first.

**The gate passed and the gate was wrong, and the batch says so.** `IsTrim` as commissioned asked
for a stretch of span one less; `zigFree_append_forces_inner` proves that such a trim can never
be appended to, since the appended legs' amplitudes force `L < L'` and `H' < H`. So §1's census
measured a property of walks outside the family the conclusion demands — 0 failures at spans 6
through 12 of a vacuous condition. Catching that after running the commissioned census, and
reporting the census honestly before explaining why it does not count, is exactly right.

**With the trim corrected the strong form is false**, 10 of 25 interior basepoints at span six
rising to 2 406 of 13 635 at span twelve, with the witness written out at `bing 0 6` basepoint 5
and the reason proved: the targets of an inner member lie at `L + 2` or above, a fold pins time
zero and moves the token one time per link, so an arm reaching `L` in five links cannot be folded
(`no_fold_of_early_low`, `bing6_arm_not_folded`). Deriving the general lemma from the witness
rather than only exhibiting the witness is the better disposal.

**`s3ZigFreeInterior_of_extendStepZF` is a proved implication with a refuted hypothesis.**
Dropping the existence clause so the induction must supply the inner walk was the right
correction, and noting that `ExtendStepSome` is a restatement of the goal rather than an
induction is the right refusal to overclaim.

**The generalised `isZigFree_append_outer'` is the lasting piece**: any inner band with
`L + 1 ≤ L'`, `H' ≤ H − 1` and `L' + 3 ≤ H'` appends. Batch 33's lemma is its `L' = L+1`,
`H' = H−1` case.

## 1. Why this batch changes route

Twelve formulations of the folding statement have been refuted, and the last two failures were
mine in the same way: a quantifier wrong (batch 27's `Tracking`), then a trim wrong (batch 34's
`IsTrim`). The common shape is that the trim, the family and the step have all been driven by
**levels** — how far the arms go — while the thing that makes a crooked sequence fold is its
**reversals**, and the reversal law says the walk must have about `⌊span/2⌋ − 1` of them.

`crookedIvF_cut_first` (batch 26) produces reversals: between an index at the bottom and a later
one at the top, a faithful crooked sequence comes within one of the top at `r` and then within
one of the bottom at `r'`, and with both crossings taken as early as possible the first two
stretches are banded — `ρ ≤ H − 2` before `r`, and `ρ ≥ L + 2` between `r` and `r'`. **Those
bands are two narrower than the ambient, which is exactly what `isZigFree_append_outer'`
requires and exactly what the trim route could not produce.**

This route has been named and deferred since batch 29 and has never been attempted. It is not
offered as likely; it is offered as the one thing on the list that has not been tried.

Batch 27's obstruction does not apply: it says three pieces of strictly smaller span need not
exist, and here only the first two are claimed, which is what `crookedIvF_cut_first` gives.

## 2. Ordinary items

**exists_cutData.** Repackaging of `crookedIvF_cut_first`. The `bandA` and `bandB` clauses are
the first-crossing minimality already in that lemma; `order` is its index order. *(supply: the
exact form of the batch-26 statement, which may need `a` and `b` chosen as a first bottom index
and a later first top index rather than arbitrary ones. If the repackaging needs a hypothesis the
commission has not written, add it and say so.)*

**cutData_spans.** Immediate from `bandA`, `bandB` and the ambient bounds.

**s3ZigFreeInterior_of_cutWalk.** `CutWalk` is stated with the cut universally quantified, so
this needs `exists_cutData` to produce one: take `a` a bottom index and `b` a top index with
`a < b` — if none exists in that order, reverse, and note that `S3ZigFreeInterior`, `IsZigFree`
and `FoldsOnto` are all invariant under reversing the sequence and the basepoint together, which
is worth a lemma of its own if it is not already available.

## 3. `cutWalk` — the search item

Search permitted. **A counterexample is a success; report it first.**

No mechanism is sketched. Every mechanism sketched for a statement in this position has been
wrong, the last two in ways the census then found, and the useful content of the last three
batches has been the refutations rather than the sketches.

What is available: the cut (`exists_cutData`); `isZigFree_append_outer'` for bands two narrower;
`foldsOnto_prefixLeg` and `isZigFree_cons` for the base end; the one-turn theorems with
`not_oneTurn_of_opposite`; `s3ZigFree_near_extreme` for basepoints within two of an extreme;
`timing_slack'`, `index_gap_of_level_gap'` and `minGap`; `no_fold_of_early_low`, which is the
obstruction any construction must respect; and `isCrookedIvF_restrict`.

What is forbidden by the record: treating the two arms as independent sequences at a common
level (`no_common_walk_pairA_pairB`); any black-box extension hypothesis (batch 27 §4); any
family with a bounded number of turns (the reversal law); and any trim of span one less
(`no_outer_member_of_span_one_trim`).

**If the census suggests `CutWalk` is false, report that and stop** — the batch is then worth
its cost, as batch 28's gate was.

## 4. Deliverables

1. Census — whether a walk built from the cut serves every interior basepoint of `bing 0 n`,
   `n = 6 … 12`, and if a construction suggests itself, at which span it was last checked.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report, in this order: any counterexample; whether the repackaging in §2 needed hypotheses
   the commission omitted; how far `cutWalk` got.

## 5. Not in this batch

The linear-time far-index check for `¬ F2PrimeOff`; Bing 1948 Theorems 4, 5, 6; the reduction in
Bing 1951; the D8/D9 gap.
