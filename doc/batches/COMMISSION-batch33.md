# Commission: batch 33 — the arms cannot be separated, and the outside-in induction

**Go!** Runs on top of the batch-32 delivery. One new file, `HPC/Fold/Pair.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## 0. On batch 32

Audited clean: forty earlier files identical, no forbidden tokens, the gate run first as asked.

**`cover_card_ge_span` is the theorem the batch was for**, and it is stronger than the census
that prompted it: any cover of the basepoints of a Lipschitz chain reaching both extremes needs
at least `⌊(H − L)/3⌋ + 1` walks — for arbitrary walks, crooked chain or not. With
`notConstantOnBand` that closes the tabulation route completely. Proving it from the level-gap
obstruction rather than by enumerating a band's walks is the better proof, and
`no_common_walk_of_level_gap` is the reusable form.

The remark on "interior" is the right kind of care: the level-gap obstruction needs two levels
three apart, at span eight the interior levels are `3, 4, 5`, so the version of
`notConstantOnBand` with both basepoints in that range is not reachable by that route, and it is
not claimed. `notConstantOnBandNonExtreme` is what the route does give, and saying so is better
than stretching the statement.

Reporting the exact minimum cover as undecided at spans 8–12 rather than guessing, and reporting
the disjoint-set lower bound separately, is also right.

## 1. What this batch adds

The construction left standing must read the arms and iterate `foldsOnto_prefixLeg` with
`isZigFree_cons`. The obvious induction hypothesis for that peels a leg off both arms and asks
for the two tails, which are two contiguous stretches of the sequence starting at a common
level. **That hypothesis is false.**

`bing 0 6`, span six. The forward stretch from index 57 and the backward stretch from index 13
both begin at level three:

```
A = 3 2 3 4 3 4 5 4 3 4 5 4 5 6
B = 3 4 3 2 3 2 1 2 3 2 1 2 1 0
```

Each is a contiguous stretch of a faithful crooked sequence, so each is faithful and crooked by
`isCrookedIvF_restrict`; each on its own folds onto a member of the family from every one of the
three admissible centres; and **no member of the family takes both**. Verified by two
implementations with different traversal orders over the whole family of the band. Ten such
pairs exist at span six and every one is built from two *different* basepoints; all sixty-seven
genuine basepoints are served.

`A` rises to `H` and `B` falls to `L`, which is `not_oneTurn_of_opposite` (batch 31) with the
turn count unbounded instead of one. The arms of a real basepoint evidently cannot do this, and
that is a fact about their joining, not about either arm.

## 2. Ordinary items

`pairA_isLip`, `pairB_isLip` by `decide` or `fin_cases`. `not_pairAtLevel` by instantiating
`PairAtLevel` at the two sequences with `σ = ρ`, `L = 0`, `H = 6`, and refuting the conclusion —
the family of the band `[0, 6]` has forty members, so `decide` over it may serve; otherwise the
bitmask reachability certificate of `SpanWitness.lean` (batch 26), which discharges a family
uniformly, is the route. `pairA_served` and `pairB_served` each exhibit one walk: the census
gives `[3, 2, 4, 1, 5]` for `A` and `[3, 4, 2, 5, 1]` for `B`. *(supply: the faithfulness of the
two stretches, either by the far-index method at these lengths — `14 × 7 × 7`, trivial — or by
`isCrookedIvF_restrict` from `bing 0 6`, whose faithfulness the project has at span six only if
it has been proved; if not, prove the two directly.)*

Report which route each took.

## 3. The induction this points to — sketch, untested

Peeling a leg from the *inside* separates the arms and loses their joining, which §1 shows is
fatal. Peel from the **outside** instead.

Let `ρ` be faithful crooked on `[L, H]` with an interior basepoint `i`. Let `[a, b]` be the
maximal contiguous stretch containing `i` whose span is at most `H − L − 1`. It contains `i`
properly, it is faithful and crooked (`isCrookedIvF_restrict`), its own extremes are attained,
and `i` is still a basepoint of it. The induction hypothesis, on span, gives a walk for that
stretch on its own band. Then **append** the outer legs: the parts of `ρ` beyond `a` and beyond
`b` are what must fold onto them.

This keeps the sequence single at every stage, so the joining is never lost, and it explains the
measured shape: the appended legs are longer than the ones before them, which is the increasing
amplitude, and the last of them reach `L + 1` and `H − 1`, which is `IsZigFree.ends`.

What it needs that the repository does not have is the **dual of `isZigFree_cons` and
`foldsOnto_prefixLeg`: appending a leg at the far end rather than prefixing one at the base.**
`IsZigFree` is stated with the ends pinned, so appending changes the `ends` clause and the last
amplitude comparison; the natural form is a lemma taking a member of `IsZigFree L' H'` for an
inner band and a pair of legs, and returning a member of `IsZigFree L H`. That lemma is the
first thing to try, and it is independent of whether the induction closes.

**This sketch is untested.** It was not censused here, and the trimming has not been checked to
behave at basepoints near the edge of the inner band. Test it before building on it, as batch 28
was gated; report if the trimming degenerates.

The cut route of batch 29 §3 remains the alternative and has still never been attempted.

## 4. Deliverables

1. Census — in particular whether the outside-in trimming of §3 is well behaved: how the span
   and the basepoint's position in the inner band move at each step, over `bing 0 6` … `bing 0 12`.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report: any counterexample to `s3ZigFreeInterior`; which route the §2 items took; the §3
   census and whether the append lemma went through.

## 5. Not in this batch

`s3ZigFreeInterior`; the linear-time far-index check for `¬ F2PrimeOff`; Bing 1948 Theorems 4,
5, 6; the reduction in Bing 1951; the D8/D9 gap.
