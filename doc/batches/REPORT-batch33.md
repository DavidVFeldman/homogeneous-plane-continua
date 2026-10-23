# Report: batch 33 — the arms cannot be separated, and the outside-in trimming

One new file, `HPC/Fold/Pair.lean`; the root `HPC.lean` updated with its import; `README.md`
notes the batch. Nothing else was touched. The whole project builds. The new file has no
`sorry`, `admit`, `axiom`, `native_decide` or `@[implemented_by]`, adds no linter warnings (the
four `unused variable` warnings in `HPC/Fold/Itinerary.lean` and `HPC/Fold/Bump.lean` are the
pre-existing ones of earlier batches, left untouched), and every theorem in it has axiom profile
inside `propext`, `Classical.choice`, `Quot.sound`.

The census program is `census-batch33.c`, its output `census-batch33.log`.

## 0. No counterexample to `s3ZigFreeInterior`

None was found here, and none is claimed. Nothing in this batch bears on it either way except
negatively, through §1: the pair hypothesis that the natural inside-out induction would use is
false, so that route is closed. `s3ZigFreeInterior` remains commented out at the end of
`HPC/Fold/Choice.lean`, where batch 32 left it; this batch does not touch that file.

## 1. The pair, and what refutes it

The data of COMMISSION-batch33 §1 is confirmed exactly. `bing 0 6` has 71 links; its forward
stretch from index 57 and its backward stretch from index 13 are

```
A = 3 2 3 4 3 4 5 4 3 4 5 4 5 6
B = 3 4 3 2 3 2 1 2 3 2 1 2 1 0
```

and `B = 6 − A` pointwise — the pair is a sequence and its own reflection. The free family of
the band `[0, 6]` has **40 members**; **12 serve `A`**, **12 serve `B`**, **none serves both**.
Folding is decided exactly, and twice: once by a forward reachability sweep over the walk's
times and once by a backward one, with the two agreeing on all 40 members. The full table of the
40 members with what each serves is in `census-batch33.log`.

The commission names `[3, 2, 4, 1, 5]` for `A` and `[3, 4, 2, 5, 1]` for `B`. Those two walks
are in the family and each does serve one of the stretches, but the other way round:
`[3, 2, 4, 1, 5]` serves `B` and `[3, 4, 2, 5, 1]` serves `A`. The shortest witnesses are
`[3, 5, 1]` for `A` and `[3, 1, 5]` for `B`, and those are the two the Lean file exhibits.

### What is proved, and it is more than was asked

`not_pairAtLevel` is proved **without enumerating the family**, and what carries it is stronger
than the enumeration would give: `no_common_walk_pairA_pairB` says that **no walk whatever**
takes both stretches — not merely no member of `IsZigFree 0 6`, but no `zigWalk` of any list at
all. The only property of the walk used is that it moves one level per step (`zigWalk_step`).

The engine is `no_common_walk_of_opposite_arms`, stated for an arbitrary unit-step centre
sequence and an arbitrary base level `b`:

* `f` starts at `b`, is at `b − 1` at index one, and is never `≤ b − 1` anywhere else;
* `g` is at `b + 1` at index one and is never `≥ b + 1` anywhere else;
* `f` reaches `b + 3` somewhere and `g` reaches `b − 3` somewhere.

Then no walk takes both. The argument: a fold pins the token to time `0` at index `0` and moves
it by at most one time per link, so the set of times it occupies is an initial contiguous
stretch (`exists_index_of_time`). `f`'s token ends at a time whose centre is `≥ b + 2`, `g`'s at
a time whose centre is `≤ b − 2`. Whichever of those two times is the earlier, the *other* arm's
token must have stood at it; but only index one of that arm is far enough from the base to be
within one of such a centre, and index one is at time `≤ 1`. That forces time `1` — hence the
walk's centres at times `0` and `1` both lie on one side of the base — and then the other arm's
value at index one, which lies on the far side, is out of reach at both of those times.

This is `not_oneTurn_of_opposite` (batch 31) with the turn count unbounded, as the commission
predicted, and it needs no case analysis over itineraries.

### The §2 items, and which route each took

* `pairA_isLip`, `pairB_isLip`: `decide +kernel` after unfolding `IsLip`, as batch 28 did for
  `cutSeq`.
* **Faithfulness**: proved **directly**, not through `isCrookedIvF_restrict`. The project does
  not have the faithfulness of `bing 0 6`, and at length 14 the decidable criterion of batch 22
  (`isCrookedIvF_of_check` with `σ = ρ`) goes through by `decide +kernel` in seconds, once
  `synthInstance.maxSize` is raised so the instance for the nested criterion is found. So
  `pairA_faithful` and `pairB_faithful` are self-contained, and the bitmask certificate of
  `SpanWitness.lean` was not needed either.
* `not_pairAtLevel`: by instantiating `PairAtLevel` at the two stretches with `σ = ρ`, `L = 0`,
  `H = 6`, and refuting the conclusion by `no_common_walk_pairA_pairB`. Neither of the two
  routes the commission offered (`decide` over the family, or the reachability certificate) was
  used; the structural obstruction replaces both.
* `pairA_served`, `pairB_served`: one explicit walk each (`[3, 5, 1]` and `[3, 1, 5]`), with the
  time assignment written out and the four clauses of `FoldsOnto` discharged by `decide`; the
  walk's levels are computed by `simp [zigLevels, zigTail, stepRun]`.

### All the pairs at span six

Over all 142 arms of `bing 0 6` (forward and backward from each of the 71 indices), every arm is
served by some member of the family, and every one of the 71 basepoints is served by a member
taking *both* of its arms. Among pairs of arms that start at a common level and are each served,
exactly **10** are served by no common member; all 10 are still distinct when counted as pairs of
sequences rather than pairs of (index, direction); and **every one of the 10 is built from two
different basepoints** — none is the two arms of a single basepoint, as it must be, since all 71
basepoints are served. The ten pairs are all at level 3, and they are

```
backward from 5, 9, 11 against forward from 59, 61, 65, and backward from 13 against forward from 57.
```

The commission's count of ten is reproduced exactly. (It speaks of "sixty-seven genuine
basepoints"; the census serves all 71 indices of `bing 0 6` as basepoints, so no exclusion was
needed to make the statement true.)

## 2. The outside-in trimming (§3), censused

For each basepoint `i` of `bing 0 n`, `n = 6 … 12`, the trimming takes the maximal contiguous
stretch containing `i` whose span is at most one less than the current one, and iterates until
the span is at most 3. Measured per span, over every basepoint:

| span | links | steps to span 3 | span ever stalls | basepoint ends at a stretch endpoint | basepoint at an extreme level of an inner band | steps where the two greedy orders differ |
|-----:|------:|----------------:|:----------------:|-------------------------------------:|-----------------------------------------------:|-----------------------------------------:|
| 6 | 71 | 3 | no | 7 of 71 | 23 of 71 | 130 |
| 7 | 170 | 4 | no | 14 of 170 | 54 of 170 | 398 |
| 8 | 409 | 5 | no | 31 of 409 | 129 of 409 | 1 165 |
| 9 | 986 | 6 | no | 72 of 986 | 310 of 986 | 3 305 |
| 10 | 2 379 | 7 | no | 171 of 2 379 | 747 of 2 379 | 9 168 |
| 11 | 5 742 | 8 | no | 410 of 5 742 | 1 802 of 5 742 | 25 004 |
| 12 | 13 861 | 9 | no | 987 of 13 861 | 4 349 of 13 861 | 67 295 |

A full trace, `bing 0 8` at basepoint 57:

```
step 0: stretch [0,408] band [0,8] span 8, level 3
step 1: stretch [0,407] (408 links) band [0,7] span 7, level 3
step 2: stretch [0,168] (169 links) band [0,6] span 6, level 3
step 3: stretch [0, 69] ( 70 links) band [0,5] span 5, level 3
step 4: stretch [1, 69] ( 69 links) band [1,5] span 4, level 3
step 5: stretch [42,69] ( 28 links) band [2,5] span 3, level 3
```

**Three things the census says.**

1. **The span is well behaved.** It drops by exactly one at every step and never stalls, at
   every basepoint of every chain tested, so the induction on span has the descent it needs and
   the number of steps is exactly `span − 3`.
2. **The maximal stretch is not unique**, and this is the real defect of the sketch as stated.
   Expanding left first and expanding right first give different stretches at a large fraction
   of the steps (the last column), so "the maximal contiguous stretch containing `i` whose span
   is at most `H − L − 1`" does not denote; the induction has to *choose*, and which choice is
   right is exactly the question the batch is trying to answer. This is the trimming degenerating
   in the sense the commission asked to be reported.
3. **The basepoint does not stay interior.** At about 30 % of the basepoints, some inner band has
   the basepoint at one of its extreme levels, and at about 7 % the basepoint ends up at an
   endpoint of the stretch (one of its arms a single link). Neither is fatal — the first is
   precisely the range batch 29's `s3ZigFree_near_extreme` covers, and the second is a trivial
   arm — but an induction that assumes the basepoint stays interior to the inner band is wrong,
   and it must appeal to the near-extreme case instead.

Not censused, and still untested: whether the two appended outer legs are actually folded onto by
the parts of `ρ` outside the stretch. That is the content of the induction step, and this batch
does not claim it.

## 3. The append lemma went through

`isZigFree_append_outer` is the dual of `isZigFree_cons` the commission asked for, and it is
proved:

```
IsZigFree (L+1) (H-1) ts  →  L + 5 ≤ H  →
  IsZigFree L H (ts ++ [L+1, H-1])  ∨  IsZigFree L H (ts ++ [H-1, L+1])
```

The disjunction is not vagueness: the `ends` clause of `IsZigFree` pins the inner member's last
two targets to `L + 2, H − 2` in one order or the other, and that order decides which pair of
legs is appended. The two constituents, `isZigFree_append_two` and `isZigFree_append_two'`, are
stated with the clauses of the family spelled out so that they can be used for an inner member
that is not itself required to sit in an `IsZigFree` of a band, and the index bookkeeping for
`ts ++ [x, y]` is isolated in `getElem!_append2_left`, `getElem!_append2_fst`,
`getElem!_append2_snd`.

Why it works: the appended legs have amplitudes `H − L − 3` and `H − L − 2`, and every amplitude
inside the inner member is at most `H − L − 4` (its band is `[L+1, H−1]`, so its last leg spans
`L + 2` to `H − 2` and, by the increase condition, it is the largest). So the amplitudes still
increase, the directions still alternate (the inner member's last leg runs towards the end the
first appended leg leaves), and the new last two targets are `L + 1, H − 1` in one order or the
other, which is the `ends` clause of the outer band.

The cut route of batch 29 §3 remains untried.

## 4. What is in the file

| name | statement |
|---|---|
| `pairA`, `pairB` | the two stretches |
| `pairA_isLip`, `pairB_isLip` | 1-Lipschitz |
| `pairA_faithful`, `pairB_faithful` | `IsCrookedIvF` with `σ = ρ`, by the decidable criterion |
| `exists_index_of_time` | a fold occupies every time below one it reaches |
| `no_common_walk_of_opposite_arms` | the general obstruction |
| `no_common_walk_pairA_pairB` | no walk of any shape takes both stretches |
| `PairAtLevel`, `not_pairAtLevel` | the commissioned statement, refuted |
| `pairA_served`, `pairB_served` | each stretch alone is served |
| `getElem!_append2_*` | indexing `ts ++ [x, y]` |
| `isZigFree_append_two`, `isZigFree_append_two'`, `isZigFree_append_outer` | the dual of `isZigFree_cons` |
