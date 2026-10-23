# Report: batch 32 — the choice rule, gated on a census

One new file, `HPC/Fold/Choice.lean`; the root `HPC.lean` updated with its import; `README.md`
notes the batch. Nothing else was touched. The whole project builds. The new file has no
`sorry`, `admit`, `axiom`, `native_decide` or `@[implemented_by]` outside the commented block at
its end, no new linter warnings (the four `unused variable` warnings in `HPC/Fold/Itinerary.lean`
and `HPC/Fold/Bump.lean` are the pre-existing ones of earlier batches, left untouched), and every
theorem in it has axiom profile inside `propext`, `Classical.choice`, `Quot.sound`.

The census program is `census-batch32.c`, its output `census-batch32.log`.

## 0. No counterexample to `s3ZigFreeInterior`

None was found, and none is claimed. `s3ZigFreeInterior` is neither proved nor refuted; it is
kept, commented out, at the end of `HPC/Fold/Choice.lean`, together with `s3ZigFree` and `s3`,
and nothing in the file depends on it. What the batch adds towards it is a negative structural
fact (§3 below) that removes a whole class of candidate constructions.

## 1. The gate: the census of covers

Conventions are those of batches 28–31. A walk of the free family is a base centre `ts[0]`
followed by turning targets in `[L+1, H−1]`, directions alternating, amplitudes strictly
increasing from the second on, the last two targets `(L+1, H−1)` or `(H−1, L+1)`; the walk moves
one level per step; `FoldsOnto` of both arms of a basepoint is decided exactly by bitmask
reachability, one `O(n)` sweep per walk resolving every basepoint at once. The whole family of a
band is enumerated: 40, 96, 224, 512, 1 152, 2 560, 5 632 walks at spans 6 … 12.

### Cover sizes, `bing 0 n`, all basepoints

| span | links | walks in the family | greedy cover | greedy, interior only | disjoint-set lower bound | exact minimum |
|-----:|------:|--------------------:|-------------:|----------------------:|-------------------------:|--------------:|
| 6 | 71 | 40 | 5 | 2 | 4 | **4** |
| 7 | 170 | 96 | 7 | 3 | 4 | **4** |
| 8 | 409 | 224 | 11 | 7 | 6 | not decided |
| 9 | 986 | 512 | 16 | 11 | 8 | not decided |
| 10 | 2 379 | 1 152 | 21 | 18 | 12 | not decided |
| 11 | 5 742 | 2 560 | 30 | 27 | 14 | not decided |
| 12 | 13 861 | 5 632 | 45 | 41 | 24 | not decided |

The exact minimum is by branch and bound (branching on the uncovered basepoint with the fewest
serving walks) under a budget of 2 000 000 nodes; it finishes at spans 6 and 7 only, and the
entry is reported as undecided elsewhere rather than guessed. The lower bound in the
penultimate column is the size of a greedily chosen set of basepoints whose serving sets are
pairwise disjoint; it is a genuine lower bound and it also grows.

The two numbers the commission reports are reproduced exactly: 7 walks at span 7, 11 at span 8,
with the heaviest covers at span 8

```
[4, 3, 5, 2, 6, 1, 7]   144 of 409
[5, 4, 6, 3, 7, 1]      102 more
[3, 2, 4, 1, 7]          62 more
```

— the same first and third walks and the same three counts as the commission's, the second a tie
with the commission's `[5, 4, 6, 2, 7, 1]`. At span 7 the cover is

```
[3, 4, 2, 5, 1, 6] 72, [4, 5, 3, 6, 1] 48, [2, 3, 1, 6] 26, [6, 1, 6] 14,
[3, 6, 1] 6, [1, 6, 1] 3, [3, 1, 6] 1.
```

**Growth.** 5, 7, 11, 16, 21, 30, 45 greedily, with lower bounds 4, 4, 6, 8, 12, 14, 24. The
cover grows with the span, faster than linearly over this range; no law is fitted to seven
points and none is claimed.

### Is the cover described by a rule?

**No.** Three tabulated rules were checked at every basepoint of `bing 0 6 … bing 0 12`, in each
case allowing the base to be any of the three admissible centres `p−1, p, p+1` (folding permits
no other):

| rule | fails at, span 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|
| backward-read targets `H−1, L+1, H−3, L+2, …` | 9/71 | 40/170 | 216/409 | 544/986 | 1 323/2 379 | 3 757/5 742 | 10 963/13 861 |
| outward alternation from the base, amplitudes `1, 2, 3, …` | 43/71 | 136/170 | 369/409 | 940/986 | 2 327/2 379 | 5 684/5 742 | 13 797/13 861 |
| the whole family of such alternations, first amplitude and direction free | 4/71 | 30/170 | 135/409 | 484/986 | 1 515/2 379 | 4 334/5 742 | 11 671/13 861 |

The third line is the generous reading of the commission's suggestion — not one walk per
basepoint but the whole outward-alternation family, `O(span²)` walks per band — and it still
misses 84 % of the basepoints at span 12. So **no rule is adopted, and none of these three is
stated as a theorem.** This is the outcome the commission flags as worth the run: the
construction must read the arms of the chain and cannot be tabulated in `L`, `H` and the base.

## 2. The ordinary item: `notConstantOnBand`

**It went by neither `decide` nor a reachability certificate.** The census supplies the pair —
already on `bing 0 4`, the basepoints `0` and `5`, at levels `0` and `3`, are served by no
common walk — but the proof that is delivered is uniform and needs no enumeration of the band's
walks at all.

`FoldsOnto` pins time `0` to the basepoint: `abs_sub_base_le_of_folds` (batch 28) gives
`|ρ i − ts[0]| ≤ 1`. Hence

* `no_common_walk_of_level_gap`: if `3 ≤ |ρ i − ρ j|` then no walk whatever — not merely no walk
  of the free family — has both `armG ρ i` and `armG ρ j` folding onto it;
* `no_common_free_walk_of_level_gap`: the same for a member of `IsZigFree L H`, whose list is
  nonempty by its length clause;
* `notConstantOnBand`, the commissioned statement, on the thirty-seven links of `cutSeq`
  (span four, levels `3 … 7`, faithful by `cutSeq_faithful`) at its basepoints `0` and `12`, of
  levels `3` and `7`;
* `notConstantOnBandNonExtreme`, the same statement with both basepoints required to be at
  non-extreme levels, on the 409 links of `ceSeq` (`bingPath 0 8`, faithful by `ceSeq_faithful`)
  at its basepoints `1` and `169`, of levels `1` and `7`.

A remark on "interior". The commissioned `NotConstantOnBand` asks only for two basepoints; its
prose asks for two interior ones. The level-gap obstruction needs the two levels three apart, so
the strongest interiority it can carry is bounded by the span of a chain whose faithfulness the
project has proved — `cutSeq` at span four and `ceSeq` at span eight. At span eight the interior
levels in the sense of `S3ZigFreeInterior` (`L+3 ≤ ρ i ≤ H−3`) are `3, 4, 5`, never three apart,
so the version with both basepoints in *that* range is not reachable by this route and is not
claimed; `notConstantOnBandNonExtreme` is the version that is, with both basepoints strictly
inside the band. The census's pairs are sharper — at span four the basepoints at levels `1` and
`3`, a gap of *two*, already share no walk — but that is a fact about the finitely many walks of
one band, while the level-gap obstruction is uniform in the chain and in the walk.

## 3. What the census turns into a theorem

The growth in §1 is not an accident of the greedy choice:

* `cover_card_ge`: a list of walks serving every basepoint of a family whose levels are pairwise
  three or more apart has at least as many walks as the family has basepoints;
* `exists_level` (with `exists_level_aux`): the discrete intermediate-value property — a
  Lipschitz sequence reaching `L` and `H` has a link at every level between;
* `cover_card_ge_span`: hence **a cover of all the basepoints of a Lipschitz chain that reaches
  both extremes has at least `⌊(H − L)/3⌋ + 1` walks**, for any walks at all, crooked chain or
  not. So no family of bounded size serves every band, and any construction must produce a walk
  that depends on the basepoint;
* `ceSeq_cover_card_ge_three`: the concrete instance, three walks at span eight.

The bound gives 3, 3, 3, 4, 4, 4, 5 at spans 6 … 12 against the measured 5, 7, 11, 16, 21, 30,
45, so it is the part of the growth that the base-pinning obstruction alone forces; the rest is
the reversal law of batches 28–29, which is not formalised here.

## 4. Verdict

The rule that chooses the turning targets is not a table. It is not constant on the band
(`notConstantOnBand`), it cannot be bounded in size (`cover_card_ge_span`), and the three
tabulated shapes that the previous batches suggested each miss most basepoints from span seven
on. Combined with the one-turn theorems of batch 31 and their limit
(`not_oneTurn_of_opposite`), what remains for `s3ZigFreeInterior` is a construction that reads
the two arms and iterates `foldsOnto_prefixLeg` with `isZigFree_cons`, choosing each leg from the
arms' behaviour — or the cut of batch 29 §3.
