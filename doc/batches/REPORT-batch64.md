# Report: batch 64 — two walks, one case split

Written in the order the commission prescribes: counterexamples first, then §1 (targets), then §2
questions 1–4, then §3 deliverables.

## 0. Counterexamples and refutations

**One refutation, of the corrected statement of the previous batch.** `LandWalkPSuffices`
(`HPC/Fold/LandWalkFail.lean`, batch 63) — the corrected landmark sentence `LandWalkP` implies
folding, for a walk with **no unit leg** — is **false**, and `HPC/Fold/LandWalkFail64.lean` proves
it (`not_landWalkPSuffices`) with an explicit thirteen-time witness.

Take the walk of the turning levels `[3, 1, 4]` from `0`:

```
walkList 0 [3,1,4] :  0  1  2  3  2  1  2  3  4      (nine times)
turn times         :  0        3     5        8
turning levels     :  0        3     1        4
legs               :     3        2       3
```

and the arm `cexArm3 = (-1, 0, 1, 2, 1, 0, -1, 0, 1, 2, 3, 4, 5)`. It is 1-Lipschitz, starts within
one of the walk's first level, every one of its levels is served by the walk, and the walk has no
unit leg (`cex3_isLip`, `cex3_band`, `cex3_noUnitLeg`).

* It **satisfies the corrected sentence** (`landWalkP_cex3`), with the single chain
  `(0, 3, 8, 11)`: the arm's time `0` at the level `-1` for the walk's start, its time `3` at `2`
  for the turning level `3`, its time `8` at `1` for the turning level `1`, and its time `11` at
  `4` for the last turning level. The gaps the walk asks for — three, two, three — are met with
  room to spare, and the trigger at the arm's last level `5`, whose only serving position is the
  walk's time `8`, is answered by the last landmark at the arm's time `11`.
* It **does not fold** (`not_foldsOnto_cex3`). The arm's two times at the level `-1`, its times `0`
  and `6`, are served by the walk's time `0` alone, so the fold stands at the walk's time `0` at
  the arm's time `6`; from there the arm's last level `5`, served only by the walk's time `8`, is
  eight steps away and only six times remain.

**Where the repair still leaks.** The sentence reads every landmark *within one* of the walk's
turning level. That is enough to order the landmarks, and it is necessary for a fold
(`landWalkP_of_foldsOnto`); it is not enough to force the fold to stand *at* the turn. Where a leg
is two steps long, that one level of slack lets the chain be satisfied by an arm that has to repeat
a level the walk passes only once — here the level `1`, which the walk passes at its times `1` and
`5`, and which the chain reads at the arm's time `8` while the fold is pinned to the walk's time
`0`.

**The limit of the refutation.** The search behind it is `probe64.c`, the batch-63 probe restricted
to the walks the statement is about and widened. Over all walks of at most four turns with levels
in `[0, 6]` and all arms of at most **thirteen** times (log `probe64b.log`):

```
                        walks    walks with a counterexample to LandWalkP's sufficiency
  shortest leg  2        1120      64
  shortest leg  3         500       0
  shortest leg  4         184       0
  shortest leg  5          50       0
  shortest leg  6           8       0
```

Every counterexample has a leg of length two; the batch-63 search missed them because its arms had
at most twelve times and its levels at most five (with twelve-time arms and five turns the same
search finds none: `probe64.log`, 2156 walks, 1 718 676 960 arms, no counterexample). So the
statement the measurement leaves standing is `LandWalkP3Suffices` — the same with `NoShortLeg`,
every leg at least three steps long — and it is stated, with `noUnitLeg_of_noShortLeg` and
`landWalkP_iff_foldsOnto_of_suffices3`, in the same file. The four-leg window of
`HPC/Fold/Leg4Land.lean` gives legs `K - P + 1 ≥ 3`, `K - M ≥ 3`, `H - 1 - M ≥ 3` and
`H - 2 - (L + 1) ≥ 3`, so that engine is inside `NoShortLeg` and is untouched by the refutation,
exactly as it was untouched by the batch-63 one.

## 1. The targets

| target | file | state |
| --- | --- | --- |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | still `sorry`; this batch closes the *partner's* side of the crossing down to one clause, closes the crossing in both orientations, and names the residue `CrossMid2L5` |
| `s3_span_nine` | `HPC/Fold/General.lean` | unchanged |
| `s3_general` | `HPC/Fold/General.lean` | unchanged |
| `theorem3` | — | unchanged, waits on `s3_general` |

What moved. Batch 63 reduced the branch, at a crossing in a band that misses the floor, to *the
partner's own `w72`*. This batch shows where that comes from and what is left of it:

* the partner's **ceiling** clause, for `w71` and for `w72` alike, is its own walk's deep-floor
  clause read on the unreflected arm (`land_w71_ceil_of_wb`, `land_w72_ceil_of_wb`);
* its **floor** clause at the descents to `L + 1` is the trichotomy's
  (`land_floor_low1_of_branch`);
* `w71`'s **deep-floor** clause triggers below the band;
* so a `wb` partner owes `w71` exactly one clause — the floor clause at its descents to **exactly**
  `L + 2` — and owes `w72` that clause and its deep-floor clause
  (`leg4Land_w71_of_wb_of_mid2`, `leg4Land_w72_of_wb_of_mid2`,
  `leg4Land_w72_of_wb_of_mid2_of_deep`).

That clause is `Mid2Floor`, and `CrossMid2L5` is the residue of the branch stated with it. Its
index arithmetic is free: `mid2Floor_of_peak_armT` and `mid2Floor_of_peak_armG` derive the clause
from the bare existence of an earlier time at `L + 6` at arm index three or more, because four
levels cost twelve steps.

Two more things a crossing no longer has to be given. `cross_floor_fail_of_not_w8` proves that the
crossing *supplies* the pairing hypothesis batch 63 assumed: an arm of the band all of whose
descents to `L + 2` carry `w8`'s landmark is served by `w8`, so the arm that is not so served has
one descent at which the landmark is missing, and that single descent answers every ascent of the
other arm. And `cross_peak_valley_core_rev`, `cross_peak_valley_armT'`,
`leg4Land_w72_ceil_of_cross_T'`, `leg4Land_w72_of_cross_of_floor_fail_T` are the batch-63 chain with
the two arms exchanged, so the crossing is now closed in **both** orientations: read from the
backward arm's ascent to the forward arm's descent, the crooked pair comes out valley-first, which
is the order the ceiling clause reads on the backward arm.

## 2. The questions

### 2.1 The partner's `w72` off the floor

**The band never misses the floor at a crossing of the corpus.** `census-batch64.c` (log
`census-batch64.log`) measures it: of the 461 stored crossings,

```
crossings with a single w8 side          461
band off the floor (no arm reaches L)      0
some arm reaches L                       461;   the w8 side 179, the partner 282
```

So question 1 is asked about an empty set on this corpus, and the hypothesis `L + 1 ≤ ρ` of
`s3_span_nine_mid5_of_cross_w72` (batch 63) is never met there. Two answers follow.

**First, what the pairing supplies off the floor, it supplies here too, once the deep clause is
written out.** The off-floor hypothesis was used in batch 63 for one thing only: to make `w72`'s
deep-floor clause vacuous. `leg4Land_w72_of_cross_of_floor_fail_deep` and its mirror take that
clause (`Deep72`) as a hypothesis instead, and then the pairing closes the `w8` side's `w72`
wherever the clause holds — which the census puts at 451 of 461 crossings on the `w8` side and 431
on the partner.

**Second, the partner's `w72` is not the pairing's at all: it is its own walk's, but one clause.**
At every crossing of the corpus the partner is served by `wb`:

```
the partner's tag:  wb only 146;  wb and w3 315;  w3 only 0;  neither 0
wb partners with w71's ceiling clause                      461 of 461
wb partners with w72's ceiling clause                      461 of 461
the partner's floor clause at the descents to 1            461 of 461
the partner descends to exactly 2 somewhere                461
Mid2Floor (the floor clause at the descents to exactly 2)  461 of 461
the partner satisfies w71                                  461;  w72  431
```

The two hundred percent figures for the ceiling clauses are `land_w71_ceil_of_wb` and
`land_w72_ceil_of_wb`, which prove them for every `wb` arm whatever; the 461 for `w71` is
`leg4Land_w71_of_wb_of_mid2` together with `Mid2Floor`, which the census finds at all 461. The
thirty crossings at which the partner fails `w72` are its deep-floor clause, exactly as batch 63
reported.

So: in a band with `L + 1 ≤ ρ` the partner's `w72` does *not* follow from the crossing and the
pairing — the crooked pair of the crossing lies on the `w8` side (240 of the 282 crossings where
the search finds it; on the partner at none) — but it does follow from the partner's own `wb`
sentence together with `Mid2Floor`, and off the floor `Mid2Floor` is all of it.

### 2.2 `w71` when an arm reaches `L`

**The partner's half is a theorem; the `w8` side's half is the pairing's, at 288 of the 461.**

* the partner: `leg4Land_w71_of_wb_of_mid2`. A `wb` arm of the band with `Mid2Floor` satisfies
  `w71` in full, with **no** hypothesis on the floor of the band — `w71`'s deep-floor clause
  triggers at `L - 1`. The commission's reading — that the partner owes `w71` "the floor clause at
  descents to exactly `L + 2` and the ceiling clause" — is halved: the ceiling clause is `wb`'s
  own.
* the `w8` side: `leg4Land_w71_of_w8_of_cross_low1` (and its mirror
  `leg4Land_w71_of_w8_of_cross_low1_T`). If at every ascent of the `w8` side to `L + 9` the partner
  has a descent to `L + 1` at which `w8`'s floor clause fails, the pairing's crooked valley sits at
  `L + 2` and `w8`'s own floor landmark at it is the peak, so the `w8` side satisfies `w71` in
  full. The hypothesis is vacuous when the `w8` side never reaches `L + 9`.

Measured:

```
the w8 side reaches 9                                              282 of 461
the hypothesis of leg4Land_w71_of_w8_of_cross_low1                 288 of 461
of those, both arms satisfy w71                                    288
crossings closed by s3_span_nine_mid5_of_cross_low1_wb_armT and
  its mirror (that hypothesis, a wb partner, Mid2Floor)            288
both arms satisfy w71 over the whole corpus                        374 of 461
```

The case does not split by which arm touches `L`: the two orientations are the same argument, and
both are proved (`..._armT` and the mirrored lemmas). It splits by whether the partner's *failing*
descent — the one the crossing hands over — reaches `L + 1` or stops at `L + 2`. Where it stops at
`L + 2` the crooked valley is at `L + 3`, which is `w72`'s valley and not `w71`'s: that is the
batch-62 level gap, unchanged, and it is why the corpus needs both walks (`w71` at 374, `w72` at
421, one or the other at all 461).

### 2.3 Assembly

**With 2.1 and 2.2 the branch at a crossing is a theorem modulo one named statement, and that
statement is the only thing the corpus still owes.** The two-walk form is
`s3_span_nine_mid5_of_cross_wb_two_walks` and its mirror: a crossing whose partner is served by
`wb` and has `Mid2Floor` folds as soon as the `w8` side satisfies `w71`, or satisfies `w72` while
the partner has its deep-floor clause. Measured:

```
the w8 side satisfies w71, or w72 with the partner's deep-floor clause    461 of 461
crossings the two theorems close, given the partner's Mid2Floor           461
```

So on this corpus the list of six of `Leg4SixCrossL5` is a list of **two**, as batch 63 reported,
and the split between them is decided by the partner: `w71` where its failing descent reaches
`L + 1`, `w72` where it stops at `L + 2` and the deep-floor clause holds.

The other assemblies, with the pairing doing the `w8` side's work instead of assuming it:

* `s3_span_nine_mid5_of_cross_low1_wb_armT` — the `w71` route, no hypothesis on the floor: a
  crossing whose `w8` side is the forward arm, whose partner is served by `wb` and has
  `Mid2Floor`, and whose crossing witness descends to `L + 1`, folds. 288 of the corpus's 461.
* `s3_span_nine_mid5_of_cross_wb_armT`, `s3_span_nine_mid5_of_cross_wb_armG` — the `w72` route in
  a band that misses the floor, in both orientations; empty on this corpus.
* `s3_span_nine_mid5_of_cross_wb_deep_armT`, `s3_span_nine_mid5_of_cross_wb_deep_armG` — the same
  with the two deep-floor clauses in place of the off-floor band.
* `s3_span_nine_mid5_offfloor_of_mid2_of_ceil` — and with both clauses assumed on both arms, the
  off-floor branch needs no pairing at all.

`Leg4SixCrossL5` is therefore not yet a theorem, and the sub-case that resists is named:

> **`CrossMid2L5`** (`HPC/Fold/CrossPartner64.lean`). At a basepoint of the branch `L + 5` the arm
> that `w8` does not serve has the floor clause of `w71` at its descents to **exactly** `L + 2`: a
> time at `L + 6` or above, at arm index three or more, four steps or more before the descent.

The census count behind it: **461 of 461**, and non-vacuous at all 461 (every partner of the corpus
does descend to exactly `L + 2`). It is not an arm-only fact — the probe of batch 61 finds arms
served by `wb` alone that fail `w71` — so it is a statement about the pairing, and what the pairing
gives at the descent is the crooked peak, which the census puts on the `w8` side.

The second thing still needed, where the crossing witness stops at `L + 2`, is the `w8` side's own
ceiling clause for `w71` (374 of 461 on the corpus) or its deep-floor clause for `w72` (451 of
461); the disjunction holds at all 461, so with `CrossMid2L5` the whole corpus of crossings is
closed.

### 2.4 `LandWalkPSuffices`

Refuted; see §0. The induction the commission asks for cannot be carried out for that statement.
What this batch supplies in its place:

* the refutation, with its diagnosis — the sentence reads landmarks within one of the turning
  level, and a two-step leg leaves exactly that much room;
* the wider search that pins the hypothesis: no counterexample at any walk whose shortest leg is
  three or more, over all walks of at most four turns with levels in `[0, 6]` and arms of at most
  thirteen times, over all walks of at most five turns with levels in `[0, 5]` and arms of at most
  twelve, and — for the walks with no short leg alone — over all walks of at most four turns with
  levels in `[0, 6]` and arms of at most **fourteen** times (`probe64c.log`: 742 walks,
  5 323 443 384 arms, no counterexample);
* the corrected statement `LandWalkP3Suffices`, with `NoShortLeg`;
* and the **base cases of its induction**, proved: `foldsOnto_walk_nil`,
  `foldsOnto_walk_one_turn`, `landWalkP_suffices_of_length_le_one`
  (`HPC/Fold/LandWalkBase64.lean`). At a walk of at most one turn neither the landmark sentence nor
  the hypothesis on the legs is needed: a monotone walk folds every arm it serves, by the clamped
  itinerary `β j = (min (f j - s - 1) (t - s)).toNat` and its reflection. So the whole content of
  the statement is in the inductive step, where the walk turns and the arm must choose a leg.

## 3. Deliverables

**New Lean files, all `sorry`-free, no `native_decide`, no new axiom.**

* `HPC/Fold/CrossPartner64.lean` — `Mid2Floor`, `land_w71_ceil_of_wb`, `land_w72_ceil_of_wb`,
  `leg4Land_w71_of_wb_of_mid2`, `leg4Land_w72_of_wb_of_mid2`, `leg4Land_w71_of_w3_of_mid2`,
  `leg4Land_w72_of_w3_of_mid2`, `Deep72`, `leg4Land_w72_of_wb_of_mid2_of_deep`,
  `cross_floor_fail_of_not_w8`, `land_floor_low1_of_branch`,
  `leg4Land_w71_of_branch_of_mid2_of_ceil`, `leg4Land_w72_of_branch_of_mid2_of_ceil`,
  `cross_peak_valley_core_rev`, `cross_peak_valley_armT'`, `leg4Land_w72_ceil_of_cross_T'`,
  `leg4Land_w72_of_cross_of_floor_fail_T`, `armG_lb`, `armT_lb`,
  `s3_span_nine_mid5_of_cross_wb_armT`, `s3_span_nine_mid5_of_cross_wb_armG`,
  `s3_span_nine_mid5_offfloor_of_mid2_of_ceil`, `armT_sep`, `mid2Floor_of_peak_armT`,
  `mid2Floor_of_peak_armG`, `leg4Land_w71_ceil_of_cross_low1'`,
  `leg4Land_w71_of_w8_of_cross_low1`, `leg4Land_w71_ceil_of_cross_low1_T'`,
  `leg4Land_w71_of_w8_of_cross_low1_T`, `s3_span_nine_mid5_of_cross_low1_wb_armT`,
  `leg4Land_w72_of_cross_of_floor_fail_deep`, `leg4Land_w72_of_cross_of_floor_fail_deep_T`,
  `s3_span_nine_mid5_of_cross_wb_deep_armT`, `s3_span_nine_mid5_of_cross_wb_deep_armG`,
  `s3_span_nine_mid5_of_cross_wb_two_walks`, `s3_span_nine_mid5_of_cross_wb_two_walks_armG`,
  `CrossMid2L5`, `s3_span_nine_mid5_of_crossMid2_of_low1`.
* `HPC/Fold/LandWalkBase64.lean` — `walkLen_one`, `walkList_one_up`, `walkList_one_down`,
  `foldsOnto_walk_nil`, `foldsOnto_walk_one_turn`, `landWalkP_suffices_of_length_le_one`.
* `HPC/Fold/LandWalkFail64.lean` — `cexArm3`, the walk facts of `[3, 1, 4]`, `cex3_noUnitLeg`,
  `cex3_band`, `cex3_isLip`, `cex3_trigger_bound`, `landWalkP_cex3`, `not_foldsOnto_cex3`,
  `not_landWalkPSuffices`, `NoShortLeg`, `noUnitLeg_of_noShortLeg`, `LandWalkP3Suffices`,
  `landWalkP_iff_foldsOnto_of_suffices3`.

All three are imported by `HPC.lean`; `lake build HPC` is clean. The project's `sorry`s are exactly
the four standing targets it had before this batch — `s3_span_nine_mid5` (`Mixed.lean`),
`s3_span_nine` and `s3_general` (`General.lean`) and `theorem3` (`Open.lean`) — and nothing this
batch adds uses any of them. The only edit to an earlier file is one docstring paragraph in
`HPC/Fold/LandWalkFail.lean`, recording that `LandWalkPSuffices` is refuted; the statement itself is
kept as batch 63 delivered it.

```
'HPC.Fold.land_w71_ceil_of_wb' depends on axioms: [propext, Quot.sound]
'HPC.Fold.land_w72_ceil_of_wb' depends on axioms: [propext, Quot.sound]
'HPC.Fold.leg4Land_w71_of_wb_of_mid2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_wb_of_mid2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_wb_of_mid2_of_deep' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w71_of_w3_of_mid2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_w3_of_mid2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_floor_fail_of_not_w8' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_floor_low1_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w71_of_branch_of_mid2_of_ceil' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_branch_of_mid2_of_ceil' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_peak_valley_core_rev' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_peak_valley_armT'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_ceil_of_cross_T'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_cross_of_floor_fail_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_wb_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_wb_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_offfloor_of_mid2_of_ceil' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.armT_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2Floor_of_peak_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.mid2Floor_of_peak_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w71_ceil_of_cross_low1'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w71_of_w8_of_cross_low1' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w71_ceil_of_cross_low1_T'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w71_of_w8_of_cross_low1_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_low1_wb_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_cross_of_floor_fail_deep' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_cross_of_floor_fail_deep_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_wb_deep_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_wb_deep_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_wb_two_walks' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_wb_two_walks_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_crossMid2_of_low1' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.walkList_one_up' depends on axioms: [propext, Quot.sound]
'HPC.Fold.walkList_one_down' depends on axioms: [propext, Quot.sound]
'HPC.Fold.foldsOnto_walk_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.foldsOnto_walk_one_turn' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.landWalkP_suffices_of_length_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cex3_noUnitLeg' does not depend on any axioms
'HPC.Fold.cex3_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cex3_isLip' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.landWalkP_cex3' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_foldsOnto_cex3' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_landWalkPSuffices' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.noUnitLeg_of_noShortLeg' depends on axioms: [propext, Quot.sound]
'HPC.Fold.landWalkP_iff_foldsOnto_of_suffices3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Censuses over the general model, under the audit protocol.** `census-batch64.c` (log
`census-batch64.log`, run as `census-batch64 40 62 200 12`) is the batch-63 census with a batch-64
block added: the stored crossings of the trichotomy are read for the two questions above — the
partner's trichotomy tag, the two ceiling clauses on it, its floor clause at the descents to `L + 1`
and at the descents to exactly `L + 2`, its `w71` and `w72`, the `w8` side's, the deep-floor clause
of `w72` on both arms, where the band reaches the floor, and the hypothesis of
`leg4Land_w71_of_w8_of_cross_low1` with the crossings its theorem closes. Every predicate is
evaluated by its own definition — `mid2Floor`, `ceil71Clause`, `ceil72Clause`, `floorLow1Clause` and
`deep72Clause` are the clauses of `Leg4Land` at `(H, K, M, P) = (9, 7, 1, 5)` and `(9, 7, 2, 5)`
with their existentials searched literally, `w8FloorFailsAt` is the negation of `w8`'s floor clause
at one descent, `landLeg4` is the sentence clause by clause — and no criterion of the engine is used
anywhere in the block. The block ends with its own audit paragraph, and the run's global definition
audit is unchanged.

`probe64.c` (logs `probe64.log`, `probe64b.log`, `probe64c.log`) is the search of §0. As in batch 63
it is a census
over walks and arms, not over the general model: it enumerates walks by their lists of turning
levels and arms as 1-Lipschitz level sequences, evaluates `walkList`, `walkLen`, `walkStop`,
`walkLevel`, the corrected sentence and `FoldsOnto` by their own definitions, decides the chain by
the backwards greedy (optimal, each landmark taken as late as possible) and folding by reachability
over the walk's positions; the only change from `probe63.c` is the restriction to walks whose
shortest leg is at least a given bound.

The numbers quoted in §0 and §2 are from those two programs and their logs.
