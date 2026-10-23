# Report: batch 59 — exact criteria for four legs

Runs on top of the batch-58 delivery. Five files are new — `HPC/Fold/Leg4Land.lean`,
`HPC/Fold/Audit59.lean`, `HPC/Fold/CoverL5Land.lean`, `HPC/Fold/LandLowAt.lean` (all imported at
the end of `HPC.lean`) — together with the census `census-batch59.c` / `census-batch59.log` and
three probes `probe59.c`, `probe59b.c`, `probe59c.c` with their logs. Every earlier Lean file is
unchanged. `lake build HPC` is clean; the only `sorry`s in the project are the pre-existing ones
(`HPC/Fold/Open.lean:47`, `s3_span_nine_mid5` in `Mixed.lean`, and the statements above it that
depend on them). No `native_decide` anywhere; every kernel evaluation is `decide +kernel`.

## 0. Counterexamples, and the definition audit

**No counterexample and no refutation this batch.** Nothing in the corpus refuted a target, a route
statement or a clause of the new criterion; the batch's result is positive (question 1) and the
census found no disagreement in either direction anywhere it looked. This section is therefore
short, but it is first because the commission asks for it first.

The definition audit is printed by the census itself (`census-batch59.log`, section
`---- the definition audit ----`). Every predicate is evaluated by its own definition, none by a
proxy: `IsCrookedIvF`, `IsLip`, `HighAt`, `LowAt`, `Leg3Valley`, `Leg3Ceil`, `Valley5`, `TopW5`,
`FoldsOnto` (the dynamic program of `HPC/Fold/Decide.lean`) for every walk used, the residues, and
— new this batch — `Leg4Land`, the landmark sentence of `HPC/Fold/Leg4Land.lean`, clause by clause,
with the index bounds the walk's own positions dictate, and `Leg4Crit`, the engine's criterion, as
the three announcements of `foldsOnto_leg4W`.

One line of the census deserves a word because it looks like a failure and is not. The carried-over
line

```
the reflection of LowAt is HighAt: fails at 299941 (must be 0)
```

is a **mislabel inherited from batches 57–58** (batch 58 reports 335 317 on the same line). `LowAt f tl th`
(`HPC/Fold/Leaf.lean:35`) has two disjuncts and `HighAt f tl th` (`Leaf.lean:42`) has one, so the
two are not mirror images, and the census reads `highAt` at the thresholds 8/2. The counter is
counting a difference between two predicates that were never claimed to be reflections of one
another. No Lean theorem is contradicted by it, and nothing in this batch depends on it; it is
reported here as a stale label rather than as a finding.

## 1. Targets

| target | status after batch 59 |
| --- | --- |
| `s3_span_nine_mid5` (`Mixed.lean`) | **open**. Reduced further: `s3_span_nine_mid5_of_leg4LandClosesL5` (`CoverL5Land.lean`) derives it from exhaustiveness stated arm by arm in *exact* form; the census finds that form satisfied at every basepoint of the branch in the corpus, with five walks. |
| `s3_span_nine` (`General.lean`) | **open**; it waits on `s3_span_nine_mid5`. |
| `s3_general` | **open**. |
| `theorem3` | **open**; `theorem3_of_S3` still reduces it to `s3_general`. |

What is *proved* this batch, all `sorry`-free:

| theorem | file | content |
| --- | --- | --- |
| `foldsOnto_leg4_iff_leg4Land` | `Leg4Land.lean` | **the exact criterion for a four-leg walk** |
| `leg4Land_of_foldsOnto` | `Leg4Land.lean` | necessity |
| `foldsOnto_leg4_of_leg4Land` | `Leg4Land.lean` | sufficiency |
| `Audit59.serves_4_6_1 … serves_6_8_1`, `pair_folds` | `Audit59.lean` | the nine walks that serve the 175-link arm, and its basepoint |
| `Audit59.land_5_6_1` vs `Audit59.not_crit_5_6_1` | `Audit59.lean` | the exact criterion holds where the engine's criterion fails |
| `s3_span_nine_mid5_of_leg4Land_direct` / `_refl`, `s3_span_nine_mid5_of_leg4LandClosesL5` | `CoverL5Land.lean` | the branch, reduced to exhaustiveness in arm-only exact form |
| `isLip_gap`, `isLip_index_gap(')`, `land_down1_of_lowAt_low`, `leg4Land_walk63718_of_lowAt_low`, `foldsOnto_walk63718_of_land` | `LandLowAt.lean` | the branch hypothesis supplies a whole clause of the exact criterion of the best walk, index bounds included |

## 2. The three questions

### Question 1 — is the landmark sentence exact for a four-leg walk? **Yes.**

`HPC/Fold/Leg4Land.lean` states the sentence and proves both halves.

The walk `leg4Walk L H K M P` runs from `P − 1` up to the peak `K`, down to the valley `M`, up to
`H − 1`, and down to `L + 1`. Its three landmark positions are

```
A = K − P + 1        (level K,     the peak)
B = 2K − P + 1 − M   (level M,     the valley)
C = 2K − P + H − 2M  (level H − 1, the top of the third leg)
```

and a step of the arm at level `v` is served, at the earliest, by walk position `2K − P − v` when
`v ≤ P − 3`, by `2K − P + 2H − 2M − 2 − v` when `v ≤ M − 2`, and by `v + 2K − P − 2M` when
`v ≥ K + 2`. `Leg4Land f H K M P` is the conjunction of the three chains those trigger levels force:

* **floor.** Before every descent to `P − 3` or below, a time at `K − 1` or above, at index at
  least `A` and at least `K − 1 − f d` steps earlier.
* **deep floor.** Before every descent to `M − 2` or below, three times in order at `K − 1` or
  above, `M + 1` or below and `H − 2` or above, the first at index at least `A`, the gaps at least
  `K − M`, `H − 1 − M` and `H − 2 − f d`.
* **ceiling.** Before every ascent to `K + 2` or above, two times in order at `K − 1` or above and
  `M + 1` or below, the first at index at least `A`, the gaps at least `K − M` and `f d − M − 1`.

**`foldsOnto_leg4_iff_leg4Land`**: for a 1-Lipschitz arm of the band `[L, H]` whose first level is
within one of `P − 1`, folding onto `leg4Walk L H K M P` *is* `Leg4Land f H K M P`, at every
parameter set of the wide engine's window (`L + 2 ≤ P ≤ L + 6`, `P ≤ K ≤ H − 1`,
`L + 1 ≤ M ≤ P − 2`, `M + 3 ≤ K`, `H ≤ K + 3`). This is for four legs what
`foldsOnto_leg3deep_iff_landmark` is for three.

Necessity is the itinerary argument of batch 49 (`foldsOnto_landmark1/2/3`; the three-landmark form
`foldsOnto_landmark3` is new here) applied at the positions above, via the position lemmas
`leg4Walk_peak/valley/top` and `leg4Walk_floor_pos/deep_pos/ceil_pos`.

Sufficiency is the greedy of `HPC/Fold/Leg4.lean` run against a new invariant, `gseq4_invLand`,
whose bounds carry the *index* of a landmark as well as its level:

```
(1)                 q j ≥ min (j, u j − P + 2, A)
(2)   a + n ≤ j  →  q j ≥ min (A + n, 2K − P + 2 − u j, B)
(2')  a ≤ j      →  q j ≥ 2K − P − u j
(3)   b + n ≤ j  →  q j ≥ min (B + n, u j + 2K − P + 2 − 2M, C)
(3')  b ≤ j      →  q j ≥ u j + 2K − P − 2M
(4)   c ≤ j      →  q j ≥ 2K − P + 2H − 2M − 2 − u j
```

where `a`, `b`, `c` range over landmark chains of the sentence and `n` is a *time credit*. The two
credit-carrying bounds are exactly what the index gaps of the sentence buy: the gap `K − M` is
`B − A`, so a valley landmark that far after a peak landmark leaves the greedy at or past the
valley position `B`, and the gap `H − 1 − M` is `C − B`. The five progress lemmas
`progLand_1/2/2'/3/3'/4` advance the bounds one step of the arm at a time, against the
advance-if-possible step `gstep4_lower2`.

**The index bounds are load-bearing.** `probe59c.c` runs the same sentence with every index gap
weakened to "strictly later" — the levels still asked for, in order, but not the gaps the walk's own
positions dictate. Over 5 800 000 random 1-Lipschitz arms of `[0, 9]` at every parameter set of the
window, **120 348 arms satisfy the level-only sentence and do not fold** (`probe59c.log`, with three
explicit witnesses printed). The index arithmetic is not decoration; it is the content.

Evidence before and after the Lean proof:

* `probe59.log` — every 1-Lipschitz arm of `[0, 9]` of length ≤ 12 (up to 713 816 arms per
  parameter set) at each of the 39 parameter sets: `land ∧ ¬fold` is 0 and `fold ∧ ¬land` is 0, in
  both the one-sided and the two-sided readings of the sentence.
* `probe59b.log` — 13 143 853 arms satisfying the sentence, over all bands `H − L ∈ [5, 12]`: the
  dynamic program rejects none of them, the greedy never loses legality, and all six invariant
  bounds hold at every step.
* `census-batch59.log` — over the general model, arms × parameter sets 160 575 668, the landmark
  sentence holds 60 320 238 times; of a capped sample of 400 000 arm × parameter-set fold
  evaluations, **`landNotFold = 0` and `foldNotLand = 0`**. The engine's criterion holds 27 399 695
  times, and the sentence holds where the engine's criterion fails **32 920 543** times — the size
  of the gap batch 58 exhibited at one arm.
* Read literally (existentials searched) against the greedy chain reading: 40 000 samples,
  0 disagreements.

### Question 2 — the 175-link witness of batch 58

`HPC/Fold/Audit59.lean` answers it in the kernel.

The forward arm of the batch-58 window of `bing 0 9` meets the criterion of **no** parameter set of
the window in either orientation (`not_leg4CritClosesL5`). Of the 58 (parameter set, orientation)
pairs, **exactly nine walks serve it**, proved by the dynamic program of `HPC/Fold/Decide.lean`
through `foldsOnto_of_foldsB (by decide +kernel)`:

| theorem | parameter set (reflected arm) | walk |
| --- | --- | --- |
| `serves_4_6_1` | `P = L+4, K = L+6, M = L+1` | `L+3 → L+6 → L+1 → L+8 → L+1` |
| `serves_4_7_1` | `P = L+4, K = L+7, M = L+1` | `L+3 → L+7 → L+1 → L+8 → L+1` |
| `serves_4_8_1` | `P = L+4, K = L+8, M = L+1` | `L+3 → L+8 → L+1 → L+8 → L+1` |
| `serves_5_6_1` | `P = L+5, K = L+6, M = L+1` | `L+4 → L+6 → L+1 → L+8 → L+1` |
| `serves_5_7_1` | `P = L+5, K = L+7, M = L+1` | `L+4 → L+7 → L+1 → L+8 → L+1` |
| `serves_5_8_1` | `P = L+5, K = L+8, M = L+1` | `L+4 → L+8 → L+1 → L+8 → L+1` |
| `serves_6_6_1` | `P = L+6, K = L+6, M = L+1` | `L+5 → L+6 → L+1 → L+8 → L+1` |
| `serves_6_7_1` | `P = L+6, K = L+7, M = L+1` | `L+5 → L+7 → L+1 → L+8 → L+1` |
| `serves_6_8_1` | `P = L+6, K = L+8, M = L+1` | `L+5 → L+8 → L+1 → L+8 → L+1` |

All nine are read on the **reflection** of the arm, and all nine have valley `M = L + 1`. The census
confirms that no other pair serves it.

The shape of the nine is the answer. A walk with `M = L + 1` has no deep-floor trigger at all —
the level `M − 2 = L − 1` is below the band — so the deep clause of the landmark sentence is
*vacuous* on it, and the arm has only to supply two landmarks: a time at `K − 1` or above at index
at least `K − P + 1`, and a time at `L + 2` or below, `K − M` steps later. On this arm the greedy
chain sits at indices 2 and 34 for `(P, K, M) = (L+5, L+6, L+1)`. The engine's criterion, by
contrast, reads its floor announcements at the base, `P − 4`, and asks there for a landmark at
`H − 2`; for `M = L + 1` the trigger of the walk and the trigger of the announcement are far apart,
and the announcement fails.

Hence the pair of theorems at one and the same parameter set:

* `Audit59.land_5_6_1 : Leg4Land armFR 9 6 1 5` — the exact criterion holds;
* `Audit59.not_crit_5_6_1 : ¬ Leg4Crit armFR (0 + 9) 6 1 5` — the engine's criterion fails
  (this is `Audit58.no_refl_5_6_1`).

`serves_armF_5_6_1`, `serves_armT_5_6_1` and `pair_folds` then show the basepoint of the batch-58
witness is served: both its arms fold onto one walk of the family. So the batch-58 refutation was a
refutation of the *engine*, never of the family — and the exact criterion sees what the engine
misses.

### Question 3 — exhaustiveness at `L + 5`, given exact criteria

With an exact criterion per walk, "every arm of the branch meets one of the criteria" becomes a
decidable property of a single arm. `HPC/Fold/CoverL5Land.lean` states it:

```
Leg4LandClosesL5 :=
  at every basepoint of the branch L + 5 there are K, M, P in the window such that
  the landmark sentences of leg4Walk L (L+9) K M P hold on both arms —
  either on the arms themselves (L+5 ≤ P ≤ L+7) or on their reflections (L+4 ≤ P ≤ L+6)
```

and proves

* `s3_span_nine_mid5_of_leg4Land_direct` / `_refl` — each clause really does give the fold, by
  `foldsOnto_leg4_of_leg4Land`;
* **`s3_span_nine_mid5_of_leg4LandClosesL5`** — `Leg4LandClosesL5` implies what the branch needs:
  at every basepoint of the branch both arms fold onto a common walk.

Unlike `Leg4CritClosesL5` of batch 58, which is false, this is a statement about the folds
themselves, so it cannot fail for a reason of the engine's making.

**On the corpus it holds.** `census-batch59.log`, `---- EVERYTHING ----`: 3 910 faithful pairs,
5 908 020 links, 46 321 non-thin; branch `L + 5` basepoints 1 384 273, of which
**1 384 273 have a parameter set serving both arms and 0 have none**. Of the 769 residual basepoints
that the five reflected three-turn walks miss, all 769 are served by a walk of the four-leg family.

Which finite list of walks. A greedy cover over the recorded basepoints of the whole branch
(200 000 basepoints) needs **five walks** (a reflected entry is written, as the census writes it,
in the reflected arm's own coordinates):

| pick | walk | covers |
| --- | --- | --- |
| 1 | reflected `P=4 K=6 M=2` : `L+6 → L+3 → L+7 → L+1 → L+8` | 136 120 |
| 2 | direct `P=5 K=7 M=3` : `L+4 → L+7 → L+3 → L+8 → L+1` | 51 180 |
| 3 | reflected `P=4 K=6 M=1` : `L+6 → L+3 → L+8 → L+1 → L+8` | 7 255 |
| 4 | direct `P=5 K=8 M=1` : `L+4 → L+8 → L+1 → L+8 → L+1` | 5 393 |
| 5 | direct `P=5 K=7 M=1` : `L+4 → L+7 → L+1 → L+8 → L+1` | 52 |

and the 769 residual basepoints alone need **three**: direct `P=5 K=7 M=2`
(`L+4 → L+7 → L+2 → L+8 → L+1`, 633), reflected `P=4 K=6 M=2` (134), direct `P=5 K=7 M=1` (2).
The single most useful walk over the branch is the reflected `P=4 K=6 M=2`,
`L+6 → L+3 → L+7 → L+1 → L+8`, which serves both arms at 949 266 of the recorded basepoints.

That walk is also the one at which the branch hypothesis and the criterion now meet.
`HPC/Fold/LandLowAt.lean` proves:

* `isLip_gap`, `isLip_index_gap(')` — for a 1-Lipschitz arm a level gap *is* an index gap, so the
  index bounds the landmark sentence asks for are free on any arm of the branch;
* **`land_down1_of_lowAt_low`** — for a 1-Lipschitz arm based at `L + 5`, the second disjunct of
  `LowAt` (before every descent to `L + 1`, a time at `L + 2` or below followed by one at `L + 6` or
  above) gives the whole descent clause of the exact criterion of `L+6 → L+3 → L+7 → L+1 → L+8`,
  index bounds included;
* `leg4Land_walk63718_of_lowAt_low` and `foldsOnto_walk63718_of_land` — the sentence assembled from
  that clause plus the two ascent clauses, and the fold read off it.

So at the branch's best walk the descent half of the exact criterion is a *theorem* from the branch
hypothesis, and what remains to be proved about an arm of the branch is the two ascent clauses.
That is the shape the remaining work at `L + 5` now has.

## 3. Deliverables

**Axioms.** Every new theorem depends only on the standard axioms; no `native_decide`, no added
axiom, no `@[implemented_by]`.

```
'HPC.Fold.foldsOnto_leg4_iff_leg4Land'           [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_of_foldsOnto'                 [propext, Classical.choice, Quot.sound]
'HPC.Fold.foldsOnto_leg4_of_leg4Land'            [propext, Classical.choice, Quot.sound]
'HPC.Fold.Audit59.pair_folds'                    [propext, Classical.choice, Quot.sound]
'HPC.Fold.Audit59.land_5_6_1'                    [propext, Classical.choice, Quot.sound]
'HPC.Fold.Audit59.not_crit_5_6_1'                [propext, Quot.sound]
'HPC.Fold.Audit59.serves_armF_5_6_1'             [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_leg4LandClosesL5' [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_leg4Land_refl'    [propext, Classical.choice, Quot.sound]
'HPC.Fold.land_down1_of_lowAt_low'               [propext, Classical.choice, Quot.sound]
'HPC.Fold.foldsOnto_walk63718_of_land'           [propext, Classical.choice, Quot.sound]
```

**Censuses.** `census-batch59.c` (generated from `census-batch58.c` by `mk59.py`, which is
idempotent) with the completed run `census-batch59.log`, run at
`rounds=40 seed=59 walk-steps=200 concat-draws=12`, over the general model and under the
audit protocol; the definition audit it prints is quoted in §0. The three probes are over **arms
alone**, and say so: `probe59.c` / `probe59.log` (exhaustive arms of `[0,9]` of length ≤ 12),
`probe59b.c` / `probe59b.log` (the invariant, over all bands `H − L ∈ [5,12]`), `probe59c.c` /
`probe59c.log` (the sentence with its index bounds removed).

**Files.** `HPC/Fold/Leg4Land.lean`, `HPC/Fold/Audit59.lean`, `HPC/Fold/CoverL5Land.lean`,
`HPC/Fold/LandLowAt.lean`, all imported at the end of `HPC.lean`; `census-batch59.c`,
`census-batch59.log`, `mk59.py`, `probe59.c`, `probe59b.c`, `probe59c.c` and their logs; this
report. The batch-58 commission is preserved as `COMMISSION-batch58.md`.
