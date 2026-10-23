# Report: batch 63 — the last clauses of the crossing

Written in the order the commission prescribes: counterexamples first, then §1 (targets), then §2
questions 1–4, then §3 deliverables.

## 0. Counterexamples and refutations

**One refutation, of a statement of the previous batch.** `LandWalkSuffices`
(`HPC/Fold/LandWalkSuff.lean`, batch 62) — the sufficiency half of the general engine, *for a walk
of any shape* — is **false**, and `HPC/Fold/LandWalkFail.lean` proves it
(`not_landWalkSuffices`), with an explicit three-time witness.

Take the walk of the turning levels `[1, 0, 3]` from `0`:

```
walkList 0 [1,0,3] :   0  1  0  1  2  3       (six times)
turn times         :   0  1  2        5
turning levels     :   0  1  0        3
```

and the arm `cexArm = (1, 2, 3)`. It is 1-Lipschitz, starts within one of the walk's first level,
and every one of its levels is served by the walk (the time `4`, at level `2`, serves all three).

* It **satisfies the sentence** (`landWalk_cex`). Clause `r = 0` is trivial; `r = 1` and `r = 2`
  fire only at the arm's last times and the chains `(0)` and `(0, 1)` serve them; and for `r ≥ 3`
  the trigger never fires, because the walk's time `4` serves every level of the arm and `4` is
  before the last turn `5`.
* It **does not fold** (`not_foldsOnto_cex`). The fold must start at the walk's time `0`, so after
  two steps it is at time `2` at the latest, and the walk's levels there are `0, 1, 0` — none of
  them serves the arm's level `3`.

**Where the sentence leaks, exactly.** `LandWalk`'s clause `r` fires at a time `d` only when every
time of the walk that serves `f d` is the `r`-th **turn time** or later, and the chain it then
returns ends at `d` itself with the walk's own turn-to-turn gap. The four-leg sentence `Leg4Land`
reads both of those at the **level** instead: its triggers are the earliest serving positions
`2K − P − v`, `2K − P + 2H − 2M − 2 − v`, `v + 2K − P − 2M`, which are not turn times, and its last
gaps `K − 1 − f d`, `H − 2 − f d`, `f d − M − 1` are measured to those positions. In the
counterexample the arm's level `3` is served earliest at the time `4`, which is not a turn time and
lies strictly before the last turn, so **no clause of `LandWalk` fires at the arm's last time at
all**. The generalisation of batch 62 lost the level-awareness of the four-leg sentence, and that
is precisely what it lost.

**The repair, and its limit.** `LandWalkP` (same file) is the sentence with both weaknesses
removed: the trigger is any position `P` at or after the `r`-th turn that no serving time precedes,
and the chain's last landmark is a time of the arm at `walkLevel r`, at least `P − walkStop r`
before `d`. It is still necessary for folding (`landWalkP_of_foldsOnto`, one application of
`foldsOnto_landmarkN` to the chain `walkStop 0 ≤ ⋯ ≤ walkStop r ≤ P`) and it excludes the
counterexample (`not_landWalkP_cex`).

It is not, however, sufficient for *every* walk. The search `probe63.c` (logs `probe63.log` for the
sentence as stated, `probe63b.log` for the corrected one) runs both implications over all 1862
walks of at most four turns with levels in `[0, 5]`, and all arms of at most twelve times, with
every predicate evaluated by its own definition:

```
                        walks    walks with a counterexample to sufficiency
                                 LandWalk        LandWalkP
  shortest leg  1        1120      510               30
  shortest leg  2         500      162                0
  shortest leg  3         184       30                0
  shortest leg  4          50        0                0
  shortest leg  5           8        0                0
```

So the sentence as stated fails even at walks all of whose legs are three long, while the corrected
sentence fails **only at walks with a leg of length one** — a unit leg, which the four-leg window
(`M + 3 ≤ K`, `P ≤ K`, `M ≤ P − 2`, `K ≤ H − 1`) excludes, so the engine of
`HPC/Fold/Leg4Land.lean` is untouched by all of this.

The unit-leg case is a refutation too, and it is also proved:
`not_landWalkP_suffices_without_noUnitLeg` is the smallest witness the search finds — the walk
`1 2 3 2 3 2 1 0` of the turning levels `[3, 2, 3, 0]` from `1`, whose second and third legs are one
step long, and the ten-time arm `0 1 2 1 0 1 2 1 0 −1`. It satisfies `LandWalkP` with the single
chain `(0, 2, 3, 6, 9)` (`landWalkP_cex2`) and does not fold (`not_foldsOnto_cex2`): each of its
three visits to the level `0` pins the fold to the walk's time `0`, from where the last level `−1`,
served only by the walk's time `7`, is five steps out of reach.

`LandWalkPSuffices` is therefore the corrected statement with the hypothesis `NoUnitLeg`, which the
two refutations show cannot be weakened in either direction. Its proof is not in this batch.

## 1. The targets

| target | file | state |
| --- | --- | --- |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | still `sorry`; this batch closes the crossing's *index* side completely and reduces the crossing to two named facts |
| `s3_span_nine` | `HPC/Fold/General.lean` | unchanged |
| `s3_general` | `HPC/Fold/General.lean` | unchanged |
| `theorem3` | — | unchanged, waits on `s3_general` |

What moved. `s3_span_nine_mid5_of_cross_w72` (`HPC/Fold/CrossPair63.lean`) proves the branch at a
crossing from two hypotheses and nothing else: the band misses the floor `L`, and the partner arm
satisfies `w72`. Everything the batch-62 reading of the pairing still owed on the index side is
supplied — the hypothesis on the partner arm is now literally *the failure of `w8`'s floor clause*,
which is what a crossing is, rather than the stronger index-two form batch 62 had to assume.

## 2. The questions

### 2.1 The `w8` side that touches `L`

**The walk that serves those crossings is `w71`, not `w81`.** At all 179 crossings of the corpus
whose `w8` side reaches the floor:

```
the w8 side satisfies w81 = L+5 → L+8 → L+1 → L+8 → L+1   179 of 179
the partner satisfies w81                                  13
both arms satisfy w81                                      13
both arms satisfy w71 = L+4 → L+7 → L+1 → L+8 → L+1       179 of 179   (and both fold onto it)
both arms satisfy w72                                     169
some walk of the family serves both arms                  179;  none: 0
```

So the commission's candidate is the wrong half of the pair: the `w8` side satisfies `w81` at every
one of those crossings — unsurprisingly, since `w81` is `w8` with its basepoint one level higher —
but the *partner* satisfies it at only 13 of them, and the pairing is what matters. What serves all
179, on both arms and by the fold itself, is `w71`. The two parameter sets `(P,K,M) = (5,7,1)` and
`(6,7,1)` (the same walk read from two basepoints) each serve all 179.

Whether the pairing supplies `w81`'s clauses is therefore not the question to press: the deep-floor
clause of `w72`, which fires exactly when the `w8` side touches `L`, is answered by moving to
`w71`, whose own deep-floor clause (`M = L + 1`, trigger `f d ≤ L − 1`) never fires inside the band.
That is the reason `w71` is immune where `w72` is not, and it is the same reason in both questions
1 and 2.

### 2.2 The partner's 30

**All thirty are the deep-floor clause, and all thirty are served by `w71`.**

```
crossings at which the partner fails w72                   30
  the clause that fails:  base 0, floor 0, deep floor 30, ceiling 0
  of those, the partner itself touches the floor L         30
  of those, the w8 side satisfies w71                      30
  of those, both arms satisfy w71                          30
  some walk of the family serves both arms there           30;  none: 0
```

The partner's thirty failures of `w72` are the clause `w72` has and `w71` has not: `w72`'s valley
level is `M = L + 2`, so its deep-floor clause triggers at `L`, and at exactly those thirty
crossings the partner arm reaches `L`. At every one of them the pair is served by `w71`, on both
arms.

**Consequently the two walks `w71` and `w72` cover the whole corpus of crossings.** Measured over
all 461:

```
w71 serves both arms                     374
w72 serves both arms                     421
w71 or w72 serves both arms              461   (none is missed)
some walk of the four-leg family does    461
```

The two are complementary in exactly the way the clause analysis predicts: `w72` closes the
crossings whose ceiling valley sits at `L + 3` (the pairing's own valley when the partner descends
only to `L + 2`), and `w71` closes the ones that touch the floor. The list of six of
`Leg4SixCrossL5` is, on this corpus, a list of two.

### 2.3 The two-index slack

**It is closed, and not by the two-level law.** The commission's first alternative fails: from the
basepoint `ρ i = L + 5` a time at `L + 7` is two levels up, and the timing law gives only
`z 2 − 1 = 2` steps for two levels, so arm index two is allowed — and the corpus indeed has such a
peak at 83 of the 461 crossings.

What closes the slack is the **three**-level law together with a property of the crooked peak that
`cross_peak_valley_core` did not record: the peak is produced by crookedness at the level
`ρ b − 1 ≥ L + 8`, so its *interval* reaches `L + 8` even though its own point value is only known
to be `L + 7`. Three levels above the basepoint costs `z 3 − 1 = 5` steps, and that is
`base_high_sep`:

> a link whose interval reaches `L + 8` is five steps or more from a link at the level `L + 5`, on
> either side.

Hence the crooked peak is never at arm index two, three or **four**, and `cross_peak_valley_armG'`
now asks the partner only for what `crossBad_of_floor_fail` supplies — no time at `L + 7` or above
at arm index **four** or more — while also returning `5 ≤ R` instead of `2 ≤ R`. The consequences
follow with the same weakening (`leg4Land_w72_ceil_of_cross'`,
`leg4Land_w72_of_cross_of_floor1'`), and `leg4Land_w72_of_cross_of_floor_fail` states the whole
thing with the hypothesis written as the crossing itself.

The census confirms the law on the corpus, and finds it tight:

```
a partner time at L+8 or above at arm index 1..4                      0 of 461
a partner interval reaching L+8 at arm index 1..4                     0
a w8-side interval reaching L+8 at arm index 1..4                     0
the least arm index at which an interval reaches L+8: w8 side 5, partner 126
the crooked peak of the literal search: found 282 times, least arm index 5,
  at arm index below five: 0
```

Five is attained, so the bound `base_high_sep` gives is exactly the right one.

### 2.4 `LandWalkSuffices`

Refuted twice; see §0. The induction the commission asks for cannot be carried out, because the
statement it would prove is false, and the natural repair is false without a hypothesis on the
walk's legs. What this batch supplies in its place is the diagnosis — the trigger and
the last gap of the sentence must be read at the level, not at the turn — the corrected sentence
`LandWalkP` with its necessity proved, the measurement that pins the remaining hypothesis (no unit
leg), and the corrected statement `LandWalkPSuffices`. The general engine is still one induction
away, but it is now an induction of a statement that is not refuted by a three-time arm.

## 3. Deliverables

**New Lean files, both `sorry`-free, no `native_decide`, no new axiom.**

* `HPC/Fold/LandWalkFail.lean` — `cexArm`, the walk facts of `[1,0,3]`, `cex_band`, `cex_isLip`,
  `landWalk_cex`, `not_foldsOnto_cex`, `not_landWalkSuffices`, `LandWalkP`,
  `landWalkP_of_foldsOnto`, `not_landWalkP_cex`, `cexArm2`, the walk facts of `[3,2,3,0]`,
  `cex2_band`, `cex2_isLip`, `landWalkP_cex2`, `not_foldsOnto_cex2`,
  `not_landWalkP_suffices_without_noUnitLeg`, `NoUnitLeg`, `LandWalkPSuffices`,
  `landWalkP_iff_foldsOnto_of_suffices`.
* `HPC/Fold/CrossPair63.lean` — `cross_peak_valley_core'`, `base_high_sep`,
  `cross_peak_valley_armG'`, `leg4Land_w72_ceil_of_cross'`, `leg4Land_w72_of_cross_of_floor1'`,
  `leg4Land_w72_of_cross_of_floor_fail`, `s3_span_nine_mid5_of_cross_w72`.

Both are imported by `HPC.lean`; `lake build HPC` is clean. The project's `sorry`s are exactly the
four standing targets it had before this batch — `s3_span_nine_mid5` (`Mixed.lean`), `s3_span_nine`
and `s3_general` (`General.lean`) and `theorem3` (`Open.lean`) — and nothing this batch adds uses
any of them.

```
'HPC.Fold.landWalk_cex' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_foldsOnto_cex' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_landWalkSuffices' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.landWalkP_of_foldsOnto' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_landWalkP_cex' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.landWalkP_cex2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_foldsOnto_cex2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_landWalkP_suffices_without_noUnitLeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.landWalkP_iff_foldsOnto_of_suffices' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_peak_valley_core'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.base_high_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_peak_valley_armG'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_ceil_of_cross'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_cross_of_floor1'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_cross_of_floor_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_cross_w72' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Censuses over the general model, under the audit protocol.** `census-batch63.c` (log
`census-batch63.log`, run as `census-batch63 40 62 200 12`) is the batch-62 census with a batch-63
block added: the stored crossings of the trichotomy are read for the three questions above — the
walks of the four-leg family that serve both arms at the floor-touching crossings and at the
partner's failures of `w72`, by the exact criterion *and* by the fold; the failing clause of `w72`,
by the clause mask; the coverage of the whole corpus by each parameter set; and the timing law at
the basepoint, both on the point sequence `ρ` and on the interval `[ρ, σ]`. Every predicate is
evaluated by its own definition — `landLeg4` and `landLeg4Mask` are `Leg4Land` clause by clause
with the index bounds the walk's positions dictate, `foldsDirect` is the folding dynamic program,
`firstAtLeast`/`firstAtMost` are literal scans — and no criterion of the engine is used anywhere in
the block. The block ends with its own audit paragraph, and the run's global definition audit is
unchanged.

`probe63.c` (logs `probe63.log`, `probe63b.log`) is the search of §0. It is a census over walks and
arms, not over the general model: it enumerates walks by their lists of turning levels and arms as
1-Lipschitz level sequences, and evaluates `walkList`, `walkLen`, `walkStop`, `walkLevel`,
`LandWalk`, the corrected sentence and `FoldsOnto` by their own definitions, the chain existence by
the backwards greedy (which is optimal, each landmark being taken as late as possible) and folding
by reachability over the walk's positions.

The numbers quoted in §0 and §2 are from those two programs and their logs.
