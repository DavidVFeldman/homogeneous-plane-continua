# Report — batch 69

The commission read is `COMMISSION-batch69.md` (identical copy `COMMISSION.md`), the batch-69
archive's text: *`Ceil72` on the high-running arm, and span nine.*

New in the project: two Lean files, `HPC/Fold/Ceil69.lean` and `HPC/Fold/LandWalkFail69.lean`, both
`sorry`-free and imported by `HPC.lean`; the census `census-batch69.c` with its log
`census-batch69.log`; the axiom profiles of every new theorem in `axioms-batch69.txt`. `lake build`
is clean on `RequestProject` and `HPC`, and the project's standing `sorry`s are still exactly the
four targets — `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`.

## 0. The refutation, first

**§2.5 is delivered as a theorem: the landmark sentence with the clause of batch 66 §2.3 added is
still not sufficient for folding.** `HPC/Fold/LandWalkFail69.lean` writes the clause out
(`BeforeClause`), writes the strengthened sentence out (`LandWalkPB`), states its sufficiency for a
walk with no short leg (`LandWalkPB3Suffices`) and for a walk whose legs are all at least `k` steps
(`LandWalkPBLegSuffices k`), and refutes both at the **fourth counterexample of `check68.log`** —
the one whose shortest leg is four:

```
walkList 0 [5,1,6,0] : 0 1 2 3 4 5 4 3 2 1 2 3 4 5 6 5 4 3 2 1 0   (twenty-one times)
turn times           : 0         5       9         14          20
turning levels       : 0         5       1          6           0
legs                 :    5         4        5            6
cexArm69 (forty times):
  -1 0 -1 0 0 -1 0 0 1 2 2 2 3 2 3 2 3 2 1 2 1 2 2 2 3 4 4 3 2 1 0 -1 0 1 2 3 4 5 6 7
```

* `landWalkPB_cex69` — the arm satisfies the strengthened sentence, with the single chain
  `(0, 25, 29, 38)`: its time `0` at the level `-1` for the walk's start `0`, its time `25` at `4`
  for the turning level `5`, its time `29` at `1` for the turning level `1`, and its time `38` at
  `6` for the turning level `6`. Two facts do the work. Only the turns `r ≤ 3` have a clause here at
  all: the walk's fourth turn is its time `20`, and no level of the arm is first served that late
  (`cex69_no_trigger_ge_four`). And the added clause of batch 66 is met wherever it is asked, for a
  blunt reason — **every** level of this arm is served by some walk position at or after the walk's
  third turn (`cex69_served_late`), so no time of the arm is one the clause speaks about
  (`cex69_beforeClause`). The added clause is therefore vacuous on this witness, which is the
  sharpest form the refutation can take: the clause is not merely insufficient, it is not even
  engaged.
* `not_foldsOnto_cex69` — the arm does not fold, decided by the dynamic program of
  `HPC/Fold/Decide.lean`, which is proved to be `FoldsOnto` itself (`foldsB_iff`) and is evaluated
  by the kernel. No itinerary is supplied by hand and no `native_decide` is used.
* Hence `not_landWalkPB3Suffices`, `not_landWalkPBLegSuffices_four` and
  `not_landWalkPBLegSuffices_le_four` — raising the leg bound to four is not the repair.

The refuted sentence is kept: `LandWalkP` and its sufficiency statements stay where batches 64 and
65 left them, and the new `LandWalkPB` is written out here with its refutation attached in the
docstring. No replacement is asked for and none is written. Nothing in the development depends on
the sufficiency of a landmark sentence: every fold it produces comes from
`foldsOnto_leg4_iff_leg4Land`, whose criterion is exact, and the sentence is used only in its
necessary direction.

## 1. The targets

`s3_span_nine_mid5`, `s3_span_nine`, `s3_general` and `theorem3` are **not** proved in this batch.
What the batch does to them is to discharge, as a theorem, the clause batch 68 left standing at the
high-run crossing — `w72`'s ceiling clause on the running arm — under one distance hypothesis, and
to reduce the branch's residue to three named statements about the corpus, all of which the census
finds hold at every crossing it stores. The residue is stated in §2.4.

## 2. The questions

### 2.1 `Ceil72` on the high-running arm

**Census first, as the commission asks.** `census-batch69.c` (block *batch 69 section 2.1*, log
`census-batch69.log`) reads the 87 high-run crossings of the stored corpus one by one — a crossing
of the trichotomy with exactly one `w8` side whose `w8` side is not deep first at `L + 2` — and
reports, at each, the witness of `Ceil72` at the first ascent, taken with its low landmark as late
as possible. The picture is completely uniform:

| measured at the 87 high-run crossings | value |
| --- | --- |
| a `Ceil72` witness exists at the first ascent | 87 of 87 |
| `Ceil72` holds at **every** ascent of the running arm | 87 of 87 |
| `Ceil71` holds on the running arm | 0 of 87 (as `w71_armG_iff_deepFirst2` predicts) |
| the level of the low landmark `k` | `L + 3` at all 87 |
| the distance `d − k` from the ascent | **70** at all 87 |
| the index of `k` | 34 to 43 |
| the index of the peak `j`, at level `L + 6` | 23 to 38 |
| a valley of the crookedness clause read between the nearest time at `L + 2` or below across the basepoint and the ascent can lie on the running arm | 87 of 87 |
| the distance from the basepoint to that nearest low time | between 56 and 65 |

The distance **70** is the answer. It is not a feature of the arm: it is the crookedness clause's
own spacing (`z 6 = 71`, the third gap of `crooked_peak_valley_high9_mid`). So the time that
supplies the `L + 3` is not a time the running arm owns by itself — it is the **valley of the
pairing read between the partner's nearby time at `L + 2` or below and the running arm's ascent**,
and the clause's spacings push that valley, and the peak before it, past the basepoint and onto the
running arm.

**That is now a theorem** (`HPC/Fold/Ceil69.lean`). Write `NearLowT ρ i L` for *some time of the
pair before the basepoint is at `L + 2` or below and at most 67 steps before it* (and `NearLowG`
for the mirror). Then

> `ceil72_at_of_nearLow_armG` — under `NearLowT`, at every time `d` of the forward arm at `L + 9`
> the pairing between that low time `a` and `d` returns a peak at `L + 7` or above and a valley at
> `ρ a + 1 ≤ L + 3` or below **as times of the forward arm**, the peak at arm index three or more,
> the valley twenty-nine steps after it and seventy steps before the ascent. These are the two
> landmarks `Ceil72` asks for, with far more room than it asks for (it wants a gap of five and a
> distance of six).
>
> `ceil72_of_nearLowT_armG` / `ceil72_of_nearLowG_armT` — hence the whole of `Ceil72` on that arm.

The arithmetic is forced and is the whole content: the clause places its peak `70` after `a` and its
valley `29` after the peak, so `a ≥ i − 67` puts the peak at arm index `3` or more — exactly the
index the clause asks for — and the valley then sits at arm index `32` or more, seventy steps before
the ascent. The high run plays no part: the hypothesis gives the clause at every ascent, whether or
not the arm has been low before it, so the theorem covers the batch-68 case and the deep-first case
alike.

So the answer to the second half of the question — *is the witness a theorem from the pairing, from
`Mid2Floor` on the running arm, or from the partner's `w3` clauses?* — is: **from the pairing**, read
across the basepoint against a low time of the partner, and neither `Mid2Floor` nor the `w3` clauses
are used. What the pairing needs, and what is not proved, is that the partner's low time is **near**:
over the corpus the nearest one is 56 to 65 steps from the basepoint, inside the 67 the argument
needs, but with only two steps to spare. That distance question is now the residue, and it is named
in Lean as `NearLowT` / `NearLowG`.

### 2.2 The deep-floor clauses where the band reaches `L`

**Census.** At all 87 high-run crossings the band reaches the floor, and at all 87 both deep-floor
clauses hold — the running arm's and the partner's (`census-batch69.log`). So `deep72_of_off_floor`
is never the reason here, and the clauses are true where they are not vacuous.

**Half of it is a theorem.** On the running arm the same pairing gives the first two landmarks and
the run itself gives the third:

> `deep72_at_of_nearLow_of_nine_armG`, `deep72_of_nearLowT_armG` — under `NearLowT`, and with an
> ascent to `L + 9` before each descent to the floor (`NineBeforeDeep`, which is what a high-run arm
> that reaches the floor after its run satisfies), the forward arm has `w72`'s deep-floor clause:
> the peak at `L + 7` or above and the valley at `L + 3` or below come from the pairing, the ascent
> to `L + 9` is the third landmark, and the timing is the plain Lipschitz one — the arm needs
> `L + 9 − f d` steps to come down from the ascent to the descent, where the clause asks for
> `L + 7 − f d`.

**The partner's clause is not a theorem here.** The partner stops below `L + 9`, so this route is
closed to it, and reading its `wb` clauses gives the familiar shortfall of one level: at a descent
to `L` the ceiling clause of `wb` returns a time at `L + 6` or above six steps earlier, where
`Deep72` asks for `L + 7` and seven. Batch 63's `leg4Land_w72_of_cross_of_floor1` and the batch-64
floor facts do not close that gap either, since both are read at the descents to `L + 1` and below
of the *reflected* arm. It remains a hypothesis of the assembly and holds at all 87 crossings of the
corpus.

### 2.3 The assembly's hypothesis: the partner below `L + 9`

**Census:** the two arms of a crossing never both reach `L + 9` — 0 of the 461 crossings (batch 68)
and 0 of the 87 high-run crossings (batch 69). **No proof is offered**, and none is claimed: the
timing law across the basepoint gives nothing here (two links at the same level are not separated by
it), and the crossing clauses are about which walks serve which arm, not about the top of the band.
By the commission's instruction the configuration is therefore **named as a case of the branch**:
`BothNineL5 ρ i L` (`HPC/Fold/Ceil69.lean`), together with the trivial case split
`armT_no_nine_or_bothNine` — where the forward arm has reached `L + 9`, either the backward arm
stops below it, which is the hypothesis the assembly carries, or both arms reach it and the case is
`BothNineL5`.

### 2.4 Assembly

With §2.1 the high-run crossing closes, modulo the three statements the census measures:

> `s3_span_nine_mid5_of_cross_highRun_nearLow_armG` (and its mirror) — at a crossing of the
> trichotomy whose `w8` side is the forward arm, **given** that the partner stops below `L + 9`
> (§2.3), that both deep-floor clauses hold (§2.2), and that a time at `L + 2` or below sits within
> 67 steps before the basepoint (§2.1), both arms fold onto one walk, namely `w72`.

So `s3_span_nine_mid5` is **not** closed, and neither is `s3_span_nine`. What the branch at `L + 5`
now owes is exactly three statements, in decreasing order of how much of the argument they carry:

1. **the distance** — at a high-run crossing, a time of the pair at `L + 2` or below within 67 steps
   across the basepoint (`NearLowT` / `NearLowG`): 87 of 87, nearest between 56 and 65;
2. **the partner's deep-floor clause** where the band reaches the floor: 87 of 87;
3. **the partner below `L + 9`** (`BothNineL5` empty): 87 of 87, 461 of 461.

Each is a statement about the two arms of one crossing, and each is now named in Lean, so the next
batch has three separate, decidable-per-crossing targets rather than one clause.

### 2.5 The probe's refutation in Lean

Delivered; see §0.

### 2.6 After span nine, a statement only

Not due: the inventory is asked for *once `s3_span_nine` is a theorem*, and it is not. Nothing is
claimed about it here.

## 3. Deliverables

1. **What is proved, `sorry`-free, with `#print axioms`.** `axioms-batch69.txt` lists all 39
   theorems of the two new files; every profile is a subset of `[propext, Classical.choice,
   Quot.sound]` and several are axiom-free. No `native_decide`, no `axiom`, no `implemented_by`.
   `HPC/Fold/Ceil69.lean`: `ceil72_at_of_nearLow_armG`, `ceil72_at_of_nearLow_armT`,
   `ceil72_of_nearLowT_armG`, `ceil72_of_nearLowG_armT`,
   `s3_span_nine_mid5_of_cross_highRun_nearLow_armG` and its mirror,
   `deep72_at_of_nearLow_of_nine_armG`, `deep72_of_nearLowT_armG`, `armT_no_nine_or_bothNine`,
   `nearLowT_of_armT_low`, `nearLowG_of_armG_low`, with the definitions `NearLowT`, `NearLowG`,
   `NineBeforeDeep`, `BothNineL5`. `HPC/Fold/LandWalkFail69.lean`: the definitions `BeforeClause`,
   `LandWalkPB`, `LandWalkPB3Suffices`, `LandWalkPBLegSuffices`, the witness `cexArm69` with its
   supporting facts, `landWalkPB_cex69`, `not_foldsOnto_cex69`, `not_landWalkPB3Suffices`,
   `not_landWalkPBLegSuffices_four`, `not_landWalkPBLegSuffices_le_four`, and
   `landWalkP_of_landWalkPB`.
2. **The census of §2.1, under the audit protocol.** `census-batch69.c` is `census-batch68.c` with
   one new block, `report69`, and nothing else changed; the log is `census-batch69.log`. The block's
   definition audit is printed in the source and repeated in the log preamble of the earlier blocks:
   `ceil72Clause` and `ceil71Clause` are the third clause of `Leg4Land` at `(H,K,M,P) = (9,7,2,5)`
   and `(9,7,1,5)` written out at `L = 0` with their existentials searched literally; `deepFirst2`
   is `DeepFirst2` of `HPC/Fold/Ceil68.lean`; `deep72Clause` is the second clause of `Leg4Land` at
   `(9,7,2,5)`; the crookedness reading uses the stored `ρ` and `σ` of the pair each crossing came
   from and reads the clause exactly as `crooked_peak_valley_high9_mid` reads it. No criterion of
   the engine is used anywhere in the block. The crossings are the stored crossings of the
   trichotomy, duplicates merged, and the arms are whole arms of the corpus, not truncated — this is
   a census over crossings, not over arms alone, so no arm-length bound applies; the arms of the 87
   run from 105 to 114 times.
3. **This report**, whose first line names the commission read, with the refutation first, then the
   targets, then the six questions.

## 4. What the corpus is, and what it is not

The 87 high-run crossings of the corpus come from a small number of distinct faithful pairs (all of
them windows of one 986-link pair in this sweep), so the uniformity of the numbers above — the
witness level `L + 3`, the distance 70, the nearest low time between 56 and 65 — should be read as
one configuration seen many times, not as 87 independent confirmations. That is the more reason to
have the §2.1 mechanism as a theorem rather than as a measurement: the theorem holds of any pair
with a low time within 67 steps of the basepoint, whatever the corpus contains.
