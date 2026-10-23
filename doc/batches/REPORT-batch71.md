# Report — batch 71

The commission read is `COMMISSION-batch71.md` (identical copy `COMMISSION.md`), the batch-71
archive's text: *the distance.*

New in the project: two Lean files, `HPC/Fold/Distance71.lean` and `HPC/Fold/Audit71.lean`, both
`sorry`-free and imported by `HPC.lean`; the census `census-batch71.c` with its log
`census-batch71.log` and its row table `census-batch71-rows.csv`; the construction attempt
`break-batch71.c` (log `break-batch71.log`) with its seeds `seeds-batch71.txt`, the minimiser
`min-batch71.c` (log `min-batch71.log`), the two stored witnesses `witness-batch71.txt` and
`witness-batch71-min.txt`, and the independent re-check `check71.py` (log `check71.log`); the axiom
profiles of all new theorems in `axioms-batch71.txt`. `lake build` is clean and the project's
`sorry`s are still exactly the four standing targets (`s3_span_nine_mid5`, `s3_span_nine`,
`s3_general`, `theorem3`).

## 0. The counterexample, first

**The distance is false.** `NearLowBandT` / `NearLowBandG` — the one statement batch 70 left the
branch `L + 5` owing at a high-run crossing — is refuted, in all three of its readings, and the
refutation is a Lean theorem checked by the kernel:

> **`not_nearLowBandCrossL5`** (`HPC/Fold/Audit71.lean`): there is a faithful pair of **290 links**
> with a basepoint at `L + 5` whose two arms satisfy `LowAt (L + 1) (L + 8)`, which is a crossing of
> the trichotomy, whose backward arm **runs high** — it reaches `L + 9` at arm index 104 with
> nothing at `L + 2` or below before it — and for which the pair has **no** time at `L + 2` or below
> within 67 steps past the basepoint, **none** at `L + 1` or below within 166, and **none** at the
> floor within 405.

Everything about the witness is put to the kernel, faithfulness included, in the manner of
`HPC/Fold/Audit57.lean`: `Audit71.faithful` is `IsCrookedIvF ρ σ` by the interval search of
`HPC/Fold/DichotomyFaithful.lean` with `decide +kernel`; `Audit71.lip`, `band_lo`, `band_hi`,
`base_level`, `lowAt_armG`, `lowAt_armT`, the three refutations that make up `Audit71.cross`,
`Audit71.highRun_armT` and `Audit71.not_nearLowBandG` are all `decide +kernel` as well. No
`native_decide`, no `axiom`; every profile in `axioms-batch71.txt` is a subset of
`[propext, Classical.choice, Quot.sound]`.

**The definition audit.** The pair is also re-checked from scratch by `check71.py` (log
`check71.log`), with `IsCrookedIvF`, `LowAt`, `Leg4Land`, `DeepFirst2`, `Ceil72`, `Deep72` and
`FoldsOnto` written out again in Python, independently of the C of the search and of the Lean:

```
the witness: 290 links, basepoint 104, the w8 side is the backward arm
  IsCrookedIvF: True            rho i = 5; the band is [2, 9]
  LowAt on the forward arm: True; on the backward arm: True
  w8: forward False, backward True;  wb: forward True, backward False
  w3: forward True, backward False;  a crossing of the trichotomy: True
  the w8 side runs high: True (first ascent at arm index 104, nothing at 2 or below before it)
  nearest time at 2 or below: 185 steps (NearLowT asks for 67)   -> FAILS
  nearest time at 1 or below: none        (the second reading, 166) -> FAILS
  nearest time at the floor:  none        (the third reading, 405) -> FAILS
  Ceil72 on the running arm: True; on the partner: True
  Deep72 on the running arm: True; on the partner: True
  w72 on the forward arm: True; on the backward arm: True
  walks of the four-leg family serving both arms: 4
```

**It is not a counterexample to `S3`.** At the witness both arms satisfy the landmark sentence of
`w72` and four walks of the four-leg family serve both arms; across the whole construction — 2229
high-run crossings at which the distance fails — `Ceil72` holds on both arms at **all 2229**, the
`w72` sentence holds on both arms at all 2229, and a walk of the family serves both arms at all
2229. What is refuted is the *hypothesis* of the batch-69 and batch-70 assemblies, not the statement
they prove.

**What it costs and what it buys.** The route of batch 69 — get `w72`'s ceiling clause from a low
time near the basepoint — is closed as a general argument: the low time is not always there. The
branch's obligation is therefore not the distance but `Ceil72` itself, and batch 71 makes that
precise: `Ceil72` on an arm of the band is *equivalent* to one landmark pair before the arm's first
ascent (`Valley3BeforeNine`, §2.3), and on a running arm its valley is at level **exactly** `L + 3`.

**The band.** The 290-link window has band `[L + 2, L + 9]`, which satisfies every hypothesis the
assembly uses (`s3_span_nine_mid5_of_cross_highRun_band_armT` asks only `L ≤ ρ` and `ρ ≤ L + 9`).
The pair it is a window of — the extreme break, 1106 links, `witness-batch71.txt` — has band exactly
`[L, L + 9]`, is faithful, is the same crossing, and breaks all three readings with the nearest low
time 185 steps away, the nearest at `L + 1` 424 and the nearest at the floor 1001. Both are in
`check71.log`; the shorter one is what the kernel checks.

## 1. The targets

`s3_span_nine_mid5`, `s3_span_nine`, `s3_general` and `theorem3` are **not** proved in this batch.
The batch's work is the refutation above, the reduction of the branch's obligation to a statement
about one landmark pair, and two theorems that derive the distance from the same statement at lower
levels. No refuted statement has been deleted: `NearLowT`, `NearLowG`, `NearLowBandT`,
`NearLowBandG` and every theorem that consumes them are conditional statements and remain true as
stated — what is now known, and recorded in `HPC/Fold/Audit71.lean` and in the headers of
`HPC/Fold/Distance71.lean`, is that their hypothesis is not always met.

## 2. The questions

### 2.1 The anatomy of the nearest low time

`census-batch71.c` re-runs the batch-70 corpus unchanged — 64 base level sequences, 7040 faithful
pairs (6796 distinct), 12 392 192 links of which 205 420 not thin, 2 444 297 basepoints of the
branch, 1351 crossings, **229 high-run crossings in 52 configurations**, arms of 105 to 2211 times,
so the batch-70 counts are reproduced exactly — and measures the anatomy of the nearest low time at
each of the 229. The full row of every crossing is in `census-batch71-rows.csv`; the table of
distinct configurations is printed in `census-batch71.log`. Uniformly:

| | |
| --- | --- |
| which arm it is a time of | the **partner's**, at all 229 (the running arm has nothing at `L + 2` or below before its ascent, by the high run) |
| its exact level | `ρ = L + 2` at all 229 — never lower; the link's upper end is `σ = L + 2` or `L + 3` |
| its arm index | 56 to 65 |
| the level profile between it and the basepoint | the pair stays in `[L + 2, L + 6]` or `[L + 2, L + 7]`: the minimum over the window is `L + 2` at all 229, the maximum `L + 6` or `L + 7`, and where it reaches `L + 7` it does so at arm index 2 or 3 |
| is it the valley or the peak of a crookedness reading | the **valley**, at 212 of the 229; never the peak; at the other 17 no reading of span at most 600 names it |

**Read from which two links.** Two readings, and no others:

| reading | count | from | to | span |
| --- | --- | --- | --- | --- |
| the pairing of `crooked_peak_valley_high9` | 190 | a link of the pair carrying `L + 1`, 295 to 304 steps **before** the basepoint | the running arm's link carrying `L + 9`, 104 to 113 steps **after** it | 408 |
| a short descending pairing | 22 | a link carrying `L + 4`, 55 to 63 steps before the basepoint | a link carrying `L + 1`, 295 to 304 steps after it | 241 |

So the answer to *what produces this time* is: at 190 of the 229 it is produced by the very reading
the branch uses one level down — the crookedness pairing between the nearest time of the pair at
`L + 1` or below and the running arm's ascent, whose valley is a time at `L + 2` or below. That is a
theorem, and §2.2 states it. What is **not** a theorem, and is what the counterexample exploits, is
that the `L + 1` time is itself near.

### 2.2 The constancy, and the timing law

**The range 56–65 is the complement of the ascent.** Writing `δ` for the distance from the basepoint
to the nearest time at `L + 2` or below and `e` for the arm index of the running arm's first ascent
to `L + 9`, the census gives

* `δ + e = 169` at **228** of the 229 (the remaining one has `δ + e = 391`), and `δ ∈ [56, 65]`
  exactly because `e ∈ [104, 113]` there;
* `δ + k = 99` at the same 228, where `k` is the arm index of the `Ceil72` valley; and `e − k = 70`
  at 228 (152 at the one exception);
* the peak of the `Ceil72` witness is at level `L + 6` at all 229, the valley at `L + 3` at all 229;
* the three nearest low times are spaced by the readings' own constants: the nearest at `L + 1`
  minus the nearest at `L + 2` is **239** or **577**, and the nearest at the floor minus the nearest
  at `L + 1` is **577** or **1393**.

Every one of these numbers is a value of the timing law: `z 6 − 1 = 70`, `z 7 − 1 = 169`,
`z 8 − 1 = 408`, and `239 = 169 + 70`, `577 = 408 + 169`, `816 = 239 + 577`, `99 = 169 − 70`. So the
answer to *is 56–65 expressible in the timing law* is **yes**, and it is the shadow of an
`ivSep`-type statement across the basepoint: `low_nine_sep` (`HPC/Fold/Distance71.lean`) proves that
a time at `L + 2` or below and a link carrying `L + 9` are at least 169 steps apart, and
`nearLow_ascent_sep_armG` reads this across the basepoint as `δ + e ≥ 169`. On the corpus the bound
is attained with **equality** — which is the whole of the constancy, and is a conjecture about
Bing's chains, not a theorem.

**And the shadow runs the other way as a theorem.** The reading of §2.1 gives, as proved statements
(`HPC/Fold/Distance71.lean`):

> `nearLowT_of_nearLow1T_armG` (mirror `nearLowG_of_nearLow1G_armT`): at a high-run crossing, a time
> of the pair at `L + 1` or below within **306** steps before the basepoint gives one at `L + 2` or
> below within **67**.
>
> `nearLow1T_of_nearFloorT_armG` (mirror): a time at the floor within **883** steps gives one at
> `L + 1` or below within 306; and the two compose, `nearLowT_of_nearFloorT_armG`.

The mechanism is the one the census sees: the pairing puts its valley at least 239 steps after the
low time (`169 + 70`) and at least 169 steps before the ascent, and the **high run** puts it before
the basepoint, because the running arm has nothing at `L + 2` or below between the basepoint and its
ascent. The constants are exactly tight: `306 = 239 + 67`, `883 = 577 + 306`. On the corpus the
`L + 1` hypothesis holds at 212 of the 220 crossings that have such a time (295 to 306 against 306;
8 lie beyond, at up to 642, and 9 crossings have no such time at all), and the floor hypothesis at
190 of 202. At the counterexample of §0 the spacing relations still hold — 424 − 185 = 239,
1001 − 424 = 577 — and it is the hypothesis, not the reading, that fails.

`s3_span_nine_mid5_of_cross_highRun_low1_armG` and its mirror are the batch-70 assembly restated on
this weaker hypothesis.

### 2.3 A reading of the ceiling clause that does not go through a low time

**First, what the clause actually asks for.** `Ceil72` on an arm of the band is equivalent to a
single landmark pair before the arm's **first** ascent:

> `Valley3BeforeNine f L` — a peak at `L + 6` or above at arm index three or more, a time at `L + 3`
> or below five steps later, and every ascent to `L + 9` at least six steps after that —
> `ceil72_of_valley3BeforeNine` and `valley3BeforeNine_of_ceil72` (`HPC/Fold/Distance71.lean`).

**Second, the level is forced.** On a running arm the valley of that pair is at level **exactly**
`L + 3` (`valley_eq_three_of_run`): the run forbids `L + 2` and below before the ascent and the
clause asks for `L + 3` or below. The census confirms it at all 229 (the low landmark is at level
`L + 3` at every one), and so does the counterexample.

**Third, which landmark each reading fails to place.** The peak is cheap: the census finds it at
level `L + 6` at all 229, at arm index 23 to 178, and `Mid2Floor` — which the crossing supplies
(`crossMid2`) — produces a peak at `L + 6` or above at index three before every descent to `L + 2`.
The **valley at exactly `L + 3`, before the ascent** is the landmark no reading places:

* a crookedness pairing returns an upper bound `ρ r' ≤ ρ a + 1` only for the lower of its two
  endpoints `a`, so to return a time at `L + 3` or below it needs an endpoint at `L + 2` or below;
* on the running arm there is none before the ascent (that is the high run), so the endpoint lies
  before the basepoint or after the ascent;
* the pairing places its landmarks strictly **between** its endpoints, so an endpoint after the
  ascent puts the valley after the ascent, where the clause cannot use it; and an endpoint before the
  basepoint places the valley between it and the ascent — before the basepoint unless the endpoint is
  near, which is exactly the distance hypothesis, and exactly the index bound `67` (the peak must
  land at arm index three, and the pairing puts it 70 steps after the endpoint);
* the readings the commission names do not help: the running arm's ascent against a **high** time of
  the partner (`L + 7` or above) pairs two levels that are two apart at best when read for a valley
  at `L + 3`, and returns nothing at `L + 3`; `w8` on the running arm fires only at times at `L + 2`
  or below, which the run excludes before the ascent; `wb` and `w3` are clauses of the *partner*.

**What does place it at the counterexample.** `check71.py` reads the landmarks of the running arm at
the 290-link witness: the peak is at arm index 29 at level `L + 6` and the valley at arm index 34 at
level `L + 3`, and the reading of least span that names that valley is the descending pairing from a
link carrying `L + 5` **36 steps before the basepoint on the running arm's own side** to the far low
time at `L + 2`, 185 steps past the basepoint (span 221). That reading has the right level — from
`L + 5` down to `L + 2` the valley is at `L + 3` — and no index bound at all: crookedness places the
valley somewhere between the two endpoints, and nothing in the clause says on which side of the
basepoint. So the question the branch now faces is not *where is the low time* but *how far after the
`L + 5` link does the pairing's valley sit* — a lower bound of five steps is immediate from the
timing law, and an upper bound is what is missing.

### 2.4 Break it — the construction

**It works.** `break-batch71.c` takes the 64 stored high-run crossings of `census-batch71.c` (one per
distinct configuration, `seeds-batch71.txt`, 986 to 2378 links) and applies three families of edit to
the partner's approach to the basepoint:

| edit | tried | faithful | still a high-run crossing | largest distance reached |
| --- | --- | --- | --- | --- |
| `raise` — lift a local minimum at `L + 2` or below out of the band | 1576 | 68 | 66 | 65 |
| `splice` — insert the Bing block `bpath(v, hi)` followed by `bpath(hi, v)`, which never descends below `L + 3` | 5039 | 1467 | 1347 | 75 |
| `stretch` — reflect and re-append a stretch of the approach that stays at `L + 3` or above | 536 | 536 | 472 | **185** |
| `band` — the same splice with `hi = L + 9`, a whole crooked chain of the sub-band | 1881 | **0** | 0 | — |

9032 edits, 2071 faithful, 1885 still with a high-run crossing, and **2229 high-run crossings at
which the distance fails** — at every one of which all three readings of `NearLowBandT` fail (the
nearest time at `L + 1` or below is 307 to 424, against 166; the nearest at the floor 884 to 1001,
against 405). Every edited pair is re-tested for `IsCrookedIvF` and re-scanned from scratch for
crossings; nothing is inherited from the seed. `min-batch71.c` then trims the most extreme break to
the 290-link window the kernel checks.

**Which edit breaks it, and which does not.** The obstruction crookedness offers is real but partial:
`raise` almost always destroys faithfulness (68 of 1576 survive) — removing a low time from a crooked
chain is what crookedness forbids — and `band`, the largest addition, **never** survives (0 of 1881):
a whole `L + 3 → L + 9 → L + 3` Bing block spliced into the approach cannot be crooked against the
material around it. What survives is the edit that adds no new level pattern at all: reflecting a
stretch of the approach and re-appending it, which is locally the chain retracing its own steps.
That is what pushes the low time from 60 steps to 185.

**And the pair still folds**, as `S3` requires: at all 2229 crossings some walk of the four-leg
family serves both arms, both arms satisfy the `w72` sentence, and `Ceil72` holds on both arms.

### 2.5 Both arms running high

`BothHighRunL5 ρ i L` — both arms reach `L + 9` with nothing at `L + 2` or below before the ascent —
is **named** (`HPC/Fold/Distance71.lean`) and measured:

| | |
| --- | --- |
| basepoints of the branch at which both arms run high | **16 235** of 2 444 297 |
| crossings of the trichotomy at which both arms run high | **0** of 1351 |
| high-run crossings at which the partner runs high too | **0** of 229 |

So the configuration is inhabited in the branch but never at a crossing, on this corpus. It is not a
theorem that it cannot happen, and this batch does not claim one; what is proved is the half that
follows from the batch-68 readings:

> `w8_of_cross_of_bothHighRun`: at a crossing, if both arms run high then one of them is a `w8` arm.

If neither were, the high run of each arm would put the *other* on `w3` (`leg4Land_w3_armT_of_highRun_armG`
and its mirror), and `w3` would serve both arms, which a crossing forbids. So the only shape
`BothHighRunL5` can take at a crossing is the one the census finds empty — the `w8` side running high
with the partner running high as well — and the missing step, unproved, is that a `w8` arm cannot run
high while its partner does. Since the partner's ceiling clause is `ceil72_of_deepFirst2_armT` in
every other case, closing that step would discharge the partner's clause in general.

### 2.6 Assembly

Not due: §2.1–2.4 do not close the distance, they refute it. The assembly of batch 70 stands as a
conditional theorem, and `s3_span_nine_mid5` is still `sorry`. What the branch at `L + 5` owes at a
high-run crossing is now stated in its sharpest form, and it is not a distance:

> **the running arm has a peak at `L + 6` or above at arm index three or more and, five steps later,
> a time at `L + 3` — necessarily exactly `L + 3` — at least six steps before its first ascent to
> `L + 9`** (`Valley3BeforeNine`, equivalently `Ceil72`).

The census sees it at all 229 crossings of the corpus and at all 2229 crossings of the construction,
including every pair at which the distance fails.

## 3. Deliverables

1. **What is proved, `sorry`-free, with `#print axioms`** (`axioms-batch71.txt`; every profile a
   subset of `[propext, Classical.choice, Quot.sound]`, two of them without `Classical.choice`; no
   `native_decide`, no `axiom`, no `implemented_by`).
   * `HPC/Fold/Distance71.lean`: `Valley3BeforeNine` with `ceil72_of_valley3BeforeNine` and
     `valley3BeforeNine_of_ceil72`; `valley_eq_three_of_run`; `low_nine_sep` and
     `nearLow_ascent_sep_armG`; the definitions `NearLow1T`, `NearLow1G`, `NearFloorT`, `NearFloorG`
     with `highRunG_link`, `highRunT_link`, `nearLowT_of_nearLow1T_armG`,
     `nearLowG_of_nearLow1G_armT`, `nearLow1T_of_nearFloorT_armG`, `nearLow1G_of_nearFloorG_armT`,
     `nearLowT_of_nearFloorT_armG`, `nearLowG_of_nearFloorG_armT`;
     `s3_span_nine_mid5_of_cross_highRun_low1_armG` and its mirror; `BothHighRunL5` with
     `w8_of_cross_of_bothHighRun`.
   * `HPC/Fold/Audit71.lean`: `NearLowBandCrossL5` and its refutation `not_nearLowBandCrossL5`, with
     the witness `Audit71.rho290`, `Audit71.sig290` and the kernel-checked facts `faithful`, `lip`,
     `band_lo`, `band_hi`, `base_level`, `lowAt_armG`, `lowAt_armT`, `not_w8_armG`, `not_wb_armT`,
     `not_w3_armT`, `cross`, `highRun_armT`, `not_nearLowBandG`.
2. **The table of §2.1 and the construction of §2.4, under the audit protocol.** `census-batch71.c`
   (log `census-batch71.log`, rows `census-batch71-rows.csv`) evaluates `IsCrookedIvF`, `LowAt`,
   `Leg4Land` (greedy, with the literal reading sampled against it — 596 samples, 0 disagreements),
   `DeepFirst2`, `Ceil72`, `Deep72`, `Mid2Floor`, `NineBeforeDeep` and the crookedness readings each
   by its own definition; it is a census over whole pairs and whole arms, so **no arm-length bound
   applies** (the arms seen run from 105 to 2211 times). `break-batch71.c` and `min-batch71.c` re-test
   every edited pair for faithfulness and re-scan it from scratch. The finding is re-checked
   independently by `check71.py` (log `check71.log`) on both stored witnesses, and by the Lean kernel
   on the shorter one.
3. **This report**, whose first line names the commission read, with the counterexample first, then
   the targets, then the six questions.

## 4. What is now open

The branch at `L + 5` no longer owes a distance; it owes `Ceil72` on the running arm of a high-run
crossing, equivalently one landmark pair before the arm's first ascent, and the census has never seen
it fail — 229 crossings of the corpus, 2229 of the construction, and every basepoint of the branch at
which it was measured. The reading that places its valley when no low time is near is identified in
§2.3 and needs one index bound; whether that bound is derivable is the natural next question, as is
the missing half of §2.5.
