# Report: batch 53 — the ceiling crossing, the branch `L + 5`, and Bing's seam

Two new Lean files, `HPC/Fold/CeilArm.lean` and `HPC/Fold/CeilCross.lean`, both `sorry`-free;
`HPC.lean` gained the two imports and nothing else was touched. `lake build HPC` is clean. Every
new theorem depends only on `propext`, `Classical.choice`, `Quot.sound`; there is no
`native_decide`, no `axiom`, no `@[implemented_by]`, and no new `sorry`. The censuses are
`census-batch53.c` with the log `census-batch53.log` and the sample file
`census-batch53-sample.txt`.

## 0. No counterexample

**No counterexample was found to any of the four targets, and none is claimed.** Over the corpus
below — 3 545 faithful pairs, 5 770 720 links of which 18 698 non-thin (0.324 %), 1 068 536
basepoints of the branch `L + 4` and 1 356 118 of the branch `L + 5` — every statement of §1 holds
wherever it is tested: the work item `unserved_three_walks` at all 321 382 unserved pairs of the
branch `L + 4`, `cross_ceil_sentence` at all 192 configurations it speaks of, and
`cross_valley_profile` at all 205 652.

## 1. The targets

### 1.1 `cross_ceil_sentence` — reduced to two clauses, and proved outside two configurations

Not proved; what the batch does is cut it down to two clauses and prove those across the
basepoint except in two named local configurations.

**The arm-level halves (`HPC/Fold/CeilArm.lean`).** Three theorems about a single 1-Lipschitz arm
of the band `[L, L + 9]` based at `L + 4`, with the two crookedness clauses:

* `valley5_of_not_leg3Ceil` — an arm that **fails** `Leg3Ceil` satisfies `Valley5`. A descent to
  `L + 1` before the unprepared ascent would, by one application of `CrookUp`, produce exactly the
  two landmarks `Leg3Ceil` asks for; so every descent to `L + 1` comes after the ascent, and the
  ascent itself is the deep peak `Valley5` wants. (Census: of the 52 638 branch basepoints with an
  arm failing `Leg3Ceil`, **no** such arm fails `Valley5`.)
* `valley5_or_vee` — an arm failing `Valley5` folds onto the V-walk based at `L + 5`. This is
  `leg3Valley_or_vee` of batch 48 with the deeper clause. (Census: 535 206 arms fail `Valley5`,
  every one of them folds onto the V-walk.)
* `topW5_or_lam` — an arm failing `TopW5` folds onto the Λ-walk based at `L + 3`. (Census: 222
  arms fail `TopW5`, every one folds onto the Λ-walk.)

In the configuration of the work item let `X` be an arm failing `Leg3Ceil` and `Y` the other one.
`X` folds onto the Λ-walk (`leg3Ceil_or_lam`), so `Y` does not; hence `Valley5 X` by the first
theorem and `TopW5 Y` by the third, and the sentence of `w₅` is short of exactly two clauses:
`TopW5 X` and `Valley5 Y`. That pair is `CeilCrossGap`, and `cross_ceil_sentence_of_gap` derives
the work item from it — **with the second disjunct**: the ceiling case, if it holds at all, holds
by `w₅`. The censuses say the same: at all 192 configurations both arms satisfy the sentence of
`w₅` (and only 71 of them satisfy the sentence of `w₄`).

**The crossing (`HPC/Fold/CeilCross.lean`).** Both remaining clauses are one application of the
crookedness clause read across the basepoint, and each has one exceptional configuration:

> `ceil_cross_peak_fwd`, `ceil_cross_peak_bwd`: `Valley5` holds of the arm that does not fail
> `Leg3Ceil`, unless `ρ` stands at `L + 6` or above two or three steps to one side of the
> basepoint (`CeilPeakResidual`).
>
> `ceil_cross_high_fwd`, `ceil_cross_high_bwd`: `TopW5` holds of the arm that fails `Leg3Ceil`,
> unless `ρ` stands at `L + 7` or above exactly four steps to one side of the basepoint
> (`CeilHighResidual`).

For the valley half the clause is applied between the failing descent of `Y` and the unprepared
`L + 8` of `X`; it returns a peak at `L + 6` and, seven steps later, a time at `L + 2`. On `X`'s
side those two are exactly the landmarks `Leg3Ceil` asks for — and `X` has none — so the peak lies
on `Y`'s side, where the only thing that can go wrong is its distance from the basepoint: the
criterion wants index four, and the Lipschitz bound allows the peak to sit at index two or three.
For the ceiling half the clause is applied between the descent at which `Y` fails to fold onto the
Λ-walk and the time at `L + 9` at which `TopW5` fails on `X`; it returns a peak at `L + 7`, which
on `X`'s side is the landmark `TopW5` asks for and on `Y`'s side is the peak the Λ-criterion asks
for. Again only its index can go wrong, and only at distance exactly four, since a climb of three
levels takes four steps and the Λ-criterion asks for five.

With both excluded the work item is a theorem: `cross_ceil_sentence_of_not_residual`, whose two
extra hypotheses are about the four steps either side of the basepoint only.

**How much that covers.** Of the 192 configurations of the work item in the corpus, 183 avoid both
residues and are therefore theorems; 9 realise `CeilPeakResidual`, and none realises
`CeilHighResidual`. At all 192 the two remaining clauses hold (`TopW5` on the failing arm fails
zero times, `Valley5` on the other arm zero times), so `CeilCrossGap` is unrefuted over the whole
corpus.

`unserved_three_walks` is therefore still open: it needs the ceiling case *and* the valley case,
and the valley case is target 1.2.

### 1.2 `cross_valley_profile` — not proved, and its residue **is** realised

Not proved, and this batch changes what is known about it. `cross_valley_profile_of_not_residual`
(batch 50) proves the item for every pair avoiding `ValleyResidual`: `ρ` standing at `L + 2` two
or three steps to one side of the basepoint. Batch 52 reported that residue unrealised over its
corpus; that count was of an arm-level proxy (`residualValleyCase` of `census-batch52.c`), not of
the predicate `HPC/Fold/CrossValley.lean` states. Read as the definition reads it, the residue is
realised, and often:

| configuration | count |
| --- | --- |
| branch basepoints realising `ValleyResidual` | 267 877 |
| of those, with an arm failing `Leg3Valley` — the case the item is called on | 110 879 |
| of those, at which the conclusion nevertheless holds | 110 879 (all) |
| branch basepoints with an arm failing `Leg3Valley` | 205 652 |
| of those, at which both arms fold onto the V-walk | 205 652 (all) |

So `cross_valley_profile_of_not_residual` does **not** cover the general model: rather more than
half of the configurations the work item speaks of lie inside its exceptional case. The item
itself is unrefuted.

One sharpening was tried and is worth recording as a negative. The faithfulness clause
`IsCrookedIvF` allows the anchor level to be any level met by the interval `[ρ, σ]` at a time
*within one* of the trigger, so a neighbour of the low link dipping to `L + 1` would buy the
missing level. The census measures exactly that: at every one of the 267 877 residual basepoints
the low link at distance two or three is a weak local minimum at `L + 2` — no neighbour of it
meets a level at or below `L + 1`. The neighbour freedom therefore buys nothing here, and the
residue is not narrowed by it.

### 1.3 `s3_span_nine_mid5` — not proved

Nothing was added to the branch `L + 5` beyond the census of §2.1. The branch waits on a list of
walks, and §2.1 shows the list is longer than the three reflected walks and longer than any list
of three-turn walks.

### 1.4 `s3_span_nine`, `s3_general`, `theorem3` — not proved

Both branches of span nine are open, so these are untouched.

## 2. The questions

### 2.1 The list at the branch `L + 5`

**What serves the pairs the three reflected walks miss.** Of the 1 356 118 basepoints of the
branch `L + 5` in this corpus, 321 874 are unserved by the two reflected canonical walks; 321 692
of those are served by one of the three reflected walks and **182 by none**. For each of the 182
the census computes the shortest walk of at most three turns based within one of `L + 5` that
serves the pair, and then, when there is none, the shortest of at most four turns. The answer:

| walk | turns | times | shortest serving walk at |
| --- | --- | --- | --- |
| `5 → 7 → 1 → 8` | 3 | 16 | 69 pairs |
| `4 → 7 → 1 → 8` | 3 | 17 | 45 pairs |
| `5 → 6 → 8 → 1` | 3 | 11 | 14 pairs |
| `5 → 3 → 8 → 1` | 3 | 15 | 8 pairs |
| `6 → 7 → 8 → 1` | 3 | 10 | 4 pairs |
| `4 → 3 → 7 → 1 → 8` | 4 | 19 | 21 pairs |
| `5 → 7 → 3 → 8 → 1` | 4 | 19 | 10 pairs |
| `6 → 3 → 7 → 1 → 8` | 4 | 21 | 4 pairs |
| `5 → 3 → 7 → 1 → 8` | 4 | 20 | 4 pairs |
| `6 → 7 → 3 → 8 → 1` | 4 | 18 | 3 pairs |

Every one of the 182 is served, and the three reflected walks together with these ten serve every
unserved pair of the branch in the corpus. The substantive point is the second half of the table:
**42 of the 182 are served by no walk of at most three turns at all**, whatever its base and
levels. At the branch `L + 4`, by contrast, three walks of three turns each serve all 321 382
unserved pairs of the same corpus. So the two branches differ not only in which walks they need
but in the *shape* of the walks: the branch `L + 5` leaves the three-leg family altogether. Any
list for it, finite or not, contains walks of four turns.

Two cautions about that finding. It is a *census* result, decided by the dynamic program over
`FoldsOnto` of `HPC/Fold/Decide.lean` reimplemented in C, and not a machine-checked theorem: the
statement "no walk of at most three turns serves this pair" quantifies over 3 630 walks, and the
attempt to isolate a witness small enough for the Lean kernel failed. `search-batch53.c` (log
`search-batch53.log`) takes each such pair and shrinks the two arms to the shortest *prefixes* that
are still served by no walk of at most three turns — the properties that make the pair a pair of
the branch (1-Lipschitz, the band, the basepoint, `LowAt`, `CrookUp`, `CrookDown`) are all
inherited by prefixes, and so is the failure to fold, so a short unserved prefix pair would be a
witness. The shortest it finds has arms of 113 and 874 steps: the hardness of these pairs is not
local, and there is no small witness to decide in the kernel. The second caution is that both
counts — 182 and 42 — are of the corpus and not of the model.

**The σ-route.** The reflection of the general model sends `(ρ, σ)` to `(a − σ, a − ρ)`, so the
branch `L + 5` of `ρ` is the branch `L + 4` of `τ = 9 − σ`. The census reads the arms of `τ` at
every basepoint of the branch: at 1 352 395 of them `τ` stands at `L + 4`, at 1 062 505 of those
both `τ`-arms satisfy `HighAt (L + 1) (L + 8)`, and at **every one of those** one of the five
walks of the branch `L + 4` serves the `τ`-pair — no failure. The three walks of `L + 4`, read on
the arms of `σ`, do therefore serve every pair of the branch `L + 5`. What they do not deliver is
a fold of the arms of `ρ`: a fold read on `σ` puts the blocks inside four consecutive links and
not three (`HPC/Fold/LinkFold.lean`), which is exactly the one link the theorem has to spare and
does not. So the σ-route reaches the branch and loses a link on the way back, and nothing in this
batch closes that gap.

### 2.2 `cross_ceil_sentence`: does crookedness across the basepoint give it, and where does the
proof stop one level short?

It gives all of it except two clauses, and those two it gives except in the two configurations of
§1.1 — `CeilPeakResidual` at distance two or three, `CeilHighResidual` at distance four. Neither
is a level shortfall: both are *index* shortfalls, the clause returning a landmark at the right
level but too near the basepoint for the criterion's index bound. That is a different failure from
the valley crossing, where the shortfall is one level (`cross_valley_low3_fwd`: the clause reaches
`L + 3` where `L + 2` is wanted).

There is a level shortfall at the ceiling too, and the batch locates it exactly:
`topW5_low3` (`HPC/Fold/CeilArm.lean`). For an arm of the branch — one satisfying the branch
hypothesis `HighAt (L + 1) (L + 8)` — before every time at `L + 9` there are two landmarks with
the gaps `TopW5` asks for, the first at `L + 6` or above and the second at **`L + 3`** or below,
where `TopW5` asks for `L + 2`. The reason is visible in the statement: the branch hypothesis
supplies a time at `L + 2`, and the clause `CrookUp` returns a landmark within one of the level it
is triggered from, so a trigger at `L + 2` yields `L + 3` and only a trigger at `L + 1` would
yield `L + 2`. This is the same one level as everywhere else in the general model, and it is why
`TopW5` on the failing arm cannot be had from the arm alone: it has to be fetched from the other
side of the basepoint, which is what `ceil_cross_high_fwd` does, at the cost of the index residue.

### 2.3 The valley residue

Realised, in abundance: see the table in §1.2. It is not excluded in the general model, and no
generator had to be invented to reach it — the two thin chains alone realise it at 92
basepoints, 38 of them with an arm failing `Leg3Valley`, and every family of the corpus realises
it. The
consequence for the target is stated there: `cross_valley_profile` needs the configuration
handled, not merely survived, and the neighbour sharpening of the faithfulness clause does not
handle it (§1.2, last paragraph).

### 2.4 Bing's seam

**Not settled in this batch, and nothing is claimed about it.** The regroup-by-level move —
dissolve every block from `h_u` on and regroup the rest of `D` by level — was not implemented, so
the question of whether it succeeds at basepoint 6 of `bing 0 4`, and whether its failure is
exactly a seam block one link wider than the theorem allows, stands open.

What can be said, and is machine-checked, is that the theorem itself is comfortable at that
basepoint. `bing 0 4` is the 13-link chain of levels `0,1,2,1,2,3,2,1,2,3,2,3,4`; its basepoint 6
stands at level 2, with forward arm `2,1,2,3,2,3,4` and backward arm `2,3,2,1,2,1,0`. An
exhaustive search over the walks of at most three turns based within one of level 2 finds 152 that
fold both arms, the shortest being the ladder `1 → 2 → 3`. So both arms fold onto a common walk
there, and `exists_blocks_first_of_folds` turns that into blocks inside three consecutive links —
as `s3_span_eight`, a theorem of this repository since batch 41, already gives for every basepoint
of a chain of span four. Whatever failed at basepoint 6 in batch 24 was a failure of the
particular construction and not of Theorem 3 at that basepoint; the prediction of the commission's
question 4 is untested either way.

## 3. The censuses

`census-batch53.c` (log `census-batch53.log`, sample `census-batch53-sample.txt`), carried over
from `census-batch52.c`: the faithfulness test is `IsCrookedIvF` exactly as
`HPC/Fold/Faithful.lean` states it, and every fold is decided by the dynamic program over
`FoldsOnto` of `HPC/Fold/Decide.lean`.

**Generators.** The base chains `bing 0 9` and `bing 9 0` (986 links each), and from each: the
thin pair; every single shaving of a peak; every single fill of a valley; random mixtures at rate
1/3; heavy mixtures at rate 1/2; the total mixture; and a random faithful perturbation walk of 80
accepted single-link steps, which leaves the shaving/filling family altogether. Outside Bing's
family: the two concatenations `bing 0 9 + bing 9 0` and `bing 9 0 + bing 0 9` (1 971 links each),
both faithful, with their shavings, fills and total mixtures. Four recursive chains whose
splitting levels differ from Bing's (`vpath (back, fwd)` for `(1,2)`, `(2,1)`, `(2,2)` up and
down) were generated and **all four are unfaithful**, which is itself a small fact about the
model: the recursion's splitting levels are not free.

**Size.** 3 545 faithful pairs; 5 770 720 links, of which 18 698 non-thin — a fraction of
**0.00324**.

**The definition audit.** At every arm of every branch basepoint the census compares the landmark
sentence of each of the three walks with the verdict of the dynamic program: 6 411 216 checks,
**0 disagreements**. This is the audit of `foldsOnto_leg3deep_iff_landmark`,
`foldsOnto_w4_iff_landmark` and `foldsOnto_w5_iff_landmark` on the corpus, and it is what licenses
reading the sentence counts above as fold counts. The three arm dichotomies proved in this batch
were audited the same way (§1.1): 535 206 arms failing `Valley5`, every one of them folding onto
the V-walk; 222 failing `TopW5`, every one folding onto the Λ-walk; and, among the 52 638 branch
basepoints with an arm failing `Leg3Ceil`, no such arm failing `Valley5`.

## 4. What is left

* `CeilCrossGap` — `TopW5` on the arm failing `Leg3Ceil` and `Valley5` on the other arm — in the
  two residual configurations. Nine configurations of the corpus lie there; all nine satisfy it.
* `cross_valley_profile` inside `ValleyResidual`, which is where most of the model is.
* A list of walks for the branch `L + 5` that includes walks of four turns, and criteria for them
  of the kind batch 51 gave the three walks of the branch `L + 4`.
* The transfer of a fold of the arms of `σ` to a fold of the arms of `ρ` without losing a link.
* Bing's seam, question 2.4.

## 5. Axioms

`#print axioms` on every theorem added in this batch:

```
'HPC.Fold.valley5_of_not_leg3Ceil'            [propext, Classical.choice, Quot.sound]
'HPC.Fold.valley5_or_vee'                     [propext, Classical.choice, Quot.sound]
'HPC.Fold.topW5_or_lam'                       [propext, Classical.choice, Quot.sound]
'HPC.Fold.topW5_low3'                         [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_ceil_sentence_of_gap'         [propext, Classical.choice, Quot.sound]
'HPC.Fold.ceil_cross_peak_fwd'                [propext, Classical.choice, Quot.sound]
'HPC.Fold.ceil_cross_peak_bwd'                [propext, Classical.choice, Quot.sound]
'HPC.Fold.ceil_cross_high_fwd'                [propext, Classical.choice, Quot.sound]
'HPC.Fold.ceil_cross_high_bwd'                [propext, Classical.choice, Quot.sound]
'HPC.Fold.ceilCrossGap_of_not_residual'       [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_ceil_sentence_of_not_residual'[propext, Classical.choice, Quot.sound]
```

No `native_decide`, no `axiom`, no `@[implemented_by]`; `HPC/Fold/CeilArm.lean` and
`HPC/Fold/CeilCross.lean` contain no `sorry`, and the batch adds none anywhere else.
