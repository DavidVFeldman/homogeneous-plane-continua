# Report: batch 58 — the criteria of the four-leg family do not close the branch `L + 5`

## 0. The refutations, first

Three statements are refuted in this batch, all at explicit faithful witnesses whose faithfulness
is itself proved in the kernel. The new Lean files are `HPC/Fold/Leg4Crit.lean` (the criterion as a
predicate), `HPC/Fold/Leg4Scan.lean` (the linear scan that makes long arms affordable),
`HPC/Fold/PairCheck.lean` (the faithfulness search, stated once for a pair of any length),
`HPC/Fold/Audit58.lean` (the witnesses and the three refutations) and `HPC/Fold/CoverL5Low.lean`
(the one positive fact, §1).

### 0.1 The walk question 1 names has no criterion the branch supplies

`Walk47181CritL5` is the statement that the criterion of `L+4 → L+7 → L+1 → L+8 → L+1` — the wide
engine `foldsOnto_leg4W` at `(P, K, M) = (L + 5, L + 7, L + 1)` — holds on both arms at every
basepoint of the branch `L + 5`. **`not_walk47181CritL5` is a theorem**: it is false.

The scale of the failure is the point. Over the 3 091 444 arms of the branch in the corpus:

| announcement of `L+4 → L+7 → L+1 → L+8 → L+1` | arms at which it fails |
|---|---|
| the base condition | 0 |
| `hfloor` (the descents to `L + 2`) | 436 124 |
| `hdeep` (the descents to `L + 1`) | **2 254 153** |
| `hceil` (the ascents to `L + 9`) | 444 998 |
| all three hold | 355 633 |

and the criterion holds on **both** arms at **145** of the 1 545 722 basepoints, while the *walk*
serves **878 410** of them. So the walk is good and its criterion is not: the criterion of the
engine is sufficient for the fold and very far from necessary.

### 0.2 No parameter set of the family does better — the criteria do not close the branch

`Leg4CritClosesL5` is the statement that at every basepoint of the branch *some* parameter set of
the engine's window has its criterion on both arms, read either on the arms or on their reflections
in the level `L + (L + 9)`. **`not_leg4CritClosesL5` is a theorem**: it is false.

The witness is the window of Bing's chain `bing 0 9` (986 links) beginning at its link 811, 175
links long, whose first link stands at `L + 5`. It is thin, hence a chain of Bing's own family; the
basepoint is its first link, so its backward arm is that link alone and nothing is hidden there.
Its forward arm fails the criterion of **all twenty-nine** parameter sets of the window, in both
orientations, and the clause that fails is named in each case: the base condition at 23 of the 58
(set, orientation) pairs, the floor announcement at 25, the deep-floor announcement at 10. This is
the shortest such arm in the whole corpus — the census bisects for it at every basepoint — so it is
not an artefact of a bad cut.

The refutation is affordable because of `HPC/Fold/Leg4Scan.lean`. Each clause of the criterion says
*for every trigger `d`, one of a handful of increasing chains of landmarks is completed strictly
before `d`*; deciding that naively costs a cube in the length of the arm, out of reach of the
kernel at 175 links, but a chain of at most three links is recognised by one left-to-right scan
carrying one flag per link. `chainScan` is that scan, `chainScan_one/two/three` say what its flags
mean, and the three lemmas `not_leg4CritG_of_floor`, `not_leg4CritG_of_deep`,
`not_leg4CritG_of_ceil` refute a clause from a trigger and its scans at linear cost.

### 0.3 The interval reading is not sufficient

`Leg4CritIvSufficient` is the engine with every landmark "at `l` or above" read on the upper end
`σ` of a link and every landmark "at `l` or below" on the lower end `ρ`, the triggers left on `ρ`.
**`not_leg4CritIvSufficient` is a theorem**: it is false, and the witness is small — a nine-link
faithful arm:

```
ρ = 5 4 5 5 5 4 5 4 3        σ = 5 4 5 6 5 4 5 4 3
```

at `(P, K, M) = (L + 6, L + 7, L + 4)`. Its floor announcement is served on the interval by the
link at index three, whose interval reaches `L + 6` although its `ρ` sits at `L + 5`; the point
reading fails there, and the arm does not fold onto `L+5 → L+7 → L+4 → L+8 → L+1`. On the corpus
the interval reading holds on **61 644** arms that do not fold.

No §1 target is refuted: all three statements are about the route, not about the commissioned
statements.

---

## 1. The targets

1. **`s3_span_nine_mid5` (`Mixed.lean`) — not proved.** What is added is one positive fact and
   three exclusions. The positive fact is that the branch hypothesis *is* one of the three
   announcements of one walk of the family (§2.1); the exclusions are §0.
2. **`s3_span_nine` (`General.lean`) — not proved**, since it waits on the branch `L + 5`.
3. **`s3_general`, `theorem3` — not proved.**

| result | file | status |
|---|---|---|
| `Leg4Window`, `Leg4CritG`, `Leg4Crit` — the engine's window and criterion as predicates | `HPC/Fold/Leg4Crit.lean` | definitions |
| `foldsOnto_of_leg4Crit` — the engine with the criterion as one hypothesis | `HPC/Fold/Leg4Crit.lean` | proved |
| `chainScan`, `chainScan_one/two/three` — the linear scan for an increasing chain | `HPC/Fold/Leg4Scan.lean` | proved |
| `not_leg4CritG_of_base/floor/deep/ceil` — refuting a criterion from its scans | `HPC/Fold/Leg4Scan.lean` | proved |
| `PairCheck.isCrookedIvF_of_search` — faithfulness of a pair of any length, by search | `HPC/Fold/PairCheck.lean` | proved |
| `Audit58.faithful` — the 175-link witness is faithful | `HPC/Fold/Audit58.lean` | proved |
| `not_walk47181CritL5` — the named candidate has no criterion the branch supplies | `HPC/Fold/Audit58.lean` | proved |
| `not_leg4CritClosesL5` — no parameter set of the window does | `HPC/Fold/Audit58.lean` | proved |
| `not_leg4CritIvSufficient` — the interval reading is not sufficient | `HPC/Fold/Audit58.lean` | proved |
| `down1_of_lowAt`, `foldsOnto_walk63718_of_lowAt`, `s3_span_nine_mid5_of_ascents` | `HPC/Fold/CoverL5Low.lean` | proved |

---

## 2. The questions

### 2.1 Question 1 — the walk that reads `L + 6`

**No, and the failing announcement is not the floor one.** The report of batch 57 named
`L+4 → L+7 → L+1 → L+8 → L+1` because its floor announcement consumes exactly the pair of links the
crookedness clause returns — a time at `L + 3` then one at `L + 6`. That much is right: the floor
announcement is the *least* often violated of its three. What the branch does not supply is the
**deep-floor** announcement, which fails at 2 254 153 of 3 091 444 arms — 73 per cent. Read at
`(P, K, M) = (L + 5, L + 7, L + 1)` with `H = L + 9` it asks, before every descent to `L + 1`, for

* a prior time at `L + 9`, or
* a prior time at `L` followed by one at `L + 7`, or
* a prior time at `L + 8`, then one at `L + 1`, then one at `L + 7`,

whereas the branch hypothesis `LowAt (L + 1) (L + 8)` offers, before every descent to `L + 1`,

* a prior time at `L + 8`, or
* a prior time at `L + 2` followed by one at `L + 6`.

Every disjunct of the announcement is one level above the corresponding disjunct of the hypothesis
— `L + 9` against `L + 8`, `L` against `L + 2`, `L + 7` against `L + 6` — which is the same one
level batch 57 measured, now appearing in the *valley* parameter rather than in the peak.

**And the second half of question 1 is answered by the same table: the peak is not what matters,
the valley is.** Lowering the peak `K` from `L + 7` to `L + 6` at `M = L + 1` changes nothing (the
criterion still holds on both arms at 0 basepoints); raising the valley `M` does everything:

| direct parameter set | walk | criterion on both arms |
|---|---|---|
| `(P, K, M) = (L+5, L+7, L+1)` | `L+4 → L+7 → L+1 → L+8 → L+1` | 145 |
| `(P, K, M) = (L+5, L+7, L+2)` | `L+4 → L+7 → L+2 → L+8 → L+1` | 260 422 |
| `(P, K, M) = (L+5, L+7, L+3)` | `L+4 → L+7 → L+3 → L+8 → L+1` | 793 095 |
| `(P, K, M) = (L+5, L+6, L+3)` | `L+4 → L+6 → L+3 → L+8 → L+1` | 697 208 |
| reflected `(P, K, M) = (L+4, L+6, L+2)` | `L+6 → L+3 → L+7 → L+1 → L+8` | **933 197** |

out of 1 545 722 basepoints. The reason the last is best is a theorem, not a statistic:

> **The branch hypothesis is one of that walk's three announcements.**
> `foldsOnto_walk63718` asks for the ascents to `L + 8`, the ascents to `L + 9` and the descents to
> `L + 1`; the third is `LowAt (L + 1) (L + 8)` with one extra disjunct offered. So at the branch
> the walk asks for **two** announcements, both about ascents
> (`down1_of_lowAt`, `foldsOnto_walk63718_of_lowAt`, `s3_span_nine_mid5_of_ascents`).

Its two remaining announcements fail at 313 046 arms (the ascents to `L + 8`) and 511 199 arms (the
ascents to `L + 9`) of the 3 091 444 in the corpus, and its descent announcement fails at **none**,
which is what the theorem says. **That is what the branch has left to prove**, and it is now a
statement about ascents alone, at a single walk, with the hypothesis already spent.

But it will not be enough by itself, and §0.2 says why: no parameter set repairs the arms this one
misses, so a *criterion* of the engine cannot be the whole of the branch. Either the two ascent
clauses must be derived from crookedness for this walk in particular (the criterion is sufficient,
so nothing more is needed at the 933 197 basepoints it already serves, and the question is what
holds at the remaining ones), or the engine needs a criterion nearer to being necessary.

### 2.2 Question 2 — the form exhaustiveness takes at `L + 5`

**It cannot take the form it took at `L + 4`, because the engine's criteria are not exact.** At
`L + 4` exhaustiveness was two arm-only dichotomies plus the crossings: every arm either folds onto
a canonical walk or fails a clause, and the failures cross. The corresponding statement at `L + 5`
would be: every arm of the branch either meets the criterion of one of a finite list of walks, or
fails a clause whose failure the partner arm's criterion consumes. §0.2 refutes the first half of
that in the strongest available form — there is an arm of the branch meeting **no** criterion of the
whole four-leg window — and the census shows the gap is not the walks' fault: every one of the 867
basepoints that the five reflected three-turn walks miss *is* served by a walk of the family, and a
greedy cover of them needs three walks; but a greedy cover of the branch by *criteria* leaves
2 804 of 200 000 sampled basepoints unreachable however many criteria are allowed.

So the answer to "which set of clauses closes the arms at `L + 5`" is: not a set of criteria of
this engine. Three things follow for the shape of any induction on the span.

* **The clauses do reflect; the criteria do not transport across the reflection of the model.** The
  census evaluates each parameter set in both orientations and they are genuinely different
  statements at the same basepoint: the direct sets with `P = L + 3` and the reflected ones with
  `P = L + 6` are excluded by the base condition alone, and of those that survive, the best direct
  set and the best reflected set serve 793 095 and 933 197 basepoints and neither contains the
  other.
* **An exact criterion is what an induction on the span would need.** The engine's criterion is
  sound — over the 400 000 sampled arms at which it holds, the arm folds every time, which is
  `foldsOnto_leg4W` on the corpus — and far from complete. Until a criterion is proved equivalent
  to the fold, "the list of walks is exhaustive" cannot be reduced to "the list of criteria is
  exhaustive".
* **What survives is the timing law and the identification of §2.1.** `ivSep` is stated at any
  level distance, and `down1_of_lowAt` shows the branch hypothesis is literally an announcement of a
  walk — the first time in this development that a branch hypothesis and a walk's criterion have
  been matched clause for clause. That identification is span-independent in form, and is the
  candidate for the inductive data.

### 2.3 Question 3 — the criteria's tolerance

**The necessity half survives and the sufficiency half does not, so the level of §0 of batch 57 is
not bookkeeping.** The interval reading — `σ ≥ l` in place of `ρ ≥ l`, and `ρ ≤ l` in place of
`σ ≤ l` — is *weaker* than the point reading, so any necessity statement it has is implied by the
point one (`leg4CritG_of_leg4Crit`). What fails is the engine: §0.3 exhibits a nine-link faithful
arm that meets the interval criterion and does not fold, and on the corpus the interval reading
holds at **61 644** arms that do not fold, against **0** such arms for the point reading.

And the interval reading does not even buy much where it is safe: the number of basepoints with
*no* parameter set whose criterion holds falls only from 15 078 to 13 068 out of 1 545 722. So the
answer is negative on both counts the question raises — the engines do not survive the reading, and
the reading does not close the gap the point form leaves.

The contrast with batch 57 is worth recording, because it is the same level read at two different
places. There the interval reading *saved* the criterion: at every one of the 485 pairs where the
V-criterion on the partner arm fails in point form, it holds in interval form, and 0 fail in
interval form. Here the interval reading breaks the engine. The difference is which side of the
implication the level sits on: `cross_high_fwd_far` *produces* a link whose interval meets a level,
and the engine *consumes* a point at a level. A level produced on the interval cannot be fed to a
consumer that reads the point, and widening the consumer makes it unsound.

---

## 3. The census

`census-batch58.c`, log `census-batch58.log`; same generators, same faithfulness test, same fold
program and the same audit protocol as batches 56 and 57. 4 924 faithful pairs, 6 598 939 links,
47 918 non-thin; 1 228 346 basepoints of the branch `L + 4` and 1 545 722 of the branch `L + 5`.
The whole batch-57 block is re-run unchanged and its three theorems fail nowhere (valley failures
236 658 with 0 misses of the V-walk, ceiling gap 0, `CeilHighResidual` 0, unserved pairs served by
none of `w₃`, `w₄`, `w₅`: 0).

What is new is the evaluation of the criteria. At every basepoint of the branch `L + 5`, for each
of the 29 parameter sets of the engine's window and each of the two orientations, the base
condition and the three announcements are evaluated on each arm, in point form and in interval
form, and the clause that fails is recorded.

| corpus | basepoints | some criterion on both arms | none | none, interval form | interval criterion without the fold |
|---|---|---|---|---|---|
| thin chains | 464 | 460 | 4 | 4 | 0 |
| single shavings | 133 462 | 132 306 | 1 156 | 1 148 | 1 172 |
| single fills | 133 632 | 132 480 | 1 152 | 1 152 | 0 |
| random mixtures (1/3) | 16 641 | 15 984 | 657 | 111 | 17 691 |
| heavy mixtures (1/2, and the total mixture) | 16 011 | 14 596 | 1 415 | 70 | 32 703 |
| faithful perturbation walks | 929 | 921 | 8 | 8 | 200 |
| outside Bing's family, and concatenations | 1 244 583 | 1 233 897 | 10 686 | 10 575 | 9 878 |
| **all** | **1 545 722** | **1 530 644** | **15 078** | **13 068** | **61 644** |

The sound direction is sampled as a check on the transcription: over 400 000 samples of an arm
meeting a criterion in point form, the arm folds onto the walk every time (0 failures), which is
`foldsOnto_leg4W` on the corpus.

The greedy cover of the branch by criteria, over the first 200 000 basepoints recorded: six point
criteria reach 197 196 of them and four interval criteria reach 198 338; the rest are reachable by
no criterion at all. The shortest arm of the branch meeting no criterion, found by bisection at
every such basepoint, is the 175-link window of `bing 0 9` at its link 811 that `Audit58` carries.

**Definition audit.** Every predicate the census is offered as evidence for is evaluated by its own
definition, none by a proxy: `IsCrookedIvF` (`le`, `width`, `adj`, and the crooked clause with
interval triggers); `IsLip`; `HighAt (L+1) (L+8)`; `LowAt (L+1) (L+8)`; `Leg3Valley`; `Leg3Ceil`;
`Valley5`; `TopW5`; `armRefl`; `FoldsOnto` by the dynamic program of `HPC/Fold/Decide.lean`, for
every walk named; the three residues. The criteria are the three announcements of `foldsOnto_leg4W`
together with its base condition, written out at `L = 0`, `H = 9` and the parameter set
`(P, K, M)`; the interval form is the same with every high landmark read on `σ` and every low
landmark on `ρ`, the triggers left on the point sequence, and is reported as such.

---

## 4. Deliverables and audit

1. **Proved, `sorry`-free.** Five new files: `HPC/Fold/Leg4Crit.lean`, `HPC/Fold/Leg4Scan.lean`,
   `HPC/Fold/PairCheck.lean`, `HPC/Fold/Audit58.lean` (generated by `gen-audit58.py`) and
   `HPC/Fold/CoverL5Low.lean`. All are in `HPC.lean`; `lake build HPC` is clean; no `sorry`, no
   `native_decide`, no new `axiom`, no `@[implemented_by]`. Of the earlier files only `Mixed.lean`
   changes, and only in the docstring of `s3_span_nine_mid5`.

   ```
   'HPC.Fold.not_leg4CritClosesL5'        depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.not_walk47181CritL5'         depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.not_leg4CritIvSufficient'    depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.Audit58.faithful'            depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.foldsOnto_of_leg4Crit'       depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.foldsOnto_walk63718_of_lowAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.s3_span_nine_mid5_of_ascents' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

2. **Census over the general model, under the audit protocol**: `census-batch58.c`, log
   `census-batch58.log`. Every statement it reports about a basepoint of the branch is read on both
   arms of the pair; the per-arm clause tallies say so where they are per-arm.

3. **Still open**: `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`. The sorries of the
   route are unchanged in number. What changed is that the route through the criteria of the
   four-leg family is closed by a theorem rather than by a measurement, and that the branch's
   remaining obligation is now a single walk and two announcements about ascents.
