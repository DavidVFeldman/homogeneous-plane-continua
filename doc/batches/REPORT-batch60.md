# Report: batch 60 — the branch `L + 5`, the arm-only half as a theorem

Written in the order the commission prescribes: counterexamples first, then §1 (targets), then §2
questions 1–3, then §3 deliverables.

## 0. Counterexamples and refutations

**None this batch.** Nothing in the batch-59 delivery was refuted, and no statement of this batch's
commission was found false. Both halves of question 1 came out affirmative and are now theorems,
and the arm-only measurements of the census agree with them everywhere.

One caution, carried from the batch-59 report and repeated here so it is not read as new evidence:
the census line about the reflection of `LowAt` is a stale label from batches 57–58 and is struck
from the audit; the commission already struck it.

## 1. The targets

| target | file | state |
| --- | --- | --- |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | still `sorry`, but now reduced to the *crossings* alone (`s3_span_nine_mid5_of_leg4TriCrossL5`, and against a list of five walks `s3_span_nine_mid5_of_leg4FiveCrossL5`) |
| `s3_span_nine` | `HPC/Fold/General.lean` | unchanged |
| `s3_general` | `HPC/Fold/General.lean` | unchanged |
| `theorem3` | — | unchanged, waits on `s3_general` |

What changed for the branch `L + 5` is the half of exhaustiveness that is about *one arm at a
time*. Batch 59 reduced the branch to `Leg4LandClosesL5` — "at every basepoint some parameter set
of the window has its landmark sentence on both arms" — and observed that with an exact criterion
this is decidable arm by arm. Batch 60 proves the arm-only half of it outright:

* **`leg4Land_tri` (`HPC/Fold/LandTri.lean`).** Every 1-Lipschitz arm of the band `[L, L + 9]`
  based at `L + 5` which satisfies the branch hypothesis `LowAt (L+1) (L+8)` satisfies the exact
  criterion `Leg4Land` of one of three walks:

  ```
  w8 : direct    (P, K, M) = (L+5, L+8, L+1)     L+4 → L+8 → L+1 → L+8 → L+1
  w3 : reflected (P, K, M) = (L+4, L+6, L+1)     L+6 → L+3 → L+8 → L+1 → L+8
  wb : reflected (P, K, M) = (L+4, L+6, L+2)     L+6 → L+3 → L+7 → L+1 → L+8
  ```

  so by `foldsOnto_leg4_of_leg4Land` it folds onto that walk.

* **`s3_span_nine_mid5_of_leg4TriCrossL5`.** What is left of the branch is exactly the
  *crossings*: a basepoint at which no one of the three serves *both* arms. `Leg4TriCrossL5` is
  that residue, written down, and the branch target follows from it.

So the branch `L + 5` is now in the state the branch `L + 4` was in after batch 48 plus the arm
half: the walks are exact, each arm has one, and only the pairing is open.

## 2. The questions

### 2.1 The two ascent clauses as arm-only dichotomies — yes, both, and more

The branch's best walk is `wb`, whose descent clause is the branch hypothesis
(`land_down1_of_lowAt_low`, batch 59). Read on the reflected arm its remaining two clauses are the
arm's ascents: the *floor* clause triggers on `f d ≥ L + 8` and the *deep* clause on `f d ≥ L + 9`.

**Measured first.** `probe60.c` enumerates every 1-Lipschitz arm of the band based at `L + 5` with
the branch hypothesis, exhaustively to length 12 and 14, and evaluates the landmark sentence of
every parameter set of the window on each arm (checked against the fold itself by the dynamic
program of `HPC/Fold/Decide.lean`: 0 disagreements). Of 1 773 593 arms of length at most fourteen,
425 020 fail the `L + 8` clause of `wb` and 205 035 fail the `L + 9` clause; **every one of them is
served by another walk of the family**, and one walk — `w8`, i.e. `L+4 → L+8 → L+1 → L+8 → L+1` —
serves every single arm that fails the `L + 8` clause. The census over the corpus
(`census-batch60.c`, log `census-batch60.log`) says the same on Bing's chains and their faithful
perturbations: of 3 491 920 arms of the branch, 299 436 fail the `L + 8` clause and 470 304 the
`L + 9` clause, all served by another walk, and `w8` alone covers every one of the 299 436.

**Then proved.** `HPC/Fold/LandTri.lean` turns the measurement into theorems:

* `leg4Land_w8_of_floor` — inside the band, the landmark sentence of `w8` *is* its floor clause:
  before every descent to `L + 2` a time at `L + 7` or above, at index at least four and at least
  `L + 7 - f d` steps earlier. Its other two clauses cannot trigger.
* `notW8_hi_after` — if `w8` fails, at a descent `d₀` to `L + 2` with no such earlier high time,
  then **every** time at `L + 8` or above is after `d₀`. (The index-four form of the clause makes
  the case `d₀ = 3` real, and it is handled: a time at `L + 8` at index three puts a time at
  `L + 7` at index four, which is the landmark.)
* `notW8_floor` — hence `d₀` itself is the landmark the ascent clause of `w3` and of `wb` asks for,
  and that clause holds. In particular **an arm that fails the `L + 8` clause of `wb` satisfies
  `w8`**: that is the first dichotomy, in contrapositive form.
* `notW8_ceil3`, `notW8_ceilWb`, `notW8_deep` — the branch hypothesis supplies the rest. Where a
  descent to `L + 1` is announced by its first disjunct (an earlier time at `L + 8`) the pair
  `(d₀, that time)` is the strong chain of `w3`; where it is announced by its second disjunct (a
  time at `L + 2` and then one at `L + 6`) that pair is the chain of `wb`; and if some descent
  needs the second disjunct then no ascent to `L + 9` can precede it, so the same pair, followed by
  the descent itself, is the three-link chain of `wb`'s deep clause.
* `leg4Land_tri` assembles these into the trichotomy.

So the answer to question 1 is yes for both ascent clauses, and the arm-only half of exhaustiveness
at `L + 5` is not merely a dichotomy per clause but a complete three-walk statement.

### 2.2 The crossings at `L + 5`

With the arm half proved, the residue is a pair whose arms are served by disjoint sets of the
three walks. The census measures it: of **1 745 960 basepoints** of the branch in the corpus,
**1 745 589** have one of the three walks serving both arms and **371** are crossings — one
basepoint in 4 700. Every one of the 371 is served by some walk of the family (none is unserved),
but no single walk serves all of them; the best are `L+4 → L+7 → L+2 → L+8 → L+1` and
`L+5 → L+7 → L+2 → L+8 → L+1`, each serving both arms at 331 of the 371, then
`L+4 → L+7 → L+1 → L+8 → L+1` at 299. Growing the list lowers the count: with
`L+4 → L+7 → L+2 → L+8 → L+1` added the crossings fall from **371 to 40**, and with
`L+5 → L+8 → L+1 → L+8 → L+1` added as well to **38** (a sixth walk, the reflected `(4,7,2)`, adds
nothing). `Leg4FiveCrossL5` and `s3_span_nine_mid5_of_leg4FiveCrossL5` are that smaller residue and
its reduction, so the branch now rests on 38 basepoints of the corpus rather than 1 745 960.

Structurally the crossing is narrow. The service sets of an arm are measured exhaustively in
`probe60b.c` (log `probe60b.log`): over the 14 742 992 arms of length at most sixteen the sets that
occur are

```
{w8} 3 703 351   {w3} 15 110   {wb} 1 034   {wb,w3} 2 729 203   {w8,w3} 395 912
{wb,w8,w3} 7 898 382                         and {} 0, {wb,w8} 0
```

and `{wb,w8}` never occurs without `w3` — an arm meeting `wb` and `w8` always meets `w3`. So a
crossing is one arm of the `{w8}` kind (it fails the shared ascent clause: it climbs to `L + 8`
before it has been at `L + 4`) against an arm of the `{w3}`, `{wb}` or `{wb,w3}` kind. Whether the
crookedness clause read at the arms' own levels and `ivSep` — the mechanism of batch 56 — closes
that configuration is exactly the open question the reduction now isolates; this batch does not
close it, and the level read from below (batch 57) was not needed anywhere in the arm half.

### 2.3 The general engine

Not settled; one half of it is now general. `HPC/Fold/LandmarkChain.lean` proves
`foldsOnto_landmarkN`: for an arbitrary walk `c` and an arbitrary increasing chain of its positions
`q 0 ≤ ⋯ ≤ q r`, if the arm's level at a step `d` is served only by the positions `q r` and later,
the fold forces steps `j 0 ≤ ⋯ ≤ j r = d` of the arm within one of the levels `c (q s)`, with
`j 0 ≥ q 0` and every gap at least the walk's own. That is the *necessity* half of the landmark
sentence for a walk with any number of legs, proved once (`beta_chain` is the itinerary form), and
it subsumes `foldsOnto_landmark1`, `foldsOnto_landmark2` and `foldsOnto_landmark3`, which until now
were three copies of one argument.

The sufficiency half — the invariant `gseq4_invLand` with one bound per leg, for a walk of any
number of legs — is not proved here. What the four-leg proof shows is what the general one will
have to carry: two bounds per interior leg, one tracking the leg's far end with a time credit and
one tracking its near end, the credit being exactly the index gap between consecutive landmark
positions. Nothing in the four-leg argument is special to four, but the invariant is a conjunction
indexed by the legs, so stating it in general needs the walk itself to be given by its list of
turning levels; that restatement is the next step and was not attempted in this batch.

## 3. Deliverables

**New Lean files, both `sorry`-free, no `native_decide`, no new axiom.**

* `HPC/Fold/LandTri.lean` — the arm-only trichotomy and the reduction of the branch to its
  crossings: `leg4Land_w8_of_floor`, `notW8_base3`, `notW8_hi_after`, `notW8_floor`,
  `notW8_ceil3`, `notW8_ceilWb`, `notW8_deep`, `leg4Land_tri`, `leg4Land_tri_armG`,
  `leg4Land_tri_armT`, `Leg4TriCrossL5`, `s3_span_nine_mid5_of_leg4TriCrossL5`,
  `Leg4FiveCrossL5`, `s3_span_nine_mid5_of_leg4FiveCrossL5`.
* `HPC/Fold/LandmarkChain.lean` — `beta_chain`, `foldsOnto_landmarkN` and the checks
  `foldsOnto_landmarkN_one`, `foldsOnto_landmarkN_two`.

`lake build HPC` is clean (8148 jobs) and both files are in `HPC.lean`.

```
'HPC.Fold.leg4Land_tri' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_leg4TriCrossL5' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w8_of_floor' depends on axioms: [propext, Quot.sound]
'HPC.Fold.foldsOnto_landmarkN' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.beta_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_leg4FiveCrossL5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Censuses.** `census-batch60.c` (log `census-batch60.log`) runs the batch-59 census under the same
audit protocol — the generators, the faithfulness test `IsCrookedIvF`, the dynamic program for
`FoldsOnto`, every predicate by its own definition — and adds the batch-60 blocks: the clauses of
the best walk arm by arm, the walks serving an arm that fails one, the crossings of the clause sets
and the crossings of the three walks of `leg4Land_tri`.

**Arm-only probes** (they say so): `probe60.c` and `probe60b.c` enumerate arms, not pairs, and
carry no faithfulness hypothesis beyond the band, the Lipschitz condition, the basepoint `L + 5`
and the branch hypothesis.

The numbers quoted above are from those three programs and their logs.
