# Report — batch 49: the crossing, the mirror, and the general engine

Runs on top of the batch-48 delivery, under `COMMISSION.md` (batch 49; the previous commission is
archived as `COMMISSION-batch48.md`). `lake build HPC` succeeds. Everything new that is proved is
`sorry`-free and uses only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`.

## 0. The counterexample, first

**`cross_ceil_profile` is false in the general model, and so are `unserved_profile` and
`unserved_leg3deep` with it.** All three fall at one basepoint, and it is a basepoint the
development already contains: `bing9sB` — the Bing chain `bing 0 9` of span nine with the peak at
its index `309` lowered from `7` to `6` — at its basepoint `336`, the pair batch 46 used to refute
`unserved_ceiling`. The refutations are `not_crossCeilProfile`, `not_unservedProfile` and
`not_unservedLeg3deep` in the new file `HPC/Fold/CrossWitness.lean`; the three statements are kept
in `HPC/Fold/Mixed.lean`, commented out, with the refutations named.

What is true at that basepoint, all of it decided on the chain itself or proved from the new
theory:

* `ρ 336 = L + 4` and both arms are `HighAt (L + 1) (L + 8)`;
* the Λ-walk does not fold the backward arm and the V-walk does not fold the forward arm
  (`not_foldsOnto_lam_sBT`, `not_foldsOnto_vee_sBG`, batch 46), so the pair is **unserved**;
* the forward arm **fails `Leg3Ceil`** (`not_leg3Ceil_sBG`): it stands at `L + 8` at its step `72`,
  and between its step `3` and that ascent it never drops to `L + 2` or below, while the clause
  needs a time at `L + 2` or below at a step at least `8`;
* hence `cross_ceil_profile` asks both arms to fold onto the Λ-walk, and the backward arm does
  not; `unserved_profile` asks the forward arm to satisfy `Leg3Ceil`, and it does not;
* and the forward arm **does not fold onto the third walk** `L+3 → L+6 → L+1 → L+8`
  (`not_foldsOnto_leg3_sBG`), so `unserved_leg3deep` — the statement the branch has rested on
  since batch 47 — fails too.

The last point is what needed a new theorem, and it is §1.3 below: the criterion for the third
walk is not only sufficient but **necessary**, so an arm failing `Leg3Ceil` cannot fold onto that
walk by any route whatever.

**Why no census saw this before.** The branch hypothesis is `HighAt (armG ρ i) (L + 1) (L + 8)`,
and the definition (`HPC/Fold/Leaf.lean`) reads

```
HighAt f tl th : ∀ d, th ≤ f d → ∃ j < d, f j ≤ tl + 1,
```

so with `tl = L + 1` the earlier time is asked at `L + 2` or below. The censuses of batches 46, 47
and 48 asked it at `L + 1` or below. That is a strictly smaller corpus — 154 of the 364 branch
basepoints of the two thin chains, 44 560 of the 105 004 of the single shavings — and every
basepoint at which an arm fails `Leg3Ceil` is outside it, because such an arm reaches `L + 8`
without ever having been below `L + 2`. Read as the definition reads it (`census-batch49b.c`),
`cross_ceil_profile` has 1 905 counterexamples over the batch-48 generators and `unserved_profile`
has 357.

**Span nine is not refuted, and that is a theorem too.** The pair at `336` is served, by the walk
`L+3 → L+2 → L+8 → L+1`: `HPC/Fold/CrossServed.lean` exhibits an itinerary for each arm — as a
base-sixteen numeral, in the manner of `bing9Nat` — and the kernel checks the three conditions of
`FoldsOnto` (`foldsOnto_w4_sBG`, `foldsOnto_w4_sBT`, `sB_served`). See §1.4 for the re-split and §3
for the census that stands behind it.

## 1. The targets, in order

### 1.1 `cross_valley_profile` — not proved, and not refuted either

The valley crossing survives every census this batch ran: **73 495 tests, no exception**
(`census-batch49b.c`, `census-batch49c.c`, `census-batch49d.log`), over the thin chains, all 576
single shavings, all 576 single fills and 800 random mixtures, with the branch hypothesis read as
the definition reads it. The asymmetry with the ceiling item is not an accident, and §2.2 says what
it is.

### 1.2 `cross_ceil_profile` — **refuted**; see §0

### 1.3 What made the refutation possible: the landmark sentence is necessary

`HPC/Fold/Landmark.lean` is the new file, and it is about arbitrary walks, not this one.
`FoldsOnto f len c` asks for an itinerary `β` — a walk position for each step of the arm, starting
at `0`, moving by at most one position per step, always within one of the arm's level. Everything
the criteria of this development ask of an arm is a consequence of the discrete intermediate value
theorem for `β`:

> **`foldsOnto_landmark2`.** If the arm's level at a step `d` is served only by the walk positions
> `q2` and later, then for any `q0 ≤ q1 ≤ q2` there are steps `j ≤ k ≤ d` with the arm within one
> of `c q0` at `j` and within one of `c q1` at `k`, and `j ≥ q0`, `k ≥ j + (q1 - q0)`,
> `d ≥ k + (q2 - q1)`.

That is the landmark sentence of REPORT-batch48.md §2.3 in the two-landmark case, for an arbitrary
walk, and `foldsOnto_landmark1` is the one-landmark case. Read on the three-leg walk, whose sixteen
positions carry `3,4,5,6,5,4,3,2,1,2,3,4,5,6,7,8` above `L`:

* a level `L + 8` is served only by the positions `14` and `15`, and the landmarks `3` (level
  `L + 6`) and `8` (level `L + 1`) give exactly `Leg3Ceil`, index bounds included
  (`leg3Ceil_of_foldsOnto_leg3`);
* a level `L + 1` is served only by `7, 8, 9`, and the landmark `3` gives a time at `L + 5` or
  above at a step at least `3` and at least four steps earlier
  (`leg3Valley4_of_foldsOnto_leg3`).

With the sufficiency proved in batch 48 this closes the criterion:

> **`foldsOnto_leg3deep_iff_landmark`.** For a 1-Lipschitz arm in `[L, L + 9]` based at `L + 4`,
> folding onto `L+3 → L+6 → L+1 → L+8` is **equivalent** to the landmark sentence `Leg3Land`.

The commissioned clauses sit between the two halves: `Leg3Valley ∧ Leg3Ceil` implies the sentence
(one index tighter at the valley) and the sentence implies the fold. The batch-48 census reported
the sentence to be equivalent to the fold over 113 019 462 arms and 54 walks; for this walk it is
now a theorem, and the necessity half is a theorem for every walk.

### 1.4 The branch `L + 4`, re-split: three walks, not one

`unserved_leg3deep` is replaced by `unserved_three_walks` (`HPC/Fold/Mixed.lean`), which asks the
same of three named walks:

| | walk | as a term | times |
|---|---|---|---|
| `w₃` | `L+3 → L+6 → L+1 → L+8` | `leg3Walk L (L+9) (L+6) (L+4)` | 16 |
| `w₄` | `L+3 → L+2 → L+8 → L+1` | `leg3Walk' L (L+9) (L+7) (L+2)` | 15 |
| `w₅` | `L+3 → L+7 → L+1 → L+8` | `leg3Walk L (L+9) (L+7) (L+4)` | 18 |

`w₄` is the reflection of `w₃` and `w₅` is `w₃` with its peak one level higher. At the **98 611**
unserved branch basepoints of `census-batch49c.c` (see §3): `w₃` serves 98 254, `w₄` serves 318 of
the 357 that `w₃` misses, and `w₅` serves the remaining 39 — and `w₅` alone serves 90 764. No pair
of any census in this repository folds onto none of the three. With that item
`s3_span_nine_mid4` is again a complete derivation, by a case analysis on the three.

### 1.5 `s3_span_nine_mid5`, `s3_span_nine`, `s3_general` — not proved

Unchanged from batch 48, and the mirror branch still needs its own argument (REPORT-batch48.md
§2.2, and §2.2 below adds one reason more).

## 2. The questions

### 2.1 Is `cross_ceil_profile` vacuous on actual pairs?

**No. It is not vacuous, and it is false.** The commission's question was whether an arm of a
faithful pair of the branch can fail `Leg3Ceil` at all. It can, and not only in the general model:
**nine basepoints of the thin chain `bing 0 9` itself** have an arm failing the clause (and nine of
`bing 9 0`). At all eighteen the item happens to hold — both arms do fold onto the Λ-walk — but
one shaving of the same chain is enough to break it (§0).

The route to the answer is worth recording, because the first two attempts were wrong:

* *Arms alone, by exhaustive search.* `census-batch49.c` walks the tree of all 1-Lipschitz arms in
  `[0,9]` based at `L + 4` that satisfy `CrookUp` and `CrookDown`, pruning a prefix as soon as a
  pair `(s,t)` violates a clause, and pruning a branch as soon as a low time comes late enough
  after a high one to settle `Leg3Ceil`. It settles nothing: at depth 20, of the 5 314 806 arms
  that reach `L + 8`, **every one** fails `HighAt (L + 1) (L + 8)`, because the climb from `L + 2`
  to `L + 8` in a crooked arm is far longer than twenty steps. The question is not reachable by
  exhaustion.
* *Arms alone, by construction.* An arm that dips to `L + 2` at its step `2` and then runs a
  crooked chain in the band `[L + 2, L + 9]` — for instance `L+4, L+3` followed by the Bing chain
  from `L + 2` to `L + 9`, 172 links — satisfies `CrookUp`, `CrookDown` and `HighAt (L+1) (L+8)`
  and fails `Leg3Ceil`. So the clause is not a consequence of the arm hypotheses.
* *Actual pairs.* Scanning `bing 0 9` with the hypothesis read as the definition reads it gives the
  nine basepoints above, and the shavings give the counterexample.

So the crossing at the ceiling is not one statement instead of two; it is one statement fewer.

### 2.2 The one index of `cross_valley_profile`

The report of batch 48 located the difficulty at one index: the clause across the basepoint
delivers a low time of the other arm, but possibly at index two or three where the V-criterion
wants four or later. This batch did not close it, and did not find a pair with the low time at
index two or three that nonetheless folds. What it can add is where the case analysis now stands,
and why the two crossings are not mirror images of each other.

Write `X` for the arm that fails `Leg3Valley`, at its descent `d₀` to `L + 1`, and `Y` for the
other arm, and suppose `Y` fails the V-criterion at an ascent `e` to `L + 7`. Applying the
crookedness clause across the basepoint, from the position of `Y`'s ascent to the position of
`X`'s descent, returns a low link `u` and, after it, a high link `u'`.

* The case `u ≤ i − 4` is exactly what is wanted: `Y` has a low time at index four or later.
* The case `u' > i + d₀ − 5` is **excluded by the timing law**: there `u'` would have to fall four
  levels to `X`'s descent in four steps, and `crookDown_fall4` allows no fewer than seven.
* The case `u ≥ i + 2` is excluded with it: `u < u' < i + 3` leaves no room.
* What is left is `u ∈ {i − 3, i − 2}`: `Y` dips to `L + 2` at its step two or three and not again
  before its ascent — the configuration of §0, read on the other arm.

In that last case the clause has to be applied a second time, and this is where the general model
costs its level: applied between `Y`'s low and `Y`'s ascent it returns a *link* meeting `L + 3`,
whose point may stand at `L + 3` and not at `L + 2`. Here the asymmetry between the two crossings
appears. The clause returns links, and a link meeting a level `l` has `ρ ≤ l ≤ σ`: for a **low**
landmark that gives `ρ ≤ l` outright, and for a **high** landmark only `σ ≥ l`, that is
`ρ ≥ l − 1`. The valley crossing asks for low times of the other arm and the ceiling crossing for
high ones — which is one reason to expect what the censuses show, that the valley item survives
where the ceiling item fails.

### 2.3 The general engine

The commission asks whether the landmark sentence is a theorem about 1-Lipschitz arms for an
arbitrary zigzag walk — as a sufficient condition first, and as a characterisation if the proof
gives it.

**The necessity half is a theorem, for every walk** (`foldsOnto_landmark1`, `foldsOnto_landmark2`,
§1.3): the sentence is not merely implied by the fold on a corpus, it is implied by the definition
of a fold, in three lines of discrete intermediate value theorem. Nothing about crookedness, the
band, the basepoint or the shape of the walk is used.

**The sufficiency half is not proved here.** For the one walk this batch needed it,
sufficiency is batch 48's engine, and putting the two together gives the first *exact* criterion in
the development for a walk of three legs (`foldsOnto_leg3deep_iff_landmark`). The general
sufficiency would have to carry the batch-48 invariants — the clock, the `R` and `S` bounds, the
slack clock — with the landmark positions of an arbitrary walk as their constants, and that is a
larger piece of work than this batch had room for. It is worth saying what the necessity half
already buys: every criterion of the development can now be *refuted* on an arm by exhibiting one
event with no landmarks behind it, which is how §0 works, and which no earlier batch could do for
any walk but the two canonical ones.

## 3. The census

All censuses of this batch read the branch hypothesis as the definition reads it.

`census-batch49.c` (log `census-batch49.log`) is over **arms alone** — it says so — and is the
exhaustive tree search of §2.1: 695 614 352 prefixes at depth 20, no arm meeting the hypotheses of
the branch and failing `Leg3Ceil` within that depth, for the reason given there.

`census-batch49b.c` (log `census-batch49b.log`) and `census-batch49c.c` (logs
`census-batch49c.log`, `census-batch49d.log`, the latter with 400 mixture rounds per chain) are
over the **general model**, on two base chains, `bing 0 9` and the same chain run the other way,
with the generators of batch 48. Every pair is verified against `IsCrookedIvF` before use and every
fold is decided exactly by the dynamic program over `FoldsOnto`.

| generator | pairs | non-thin links | branch basepoints | unserved |
|---|---|---|---|---|
| the thin chains themselves | 2 | 0 / 1 972 | 364 | 110 |
| **shaving** a peak (`ρ` lowered at a strict local maximum) | 576 | 576 / 567 936 (0.10 %) | 105 004 | 31 596 |
| **filling** a valley (`σ` raised at a strict local minimum) | 576 | 576 / 567 936 (0.10 %) | 104 832 | 31 680 |
| random mixtures of the two | 800 | 153 913 / 788 800 (19.5 %) | 171 264 | 35 225 |

(Of the 381 464 branch basepoints, 183 232 also meet the stronger reading of the hypothesis used by
the batch-48 census; the other 198 232 are new to this census.)

What they find:

* **`cross_ceil_profile`: 1 905 failures** out of 17 115 tests — 18 among the single shavings,
  1 887 among the mixtures, none among the thin chains or the fills.
* **`unserved_profile`: 357 failures** out of 98 611 unserved pairs.
* **`cross_valley_profile`: 73 495 tests, no failure.**
* `leg3Valley_or_vee` and `leg3Ceil_or_lam`, the theorems of batch 48, are confirmed 79 959 and
  17 115 times respectively, with no exception, over a corpus twice the size of the one they were
  checked on.
* `unserved_profile_one`, also a theorem, has no exception.
* **The three walks cover everything**: at all 98 611 unserved basepoints one of `w₃`, `w₄`, `w₅`
  folds both arms (§1.4). Every pair that neither `w₃` nor `w₄` serves is served by `w₅`, and the
  brute-force search over every zigzag walk with at most three turns confirms `w₅` as the shortest
  serving walk in each such case.

A generator that did **not** work: twelve base chains from a randomised Bing recursion (the turning
levels chosen within two of the endpoints rather than at one) were all rejected by the faithfulness
check, so the base chains remain the two Bing chains. Their shavings, fills and mixtures are the
general pairs.

## 4. What is left

* The branch `L + 4`: `unserved_three_walks` — the branch is now a statement about three walks,
  and the criterion for each of them can be read off the landmark theorem exactly as `Leg3Ceil` is
  for the first; `deepValley_of_foldsOnto_leg3deep` (`HPC/Fold/Landmark.lean`) does it for the
  valley clause of the third of them.
* `cross_valley_profile`: open, with no counterexample in 73 495 tests, and with one case of its
  analysis left (§2.2).
* The branch `L + 5`: its own argument, as batch 48 established.
* `s3_span_nine` follows from the two branches; `s3_general` waits on spans ten and above.
