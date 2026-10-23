# Report — batch 50: the program, the three walks, and the audit

Runs on top of the batch-49 delivery, under `COMMISSION.md` (batch 50; the previous commission is
archived as `COMMISSION-batch49.md`). `lake build HPC` succeeds. Everything new that is proved is
`sorry`-free and uses only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`.

## 0. No counterexample, and what was refuted instead

**No target was refuted this batch.** `cross_valley_profile` and `unserved_three_walks` both
survive every test run here — 54 030 and 80 041 respectively, over a corpus half again as large as
batch 49's and with one generator family that is new (§3) — and neither is proved.

One statement *was* refuted, and it was one of this batch's own: the guess that the second walk
`w₄ = L+3 → L+2 → L+8 → L+1` announces its descents to `L + 1` in the way `w₃` does. It does not,
and the definition audit of §4 found it on 22 223 arms of the corpus before it reached Lean. The
reason is visible in the walk: its position `1` already carries the level `L + 2`, which serves
`L + 1`, so an arm may drop to `L + 1` at its step one and fold all the same. What `w₄` does
announce is its ascents to `L + 8` and its descents to the floor `L` (§1.2). The lesson is the
answer to question 1: **which events a walk announces is a property of the walk, and the three
walks of the branch announce different ones.**

## 1. The targets, in order

### 1.1 `unserved_three_walks` — not proved in general; proved for a thin sequence

* **Thin form: a theorem.** `unserved_three_walks_thin` (`HPC/Fold/ThreeWalksThin.lean`): for a
  thin faithful crooked sequence, a pair of the branch that folds onto neither canonical walk folds
  onto one of the three walks — and always onto the *first* of them, by the batch-45 announcements
  and the engine `foldsOnto_leg3deep_branch`. So at this branch the difference between the thin and
  the general model is exactly the second and third walk: in the thin model the left disjunct
  always holds, in the general model it does not (`not_unservedLeg3deep`, batch 49). Neither
  `HighAt` hypothesis nor either end of the band is used.
  `s3_span_nine_mid4_thin_of_three` re-runs the general derivation of the branch on a thin
  sequence, which checks that the re-split of batch 49 lost nothing already proved.
* **The general item: not proved, not refuted.** At the 80 041 unserved branch basepoints of this
  batch's census one of the three walks serves every pair, with no exception.
* **An instrument for refuting it.** `three_walks_necessary` (`HPC/Fold/LandmarkW.lean`): if a pair
  folds onto one of the three walks, then both arms satisfy `Leg3Ceil`, or both satisfy `CeilW4`,
  or both satisfy `Valley5`. A pair at which each of those three clauses fails on some arm
  therefore refutes the item. Over the whole corpus the instrument never fires: there is no such
  pair (§3).
* **The pair that decided batch 49, decided again.** `HPC/Fold/DecideWitness.lean` settles at the
  basepoint `336` of `bing9sB`, by kernel computation on the chain and with no itinerary written by
  hand, that the pair is unserved by the two canonical walks, that `w₃` misses its forward arm, and
  that **both** `w₄` and `w₅` serve it. The last was not known: the work item holds there twice
  over. The refutation of batch 49 and the fold of `HPC/Fold/CrossServed.lean` are thereby
  re-derived through a completely different route.

### 1.2 The landmark criteria of `w₄` and `w₅` (question 1, and the means of §1.1)

`HPC/Fold/Landmark.lean` read the necessity half of the landmark sentence off `w₃`. This batch does
the same for the other two, in `HPC/Fold/LandmarkW.lean`:

| walk | levels above `L` | what a fold onto it announces |
|---|---|---|
| `w₃` | `3,4,5,6,5,4,3,2,1,2,3,4,5,6,7,8` | descents to `L+1` (`Valley4`); ascents to `L+8` (`Leg3Ceil`) |
| `w₄` | `3,2,3,4,5,6,7,8,7,6,5,4,3,2,1` | ascents to `L+8` (`CeilW4`); descents to `L` (`BottomW4`) |
| `w₅` | `3,4,5,6,7,6,5,4,3,2,1,2,3,4,5,6,7,8` | descents to `L+1` (`Valley5`); ascents to `L+9` (`TopW5`) |

Sufficiency is settled for one of the two: the engine of `HPC/Fold/Leg3Deep.lean` is stated for an
arbitrary peak level, and at `K = L + 7` it is `w₅`, so `foldsOnto_w5_branch` serves an arm that
announces its descents to `L + 1` and its ascents to `L + 9`. The two halves for `w₅` do not meet —
the announcements ask a time *at* the peak level where the landmark sentence tolerates one level
less, which is the gap batch 48 closed for `w₃` — so the criterion for `w₅` is not yet exact, and
`w₄` has no engine at all in the development (its engine, `foldsOnto_leg3'`, is stated for an arm
based at the walk's own trough, not at `L + 4`).

The entries that are *missing* from the table are as informative as the ones that are there: `w₄` announces
nothing about `L + 1` (its position `1` serves that level), and `w₅` announces nothing about
`L + 8` (its peak `L + 7` serves that level). The clauses compare as one would hope:
`Leg3Valley → Valley4`, `Valley5 → Valley4`, so a fold onto `w₃` or onto `w₅` gives `Valley4`
(`valley4_of_foldsOnto_w3_or_w5`), and an arm failing `Valley4` folds onto the V-walk by itself
(`valley4_or_vee`) and leaves only `w₄` of the three.

### 1.3 `cross_valley_profile` — not proved, and not refuted

54 030 tests this batch, no failure; 127 525 with batch 49's. The case analysis stands where
REPORT-batch49.md §2.2 left it, and §2.2 below adds one measurement of the residual case — and now
also the analysis itself, as machine-checked theorems in `HPC/Fold/CrossValley.lean` (§2.2.1).

### 1.4 `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3` — not proved

Unchanged. The mirror branch still needs its own argument (REPORT-batch48.md §2.2).

## 2. The questions

### 2.1 Why three walks?

Because a walk announces the events its *own* positions force, and the three walks force different
ones (§1.2). Concretely: an unserved pair whose forward arm fails `Leg3Ceil` cannot be served by
`w₃` — that is the batch-49 refutation — but `Leg3Ceil` is not asked by `w₄` or by `w₅`, and at the
basepoint `336` of `bing9sB` both of them serve the pair (§1.1). Symmetrically an arm failing
`Valley4` cannot be served by `w₃` or `w₅` and leaves only `w₄`. So the three walks are not three
guesses at one sentence; they are three different sentences, and what `unserved_three_walks` claims
is that every unserved pair of the branch satisfies one of them on both arms.

Whether *three* suffice is not decided here. What can be said is what the corpus says and what the
instrument says. The corpus (80 041 unserved pairs): `w₃` serves 79 869, `w₄` 12 068, `w₅` 78 076;
the 172 pairs `w₃` misses — those are exactly the pairs refuting the older `unserved_profile` — are
all served by one of the other two, and no pair of any census in this repository is served by none
of the three. The instrument (`three_walks_necessary`) fires at no pair of the corpus, so the
corpus contains no *witness* against the item of the kind the landmark theory can recognise. A
fourth walk, or a pair-dependent family, is neither needed on this corpus nor excluded in general.

### 2.2 The last case of `cross_valley_profile`

The commission asks whether the residual case — the other arm `Y` dipping to `L + 2` at its step
two or three and not again before its ascent — is closed by a second application of the clause, or
realised by a general pair that folds anyway, or realised by one that does not.

What this batch can add is that **the configuration is common on arms and never occurs opposite a
failing arm**. Counting arms whose low times (`≤ L + 2`) before their first ascent to `L + 7` all
fall at the step two or three: **11 182 arms of the corpus realise it, and not one of them folds
onto the V-walk** — as the exact V-criterion of `HPC/Fold/Profile.lean` predicts, since that
criterion asks a low time at index four or later. So each of those 11 182 arms would refute
`cross_valley_profile` at once if it were ever the partner of an arm failing `Leg3Valley`; over
54 030 tests it never is. The item is therefore not vacuous and not nearly-refuted: it is held up
by a genuine exclusion across the basepoint, of which the batch-49 analysis proves every case but
this one.

A **steered search** was run as well (`search-batch50.c`, log `search-batch50.log`). It hill-climbs
over the same move set as the perturbation-walk generator — one link of `ρ` or `σ` changed at a
time, kept when the pair is still faithful — minimising

> `O(pair) = ` the least, over branch basepoints with an arm failing `Leg3Valley`, of the number of
> low witnesses the *other* arm's worst ascent has,

so that `O = 0` is a counterexample. Over six restarts of three thousand steps the search reaches
`O = 1` and never `O = 0`: it can arrange for the arm opposite a failing arm to have exactly one
low time in the window the V-criterion asks about, and not for it to have none. That is weak
evidence — the move set accepts about one proposal in thirty — but it is evidence of the same kind
as the census, obtained by trying to break the item rather than by sampling.

Where the proof still stops is unchanged, and it is one level: applied a second time, between `Y`'s
low time and `Y`'s ascent, the crookedness clause returns a *link* meeting `L + 3`, whose point may
stand at `L + 3` where the V-criterion wants `L + 2`. The timing laws close the index side of the
case — a climb of four levels needs seven steps (`crookUp_climb4`), which places the high landmark
out of the window the failing arm's clause leaves open — but not the level side.

#### 2.2.1 The analysis, as theorems

The prose of the two preceding paragraphs is now a Lean file, `HPC/Fold/CrossValley.lean`, and the
statement it ends at is a **dichotomy**:

> **`cross_valley_dichotomy`.** Under the hypotheses of the work item — and using neither `HighAt`
> clause nor either end of the band — either *both* arms fold onto the V-walk, which is the work
> item's conclusion, or the sequence stands at exactly `L + 2` at one of the four times `i − 3`,
> `i − 2`, `i + 2`, `i + 3` around the basepoint (`ValleyResidual`).

So `cross_valley_profile` is a theorem for every pair avoiding that configuration
(`cross_valley_profile_of_not_residual`), and what is left of it is a statement about the three
steps either side of the basepoint. The engine is `cross_valley_low_fwd` / `cross_valley_low_bwd`,
which read the crookedness clause across the basepoint between the other arm's ascent to `L + 7`
and the failing arm's descent to `L + 1`, and combine it with `crookDown_fall4`, `crookUp_climb4`
and the failure window to pin the returned links.

The cost of the residual configuration is then measured exactly, and with no exceptional case:

> **`cross_valley_armT_low3`, `cross_valley_armG_low3`.** If one arm fails the valley clause, then
> before every ascent of the other arm to `L + 7` that arm stands at `L + 3` or below at a step at
> least four.

That is the V-criterion of `critVeeProfile_iff_of_isLip` with `L + 3` in place of the `L + 2` it
asks for: the index side is closed everywhere, the level side is short by one everywhere it is
short at all. It is the same one level by which the general crookedness clause falls short of the
thin one, which is where the whole of the general-model residue in this repository sits.

### 2.3 Sufficiency of the landmark sentence for an arbitrary walk

Still not proved, and this batch did not attempt the general engine. Two things changed around it.

* The necessity half, which is a theorem for every walk since batch 49, is now *read* on two more
  walks, and reading it is mechanical: the positions of the walk that serve a level, then
  `foldsOnto_landmark1` or `foldsOnto_landmark2` (§1.2). The reading also shows what the general
  sufficiency would have to respect — that a walk announces only what its own positions force, so
  the sentence has a different shape for each walk, and the guess that it does not is what §0
  refutes.
* The comparison of sentence with fold is no longer a census-only matter. `foldsB_iff`
  (`HPC/Fold/Decide.lean`) proves the dynamic program every census runs equivalent to `FoldsOnto`,
  in both directions, for any arm and any walk; `FoldsOnto` is therefore a decidable predicate of
  concrete data, and on any given arm and walk the kernel now decides the fold, the sentence, and
  their agreement. Where batch 48's census compared the two over 113 019 462 arms outside Lean, the
  same comparison is now available inside it.

## 3. The census

`census-batch50.c` (log `census-batch50.log`), over the **general model**, on the two base chains
`bing 0 9` and `bing 9 0`. Every pair is verified against `IsCrookedIvF` before use, every fold is
decided by the dynamic program of `HPC/Fold/Decide.lean`, and the branch hypothesis is read as the
definition reads it (a time at `L + 2` or below before every time at `L + 8`).

| generator | pairs | non-thin links | branch basepoints | unserved |
|---|---|---|---|---|
| the thin chains themselves | 2 | 0 / 1 972 | 364 | 110 |
| shaving a peak | 576 | 576 / 567 936 (0.10 %) | 105 004 | 31 596 |
| filling a valley | 576 | 576 / 567 936 (0.10 %) | 104 832 | 31 680 |
| random mixtures, rate 1/3 | 80 | 15 241 / 78 880 (19.3 %) | 16 922 | 3 657 |
| heavy mixtures, rate 1/2, and the total mixture | 82 | 24 326 / 80 852 (30.1 %) | 18 950 | 3 463 |
| **random faithful perturbation walks** (new) | 188 | 8 110 / 185 368 (4.4 %) | 36 023 | 9 535 |
| **all** | **1 504** | **48 829 / 1 482 944 (3.3 %)** | **282 095** | **80 041** |

The new generator leaves the shaving-and-filling family altogether: it changes one link of `ρ` or
of `σ` at a time, at *any* index and in either direction, keeps the change when the pair is still
faithful, and iterates, scanning the pair at every accepted step. Nothing asks the changed link to
sit at a local extremum, and the pairs it reaches are not shavings of a thin chain. (The total
mixture — every peak shaved and every valley filled at once — is faithful, and is included above.)

What the census finds:

* **`cross_valley_profile`: 54 030 tests, no failure.**
* **`unserved_three_walks`: 80 041 unserved pairs, no failure** — `w₃` serves 79 869, `w₄` 12 068,
  `w₅` 78 076.
* **`three_walks_necessary` never fires**: no unserved pair has all three of `Leg3Ceil`, `CeilW4`,
  `Valley5` failing on some arm.
* The necessity theorems of `HPC/Fold/Landmark.lean` and `HPC/Fold/LandmarkW.lean` are confirmed
  492 306 times for `w₃`, 238 572 for `w₄` and 421 637 for `w₅`, with no exception. (It was this
  test that refuted the mistaken valley clause for `w₄`, §0.)
* `leg3Valley_or_vee` (58 632 confirmations), `leg3Ceil_or_lam` (13 252), `valley4_or_vee`
  (58 632) and `unserved_profile_one`: no exception.
* `unserved_profile`, refuted in batch 49, fails 172 times here.
* The residual case of `cross_valley_profile`: realised by 11 182 arms, none folding onto the
  V-walk, none opposite a failing arm (§2.2).

`search-batch50.c` is the steered search of §2.2 over the same generator family.

## 4. The definition audit

The commission asks that every predicate a census evaluates and the development defines be checked
against the definition by kernel evaluation in Lean, on the census's own objects, and that the
report say which predicates and how many objects.

`census-batch50.c` writes a sample of the arms it meets to `census-batch50-audit.txt`, one per
distinct verdict signature and at most three per generator, together with the verdict its own
program gives on every predicate; `gen-audit50.py` turns that file into `HPC/Fold/Audit50.lean`,
where the *definitions* are decided by the kernel on the same objects. A disagreement would be a
build failure.

* **Objects: 12 arms**, of 13 to 64 steps, drawn from the thin chains, a shaving, a fill and a
  mixture (the audit objects are the arms' first 64 steps, which are sequences like any other).
* **Predicates: 13** — `HighAt`, `Leg3Valley`, `Leg3Ceil`, `Valley4`, `Valley5`, `CeilW4`,
  `BottomW4`, `TopW5`, and `FoldsOnto` for each of the five walks the census decides (Λ, V, `w₃`,
  `w₄`, `w₅`).
* **156 kernel checks, all agreeing with the census**, and both verdicts occur for every predicate
  that has both on the corpus.

The fold verdicts are auditable at all only because of `HPC/Fold/Decide.lean`. Before it, a census
verdict of *no fold* had no counterpart in Lean: a fold could be exhibited by an itinerary, but the
absence of one could be shown only through a criterion proved necessary. Now `decide` settles both.

## 5. What is new in Lean

| file | what |
|---|---|
| `HPC/Fold/Decide.lean` | the dynamic program over folds, and `foldsB_iff`: it decides `FoldsOnto` exactly. `FoldsOnto` becomes a decidable predicate of concrete data |
| `HPC/Fold/LandmarkW.lean` | the landmark criteria of `w₄` and `w₅` (`CeilW4`, `BottomW4`, `Valley5`, `TopW5`), the sufficiency half for `w₅` (`foldsOnto_w5_branch`), how the clauses compare, and `three_walks_necessary` |
| `HPC/Fold/ThreeWalksThin.lean` | `unserved_three_walks_thin`: the standing work item of the branch, on a thin sequence |
| `HPC/Fold/DecideWitness.lean` | the batch-49 pair decided by the program: unserved, missed by `w₃`, served by `w₄` **and** by `w₅` |
| `HPC/Fold/Audit50.lean` | the definition audit: 12 arms of the census, 13 predicates, 156 kernel checks (generated by `gen-audit50.py`) |
| `HPC/Fold/CrossValley.lean` | the valley crossing as far as it goes: `cross_valley_dichotomy`, `cross_valley_profile_of_not_residual`, and `cross_valley_armT_low3` / `cross_valley_armG_low3`, the relaxed criterion that holds with no exceptional case (§2.2.1) |

## 6. What is left

* The branch `L + 4`: `unserved_three_walks`, in the general model. Its thin form is a theorem, its
  necessity side is `three_walks_necessary`, and the sufficiency side needs, for each of the three
  walks, an engine of the kind batch 48 built for `w₃`.
* `cross_valley_profile`: open, with no counterexample in 127 525 tests over two batches, and with
  one case of its analysis left — short by one level, not by one index (§2.2). That case is now
  named by a theorem: it is `ValleyResidual`, the sequence standing at `L + 2` two or three steps
  to one side of the basepoint, and outside it the work item is proved (§2.2.1).
* The branch `L + 5`: its own argument.
* `s3_span_nine` follows from the two branches; `s3_general` waits on spans ten and above.
