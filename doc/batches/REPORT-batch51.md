# Report — batch 51: engines for `w₄` and `w₅`, and the level

Runs on top of the batch-50 delivery in its continued form, under `COMMISSION.md` (batch 51).
Nothing is refuted this batch; no target of §1 is proved in the general model. What the batch
delivers is the answer to question 1 — **all three walks of the branch now have an exact
criterion** — and, with it, the standing work item restated with no `FoldsOnto` in it. Question 3's
second half gets a negative answer, in Lean.

## 1. No counterexample

No statement of the development is refuted by this batch. The census `census-batch51.c` finds no
failure of `cross_valley_profile` (49 756 tests) and none of `unserved_three_walks` (73 804
unserved branch basepoints).

## 2. The targets of §1

### 2.1 `unserved_three_walks` — not proved, and now three sentences

The item stands. What is new is its form. Since batch 48 the first walk `w₃` has an exact criterion
(`foldsOnto_leg3deep_iff_landmark`); this batch gives one to the other two.

* **`w₅ = L+3 → L+7 → L+1 → L+8`** (`HPC/Fold/ProfileK.lean`). The batch-48 profile engine is
  restated with the peak as a parameter: `foldsOnto_leg3_profileK_min` folds a 1-Lipschitz arm of
  `[L, H]` based at `P` onto `leg3Walk L H K P` from announcements that ask a time at `K - 1` — one
  below the peak — at a step at least the peak position `K - P + 1`, the ceiling clause adding a
  time at `L + 2` at least `K - L - 1` steps later. Nothing in the batch-48 argument used the peak
  being `L + 6`: the clock reaches the peak position, the slack clock crosses to the valley
  position, and the constants `3`, `5`, `8` of that file are `K - P + 1`, `K - L - 1`,
  `2K - P - L`. At `K = L + 6` the engine is the batch-48 one (`foldsOnto_w3_profileK`); at
  `K = L + 7` it is `w₅`, and there the two halves meet exactly:

  > `foldsOnto_w5_iff_landmark`: for a 1-Lipschitz arm of `[L, L + 9]` based at `L + 4`, folding
  > onto `w₅` **is** `Valley5 ∧ TopW5`.

  Necessity is batch 50's (`valley5_of_foldsOnto_w5`, `topW5_of_foldsOnto_w5`); sufficiency is the
  engine at the peak `L + 7`, which asks a time at `L + 6` where `foldsOnto_w5_branch` asked
  `L + 7`. The one level of question 2 is paid for here by the index clauses, exactly as in
  batch 48.

* **`w₄ = L+3 → L+2 → L+8 → L+1`** (`HPC/Fold/ProfileP.lean`). This walk had no engine at the
  branch's basepoint at all, "its engine being stated for an arm based at the walk's own trough".
  Under the reflection `g = 2L + 9 - f` the walk becomes `leg3Walk L (L + 9) (L + 7) (L + 7)` — a
  three-leg walk whose trough is its own peak — and the arm of the branch becomes an arm based at
  `L + 5 = P - 2`. So the engine is needed at a basepoint far above `L + 4` and for an arm starting
  two levels below the walk's trough. `foldsOnto_leg3_profileP_min` removes both restrictions:

  * the announcement of the descents is asked at the threshold `P - 3`, which is what the walk's
    first leg fails to serve, rather than at `L + 1`. For `P ≤ L + 4` that is the same clause or a
    weaker one, so nothing is lost at the old basepoints;
  * the arm may start anywhere in the window `[P - 2, P]` of the walk's first position;
  * the trough may be the peak (`P ≤ K`, where the earlier engines asked `P + 1 ≤ K`), which forced
    primed copies of `val3_bounds`, `val3_walk` and `foldsOnto_leg3_of_val3`.

  Read back through the reflection this asks of an arm `f` of the branch a clause the previous
  batch's landmark reading of `w₄` did not have:

  > **`MidW4`**: before every ascent to `L + 5` a time at `L + 3` or below, at a step at least `1`
  > and at least two steps earlier.

  It is necessary (`midW4_of_foldsOnto_w4`: an ascent to `L + 5` is served only by the positions
  `3` and later of `w₄`, and the landmark `1` carries `L + 2`), and it is what separates `w₄` from
  the walks that climb first: `w₄` descends before it climbs, so the two-step arm `L+4, L+5` folds
  onto no prefix of it while satisfying `CeilW4` and `BottomW4` vacuously. With it:

  > `foldsOnto_w4_iff_landmark`: for a 1-Lipschitz arm of `[L, L + 9]` based at `L + 4`, folding
  > onto `w₄` **is** `MidW4 ∧ CeilW4 ∧ BottomW4`.

  Sufficiency needs only `MidW4` and `BottomW4`; in the form the proof consumes, `MidW4` already
  implies `CeilW4`.

With the three criteria exact, `HPC/Fold/ThreeWalks.lean` closes the loop.
`ThreeWalksSentence g t L` is the disjunction of the three landmark sentences, each read on both
arms, and

> `three_walks_iff_sentence`: for two 1-Lipschitz arms of the band based at `L + 4`, the two arms
> fold onto one of the three walks — both onto the same one — **exactly when** one of the three
> sentences holds of both.

So `unserved_three_walks` is now: *an unserved pair of the branch satisfies one of three explicit
sentences about the levels of its two arms* (`unserved_three_walks_of_sentence`,
`unserved_three_walks_iff_sentence`, `s3_span_nine_mid4_of_sentence`). No fold appears in it. The
three sentences are genuinely different:

| walk | what each arm must satisfy |
|---|---|
| `w₃` | `Leg3Land`: descents to `L + 1` announced at `L + 5` (step ≥ 3, gap ≥ 4); ascents to `L + 8` announced at `L + 5` then `L + 2` |
| `w₄` | `MidW4`: ascents to `L + 5` announced at `L + 3` (step ≥ 1, gap ≥ 2); `BottomW4`: descents to `L` announced at `L + 3` then `L + 7` |
| `w₅` | `Valley5`: descents to `L + 1` announced at `L + 6` (step ≥ 4, gap ≥ 5); `TopW5`: ascents to `L + 9` announced at `L + 6` then `L + 2` |

Two further consequences are in the same file. `three_walks_w3_of_land`: the first disjunct of the
item needs nothing but `Valley4` and `Leg3Ceil` on both arms — no crookedness, no hypothesis on the
pair. And `unserved_three_walks_or_cross`: at any pair of the branch, either the first walk already
serves both arms, or some arm fails one of the two clauses and is therefore served by a canonical
walk (`leg3Valley_or_vee`, `leg3Ceil_or_lam` of batch 48). So what the item asks is entirely a
statement across the basepoint.

### 2.2 `cross_valley_profile`

Still open, and still in the shape batch 50 left it: a theorem off the residual configuration
(`cross_valley_profile_of_not_residual`), with the residue a statement about the three steps either
side of the basepoint. This batch adds no case analysis to it; it adds the measurement of what the
relaxed clause is worth (§3.3), which is a negative answer.

### 2.3 `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`

Untouched: they rest on §2.1 and on the `L + 5` branch, and no part of either was closed this
batch.

## 3. The questions of §2

### 3.1 The sufficiency halves for `w₄` and `w₅` — **yes, both, and the three criteria are exact**

Answered in §2.1. Both engines are of the batch-48 kind: numerical invariants on the greedy time
with the walk's landmark positions as constants (`prog3_profileK`, `gseq3_invK`; `val3_gstepP`,
`prog3_profileP`, `gseq3_invP`). The three exact criteria do make `unserved_three_walks` a
statement about crookedness and three sentences, and that statement is
`unserved_three_walks_iff_sentence`.

What the engines cost in generality is worth recording: the peak `K`, the trough `P`, the starting
window `[P - 2, P]` and the two index constants `a = K - P + 1`, `b = K - L - 1` are now parameters,
so a fourth walk of the same three-leg shape would need no new engine — only its landmark reading.

### 3.2 The one level — where it is paid for

Both new criteria pay the level the same way batch 48 did: the clause returns a time at `K - 1`
(one below the peak), which is exactly what the general crookedness clause supplies, and the
missing level is paid for with index bounds — `a ≤ j` (the clock reaching the peak position) and
`j + b ≤ k` (the slack clock crossing from the peak to the valley). The commission asks the
question about `Itinerary.lean` rather than about span nine, and nothing in this batch bears on the
three-link form: the engines are statements about a point sequence `ρ` and use no link. What the
batch does show is that at the level of *arms* the gap is closed for every walk of the branch, so
whatever remains of the one level is not a defect of the criteria.

### 3.3 `ValleyResidual` as a pair, and the relaxed criterion — **the relaxed criterion is not
enough**

The first half is unchanged: no pair realising `ValleyResidual` with a failing arm and an other arm
missing the V-walk has been found, and none is excluded.

The second half is answered negatively, in Lean (`HPC/Fold/Relaxed.lean`). `Relaxed f L` is the
clause that batch 50 proved to hold with no exceptional case: before every ascent to `L + 7` a time
at `L + 3` or below, at a step at least four. For each of the five walks of the development there
is an arm of the band based at `L + 4`, of at most nine steps, satisfying the clause and not
folding onto that walk (`relaxed_serves_no_walk`, every fold verdict decided in the kernel):

* `L+4, L+3, L+2, L+1` — vacuous in the clause, too early at the valley for the Λ-walk, `w₃`
  and `w₅`;
* `L+4, L+5` — the trough clause `MidW4` fails at once, so not `w₄`;
* `L+4, L+3, L+2, L+2, L+3, L+4, L+5, L+6, L+7` — announced at its step `4`, and still not the
  V-walk.

Outside Lean, `census-batch51.py` searches every walk of at most three turns over the band with a
basepoint in `[L + 3, L + 5]` against all 63 646 arms of at most eleven steps satisfying the
clause: **no walk serves them all**. In the other direction the same search finds that every such
arm does fold onto at least one of the five, which is the honest statement of what the relaxed
clause is worth: it does not name a walk, and it does not by itself decide one.

## 4. The censuses

### 4.1 Over the general model: `census-batch51.c` (log `census-batch51.log`)

Generators, over the two base chains `bing 0 9` and `bing 9 0` (all pairs verified against
`IsCrookedIvF` before use, every fold decided by the dynamic program of `HPC/Fold/Decide.lean`):

| generator | pairs | branch basepoints | unserved | non-thin links |
|---|---|---|---|---|
| the thin chains | 2 | 364 | 110 | 0 / 1 972 |
| single shavings | 576 | 105 004 | 31 596 | 576 / 567 936 |
| single fills | 576 | 104 832 | 31 680 | 576 / 567 936 |
| random mixtures (rate 1/3) | 80 | 16 987 | 3 419 | 15 472 / 78 880 |
| heavy mixtures (rate 1/2, and the total mixture) | 82 | 19 047 | 3 543 | 24 257 / 80 852 |
| random faithful perturbation walks | 62 | 11 390 | 3 456 | 982 / 61 132 |
| **all** | **1 378** | **257 624** | **73 804** | **41 863 / 1 358 708 (3.081 %)** |

Results over the whole corpus:

* `unserved_three_walks`: served by `w₃` 73 733, by `w₄` 10 750, by `w₅` 72 052; by one of the three
  73 804; **by none, 0**.
* `three_walks_iff_sentence`: the sentence holds at all 73 804 unserved pairs and agrees with the
  fold verdicts at every one — 0 disagreements.
* `cross_valley_profile`: 49 756 tests, 0 failures.
* **exactness audits** — the census checks its own predicates against the three equivalences proved
  this batch, in both directions, on every arm: `w₃` 515 248 checks, `w₄` 515 248, `w₅` 515 248,
  **0 failures**. A disagreement would be a bug in the census, since the three are theorems.
* necessity audits (batch 50's): `w₃` 448 825, `w₄` 217 263, `w₅` 384 085 checks, 0 failures.
* `leg3Valley_or_vee` 54 064 confirmations, `leg3Ceil_or_lam` 12 359, Valley4-or-vee 54 064; 0
  failures of any.

### 4.2 Over arms alone: `census-batch51.py` (log `census-batch51-arms.log`)

This one says so: it is a census over arms, not over crooked pairs. Exhaustively over all 713 817
1-Lipschitz arms of `[L, L + 9]` based at `L + 4` of at most thirteen steps, and over 200 000 random
arms of fourteen to forty steps, it compares the fold onto `w₄` with `MidW4 ∧ CeilW4 ∧ BottomW4`,
in the commissioned and in the minimal form: **0 disagreements in either direction**. It was this
census that found the missing clause — before `MidW4` was added, 277 506 of the 713 817 arms
satisfied the batch-50 sentence and did not fold — and the clause reached Lean only after the
census agreed with it. The relaxed-clause search of §3.3 is in the same file.

### 4.3 The definition audit: `HPC/Fold/Audit51.lean`

Generated by `gen-audit51.py` from `census-batch51-audit.txt`, the sample the census writes as it
runs: **13 arms of the census, 14 predicates, 182 kernel checks, every one agreeing with the
census**. The predicates audited are `HighAt`, `Leg3Valley`, `Leg3Ceil`, `Valley4`, `Valley5`,
`CeilW4`, `BottomW4`, `TopW5`, the new `MidW4`, and `FoldsOnto` for each of the five walks. No
census of this batch is unaudited.

## 5. What is in Lean

| file | what it adds |
|---|---|
| `HPC/Fold/ProfileK.lean` | the profile engine with the peak as a parameter; `foldsOnto_w5_profile_min`; `foldsOnto_w5_iff_landmark` |
| `HPC/Fold/ProfileP.lean` | the engine with the trough as a parameter and the arm starting below it; `MidW4` and its necessity; `foldsOnto_w4_profile_min`; `foldsOnto_w4_iff_landmark` |
| `HPC/Fold/ThreeWalks.lean` | `ThreeWalksSentence`; `three_walks_iff_sentence`; the work item and the branch restated on it |
| `HPC/Fold/Relaxed.lean` | `Relaxed`; the five kernel refutations, `relaxed_serves_no_walk` |
| `HPC/Fold/Audit51.lean` | the definition audit: 13 arms, 14 predicates, 182 kernel checks |

All of it is `sorry`-free and depends only on `propext`, `Classical.choice`, `Quot.sound`; no
`native_decide` is used anywhere. The `sorry`s of the development are exactly the ones batch 50
left: `cross_valley_profile`, `unserved_three_walks`, `s3_span_nine_mid5` in
`HPC/Fold/Mixed.lean`, the two of `HPC/Fold/General.lean`, and the older work items of
`Closure.lean`, `Minimal2.lean`, `Step.lean`, `Span.lean`, `Open.lean`.

## 6. What the batch does not settle

The work item itself. Both halves of the branch now read as sentences about the levels of the two
arms, and at no pair of any census does the sentence fail; what is missing is the crookedness
argument that produces one of the three sentences from the failure of the two canonical walks.
`cross_valley_profile` keeps its one configuration, and the relaxed clause — the one thing that
holds there with no exception — is now known not to name a walk by itself.
