# Report: batch 57 — the branch `L + 5` does not reflect, and the one level that stops it

## 0. The refutation, first

**The valley crossing does not reflect.** Question 1 asks whether the branch `L + 5` yields to the
law that closed the branch `L + 4` — the crookedness clause read at the two arms' own levels, then
`ivSep` — now that the arms can be read upside down and the interval clause is symmetric under
`(ρ, σ) ↦ (a − σ, a − ρ)`. It does not, and the first crossing is already false.

`ReflValleyCrossL5` (`HPC/Fold/Audit57.lean`) is `cross_valley_vee_pair` written out with the
basepoint at `L + 5`, the branch hypothesis `LowAt (L + 1) (L + 8)` on both arms, and every arm
replaced by its reflection `armRefl (L + (L + 9))`:

> if the reflection of either arm fails `Leg3Valley`, then both reflected arms fold onto the V-walk
> based at `L + 5`.

**`not_reflValleyCrossL5` is a theorem**: the statement is false. The witness is an explicit
faithful pair of 71 links — the window `[676, 746]` of a faithful random mixture (rate 1/3) of
Bing's chain `bing 0 9`, 986 links, emitted and shrunk by `census-batch57.c` — with the basepoint
at its index `56`, where
`ρ` stands at `L + 5` (with `L = 0`). Every clause is put to the kernel:

* `Audit57.faithful : IsCrookedIvF rho71 sig71` — **faithfulness itself is proved**, not assumed,
  by the interval form of the search of `HPC/Fold/DichotomyFaithful.lean`: for each link and each
  pair of levels at distance three or more, the clause is checked at the least index at which the
  far level is met, which suffices because the clause is monotone in the far index;
* the band `[L, L + 9]`, `ρ` at `L + 5` at the basepoint, and both arms `LowAt (L + 1) (L + 8)`;
* the reflection of the forward arm (15 links) fails `Leg3Valley`;
* the reflection of the backward arm (57 links) **does not fold** onto the V-walk based at `L + 5`,
  by the dynamic program of `HPC/Fold/Decide.lean`.

Earlier audits of non-thin pairs (batches 50–52, 55) left faithfulness to the census; this one does
not, so the refutation is unconditional. Axioms: `[propext, Classical.choice, Quot.sound]`.

**What is short is exactly one level, and it is a level, not an index.** The positive half of the
same reading is proved in the new file `HPC/Fold/FloorFar.lean`. At the branch `L + 5` the two
timing bounds of batch 56 survive verbatim — the clause returns two links, one twenty-nine steps
from the ascent and one twelve steps from it — so the witness is still forced ten steps past the
basepoint (`cross_high_fwd_far`, `cross_high_bwd_far`, and the arm-level corollaries
`critLamIv_armT_of_fail_armG`, `critLamIv_armG_of_fail_armT`). But the level it is returned at is
one too low: reading the clause upwards at an ascent `k = ρ t ≥ L + 8` gives a link `r` with

```
ρ r ≤ k − 1 ≤ σ r,   hence   L + 6 ≤ ρ r ≤ L + 7   and   L + 7 ≤ σ r,
```

so the *interval* of the witness reaches `L + 7` while its `ρ` may sit at `L + 6` — and the
Λ-criterion of the branch `L + 5` reads `ρ`. The asymmetry is in the model: a link is the interval
`[ρ, ρ + 1]`, so a level read from below and a level read from above differ by one. The census
confirms the shape precisely: over 1 378 202 basepoints of the branch, the V-criterion on the
partner arm fails in point form at **486** pairs and in interval form at **none** — at every
failure, and only there, the interval form saves what the point form loses.

No §1 target is refuted: `ReflValleyCrossL5` is a statement about the route, not one of the
commissioned statements.

---

## 1. The targets

1. **`s3_span_nine_mid5` (`Mixed.lean`) — not proved.** The route through
   `s3_span_nine_mid5_of_sentence` is now known to be insufficient over the corpus as well as
   refuted in its crossing: the five reflected walks (the two reflected canonical walks and
   `w₃ᴿ`, `w₄ᴿ`, `w₅ᴿ`) leave **950** of 1 378 202 basepoints of the branch unserved, so
   `ThreeWalksSentence5` cannot hold at every unserved pair. The docstring of the target now
   records what is known and what the next route has to be.
2. **`s3_span_nine` (`General.lean`) — not proved**, since it waits on the branch `L + 5`;
   `s3_span_nine'` derives it from the two branches as before.
3. **`s3_general`, `theorem3` — not proved.**

What is added to the route:

| result | file | status |
|---|---|---|
| `not_reflValleyCrossL5` — the reflected valley crossing is false | `HPC/Fold/Audit57.lean` | proved |
| `Audit57.faithful` — the 71-link counterexample pair is faithful | `HPC/Fold/Audit57.lean` | proved |
| `cross_high_fwd_far`, `cross_high_bwd_far` — the far witness at `L + 5`, in interval form | `HPC/Fold/FloorFar.lean` | proved |
| `critLamIv_armT_of_fail_armG`, `critLamIv_armG_of_fail_armT` — the same on the arms | `HPC/Fold/FloorFar.lean` | proved |

---

## 2. The questions

### 2.1 Question 1 — does the branch `L + 5` yield to the interval clause and `ivSep`?

**No, and the obstruction is exactly one level.** §0 is the answer: the two bounds transport, the
level does not, and the first crossing of the reflected route is false at a faithful pair. Three
further facts from the census sharpen it.

* **The failure needs several non-thin links.** The reflected valley crossing holds at every
  basepoint of the thin chains, of all 576 single shavings, of all 576 single fills and of the
  faithful perturbation walks; it fails only on mixtures — 178 of 2 394 at rate 1/3, 302 of 2 002
  at rate 1/2, 6 of 162 042 on the chains outside Bing's family. One shaved peak or one filled
  valley is not enough to lose the level; a run of them is.
* **The reflected ceiling crossing fails too.** The gap statement (`TopW5` on the failing arm,
  `Valley5` on the other) fails at **916** pairs of the branch, against **0** at the branch `L + 4`.
* **The branch hypothesis is not the mirror of the one at `L + 4`.** `LowAt (L + 1) (L + 8)` does
  not reflect to `HighAt (L + 1) (L + 8)`: at **298 522** of the 1 378 202 basepoints the reflected
  arms fail `HighAt`, because `LowAt` carries a second clause that `HighAt` does not. So even the
  hypotheses of the two branches are not mirror images, quite apart from the crossings.

**What the branch needs instead.** A walk whose criterion consumes a witness at `L + 6` rather than
`L + 7`. The four-leg walk `L+4 → L+7 → L+1 → L+8 → L+1` (`foldsOnto_walk47181`,
`HPC/Fold/CoverL5.lean`, proved in batch 56) is the natural candidate: its floor announcement is
met by a time at `L + 3` followed by one at `L + 6` — exactly the pair of links the crookedness
clause returns — and it alone serves 749 of the 950 residual basepoints. What is missing for it are
its other two announcements, which still read `L + 7` and `L + 9` on `ρ`. That is the next batch's
question, and it is now a precise one.

### 2.2 Question 2 — is the `L + 4` proof a template, and if so what is the induction on?

**Not as it stands: the step that does not generalise is the one this batch refutes.** The shape of
the `L + 4` proof is: the leaf of `s3_span_seven_of_cases`; a split by `dichotomy_at`; for each
branch a finite list of walks with exact landmark criteria; arm-only dichotomies putting a failing
arm onto a canonical walk; crossings closed by the clause at the arms' own levels and `ivSep`. Of
these four ingredients, three do generalise and one does not.

* **The walks and their criteria generalise.** `foldsOnto_leg4W` and its predecessors give an
  exact criterion for every walk of a wide window, at any span, and `HPC/Fold/ArmReflect.lean`
  transports each criterion through the reflection of an arm. Nothing in this machinery is special
  to span nine.
* **The timing generalises.** `ivSep` is stated for any level distance `d` and gives `z d − 1`
  steps; the crossing lemmas of `HPC/Fold/FloorFar.lean` are the same proof at a different pair of
  levels. This is the part of batch 56 that is genuinely a law and not a computation.
* **The dichotomies do not generalise by reflection.** `CrookUp` and `CrookDown` are not mirror
  images (batch 48, `HPC/Fold/ArmReflectGap.lean`), and the crossing that replaced them at
  `L + 4` is false at `L + 5` (§0). Concretely: the model's clause reads a level *from below* on
  `ρ`, so it is one level stronger in one direction than the other, and a branch whose criteria
  need the weak direction is not served.

So the template is: *list of walks + exact criteria + timing law*, with the choice of walks made so
that their announcements are on the side the clause reads well. If there is an induction, it is on
the span with that choice as the inductive data — for each `(span, basepoint level)` a finite list
of walks and a rule choosing among them — and not on a symmetry of the model, because the model has
none: the reflection of a faithful pair `(ρ, σ)` is `(a − σ, a − ρ)`, whose point sequence is
`a − σ` and not `a − ρ` (batch 48), and that single link of slack is what §0 exhibits. A statement
of `S3` at every span by this route therefore needs, at each span, a proof that the finite list of
walks is exhaustive; no such proof exists at any span above nine, and at span nine it exists only
for the branch `L + 4`.

### 2.3 Question 3 — Bing's seam with the end clause imposed

**Imposing the clause changes nothing: it excludes no consolidation, and the batch-56 table is
reproduced exactly.** `seam-batch57.py` (log `seam-batch57.log`) repeats `seam-batch56.py` with `H`
restricted to the width-two consolidations of the inner chain with respect to `E(2, m − 1)` that
satisfy Bing's end clause — *any link of `H` containing an end link of the inner chain which meets
its extreme link lies in that link and its neighbour*, which for a width-two block is the window
`{e₂, e₃}` at the low end and `{e_{m−2}, e_{m−1}}` at the high end.

| pass | basepoints | with an `H` satisfying the clause | `h_u` inside the end links | `F` a chain | `d_i` first only | blocks of `F` of width ≥ 3 | seam widths |
|---|---|---|---|---|---|---|---|
| thin: `bing 0 4`, `0 5`, `0 6` | 84 | **84** | 0 | 59 | 25 | 0 | [2] |
| general: nine single shavings of `bing 0 6`, `bing 0 7` | 820 | **820** | 0 | 357 | 463 | 0 | [2] |

Over the whole run, **2 028 of the 2 028** least consolidations satisfy the end clause, and at **0**
basepoints does none — so the answer to the sub-question is that such an `H` exists at every
basepoint, and moreover the clause is not binding at the least number of blocks. The reason is
visible in the small cases: the inner chain spans the levels `1 … m − 2`, so a consolidation of the
least size is forced to put its extreme blocks at the windows `{1, 2}` and `{m − 3, m − 2}`, which
is what the clause asks.

Consequently the batch-56 findings stand unchanged with the clause imposed: no seam of width three
anywhere, `h_u` never inside the two end links, `F` a chain at 59 of 84 (357 of 820), `d_i` in the
first link of `F` only at 25 of 84 (463 of 820). The repair recorded for completeness — keep `h_u`
as a block of `F` — again restores a chain at 54 of 84 and 570 of 820, with seams of width 1 (thin)
and 1 or 2 (general).

---

## 3. The census

`census-batch57.c`, log `census-batch57.log`; same generators, same faithfulness test, same fold
program and the same audit protocol as batch 56. 3 759 faithful pairs, 5 877 570 links, 45 490
non-thin. At every basepoint of the branch `L + 5` the two arms are reflected in the level 9 and
the four statements of the branch `L + 4` are evaluated on the reflections.

The branch `L + 4` is re-checked unchanged, and the three theorems of batch 56 fail nowhere:
valley failures 210 369 with 0 misses of the V-walk, the witness never before index 12 (least index
seen 12), ceiling failures 53 790 of which 558 miss the Λ-walk with 0 failures of the gap,
`CeilHighResidual` 0, unserved pairs 325 640 served by none of `w₃`, `w₄`, `w₅`: 0.

The branch `L + 5`, by corpus:

| corpus | basepoints | served by a reflected walk | residue | reflected valley failures / then missing the V-walk | ceiling gap failures | `LowAt` not reflecting to `HighAt` |
|---|---|---|---|---|---|---|
| thin chains | 464 | 464 | 0 | 70 / 0 | 0 | 100 |
| single shavings | 133 462 | 133 462 | 0 | 20 132 / 0 | 0 | 28 770 |
| single fills | 133 632 | 133 632 | 0 | 20 160 / 0 | 0 | 28 800 |
| random mixtures (1/3) | 16 678 | 16 326 | 352 | 2 394 / 178 | 333 | 4 090 |
| heavy mixtures (1/2, and the total mixture) | 16 223 | 15 637 | 586 | 2 002 / 302 | 570 | 4 251 |
| faithful perturbation walks | 1 614 | 1 614 | 0 | 248 / 0 | 0 | 338 |
| outside Bing's family, and concatenations | 1 076 129 | 1 076 117 | 12 | 162 042 / 6 | 13 | 232 173 |
| **all** | **1 378 202** | **1 377 252** | **950** | **207 048 / 486** | **916** | **298 522** |

In every one of the 486 failures the V-criterion on the partner arm fails in point form and holds
in interval form; the interval form fails **0** times, which is `cross_high_fwd_far` on the corpus.

All 950 residual basepoints are served by a walk of the wide four-leg family (0 by none), and a
greedy cover needs three walks: `L+4 → L+7 → L+1 → L+8 → L+1` (749), the reflected
`L+6 → L+3 → L+7 → L+1 → L+8` (105 more) and `L+4 → L+7 → L+2 → L+8 → L+1` (the last 96) — the same
three walks batch 56 proved criteria for in `HPC/Fold/CoverL5.lean`.

**Definition audit.** Every predicate the census is offered as evidence for is evaluated by its own
definition, none by a proxy: `IsCrookedIvF` (`le`, `width`, `adj`, and the crooked clause with
interval triggers); `IsLip`; `HighAt (L+1) (L+8)`; `LowAt (L+1) (L+8)`; `Leg3Valley`; `Leg3Ceil`;
`Valley5`; `TopW5`; `armRefl` (the reflection of an arm in the level 9); `FoldsOnto` by the dynamic
program of `HPC/Fold/Decide.lean`, for the Λ-walk, the V-walk, `w₃`, `w₄`, `w₅`, their reflections
and every walk of the four-leg family; the three residues. The interval form of the V-criterion is
reported as such: it is the definition with `ρ` replaced by the interval `[ρ, σ]` at the witness.

---

## 4. Deliverables and audit

1. **Proved, `sorry`-free.** New files `HPC/Fold/FloorFar.lean` (the far witness at the branch
   `L + 5` in interval form) and `HPC/Fold/Audit57.lean` (the faithful counterexample and the
   refutation). Both are in `HPC.lean`; `lake build HPC` is clean; no `sorry` in either file, no
   `native_decide`, no new `axiom`, no `@[implemented_by]`.

   ```
   'HPC.Fold.not_reflValleyCrossL5'          depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.Audit57.faithful'               depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.cross_high_fwd_far'             depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.critLamIv_armT_of_fail_armG'    depends on axioms: [propext, Classical.choice, Quot.sound]
   'HPC.Fold.critLamIv_armG_of_fail_armT'    depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

2. **Census over the general model, under the audit protocol**: `census-batch57.c`, log
   `census-batch57.log`. Every statement it reports on the branch `L + 5` is read on the reflected
   arms of the pair, never on an arm alone.

3. **The §2.3 table with its program**: `seam-batch57.py`, log `seam-batch57.log`.

4. **Still open**: `s3_span_nine_mid5`, `s3_span_nine`, `s3_general`, `theorem3`. The sorries of
   the route are unchanged in number; what changed is that one of the two routes to the branch
   `L + 5` is closed by a theorem rather than by a measurement, and the level that closes it is
   named.
