# Report: batch 40 — span eight, every basepoint

Four new files, `HPC/Fold/Leg3Mid.lean`, `HPC/Fold/Span8Mid.lean`, `HPC/Fold/Leg4.lean`,
`HPC/Fold/Span8Mid4.lean`, and the assembly `HPC/Fold/Span8Full.lean`; root `HPC.lean` updated;
`README.md` notes the batch. Nothing else is touched — the earlier Lean files are byte-identical
to the batch-39 delivery. The search programs are `census-batch40.c` (the branching census with
the exact crookedness automaton) and `census-batch40b.c` (the announcement prober), with output
in `census-batch40.log` and `census-batch40b.log`.

## 0. No counterexample, and what is new

**No counterexample to `theorem3` was found**, and nothing in this run suggests one. The
commissioned open statement in `HPC/Fold/Open.lean` keeps its `sorry`; it is still the only
`sorry` in the project.

Batch 39 left exactly one case of span eight open: a basepoint standing exactly four levels
above the floor of a band of width exactly eight. This batch closes it, so span eight is now
complete:

> **`s3_span_eight`.** Let `ρ` be (the minimal-index reading of) a faithful crooked sequence with
> values in `[L, H]` and `H ≤ L + 8`. Then every basepoint `i` is served: the two arms at `i`
> fold onto one common walk.

and its chain-level reading

> **`theorem3_span_eight`.** For a crooked chain whose minimal-index range spans at most eight
> links, every basepoint admits a block map whose blocks each lie in three consecutive links of
> the coarse chain.

Both are `sorry`-free, with axiom profile inside `propext`, `Classical.choice`, `Quot.sound`.

## 1. The leaf, and why three legs are not enough

By `s3_span_seven_of_cases` (batch 38) a basepoint at level `p` can only fail when both arms are
`HighAt (p − 3) H` and both arms are `LowAt L (p + 3)`. With `H = L + 8` and `p = L + 4` that
leaf reads: both arms `HighAt (L+1) (L+8)` and both arms `LowAt L (L+7)`. Two applications of
`dichotomy_at`, at the level pairs `(L, L+8)` and `(L+1, L+7)`, split the leaf into four
branches, and the dichotomy gives the *same* branch for both arms, so a walk serving a branch
serves both arms at once.

The census `census-batch40.c` reads the crookedness clause family exactly: for each level pair
`(a, b)` with `a + 3 ≤ b` it carries a state machine (states 0/1/2/3, measured since the last
trigger level, with resets and two-sided witness windows) rather than the weaker single-flag
reading of batch 39. Sharpening the arm class this way makes the middle basepoint solvable at
splitting depth two, with the four walks (levels written as offsets from `L`)

| branch | walk |
|---|---|
| `LowAt (L,L+8)` and `LowAt (L+1,L+7)` | `3,4,5,6,5,4,3,2,3,4,5,6,7,6,5,4,3,2,1` |
| `LowAt (L,L+8)` and `HighAt (L+1,L+7)` | `5,4,3,2,3,4,5,6,7,6,5,4,3,2,1` |
| `HighAt (L,L+8)` and `LowAt (L+1,L+7)` | `3,4,5,6,5,4,3,2,1,2,3,4,5,6,7` |
| `HighAt (L,L+8)` and `HighAt (L+1,L+7)` | `5,4,3,2,3,4,5,6,5,4,3,2,1,2,3,4,5,6,7` |

The two mixed branches are three-leg walks; the two pure branches have four legs, and that is
forced: restricting the same search to three-leg shapes finds no solution even at splitting
depth three (second half of `census-batch40.log`).

## 2. The three-leg engine at a middle basepoint (`HPC/Fold/Leg3Mid.lean`)

The engine of batch 39 (`HPC/Fold/Leg3.lean`) assumed the basepoint at `L + 3`; several of its
announcement thresholds were written relative to the floor. `Leg3Mid.lean` is the same greedy
fold with the basepoint `P` allowed anywhere with `L + 2 ≤ P ≤ L + 4`: the thresholds attached to
the basepoint are written `P − 3, P − 2, P − 1`, while the thresholds tied to the walk's valley
stay at `L + 2`. Its interface is `foldsOnto_leg3M`; the reflected form `foldsOnto_leg3M'` (no
crookedness is used inside the engine, so reflecting an arm is free) lives in
`HPC/Fold/Span8Mid.lean`.

## 3. The two mixed branches (`HPC/Fold/Span8Mid.lean`)

* `foldsOnto_span8_mid_high_low` — branch `HighAt (L,L+8)`, `LowAt (L+1,L+7)`; peak `L + 6`. The
  engine's floor announcement is the branch condition `LowAt (L+1) (L+7)` read verbatim, and its
  ceiling announcement is the branch condition `HighAt L (L+8)`. No crookedness clause is needed.
* `foldsOnto_span8_mid_low_high` — the reflection of the previous one, through
  `foldsOnto_leg3M'`.

## 4. The four-leg engine (`HPC/Fold/Leg4.lean`)

`leg4Walk L H K M P` runs from `P − 1` up to the peak `K`, down to the valley `M`, up to `H − 1`,
and down to `L + 1`. The fold is again the greedy time assignment: at each step the arm is
carried as far along the walk as its new level allows (`gstep4`, `gseq4`). The invariant
`gseq4_inv` is the window condition `Val4` together with six progress clauses, each switched on
by a feature of the arm's past:

```
E  : the arm has been at P − 2 or below
R  : the arm has been at K or above, or E and after that at K − 1 or above
E2 : the arm has been at K + 1 or above, or E and after that at K or above
S  : the arm has been at M − 1 or below, or E2 and after that at M + 1 or below
S2 : the arm has been at M − 1 or below, or at K + 1 or above and after that at M or below
T  : the arm has been at K + 2 or above, or S2 and after that at H − 2 or above
```

The arm enters only through three announcements, and this is the whole interface
(`foldsOnto_leg4`):

* **floor.** Every descent to `M − 1` or below is preceded by a time at `K` or above, or by a
  time at `P − 2` or below followed by one at `K − 1` or above.
* **deep floor.** Every descent to `M − 2` or below is preceded by a time at `K + 2` or above,
  or by a time at `M − 1` or below followed by one at `H − 2` or above, or by three times, in
  order, at `K + 1` or above, at `M` or below, and at `H − 2` or above.
* **ceiling.** Every ascent to `K + 2` or above is preceded by a time at `M − 1` or below, or by
  two times, in order, at `K + 1` or above and at `M + 1` or below, or by three times, in order,
  at `P − 2` or below, at `K` or above, and at `M + 1` or below.

No crookedness is used inside the engine, so its reflection is free. The third clause of the
deep-floor announcement is genuinely needed: the prober `census-batch40b.c` shows the two-clause
version fails on the fourth branch, with the explicit violating arm recorded in
`census-batch40b.log`.

## 5. The two four-leg branches (`HPC/Fold/Span8Mid4.lean`)

Both use the parameters `H = L + 8`, `K = L + 6`, `M = L + 2`, `P = L + 4`.

* `foldsOnto_span8_mid_low_low` — branch `LowAt (L,L+8)`, `LowAt (L+1,L+7)`. The floor
  announcement is `LowAt (L+1) (L+7)`, the deep-floor announcement is `LowAt L (L+8)`, and the
  ceiling announcement is the leaf condition `HighAt (L+1) (L+8)` followed by one application of
  `CrookUp.levels` at the levels `(L + 2, L + 8)`.
* `foldsOnto_span8_mid_high_high` — branch `HighAt (L,L+8)`, `HighAt (L+1,L+7)`, the arm read
  upside down and folded onto `leg4Walk'`. The floor announcement of the reflected arm is
  `HighAt (L+1) (L+7)`, its ceiling announcement is the leaf condition `LowAt L (L+7)` (both of
  that condition's clauses), and its deep-floor announcement is the engine's three-time clause:
  `HighAt L (L+8)` gives an earlier time at `L + 1` or below, and one application of
  `CrookUp.levels` at the levels `(L + 1, L + 8)` inserts between it and the trigger a time at
  `L + 6` or above followed by a time at `L + 2` or below.

## 6. The assembly (`HPC/Fold/Span8Full.lean`)

`s3_span_eight_middle` does the middle basepoint: outside the leaf it defers to `s3_of_not_lowAt`
and `s3_of_not_highAt`, inside the leaf it branches on the two dichotomies and applies the four
folds above. `s3_span_eight` then drops the off-centre hypothesis of batch 39's
`s3_span_eight_off_center`, and `theorem3_span_eight` is the chain-level reading, obtained from
`s3_span_eight` exactly as `theorem3_span_eight_off_center` was obtained from its off-centre
predecessor.

## 7. Verification

`lake build HPC` succeeds. The only `sorry` in the project is the commissioned open statement at
`HPC/Fold/Open.lean:47`. `#print axioms` for `s3_span_eight`, `theorem3_span_eight` and
`foldsOnto_leg4` reports `[propext, Classical.choice, Quot.sound]`.
