# Report: batch 39 — span eight, off the middle level

Three new files, `HPC/Fold/Crook.lean`, `HPC/Fold/Leg3.lean` and `HPC/Fold/Span8.lean`; root
`HPC.lean` updated; `README.md` notes the batch. Nothing else is touched — the forty-eight
earlier Lean files are byte-identical to the batch-38 delivery. The census programs are
`census-batch39.c` and `census-batch39b.c`, the output is `census-batch39.log`.

## 0. No counterexample, and what is new

**No counterexample to `theorem3` was found**, and nothing in this run suggests one. The
commissioned open statement in `HPC/Fold/Open.lean` keeps its `sorry`; it is still the only
`sorry` in the project.

What the run delivers is span eight, away from one basepoint height:

> **`s3_span_eight_off_center`.** Let `ρ` be (the minimal-index reading of) a faithful crooked
> sequence with values in `[L, H]` and `H ≤ L + 8`. Then every basepoint `i` is served — the two
> arms at `i` fold onto one common walk — except possibly one with `ρ i = L + 4` when the span is
> exactly eight.

and its chain-level reading `theorem3_span_eight_off_center`. Everything is `sorry`-free with
axiom profile inside `propext`, `Classical.choice`, `Quot.sound`.

## 1. The crookedness clause family on an arm (`HPC/Fold/Crook.lean`)

Batch 38 used a single instance of the crookedness clause on an arm (`Zig`: between a time at
`L + 1` or below and a later time at `H` the arm has been at `H − 2` or above and afterwards at
`L + 2` or below). This file proves the clause in full, on both arms, at every span:

```
CrookUp   f : s < t, f s + 3 ≤ f t  →  ∃ s<u<u'<t,  f u ≥ f t − 2  ∧  f u' ≤ f s + 1
CrookDown f : s < t, f t + 3 ≤ f s  →  ∃ s<u<u'<t,  f u ≤ f t + 1  ∧  f u' ≥ f s − 2
```

`crookUp_armG`, `crookUp_armT`, `crookDown_armG`, `crookDown_armT`. The level forms
`CrookUp.levels` and `CrookDown.levels` are what the leaves use: for `a + 3 ≤ b`, a time at
`a` or below followed by a time at `b` or above forces, in between, a time at `b − 2` or above
followed by a time at `a + 1` or below. `Zig` is the instance `a = L + 1`, `b = H`
(`zig_of_crookUp`), so batch 38's `zig_armG`/`zig_armT` are corollaries. Two immediate
consequences are recorded: a crooked arm can neither descend (`no_monotone_drop`) nor climb
(`no_monotone_climb`) three levels monotonically.

## 2. The three-leg folding engine (`HPC/Fold/Leg3.lean`)

Batch 38's span-seven leaf walk `walk7` is one member of a family: from `P − 1` up to a peak `K`,
down to `L + 1`, up to `H − 1`. `leg3Walk L H K P` is the family, `leg3Len` its number of times,
and `foldsOnto_leg3` the folding theorem, for any band `[L, H]`, any peak `P + 1 ≤ K ≤ H − 1` and
any basepoint `L + 2 ≤ P ≤ L + 3`.

The fold is the greedy time assignment (`gstep3`, `gseq3`): at each step the arm is carried as far
along the walk as its new level allows. The invariant `gseq3_inv` is the window condition `Val3`
together with four progress clauses, each switched on by a feature of the arm's past:

```
E  : the arm has been at L + 1 or below
E2 : the arm has been at K + 1 or above, or E and after that at K or above
R  : the arm has been at K or above, or E and after that at K − 1 or above
S  : E2, and after that the arm has been at L + 2 or below (or the arm has been at L)
```

The arm enters only through two announcements — this is the whole interface of the engine:

* **floor.** Every descent to `L` is preceded by a time at `K` or above, or by a time at `L + 1`
  or below followed by one at `K − 1` or above.
* **ceiling.** Every ascent to `K + 2` or above is preceded by a time at `L`, or by two times, in
  order, at `K + 1` or above and at `L + 2` or below, or by three times, in order, at `L + 1` or
  below, at `K` or above, and at `L + 2` or below.

No crookedness is used inside the engine, so its reflection is free (`leg3Walk'`,
`foldsOnto_leg3'` in `HPC/Fold/Span8.lean`) and it serves basepoints near the top of the band as
well as near the bottom.

The two-time form of the ceiling announcement is what makes the basepoint `L + 5` work; with only
the three-time form that basepoint is out of reach, because at span eight a time at `H − 1` or
above can only be announced by a time at `H`.

## 3. Span eight (`HPC/Fold/Span8.lean`)

`s3_span_seven_of_cases` (batch 38) reduces every span to the *leaf*: both arms `HighAt (p−3) H`
and both arms `LowAt L (p+3)`, where `p = ρ i`. At span eight the near-extreme theorem disposes of
`p ≤ L + 2` and `p ≥ L + 6`, leaving `p ∈ {L+3, L+4, L+5}`. One further application of
`dichotomy_at` splits each surviving height into two branches, and each branch names a peak:

| basepoint | split | branch | peak | walk |
|---|---|---|---|---|
| `L+3` | `(L, L+7)` | `HighAt` | `K = L+5` | `L+2,…,L+5,…,L+1,…,L+7` |
| `L+3` | `(L, L+7)` | `LowAt`  | `K = L+6` | `L+2,…,L+6,…,L+1,…,L+7` |
| `L+5` | `(L+1, L+8)` | `LowAt`  | `K = L+5` | the reflection of the first |
| `L+5` | `(L+1, L+8)` | `HighAt` | `K = L+6` | the reflection of the second |

At `L + 3` the floor announcement is the leaf (or branch) `LowAt` and the ceiling announcement is
the `HighAt` condition followed by one instance of `CrookUp.levels`. At `L + 5` — where the arm is
reflected, so that the engine sees the basepoint `L + 3` again — **no crookedness clause is
needed**: the leaf `HighAt (L+2) (L+8)` is exactly the engine's floor announcement and the branch
condition is exactly its two-time ceiling announcement.

`foldsOnto_span8_low_high`, `foldsOnto_span8_low_low`, `foldsOnto_span8_high_low`,
`foldsOnto_span8_high_high` are the four leaves; `s3_span_eight_off_center` assembles them with
`s3_near_extreme`, `s3_of_not_highAt`, `s3_of_not_lowAt` and `s3_span_seven`, and
`theorem3_span_eight_off_center` reads the result on crooked chains (the off-centre hypothesis
there is `minIdx i ≠ minIdx s + 4` for every `s`, which is what `ρ i ≠ L + 4` becomes when `L` is
the floor of the minimal-index range).

## 4. What is left: the middle basepoint

The open case is a basepoint exactly four levels above the floor, at span exactly eight. It is
genuinely different, and not for want of searching:

* The three-leg engine needs `L + 2 ≤ P ≤ L + 3`; a middle basepoint is at distance four from both
  ends, so neither the engine nor its reflection applies to it.
* `census-batch39.c` searches, with the leaf conditions, the full crookedness clause family and
  one dichotomy split, for three-leg walks of length at most eighteen serving both branches. For
  the basepoints `L + 3` and `L + 5` it returns exactly the four walks formalised here; for
  `L + 4` it returns `NOT SOLVED` (`census-batch39.log`).
* `census-batch39b.c` checks whether the span-eight leaf can instead be split into branches on
  which batch 38's bump-walk theorem already applies; it cannot, already at span seven.

The obstruction is easy to describe. A split at `(L, th)` is informative only on its `HighAt`
side, because `LowAt L th` for `th ≤ L + 7` already follows from the leaf condition
`LowAt L (L + 7)`; so the residual case at `L + 4` carries the leaf conditions together with the
`LowAt` side of every split, and then no condition announces a high time before a low one. Any
walk serving that case must therefore distinguish arms by a feature that no monotone three-leg
fold records. A four-leg engine (two peaks, with a reset-based feature set) is the natural next
step.

## 5. Verification

`lake build HPC` succeeds with one `sorry` warning, `HPC/Fold/Open.lean:47` — the commissioned
open statement — and no others. `#print axioms` for `s3_span_eight_off_center`,
`theorem3_span_eight_off_center` and `foldsOnto_leg3` reports `propext`, `Classical.choice`,
`Quot.sound`.
