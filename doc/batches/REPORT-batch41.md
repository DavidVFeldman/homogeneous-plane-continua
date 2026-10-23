# Report: batch 41 — span nine

Three new files, `HPC/Fold/Span9.lean`, `HPC/Fold/Span9Mid.lean` and `HPC/Fold/Span9Mid5.lean`;
root `HPC.lean` updated with their imports; `README.md` notes
the batch. Nothing else is touched — the earlier Lean files are byte-identical to the batch-40
delivery. The searches are `census-batch41.c` (the branching census of batch 40, with its
three-leg shape search replaced by a `k`-leg shape search), `census-batch41b.c` (a prober that
checks one explicit walk against one explicit class) and `census-batch41c.c` (the same census with
the walk family cut down to what the repository's engines can realize), with output in
`census-batch41.log`, `census-batch41b.log` and `census-batch41c.log`.

## 0. No counterexample, and what is new

**No counterexample to `theorem3` was found**, and nothing in this run suggests one. The
commissioned open statement in `HPC/Fold/Open.lean` keeps its `sorry`; it is still the only
`sorry` in the project.

Batch 40 completed span eight. At span nine the interior basepoints stand at `L + 3`, `L + 4`,
`L + 5` and `L + 6` (`s3_near_extreme` serves everything within two of an extreme). This batch
settles the two outer ones outright, and each of the two middle ones except for a single named
branch. First the outer ones:

> **`s3_span_nine_off_center`.** Let `ρ` be (the minimal-index reading of) a faithful crooked
> sequence with values in `[L, H]` and `H ≤ L + 9`. Then every basepoint `i` is served — the two
> arms at `i` fold onto one common walk — except possibly one with `ρ i = L + 4` or `ρ i = L + 5`
> when `H = L + 9`.

and its chain-level reading

> **`theorem3_span_nine_off_center`.** For a crooked chain whose minimal-index range spans at most
> nine links, every basepoint that stands neither exactly four nor exactly five above the range's
> floor admits a block map whose blocks each lie in three consecutive links of the coarse chain.

Then the two middle heights, one half of each (`HPC/Fold/Span9Mid.lean`,
`HPC/Fold/Span9Mid5.lean`):

> **`s3_span_nine_mid_low`.** At span nine a basepoint with `ρ i = L + 4` is served unless both
> arms are `HighAt (L + 1) (L + 8)`.
>
> **`s3_span_nine_mid_high`.** At span nine a basepoint with `ρ i = L + 5` is served unless both
> arms are `LowAt (L + 1) (L + 8)`.
>
> **`s3_span_nine_except`.** Everything above assembled: at span at most nine every basepoint is
> served except possibly one at `L + 4` whose two arms are both `HighAt (L + 1) (L + 8)`, or one
> at `L + 5` whose two arms are both `LowAt (L + 1) (L + 8)`.

All of these are `sorry`-free, with axiom profile `[propext, Classical.choice, Quot.sound]`.

## 1. The search

`census-batch41.c` is `census-batch40.c` with one change: the walk search, previously restricted
to three-leg shapes (up, down, up, or the reflection), now enumerates shapes with any number of
legs up to a bound given on the command line. Everything else — the exact crookedness automaton
for the whole clause family `Cl(a,b)`, `Dl(a,b)`, the `HighAt`/`LowAt` condition automata, the
unbounded reachability search over (level, condition flags, clause states, set of legal walk
times), and the recursive splitting on the dichotomy — is unchanged, so a positive answer covers
arms of every length.

Run at span nine, splitting depth two, at most five legs, walks of at most 22 times
(`census-batch41.log`):

* basepoint `L + 3`: solved, three three-leg walks;
* basepoint `L + 6`: solved, three three-leg walks;
* basepoints `L + 4` and `L + 5`: **not** solved at that depth and length.

So span nine splits the way span eight did, with the two middle heights the hard ones — only at
span nine there are two of them, and neither is served by any walk of at most five legs at
splitting depth two.

The walks printed by the census are not always the shortest or the most convenient ones; the
prober `census-batch41b.c` was used to confirm the six walks actually formalized, each of which is
exactly of the shape `leg3Walk` or of its reflection `leg3Walk'` (`census-batch41b.log`).

## 2. The leaf at height `L + 3`

By `s3_span_seven_of_cases` a basepoint at level `p` fails only if both arms are
`HighAt (p − 3) H` and both arms are `LowAt L (p + 3)`. With `H = L + 9` and `p = L + 3` that
leaf reads: both arms `HighAt L (L + 9)` and both arms `LowAt L (L + 6)`. Splitting with
`dichotomy_at` at `(L, L + 7)` and, on the `LowAt` side, again at `(L, L + 8)` gives three
branches (levels as offsets from `L`):

| branch | peak | walk |
|---|---|---|
| `HighAt (L, L+7)` | `L + 5` | `2,3,4,5,4,3,2,1,2,3,4,5,6,7,8` |
| `LowAt (L, L+7)` and `LowAt (L, L+8)` | `L + 7` | `2,3,4,5,6,7,6,5,4,3,2,1,2,3,4,5,6,7,8` |
| `LowAt (L, L+7)` and `HighAt (L, L+8)` | `L + 6` | `2,3,4,5,6,5,4,3,2,1,2,3,4,5,6,7,8` |

Each is `foldsOnto_leg3` (`HPC/Fold/Leg3.lean`) at `P = L + 3`, `H = L + 9` and the stated peak,
and the two announcements are read off as follows.

* `foldsOnto_span9_low_high`, peak `L + 5`: the floor announcement is the leaf
  `LowAt L (L + 6)` read verbatim; the ceiling announcement is the branch `HighAt L (L + 7)`
  followed by one application of `CrookUp.levels` at the levels `(L + 1, L + 7)`.
* `foldsOnto_span9_low_low`, peak `L + 7`: the floor announcement is the branch
  `LowAt L (L + 8)`; the ceiling announcement is the leaf `HighAt L (L + 9)` followed by
  `CrookUp.levels` at `(L + 1, L + 9)`.
* `foldsOnto_span9_low_mid`, peak `L + 6`: the floor announcement is the branch
  `LowAt L (L + 7)`; the ceiling announcement is the branch `HighAt L (L + 8)` followed by
  `CrookUp.levels` at `(L + 1, L + 8)`.

## 3. The leaf at height `L + 6`

Here the leaf is: both arms `HighAt (L + 3) (L + 9)` and both arms `LowAt L (L + 9)`. The arm is
read upside down, `g = L + H − f`, so that the engine sees the basepoint `L + 3` again, and the
fold is onto the reflected walk `leg3Walk'` through `foldsOnto_leg3'` (batch 39). The splits are
at `(L + 1, L + 9)` and, on the `LowAt` side, at `(L + 2, L + 9)`:

| branch | peak (reflected) | walk |
|---|---|---|
| `HighAt (L+1, L+9)` | `L + 7` | `7,6,5,4,3,2,3,4,5,6,7,8,7,6,5,4,3,2,1` |
| `LowAt (L+1, L+9)` and `LowAt (L+2, L+9)` | `L + 5` | `7,6,5,4,5,6,7,8,7,6,5,4,3,2,1` |
| `LowAt (L+1, L+9)` and `HighAt (L+2, L+9)` | `L + 6` | `7,6,5,4,3,4,5,6,7,8,7,6,5,4,3,2,1` |

No crookedness clause is used at this height; in each branch the engine's two announcements are
exactly a leaf condition and a branch condition, read through the reflection:

* `foldsOnto_span9_high_high`, peak `L + 7`: ceiling from the branch `HighAt (L+1) (L+9)`, floor
  from the leaf `LowAt L (L + 9)` (both of its clauses).
* `foldsOnto_span9_high_low`, peak `L + 5`: ceiling from the leaf `HighAt (L+3) (L+9)`, floor from
  the branch `LowAt (L+2) (L+9)`.
* `foldsOnto_span9_high_mid`, peak `L + 6`: ceiling from the branch `HighAt (L+2) (L+9)`, floor
  from the branch `LowAt (L+1) (L+9)`.

The asymmetry between the two heights — crookedness needed at `L + 3`, not needed at `L + 6` — is
not an accident of the search: `HighAt` is the one-clause condition and `LowAt` the two-clause
one, so reflecting an arm does not carry the leaf of one height to the leaf of the other.

## 4. The two middle heights, one half each

At `L + 4` the leaf is: both arms `HighAt (L + 1) (L + 9)` and both arms `LowAt L (L + 7)`. One
application of `dichotomy_at` at `(L + 1, L + 8)` splits it; the `LowAt` side splits once more at
`(L, L + 9)` and both resulting branches are served (`HPC/Fold/Span9Mid.lean`):

* `LowAt (L+1,L+8)` and `LowAt (L,L+9)`: the four-leg walk with peak `K = L + 7` and valley
  `M = L + 2`; floor and deep floor are the two branch conditions read verbatim, and the ceiling
  is the leaf `HighAt (L + 1) (L + 9)` with one application of `CrookUp.levels` at `(L + 2, L + 9)`.
* `LowAt (L+1,L+8)` and `HighAt (L,L+9)`: the three-leg walk with peak `K = L + 7`, both
  announcements read verbatim.

At `L + 5` the leaf is: both arms `HighAt (L + 2) (L + 9)` and both arms `LowAt L (L + 8)`. The
same level pair `(L + 1, L + 8)` splits it, this time with the `HighAt` side served, again after a
second split at `(L, L + 9)`; the arm is read upside down so that the engines see the basepoint
`L + 4` (`HPC/Fold/Span9Mid5.lean`):

* `HighAt (L+1,L+8)` and `LowAt (L,L+9)`: three legs, peak `K = L + 7` for the reflected arm, no
  crookedness clause.
* `HighAt (L+1,L+8)` and `HighAt (L,L+9)`: four legs, peak `K = L + 7`, valley `M = L + 2`; the
  deep-floor announcement is the engine's three-time clause, supplied by `HighAt L (L + 9)` and one
  application of `CrookUp.levels` at `(L + 1, L + 9)`.

The walks are, as offsets from `L`,

| height | branch | walk |
|---|---|---|
| `L+4` | `LowAt (1,8)`, `LowAt (0,9)` | `3,4,5,6,7,6,5,4,3,2,3,4,5,6,7,8,7,6,5,4,3,2,1` |
| `L+4` | `LowAt (1,8)`, `HighAt (0,9)` | `3,4,5,6,7,6,5,4,3,2,1,2,3,4,5,6,7,8` |
| `L+5` | `HighAt (1,8)`, `LowAt (0,9)` | `6,5,4,3,2,3,4,5,6,7,8,7,6,5,4,3,2,1` |
| `L+5` | `HighAt (1,8)`, `HighAt (0,9)` | `6,5,4,3,2,3,4,5,6,7,6,5,4,3,2,1,2,3,4,5,6,7,8` |

each verified against its class by the prober (`census-batch41b.log`), and each found by the sweep
`census-batch41f.c`, which asks, for every first branch condition, whether one further split
serves both of its sides with walks the engines can realize.

## 5. The assembly

`s3_span_nine_off_center` defers to `s3_span_eight` when `H ≤ L + 8`, to `s3_near_extreme` within
two of an extreme, and to `s3_of_not_lowAt` / `s3_of_not_highAt` outside the leaf; inside the leaf
it branches on the two dichotomies at the relevant height and applies the six folds above.
`theorem3_span_nine_off_center` is the chain-level reading, obtained from it exactly as
`theorem3_span_eight_off_center` was obtained from its predecessor.

## 6. What is left at span nine, and what the deeper searches say

What is left is one branch at each of the two middle heights: `L + 4` with both arms
`HighAt (L + 1) (L + 8)`, and `L + 5` with both arms `LowAt (L + 1) (L + 8)`. Three further
searches were run, all recorded in `census-batch41c.log`.

* The general shape family (any number of legs up to six, at most 24 times) at splitting depth
  **three**: **not solved**, at both heights. So neither middle basepoint is served by a tree of
  that shape and depth, in the automaton model.
* `census-batch41c.c` restricts the walk family to what the repository's engines can actually
  realize — `leg3Walk` with `L + 2 ≤ P ≤ L + 4`, `leg4Walk` with `M = P − 2`, `M + 3 ≤ K`,
  `H ≤ K + 3`, and the reflections of both. It reproduces batch 40's span-eight solution at the
  middle basepoint, which is the check that the restriction is faithful. At span nine it does not
  solve `L + 5` at splitting depth **four**, and its run at `L + 4` was stopped by a time limit
  before concluding.

* `census-batch41h.c` runs a greedy closure: starting from the leaf at a basepoint, it repeatedly
  looks for a level pair one of whose two dichotomy sides is served — outright, or after one
  further split — and then adds the *other* side to the class permanently, which is exactly the
  shape of the Lean proofs above. At `L + 5` this stops after twelve rounds without settling the
  basepoint (`census-batch41h.log`); the pair `(L + 1, L + 8)` used in `s3_span_nine_mid_high` is
  among the rounds it finds. At `L + 4` the same run was stopped by a time limit after eight
  rounds; the pairs it had found, beyond the one used in `s3_span_nine_mid_low`, were
  `(L+1,L+9)`, `(L+2,L+8)`, `(L+2,L+9)`, `(L+3,L+8)`, `(L+3,L+9)` and `(L+4,L+8)`, each of which
  would shrink the open class a little further at the cost of one more fold lemma.

So the two remaining branches at span nine look as if they need genuinely new material — a walk of
five legs or more with its own engine, or an arm condition beyond the dichotomy and the
crookedness clause family. Note that a negative answer from the census is not a proof of
impossibility: the automaton over-approximates the class of arms, so the failing arm it exhibits
need not come from an actual crooked sequence.

## 7. Verification

`lake build HPC` succeeds. The only `sorry` in the project is the commissioned open statement at
`HPC/Fold/Open.lean:47`. `#print axioms` for `s3_span_nine_off_center`,
`theorem3_span_nine_off_center`, `s3_span_nine_mid_low`, `s3_span_nine_mid_high` and
`s3_span_nine_except` reports `[propext, Classical.choice, Quot.sound]`.
