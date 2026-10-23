# Report: batch 62 — the crossing on the boundary of the timing law

Written in the order the commission prescribes: counterexamples first, then §1 (targets), then §2
questions 1–3, then §3 deliverables.

## 0. Counterexamples and refutations

**None this batch.** Nothing in the batch-61 delivery was refuted; every earlier Lean file is
unchanged and `lake build HPC` is clean. No statement of this batch's commission was found false.
Two measurements correct one expectation and are reported as facts of the census, not as
refutations:

* the extremal configuration of question 2 is **not** a single shape — the sum `dT + dG` is
  seventy at *every* crossing of the corpus, but the window between the two events takes **121
  distinct shapes** (all of exactly seventy-one links) among the 461 crossings recorded;
* the argument of question 1 does **not** stop at an index: every index gap the landmark sentence
  asks for is supplied by the timing law with an order of magnitude to spare. It stops at a
  **level**, and at exactly one.

## 1. The targets

| target | file | state |
| --- | --- | --- |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | still `sorry`; the residue is unchanged as a statement (`Leg4SixCrossL5`, `Leg4QuadCrossL5`), but this batch proves most of what a crossing owes the fourth and fifth walks |
| `s3_span_nine` | `HPC/Fold/General.lean` | unchanged |
| `s3_general` | `HPC/Fold/General.lean` | unchanged |
| `theorem3` | — | unchanged, waits on `s3_general` |

What moved is question 1: the two owed clauses are now read off the pairing itself, and what is
left of them is named exactly. `HPC/Fold/CrossPair62.lean` proves the reading; the census
`census-batch62.c` measures how much of the branch it closes.

## 2. The questions

### 2.1 The two owed clauses, from the pairing

**The input.** At a crossing the `w8` side `X` climbs and the other side `Y` descends. Put
`a = i − dT` at the partner's descent to `L + 2` and `b = i + dG` at the `w8` side's ascent to
`L + 9`. Crookedness applied to that one pair gives, in `cross_peak_valley_core`, a peak `r` and a
later valley `r'` strictly between them, and `ivSep` spaces all four indices:

```
a + 70 ≤ r,   r + 29 ≤ r',   r' + 70 ≤ b,   ρ r ≥ L + 7,   ρ r' ≤ ρ a + 1.
```

Those separations are `z 6 − 1 = 70`, `z 5 − 1 = 29` and `z 6 − 1 = 70` again.

**Both witnesses are times of the arm that owes the clause.** `cross_peak_valley_armG`: the peak
cannot lie on the partner arm, because seventy steps separate it from the partner's own descent,
and a time at `L + 7` or above that far before a descent to `L + 2` is precisely the landmark that
`w8`'s floor clause asks for there — which at a crossing the partner does not have. So `r`, and
with it `r'`, lies on the `w8` side, at arm index at least two.

**Where it stops: at a level, by one.** What the ceiling clause of `w71` asks for is a peak at
`L + 6` and a valley at `L + 2`. What the pairing supplies is a peak at `L + 7` — more than
enough — and a valley at `ρ a + 1`, one level above the partner's own descent. When the partner
descends to `L + 1` the valley is at `L + 2` and the clause closes
(`leg4Land_w71_ceil_of_cross_low1`); when the partner descends only to `L + 2` the valley is at
`L + 3` and it does not.

The index side of the clause is never the obstruction, and this batch makes that precise:
`armG_sep` reads the timing law on a single arm, so the gap `K − M = 6` that the sentence asks for
between the peak and the valley is bought by `z 5 − 1 = 29`, and the gap `f d − M − 1 ≤ 7` before
the ascent by `z 6 − 1 = 70`. The *only* index question left anywhere in the argument is a
two-index one, recorded honestly below.

**The two clean reductions.**

* `leg4Land_w71_of_w8_of_low1` — **the `w8` side owes `w71` nothing but a valley at `L + 1`.** If
  before every ascent to `L + 9` the arm has a time at `L + 1` or below seven steps earlier, the
  whole of `w71` follows: `w8`'s own floor landmark at that valley is the peak, and the level
  `L + 1` buys the extra step of the gap.
* `leg4Land_w72_ceil_of_cross` and `leg4Land_w72_of_cross_of_floor1` — one level up in the walk
  the clause closes as it stands. The fifth walk `w72 = L+4 → L+7 → L+2 → L+8 → L+1` asks its
  ceiling valley to sit at `M + 1 = L + 3`, which is exactly where the pairing puts it, and its
  peak at `K − 1 = L + 6`, which is where the crooked peak is. So **the `w8` side of a crossing
  satisfies `w72` in full as soon as it stays at `L + 1` or above**, its deep-floor clause being
  the only one that can fire below that.

**The residue in Lean, named.** Two things, and only two:

1. the valley's level — `ρ a + 1` where the walk wants `L + 2`, i.e. whether the partner's descent
   reaches `L + 1`;
2. two indices — `cross_peak_valley_armG` asks that the partner have no time at `L + 7` or above
   at arm index **two or three** before its descent, while the crossing hypothesis
   `¬ Leg4Land (armT …) (L+9) (L+8) (L+1) (L+5)` literally gives the same statement from index
   **four** on. `crossBad_of_floor_fail` proves the index-four half from the failure of `w8`'s
   floor clause, so the gap is exactly a partner peak at `L + 7` or above at arm index `2` or `3`;
   the census finds it at 83 of the 461 crossings.

No second pairing (the partner's own `L + 9` against the `w8` side's opening) was needed for what
is proved here; whether it removes either residue is not settled.

**What the census says.** `census-batch62.c` (log `census-batch62.log`, run as
`census-batch62 40 62 200 12`) stores every crossing of the trichotomy whole — both arms and the
faithful pair — and reads the batch-62 quantities off them. 461 distinct crossings, every one with
exactly one `w8` side:

```
the partner descends to L+1 or below           355 of 461   (to L+2 and no lower: 106)
the w8 side reaches L+9 at all                 282
the w8 side has w71's ceiling clause           374
the w8 side satisfies w71 in full              374
the w8 side satisfies w72 in full              451
the partner satisfies w71 in full              461
the partner satisfies w72 in full              431
both arms satisfy w71                          374          (residue 87)
both arms satisfy w72                          421          (residue 40)
the w8 side touches L (w72's deep floor fires) 179
the two-index slack occurs                      83
```

The crooked pair was also looked for directly in the stored sequence, with the separations the
theorem carries: the greedy search (first peak at `L + 7` or above at least seventy steps after
the partner's descent, then the first valley twenty-nine steps later and seventy before the
ascent) found it **on the `w8` side 240 times and on the partner side never**; in 42 cases the
greedy choice did not close, which is a limitation of that search and not a counterexample —
`cross_peak_valley_core` proves the pair exists.

Two readings of the table. First, the partner side is not the difficulty at all: it satisfies
`w71` at every one of the 461 crossings. Second, the whole of the residue is the `w8` side's
ceiling clause, exactly as the batch-61 picture predicted, and it is smaller against `w72`
(40 crossings) than against `w71` (87).

### 2.2 Why exactly seventy

**The equality is forced on the corpus; the configuration is not one shape.**

At all 461 crossings `dT + dG = 70` exactly — the `w8` side's first climb to `L + 8` and the
partner's first descent to `L + 2`, with no exception and no missing index. `cross_high8_low2_far`
(batch 61) proves `dT + dG ≥ 70` from `z 6 = 71`, so every crossing of the corpus sits on the
boundary of the timing law. The window between the two events therefore always has exactly
seventy-one links: it is a shortest faithful crooked sequence spanning six levels.

But it is **not** a single shape. Reduced modulo the reflection `(ρ, index) ↦ (9 − ρ, reversed)`,
the 461 windows fall into **121 distinct sequences**, all of length seventy-one. The first four
crossings of the run happen to share one window,

```
87666567656545556665554565454345455545656665654565454344455544434543332
```

at `dT/dG = 65/5, 61/9, 59/11, 57/13` — the same seventy-one links read from a different
basepoint — which is why the basepoint, not the window, is what varies there. Across the corpus
the windows genuinely differ.

So the answer to the question as asked is: yes to the first half, no to the second. A crossing
exists only at the extremal configuration of the timing law, and that is a strong constraint —
seventy-one links, six levels, no slack. It is not a *single* shape of Bing's chain up to shaving
and filling, so the proof of question 1 has a family to handle, not one configuration. What the
extremality does buy is what §2.1 uses: at an extremal window every index gap in sight is of the
order of seventy, which is why the sentence's own index arithmetic is free and only the level
question survives.

### 2.3 Sufficiency for `LandWalk`, stated

`HPC/Fold/LandWalkSuff.lean` supplies the three pieces question 3 asks for.

* **The greedy, for a walk of any shape.** `gstepWalk` and `gseqWalk` are the greedy step and
  greedy time-assignment of `HPC/Fold/Leg4.lean` with the four-leg walk replaced by
  `walkList s ts`: advance if the next time serves the new level, stay if the current one does,
  otherwise retreat. `foldsOnto_of_gseqWalk` is proved: **if the greedy time serves the arm's
  level at every index, the arm folds onto the walk.** That is the whole of what the greedy is
  for, and it is now available for walks of every shape.
* **The invariant.** `LandChainAt f s ts r a` is a landmark chain of the sentence — times
  `a 0 ≤ ⋯ ≤ a r` of the arm at the walk's first `r + 1` turning levels, separated by the walk's
  own turn-time gaps — and `WalkInvLand` is two bounds per leg, uniform in the leg:

```
(capped)    a r + n ≤ j  →  min (min (walkStop r + n) (walkStop r + |u j − walkLevel r| + 1))
                                (walkStop (r+1))                ≤ q j
(uncapped)  a r     ≤ j  →  walkStop r + |u j − walkLevel r|    ≤ q j + 1
```

  For the four-leg walk these are exactly the six bounds of `gseq4_invLand`: the capped bound at
  `r = 0` with credit `j` is `(1)`, at `r = 1` it is `(2)`, at `r = 2` it is `(3)`; the uncapped
  bound at `r = 1, 2, 3` is `(2′)`, `(3′)`, `(4)`. The credit `n` is the number of steps by which
  the chain's last landmark precedes the index, and it is spendable precisely because the
  sentence's gap between consecutive landmarks *is* the walk's gap between consecutive turn times.
* **The statement.** `LandWalkSuffices` is the sufficiency half, for a walk of any shape and an
  arm every one of whose levels some time of the walk serves;
  `landWalk_iff_foldsOnto_of_suffices` records that with it the landmark sentence *is* folding,
  necessity being `landWalk_of_foldsOnto` of batch 61. `landChainAt_of_landWalk` extracts the
  chain the sentence produces in the form the invariant consumes.

The proof of `LandWalkSuffices` — the induction of `gseq4_invLand` carried out against
`WalkInvLand` over `walkList s ts` — is not in this batch, and remains the only missing half of
the general engine.

## 3. Deliverables

**New Lean files, both `sorry`-free, no `native_decide`, no new axiom.**

* `HPC/Fold/CrossPair62.lean` — `cross_peak_valley_core`, `armG_sep`, `cross_peak_valley_armG`,
  `crossBad_of_floor_fail`, `leg4Land_w71_of_w8_of_low1`, `leg4Land_w71_ceil_of_cross_low1`,
  `leg4Land_w72_ceil_of_cross`, `leg4Land_w72_of_cross_of_floor1`.
* `HPC/Fold/LandWalkSuff.lean` — `ValWalk`, `gstepWalk`, `gstepWalk_dist`, `gseqWalk`,
  `gseqWalk_zero`, `gseqWalk_succ`, `foldsOnto_of_gseqWalk`, `LandChainAt`, `WalkInvLand`,
  `landChainAt_of_landWalk`, `LandWalkSuffices`, `landWalk_iff_foldsOnto_of_suffices`.

Both are imported by `HPC.lean`; `lake build HPC` is clean.

```
'HPC.Fold.cross_peak_valley_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.armG_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cross_peak_valley_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w71_of_w8_of_low1' depends on axioms: [propext, Quot.sound]
'HPC.Fold.leg4Land_w71_ceil_of_cross_low1' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_ceil_of_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_w72_of_cross_of_floor1' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.foldsOnto_of_gseqWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.landChainAt_of_landWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.landWalk_iff_foldsOnto_of_suffices' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Census over the general model, under the audit protocol.** `census-batch62.c` (log
`census-batch62.log`, run as `census-batch62 40 62 200 12`) is the batch-61 census with a
batch-62 block added: the crossings of the *trichotomy* stored whole — both arms and the faithful
pair they were found in, duplicates merged — and then read for the two indices of the timing law,
the shape of the window between them, the level the partner's descent reaches, the clauses each
side owes `w71` and `w72`, the two-index slack, and the crooked pair of `cross_peak_valley_core`
searched for literally in the stored sequence. Every predicate is evaluated by its own definition:
`Leg4Land` clause by clause with the index bounds the walk's positions dictate, the ceiling clause
with both existentials written out, the first-time indices by literal scans, and no criterion used
anywhere in the block. The definition audit at the end of the log lists them, and the block ends
with its own audit paragraph.

The numbers quoted in §2 are from that program and its log.
