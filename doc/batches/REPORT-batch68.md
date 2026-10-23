# Report: batch 68 — the ceiling clause read the other way, and what the branch `L + 5` still owes

The commission read is **batch 68**, "what the branch `L + 5` still owes, and the assembly", pasted
into the prompt and saved here as `COMMISSION-batch68.md`. House order: counterexamples first, then
the targets, then the questions 1–4, then the deliverables.

**Headline.** §2.2(a) is answered yes, and it is a theorem:

> `ceil71_of_deepFirst2_armG` / `..._armT` (`HPC/Fold/Ceil68.lean`) — the pairing at the top of the
> band read *inside one arm* returns exactly the two landmarks `w71`'s ceiling clause asks for. An
> arm of the branch that satisfies `Mid2Floor` and has been at `L + 2` or below before each of its
> own times at `L + 9` satisfies `w71` in full (`w71_armG_of_deepFirst2`), and the converse holds
> as well (`w71_armG_iff_deepFirst2`).

Hence `s3_span_nine_mid5_of_cross_deepFirst2`: **at a crossing of the trichotomy both of whose arms
have been at `L + 2` or below before each of their own times at `L + 9`, the pair folds — onto
`w71` itself.** Over the corpus that is 374 of the 461 crossings. The other 87 are exactly the
crossings whose `w8` side runs high — reaches `L + 9` with nothing at `L + 2` or below before it —
and for them §2.1 is answered by a theorem as well (`cross_partner_wb_of_no_nine_armT`: the partner
is a `wb` arm wherever it stops below `L + 9`, which at those 87 it always does), leaving
`s3_span_nine_mid5_of_cross_highRun_armG` to close them from one clause: `w72`'s ceiling clause on
the high-running arm, with the two deep-floor clauses that a band missing the floor makes vacuous.

## 0. Counterexamples

**None this batch.** Nothing stated in earlier batches was refuted, and no statement written here
was found false. Every clause measured in the census of §2.2(c) is evaluated by its own definition,
and the definition audit for the block is printed with it.

One near-miss is worth recording as a fact rather than as a refutation: `w71`'s ceiling clause on an
arm of the branch that satisfies `Mid2Floor` is *equivalent* to the arm's having been at `L + 2` or
below before each of its own times at `L + 9` (`w71_armG_iff_deepFirst2`, `deepFirst2_of_ceil71`).
So at the 87 crossings whose `w8` side runs high, `w71` is not merely unproved on that arm — it is
**false** there, and no sharpening of the pairing can recover it. That is what forces the `w72`
route of §2.3.

## 1. The targets

| target | file | state |
| --- | --- | --- |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | still `sorry`; the crossings now split into 374 closed outright (`s3_span_nine_mid5_of_cross_deepFirst2`) and 87 reduced to one clause (`s3_span_nine_mid5_of_cross_highRun_armG` and its mirror) |
| `s3_span_nine` | `HPC/Fold/General.lean` | unchanged; see §2.3 — it already follows from `s3_span_nine_mid4` and `s3_span_nine_mid5` with **no further case**, and that derivation is `s3_span_nine'` (`HPC/Fold/Mixed.lean`) |
| `s3_general` | `HPC/Fold/General.lean` | unchanged; waits on spans ten and above, which this commission excludes |
| `theorem3` | `HPC/Fold/Open.lean` | unchanged, waits on `s3_general` |

## 2. The questions

### 2.1 The partner's `wb` at a crossing

**Partly a theorem, and a theorem exactly where the assembly needs it.**

`w3` and `wb` differ in one clause only: `wb`'s deep clause, whose trigger on the reflected arm is
`L`, that is a time of the *unreflected* arm at `L + 9`. `w3`'s ceiling clause is the stronger of
the two remaining, and the base clause is shared. So

* `leg4Land_wb_of_w3_of_no_nine` — a `w3` arm that never reaches `L + 9` is a `wb` arm;
* `leg4Land_wb_of_not_w8_of_no_nine` — with `leg4Land_tri`, **an arm of the branch that `w8` does
  not serve and that never reaches `L + 9` is served by `wb`**;
* `cross_partner_wb_of_no_nine_armT` and `..._armG` — at a crossing, the partner of a `w8` side is
  such an arm, so if it stops below `L + 9` it is a `wb` arm.

The hypothesis is not decoration: where the partner does reach `L + 9`, `wb`'s deep clause is a real
demand on it and neither the trichotomy nor the crossing clauses give it. The census measures the
split: of the 461 crossings, the `w8` side reaches `L + 9` at 282 and the partner at 179, and
**never both** (0 of 461). So the theorem above covers 282 of the 461 outright — and, what matters
for the assembly, **all 87 of the crossings that §2.2 leaves**, since the high run is always on the
`w8` side and the arm that runs high is the one that reaches `L + 9`.

Where the partner does reach `L + 9` the census says it is still a `wb` arm (461 of 461 have exactly
one `wb` arm and exactly one `w8` arm; the partner is `wb` only at 146 and both `wb` and `w3` at
315; **no crossing has a partner on `w3` only, and none has no `wb` arm at all**). So "partner on
`wb`" is true over the whole corpus, and this batch proves it from the trichotomy exactly when the
partner stops below `L + 9`; the remaining case is `wb`'s deep clause on an arm that reaches the top
of the band, and that clause is the same object as `w71`'s ceiling clause read on the unreflected
arm (`land_w71_ceil_of_wb`), so §2.2(a) settles it too whenever that arm is deep first at `L + 2`.

### 2.2 The `w8` side's disjunction

#### (a) The pairing read the other way — **yes, and at the level `w71` asks for**

`crooked_peak_valley_high9` (batch 67) reads crookedness between a link at `L + 1` or below and a
link carrying `L + 9`, and returns a peak at `L + 7` or above and then a valley at `ρ a + 1` or
below, spaced `169`, `70`, `169`. Batch 67 read it *across* the basepoint, so that the peak decided
which arm got which clause. Read with **both ends on the same arm** — the arm's own earlier time at
`L + 1` or below, and its own time at `L + 9` — the peak and the valley are times of that arm, and

```
peak   L + 7 or above, arm index ≥ 169      w71 asks for L + 6, arm index ≥ 3
valley L + 2 or below, 70 steps later       w71 asks for L + 2, 6 steps later
ascent 169 steps after the valley           w71 asks for 7 steps after it
```

so the clause is met with a great deal of room: `ceil71_at_of_low1_armG`, `ceil71_at_of_low1_armT`.
The level the pairing returns is exactly the `L + 2` the clause asks for, not one above it.

The earlier time need only be at `L + 2`, not at `L + 1`: at a descent to *exactly* `L + 2` the
floor clause `Mid2Floor` supplies the peak and the timing law supplies both gaps — four levels cost
twelve steps (`z 4 = 13`) where the clause asks six, and seven levels cost 169 (`z 7 = 170`) where
it asks seven (`ceil71_at_of_mid2_of_sep`). Hence

* `ceil71_of_deepFirst2_armG`, `ceil71_of_deepFirst2_armT` — the clause in full from `Mid2Floor` and
  `DeepFirst2`;
* `leg4Land_w71_of_tri_of_mid2_of_ceil` — the rest of `w71` is already owned by every arm of the
  branch: the floor clause at the descents to `L + 1` or below comes from whichever of `w8`, `w3`,
  `wb` serves the arm, the one at exactly `L + 2` is `Mid2Floor`, and `w71`'s deep clause triggers
  at `L - 1` and is vacuous in the band;
* `w71_armG_of_deepFirst2`, `w71_armT_of_deepFirst2`, and the equivalence
  `w71_armG_iff_deepFirst2`, `w71_armT_iff_deepFirst2`.

The same pairing read against a link at `L + 2` (`crooked_peak_valley_high9_mid`, spacings `70`,
`29`, `70`) returns a valley at `L + 3` or below, which is what `w72`'s ceiling clause asks:
`ceil72_of_deepFirst2_armG`, `ceil72_of_deepFirst2_armT`.

#### (b) Is a `w8` side failing both clauses excluded by the nine-level bound?

**Not by the bound, so far as this batch can see; and the corpus has no instance.**

What a failure of `w71`'s ceiling clause says is now exact: on an arm of the branch with
`Mid2Floor`, the clause fails precisely when the arm reaches `L + 9` with no time at `L + 2` or
below before it (`w71_armG_iff_deepFirst2`). The nine-level bound `z 9 = 986` is a statement about
the *distance* between two links nine levels apart; it forbids a quick descent to `L`, not the
absence of one. An arm that leaves the basepoint at `L + 5`, climbs to `L + 9` and only then goes
down violates no separation: four levels cost `z 4 - 1 = 12` steps and the arm is free to take them.
So the bound does not exclude the first failure, and it does not exclude the pair either — what
excludes the pair, if anything does, would have to be a reason for a time at `L + 3` or below with a
peak before it, which is the content of `w72`'s ceiling clause and not of the timing law.

The census measures it: over the 461 crossings the `w8` side fails `w71`'s ceiling clause at 87 and
`w72`'s at **none**, so the double failure is empty (0 of 461) — the same disjointness batch 65
reported, now measured at the clause the assembly actually uses.

#### (c) The census over the crossings — `census-batch68.c`, log `census-batch68.log`

Run as `census-batch68 40 62 200 12`, under the audit protocol; the block ends with its own
definition audit and uses no criterion of the engine. Over the **461** stored crossings of the
trichotomy (duplicates merged, no overflow):

```
2.1  the partner's walk
     crossings with exactly one wb arm      461      with two 0      with none 0
     crossings with exactly one w8 side     461      with two 0      with none 0
     the partner's tag: wb only 146   wb and w3 315   w3 only 0   neither 0
     tag pairs (1 = wb, 2 = w8, 4 = w3):  (1,2) 97   (2,1) 49   (2,5) 179   (5,2) 136

2.2(c)  the w8 side's disjunction
     A: the w8 side satisfies w71                                   374
     B: the w8 side satisfies w72 and the partner has Deep72        421
     both 334      neither 0
     B and not A 87;  of those the partner's deep-floor clause holds  87  (all of them)
     the w8 side satisfies w71 374, w72 451;  its w71 ceiling clause 374, its w72 ceiling 461
     the partner's deep-floor clause 431;  the w8 side's 451

the reach of this batch's theorems, over all 461 crossings (922 arms)
     arms deep first 632;  deep first at 2  835;  arms reaching 9  461
     arms with an ascent to 9 and nothing at 1 or below before it  290;  at 2 or below  87
     crossings with both arms deep first 171;  both arms deep first at 2  374
     arms satisfying w71 835;  arms with w71's ceiling clause 835   (the two agree exactly)
     crossings with both arms on w71 374;  with both on w72 421
     crossings with Mid2Floor on both arms 461   (crossMid2 says all of them)

where the top of the band is reached
     the w8 side reaches 9  282;  the partner reaches 9  179;  both  0
     the w8 side has a high run 87;  the partner  0
     the w8 side fails w71's ceiling clause 87;  w72's 0;  both 0
```

Two of these lines are the theorems of §2.2(a) seen from outside: *arms satisfying `w71`* and *arms
deep first at `L + 2`* are the same 835 of the 922, and *crossings with both arms on `w71`* and
*crossings closed by `s3_span_nine_mid5_of_cross_deepFirst2`* are the same 374 of the 461. The
residue is the 87 crossings with a high run, all of them with the run on the `w8` side, all of them
with the partner short of `L + 9`, and all of them meeting disjunct B.

### 2.3 Assembly

**`s3_span_nine` follows from the three with no further case, and the derivation is already
written.** `s3_span_nine_of_mid` (`HPC/Fold/CrossArm.lean`) reduces span nine to the two branches,
and `s3_span_nine'` (`HPC/Fold/Mixed.lean`) is that reduction applied to `s3_span_nine_mid4` and
`s3_span_nine_mid5`; `s3_span_nine` in `General.lean` is the same statement and is left `sorry` only
because `s3_span_nine_mid5` is. So no case remains to be named there: the whole of span nine now
rests on the branch at `L + 5`, and the branch at `L + 5` rests on the crossings.

For `s3_span_nine_mid5` itself the split is now:

* not a crossing — one of the three walks of the trichotomy serves both arms, and
  `s3_span_nine_mid5_of_leg4Land_refl` / `..._direct` folds the pair;
* a crossing with both arms deep first at `L + 2` — **closed**, onto `w71`
  (`s3_span_nine_mid5_of_cross_deepFirst2`; `s3_span_nine_mid5_of_cross_deepFirst` is the same with
  the batch-66 hypothesis at `L + 1`);
* a crossing with a high run — reduced to one clause. `s3_span_nine_mid5_of_cross_highRun_armG` and
  its mirror: with the `w8` side the running arm and the partner short of `L + 9`, the partner is a
  `wb` arm (§2.1), `crossMid2` gives both arms `Mid2Floor`, so the partner satisfies `w72` as soon
  as it has the deep-floor clause and the `w8` side satisfies `w72` as soon as it has the
  deep-floor clause and `Ceil72`; both deep-floor clauses are vacuous in a band that misses the
  floor (`deep72_of_off_floor`). What is left to prove is therefore exactly
  **`Ceil72` on a high-running `w8` side** — a time at `L + 3` or below before its ascent to
  `L + 9`, with a time at `L + 6` or above five steps before that — together with the two
  deep-floor clauses where the band reaches `L`.

On the way, one structural fact about the high run, which is what made §2.1 findable:
`partner_w3ceil_of_highRun_armG` and its mirror — when an arm reaches `L + 9` with nothing at
`L + 2` or below before it, the pairing's valley **cannot** lie on that arm, so the peak and the
valley are both times of the partner and, in the partner's own order, they read valley, peak,
descent: `w3`'s ceiling clause at every descent of the partner to `L + 1`. With the floor clause
that every arm failing `w8` owns (`w8_floor_fail_of_not_w8`, `notW8_floor`) this gives
`leg4Land_w3_armT_of_highRun_armG`: **at a crossing the partner of a high-running `w8` side is a
`w3` arm** (`cross_partner_w3_of_highRun_armG`). The census's 315 partners tagged both `wb` and `w3`
are this phenomenon seen from outside.

### 2.4 The engine probe

**Run, to forty, and the answer is negative.** `probe68.c` is `probe65b.c` with the arm bound raised
from thirty to forty and with the clause of batch 66 §2.3 added to the sentence: every time of the
arm whose level is served only by walk positions before the `r`-th turn must come before the `r`-th
landmark, the landmark being the one the backwards greedy returns, which is the latest admissible
one and so optimal for the added clause as well as for the gaps. It is a census over **walks and
arms** and not over the general model, and it says so; its arm-length bound is **forty times**,
against walks of up to twenty-one — twice the walk's length, which is the batch-64 rule.

The complete run (`probe68c.log`): **742 walks, 146 443 515 arms tested, deepest prefix reached 40,
twelve counterexamples**, one of them at a walk whose shortest leg is four. Two further runs at
larger budgets (`probe68.log`, `probe68b.log`) were stopped before completing the sweep; between
them they printed thirteen more, including two at shortest leg four. Four counterexamples — two at
shortest leg three and two at four — were re-checked by `check68.py` (log `check68.log`), written
from the definitions and sharing no code with the probe: in each the arm is 1-Lipschitz, starts
within one of the walk's first level, has every level served, satisfies the sentence **with the
added clause**, and does not fold.

So **no sufficiency statement for the landmark sentence is written**, and the clause of batch 66
§2.3 is not the repair. Nothing in the development depends on sufficiency: every fold is produced
by `foldsOnto_leg4_iff_leg4Land`, whose criterion is exact and proved, and `LandWalk` is used only
in its necessary direction. Details in `PROBE-batch68.md`.

## 3. Deliverables

**One new Lean file, `sorry`-free, no `native_decide`, no new axiom: `HPC/Fold/Ceil68.lean`.** It is
imported by `HPC.lean`; the only edit to an earlier file is that one import line. `lake build HPC`
is clean and free of linter warnings in the new file. The project's `sorry`s are exactly the four
standing targets — `s3_span_nine_mid5` (`Mixed.lean`), `s3_span_nine` and `s3_general`
(`General.lean`) and `theorem3` (`Open.lean`) — and nothing this batch adds uses any of them.

Contents: the definitions `Ceil71`, `Ceil72`, `DeepFirst2`; the pairing at `L + 2`
(`crooked_peak_valley_high9_mid`, `crooked_valley_peak_high9_mid`); the clause from a low time
(`ceil71_at_of_low1_armG`, `ceil71_at_of_low1_armT`), from a descent to exactly `L + 2`
(`ceil71_at_of_mid2_of_sep`) and in full (`ceil71_of_deepFirst2_armG/armT`,
`ceil71_of_deepFirst_armG/armT`, `ceil72_of_deepFirst2_armG/armT`); the rest of `w71` and `w72`
(`leg4Land_w71_of_tri_of_mid2_of_ceil`, `leg4Land_w72_of_tri_of_mid2_of_ceil`); the arms
(`w71_armG_of_deepFirst2`, `w71_armT_of_deepFirst2`) and the folds
(`s3_span_nine_mid5_of_deepFirst2`, `s3_span_nine_mid5_of_cross_deepFirst2`,
`s3_span_nine_mid5_of_cross_deepFirst`); the equivalence (`deepFirst2_of_ceil71`, `ceil71_of_w71`,
`w71_armG_iff_deepFirst2`, `w71_armT_iff_deepFirst2`); the high run
(`partner_w3ceil_of_highRun_armG/armT`, `w8_floor_fail_of_not_w8`,
`leg4Land_w3_armT_of_highRun_armG`, `leg4Land_w3_armG_of_highRun_armT`,
`cross_partner_w3_of_highRun_armG/armT`); the partner's walk (`leg4Land_wb_of_w3_of_no_nine`,
`leg4Land_wb_of_not_w8_of_no_nine`, `cross_partner_wb_of_no_nine_armT/armG`); and the assembly on
`w72` (`s3_span_nine_mid5_of_cross_highRun_armG/armT`, `deep72_of_off_floor`).

The `#print axioms` of every theorem of the file is in `axioms-batch68.txt`; all are
`[propext, Classical.choice, Quot.sound]` or a subset.

**Censuses.** `census-batch68.c` (log `census-batch68.log`, run as `census-batch68 40 62 200 12`) is
the batch-65 census with a batch-68 block added: the crossings of the trichotomy read one by one for
§2.1, §2.2(b) and §2.2(c), with its own definition audit. It is a census over the general model,
under the audit protocol.

`probe68.c` is a census over **walks and arms** and not over the general model. It enumerates walks
by their turning levels — at most four turns, levels in `[0, 6]`, shortest leg at least three — and
for each runs randomised depth-first descents over 1-Lipschitz arms to **forty** times, pruning on
the two prefix-monotone conditions, and evaluates `walkList`, `walkLen`, `walkStop`, `walkLevel`,
the corrected sentence with the added clause, and `FoldsOnto` by their own definitions. Its
arm-length bound is **forty times**, against walks of up to twenty-one times, which is the bound the
batch-64 rule asks for. Logs: `probe68c.log` (complete sweep, 742 walks, 146 443 515 arms, twelve
counterexamples, deepest prefix 40), and the partial deeper runs `probe68b.log` and `probe68.log`.
`check68.py` (log `check68.log`) re-checks four of the counterexamples independently. The write-up
is `PROBE-batch68.md`.

## 4. Not in this batch

`Ceil72` on a high-running `w8` side, which is what the branch at `L + 5` now owes; the partner's
`wb` where the partner itself reaches `L + 9`; spans ten and above; Bing 1948 Theorems 4, 5, 6, 13;
the 1951 reduction; the linear-time far-index check; Bing's seam. No new sufficiency statement for
the landmark sentence is written here: see `PROBE-batch68.md`.
