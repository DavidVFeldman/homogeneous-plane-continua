# Report: batch 65 — two refutations, and the residue restated

Written in the order the commission prescribes: counterexamples first, then §1 (targets), then §2
questions 1–4, then §3 deliverables.

## 0. Counterexamples

**Two refutations, one of each statement the previous batch left standing.**

### 0.1 `CrossMid2L5` is false, at a basepoint of Bing's own chain

`CrossMid2L5` (`HPC/Fold/CrossPartner64.lean`, batch 64) — *at a basepoint of the branch `L + 5`
the arm that `w8` does not serve has the floor clause of `w71` at its descents to exactly `L + 2`*
(`Mid2Floor`) — is **false**, and `HPC/Fold/CrossMid2Fail65.lean` proves it
(`not_crossMid2L5`).

The witness is the basepoint `145` of `bing 0 9` (`HPC/Fold/Bing9.lean`: 986 links, faithful, span
exactly nine with both ends attained, all already proved there). Its backward arm reads

```
arm index :  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 …
level     :  5  4  3  4  3  2  3  4  3  4  5  4  3  4  5  4  5  6 …
```

* both arms are `LowAt (L + 1) (L + 8)` (`bing9_lowAt_armG`, `bing9_lowAt_armT`), so the basepoint
  lies in the branch;
* the backward arm stands at `L + 2` at its arm index **five** (`bing9_armT_five`), and
  `Mid2Floor` asks there for a time at `L + 6` or above at arm index three or more and four steps
  earlier — an index in `[3, 1]`, which is empty (`not_mid2Floor_bing9_armT`);
* so that arm is served by none of `w8`, `w71`, `w72` (`not_w8_bing9_armT`, `not_w71_bing9_armT`,
  `not_w72_bing9_armT`), and in particular `w8` does not serve it, which is the whole hypothesis
  `CrossMid2L5` puts on the arm.

The hypothesis of the batch-64 assembly `s3_span_nine_mid5_of_crossMid2_of_low1` is therefore never
met and that assembly is vacuous.

**Why the statement looked safe, and how early the failure can be.** Three arm facts, all proved:

* `mid2Floor_of_leg4Land` — `Mid2Floor` is *implied* by the landmark sentence of every walk of the
  family based at `L + 5` whose peak is at `L + 7` or above: their common floor clause fires at
  the descents to `L + 2` and returns exactly what `Mid2Floor` asks. So only an arm outside all of
  `w8`, `w71`, `w72` can fail it — which is why a statement quantified over the arms `w8` misses
  looked like a statement about a thin set.
* `not_leg4Land_of_early_low` — conversely, an arm standing at `L + 2` or below at an index of six
  or less satisfies **none** of those three walks: the floor clause asks for a landmark at index
  `K − P + 1 ≥ 3` and `K − 1 − f d ≥ 4` steps before the descent, and `[3, d − 4]` is empty.
* `arm_low_index_ge_five` — and the timing law (`ivSep3`: three levels cost five steps) puts the
  first such descent no earlier than arm index five. So the window in which the branch's own walks
  are defeated outright is exactly the two arm indices `5` and `6`; Bing's chain occupies the first
  of them, and `census-batch65.c` reports `5` as the least index of a descent to exactly `L + 2`
  anywhere in the corpus.

Past index six the clause can still fail — it fails at any descent to `L + 2` whose arm has stayed
at `L + 5` or below throughout `[3, d − 4]` — so this is not a boundary effect of the first steps.
The census measures it: of the corpus's **2 786 644** arms of the branch (at **1 393 322**
basepoints), `Mid2Floor` fails on **310 028**, and `CrossMid2L5` fails at **308 258** basepoints.

**What the refutation does not touch.** The basepoint `145` is *not* a crossing of the trichotomy:
`probe65.c` reads its two arms and finds both served by `wb`, so the pair folds onto that walk (the
arm half of this — that the arm failing `Mid2Floor` is a `wb` arm — is proved,
`leg4Land_wb_bing9_armT`; the forward arm's sentence is measured, its arm being 841 links long).
`CrossMid2L5` dropped the crossing and kept only "`w8` does not serve the arm", and that is the
defect. `CrossMid2L5'` (same file) is the statement with the crossing written out exactly as
`Leg4TriCrossL5` writes it, `TriCrossL5` names the crossing, and
`s3_span_nine_mid5_of_crossMid2'_of_low1` rebuilds the batch-64 assembly on it. Over the corpus the
corrected statement is untouched: **none** of the 461 crossings of the trichotomy has an arm
failing `Mid2Floor`.

### 0.2 `LandWalkP3Suffices` is false as well

`LandWalkP3Suffices` (`HPC/Fold/LandWalkFail64.lean`) — the corrected landmark sentence `LandWalkP`
implies folding for a walk **every one of whose legs is at least three steps long** — is **false**,
and `HPC/Fold/LandWalkFail65.lean` proves it (`not_landWalkP3Suffices`).

This is the batch-64 rule of §0 doing its work: *a sufficiency statement is not written until the
arm probe has covered arms at least twice the walk's length.* The batch-64 search was exhaustive to
arms of **fourteen** times over walks of up to twenty times, so the rule was not met, and this batch
looked for the counterexample before attempting the induction.

The walk is the turning levels `[5, 2, 6]` from `1`:

```
walkList 1 [5,2,6] :  1  2  3  4  5  4  3  2  3  4  5  6     (twelve times)
turn times         :  0           4        7           11
turning levels     :  1           5        2            6
legs               :     4           3           4
```

and the arm is thirty times long:

```
cexArm65 : 0 0 1 2 2 3 2 2 3 4 5 4 3 2 1 2 1 1 1 2 2 1 0 1 2 3 4 5 6 7
```

* it satisfies the corrected sentence (`landWalkP_cex65`) with the single chain `(0, 10, 13, 27)`:
  the arm's time `0` at the level `0` for the walk's start `1`, its time `10` at `5` for the
  turning level `5`, its time `13` at `2` for the turning level `2`, and its time `27` at `5` for
  the last turning level `6`; the gaps the walk asks for — four, three, four — are met with room to
  spare, and the only trigger reaching past the first turn is the arm's last level `7`, which the
  walk's time `11` alone serves (`cex65_trigger_bound`);
* it does not fold (`not_foldsOnto_cex65`): the arm's time `22` is at the level `0`, which only the
  walk's time `0` serves, so the fold stands at the walk's start there, and the arm's last level
  `7`, served only by the walk's time `11`, is seven times later — `0 + 7 < 11`.

**Lengthening the legs is not the repair.** The search `probe65b.c` finds 43 counterexamples, 41 at
walks whose shortest leg is three and **two at walks whose shortest leg is four**:

```
s = 0, ts = [5,1,6,1]   legs 5,4,5,5   walk 0 1 2 3 4 5 4 3 2 1 2 3 4 5 6 5 4 3 2 1
  arm (30) -1 0 0 1 1 2 2 2 3 3 4 4 4 4 3 4 3 3 2 1 0 -1 0 1 2 3 4 5 6 7
s = 0, ts = [5,1,6,2]   legs 5,4,5,4   walk 0 1 2 3 4 5 4 3 2 1 2 3 4 5 6 5 4 3 2
  arm (30) -1 -1 0 0 -1 0 1 1 1 1 0 0 1 2 3 4 3 2 2 1 0 -1 0 1 2 3 4 5 6 7
```

Both were re-checked, against the definitions of `walkList`, `walkLen`, `walkStop`, `walkLevel`,
`LandWalkP` and `FoldsOnto`, by a second program written independently of the probe: in each the
sentence holds, the band condition holds, the arm is 1-Lipschitz and starts within one of the
walk's first level, and the arm does not fold. **The first of them is formalized here too.**
`HPC/Fold/LandWalkFail65.lean` states the leg bound as a parameter,

```
LegAtLeast k s ts        every leg of the walk is at least k times long  (LegAtLeast 3 = NoShortLeg)
LandWalkPLegSuffices k   LandWalkP3Suffices with NoShortLeg replaced by LegAtLeast k
```

with `landWalkPLegSuffices_three_iff : LandWalkPLegSuffices 3 ↔ LandWalkP3Suffices`, and proves
`not_landWalkPLegSuffices_four : ¬ LandWalkPLegSuffices 4` at the arm `cexArmB65` above:
`cexB65_legAtLeast_four` (legs five, four, five, five), `cexB65_isLip`, `cexB65_band`,
`cexB65_trigger_bound`, `landWalkP_cexB65` with the chain `(0, 10, 18, 27)` — the case `r ≥ 4` is
vacuous, since the walk's fourth turn is at its time `19` and no trigger of this arm exceeds `14` —
and `not_foldsOnto_cexB65`: the arm's time `21` is at the level `-1`, which only the walk's start
serves, and its last level `7` is served by the walk's time `14` alone, eight times later. Since a
longer leg bound implies a shorter one (`legAtLeast_mono`), `not_landWalkPLegSuffices_le_four` gives
`¬ LandWalkPLegSuffices k` for **every** `k ≤ 4` — the leg bound of the standing statement cannot be
repaired by raising it to four, and the second leg-four witness is left as measured only.

**The mechanism.** The sentence pins each landmark to within one level of a turn. An arm may meet
every landmark early and then be dragged back to a level the walk passes once — here the level `0`
at the arm's time `22`, which only the walk's *start* serves — after which the walk's far end is out
of reach. Because the return is to the start and not to a turn, no bound on the legs closes it. A
sufficiency statement for the landmark sentence therefore needs a hypothesis of a different kind,
and by the rule quoted above none should be written until a probe has covered arms of at least
twice the walk's length, which for the walks of `probe65b.c` is **forty** times; this batch reached
thirty, and by sampling rather than by a sweep. No new sufficiency statement is written here.

## 1. The targets

| target | file | state |
| --- | --- | --- |
| `s3_span_nine_mid5` | `HPC/Fold/Mixed.lean` | still `sorry`; this batch removes a route that did not exist — the batch-64 residue is false — and restates it so that the route is available again |
| `s3_span_nine` | `HPC/Fold/General.lean` | unchanged |
| `s3_general` | `HPC/Fold/General.lean` | unchanged |
| `theorem3` | `HPC/Fold/Open.lean` | unchanged, waits on `s3_general` |

What moved, exactly: `s3_span_nine_mid5_of_crossMid2_of_low1` (batch 64) reduced the branch at a
crossing to `CrossMid2L5`, and `CrossMid2L5` is false, so that reduction proved nothing. The same
reduction from `CrossMid2L5'` — the statement with the crossing of the trichotomy as a hypothesis —
is `s3_span_nine_mid5_of_crossMid2'_of_low1`, and it is a theorem. Everything else batch 64 proved
about the partner (`land_w71_ceil_of_wb`, `leg4Land_w71_of_wb_of_mid2`, the two-walk assemblies) is
about arms and crossings with `Mid2Floor` assumed, and is untouched.

## 2. The questions

### 2.1 `CrossMid2L5` from the pairing

**It does not follow from the pairing, because it is false.** See §0.1. The commission's own reading
of the question — "whether the clause read between that descent and the `w8` side's ascent returns
a peak on the *partner's* side at that descent" — is answered in the negative in the strongest way:
at the arm's index `5` there is no room for *any* landmark chain, whatever the pairing supplies,
because `Mid2Floor` wants an index in `[3, d − 4] = [3, 1]`. The peak the pairing returns lies on
the `w8` side, as the batch-64 census suggested, and no reading of it can be placed on the partner
at such a descent.

The commission's second question — "say what else on the partner supplies `L + 6` before its
`L + 2`" — has the answer *nothing*: `wb`'s ceiling clause fires at the descents to `L + 1` and not
at those to `L + 2` (that is the gap batch 64 identified), and the descent to `L + 2` does not
inherit the `L + 6`–`L + 3` chain, because an arm can reach `L + 2` five steps from the basepoint
while `wb`'s clause has not fired at all. The corpus measurement:

```
arms of the branch measured                                        2 786 644  (1 393 322 basepoints)
arms that descend to exactly 2 somewhere                           2 576 186
least arm index of a descent to exactly 2 seen anywhere                    5   (= the timing bound)
arms failing Mid2Floor                                               310 028
  of those, arms satisfying w8 / w71 / w72 (theorem: 0)              0 / 0 / 0
  of those, arms whose first descent to exactly 2 is at index ≤ 6      76 178
  the tag of the failing arm: wb 284 379;  w3 191 296;  neither             0
basepoints at which some arm fails Mid2Floor                         310 028
  of those, with the other arm served by w8 (counterexamples)        308 258
  of those, a walk of the four-leg family serves both arms anyway    310 028
  of those, genuine crossings of the trichotomy                              0   (of 461 crossings)
```

So the residue, corrected, is `CrossMid2L5'`, and what the corpus supports is exactly that: the
clause can fail on an arm of the branch, often, but never on the partner of a crossing.

### 2.2 The `w8` side's disjunction

**The two failures do not exclude each other; the two *clauses* nevertheless never fail together on
the corpus.** The commission asks whether "a witness stopping at `L + 2` and a `w8` side touching
`L` cannot both happen at one crossing". Over the 461 crossings with a single `w8` side
(`census-batch65.c`):

```
A, the partner's failing descents all stop at 2 (none reaches 1)      315
B, the w8 side touches 0                                              179
A and B together (the proposed exclusion asks for 0)                  142
neither                                                               109
w71's ceiling clause on the w8 side                                   374
w72's deep clause on the w8 side                                      451
either of the two (the disjunction)                                   461
the ceiling clause fails and A holds                                   87
the deep clause fails and B holds                                      10
```

So the proposed route is closed: `A ∧ B` happens at 142 of the 461 crossings, and the disjunction
cannot be obtained by excluding one of the two conditions. What the corpus does show is that the
two *clause failures* are disjoint — 87 crossings fail the ceiling clause, 10 fail the deep clause,
and `374 + 451 − 461 = 364` have both, so no crossing fails both — but that disjointness is a
measurement here and not a theorem, and the conditions `A` and `B` are not what separates them:
every one of the 87 has `A` and every one of the 10 has `B`, yet 142 crossings have both `A` and
`B` and fail neither clause. A proof of the disjunction therefore has to read more than which end
the witness stops at.

### 2.3 Assembly

Question 3 asked for the assembly "if 1 and 2 close". Neither closed: 1 is refuted and 2's proposed
route is refuted. What is assembled instead is the corrected reduction
`s3_span_nine_mid5_of_crossMid2'_of_low1`: at a crossing of the trichotomy whose forward arm is
served by `w8`, whose backward arm is served by `wb`, and whose crossing witness descends to
`L + 1`, the pair folds, given `CrossMid2L5'`. `Leg4SixCrossL5`, `s3_span_nine_mid5` and
`s3_span_nine` are not proved.

### 2.4 `LandWalkP3Suffices`

Refuted; see §0.2, and refuted again with the leg bound raised to four
(`not_landWalkPLegSuffices_le_four`). The probe bound is stated there as the commission asks: the
previous exhaustive bound was fourteen times against walks of up to twenty; this batch searched to
thirty times by randomised deep descents, and the bound the rule asks for — twice the walk's
length, forty times — has not been reached, so no replacement sufficiency statement is written. The inductive step the
commission asks for cannot be carried out for the statement as it stands.

## 3. Deliverables

**New Lean files, both `sorry`-free, no `native_decide`, no new axiom.**

* `HPC/Fold/CrossMid2Fail65.lean` — `mid2Floor_of_leg4Land`, `mid2Floor_of_leg4Land_w8`,
  `mid2Floor_of_leg4Land_w71`, `mid2Floor_of_leg4Land_w72`, `not_mid2Floor_of_early`,
  `not_leg4Land_of_early_low`, `arm_low_index_ge_five`, `armG_low_index_ge_five`,
  `armT_low_index_ge_five`, `bing9Pt`, `bing9Pt_level`, `bing9_armT_five`, `bing9_lowAt_armG`,
  `bing9_lowAt_armT`, `not_mid2Floor_bing9_armT`, `not_w8_bing9_armT`, `not_w71_bing9_armT`,
  `not_w72_bing9_armT`, `not_crossMid2L5`, `leg4Land_wb_bing9_armT`, `TriCrossL5`, `CrossMid2L5'`,
  `s3_span_nine_mid5_of_crossMid2'_of_low1`.
* `HPC/Fold/LandWalkFail65.lean` — `cexArm65`, the walk facts of `[5, 2, 6]` from `1`,
  `cex65_noShortLeg`, `cex65_band`, `cex65_isLip`, `cex65_trigger_bound`, `landWalkP_cex65`,
  `not_foldsOnto_cex65`, `not_landWalkP3Suffices`; and the leg-bound family `LegAtLeast`,
  `legAtLeast_mono`, `legAtLeast_three_iff_noShortLeg`, `LandWalkPLegSuffices`,
  `landWalkPLegSuffices_three_iff`, with the four-leg witness `cexArmB65`, the walk facts of
  `[5, 1, 6, 1]` from `0`, `cexB65_legAtLeast_four`, `cexB65_band`, `cexB65_isLip`,
  `cexB65_trigger_bound`, `landWalkP_cexB65`, `not_foldsOnto_cexB65`,
  `not_landWalkPLegSuffices_four` and `not_landWalkPLegSuffices_le_four`.

Both are imported by `HPC.lean`; `lake build HPC` is clean. The project's `sorry`s are exactly the
four standing targets it had before this batch — `s3_span_nine_mid5` (`Mixed.lean`), `s3_span_nine`
and `s3_general` (`General.lean`) and `theorem3` (`Open.lean`) — and nothing this batch adds uses
any of them. The only edits to earlier files are two docstring paragraphs recording the
refutations: one in `HPC/Fold/LandWalkFail64.lean` at `LandWalkP3Suffices`, and none was needed at
`CrossMid2L5`, whose refutation is stated in the new file that imports it. Both refuted statements
are kept exactly as they were delivered.

```
'HPC.Fold.mid2Floor_of_leg4Land' depends on axioms: [propext, Quot.sound]
'HPC.Fold.not_mid2Floor_of_early' depends on axioms: [propext, Quot.sound]
'HPC.Fold.not_leg4Land_of_early_low' depends on axioms: [propext, Quot.sound]
'HPC.Fold.arm_low_index_ge_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.armG_low_index_ge_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.armT_low_index_ge_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.bing9Pt_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.bing9_armT_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.bing9_lowAt_armG' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.bing9_lowAt_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_mid2Floor_bing9_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_w8_bing9_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_w71_bing9_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_w72_bing9_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_crossMid2L5' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.leg4Land_wb_bing9_armT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.s3_span_nine_mid5_of_crossMid2'_of_low1' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cex65_noShortLeg' does not depend on any axioms
'HPC.Fold.cex65_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cex65_isLip' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cex65_trigger_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.landWalkP_cex65' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_foldsOnto_cex65' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_landWalkP3Suffices' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.legAtLeast_mono' does not depend on any axioms
'HPC.Fold.legAtLeast_three_iff_noShortLeg' depends on axioms: [propext]
'HPC.Fold.landWalkPLegSuffices_three_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cexB65_legAtLeast_four' does not depend on any axioms
'HPC.Fold.cexB65_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cexB65_isLip' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.cexB65_trigger_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.landWalkP_cexB65' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_foldsOnto_cexB65' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_landWalkPLegSuffices_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.Fold.not_landWalkPLegSuffices_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Censuses over the general model, under the audit protocol.** `census-batch65.c` (log
`census-batch65.log`, run as `census-batch65 40 62 200 12`) is the batch-64 census with a batch-65
block added. The block reads `Mid2Floor` over **every** basepoint of the branch of the corpus and
not only over the stored crossings — the arms, their first descent to exactly `L + 2`, the walks
that do serve them, the trichotomy tag of every failing arm, and whether the basepoint is a
crossing — and measures the two failure modes of question 2 over the stored crossings. Every
predicate is evaluated by its own definition: `mid2Floor` is `Mid2Floor` written out at `L = 0` with
its existential searched literally, `landLeg4` is `Leg4Land` clause by clause, `ceil71Clause`,
`deep72Clause`, `touchesZero`, `reachesNine` and `w8FloorFailLow` are the batch-64 definitions, and
no criterion of the engine is used anywhere in the block. The block ends with its own audit
paragraph and the run's global definition audit is unchanged.

`probe65.c` (log `probe65.log`) is a census over Bing's plain chain alone, and says so: it reads
the basepoint `145` link by link — the tags of both arms, `LowAt`, `Mid2Floor`, the first descent
to exactly `L + 2`, `w71` and `w72` — and then sweeps the chain's 232 branch basepoints, finding 52
with an arm failing `Mid2Floor`, none of them a crossing.

`probe65b.c` (log `probe65b.log`) is the search of §0.2, over **walks and arms** and not over the
general model. It enumerates walks by their turning levels — at most four turns, levels in `[0, 6]`,
shortest leg at least three — and for each runs randomised depth-first descents over 1-Lipschitz
arms to **thirty** times with a budget of two million nodes per walk, pruning on the two
prefix-monotone conditions (a level of the arm that no time of the walk serves, and a trigger the
sentence leaves unmet, are both permanent). It evaluates `walkList`, `walkLen`, `walkStop`,
`walkLevel`, the corrected sentence and `FoldsOnto` by their own definitions, deciding the chain by
the backwards greedy (optimal: each landmark as late as possible) and folding by reachability over
the walk's positions. It is a sample and not a sweep: 742 walks, 1 421 562 594 arms tested, 43
counterexamples, deepest prefix reached thirty. Its arm-length bound is thirty times, against walks
of up to twenty times; the rule of §0 of the batch-64 report asks for forty, which has not been
reached and which is why no new sufficiency statement is written.

The numbers quoted in §0 and §2 are from those three programs and their logs.

## 4. Not in this batch

Spans ten and above; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index
check; Bing's seam. No new sufficiency statement for the landmark sentence, for the reason in §2.4.
