import HPC.Fold.Span9Mid5
import HPC.Fold.Zig77Main

/-!
# `S3` at every span

State of the fold route after batch 41 (all proved, standard axioms):

* `theorem3_of_S3` — `S3` gives Bing 1948 Theorem 3 (`HPC/Fold/Span.lean`);
* `s3_span_seven_of_cases` — no span hypothesis: a basepoint at level `p` can fail only when
  both arms are `HighAt (p - 3) H` and both arms are `LowAt L (p + 3)` (the leaf);
* `s3_span_eight` — every basepoint at span at most eight;
* `s3_span_nine_except` — every basepoint at span at most nine except two named branches:
  `ρ i = L + 4` with both arms `HighAt (L + 1) (L + 8)`, and `ρ i = L + 5` with both arms
  `LowAt (L + 1) (L + 8)`.

Every fold lemma so far proves a statement about a *class* of single arms (a branch of the
dichotomy tree) and serves every arm of the class with one walk. `S3` asks for less: a walk for
the two arms of one sequence at one basepoint.

**Batch 77: closed.** No `sorry` remains in this file: the target is proved from `Z77.s3_zig`
(`HPC/Fold/Zig77Main.lean`). The history below is kept as it was.

Every `sorry` is a work item. Uncompiled.

**After batch 42.** Neither target below is proved. What this batch added instead is the exact
criterion for the fold, in `HPC/Fold/Profile.lean`: an arm starting within one of `p` folds onto
the Λ-walk based at `p` if and only if, before it ever drops to `p - 2`, it stands at the peak
level `κ - 1` at an index at least `κ - p` (`foldsOnto_lam_iff_profile`,
`critLamProfile_iff_of_isLip`), and the mirror statement for the V-walk
(`foldsOnto_vee_iff_profile`). What decides a fold is therefore not which events occur in an arm
but how late they occur, and crookedness bounds that: three levels need four steps, four levels
seven, five levels twelve (`crookUp_climb3`, `crookUp_climb4`, `crookUp_climb5`, and their
reflections). `HPC/Fold/Span9Profile.lean` applies this to the two open branches: at either of
them a basepoint is served as soon as its two arms meet the *same* end of the band first. The
census of REPORT-batch42.md finds no arm of the branch that meets neither, so what is left open
at span nine is a basepoint whose two arms meet different ends first.

`HPC/Fold/CrossArm.lean` reads the crookedness clause across the basepoint — `crookUp_seq`,
`crookDown_seq` — and excludes the first sub-case of that configuration: no basepoint of a
span-nine sequence keeps one arm off the floor of the band and the other off its ceiling
(`no_arm_split_high_low`, `s3_span_nine_no_vacuous_mix`). It also makes the gap exact:
`s3_span_nine_of_attained` reduces `s3_span_nine` to the case in which both ends of the band are
attained, and `s3_span_nine_of_mid` reduces it further to the two branches above, stated with
those ends as hypotheses.

**After batch 43.** Neither target below is proved, and the configuration left open is now known
to be inhabited, so it cannot be excluded. `HPC/Fold/Timing.lean` reads Bing's Theorem 7 on an arm
(`armG_gap`, `armT_gap`) and so removes the index clause from the Λ-criterion at the branch
`L + 4` (`s3_span_nine_mid_low_of_lam`). With the criteria in that exact form,
`HPC/Fold/MixedWitness.lean` exhibits an actual faithful crooked pair — basepoint `138` of the
409-link chain `ceSeq`, in the band `[0, 9]`, both arms `HighAt (L+1) (L+8)` — at which the
Λ-walk fails on one arm and the V-walk on the other (`mix_no_common_walk_of_the_two`), and at
which a four-leg walk `L+3 → L+6 → L+1 → L+8` folds both (`mix_served_by_four_leg`). The census
`census-batch43.c` finds 55 such basepoints among the 182 of the branch in `bing 0 9`, all served
by that walk. What span nine needs is therefore a third walk with an exact criterion of its own,
and a rule choosing between the three; the batch-42 census that reported the configuration empty
had skipped every basepoint with an arm of more than 512 links.

**After batch 45.** Neither target below is proved in the general model, and one of them is now
proved in the thin form of the model. The batch-44 work item `unserved_high8` was refuted on an
actual pair (`not_unservedHigh8`, `HPC/Fold/Bing9Witness.lean`), the branch `L + 4` was re-split
on the announcement the three-leg engine actually consumes (`CeilAnn`, `HPC/Fold/Mixed.lean`),
and for a **thin** sequence `σ = ρ` the two remaining work items, both branches and the whole of
span nine are theorems: `s3_span_nine_thin` (`HPC/Fold/ThinSpan9.lean`). The general model is
short by one level — where the thin crookedness clause produces a time at `L + 7`, the general
clause produces only a link with `ρ = L + 6` and `σ = L + 7` — and the two targets below also
wait on the spans ten and above, which no batch has yet opened.

**After batch 47.** Neither target below is proved. The branch `L + 4` rests on one work item,
`unserved_leg3deep` (`HPC/Fold/Mixed.lean`): a pair of the branch folding onto neither canonical
walk has both arms folding onto the third walk `L+3 → L+6 → L+1 → L+8` itself. Three facts about
the general model were settled on the way: the *raise* of a faithful pair — every link read at the
greatest level it meets — need not be faithful, so not every faithful pair is a shaving of a thin
one (`HPC/Fold/Raise.lean`); a fold read on `σ` instead of `ρ` gives blocks inside four
consecutive links and not three (`HPC/Fold/LinkFold.lean`); and the model is symmetric under
reflection of the levels, with *filling a valley* as the reflection of shaving a peak
(`HPC/Fold/Reflect.lean`).

**After batch 48.** Neither target below is proved, and the branch `L + 4` is down to two
statements across the basepoint. The arm-only half is now a theorem: a 1-Lipschitz arm based at
`L + 4` meeting the two profile clauses folds onto the third walk `L+3 → L+6 → L+1 → L+8`
(`foldsOnto_leg3deep_profile`, and in its sharpest form `foldsOnto_leg3deep_profile_min`,
`HPC/Fold/Leg3Profile.lean`), proved by carrying the greedy time with four numerical invariants —
a clock, the `R` bound, a slack clock and the `S` bound — in place of the four history features of
the engine. An arm *failing* a clause is served by a canonical walk on its own
(`leg3Valley_or_vee`, `leg3Ceil_or_lam`), so an unserved pair has an arm meeting each clause
(`unserved_profile_one`), and `unserved_profile` is now a derivation from `cross_valley_profile`
and `cross_ceil_profile`: if either arm fails a clause, both arms fold onto the same canonical
walk. The branch `L + 5` is not the reflection of the branch `L + 4` in the general model: the
reflected point sequence is `a − σ`, which stands at `L + 4` at the basepoint only when the link
there is thin, and the folds it delivers are folds of `a − σ` and not of `a − ρ`, a difference
that costs one link (`HPC/Fold/LinkFold.lean`). See REPORT-batch48.md.

**After batch 49.** Neither target below is proved, and the route the branch `L + 4` took through
a single third walk is **refuted**. Three statements fall together at one basepoint of the general
model — the basepoint `336` of `bing9sB`, `bing 0 9` with one peak shaved, which batch 46 already
used: `cross_ceil_profile`, `unserved_profile` and `unserved_leg3deep` (`not_crossCeilProfile`,
`not_unservedProfile`, `not_unservedLeg3deep`, `HPC/Fold/CrossWitness.lean`). What decides them is
a converse the development did not have: by the itinerary's intermediate value theorem the
landmark sentence of a walk is **necessary** for a fold onto it (`foldsOnto_landmark1`,
`foldsOnto_landmark2`, `HPC/Fold/Landmark.lean`), so for the third walk `Leg3Ceil` is necessary as
well as sufficient and the criterion is exact (`foldsOnto_leg3deep_iff_landmark`) — and the arm at
that basepoint fails `Leg3Ceil`, so no fold onto that walk is possible. The pair is served all the
same, by the reflected walk `L+3 → L+2 → L+8 → L+1`, and the branch is re-split on
`unserved_three_walks` (`HPC/Fold/Mixed.lean`): an unserved pair folds onto one of three named
walks. The earlier censuses had missed the basepoint because they read the hypothesis
`HighAt (armG ρ i) (L + 1) (L + 8)` one level lower than the definition does; `census-batch49b.c`
reads it as the definition does. See REPORT-batch49.md.

**After batch 57.** Neither target below is proved. The branch `L + 4` is complete since batch 56,
and the branch `L + 5` is now known not to close by reflecting it: `ReflValleyCrossL5`, the
reflection of the valley crossing `cross_valley_vee_pair`, is refuted at an explicit 71-link
faithful pair (`not_reflValleyCrossL5`, `HPC/Fold/Audit57.lean`), the faithfulness of the pair
being itself checked by the kernel. What does reflect is the timing: `HPC/Fold/FloorFar.lean`
proves that the crookedness clause and Bing's Theorem 7 still place the witness ten steps from the
basepoint at the branch `L + 5`, but only as a link whose *interval* reaches `L + 7` — its `ρ` may
be `L + 6`, and the Λ-criterion reads `ρ`. That one level is the whole obstruction: over the
corpus of `census-batch57.c` the point form of the witness fails at 486 pairs and the interval form
at none, and the five reflected walks leave 950 of 1 378 202 basepoints of the branch, every one of
them served by the four-leg family. See REPORT-batch57.md.

**After batch 68.** `s3_span_nine` below needs no case beyond the two branches: `s3_span_nine_of_mid`
(`HPC/Fold/CrossArm.lean`) reduces span nine to them, and `s3_span_nine'` (`HPC/Fold/Mixed.lean`) is
that reduction applied to `s3_span_nine_mid4` and `s3_span_nine_mid5`, so the statement below is
`sorry` only for as long as `s3_span_nine_mid5` is. At the branch `L + 5` the crossings of the
trichotomy now split in two: where both arms have been at `L + 2` or below before each of their own
times at `L + 9` the pair folds onto `w71` (`s3_span_nine_mid5_of_cross_deepFirst2`,
`HPC/Fold/Ceil68.lean`, 374 of the corpus's 461 crossings), and the rest — the crossings whose `w8`
side reaches `L + 9` with nothing at `L + 2` or below before it — are reduced to `w72`'s ceiling
clause on that arm (`s3_span_nine_mid5_of_cross_highRun_armG`). See REPORT-batch68.md.

**After batch 69.** That last clause is discharged, under one distance hypothesis:
`ceil72_of_nearLowT_armG` (`HPC/Fold/Ceil69.lean`) proves `w72`'s ceiling clause on an arm as soon
as the pair has a time at `L + 2` or below within 67 steps across the basepoint — the crookedness
pairing read between that time and the arm's ascent returns both of the clause's landmarks as times
of the arm, the valley at `L + 3` and seventy steps before the ascent, which is what the census sees
at all 87 high-run crossings of the corpus. The same pairing gives the running arm `w72`'s
deep-floor clause where its descents to the floor come after the run (`deep72_of_nearLowT_armG`).
What the branch at `L + 5` still owes is three statements about the two arms of a crossing, all of
which hold throughout the corpus and none of which is proved: the distance hypothesis
(`NearLowT` / `NearLowG`), the partner's deep-floor clause, and the partner stopping below `L + 9`
(the complementary case being named `BothNineL5`). See REPORT-batch69.md.
-/

namespace HPC.Fold

-- Commented-out statement `s3_span_nine` removed in batch 103; see `LEDGER.md`.

/-- **`S3`, every span.** Proved in batch 77 by the greedy jump zigzag,
`HPC/Fold/Zig77Main.lean` (`Z77.s3_zig`). -/
theorem s3_general : S3 := Z77.s3_zig

end HPC.Fold
