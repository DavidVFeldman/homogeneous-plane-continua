# Report: batch 44 — the third walk, and the engine it needs

Runs on top of the batch-43 delivery. Everything earlier is untouched. `HPC/Fold/Mixed.lean` is
the commissioned file; `HPC/Fold/Leg3Deep.lean` is new and is the engine the batch turned out to
need; root `HPC.lean` imports both. `lake build HPC` succeeds. The only `sorry`s in the project
are `theorem3` (`HPC/Fold/Open.lean`), the two targets of `HPC/Fold/General.lean`, and, in
`Mixed.lean`, `s3_span_nine_mid5` and the two named work items `unserved_high8`,
`unserved_valley`. `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for
everything proved.

**No counterexample was found.** Every one of the 66 382 branch pairs the census met is served by
a walk; nothing in the batch points at `S3` being false at span nine.

## 0. What is proved

**The third walk has an engine and a criterion.** The walk that batch 43 identified —
`L+3 → L+6 → L+1 → L+8` — is `leg3Walk L (L+9) (L+6) (L+4)` in the repository's notation: three
legs, valley at the floor level `L + 1`, basepoint `L + 4`. It is *not* a walk of the four-leg
engine `HPC/Fold/Leg4.lean`, whose hypothesis `hPM : P - 2 ≤ M` forces the valley to `L + 2`; and
it is not a walk of the three-leg engine `HPC/Fold/Leg3.lean`, whose hypothesis `hPL : P ≤ L + 3`
keeps the basepoint within two of the valley. That is why batch 43 had to exhibit its fold by an
explicit time assignment.

`HPC/Fold/Leg3Deep.lean` closes the gap. `foldsOnto_leg3_deep` is `foldsOnto_leg3` with
`P ≤ L + 4` in place of `P ≤ L + 3`, at the price of exactly one announcement: at `P = L + 3` the
valley `L + 1` lies inside the window of the walk time `0`, so descents to it need no
announcement, while at `P = L + 4` they do (the arm `L+4, L+3, L+2, L+1` folds onto no prefix of
the walk). The invariant, its four features and its eleven progress clauses are those of
`HPC/Fold/Leg3.lean` with the floor clause read one level higher.

On top of it:

* `foldsOnto_leg3deep_branch` — an arm of the branch folds onto `L+3 → L+6 → L+1 → L+8` as soon as
  (i) every descent to `L + 1` is preceded by a time at `L + 6` or above (or by a time at `L + 1`
  or below followed by one at `L + 5` or above), and (ii) every ascent to `L + 8` is preceded by a
  time at `L + 1` or below. The engine's ceiling announcement, which is a three-time clause, is
  *derived* from (ii) by one application of the crookedness clause (`valleyBranch_ceiling`).
* `s3_span_nine_mid4_of_valley` — both arms of a basepoint at `L + 4` satisfying (i) and (ii) fold
  onto that one walk. This is the third walk with a criterion of its own, which is what
  REPORT-batch43.md named as missing.

**The branch `L + 4` is now a two-line case analysis over three walks.** `s3_span_nine_mid4` is
proved from: the Λ-walk if both arms fold onto it, the V-walk if both arms fold onto it, and
otherwise `s3_span_nine_mid4_of_valley` — with the two hypotheses (i), (ii) supplied by the two
work items `unserved_valley`, `unserved_high8`, which are the only `sorry`s of the branch.

**Two facts that halve those work items.** `valley_or_vee`: an arm that fails (i) folds onto the
V-walk. `high8_or_lam`: an arm that fails (ii) folds onto the Λ-walk. (Both use the timing law:
`crookDown_fall3` puts the arm's first descent to `L + 1` at index four or later, `crookUp_climb4`
puts a time at `L + 8` at index seven or later, which is what the exact profile criteria of
`HPC/Fold/Profile.lean` ask for.) So the failure of (i) or (ii) is never the fault of the arm that
exhibits it: what remains in each work item is that the *other* arm then also folds onto the same
walk — a statement across the basepoint.

**Two general facts, new in the repository.**

* `arm_lam_or_vee` (from `ann_dichotomy`): every arm satisfies the Λ-announcement or the
  V-announcement. Batch 43 checked "no arm of the census fails both criteria"; it is now proved,
  and for arbitrary integer sequences: whichever of the two events happens first decides.
* `seq_gap`, `cross_gap_ge`, `cross_gap_le`, `mix_events_far` — Bing's timing law (`minGap`) read
  **across the basepoint**, as `armG_gap` and `armT_gap` of batch 43 read it along one arm. The
  consequence for the mixed configuration is quantitative: if the backward arm stands at `L + 1`
  at its step `dT` and the forward arm at `L + 7` at its step `dG`, then `dT + dG ≥ 70`, because
  the window between the two times spans six levels and `z 6 = 71`. A pair may be mixed, but not
  mixed early.

## 1. §2.1 — are three walks enough on actual pairs?

**On the corpus, yes, and the third walk is forced.** `census-batch44b.c` (log
`census-batch44b.log`) decides folding *exactly*, by the dynamic program over the definition
`FoldsOnto`, not by any criterion or announcement; and it ranges over actual faithful crooked
sequences in the thin form `sigma = rho`, verified pair by pair by the routine of
`census-batch43.c`. Over 66 382 branch basepoints (`bing 0 9` entire, its windows of span nine,
`bing a b` with `|a-b| ≥ 9`, and crooked concatenations):

| | |
|---|---|
| served by the Λ-walk based at `L+3` | 10 425 |
| served by the V-walk based at `L+5` | 37 010 |
| served by neither | 19 184 |
| of those, served by `L+3 → L+6 → L+1 → L+8` | **19 184** |
| served by no walk of at most three legs | **0** |

So the three-walk claim of batch 43 stands, on a corpus thirty times larger and with the fold
decided exactly. Two further facts from the same run:

* **No single walk serves the whole branch.** Intersecting the walks of at most four legs over
  all 66 382 branch pairs leaves nothing. A rule choosing among walks is unavoidable.
* **Exactly four walks of at most three legs serve all 19 184 pairs the canonical walks miss**, and
  all four are `L+3 → L+6 → L+1 → L+8` or `L+3 → L+7 → L+1 → L+8`, with or without a last step to
  `L + 9`. Every one of them has its valley at the floor `L + 1` and its basepoint at `L + 4`, so
  every one of them needs the new engine.
* Of the nine walks that the engines *already in the repository* can produce at this basepoint
  (Λ and V based at `L+3, L+4, L+5`; the four-leg engine with `K = L+6, L+7, L+8`), none serves
  6 254 of the branch pairs. The valley of the four-leg engine is pinned at `L + 2`, and moving it
  to `L + 1` is the whole difference: `L+3 → L+6 → L+2 → L+8` serves 12 930 of the 19 184.

**The two hypotheses of the third walk hold exactly where they are needed.** Over the 38 368 arms
of the 19 184 pairs the canonical walks miss, the valley announcement holds 38 368 times and the
`L + 1`-before-`L + 8` clause holds 38 368 times. Over all 132 764 branch arms each fails about a
quarter of the time, and over the arms of merely *mixed* pairs (one arm Λ-only, one V-only by
announcement) the failures are 47 250 and 34 880. So the work items are correctly conditioned on
the pair, not on the branch: a fact worth recording, since the first form this batch tried —
conditioning on the mixed configuration alone — is false, and the census refuted it before it was
proved.

## 2. §2.2 — does the thin form `sigma = rho` lose anything?

Not settled. Both censuses of this batch range over thin sequences only, and say so. What can be
said is that nothing in the Lean material depends on thinness: every theorem proved here is
stated for the faithful model `IsCrookedIvF ρ σ`, and the thin sequences enter only as the source
of the counts above. The question — whether every arm-pair of the faithful model is an arm-pair of
some thin sequence — is untouched, and the honest reading of the counts is the one the commission
asks for: they are counts over a subclass of actual pairs.

## 3. §2.3 — is the count of walks per branch a function of the span?

The batch gives one new datum rather than an answer. At span nine the branch `L + 4` needs three
walks, and the third is forced up to the four listed above; at span eight the middle basepoint
needed four. What the batch *does* show is that the shapes are not free: the third walk is exactly
the `leg3Walk` family one level deeper than the engine of batch 38 allowed, so the family of walks
the repository can drive grew by one parameter value, not by a new construction. Whether the count
follows from the leaf and the profile criteria without a search is still open; the evidence here is
that the walk is determined by the *timing* facts — the valley must be reachable by step seven,
which is the first step at which an arm can stand at `L + 1` and still be announced — rather than
by the events.

## 4. Deliverables

1. Proved, `sorry`-free, standard axioms: `foldsOnto_leg3_deep` and the whole of
   `HPC/Fold/Leg3Deep.lean`; in `HPC/Fold/Mixed.lean`: `ann_dichotomy`, `arm_lam_or_vee`,
   `seq_gap`, `cross_gap_ge`, `cross_gap_le`, `mix_events_far`, `mix_events_far'`,
   `valleyBranch_ceiling`, `foldsOnto_leg3deep_branch`, `s3_span_nine_mid4_of_valley`,
   `foldsOnto_vee_of_valley_fail`, `foldsOnto_lam_of_high8_fail`, `valley_or_vee`, `high8_or_lam`,
   `lamAnn_valley`, `veeAnn_high8`; and `s3_span_nine_mid4` modulo its two work items.
2. Censuses. `census-batch44.c` (log `census-batch44.log`) — announcements and the greedy of the
   four-leg engine; `census-batch44b.c` (log `census-batch44b.log`) — the exact fold, the walk
   families, and the counts of §1. Both range over **thin** faithful crooked sequences
   (`sigma = rho`), each verified pair by pair against `IsCrookedIvF`, with the test first run on
   paths whose status is known. Nothing in them ranges over a one-arm class.
3. What is open: `s3_span_nine_mid5`; the two work items `unserved_high8` and `unserved_valley`;
   and, above them, `s3_span_nine`, `s3_general`, `theorem3`.
