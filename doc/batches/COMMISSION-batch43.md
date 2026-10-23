# Commission: batch 43 — Bing's timing law on arms, and the mixed configuration

**Go!** Runs on top of the batch-42 delivery. One new file, `HPC/Fold/Timing.lean`; root
`HPC.lean` updated. Nothing else touched.

## 0. On batch 42

Audited: every earlier Lean file identical; live `sorry`s are `theorem3` (`Open.lean`) and the two
commissioned targets of `General.lean`. The answers to §2.1 and §2.2 are the result of the batch:
the open branches are inhabited by actual pairs (10 588 and 11 184 in the windows of
`bing 0 N`, `N = 9, 10, 11`), all served, all by one Λ-walk (its mirror at `L + 5`); and
`foldsOnto_lam_iff_profile` / `foldsOnto_vee_iff_profile` make the fold exact, with the timing of
events, not the events alone, deciding it. `no_arm_split_high_low` is the first fold argument in
the repository to use the clause across the basepoint.

## 1. A timing law already in the repository

`minGap` (batch 30, the engine of Bing's Theorem 7) with `isCrookedIvF_restrict` bounds how fast
an arm of a faithful crooked sequence moves: levels `d` apart are at least `z d - 1` steps apart,
`z = 1, 2, 3, 6, 13, 30, 71, 170, 409, 986, …`. Three levels take five steps, four take twelve,
five take twenty-nine. The census `census-batch42g.c` and the lemmas `crookUp_climb3/4/5` use the
one-arm clause `CrookUp`/`CrookDown`, which is a function of `ρ` along the arm alone, and give
four, seven, twelve. The one-arm class is strictly larger than the class of actual arms.

Three consequences for the batch-42 record, stated as facts:

* The negative witness `4 3 2 2 1` (offsets from `L`) for "the branch at `L + 4` is not served by
  the Λ-walk" falls three levels in four steps, so it is not an arm of any faithful crooked
  sequence. The longer witnesses of `census-batch42h.log` (`4 3 2 2 2 1`, …) pass the step
  count; whether any of them, or any *actual* arm of the branch, fails the Λ-walk is open.
* The index clause `5 ≤ j` of `s3_span_nine_mid_low_of_lamProfile` follows from the level `L + 7`
  (three levels above the basepoint). `s3_span_nine_mid_low_of_lam` in `Timing.lean` states that
  form.
* `z 9 = 986`, so every faithful crooked sequence of span nine has at least 986 links
  (`minimality`). That is why the exhaustive and random censuses of `census-batch42.c` and
  `census-batch42c.c` found no sequence of span nine, and why any census of span nine is a census
  of long sequences.

## 2. Questions, asked as questions

1. **Is the mixed configuration inhabited?** A faithful crooked sequence of span nine (with both
   ends attained) and a basepoint in an open branch whose two arms meet different ends of the band
   first. Exhibiting one — by construction if not by search — or excluding it in Lean are both
   answers. If one exists and is unserved, that is a counterexample to `theorem3` and is reported
   first.
2. **Does the Λ-walk serve every actual pair of the branch at `L + 4`?** Equivalently, by
   `s3_span_nine_mid_low_of_lam`: does each arm of such a basepoint stand at `L + 7` before it
   drops to `L + 1`?
3. **Does the profile criterion with the timing law give a uniform statement?** `S3` at every span,
   or a reduction of it that no longer mentions a span.

No opinion is offered on the answers.

## 3. Targets

1. `armG_gap`, `armT_gap`, `s3_span_nine_mid_low_of_lam` in `Timing.lean`.
2. `s3_span_nine`, `s3_general` in `General.lean`; if `s3_general` is proved, close `theorem3`
   by `theorem3_of_S3`.

A counterexample is a success and is reported first.

## 4. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. A census of whatever was explored. Each census says whether it ranges over actual sequences
   (which ones), over arms of actual sequences, or over a class defined by one-arm clauses. A
   negative witness from a one-arm class is checked against `armG_gap` before it is reported.
3. Report: any counterexample first; then §2 1–3 in order, negative answers included.
   **Settling §2.1 or §2.2 without proving a span target is a good outcome.**

## 5. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
