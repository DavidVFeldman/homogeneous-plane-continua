# Commission: batch 59 — exact criteria for four legs

**Go!** Runs on top of the batch-58 delivery. No new file is prescribed.

## 0. On batch 58

Audited: every earlier Lean file identical except the docstring of `s3_span_nine_mid5`; five new
files; standard axioms, no `native_decide`; no target refuted. Three route statements refuted at
faithful witnesses with faithfulness proved in the kernel (`PairCheck.lean` states the search once
for any length; `Leg4Scan.lean` makes a 175-link refutation affordable by a linear scan). One
positive fact: the branch hypothesis `LowAt (L + 1) (L + 8)` *is* the descent announcement of the
walk `L+6 → L+3 → L+7 → L+1 → L+8` (`down1_of_lowAt`), so at that walk the branch owes two
announcements about ascents and nothing else (`s3_span_nine_mid5_of_ascents`). First time a branch
hypothesis and a walk's criterion have matched clause for clause.

What the refutations say, together: the four-leg engine's criteria are **sound and far from
necessary**. The walks serve the branch — every one of the 867 basepoints the reflected three-turn
walks miss is served by a four-leg walk — but no criterion of the engine's window holds on a
175-link thin arm of Bing's own chain that some walk of the window does serve, and the interval
reading of the criteria is unsound (nine-link witness). At `L + 4` exhaustiveness was two
arm-only dichotomies, and those existed because the three-leg criteria are *exact*
(`foldsOnto_leg3deep_iff_landmark`, `foldsOnto_w4_iff_landmark`, `foldsOnto_w5_iff_landmark`). At
`L + 5` there is no exact criterion for any four-leg walk, and that is the whole difference.

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`), with `s3_span_nine_mid5_of_ascents` as its current form.
2. `s3_span_nine` (`General.lean`).
3. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **An exact criterion for a four-leg walk.** The necessity half of the landmark sentence is a
   theorem for every walk (`foldsOnto_landmark1`, `foldsOnto_landmark2`, batch 49); for three legs
   the sufficiency half was proved by the batch-48 invariants and the two halves met. Whether the
   landmark sentence for `leg4Walk L H K M P` — with its landmarks at `K`, `M`, `H − 1` and the
   index bounds the walk's positions dictate — is *equivalent* to the fold, on the wide window, is
   asked. The census can test the candidate sentence against `foldsB` before it is attempted, as
   `census-batch47c.c` did for three legs. If it is exact, the dichotomies of `L + 4` have their
   analogue; if some arm folds without meeting it, the sentence is missing a landmark and the census
   will show which.
2. **The 175-link witness.** Which walks of the family serve the arm of `Audit58`, and what does
   the exact criterion of question 1 say about it. The arm is thin and from `bing 0 9`, so whatever
   serves it is a fact about Bing's chain itself.
3. **Exhaustiveness at `L + 5`, given exact criteria.** With an exact criterion per walk, the
   statement "every arm of the branch meets one of the criteria or fails a clause the partner arm's
   criterion consumes" becomes decidable on the corpus arm by arm. Whether it holds, and with which
   finite list of walks, is the branch's exhaustiveness in the form batch 58 §2.2 says it must take.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the audit protocol; censuses over arms alone say so.
3. Report: any counterexample first; then §1; then §2 1–3.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam
(paraphrase to be checked against the paper first).
