# Commission: batch 58 — the branch `L + 5` by the walk that reads `L + 6`

**Go!** Runs on top of the batch-57 delivery. No new file is prescribed.

## 0. On batch 57

Audited: every earlier Lean file identical except `General.lean` and `Mixed.lean` (docstrings);
two new files; standard axioms, no `native_decide`; no target refuted. The reflected valley
crossing at `L + 5` is refuted by a 71-link faithful pair whose faithfulness is itself proved in
the kernel (`Audit57.faithful`, `not_reflValleyCrossL5`) — the first non-thin refutation in the
repository that leaves nothing to the census. The timing bounds transport to `L + 5` verbatim
(`FloorFar.lean`: the witness is still ten steps out); what does not transport is the level:
reading the clause upward at an ascent returns a link whose interval reaches `L + 7` and whose
`ρ` may sit at `L + 6`, and the criterion reads `ρ`. The census fixes the shape: 486 point-form
failures of the partner criterion, 0 interval-form failures, all on mixtures.

Three facts fixed by the batch:

* **The two branches are not mirror images at any level**: not in the crookedness clauses (batch
  48), not in the crossings (this batch), and not even in the branch hypotheses — `LowAt` carries
  a second clause `HighAt` does not, and 298 522 reflected basepoints fail `HighAt`.
* **The model reads levels from below.** A link is `[ρ, ρ + 1]`; a level read from below on `ρ`
  and from above on `σ` differ by one, and the criteria read `ρ`. This is the asymmetry that
  survived `ivSep`, and it is the one the report names as "the next batch's question".
* **Bing's seam with the end clause imposed: unchanged.** The clause excludes no least
  consolidation (2 028 of 2 028 satisfy it), and the batch-56 table is reproduced: no width-three
  seam, `F` not a chain at 25 of 84 thin and 463 of 820 general basepoints. One caution is
  recorded before this becomes a proposition: the construction was transcribed from a paraphrase
  of p. 733, not from the paper's text. The exposition's author will check the wording; until
  then the finding is about the paraphrase.

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`).
2. `s3_span_nine` (`General.lean`).
3. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The walk that reads `L + 6`.** The report names `L+4 → L+7 → L+1 → L+8 → L+1`
   (`foldsOnto_walk47181`) as the candidate: its floor announcement consumes exactly the pair of
   links the clause returns (`L + 3` then `L + 6`), and it alone serves 749 of the 950 residual
   basepoints. Its other two announcements read `L + 7` and `L + 9` on `ρ`. Whether the branch
   hypothesis `LowAt (L + 1) (L + 8)` — in particular its second clause, the one `HighAt` lacks —
   together with `ivSep` supplies those two, is the branch. If they are one level short in the same
   way, whether a walk one level lower (peak `L + 6` in place of `L + 7`) has a criterion the clause
   can meet, is the question after it.
2. **Exhaustiveness without search.** The report's answer to the template question is that the
   list of walks at each `(span, level)` must be proved exhaustive, and at span nine that exists
   only for `L + 4`. At `L + 4` exhaustiveness was not a search: it was two arm-only dichotomies
   (`leg3Valley_or_vee`, `leg3Ceil_or_lam`) that put every arm on a canonical walk or into a
   clause, plus the crossings. Whether the same holds at `L + 5` — every arm of the branch fails
   one of a finite set of clauses or folds onto a canonical walk, and the failures cross — is asked
   as the form exhaustiveness takes; if a set of clauses closes the arms at `L + 5` the way two did
   at `L + 4`, say which, and whether the set is the same at every span up to reflection of the
   *clauses* (which do reflect) rather than of the model (which does not).
3. **The criteria's tolerance.** Every exact criterion reads "within one of the landmark" and
   spends that tolerance on the walk's own peak. Whether a criterion can be stated for a fold onto
   the same walk that reads high landmarks on the interval — `σ ≥ l` rather than `ρ ≥ l − 1` — and
   whether `foldsOnto_landmark2` (necessity) and the engines (sufficiency) survive that reading,
   is asked. If they do, the level of §0 is bookkeeping; if the necessity half fails, the census
   will show an arm that meets the interval reading and does not fold.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the audit protocol; censuses over arms alone say so.
3. Report: any counterexample first; then §1; then §2 1–3.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam
(the paraphrase is to be checked against the paper before the next run of it).
