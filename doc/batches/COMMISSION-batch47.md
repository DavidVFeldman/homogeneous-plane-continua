# Commission: batch 47 — the branch at `L + 4` in the general model

**Go!** Runs on top of the delivery that carried batches 45 and 46 (Aristotle's numbering). No new
file: the targets are the `sorry`s of `HPC/Fold/Mixed.lean` and `HPC/Fold/General.lean` as they
stand. Root `HPC.lean` unchanged.

## 0. On batches 45 and 46

Audited: every earlier Lean file identical except `Mixed.lean` and the `General.lean` docstring;
`bing 0 9` is in Lean and faithful (`bing9_faithful`); span nine is proved for thin sequences
(`s3_span_nine_thin`); the thin model is reflection-symmetric (`isCrookedIvF_reflect`); shaving a
strict peak preserves faithfulness (`isCrookedIvF_shave`); and both work items of batch 44 are
refuted by shaved chains (`not_unservedCeiling`, `not_unservedValley`). Standard axioms, no
`native_decide`. Live `sorry`s: `theorem3`, `s3_span_nine`, `s3_general`, `s3_span_nine_mid4`,
`s3_span_nine_mid5`, all in the general model.

The two refutations were of statements the runs formulated themselves; both were supported only
by thin censuses, which the runs then showed could not have refuted them. Three things from this
pair of batches are worth carrying forward as fixed facts:

* **The general model is the target, not an artifact.** By `realization` (batch 22) every faithful
  pair `(ρ, σ)`, shaved or not, is the `(minIdx, maxIdx)` of an actual 1948-crooked chain. The
  conclusion of Theorem 3 comes from `exists_blocks_first_of_folds`, which is stated for a fold of
  `minIdx`, that is of `ρ`. So the arms to be folded are arms of `ρ`, and the clause returns links.
* **No census over thin sequences is evidence about the open statements.** From here every census
  says it ranges over the general model and how its non-thin pairs were generated.
* **Span nine on thin sequences is proved.** Whatever closes the general branch, the thin case is
  the check it must pass.

## 1. Targets

`s3_span_nine_mid4`, `s3_span_nine_mid5` in `Mixed.lean`; then `s3_span_nine`, `s3_general` in
`General.lean`; if `s3_general` is proved, close `theorem3` by `theorem3_of_S3`. A counterexample
to any of these is a success and is reported first. If a route is refuted, the refuted statement is
kept, commented out, with the refutation named, as batch 46 did.

REPORT-batch46.md §5 records two candidates the run itself suggested and did not attempt:
announcements read on `σ` rather than `ρ`, and a fourth walk paid for by the missing level. They
are the run's, recorded here so they are not lost; this commission neither adds to nor prescribes
them.

## 2. Questions, asked as questions

1. **Is every faithful pair a shaving of a thin one?** Shaving lowers `ρ j` to `σ j − 1` at a
   strict peak. Whether the reverse — raising `ρ j` to `σ j` at every non-thin link — always gives
   a faithful thin sequence, and whether a fold of the thin sequence transfers to the general one,
   is asked. If it does, `s3_span_nine_thin` is most of `s3_span_nine`; if it does not, the
   witness is worth having.
2. **Can the fold be of `σ` or of the interval?** `exists_blocks_first_of_folds` folds `ρ`. Whether
   a fold of `σ`, or a fold in which the window condition reads the whole link `[ρ j, σ j]`, also
   yields the block conclusion of Theorem 3 is a question about `Itinerary.lean`, and it decides
   whether the run's first candidate in §5 is available.
3. **Which walk, as a function of which announcements, on general pairs?** Both witnesses of
   batch 46 are served by walks of at most three legs; the census says every unserved general pair
   met so far is. What is missing is the rule. Whether that rule can be stated on links rather
   than on levels of `ρ` is the form of the question the counterexamples suggest.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. A census of whatever was explored, each stating that it ranges over the general model, with
   its generator named (shavings of `bing 0 N`, or otherwise), and the fraction of non-thin links.
3. Report: any counterexample first; then §1; then §2 1–3, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
