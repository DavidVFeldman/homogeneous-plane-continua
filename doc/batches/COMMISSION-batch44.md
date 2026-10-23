# Commission: batch 44 — the two branches at span nine, ends attained

**Go!** Runs on top of the batch-43 delivery. One new file, `HPC/Fold/Mixed.lean`; root
`HPC.lean` updated. Nothing else touched.

## 0. On batch 43

Audited: every earlier Lean file identical except the docstring of `General.lean`; live `sorry`s
are `theorem3` and the two targets of `General.lean`. All three commissioned targets of
`Timing.lean` proved, with `z_mono` and the three-level corollaries. The mixed configuration is
inhabited — 55 of the 182 branch basepoints of `bing 0 9`, and a Lean witness at basepoint 138 of
`ceSeq` — so batch 42's "mixed: 0" was a buffer limit, found and named by the run itself. That
correction is the most useful thing in the batch. Noted and agreed: the Lean witness lives in a
span-eight chain read in a nine-wide band, so it is served by `s3_span_eight`; what it refutes is
the two-walk method, not a case of the theorem.

Record of the corpus, as the report states it: every sequence verified against `IsCrookedIvF` in
its thin form `σ = ρ`. That is a subclass of the faithful model; the pairs counted are actual, and
the class of all actual pairs is larger.

## 1. Targets

`s3_span_nine_mid4` and `s3_span_nine_mid5` in `Mixed.lean` — the hypotheses `key4` and `key5` of
`s3_span_nine_of_mid`, verbatim, so that `s3_span_nine'` follows by that theorem and is written
out already. Then `s3_span_nine` and `s3_general` in `General.lean` as before; if `s3_general` is
proved, close `theorem3` by `theorem3_of_S3`. A counterexample is a success and is reported first.

The report's own account of what is missing — an exact criterion for `w4` in the style of
`Profile.lean`, a rule choosing among three walks — is in the file's docstring. This commission
adds nothing to it and does not prescribe it.

## 2. Questions, asked as questions

1. **Are three walks enough on actual pairs?** "No arm fails both criteria" and "the four-leg walk
   serves every mixed pair" are both checked on the corpus and neither is proved. Either could
   fail on an actual pair outside the corpus, and either failure is a fact worth a theorem.
2. **Does the thin form `σ = ρ` lose anything?** The census verifies crookedness with `σ = ρ`. Is
   every pair of the faithful model an arm-pair of some thin sequence, or is there an actual pair
   with `σ = ρ + 1` somewhere that no thin sequence produces? If the second, the census is a
   census of a subclass and the report should say so.
3. **Is the count of walks per branch a function of the span?** Span eight needed four walks at
   the middle basepoint, span nine three at each of two heights (if §2.1 holds). Whether that
   count, and the shapes, follow from the leaf and the profile criteria without a search is the
   question that decides whether span-by-span ends.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. A census of whatever was explored, each saying whether it ranges over thin sequences, the
   faithful model, or a one-arm class.
3. Report: any counterexample first; then §2 1–3 in order, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
