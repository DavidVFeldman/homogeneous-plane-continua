# Commission: batch 48 — the two halves of the branch at `L + 4`

**Go!** Runs on top of the batch-47 delivery. No new file: the targets are the `sorry`s of
`HPC/Fold/Leg3Profile.lean`, `HPC/Fold/Mixed.lean` and `HPC/Fold/General.lean` as they stand. Root
`HPC.lean` unchanged.

## 0. On batch 47

Audited: every earlier Lean file identical except `Mixed.lean` and the `General.lean` docstring;
standard axioms, no `native_decide`. Both negative answers are theorems rather than checks:
the raise of a faithful pair need not be faithful (`exists_faithful_not_isShavingOfThin`, with a
six-link least witness and an exhaustive census behind it), and a fold of `σ` yields the block
conclusion with four links, not three (`exists_blocks_first_of_folds_max`). The general model is
reflection-symmetric (`isCrookedIvF_reflect_general`), which also gives the second generator,
filling (`isCrookedIvF_fill`). The lowering `(ρ, ρ)` of a shaved pair is never faithful (288 of
288), so the general model's point sequences lie outside the thin model in both directions.

The branch `L + 4` now rests on two statements of different kinds, and the split is clean:

* `foldsOnto_leg3deep_profile` — arms alone, no crookedness, no pairs. The criterion
  `Leg3Valley ∧ Leg3Ceil` is the engine's, with the peak demand lowered from `L + 6` to `L + 5` and
  paid for by index clauses tied to the walk's three landmarks. Checked sufficient on every
  1-Lipschitz arm of length ≤ 16 and two million random longer ones; not necessary (59 982
  folding arms of length 16 fail it), which is fine.
* `unserved_profile` — where crookedness enters: an unserved pair of the branch meets the
  criterion on both arms. Checked on all 6 340 unserved basepoints of the shaved corpus.

The answer to batch 47's question 2.3 is recorded: the walk is `L+3 → L+6 → L+1 → L+8` on every
unserved pair of every general census so far, and the criterion above is what stands in for the
announcements.

## 1. Targets

1. `foldsOnto_leg3deep_profile` (`Leg3Profile.lean`).
2. `unserved_profile` (`Mixed.lean`). With both, `s3_span_nine_mid4` is complete.
3. `s3_span_nine_mid5`.
4. `s3_span_nine`, `s3_general`; if `s3_general` is proved, close `theorem3` by `theorem3_of_S3`.

A counterexample to any of these is a success and is reported first. A refuted statement is kept,
commented out, with the refutation named.

REPORT-batch47.md §5 records the run's own view of the two halves: `Profile.lean` as the model
for the first, `MixedThin.lean` one level lower as the model for the second, with
`census-batch47c.c` as the instrument for testing any variant of the criterion before it is
attempted. Recorded so it is not lost; not prescribed.

## 2. Questions, asked as questions

1. **Does the criterion survive the proof?** If `foldsOnto_leg3deep_profile` needs its clauses
   adjusted, the adjusted criterion is re-checked against `census-batch47c.c` and against the
   6 340 unserved pairs before `unserved_profile` is attempted with it.
2. **Is `s3_span_nine_mid5` the reflection of `s3_span_nine_mid4` in the general model?**
   `isCrookedIvF_reflect_general` reflects `(ρ, σ)` to `(a − σ, a − ρ)`, so the reflected point
   sequence is `a − σ`, not `a − ρ`. Whether the branch at `L + 5` follows from the branch at
   `L + 4` by that reflection together with `isCrookedIvF_sig_isLip`, or needs its own argument, is
   asked.
3. **The general form.** The Λ-criterion (`Profile.lean`) and the three-leg criterion
   (`Leg3Profile.lean`) both read: at each landmark of the walk, the arm has stood within one of
   the landmark's level at a step no earlier than the landmark's position, in order. Whether that
   sentence, for an arbitrary zigzag walk, is a sufficient condition for `FoldsOnto` is asked as a
   question about arms alone; if it is, the crookedness half of every branch has one shape.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. A census of whatever was explored, over the general model, generator named, fraction of
   non-thin links stated; censuses over arms alone say so.
3. Report: any counterexample first; then §1 in order; then §2 1–3, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
