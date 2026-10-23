# Commission: batch 45 — the two statements across the basepoint

**Go!** Runs on top of the batch-44 delivery. No new file: the targets are the three `sorry`s of
`HPC/Fold/Mixed.lean` as they stand. Root `HPC.lean` unchanged.

## 0. On batch 44

Audited: every earlier Lean file identical; live `sorry`s are `theorem3`, the two targets of
`General.lean`, and in `Mixed.lean` the work items `unserved_high8`, `unserved_valley` and the
branch `s3_span_nine_mid5`. Everything else proved, standard axioms.

What the batch settled: the third walk is `leg3Walk L (L+9) (L+6) (L+4)`, one parameter value
past the engine of batch 38, and `Leg3Deep.lean` drives it. `arm_lam_or_vee` turns batch 43's
checked "no arm fails both criteria" into a theorem for arbitrary integer sequences. `valley_or_vee`
and `high8_or_lam` reduce each work item to a statement about the *other* arm. `mix_events_far`
reads `minGap` across the basepoint: the two events of a mixed pair sit at least 70 steps apart.
And the census refuted the first form of the work items (conditioned on the mixed configuration
alone) before it was proved — recorded here as the batch's own check working as intended.

## 1. Targets

1. `unserved_high8`, `unserved_valley` in `Mixed.lean`, as stated. With them `s3_span_nine_mid4`
   is complete.
2. `s3_span_nine_mid5`.
3. Then `s3_span_nine`, `s3_general` in `General.lean`; if `s3_general` is proved, close
   `theorem3` by `theorem3_of_S3`.

A counterexample to any of these is a success and is reported first. If a work item is false on
an actual pair, the pair is exhibited and the branch is re-split; the report says which.

## 2. Questions, asked as questions

1. **Is `s3_span_nine_mid5` the reflection of `s3_span_nine_mid4`?** Batch 41 recorded that the
   two heights are not mirror images: `HighAt` has one clause and `LowAt` two, so reflecting an arm
   does not carry one branch condition to the other. Whether the three walks at `L + 5` are the
   reflections of the three at `L + 4`, and whether the same two statements across the basepoint
   suffice there, is asked and not assumed.
2. **What do the two work items say about the pair, in the language of `mix_events_far`?** Each
   is a statement across the basepoint; the repository now has one tool for those. Whether the
   items follow from timing alone, or need the crookedness clause across the basepoint as
   `no_arm_split_high_low` did, is a fact about the proof worth recording either way.
3. **Standing question from batch 44:** does the thin form `σ = ρ` lose pairs? Unchanged, not
   settled, not urgent; the Lean material does not depend on it.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. A census of whatever was explored, each saying whether it ranges over thin sequences, the
   faithful model, or a one-arm class.
3. Report: any counterexample first; then §1 in order; then §2 1–3, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
