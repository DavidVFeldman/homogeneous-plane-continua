# Commission: batch 49 — the crossing, the mirror, and the general engine

**Go!** Runs on top of the batch-48 delivery. No new file is prescribed: the targets are the
`sorry`s of `HPC/Fold/Mixed.lean` and `HPC/Fold/General.lean` as they stand. Root `HPC.lean`
unchanged unless the run adds a file of its own.

## 0. On batch 48

Audited: every earlier Lean file identical except `Leg3Profile.lean`, `Mixed.lean` and the
`General.lean` docstring; standard axioms, no `native_decide`; no counterexample.
`foldsOnto_leg3deep_profile` is a theorem, proved by four numerical invariants on the greedy time
(clock, `R`, slack clock, `S`) in place of the engine's history features, and with two of the four
index bounds unused (`foldsOnto_leg3deep_profile_min`). `leg3Valley_or_vee`, `leg3Ceil_or_lam` and
`unserved_profile_one` put the arm-only half of the branch away. What remains of the branch
`L + 4` is the crossing alone: `cross_valley_profile` and `cross_ceil_profile`.

Two facts from the report that this commission fixes as the frame:

* Reflection does not carry the branch `L + 4` to the branch `L + 5` in the general model, for two
  reasons the report states exactly (the reflected point sequence is `a − σ`, so a non-thin
  basepoint leaves the branch, and a fold of `a − σ` is a window-two statement about `a − ρ`,
  `exists_blocks_first_of_folds_max`). The branch `L + 5` needs its own argument.
* The landmark sentence of REPORT-batch48.md §2.3, tested on 54 zigzag walks and 113 019 462
  arms, is met by an arm exactly when the arm folds — not sufficient only, but equivalent, on that
  corpus. Nothing proves it.

## 1. Targets

1. `cross_valley_profile`, `cross_ceil_profile` (`Mixed.lean`). With them `s3_span_nine_mid4` is
   complete.
2. `s3_span_nine_mid5`.
3. `s3_span_nine`, `s3_general`; if `s3_general` is proved, close `theorem3` by `theorem3_of_S3`.

A counterexample to any of these is a success and is reported first. A refuted statement is kept,
commented out, with the refutation named.

## 2. Questions, asked as questions

1. **Is `cross_ceil_profile` vacuous on actual pairs?** No arm of any census fails `Leg3Ceil`. If
   an arm of a faithful pair of the branch cannot fail it — a statement about one arm and
   crookedness, of the kind `leg3Ceil_or_lam` already half makes — then `cross_ceil_profile` is a
   corollary and the crossing is one statement, not two. Whether that is so, or a failing arm can be
   constructed (shaving, filling, or a chain other than Bing's), is asked.
2. **The one index of `cross_valley_profile`.** The report says exactly what the clause across the
   basepoint delivers and what it does not: a low time of the other arm, but possibly at index two
   or three where the V-criterion wants four or later. Whether the timing laws across the basepoint
   (`seq_gap`, `cross_gap_ge`, `mix_events_far`) close that gap, or a second application of the
   clause does, or a pair exists with the low time at index two or three that nonetheless folds
   (so the V-criterion's index clause is the wrong instrument there), is asked.
3. **The general engine.** The landmark sentence of §2.3 is the run's own, and the run says its
   §1.1 proof is written so that it could become the general one. Whether the sentence, for an
   arbitrary zigzag walk, is a theorem about 1-Lipschitz arms — as a sufficient condition first,
   and as a characterisation if the proof gives it — is asked. If it is, every arm-only half of
   every branch at every span has one proof, and what varies with the span is the crossing alone.
   The run states the theorem in its own terms; this commission does not.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. A census of whatever was explored, over the general model, generators named (shaving, filling,
   mixtures, other chains), fraction of non-thin links stated; censuses over arms alone say so.
3. Report: any counterexample first; then §1 in order; then §2 1–3, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
