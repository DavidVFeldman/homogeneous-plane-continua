# Commission: batch 52 — the crossing argument

**Go!** Runs on top of the batch-51 delivery. No new file is prescribed: the targets are the
`sorry`s of `HPC/Fold/Mixed.lean` and `HPC/Fold/General.lean` as they stand.

## 0. On batch 51

Audited: every earlier Lean file identical except `Mixed.lean`; five new files; standard axioms,
no `native_decide`; nothing refuted, no target proved. All three walks of the branch now have exact
criteria (`foldsOnto_leg3deep_iff_landmark`, `foldsOnto_w4_iff_landmark`,
`foldsOnto_w5_iff_landmark`), the engines are parametrised by peak, trough, start window and two
index constants, and `three_walks_iff_sentence` restates the work item with no `FoldsOnto` in it.
`unserved_three_walks_or_cross` says the item is entirely a statement across the basepoint. The
relaxed clause does not name a walk (`relaxed_serves_no_walk`). The arms-only census found the
missing clause `MidW4` before it reached Lean; the definition audit covers 14 predicates on 13 arms.

The state of the branch `L + 4`, as the record now has it: every pair either folds onto `w₃`
outright, or has an arm failing `Valley4` or `Leg3Ceil`, which arm then folds onto a canonical walk
by itself. What is unproved is only what the *other* arm does then. In the valley case that is
`cross_valley_profile`, proved off `ValleyResidual`. In the ceiling case the analogous cross item
was refuted (batch 49) and the pair is served by `w₄` or `w₅` instead.

## 1. Targets

1. `unserved_three_walks` (`Mixed.lean`), in its sentence form.
2. `cross_valley_profile`.
3. `s3_span_nine_mid5`.
4. `s3_span_nine`, `s3_general`; if `s3_general` is proved, close `theorem3` by `theorem3_of_S3`.

A counterexample to any of these is a success and is reported first, after a definition audit of
the predicates that found it. A refuted statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The ceiling case as a crossing.** When an arm `X` fails `Leg3Ceil` (so `X` folds onto Λ), the
   censuses say the pair folds onto `w₄` or `w₅`. Each of those is now an exact sentence about the
   two arms. Whether the failure of `Leg3Ceil` on `X`, the failure of Λ on the other arm `Y`, and
   the crookedness clause across the basepoint together give `MidW4 ∧ BottomW4` on both arms, or
   `Valley5 ∧ TopW5` on both, is the ceiling half of the item, and it is asked in that form — as
   the valley half was asked in batch 49 and answered by `CrossValley.lean` off one configuration.
2. **`ValleyResidual` as a pair**, unchanged: realise it with a failing arm and an other arm
   missing the V-walk, or exclude it.
3. **The branch `L + 5` at the level of arms.** The engines are statements about 1-Lipschitz arms
   with parameters, and reflecting an *arm* `f ↦ 2L + 9 − f` needs no symmetry of the model. Whether
   the arm-only half of the branch `L + 5` (criteria, `_or_lam`/`_or_vee` lemmas, the three-walk
   sentence) is the reflection of the branch `L + 4`'s, leaving only the crossing statements to be
   argued separately, is asked. If so, the two branches share everything but the crossings.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model, generators named, fraction of non-thin links stated, with the
   definition audit; censuses over arms alone say so.
3. Report: any counterexample first; then §1 in order; then §2 1–3, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
