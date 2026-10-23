# Commission: batch 50 — three walks, the valley crossing, and a census protocol

**Go!** Runs on top of the batch-49 delivery. No new file is prescribed: the targets are the
`sorry`s of `HPC/Fold/Mixed.lean` and `HPC/Fold/General.lean` as they stand.

## 0. On batch 49

Audited: every earlier Lean file identical except `Mixed.lean` and the `General.lean` docstring;
standard axioms, no `native_decide`. Three statements refuted at one basepoint (`bing9sB`, 336) and
kept commented out with the refutations named; the same pair proved served by `w₄` in the kernel,
so span nine stands. The necessity half of the landmark sentence is a theorem for every walk
(`foldsOnto_landmark1`, `foldsOnto_landmark2`, discrete intermediate value theorem on `β`), and for
the third walk the criterion is now exact (`foldsOnto_leg3deep_iff_landmark`). `cross_valley_profile`
survives 73 495 tests; its case analysis is down to one case (`u ∈ {i − 3, i − 2}`), and the report
gives the structural reason the valley crossing behaves differently from the ceiling one: a link
meeting a low landmark gives `ρ ≤ l` outright, a link meeting a high one gives only `ρ ≥ l − 1`.

**The census read the branch hypothesis wrong, and this is the third time a census and a Lean
statement have not measured the same thing** (batch 42: a 512-entry buffer; batch 44: `CeilAnn`
for `HighAt f L (L + 8)`; batch 49: `L + 1` for `L + 2`). Each time the run found its own error, and
each time a refutation was hidden behind it. From this batch on:

> **Definition audit.** Every predicate a census evaluates that has a Lean definition
> (`HighAt`, `LowAt`, `Leg3Valley`, `Leg3Ceil`, `Leg3Land`, `FoldsOnto`, `IsCrookedIvF`, …) is
> checked against that definition on a sample of the census's own objects by kernel evaluation in
> Lean — the way `Bing9Witness.lean` and `CrossServed.lean` already decide facts about arms — and
> the report says which predicates were audited and on how many objects. A census whose predicates
> are not audited is reported as unaudited.

## 1. Targets

1. `unserved_three_walks` (`Mixed.lean`). With it `s3_span_nine_mid4` is complete.
2. `cross_valley_profile`, if it is still on the route after 1.
3. `s3_span_nine_mid5`.
4. `s3_span_nine`, `s3_general`; if `s3_general` is proved, close `theorem3` by `theorem3_of_S3`.

A counterexample to any of these is a success and is reported first, after a definition audit of
the predicates that found it.

## 2. Questions, asked as questions

1. **Why three walks?** Each of `w₃`, `w₄`, `w₅` now has an exact landmark criterion, or can be
   given one by `Landmark.lean`. Whether an unserved pair of the branch meets one of the three is
   then a statement about crookedness and three explicit sentences. Whether that statement has a
   proof, or a fourth walk is needed, or the set of walks depends on the pair in a way no finite
   list captures, is asked. The report's numbers (`w₅` alone serves 90 764 of 98 611) are recorded.
2. **The last case of `cross_valley_profile`.** The report leaves `Y` dipping to `L + 2` at its step
   two or three and not again before its ascent. Whether that case is closed by a second
   application of the clause in the general model, or a general pair realises it and folds anyway
   (so the V-criterion's index clause is the wrong instrument), or a general pair realises it and
   does not fold onto the V-walk but folds onto one of the three walks (so the item is false but
   the branch survives), is asked.
3. **Sufficiency of the landmark sentence for an arbitrary walk.** Necessity is done. The run says
   the batch-48 invariants with a walk's landmark positions as constants are the shape of the
   general engine. Whether that is a theorem is asked, as before; if it is, the branch at any span
   is a statement about crookedness and a finite list of sentences, and question 1 is its instance.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model, generators named, fraction of non-thin links stated, with the
   definition audit of §0; censuses over arms alone say so.
3. Report: any counterexample first; then §1 in order; then §2 1–3, negative answers included.

## 4. Not in this batch

Spans ten and above one at a time; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the
linear-time far-index check.
