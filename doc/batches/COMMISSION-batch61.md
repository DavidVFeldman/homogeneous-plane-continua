# Commission: batch 61 — the crossing at `L + 5`

**Go!** Runs on top of the batch-60 delivery. No new file is prescribed.

## 0. On batch 60

Audited: every earlier Lean file identical except the docstring of `s3_span_nine_mid5`; two new
files; standard axioms, no `native_decide`; no refutation. **The arm-only half of exhaustiveness at
`L + 5` is a theorem**: every arm of the branch meets the exact criterion of one of three walks
(`leg4Land_tri`: `w8 = L+4 → L+8 → L+1 → L+8 → L+1`, `w3 = L+6 → L+3 → L+8 → L+1 → L+8`,
`wb = L+6 → L+3 → L+7 → L+1 → L+8`), and the branch is reduced to the crossings
(`s3_span_nine_mid5_of_leg4TriCrossL5`; with five walks, `s3_span_nine_mid5_of_leg4FiveCrossL5`).
The necessity half of the landmark sentence is now one theorem for a walk of any number of legs
(`foldsOnto_landmarkN`, subsuming the one-, two- and three-landmark forms).

The crossing is narrow and its shape is measured: of 1 745 960 basepoints, 371 are crossings of the
three walks and 38 of the five; the service sets that occur are `{w8}`, `{w3}`, `{wb}`, `{wb,w3}`,
`{w8,w3}`, all three — never `{wb,w8}` without `w3`, never empty. So a crossing is an arm of the
`{w8}` kind (it reaches `L + 8` before the landmark the shared ascent clause asks for) against an
arm of the `{w3}`, `{wb}` or `{wb,w3}` kind. This is the situation of batch 55 at `L + 4`: the
arm half proved, the crossing to be closed by the clause at the arms' own levels and `ivSep`.

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`), through `Leg4TriCrossL5` or `Leg4FiveCrossL5`.
2. `s3_span_nine` (`General.lean`).
3. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The crossing.** A `{w8}`-arm `X` climbs to `L + 8` without the earlier landmark; the other arm
   `Y` fails `w8`'s floor clause, so `Y` descends to `L + 2` with no earlier time at `L + 7` or
   above. Whether the clause read between `X`'s climb and `Y`'s descent, at their own levels, with
   `ivSep` placing what it returns, puts both arms onto one of the five walks — and if the argument
   stops, whether it stops at an index (batch 53's kind) or at the level read from below (batch
   57's kind) — is the branch. The 38 five-walk crossings of the corpus are the test set; which walk
   serves each of them is a census fact to have before the proof is attempted.
2. **Is five the list?** With a sixth walk the count did not fall. Whether the 38 are served by a
   common walk outside the window of the wide engine, or by five walks with a rule choosing among
   them, is asked; the necessity theorem now applies to any walk, so a candidate's criterion can be
   read off before its engine exists.
3. **The general engine, stated.** The report says the four-leg invariant is not special to four
   but needs the walk given as its list of turning levels. Whether that restatement — a walk as a
   list of levels, the landmark sentence as a conjunction over its legs, the invariant as two
   bounds per interior leg — is a theorem is asked; its statement alone, in Lean, would be a
   deliverable.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the audit protocol; censuses over arms alone say so.
3. Report: any counterexample first; then §1; then §2 1–3.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam.
