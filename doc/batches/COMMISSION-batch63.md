# Commission: batch 63 — the last clauses of the crossing

**Go!** Runs on top of the batch-62 delivery. No new file is prescribed.

## 0. On batch 62

Audited: every earlier Lean file identical; two new files; standard axioms, no `native_decide`;
no refutation. The crossing's owed clauses are now read off the pairing itself
(`cross_peak_valley_core`: one application of the clause between the partner's descent and the
`w8` side's ascent, spaced by `ivSep` at 70, 29, 70; `cross_peak_valley_armG`: both witnesses lie
on the `w8` side). The index side is never the obstruction — every gap the sentence asks is bought
by the timing law with an order of magnitude to spare — and the argument stops at **one level**:
the valley the pairing returns sits at `ρ a + 1`, one above the partner's descent.

Two clean consequences: against `w71` the `w8` side owes only a valley at `L + 1`
(`leg4Land_w71_of_w8_of_low1`); against `w72 = L+4 → L+7 → L+2 → L+8 → L+1`, whose ceiling valley
sits exactly where the pairing puts it, the `w8` side satisfies the whole criterion as soon as it
stays at `L + 1` or above (`leg4Land_w72_of_cross_of_floor1`). The corpus (461 distinct crossings):
the partner satisfies `w71` at all 461 and `w72` at 431; the `w8` side satisfies `w72` at 451; both
arms satisfy `w72` at 421. Every crossing is extremal for the timing law (`dT + dG = 70`), but the
extremal window takes 121 distinct shapes, so the proof has a family, not one case.

`LandWalkSuff.lean` states the general sufficiency (`LandWalkSuffices`, with the greedy
`gseqWalk` for any walk and the two-bounds-per-leg invariant `WalkInvLand`) and proves the greedy
folds whenever it stays legal; the induction itself is the missing half.

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`), through `Leg4SixCrossL5` or `Leg4QuadCrossL5`.
2. `s3_span_nine` (`General.lean`).
3. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The `w8` side that touches `L`.** At 179 of 461 crossings the `w8` side reaches the floor, so
   `w72`'s deep-floor clause fires. Which walk serves those crossings, and whether the pairing —
   the same application, or one more between the `w8` side's own time at `L` and something on the
   partner — supplies that walk's clauses, is asked. If it is `w81 = L+5 → L+8 → L+1 → L+8 → L+1`,
   its exact criterion is one more instance of `foldsOnto_leg4_iff_leg4Land`.
2. **The partner's 30.** The partner satisfies `w71` always and `w72` at 431 of 461. Which clause
   of `w72` fails at the other 30, and whether at those the `w8` side satisfies `w71` (so the pair is
   served by `w71`), is asked; the census has the crossings stored whole.
3. **The two-index slack.** `cross_peak_valley_armG` needs the partner to have no peak at `L + 7` or
   above at arm index two or three before its descent; the crossing hypothesis gives it from index
   four. At 83 crossings the slack occurs. Whether a partner peak at index two or three is excluded
   by the timing law from the basepoint (three levels in two steps), or handled by reading the
   clause from that peak instead, is asked.
4. **`LandWalkSuffices`.** The induction of `gseq4_invLand` carried over `walkList s ts` against
   `WalkInvLand`. This is the general engine; with it every walk of every span has an exact
   criterion.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the audit protocol; censuses over arms alone say so.
3. Report: any counterexample first; then §1; then §2 1–4.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam.
