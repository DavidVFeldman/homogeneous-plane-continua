Commission: batch 71 — the distance

Go! Runs on top of the batch-70 delivery. No new file is prescribed. This text is pasted into the prompt and is in the archive as COMMISSION-batch71.md; the report names it in its first line.

0. On batch 70

Audited: every earlier Lean file identical except two import lines; two new files, thirty theorems on standard axioms or subsets, no native_decide; the four sorrys are the four standing targets; widened census, independent re-check and stored witness present.

The finding: BothNineL5 is inhabited (39 of 229 high-run crossings on the widened corpus; witness a 2378-link window of bing 0 10, re-checked from literal definitions). The assembly hypothesis of batches 68–69 was not innocuous. It is not a counterexample to S3: w72 serves both arms at all 39. Recorded fact: the corpus of batches 68–69 was one configuration, and a hypothesis that held on it did not survive widening. The widening rule stands: a statement measured on the corpus is re-measured on a wider corpus before it is assumed.

Results, all theorems:

Both deep-floor clauses at a high-run crossing (Deep70.lean): the running arm's from the pairing read inside the arm from its ascent to its floor descent; the partner's from the pairing read at the partner's floor descent against the running arm's link carrying L + 9 — the level wb missed — with the high run forcing the valley before the basepoint and crossMid2 supplying the third landmark.
The symmetric assembly s3_span_nine_mid5_of_cross_ceil_deep: at a crossing, both arms with Deep72 and Ceil72 fold onto w72; no w8 side, no BothNineL5, no partner clause.
The distance bound is the reading's, set by the low time's level: L + 2 or below within 67, L + 1 or below within 166, the floor within 405 (NearLowBandT); any of the three gives Ceil72 on the running arm.

The census (7040 faithful pairs, 2 444 297 basepoints of the branch, 1351 crossings, 229 high-run crossings in 52 configurations): the nearest time at L + 2 or below before the basepoint is 56 to 65 steps away at every one of the 229 — the same range as batch 69's single configuration; the L + 1 and floor readings never fire (295 to 642; 872 to 2035). The partner's Ceil72 is vacuous where it stops below L + 9 (190) and follows from DeepFirst2 at all 39 where it does not.

What the branch at L + 5 owes is one statement: at a high-run crossing, a time of the pair at L + 2 or below within 67 steps before the basepoint (NearLowBandT / NearLowBandG). Nothing proved bounds it: w8_floor_fail_of_not_w8 gives the partner a low descent with no index bound.

1. Targets
s3_span_nine_mid5 (Mixed.lean), then s3_span_nine through s3_span_nine'.
s3_general; if proved, close theorem3 by theorem3_of_S3.

A counterexample is a success and is reported first, after a definition audit. A refuted statement is kept, commented out, with the refutation named.

2. Questions, asked as questions
The anatomy of the nearest low time. At each of the 229 (and per configuration): which arm it is a time of; its exact level (L + 2, or lower); its arm index; the level profile of the pair between it and the basepoint; and whether it is itself the valley or peak of some crookedness reading — read from which two links (the basepoint's own link? the running arm's ascent? a partner time at L + 7 or above?). Batch 55's far-witness table is the model. The question is what produces this time, since nothing proved does.
The constancy. The range 56 to 65 did not move when the corpus grew thirty-fold and the configurations went from one to 52. Is 56–65 expressible in the timing law — a difference or sum of z-values and small offsets — and does the value at a given crossing depend on a parameter the census can name (the index of the running arm's ascent, the partner's descent to L + 2, the level of the basepoint's link)? A formula that fits all 229 is a conjecture to record, not a theorem; whether it is the shadow of an ivSep-type statement across the basepoint is the question.
A reading of Ceil72's peak not through a low time. The binding constraint is the peak at arm index three or more, at L + 6 or above, with the valley at L + 3 or below five steps later, both before the ascent. The running arm satisfies Mid2Floor (crossMid2), fails DeepFirst2, and is served by w8; the partner is a w3 arm and a wb arm (cross_partner_w3_of_highRun). Whether any of these, or the pairing read from the running arm's ascent against a high time of the partner (L + 7 or above — the partner's w3 ceiling clause gives one before each of its descents to L + 1), returns the two landmarks on the running arm without a near low time, is asked. If no reading does, say which landmark each reading fails to place.
Break it. The corpus never leaves 56–65. The strongest test of the distance statement is a targeted construction: a faithful pair (in the general model, shaving and filling allowed) with a high-run crossing whose nearest time at L + 2 or below is more than 67 steps before the basepoint. Search by construction rather than by sampling — starting from a stored high-run crossing and lengthening the partner's approach to the basepoint while preserving faithfulness, or by any other means. A success is a refutation of NearLowBandT as a residue and is reported first; whether the pair still folds (which it must if S3 holds) is then the next question. A failure to construct one, with the obstruction named, is evidence of a different kind from sampling.
Both arms running high. At all 39 both-nine crossings the partner is DeepFirst2. Is it a theorem at a crossing that the two arms cannot both run high — the partner reaching L + 9 before any time at L + 2 or below while the running arm does the same? If it is, the assembly's partner clause is discharged in general (vacuous or ceil72_of_deepFirst2); if it is not, BothHighRunL5 is a named case and the census says whether it is inhabited.
Assembly, if §2.1–2.4 close the distance: s3_span_nine_mid5, then s3_span_nine; then the inventory of batch 69 §2.6.

No opinion is offered on the answers.

3. Deliverables
Whatever is proved, sorry-free, with #print axioms.
The table of §2.1 and the construction attempt of §2.4, under the audit protocol; censuses over arms alone say so and state their arm-length bound.
Report: first line names the commission read; any counterexample first; then §1; then §2 1–6.
4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not); a replacement sufficiency statement for the landmark sentence; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam.
