Commission: batch 70 — three statements about one crossing, on a wider corpus

Go! Runs on top of the batch-69 delivery. No new file is prescribed. This text is pasted into the prompt and is in the archive as COMMISSION-batch70.md; the report names it in its first line.

0. On batch 69

Audited: every earlier Lean file identical except a docstring in General.lean and two import lines; two new files, 30 theorems on standard axioms or subsets, no native_decide; the four sorrys are the four standing targets; census log present.

The refutation of §2.5 is in Lean: LandWalkPB (the landmark sentence with the batch-66 clause) and its sufficiency statements are false at the forty-time witness of check68.log whose shortest leg is four; the added clause is vacuous on the witness, and FoldsOnto is refuted by the kernel through foldsB_iff. The sentence stays, commented, with the refutation named. No replacement is asked for.

Results, all theorems:

Ceil72 on the running arm from the pairing read across the basepoint: under NearLowT (a time of the pair at L + 2 or below within 67 steps before the basepoint) every ascent of the forward arm to L + 9 has the clause's two landmarks as times of that arm, the valley at L + 3 seventy steps before the ascent (ceil72_of_nearLowT_armG, mirror). Neither Mid2Floor nor the partner's w3 clauses are used, and the high run plays no part.
The running arm's deep-floor clause from the same pairing where its floor descents follow the run (deep72_of_nearLowT_armG).
s3_span_nine_mid5_of_cross_highRun_nearLow_armG (mirror): a high-run crossing folds onto w72 given three hypotheses.

The census at the 87 high-run crossings: witness at L + 3, distance 70, peak at L + 6, nearest low time 56 to 65 steps before the basepoint — uniform. Report §4 records that all 87 are windows of one 986-link pair: one configuration seen 87 times.

What the branch at L + 5 owes is now three named statements about the two arms of one crossing:

NearLowT / NearLowG — the distance (87 of 87; 56 to 65 against a bound of 67);
the partner's deep-floor clause where the band reaches the floor (87 of 87; the wb clauses return L + 6 and six where Deep72 asks L + 7 and seven);
BothNineL5 empty — the partner stops below L + 9 (87 of 87, 461 of 461; the timing law gives nothing for two links at one level).
1. Targets
s3_span_nine_mid5 (Mixed.lean), then s3_span_nine through s3_span_nine'.
s3_general; if proved, close theorem3 by theorem3_of_S3.

A counterexample is a success and is reported first, after a definition audit. A refuted statement is kept, commented out, with the refutation named.

2. Questions, asked as questions
The corpus, before anything else. Report §4 says the 87 high-run crossings are one configuration. Before any of the three statements is attempted in Lean, the census is asked to widen the corpus of crossings and re-measure all three: other faithful pairs of span nine (bing 0 N for larger N; subchains at other offsets; the random and grid subchains of batch 29; shaved and filled pairs where the general model differs from the thin one), with the count of distinct configurations reported alongside the count of crossings. Whether the three statements survive, and what the observed range of the nearest low time becomes, is the first result of the batch. A crossing violating any of the three is a finding and is reported first, with a definition audit; if it is a counterexample to S3 at span nine it is a counterexample to theorem3.
The distance. Two steps of slack against a bound of 67 is thin. Is 67 the pairing's bound — the clause's spacings 70 and 29 and the index the peak must reach — or is it the bound of the reading chosen (the peak read at arm index three)? Reading the same pairing against a later low time, or against a different high time of the running arm, may carry a different bound; which readings are available and what bound each gives is asked. Separately: what forces a low time within reach of the basepoint at a crossing at all? The crossing clauses say the partner is not served by w8, w71, w72 and the w8 side is; whether the partner's failure of w8 puts a time at L + 2 or below within a bounded distance of the basepoint — and what the bound is — is the statement.
The partner's deep-floor clause. wb's ceiling clause returns L + 6 and six; Deep72 asks L + 7 and seven. The seam is the one batch 67 closed for w3/wb by reading the pairing against a link carrying L + 9 rather than a time at L + 8. Whether a reading of the pairing at the partner's floor descent against the running arm's L + 9 returns the missing level is asked; and whether the partner's clause is needed at all — that is, whether the assembly can fold the pair onto w72 with the partner's deep-floor clause replaced by something the partner already has — is asked alongside, since the batch-64 assembly took it from leg4Land_w72_of_cross_of_floor1 at descents of the reflected arm.
BothNineL5. Is it inhabited by any faithful pair, on the wider corpus of §2.1? If a crossing with both arms reaching L + 9 exists, which walk serves it, and does the batch-67 top-of-band pairing (crooked_peak_valley_high9) read between the two L + 9 times give anything? If none is found, the question of what excludes it stays open and is not assumed.
Assembly, if §2.2–2.4 close: s3_span_nine_mid5, then s3_span_nine; then the inventory of batch 69 §2.6 (which lemmas carry the span as a parameter), as a statement only.

No opinion is offered on the answers.

3. Deliverables
Whatever is proved, sorry-free, with #print axioms.
The widened census of §2.1, under the audit protocol, with the count of distinct configurations; censuses over arms alone say so and state their arm-length bound.
Report: first line names the commission read; any counterexample first; then §1; then §2 1–5.
4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not); a replacement sufficiency statement for the landmark sentence; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam.
