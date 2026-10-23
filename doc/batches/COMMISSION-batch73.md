Commission: batch 73 — the w8-failing descent, read against the ascent

Go! Runs on top of the batch-72 delivery. No new file is prescribed. This text is pasted into the prompt and is in the archive as COMMISSION-batch73.md; the report names it in its first line.

0. On batch 72

Audited: every earlier Lean file identical except two import lines; two new files, 23 theorems on standard axioms or subsets, kernel-checked witness, no native_decide; the four sorrys are the four standing targets; census, construction, minimiser, re-check and witnesses present.

The counterexample: Valley3BeforeNine (equivalently Ceil72) on a running arm is false without the crossing — a 78-link thin window of bpath 0 9, kernel-checked; 194 076 failures on the corpus, none at a crossing; a walk of the family serves every one. Recorded fact: the statement needs the crossing, and what the crossing supplies is now known — the running arm is a w8 arm (leg4Land_w8_of_run), so the crossing takes w8 off the partner.

Results, all theorems: not_bothHighRun_of_cross (at most one arm runs high at a crossing); ceil72_partner_of_cross_highRunG (the partner's clause, in general); s3_span_nine_mid5_of_cross_highRun_ceilRun_armG (+ mirror): a high-run crossing folds given Ceil72 on the running arm alone; run_peak_armG (the peak is free; only the valley remains); crooked_mid5_low2; partnerLow_of_cross_highRunG and partnerLow_sep_of_cross_highRunG.

Construction: no edit of 55 829 produced a crossing whose running arm fails the valley; cut is never faithful; no edit ever took w8 off the partner.

What the branch at L + 5 owes: Ceil72 on the running arm of a high-run crossing.

1. Targets
s3_span_nine_mid5 (Mixed.lean), then s3_span_nine through s3_span_nine'.
s3_general; if proved, close theorem3 by theorem3_of_S3.

A counterexample is a success and is reported first, after a definition audit. A refuted statement is kept, commented out, with the refutation named.

2. Questions, asked as questions
Does the w8-failing descent, rather than the nearest low time, place the valley? This is a question about three theorems already in the repository, checked here against their Lean statements and not against the reports; it may miss a clause, and that is what the question is for.
w8_floor_fail_of_not_w8 (Ceil68.lean), applied to the partner armT ρ i — which fails w8 at a high-run crossing because the running arm is a w8 arm (leg4Land_w8_armG_of_highRun) and TriCrossL5's first clause forbids both — returns a partner descent d₀ with armT d₀ ≤ L + 2 and: for every partner index j with 4 ≤ j and j + (L + 7 − armT d₀) ≤ d₀, armT j < L + 7. This is what partnerLow_of_cross_highRunG is built from; the report used only the existence of d₀.
crooked_peak_valley_high9_mid (Ceil68.lean) between a := the chain index of d₀ (a < i) and b := the running arm's link at any ascent to L + 9 (ρ b ≤ L + 9 ≤ σ b, i < b) returns r, r' with a + 70 ≤ r, r + 29 ≤ r', r' + 70 ≤ b, L + 7 ≤ ρ r, L + 8 ≤ σ r, ρ r' ≤ ρ a + 1 ≤ L + 3.
Where is r? If r < i, it is a partner time at index j = i − r with armT j = ρ r ≥ L + 7; armT_index_of_sig8 (Mid2Index67.lean, L + 8 ≤ σ r) gives j ≥ 5 ≥ 4; and j + (L + 7 − armT d₀) ≤ d₀ reads a + (L + 7 − ρ a) ≤ r, true since L + 7 − ρ a ≤ 7 ≤ 70. So the w8-failure clause gives ρ r < L + 7: contradiction. If r = i, ρ i = L + 5 < L + 7: contradiction. So i < r, and r is a running-arm time at index ≥ 5 (armG_index_of_sig8), with r' a running-arm time after it.
Ceil72 (armG ρ i) L asks, at every d with armG d ≥ L + 9: j ≥ 3 with armG j ≥ L + 6, k ≥ j + 5 with armG k ≤ L + 3, k + (armG d − (L + 3)) ≤ d. With j := r − i ≥ 5, k := r' − i ≥ j + 29, and k + 70 ≤ d, where armG d − (L + 3) = 6: all met.
If this is right, Ceil72 holds on the running arm at every high-run crossing with no distance hypothesis, and s3_span_nine_mid5_of_cross_highRun_ceilRun_armG (with its mirror) closes the high-run crossings. Batch 69 read the pairing from the nearest low time, which may have a partner high before it; the descent w8's failure returns is the one that does not, and that is the only difference. If it is wrong, the report names the clause that fails and, if possible, a pair at which the reading's conclusion is false.
Assembly. If §2.1 holds: s3_span_nine_mid5 from the non-crossings (s3_span_nine_mid5_of_leg4Land_refl / _direct), the crossings with both arms DeepFirst2 (s3_span_nine_mid5_of_cross_deepFirst2), and the high-run crossings (§2.1, both orientations; not_bothHighRun_of_cross says these are exhaustive with the previous case at a crossing — confirm). Then s3_span_nine from s3_span_nine'. Both are targets of this batch.
The inventory (batch 69 §2.6), due once s3_span_nine is a theorem: which lemmas in its proof carry the span as a parameter and which are stated for nine alone (fixed offsets L + k, the six walk names, the level L + 5). A statement only; no proof about other spans is asked.
If §2.1 fails: the census question of batch 72 §2.2 restricted to the w8-failing descent — at each of the 229 and at batch 71's 2229, where the pairing from d₀ puts its peak and valley — decides whether the reading is wrong in general or only in some clause.

No opinion is offered beyond what §2.1 states, and §2.1 is a question.

3. Deliverables
Whatever is proved, sorry-free, with #print axioms.
Censuses under the audit protocol where asked; censuses over arms alone say so and state their arm-length bound.
Report: first line names the commission read; any counterexample first; then §1; then §2 1–4.
4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not); a replacement sufficiency statement for the landmark sentence; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam.
