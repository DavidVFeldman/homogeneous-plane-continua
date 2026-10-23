Commission: batch 72 — the valley at L + 3

Go! Runs on top of the batch-71 delivery. No new file is prescribed. This text is pasted into the prompt and is in the archive as COMMISSION-batch72.md; the report names it in its first line.

0. On batch 71

Audited: every earlier Lean file identical except two import lines; two new files, 21 theorems on standard axioms or subsets, fifteen facts by decide +kernel, no native_decide; the four sorrys are the four standing targets; census, construction, minimiser, independent re-check and both witnesses present.

The counterexample: the distance (NearLowBandT/G, all three readings) is false at a high-run crossing — a 290-link faithful pair, kernel-checked including faithfulness, nearest low time 185 steps from the basepoint against 67, no L + 1 or floor time at all. Not a counterexample to S3: Ceil72 and w72 hold on both arms there and at all 2229 broken crossings of the construction. The batch-69/70 assemblies stand as conditional theorems whose hypothesis is not always met. Recorded fact: the construction that breaks the distance is the one that adds no new level pattern — a stretch of the approach at L + 3 or above, reflected and re-appended; the edits that add a pattern (raising a low, splicing a whole sub-band block) are what crookedness kills.

Results, all theorems:

Ceil72 on an arm of the band is equivalent to one landmark pair before the arm's first ascent (Valley3BeforeNine); on a running arm the valley is at exactly L + 3 (valley_eq_three_of_run).
low_nine_sep: a time at L + 2 or below and a link carrying L + 9 are at least 169 steps apart; read across the basepoint, δ + e ≥ 169. The corpus attains equality at 228 of 229 — the whole of the 56–65 constancy — which is a conjecture about Bing's chains, not a theorem.
The distance descends: L + 1 within 306 gives L + 2 within 67; the floor within 883 gives L + 1 within 306. Constants tight; hypotheses not always met.
w8_of_cross_of_bothHighRun: at a crossing where both arms run high, one is a w8 arm.

Census facts: the nearest low time at the 229 is always the partner's, at exactly L + 2, and at 190 of 229 it is the valley of crooked_peak_valley_high9 read from an L + 1 link 295–304 steps before the basepoint to the running arm's ascent. Valley3BeforeNine has never been seen to fail: 229 crossings, 2229 broken crossings, every basepoint measured. At the counterexample its valley is named by a descending pairing from a link carrying L + 5, 36 steps before the basepoint on the running arm's side, to the far L + 2 time (span 221) — a reading with the right level and no index bound.

What the branch at L + 5 owes: Valley3BeforeNine on the running arm of a high-run crossing.

1. Targets
s3_span_nine_mid5 (Mixed.lean), then s3_span_nine through s3_span_nine'.
s3_general; if proved, close theorem3 by theorem3_of_S3.

A counterexample is a success and is reported first, after a definition audit. A refuted statement is kept, commented out, with the refutation named.

2. Questions, asked as questions
Is it a crossing fact at all? Valley3BeforeNine on a running arm has not failed anywhere it was measured. Census first, under the audit protocol, over the batch-70 corpus and the 2229 broken pairs: at every basepoint of the branch (not only crossings) whose arm runs high, does the running arm satisfy Valley3BeforeNine? At every basepoint of the band [L, L + 9] with LowAt on that arm? Without LowAt? The answer places the statement: a fact about a running arm of a faithful pair with the branch hypothesis, or about a running arm of a faithful pair, or something that needs the crossing. If it holds without the crossing, the batch-64 rule applies before any Lean statement: probe the arm-only class (the automaton over 1-Lipschitz arms with the one-arm crookedness clauses) to arms of at least twice the length of the shortest witness ascent, and report whether the arm-only version fails — batch 66's not_armCrossMid2L5 says what to expect, but it is a question.
The reading that places the valley. At the counterexample the L + 3 valley is named by the descending pairing from an L + 5 link on the running arm's side to the far L + 2 time. Over the 229 and a sample of the 2229: is the same reading available at each (an L + 5 or higher link on the running arm's side before the basepoint, and some L + 2 time past it), and does it name the Ceil72 valley? Then the index question: the valley lies between the endpoints; what bounds how far past the L + 5 link it sits — in particular, what puts it before the running arm's first ascent to L + 9? low_nine_sep separates the L + 2 endpoint from the ascent by 169; whether that, with the pairing's own spacing, places the valley on the near side of the ascent is asked. If the valley can lie past the ascent, the census can look for an instance.
Break the valley. The construction machinery of batch 71 (break-batch71.c), aimed at Valley3BeforeNine on the running arm instead of at the distance: edits to the running arm's approach — the stretch between the basepoint and its first ascent — that remove every time at L + 3 before the ascent, or push the peak below L + 6, or push the L + 3 time to within five steps of the ascent, while preserving faithfulness. The batch-71 lesson is that edits adding no new level pattern survive; a running arm that rises from L + 5 to L + 9 dipping only to L + 4 is the target shape. A faithful pair with such an arm at a crossing is a counterexample to S3 at span nine unless another walk serves it — and is reported first either way. The obstruction, if the construction fails, is to be named as batch 71 named raise's and band's.
BothHighRunL5 at a crossing. The missing half: a w8 arm cannot run high while its partner runs high. Sixteen thousand basepoints have both arms running high, none a crossing. Whether the two high runs, read against each other through the partner's LowAt (each arm's descent to L + 1 comes after its ascent), give w3 or wb to both arms — or whether a shape exists that the corpus lacks — is asked. Closing it discharges the partner's Ceil72 in general.
Assembly, if §2.1–2.3 make Valley3BeforeNine a theorem: s3_span_nine_mid5, then s3_span_nine; then the inventory of batch 69 §2.6.

No opinion is offered on the answers.

3. Deliverables
Whatever is proved, sorry-free, with #print axioms.
The censuses of §2.1 and §2.2 and the construction of §2.3, under the audit protocol; censuses over arms alone say so and state their arm-length bound.
Report: first line names the commission read; any counterexample first; then §1; then §2 1–5.
4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not); a replacement sufficiency statement for the landmark sentence; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam.
