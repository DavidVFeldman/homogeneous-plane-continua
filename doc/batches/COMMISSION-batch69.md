# Commission: batch 69 — `Ceil72` on the high-running arm, and span nine

**Go!** Runs on top of the batch-68 delivery. No new file is prescribed. This text is pasted into
the prompt and is in the archive as `COMMISSION-batch69.md`; the report names it in its first line.

## 0. On batch 68

Audited: every earlier Lean file identical except a docstring in `General.lean` and one import line;
one new file, 37 theorems on standard axioms, no `native_decide`; the four `sorry`s are the four
standing targets; census, probe and independent-check logs present. No refutation of an earlier
statement.

Results, all theorems:

* The pairing at the top of the band read inside one arm returns `w71`'s ceiling clause exactly;
  with `Mid2Floor` and `DeepFirst2` (at `L + 2` or below before each own time at `L + 9`) the arm
  satisfies `w71` in full, and conversely: `w71_armG_iff_deepFirst2`. Hence at a high-running arm
  `w71` is false, not unproved.
* `s3_span_nine_mid5_of_cross_deepFirst2`: a crossing both of whose arms are `DeepFirst2` folds
  onto `w71` (374 of the corpus's 461).
* A non-`w8` arm that never reaches `L + 9` is a `wb` arm; the partner of a high-running `w8` side
  is also a `w3` arm (the pairing's valley cannot lie on the running arm).
* `s3_span_nine'`: span nine is the two branches, no further case. `s3_span_nine_mid5` is now:
  non-crossings (closed), `DeepFirst2` crossings (closed), and high-run crossings, reduced by
  `s3_span_nine_mid5_of_cross_highRun_armG` (+ mirror) to `Ceil72` on the running arm and the two
  deep-floor clauses where the band reaches `L`.
* The engine probe to forty is negative: the landmark sentence with the batch-66 clause has twelve
  counterexamples among 742 walks and 146 M arms, four re-checked independently. No sufficiency
  statement is written; nothing in the development depends on one.

Census facts (461 crossings): exactly one `wb` arm and one `w8` side at every crossing; the `w8`
side reaches `L + 9` at 282, the partner at 179, never both; the high run occurs at 87, always on
the `w8` side; `Ceil72` holds on the `w8` side at 461 of 461; at the 87, both deep-floor clauses
hold.

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`), then `s3_span_nine` (`General.lean`) through `s3_span_nine'`.
2. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **`Ceil72` on the high-running arm.** The arm reaches `L + 9` with nothing at `L + 2` or below
   before it; `Ceil72` asks for a time at `L + 3` or below before the ascent with a time at `L + 6`
   or above five steps before that. Batch 68 showed the pairing's valley against the partner's
   descent cannot lie on this arm, and the arm has no own time at `L + 2` to read
   `crooked_peak_valley_high9_mid` from. So which time supplies the `L + 3`? Asked first as a
   census question under the audit protocol, as batch 55 did for the far witness: at each of the
   87, the index and level of the `Ceil72` witness on the running arm, its distance from the
   ascent, and which link of which arm the crookedness clause returns when read from it. Whether the
   witness is then a theorem from the pairing, from `Mid2Floor` on the running arm (which `crossMid2`
   supplies), or from the partner's `w3` clauses, is the second question.
2. **The deep-floor clauses where the band reaches `L`.** `deep72_of_off_floor` makes them vacuous
   off the floor. Where the band reaches `L`: is the running arm's deep-floor clause, and the
   partner's, a theorem at a high-run crossing? Batch 63's `leg4Land_w72_of_cross_of_floor1` and
   batch 64's floor facts (the band never misses the floor at a crossing, 0 of 461) are the
   recorded material; how they meet the high-run hypothesis is asked.
3. **The assembly's hypothesis.** `s3_span_nine_mid5_of_cross_highRun_armG` assumes the partner
   stops below `L + 9`. The census says the two arms never both reach `L + 9` (0 of 461). Is that a
   theorem at a crossing — from the timing law across the basepoint (`ivSep`), from the crossing
   clauses, or otherwise — or at least at a high-run crossing? If it is not, the case where both
   reach `L + 9` is a case of the branch and is named as such.
4. **Assembly.** With §2.1–2.3, `s3_span_nine_mid5` closes and `s3_span_nine` follows by
   `s3_span_nine'`. Both are targets of this batch.
5. **The probe's refutation in Lean.** One of the four independently checked counterexamples of
   `PROBE-batch68.md` — a walk, an arm, the sentence with the added clause satisfied, `FoldsOnto`
   false — stated and kernel-checked, as `not_landWalkP3Suffices` was in batch 65. The refuted
   sentence is kept, commented out, with the witness named. No replacement is asked for.
6. **After span nine, a statement only.** Once `s3_span_nine` is a theorem, the report may list
   which of the lemmas in its proof carry the span as a parameter and which are stated for nine
   alone (levels `L + k` with fixed `k`, walk names, the number 461). No proof about other spans is
   asked; this is an inventory.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. The census of §2.1, under the audit protocol; censuses over arms alone say so and state their
   arm-length bound.
3. Report: first line names the commission read; any counterexample first; then §1; then §2 1–6.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
a replacement sufficiency statement for the landmark sentence; Bing 1948 Theorems 4, 5, 6, 13; the
1951 reduction; the linear-time far-index check; Bing's seam.
