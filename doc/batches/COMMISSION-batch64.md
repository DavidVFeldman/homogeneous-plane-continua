# Commission: batch 64 — two walks, one case split

**Go!** Runs on top of the batch-63 delivery. No new file is prescribed.

## 0. On batch 63

Audited: every earlier Lean file identical; two new files; standard axioms, no `native_decide`.
One refutation, of batch 62's own general statement: `LandWalkSuffices` is false (three-time
witness), because the sentence read triggers and last gaps at the walk's *turn times* where the
four-leg sentence reads them at the *level*. The corrected `LandWalkP` is necessary for any walk
and excludes the witness; it is sufficient, on the search, exactly for walks without a unit leg
(`not_landWalkP_suffices_without_noUnitLeg` for the other side), so `LandWalkPSuffices` carries
`NoUnitLeg` and cannot be weakened either way. The four-leg window excludes unit legs, so
`Leg4Land` is untouched.

The crossing is now two walks and one split. Over the 461 stored crossings: `w72` serves both arms
at 421 and `w71` at 374; **`w71` or `w72` at all 461**. The partner's 30 failures of `w72` are all
its deep-floor clause, all where the partner touches `L`, all served by `w71`. The 179 crossings
where the `w8` side touches `L` are all served by `w71`. So: a crossing in a band that misses the
floor is served by `w72`; a crossing where some arm reaches `L` is served by `w71`, whose
deep-floor clause never fires inside the band. The two-index slack is closed by the three-level
law on the crooked peak's *interval* (`base_high_sep`, tight at five), and
`s3_span_nine_mid5_of_cross_w72` proves the branch at a crossing from `L + 1 ≤ ρ` and the
partner's `w72` alone.

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`).
2. `s3_span_nine` (`General.lean`).
3. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The partner's `w72` off the floor.** `s3_span_nine_mid5_of_cross_w72` takes the partner's
   `w72` as a hypothesis. On the corpus the partner fails `w72` only by touching `L`. Whether, in a
   band with `L + 1 ≤ ρ`, the partner's `w72` follows from the crossing and the pairing — its
   floor and ceiling clauses from `w8`'s failing floor clause and the crooked peak, as the `w8`
   side's did — is the first half of the branch.
2. **`w71` when an arm reaches `L`.** Whether both arms satisfy `w71`'s exact criterion at a
   crossing in which some arm reaches `L`: the `w8` side owes `w71` a valley at `L + 1` before its
   ascents to `L + 9` (`leg4Land_w71_of_w8_of_low1`); the partner owes the floor clause at descents
   to exactly `L + 2` and the ceiling clause (`leg4Land_w71_of_wb_of_rest`). Whether the arm that
   reaches `L`, paired across the basepoint with the other arm's extremes and spaced by `ivSep`,
   supplies these, is the second half. If the case splits further by which arm touches `L`, say so.
3. **Assembly.** With 1 and 2, `Leg4SixCrossL5` (or a two-walk form of it) is a theorem, and
   `s3_span_nine_mid5`, `s3_span_nine` follow. If some sub-case resists, name it as a statement
   with the census count behind it.
4. **`LandWalkPSuffices`**, with `NoUnitLeg`. The induction of `gseq4_invLand` over `walkList`
   against `WalkInvLand`, now for a statement not refuted by a short arm.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the audit protocol; censuses over arms alone say so.
3. Report: any counterexample first; then §1; then §2 1–4.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam.
