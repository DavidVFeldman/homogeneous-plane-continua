# Commission: batch 60 — the branch `L + 5` with exact criteria in hand

**Go!** Runs on top of the batch-59 delivery. No new file is prescribed.

## 0. On batch 59

Audited: every earlier Lean file identical; four new files; standard axioms, no `native_decide`;
no counterexample, no refutation. **The four-leg criterion is exact**
(`foldsOnto_leg4_iff_leg4Land`) on the whole wide window, with the index bounds proved
load-bearing (120 348 arms meet the level-only sentence and do not fold). The batch-58 witness is
served by nine walks, all with valley `L + 1`, where the deep clause is vacuous — the exact
criterion sees what the engine's criterion missed (`land_5_6_1` against `not_crit_5_6_1`). The
branch is reduced to exhaustiveness in arm-only exact form (`Leg4LandClosesL5`,
`s3_span_nine_mid5_of_leg4LandClosesL5`), which holds at all 1 384 273 basepoints of the corpus
with five walks. And at the branch's best walk, `L+6 → L+3 → L+7 → L+1 → L+8`, the descent clause
of the exact criterion is a theorem from the branch hypothesis, index bounds included
(`land_down1_of_lowAt_low`); the two ascent clauses are what remains.

Noted from the report: the census line "the reflection of `LowAt` is `HighAt`: fails at …" is a
stale label counting a difference between two predicates never claimed to be reflections. It is
struck from the audit list.

The situation at `L + 5` is now the situation at `L + 4` before batch 48: exact criteria for the
walks, one clause of the best criterion already supplied by the hypothesis, and exhaustiveness to
be argued.

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`), through `Leg4LandClosesL5` or otherwise.
2. `s3_span_nine` (`General.lean`).
3. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The two ascent clauses as arm-only dichotomies.** At `L + 4` the pattern was: an arm failing
   a clause of the exact criterion folds onto a canonical walk by itself (`leg3Valley_or_vee`,
   `leg3Ceil_or_lam`), so a failure is never the failing arm's problem, and what remains is a
   crossing. Whether the same holds at `L + 5` for the two ascent clauses of
   `L+6 → L+3 → L+7 → L+1 → L+8` — an arm of the branch failing the `L + 8` clause, or the `L + 9`
   clause, folds onto a reflected canonical walk or onto another walk of the five — is asked.
   With exact criteria the failing arm's alternative is itself a decidable sentence, so the census
   can say which walk before Lean is asked.
2. **The crossings at `L + 5`.** If the dichotomies of question 1 hold, the residue is a pair whose
   arms fail different clauses. Whether the clause read at the arms' own levels and `ivSep` (the
   mechanism of batch 56) close those crossings — and where, if anywhere, the level read from
   below (batch 57) stops them — is the branch.
3. **The general engine.** `gseq4_invLand` carries a time credit per landmark chain; the report
   says the two credit-carrying bounds are exactly what the index gaps buy. Whether the same
   invariant, with one bound per leg, proves the landmark sentence exact for a walk of any number
   of legs — the general sufficiency asked since batch 48 — is asked again, now with a four-leg
   proof to generalise from. If it does, the arm-only half of every branch at every span is one
   theorem.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. Censuses over the general model under the audit protocol; censuses over arms alone say so.
3. Report: any counterexample first; then §1; then §2 1–3.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam
(paraphrase to be checked against the paper first).
