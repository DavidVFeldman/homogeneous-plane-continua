# Commission: batch 68 — what the branch `L + 5` still owes, and the assembly

**Go!** Runs on top of the batch-67 delivery. No new file is prescribed.

**On the intake.** The workspace's `COMMISSION.md` is the batch-65 text; batches 66 and 67 ran from
the previous report's residue list because the uploaded commissions did not reach the workspace.
This text is therefore also pasted into the prompt. The report states, in its first line, which
commission it read (this one is "batch 68") and saves a copy as `COMMISSION-batch68.md`.

## 0. On batch 67

Audited: every earlier Lean file identical except four import lines of `HPC.lean`; four new files;
standard axioms, no `native_decide`; the four `sorry`s are the four standing targets.

One refutation, of an arm-only reading: `Mid2Floor2` does not imply `Mid2Floor` on an arm
(`not_mid2Floor_of_mid2Floor2_arm`, fifteen-time witness `cex67` obeying `ArmSep`). Recorded fact:
the index is recovered from the pairing, not the arm.

Results, all theorems:

* `highFirst_or_deepFirst` — every arm of the band is high first or deep first; the mixed case is
  across the two arms only.
* `crooked_peak_valley_high9`, `crooked_valley_peak_high9` — the pairing read against a link at
  `L + 1` or below and a link carrying `L + 9`: peak carrying `L + 8` (level `≥ L + 7`), valley
  `≤ L + 2`; spacings 169, 70, 169. These are the levels `w3`'s ceiling clause and `wb`'s deep
  clause ask for, so the `L + 2`/`L + 1` seam of batches 64–66 is closed.
* `w3_or_wb_of_land` — with the branch hypothesis and the ascent landmark on both arms, one
  reflected walk serves both arms.
* `crossMid2` — at a crossing of the trichotomy, both arms satisfy `Mid2Floor`; `crossMid2L5'`
  follows. The residue named in batch 64 is a theorem.
* `s3_span_nine_mid5_of_cross_wb_two_walks_of_cross` (+ mirror) — at a crossing whose partner is
  served by `wb`, the pair folds if the `w8` side satisfies `w71`, or satisfies `w72` while the
  partner has its deep-floor clause.

## 1. Targets

1. `s3_span_nine_mid5` (`Mixed.lean`).
2. `s3_span_nine` (`General.lean`).
3. `s3_general`; if proved, close `theorem3` by `theorem3_of_S3`.

A counterexample is a success and is reported first, after a definition audit. A refuted
statement is kept, commented out, with the refutation named.

## 2. Questions, asked as questions

1. **The partner's `wb` at a crossing.** The assembly's hypothesis is that the partner is served by
   `wb`. `mid2Fail_w3_or_wb` places a `Mid2Floor`-failing arm on `w3` or `wb`, but at a crossing the
   partner now *satisfies* `Mid2Floor` (`crossMid2`), so that lemma does not apply to it. What is
   known: the partner is served by none of `w8`, `w71`, `w72` (the crossing clauses); the
   trichotomy `leg4Land_tri`; the batch-64 census, partner on `wb` at 461 of 461. Whether "partner
   on `wb`" is a theorem at a crossing — from the trichotomy and the crossing clauses alone, or
   with the pairing — is asked; if it is not, what the partner is instead is the answer.
2. **The `w8` side's disjunction.** At a crossing with the partner on `wb`: the `w8` side satisfies
   `w71`'s ceiling clause, or `w72`'s deep clause while the partner has its deep-floor clause.
   Batch 64 measured this at 461 of 461; batch 65 measured the two clause failures at 87 and 10,
   disjoint. Three questions, in order: *(a)* does the pairing at the top of the band
   (`crooked_peak_valley_high9`), which supplied `w3`'s ceiling clause on the partner from the
   `w8` side's time at `L + 9`, read the other way — the `w8` side's ceiling clause from the
   partner's descent — and is the level it returns the one `w71` asks for? *(b)* the batch-66 §2.2
   question, unanswered for two batches: whether a `w8` side failing both clauses is excluded by
   the nine-level bound (`L` to `L + 9`, 985 steps) in an arm of span nine. *(c)* a census under
   the audit protocol over the crossings only: at each of the 461, which disjunct holds, and, where
   `w72` is the one, whether the partner's deep-floor clause holds with it. No census has been run
   since batch 65; §2.2(c) is the first one asked for.
3. **Assembly.** With §2.1 and §2.2, `s3_span_nine_mid5` closes through `Leg4SixCrossL5`,
   `crossMid2`, and the two-walk form. Then `s3_span_nine`: `s3_span_nine_except` left two branches,
   `s3_span_nine_mid4` closed one, `s3_span_nine_mid5` closes the other. Whether `s3_span_nine`
   follows from those three with no further case is asked; if some case remains, name it.
4. **The engine probe.** No probe has been run in three batches. The batch-64 rule asks for arms of
   forty times before any sufficiency statement is written for the landmark sentence with the
   added clause of batch 66 §2.3 (every time at a level served only by walk positions before the
   `r`-th turn comes before the `r`-th landmark). The probe to forty is a deliverable of this batch
   regardless of §2.1–2.3, with its result stated either way; no Lean statement is asked for.

No opinion is offered on the answers.

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. The censuses of §2.2(c) and §2.4, under the audit protocol; censuses over arms alone say so and
   state their arm-length bound.
3. Report: first line names the commission read; any counterexample first; then §1; then §2 1–4.

## 4. Not in this batch

Spans ten and above one at a time (the general statement is a target; individual spans are not);
Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index check; Bing's seam.
