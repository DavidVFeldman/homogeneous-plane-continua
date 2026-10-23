# Commission: batch 122 — reconnaissance: can Bing's induction for Theorem 3 be closed by a stronger hypothesis?

**Go!** Runs on top of the batch-121 delivery. No skeleton. One file accompanies this commission,
`COMMISSION-batch122.md` (also pasted into the prompt). Lean work goes in a new file
`HPC/Fold/Recon122.lean` (import it at the end of `HPC.lean`); open statements as `def … : Prop`,
no new `sorry`. Census programs and logs in `doc/census/` as in batch 121. No existing file is to be
edited except `HPC.lean`, `Axioms.lean`/`axioms.txt` (group "Reconnaissance, batch 122"), and the
housekeeping of §3.

The report names the commission read in its first line and answers each question *proved /
refuted / open with the obstruction stated*.

## 0. On batch 121

Audited and accepted in full: the respective reading refuted (my slip, recorded as such), Bing's
wording open, the census corrected to the possible-meeting table with `theorem3_end_of_model`
making its verdict a theorem about all chains in the corpus, and the special case of Bing's proof
certified defective (`seam_every_H_fails`). Recommendation accepted: `theorem3_end` stays the
audited target, `Theorem3LiteralOr` is the Prop for Theorem 3 as printed. 436 declarations,
`sorryAx` in two.

## 1. The question

REPORT-batch121 §Q4, the Cbot row: on the K = 5 corpus of special-case instances (n = 11, 12),
under the bottom-anchored grouping `bingSpecialFCbot`, for *every* instance *some* H satisfying
Bing's induction hypothesis makes F a chain with d_i first — while under Bing's own grouping at
least half the instances fail for every H. So Bing's argument may close if the induction
hypothesis is strengthened by a property P of the consolidation that (i) makes his regrouping
work and (ii) is itself reproduced by the regrouping. The report named what P must control: the
time of the block of the end link d_h relative to the levels of the links it meets, and what the
links of h_{u−1} meet — "end-time control". Nobody has looked for P. This batch looks.

Everything below is in the faithful model (ρ, σ) unless a chain is needed; by
`exists_chain_iff_isCrookedIvF` and `linkChain_only` nothing is lost for Bing's statement on
realized chains, and the only-clause is automatic there.

## 2. Questions

**Q1 — What distinguishes the H that work?** On the special-case instances of the batch-121 corpus
(K = 5, n = 11, 12, 13; and K = 6 at the first n where instances exist — the report says none up to
n = 14; go to n = 16 or report that there are none), for each instance (seq, h, k, i) list the H
satisfying the induction hypothesis (`SeamIH`-style: basepoint first and only, blocks in two
adjacent links of E(1, r−1), the "or" end clause for d₁ and d_h) and mark which make F a chain
under Cbot, and under Bing's reading A. Then find the weakest property P(H) you can state in
sequence terms such that every H with P works under Cbot (or under some single fixed reading),
and P is satisfiable at every instance. Candidates to test first, in increasing strength — test,
do not assume: (a) the block of d_h is the *last* block of H (u = max H); (b) every link of
h_{u−1} has σ ≥ r − 3 (so h_{u−1} ⊆ e_{r−3} + e_{r−2} and meets only the top group); (c) both;
(d) the "end-time" form: the block of each end link of D(1, h) that meets an extreme level of
E(1, r−1) is the last block of H in which any link reaches that level. Report P (or the finding
that no property of H alone separates the working H from the failing ones at some instance —
then say what else the choice depends on).

**Q2 — Does P reproduce?** This is the crux. For the strengthened statement
`Theorem3LiteralOr ∧ P` to be provable by Bing's induction, the F built in each case must satisfy
P relative to E. Check, on the same corpus: (a) base cases m ≤ 4 and the case d_i ⊆ e₁ + e₂ (level
grouping): does the level-grouped F satisfy P? (b) special case: for each instance, is there an H
with P such that F (Cbot) has P? (c) general case: the regrouping of REPORT-batch121 §Q4 — does F
have P when H has P? If P fails to reproduce, say where, and whether a different P (perhaps
stronger, perhaps two-sided) reproduces; iterate once or twice if the corpus suggests a candidate,
and stop if none does. A reproducing P on the corpus is the positive outcome; a certificate that
every property of a natural class fails to reproduce is the negative one.

**Q3 — The strengthened statement.** If Q2 finds a reproducing P: record `Theorem3Strong : Prop`
(Bing's statement in the block reading plus P), prove `Theorem3Strong → Theorem3LiteralOr` and
`→ Theorem3EndStmt`, and attempt the proof of `Theorem3Strong` in the faithful model by Bing's
induction, now with the seams closed — proved, or open with the exact step that resists. No
`sorry`; if the proof is partial, keep the proved lemmas and record the statement as a Prop. If Q2
is negative, Q3 is "not reached".

**Q4 — The three-link end clause.** Independently of Q1–Q3: is there a three-link analogue of P
(end-time control for the end links of the whole chain) that the Z77 zigzag can be made to satisfy
by a change of the *greedy choice* rather than by post-processing (batch 86 showed the
post-processings fail)? Reconnaissance only: state the candidate as a Prop in the sequence model,
census it on the batch-121 corpus (T3ENDP classes), and report whether Z77's construction
satisfies it as is (`Fit`, `greedy_fit`) or where it would have to change. Do not modify Z77.

**Q5 — Assessment.** Proved / refuted / open for: a reproducing P exists (on the corpus); Bing's
induction closes with it (in Lean); `theorem3_end` by Q4. One paragraph on what a proof would need
if both are open.

Not in scope: `fugate_cor1`, `treeLike_nonseparating`, `PlaneFacts`. No new `sorry`.

## 3. Housekeeping (this batch)

1. `README.md`: replace "Theorems 1–15 (Theorem 3 without its end-link clause)" by "Theorems 1–15;
   Theorems 3 and 4 in the three-link form (Bing: two adjacent links); Theorem 3's end clause open
   (`theorem3_end`); Bing's proof of Theorem 3 is incomplete as written (`LEDGER.md` §1,
   REPORT-batch121)"; batch count.
2. `OPEN.md` item 1: cite `theorem3_end_of_model`, the census class T3ENDP and its corpus,
   `Theorem3LiteralOr`, `theorem3EndStmt_of_literalOr`, and the proof defect with its certificate.
3. `doc/census/README.md`: list the batch-121 programs and logs (and this batch's).
4. Delete any stray `theorems-3-4-scheduling(NN).md` at the root; the uploaded notes to
   `doc/theorems-3-4-scheduling.md` as usual.

## 4. Deliverables

1. `HPC/Fold/Recon122.lean` (Props, implications, whatever is proved); `axioms-batch122.txt`;
   `axioms.txt` regenerated (`sorryAx` stays at two).
2. Census programs and logs; tables in the report in the batch-121 format, including the per-
   instance counts "H satisfying IH / with P / working".
3. Report: first line names the commission read; Q1–Q5 in order; housekeeping confirmed.
