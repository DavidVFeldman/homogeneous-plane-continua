# Commission: batch 74 — after span nine

Go! Runs on top of the batch-73 delivery. No new file is prescribed. This text is pasted into the
prompt and is in the archive as COMMISSION-batch74.md; the report names it in its first line.

## 0. On batch 73

Audited: Mixed.lean and General.lean changed only by commenting out the three relocated statements
with pointers; two new files; nine theorems, all on [propext, Classical.choice, Quot.sound]; no
native_decide; the repository's sorrys are s3_general and theorem3.

s3_span_nine is a theorem: for a faithful pair in a band [L, H] with L + 3 ≤ H ≤ L + 9, the two
arms of every basepoint fold onto a common walk. The reading of batch 73 §2.1 was correct in every
clause (ceil72_run_of_cross_highRunG), with one correction of detail recorded (armG d − (L + 3) ≤ 6,
equality at exactly L + 9); exhaustiveness at a crossing is by highRunG_of_not_deepFirst2, not by
not_bothHighRun_of_cross. Recorded fact: the residue named in batch 64 (Leg4TriCrossL5) is a
theorem (leg4TriCrossL5_holds).

The inventory (inventory-batch73.md): 471 declarations in the dependency graph, 304 pinning a level
offset, 161 parametric; the walks are fixed tuples of levels.

## 1. Targets

s3_general (General.lean); if proved, close theorem3 by theorem3_of_S3.

Individual spans above nine are not targets. This batch is reconnaissance and packaging; a proof of
s3_general is not expected from it, and a census result is a good outcome.

## 2. Questions, asked as questions

1. Package what is proved. theorem3_of_S3 takes D with k links, and the pair's span is at most
   k − 1. State and prove, in a new file, Bing 1948 Theorem 3 in the block reading and three-link
   form unconditionally for D with at most ten links — the statement of theorem3 with the
   hypothesis k ≤ 10 (or whatever bound the reduction actually yields; if the reduction loses a
   level, say so and state the true bound). Also s3_span_le_nine : S3 restricted to H ≤ L + 9, as a
   named statement, since S3's attainment hypotheses are not needed. These are the milestone
   statements; #print axioms for each.
2. What the downstream uses need. theorem3 is consumed by Theorem 4's hard case
   (Chains/Consolidation.lean, exists_blocks_first_last is the easy case; the reduction is
   COMMISSION-batch4 §3 and the notes' §4), and Theorem 4 by Theorem 13 and the 1951 reduction.
   Asked as a question about the repository's own reductions: when Theorem 4's hard case calls
   Theorem 3, is the chain D it passes arbitrary, or is it — or can it be, by a consolidation that
   Theorem 1 says preserves crookedness — a chain of bounded length? If bounded, what bound, and is
   it at most ten? If not, the answer is "arbitrary", and it settles that s3_general is needed for
   the classification and not only for Bing's statement.
3. Reconnaissance at spans ten, eleven, twelve. A census, under the audit protocol, over faithful
   pairs of those spans (the batch-70 corpus builder with the band widened; windows of bing 0 N for
   larger N; vpath chains; shaved and filled pairs): at every basepoint, is there a walk of the
   four-leg family serving both arms? If not, the least number of legs that does, and the count of
   basepoints needing each. Is the structure of span nine — two branches, a trichotomy of walks at
   each, crossings served by a fifth and sixth walk — visible at span ten, and how many branches and
   walks does span ten show? This is the question batch 41 asked at span nine ("does the span-by-span
   route converge?") asked one span up, with the span-nine answer now known.
4. The parametric core. Of the 161 declarations that carry their levels as parameters, which form
   the engine — the timing law (z, minGap, ivSep, ArmSep), the exact fold criteria
   (foldsOnto_leg4_iff_leg4Land and the three-leg ones), the pairing lemmas read at parametric
   levels — and which of the 304 fixed ones are instances of a parametric lemma applied at a literal
   level (so that a parametric restatement would prove them at once)? A statement about the
   repository, not a proof.

No opinion is offered on the answers.

## 3. Deliverables

§2.1 as Lean, sorry-free, with #print axioms.
The census of §2.3, under the audit protocol; censuses over arms alone say so and state their
arm-length bound.
Report: first line names the commission read; any counterexample first (a basepoint at span ten
served by no walk of any family searched is reported first, with a definition audit); then §1; then
§2 1–4.

## 4. Not in this batch

Proofs at spans ten and above (the general statement is a target; individual spans are not); a
replacement sufficiency statement for the landmark sentence; Bing 1948 Theorems 4, 5, 6, 13 as
proofs (Theorem 4's reduction is read, not proved, in §2.2); the 1951 reduction; the linear-time
far-index check; Bing's seam.
