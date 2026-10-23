Commission: batch 75 — reconnaissance for a general argument

Go! Runs on top of the batch-74 delivery. No new file is prescribed. This text is pasted into the
prompt and is in the archive as COMMISSION-batch75.md; the report names it in its first line.

0. On batch 74

Audited: one new file (Target74.lean), one docstring correction in Span.lean, nothing else changed;
s3_span_le_nine and theorem3_ten_links on [propext, Classical.choice, Quot.sound]; the repository's
sorrys are s3_general and theorem3.

Recorded facts: the chain D that Theorem 4's hard case passes to Theorem 3 is arbitrary, so
s3_general is needed for the classification. The four-leg family serves every basepoint at span ten
and fails at spans eleven (19 basepoints) and twelve (962, including bing 0 12 thin); the least
walks found there are the span-nine w72 with one ascent to H − 1 appended. The batch-26 bound
⌊span/2⌋ − 1 on turning targets is false at span eleven; corrected in place. The engine is
parametric in the walk and pinned in the band.

1. Targets

s3_general remains the target. No proof is expected from this batch. It is a census-and-statements
batch: its deliverable is evidence about whether an argument uniform in the span exists, and of what
kind. A negative answer to any question below, established, is a good outcome.

2. Questions, asked as questions

1. Does the least walk at span S extend a least walk at a lower span? The span-eleven and
   span-twelve witnesses need 4 → 7 → 2 → 8 → 1 → 10 and 4 → 7 → 2 → 9 → 1 → 11: the span-nine walk
   w72 with a final ascent appended. Over the batch-74 corpus at spans 10, 11, 12, at every
   basepoint whose least leg count is k ≥ 3: is some least walk obtained from a walk that serves the
   same basepoint read in a sub-band (the pair restricted to a band [L', H'] of smaller span
   containing the basepoint's level, via isCrookedIvF_restrict) by appending legs at the ends?
   Report the fraction, and the shape of the appended legs (always an ascent to H − 1? to L + 1?
   both?). If the answer is "always, by one leg per two levels of span", that is a conjecture to
   record; if it fails, the failing basepoint is the finding.
2. What does the split lemma see? foldsFrom_split (Span.lean) glues a fold on a prefix of one arm to
   a fold on its suffix. At the five-leg basepoints of spans eleven and twelve: is there a split
   index on each arm at which the prefix lies in a sub-band of span ≤ 9 (so s3_span_nine applies to
   it) and the suffix likewise — and do the two folds meet at a common walk time? This is a census
   question about where the arms cross from one sub-band to another, not a proof question. The
   obstruction, if any, is the one the commission wants named: a common walk for both arms must be
   one walk, and gluing along one arm says nothing about the other.
3. The growth of the least leg count. Over the corpus, the maximum least leg count is 3, 4, 4, 5, 5
   at spans 8–12 (batch 74: 44 four-leg basepoints at nine; 2817 at ten; five at eleven and twelve).
   Extend the census to spans 13 and 14 if the corpus builder reaches them within the pair-length
   cap, and report the maximum least leg count and the levels at which it is attained. Whether the
   count is ⌊(S − 1)/2⌋, or ⌈S/3⌉ + 1, or something else, is a conjecture to record with its data;
   whether it is bounded is what S3 needs to know nothing about (S3 allows any walk), so this
   question is about the shape of a proof, not the truth of the statement.
4. The branch structure as a function of span. Batch 74: branches = the S − 5 middle levels; the
   extreme three levels at each end are single-walk at every span. Is the single-walk fact at the
   extreme levels a theorem at every span — that is, does the repository's argument for the levels
   L, L + 1, L + 2, H − 2, H − 1, H at span nine use the span, or only the distance to the nearer
   end? A parametric restatement of those lemmas alone — stated for a band [L, H] with no bound on
   H − L, proved if the proof goes through unchanged — is the one Lean deliverable asked for; if the
   proof does not go through, say which step uses the span.
5. What the general model adds. Every refutation since batch 55 that mattered came from the general
   model (shaved/filled pairs, σ ≠ ρ) or from windows of longer Bing chains. At spans 10–12, do the
   thin pairs alone (σ = ρ) show the same least leg counts, or lower? If lower, the general model is
   where the difficulty lives, and any uniform argument must be about σ.

No opinion is offered on the answers. A route to s3_general is not asked for and is not to be
proposed; what is asked for is the evidence a route would have to answer to.

3. Deliverables

§2.4's parametric restatement as Lean if it goes through, sorry-free, with #print axioms; otherwise
the step that fails, named.
The censuses of §2.1, §2.2, §2.3, §2.5 under the audit protocol, over whole arms, with two
independent FoldsOnto deciders as in batch 74; any witness re-checked by code sharing nothing with
the census.
Report: first line names the commission read; any basepoint served by no walk of any family searched
first, with a definition audit; then §1; then §2 1–5; then a one-paragraph statement of what the
evidence says about the existence of an argument uniform in the span, as evidence and not as a
route.

4. Not in this batch

Proofs at spans ten and above; a proof of s3_general; a replacement sufficiency statement for the
landmark sentence; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time far-index
check; Bing's seam.
