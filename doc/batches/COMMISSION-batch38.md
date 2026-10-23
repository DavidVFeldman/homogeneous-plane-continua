# Commission: batch 38 — span seven, by batch 37's method

**Go!** Runs on top of the batch-37 delivery. One new file, `HPC/Fold/Span7.lean`; root `HPC.lean`
updated. Nothing else touched.

## 0. On batch 37

Audited clean: forty-five earlier files identical, and exactly one live `sorry` in the whole
project — the `theorem3` of `Open.lean`, which is the target.

**`s3_span_six` and `theorem3_span_six` are the first advance on Theorem 3 in ten batches**, and
they came from removing the commission's formulation rather than from replacing it. That is worth
recording plainly, and it is why this commission again proposes nothing.

Three things in the delivery are worth more than the span-six result itself.

**`span6_dichotomy` is span-independent.** It needs only `L + 3 ≤ H`, and it is one application of
the crookedness clause: an `H`-time before the basepoint and an `L`-time after it give
`b < r < r' < a`, and whichever side `r` falls on hands one arm the condition it was missing. That
is the reusable half of the method, already proved for every span.

**The folding half uses no crookedness at all.** `foldsOnto_walk6_of_lowLate` is about any
1-Lipschitz arm in the band, so its reflection follows by reflecting the arm — legitimate exactly
because `not_isCrookedSeq_neg` has nothing to bite on. The separation of the two halves is what
makes the argument clean, and it is the opposite of every formulation batches 6–36 tried, each of
which mixed the two.

**The negative results are as useful as the positive one.** "One arm folds onto the other" is
false at 870 instances and already at span five — the cheapest sequence-dependent rule there is,
and the first thing anyone would try after the family approach is refuted. And the one-clause
`LowLate` has no walk of length ≤ 10 serving it, even with local crookedness imposed on every
window of size ≤ 6, which is what forced the two-clause form. Recording the route that was
abandoned and why is what made the delivered form look inevitable rather than lucky.

## 1. The target

`s3_span_seven` and `theorem3_span_seven`, stated in `HPC/Fold/Span7.lean` with one `sorry` each.
Span six is done; span seven is the next with content.

**The method is yours and the choices are yours.** Batch 37 §3 says the inductive datum should be
a pair of conditions on the arms that some walk serves and that the crookedness clause can deliver
on one side or the other. The second half is `span6_dichotomy`, already general. The first half is
what changes with the span: `walk6` and `walk6'` will not serve at seven, and the reversal law says
the number of walks must grow. How many conditions, what they are, and how many walks — this
commission has no opinion, and the record of what happened when it had opinions is in §2.

If the conditions generalise to a scheme indexed by the span, say so and state it; if they do not,
span seven alone is the deliverable and that is a good outcome.

## 2. The record

Unchanged from batch 37's COMMISSION §2 — fifty-nine `not_`/`no_` theorems, grouped by what they
forbid — with three additions from batch 37 itself:

* no walk of length ≤ 12 serves every span-six basepoint, so the walk depends on the sequence;
* "one arm folds onto the other" is false, at spans five, six and eight;
* the one-clause weakening of `LowLate` is served by no walk of length ≤ 10.

And the standing constraints: no bounded family of walks (the reversal law); no treating the arms
as independent sequences at a common level (`no_common_walk_pairA_pairB`); no extension of an
inner walk by two outer legs (`not_extendStepMin`); no black-box extension hypothesis (batch 27
§4); reflection only where no crookedness hypothesis lies beneath (`not_isCrookedSeq_neg`).

## 3. Deliverables

1. Whatever is proved, `sorry`-free, with `#print axioms`.
2. A census of whatever was explored, including the conditions tried and rejected.
3. Report: any counterexample first; the conditions and walks chosen; whether they look like a
   scheme in the span; what was abandoned and why. **A run that closes routes without proving
   span seven is a good outcome.**

## 4. Not in this batch

Spans eight and above; Bing 1948 Theorems 4, 5, 6, 13; the 1951 reduction; the linear-time
far-index check.
