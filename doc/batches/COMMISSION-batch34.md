# Commission: batch 34 — the outside-in induction step, gated on spans 9–12

**Go!** Runs on top of the batch-33 delivery. One new file, `HPC/Fold/Step.lean`; root
`HPC.lean` updated. Nothing else touched. **§1 is a gate: run it before writing Lean.**

## 0. On batch 33

Audited clean: forty-one earlier files identical, no forbidden tokens.

Three things to record. **`no_common_walk_pairA_pairB` is stronger than the commissioned
statement** — no walk whatever takes both stretches, not merely no member of the family, and the
only property used is that a walk moves one level per step. **The commission's two named walks
were swapped**: `[3,2,4,1,5]` serves `B` and `[3,4,2,5,1]` serves `A`, and the shortest witnesses
are `[3,5,1]` and `[3,1,5]`. And **`B = 6 − A` pointwise** — the refuting pair is a stretch and
its own reflection, which is worth knowing: the obstruction is exactly maximal opposition of the
two demands, and the arms of a real basepoint evidently cannot achieve it.

The trimming census did its job. The span drops by exactly one at every step and never stalls,
so the descent is sound. The two defects found are real: the maximal stretch is **not unique**,
so "the maximal contiguous stretch" does not denote and the induction must choose; and the
basepoint does not stay interior, reaching an extreme level of some inner band about 30 % of the
time — which `s3ZigFree_near_extreme` covers, so it is a case split and not a failure.

`isZigFree_append_outer` is exactly the dual that was wanted, and the disjunction in its
conclusion is forced by the inner member's `ends` clause rather than being slack.

## 1. The gate

What batch 33 left uncensused is the content of the step, and it holds in the strong form.

For each basepoint, take the trimmed stretches (greedy left-first and greedy right-first, which
batch 33 shows may differ). Ask whether some trim has: at least one walk of its band serving the
inner stretch's two arms at the basepoint, and **every** such walk extending — by appending
`[L+1, H−1]` or `[H−1, L+1]` — to a walk serving the whole arms.

Measured here, with folding decided exactly by reachability: **0 failures of 71 basepoints at
span 6, 0 of 170 at span 7, 0 of 409 at span 8.** The weaker "some walk extends" form also holds
at all three.

The quantifier is the point. The induction hypothesis returns *some* walk for the inner stretch
and gives no control over which, so the step must extend every inner-serving walk, not merely
one. Both forms were measured; "every" is the one stated.

> **Census `ExtendStep` at spans 9, 10, 11 and 12 — every basepoint of `bing 0 n` — before any
> of §§2–3. If it fails, stop, report the failing basepoint with its trims and the inner walk
> that does not extend, and deliver nothing else.** A failure is the batch's result and cheap at
> that price: the two previous families each had evidence that stopped one span short of their
> counterexample.

If it holds, report also whether one of the two greedy trims always works, or whether the choice
between them is genuinely needed — batch 33 measured that they differ often, but not whether
both are ever required.

## 2. The ordinary item

**s3ZigFreeInterior_of_extendStep.** Strong induction on `(H − L).toNat`.

Base `H ≤ L + 3`: no interior basepoint exists, since `L + 3 ≤ ρ i ≤ H − 3` is then empty.
Also dispose of `H = L + 4`, where the hypothesis of `ExtendStep` holds but the inner band has
span `3` and carries no interior basepoint: there the inner walk is supplied by
`s3ZigFree_near_extreme` applied to the stretch, since every level of a span-3 band is within
two of an extreme.

Step: `ExtendStep` gives `a, b, L', H'` and an inner walk. The inner stretch is faithful and
crooked by `isCrookedIvF_restrict` (batch 30), its extremes are attained by `IsTrim`, and its
span is strictly smaller, so the induction hypothesis applies to it — **at the basepoint
`i − a`, which may or may not be interior to `[L', H']`**. Case split: if it is interior, the
induction hypothesis gives a walk serving the inner arms; if not, `s3ZigFree_near_extreme`
(batch 29) does, at any span. Either way some inner-serving walk exists, so the "every" clause
of `ExtendStep` applies to it and returns the extension, which `isZigFree_append_outer` places
in `IsZigFree L H`.

*(supply: the arm-restriction bookkeeping — that the arms of the stretch at `i − a` are the
restrictions of the arms of `ρ` at `i` — and the `Fin` arithmetic of `⟨a + j.val, _⟩`. Batch 30's
`isCrookedIvF_restrict` has the same shape and its proof should transfer.)*

## 3. `extendStep` — the search item

Search permitted. **A counterexample is a success; report it first** — and note that §1 will
already have found it if it is at span twelve or below.

No sketch is offered, because every sketch this project has offered for a statement in this
position has been wrong in a way the census then found. What is available: `crookedIvF_cut_first`
(batch 26), `timing_slack'` and `index_gap_of_level_gap'` (batch 30), `minGap` (batch 30),
`foldsOnto_prefixLeg` and `isZigFree_cons` (batch 31), `isZigFree_append_outer` (batch 33), and
the one-turn theorems with `not_oneTurn_of_opposite` (batch 31). The constraint from batch 33 is
that the two arms must not be separated: any argument that treats them as two independent
sequences at a common level is refuted by `no_common_walk_pairA_pairB`.

## 4. Deliverables

1. **The §1 census, first**, with its verdict before anything else, and the greedy-trim question.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report: the §1 result; any counterexample; whether `s3ZigFreeInterior_of_extendStep` went
   through and what the case split on interiority cost; what was supplied.

## 5. Not in this batch

The linear-time far-index check for `¬ F2PrimeOff`; Bing 1948 Theorems 4, 5, 6; the reduction in
Bing 1951; the D8/D9 gap.
