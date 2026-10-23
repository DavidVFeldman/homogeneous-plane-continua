# Commission: batch 32 — the choice rule, gated on a census

**Go!** Runs on top of the batch-31 delivery. One new file, `HPC/Fold/Choice.lean`; root
`HPC.lean` updated. Nothing else touched. **§1 is a gate: run the census before writing Lean.**

## 0. On batch 31

Audited clean: thirty-nine earlier files identical, no forbidden tokens.

**The refutation of `arm_timing` is correct and the commission was wrong.** The timing bound
controls the distance from `ρ i` to the extreme an arm reaches, not whether `ρ i` is itself
extreme; a basepoint one level below the top reaches the top in one index at every span, and
`cutSeq` at index 11 is the witness. Keeping it as `ArmTimingClaim` with `not_armTimingClaim`
beside the corrected statement is the right disposal.

**`not_oneTurn_of_opposite` is the useful theorem.** It makes formal what eleven formulations
met as an impression: a basepoint whose forward arm rises two above the base before coming
within one of `L + 1`, and whose backward arm falls two below before coming within one of
`H − 1`, is served by no one-turn walk at all. With `s3ZigFreeInterior_descentFirst` and
`_ascentFirst` the one-turn case is now completely settled — proved where it holds, refuted
where it does not — and the coverage table shows it settling a shrinking fraction: 3 880 of the
13 635 interior basepoints at span 12.

`foldsOnto_prefixLeg` with `isZigFree_cons` is one full step of a multi-leg construction. The
rule that chooses the targets is all that is missing.

## 1. The gate

Two measurements were made here, and they bound what the rule can be.

**No single walk per band.** Take the targets read backwards from the end as
`H−1, L+1, H−3, L+2, H−5, …`, stopped at `⌊span/2⌋ − 1` of them. At spans 6, 8, 10, 12 this is
`[1,5]`, `[5,1,7]`, `[2,7,1,9]`, `[7,2,9,1,11]` — exactly the minimal itineraries batches 28–29
found at the hardest basepoint of each span. With its base free among the three admissible
centres it nevertheless fails at 4 of 71 basepoints at span 6, 30 of 170 at span 7, 120 of 409
at span 8, 389 of 986 at span 9, 1 236 of 2 379 at span 10.

**A growing but small cover.** Greedily covering every basepoint by walks of the free family
takes 7 walks at span 7 and 11 at span 8. The heaviest at span 8: `[4,3,5,2,6,1,7]` covering 144
of 409, then `[5,4,6,2,7,1]` covering 102 more, then `[3,2,4,1,7]` covering 62 more.

> **Compute the minimum cover, or a good greedy one, at spans 6 through 12, and report the
> walks and what each covers, before writing any Lean.** Two things to extract: how the cover
> size grows with span, and whether the covering walks are described by a rule in `L`, `H` and
> the base — for instance an outward alternation from the base with amplitudes increasing by
> one. **Do not adopt such a rule on the strength of the top few covers**; state it only if it
> covers every basepoint of `bing 0 6` … `bing 0 12` exactly, and say at which span it was last
> checked. An outward-spiral rule was drafted here and discarded: the draft failed at 5 of 170
> basepoints at span 7 and 201 of 986 at span 9, and its implementation was in any case faulty,
> so it is reported as a direction and not as evidence.

If the cover has no rule, that is the batch's result and worth the run: it would say the
construction must read the arms and cannot be tabulated, which narrows the remaining routes to
the cut of batch 29 §3.

## 2. The ordinary item

**notConstantOnBand.** Two interior basepoints of one chain served by no common walk. The
census of §1 supplies a pair as soon as the greedy cover needs two walks; take the smallest
chain where it does. The proof is then two applications of `not_oneTurn_of_opposite` if both
basepoints fall under it, or a reachability certificate of the kind `SpanWitness.lean` (batch
26) uses, over the finitely many walks of the band. *(supply: the enumeration of the band's
walks. The family is finite for fixed `L, H` — the turning levels lie in `[L+1, H−1]` and the
amplitudes strictly increase after the first — so this is a `decide` if the count is small
enough, and a certificate otherwise. Report which.)*

## 3. `s3ZigFreeInterior` — the search item

Search permitted. **A counterexample is a success; report it first.**

Whatever the census says, the two constraints stand: the reversal law (the walk's turn count
must grow like `⌊span/2⌋ − 1`, so no fixed family works) and no black-box extension hypothesis
(batch 27 §4). The tools are `foldsOnto_prefixLeg`, `isZigFree_cons`, `timing_slack'`,
`index_gap_of_level_gap'`, `armG_index_gap`, `armT_index_gap`, `isCrookedIvF_restrict`, and the
one-turn theorems with their limit.

## 4. Deliverables

1. **The §1 census, first**, with the cover tables and the verdict on whether a rule describes
   them.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report: the census; any counterexample to `s3ZigFreeInterior`; whether `notConstantOnBand`
   went by `decide` or by certificate.

## 5. Not in this batch

The linear-time far-index check for `¬ F2PrimeOff`; Bing 1948 Theorems 4, 5, 6; the reduction
in Bing 1951; the D8/D9 gap.
