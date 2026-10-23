# Commission: batch 36 — shortest serving walks, gated

**Go!** Runs on top of the batch-35 delivery. One new file, `HPC/Fold/Minimal2.lean`; root
`HPC.lean` updated. Nothing else touched. **§1 is a gate: run it before writing Lean.**

## 0. On batch 35

Audited clean: forty-three earlier files identical.

**The commissioned `CutData` was empty and the batch proved it with no hypotheses.** `atR` asked
for `ρ r ≥ H − 1` while `bandA` asked for `ρ j ≤ H − 2` over a range including `j = r`; likewise
at the bottom. That is not a subtle error and it should have been caught before the commission
went out, by instantiating the structure on `cutSeq` — which is exactly what the batch did.
Reporting the emptiness first, then tracing it through `exists_cutData` (false, with satisfiable
hypotheses), `cutData_spans` (vacuously true), `cutWalk` (provable in three lines by vacuity) and
`s3ZigFreeInterior_of_cutWalk` (equivalent to the goal), is the right disposal, and
`s3ZigFreeInterior_iff_cutWalk_imp` is the honest way to say that last one.

**The premise of the route change was also false, and that is the substantive finding.** I wrote
that the cut's stretches are "two narrower than the ambient". They are narrower at one end only;
`isZigFree_append_outer'` needs strictly inside at both. The first stretch contains the bottom
index itself, so batch 34's obstruction applies verbatim — `no_outer_member_of_boundary_trim`,
and the census finding that the first stretch has a level at `L` in **every** one of 2 376 400
cuts at span ten. And with the only repair available, the cut's core is a *worse* trim than batch
34's: it fails the weak form already at span six, where batch 34's trims passed it everywhere.

`cutWalk'_iff_s3ZigFreeInterior` states the verdict exactly: the route adds data, not strength.

Two lasting pieces: the corrected `CutData'` with `exists_cutData'`, and the reversal symmetry
`isCrookedIvF_revSeq` and `s3ZigFreeInterior_arms_rev`, which were not available and are wanted
independently.

## 1. The gate

Batch 34 refuted the step in the "every serving walk extends" form and proved the mechanism:
`no_fold_of_early_low` — the inner member's targets lie at `L + 2` or above, a fold pins time
zero and moves the token one time per link, so an arm reaching `L` early cannot be folded. That
names the culprit: the inner walk is **too long**.

Measured here, over the inner trims of batch 34 (bands strictly inside `[L, H]`, at least three
wide, maximal stretch containing the basepoint): at every interior basepoint of `bing 0 6`,
`bing 0 7` and `bing 0 8` there is a trim for which **every shortest serving walk extends** —
25 of 25, 104 of 104, 319 of 319. The failures of the unrestricted "every" form are all at longer
walks.

> **Census `ExtendStepMin` at spans 9, 10, 11 and 12 — every interior basepoint of `bing 0 n` —
> before any of §§2–3. If it fails, stop, report the failing basepoint with its trims and the
> shortest serving walk that does not extend, and deliver nothing else.**

Also report, if it holds, whether the *unique* shortest walk is ever needed — that is, whether
there are basepoints where some shortest serving walk extends and another does not, at every
trim. That would distinguish "shortest" from "some shortest" and matters for §2.

## 2. Why no strengthening of the statement is needed

The family of a fixed band is finite: turning levels lie in `[L+1, H−1]`, and the amplitudes
strictly increase after the first, so both the number of targets and each amplitude are bounded
by the span. Hence from the induction hypothesis's walk a *shortest* serving walk exists, and the
step need only extend those. This is what `finite_isZigFree` and `exists_shortest_serving` are
for, and it is why `S3ZigFreeInterior` can be proved as it stands rather than replaced by a
stronger statement — which is what the last three batches kept trying to do.

**finite_isZigFree.** A member is determined by its list of targets; the list has length at most
`H − L` (amplitudes are positive, strictly increasing after the first, and bounded by `H − L − 2`)
and each entry lies in `[L+1, H−1]`. So the set injects into lists of bounded length over a
finite set. *(supply: the bound on the number of targets. If it is easier to bound the length by
the walk's length instead, do that and say so.)*

**exists_shortest_serving.** A nonempty set of naturals — the lengths `(zigWalk ts).1` of serving
members — has a least element; take a member attaining it. Needs `finite_isZigFree` only if the
argument goes through the finite set; `Nat.find` on the predicate "some serving member has walk
length `k`" avoids it, and is probably shorter. Report which was used.

**s3ZigFreeInterior_of_extendStepMin.** Strong induction on `(H − L).toNat`, as
`s3ZigFreeInterior_of_extendStepZF` (batch 34), with one change: after the induction hypothesis
supplies a serving walk for the inner stretch, apply `exists_shortest_serving` to replace it by a
shortest one before invoking the step. The hypothesis `L + 6 ≤ H` makes the base vacuous, as
batch 34 found. The interiority case split and its `s3ZigFree_near_extreme` branch are unchanged.

## 3. `extendStepMin` — the search item

Search permitted. **A counterexample is a success; report it first** — §1 will already have found
it if it is at span twelve or below.

No mechanism is sketched. Three have been sketched in the last three batches and all three were
wrong: a quantifier that collapsed the statement, a trim that could not be appended to, and a
structure that was empty. The record's constraints are in batch 35 §3 and are unchanged, with one
addition: `no_fold_of_early_low` is not only an obstruction to respect but the reason the length
restriction is the right one, so a proof should be expected to use it.

## 4. Deliverables

1. **The §1 census, first**, with its verdict and the uniqueness question.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report: the §1 result; any counterexample; whether `finite_isZigFree` went by the target
   bound or another route; how far `extendStepMin` got.

## 5. Not in this batch

The linear-time far-index check for `¬ F2PrimeOff`; Bing 1948 Theorems 4, 5, 6; the reduction in
Bing 1951; the D8/D9 gap.
