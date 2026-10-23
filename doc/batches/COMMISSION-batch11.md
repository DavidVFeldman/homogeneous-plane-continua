# Commission: batch 11 — the Phase Lemma

**Go!** Runs on top of the batch-10 delivery. One new file, `HPC/Fold/Phase.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

Batch 10 left the dichotomy needing the two arms' demands to *agree*. Measurement shows they
need only agree within one: in every instance where the V family fails, the peak demands differ
by exactly one and the Λ family still works. The reason is the phase. This batch proves the
fact behind it — a crooked sequence cannot climb monotonically — and draws the consequence.

`Agreement` replaces `Exclusion` and `Balance` as the central conjecture and is recorded as a
definition. The residual small case is recorded as `SmallDemandCase`. Neither is proved here.

## Protocol

As batches 1–10. Expected: `IsCrookedSeq`, `NonAscAt`, `phase`, `phase_eq_one`,
`phase_zero_or_one`, `hStarArm`, `hStarArm_mem`, `lStarArm`, `hStar`, `lStar`, `SegLam`,
`SegVee`, `armG`, `armT`.

## 1. The Phase Lemma — proof

**exists_nonAsc_of_climb.** Let `A 0 = p` and `A j ≥ p + 3`, so `|A j − A 0| ≥ 3` and
`A 0 < A j`. Crookedness at `(0, j)` gives `0 < r < r' < j` with `A r` within the ascending
window of the target — `A j − 2 ≤ A r ≤ A j − 1` — and `A r'` within that of the source —
`p ≤ A r' ≤ p + 1`.

Then `A r ≥ A j − 2 ≥ p + 1 ≥ A r'`, with `r < r'`. So the sequence does not strictly increase
across `[r, r']`: there is an index `t` with `r < t ≤ r'` and `A t ≤ A (t−1)`, since otherwise
`A` would be strictly increasing on `[r, r']` and `A r < A r'`. That `t` is a non-ascending
step, and `t ≤ r' < j`.

*(supply: the step-extraction — if every step on `[r, r']` ascends strictly then `A r < A r'` —
by induction on `r' − r`. This is the only real content; the rest is unpacking
`IsCrookedSeq`.)*

Note the weakened `IsCrookedSeq` of batch 7 suffices: only the bounds `A r ≥ A j − 2` and
`A r' ≤ p + 1` are used, not the exact values.

**phase_eq_one_of_climb.** `phase A j = 1` iff some `t ≤ j` is a non-ascending step, which is
`exists_nonAsc_of_climb`.

## 2. The one-short lemma

**exists_peak_index_of_one_short.** Let `d := hStarArm A p`, and suppose `h − 1 ≤ d` and
`p + 3 ≤ d`. By `hStarArm_mem` there is `s` with `A s = d` and `p − 1 ≤ A j` for every
`j ≤ s`. Since `A s = d ≥ p + 3`, `phase A s = 1` by `phase_eq_one_of_climb`. Hence
`A s + phase A s = d + 1 ≥ h`. The second conclusion is the side condition from
`hStarArm_mem`.

This is the step the earlier batches lacked: an arm whose demand is one short of `hStar` still
reaches `hStar` in the phase-adjusted sense, provided its demand is at least `p + 3`. Combined
with `segLam_of_peak_before_drop` (batch 10) it gives `SegLam` for that arm.

## 3. The two recorded statements

`Agreement` and `SmallDemandCase` are definitions; nothing to prove.

`Agreement` is the conjecture the dichotomy needs. `SmallDemandCase` covers `hStar ≤ p + 3`,
where the one-short lemma does not apply because the climb is too short to force a reversal;
there the arms move within a band of four levels and the argument should be finite, but it has
not been done.

If either is **found false** while formalizing, report it in preference to anything else.

## 4. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: how the step-extraction was done; whether the weakened `IsCrookedSeq` sufficed
   throughout; what was supplied; any statement that did not go through.

## 5. Not in this batch

`Agreement`; `SmallDemandCase`; the assembly of these into `F2Prime`; Bing 1948 Theorems 4, 5,
6; the reduction in Bing 1951; the D8/D9 gap.
