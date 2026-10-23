# Commission: batch 13 — upward and symmetric crookedness

**Go!** Runs on top of the batch-12 delivery. One new file, `HPC/Fold/Symmetry.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

Batch 12 established that `IsCrookedSeq` is preserved by reversing a sequence but not by
negating it, because `minIdx` is a minimum and every transported bound sits one unit low. Two
consequences, both addressed here.

The unsoundness: any argument "by reflection" is invalid for statements taking crookedness as
a hypothesis. `MixedGap` is such a statement, and its natural proof wants exactly that
reflection.

The opportunity: transporting through `maxIdx` instead displaces every bound one unit *up*,
and under the upward form the Synchronization Lemma becomes **exact** — a link at `p − 1`
followed by one at exactly `p + 1`, where `IsCrookedSeq` yields only `p − 1` followed by
something `≥ p`. That sharpening is what `MixedGap` appeared to need.

## Protocol

As batches 1–12. Expected: `IsCrookedSeq`, `sync`, `revSeq`, `isCrookedSeq_revSeq`,
`Chain.Refines.maxIdx`, `maxIdx_subset`, `le_maxIdx`, `subset_adjacent_of_subset`,
`Chain.link_nonempty`, `Chain.IsCrookedIn'`, `hStarArm`, `lStarArm`, `armG`, `armT`.

## 1. The three notions

For `s < t` with levels differing by at least three, all three ask for `s < r < r' < t`; they
differ only in where `f r` and `f r'` may sit. Ascending case (`f s < f t`):

| | `f r` | `f r'` |
|---|---|---|
| `IsCrookedSeq` (minIdx) | `[f t − 2, f t − 1]` | `[f s, f s + 1]` |
| `IsCrookedSeqUp` (maxIdx) | `[f t − 1, f t]` | `[f s, f s + 1]` |
| `IsCrookedSeqSym` | `[f t − 2, f t]` | `[f s, f s + 2]` |

Descending case: mirror each row. Note the `f r'` column agrees for the first two in the
ascending case and differs in the descending one; this asymmetry is why neither is
negation-symmetric.

## 2. Implications and symmetries

**IsCrookedSeq.sym, IsCrookedSeqUp.sym.** Widen the intervals; the same witnesses serve.

**IsCrookedSeqSym.neg.** Put `g := −f`. Then `g s < g t` iff `f t < f s`, so the ascending case
for `g` is the descending case for `f`, which gives `f r ∈ [f t, f t + 2]` and
`f r' ∈ [f s − 2, f s]`; negating, `g r ∈ [g t − 2, g t]` and `g r' ∈ [g s, g s + 2]` — exactly
the ascending case for `g`. The descending case is the same computation the other way. The
slack of two on each side is what makes this close; with slack one it does not.

**IsCrookedSeqSym.rev.** As batch 12 proved for `IsCrookedSeq`: reversal exchanges the
ascending and descending cases *and* exchanges the two witnesses, `r ↦ n − 1 − r'`,
`r' ↦ n − 1 − r`, and under that double exchange the bounds match. Lift batch 12's
`isCrookedSeq_revSeq` argument rather than reproving if it factors.

**not_isCrookedSeq_neg.** A witness that the displaced form really is not negation-symmetric.
Any explicit short sequence will do; find one by taking a sequence whose only gap-3 pair forces
`f r'` to sit at `f s + 1` and checking that the negated sequence needs `f r'` at `g s − 1`,
outside `[g s − 2, g s − 1]`. *(supply: the sequence. If a search is easier than a
construction, run one over short sequences; report the witness found.)*

## 3. Transport through `maxIdx`

**isCrookedSeqUp_maxIdx.** Let `s < t` with `|maxIdx t − maxIdx s| ≥ 3`; write `h' := maxIdx s`,
`k' := maxIdx t`. `E.link s ⊆ D.link h'` and `E.link t ⊆ D.link k'` (`maxIdx_subset`), and both
links are nonempty, so both meet those coarse links and `IsCrookedIn'` applies to the pair
`(h', k')`. It gives `r, r'` between `s` and `t` with `E.link r ⊆ D.link (k' ∓ 1)` and
`E.link r' ⊆ D.link (h' ± 1)`.

Now the key step, and the whole point of the batch. From `E.link r ⊆ D.link (k' − 1)` and
`le_maxIdx`, `maxIdx r ≥ k' − 1`. From `maxIdx_subset` and `subset_adjacent_of_subset`,
`|maxIdx r − (k' − 1)| ≤ 1`, so `maxIdx r ≤ k'`. Hence `maxIdx r ∈ [k' − 1, k']`, which is
`[f t − 1, f t]` — one higher than the `[f t − 2, f t − 1]` that `minIdx` gives, because
`le_maxIdx` bounds from below where `minIdx_le` bounds from above. Same for `r'` at the other
end. *(supply: the orientation bookkeeping, as in batch 7's `isCrookedSeq_minIdx`.)*

## 4. The sharpened Synchronization Lemma

**sync_up.** `f u = p + 2`, `f v = p − 2`, so the descending case applies with source `u`,
target `v`, and gap `4`. `IsCrookedSeqUp` gives `f r ∈ [f v, f v + 1] = [p − 2, p − 1]` and
`f r' ∈ [f u − 1, f u] = [p + 1, p + 2]`. Now `hmid` pins both: `f r ≥ p − 1` forces
`f r = p − 1`, and `f r' ≤ p + 1` forces `f r' = p + 1`.

Compare batch 7's `sync`, where the second witness only satisfied `f r' ∈ [p, p + 1]` and
`hmid` could not pin it. The exactness here comes entirely from the upward displacement.

**sync_up'.** The ascending case, symmetrically.

**sync_sym.** The same argument under `IsCrookedSeqSym`, where the slack of two leaves
`f j ≤ p` and `p ≤ f k` and nothing sharper. Stated because it is the version safe to reflect.

## 5. `MixedGap` restated

`MixedGapUp` and `MixedGapUp_witnesses` are definitions; nothing to prove. The second records
the shape of the intended proof: in the residual configuration one arm's first exit from
`[p − 1, p + 1]` is upward and the other's is downward, with everything between inside the
window, so `sync_up` applies with those two exits as witnesses. Establishing that the
witnesses exist — that is, deriving `MixedGapUp_witnesses` from the two gap hypotheses — is
the next batch's work, not this one's.

## 6. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: the witness found for `not_isCrookedSeq_neg`; whether `IsCrookedSeqSym.rev` factored
   through batch 12's reversal argument; what was supplied; any statement that did not go
   through.

## 7. Not in this batch

`MixedGapUp` and `MixedGapUp_witnesses`; `SmallDemandCase`; `HighExitValley`; the assembly into
`F2Prime`; Bing 1948 Theorems 4, 5, 6; the reduction in Bing 1951; the D8/D9 gap.
