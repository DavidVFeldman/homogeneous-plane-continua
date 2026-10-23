# Commission: batch 7 — the Synchronization Lemma

**Go!** Runs on top of the batch-6 delivery. One new file, `HPC/Fold/Sync.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

## Purpose

The dichotomy that Bing 1948 Theorems 3 and 4 were to rest on (Lemma F2 of the project notes)
is false; a counterexample is on record. Its replacement (F2′) is not yet proved. This batch
proves the fact that every version of the dichotomy needs and that is elementary: crookedness
forbids the two arms of a chain from leaving the window around the basepoint's level in
opposite directions without a wiggle in between.

Verified against brute force on 2 977 090 basepoints (all crooked sequences of length ≤ 12 on
six levels, plus random crooked sequences up to length 56): no exceptions.

## Protocol

As batches 1–6. Batch-4 results expected: `Chain.Refines.minIdx`, `minIdx_subset`,
`minIdx_le`, `minIdx_near_of_inter`, `subset_adjacent_of_subset`. Batch-1: `Chain.Between`,
`Chain.IsCrookedIn'`, `Chain.link_nonempty`.

## 1. Definition

`IsCrookedSeq f`: for `s < t` with `3 ≤ |f t − f s|`, there are `s < r < r' < t` with `f r`
the value adjacent to `f t` on the side of `f s`, and `f r'` the value adjacent to `f s` on
the side of `f t`. (Ascending case: `f r = f t − 1`, `f r' = f s + 1`. Descending case:
`f r = f t + 1`, `f r' = f s − 1`.) This is the 1948 condition transported to levels.

## 2. Statements

`sync`, `sync'` (mirror), `no_immediate_opposite_exit`, `sync_dip`, and `isCrookedSeq_minIdx`.

## 3. Proofs

**sync.** `f u = p + 2`, `f v = p − 2`, so `|f v − f u| = 4 ≥ 3` and `f v < f u`. Apply
`IsCrookedSeq` at `(u, v)`: there are `u < r < r' < v` with `f r = f v + 1 = p − 1` and
`f r' = f u − 1 = p + 1`. Take `j := r`, `k := r'`. The hypothesis `hmid` is not needed for
this statement — it is carried because the corollaries use it and because it records the
intended situation (the two exits are the *first* ones, so everything between stays in the
window). *(supply: if the formalization finds `hmid` genuinely unused, keep it and mark it
with a leading underscore, noting this in the report.)*

**sync'.** Same with the ascending case of `IsCrookedSeq`: `f r = f v − 1 = p + 1`,
`f r' = f u + 1 = p − 1`.

**no_immediate_opposite_exit.** `a < b` since `a.val + 4 = b.val`. Apply `sync` with
`u := a`, `v := b`, giving `a < j < k < b` with `f j = p − 1` and `f k = p + 1`. But the only
index strictly between `a` and `b` other than `i` are the two neighbours of `i`; more simply,
`j < k` with both strictly between forces `b.val − a.val ≥ 3`, which holds, so use `hmid`
and the levels: `f i = p` by `hfi`, so `i ∉ {j, k}`. The indices strictly between `a` and `b`
are `a+1`, `i`, `i+1`. So `{j, k} ⊆ {a+1, i+1}` with `j < k`, forcing `j = a+1`, `k = i+1`,
hence `f (a+1) = p − 1`. But `f a = p + 2` and `f` is not assumed Lipschitz here — **so add
the Lipschitz hypothesis** `hlip : ∀ s t : Fin n, t.val = s.val + 1 → |f t − f s| ≤ 1` to this
theorem's statement and derive the contradiction from `|f (a+1) − f a| = |p − 1 − (p + 2)| = 3`.
Record the added hypothesis in the report.

**sync_dip.** Immediate from `sync`.

**isCrookedSeq_minIdx.** Let `s < t` with `|minIdx t − minIdx s| ≥ 3`. Put `h' := minIdx s`,
`k' := minIdx t`. `E.link s ⊆ D.link h'` and `E.link t ⊆ D.link k'` (`minIdx_subset`), so both
meet the respective coarse links (`link_nonempty`). Since `|h' − k'| ≥ 3 > 2`, the
`IsCrookedIn'` hypothesis applies to the pair `(h', k')` and the links `s, t`, giving `r, r'`
with `Between s r r' t` and `E.link r ⊆ D.link (k' ∓ 1)`, `E.link r' ⊆ D.link (h' ± 1)`. From
`minIdx_le` and `subset_adjacent_of_subset`, `minIdx r` equals `k' ∓ 1` or is adjacent to it;
**this is where the conversion may lose a unit**, since `minIdx r ≤ k' ∓ 1` with equality only
if no smaller coarse link contains `E.link r`. *(supply: prove what is true. If the exact
values `f r = f t ∓ 1` cannot be had and only `|f r − f t| ≤ 2` is available, weaken
`IsCrookedSeq` to that form throughout the file — adjusting `sync` to conclude
`f j ≤ p` and `f k ≥ p` in place of the exact values, and `no_immediate_opposite_exit`
accordingly — and record the weakening. The corollaries the project needs are the ordering
and the exclusion of immediate opposite exits, both of which survive the weaker form.)*

`Between s r r' t` gives `s < r < r' < t` in the orientation `s < t`.

## 4. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: the two directed changes (Lipschitz hypothesis on
   `no_immediate_opposite_exit`; any weakening of `IsCrookedSeq` forced by
   `isCrookedSeq_minIdx`), what was supplied, and any statement that did not go through.

## 5. Not in this batch

F1′ (folding onto the one-bump itinerary), F2′ (the corrected dichotomy), Bing 1948
Theorems 3–6, the reduction, the D8/D9 gap.
