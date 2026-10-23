# Commission: batch 22 — the faithful model, with a realization theorem

**Go!** Runs on top of the batch-20 delivery. One new file, `HPC/Fold/Faithful.lean`; root
`HPC.lean` updated. Nothing else touched. Every `sorry` is a work item; delivery contains none.

**Batch 21 is withdrawn.** It targeted `IsCrookedIv`, which this batch shows is not the
faithful model. Do not run it.

## Purpose

Twice now a model of crookedness at the level of sequences has been necessary but not
sufficient, and twice the witnesses that refuted the conjectures lived in the gap. The batch-20
model `IsCrookedIv` is the second instance. Its two omissions are geometric, and are derived
in §1 rather than guessed. This batch defines the corrected model `IsCrookedIvF`, proves that a
crooked chain lands in it, and — the point of the batch — **proves that every sequence in it is
realized by an explicit chain of open rectangles in `ℝ × ℝ`**, crooked in the 1948 sense, with
exactly the given minimal and maximal indices. After this, the model question cannot recur: a
sequence in `IsCrookedIvF` is a chain by construction, and any future counterexample refutes
Bing's statement, not a sequence statement.

Evidence over the corrected model, with attained extremes and the `hStar`/`lStar` witness:
all chains of length ≤ 8 on five levels, 955 268 basepoints, and random chains at lengths 14,
22, 30 on up to nine levels, 8 360 basepoints — no failure of `F2Prime`. The two batch-20
witnesses fail the model: both violate the adjacency condition at three places, and both fail
a forced-meeting crookedness hypothesis.

## Protocol

As batches 1–17 and 20: complete proofs supplied. The realization theorem is the one large
item; its construction is explicit and §3 gives every endpoint.

## 1. The two conditions, derived

Let `E` refine `D`; write `I(t) = [minIdx t, maxIdx t]` for the indices of coarse links
containing `E.link t`. Every index strictly between `minIdx` and `maxIdx` also contains the
link (a link inside `d_j` and `d_{j+1}` is inside both; there is nothing between), so `I(t)` is
exactly the set of containing indices.

**Adjacency.** `E.link t ∩ E.link (t+1) ≠ ∅`, and that intersection lies inside `d_j` for every
`j ∈ I(t) ∪ I(t+1)`. A nonempty set inside `d_j` and `d_{j'}` forces `|j − j'| ≤ 1` by the
chain axiom of `D`. So `I(t) ∪ I(t+1)` is pairwise adjacent, hence contained in two
consecutive indices: `max (σ t) (σ (t+1)) ≤ min (ρ t) (ρ (t+1)) + 1`. Batch 20's `adj` asked
only that the two intervals be within distance one, which admits `{a, a+1}` next to `{a+2}`.

**Forced meetings.** `E.link t ∩ E.link (t+1) ≠ ∅` and `E.link (t+1) ⊆ d_j` for `j ∈ I(t+1)`,
so `E.link t` meets `d_j`. Likewise on the left. Hence `E.link t` meets `d_j` for every
`j ∈ I(t−1) ∪ I(t) ∪ I(t+1)`, and `IsCrookedIn'` fires on each such meeting. Batch 20's
`crooked` fired only on `I(t)`.

Both conditions are necessary. §3 shows they are jointly sufficient.

## 2. Small lemmas

**IsCrookedIvF.isCrookedIv.** `adj` implies batch 20's weaker adjacency; `crooked` with the
witness `u := s` and `u := t` in the two existentials gives batch 20's clause.

**isCrookedIvF_minIdx_maxIdx.** `le`, `width` as in batch 20. `adj`: §1, with
`subset_adjacent_of_subset` applied to the intersection point and the two containing links.
`crooked`: given `u` within one of `s` with `h ∈ I(u)`, `E.link s` meets `d_h` — if `u = s` by
containment, if `u = s ± 1` because `E.link s ∩ E.link u ≠ ∅` (adjacent links) and
`E.link u ⊆ d_h`; likewise for `t`, `k`. Then `IsCrookedIn'` at `(h, k)` gives the witnesses
exactly as in batch 20.

## 3. The realization

Fix `ρ σ` in the model with `0 ≤ ρ` and `σ < M`.

**Strips.** `strip j = (j, j + 3/2) × ℝ`. Consecutive strips meet in `(j+1, j+3/2) × ℝ`; strips
two apart are disjoint since `j + 3/2 ≤ j + 2`. So `stripChain M` is a chain; openness is
`isOpen_Ioo.prod isOpen_univ`.

**The `x`-range of link `t`.** Write `a := ρ t`, `b := σ t`. The *core* is `(a + 1/8, b + 1)`
when `a = b`, i.e. `(a + 1/8, a + 1)`, which lies in `strip a` and meets no other strip; and
`(a + 9/8, a + 11/8)` when `b = a + 1`, which lies in `strip a ∩ strip (a+1)` and meets no
other. Then extend for the neighbours:

* if `t + 1 < n` and `σ (t+1) = b + 1` (the right neighbour touches `b + 1`), replace the right
  endpoint by `b + 11/8` — the range now reaches into `strip b ∩ strip (b+1)`, meeting
  `strip (b+1)` without lying in it (its left part is outside `strip (b+1)`);
* if `t + 1 < n` and `ρ (t+1) = a − 1`, or `t > 0` and `ρ (t−1) = a − 1`, replace the left
  endpoint by `a − 3/8`, reaching into `strip (a−1) ∩ strip a`;
* symmetrically on the right for the left neighbour.

By `adj`, a neighbour touches at most one index outside `I(t)`, and only an adjacent one, so
at most one extension on each side is ever required and never both in a direction that would
put the range inside a strip it should not lie in. *(supply: the case table — for each of the
five shapes of `(I(t−1), I(t), I(t+1))` that `adj` allows, the endpoints; and the check that
the resulting open interval lies inside exactly the strips indexed by `I(t)` and meets exactly
the strips indexed by `I(t−1) ∪ I(t) ∪ I(t+1)`.)*

**Lanes.** `linkRect t = linkX t × (t, t + 3/2)`. Consecutive lanes overlap in `(t+1, t+3/2)`;
lanes two apart are disjoint. So non-consecutive links are disjoint regardless of `x`, and
consecutive ones meet iff their `x`-ranges meet, which they do by construction: the extension
rule puts both ranges into the common overlap zone when their intervals differ, and both cores
lie in a common strip when they agree. *(supply: the `x`-overlap for each adjacency shape.)*
Hence `linkChain` is a chain.

**Refinement and indices.** `linkRect t ⊆ strip j` iff `linkX t ⊆ (j, j + 3/2)` iff
`j ∈ I(t)`, by the endpoint table. So `minIdx t = ρ t` and `maxIdx t = σ t`.

**Crookedness.** `IsCrookedIn'` for `(linkChain, stripChain)`: a hypothesis
`(linkRect s ∩ strip h).Nonempty` holds iff `h ∈ I(s−1) ∪ I(s) ∪ I(s+1)` by the endpoint table;
that is exactly the existential in `IsCrookedIvF.crooked`, which then supplies `r, r'` with
`k ∓ 1 ∈ I(r)`, i.e. `linkRect r ⊆ strip (k ∓ 1)`, and likewise for `r'`. `Between` from the
index order.

## 4. The witnesses

**ivSeq_not_faithful, lpivSeq_not_faithful.** Either condition suffices; adjacency is the
cheaper. `ivSeq`/`ivSig` at `t = 5`: intervals `(6,6)` and `(7,8)`, and
`max 6 8 = 8 > min 6 7 + 1 = 7`. `lpivSeq`/`lpivSig` at `t = 0`: `(5,5)` and `(6,7)`,
`7 > 6`. One `decide` or one `norm_num` each on the `adj` field.

## 5. The route

`F2PrimeF` is `F2PrimeIv` with `IsCrookedIvF` for `IsCrookedIv`. **theorem3_of_F2PrimeF**:
batch 20's `theorem3_of_F2PrimeIv` with `isCrookedIvF_minIdx_maxIdx` in place of
`isCrookedIv_minIdx_maxIdx`. The `ExitReach`/valley restatements and the assembly are deferred
to the conjecture batch to keep this one to the model.

## 6. Deliverables

1. Census.
2. The file compiled, every `sorry` discharged, `#print axioms` for every theorem.
3. Report: the endpoint table used in §3 and any adjustment to the constants `1/8, 3/8, 9/8,
   11/8`; what was supplied; any statement that did not go through. If the realization
   theorem does not go through as stated — in particular if some shape allowed by `adj` cannot
   be placed — report that first: it would mean `adj` is still too weak, and the model would
   need a third condition.

## 7. Not in this batch

The three conjectures over `IsCrookedIvF`, and the assembly `f2PrimeF_of_…`. They follow, under
the relaxed protocol, once the realization theorem is in.
