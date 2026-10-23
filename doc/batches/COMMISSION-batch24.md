# Commission: batch 24 — the off-center family, Bing's chains, `F2PrimeOff`

**Go!** Runs on top of the batch-23 delivery. One new file, `HPC/Fold/OffCenter.lean`; root
`HPC.lean` updated. Nothing else touched.

## Protocol

Ordinary items (§3.1–3.3) with proofs supplied; adapt the skeleton's names to
`Itinerary.lean`'s actual signatures where they differ and say so. Then one search item,
`f2PrimeOff`, as batches 18–23: search permitted, time unbounded, sketch in §3.4. Census, axiom
audit, no silent weakening. **A counterexample to `F2PrimeOff` is a success; report it first**,
with its `σ` and `IsCrookedIvFCheck2`. A run that proves neither is legitimate.

## 1. Why this family

Every itinerary in batches 6–23 began at a window centered on `p`. At the refuting chains the
schedules that exist begin at a window with `p` on an edge: at basepoint 6 of `bing 0 4` the
three-level windows are centered `1, 3, 1, 0`, with `p = 2`. `SegLam`/`SegVee` are built around a
center at `p` and are retired; the statement is made through `FoldsOnto` directly.

## 2. Evidence, and where it comes from

Chains shorter than nine links never reach the inductive case of Theorem 3, and random walks
essentially never produce crooked chains of span ≥ 5. The evidence below is the first in this
project gathered at induction depth, all with attained extremes and three-level windows,
tested by reachability:

* `bing 0 n`, `n = 4 … 7` (13, 30, 71, 170 links; spans 5–8): every basepoint, no failure.
* 5 207 contiguous subchains of `bing 0 7` of length ≥ 9 and span ≥ 5, 361 126 basepoints: no
  failure. (Subchains of a crooked chain are crooked.)
* The two batch-23 witnesses, every basepoint: no failure. The 71-term one *is* `bing 0 6`.
* The faithful exhaustive corpus to length 8 (base case only): no failure.

The same family with two-level windows fails from `bing 0 4` on: two-link itineraries need
windows stepping by two, which the third level absorbs. Bing's two-link statement nonetheless
holds at every basepoint of `bing 0 4`, `bing 0 5`, `bing 0 6` by exhaustive search; it is not
what this batch claims.

## 3. Proofs and sketches

### 3.1 `theorem3_of_F2PrimeOff`

`hcr.1 : E.Refines D`; `ρ := minIdx`, `σ := maxIdx`, `IsLip ρ` from `minIdx_lip`, faithful
membership from `isCrookedIvF_minIdx_maxIdx`, `L`/`H` the attained minimum and maximum of `ρ`
(batch 9's construction). If `H < L + 3`: batch 9's degenerate branch (one or two blocks by
level). Otherwise `hF2` gives `c₀` and an itinerary `(len, c)` with both arms folding;
`exists_blocks_first_of_folds hcr.1 i len c hG hT` is the conclusion.

### 3.2 Bing's chains

**bingPath.** `decreasing_by`: in the recursive branches `|b − a| ≥ 3`, and each call has
distance `|b − a| − 1`, `|b − a| − 2`, `|b − a| − 1` respectively; `omega` after unfolding
`toNat`. **bingPath_length.** Induction on `(|b − a|).toNat`; base cases give `1, 2, 3` for
distance `0, 1, 2`; the step is `z (d−1) + (z (d−2) − 1) + (z (d−1) − 1) = z d` by the
recurrence, using `List.length_append`, `List.length_tail`, and that the pieces are nonempty.
**z_small.** `decide` or `rfl`. **bing04_faithful, bing05_faithful.** By
`IsCrookedIvFCheck2` and `decide`; batch 23 reports the full check is intractable at length 42,
so length 30 may need the cheaper criterion as well — if it does not evaluate, prove `bing 0 4`
only and report. **lpSeq_eq_bing06.** `decide` or `rfl` on the list.

### 3.3 The family

`offLam`/`offVee` return a length and a walk; nothing is asked about them here beyond being
well-formed. (If a lemma that their walks are 1-Lipschitz is convenient for §3.4, add it.)

### 3.4 `f2PrimeOff` — sketch

Bing's induction on the span `H − L`, in the sequence model, with the tracking step explicit.

*Base.* `H − L ≤ 4`: one window of three levels or the monotone walk.

*Monotone.* `ρ i ≤ L + 1` or `≥ H − 1`: the monotone walk from `c₀ = L + 1` or `H − 1`.

*Special case* (only the end links meet `L` or `H`, ends oriented `L … H`). Faithful
crookedness at the pair of ends gives `h′ < k′` with `H − 1 ∈ [ρ h′, σ h′]`,
`L + 1 ∈ [ρ k′, σ k′]`. Subcase `i ≤ h′`: induction on `[0, h′]` with range `[L, H − 1]` yields a
fold of both arms of that segment onto a member of the family for the sub-range; the member is
extended past its peak by the descent to `L + 1` and the climb to `H − 1`, and the remainder
`h′ + 1 … n − 1` — which by construction descends from near `H − 1` to `L + 1` and then climbs to
`H` — folds onto that extension by Lemma F1's peak-window criterion. Subcase `k′ ≤ i`:
reflection of the statement (not of a crookedness proof; the family and `FoldsOnto` are
symmetric under negation and reversal). Subcase `h′ < i < k′`: induction on `[h′, k′]` with
range `[L + 1, H − 1]` — **this is where the batch-24 implementation of Bing's construction
fails and where the sketch is least certain.** The lesson from `bing 0 4`, basepoint 6: the
sub-fold must use the *global* top window, and the two tails then fold onto the *same*
extended itinerary in opposite directions — one climbing to `H`, one descending to `L` — which
is possible for the off-center family because its two ends are the two extremes. Concretely:
take the sub-fold's itinerary, replace its peak (or valley) by the global one, and show each
tail folds onto the tail of the itinerary beyond the point where the sub-fold left it; that is
a peak-window criterion applied to a crooked tail, i.e. Lemma F1 with the tail as the arm.

*General case.* Maximal segment around `i` with no interior link meeting `L` or `H`; special
case there; the outer tails are absorbed as in the middle subcase.

Expect the middle subcase to be the whole difficulty. The corpus of §2 can be consulted for
any sub-claim; `bing 0 n` and its subchains are available on demand at any span.

## 4. Deliverables

1. Census.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report: any counterexample; whether `bing05_faithful` evaluated; for `f2PrimeOff`, which
   cases went through, and for the middle subcase what the tracking step needed.

## 5. If `f2PrimeOff` falls

`theorem3` follows, and Bing 1948 Theorem 3 in the block reading is unconditional.
