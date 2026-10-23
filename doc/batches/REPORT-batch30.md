# Report: batch 30 — Bing's Theorem 7, and the timing bound

One new file, `HPC/Fold/Minimal.lean`; root `HPC.lean` updated with its import; `README.md`
updated. Nothing else touched. The whole project builds. The new file has no `sorry`, `admit`,
`axiom`, `native_decide` or `@[implemented_by]`, and no linter warnings; every theorem in it has
axiom profile inside `propext`, `Classical.choice`, `Quot.sound`. The census program is
`census-batch30.c`, its output `census-batch30.log`.

## 1. No counterexample to `Minimality` — it is a theorem

**`Minimality` is proved**, in full, at every span, with no extra hypothesis:
`HPC.Fold.minimality`. A faithful crooked sequence whose levels fill `[L, H]` has at least
`z (H − L)` terms. Since `bingPath` (batch 24) has exactly `z (H − L)` terms
(`bingPath_length`), the bound is attained: this is Bing 1948 Theorem 7 and its sharpness
together.

The proof is the commission's §3, with one change that makes the induction close, and the change
is the whole content of the thing.

**Measure the gap with the intervals, not with `ρ`.** The statement that carries the induction is
`minGap`:

> if one link of a faithful crooked sequence meets coarse level `l` and another, distinct, link
> meets `l + d`, then the sequence has at least `z d` links.

"Meets" here is `ρ u ≤ l ≤ σ u` — the link's own interval of coarse indices, not just its lower
end. This matters exactly where the commission's sketch stalls. At the pair of links meeting `l`
and `l + d` the crookedness clause returns `r` before `r'` with `r` meeting `l + d − 1` and `r'`
meeting `l + 1`. In terms of `ρ` alone the first stretch only gets from `l` to `l + d − 2`; in
terms of intervals it gets from `l` to `l + d − 1`. So the three stretches

* from the low link to `r`: levels `d − 1` apart,
* from `r` to `r'`: levels `d − 2` apart,
* from `r'` to the high link: levels `d − 1` apart,

overlap in exactly two links, and strong induction on `d` gives
`2·z (d−1) + z (d−2) − 2 = z (d)` links — Bing's recurrence, read backwards, term for term. The
base cases are `d = 0, 1` (one and two links, the latter from the two links being distinct) and
`d = 2`, where the adjacency clause of the faithful model forbids the two links from being
neighbours, so three links are needed. The two index orders — low link before high, or after —
are handled by the two implications of the crookedness clause; they are mirror images.

Bing's own recursion `P(a,b) = P(a,b∓1) · P(b∓1,a±1) · P(a±1,b)` is visible in those three
stretches, and the `− 2` of the recurrence is the two shared junctions `r`, `r'`.

`Minimality` as commissioned follows at once: the two extremes are met by `ρ` itself, and they
are distinct links as soon as `L < H`; when `L = H` the bound is `z 0 = 1`.

The commission's caution about batch 27 §2 was well placed and did not bite: the three pieces
here are bounded *below* in span, which is what `crookedIvF_cut_first`'s direction supplies, and
no piece is claimed to have strictly smaller span in the sense batch 27 refuted. In the event the
cut used is the raw crookedness clause of the model rather than `crookedIvF_cut_first`, since the
first-crossing refinement is not needed once the intervals are used.

## 2. The ordinary items

All four went through as stated.

* **`z_ge_of_le`, `z_gt_linear`.** From the recurrence, with `z_pos`. `z` is monotone because
  `2·z(n+2) + z(n+1) − 2 ≥ z(n+2)` whenever both terms are positive, and `2 d ≤ z d` for `d ≥ 3`
  by two-step induction off `z 3 = 6`, `z 4 = 13`.
* **`isCrookedIvF_restrict` went through exactly as stated.** The transfer is direct and the
  commission's worry about the neighbour just outside the stretch does not arise in this
  direction: a forced-meeting witness for the *restricted* sequence is in particular a witness
  for the ambient one, and the two indices the ambient clause returns lie strictly between the
  endpoints of the stretch, hence inside it. Only the index arithmetic had to be supplied. This
  lemma is now available to the earlier censuses that assumed restriction silently.
* **`index_gap_of_level_gap`.** Proved, in the commissioned form, and also as
  `index_gap_of_level_gap'` with the hypotheses the proof does not need dropped — neither
  `Minimality`, which is now a theorem, nor the Lipschitz clause, which the model forces
  (`IsCrookedIvF.isLip`, also new here). The route is `minGap` applied to the stretch from `s` to
  `t` through `isCrookedIvF_restrict`, rather than through the min/max of `ρ` on the stretch; the
  gap between the two endpoint levels is available directly, so the detour through the extremes
  of the stretch is unnecessary.
* **`timing_slack`.** Proved, commissioned form and unconditional form `timing_slack'`. The
  bound actually available is `2 (H − L) − 1` — `z d ≥ 2 d` — of which the commissioned
  `H − L − 2` uses less than half.

## 3. Census

`census-batch30.c`, output in `census-batch30.log`. Everything below is a check of a theorem
now proved; nothing contradicts it.

**Bing's chains.** `bingPath 0 n` for `n = 3 … 8` has lengths 6, 13, 30, 71, 170, 409 — exactly
`z 3 … z 8` — is faithful and crooked in the model at each `n`, and every one of its pairs of
indices at level distance `d ≥ 3` (1, 7, 45, 290, 1921, 12829 pairs respectively) is at least
`z d − 1` apart. No exception.

**Subchains.** 800 random contiguous subchains of each of `bing 0 4 … bing 0 8`: every one is
faithful and crooked — the restriction lemma, checked — and no pair violates the gap bound.

**Shortest sequences, exhaustively.** Over *all* faithful crooked sequences with `ρ` confined to
`[0, span]` and both ends attained, by iterative deepening with the crookedness clause used as a
prune: the shortest has 2, 3, 6, 13 terms at spans 1, 2, 3, 4, against `z 1 = 2`, `z 2 = 3`,
`z 3 = 6`, `z 4 = 13`. The span-4 witness is
`ρ = 0 1 1 1 2 2 2 1 2 2 2 3 4`, `σ = 0 1 2 1 2 3 2 1 2 3 2 3 4`, found after 34 364 205 nodes,
and every contiguous stretch of it is again faithful and crooked. At span 5 the target is
`z 5 = 30` and exhaustion to depth 29 is out of reach; the search was run to a budget of
120 000 000 nodes at depth at most 20 instead, and found nothing — a partial check only, and
reported as such in the log.

## 4. What this closes, and what it does not

`no_zigWalk_fold_veeSeq` (batch 29) exhibited a sequence — the straight descent
`6,5,4,3,2,1,0` — with no walk of unit steps at all, and said that the interior of `S3ZigFree`
cannot be settled without crookedness. `timing_slack` says that obstruction cannot arise inside
the model: between a link at `L` and a later link at `H` a faithful crooked sequence has at
least `2 (H − L) − 1` indices, while a unit-step walk needs `H − L − 2`. The token has slack,
at every span. Turning slack into a walk is the interior case of `S3ZigFree`, and it is not in
this batch.
