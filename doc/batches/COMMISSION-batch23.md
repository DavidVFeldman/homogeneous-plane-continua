# Commission: batch 23 — the three conjectures over the faithful model

**Go!** Runs on top of the batch-22 delivery. One new file, `HPC/Fold/ClosureF.lean`; root
`HPC.lean` updated. Nothing else touched.

## Protocol

Two ordinary work items with proofs supplied (§1). Then the three conjectures, as batches 18
and 19: search permitted, time unbounded, the English a sketch. Census, axiom audit, no silent
weakening. **A counterexample to any of the three is a success; report it first**, and check
it with `IsCrookedIvFCheck` — by `realization` it is then a chain. A run that proves none and
refutes none is legitimate; keep sound partials and say how far the search got.

## 1. The two ordinary items

**f2PrimeF_of_exitReachF.** Batch 20's `f2PrimeIv_of_exitReachIv` with `IsCrookedIvF` for
`IsCrookedIv`; the crookedness hypothesis is only passed through, as the batch-20 report
confirmed.

**IsCrookedIvF.isCrookedSeqUp.** Batch 20 proved `IsCrookedIv → IsCrookedSeq ρ` by
instantiating the clause at `h := ρ s`, `k := ρ t`. Instantiate instead at `h := σ s`,
`k := σ t` (witnesses `u := s`, `u := t` in the two existentials) and read the conclusions
`ρ r ≤ k ∓ 1 ≤ σ r ≤ ρ r + 1` as `σ r ∈ [k ∓ 1, k ∓ 1 + 1]`, the up-form window of batch 13
(`IsCrookedSeqUp`: near-target in `[f t − 1, f t]`, near-source in `[f s + 1, f s + 2]` for
ascending pairs — check the exact windows against `Symmetry.lean` and adjust which of `ρ r`,
`σ r` is read).

So a single faithful sequence carries the down form on `ρ` and the up form on `σ`, with
`σ − ρ ∈ {0, 1}`. Batch 13 showed the two forms pin different witnesses exactly: the down form
pins the near-target link, the up form the near-source. Together they give the Synchronization
Lemma in the combined form — across an upward exit and a downward exit with the window intact,
a link at exactly `p − 1` followed by one at exactly `p + 1`, or the reverse. This is the
sharpening §17 of the notes wrongly attributed to `maxIdx` alone; here it is legitimate, and
it is the tool the sketch for `ExitReachF` wants. State it as a lemma before using it.

## 2. What the conjectures say, and the evidence

The batch-16 statements with attainment, over `IsCrookedIvF ρ σ`. **The evidence is thinner
than in earlier batches, and honestly so:** the faithful model is much more restrictive than
the interval model (geometric adjacency alone cuts the exhaustive length-8 corpus on five
levels from 955 268 basepoints to 26 432), and random crooked chains are rare at length 24.
Over the faithful model with attained extremes: all chains of length ≤ 8 on five levels,
26 432 basepoints; random chains at lengths 16 and 24 on up to eight levels, 432 more. No
failure of `ExitReachF`, `HighExitValleyF`, `LowExitPeakF`, or `F2PrimeF`. Batch 22's own
census at length ≤ 7 agrees.

The earlier, larger corpora (batches 16–20) were over models now known to be strictly larger
than the class of chains; their zero-failure counts remain true of the subclass. Every
sequence that ever refuted a conjecture in this position lies outside the class.

## 3. Sketches

### `HighExitValleyF`

By batch 17 (`demands_lt_of_open`, `exists_drop_before_exceed`, `pre_drop_eq` — all stated for
`IsCrookedSeq`, which `IsCrookedIvF.isCrookedIv.isCrookedSeq` supplies), in the open case both
demands are below `H − 1`, the exceeding index `u` follows the first drop `d`, and the level
before `d` is `p − 1`. The mechanism (batch 19 §3): if `L` is attained on the exceeding arm at
`ℓ < u`, crookedness on the pair `(ℓ, u)` — gap `≥ 3` — gives a near-target witness at level
`≥ hStar`, hence at or past the peak index, followed by a near-source witness at `≤ L + 1`: the
visit. The sub-claim *`L` is attained on the exceeding arm before its exceeding index* was
refuted in batch 19 by a sequence now known to be no chain (`hvSeq'`), so it is open again over
this model. What the faithful model adds that the down form lacks: forced meetings fire
hypotheses at levels one beyond the link's own interval, so a link's neighbours contribute
pairs; this is the extra crookedness that separates chains from the refuting sequences, and it
should be looked for at exactly the place a sequence-model proof breaks.

### `LowExitPeakF`

Do not reflect a proof that uses crookedness (batch 13). But note: over the faithful model,
the *up* form is available on `σ`, and the reflection of the down form is the up form
(`isCrookedSeqUp_neg_iff`). So the reflected argument can be run on `σ` rather than on `−ρ`,
provided the argument's other ingredients (`hStar`, arms, phase) are transported with
`σ − ρ ∈ {0, 1}` accounted for. This is the first batch in which a legitimate reflection route
exists; report whether it was usable.

### `ExitReachF`

Batch 18 §3, with the combined Synchronization Lemma of §1 as the tool for the branch that
broke every earlier formulation — the arm that does *not* fail the Λ side. The floor
`min (L + 1) p` in `lStar` and the cap `max (H − 1) p` in `hStar` are what make the two sides
complementary, and only with attained extremes.

## 4. Deliverables

1. Census.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report, in this order: any counterexample, with its `σ` and its `IsCrookedIvFCheck`; which
   of the three were proved, with the actual mechanism; whether the combined Synchronization
   Lemma and the `σ`-side reflection were usable; for anything not proved, how far the search
   got.

## 5. If all three fall

`f2PrimeF` and `theorem3` follow by the lines in the skeleton, and Bing 1948 Theorem 3 in the
block reading is unconditional.
