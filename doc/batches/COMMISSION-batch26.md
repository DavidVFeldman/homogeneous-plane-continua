# Commission: batch 26 — `S3`, the folding statement with the itinerary existentially quantified

**Go!** Runs on top of the batch-25 delivery. One new file, `HPC/Fold/Span.lean`; root
`HPC.lean` updated. Nothing else touched.

## 0. Read this first

Batch 25's counterexample is correct and its faithfulness proof is a good technique. This
commission reports a second counterexample, found after that delivery, which closes the route
batch 25 proposed to repair.

**`F2PrimeOff` is false.** The batch-25 census scored `OffDichotomy` on `bing 0 10` but scored
`F2PrimeOff` itself only through `bing 0 9`. Scored on all 2 379 basepoints of `bing 0 10`
(faithful, `σ = ρ`, `L = 0`, `H = 10`), it fails at **eight** basepoints — 343, 347, 349, 351,
2027, 2029, 2031, 2035, all of level 5. Spans 8 and 9 are clean. So batch 25 §4's repair —
keep the family, restore the free peak and valley — is not available: the free peak and valley
are already in `F2PrimeOff`, and `F2PrimeOff` is what fails.

**Why, measurably.** For a basepoint, let `k` be the least number of turning targets of an
itinerary onto which both arms fold, with the base centre free in `{p−1, p, p+1}`, the turning
levels free in `[L+1, H−1]`, and directions alternating. The maximum of `k` over basepoints:

| span | 4 | 5 | 6 | 7 | 8 | 10 |
|---|---|---|---|---|---|---|
| max `k` | 1 | 1 | 2 | 2 | 3 | 4 |

This is `⌊span/2⌋ − 1` (spans 4–7 exhaustive over `bing 0 n`; spans 8 and 10 sampled, including
every known failure). `offLam` and `offVee` are the case `k = 3`, which is exactly why they
hold through span 9 and fail at span 10. **The number of reversals grows linearly with the
span, so no family of itineraries with a bounded number of turning points can witness Theorem
3.** Do not propose one, and do not accept a statement that names a shape.

Anatomy at basepoint 343 (`p = 5`; forward arm 2 036 links with maximum 10 and minimum 1;
backward arm 344 links with maximum 7 and minimum 0). On each of the thirty members of the
family exactly one arm fails. The instructive near-miss is `offVee c 2 0 10` for
`c ∈ {4, 5, 6}`: the forward arm folds, and the backward arm fails only at its **last** index,
where it is at level 0 and needs a centre within one of 0, while the V shape puts a sweep to
level 9 between the valley and that final descent, and the backward arm's maximum is 7. The
least itinerary that works is `5 → 2 → 7 → 1 → 9`, whose two intermediate turns are interior
levels. Two-bump families that sweep between the extremes fail at all eight basepoints; all
four alternating shapes were tested.

Provenance: two implementations with different traversal orders — forward set-reachability and
backward boolean dynamic programming — agree on every itinerary of every basepoint tested, with
the family transcribed from the delivered `offLam`/`offVee` rather than reconstructed; the
faithfulness of `bing 0 10` was re-checked independently by the far-index method of batch 25
§3. This is a finite computation, not a proof; §3 asks for the Lean version.

## 1. The target

`S3`: from any basepoint of a faithful crooked sequence with attained extremes, both arms fold
onto a common itinerary — `∃ len c, FoldsOnto (armG ρ i) len c ∧ FoldsOnto (armT ρ i) len c`.
Nothing about `c` is prescribed. Batch 6's `exists_blocks_first_of_folds` already takes an
arbitrary `len` and `c`, so `theorem3_of_S3` is that lemma applied to `minIdx`, with
`isCrookedIvF_minIdx_maxIdx` for the hypothesis and batch 9's degenerate branch below
`L + 3 ≤ H`.

## 2. Ordinary items

**theorem3_of_S3.** As `theorem3_of_F2PrimeOff` (batch 24), with `hS3` in place of `hF2` and
the itinerary taken from its conclusion.

**s3_of_f2PrimeOff.** One `obtain` and one `exact`: a member of the one-bump family is an
itinerary. Recorded so that batches 24–25 are visibly subsumed.

**s3_span_five.** From batch 25's `f2PrimeOff_span_five`, through `s3_of_f2PrimeOff`'s
argument applied pointwise.

**foldsOnto_iff_foldsFrom, foldsFrom_extend, foldsFrom_split.** `FoldsFrom` is `FoldsOnto` with
the start time prescribed. The first is definitional. The second rebuilds the same `β`; the
window condition is unchanged because `β j < len` and `c'` agrees below `len`. The third glues:
take `β` on `[0, s]` from `hpre` and `β'` on `[s, m)` from `hsuf`, and define `β j` as the
first for `j ≤ s` and the second for `j ≥ s`; the two agree at `s` (both give `u₁`), so the
Lipschitz condition holds across the seam and the window condition holds by cases. *(supply:
the index arithmetic; `Fin.lt_or_ge` on `j.val` and `s`.)*

## 3. A second counterexample, if it will evaluate

`¬ F2PrimeOff`, at basepoint 343 of `bing 0 10`. The failure at the basepoint is thirty
instances of `¬ FoldsOnto`, each of which needs a certificate that no Lipschitz `β` exists —
harder than batch 25's `¬ BottomOnTime`, which was a level-and-index inequality. Two routes:

* Prove `¬ FoldsOnto f len c` from a *cut*: an index `j` and a set `S` of times such that every
  time reachable at `j` lies in `S` and no `u ∈ S` has `|f (j+1) - c u'| ≤ 1` for any `u'`
  within one of `u`. The forward reachability computation supplies `S` and `j` for each of the
  thirty members; the sets are small (at most `len ≤ 23` elements).
* Or a level argument for the members where one exists: for every Λ member the backward arm
  must reach a centre within one of `H − 1 = 9` to pass the final ascent, and its maximum is 7.
  This disposes of the Λ half cheaply; the V half needs the cut.

The faithfulness of `bing 0 10` — 2 379 links, span 10 — by the batch-25 method is
`2379 × 11 × 11` checks against `409 × 9 × 9`, roughly nine times the work of a four-minute
evaluation. **If it does not evaluate, state `¬ F2PrimeOff` with faithfulness as an explicit
hypothesis, exactly as batch 25 first did, and say so.** Skipping this item entirely is also
acceptable; report which.

## 4. `s3` — sketch

Induction on the span `H − L`. Base `H ≤ L + 5`: `s3_span_five`.

Step. Bing's Theorem 3 argument, in the sequence model. Let `a` be an index attaining `L` and
`b` one attaining `H`. Faithful crookedness at the pair `(a, b)` gives `a < r < r' < b` (or the
reverse order) with `ρ r` within one of `H − 1` and `ρ r'` within one of `L + 1`. These cut the
sequence into three pieces, each of which stays within a band of span at most `H − L − 1`:
the piece before `r` never exceeds `H − 1` up to that point, and so on. *(This is the step to
get right; the corpus can be consulted. The three pieces of Bing's special case are
`D(0,h′)`, `D(h′,k′)`, `D(k′,n−1)` in the notation of `bing-theorems-3-4-notes.md` §4.)*

The basepoint lies in one of the three pieces. Apply the induction hypothesis to that piece with
its own band, obtaining an itinerary `c₀` onto which both of *its* arms fold. Then extend: each
of the two outer pieces is a 1-Lipschitz sequence attached at a cut point, and must be folded
onto a continuation of `c₀`. That is `foldsFrom_split` with the continuation chosen so that the
outer piece folds onto it — and the choice is where the reversal count grows, since the
continuation must sweep to the extreme the outer piece reaches.

The reversal law of §0 is a constraint on any proof: the itinerary the induction produces must
have about `⌊span/2⌋ − 1` turns, so each step of the induction adds roughly half a turn. A step
that adds a bounded itinerary to a bounded itinerary cannot be right; a step that appends one
sweep per two levels of span can be.

Two things known not to work, so that they are not retried: a family with a fixed number of
turns (§0); and choosing the continuation to sweep to an extreme and back, which is what the
two-bump shapes do and which fails at all eight span-10 basepoints.

## 5. Deliverables

1. Census.
2. Whatever is proved, `sorry`-free, with `#print axioms`.
3. Report, in this order: any counterexample to `S3` — **report it first**, with `σ` and the
   faithful check; whether the §3 item was done, and with or without the faithfulness
   hypothesis; whether `s3` was proved and by what induction; for a partial result, which cases
   closed and where the reversal count came from.

## 6. If `s3` falls

`theorem3` follows by the line in the skeleton, and Bing 1948 Theorem 3 in the block reading is
unconditional.
