# Report: batch 25 — `OffDichotomy`

## 0. Headline: `OffDichotomy` is false

**A counterexample was found, and it is reported first, as the protocol asks.**

The witness is Bing's own chain from level `0` to level `8`, i.e. `bingPath 0 8` of
`HPC/Fold/OffCenter.lean`: **409 links, levels `0 … 8`, with `σ = ρ`**, a member of the
faithful model (`IsCrookedIvF ρ ρ`, proved in Lean — §3). At its basepoint
**`i = 57`**, of level `p = 3`, with `L = 0` and `H = 8`, **none of the three base centers
`c₀ ∈ {2, 3, 4}` puts both arms on time at the bottom, or both on time at the top.**

Anatomy of the failure (`G` = forward arm, 352 links; `T` = backward arm, 58 links; both start
at level three):

```
T = 3 4 3 4 5 4 3 4 3 2 3 4 3 2 3 2 1 2 3 2 3 4 3 2 3 4 3 4 5 4 3 4 3 2 3 4 3 2 3 2 1 2 3 2 3 4 3 2 3 2 1 2 3 2 1 2 1 0
G = 3 2 3 4 3 4 5 4 3 4 5 4 5 6 5 4 5 4 3 4 5 4 3 4 3 2 3 4 3 4 5 4 3 …   (level 8 first at index 351)
```

* `max T = 5 < H − 2 = 6`: the backward arm never reaches the top band, so `TopOnTime T c₀ 8`
  is false for every `c₀` — the crossing index `j` would have to satisfy `T j ≥ 6`.
* `c₀ = 2`: `T` rises to `4 > c₀ + 1 = 3` at its **first** step, before ever visiting the
  bottom band, so `BottomOnTime T 2 0` fails.
* `c₀ = 3`: `T` rises to `5 > c₀ + 1 = 4` at index four, and the only admissible earlier
  indices `j = 2, 3` have `T j = 3, 4`, above the band `min (L+2) c₀ = 2`; so
  `BottomOnTime T 3 0` fails.
* `c₀ = 4`: here `BottomOnTime T 4 0` *does* hold (`T` reaches `2` at index nine without
  exceeding `5`), but `BottomOnTime G 4 0` fails: `G` climbs to `6 > c₀ + 1 = 5` at index
  thirteen, and its only earlier visit to the bottom band is at index one, which is **too
  early** — the ladder token cannot be at the bottom position before index
  `c₀ − L − 1 = 3`.

So the failure uses both halves of the criterion: the level clause on one arm and the *index*
clause (Bing's schedule) on the other. It is invisible below induction depth eight, which is
exactly where the batch-24 census stopped.

**The folding condition `F2PrimeOff` is not affected.** At the same basepoint both arms fold
onto the non-self ladder `offLam 2 5 0 8` (base centre `p − 1`, peak `p + 2`), and the same is
true at each of the eight failing basepoints of `bing 0 8` and at every failing basepoint
sampled in `bing 0 9`. What the counterexample refutes is batch 24's *reduction* of
`F2PrimeOff` to the two self-ladders, not `F2PrimeOff` itself, and nothing proved in batches
6–24 is touched.

## 1. What is delivered in Lean

New files: `HPC/Fold/Dichotomy.lean` (the commissioned file),
`HPC/Fold/DichotomyWitness.lean` (the counterexample) and `HPC/Fold/DichotomyFaithful.lean`
(the witness is faithful); `HPC.lean` updated. Nothing else
touched. The whole project builds; no `sorry`, no `admit`, no `axiom`, no `native_decide`, no
`@[implemented_by]`, and no linter warning in the new files.

### The ordinary item

* `arm_first_exit` — the single-arm exit lemma off centre, proved. As §3.1 of the commission
  anticipated, the Lipschitz hypothesis is not needed; neither is the hypothesis that the arm
  starts within one of `c`, so both were dropped and the statement proved is more general.

### The search item

* `ce_not_offDichotomyAt : ¬ OffDichotomyAt ceSeq ceBase 8 0` — the failure at basepoint 57 of
  the explicit 409-link chain, proved outright, with no hypotheses.
* `ceSeq_faithful : IsCrookedIvF ceSeq ceSeq` — the witness is a member of the faithful model
  (§3), and hence
* `not_offDichotomy : ¬ OffDichotomy` — **the commissioned statement is refuted**, with no
  hypotheses and no `native_decide`; `not_offDichotomy_of_faithful` is the intermediate form.
* `ce8_eq_bingPath : bingPath 0 8 = ce8` and `ce8_length : ce8.length = 409` — the literal
  really is Bing's chain, and its length is the value `z 8` of his recurrence.
* Supporting general lemmas: `not_bottomOnTime_of_rise` and `not_topOnTime_of_fall` (how to
  refute the two criteria: one index where the arm leaves the window, plus the finitely many
  admissible earlier indices), `bottomOnTime_of_le`, `topOnTime_of_ge` (the trivial clauses).

### Sound partial results, proved before the counterexample was found and still valid

* `offDichotomyAt_near_extreme` — **the near-extreme case of the dichotomy**: at a basepoint
  whose level is within *two* of an extreme, the dichotomy holds outright, by the trivial
  clause (`c₀ = L + 1` puts both arms on time at the top because no arm can fall below `L`;
  `c₀ = H − 1` puts both on time at the bottom). No crookedness, no Lipschitz condition.
* `f2PrimeOff_near_extreme` — hence the conclusion of `F2PrimeOff` at every such basepoint,
  which strengthens batch 24's `f2PrimeOff_monotone` from "within one" to "within two".
* `f2PrimeOff_span_five` — hence **the folding condition for every span up to five**, which
  subsumes batch 24's `f2PrimeOff_span_three`.
* `offDichotomy_of_interior` — the reduction of the dichotomy to interior basepoints (level at
  least three from each extreme, so spans six and above). Consistently with the
  counterexample, whose basepoint is at level `L + 3`, it is exactly the interior that fails.
* `f2PrimeOff_of_offDichotomyAt` — the pointwise form of batch 24's reduction.

### Axiom audit

```
arm_first_exit                 [propext, Classical.choice, Quot.sound]
bottomOnTime_of_le             (no axioms)
topOnTime_of_ge                [propext, Quot.sound]
not_bottomOnTime_of_rise       [propext, Quot.sound]
not_topOnTime_of_fall          [propext, Classical.choice, Quot.sound]
offDichotomyAt_near_extreme    [propext, Classical.choice, Quot.sound]
f2PrimeOff_of_offDichotomyAt   [propext, Classical.choice, Quot.sound]
f2PrimeOff_near_extreme        [propext, Classical.choice, Quot.sound]
f2PrimeOff_span_five           [propext, Classical.choice, Quot.sound]
offDichotomy_of_interior       [propext, Classical.choice, Quot.sound]
ce8_eq_bingPath, ce8_length    [propext, Classical.choice, Quot.sound]
ceSeq_isLip                    [propext, Classical.choice, Quot.sound]
ce_not_offDichotomyAt          [propext, Classical.choice, Quot.sound]
not_offDichotomy_of_faithful   [propext, Classical.choice, Quot.sound]
ceSeq_faithful                 [propext, Classical.choice, Quot.sound]
not_offDichotomy               [propext, Classical.choice, Quot.sound]
```

## 2. The census

`census-batch25.py` implements the dichotomy over the faithful model, reusing the model, the
ladders and the fold test of `census-batch24.py` verbatim; `search-batch25.py` adds a fast
faithfulness test and the searches. Each basepoint is scored by the number of the (at most six)
pairs `(c₀, side)` that work; score `0` is a failure of the dichotomy.

| corpus | basepoints | least score | failures |
|---|---|---|---|
| `bing 0 4`, `bing 0 5`, `bing 0 6` | 13 + 30 + 71 | 2 | 0 |
| `bing 0 7` | 170 | 1 | 0 |
| 11 485 subchains of `bing 0 7`, length ≥ 9, span ≥ 4 | 801 944 | 1 | 0 |
| exhaustive faithful corpus, length 8 and 9, 4/5/6 levels | 4 992 + 32 400 | 2 | 0 |
| random faithful chains, length 40 and 80 | 6 200 + 7 520 | 2 | 0 |
| hill-climbing from subchains of `bing 0 7`, 10 runs | — | 2 | 0 |
| **`bing 0 8`** | **409** | **0** | **8** (indices 57, 59, 61, 65, 343, 347, 349, 351) |
| **`bing 0 9`** | **986** | **0** | **148** |
| **`bing 0 10`** | **2 379** | **0** | **849** |

The eight failures in `bing 0 8` are two mirror-image families: four at level three near the
start (the first is index 57) and four at level five near the end. Failures become common as
the span grows.

Two independent implementations agree. The one-pass criteria of `census-batch25.py`
(`bot_fast`, `top_fast`) were checked against the definitional `bottom_on_time` / `top_on_time`
of `census-batch24.py` at every basepoint, arm and centre of the exhaustive faithful corpus of
length 8 on 5 levels (13 614 chains, 0 disagreements), and the batch-24 census itself, run on
`bing 0 8` with `python3 census-batch24.py dichotomy bing 8`, reports the same eight failures,
the first at index 57 — and no unsoundness of either criterion anywhere (whenever a criterion
holds, the corresponding self-ladder does take the arm).

No shorter counterexample exists in the corpora searched: no contiguous subchain of `bing 0 8`
shorter than the whole chain fails (the failure needs both extremes, and `L = 0` is attained
only at the first link and `H = 8` only at the last); no maximal window of span ≤ 7 of
`bing 0 9` or `bing 0 10` fails; and 400 random deletions from `bing 0 8` all destroyed either
faithfulness or the failure. This is expected: Bing's recurrence `z` gives the minimum length
of a crooked chain of a given span, and a span-8 chain needs 409 links — random faithful chains
of length 80 reach span 4 at most.

## 3. The faithfulness of the witness, inside Lean

`IsCrookedIvF ceSeq ceSeq` is proved in `HPC/Fold/DichotomyFaithful.lean`, in about four
minutes of kernel evaluation. The straightforward route does not work: the cheap criterion
`IsCrookedIvFCheck2` of `HPC/Fold/ClosureF.lean` evaluates by `decide +kernel` in 101 s for the
71-link chain `bing 0 6`, but its cost is superquadratic in the length, and at 409 links the
kernel had consumed over 50 GB without finishing. Two observations make the check cheap.

* **Monotonicity in the far index.** The crookedness clause for `s < t` and levels `x, y` asks
  for `s < r < r' < t` at prescribed levels; witnesses for a smaller `t₀ ≤ t` are witnesses for
  `t`. So it suffices to check, for each index `s` and each pair of levels `x` met at `s` and
  `y`, the *least* `t₀ > s` at which `y` is met: `409 × 9 × 9` checks instead of one per pair
  of indices.
* **A numeral for the chain.** The levels are `0 … 8`, so the chain is one natural number in
  base sixteen and a link is a shift and a mask — two machine operations for the kernel,
  instead of walking a 409-element list.

The Lean file defines that search (`levHas`, `firstLev`, `firstVal`, `checkOne`, `checkAll`),
evaluates it (`checkAll_true`, by `decide +kernel`), proves the specifications of the two
searches by induction on the fuel, and assembles them into `ceSeq_faithful`; the numeral is tied
to the chain by `rhoN_eq`. Independently, the same fact is checked outside Lean by
`search-batch25.py check 8` and, for `n ≤ 7`, by the definitional `is_faithful` of
`census-batch24.py`.

## 4. What to repair

The reduction of batch 24 is sound but lossy in a specific way: it restricts the family to the
two *self-ladders* `offLam c₀ c₀ L H` and `offVee c₀ c₀ L H`, i.e. to peak `h = c₀` and valley
`l = c₀`, while `F2PrimeOff` allows any peak `c₀ ≤ h ≤ H − 1` and any valley `L + 1 ≤ l ≤ c₀`.
At every failing basepoint the itinerary that works has a peak strictly above the base centre
(`offLam 2 5 0 8` at the level-three failures, `offVee 4 2 0 8` and `offVee 5 2 0 8` at the
level-five ones). A repaired dichotomy should therefore attach to each base centre the full
one-parameter family: an arm is "on time" for `offLam c₀ h L H` if it first climbs to within
one of `h` and then descends to the bottom band, each on the ladder's schedule. Batch 24's
`foldsOnto_offLam_self` generalises to that statement, and the census of `F2PrimeOff` — which
has never failed, on any corpus, including `bing 0 8`, `bing 0 9` and `bing 0 10` at the
basepoints sampled here — suggests the generalised dichotomy is the right conjecture.

## 5. Files

* `HPC/Fold/Dichotomy.lean` — the commissioned file: `arm_first_exit`, the trivial criteria,
  the refutation lemmas, `OffDichotomyAt`, the near-extreme case, `f2PrimeOff_near_extreme`,
  `f2PrimeOff_span_five`, `offDichotomy_of_interior`; `offDichotomy`, `f2PrimeOff` and
  `theorem3` kept commented out at the end, as they are not established.
* `HPC/Fold/DichotomyWitness.lean` — the 409-link chain and the counterexample.
* `HPC/Fold/DichotomyFaithful.lean` — the witness is faithful, hence `not_offDichotomy`.
* `census-batch25.py` — the census (`bing`, `bingsub`, `ex`, `rand`, `seq`, `deep`, `agree`,
  `climb`).
* `search-batch25.py` — the fast faithfulness test and the searches (`check`, `validate`,
  `windows`, `shrink`, `anneal`).
* `COMMISSION-batch25.md` — the commission text, as delivered.
