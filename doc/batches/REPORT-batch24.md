# Report: batch 24 — the off-center family, Bing's chains, `F2PrimeOff`

Everything below lives in the single new file `HPC/Fold/OffCenter.lean`; the root `HPC.lean`
gained the one import. Nothing else was touched. The whole project builds, the new file has no
`sorry`, `admit`, `axiom`, `native_decide` or `@[implemented_by]`, and produces no linter
warning; every declaration in it has axiom profile inside `propext`, `Classical.choice`,
`Quot.sound` (`z_small` uses none).

## 1. No counterexample

**No counterexample to `F2PrimeOff` was found, and none is claimed.** The commission asks for
one first if it exists; the census (`census-batch24.py`, an exploratory computation — the Lean
file, not the script, is the evidence for everything proved) reproduces and extends §2 of the
commission and finds no failure anywhere:

| corpus | size | failures of `F2PrimeOff` |
| --- | --- | --- |
| `bing 0 n`, `n = 4,5,6,7` | 13 + 30 + 71 + 170 = 284 basepoints | 0 |
| subchains of `bing 0 7`, length ≥ 9, span ≥ 5 | 7 559 subchains, 665 322 basepoints | 0 |
| faithful exhaustive, length 8 on six levels | 13 614 pairs, 108 912 basepoints | 0 |
| faithful exhaustive, length 9 on six levels | 50 486 pairs, 454 374 basepoints | 0 |
| the batch-23 42-term witness (`σ ≠ ρ`) | 42 basepoints | 0 |
| the batch-23 71-term witness (it *is* `bing 0 6`) | 71 basepoints | 0 |
| random faithful chains, length 40 on 10 levels and length 80 on 14 levels | 2 300 chains | 0 |

The random chains are of small span, as the commission warns, so they test little; the weight
is on the Bing corpus and the exhaustive corpus. Adversarial search (`search-batch24.py`:
hill-climbing on subchains of `bing 0 6` under 1-Lipschitz mutations that keep membership in
the faithful model, minimising the number of members of the family that both arms fold onto)
never drove that number below 3, and over all 7 559 subchains of `bing 0 7` the hardest
basepoint still has five working itineraries. `F2PrimeOff` looks robustly true, with slack.

## 2. What is proved

### 2.1 Ordinary items (§3.1–3.3)

* `theorem3_of_F2PrimeOff` — exactly the route of §3.1: `minIdx`/`maxIdx`, `minIdx_lip`,
  `isCrookedIvF_minIdx_maxIdx`, the attained extremes, batch 9's degenerate branch below
  `L + 3 ≤ H` (`exists_blocks_first_of_range_le_two`), and, in the main branch,
  `exists_blocks_first_of_folds` applied directly to the two folds — no `SegLam`, no `SegVee`,
  no bump bridge.
* `bingPath`, with its termination proof: the three recursive calls have distance
  `|b − a| − 1`, `|b − a| − 2`, `|b − a| − 1`, and after rewriting `(|x|).toNat` as `x.natAbs`
  the three goals are `omega`. The commission's `if h :` binder is unused and is written `_h`.
* `bingPath_length : (bingPath a b).length = z (|b − a|).toNat`, by induction on a fuel bound,
  through `bingPath_length_aux`; `z_pos` (needed to take tails) by a three-step induction; the
  recurrence step is `z (p+3) = 2 * z (p+2) + z (p+1) − 2`, which holds by `rfl`.
* `z_small : z 3 = 6 ∧ z 4 = 13 ∧ z 5 = 30 ∧ z 6 = 71 ∧ z 7 = 170 ∧ z 8 = 409`, by `decide`.
* `bing04_faithful`, `bing05_faithful` — **`bing05_faithful` did evaluate.** Both go through
  `IsCrookedIvFCheck2` and `decide +kernel`, as the commission suggests, at length 13 and
  length 30.
* `lpSeq_eq_bing06` — the batch-23 71-term witness is `bing 0 6`, verbatim.

One addition was needed for §3.2, and it is the only departure from the skeleton.
`bingPath` is defined by well-founded recursion, which the kernel does not reduce, so
`decide` cannot see `bingPath 0 4` at all — not even its length, which appears in the *type* of
`bing 0 4`. The file therefore adds `bingRun` (the monotone base case), the three equation
lemmas `bingPath_base`, `bingPath_up`, `bingPath_down`, a fuel-driven structurally recursive
copy `bingAux`, and `bingPath_eq_aux : (|b − a|).toNat ≤ m → bingPath a b = bingAux m a b`.
With it, `bingPath 0 4`, `bingPath 0 5` and `bingPath 0 6` reduce to explicit lists by `rfl`
(`bingPath_04`, `bingPath_05`, and inside `lpSeq_eq_bing06`), and the faithfulness statements
are obtained by rewriting the list inside the dependent type before deciding.

### 2.2 The search item: the monotone case, and a reduction

`f2PrimeOff` is **not** proved. Two things about it are.

**The monotone case is proved outright, and needs no crookedness.**
`f2PrimeOff_monotone`: if `ρ i ≤ L + 1` or `H − 1 ≤ ρ i` then the conclusion of `F2PrimeOff`
holds at `i`. The two itineraries used are the pure ladders `offLam (L+1) (H−1) L H`, whose
first run is the ladder of centers `L+1, …, H−1`, and its mirror `offVee (H−1) (L+1) L H`; the
time-assignment is the closed form `β k = (min (f k) (H−1) − (L+1)).toNat`, respectively
`β k = ((H−1) − max (f k) (L+1)).toNat`, which is 1-Lipschitz because it is a clamp of a
1-Lipschitz function, is `0` at the basepoint exactly because the basepoint level is extreme,
and puts every level within one of its center. Since `L ≤ ρ i ≤ H`, at span three every
basepoint is of this kind, so `f2PrimeOff_span_three` settles `H = L + 3` completely: the base
case of the commission's §3.4 induction, for the sequence model, is done.

**The general case is reduced to a statement with no folding in it.** The two ladders through
an arbitrary base center are `offLam c₀ c₀ L H` — descend from `c₀` to the bottom, then climb
to `H − 1` — and its reflection `offVee c₀ c₀ L H`. Past the bottom the climb covers every
level, so an arm that has crossed can be tracked whatever it then does; the entire constraint
is the crossing, and the crossing is a matter of *schedule*: the token starts at position `0`
and moves at most one position per index, so if it is to stand on the bottom at index `j` the
arm must have been, at each earlier index `k`, no higher than `min (L+2) c₀ + (j − k)`, and
never above `c₀ + 1`. That is the definition

```
BottomOnTime f c₀ L : (∀ k, f k ≤ c₀ + 1) ∨
  ∃ j, (c₀ − L − 2).toNat + 1 ≤ j ∧ ∀ k ≤ j, f k ≤ c₀ + 1 ∧ f k ≤ min (L+2) c₀ + (j − k)
```

with `TopOnTime f c₀ H := BottomOnTime (−f) (−c₀) (−H)`. The two folds
`foldsOnto_offLam_self` and `foldsOnto_offVee_self` prove that these criteria suffice; the
second is deduced from the first by the reflection `offVee_self_len`, `offVee_self_walk` and
batch 6's `foldsOnto_neg`. The time-assignment in the first is

```
β k = if k ≤ j then min k (max (b − (j − k)) (c₀ − max (f k) (L+1)).toNat)
               else min (A (f k)) (b + (k − j))
```

with `b` the bottom position and `A` the position of a level on the climb: a ramp that
guarantees arrival on schedule, a tracker that follows the arm down when it descends faster,
and a cap by the index that keeps the start at `0`. The cap makes the token lag by one position
in exactly one situation — when the arm has moved at full speed since the start — and the
window still holds there, which is where the new auxiliary `abs_sub_le_of_isLip` (a 1-Lipschitz
sequence moves by at most the number of steps) is used.

What remains is `OffDichotomy`: at every basepoint, for one of the three base centers, **both**
arms cross the bottom on schedule, or **both** cross the top on schedule. `OffDichotomy` is
`f2PrimeOff`'s whole content as far as this batch can see it:

```
theorem f2PrimeOff_of_offDichotomy (hd : OffDichotomy) : F2PrimeOff
```

and `OffDichotomy` mentions no walk, no time-assignment and no `FoldsOnto` — only inequalities
between the arm's levels and its indices. It is a statement about crooked sequences of the kind
the earlier batches state, and it is the natural target for a next batch.

The census scores `OffDichotomy` too, with the criteria transcribed from the Lean definitions,
and additionally verifies on every instance that each criterion really does give the fold
(`BottomOnTime`/`TopOnTime` "unsound" counters, always zero — a check on the Lean lemmas, not a
substitute for them):

| corpus | failures of `OffDichotomy` | criterion-without-fold |
| --- | --- | --- |
| `bing 0 n`, `n = 4,5,6,7` | 0 | 0 |
| subchains of `bing 0 6`, length ≥ 9, span ≥ 5 | 0 | 0 |
| subchains of `bing 0 7`, length ≥ 9, span ≥ 5 (7 559 subchains) | 0 | 0 |
| faithful exhaustive, length 8 on six levels | 0 | 0 |
| faithful exhaustive, length 9 on six levels | 0 | 0 |
| the batch-23 42-term witness | 0 | 0 |

## 3. On the middle subcase of §3.4

The commission expects the middle subcase `h′ < i < k′` to be the whole difficulty, and to need
a sub-fold whose peak is replaced by the global one. The reduction above says something about
where that difficulty now sits. Once the family is restricted to the two ladders — which the
census shows is no loss anywhere in the corpus: at every basepoint of every corpus above, one
of `offLam c₀ c₀ L H`, `offVee c₀ c₀ L H` with `c₀ ∈ {p−1, p, p+1}` already takes both arms —
the itinerary carries no free height or depth parameter at all, and "replacing the sub-fold's
peak by the global one" is not available as a move: there is nothing left to choose but `c₀`
and the side of the dichotomy. Correspondingly, the tracking step has become the arithmetic
schedule inside `BottomOnTime`, which is proved here once and for all, and the induction is
pushed entirely into the choice of `c₀` and of the side.

Two smaller findings from the search, recorded because they cost effort:

* The plainest guesses fail. The itinerary `offVee c₀ (L+1) L H` — descend to the bottom, sweep
  to the top, sweep back — takes both arms at every basepoint of `bing 0 5`, but fails at 34
  basepoints of `bing 0 6` and `bing 0 7`, where an intermediate valley is needed.
* A criterion phrased on levels alone is not enough, in either direction. "The arm reaches
  `L + 1` before it first exceeds `c₀ + 1`" is sufficient for the fold (0 failures of that
  implication over the whole corpus) but leaves 20 basepoints of `bing 0 7` uncovered;
  relaxing `L + 1` to `L + 2` covers everything but is no longer sufficient — it predicts a
  fold that does not exist at 322 corpus instances, the token being unable to cross the bottom
  in the time the arm gives it. Only the schedule form above is both.

## 4. Files

* `HPC/Fold/OffCenter.lean` — the commissioned file, as delivered above.
* `HPC.lean` — the one added import (the batch-23 witness imports are kept).
* `COMMISSION-batch24.md` — the commission text.
* `census-batch24.py` — the model, the two walks, `FoldsOnto` by reachability, `bingPath`, and
  the two censuses (`F2PrimeOff` and `OffDichotomy`) over the corpora above.
* `search-batch24.py` — the adversarial search.
