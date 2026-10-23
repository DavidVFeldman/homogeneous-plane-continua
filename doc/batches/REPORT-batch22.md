# Report — batch 22: the faithful model, with a realization theorem

One new file, `HPC/Fold/Faithful.lean`; root `HPC.lean` updated to import it. Nothing else in
the project was touched. The whole project builds. The new file contains no `sorry`, `admit`,
`axiom`, `native_decide` or `implemented_by`, produces no linter warnings, and every
declaration in it has axiom profile within `propext`, `Classical.choice`, `Quot.sound`. The
commission text is kept as `COMMISSION-batch22.md`; the census script is `census-batch22.py`.

## 1. Everything commissioned went through

Delivered complete, with the statements exactly as commissioned:

* `IsCrookedIvF` — the faithful model, with geometric adjacency and forced-meeting
  crookedness;
* `IsCrookedIvF.isCrookedIv` — it implies the batch-20 model;
* `isCrookedIvF_minIdx_maxIdx` — **necessity**: a chain crooked in the 1948 sense lands in the
  model via `(minIdx, maxIdx)`;
* `strip`, `linkX`, `linkRect`, `stripChain`, `linkChain` — the construction;
* `realization` — **sufficiency**: every sequence in the model with `0 ≤ ρ` and `σ < M` is the
  `(minIdx, maxIdx)` pair of an explicit chain of open rectangles in `ℝ × ℝ`, crooked in the
  1948 sense inside the chain of strips;
* `ivSeq_not_faithful`, `lpivSeq_not_faithful` — the two batch-20 witnesses are outside the
  model;
* `F2PrimeF` and `theorem3_of_F2PrimeF` — the route, over the corrected model.

In particular §6's contingency did not arise: **no shape allowed by `adj` failed to be placed**,
so the model needs no third condition.

Added beyond the commission, because they were useful and are reusable:

* `IsCrookedIvF.near` — the symmetric reading of `adj`, covering `u = t` as well, which is the
  workhorse of both §2 and §3;
* `IsCrookedIvFCheck` and `isCrookedIvF_of_check` — a decidable criterion for the model (the
  width clause pins each of `h`, `k` to an endpoint of the interval of its witnessing
  neighbour, so two index quantifiers and two Booleans suffice), the analogue of batch 20's
  `isCrookedIv_of_check`; future witnesses over this model can be checked by `decide`;
* `demoRho`, `demoSig`, `demo_isCrookedIvF`, `demo_realized` — a six-term member of the model
  whose crookedness clause genuinely fires, together with its realization; this pins down that
  `realization` is not vacuous;
* `crookedIvF_step` — batch 20's `crookedIv_step` with *meeting* hypotheses instead of
  containment (the forced-meeting clause needs exactly this);
* the interval lemmas `ioo8_subset_iff`, `ioo8_inter_nonempty_iff` and the endpoint tables
  `strip_table`, `meet_range`, `meet_table`, `lxN_lt_rxN`, `lxN_lt_rxN_adj`,
  `linkRect_subset_strip_iff`, `linkRect_meet_strip_iff`.

## 2. The endpoint table, and the constants

All endpoints are kept as integers in **eighths**: `lxN` and `rxN` return `8x`, and `linkX t`
is the open interval `(lxN/8, rxN/8)`. A strip is `strip j = (j, j + 3/2) × ℝ`, whose
`x`-range is `(8j/8, (8j+12)/8)`, so every containment and every overlap between a link range
and a strip range is a pair of linear inequalities over `ℤ`, discharged by `omega`. This is the
one deliberate deviation from the commission's presentation, and it is what makes the case
table mechanical.

Write `a = ρ t`. Two Boolean flags decide the endpoints:

* `ExtL ρ t` — some neighbour `u` of `t` has `ρ u ≤ a − 1`;
* `ExtR σ t` — some neighbour `u` of `t` has `σ u ≥ σ t + 1`.

| shape of link `t`           | `lxN` | `rxN` | `x`-range          |
|-----------------------------|-------|-------|--------------------|
| width 2, `σ t = a + 1`      | `8a+9`  | `8a+11` | `(a + 9/8, a + 11/8)` |
| width 1, no extension       | `8a+4`  | `8a+8`  | `(a + 1/2, a + 1)`    |
| width 1, left extension     | `8a+2`  | —       | left end `a + 1/4`    |
| width 1, right extension    | —       | `8a+11` | right end `a + 11/8`  |

Two of the commission's constants for width-1 links had to be changed; the width-2 core
`(a + 9/8, a + 11/8)` and the right extension to `a + 11/8` are as commissioned.

* The core `(a + 1/8, a + 1)` is too wide on the left: since `strip (a−1) = (a−1, a + 1/2)`,
  any range reaching below `a + 1/2` *meets* `strip (a−1)`, which must not happen when there
  is no left extension. The core used here is `(a + 1/2, a + 1)`.
* The left extension to `a − 3/8` leaves `strip a = (a, a + 3/2)` altogether, so the link would
  no longer lie in the strip its own interval names. The overlap zone to reach into is
  `strip (a−1) ∩ strip a = (a, a + 1/2)`; the constant used here is `a + 1/4`.

With these two changes every shape allowed by `adj` is placed, and the overlap of neighbours
is genuine in each: for two width-1 links at levels `a` and `a + 1`, the left one ends at
`a + 11/8` and the right one begins at `(a+1) + 1/4 = a + 10/8`, overlapping in
`(a + 10/8, a + 11/8)`; for a width-1 link at `a` beside a width-2 link at `{a, a+1}`, the
common zone is `(a + 9/8, a + 11/8)`; beside a width-2 link at `{a−1, a}` it is
`(a + 1/4, a + 3/8)`; and two links with the same interval share their cores.

The table then yields, for every `j`:

* `linkX t ⊆ (j, j + 3/2)` iff `ρ t ≤ j ≤ σ t` — `strip_table`;
* `linkX t` meets `(j, j + 3/2)` iff `j` lies in the interval of `t` or of a neighbour of `t` —
  `meet_table`, via the intermediate form `meet_range`, which says the meeting set is exactly
  `[ρ t − [ExtL], σ t + [ExtR]]`;
* neighbouring links overlap — `lxN_lt_rxN_adj`.

Three facts from `adj` do the work in these proofs: for neighbours `t`, `u` one has
`σ t ≤ ρ u + 1` and `σ u ≤ ρ t + 1` (`IsCrookedIvF.near`); a width-2 link therefore has
neither flag set (`not_extL_of_width_two`, `not_extR_of_width_two`), so its neighbours' index
intervals lie inside its own; and a width-1 link's neighbours reach at most one index beyond it
on each side.

Lanes: `linkRect t = linkX t ×ˢ (t, t + 3/2)`, the same `3/2` geometry in the second
coordinate, so links two or more apart are disjoint regardless of their `x`-ranges, and
neighbouring links meet exactly when their `x`-ranges do.

## 3. What was supplied

* The case table of §3 and the overlap check for each adjacency shape (the commission's two
  `supply` notes). Both are folded into the integer lemmas above, so the case analysis is on
  the two flags and the width rather than on the five shapes of `(I(t−1), I(t), I(t+1))`.
* The `i = j` case of the 1948 crookedness clause. `IsCrookedIn'` quantifies over *arbitrary*
  pairs of links, so besides the ascending case (which is the model's clause) and the
  descending case (the model's clause with the roles of the two ends and of `r`, `r'`
  exchanged), one must dispose of `i = j`: a single link meets only indices in
  `[ρ i − 1, ρ i + 1]`, so two of its meeting indices are never three apart.
* The index bookkeeping between `ℤ`-valued levels and `Fin M` strip indices, which is where
  the hypotheses `0 ≤ ρ` and `σ < M` are consumed.
* `minIdx`/`maxIdx`: the containment table gives `ρ t ≤ minIdx t` and `minIdx t ≤ ρ t` from
  `minIdx_le`, and symmetrically for `maxIdx`.

## 4. Census

`census-batch22.py` enumerates the faithful model on all chains of length `n ≤ 7` over five
levels: **35 103** members. For each member it recomputes `lxN`/`rxN` and checks, in eighths,
that

* the set of strips containing the `x`-range of link `t` is exactly `[ρ t, σ t]`;
* the set of strips met by it is exactly `I(t−1) ∪ I(t) ∪ I(t+1)`;
* neighbouring `x`-ranges overlap.

**0 failures.** The script also reports the members whose crookedness clause is not vacuous —
768 of them, the shortest of length 6 — and the first such member is the one formalized as
`demoRho`/`demoSig`; and it confirms that `ivSeq`/`ivSig` violates geometric adjacency at
`t ∈ {5, 6, 8, 9, 16, 17, 18, 20}` and `lpivSeq`/`lpivSig` at
`t ∈ {0, 7, 8, 9, 11, 15, 16, 18, 19, 20, 22}`. The Lean proofs use one violation each
(`t = 5` and `t = 0` respectively), as the commission suggests; the adjacency route is indeed
the cheaper one, and no crookedness instance is needed.

## 5. Statements that did not go through

None. Every commissioned statement is proved as stated.

## 6. Remarks

* The realization is a chain of *open rectangles* in the plane with the max metric; the strips
  are unbounded in the second coordinate. Nothing in `Chain` asks for bounded or connected
  links, and Bing's 1948 crookedness is read off the same two tables.
* Because `realization` exists, the model question is closed in the direction that matters for
  the programme: a sequence in `IsCrookedIvF` *is* a chain, so any future counterexample over
  this model refutes a statement about chains, not a statement about sequences. The three
  conjectures over `IsCrookedIvF` and the assembly `f2PrimeF_of_…` are, as §7 of the commission
  says, not in this batch.
