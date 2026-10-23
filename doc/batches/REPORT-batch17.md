# Report — batch 17: shrinking the valley conjectures

One new file, `HPC/Fold/Shrink.lean` (130 lines); root `HPC.lean` as supplied by the batch; the
commission text kept as `COMMISSION-batch17.md`. Nothing else in the project was touched. The
census script is `census-batch17.py`, added for reproducibility.

`lake build` succeeds on `RequestProject` and `HPC`. The new file contains no
`sorry`/`admit`/`axiom`/`native_decide`/`implemented_by` and elaborates with no linter
warnings. Axiom profiles: `valleyBefore_of_cap` uses `[propext, Quot.sound]`; the other four
declarations use `[propext, Classical.choice, Quot.sound]`.

**Headline.** All five commissioned statements went through exactly as stated. Nothing had to
be adjusted, weakened or renamed, and no statement was refuted. The one deviation from the
commission's English is a *simplification*: `demands_lt_of_open` does not need the ambient
hypotheses `hHρ`, `hLρ`, `hrange` at all — the conclusion is pure `min`/`max` arithmetic from
`hopen` — so they are kept as commissioned under underscore names and the fact is recorded in
the docstring. As the commission says, nothing is claimed here about `HighExitValleyOpen`
itself.

## 1. Census

Exhaustive enumeration of all 1-Lipschitz sequences on six levels, filtered for the **down**
form `IsCrookedSeq`, every basepoint of every surviving sequence with `L + 3 ≤ H` (`L`, `H` the
sequence's own minimum and maximum, the tightest admissible choice):

| lengths | crooked sequences | basepoints | cap binds | open |
|---|---|---|---|---|
| 4 – 12 | 429 496 | 1 512 136 | 1 511 684 | 452 |

So the cap `hStar = max (H − 1, p)` binds at 99.970 % of basepoints; at all of those the two
valley clauses are vacuous by `valleyBefore_of_cap`, which is now proved in Lean. The 452
remaining ("open") basepoints are the entire content of `HighExitValleyOpen` in this corpus.
They first appear at length 10 (4 of them), then 56 at length 11 and 452 at length 12.

At every one of the 452 open basepoints:

* the conclusion of `demands_lt_of_open` holds — both demands and `p` are strictly below
  `H − 1` (this is also proved in Lean, so the check is only a sanity test of the script);
* the valley clause holds at every admissible peak index `s` — no failure of
  `HighExitValley`, hence none of `HighExitValleyOpen`;
* the shape `(hStar − p, H − 1 − hStar, L − (p − 2))` is `(0, 1, 0)` in all 452 instances,
  the shape the commission reports as the overwhelming one and the one in which the visit is
  forced by the Lipschitz property alone. The other three shapes the commission lists,
  `(0,1,−1)`, `(0,2,0)`, `(1,1,0)`, do not occur on six levels at lengths ≤ 12; they come from
  the wider and longer runs cited there, which are not reproduced here.

This is an exploratory computation in a separate script, not a Lean-checked claim; it is
recorded as evidence for the conjectural proposition `HighExitValleyOpen`, exactly as the
corpus figures of earlier batches are. Everything asserted *in Lean* in this batch is proved
outright.

### Declarations, in file order

"Project" dependencies are results and definitions from earlier batches (batch number in
parentheses); "mathlib" lists library lemmas used beyond the `omega`, `rcases`/`obtain`,
`push_neg`, `by_contra` tactics.

| name | kind | project dependencies | mathlib dependencies |
|---|---|---|---|
| `valleyBefore_of_cap` | thm | `ValleyBefore` (b10) | — |
| `exists_drop_before_exceed` | thm | `hStarArm` (b9), `le_hStarArm` (b9), `le_hStarArm_of_window` (b14), `exists_least_index` (b6) | `Fin.le_def`, `Fin.lt_def`, `Fin.ext` |
| `pre_drop_eq` | thm | `IsLip` (b6) | `abs_le`, `Fin.lt_def` |
| `HighExitValleyOpen` | def | `IsLip` (b6), `IsCrookedSeq` (b7), `hStar` (b9), `ValleyBefore` (b10), `armG`, `armT` (b6), `phase` (b8) | — |
| `highExitValley_iff_open` | thm | `HighExitValley` (b10), `HighExitValleyOpen`, `valleyBefore_of_cap` | `le_max_left`, `le_trans` |
| `demands_lt_of_open` | thm | `hStar`, `hStarArm` (b9), `armG`, `armT` (b6) | `min_cases`, `max_choice`, `le_max_left`, `le_max_right`, `le_trans` |

## 2. How the statements were proved

**`valleyBefore_of_cap`** (§1 of the commission). Unfolding `ValleyBefore`, the hypothesis at
`u` is `h + 1 < A u`, while `A u ≤ H ≤ h + 1`; `omega` closes it. The conclusion then holds for
every `u` and every `s`, vacuously. Note the statement needs no Lipschitz, crookedness or
basepoint hypothesis.

**`exists_drop_before_exceed`** (§2). From `le_hStarArm` and `hdem`, `p ≤ h`. If every `j ≤ u`
had `p − 1 ≤ A j`, then `le_hStarArm_of_window` (batch 14) gives `A u ≤ hStarArm A p ≤ h`,
contradicting `h + 1 < A u`; so the set of `j ≤ u` with `A j ≤ p − 2` is nonempty and
`exists_least_index` supplies its least element `d`. `d ≠ u` because `A u > h + 1 ≥ p + 1`,
while `A d ≤ p − 2`; and for `j < d` minimality gives `¬(j ≤ u ∧ A j ≤ p − 2)`, where `j ≤ u`
holds, so `p − 1 ≤ A j`.

**`pre_drop_eq`** (§2). `p − 1 ≤ A d'` by `hpre` at `d' < d`; and `IsLip A d' d` with
`d.val = d'.val + 1` gives `|A d − A d'| ≤ 1`, hence `A d' ≤ A d + 1 ≤ p − 1`.

**`highExitValley_iff_open`** (§3). (⇒) drops the openness hypothesis. (⇐) splits on
`hStar < max (H − 1) (ρ i)`. In the open case apply the hypothesis. Otherwise
`max (H − 1) (ρ i) ≤ hStar`, so `H − 1 ≤ hStar` by `le_max_left`, and `valleyBefore_of_cap`
applies to each arm, whose values are bounded by `H` because the arm's values are values of `ρ`.

**`demands_lt_of_open`** (§2). Unfold `hStar`. If the `min` equalled its second argument
`max (H − 1) (ρ i)`, `hopen` would say that argument is strictly less than itself; so the `min`
is its first argument `X = max (max hG hT) (max p (L + 1))`, and `X < max (H − 1) (ρ i)`. Each
of `hG`, `hT`, `p` is `≤ X`; and `max (H − 1) (ρ i)` is either `H − 1` or `ρ i`, the latter
impossible since `p = ρ i ≤ X`. Hence all three are `< H − 1`.

## 3. Nothing omitted

Every statement in the commission's §§1–3 is in the file and proved. Nothing was deferred, and
the items listed in §5 (`HighExitValleyOpen` itself, the reflected shrinking of `LowExitPeak`,
`ExitReach`, Bing 1948 Theorems 4–6, the Bing 1951 reduction, the D8/D9 gap) are untouched, as
directed.
