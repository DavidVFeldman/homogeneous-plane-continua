# Report — batch 3: Bing's description of `M`, and Theorem 12 conditional on Theorem 6

Delivered complete. `lake build` succeeds on `RequestProject` and `HPC`; the two new files
contain no `sorry`, `admit`, `axiom`, `native_decide` or `implemented_by`, and `#print axioms`
reports exactly `[propext, Classical.choice, Quot.sound]` for every theorem of both files
(list in §4).

Nothing in `HPC/Chains/` or `HPC/Covers/` was touched. `HPC.lean` is the one supplied with the
batch. The batch-3 commission text is kept as `COMMISSION-batch3.md`.

## 1. Census

### `HPC/PseudoArc/Description.lean`

Commissioned:

| name | status |
|---|---|
| `Description` (structure) | as commissioned |
| `Description.M` | as commissioned |
| `Description.P_mem_M`, `Description.Q_mem_M` | proved |
| `Description.two_le_n_of_lt` | proved |
| `Description.refines_of_le` | proved |
| `Description.closure_union_subset` | proved |
| `Description.isClosed_M`, `Description.isCompact_M` | proved |
| `Description.crooked_of_lt` | proved (batch-1 T5) |
| `Description.exists_closure_link_subset` | proved |
| `Description.link_inter_M_nonempty` | proved |
| `Description.M_subset_union` | proved |
| `Description.n_tendsto_atTop` | proved (batch-1 T7) |
| `Description.exists_level_refining` | proved |
| `Description.IsPattern`, `Description.PatternFollowing` | as commissioned |

Added (not commissioned, needed by the proofs):

* `Chain.union_subset_of_refines` — a refinement covers no more than what it refines.
* `Chain.isConsolidationOf_self` — every chain is a consolidation of itself; this is what makes
  a *level* count as a (trivial) consolidation of a level in the construction of §3.
* `Description.isBounded_M` — `M` is bounded, being covered by the finitely many links of
  level `0`. Needed because `Metric.diam` of an unbounded set is `0`, so batch-1 T7 and
  `Metric.dist_le_diam_of_mem` both want it.

Mathlib used: `Nat.le_induction`, `subset_closure`, `closure_minimal`, `isClosed_closure`,
`isClosed_iUnion_of_finite`, `isClosed_iInter`, `IsClosed.isCompact`,
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`,
`Bornology.isBounded_iUnion`, `Bornology.IsBounded.subset`, `Metric.dist_le_diam_of_mem`,
`dist_pos`, `tendsto_natCast_atTop_iff`, `Filter.tendsto_atTop`,
`Filter.Tendsto.eventually_lt_const`, `Filter.eventually_ge_atTop`, `lt_div_iff₀`,
plus batch-1 `Chain.link_nonempty`, `Chain.adjacent_iff`, `Chain.Refines.trans`,
`Chain.isCrookedIn'_of_refines`, `Chain.diam_le_length_mul`, `Chain.exists_value_between`.

### `HPC/PseudoArc/Uniqueness.lean`

Commissioned:

| name | status |
|---|---|
| `Chain.pattern_matching` | proved |
| `Chain.diam_le_of_followsPattern` | proved |
| `Chain.diam_le_of_refines` | proved |
| `Chain.exists_pattern_of_refines` | proved |
| `Description.exists_homeomorph` | proved (Theorem 12, conditional on `PatternFollowing`) |

Added (the machinery of §3 of the commission):

* `Description.CanFollow Δ lv C` — every pattern in the chain `C` is followed by a
  consolidation of a level of `Δ` deeper than `lv`. This is the property of one side of the
  construction that permits the *other* side to be refined.
* `Description.canFollow_level` — `PatternFollowing` gives `CanFollow` for a level.
* `Description.M_subset_consolidation`, `Description.consolidation_link_inter_M_nonempty` —
  conditions (1) and (2) of Theorem 11 for a consolidation of a level.
* `Description.exists_half_step` — one half-step, stated over two arbitrary spaces so that it
  can be applied with the two sides in either order.
* `Rung` (structure) — one level of the alternating construction: two chains with the same
  number of links, one in each space, each from its `P` to its `Q` and a consolidation of a
  level of its description, with a common mesh bound `mesh`, and with one of the two sides
  distinguished as the one that `CanFollow` and carries the sharper bound `mfollow`.
* `Rung.exists_base`, `Rung.exists_next` — level `0`, and the step.

Mathlib used: `Metric.diam_mono`, `Metric.dist_le_diam_of_mem`, `isBounded_of_compactSpace`,
`Set.subset_biUnion_of_mem`, `Filter.Tendsto.eventually_lt_const`,
`Filter.Tendsto.eventually_ge_atTop`, `summable_nat_add_iff`, `summable_geometric_two`,
`max_eq_right`, `pow_pos`, `Nat.rec`, `Continuous.homeoOfEquivCompactToT2` (through batch 2),
plus batch-1 `Chain.link_nonempty`, `Chain.adjacent`, `Chain.refineIdx`,
`Chain.refineIdx_subset`, `Chain.pattern_lipschitz`, `Chain.exists_consolidation_isFrom`, and
batch-2 `MatchingCovers.exists_homeomorph`.

## 2. Changes to the skeleton

**None to any commissioned statement.** Both files compiled as received (with the proofs still
`sorry`) with no change to syntax or mathlib names; nothing had to be renamed, reordered or
restated. The only edits to the supplied text are the removal of the two "Uncompiled / every
`sorry` is a work item" sentences from the module docstrings, and the insertion of the §3
machinery listed above between `Chain.exists_pattern_of_refines` and
`Description.exists_homeomorph`.

No commissioned hypothesis turned out to be unnecessary in batch 3, so — unlike batches 1 and
2 — there is no underscore-named hypothesis to report.

Two commissioned statements are proved but not used further in this batch:
`Chain.diam_le_of_refines` and `Description.crooked_of_lt`. The crookedness field of a
`Description` is likewise not used by Theorem 12 itself: in Bing's argument crookedness enters
only through Theorem 6, which is the hypothesis `PatternFollowing` here. This is a property of
the conditional statement as commissioned, not a weakening of it.

## 3. What was supplied at each step

**§2, properties of a description.** As in the commission. Three points are worth recording.

* `exists_closure_link_subset`: the case `s = 0` is taken separately (the first link of level
  `i+1` is the witness, since the closure-refinement map `χ` sends it to the first link of
  level `i`); for `s > 0` the witness comes from the one-sided discrete intermediate value
  theorem of `HPC/Chains/Aux.lean`, transported to chains by batch-1
  `Chain.exists_value_between`, applied between the last index of level `i+1` (where `χ` is
  `n i − 1 ≥ s`) and the first (where `χ` is `0 < s`). That `χ` sends first link to first and
  last to last is exactly the uniqueness clauses of `IsFrom` at level `i`.
* `link_inter_M_nonempty`: the nested sequence of links is built by `Nat.rec` over the choice
  function extracted from `exists_closure_link_subset`, the recursion being type-correct
  because `i + (k+1)` and `(i + k) + 1` are definitionally equal. The common point lies in
  `closure ℓ_{k+1} ⊆ ℓ_k`, which is what puts it in the *open* link `ℓ_0` and in every level's
  union, including the levels below `i` via `refines_of_le`.
* `n_tendsto_atTop`: batch-1 T7 is applied with `ε := 2 · ε i` so that its strict inequality
  `diam (link) < ε` is available from the non-strict `diam_le` of the description.

**§3, Theorem 12.** The construction is carried out exactly as in the commission, taking
option (a): the side to which pattern following is applied is always a level of its
description. It is organised so that no parity argument is needed anywhere.

* A `Rung` records *which* side can currently follow patterns, as a disjunction; the step
  `Rung.exists_next` splits on that disjunction and closes each branch by the same lemma
  `Description.exists_half_step`, instantiated with the two spaces in the two possible orders.
  The side that could follow keeps its mesh bound (it follows a pattern in its predecessor,
  `Chain.diam_le_of_followsPattern`) and loses the ability; the side that was refined is now a
  level, so it can follow, and its mesh is the `δ` of the step. The `Rung` sequence is then an
  ordinary `Nat.rec` iteration, and the alternation is invisible to the rest of the proof.
* Mesh bookkeeping: the step is called with `δ k = (1/2)^(k+2)` and returns a rung with
  `mfollow = (1/2)^(k+2)` and `mesh = max ((1/2)^(k+2)) (previous mfollow)`. With
  `mfollow` of the base rung equal to `1/2` this gives `mfollow k = (1/2)^(k+1)` and
  `mesh (k+1) = (1/2)^(k+1)` for every `k`, so `ε' i := 2 · mesh i` is positive and summable
  (its shift by one is the geometric series `(1/2)^k`; the value at `0`, which involves the
  diameter of the whole of `X₂`, is finite and irrelevant to summability). Every link at level
  `i` on either side has diameter `≤ mesh i < ε' i`, which is both condition (3) of Theorem 11
  and the strict bound needed by `Chain.pattern_matching`.
* Base rung: a level `Δ₁.D a` with `Δ₁.ε a < 1/2` and `Δ₁.ε a < dist P₁ Q₁` (so that
  `two_le_n_of_lt` applies), matched on side 2 by batch-1 T6 against a level of `Δ₂` with at
  least that many links, which exists by `n_tendsto_atTop`.
* Conditions (1) and (2) of Theorem 11 hold at every rung because both sides are
  consolidations of levels (`M_subset_consolidation`, `consolidation_link_inter_M_nonempty`);
  condition (4), in both directions, is `Chain.pattern_matching` applied to the common pattern
  recorded by the step.
* Tracking: at every rung and on both sides, `P` lies in link `0` and `Q` in the last link, so
  the constant index sequence `i ↦ 0` tracks `P₁` and `P₂`, and `i ↦ N i − 1` tracks `Q₁` and
  `Q₂`; the tracking clause of batch-2 Theorem 11 then gives `T P₁ = P₂` and `T Q₁ = Q₂`.

No statement failed to go through, and none was weakened or replaced.

## 4. Axiom profiles

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of:

`Chain.union_subset_of_refines`, `Chain.isConsolidationOf_self`, `Description.P_mem_M`,
`Description.Q_mem_M`, `Description.two_le_n_of_lt`, `Description.refines_of_le`,
`Description.closure_union_subset`, `Description.isClosed_M`, `Description.isCompact_M`,
`Description.crooked_of_lt`, `Description.exists_closure_link_subset`,
`Description.link_inter_M_nonempty`, `Description.M_subset_union`, `Description.isBounded_M`,
`Description.n_tendsto_atTop`, `Description.exists_level_refining`, `Chain.pattern_matching`,
`Chain.diam_le_of_followsPattern`, `Chain.diam_le_of_refines`,
`Chain.exists_pattern_of_refines`, `Description.canFollow_level`,
`Description.M_subset_consolidation`, `Description.consolidation_link_inter_M_nonempty`,
`Description.exists_half_step`, `Rung.exists_base`, `Rung.exists_next`,
`Description.exists_homeomorph`.

## 5. Not in this batch

Theorem 6 (the `PatternFollowing` hypothesis), Theorems 3, 4, 5; the reduction in Bing 1951;
the D8/D9 gap.
