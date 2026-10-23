# Report — batch 5: schedules and the range-covering lemma

Delivered complete. `lake build` succeeds on `RequestProject` and `HPC`; the new file
`HPC/Chains/Schedule.lean` contains no `sorry`, `admit`, `axiom`, `native_decide` or
`implemented_by`, and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`
for every one of its theorems (list in §4).

Nothing outside `HPC/Chains/Schedule.lean` was touched except the root `HPC.lean`, which is the
one supplied with the batch. The batch-5 commission text is kept as `COMMISSION-batch5.md`.

## 1. Census

Commissioned:

| name | status |
|---|---|
| `Chain.unionRange` | as commissioned |
| `Chain.IsSchedule` | as commissioned |
| `Chain.IsSchedule.exists_blockMap` | proved |
| `Chain.exists_blocks_of_schedule` | proved |
| `Chain.schedule_of_blocks` | proved |
| `Chain.exists_blocks_of_walk` | proved |
| `Chain.range_covering` | proved |

Added (not commissioned, needed by the proofs):

* `HPC.exists_eq_of_lip_mono`, `HPC.exists_eq_of_lip_anti`, `HPC.exists_eq_of_lip` (private) —
  the discrete intermediate value theorem *on `Fin m`*: a function `Fin m → ℕ` moving by at most
  one between adjacent indices attains every value between two of its values. The lemmas of
  `HPC/Chains/Aux.lean` are stated for functions on all of `ℕ`, and transporting a function on
  `Fin m` to `ℕ` requires a clamping argument that is longer than the direct induction on the
  distance between the two indices; the direct induction is what is used. The unoriented form
  `exists_eq_of_lip` is the one the surjectivity of a schedule needs, since `0` and the maximum
  may be attained in either order.
* `Chain.mem_unionRange` — the membership criterion for `unionRange`, unfolding the double
  indexed union into `∃ j', j ≤ j' < j + w ∧ j' < n ∧ x ∈ D.link ⟨j', _⟩`.
* `Chain.link_subset_unionRange` — a single link whose index lies in the window is contained in
  the window.

Mathlib used: `Finset.exists_max_image`, `Finset.exists_min_image`, `Finset.mem_Ico`,
`Finset.mem_filter`, `Finset.mem_univ`, `Set.mem_iUnion`, `Set.subset_biUnion_of_mem`,
`Fin.ext`, `Fin.isLt`, `Fin.le_def`, `not_le`, `lt_trans`, `le_trans`, plus `omega`, `simp`,
`push_neg`, `norm_num`. Batch-1 results used: `Chain.link_nonempty`, `Chain.Between`,
`Chain.IsCrookedIn'`, `Chain.Refines`. Batch-4 results used: `Chain.IsBlockMap`,
`Chain.ofBlocks`, `Chain.ofBlocks_link`, `Chain.Refines.minIdx`, `Chain.minIdx_subset`,
`Chain.minIdx_le`, `Chain.subset_adjacent_of_subset`, `Chain.minIdx_near_of_inter`.

## 2. Changes to the skeleton

None. Every commissioned statement is delivered verbatim as received, with the same names,
hypotheses and conclusions; only the `sorry`s were replaced. No commissioned hypothesis turned
out to be unnecessary: `hw : 1 ≤ w` is used in `exists_blocks_of_schedule` (with `w = 0` the
window `[j, j)` is empty and the conclusion fails), and `hm : 0 < m` is used in
`schedule_of_blocks` to know `0 < p`, without which `IsSchedule.zero` is false.

`Chain.minIdx_lip` is listed in the protocol as expected to be used; in the event it is not
needed, because the Lipschitz clause of every schedule produced here comes from the block map
(`IsBlockMap.lip`) rather than from `minIdx`. Likewise the discrete intermediate value lemmas of
`Aux` are replaced by the `Fin m` versions described in §1.

## 3. What was supplied at each step

* **`IsSchedule.exists_blockMap`.** `M := β tM` for a maximiser `tM` supplied by
  `Finset.exists_max_image` on `Finset.univ`, nonempty because `β` attains `0`; `p := M + 1` and
  `β' t := ⟨β t, _⟩`. The Lipschitz clause is `hβ.lip` verbatim, since `(β' t).val = β t` by
  `rfl`. Surjectivity: for `u : Fin p` one has `β t₀ = 0 ≤ u.val ≤ M = β tM`, so
  `exists_eq_of_lip` (§1) produces `t` with `β t = u.val`, i.e. `β' t = u` by `Fin.ext`.
* **`exists_blocks_of_schedule`.** As commissioned. The fiber is the `Finset`
  `univ.filter (β' · = u)`, nonempty by surjectivity; `Finset.exists_min_image` supplies the link
  `tmin` of the fiber with least `minIdx`, and `j := (minIdx tmin).val`. For `t` in the fiber,
  `β t = β tmin` (the values of `β'` determine those of `β`), so `hwin` gives
  `minIdx t ≤ j + (w − 1) < j + w`, while minimality gives `j ≤ minIdx t`; hence
  `E.link t ⊆ D.link (minIdx t) ⊆ unionRange j w` by `minIdx_subset` and
  `link_subset_unionRange`. The union over the fiber is the block by `ofBlocks_link`.
* **`schedule_of_blocks`.** `0 < p` because `Fin m` is nonempty and `β'` lands in `Fin p`;
  `IsSchedule.zero` is then surjectivity applied to `⟨0, _⟩`, and `IsSchedule.lip` is
  `hβ'.lip`. The window claim is isolated as the auxiliary `key`: if `β' t = u` and the block `u`
  lies in `unionRange j w`, then `j − 1 ≤ minIdx t ≤ j + w − 1` in `ℤ` (which is how the two
  truncated subtractions of the English argument are avoided). Lower end: `E.link t` is nonempty,
  a point of it lies in some `D.link j'` with `j ≤ j' < j + w`, and `minIdx_near_of_inter` gives
  `|minIdx t − j'| ≤ 1`. Upper end: the same inequality gives `minIdx t ≤ j + w`, and the value
  `j + w` is excluded exactly as in the commission — if `minIdx t = j + w` then *every* point of
  `E.link t` lies in a link `D.link j'` of the window with `|j + w − j'| ≤ 1`, forcing
  `j' = j + w − 1`, so `E.link t ⊆ D.link ⟨j + w − 1⟩` and `minIdx_le` contradicts
  `minIdx t = j + w`. Applying `key` to `t` and to `t'` with the same block gives two values in an
  interval of length `w`.
* **`exists_blocks_of_walk`.** `exists_blocks_of_schedule` with `w := 3`; the window hypothesis
  is `hb t` and `hb t'` combined, using `β t = β t'` so that both are measured against the same
  value `b (β t)`.
* **`range_covering`, the four extremal indices.** `Finset.exists_min_image` and
  `Finset.exists_max_image` on `univ.filter (· ≤ i)` and `univ.filter (i ≤ ·)`, both nonempty
  because they contain `i`; this gives `tlo, thi, glo, ghi` together with the extremality
  statements, and the memberships of `i` give `lo_T ≤ ρ i ≤ hi_T` and `lo_G ≤ ρ i ≤ hi_G`.
* **`range_covering`, the four equivalences.** Only the direction that is used is needed, and it
  is immediate: the witness for every clause is one of the four extremal indices. For instance
  `lo_G ≤ lo_T + 1` gives `∀ t ≤ i, ∃ g ≥ i, ρ g ≤ ρ t + 1` by taking `g := glo`, since
  `ρ glo = lo_G ≤ lo_T + 1 ≤ ρ t + 1`; the other three are the same with `ghi`, `tlo`, `thi`.
* **`range_covering`, Claims A and B.** As in the commission. The `Between` alternative is
  resolved by transitivity: in Claim A the second alternative would give `ghi < tlo`, contradicting
  `tlo ≤ i ≤ ghi`, and dually in Claim B. The step "`ρ r ≥ hi_G − 2`" is
  `subset_adjacent_of_subset` applied to the two containments `E.link r ⊆ D.link (ρ r)` and
  `E.link r ⊆ D.link ⟨hi_G − 1⟩`; the step "`ρ s ≤ lo_T + 1`" is `minIdx_le`. All remaining
  arithmetic, including the truncated subtraction `hi_G − 1`, is `omega`.
* **`range_covering`, the conclusion.** The case split of the commission: on
  `lo_T + 2 ≤ lo_G` (Claim A gives the second disjunct) and, failing that, on
  `hi_G + 3 ≤ hi_T` (Claim B gives the second disjunct, otherwise the first disjunct holds
  outright).

## 4. Axiom profiles

`#print axioms` returns `[propext, Classical.choice, Quot.sound]` for each of
`Chain.mem_unionRange`, `Chain.link_subset_unionRange`, `Chain.IsSchedule.exists_blockMap`,
`Chain.exists_blocks_of_schedule`, `Chain.schedule_of_blocks`, `Chain.exists_blocks_of_walk`,
`Chain.range_covering`. No decision procedure beyond `omega` is used; `native_decide` and
`decide` do not appear.

## 5. Statements that did not go through

None. Every commissioned statement was proved with its meaning unchanged.
