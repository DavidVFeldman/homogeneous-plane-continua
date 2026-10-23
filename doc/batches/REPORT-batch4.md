# Report — batch 4: consolidation infrastructure

Delivered complete. `lake build` succeeds on `RequestProject` and `HPC`; the new file
`HPC/Chains/Consolidation.lean` contains no `sorry`, `admit`, `axiom`, `native_decide` or
`implemented_by`, and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`
for every one of its 28 theorems (list in §4).

Nothing outside `HPC/Chains/Consolidation.lean` was touched except the root `HPC.lean`, which is
the one supplied with the batch. The batch-4 commission text is kept as `COMMISSION-batch4.md`.

## 1. Census

Commissioned:

| name | status |
|---|---|
| `Chain.IsBlockMap` | as commissioned |
| `Chain.ofBlocks`, `Chain.ofBlocks_link` | as commissioned |
| `Chain.ofBlocks_isConsolidationOf` | proved |
| `Chain.reverse` | as commissioned |
| `Chain.reverse_reverse` | proved |
| `Chain.Refines.reverse_left`, `Chain.Refines.reverse_right` | proved |
| `Chain.IsCrookedIn'.reverse_left`, `Chain.IsCrookedIn'.reverse_right` | proved |
| `Chain.IsCrookedIn'.sub`, `Chain.IsCrookedIn'.restrict` | proved |
| `Chain.subset_adjacent_of_subset` | proved (hypothesis `h` unused, see §2) |
| `Chain.Refines.minIdx`, `Chain.minIdx_subset`, `Chain.minIdx_le` | proved (encoding changed, §2) |
| `Chain.Refines.maxIdx`, `Chain.maxIdx_subset`, `Chain.le_maxIdx` | proved |
| `Chain.minIdx_lip`, `Chain.maxIdx_lip` | proved |
| `Chain.minIdx_near_of_inter` | proved |
| `Chain.group` | as commissioned |
| `Chain.Refines.monoBlocks` | as commissioned (built by choice, §2) |
| `Chain.monoBlocks_spec` | proved |
| `Chain.exists_blocks_first_last` | proved |
| `Ecx`, `Dcx` | as commissioned |
| `Dcx_refines`, `Dcx_isCrookedIn'` | proved |
| `not_exists_strong_first_block` | proved |

Added (not commissioned, needed by the proofs):

* `HPC.exists_adjacent_cross_mono`, `HPC.exists_adjacent_cross` — the "first index where the
  value crosses" lemma the commission points to, in the sharper form the adjacency proof of
  `ofBlocks` needs: a `1`-Lipschitz `g : ℕ → ℤ` passing from a value `≤ p` to a value `≥ p + 1`
  takes the values `p` and `p + 1` at two *adjacent* indices between the two given ones (in one
  order or the other). The lemmas of `HPC/Chains/Aux.lean` produce two indices in order but not
  adjacent ones, which is not enough here.
* `Chain.blockLink_adjacent` — the adjacency condition for the links of a block consolidation,
  stated for the raw unions so that it can be used as the `adjacent` field of `ofBlocks`.
* `Chain.reverse_link` — `D.reverse.link i = D.link (Fin.rev i)`, a `simp` lemma.
* `Chain.minIdx_set_nonempty` — the set of indices of links of `D` containing `E.link t` is a
  nonempty set of naturals; this is what `minIdx` takes the infimum of.
* `Chain.Refines.exists_monoBlocks` — the monotone grouping lemma in existential form (§2).
* `Dcx_mem_bounds` — every link of `Dcx` lies in the interval `(2.2, 6.8)`, the one interval
  computation behind `Dcx_isCrookedIn'`.

Mathlib used: `Nat.find`, `Nat.find_spec`, `Nat.find_min`, `Nat.find_le`, `Nat.sInf_mem`,
`Nat.sInf_le`, `Finset.exists_min_image`, `Finset.exists_max_image`, `Fin.rev`, `Fin.rev_rev`,
`Fin.val_rev`, `Fin.rev_le_rev`, `Fin.ext`, `isOpen_biUnion`, `Set.mem_biUnion`,
`Set.subset_biUnion_of_mem`, `Set.iUnion₂_subset`, `Set.subset_union_left/right`,
`Set.Ioo_inter_Ioo`, `Set.nonempty_Ioo`, `Set.Ioo_subset_Ioo`, `isOpen_Ioo`, plus `omega`,
`norm_num`, `linarith`, `fin_cases`, and the batch-1 results `Chain.link_nonempty`,
`Chain.adjacent_iff`, `Chain.sub`, `Chain.Between.symm`.

## 2. Changes to the skeleton

1. **`minIdx`, `maxIdx`, `monoBlocks` are declared in the `Chain.Refines` namespace.** The
   skeleton writes `h.minIdx t` for `h : E.Refines D`, which resolves to `Chain.Refines.minIdx`;
   declared as `Chain.minIdx` the dot notation does not elaborate. The three definitions are
   therefore `Chain.Refines.minIdx`, `Chain.Refines.maxIdx`, `Chain.Refines.monoBlocks`. All
   theorem names and all statements are unchanged.
2. **`minIdx` is defined by least element rather than `Nat.find`.** `minIdx h t` is
   `sInf {j | ∃ hj : j < n, E.link t ⊆ D.link ⟨j, hj⟩}`, with the bound `sInf … < n` read off
   `Nat.sInf_mem`. This is the encoding change the commission permits; it avoids carrying a
   decidability instance through every later proof. The specification (`minIdx_subset`,
   `minIdx_le`) is exactly as commissioned, and it is those two properties that every later
   proof uses.
3. **`monoBlocks` is a choice of a block map satisfying the specification.** The construction is
   carried out in `Chain.Refines.exists_monoBlocks`, which states the three properties of
   `monoBlocks_spec` existentially; `monoBlocks` is then the chosen witness and `monoBlocks_spec`
   is its specification. This keeps the `Σ`-typed signature of the commission and makes the
   `let ⟨p, β, hβ⟩ := …` of `monoBlocks_spec` reduce definitionally.
4. **`subset_adjacent_of_subset` does not use its refinement hypothesis.** Both containments
   are given, and a link of `E` is nonempty, so the two links of `D` meet. Following the batch-1
   and batch-2 convention the hypothesis is kept as commissioned and renamed `_h`.
5. No other change: no statement was weakened, none failed to go through, and no mathlib name
   in the skeleton needed adjusting.

## 3. What was supplied at each *(supply)* marker

* **`IsCrookedIn'.reverse_right`, the index arithmetic.** With `H := rev k` and `K := rev h` one
  has `H + 2 < K` exactly when `h + 2 < k`; the hypothesis applied to the pair `(H, K)` with the
  roles of `i` and `j` exchanged returns `r, s` with `Between j r s i`, and `Between.symm` turns
  this into `Between i s r j`. The two containments match after the two index identities
  `rev ⟨k − 1⟩ = ⟨(rev k) + 1⟩` and `rev ⟨h + 1⟩ = ⟨(rev h) − 1⟩`, both `Fin.ext` plus
  `Fin.val_rev` and `omega`.
* **`monoBlocks_spec`, the case split on `v` and the arithmetic of `group`.** With
  `g t = group n (minIdx t)`, `g₀` its minimum, `g₁` its maximum, `p = g₁ − g₀ + 1` and
  `β t = g t − g₀`, a block `u` collects the links with `g t = v := u + g₀`, and `v ≤ g₁ ≤ n − 3`.
  If `v = 0` then `min (a − 1) (n − 3) = 0` with `n − 3 ≥ 1`, so the minimal index `a` is `0` or
  `1` and the block lies in `D.link 0 ∪ D.link 1`. If `1 ≤ v < n − 3` then `a − 1 = v`, so `a` is
  exactly `v + 1` and the block lies in `D.link (v+1) ∪ D.link (v+2)`. If `v = n − 3` then
  `a ≥ n − 2`, so `a` is `n − 2` or `n − 1` and the block lies in `D.link (n−2) ∪ D.link (n−1)`.
  For the last two clauses: `a ≤ 1` forces `g t = 0`, which is the least possible value, so
  `g₀ = 0` and `β t = 0`; `a ≥ n − 2` forces `g t = n − 3`, which is the greatest possible value,
  so `g₁ = n − 3` and `β t = p − 1`. Surjectivity of `β` is the discrete intermediate value
  argument: `g` moves by at most one between adjacent links (`minIdx_lip`, plus the fact that
  `j ↦ min (j − 1) (n − 3)` is monotone with increments `≤ 1`), so it attains every value
  between `g₀` and `g₁`. The degenerate case `m = 0` is handled separately with `p = 0`.
* **`ofBlocks`, adjacency.** As in the commission, with `exists_adjacent_cross` (§1) supplying
  the crossing: walking from a link of block `u` to a link of block `u + 1`, two *adjacent*
  indices of `D` carry the values `u` and `u + 1`, and the corresponding links of `D` meet.

## 4. Axiom profiles

`#print axioms` returns `[propext, Classical.choice, Quot.sound]` for each of:

`exists_adjacent_cross_mono`, `exists_adjacent_cross`, `Chain.blockLink_adjacent`,
`Chain.ofBlocks_link`, `Chain.ofBlocks_isConsolidationOf`, `Chain.reverse_reverse`,
`Chain.Refines.reverse_left`, `Chain.Refines.reverse_right`, `Chain.IsCrookedIn'.reverse_left`,
`Chain.IsCrookedIn'.reverse_right`, `Chain.IsCrookedIn'.sub`, `Chain.IsCrookedIn'.restrict`,
`Chain.subset_adjacent_of_subset`, `Chain.minIdx_set_nonempty`, `Chain.minIdx_subset`,
`Chain.minIdx_le`, `Chain.maxIdx_subset`, `Chain.le_maxIdx`, `Chain.minIdx_lip`,
`Chain.maxIdx_lip`, `Chain.minIdx_near_of_inter`, `Chain.Refines.exists_monoBlocks`,
`Chain.monoBlocks_spec`, `Chain.exists_blocks_first_last`, `Dcx_refines`, `Dcx_mem_bounds`,
`Dcx_isCrookedIn'`, `not_exists_strong_first_block`
(plus `Chain.reverse_link`, which is `rfl`).

The only decision procedure used is the kernel's `decide`, once, to discharge the impossible
index `j = 4` in `not_exists_strong_first_block`; `native_decide` is not used anywhere.

## 5. Statements that did not go through

None. Every commissioned statement was proved with its meaning unchanged.
