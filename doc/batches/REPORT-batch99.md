Commission read: `COMMISSION-batch99.md` (batch 99: closing Bing's Theorem 10 (Duke 1951) with Fugate's counting argument). Its skeleton `LastLink99.lean` is saved as `HPC/Plane/LastLink99.lean`, and `import HPC.Plane.LastLink99` is added at the end of `HPC.lean`.

# Report, batch 99

## Summary

* **Refutation first.** The skeleton's `lastLink_of_minimal` is **false as stated**, in the
  degenerate case `K = {p}`. `lastLink_of_minimal_skeleton_false` proves its negation, with
  `D = (ℝ, ℝ)`, `K = {0}`, `p = 0`, `F = (ℝ)`. All hypotheses hold, and `F` has the least possible
  length (one), but `K` has no point other than `p`. This is the small case the commission flags
  in item 2, step 1 (`m = 2`, `p ∈ d₁ ∩ d₂`).
* **Item 2, corrected shape: proved.** `lastLink_of_minimal` adds the hypothesis `K.Nontrivial`.
  The hypotheses `hK` (`K` is a continuum) and `hpK` (`p ∈ K`) are not used and are removed.
* **Item 1 (`exists_link_in_between`): proved**, in the skeleton's shape minus the unused
  hypothesis `hFD`.
* **Item 3 (`exists_minimal_T10Chain`): proved**, using `Nat.find`.
* **Item 4 (`theorem10_1951'`): proved, in the skeleton's shape. So Bing's Theorem 10 (Duke 1951,
  p. 659) is now proved with standard axioms and no `sorry`.**
* **The edit to `EndPoints51.lean` cannot be made.** Replacing the `sorry` of `theorem10_1951` by
  `theorem10_1951' hM D hD hp` would create an import cycle. `LastLink99` needs the surgery
  `theorem10_1951_of_lastLink` (`Surgery91.lean`), and `Surgery91.lean` imports `EndPoints51.lean`
  through `CondB`. As the commission allows, `EndPoints51.lean` is **left unchanged** and
  `theorem10_1951'` is the `sorry`-free form. For the same reason, `endPoint_of_condA` keeps its
  `sorryAx`. Its proof is repeated, unchanged except that it calls `theorem10_1951'`, as
  `endPoint_of_condA'` in `LastLink99.lean`, which is `sorry`-free. That is Theorem 13,
  sufficiency for condition A.
* **Flags A–C do not arise.** The shortening is built differently from Fugate's `D(y,x) ∩ F*(t,j)`
  (details below). No `∩`-convention is needed, the junction is automatic, and `p` stays in the
  first link only.
* **Axioms** (`Axioms99.lean` writes `axioms-batch99.txt`). Every batch-99 declaration uses only
  `propext`, `Classical.choice` and `Quot.sound`. Downstream, after the change:
  * `theorem10_1951` and `endPoint_of_condA` (`EndPoints51.lean`) still use `sorryAx`, since the
    file could not be edited. Their replacements `theorem10_1951'` and `endPoint_of_condA'` are
    clean.
  * `theorem11_1951_of_T10` was already clean: it takes Theorem 10 as the hypothesis `hT10`. That
    hypothesis is now discharged by `theorem10_1951'`. Its other hypothesis `hdeg` is the
    refuted Q-deg (batch 97), so this does **not** yield Theorem 11.
  * `theorem11_1951_of_T10'` is unchanged (`sorry`, not attempted, per §3). Its only hypothesis,
    `hT10`, is now a theorem, so a proof of it would prove Theorem 11 outright.

## The argument (item 2) and how it avoids flags A–C

Notation: `F = (f_0, …, f_{k−1})` is a least-length Theorem-10 chain for `K` from `p`, refining
`D = (d_0, …, d_{m−1})`. For each `i`, `a i` is a choice of `D`-index with `f_i ⊆ d_{a i}`.
Consecutive values of `a` differ by at most one (`clampVal_step`).

**The shortening (`exists_shorter_T10Chain`).** Suppose that for some `j`, the value `a j` is
extreme (a minimum or a maximum) among `a j, …, a (k−1)`, and that some value repeats in that
range. Keep `f_0, …, f_{j−1}`. Replace the tail by the chain whose links are
`g_e = ⋃ {f_i : i ≥ j, |a i − a j| = e}`, for `e = 0, …, E`. This is the block consolidation
`Chain.ofBlocks` (batch 4) along the block map `β i = i` for `i < j` and `β i = j + |a i − a j|`
for `i ≥ j`.
* `β` is surjective by the discrete intermediate value theorem.
* `β` moves by at most one per step.
* `β` is constant-`a` on each block, because `a j` is extreme. So each block lies in one link of
  `D`, and the new chain refines `D`.
* It covers everything `F` covered.
* `p ∈ f_0 ⊆` the first link. `p` is not in the closure of any other link, since each of those is a
  finite union of links `f_i` with `i ≠ 0`.
* It has `j + E + 1` links. This is fewer than `k`, because the tail of `k − j` links maps onto
  `E + 1` values with at least one collision (a counting argument via `Finset.card_image_le`).

The new links are unions of tail links of `F`, not intersections `d_i ∩ F*(t, j)`:
* **Flag A** does not arise: no `∩`-convention is used.
* **Flag B** does not arise. The only earlier link that meets the tail is `f_{j−1}`, and it meets
  only `f_j`, so it meets only the block of `f_j`. That block is the first one, `e = 0`, because
  `a j` is extreme.
* **Flag C** does not arise. When `j = 0` the first block contains `f_0 ∋ p`. All other blocks are
  unions of links `f_i` with `i ≥ 1`.

**The combinatorial core (`exists_extreme_repeat`).** Let `g` move by at most one per step, and let
`g N` lie between `g u` and `g v` with `u ≤ v < N`. Then some `j < N` has `g j` extreme on
`[j, N]`, and the value `g N` occurs again in `[j, N)`. Proof: let `L` and `H` be the minimum and
maximum of `g` on `[u, N]`.
* If `g N = L`: `L` is attained at `u` or at `v`; take `j` to be that index.
* If `g N = H`: the same argument.
* Otherwise `L < g N < H`. Take `j` to be the earlier of an index attaining `L` and an index
  attaining `H`. The intermediate value theorem gives an index between them with value `g N`, and
  that index is not `N`.

**`lastLink_of_minimal`.** Suppose, for contradiction, that no point of `K ∖ {p}` lies in
`f_{k−1} ∩ (d_0 ∪ d_{m−1})`.
1. *A point `y ≠ p` of `K` in `f_{k−1}`.*
   * If `k = 1`, this is where `K.Nontrivial` is used.
   * If `k ≥ 2` and `f_{k−1}` misses `K`, dropping `f_{k−1}` gives a shorter chain (`F.sub`).
   * Otherwise take any point of `K ∩ f_{k−1}`; it is not `p`, because `p ∉ cl f_{k−1}`.
2. Hence `r = a (k−1)` satisfies `1 ≤ r ≤ m − 2`, and so `m ≥ 3`.
3. *Two more links.* Pick `z₀ ∈ K ∩ d_0` in `f_{i₀}` and `z₁ ∈ K ∩ d_{m−1}` in `f_{i₁}`. Neither
   `i₀` nor `i₁` is `k − 1`. If `k = 1`, both points would have to be `p`, but `d_0 ∩ d_{m−1} = ∅`.
   We have `a i₀ ≤ 1 ≤ r ≤ m − 2 ≤ a i₁`.
4. *Contradiction.* The combinatorial core, applied with `u, v = min/max(i₀, i₁)` and
   `N = k − 1`, gives `j`. The shortening then gives a shorter Theorem-10 chain, which contradicts
   minimality.

The last links `f_t`, `f_s` in Fugate's text are not needed: any links meeting `K ∩ d_0` and
`K ∩ d_{m−1}` will do.

## Item 4: the assembly (`theorem10_aux`)

The proof is by strong induction on the length `m` of `D`. Fix `D` and suppose the theorem fails
for some `M`.
1. **Minimal counterexample (Zorn).** Apply Zorn to the subcontinua `W ⊆ M` through `p` for which
   it fails. The lower bound of a nested family is its intersection:
   * The intersection is a continuum by `isPreconnected_sInter_chain'`. This is a new version of
     the batch-13 lemma, without `CompactSpace`.
   * The theorem fails for it. If a chain `E` covered the intersection, some member would already
     lie in the open set `E.union` (`exists_subset_nhds_of_isCompact'`).

   Let `M'` be minimal. Condition A passes to `M'`.
2. **`M'` meets every link of `D`.** If `M'` missed `d_0`, the subchain `D(1..m−1)`, which is
   shorter, would cover `M'`. The induction hypothesis would then give a chain refining that
   subchain, hence refining `D`. The case of `d_{m−1}` is the same. Once `M'` meets both end
   links, it meets every link (`Chain.inter_link_nonempty_between`).

   No trimming of `D` is needed, so the commission's concern about the trimmed chain and the final
   refinement does not arise.
3. **Small cases.** If `m = 1`, `D` itself is a Theorem-10 chain. If `M' = {p}`, the one-link
   subchain `D(i₀..i₀)` through `p` is one.
4. **`K`.** `K` is the larger of two proper subcontinua through `p`; they are nested by condition
   B:
   * one from `exists_proper_meeting_all_links` (batch 91), which meets every link;
   * one from `exists_proper_subcontinuum_meeting` with `O = {p}ᶜ`, which is nondegenerate.

   So `K` is proper, nondegenerate and meets every link. This handles the `m = 2`,
   `M'' = {p}` case flagged in the commission.
5. **Conclusion.** By the minimality of `M'`, `K` has a Theorem-10 chain. Take a least one
   (item 3). By item 2, its last link meets `K ∩ (d_0 ∪ d_{m−1})` at some `y ≠ p`. The surgery
   `theorem10_1951_of_lastLink`, or its mirror form, then gives a Theorem-10 chain for `M'`, which
   is a contradiction.

## Shape changes recorded

| declaration | change |
|---|---|
| `exists_link_in_between` | unused hypothesis `hFD` removed |
| `lastLink_of_minimal` | `K.Nontrivial` added (the original is refuted); unused `hK`, `hpK` removed |
| `exists_minimal_T10Chain`, `theorem10_1951'`, `IsT10Chain` | unchanged |

New declarations:
* `clampVal`, `clampVal_of_lt`, `clampVal_step`;
* `exists_extreme_repeat`, `exists_shorter_T10Chain`;
* `isPreconnected_sInter_chain'`, `subset_sub_union`, `refines_of_refines_sub`;
* `theorem10_aux`, `endPoint_of_condA'`;
* `univChainR`, `lastLink_of_minimal_skeleton_false`.

## Files

* `HPC/Plane/LastLink99.lean` (new): the skeleton, completed. It contains no `sorry`.
* `HPC.lean`: the import line is added.
* `Axioms99.lean`, `axioms-batch99.txt` (new).
* No other existing file is edited. In particular `EndPoints51.lean` is unchanged, because of the
  import cycle explained above.

## Not attempted (per §3)

`covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`,
`isArc_of_separatesPairs`, `exists_degenerate_interior_elt`, `theorem11_1951_of_T10'`.
