Commission read: `COMMISSION-batch85.md` (batch 85 — Bing 1951, part two: Theorem 10 and the end-point theorems of §5), with its skeleton `EndPoints51.lean` (saved as `HPC/Plane/EndPoints51.lean`; `import HPC.Plane.EndPoints51` added at the end of `HPC.lean`). This batch was run after batches 86 and 87, on the same workspace.

# Report — batch 85

**Summary.**
* **Counterexamples: none.** No statement of the skeleton was found to be false.
* Of the seven statements, **six are proved with no `sorry`**: `condB_of_condA`, `condB_of_endPoint`, `theorem14_1951`, `theorem15_1951`, `exists_not_endPoint_of_not_HI`, and `endPoint_of_condA` *modulo* `theorem10_1951`.
* **`theorem10_1951` is open** (`sorry`). So `endPoint_of_condA`, which is proved from it, depends on `sorryAx`. Its own proof is complete: all the remaining work is Theorem 10.
* `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every proved result. `theorem10_1951` and `endPoint_of_condA` also list `sorryAx`. The output is in `axioms-batch85.txt`, produced by `lake env lean Axioms85.lean`.
* `lake build HPC` completes. The `sorry` warnings are the three parked ones (`HPC/Fold/Theorem4.lean` `theorem3_end`; `HPC/PseudoArc/Theorem14.lean` `covering_step` and `theorem14`) plus `theorem10_1951` in `HPC/Plane/EndPoints51.lean`.
* `covering_step`, `theorem14` (1948) and `theorem3_end` were not attempted (§4.3).

**Files** (all new, in `HPC/Plane/`):
* `EndPoints51.lean`: the skeleton, with the final statements and proofs. The root copy `EndPoints51.lean` is left as it was uploaded.
* `EndPointsAux.lean`: weak chains and how to trim them to chains (`weak_split`, `exists_chain_of_weak`); `linkN`, which indexes a chain's links by `ℕ`; `exists_chain_last_only`; limits of finely chained sets inside a compact set (`limSup_subset_of_mem_of_compact`, `isPreconnected_limSup_of_compact`); `chainedAt_initial`; and Bing's `δ` (`exists_delta_link_between`).
* `EndPointsT15.lean`: the construction behind Theorem 15. This is a discrete intermediate value theorem (`int_ivt`), `refine_between`, one level of the construction (`exists_next_level`), the structure `Level51`, and the sequence of levels (`exists_level_sequence`).

**Reshaped statements.**
* `condB_of_condA`, `condB_of_endPoint`, `exists_not_endPoint_of_not_HI`: the hypothesis `hM : Fold.Q78.IsContinuum M` was never used, so it has been **removed**. The statements are therefore more general. Conclusions are unchanged.
* `theorem14_1951`: statement unchanged. Of `IsSnakeLike M`, the proof uses only the continuum part: the chains come from the end-point hypotheses at `p` and at `q`.
* `theorem10_1951`, `endPoint_of_condA`, `theorem15_1951`: statements unchanged.

## 1. Counterexamples

None.

## 2. The targets, in order

1. **`theorem10_1951`** (Theorem 10) — **open**. See §3.6 below for what has been checked and what is missing.
2. **`condB_of_condA`** (Theorem 12, A ⇒ B) — **proved** (item 5 of §3 of the commission, as written). Given `h ∈ H ∖ K` and `k ∈ K ∖ H`, the set `H ∪ K` is a nondegenerate continuum through `p`. Condition A gives `q` with `H ∪ K` irreducible between `p` and `q`. Then `q ∈ H` forces `H = H ∪ K ∋ k`, and `q ∈ K` forces `K = H ∪ K ∋ h`.
3. **`endPoint_of_condA`** (Theorem 13, sufficiency for A) — **proved from `theorem10_1951`**, by the route in §3.3 of the commission. Take an `ε`-chain `D` covering `M` and refine it by Theorem 10. A refinement of an `ε`-chain is again an `ε`-chain, and `p ∉ closure e_j` gives `p ∉ e_j`.
4. **`condB_of_endPoint`** (Theorem 13, necessity) — **proved**. See §3.4 below.
5. **`theorem14_1951`** (Theorem 14) — **proved**. See §3.7 below.
6. **`theorem15_1951`** (Theorem 15, with the subcontinuum nondegenerate and `p ≠ q`) — **proved**. See §3.8 below.
7. **`exists_not_endPoint_of_not_HI`** (Theorem 16, the self-contained half) — **proved**. A subcontinuum `K` of `M` is decomposable as `A ∪ B`, with `A`, `B` proper subcontinua. Since `K` is connected and `A`, `B` are closed, they meet at some point `p`. If `p` were an end point, condition B (by `condB_of_endPoint`) would give `A ⊆ B` or `B ⊆ A`, so `K = B` or `K = A`, which is a contradiction.

## 3. §3 items, claim by claim

### Item 4 — Theorem 13, necessity (`condB_of_endPoint`, helper `endPoint_aux`)

* *"`ε` less than `dist(h, K)` and `dist(k, H)` is positive."* **Confirmed**, using `IsClosed.notMem_iff_infDist_pos`. Only closedness and nonemptiness are used, so no compactness is needed here.
* *"Let `d_i` be the last link meeting `H ∪ K`."* **Confirmed.** It is a maximum over a finite nonempty set, and the first link contains `p ∈ H`.
* *"`H` meets every `d_1, …, d_i`."* **Confirmed**, by `Chain.inter_link_nonempty_between` applied to the preconnected `H`, which contains `p ∈ d_1` and a point of `d_i`. The cases `j = 0` and `j = i` are handled separately.
* *"`k` lies in some `d_j` with `j ≤ i`, which meets `H`, so `dist(k, H) < ε`."* **Confirmed.** This is the reading of Bing's "no point of `H` is farther than `ε` from `H`" that the commission suggests. The argument needs only that `p` is in the first link. The hypothesis "in no other link" (the second half of condition C) is **not used**.
* *"The same argument gives the half of Theorem 16."* **Confirmed** (target 7).

### Item 6 — Theorem 10 (open)

What was established, informally and in part in Lean:

* *Minimal counterexample by Zorn.* **Confirmed informally.** Let `E` be a chain that works for `⋂ M_i`, a nested intersection of continua through `p`. Then `E.union` is an open set containing the compact `⋂ M_i`, so it contains `M_i` for large `i`, and `E` works for that `M_i`. Hence the family of *counterexample* subcontinua through `p` is closed under nested intersections, and a minimal counterexample `M'` exists. Condition A passes to subcontinua through `p`.
* *Links of `D` missing `M'`.* The links of `D` that meet `M'` form a run of consecutive indices, and that run is a chain covering `M'`. This is **proved** in Lean as `exists_chain_of_weak` / `exists_chain_last_only`, for the general "weak chain" case. So one may assume every link of `D` meets `M`, as Bing does.
* *Existence of `M''`* (a proper subcontinuum through `p` meeting every link of `D`). **Not checked in detail, and not written in Lean.** The natural candidate is the component of `p` in `M` minus a small open set near the far point of irreducibility. The case where some link of `D` meets `M` only near that point is not settled here.
* *The choice of `N`.* `N` is open, meets `M''`, and has `N̄ ⊆ d_1 ∩ f_j ∖ {p}`. **Confirmed**, *given* a point of `M'' ∩ f_j ∩ d_1` other than `p`.
* *"The component of `M ∖ N` containing `p` lies in `M''`."* **Confirmed, using condition B** (which follows from A, target 2). Let `C` be that component. `C` and `M''` are both subcontinua of `M` through `p`, so `C ⊆ M''` or `M'' ⊆ C`. The second is impossible, because `M''` meets `N` and `C` does not.
* *The separation `M ∖ N = H ∪ K`, with `H ⊇ C` covered by `F`.* **Confirmed informally.** In the compact metric space `M ∖ N`, the component `C` is the intersection of the clopen sets containing it. By compactness, one of those clopen sets lies inside the open set `F.union`.
* *The displayed `E` is a chain covering `M` and refining `D`.* It covers `M` and refines `D`: **confirmed**. It is a chain only in the **weak** sense: links two apart are disjoint, but adjacent links may fail to meet. It must be trimmed to a chain with `exists_chain_of_weak`. The trimmed chain still has `p` in its first link only, and `p` is not in the closure of any other link, because `N̄ ∌ p` and the other links avoid a neighbourhood of `p`.
* **Missing claim.** *"The last link of `F` intersects `M'' · (d_1 + d_m)`, or else a chain with fewer links than `F` with the required properties covers `M''`."* **Not established.** Deleting `f_j` does not give a chain covering `M''` when `f_j` contains points of `M''` in no other link. Bing gives no construction of the shorter chain, and none was found. Replacing "fewer links" by other minimality measures, or by strengthened invariants in the Zorn argument, fails. Those invariants involve open conditions that are not preserved under nested intersections, and the case "`f_j` lies in a middle link of `D`" is not excluded. Without this claim the surgery has no `N`, so Theorem 10 remains `sorry`. Whether the claim is true, or whether Theorem 10 needs a different proof, is **not determined**.

### Item 7 — Theorem 14 (`theorem14_1951`; `δ` in `exists_delta_link_between`)

* *Bing's `δ`.* **Reconstructed and proved** (`exists_delta_link_between`). The setting is:
  * `M` is irreducible between `p` and `q`;
  * `O` is an open set;
  * `x ∈ M ∩ O` with `x ≠ p, q`.

  Then there is `δ > 0` with the following property. Every `δ`-chain `F` covering `M` with `p` in its first link has a link `f_j ⊆ O`, with `j > 0`, that comes before every link containing `q`. The proof is by contradiction. The bad `1/k`-chains give, for each `k`, the union of the links from `p` up to the first link containing `q`, restricted to the links not inside `O`. These are finely chained sets from near `p` to near `q`. Their `limSup` is a closed preconnected subset of `M` containing `p` and `q` (`isPreconnected_limSup_of_compact`, the batch-81 limit argument without the compact-ambient-space hypothesis). It misses `x`, because a link containing a point near `x` lies in `O` once it is small enough. This contradicts irreducibility.
* *The fine chain `F` at `p`.* It comes from condition C at `p`, with mesh `< min(δ, ε)`.
* *The chain `D` with `q ∈ d_n − d_{n−1}` and `d_1` meeting `M`.* It comes from condition C at `q`: reverse the chain, then trim it to the links meeting `M` (`exists_chain_last_only`). The trimmed chain has at least 2 links, because its mesh is less than `dist(p, q)/2`.
* *The point of `M` in `d_1` for Bing's `δ`.* **Confirmed**: there is a point of `M ∩ d_1` other than `p` (and not `q`, which is in the last link only). If `d_1 ∩ M = {p}`, then `M` would be separated by the open sets `d_1` and `{p}ᶜ`.
* *The new chain* `f_1, …, f_{j−1}, N·d_1, …, N·d_n`. It is **proved**, with one repair: the link at the joint is `f_j ∪ (N' ∩ d_1)`, where `N'` is the union of the links from `f_j` on. This keeps the joint adjacent. The result is an `ε`-chain from `p` to `q` covering `M`.
* *The case `p = q`.* **Confirmed degenerate.** Irreducibility gives `M = {p}`, and one ball of radius `ε/3` is the required chain.

### Item 8 — Theorem 15 (`theorem15_1951`; construction in `EndPointsT15.lean`)

* *The sequence `C_i`.* **Proved** (`exists_level_sequence`, one step at a time with `exists_next_level`). The `C_i` are chains of mesh `< 1/(i+1)` covering `M`, every link meets `M`, and link closures nest. The fine chain is taken below the Lebesgue number of the coarse one, and trimmed to the links meeting `M`.
* *The subchains `D_i`.* The marked indices `s_i + 2 ≤ t_i` have end-link closures inside the previous end links, and the links between them have closures in links between `s_{i−1}` and `t_{i−1}`. This is **confirmed, with a repair**. Taking arbitrary links with closure in the coarse end links is not enough. Choose a **minimal pair**: a fine link with closure in the coarse link `s`, and one with closure in the coarse link `t`, as close together as possible. The fine links between them then map into coarse links strictly between `s` and `t`. This uses the discrete intermediate value theorem `int_ivt`, applied to the index of a coarse link containing each fine closure, which changes by at most 1 per step. `C_1` needs at least 3 links, and `M` being nondegenerate provides this.
* *The limit `N = ⋂ K_i`.* Here `K_i` is `M` intersected with the union of the closures of the links of `D_i`. It is **proved** to be a nondegenerate subcontinuum of `M`. It is compact and preconnected as a limit of finely chained sets. `p` is in the nested end-link closures at `s_i`, and `q` in those at `t_i`. `p ≠ q` because the end links of each `D_i` are disjoint (`s_i + 2 ≤ t_i`).
* *Opposite end points.* **Proved, with a repair**: `D_i` is not itself a chain *from* `p` *to* `q`, because `p` may also lie in the second link. The chain used at level `i` consists of the links of `D_i`, with the closures of the end links of `D_{i+1}` removed from all links except the end ones. This gives `IsFrom p q`. It is again an `ε`-chain covering `N` (the removed closures lie in the end links).
* *`N` is snake-like.* **Proved**, directly from the chains above.

## 4. Not attempted

`covering_step`, `theorem14` (1948), `theorem3_end` (as instructed). §3 Theorems 6–7, Theorem 5, Theorems 8, 9, 11, Theorem 12 B ⇒ A, and the external steps of Theorem 16 (commission §5).
