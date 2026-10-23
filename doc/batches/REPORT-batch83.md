Commission read: `COMMISSION-batch83.md`, with its skeleton `Theorem14.lean` (saved as `HPC/PseudoArc/Theorem14.lean`; `import HPC.PseudoArc.Theorem14` added at the end of `HPC.lean`).

# Report — batch 83: irreducible subcontinua; Theorems 14 and 15

**Summary.**
* Items 1–3 are proved with statements unchanged: `exists_irreducible`, `Description.irreducible_unique`, `Description.theorem15_of_theorem14`.
* Item 4, `exists_description_covering`, is **reduced, not proved**. It now follows (proved: `exists_description_covering_of_step`) from a claim about a single level, `covering_step`, and that claim remains `sorry`. §3.3 below states the obstruction.
* Item 5, `theorem14`, is **not proved** (`sorry`). Item 6, `theorem15`, is the skeleton's term `theorem15_of_theorem14 … (theorem14 …)`, so it depends on that `sorry`.
* No counterexample to any skeleton statement was found.
* `#print axioms` shows `[propext, Classical.choice, Quot.sound]` for every proved result. `covering_step`, `exists_description_covering`, `theorem14` and `theorem15` also show `sorryAx`. The output is in `axioms-batch83.txt`, produced by `lake env lean Axioms83.lean`.
* `lake build HPC` completes. It warns of `sorry` in three places:
  * `HPC/Fold/Theorem4.lean:23` (`theorem3_end`, parked, unchanged);
  * `HPC/PseudoArc/Theorem14.lean`, in `covering_step`;
  * `HPC/PseudoArc/Theorem14.lean`, in `theorem14`.
* `theorem3_end` was not attempted, because items 4 and 5 are not done (§4 of the commission).

**Files.**
* `HPC/PseudoArc/Theorem14.lean`: the skeleton, filled in where proved, plus the lemmas listed below.
* `HPC/PseudoArc/T14Irred.lean`: new supporting file. It contains:
  * the nested-intersection lemma;
  * the tools for carrying subsets of `M` along a homeomorphism (`homImage`);
  * `IsSubchainFrom.ends` and `IsSubchainFrom.inter_link_nonempty`;
  * Bing's limiting set (`exists_least_connected`);
  * the generalised description assembly (`exists_description_of_steps`);
  * the composant lemma;
  * the two closeness lemmas for subchain spans.
* `Axioms83.lean`, `axioms-batch83.txt`.

## 1. Counterexamples

None. I checked the skeleton's hypotheses against the claims:
* `P_i ≠ R_i` (§3.5) is needed.
* `W_i ≠ M` (§3.2) is needed.
* The `hPQ` hypothesis of `irreducible_unique` is **not** used. It is kept because the skeleton has it, the docstring says so, and it leaves one unused-variable warning.

## 2. Targets, in order

### 2.1 `IsIrreducibleBetween` and `exists_irreducible` — proved

The proof is Zorn (`zorn_superset_nonempty`) on the subcontinua of `K` that contain `A` and `B`. The lower bound of a nonempty chain `c` is `⋂₀ c`:
* It is compact because it is closed in a compact space.
* It contains `A` and `B`.
* It is preconnected by the new `T14.isPreconnected_sInter_chain`. Suppose `⋂₀ c ⊆ u ∪ v` with `u`, `v` closed and disjoint. Thicken them to disjoint open sets. Because the chain is directed and its members are compact, some member of `c` lies inside the union of the two thickenings (`exists_subset_nhds_of_isCompact'`). That member is connected, so it lies in one thickening, and then so does the intersection.

A minimal element is irreducible.

### 2.2 `Description.irreducible_unique` — proved (the proof of §3.1)

Bing's witness is `exists_least_connected`: for distinct `A`, `B` in `M` there is an `L` that is:
* closed and preconnected;
* contains `A` and `B`;
* lies inside `M`;
* lies inside every closed preconnected `K ⊆ M` containing `A` and `B`.

`L` is `T13.limSup {k | k₀ ≤ k}` of the spans of chosen subchains `D_k(A, B)`, with `ε_k < dist A B` for `k ≥ k₀`. The three points of §3.1 go through as written:
* **`L` is a connected subset of `M` through `A` and `B`.** Connectedness is `T13.isPreconnected_limSup` with `Chain.chainedAt_span`. `L ⊆ M` follows from refinement of the levels.
* **Minimality.** `K ⊆ (D_k)^*` meets every link of `D_k(A, B)` (new `IsSubchainFrom.inter_link_nonempty`, from `inter_link_nonempty_between`). So each point of the span is within `ε_k` of `K`. Hence `L ⊆ closure K = K`. The commission's "`ε` decreasing" is not needed: for a given `δ`, take `N` with `ε_k < δ/2` for all `k ≥ N`.
* **Uniqueness.** Every irreducible `W ⊆ M` between `A` and `B` contains `L`, and `L` is a subcontinuum through `A` and `B`, so `W = L`.

### 2.3 `Description.theorem15_of_theorem14` — proved (Bing's proof, with the gap of §3.2 closed)

**The partner point** (`exists_irreducible_partner`, confirming §3.2 bullet 3). `W_i` is indecomposable by `theorem10`, so `composant W_i P_i ≠ W_i` (`composant_ne_of_indecomposable`); this is where nondegeneracy enters. Choose `R_i ∈ W_i` outside that composant. Then:
* `P_i ≠ R_i`, because `{P_i}` is a proper subcontinuum of the nondegenerate `W_i`.
* `W_i` is irreducible between `P_i` and `R_i`.
* `R_i` is in the composant of `P_i` in `M`, witnessed by the proper subcontinuum `W_i`. This is where `W_i ≠ M` is used (§3.2 bullet 1).

**Transport** (`IsIrreducibleBetween.homImage`, confirming §3.2 bullet 4). Let `homImage T S` be the image of `S ∩ M` under `T : M ≃ₜ M`, read in `X`. It carries continua inside `M` to continua (`isContinuum_homImage`, via `IsInducing.subtypeVal`), and `homImage T.symm` undoes it. So irreducibility between `A` and `B` passes to irreducibility between `T A` and `T B`.

**Conclusion.** The set in the goal is by definition `homImage T W₁`. It is irreducible between `P₂ = T P₁` and `R₂ = T R₁`, so it equals `W₂` by `irreducible_unique`.

On §3.2 bullet 2 (the reading of "a composant not containing `W_i`"): the proof uses only `Q_i ∉ composant M P_i`, as the skeleton states it.

### 2.4 `Description.exists_description_covering` — reduced to one level; the one-level claim is open

**Proved.**
* `exists_description_of_steps` (in `T14Irred.lean`). This is the assembly of Theorem 13 (`exists_description_from'`) with an arbitrary property `G` of the step chains carried to every level of the new description. It says nothing new about crookedness: the new levels are crooked by Theorems 1 and 2 (`isCrookedIn'_of_isConsolidationOf`, `isCrookedIn'_of_refines`), as in batch 81. **No step chain has to be crooked in anything.**
* `CoversUpTo F P' R W`: there is some `b` such that `F.sub 0 b` is a chain from `P'` to `R` and `W ⊆ F.span 0 b`.
* `CoveringStep Δ P' Q' R W`: for every `L` there are `k > L` and a consolidation `F` of `D_k` such that:
  * `F` is a chain from `P'` to `Q'`;
  * each link of `F` has its closure inside a link of `D_L`;
  * each link of `F` has diameter at most `1/(L+1)`;
  * `CoversUpTo F P' R W`.
* `exists_description_covering_of_step`: `CoveringStep` implies the skeleton's conclusion exactly.
* `exists_description_covering` is proved from `covering_step`, which is the `sorry`.
* **Caveat.** `CoveringStep` may be stronger than item 4. Item 4 asks for *some* description; `CoveringStep` asks for consolidations of levels of the *given* `Δ`. It is the form the batch-81 construction produces.

**Also proved** (facts about `W` in §3.3):
* `IsIrreducibleBetween.subset_of_isPreconnected`: `W` lies in every closed connected subset of `M` through `P'` and `R`.
* `IsIrreducibleBetween.ne_M_and_not_mem`: under item 4's hypotheses, `W ≠ M` and `Q' ∉ W`.
* `not_mem_composant_of_mem_composant`: if `R` is in the composant of `P'` and `Q'` is not, then `Q'` is not in the composant of `R` either. The union of two proper subcontinua through `R` is proper, since `M` is indecomposable. So descriptions from `R` to `Q'` exist (`exists_description_from`).
* `subset_thickening_span`: for every `η > 0`, from some level on, `W` lies in the open `η`-neighbourhood of the span of **every** subchain `D_k(P', R)`. Together with `span_subset_cthickening` (every such span lies within `ε_k` of `W`), the spans converge to `W` in the Hausdorff sense. This makes §3.3 bullet 4 precise.

**§3.3, claim by claim.**
1. *Theorem 13's construction gives a description from `P'` to `Q'`.* **Confirmed** (`exists_description_from`).
2. *`W` is not in general covered by the `(P', R)`-subchain of a chain; the block map must send `W`'s links to blocks at or before `R`'s.* **Confirmed.** An informal necessary condition, not formalized: let `F` be a block consolidation whose links have diameter at most `η`, and suppose `F` covers `W` up to `R` at block `b`. A 1-Lipschitz block path from the fine link of `P'` (block `0`) to a fine link of `R` visits every block index up to `b`, and blocks are small. So `W` must lie within about `2η` of the span of that fine subchain. At the level of spans, `subset_thickening_span` (proved) says this closeness does hold for deep levels. Containment does not follow from it.
3. *Theorem 9 controls the opposite side.* **Confirmed.** As stated, `theorem9` only bounds the blocks of `u ≥ r` from below (`β t ≤ β u`). It says nothing that places `W`'s links in blocks `≤ β t`. The covering therefore does not follow from `theorem9`'s conclusion. A monotone block map sends every fine link after `R`'s into a block at or after `R`'s, so no monotone block map can fold back the part of `W` beyond `R`. The fold has to come from blocks that go back down (block maps are 1-Lipschitz, not monotone), and `theorem9` does not produce those on `W`'s side.
4. *`W = limsup S_k`, close to `S_k` but not contained.* **Confirmed and strengthened**, as above.

**The obstruction, stated.** What remains is `covering_step`: a single-level, crookedness-free statement.

> For each `L`, some deep level `D_k` has a consolidation with small links, running from `P'` to `Q'`, in which every link meeting `W` comes, in chain order, no later than the first link containing `R`.

Consider any such consolidation `F` with links of size `η`. The part of `M` near `W` lies in `F(0..b)`. The rest of `M` can meet it only through links `b` and `b+1`, which lie near `R`. So `R` must act as a "cut point at scale `η`" between `W` and `Q'`.

This is consistent with hereditary indecomposability: any subcontinuum through a point of `W` that leaves `W` contains `W`, and hence `R`. But I did not find a construction of such an `F` from the tools in the repository:
* **Theorem 4.** The fold of `theorem4_pair` needs the subchain between its two basepoints to reach both end links of the coarse chain. The subchain from `P'` to `R` does not reach the end containing `Q'`.
* **Concatenating a chain of `W` with a chain from `R` to `Q'`.** Adjacency fails wherever the second chain passes near `W` away from `R`.
* **Block maps read off an intermediate level's pattern.** These reproduce the intermediate level itself, which has the same folding problem.

### 2.5 `Description.theorem14` — not proved

§3.4, claim by claim:
1. *The invariant.* **Confirmed as necessary.** Carrying only `R`'s link index fails at a half-step. When side `B` is refined by a level `D_c` with `R_B ∈ D_c.link ρ'`, the pattern value `x ρ'` can be `ρ ± 1` if `R_B` lies in two adjacent links of the old chain. Side `A` then has to put `R_A` in `C_A.link (ρ ± 1)`, and nothing guarantees that. Relaxing the invariant to "adjacent positions" does not help: the error grows by one at each half-step. So the pattern has to be chosen with `x ρ' = ρ`. That choice is possible when `D_c` is fine, because a small link containing `R_B` lies inside the open `C_B.link ρ`. It then needs Bing's position control, which is where the `W`-covering invariant enters.
2. *The base rung.* **Open.** It needs `covering_step` at the level used (§2.4).
3. *The point `A`.* **Open.** The requirement that `X_{1,j}(P_1, A)` lie inside `Y_{1,1}(P_1, R_1)` is again a covering statement of the §3.3 kind.
4. *Three applications of Theorem 5.* **Not attempted in Lean.** The value constraint `h ≤ x t ≤ k` of `Theorem5Statement` needs the invariant "`Y_{2,2}(P_2, R_2)` refines `Y_{2,1}(P_2, R_2)`", as the commission says. That is another carried covering invariant, and it waits on 2 and 3.
5. *`Y_{1,2}` as a chain.* **Not attempted in Lean.** The batch-82 lesson applies. Cross-intersections of the unions `E_1(n) ∪ E_2(n) ∪ E_3(n)` can arise only at the two junctions. No lemma about this was written.
6. *Theorem 11 at the end.* **Confirmed as a plan.** `MatchingCovers.exists_homeomorph` with its tracking clause gives `T R₁ = R₂` once one index sequence tracks `R₁` and `R₂`. The rest of Theorem 14 is the construction of the covers.

### 2.6 `Description.theorem15` — conditional

It is the skeleton's term `theorem15_of_theorem14 Δ hPQ (theorem14 Δ hPQ) …`. It is proved except for `theorem14`.

## 3. `theorem3_end`

Not attempted: items 4 and 5 are not done.
