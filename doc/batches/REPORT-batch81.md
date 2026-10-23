Commission read: `COMMISSION-batch81.md`, with its skeleton `Theorem13.lean` (saved as `HPC/PseudoArc/Theorem13.lean`; `import HPC.PseudoArc.Theorem13` added at the end of `HPC.lean`).

# Report — batch 81: Bing's Theorem 13, `M` is homogeneous

## 0. Counterexamples and statement changes (reported first)

**No counterexample.** I audited the definitions (`composant`, `IsSubchainFrom`,
`Theorem13Statement`, `IsIndecomposable`, `Description`) and found no statement that fails as written.
No statement was reshaped. The only edits to the skeleton are these:

* The two index-bound placeholders in `exists_subchain_meets_ends` are discharged from
  `Δ.isFrom j`: `⟨0, by have := Δ.isFrom j; exact this.1⟩` and
  `⟨Δ.n j - 1, by have := (Δ.isFrom j).1; omega⟩`.
* One import (`HPC.PseudoArc.T13Step`) and the proofs are added.

The skeleton's hypothesis `hnd : M.Nontrivial` of `composant_ne_of_indecomposable` turned out to
be **unnecessary**. If `M` is a single point, its composant is empty, since there is no proper
subcontinuum. I kept the hypothesis because the skeleton has it, and noted this in its docstring.
The `P ≠ Q` lesson of batch 80 does not bite here. Every place that needs a nondegeneracy
hypothesis already has `hPQ`.

## 1. Targets

All four are proved in `HPC/PseudoArc/Theorem13.lean` with the skeleton's statements. `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for each; the output is in `axioms-batch81.txt`, produced
by `lake env lean Axioms81.lean`.

1. `HPC.composant_ne_of_indecomposable`.
2. `HPC.Description.exists_subchain_meets_ends`.
3. `HPC.Description.exists_description_from`.
4. **`HPC.Description.theorem13`**: `Theorem13Statement Δ` for every description of a compact
   metric space with `P ≠ Q`.

With 4 in place, both results of Bing 1948 used by the classification are machine-checked:
`theorem12` (uniqueness) and `theorem13` (homogeneity). The only live `sorry` in the repository is
still `theorem3_end`, which none of this batch uses.

New supporting files, all without `sorry`:

* `HPC/PseudoArc/T13Topo.lean`. Pure point-set topology, importing only Mathlib:
  * `ChainedAt`, `limSup`, and `isPreconnected_limSup`;
  * clopen boundary bumping, `clopen_meets_closure_diff`;
  * `false_of_interior`: a proper subcontinuum of an indecomposable continuum has empty interior;
  * `exists_not_mem_proper_subcontinua`, via Baire.
* `HPC/PseudoArc/T13Chains.lean`. `Chain.span` and `chainedAt_span`; `Description.isConnected_M`,
  `isContinuum_M`, `exists_isSubchainFrom`, `false_of_disjoint_limit` and
  `exists_subchain_meets_ends'`.
* `HPC/PseudoArc/T13Step.lean`. `IsFrom.reverse`, `IsConsolidationOf.reverse`, `.union_eq`,
  `dist_le_of_mem_unionRange`, `exists_blockChain` (Theorem 4 on a subchain), `exists_step`, and
  `exists_description_from'`.

## 2. The eleven claims of §3

**Claim 1: the limiting set is a continuum containing `R` and `S`.** The second reason offered
in the commission is the right one. Connected links are **not** needed.

* `T13.ChainedAt A ε` says `A` cannot be split between two sets whose points are more than `ε`
  apart.
* `T13.isPreconnected_limSup` proves the following. Let `A k` (`k ∈ I`, `I` infinite) be
  `ε_k`-chained, with `ε_k → 0`, all containing a common point. Then their topological limit
  superior `⋂_N closure (⋃_{k ∈ I, k ≥ N} A k)` is connected. This needs a compact metric space.
* The proof separates the limit by two closed sets and thickens them by `δ/2`. By compactness,
  the tail closures eventually lie in the two thickenings. Once `ε_k < δ/2`, each chained `A k`
  lies in the thickening of the side that contains the common point. So the other side misses
  the limit.
* `Chain.chainedAt_span` shows that any run of consecutive links of diameter at most `ε` is
  `ε`-chained. The proof is an induction along the links.
* A by-product: **the repository did not prove that `M` itself is connected.** Theorem 10 is
  stated for subcontinua `K ⊆ M` and was never applied to `M`. This is now
  `Description.isConnected_M`. It is the same lemma applied to `A k = (D k)^*`, since
  `⋃_{k ≥ N} (D k)^* = (D N)^*`. Theorem 13 needs it to apply Theorem 10 to `K = M`.

**Claim 2: the continuum is `M`.** Immediate from the definition of `composant`. See the last
line of `false_of_disjoint_limit`, and `mem_composant_self`: `{R}` is a proper subcontinuum
when `P ≠ Q`.

**Claim 3: some `k > j` has `D_k(R,S)` meeting both end links.** The chain of containments the
commission worried about (links of `D_{j+1}`, closures) is **not needed**. Suppose infinitely many
`D_k(R,S)` miss the first link `d(j)_1`. That link is itself an open set, and it meets `M`
(`link_inter_M_nonempty`). It is disjoint from every one of those `D_k(R,S)^*`, so no point of
`d(j)_1` lies in their limit superior. So the limit is a proper subcontinuum of `M` containing `R`
and `S`, a contradiction.

The argument is `false_of_disjoint_limit`, and the case split is in
`exists_subchain_meets_ends'`. It needs `P` or `Q` in the first or last link only through
"`d(j)_1 ∩ M ≠ ∅`". The subchains exist once the mesh is below `dist R S`
(`exists_isSubchainFrom`: the links through `R` and those through `S` are then disjoint, and one
set lies entirely below the other). `R ≠ S` follows from `S ∉ composant R` and `P ≠ Q`.

**Claim 4: `composant(R) ≠ M`.** Proved as `T13.exists_not_mem_proper_subcontinua`; the target
follows in three lines. The route:

* **(a)** `false_of_interior`: no proper subcontinuum `K` of an indecomposable `M` contains
  `O ∩ M ≠ ∅` for an open `O`. Put `L = closure (M \ K)`; then `L ≠ M`, because `L` misses `O`.
  * Every nonempty closed, relatively open subset of `L` meets `closure (M \ L) ⊆ K`. This is
    boundary bumping in clopen form (`clopen_meets_closure_diff`, from connectedness of `M`
    alone). It needs no components and no Šura-Bura.
  * If `L` is connected, `M = K ∪ L` is a decomposition.
  * Otherwise split `L = L₁ ⊔ L₂` into closed pieces. Each `K ∪ Lᵢ` is a continuum
    (`isPreconnected_union_clopen`). Each is proper, because `M \ K` is dense in `L` and so meets
    the other piece. Then `M = (K ∪ L₁) ∪ (K ∪ L₂)` is a decomposition.
* **(b)** Take a countable basis of `X` and the basic sets `b` meeting `M`. Each proper
  subcontinuum through `p` lies in `connectedComponentIn (M \ b) p` for a basic `b` around a
  point outside it. Each of those components is a proper subcontinuum; it is closed because the
  closure of a connected set in the closed set `M \ b` stays in the component.
* **(c)** Apply Baire (`nonempty_interior_of_iUnion_of_closed`) in the compact subspace `M`. If
  the composant were `M`, one of the countably many components would have interior in `M`,
  contradicting (a).

Mathlib has no boundary bumping theorem that I found; the clopen form above is all that is used.

**Claim 5: Theorem 4 gives a chain from `R` to `S`.** Proved as `Chain.exists_blockChain`, using
`Fold.theorem4_pair` and `Q78.isFrom_ofBlocks_iff` as the commission suggested.

* Say the subchain `[a, b]` of `D_k` runs from `R` (at `a`) to `S` (at `b`). By the uniqueness
  clauses of `IsFrom`, the links of `D_k` through `R` are among `{a−1, a}` and those through `S`
  among `{b, b+1}`.
* So the basepoint pairs are `(a−1, a)` and `(b, b+1)`, truncated at the ends of the chain.
* `r' ≤ s'` needs `b − a ≥ 2`. This holds once the coarse chain has at least **5** links: two
  links of `D_k` that meet the two end links of a 5-link chain cannot be adjacent. So the
  construction picks levels `m` with `n m ≥ 5` (`n_tendsto_atTop`).
* If the subchain runs the other way (`S` at `a`), the same construction with `R` and `S` swapped
  gives a chain from `S` to `R`, and that chain is then reversed (`IsFrom.reverse`,
  `IsConsolidationOf.reverse`).
* Mesh: each block lies in three consecutive links of `D_m`, so any two of its points are within
  `3 ε_m` (`dist_le_of_mem_unionRange`, through the middle link).

**Claim 6: `D_j` is crooked in `E_1`.** This is Theorem 1, `Chain.isCrookedIn'_of_isConsolidationOf`
(`D.IsConsolidationOf E → F.IsCrookedIn' E → F.IsCrookedIn' D`). It takes the target `F = D_{K+1}`,
crooked in `E = D_K` by the description's `crooked` field, and coarsens `E` to its consolidation
`D = E_i`. The only transitivity used is `Δ.crooked_of_lt` (`D_k` crooked in `D_m`, `k > m`), which
is `isCrookedIn'_of_refines` composed with `refines_of_le`. That is what feeds Theorem 4.

**Claim 7: closures of pairs of links lie in a link of `D_j`.** A Lebesgue number
(`lebesgue_number_lemma_of_metric`) for the links of `D_L` covering the compact set
`closure (D_{L+1})^*`. I did not use `eventually_thick`. The statement actually used is for a whole
block (claim 8), not for pairs.

**Claim 8: `E_2` is contained in `D_j`.** Proved in `exists_step`.

* Choose the coarse level `m ≥ L+1` with `3 ε_m < min δ (1/(L+1))`, where `δ` is the Lebesgue
  number for level `L`.
* Every block `B` of the new chain is nonempty and lies in `(D_k)^* ⊆ (D_{L+1})^*`. Its points
  are within `3 ε_m` of any one of them, `x₀`. So `closure B ⊆ closedBall x₀ (3 ε_m) ⊆ ball x₀ δ`,
  which lies in a link of `D_L`.
* **Bound on `k`:** the requirement is on the *coarse* level `m` of Theorem 4, namely
  `3 ε_m < δ_L`. The fine level `k` is whatever the reaching-both-ends step returns after `m`.
* The step is applied with `L = K_i + 1`, where `K_i` is the level that `E_i` consolidates. So
  every link of `E_{i+1}` has its closure inside a link of `D_{K_i+1}`. That closure lies inside
  a link of `D_{K_i}`, which lies in a link of `E_i`. This is condition (2).

**Claim 9: "By Theorem 2, `E_2` is crooked in `E_1`."** The commission's second reading is
**confirmed**, with the order it gives: claim 8 first, then Theorem 2.

* `E_{i+1}` refines `D_{K_i+1}` (claim 8).
* `D_{K_i+1}` is crooked in `D_{K_i}` (description), hence crooked in its consolidation `E_i`
  (Theorem 1).
* So `E_{i+1}`, which refines `D_{K_i+1}`, is crooked in `E_i`. This is Theorem 2 in the form
  `isCrookedIn'_of_refines`: a chain that refines a chain crooked in `D` is crooked in `D`.
* That is exactly Bing's "By Theorem 2", with `E_2` in the role of the refining chain.
* It is not "coarsening the fine chain". Coarsening `D_k` to `E_2` is never needed: `E_2` is used
  only through the fact that it refines `D_j`.

**Claim 10: the sequence is a `Description X R S` with the same `M`.** Proved as
`exists_description_from'`.

* The levels are `lev 0 = 0` and `lev (i+1) = K (lev i) + 1`.
* The chains are `E_i = F (lev i)`, with `F` and `K` from `exists_step` via `choose`.
* The fields:
  * `isFrom`: from the step;
  * `crooked`: claim 9;
  * `closure_subset`: claim 8;
  * `ε i = 1/(i+1)`, using `diam ≤ 1/(lev i + 1)` and `lev i ≥ i`;
  * `bdd`: each link's closure lies in a bounded link.
* `M' = M`: `E_i^* = (D_{K(lev i)})^*` (`IsConsolidationOf.union_eq`), and
  `K(lev i) ≥ i`, so `⋂_i (D_{K(lev i)})^* = ⋂_i (D_i)^*`.

**Claim 11: assembling Theorem 13.** Exactly as in the commission.

* `M` is indecomposable: `theorem10` applied to `K = M`, with `isContinuum_M` (claim 1's
  by-product).
* For each `n`, pick `Q_n ∈ M \ composant(P_n)` by claim 4, and let `Δ_n` be the description from
  `P_n` to `Q_n` given by claim 10. `P_n ≠ Q_n` holds because `P_n ∈ composant(P_n)`
  (`ne_of_not_mem_composant`).
* `theorem12 Δ₁ Δ₂` gives `T` with `T P₁ = P₂`. It is transported along `Δ₁.M = Δ.M = Δ₂.M` by
  `Homeomorph.setCongr`.

## 3. What Bing's text lacked, in summary

* Connectedness of `M`, and the connectedness of the limiting set when links are not connected.
  Both are supplied by the chained-limit lemma.
* The properness of composants: Baire plus clopen boundary bumping.
* Claim 3's properness of the limit: simpler than the commission feared, since the end link
  itself is the neighbourhood to use.
* Theorem 4's basepoints must be *pairs* of links (batch 79). The subchain must be at least
  three links long, which needs coarse chains of at least 5 links.
* Claim 9's "Theorem 2" is Theorem 2 applied to `E_2` as a refinement of `D_j`, after claim 8.

## 4. Build

* `lake build HPC` succeeds (8217 jobs). The only `sorry` warning is the parked `theorem3_end`
  (`HPC/Fold/Theorem4.lean`). The one new warning is the unused `hnd` noted in §0.
* `rg sorry` over the new files finds only the phrase in the skeleton's module docstring.
