Commission read: `doc/batches/COMMISSION-batch169.md` ("Commission: batch 169 — Part E, Hagopian 1976 XIV: Theorem 1 — above and below a crossing continuum; generic `p`, `q`; the dichotomy for `R(E)`; T13; Property 3").

# Report, batch 169

## 0. Summary

* **§1.1, meagreness: proved** (`isMeagre_Rset`), by a shorter route than the commission's.
  Every extension of `E`, away from either end set, is a proper subcontinuum of `M` through a fixed
  point `e ∈ E`. So `R(E)` lies in the composant of `e`, which is meagre (Moore 136–137).
* **A (above and below): disjointness proved, covering open** (`crossing_sides`, `belowSet`,
  `aboveSet`). On the question about `K`: **`K` is not needed for `p`, `q`**. It remains in use as
  the reference for positions, and as the place where T17 picks `yᵢ₋₁`. Hagopian already compares
  positions of points off `K` (the `f(yᵢ)`). The covering half is used at "Hence `f(yᵢ₋₁)` is either
  above `d⁻¹[I]` or below `d⁻¹[J]`". It fails for arbitrary crossing continua (bubbles; informal
  example, §1.A).
* **B (generic `p`, `q`): proved** (`exists_generic_pq`), with all five requested properties.
  "Below/above" is relative to the vertical over `t₀` (A). The route is changed: `p`, `q` are not
  on `K₀`.
* **C (the dichotomy): proved from `Cl R(E) = M`** (`Rset_homeo_dichotomy_of_closure`, route C.1).
  In general it is **open**. It is stated as the `Prop` **`RsetDichotomy k`** (C.3), under which T12
  holds in the weakest form of report 168 §1.A, conditions 2–3 (`hagopian76_T12_of_dichotomy`).
  `Cl R(E) = M` (`closure_Rset_eq_univ`) is open.
* **D (T13): the compactness half proved, the extension half open.** `iInter_chain_extension`: the
  intersection of a nonempty chain of separating extensions contains `E`, is a continuum, and still
  separates. That it is again an extension is the `Prop` **`ExtChainInter`**. Under it, Zorn's lemma
  gives the irreducible `F` (`hagopian76_T13`).
* **E (Property 3): open, not attempted.**
* **F (`follows_essential_crossing`): open.** Genericity does not help. `Cᵢ₋₁` is fixed by `Cl Cᵢ`,
  so its points cannot be chosen.
* **G (T15–T17, Theorem 1): not reached.** A skeleton proposal is in §5.
* **Nothing is refuted formally.** No defective proof is added; the count stays at fourteen.

`lake build HPC` succeeds with `import HPC.Hagopian.Hagopian76N` at the end of `HPC.lean`. All 33
new theorems use only `propext`, `Classical.choice` and `Quot.sound`. The regenerated `axioms.txt`
has 1769 lines (1736 + 33), and `sorryAx` appears in none of them. No declaration uses `sorry`.
The word occurs only in the comment block at the end of `Hagopian76N.lean`, which holds the open
shapes.

Files (all under `HPC/Hagopian/`):
* `Hagopian76N.lean`: the skeleton, with the delivered statements and the open items commented out.
* `H76Meagre.lean`: `extension_proper`, `Rset_subset_composant`, `isMeagre_Rset_aux`,
  `exists_notMem_Rset`.
* `H76Sides.lean`: `belowSet`, `aboveSet`, `isOpen_joined`, `belowSet_isOpen`, `aboveSet_isOpen`,
  `mem_belowSet`, `mem_aboveSet`, `belowSet_of_preconnected`, `aboveSet_of_preconnected`,
  `crossing_sides_aux`.
* `H76T12Sides.lean`: `T12_sides_aux`. This is the batch-168 construction, unchanged, with the
  position data of `Z = Cl B` in the conclusion. The batch-168 file is not edited.
* `H76Generic.lean`: `SepIn.mono`, `subset_Rset_self`, `val_mem_toPt_iff`, `exists_generic_pq_aux`.
* `H76Dichot.lean`: `RsetDichotomy`, `image_composant`, `disjoint_image_Rset`,
  `Rset_dichotomy_of_closure_aux`.
* `H76ChainSep.lean`: `SepIn`, `sepIn_iInter_of_directed`, `directed_supset_of_isChain`,
  `toPt_sInter`, `sepIn_sInter_chain`, `iInter_chain_isContinuum`, `ExtChainInter`,
  `T13_of_chainInter`.

**Hypotheses as `Prop`s** (deliverable 1, C.3):
* `RsetDichotomy k`: `∀ g : M ≃ₜ M, (g '' Rset k ∩ Rset k).Nonempty → g '' Rset k = Rset k`;
* `ExtChainInter E X₀ O p q`: every nonempty chain of extensions of `E` away from `X₀`, each
  separating `p` from `q` in `O`, has an intersection that is an extension away from `X₀`.

## 1. The items

STATUS lines, in order: `STATUS: §1.1 proved`; `STATUS: A proved (disjointness); covering open`;
`STATUS: B proved`; `STATUS: C open (proved from Cl R(E) = M; C.3 Prop RsetDichotomy)`;
`STATUS: C.1 open`; `STATUS: D open (compactness half proved; T13 proved under ExtChainInter)`;
`STATUS: E open (not attempted)`; `STATUS: F open`; `STATUS: G open (not reached)`.

### 1.1 `R(E)` is meagre

`isMeagre_Rset`. The commission's route (countable chains and nowhere density) works, but this one is
shorter:
* `extension_proper`: an extension `F` of `E` away from `k⁻¹(0)` or `k⁻¹(1)` is a continuum, and
  `F ≠ M`, because Lemma 4 (for `k`, or for `σ ∘ k` via `layer_symm_comp`) gives a strictly larger
  extension.
* `Rset_subset_composant`: so every point of `R(E)` lies in a proper subcontinuum through `e`, for
  any fixed `e ∈ E`.
* `composant_isMeagre` (batch 155, Moore 136–137) finishes. `M` is nontrivial because `k` is onto
  `[0, 1]`.
* `exists_notMem_Rset`: every nonempty open subset of `M` has a point off `R(E)` (Baire).

### 1.A Above and below a crossing continuum

**Definitions** (`H76Sides.lean`). For `Z ⊆ R²`, `D = F[D′]`, `t₀` and heights `u`, `w₂`:
* `belowSet π F D′ t₀ u Z`: the points `P` of `π⁻¹[D] − Z` such that some connected
  `S ⊆ π⁻¹[D] − Z` contains `P` and a point over `F(t₀, v)` with `0 < v ≤ u`;
* `aboveSet π F D′ t₀ u w₂ Z`: the same with `u ≤ v < w₂`.

**Proved.**
* Both sets are open in `R²` if `Z` is closed: a ball around `P` inside `π⁻¹[D] − Z` can be added
  to `S`. Connected sets inside `π⁻¹[D] − Z` propagate membership (`belowSet_of_preconnected`).
* **`crossing_sides`**: for a crossing continuum `Z = Cl B` with the hypotheses of
  `crossing_separates`, missing the vertical at heights `(0, u₁]` and `[u₂, w₂)`, `belowSet … u₁ Z`
  and `aboveSet … u₂ w₂ Z` are disjoint. Proof: a common point gives a connected set from a point
  over `F(t₀, v₁)` to one over `F(t₀, v₂)`, `v₁ ≤ u₁ < u₂ ≤ v₂`, missing `Z`. This is excluded by
  `crossing_separates` at the heights `v₁`, `v₂`.

**The reference to the vertical.** The commission's "joined to points just over the bottom edge"
(and "just under `I₂`") is rendered through the vertical over `t₀`. Near the bottom, the strip below
the lowest height of `Z` is connected, misses `Z`, and meets the vertical, so the two notions agree
there. Near `I₂` the vertical part `[u₂, w₂)` plays the same role.

**Not proved: the covering half.**
* As stated for arbitrary crossing continua, it is **false**. Let `Z` be a crossing arc with a small
  circle attached away from the vertical. The open disc inside the circle is a component of
  `π⁻¹[D] − Z` that reaches neither edge. *This is an informal example; it is not formalized.*
* For `Z ⊆ M` the covering requires `Z` not to separate the plane. That holds if `Z` is a
  non-separating plane continuum; whether the separators of T17 (`d⁻¹[I]`, subcontinua of
  `F ⊆ M`) are non-separating is not settled here.

**Reading of pp. 347–349 for `K` and `yᵢ ∈ K`.** Every use of `K` and of positions:
1. "A point `p` of `K` …", "points of `K ∩ (W − R(E))`": `p`, `q` on `K`. **Not needed** (B).
2. "R(E) intersects an arc in K that is irreducible between C and the q-component …": the
   separation. Done by `crossing_separates`, which uses the vertical only through the hypotheses
   `hlo`/`hhi` on `Z`.
3. Property 4: "There exists a point `yₙ` of `K` such that …". The induction step uses `yᵢ` only
   through positions ("`yᵢ` is between `d⁻¹[I]` and `d⁻¹[J]`") and distances ("Since both `yᵢ` and
   `yᵢ₋₁` are within `ε₃` of `d⁻¹[V]`"). So `yₙ ∈ π⁻¹[D]` with positions in the sense of
   `belowSet`/`aboveSet` suffices. The base case `yₙ = p` then needs no `K`.
4. "Let `yᵢ₋₁` be a point of `K ∩ Cᵢ₋₁`": `K` is a convenient place to pick a point of the crossing
   component `Cᵢ₋₁`. It is nonempty because `K₀` is a cross-cut (`hagopian76_K0_crosscut`).
5. "By considering the position of `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]]`, we see that `yᵢ₋₁` is between `d⁻¹[I]` and
   `d⁻¹[J]`"; "The point `yᵢ₋₁` is below `C`": positions of points of `K`, so the three-part cut
   along `K₀` (`crossing_pair_separates`) applies.
6. "`f(yᵢ)` is above `d⁻¹[I]`", "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`. It is
   not above `d⁻¹[I]` because …": **positions of points not on `K`**. These need "above/below" for
   arbitrary points, and the "either … or" needs the **covering** half.

**Conclusion.** `K` is not essential for `p`, `q`, nor for the `yᵢ`. It is essential as the
reference of the position relations, and these relations are already applied by Hagopian to points
off `K` (item 6). What T17 needs beyond what is proved is the covering half for the separators
`d⁻¹[I]`, `d⁻¹[J]` (and `P`).

### 1.B Generic `p`, `q` — proved

**`exists_generic_pq`.** In the set-up of `hagopian76_T12`, there is `x ∈ k⁻¹(t₀)` such that for
every `ε > 0` there are `ε`-homeomorphisms `h`, `h₁`, heights `0 < u₁ < u₂ < w₂`, an extension `H` of
`E` away from `k⁻¹(0)` and a connected `B ⊆ π⁻¹[D]` with:
1. `p = h(x) ∉ R(E)`, `q = h₁(x) ∉ R(E)`;
2. `Z = Cl B` compact, `Z ⊆ H − E`, meeting both open side edges, missing the vertical at heights
   `(0, u₁]` and `[u₂, w₂)`;
3. `p ∈ belowSet … u₁ Z`, `q ∈ aboveSet … u₂ w₂ Z`;
4. `SepIn (π⁻¹[D]) H p q` and `SepIn (π⁻¹[D]) R(E) p q`. `SepIn` includes `p`, `q ∈ π⁻¹[D] − H`;
5. the closures of the components of `M ∩ π⁻¹[D]` through `p` and through `q` meet both open side
   edges.

**Route** (`exists_generic_pq_aux`), changed from the commission's:
1. `T12_sides_aux` (the batch-168 construction) gives `p₀ = h₀(x)` and `q₀ = h₁′(x)` on `K₀` at
   heights `u₁ < u₂`, with `Z` between them. Both lie in `π⁻¹[D] − Z` (`seg_subset_rect_domain`
   and the vertical-avoidance of `Z`). So `p₀ ∈ belowSet`, `q₀ ∈ aboveSet`.
2. `belowSet ∩ ball(p₀, ρ/2)` is open in `R²` and meets `M` at `p₀`. Its trace on `M` is a nonempty
   open subset of `M`, so it contains a point `p ∉ R(E)` (`exists_notMem_Rset`). The same holds for
   `q` near `q₀` in `aboveSet`.
3. `p`, `q` lie within `ρ` of `x`, so `p = h(x)` and `q = h₁(x)` with `h`, `h₁` small (Lemma 2).
   The Lemma-2 radius is fixed before T12 is applied, which is why `T12_sides_aux` is applied with
   `ρ/2`.
4. Separation: a connected `S ⊆ π⁻¹[D] − H` through `p` and `q` misses `Z ⊆ H`. So `q` would be
   below `Z` (`belowSet_of_preconnected`) and above `Z`, contradicting `crossing_sides`. For `R(E)`:
   `SepIn.mono`, since `H ⊆ R(E)` and `p`, `q ∉ R(E)`.
5. Crossing: Lemma T (`crossing_translate`) applies to `h` and `h₁`. They are `δ`-small (the `ε` is
   replaced by `min ε δ` at the start), `p`, `q ∉ E ⊆ R(E)`, and `π(p)`, `π(q)` lie over `D`.

The commission's nonemptiness check ("the part above `Z` near `x` is nonempty") is not needed. The
open sets are nonempty because they contain `p₀` and `q₀`, which come from Lemma T′.

### 1.C The dichotomy

* **Route C.1: proved conditionally** (`Rset_homeo_dichotomy_of_closure`). If `Cl R(E) = M`, then
  `R(E) = composant_M(y)` for every `y ∈ R(E)` (`hagopian76_Rset_composant`,
  `composant_eq_composant_univ`). A homeomorphism carries composants to composants
  (`image_composant`). If `g(y) ∈ R(E)` for some `y ∈ R(E)`, then
  `g[R(E)] = composant(g y) = R(E)`. Disjointness of distinct composants is not even needed.
* **C.1 itself (`closure_Rset_eq_univ`): open.** I have no argument either way. The suggested
  route (crossing pieces of `R(X, E)` near every point, transported by Effros) shows that `Cl R(E)`
  and its translates `g[Cl R(E)]` accumulate everywhere. But a family of translates of a nowhere
  dense continuum can be dense, so no contradiction follows.
* **Route C.2: open.** Absorption (`subset_extUnion_of_meets`) gives the following. Let
  `z ∈ g[R(E)] ∩ F′` with `F′` an extension away from `k⁻¹(0)`, and let `G ⊆ g[R(E)]` be a continuum
  through `z`. If `G` misses `k⁻¹(0)`, then `G ⊆ R(k⁻¹(0), E)`. If it misses `k⁻¹(1)` and meets `E`,
  then `G ⊆ R(k⁻¹(1), E)`. Every point `w` of `g[R(E)]` lies in such a `G` (an extension on each
  side, joined at `g[E]`). The case left is a `G` meeting both `k⁻¹(0)` and `k⁻¹(1)`, i.e. with
  `E ⊆ G ⊆ g[R(E)]` (end-set property). Taking `G` irreducible from `w` to `E` does not exclude it:
  `G` could be indecomposable with `w` and `E` in different composants. This is the obstruction.
  The commission's "end set of `E″` missing `g[F]`" is the same point, seen from the other side.
* **Route C.3: done.** `RsetDichotomy k` is the hypothesis. `disjoint_image_Rset`: under it,
  `x ∈ R(E)`, `g(x) ∉ R(E)` give `g[R(E)] ∩ R(E) = ∅`. **`hagopian76_T12_of_dichotomy`** gives
  report 168's weakest T12, conditions 2–3:
  * `p = h(x)` and `f = h₁h⁻¹`, a `2ε`-homeomorphism with `f(p) = h₁(x)`;
  * an extension `H` away from `k⁻¹(0)` separating `p` from `f(p)`;
  * `h[R(E)] ∩ R(E) = ∅ = h₁[R(E)] ∩ R(E)`;
  * the `p`-component crosses.

  Condition 1 (`Cl C_p` essential to `h[R(E)]`) needs `hagopian76_T12_parts12` with Hagopian's `h`.
  Report 168 §1.A reduces this to the dichotomy as well. It is not assembled here.

### 1.D T13

* **Separation of the intersection: proved** (`sepIn_iInter_of_directed`, `sepIn_sInter_chain`).
  * A connected `S ⊆ O − ⋂ Cᵢ` through `p`, `q` lies in a component of the open set `O − ⋂ Cᵢ`.
    That component is path-connected, so it contains an arc from `p` to `q`.
  * The arc is compact and misses `⋂ Cᵢ`. For a directed family of compact sets it then misses some
    `Cᵢ` (`IsCompact.elim_directed_family_closed`), a contradiction.
* **The intersection is a continuum containing `E`: proved** (`iInter_chain_isContinuum`, via
  `isPreconnected_iInter_directed`, batch 155).
* **The intersection is an extension: open** (`ExtChainInter`).
  * *Obstruction:* the intersection must be irreducible, and must carry an admissible decomposition
    with void-interior layers and end set `k⁻¹(0)`.
  * By `ext_layers`, each extension `F ≠ E` is `d⁻¹[[0, s]]` of any larger one, so a decreasing
    chain looks like a decreasing chain of initial segments of a ray. The candidate decomposition
    of the intersection uses the restricted layers. Its last layer is the limit of the last layers
    of the members, and showing that it is a single layer of the ray (rather than a union of
    several) needs an argument that is not given.
  * The intersection is not `E` itself when all members separate (E misses `π⁻¹[D]`).
* **T13 under `ExtChainInter`: proved** (`hagopian76_T13`). Zorn's lemma (`zorn_superset_nonempty`)
  on the separating extensions inside a given one `H`, with intersections as lower bounds. `H` is
  supplied by `exists_generic_pq` (`O = π⁻¹[D]`, `X₀ = k⁻¹(0)`, `q = f(p)`).

### 1.E Property 3 — open (not attempted)

Unchanged from batch 168 (§1.D there).

### 1.F T17's missing statement — open

`Cᵢ₋₁` is "the first component of `M ∩ π⁻¹[D]` (whose closure intersects both side edges) that is
met by extending `Cl Cᵢ` away from `X`". It is determined by `Cl Cᵢ`. A could let T17 choose the
point `yᵢ₋₁ ∈ Cᵢ₋₁` freely, but not the component. Lemma T covers a component only through a point
`h′(x′)`, with `h′` small and `x′` in the middle range of `E`. Such a point gives crossing and the
essential translate (`crossing_essential`). Whether `Cᵢ₋₁` contains one is the missing statement of
report 168 §1.E. **Lemma T does not cover it.** Genericity of `yᵢ₋₁` makes no difference, because
the question is about the component, not the point.

### 1.G T15–T17, Theorem 1 — not reached

See §5.

## 2. Ledger entries (`LEDGER.md` §6, batch 169)

1. **p. 347, T12:** "Let p and q be points of K ∩ (W − R(E)) …". **`K` is not needed for `p`, `q`;
   proved** (`exists_generic_pq`). `K` is the reference for positions, and Hagopian applies those
   positions to points off `K`.
2. **pp. 347–349, the tacit dichotomy:** proved from `Cl R(E) = M`; open in general; carried as
   `RsetDichotomy`.
3. **p. 347, T13:** "Let F be a continuum that is irreducible with respect to the following
   properties …". The starting extension is proved (`exists_generic_pq`). The chain step is proved
   up to `ExtChainInter` (gap, open).
4. **p. 347, Property 3:** open; not attempted.
5. **pp. 347–349, T15–T17:** "Hence f(yᵢ₋₁) is either above d⁻¹[I] or below d⁻¹[J]" needs the
   covering half of above/below, which fails for arbitrary crossing continua (informal example).
   "Let Cᵢ₋₁ be the first component …": Lemma T does not cover it (F).
6. **`Cl R(E) = M`?** Open; it would give the dichotomy.

## 3. Axioms

Group *Hagopian 1976 XIV (batch 169)* of `Axioms.lean`; the per-theorem output is in
`doc/batches/audits/axioms-batch169.txt`. Each of the 33 theorems depends on
`[propext, Classical.choice, Quot.sound]`:
* `isMeagre_Rset`, `crossing_sides`, `exists_generic_pq`, `hagopian76_T12_of_dichotomy`,
  `Rset_homeo_dichotomy_of_closure`, `iInter_chain_extension`, `hagopian76_T13`;
* `extension_proper`, `Rset_subset_composant`, `isMeagre_Rset_aux`, `exists_notMem_Rset`;
* `isOpen_joined`, `belowSet_isOpen`, `aboveSet_isOpen`, `mem_belowSet`, `mem_aboveSet`,
  `belowSet_of_preconnected`, `aboveSet_of_preconnected`, `crossing_sides_aux`;
* `T12_sides_aux`;
* `SepIn.mono`, `subset_Rset_self`, `val_mem_toPt_iff`, `exists_generic_pq_aux`;
* `image_composant`, `disjoint_image_Rset`, `Rset_dichotomy_of_closure_aux`;
* `sepIn_iInter_of_directed`, `directed_supset_of_isChain`, `toPt_sInter`, `sepIn_sInter_chain`,
  `iInter_chain_isContinuum`, `T13_of_chainInter`.

`T12_sides_aux` is compiled with `maxHeartbeats 1000000` (as `T12_part3_aux`), and
`exists_generic_pq_aux` with `800000`; this does not affect the axioms.

## 4. Dependency map of Theorem 1, updated

```
T6/T7 ─ hagopian76_D ─ hagopian76_K0 ─ K0_crosscut
            │               │
            │      crossing_translate (Lemma T) ── crossing_translate_in_aux
            │               │                                │
            │      K0_dense_low (Lemma T′)       crossing_piece_of_R (Lemma R)
            │               │                                │
            │               │        crossing_separates ─ crossing_pair_separates
            │               │                │               │
            │               │        crossing_sides [A: disjoint; covering open]
            │               │                │
T8/T9_full ─ crossing_essential ─ T12_parts12 │   isMeagre_Rset ─ exists_notMem_Rset
                                              │               │
                         T12_sides_aux ─ exists_generic_pq [B] (p, q ∉ R(E); H separates; crossing)
                                              │
   Cl R(E) = M [open] ──► RsetDichotomy [C, open; C.3 hypothesis] ──► hagopian76_T12_of_dichotomy
                                              │
     iInter_chain_extension ─ ExtChainInter [open] ──► hagopian76_T13 [D, conditional]
                                              │
   Property 3 (crossing_set_closed; shift g)  │                          [open]
                                              │
   T15–T17 (I finite; Property 4; Bing; covering half of A; F)           [open]
                                              │
                               hagopian76_theorem1                       [open]
```

## 5. Skeleton proposal for what remains

```
-- C.2: the remaining case of the dichotomy
theorem continuum_in_translate_containing_E … (g : M ≃ₜ M) (G : Set M) (hG : IsContinuum G)
    (hGg : G ⊆ g '' Rset k) (hEG : E ⊆ G) : G ⊆ Rset k
theorem Rset_homeo_dichotomy … : RsetDichotomy k
-- D: the extension half
theorem extChainInter … : ExtChainInter E (layer k 0) O p q
-- A: the covering half, for non-separating separators
theorem crossing_sides_cover … (hZ : ¬ SeparatesPlane Z) :
    π ⁻¹' (F '' D') \ Z ⊆ belowSet π F D' t₀ u₁ Z ∪ aboveSet π F D' t₀ u₂ w₂ Z
theorem subcontinuum_nonseparating … (Z ⊆ M, Z a proper subcontinuum) : ¬ SeparatesPlane Z
-- E: Property 3 (report 167 §5)
theorem crossing_set_closed …; theorem hagopian76_property3 …
-- F: the first crossing component is low somewhere
theorem follows_essential_crossing … (C crossing component, Cl C essential to h[R(E)]) :
    ∃ h′ small, ∃ x′, h′ x′ ∈ C ∧ (k x′ in the middle range)
-- G
theorem hagopian76_property4_step … ; theorem hagopian76_T15_T17 … : False
theorem hagopian76_theorem1 : Hagopian76Thm1
```

## 6. Build provenance

The run started from a checkout with no local build outputs of `HPC`; the compiled Mathlib files
were present. The import closure of `Hagopian76M` was built first. After that, each new file was
checked with `lake env lean`, then `lake build HPC.Hagopian.Hagopian76N`, then `lake build HPC`.
`axioms.txt` was regenerated with `lake env lean Axioms.lean > axioms.txt`.
