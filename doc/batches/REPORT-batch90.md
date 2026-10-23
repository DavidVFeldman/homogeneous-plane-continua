Commission read: `COMMISSION-batch90.md` (batch 90: Bing, *Concerning hereditarily indecomposable continua*, Pacific J. Math. 1 (1951), §3, Theorem 2: most compact continua are pseudo-arcs).

# Report, batch 90

## Counterexamples

None. No statement of the skeleton was found false.

## Files

* `HPC/Plane/Most51.lean`: the skeleton, with proofs. It is imported at the end of `HPC.lean`. The
  skeleton's single import was replaced by `Mathlib`, `HPC.Plane.PseudoArc51`,
  `HPC.Plane.Monotone51` and `HPC.Plane.DescrM`.
* `HPC/Plane/DescrM.lean` (new): batch 84's planar description, started from `m ≥ 3` standard
  rectangles instead of 3.
* `HPC/Plane/Most51Geom.lean` (new, imported by `HPC.lean`): the partial results for item 7.
* `Axioms90.lean` and `axioms-batch90.txt`: the axiom check.

`lake build HPC` passes. The only `sorry` in the three new files is the body of
`exists_tame_chain_near`. All the results below use only `propext`, `Classical.choice` and
`Quot.sound`. The exceptions are `exists_tame_chain_near`, `dense_pseudoArcs` and `theorem2_HIC`,
which also show `sorryAx` (see `axioms-batch90.txt`).

## Changes to statement shapes

* `exists_pseudoArc_in_tameChain`: the skeleton's `[CompleteSpace E]` is dropped because the proof
  does not use it. Nothing else changed.
* Nothing else changed. Completeness is not used anywhere, but it is kept on
  `exists_tame_chain_near`, `dense_pseudoArcs` and `theorem2_HIC`, where the skeleton has it.
  `theorem2_HIC` keeps its conclusion.
* Added `GeomLemma E`, which states the conclusion of `exists_tame_chain_near` for all `g` and `ε`.
  Added `dense_pseudoArcs_of` and `theorem2_HIC_of`, which take `GeomLemma E` as an explicit
  hypothesis. They state openly what density depends on, and they have no `sorry` in their
  dependencies.

## Items 1–8

**1. `Cont`, `isClosed_cont`, `CompleteSpace (Cont S)`.** Proved.
* The proof uses Mathlib's description of the Hausdorff-metric topology on `NonemptyCompacts` as
  the Vietoris topology (`NonemptyCompacts.isOpen_subsets_of_isOpen` and
  `isOpen_inter_nonempty_of_isOpen`).
* Suppose `K` is not connected. Its two closed pieces are separated by disjoint open sets `U` and
  `V` (by normality). The sets `L` with `L ⊆ U ∪ V` that meet both `U` and `V` then form an open
  neighbourhood of `K` made of disconnected sets.
* Completeness follows from `IsClosed.completeSpace_coe`.

**2. `isClosed_notCoverable`.** Proved. The coverable continua form an open set, a union of the
open sets `{L | L ⊆ D.union}`. This is the Vietoris form of Bing's "if a `1/i`-chain covers `f₀`,
it covers some `f_j`."

**3. `isClosed_separated`.** Proved by sequences.
* Let `K^n → K`. The union `T = K ∪ ⋃ K^n` is compact, by `isCompact_biUnion_coe_of_isCompact` and
  `Tendsto.isCompact_insert_range`. The nonempty compacta inside `T` form a compact set
  (`isCompact_subsets_of_isCompact`).
* One subsequence makes the witnesses `(K₁ⁿ, K₂ⁿ, xₙ, yₙ)` converge in `𝒯 × 𝒯 × T × T`.
* The limit has every required property:
  - **Inclusion:** passes to the limit by the `infDist`/Hausdorff inequalities
    (`Most.subset_of_tendsto`).
  - **Connectedness of `K₁`, `K₂` and `K₁ ∪ K₂`:** follows from item 1. The union map `⊔` is
    Lipschitz on `NonemptyCompacts`.
  - **Separation points:** `infDist` is jointly continuous (`Most.tendsto_infDist`), so the
    inequalities `≥ 1/(i+1)` pass to the limit.

**4. `isClosed_degenerate`.** Proved. If `K` contains two points `a ≠ b`, the sets `L` that meet
both `ball a (d/2)` and `ball b (d/2)` form an open neighbourhood of `K` containing no singleton.

**5. `isGδ_pseudoArcs`.** Proved. The set of pseudo-arcs is the intersection of the complements of
`F_i`, `G_i` and the degenerate continua, which is a countable intersection of open sets. The
identifications behind this are:
* `Most.isSnakeLike_iff`: not in any `F_i` ⇔ chainable.
* `Most.isHI_iff`: not in any `G_i` ⇔ hereditarily indecomposable.
  - (⇐) A decomposition `A ∪ B` with neither piece the whole gives points of `A ∖ B` and `B ∖ A`
    at positive distance from the other piece.
  - (⇒) A `G_i` witness `K₁ ∪ K₂` is a subcontinuum, so it is indecomposable. Then one of `K₁`,
    `K₂` contains the other, which contradicts the distance `≥ 1/(i+1)`.
* `Most.nontrivial_iff`: not degenerate ⇔ nontrivial.

**6. `exists_pseudoArc_in_tameChain`.** Proved, by the **plane route**, not by generalising
`real_step`.
* `exists_pseudoArc_stdRect` (in `DescrM.lean`) runs batch 84's construction from `m` standard
  rectangles. Every step is unchanged (`desc_step`). It gives a pseudo-arc `M` inside
  `⋃_{j<m} stdRect j`.
  - `M` meets every rectangle because it is connected, lies in the union of the chain, and meets
    the first and last links (`Chain.inter_link_nonempty_between`).
* The plane is placed in `E` by `(a, b) ↦ a e₁ + b e₂`, which maps `stdRect j` into `stdBox e₁ e₂ j`.
  The image is then carried by the tame chain's homeomorphism `Φ`.
* The image is again a pseudo-arc by batch 89's `theorem4_HIC`. A continuous injection is monotone,
  and its fibres are proper because `M` is nondegenerate.

**7. `exists_tame_chain_near`.** **Open (`sorry`).** See the next section.

**8. `dense_pseudoArcs`, `theorem2_HIC`.** Proved from item 7.
* Let `D` be the tame chain item 7 gives for `ε/3`, and `h` the pseudo-arc that item 6 puts in `D`.
  Then `h` lies within `2ε/3` of `g` in the Hausdorff metric.
  - The links are bounded because `D.union` lies inside a thickening of the compact set `g`. So the
    skeleton's `diam < ε` (which is weak for unbounded sets) is enough.
* The `G_δ` half is unconditional (item 5).
* `dense_pseudoArcs_of` and `theorem2_HIC_of` are the same results with `GeomLemma E` as a
  hypothesis.

## Item 7 in detail

Below, *the geometric lemma* means the conclusion of `exists_tame_chain_near`.

**Proved, in `HPC/Plane/Most51Geom.lean`:**

* **Tame chains in `E`.**
  - `stdBoxChain`: the standard boxes form a chain (`isOpen_stdBox`, `stdBox_inter_nonempty_iff`).
  - `Chain.mapHomeo`: the image of a chain under a homeomorphism is a chain.
  - `tameChainE` and `isTameChain_tameChainE`: every homeomorphism of `E` together with an
    orthonormal pair gives a tame chain of every length.
* **Shears.** `shear`: the map `x ↦ x + f ⟪x, e₁⟫` is a homeomorphism of `E` when `f` is continuous
  and orthogonal to `e₁`.
* **The tube around an unbent arc, in every dimension `≥ 2`.**
  - `exists_tame_chain_near_graph` treats the arc `t ↦ p + t e₁ + f t` for `0 ≤ t ≤ L`, which is a
    graph over a line. The geometric lemma holds for it, with homeomorphism
    `x ↦ p + c x + f(c ⟪x, e₁⟫)` (a scaling, a shear and a translation).
  - **Corollaries:**
    - `exists_tame_chain_near_of_graph_approx`: the geometric lemma holds for every `g` that lies
      within `ε/2`, both ways, of such an arc.
    - `exists_tame_chain_near_segment`: the geometric lemma holds for every point and every
      straight segment of a real inner product space of dimension `≥ 2`. It uses
      `exists_unit_orthogonal` and `exists_orthonormal_pair`, which hold under `2 ≤ Module.rank`.
* **The arc, as a broken line that need not be simple, in every dimension and every normed space.**
  - `exists_eps_walk`: a compact connected set has an `ε`-walk through finitely many of its points
    whose `ε`-balls cover it. The proof joins any two points by an `ε`-walk (`induction₂'`) and
    concatenates walks through a finite `ε`-net.
  - `exists_broken_line_near`: the polygonal path through such a walk is within `ε` of `g`, and `g`
    is within `ε` of it. This is Bing's "broken line `ab` whose distance from `g` is less than
    `ε/2`", except that the line is not shown to be simple.

**Not done, which is the obstruction.** Two steps are missing.

1. **The simple arc.**
   - The broken line has to be made simple and kept away from itself: non-adjacent pieces must be
     at a positive distance, or a chain of balls along it cannot have disjoint non-adjacent links.
   - In dimension `≥ 3` this is general position (perturb the vertices).
   - In the plane it is the boundary of a thin neighbourhood of a spanning tree.
   - Neither was formalised.
2. **The tube homeomorphism.**
   - Even for a simple polygonal arc, the tube around it has to be the image of the straight box
     strip under a homeomorphism of `E`. That means bending the strip at every corner.
   - The shear construction only produces arcs that are graphs over a line. Such an arc cannot turn
     back, so it cannot approximate, for example, a circle.
   - Compositions of shears along different axes can make U-turns. I did not find a systematic
     construction for arbitrary polygonal arcs.
   - Weakening `IsTameChain` to "image of a neighbourhood of the strip under an open embedding"
     (which item 6 would also accept) would allow piecewise-affine or polar maps at the corners.
     The injectivity of such a map along a whole arc, and in dimension `≥ 3` the choice of normal
     frames, would still have to be proved.
   - I kept the skeleton's global-homeomorphism definition. The weakening was not needed for the
     cases that are proved.

By dimension: in the plane, in dimension `≥ 3`, and in Hilbert space alike, the walk, the broken
line, and the tube around unbent arcs are done. The simple arc and the bending are not done in any
dimension.

## Not attempted

As instructed: `covering_step`, `theorem14` (1948), `theorem3_end`, `theorem10_1951`.
