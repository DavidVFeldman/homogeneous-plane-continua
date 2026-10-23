Commission read: `doc/batches/COMMISSION-batch194.md` ("Commission: batch 194 — H–O Theorem 1, II: PL graphs; simple folds; Lemma 6, Theorem 8, Prop. 7").

# Report, batch 194

## 0. Summary, omissions, shape changes

**Every item of commission §2–§8 is proved.** Nothing is refuted (apart from the two certificates
of §8, which refute printed statements of H–O as the commission asked) and nothing is commented
out. `HOThm20` remains the only open input of `homeomorph_pseudoArc_of_indec_homogeneous`.

The skeleton `doc/batches/skeletons/HO16B.lean` is split over nine files under `HPC/HO16/`:

* `HPC/HO16/FoldDefs.lean` (§2: `relFrontier`, `IsFoldTriple`, `IsSimpleFoldOf`),
* `HPC/HO16/Subdiv.lean` (§3.1: common subdivision of finitely many segments; imports Mathlib only),
* `HPC/HO16/PLLib.lean` (§3: the nine library lemmas of the skeleton and further lemmas),
* `HPC/HO16/Lemma6.lean` (§5: `ho16_lemma6`; set algebra of folds; inverse of `φ|Fᵢ`),
* `HPC/HO16/FoldExists.lean` (§4: `exists_simpleFold`),
* `HPC/HO16/Thm8Fold.lean` (§6: `ho16_theorem8`),
* `HPC/HO16/Prop7.lean` (§7: `ho16_prop7`, Lemma (L), Claim 7.1),
* `HPC/HO16/FoldExample.lean` (non-vacuity: a concrete fold triple, §2 below),
* `HPC/HO16/HO16B.lean` (§8: `SurjSemiSpanZero`, the two certificates; header lists the split).

`HPC.lean` ends with `import HPC.HO16.HO16B`; `lake build HPC` succeeds (8753 jobs). No new file
contains `sorry`, `admit` or `axiom`; the nine new files build without warnings.

`axioms.txt` has **2824 lines** (2712 + 112 added, none removed). `sorryAx` occurs in none of
them. The 112 new theorems (group "H–O Theorem 1, II (batch 194)" of `Axioms.lean`; copy in
`doc/batches/audits/axioms-batch194.txt`) all use exactly `propext`, `Classical.choice`,
`Quot.sound` (§4).

**Shape changes** (each also recorded at the statement):
1. `IsPLGraph.finite_components` and `IsPLGraph.inter_connectedComponentIn`: the skeleton writes
   `connectedComponentIn`; inside the namespace `IsPLGraph` this name resolves to the theorem
   `IsPLGraph.connectedComponentIn` (stated just before), and the statements do not elaborate.
   Written `_root_.connectedComponentIn` (Mathlib's function). Nothing else changes.
2. `exists_simpleFold`, `ho16_lemma6`, `ho16_prop7`: the binders
   `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]` come from a `variable` line of the
   section instead of the signature; the elaborated statements are the skeleton's.

All other definitions and statements (3 definitions of §2, `SurjSemiSpanZero`, 15 theorems) are
textually the skeleton's (checked by a script comparing each declaration with the skeleton).

**Omissions.**
* §9.3 asks to "update the count of false printed statements in `LEDGER.md`". The ledger keeps no
  running number of false printed statements (only of defective proofs, which stays at sixteen;
  Jones 1949 Theorem 1 and Moore 1920 Theorem 4 are recorded in prose with their Lean names). The
  reclassification of HO.8 is therefore recorded in prose in the H–O section; no number is changed.
* The regression tests of §7 step 4 and the two remarks of p. 186 (§9.7) are checked by hand, not
  formalized (the commission asks for words for the first remark).
* The uniqueness clause of pp. 185–186 is not formalized (commission §9.5: "not formalized, not
  used").

Status lines:
* STATUS: §2 `relFrontier`, `IsFoldTriple`, `IsSimpleFoldOf` defined (skeleton text)
* STATUS: §3.0 `IsPLGraph.exists_refinement` proved
* STATUS: §3.1 `isPLGraph_biUnion` proved
* STATUS: §3.2 `IsPLGraph.union` proved
* STATUS: §3.3 `IsPLGraph.closure_diff` proved
* STATUS: §3.4 `IsPLGraph.relFrontier_finite` proved
* STATUS: §3.5 `IsPLGraph.connectedComponentIn` proved
* STATUS: §3.5 `IsPLGraph.finite_components` proved (shape change 1)
* STATUS: §3.6 `IsPLGraph.inter_connectedComponentIn` proved (shape change 1)
* STATUS: §3.7 `IsPLGraph.image_fst` proved
* STATUS: §4 `exists_simpleFold` proved
* STATUS: §5 `ho16_lemma6` proved
* STATUS: §6 `ho16_theorem8` proved
* STATUS: §7 `ho16_prop7` proved
* STATUS: §8 `ho16_theorem1_printed_false` proved
* STATUS: §8 `ho16_theorem1prime_printed_false` proved

## 1. The items, in order

### §2. Definitions (`FoldDefs.lean`)

`relFrontier`, `IsFoldTriple`, `IsSimpleFoldOf` exactly as in the skeleton. The fold is
`F₁ ∪ F₂ ∪ F₃ ⊆ E × ℝ` with projection `Prod.fst`.

### §3. The PL-graph library (`Subdiv.lean`, `PLLib.lean`)

* **§3.1, the core** (`Subdiv.exists_common_subdivision`): for a finite set `T` of nondegenerate
  segments and a finite set `P` of points there is a finite set `S` of nondegenerate pieces with:
  each piece inside some segment of `T`; two different pieces meet at most in common endpoints;
  every point of a segment `t ∈ T` lies in a piece contained in `t`; and every point of `P` on a
  segment is an endpoint of a piece. Route as in the commission's sketch: the cut points `V` are
  the endpoints of the segments, the points of `P` and the endpoints of the pairwise intersections
  (a pairwise intersection is a parameter interval `cutI`, whose ends are in `V`, `cutV`); a piece
  (`IsPiece`) is a segment between two cut points, inside a segment of `T`, whose open segment
  contains no cut point. "Each piece once" is enforced in `exists_common_subdivision` by keeping
  the orientation `(a, b)` with `a` before `b` in a well-ordering of `E`, so no `Sym2` is needed.
  The two
  crossing cases of the commission's argument are `piece_cross` and `piece_same` (via
  `real_cross`, `real_same` on the parameter line).
* `isPLGraph_biUnion` and `IsPLGraph.union` from §3.1.
* **§3.0, `IsPLGraph.exists_refinement`**: §3.1 applied to the edges of `G` and of all `Aᵢ`, with
  `P` the given finite set; then each `Aᵢ` is the union of its edges and every other edge meets
  `Aᵢ` only at endpoints. `IsPLGraph.exists_refinement_one` is the case of one subgraph.
* From a refined decomposition: `closure_diff_eq_of_refined` (`closure (G \ A)` is the union of the
  edges not in `A`; gives §3.3); `relFrontier_subset_vertices` (frontier ⊆ vertices; gives §3.4);
  `connectedComponentIn_eq_biUnion` (a component is the union of the edges it contains; gives §3.5,
  both lemmas, and with refinement for `A`, §3.6).
* §3.7 `IsPLGraph.image_fst`: the edges of `F` map to nondegenerate segments (injectivity), and the
  disjointness condition transfers because `Prod.fst` is injective on `F` and affine on each edge.
* Further lemmas for later batches: `PairwiseEndpoints` (the disjointness clause as a named `Prop`),
  `isPLGraph_biUnion_filter` (any subfamily of the edges of a decomposition is a PL graph),
  `IsPLGraph.mem_closure_diff_finite` (a point of a PL graph is a limit of points outside any finite
  set), `IsPLGraph.comp_mem_nhdsWithin` and `IsPLGraph.exists_open_comp` (components are relatively
  open; `Prop7.lean`), `isPreconnected_lift` (copies of connected sets under an injective `φ|F`).

### §4. Simple folds exist (`FoldExists.lean`)

`exists_simpleFold`, by the commission's construction: a refinement in which `G₁, G₂, G₃` are
unions of edges and the points of `∂G₁ ∪ ∂G₃` are vertices; then every edge is cut at its midpoint
(`exists_midpoint_subdivision`; a midpoint is never an old vertex, so no edge has both ends in
`∂G₁`, nor both in `∂G₃`); heights `h₁ = 1` on `∂G₁` and `0` elsewhere, `h₂ = 1`, `h₃ = 1` on `∂G₃`
and `2` elsewhere; `Fᵢ = liftG Sᵢ hᵢ`, the union of the lifted edges. `liftG_props` gives the PL,
injectivity and image clauses; the strict height comparisons on inner points of edges
(`lineMap_lt_lineMap`) give (F5).

### §5. Lemma 6 (`Lemma6.lean`)

`ho16_lemma6`, items (1), (2), (4), (5), (6), (7), by the commission's sketch: set algebra
(`fold_diff_left`, `relFrontier_left_eq`: `∂G₁ = G₂ ∩ cl(G₃ \ G₂)`, `relFrontier_mid_eq`,
`relFrontier_disjoint`, `relFrontier_diff_left`); finiteness from §3.4; for (5) a point of
`F₁ ∩ F₂` is a limit of points of `F₂ \ F₁` (`IsPLGraph.mem_closure_diff_finite`); (6) with the
open sets of the commission; (7) from `image_fst_mem_nhdsWithin` (a continuous injection of a
compact set maps relative neighbourhoods onto relative neighbourhoods) and the fact that `φ(p)` is
off `∂G₁` (resp. `∂G₂`, `∂G₃`).

### §6. Theorem 8, (1) ⇒ (2), for simple folds (`Thm8Fold.lean`)

`ho16_theorem8`, by the commission's proof: `ho16_theorem8_core` with `hfin₁`, `hfin₃` from §5 and
§3.4 and fans from `IsPLGraph.exists_fan`; `ψᵢ = invFunOn Prod.fst Fᵢ` is continuous on `Gᵢ`
(`continuousOn_invFunOn_fst`); `g = ψᵢ ∘ h` on `Xᵢ`. On `X₁ ∩ X₂`, `h x ∈ ∂G₁ = φ(F₁ ∩ F₂)`, so
`ψ₁(h x) = ψ₂(h x)` (both are the point of `F₁ ∩ F₂` over `h x`); likewise on `X₂ ∩ X₃`;
`X₁ ∩ X₃ = ∅`. Continuity by gluing on the three closed pieces; `φ ∘ g = h`, so
`dist (f x) (g x).1 < ε`.

### §7. Proposition 7 (`Prop7.lean`)

`ho16_prop7` as stated on p. 186.
1. **Existence of `K`** (`exists_comp_meets_both`, via `compsMiss`, `Z_disjoint`): if no component
   of `G₂` met both closures, the union of `cl(G₁ \ G₂)` with the components meeting it, and the
   union of the rest with `cl(G₃ \ G₂)`, would be disjoint nonempty closed sets covering `G`
   (finitely many components, §3.5).
2. **Claim 7.1** (`lift_subset_of_meets_both`).
3. **`φ(C)` is open** (`image_comp_mem_nhds_glue`, `image_comp_eq`): the commission's preferred
   route, without boundary bumping (the component `K` of `G₂` through `φ(p)` must meet `∂G₃`, by
   Lemma (L)(a); then Claim 7.1 for the `F₂`-copy of `K`). Points off `∂F₂` by Lemma 6 (7) and the
   openness of components.
4. **`F′` is a simple fold** (`frontier_clause`, `left_diff_subset_Z`, `mem_comp_of_mid`,
   `mem_comp_of_sides`): Lemma (L) is `disjoint_lift_of_disjoint_right` ((a)),
   `mem_comp_of_mid`/`mem_comp_of_sides` ((b)) and `comp_not_disjoint_both` ((c)). Every clause of
   `IsSimpleFoldOf` is checked; **no clause fails**. The PL clauses come from §3.6 (components of a
   PL graph meet PL subgraphs in PL graphs) and `IsPLGraph.image_fst`.
   The symmetric cases (`1 ↔ 3`) are reduced to each other by `IsSimpleFoldOf.symm`.

**Regression tests** (by hand, not formalized). (i) `G = [0, 4]`, `G₁ = [0, 3]`,
`G₃ = [½, 1] ∪ [2, 4]`: `∂G₁ = {3}`, `∂G₃ = {½, 1, 2}`; `F₂[½, 1] ∪ F₃[½, 1]` is a circle component
(its image `[½, 1]` misses `∂G₁`); the component through `F₁` contains `F₂[2, 3]` (glued at `3`)
and `F₃[2, 4]` (glued at `2`), and its pieces give `([0, 3], [2, 3], [2, 4])` with `∂G₁′ = {3}`,
`∂G₃′ = {2}`, as the theorem says. (ii) `G = [0, 3]`, `G₁ = [0, 1] ∪ [2, 3]`, `G₃ = [½, 3]`:
`∂G₁ = {1, 2}`, `∂G₃ = {½}`; the component through `F₁[0, 1]` is `F₁[0, 1] ∪ F₂[½, 1] ∪ F₃[½, 3]`,
the glue point over `2 ∈ ∂G₁` is in the other component `F₁[2, 3] ∪ F₂[2, 3]`, and the restriction
is `([0, 1], [½, 1], [½, 3])` with `∂G₁′ = {1}`. Both agree with `ho16_prop7`.

### §8. Theorem 1 and Theorem 1′ as printed (`HO16B.lean`)

`SurjSemiSpanZero` as in the skeleton. With `X = Unit`: `isHereditarilyIndecomposable_unit`,
`hoSpanZero_unit`, `surjSemiSpanZero_unit`, `not_homeomorph_pseudoArc_unit` (an `IsPseudoArc` set
has two distinct points). `ConnectedSpace Unit` and the metric instances are found by instance
search (no hand-supplied instance was needed). `ho16_theorem1_printed_false` and
`ho16_theorem1prime_printed_false` follow.

## 2. Non-vacuity notes

For each theorem whose hypotheses include a named `Prop` or structure:

* **`IsFoldTriple`** (`exists_simpleFold`, `IsFoldTriple.isPLGraph`, …) and **`IsSimpleFoldOf`**
  (`ho16_lemma6`, `ho16_theorem8`, `ho16_prop7`, `IsSimpleFoldOf.symm`, the helpers of
  `Prop7.lean`).
  1. *Satisfiable, and in the strong form needed by `ho16_prop7`.* `exists_simpleFold_example`
     (`FoldExample.lean`, proved): for `G = [0, 3]`, `G₁ = [0, 2]`, `G₂ = [1, 2]`, `G₃ = [1, 3]` in
     `ℝ` (`isFoldTriple_example`) there are `F₁, F₂, F₃` with `IsSimpleFoldOf`, `G` is connected,
     and `∂G₁ = {2}`, `∂G₃ = {1}` are nonempty (`relFrontier_example_left`, `_right`). So every
     hypothesis of `ho16_prop7`, `ho16_lemma6` and (with any hereditarily indecomposable `X`, e.g.
     a point, `isHereditarilyIndecomposable_unit`) `ho16_theorem8` is met by a concrete instance.
     More generally `exists_simpleFold` shows `IsSimpleFoldOf` is satisfiable over every
     `IsFoldTriple`.
  2. *Not equivalent to the conclusions.* `IsSimpleFoldOf` is the clause list of H–O's Definition 5;
     the conclusions (Lemma 6 (5)–(7), the lifting of maps in Theorem 8, the component statement of
     Proposition 7) are not among its clauses and need the PL library, compactness arguments, K–M
     Lemma 2 (`ho16_theorem8_core`) and Claim 7.1 / Lemma (L) respectively.
* **`IsPLGraph`** (library hypotheses): a definition from batch 193, satisfied by every
  nondegenerate segment (`isPLGraph_Icc` for intervals of `ℝ`); the library conclusions (closures,
  frontiers, components) are not clauses of it.
* **`PairwiseEndpoints`** (hypothesis of `isPLGraph_biUnion_filter`, `liftG_props`, …): the
  disjointness clause of `IsPLGraph`, satisfied by the decomposition of every PL graph (and by
  the singleton decomposition of `isPLGraph_Icc`).
* **`IsHereditarilyIndecomposable`** (`ho16_theorem8`): satisfied by a point
  (`isHereditarilyIndecomposable_unit`); the theorem with `X` a point is a non-trivial instance
  only of the gluing, but the hypothesis is the published one (H–O Theorem 8 (1)) and is not
  contradictory.
* The §8 certificates have no hypotheses.

## 3. Ledger entries

In `LEDGER.md`, section "Hoehn–Oversteegen 2016 and Krasinkiewicz–Minc 1977 (batch 193)". All
quotations were checked against page images at 200 dpi (H–O pp. 177, 178, 185, 186, 187, 212;
Lelek pp. 631–633), the bars of p. 188 at 400 dpi.
* **HO.4:** the "further observation" of batch 193 (`Kᵢ = f⁻¹(Gᵢ \ G₂)` without closure) is
  removed and the reason recorded: the page image of p. 188 at 400 dpi prints the closure bar in
  "Let Kᵢ = f⁻¹(cl(Gᵢ \ G₂))" and in "f⁻¹(yⱼ¹) ⊂ f⁻¹(cl(G₁ \ G₂)) = K₁ ⊂ X₁"; the text layer drops
  overlines. The fan-disjointness gap remains.
* **HO.2:** checked against `lelek1979.pdf`. Confirmed: a research announcement ("The purpose of
  the present paper(1) is to announce some results … A complete version will be published
  elsewhere"); Propositions 1–4 "rather straightforward", no proofs; Lemma 5 and Theorem 6 without
  proof; Corollaries 7–8 assume `dim X ≤ 1`, Corollary 9 does not ("If X is compact and σ(X) = 0,
  then each mapping f: X → T is inessential"); p. 633 gets Corollary 10 by citing [4] for dimension
  one of non-degenerate span-zero continua, Corollary 9, [3] for the passage to all
  one-dimensional polyhedra (without argument), and the Case–Chamberlin characterization [1]. The
  referee's reading is confirmed. Not used on this route; not counted.
* **HO.1 and HO.8, classification:** agreed with the commission. HO.8 (Theorem 1′, p. 212) is now a
  false printed statement at a degenerate case, certificate `ho16_theorem1prime_printed_false`,
  counted like Jones 1949 Theorem 1 and Moore 1920 Theorem 4; HO.1 (p. 211) stays a misprint
  (Theorem 1 is stated correctly on p. 180), certificate `ho16_theorem1_printed_false` as
  supporting evidence. The ledger says why the two are counted differently. The ledger has no
  numeric count of false printed statements to update (§0).
* **HO.9 (new), Lemma 6:** stated without proof ("left to the reader"); (1), (2), (4)–(7) verified
  for `IsSimpleFoldOf` (`ho16_lemma6`); (3) by definition.
* **HO.10 (new), pp. 185–186:** existence verified in the form of §4 (`exists_simpleFold`), not by
  the quotient; uniqueness "not formalized, not used".
* **HO.11 (new), Proposition 7:** existence of `K` — unargued, supplied; the application of
  Claim 7.1 (`φ(C′) ⊆ G₂`) — unargued, supplied (by the preferred route); "It is straightforward to
  check … F′ … is a simple fold" — unargued, supplied through Lemma (L); no clause fails; the
  regression tests agree.
* **HO.12 (new), p. 186 remarks:** both right. First: example `G = [0, 2]`, `G₁ = G`,
  `G₂ = G₃ = [1, 2]` (`∂G₁ = ∅`, `F₁` clopen). Second: `∂G₁ = ∅` makes `G₁` clopen, so `G₁ = G`;
  (F5) separates `F₁` from `F₂ ∪ F₃ ≠ ∅`; (F4) gives the homeomorphism.

No defective proof is added; the count of defective proofs stays at sixteen.

## 4. Axioms

`axioms.txt` regenerated by `lake env lean Axioms.lean`: **2824 lines** (2712 before, 112
added, none removed); `sorryAx` in no line. The 112 lines of the new group are in
`doc/batches/audits/axioms-batch194.txt`. **All 112 use exactly the three standard axioms
`propext`, `Classical.choice`, `Quot.sound`.**

Main theorems:
```
'HPC.HO16.IsPLGraph.exists_refinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.ho16_lemma6' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.exists_simpleFold' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.ho16_theorem8' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.ho16_prop7' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.exists_simpleFold_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.ho16_theorem1_printed_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'HPC.HO16.ho16_theorem1prime_printed_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. Dependency map of `homeomorph_pseudoArc_of_indec_homogeneous`

Unchanged from batch 193:

```
homeomorph_pseudoArc_of_indec_homogeneous        (HO16A)      proved, from HOThm20
├── pseudoArc_unique                              (HPC.Plane)  proved (earlier batches)
└── isPseudoArc_of_indec_homogeneous              (HO16A)      proved, from HOThm20
    ├── hagopian76_theorem1                       (HPC.Hagopian) proved (earlier batches)
    ├── theoremC                                  (HPC.Span)   proved (batch 192)
    └── ho16_theorem1_plane                       (HO16A)      proved, from HOThm20
        ├── HOThm20                               (Defs)       ** OPEN: named Prop hypothesis **
        ├── ho16_theorem4                         (Thm4)       proved
        ├── interior_eq_empty_of_hi               (Plane)      proved
        ├── exists_plGraph_approx                 (Grid)       proved
        ├── exists_path_approx                    (Plane)      proved
        ├── IsPLGraph.isCompact                   (Defs)       proved
        └── isSnakeLike_univ_of_epsMap            (HPC.Plane)  proved (earlier batches)
```

`HOThm20` is the only open input. **Now in place for its proof** (H–O §4–§5):
* simple folds as sets (`IsSimpleFoldOf`), their existence (`exists_simpleFold`, the construction
  of pp. 185–186) and their basic properties (`ho16_lemma6`);
* **Theorem 8, (1) ⇒ (2), for simple folds** (`ho16_theorem8`), with K–M Lemma 2 and the core from
  batch 193;
* Proposition 7 (`ho16_prop7`): reduction of a fold on a connected graph to a connected fold;
* the PL-graph library: refinement, unions, closures of differences, finite frontiers, components
  (finitely many, open, PL, traces of subgraphs PL), images under `Prod.fst`.

**Still missing:** Definitions 9, 12, 13, 16; Propositions 10, 11, 17, 19; Lemma 18; Theorem 15;
Theorem 20 itself.

## 6. Comments on the plan for the stairwell batches

* **Propositions 10–11** (components of `G \ B` for finite `B`): with `IsPLGraph.exists_refinement`
  taking `P = B`, `B` consists of vertices, the components of `G \ B` are unions of open edges and
  vertices, and their closures are unions of edges (`isPLGraph_biUnion_filter`), with frontiers
  inside `B` (as in `relFrontier_subset_vertices`). The argument of `connectedComponentIn_eq_biUnion`
  should carry over with "share a vertex not in `B`" as the relation. Expect a lemma
  "`G \ B` is locally connected and its components are relatively open", as `IsPLGraph.exists_open_comp`.
* **Definition 12** (straight sets, generic points): branch points and endpoints are best defined by
  the number of edges at a vertex **of a refined decomposition**, with a lemma that this number does
  not change under further refinement for an existing vertex, and is `2` at a new (inner) vertex.
  §3.1 already provides common refinements of two decompositions (apply it to the union of both edge
  sets), so "independent of the decomposition" reduces to that invariance. The commission's remark
  stands: straight sets are graphs of continuous functions over PL subgraphs, so only their
  projections are PL graphs; the lifting lemmas `liftG_props` handle PL heights only, and a version
  for continuous heights (homeomorphic copies, no PL structure on the set itself) will be needed.
* **"A subcontinuum of a PL graph is a PL graph"** (needed if regular subsets are to be PL in
  general, and possibly for Theorem 15): not proved. With refinement, a subcontinuum `K` of `G` is
  the union of edges it contains plus partial edges at finitely many ends; the obstruction is to show
  that `K` meets each edge in a closed interval (connectedness on an edge) and that only finitely many
  partial edges occur — both are finite combinatorics after §3.0.
* **Propositions 17, 19** (unfolding stairwells by simple folds): `exists_simpleFold` gives folds for
  arbitrary triples, and `ho16_prop7` reduces to connected folds; the induction over
  `E, E × ℝ, (E × ℝ) × ℝ, …` needs only that the fold `F₁ ∪ F₂ ∪ F₃` is a PL graph in `E × ℝ`
  (`IsSimpleFoldOf.isPLGraph_union`) and that `Prod.fst` composes, so the definitions should be
  stated for an arbitrary real normed space, as here.
* **Theorem 20**: the separator `M` and the map into `U ∩ (G × [0, 1])` should be handled by
  composing `ho16_theorem8` along the finite tower of folds produced by Proposition 19; the
  estimate is additive in the `ε`s, and each step only needs the projection `Prod.fst`.

## 7. Files

The tarball `doc/batches/batch194-files.tar.gz` contains every file added or changed in this run
(including this report, the audit, the notes and the uploads); the list is
`doc/batches/batch194-MANIFEST.txt`.
