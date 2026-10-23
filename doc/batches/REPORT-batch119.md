Commission read: COMMISSION-batch119.md (batch 119 — Bing 1951 (Duke), Theorem 7, part I: the links, general position, cross-cuts).

# Report, batch 119

**Outcome.** Items 1–4 are proved; no `sorry` remains in any new file. Nothing in the skeleton was
refuted. Item 5 is **open**, with the obstruction stated below. Every statement of items 1–4 depends
on `[propext, Classical.choice, Quot.sound]` only (`doc/batches/audits/axioms-batch119.txt`);
`PlaneFacts` is a hypothesis, so the number of declarations with `sorryAx` is unchanged (two, the
open targets `theorem3_end` and `fugate_cor1`).

The skeleton is installed as `HPC/Plane/Tree7.lean`, and `import HPC.Plane.Tree7` is now the last
line of `HPC.lean`. The uploads were filed as usual: `doc/batches/COMMISSION-batch119.md` and
`doc/batches/skeletons/Tree7.lean`. Auxiliary material is in five new files:

| file | contents |
| --- | --- |
| `HPC/Plane/Tree7Star.lean` | strongly star-shaped sets (`StrongStar`): a finite union of open convex sets containing `c`; connected, regular open, complement and exterior connected and unbounded; the notched square |
| `HPC/Plane/Tree7Arcs.lean` | reversal, concatenation, segments as arcs, an arc minus its ends is connected, two arcs closing up, `TwoArcs`, `twoArcs_base`, `TwoArcs.move`, `split_two'` |
| `HPC/Plane/Tree7Cross.lean` | the cross-cut theorem `crosscut'` |
| `HPC/Plane/Tree7GP.lean` | lines `lineSet`, finite unions of lines have empty interior, non-parallel segments meet at most once, the three "bad translation" lemmas |
| `HPC/Plane/Tree7Notched.lean` | `notchedVertices`, `notchedPoly` (moved here), axis-parallel segments, `closure_notched`, the frontier, injectivity and the 400 edge-pair conditions |

No existing file was edited except `HPC.lean` (the import), `Axioms.lean` (a new group) and
`axioms.txt` (regenerated).

## Refutations

None. On the candidates named in the commission:

* **The vertex list of item 2** is correct as given: `frontier_notched` proves that the frontier of
  `notched o δ η r a b` is exactly `polygonOf notchedVertices`, and `isSimpleClosedPolygon_notchedPoly`
  that the 20-gon is simple. Neither the orientation nor the starting vertex was changed.
* **`InGeneralPosition`** is satisfiable as stated (`exists_gp_translation`) and gives what its
  docstring claims (`finite_inter_of_gp`). See item 3 for the judgement asked for.
* **The hypotheses of `crosscut`.** `hcU` is needed: `hcJ` alone allows an arc running outside `J`
  (its interior then lies in the exterior of `J`), and then `polyInterior J \ c = polyInterior J`
  while one of `polyInterior (αᵢ ∪ c)` contains `polyInterior J` together with the region between
  `c` and `J`. This is an informal argument; no Lean certificate was made. `hab` is implied by `hc`
  (`IsSimplePolyArc.ne`) and was kept.
* **The closure clauses of `crosscut`** are true and proved.

## Item 1 — the links of Theorem 6: proved

`exists_notched_cover_param` (the constants are those of the commission: `δ = ε/2`,
`r = min (r₀/2) (δ/4)`, `η = r/2`, `I` = the grid squares meeting `M`), `isBounded_notched`,
`isConnected_notched`, `isConnected_compl_notched`, `regular_notched`, `PlaneFacts.polyInterior_regular`,
`compFamily_isBounded`, `compFamily_regular`, `compFamily_compl_connected`, `treeChain_of_cover`
(the tail of the proof of `theorem6_1951`, copied; `Tree6.lean` was not edited), `theorem7_weak`.

The star-shapedness is used in a strong form: `N` is *strongly star-shaped* about `c` if
`c + t • (y - c) ∈ N` for all `y ∈ closure N` and `0 ≤ t < 1`. A finite union of open convex sets
containing `c` has this property (`Convex.combo_interior_closure_mem_interior`), and it gives at once
connectedness, regular openness (points just beyond a point outside `N` on the ray from `c` lie
outside `closure N`), and the connectedness and unboundedness of both `Nᶜ` and `(closure N)ᶜ` (push
points outwards along rays to the complement of a large sup-metric ball, whose complement is the
union of four half-planes).

Shape changes (each only drops a hypothesis): `hδ : 0 < δ` dropped from `isConnected_notched`,
`isConnected_compl_notched`, `regular_notched` (and from `frontier_notched`,
`notched_eq_polyInterior`, `isSimpleClosedPolygon_notchedPoly`, `exists_gp_translation`): it follows
from `0 < r` and `4 r ≤ δ`. `hu₀ : ¬ IsBounded d₀ᶜ` dropped from `compFamily_compl_connected`: the
common point of `d₀ᶜ` and `dᶜ` comes from `dᶜ` being unbounded and `d₀` bounded. `notchedFamily` is
marked `noncomputable` (it uses classical decidable equality on sets).

## Item 2 — the 20-gon: proved, unconditionally

`isSimpleClosedPolygon_notchedPoly`, `frontier_notched`, `notched_eq_polyInterior` (by
`polyInterior_eq_of_split` with `U = notched`, `V = (closure notched)ᶜ`, no `jct`).

The finite checks were done as the commission suggested: each edge of the 20-gon is axis-parallel,
and an axis-parallel segment is a box (`segment_vert`, `segment_horiz`). Membership in an edge then
becomes linear arithmetic. The frontier is computed by a case analysis on which of the three closed
rectangles of `closure notched` contains the point and which side it is on, and the edge
conditions by enumerating all 400 ordered pairs of edges. This is about seven minutes of
elaboration, so the two definitions `notchedVertices` and `notchedPoly` were **moved verbatim** to
`HPC/Plane/Tree7Notched.lean`, which does not import the other new files and is compiled once.
`Tree7.lean` keeps the vertex table as a comment.

## Item 3 — general position by translation: proved

`polyEdge`, `IsSimpleVertices`, `isSimpleClosedPolygon_iff`, `InGeneralPosition` (unchanged),
`finite_inter_of_gp`, `notched_translate`, `notchedVertices_translate`, `subset_translate_of_compact`,
`exists_gp_translation`, `PlaneFacts.exists_gp_cover`.

`exists_gp_translation` is proved by putting every bad translation on a line instead of the
commission's three kinds of closed nowhere dense set. With `w = notchedVertices o …` and
`w(t) = w + t`:
(i) `v i` on edge `j` of `w(t)` puts `t` on the line through `v i - w j` with the direction of that
edge; (ii) `w j + t` on edge `i` of `v` puts `t` on the line through `v i - w j` with the direction of
that edge (any direction if the edge is degenerate, since `v` is not assumed injective); (iii) an edge
of `v` parallel to edge `j` and meeting it after translation puts `t` on the line of (i). The 20-gon's
edges are nonzero (`notched_edge_ne`), a finite union of lines has empty interior, so some `t` in
`ball 0 l` avoids all of them.

`PlaneFacts.exists_gp_cover` follows the commission's outline, with one correction to it: `enclose`
gives `polyInterior J ⊆ G`, but not `closure (polyInterior J) ⊆ G`, which the Lebesgue-number step
needs. `enclose` is therefore applied to the open set `thickening (l₀/2) M`, where
`thickening l₀ M ⊆ G`, and then `closure (polyInterior J) ⊆ cthickening (l₀/2) M ⊆ G`. Diameters and
the no-triple property are not transported along the translation: they hold for every offset
(`diam_notched_le`, `notched_no_triple`).

**On the definition (the judgement asked for).** I recommend keeping `InGeneralPosition` as it is.
For simple `v` and `w` it already implies the alternative the commission suggests: a common point of
`polygonOf v` and `polygonOf w` is not a vertex of either (the first two clauses), so it is interior
to exactly one edge of each, and those edges are not parallel (third clause). The intersection is
then finite (`finite_inter_of_gp`), and every crossing is transversal. For batch 120 a derived lemma
stating exactly this form ("each common point lies in the relative interior of a unique edge of
each, and the two edges are not parallel") would be convenient; it does not need a new definition.
The one thing batch 120's crossing analysis will still have to prove is that at a transversal
crossing the second polygon passes from one side of the first to the other. This is a local
statement in the style of `polygon_local_rays`/`ball_diff_rays`. Batch 120 may also prefer to apply
the general-position property to `notchedPoly` against `J` through `isSimpleClosedPolygon_iff`,
which is available.

## Item 4 — cross-cuts: proved

`IsSimpleClosedPolygon.split_two`, `isSimpleClosedPolygon_of_arcs`,
`IsSimplePolyArc.isConnected_diff_ends`, `PlaneFacts.crosscut`.

* `split_two`: a simple closed polygon is an arc plus its closing edge (`twoArcs_base`; the only
  geometric input is that a nondegenerate segment is not contained in a finite set, which excludes
  overlapping adjacent edges). The two ends are then moved one at a time to `a` and `b`
  (`TwoArcs.move`): split the arc containing the new point and glue the other piece to the other arc.
* `isSimpleClosedPolygon_of_arcs` comes from batch 118's `isSimpleClosedPolygon_of_two_arcs` after
  reversing the second arc, so `IsThreaded` was not needed and `m = 2` does not arise.
* `isConnected_diff_ends`: each segment minus the ends of the arc lies between its open segment and
  its closure; consecutive pieces share their common vertex.
* `crosscut`: as in the docstring, with one simplification: **`local_side` is not used**. That
  `α₂ \ {a, b}` lies in the exterior `V₁` of `α₁ ∪ c` follows because its points are in
  `closure V` (`PlaneFacts.split`) and `V ⊆ V₁`; `U₁ ⊆ U` follows because `U₁` is connected, misses
  `J` and cannot lie in `V ⊆ V₁`. The rest uses `split` and `janiszewski` (with `Γ₁ ∩ Γ₂ = c`
  connected) as outlined.

**Shapes for batch 120.** (i) The cross-cut induction can use `crosscut` as stated. It will probably
also want the exterior form: `closure (polyInterior Γᵢ) = polyInterior Γᵢ ∪ Γᵢ`, from
`PlaneFacts.split`, and "a cross-cut of `J` lying in `closure (polyInterior Γᵢ)` and missing
`c \ {a, b}` is a cross-cut of `Γᵢ`". These are short consequences and need no change here. (ii) For
the crossing structure, the derived form of general position above, together with
`notched_eq_polyInterior` and `frontier_notched`. (iii) Needs nothing new from this batch beyond
`notched_eq_polyInterior`.

## Item 5 — the hypothesis: open

`treeLike_nonseparating (hPF : PlaneFacts) (hM : IsTreeLike M) : ∀ K ⊆ M, IsContinuum K →
¬ SeparatesPlane K` was neither proved nor refuted, and no `sorry` or field was added.

The reduction is elementary (informal, not formalized). Suppose `K ⊆ M` separates the plane, and let
`w` be in a bounded component of `Kᶜ`, with `d = dist w M`. Take a tree chain `G` covering `M` with
mesh `< d/2`, and intersect every link with the open `d/2`-neighbourhood of `M`. This keeps the
property of having no three links with a common point, and it keeps the property of having no
circular subchain, because the intersection graph only loses edges and a graph with a cycle has an
induced cycle, which is a circular chain. Then `U = ⋃ G` is an open set containing `K` and not `w`.
The component of `w` in `Uᶜ` lies in the component of `w` in `Kᶜ`, so `U` separates `w` from `∞`. No
single link can do this: a link stays at distance `≥ d/2` from `w`, and a set separating `w` from `∞`
in the sup metric then has diameter `≥ d`. A proof therefore needs: **the union of the links of a
tree chain of mesh `< d/2`, all at distance `≥ d/2` from `w`, does not separate `w` from `∞`.** The
small mesh matters here. Two links forming a chain can separate a point that neither link separates
alone, for example a C-shaped link and a small link bridging its gap and meeting it at both ends. But
such a C-shaped link has diameter `≥ d`.

That statement is where the interface falls short. The natural induction removes a leaf of the tree
chain (coherence and the absence of circular subchains make the nerve a tree) and glues it back
with Janiszewski. But Janiszewski (the only separation tool in `PlaneFacts`) needs compact sets with
connected or empty intersection, and Bing's links are arbitrary open sets: neither the links nor
their pairwise intersections need be connected, and the closures of two adjacent links can meet in
many pieces. The classical proofs avoid this with an invariant that sees the nerve rather than the
sets. One is Borsuk's criterion: a compactum separates the plane iff it admits an essential map to
the circle, and a tree-like continuum admits none because each map factors up to homotopy through
an ε-map to a tree. The other is Čech cohomology: `Ȟ¹(M) = 0` for tree-like `M`, and Alexander
duality. Neither essential maps to `S¹` nor Čech cohomology is in the repository or in `PlaneFacts`.
A proof inside the present interface would need a new field of comparable strength, for example
Borsuk's separation criterion for compacta, or Janiszewski for compact sets whose intersection has
finitely many components counted with the right multiplicity (the "unicoherence" form). Finding a
refutation would require a tree-like continuum containing a separating subcontinuum, which the
classical theorem excludes. I found no reason to suspect the definitions, so I expect the
implication to be true.

## Ledger notes

* **(a) "the components of `d₀ ∩ dᵢ` are interiors of simple closed curves".** I agree with the
  commission's analysis: the assertion is true in general and unargued by Bing. I see no
  counterexample. Its general proof needs the structure of the frontier of a component (a compact
  subset of the graph `J ∪ ∂dᵢ`), and the Jordan curve theorem excludes pinch points and slits.
  This is an informal assessment; nothing in this batch formalizes it. The repository's route is
  general position: item 3 provides it (`PlaneFacts.exists_gp_cover`) and item 4 provides the
  cross-cut theorem; batch 120 does the induction. The weak form `theorem7_weak` (links bounded,
  open, connected, regular open, not separating the plane) is already a theorem relative to
  `PlaneFacts`.
* **(b) "tree-like" versus "contains no continuum separating the plane".** As in item 5: open
  relative to `PlaneFacts`; the obstruction is the lack of a separation invariant that applies to
  the union of non-connected links, such as Borsuk's criterion or Čech cohomology.
* **Correction to the outline of `exists_gp_cover`**: `enclose` does not control
  `closure (polyInterior J)`; it must be applied to a thickening of `M` whose closure lies in `G`.

## Not attempted

Batch 120 (the cross-cut induction, the crossing structure, `theorem7_1951`); `theorem3_end`;
`fugate_cor1`.
