Commission read: COMMISSION-batch130.md (batch 130 — `enclose`, part I: the grid union, its boundary graph, simple cycles, the enclosing polygon).

# Report, batch 130

**Outcome.** Nothing refuted; every item is **proved**. The skeleton `Enc1.lean` is delivered with
every `sorry` replaced by a proof, spread over three files:

* `HPC/Plane/Enc1Cyc.lean` — items 1 and 2 (the interior as the odd set; simple cycles);
* `HPC/Plane/Enc1Grid.lean` — the grid geometry of item 3 for an **arbitrary** finite index set of
  squares (`sqUnion δ S`, `bdryOf δ S`);
* `HPC/Plane/Enc1.lean` — item 3 for `M` (`sqIdx`, `gridUnion`, `sqEdges`, `bdryGraph`) and item 4.

`import HPC.Plane.Enc1` is added at the end of `HPC.lean`. No existing file is edited except
`HPC.lean`, `Axioms.lean` (new group "Enclosing polygon (batch 130)"), `axioms.txt` (regenerated)
and `README.md` (batch count).

| item | verdict |
|---|---|
| refutation candidates (`frontier_gridUnion` at diagonal vertices; `disjoint_frontier_gridUnion` with `cthickening δ`; the `List.foldr` form of the decomposition; `IsSimpleCycle`) | **none refuted** (below) |
| 1. `polyInterior_eq_oddSet`, `polyEdges`, `cycParity_polyEdges`, `graphSet_polyEdges` | **proved**, as stated |
| 2. `IsSimpleCycle`, `exists_simpleCycle_decomposition`, `cycParity_foldr` | **proved**; `IsSimpleCycle` as in the skeleton; the `List.foldr` form kept |
| 3. the grid union (`gsq` … `graphSet_bdryGraph_subset`) | **proved**; `bdryGraph` defined via the exclusive-or indexing, its skeleton description proved as `mem_bdryGraph_iff_card`; unused hypotheses dropped |
| 4. `farPt` … `exists_enclosing_polygon` | **proved**; `exists_enclosing_polygon` exactly as stated |

Build: `lake build HPC` succeeds. No `sorry` in the three new files. `axioms.txt` regenerated
(611 lines, 26 new in the group "Enclosing polygon (batch 130)"; `sorryAx` in **one line**, `HPC.Plane.fugate_cor1`, unchanged); the previous `axioms.txt` is saved
as `doc/batches/audits/axioms-before-batch130.txt`. Per-batch audit:
`doc/batches/audits/axioms-batch130.{lean,txt}` (all 65 theorems of the three new files and
`fugate_cor1`; every theorem except `fugate_cor1` shows `[propext, Classical.choice, Quot.sound]`
or, for the four index lemmas `fnxt_*`, the subset `[propext, Quot.sound]`).

## Refutations first: none

* **`frontier_gridUnion` at a vertex with two diagonally opposite squares of `Q`.** The statement
  holds. Such a vertex is a frontier point and an end of four boundary edges, and the statement
  only asserts equality of point sets, so nothing is violated. The proof never looks at vertex
  configurations: both sides are shown equal to "the points lying in a square of `S` and in a
  square not in `S`" (`mem_frontier_sqUnion_iff`, `mem_graphSet_bdryOf_iff`).
* **`disjoint_frontier_gridUnion` with `cthickening δ`.** Holds; only `M ⊆ cthickening δ M` is used
  (every square containing a point of `M` is in `sqIdx`). The thickening plays no role beyond that
  and the bound `Q ⊆ cthickening (2δ) M`.
* **The `List.foldr` form of `exists_simpleCycle_decomposition`.** Kept as stated, with
  `L.Pairwise Disjoint`; `cycParity_foldr` is proved for it (`mem_foldr_union`, `Finset.sum_union`).
* **`IsSimpleCycle`.** Kept exactly as in the skeleton: `∃ n v, IsSimpleVertices v ∧ graphSet C =
  polygonOf v ∧ ∀ x, cycParity C x = parity v x`. This is all that item 4 uses.

## Item 1: the interior as the odd set

`polyInterior_eq_oddSet` is `polyInterior_eq_of_split` applied to the two parity classes, with
the unboundedness of the even class taken from the proof of `jct_polygon` (`polygon_separates`).
`cycParity_polyEdges` needs only injectivity of `v` (the edge map `i ↦ (v i, v (i+1))` is
injective on its first coordinate), then `Finset.sum_image` and `Finset.sum_boole`.
`graphSet_polyEdges` is by `simp`.

## Item 2: simple cycles

The argument is a graph-theoretic one, with no planar geometry:

* `exists_other_nbr`: in a cycle, a point adjacent to `q` has a second neighbour `r ≠ q`. Its
  degree is positive, hence at least `2`, so a second segment exists. Its other end is not `q`,
  because `(p, q)` and `(q, p)` cannot both be in a proper graph: they are distinct segments with
  the same point set.
* `cycle_or_extend`, `exists_cycle_vertices`: paths are `f : ℕ → Pt` on `[0, k)`, with distinct
  points and consecutive points adjacent. At the end `f (k-1)` take a neighbour `r ≠ f (k-2)`.
  If `r = f i` for some `i < k`, then `i ≤ k - 3` and `f i, …, f (k-1)` is a cyclic sequence of at
  least three distinct adjacent vertices. Otherwise the path extends. Lengths are bounded by
  `card (vertices Z)`, so induction on the difference ends the walk.
* `simpleCycle_of_vertices`: from such a sequence `w : Fin n → Pt`, take the segment of `Z` joining
  `w i` and `w (i+1)`, in whichever orientation `Z` has it, and call the set of these segments `C`.
  The map to segments is injective (`n ≥ 3`). The conditions of `IsSimpleVertices w` follow from
  properness: distinct segments meet only at common ends. `graphSet C = polygonOf w`, and
  `cycParity C = parity w` (`ceInd_comm` handles the orientation). Every degree of `C` is even:
  `deg C p = #{i | p = w i} + #{i | p = w (i+1)}`, and the two counts agree under the cyclic
  shift.
* `exists_simpleCycle_decomposition`: strong induction on `card Z`. `Z \ C` is again a cycle,
  since `deg Z = deg C + deg (Z \ C)`.

## Item 3: the grid union

Definitions adopted:

* `sqIdx M δ := if h : S.Finite then h.toFinset else ∅`, where `S` is the set of indices of squares
  meeting `cthickening δ M`. `finite_sqIdx_set` shows `S` is finite for bounded `M` and `δ > 0`,
  so `mem_sqIdx_iff` holds as stated.
* `hseg δ a b := ((δa, δb), (δ(a+1), δb))` and `vseg δ a b := ((δa, δb), (δa, δ(b+1)))`, both
  lexicographically increasing. `sqEdges δ a b := {hseg a b, hseg a (b+1), vseg a b, vseg (a+1) b}`.
* **Change of shape:** `bdryGraph M δ := bdryOf δ (sqIdx M δ)`. Here `bdryOf δ S` consists of the
  `hseg δ a b` with `(a, b) ∈ S` xor `(a, b-1) ∈ S`, and the `vseg δ a b` with `(a, b) ∈ S` xor
  `(a-1, b) ∈ S`. The skeleton's description ("edges of squares of `sqIdx` belonging to exactly
  one square of `sqIdx`") is proved as `mem_bdryGraph_iff_card`:
  `s ∈ bdryGraph M δ ↔ (sqIdx.filter (s ∈ sqEdges ·)).card = 1`.

The local case analysis is organised around one characterisation, for any finite `S`:

* `mem_frontier_sqUnion_iff`: `z ∈ frontier (sqUnion δ S)` iff `z` lies in a square of `S` and in
  a square not in `S`.
  * `→`: if every square containing `z` is in `S`, then `z` is interior (`mem_interior_sqUnion`).
    The squares containing `z` cover a neighbourhood of it: in each coordinate a point is in one
    or two grid intervals (`exists_nbhd_cover`), and balls in the sup metric are products.
  * `←`: points strictly inside a square not in `S` lie in no other closed square
    (`idx_eq_of_strict`), so they are outside the union. Points `z + t (c - z)`, with `c` the
    centre of that square, approach `z` (`exists_near_not_mem`).
* `mem_graphSet_bdryOf_iff`: the same condition characterises the points of boundary edges.
  * `→`: both squares of a boundary edge contain its points.
  * `←`: given `(a, b) ∈ S` and `(a', b') ∉ S`, both containing `z`, the square `(a', b)` also
    contains `z`. If it is in `S`, the pair `(a', b)`, `(a', b')` lies in one column; otherwise
    the pair `(a, b)`, `(a', b)` lies in one row. Two squares of a column (resp. row) containing
    `z`, one in `S` and one not, are vertically (resp. horizontally) adjacent, and their common
    edge is a boundary edge through `z` (`mem_graphSet_bdryOf_col`, `_row`). Diagonal vertices
    therefore need no separate treatment.
* `frontier_sqUnion` follows from these two. `isProper_of_gridSeg` shows that any finite set of
  grid edges of one mesh is proper. Distinct point sets come from the lexicographic orientation
  (`eq_of_segment_eq_lex`). Intersections are handled in four cases (h/h, h/v, v/h, v/v) with
  integer bookkeeping (`idx_close`).

Then for `M`: `gridUnion_subset_cthickening` (the square diameter is `δ` in the sup metric, and
`cthickening_cthickening_subset`), `isCompact_gridUnion`, `disjoint_frontier_gridUnion`,
`subset_interior_gridUnion`, `frontier_gridUnion` and `graphSet_bdryGraph_subset`.

**Hypotheses dropped** (unused): `hM` from `isProper_bdryGraph`, `frontier_gridUnion`,
`graphSet_bdryGraph_subset` and `interior_gridUnion_disjoint_component`; `hM` and `hδ` from
`farPt_not_mem`. `isProper_bdryGraph`, `frontier_gridUnion`, `graphSet_bdryGraph_subset` and
`interior_gridUnion_disjoint_component` take `M` explicitly.

## Item 4: the outer cycle and the enclosing polygon

* `gridR M δ := sSup (Prod.fst '' gridUnion M δ)` and `farPt M δ := (gridR M δ + 1, 0)`. The open
  half-plane `Ioi (gridR M δ) ×ˢ univ` is preconnected, misses the graph and contains the far
  point, so it lies in the component `K` (`halfPlane_subset_component`). Hence `K` is unbounded
  (`not_isBounded_component`).
* `interior_gridUnion_disjoint_component`: `K` is preconnected and misses `frontier Q`, so
  `K ⊆ Qᶜ ∪ interior Q`. It meets the open set `Qᶜ` at the far point, so `K ⊆ Qᶜ`.
* `cycParity_oddSet_eq_one_on`: for `x ∈ M`, compare `gFun` at `x` (not in `K`, not on the graph)
  with `gFun` at a point `y` of the half-plane east of the `R` of `cycParity_far` (in `K`). This
  gives `0 + cycParity Z x = 1 + 0`. The value of `cycParity Z` at the far point itself is never
  needed.
* `exists_enclosing_polygon`, as stated. Decompose `Z`. The parities sum to `1` at a point
  `x₀ ∈ M`, so some simple cycle `C` has parity `1` there. Then
  `parity_eq_of_isPreconnected` on `M`, which misses `graphSet C ⊆ frontier Q`, and
  `polyInterior_eq_oddSet` give `M ⊆ polyInterior J`. `K` is connected, unbounded and misses `J`,
  so `polyInterior_disjoint_of_unbounded` applies.

## For batch 131

* What remains of `enclose` is `polyInterior J ⊆ G` for small mesh. By
  `exists_enclosing_polygon`, it suffices that `Kᶜ ⊆ G`, i.e. every point of `Gᶜ` lies in
  `K = connectedComponentIn (graphSet (bdryGraph M δ))ᶜ (farPt M δ)`. Useful facts already
  available: `graphSet (bdryGraph M δ) ⊆ gridUnion M δ ⊆ cthickening (2δ) M`
  (`graphSet_bdryGraph_subset`, `gridUnion_subset_cthickening`), and the half-plane east of
  `gridR M δ` lies in `K` (`halfPlane_subset_component`). A path in the complement of
  `cthickening (2δ) M` from a point to that half-plane is a path in
  `(graphSet (bdryGraph M δ))ᶜ`, so its points lie in `K`. Hence a compact connected set `P`
  with `infDist P M > 2δ` that meets the half-plane lies in `K`.
* `exists_enclosing_polygon` needs only `IsContinuum M` (compact and connected), not
  `¬ SeparatesPlane M`. Non-separation enters only in batch 131 (the paths in `Mᶜ`).
* The grid lemmas hold for any finite index set (`sqUnion`, `bdryOf`), in case a different choice
  of squares is convenient.

## Not attempted

Batch 131, `fugate_cor1`, `treeLike_nonseparating`.
