Commission read: COMMISSION-batch120.md (batch 120 — Bing 1951 (Duke), Theorem 7, part II: the components are polygon interiors; `theorem7_1951`).

# Report, batch 120

**Outcome.** Items 1–5 are **proved**, including `theorem7_1951`. No `sorry` remains in
`HPC/Plane/Tree7Comp.lean`. No statement of the skeleton was refuted. Two arguments in the
skeleton's docstring of `component_inter_eq_polyInterior` have a false step (see *Refutations*), but
the statement is true and is proved by a shorter argument. Every theorem of the batch depends only
on axioms among `[propext, Classical.choice, Quot.sound]` (`doc/batches/audits/axioms-batch120.txt`).
`PlaneFacts` is a hypothesis, so `sorryAx` still occurs in exactly two declarations of `axioms.txt`,
the open targets `theorem3_end` and `fugate_cor1` (413 declarations, up from 401).

**Installation.** The skeleton is installed as `HPC/Plane/Tree7Comp.lean`, and
`import HPC.Plane.Tree7Comp` is now the last line of `HPC.lean`. The uploads were filed as
`doc/batches/COMMISSION-batch120.md` and `doc/batches/skeletons/Tree7Comp.lean`. No auxiliary file
was needed: the file is about 800 lines, and its auxiliary lemmas are in its §0.

**Edits to existing files.** No existing Lean file was edited except `Axioms.lean` (new group
"Bing 1951 (Duke) §3, Theorem 7 — relative to `PlaneFacts` (batch 120)", 12 entries). `axioms.txt`
was regenerated, and the previous version is kept as `doc/batches/audits/axioms-before-batch120.txt`.
`README.md` and `OPEN.md` were edited as asked in §3.3.

**Housekeeping.**
* `theorems-3-4-scheduling(23).md`, `(24).md` and `(25).md` were deleted from the repository root.
* The notes file was uploaded with this run as `theorems-3-4-scheduling(26).md`. It was moved to
  `doc/theorems-3-4-scheduling.md`, replacing the copy there.

## Refutations

No statement was refuted. On the candidates named in the commission:

* **The `c ∩ c' ⊆ J` clause.** It is enough, as you expected. In the induction, a cross-cut `c'` of
  `C.erase c` meets `c` only in `J`. So `c' \ J`, which is `c'` minus its ends, is connected and lies
  in `polyInterior J \ c = U₁ ⊔ U₂`, hence in one side. Its ends lie in `closure Uᵢ ∩ J = αᵢ`
  (`IsCrosscut.inter_subset_side`). Two cross-cuts of the same side meet in
  `c' ∩ c'' ⊆ c' ∩ J ⊆ αᵢ ⊆ Γᵢ`. Nothing else is needed.
* **The degenerate cases.** The statement is true in each case, but the docstring's arguments for
  `X = ∅` and `X = {a}` each contain a false step:
  - `X = ∅`: the docstring first shows `P ⊆ U`, then claims that `closure U = U ∪ J` misses `P`.
    It does not, since `P ⊆ U`.
  - `X = {a}`, first branch: the docstring uses that `U ∪ (J \ {a})` misses `P`. This contradicts
    the case hypothesis `P ∩ U ≠ ∅`.

  The proof avoids both. For `|X| ≤ 1` the set `P \ J = P \ X` is connected: it is `P`, or `P`
  minus one point (`IsSimpleClosedPolygon.isConnected`, `isConnected_diff_singleton`). Then:
  - If `P ∩ U = ∅`, `U` is connected, misses `P = frontier N` and contains `x ∈ N`, so `U ⊆ N`
    and the component is `U`.
  - If `P ∩ U ≠ ∅`, then `P \ J ⊆ U`, so `P ⊆ U ∪ J`. The new lemma
    `PlaneFacts.polyInterior_subset_of_subset` gives `N ⊆ U`, and the component is `N`. That lemma
    works because the exterior `V` of `J` is connected, unbounded and misses `P`, so it misses the
    bounded set `N`. As `N` is open and `J ⊆ closure V`, `N` misses `J` too.

  The analysis of `J \ {a}` is not needed.
* **The `X = ∅` argument.** False as written; see the previous point. The corrected argument above
  covers `X = ∅` and `X = {a}` together.

## Items

### 1. Cross-cut families and the induction — proved

All three are proved: `connectedComponentIn_union_of_disjoint_open`, `IsCrosscut.of_side` and
`PlaneFacts.components_of_crosscuts`.

* **Change of shape in `IsCrosscut.of_side`.** `hside` is now `c' \ J ⊆ polyInterior (α ∪ c)`. For
  a cross-cut, `c' ∩ J = {a, b}`, so `c' \ J = c' \ {a, b}` (`diff_eq_diff_of_inter_eq`), and the
  awkward quantification over the ends goes away. The hypothesis `hΓ` was unused and was dropped.
* **The induction.** Strong induction on `C.card`, as in the docstring. Write `U₁`, `U₂` for the
  two sides of `c`. The two sub-families are filters of `C.erase c` by `c' \ J ⊆ U₁` and by
  `c' \ J ⊆ U₂`.
* **The split of `polyInterior J \ ⋃ C`.** Take a point of `U₁` on a cross-cut of the second family.
  It is off `J`, so it would lie in `U₂`, which is impossible. No closure argument is needed.
* **The clause `Γ ⊆ J ∪ ⋃ C`** cost nothing and was kept.

### 2. Decompositions — proved

`exists_arc_decomposition` is proved by `Finset.induction_on` with `IsSimplePolyArc.split`, as
outlined. The new point `x` lies in exactly one piece, since two pieces meet only in the old cut
points.

`exists_polygon_decomposition` is proved with `split_two` at two points `a ≠ b` of `X`, then
`exists_arc_decomposition` on each arc with the points of `X \ {a, b}` lying on it. Statements
unchanged.

### 3. The cross-cut family of `P` in `J` — proved

`PlaneFacts.exists_crosscutFamily` is proved as in the docstring. The family consists of the pieces
of the decomposition that meet `polyInterior J`.

The exterior is not needed. A piece minus its ends is connected and misses `J = frontier U`
(`γ ∩ J = γ ∩ X = ends`). If it meets `U`, it lies in `U` (`subset_of_isConnected_of_disjoint_frontier`).
The hypothesis `2 ≤ hfin.toFinset.card` was kept in that form.

### 4. Identification and the main theorem — proved

All three are proved: `subset_of_isConnected_of_disjoint_frontier`,
`PlaneFacts.connectedComponentIn_inter_eq` and `PlaneFacts.component_inter_eq_polyInterior`.

* **Change of shape in `PlaneFacts.connectedComponentIn_inter_eq`.** The hypothesis
  `hU : IsOpen U` was unused and was dropped.
* **The main theorem.** The case `2 ≤ |X|` follows the docstring. The cases `|X| ≤ 1` use the
  corrected argument given under *Refutations*.

### 5. Theorem 7 — proved

* **`isSimpleVertices_notchedVertices`.** It was not in `Tree7Notched` under another name. It is
  assembled from `notchedVertices_injective` and `notchedVertices_edges`, the two facts behind
  `isSimpleClosedPolygon_notchedPoly`.
* **`finite_inter_notchedPoly_of_gp`.** This is `finite_inter_of_gp`, since `notchedPoly` is by
  definition `polygonOf notchedVertices`.
* **`theorem7_1951`.** Assembled as in the docstring, in this order:
  1. `PlaneFacts.exists_gp_cover`;
  2. `treeChain_of_cover` with `D = notchedFamily o δ η r I`;
  3. for each member `connectedComponentIn (polyInterior J ∩ notched …) y`, rewrite with
     `notched_eq_polyInterior`;
  4. apply `component_inter_eq_polyInterior` with `isSimpleClosedPolygon_notchedPoly` and
     `finite_inter_notchedPoly_of_gp`.

  The statement is unchanged from the skeleton.

## Ledger note for Theorem 7 (final form)

(a) **"The components of `d₀ · dᵢ` are interiors of simple closed curves."** Bing asserts this
without argument. It is true in general; this is an informal claim, not checked here.

Here it is established for any two simple closed polygons whose boundaries meet in finitely many
points (`PlaneFacts.component_inter_eq_polyInterior`), relative to `PlaneFacts`. Each component is
the interior of a simple closed polygon. The proof uses cross-cut induction, needs no
transversality, and handles the degenerate cases by connectedness. A translation of the grid
(batch 119, `exists_gp_translation`) puts the notched squares in general position with
`J = polygonOf v`, which makes the intersection finite (`finite_inter_of_gp`).

(b) **The hypothesis.** Bing states Theorem 7 for tree-like continua. His proof, through Theorem 6,
uses "contains no continuum which separates the plane".

`theorem7_1951` is stated with the latter hypothesis: no subcontinuum of `M` separates the plane.
The implication "tree-like ⇒ no subcontinuum separates the plane" (`treeLike_nonseparating`) is open
relative to `PlaneFacts` (batch 119, item 5: no separation tool for unions of non-connected open
links; Borsuk/Čech). It was not attempted in this batch.

(c) **Scope.** With Theorem 7, §3 of the Duke paper (Theorems 6 and 7) is checked relative to
`PlaneFacts`.

## Deliverables

1. Items 1–5 are in `HPC/Plane/Tree7Comp.lean`. `#print axioms` for every theorem of the file
   (23 theorems, including the auxiliary lemmas of §0) is in `doc/batches/audits/axioms-batch120.txt`,
   generated by `axioms-batch120.lean`. `axioms.txt` was regenerated; the only new lines are the 12
   entries of the batch-120 group.
2. This report.
3. `README.md` and `OPEN.md`:
   - `README.md` now lists Duke 1951 "Theorems 1–16", with the note that 6 and 7 are relative to
     `PlaneFacts` (jct for polygons, enclosing polygon, Janiszewski for compacta). The batch count
     is now 120.
   - `OPEN.md` keeps the two live items unchanged and has a new section "Relative results" listing
     `theorem6_1951`, `theorem7_1951` and the interface.
4. Not attempted: `theorem3_end`, `fugate_cor1`, `treeLike_nonseparating`.

**Build.** `lake build HPC HPCArchive HPCCensus` succeeds. The search for `sorry` in
`HPC/Plane/Tree7Comp.lean` finds nothing.
