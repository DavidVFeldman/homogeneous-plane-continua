# Commission: batch 130 — `enclose`, part I: the grid union, its boundary graph, simple cycles, the enclosing polygon

**Go!** Runs on top of the batch-129 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch130.md` — this text (also pasted into the prompt);
* `Enc1.lean` — a skeleton, `sorry`s as work items, including the bodies of `sqIdx`, `sqEdges`,
  `bdryGraph`, `farPt` (definitions for you to write). Save it as `HPC/Plane/Enc1.lean`, add
  `import HPC.Plane.Enc1` at the end of the root `HPC.lean`. Shapes may be adjusted with the change
  recorded. No existing file is to be edited except `HPC.lean`, `Axioms.lean`/`axioms.txt` (group
  "Enclosing polygon (batch 130)"), `README.md` (batch count).

The report names the commission read in its first line; items *proved / refuted / open with the
obstruction stated*.

## 0. On batch 129

Audited and accepted: the field is polygonal and proved, `planeFacts_of_enclose` typechecks,
`PlaneFacts` has one undischarged field. One gap in my commissioned argument, caught and fixed:
`A := Γ₁ ∩ closure (h₁ ∩ h₂)` does not give `A ∩ B ⊆ Γ` (a common point outside `closure U` is no
candidate for `q`); the sets must be `Γᵢ ∩ closure (U ∩ h₁ ∩ h₂)` — recorded in my notes as a
commission slip. The general saturated-set form of the polygonality lemma, needing no Jordan curve
theorem, is noted with appreciation, as is the forced re-proof of `theorem7_weak`. 585
declarations, `sorryAx` in one line, root tidy.

## 1. The design

The skeleton header has it. The point of the design: **no classification of polyomino
boundaries.** The boundary graph `G₀` of the grid union `Q` is an arbitrary proper graph of grid
segments; batch 128's `oddSet G₀ (far point)` is a cycle `Z` whose parity is `1` on `M` (by
`gFun_const`, since `M ⊆ interior Q` is off the unbounded component `K`); a decomposition of `Z` into
simple cycles and the additivity of parity give one simple closed polygon `J` with odd parity on
the connected `M`; `polyInterior J` is the odd parity set; `K` lies outside `J`. Degree-4 vertices
of `Z` (two squares of `Q` touching at a corner) are harmless: the decomposition into simple cycles
is a graph-theoretic fact and never needs the local planar picture.

## 2. Items

1. **The interior as the odd set** (`polyInterior_eq_oddSet`, `polyEdges`, `cycParity_polyEdges`,
   `graphSet_polyEdges`). The first is inside the proof of `jct_polygon`; expose it.
2. **Simple cycles** (`IsSimpleCycle`, `exists_simpleCycle_decomposition`, `cycParity_foldr`). The
   decomposition is the one graph-theoretic argument of the batch (docstring). `IsSimpleCycle`'s
   definition is yours to settle: the later steps need only `IsSimpleClosedPolygon (graphSet C)`
   and `cycParity C = parity v` for the vertex list `v` of that polygon. A closed trail without
   repeated vertices in a *proper* graph has, as point set, a simple closed polygon, and its
   `cycParity` is the `parity` of that vertex list (`cycParity_polyEdges` after identifying the edge
   sets).
3. **The grid union** (`gsq`, `sqIdx`, `gridUnion`, `mem_sqIdx_iff`, `gridUnion_subset_cthickening`,
   `isCompact_gridUnion`, `disjoint_frontier_gridUnion`, `sqEdges`, `bdryGraph`,
   `isProper_bdryGraph`, `frontier_gridUnion`, `graphSet_bdryGraph_subset`). `frontier_gridUnion`
   is the local case analysis at interior points, edge points and vertices of the grid (docstring);
   `gridSq` and `mem_gridSq_floor` (batch 117) exist. Orient the grid segments lexicographically so
   that `IsProper`'s "distinct point sets" clause holds by construction.
4. **The outer cycle** (`farPt`, `farPt_not_mem`, `interior_gridUnion_disjoint_component`,
   `cycParity_oddSet_eq_one_on`, `exists_enclosing_polygon`). All from batch 128 (`oddSet`,
   `isCycle_oddSet`, `gFun_const`), `cycParity_far`, items 1–3 and
   `polyInterior_disjoint_of_unbounded` (batch 118).

Report each item; refutations first (candidates: `frontier_gridUnion` — a vertex of the grid with
exactly two diagonally opposite squares in `Q` is a frontier point *and* an end of four boundary
edges, which the statement allows; `disjoint_frontier_gridUnion` with `cthickening δ`;
`exists_simpleCycle_decomposition`'s `List.foldr` form — change to a `Finset (Finset Seg)` with a
pairwise-disjointness clause if that is easier; `IsSimpleCycle`).

## 3. Deliverables

1. Items 1–4; `#print axioms` in `doc/batches/audits/axioms-batch130.txt`; `axioms.txt`
   regenerated (`sorryAx` in one line).
2. Report: first line names the commission read; items in order; the definitions adopted; what
   batch 131 (the uniform path argument `Kᶜ ⊆ G` for small mesh, `enclose_holds`, `planeFacts_holds`,
   and the retirement of the interface: `theorem6_1951`, `theorem7_1951` and everything else stated
   with `(hPF : PlaneFacts)` given unconditional forms, the `Axioms.lean` interface note removed,
   `OPEN.md` *Relative results* emptied, README) should know.
3. Housekeeping: uploads to `doc/batches/`, `doc/batches/skeletons/`; notes to `doc/`; nothing at
   the root.
4. Not attempted: batch 131, `fugate_cor1`, `treeLike_nonseparating`.
