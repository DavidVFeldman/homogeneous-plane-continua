# Commission: batch 117 — Bing 1951 (Duke) §3, Theorems 6 and 7: definitions, the plane-topology interface, the grid cover

**Go!** Runs on top of the batch-116 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch117.md` — this text (also pasted into the prompt);
* `Tree67.lean` — a skeleton. Save it as `HPC/Plane/Tree67.lean` and add
  `import HPC.Plane.Tree67` at the end of the root `HPC.lean`. Every `sorry` is a work item;
  the fields of `PlaneFacts` are hypotheses, not work items. Shapes may be adjusted with the
  change recorded. No existing file is to be edited, except `Axioms.lean`/`axioms.txt` (new group
  "Bing 1951 (Duke) §3, Theorems 6–7 — relative to `PlaneFacts`", batch 117).

The report names the commission read in its first line.

## 0. On batch 116

Audited: the housekeeping exactly as asked; 349 declarations; `sorryAx` in two.

## 1. The plan for §3 (three batches)

Bing's proof of Theorem 6 (p. 656), transcribed in the skeleton's header and here in full:

[Quotation moved to doc/sources/transcriptions/bing51duke.md, §doc/batches/COMMISSION-batch117.md, Bing's proof of Theorem 6 (p. 656); batch 204.]

* **Batch 117 (this one):** the definitions (simple closed polygon, `polyInterior`, separation,
  coherent, circular chain, tree chain, tree-like); the interface `PlaneFacts` (polygonal Jordan
  curve theorem; the enclosing polygon; Janiszewski) and what follows from `jct` for
  `polyInterior`; the first paragraph of the proof: `M` nowhere dense, a grid with no vertex on
  `M`, the notched enlargements `d_i` with `M·q̄_i ⊆ d_i`, no triple points, diameter `< ε`; two
  lemmas for later (components of open sets are open; minimal covers are coherent).
* **Batch 118:** the second and third paragraphs relative to `PlaneFacts`: `J` from `enclose`
  with `G = ⋃ d_i`; `H` = components of `polyInterior J ∩ d_i`; a minimal finite subcover `H'`
  of `M`; no triple points; the circular-chain contradiction — a simple closed polygon threaded
  through `h_1, …, h_m` (polygonal arcs in the connected open `h_i`, consecutive ones trimmed to
  meet only at their common point), `W ∩ polyInterior = ∅` since `W` is connected and unbounded
  and misses the polygon (no Jordan theorem needed for that), and the point `q` from `jct` and
  `janiszewski`; coherence from minimality; hence `theorem6_1951 (h : PlaneFacts)`.
* **Batch 119:** Theorem 7: the links `h` are interiors of simple closed polygons (components of
  the intersection of two polygon interiors; the notched squares are star-shaped polygons), and
  the hypothesis: Bing's Theorem 7 assumes "tree-like" while his proof uses "contains no
  separating continuum"; the implication (tree-like ⇒ no subcontinuum separates the plane) is
  not in his text. Both facts to be added to `PlaneFacts` or proved; ledger.

Why an interface: the three facts are theorems of plane topology whose formalization is a project
of its own (the Mizar and HOL Light ports are on other toolchains). Every result of §3 will carry
the explicit hypothesis `PlaneFacts`, so the audit shows exactly what is assumed; the interface
can be discharged later by proof or by import.

## 2. Items

1. **Definitions** (`polygonOf`, `IsSimpleClosedPolygon`, `polyInterior`, `SeparatesPlane`,
   `SeparatesPts`, `IsCoherent`, `IsCircularChain`, `IsTreeChain`, `IsTreeLike`). Check them
   against p. 653 and say if a reading differs (in particular: Bing's circular chain has "more
   than two links and the first and last links intersect", and a chain's links meet *iff*
   adjacent — the skeleton's `IsCircularChain` says exactly that; a tree chain's "no subcollection
   is a circular chain" quantifies over subsets, including the whole).
2. **`PlaneFacts`** and `PlaneFacts.polyInterior_eq`: from `jct`, `polyInterior J = U` (the
   bounded component: every point of `U` has bounded component `U`; a point of `V` has unbounded
   component `V`), hence open, connected, bounded, with frontier `J`, and
   `(J ∪ polyInterior J)ᶜ = V` connected. Say if `jct`'s formulation should be changed (for
   instance, adding `J ⊆ closure U` is implied by `frontier U = J`).
3. **The grid**: `interior_eq_empty_of_noSeparating` (a closed square `Q ⊆ M`: the boundary of
   `Q` is a continuum contained in `M` and separates the plane, since its complement is the
   disjoint union of the two nonempty open sets `interior Q` and `(closure Q)ᶜ`);
   `exists_grid_offset` (the bad offsets `{o ∈ [0,ε)² | some vertex lies in M}` are a finite union,
   over the lattice points `v` with `v + [0,ε)²` meeting the bounded `M`, of the closed nowhere
   dense sets `(M − v) ∩ [0,ε)²`); `finite_gridSq_meeting`; `notched`, `isOpen_notched`,
   `diam_notched_le` (sup metric: the set lies in a box of side `ε + 2η`),
   `inter_gridSq_subset_notched` (a point of `M` in the closed square is at distance `≥ r` from
   the four corners, so it is in the open square or on a side at distance `≥ r` from its ends,
   hence in a strip), `notched_no_triple` (two notched squares of distinct index meet only if the
   indices differ by one step and then inside the strip along the common side, which lies in
   `(open square) ∪ (strip)` of each and avoids the `r`-corners; a point in three distinct ones
   would need three indices pairwise one step apart — impossible; and two squares diagonal to each
   other meet only near the common corner, which is excluded as `η < r`). Constants may be
   changed; record.
4. **`exists_notched_cover`**: `δ := ε/4` (or whatever makes `diam < ε` in the sup metric), the
   offset from item 3, `r := ` half the distance from `M` to the (finite relevant part of the)
   vertex set, `η := r/2`, `D := ` the notched squares of the indices meeting `M`; every link meets
   `M`; covering since `M ⊆ ⋃ q̄` and `M ∩ q̄ ⊆ d`.
5. **Two lemmas**: `isOpen_connectedComponentIn_of_isOpen` (local connectedness of `Pt`;
   Mathlib: `IsOpen.connectedComponentIn` for locally connected spaces — find it),
   `isCoherent_of_minimal_cover` (as in the docstring).

Report each item *proved / refuted / open with the obstruction stated*; refutations first (the
definitions are the likeliest place for a slip). No new `sorryAx` is expected: `PlaneFacts` is a
hypothesis, not an axiom, so the audit stays at two.

## 3. Deliverables

1. Items 1–5; `#print axioms` in `axioms-batch117.txt`; `axioms.txt` regenerated (`sorryAx` in 2).
2. Report: first line names the commission read; items in order; any reading of p. 653 that
   differs from the skeleton.
3. Not attempted: Theorems 6 and 7 themselves (batches 118, 119); `theorem3_end`, `fugate_cor1`.

## 4. Next

Batch 118 as in §1.
