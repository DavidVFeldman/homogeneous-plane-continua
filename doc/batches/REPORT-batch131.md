Commission read: COMMISSION-batch131.md (batch 131 — `enclose`, part II: the uniform path argument, `enclose_holds`, `planeFacts_holds`; Theorems 6 and 7 of Bing 1951 (Duke) unconditional; the interface retired).

# Report, batch 131

**Outcome.** Nothing refuted; every item is **proved**. The skeleton `Enc2.lean` is delivered as
`HPC/Plane/Enc2.lean` with every `sorry` replaced by a proof; `import HPC.Plane.Enc2` is added at
the end of `HPC.lean`. `PlaneFacts` is proved (`planeFacts_holds`), and Theorems 6 and 7 of Bing
1951 (Duke) hold with no hypothesis beyond their own (`theorem6_1951`, `theorem7_1951`,
`theorem7_weak`).

| item | verdict |
|---|---|
| refutation candidates (`compl_closedBall_subset_component`; `exists_far_piece`'s bound `r ≤ infDist p M`; `eastRay_subset_component`) | **none refuted** (below) |
| 1. uniform membership (`outerComp` … `compl_closedBall_subset_component`) | **proved**; `hMne` dropped from two statements (unused) |
| 2. paths and their distance from `M` (`joinedIn_compl_of_not_separates` … `exists_uniform_pieces`) | **proved**, as stated |
| 3. `exists_mesh_compl_subset`, `enclose_holds`, `planeFacts_holds`, `theorem7_1951`, `theorem6_1951`, `theorem7_weak` | **proved**, as stated |

Build: `lake build HPC` succeeds. No `sorry` in `HPC/Plane/Enc2.lean`. `axioms.txt` regenerated:
629 lines (611 before, 18 new in the group for batch 131); `sorryAx` in **one line**,
`HPC.Plane.fugate_cor1`, unchanged. The previous `axioms.txt` is saved as
`doc/batches/audits/axioms-before-batch131.txt`. Per-batch audit:
`doc/batches/audits/axioms-batch131.{lean,txt}` (all 19 theorems of `Enc2.lean`, the three renamed
relative theorems, and `fugate_cor1`); every theorem except `fugate_cor1` shows
`[propext, Classical.choice, Quot.sound]`.

## Refutation candidates

* **`compl_closedBall_subset_component`** — holds. The four open half-planes
  `{x.1 > R+1}`, `{x.2 > R+1}`, `{x.2 < -(R+1)}`, `{x.1 < -(R+1)}` are products of intervals, hence
  preconnected, and all their points are at distance `≥ 1 > 2δ` from `M`, so each lies in
  `(graphSet (bdryGraph M δ))ᶜ`. With `T := max (R + 2) (gridR M δ + 1)`: the eastern one meets
  `Ioi (gridR M δ) ×ˢ univ` at `(T, 0)`; the northern one meets the eastern one at `(T, T)`; the
  southern one meets the eastern one at `(T, -T)`; the western one meets the northern one at
  `(-T, T)`. These meetings are points of sets already shown to be in the outer component, so
  `subset_component_of_far` applies in turn.
* **`exists_far_piece`** — holds with `≤`. On the ball, `infDist x M ≤ infDist p M + dist x p` and
  `d ≤ infDist x M`, `dist p x ≤ r = d/2`, so `infDist p M ≥ d - r = r`; on the range of the path,
  `infDist p M ≥ d ≥ r`.
* **`eastRay_subset_component`** — holds; the ray meets the half-plane at
  `(max (R + 1) (gridR M δ + 1), 0)`.

## Items

**1. Uniform membership.**
* `not_mem_graphSet_bdryGraph_of_far`: `graphSet ⊆ gridUnion ⊆ cthickening (2δ) M`
  (`graphSet_bdryGraph_subset`, `gridUnion_subset_cthickening`), and
  `x ∈ cthickening ε M ↔ infEDist x M ≤ ofReal ε` (`Metric.mem_cthickening_iff`) gives
  `infDist x M ≤ 2δ` by `ENNReal.toReal_mono`. This holds for every `M`, so
  **`hMne` is dropped** here and in `subset_component_of_far` (shape change).
* `subset_component_of_far`: `IsPreconnected.subset_connectedComponentIn` after re-basing the
  component at the meeting point (`connectedComponentIn_eq`).
* `eastRay`, `isPreconnected_eastRay` (image of `Ici` under a continuous map),
  `one_le_infDist_eastRay`, `eastRay_subset_component`, `compl_closedBall_subset_component`.
* Two helpers added: `one_le_infDist_of_far_coord` (if `M ⊆ ball 0 R` and `|p.1| ≥ R + 1` or
  `|p.2| ≥ R + 1`, then `1 ≤ infDist p M`; sup metric, `Metric.le_infDist`) and
  `pos_of_subset_ball` (`0 < R` when `M` is nonempty).

**2. Paths and their distance from `M`.**
* `joinedIn_compl_of_not_separates`: **Mathlib lemmas used for path-connectedness:**
  `IsOpen.isConnected_iff_isPathConnected` (the instance `LocPathConnectedSpace (ℝ × ℝ)` is found
  by instance search, no manual argument needed) and `IsPathConnected.joinedIn`. The path is
  `JoinedIn.somePath`, with `JoinedIn.somePath_mem`.
* `exists_pos_infDist_le_of_disjoint`: **Mathlib lemmas used for the positive gap:**
  `IsCompact.exists_isMinOn` applied to `continuous_infDist_pt M`, and
  `IsClosed.notMem_iff_infDist_pos` (the minimum is positive because `M` is closed and nonempty and
  the minimiser is not in `M`). Empty `P`: `d = 1`.
* `exists_far_piece`: `P := closedBall x (d/2) ∪ range γ`; preconnected by
  `IsPreconnected.union` at `x` (`Convex.isPreconnected` for the ball, `isPreconnected_range` for
  the path); the distance bound via `Metric.infDist_le_infDist_add_dist`.
* `exists_uniform_pieces`: `IsCompact.elim_finite_subcover` for the balls `ball x (r x)`,
  `x ∈ C`; `d := min' (insert 1 (t.image r))` (so `C = ∅` needs no separate case).

**3. `enclose`.** `exists_mesh_compl_subset` with `δ := min d 1 / 3` (so `2δ < 1` and `2δ < d`),
exactly as the skeleton's docstring; `enclose_holds` from it and `exists_enclosing_polygon`;
`planeFacts_holds := planeFacts_of_enclose enclose_holds`; `theorem7_1951`, `theorem6_1951`,
`theorem7_weak` by specialising the relative forms at `planeFacts_holds`, statements verbatim
from `Tree7Comp.lean` minus `(hPF : PlaneFacts)`.

**Other shape change.** `import HPC.Plane.Tree7Comp` is added to `Enc2.lean`: the relative
theorems live in `Tree7Comp.lean`, which is not imported by `Enc1` or `JanPoly`.

## Edits

1. `HPC/Plane/Tree7Comp.lean`: `theorem7_1951 → theorem7_1951_rel`,
   `theorem6_1951 → theorem6_1951_rel`, `theorem7_weak → theorem7_weak_rel`; statements and
   proofs unchanged (the internal references updated); each docstring gains "Relative form; the
   unconditional theorem is `HPC.Plane.…` in `Enc2.lean` (batch 131)". `HPCCensus.lean` and
   `HPCArchive.lean` contain no reference to them; `Axioms.lean` updated. **Decision recorded:**
   the internal `PlaneFacts.*` lemmas of `Tree6`, `Tree7`, `Tree7Comp`, `Tree7Cross` are left
   relative; `planeFacts_holds` instantiates them wherever needed.
2. `HPC/Plane/Tree67.lean`: module docstring gains "— discharged in batch 131: `planeFacts_holds`
   (`Enc2.lean`)". The structure is unchanged.
3. `HPC/Plane/Tree7.lean`: the comment on `treeLike_nonseparating` notes that `PlaneFacts` is now
   proved, so the question is unconditional; still open; not attempted.
4. `Axioms.lean`: new group "Enclosing polygon, part II; `PlaneFacts` discharged; Duke Theorems
   6–7 unconditional (batch 131)" with all 19 theorems of `Enc2.lean`; the Duke §3 group headers
   now read "relative forms", and the note of the first §3 group is replaced by "`PlaneFacts`
   proved in batch 131 (`planeFacts_holds`); the relative forms below are instantiated in
   `Enc2.lean`". The old `#print axioms` lines for the three theorems now name the `_rel` forms.
   `axioms.txt` regenerated.
5. `OPEN.md`: *Relative results* reduced to the commissioned single line. `OPEN.md` has no
   numbered item 2 (its only numbered item is `fugate_cor1`); the paragraph on
   `treeLike_nonseparating`, which sat in the *Relative results* section, is moved to a short
   section *Not attempted* and reworded: no longer relative to an interface.
6. `README.md`: the Duke paragraph states that Theorems 6 and 7 are proved outright (JCT for
   polygons, the enclosing polygon and polygonal Janiszewski all proved in the repository,
   batches 125–131); batch count 131.
7. `LEDGER.md`: no row mentions the interface as a caveat on Theorems 6–7; unchanged.
8. Housekeeping: `theorems-3-4-scheduling(36).md` moved from the root to `doc/notes/`. The upload
   `theorems-3-4-scheduling.md` (a strict superset of `doc/theorems-3-4-scheduling.md`, adding
   §§155–156) replaces `doc/theorems-3-4-scheduling.md`. The commission is filed under
   `doc/batches/`, the skeleton under `doc/batches/skeletons/`. Nothing is left at the root.

## Declarations that still take `(hPF : PlaneFacts)`

Complete list (obtained by scanning every theorem of the `HPC` library for a hypothesis of type
`PlaneFacts`; the structure projections `PlaneFacts.jct`, `.enclose`, `.janiszewski` are omitted):

* `HPC/Plane/Tree6.lean`: `PlaneFacts.split`, `PlaneFacts.local_side`, `PlaneFacts.sides`,
  `PlaneFacts.exists_theta_point`, `PlaneFacts.compl_polyInterior`, `compFamily_no_circular`;
* `HPC/Plane/Tree67.lean`: `PlaneFacts.polyInterior_eq` (the hypothesis is named `h` there);
* `HPC/Plane/Tree7.lean`: `PlaneFacts.polyInterior_regular`, `treeChain_of_cover`,
  `PlaneFacts.exists_gp_cover`, `PlaneFacts.crosscut`;
* `HPC/Plane/Tree7Cross.lean`: `PlaneFacts.isCompact_poly`, `PlaneFacts.crosscut'`;
* `HPC/Plane/Tree7Comp.lean`: `PlaneFacts.components_of_crosscuts`,
  `PlaneFacts.exists_crosscutFamily`, `PlaneFacts.connectedComponentIn_inter_eq`,
  `PlaneFacts.polyInterior_subset_of_subset`, `PlaneFacts.component_inter_eq_polyInterior`,
  `theorem7_1951_rel`, `theorem6_1951_rel`, `theorem7_weak_rel`.

21 declarations in all. Each is internal or a relative form; the three user-facing theorems have
unconditional counterparts in `Enc2.lean`.

## Not attempted

`fugate_cor1`, `treeLike_nonseparating`, as commissioned.
