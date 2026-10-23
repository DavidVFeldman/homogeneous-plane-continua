Commission read: COMMISSION-batch117.md (batch 117 — Bing 1951 (Duke) §3, Theorems 6 and 7: definitions, the plane-topology interface, the grid cover).

# Report, batch 117

**Outcome.** Two statements of the skeleton are refuted and corrected. One is a field of the
interface `PlaneFacts`: as commissioned the structure had no inhabitant, so every result stated
relative to it would have been vacuous. Every other item is proved. The skeleton is saved as
`HPC/Plane/Tree67.lean` (the uploaded original is in `doc/batches/skeletons/Tree67.lean`), and
`import HPC.Plane.Tree67` is the last line of `HPC.lean`. No `sorry` remains in the file. No existing
file was edited except `HPC.lean` (the import), `Axioms.lean` (new group) and `axioms.txt`. The two uploads were moved to their usual places: `doc/batches/COMMISSION-batch117.md` and `doc/batches/skeletons/Tree67.lean`.
Theorems 6 and 7 themselves, `theorem3_end` and `fugate_cor1` were not attempted.

## Refutations

1. **`PlaneFacts.janiszewski` is false as stated.** It is stated for *closed* `A`, `B`.
   `janiszewski_closed_false` proves the negation of the field. Take `A = [0, ∞) × {0}` and
   `B = (−∞, 0] × {0}`. Both are closed and `A ∩ B = {(0,0)}` is connected. Neither separates
   `(0, 1)` from `(0, −1)`: the union of the convex half-planes `y > 0`, `x < 0` (resp. `x > 0`) and
   `y < 0` is a connected set that avoids it. But `A ∪ B` is the `x`-axis, which separates them.
   Janiszewski's theorem holds for closed sets of `S²`. Closed unbounded sets of `ℝ²` are not
   closed in `S²` once `∞` is added, and the two rays meet at `∞`.
   **Correction:** the field now asks `IsCompact A → IsCompact B`. This is the plane form of the
   theorem, and it covers batch 118's use, where `A` and `B` are closures of bounded links. The
   commissioned structure is kept in a block comment next to the corrected one. `jct` and
   `enclose` are unchanged. I see nothing false in them, but the repository cannot check that the
   corrected interface is consistent: that would amount to proving it.
2. **`inter_gridSq_subset_notched` is false as stated** (`inter_gridSq_subset_notched_false`).
   Take `o = 0`, `ε = 1`, `η = 1/8`, `r = 1/4` and `M = {(0, 1/4)}`. The point is at sup-distance
   `≥ 1/4` from every vertex of the unit grid and lies in the closed unit square. It is in none of
   the three parts of the notched square: the open square and the horizontal strip need
   `0 < x`, and the vertical strip needs `1/4 < y`, because the strips are open and stop at exactly
   distance `r`. **Correction:** `hfar` now reads `r < dist p v`. `exists_notched_cover` supplies
   this, since `r ≤ r₀/2 < r₀`. The commissioned statement is kept in a block comment.

## Items

1. **Definitions — checked, unchanged in meaning.** `polygonOf`, `IsSimpleClosedPolygon`,
   `polyInterior`, `SeparatesPlane`, `SeparatesPts`, `IsCoherent`, `IsCircularChain`,
   `IsTreeChain` and `IsTreeLike` read as on p. 653.
   * `IsCircularChain`: more than two links, with `d i ∩ d j ≠ ∅ ↔ |i − j| ≤ 1 ∨ {i, j} = {0, m−1}`.
     Taking `i = j` forces the links to be nonempty, as in Bing. The coercion `(i : ℤ)` is
     `((i.val : ℕ) : ℤ)` (checked by `rfl`).
   * `IsTreeChain` quantifies over every `G' ⊆ G`, including `G` itself.
   * In `IsSimpleClosedPolygon`, the set `{v i, v j, v (i+1)}` has one vertex too many for adjacent
     edges. This is harmless: the intersection of two segments is convex and contains the common
     vertex, so it is a subset of that three-point set only if it is that vertex alone.
   * Two edits to the text, neither changing meaning: the unused binder names `hn`, `hm` in the
     existentials became `_` (linter), and `open scoped Classical` was added, because
     `IsCoherent`'s `G \ G'` needs `DecidableEq (Set Pt)` and the skeleton did not elaborate
     without it.
2. **`PlaneFacts.polyInterior_eq` — proved.** For a point of `U` its component in `Jᶜ` is `U`, and
   for a point of `V` it is `V` (`connectedComponentIn_eq_of_split`). Hence `polyInterior J = U`
   (`polyInterior_eq_of_split`), which uses only that `U` is bounded and `V` is not. Then
   `(J ∪ U)ᶜ = V`. Only `frontier U = J` from `jct` is used; `frontier V = J` is not needed here.
   Adding `J ⊆ closure U` to `jct` would be redundant, since it follows from `frontier U = J`. I
   would not change `jct`'s formulation.
3. **The grid — proved.**
   * `interior_eq_empty_of_noSeparating`: a ball inside `M` contains a sphere (a square boundary in
     the sup metric). The sphere is a continuum (`isConnected_sphere`, `rank ℝ (ℝ × ℝ) = 2`), and its
     complement splits into the open ball and the open exterior. The skeleton's hypothesis `hM`
     was not needed and was dropped.
   * `exists_grid_offset`: proved by Baire's theorem instead of the commissioned finite union. The
     bad offsets for vertex `(a, b)` form a translate of `M`, which is closed and nowhere dense,
     and countably many such sets cannot cover the plane. `hb` and `hε` were not needed and were
     dropped.
   * `finite_gridSq_meeting`: the indices lie in `[−N, N]²` with
     `N = ⌈(R + |o₁| + |o₂|)/ε⌉ + 1`.
   * `isOpen_notched`.
   * `diam_notched_le`: the set lies in the closed box of side `ε + 2η` (`notched_subset_box`).
   * `inter_gridSq_subset_notched` (corrected form): a point on a side is at distance `> r` from
     that side's two corners, so it is in the strip. `hε`, `hr` and `hrε` were not needed and were
     dropped.
   * `notched_no_triple`: `notched_bound` (`2η < ε`) shows that meeting squares have indices at
     most one apart in each coordinate. `notched_diag1` and `notched_diag2` (`η < r`) show that
     diagonal neighbours are disjoint. Together these give `notched_adj`. Three distinct indices
     that pairwise share a side are then impossible (`omega`).
4. **`exists_notched_cover` — proved.** The constants are as follows:
   * grid side `δ = ε/2`;
   * offset `o` from item 3;
   * `r₀ > 0`, the minimum over `M` of the distance to the closed vertex set
     (`isClosed_gridVertices`, `exists_far`);
   * `r = min (r₀/2) (δ/4)` and `η = r/2`;
   * `D` = the notched squares whose indices meet `M`.

   Then `diam ≤ δ + 2η ≤ 5ε/8 < ε`. Each `p ∈ M` lies in the square with index
   `(⌊(p₁ − o₁)/δ⌋, ⌊(p₂ − o₂)/δ⌋)`. Distinct sets in `D` have distinct indices. The skeleton's
   `hb` follows from compactness and was dropped.
5. **Two lemmas — proved.**
   * `isOpen_connectedComponentIn_of_isOpen` is `IsOpen.connectedComponentIn`, since `ℝ × ℝ` is
     locally connected.
   * `isCoherent_of_minimal_cover`: minimality (`hmin'`) is not needed. It suffices that every
     member is open and meets the connected set `M`. A split of `G` with no intersections across
     would split `M` into two disjoint nonempty relatively open parts. `hmin'` was dropped, and the
     name was kept for batch 118.

## Audit

* `Axioms.lean` has a new group, "Bing 1951 (Duke) §3, Theorems 6–7 — relative to `PlaneFacts`
  (batch 117)", with 11 theorems and the 2 refutations.
* `doc/batches/audits/axioms-batch117.txt` is `#print axioms` for all 25 theorems of `HPC/Plane/Tree67.lean`, from the script `axioms-batch117.lean`. Every one shows exactly `[propext, Classical.choice, Quot.sound]`.
* `doc/batches/audits/axioms-before-batch117.txt` is the previous `axioms.txt`.
* `axioms.txt` is regenerated (362 lines, up from 349), and `sorryAx` still appears in exactly two lines: `theorem3_end`
  and `fugate_cor1`.

None of the batch-117 theorems takes `PlaneFacts` as a hypothesis except `polyInterior_eq`: the grid
cover is unconditional.

## Next

Batch 118 as planned, now with the compact form of `janiszewski`. Its closed sets are closures of
links, which are bounded, so the correction costs nothing there.
