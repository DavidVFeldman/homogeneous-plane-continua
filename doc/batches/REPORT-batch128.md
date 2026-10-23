Commission read: COMMISSION-batch128.md (batch 128 — polygonal Janiszewski, part II: a separating graph contains an odd cycle; `JaniszewskiPoly` proved).

# Report, batch 128

**Outcome.** Nothing refuted; every item is **proved**. `JaniszewskiPoly` is proved
(`HPC.Plane.janiszewskiPoly_holds`), via `separatingGraphHasOddCycle`. Nothing is open.

| item | verdict |
|---|---|
| refutation candidates (`edge_local`'s `∀ ρ' ≤ ρ`; `oddSet` via `⊆ C`; `gFun_eq_across_edge` at non-generic points) | **none refuted** (below) |
| 1. local structure at an edge (`segDir`, `edge_local`, `sideRadius` — design —, `sideStrip`, `sideStrip_subset_compl`, `sideStrip_nonempty`, `sideStrip_isPreconnected`, `subset_or_disjoint_component`) | **proved**; `edge_local` as stated; `sideStrip_subset_compl` without its two unused hypotheses |
| 2. the odd set (`oddSet`, `oddSet_subset`, the sector lemma, `even_deg_oddSet`, `isCycle_oddSet`) | **proved**; the sector lemma in the circle form `vertex_arcs` (below) |
| 3. the parity step (`gFun`, `gFun_eq_across_edge`, `gFun_locallyConstant`, `gFun_const`, `cycParity_oddSet_ne`, `separatingGraphHasOddCycle`, `janiszewskiPoly_holds`) | **proved**, all as stated (`gFun` under `open Classical in`) |

Build: `lake build HPC` succeeds. No `sorry` in `HPC/Plane/Cyc2.lean` or `HPC/Plane/Cyc2Circle.lean`.
`axioms.txt` regenerated (549 lines, 18 new); `sorryAx` occurs in **one line**, `HPC.Plane.fugate_cor1` (unchanged).
Per-batch audit: `doc/batches/audits/axioms-batch128.{lean,txt}` (all 63 theorems of the two new
files, plus `fugate_cor1`; every theorem of the two files shows exactly
`[propext, Classical.choice, Quot.sound]`); the previous `axioms.txt` is saved as
`doc/batches/audits/axioms-before-batch128.txt`.

Files:

* `HPC/Plane/Cyc2.lean` — new (993 lines): the skeleton with every `sorry` replaced by a proof,
  the sector lemma in the form used, and the auxiliary statements listed below;
* `HPC/Plane/Cyc2Circle.lean` — new (215 lines): two self-contained tools, the jump formula for a
  `ZMod 2`-valued function on an interval and the points of a Euclidean circle (below);
* edited as allowed: `HPC.lean` (`import HPC.Plane.Cyc2` at the end), `Axioms.lean` (group
  "Polygonal Janiszewski (batch 128)"), `axioms.txt`, `README.md` (batch count 128), `OPEN.md`
  (*Relative results*: `JaniszewskiPoly` proved, the field change is batch 129);
* housekeeping: the commission is `doc/batches/COMMISSION-batch128.md`, the skeleton
  `doc/batches/skeletons/Cyc2.lean`; `theorems-3-4-scheduling(34).md` contains all of
  `doc/theorems-3-4-scheduling.md` (a strict extension: §153 added) and replaces it. Nothing is
  left at the root.

## Refutations first: none

* **`edge_local`'s `∀ ρ' ≤ ρ` form** holds: `ρ = min (sideRadius G e p) (min s₀ (1 − s₀) · ‖d‖)`
  where `p = e.1 + s₀ d`. The first bound keeps the ball off the other segments and the ends of
  `e`; the second makes every point of the line of `e` inside the ball a point of `e`. Both
  survive shrinking.
* **`oddSet` via `⊆ C` of the whole strip** is sound because the strip *is* preconnected
  (`sideStrip_isPreconnected`) and lies in `(graphSet G)ᶜ`, so it lies in `C` or misses it
  (`subset_or_disjoint_component`). Consequently a point of a strip is in `C` iff the whole strip
  is (`mem_C_iff_of_mem_sideStrip`); this is the only way the definition is used.
* **`gFun_eq_across_edge` at points where `cycParity_flip`'s hypotheses fail** needs no generic
  point at `p`: the flip is used once per edge, at a generic point `p'` of `e` (see item 3), and
  transported to `p` through the side strips, on which the parity of the odd set is constant
  (`cycParity_eq_on_sideStrip`).

## Other changes of shape

* `sideStrip_subset_compl (G e s)`: the hypotheses `hG : IsProper G` and `he : e ∈ G` of the
  skeleton were unused and are dropped (`G`, `e` explicit).
* `gFun` is stated under `open Classical in`: `z ∈ connectedComponentIn (graphSet G)ᶜ x` is not
  decidable, and the skeleton's `gFun` does not compile without it. The same for the auxiliary
  `side_jump`.
* `vertex_sectors_placeholder` is replaced by `vertex_arcs` (item 2).

## Item 1: local structure at an edge

* **`sideRadius G e p := infDist p (otherSegs G e) / 2`**, with
  `otherSegs G e := (⋃ t ∈ G.erase e, segSet t) ∪ {e.1, e.2}` — a nonempty closed set not
  containing any non-vertex point of `e` (`not_mem_otherSegs`, from properness). Facts:
  `sideRadius_pos` at non-vertex points of `e`; `sideRadius_lipschitz`
  (`sideRadius p ≤ sideRadius q + dist p q / 2`); `mem_segSet_of_mem_ball_sideRadius` (a point of
  the graph in `ball p (sideRadius G e p)` lies on `e` and is not an end of `e`).
* `halfDisk_subset_compl`: a half-disk of radius `≤ sideRadius` at a point of `e` misses the
  graph (its points off the line of `e` are not on `e`, and the ball meets the graph only on `e`).
* `sideStrip_isPreconnected`: the non-vertex points of `e` are exactly `openSegment ℝ e.1 e.2`
  (`nonvertex_eq_openSegment`), which is preconnected; the half-disks are convex; and for `p'`
  within `sideRadius p / 2` of `p` on the open segment, the half-disks of `p` and `p'` on the same
  side share a point (a point of the half-disk of radius `sideRadius p / 4` at `p` lies in the
  half-disk at `p'`, since `sideRadius p' > 3/4 · sideRadius p` and the side of a point is the same
  for two centres on the line of `e`, `mem_halfDisk_of_shift`). Then
  `isPreconnected_biUnion_of_local_meet` (batch 118) applies over the open segment.

## Item 2: the odd set and its cycle property — the sector lemma as proved

**Angle machinery: `Complex.arg` and `Real.Angle`**, on a Euclidean circle (although `Pt` carries
the sup metric). In `Cyc2Circle`: `circPt w ρ θ := (w.1 + ρ cos θ, w.2 + ρ sin θ)`,
`eNorm u := √(u.1² + u.2²)`, `dirAngle u := Complex.arg ⟨u.1, u.2⟩`.

* `circPt_mem_segment_iff`: for `w ≠ v` and `0 < ρ < eNorm (v − w)`, the circle point at `θ` lies on
  `[w, v]` iff `eNorm (v − w) · (cos θ, sin θ) = v − w`;
* `exists_angle`: `dirAngle u` is such an angle (`Complex.cos_arg`, `Complex.sin_arg`);
* `angle_unique`: two such angles differ by `2πk` (`Real.Angle.cos_sin_inj`).

**The sector lemma, as proved** (`vertex_arcs`). For `w` an end of some edge of the proper graph
`G` there are `ρ > 0`, `α : ℝ` and `θ : Seg → ℝ` such that

1. `circPt w ρ α ∉ graphSet G`;
2. `θ e ∈ (α, α + 2π)` for every edge `e` at `w`;
3. `θ` is injective on the edges at `w`;
4. every `t ∈ (α, α + 2π)` with `circPt w ρ t ∈ graphSet G` is `θ e` for an edge `e` at `w`;
5. for every edge `e` at `w` there is a side `s` with `circPt w ρ t ∈ sideStrip G e s` for `t`
   just below `θ e` and `circPt w ρ t ∈ sideStrip G e (!s)` for `t` just above `θ e`.

Proof: `ρ` is below the distance from `w` to the segments not at `w` (`exists_vertex_radius`) and
below the lengths of the edges at `w`; `α ∈ (0, 1)` avoids the finitely many `dirAngle`s;
`θ e := toIocMod 2π α (dirAngle (othEnd w e − w))`. The crossing point `circPt w ρ (θ e)` is at
Euclidean distance `ρ` from `w`, so it is neither end of `e`, hence not a vertex, hence on no other
edge — this gives 3 and lets the side strips at that point be used. For 5, with
`u = othEnd w e − w = eNorm u · (cos θ e, sin θ e)`, the cross product of `circPt w ρ t − circPt w ρ (θ e)`
with `u` is `ρ · eNorm u · sin (θ e − t)` (`circ_cross_formula`), positive just below `θ e` and
negative just above; `segDir e = ±u` decides which side is `true`. The arcs between consecutive
crossings play the part of the sectors; they are never named.

**Counting** (`even_deg_oddSet`). `F t := [circPt w ρ t ∈ C]` is locally constant at every `t`
of `[α, α + 2π]` other than the crossing angles (`memC_eventually`: `C` and
`(graphSet G)ᶜ \ C` are open), and at `θ e` it is `c` just below and `c + [e ∈ oddSet]` just above
(5, `mem_C_iff_of_mem_sideStrip`, `side_jump`). The jump formula `zmod2_jump_sum`
(`Cyc2Circle`, by induction on the number of jumps, cutting at the smallest) gives
`F (α + 2π) = F α + ∑_{e at w} [e ∈ oddSet]`; `F (α + 2π) = F α` by periodicity, so
`deg (oddSet G x) w` is even. Degree one needs no separate case (the sum is a single term, forced
to be `0`). A point `w` that is an end of no edge has degree `0`. `isCycle_oddSet` follows with
`IsProper.subset`.

## Item 3: the parity step, path-free

* `cycParity_eq_on_sideStrip`: `cycParity (oddSet G x)` is constant on each side strip (strip
  preconnected, in `(graphSet G)ᶜ ⊆ (graphSet (oddSet G x))ᶜ`, `isCycle_oddSet`).
* `cycParity_sideStrip_ne_iff`: for `z₁` in the `true` strip and `z₂` in the `false` strip of `e`,
  `cycParity (oddSet G x) z₁ ≠ cycParity (oddSet G x) z₂ ↔ e ∈ oddSet G x`. If `e ∉ oddSet`, the
  midpoint of `e` is off `graphSet (oddSet G x)` and a ball about it, containing a half-disk on each
  side, has constant parity. If `e ∈ oddSet`, `cycParity_flip` is applied at one point `p'` of `e`:
  the midpoint if `e` is horizontal, otherwise a point of `e` at a height different from all
  vertices of the odd set (`exists_near_on_segment`), which is then automatically not an end of `e`.
  The two flip points, within `min (edge_local radius) (sideRadius)` of `p'`, are off `graphSet G`
  (near `p'` the graph is `e ⊆ graphSet (oddSet G x)`), so each lies in a strip; equal strips would
  give equal parities.
* `gFun_eq_of_mem_sideStrip`: `gFun` takes one value on the union of the two strips of an edge
  (both summands flip iff `e ∈ oddSet`); `gFun_eq_across_edge` follows with `edge_local`.
* `gFun_const`: on `S := (vertices G)ᶜ`, which is preconnected
  (`Set.Countable.isConnected_compl_of_one_lt_rank`, with `1 < Module.rank ℝ (ℝ × ℝ)` from
  `rank_prod'`), the relation "`gFun` off the graph near `a` equals `gFun` off the graph near `b`"
  is closed under `IsPreconnected.induction₂'`: it holds locally (`gFun_locallyConstant` off the
  graph, `gFun_eq_across_edge` at non-vertex points of the graph) and is transitive because every
  point of `S` has points off the graph arbitrarily close (a half-disk, from `edge_local`).
* `cycParity_oddSet_ne`: `gFun x = 1 + cycParity Z x`, `gFun y = 0 + cycParity Z y`.
* `separatingGraphHasOddCycle := ⟨oddSet G x, oddSet_subset, isCycle_oddSet, cycParity_oddSet_ne⟩`;
  `janiszewskiPoly_holds := janiszewskiPoly_of_oddCycle separatingGraphHasOddCycle`, as in the
  skeleton.

## Auxiliary statements added

`HPC/Plane/Cyc2Circle.lean`: `zmod2_const_of_loc`, `zmod2_jump_sum`, `circPt`, `eNorm`,
`eNorm_sq`, `eNorm_pos`, `continuous_circPt`, `circPt_add_two_pi`, `circPt_add_int_mul_two_pi`,
`dist_circPt_le`, `circPt_mem_segment_iff`, `dirAngle`, `dirAngle_mem_Ioc`, `exists_angle`,
`angle_unique`, `eq_of_two_pi_mul`.

`HPC/Plane/Cyc2.lean`: `segDir_ne_zero`, `not_mem_other_seg`, `not_mem_vertices_of_ne_ends`,
`vertices_mono`, `vertices_subset_graphSet`, `midpoint_mem_segSet`, `midpoint_ne_ends`,
`midpoint_not_mem_vertices`, `otherSegs` (+ `isClosed_otherSegs`, `otherSegs_nonempty`,
`not_mem_otherSegs`), `sideRadius_pos`, `sideRadius_lipschitz`,
`mem_segSet_of_mem_ball_sideRadius`, `halfDisk_subset_sideStrip`, `halfDisk_subset_compl`,
`nonvertex_eq_openSegment`, `mem_halfDisk_of_shift`, `memC_eventually`,
`mem_C_iff_of_mem_sideStrip`, `mem_oddSet`, `side_jump`, `othEnd` (+ `segSet_eq_othEnd`,
`ne_othEnd`, `segDir_eq_of_eq`, `segDir_eq_of_ne`), `exists_pos_lt_finset`,
`int_eq_zero_of_two_pi_mul`, `eNorm_circPt_sub`, `circ_cross_formula`, `exists_vertex_radius`,
`vertex_arcs`, `cycParity_eq_on_sideStrip`, `cycParity_sideStrip_ne_iff`,
`zmod2_add_eq_add_of_iff`, `gFun_eq_of_mem_sideStrip`.

## For batch 129 (the field change)

* **The form of "finite union of segments".** `JaniszewskiPoly` applies directly to sets of the
  form `graphSet S` with `S : Finset Seg` and `∀ s ∈ S, s.1 ≠ s.2`; no properness is needed (the
  subdivision inside `janiszewskiPoly_of_oddCycle` takes care of overlaps and crossings). The
  hypothesis on `A ∩ B` is `IsConnected (graphSet SA ∩ graphSet SB) ∨ graphSet SA ∩ graphSet SB = ∅`
  and the separation is `SeparatesPts`, exactly as in the field.
* **Degenerate segments.** A degenerate segment `(a, a)` whose point lies on another segment of the
  family can be dropped without changing `graphSet`. A genuinely isolated point cannot be written
  with nondegenerate segments, and `JaniszewskiPoly` as proved does not cover it; if the call site
  in batch 129 can produce isolated points, either exclude them in the polygonal field or prove
  that adding finitely many points to `A`, `B` changes neither the hypotheses' use nor the
  conclusion (this was not attempted here). "Doubling" a degenerate segment does not help: it is
  still degenerate.
* **Tools from this batch that may help with `crosscut'` and `exists_theta_point`.** `edge_local`
  and the side strips give, at a non-vertex point of an edge of a proper graph, the two local sides
  and their membership in components; `gFun_const`'s argument shows how to pass a locally constant
  function across the edges of a graph using only that the plane minus finitely many points is
  connected.

Not attempted, as commissioned: batch 129, `enclose`, `fugate_cor1`, `treeLike_nonseparating`.
