Commission read: COMMISSION-batch126.md (batch 126 — `jct` part II: the two sides are connected; the field discharged).

# Report, batch 126

**Outcome.** No refutation. Every item is **proved**; every statement of the skeleton is kept
verbatim, and the one `def` to design (`sideNbhd`) is defined below.

| item | verdict |
|---|---|
| 1. local structure at an edge (`polygon_local_chord`, `halfDisk`, `halfDisk_convex`, `halfDisk_nonempty`, `ball_diff_chord`) | **proved**, as stated |
| 2. the flip across every edge (`parity_flip_edge`) | **proved**, as stated; the main line uses the two generic-point flips `parity_flip_at`, `parity_flip_vertical` (new) |
| 3. the vertex (`vertex_two_pieces`) | **proved**, as stated (the proof works at every point of `Γ`) |
| 4. first hit and neighbourhood (`exists_first_hit`, `exists_segment_to_boundary`, `sideNbhd`, `sideNbhd_subset`, `sideNbhd_isConnected`, `sideNbhd_near`, `exists_segment_to_sideNbhd`) | **proved**; `sideNbhd` designed (below) |
| 5. the theorem (`isConnected_parity_set`, `frontier_parity_set`, `jct_polygon`, `planeFacts_of_enclose_janiszewski`) | **proved**; `jct_polygon` is the field `PlaneFacts.jct` verbatim and `⟨jct_polygon, henc, hjan⟩ : PlaneFacts` typechecks as written |

Build: `lake build HPC` succeeds. No new `sorry`. `axioms.txt` regenerated (517 lines, 19 new); `sorryAx` occurs in
**one line**, `HPC.Plane.fugate_cor1` (unchanged). Every other line shows
`[propext, Classical.choice, Quot.sound]` or a subset. Per-batch audit:
`doc/batches/audits/axioms-batch126.{lean,txt}` (all 42 theorems of `HPC/Plane/Jct2.lean`, plus
`fugate_cor1`); the previous `axioms.txt` is saved as
`doc/batches/audits/axioms-before-batch126.txt`.

Files:

* `HPC/Plane/Jct2.lean` — new: the commissioned skeleton, every `sorry` replaced by a proof, plus
  the auxiliary statements listed below;
* edited as allowed: `HPC.lean` (`import HPC.Plane.Jct2` at the end), `Axioms.lean` (group
  "Jordan curve theorem for polygons (batch 126)"), `axioms.txt`, `OPEN.md` (*Relative results*),
  `README.md` (§3 wording, batch count 126, Bing 1948 line).

Refutation candidates named in the commission, checked:

* *the shape of `halfDisk` with the sup-metric ball*: harmless. `halfDisk p d ρ s` is the sup-ball
  (an open square) intersected with an open half-plane, hence convex (`halfDisk_convex`), and
  nonempty for `d ≠ 0` (`halfDisk_nonempty`, the point `p ± τ (d.2, −d.1)` with
  `τ = ρ / (2 (|d.1| + |d.2| + 1))`). Nothing uses roundness of the ball.
* *`ball_diff_chord`'s radius quantification* (`∃ ρ, ∀ ρ' ≤ ρ`): true as stated. `ρ` is the minimum
  of the chord radius of `polygon_local_chord` and `min s₀ (1 − s₀) · ‖d‖`, where `p = a + s₀ d`
  (`0 < s₀ < 1` since `p` is not a vertex); below it a point of the line through the edge lies on
  the edge, so the ball minus `Γ` is exactly the two half-disks, for every smaller radius.
* *`exists_segment_to_sideNbhd`'s reliance on how `sideNbhd` is cut*: with the definition adopted
  (all preconnected local pieces) there is no cutting; the end of the first-hit segment inside the
  connected local piece at the hit point lies in `sideNbhd` directly.

## 1–3. Local structure, the flips, the vertex

**Actually used by the main line: `mem_closure_parity_set`.** *Every point of `Γ` lies in the
closure of both parity classes.* For a point `w` of edge `i`:

* non-horizontal edge: by `exists_near_on_segment` there is a point `p` of the edge arbitrarily near
  `w` whose height is no vertex height (the heights along the edge are an affine function of the
  parameter with nonzero slope, and finitely many values are to be avoided); at `p`,
  `parity_flip_at` (the argument of `exists_parity_flip`, at a given point) gives
  `p ∓ t (1, 0)` off `Γ` with different parities, for all small `t`;
* horizontal edge: likewise a point `p` of the edge arbitrarily near `w` whose abscissa is no vertex
  abscissa — so `p` is not a vertex — and `parity_flip_vertical` gives `p ± t (0, 1)` off `Γ` with
  different parities.

`parity_flip_vertical` is the horizontal case sketched in REPORT-batch125 §1: by `crossesEast_jump`
at `p` for each edge `j ≠ i` (`p` lies on no other edge, `not_mem_polyEdge_of_ne`), the indicator
of edge `j` is the same at `p + t (0,1)` as at `p`, and changes by
`vJump p (v j) + vJump p (v (j+1))` at `p − t (0,1)`; edge `i` itself is never counted. Summing,
`parity (p + t e₂) + parity (p − t e₂) = Σ_{j ≠ i} J_j = (Σ_j J_j) + J_i = 0 + 1`, since the jumps
telescope (`sum_vJump_telescope`) and `J_i = vJump p a + vJump p b = 1` (both ends at the height
of `p`, exactly one to its right). The lemma the commission asked to be stated is therefore
`crossesEast_jump` itself, applied at a point lying on exactly one edge, to the *other* edges.

From `mem_closure_parity_set`, `local_side_of_split` (batch 118, with
`Γᶜ = S_e ∪ S_{e+1}`, `compl_eq_union_parity_sets`, `disjoint_parity_sets`) gives
**`local_piece`**: at every `w ∈ Γ`, for all small `r`, `S_e ∩ ball w r` is nonempty and connected.
This replaces the half-disk/vertex-piece bookkeeping of the design: vertices need no separate
treatment.

**Items 1–3 as stated** are proved as well, but are not needed by the main line:

* `polygon_local_chord`: `ρ` such that the ball misses the (closed) union of the other edges; the
  chord parametrisation from `segment_eq_image'`.
* `ball_diff_chord`: above.
* `parity_flip_edge`: the half-disks lie in `Γᶜ` (points of the edge have cross product `0`), are
  convex, so each has constant parity; a pair of points of different parity, one in each, comes
  from `parity_flip_vertical` at `p` (horizontal edge: `p ± t (0,1)`, cross product `∓ t d.1`) or
  from `parity_flip_at` at a generic point `q` of the edge within `ρ/2` of `p` (non-horizontal:
  `q ± t (1,0)`, cross product `± t d.2`).
* `vertex_two_pieces`: `polygon_local_rays` and `ball_diff_rays` give `ball (v i) ρ \ Γ = Q₁ ∪ Q₂`
  with `Q₁`, `Q₂` preconnected in `Γᶜ`; by `mem_closure_parity_set` the ball contains points of both
  parities, which cannot lie in one piece (`parity_eq_of_isPreconnected`); so one piece is even and
  the other odd. (Nothing in the proof uses that `v i` is a vertex.)

## 4. First hit and the neighbourhood

* `exists_first_hit`: `T = {t ∈ [0,1] | x + t (y − x) ∈ Γ}` (with `y = v 0`) is compact and
  nonempty, `t₀ = sInf T ∈ T`, `t₀ > 0`; `p = x + t₀ (y − x)`. `segment_subset_of_first_hit`: the
  segment from `x` to `x + t (p − x)`, `t < 1`, lies in `Γᶜ`. `exists_segment_to_boundary` follows
  (no simplicity needed, as in the skeleton).

**The definition of `sideNbhd` adopted:**

```
def sideNbhd (v : Fin n → Pt) (e : ZMod 2) : Set Pt :=
  ⋃ (w ∈ polygonOf v) (r : ℝ) (_ : 0 < r)
    (_ : IsPreconnected ({x | x ∉ polygonOf v ∧ parity v x = e} ∩ ball w r)),
    {x | x ∉ polygonOf v ∧ parity v x = e} ∩ ball w r
```

the union of *all* preconnected local pieces of the parity class `S_e` at points of `Γ`.

* `sideNbhd_subset`: immediate.
* `sideNbhd_isConnected`: write `sideNbhd = ⋃_{w ∈ Γ} P w`, `P w` the union of the preconnected
  pieces at `w`. `P w` is preconnected: any two pieces at `w` contain `S_e ∩ ball w (min r₁ r₂)`,
  nonempty since `w ∈ closure S_e` (`isPreconnected_of_forall_pair`). For `w'` within the
  `local_piece` radius `r₀ w` of `w`, `P w ∩ P w' ≠ ∅` (a point of `S_e` near `w'` in both base
  pieces). `isPreconnected_biUnion_of_local_meet` (batch 118) over the preconnected `Γ`
  (`isPreconnected_polygonOf`: consecutive edges share a vertex, `IsPreconnected.iUnion_of_chain`)
  concludes. Nonempty since `n ≥ 3`.
* `sideNbhd_near`: the piece at `p` of radius `min ρ (r₀ p)`.
* `exists_segment_to_sideNbhd`: first hit `p`, a point `z = x + t (p − x)` inside `ball p (r₀ p)`
  (`exists_param_near_end`); `z ∈ S_{parity x}` by constancy along the segment, and the piece at
  `p` of radius `r₀ p` is connected, so `z ∈ sideNbhd`.

No finite cover of the edges by chord balls and no chaining of half-disks along the cycle is
needed: the local connectedness is supplied pointwise by `local_side_of_split`, and the chaining by
the connectedness of `Γ`.

## 5. The theorem

* `isConnected_parity_set`: `isPreconnected_of_forall` from a base point of `sideNbhd v e`: each
  `y ∈ S_e` lies in `sideNbhd v e ∪ [y, z]` (preconnected, `⊆ S_e`).
* `frontier_parity_set`: `S_e` open, so `frontier S_e = closure S_e \ S_e`; `⊆ Γ` since
  `closure S_e ⊆ S_{e+1}ᶜ`; `⊇` by `mem_closure_parity_set`.
* `jct_polygon`: `U = S_1`, `V = S_0`; open (`isOpen_parity_set`), `Jᶜ = U ∪ V`, disjoint, connected,
  `U` bounded and `V` unbounded (`polygon_separates`), frontiers `= J`.
* `planeFacts_of_enclose_janiszewski := ⟨jct_polygon, henc, hjan⟩`, verbatim.

## Notes for part III (polygonal Janiszewski, batches 127–129)

* The parity machinery needs **no general position and no simplicity** for local constancy
  (`parity_eventually_eq`, `parity_eq_of_isPreconnected`) and for `0` far away; simplicity enters
  only through the flips (`parity_flip_at`, `parity_flip_vertical`, both use
  `not_mem_polyEdge_of_ne`) and through `polygon_local_rays`.
* The flips are proved at *generic* points only (a point of a non-horizontal edge at a height that
  is no vertex height; any non-vertex point of a horizontal edge). For a mod-2 cycle argument with
  several polygons, the same proof gives the flip of the parity of one closed polygon `v` across its
  edge `i` at any point lying on no other edge of `v` and at no vertex height: the hypotheses used
  are exactly `p ∈ polyEdge v i`, `∀ j ≠ i, p ∉ polyEdge v j`, and `∀ k, (v k).2 ≠ p.2`. Those are
  the natural hypotheses for a sum of polygons (parities add mod 2).
* `parity` is additive under formal sums of closed polygons only if the sum is taken over edges;
  `parity_eq_sum` gives the edge-sum form, `crossesEast_jump` the per-edge local rule — both are
  edge-local and do not see the polygon structure except in `sum_vJump_telescope` (which only needs
  that each vertex is an end of an even number of edges, i.e. a mod-2 cycle). That is the form to
  generalise for mod-2 1-cycles.
* `mem_closure_parity_set` and `local_side_of_split` give, for any simple closed polygon, the
  local two-sidedness at every point; `sides_of_split` (batch 118) is now unconditional for simple
  closed polygons (its hypotheses `hfU`, `hfV` are `mem_closure_parity_set`).

## Deliverables / not attempted

Items 1–5 above; `doc/batches/audits/axioms-batch126.txt`; `axioms.txt` regenerated (`sorryAx` in one
line). Housekeeping: `COMMISSION-batch125.md` → `doc/batches/`, `Jct1.lean` →
`doc/batches/skeletons/`, `axioms-batch125.txt` → `doc/batches/audits/` (identical copy already
there; the root copy removed); the notes `theorems-3-4-scheduling(31).md` and this batch's
`theorems-3-4-scheduling(32).md` (a superset of (31)) → `doc/theorems-3-4-scheduling.md`,
replacing the older copy; this batch's uploads `COMMISSION-batch126.md` → `doc/batches/`,
`Jct2.lean` → `doc/batches/skeletons/`.

Not attempted (as commissioned): `enclose`, `janiszewski`, `fugate_cor1`,
`treeLike_nonseparating`.
