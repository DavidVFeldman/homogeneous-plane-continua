Commission read: COMMISSION-batch129.md (batch 129 — polygonal Janiszewski, part III: polygonal sets, the field change, the two uses; `PlaneFacts` down to one field).

# Report, batch 129

**Outcome.** Nothing refuted; every item and every edit is **proved**. The field `janiszewski` of
`PlaneFacts` now asks polygonal sets and is proved (`HPC.Plane.janiszewski_polygonal`);
`HPC.Plane.planeFacts_of_enclose : (enclose) → PlaneFacts` typechecks as
`⟨jct_polygon, henc, janiszewski_polygonal⟩`. **The interface has one undischarged field,
`enclose`.** Nothing is open.

| item | verdict |
|---|---|
| refutation candidates (`separatesPts_insert_iff` as stated; the reduction in `janiszewski_polygonal`; `isPolygonal_frontier_inter_closure`) | **none refuted** (below) |
| 1. polygonal sets | **proved** (all as stated; `IsPolygonal` moved to `HPC/Plane/Polygonal.lean`) |
| 2. isolated points, `janiszewski_polygonal` | **proved**, as stated, no extra hypothesis |
| 3. `polyInterior_local_halfDisk` | **proved**, as stated |
| 4. `isPolygonal_segment_inter_polygon`, `exists_open_pieces`, `isPolygonal_frontier_inter_closure` | **proved**, as stated; the last in a general form that needs no Jordan curve theorem |
| edit 1: the field; `planeFacts_of_enclose` | **done**; `planeFacts_of_enclose_janiszewski` kept, with the polygonal `hjan` |
| edit 2: `crosscut'` | **done** (statement unchanged) |
| edit 3: `exists_theta_point` | **done**, with `A := Γ₁ ∩ closure (U ∩ h₁ ∩ h₂)` (one gap in the commissioned argument, below) |
| edit 4: `compFamily_no_circular`, `treeChain_of_cover`, `theorem7_1951`, `theorem6_1951` | **done**; also `theorem7_weak` (forced, below) |
| edit 5: audit, `OPEN.md`, `README.md` | **done** |

Build: `lake build HPC` succeeds. No `sorry` in `HPC/Plane/Polygonal.lean`,
`HPC/Plane/PolygonalPoly.lean` or `HPC/Plane/JanPoly.lean`, nor in the edited proofs.
`axioms.txt` regenerated (585 lines, 36 new, of which 8 re-list edited theorems in the new group);
`sorryAx` occurs in **one line**, `HPC.Plane.fugate_cor1` (unchanged). Per-batch audit:
`doc/batches/audits/axioms-batch129.{lean,txt}` (all 59 theorems of the three new files, the 8
edited theorems, and `fugate_cor1`; every theorem except `fugate_cor1` shows exactly
`[propext, Classical.choice, Quot.sound]`); the previous `axioms.txt` is saved as
`doc/batches/audits/axioms-before-batch129.txt`.

## Refutations first: none

* **`separatesPts_insert_iff` as stated** holds (`q ≠ x`, `q ≠ y`, `A` closed). `→`: the component
  `K` of `x` in `Aᶜ` is open and connected, and `K ∖ {q}` is connected
  (`isConnected_diff_singleton_of_isOpen`), misses `insert q A` and contains `x`, so it contains `y`
  if `K` does. `←`: components are monotone. Closedness of `A` is used (openness of `K`).
* **The reduction in `janiszewski_polygonal`** needs no unforeseen hypothesis. Write `A = A' ∪ P_A`,
  `B = B' ∪ P_B` with `A'`, `B'` the `graphSet`s of the nondegenerate segments and `P_A`, `P_B` finite
  (`IsPolygonal.exists_split`). If `x` or `y` is in `A ∪ B` there is nothing to prove; otherwise
  finitely many extra points change no separation of `x` from `y` (`separatesPts_union_finite_iff`,
  induction on `separatesPts_insert_iff`). The intersection (`inter_split_connected`): either
  `A ∩ B ⊆ A' ∩ B'`, and then `A ∩ B = A' ∩ B'`; or some `f ∈ A ∩ B` is off `A' ∩ B'`, i.e. an extra
  point of `A` (or of `B`), which has a neighbourhood meeting `A` (or `B`) only in `f`, so `f` is
  isolated in `A ∩ B`; a connected `A ∩ B` is then `{f}`, and `A' ∩ B' ⊆ {f}` with `f ∉ A' ∩ B'`
  gives `A' ∩ B' = ∅`. In both cases `JaniszewskiPoly` applies to `A'`, `B'`. This is exactly the
  subtle case of the commission (a connected `A ∩ B` with two points has no isolated point; a
  single-point `A ∩ B` is handled by the `∅` case).
* **`isPolygonal_frontier_inter_closure`** holds, and more: for **any** polygonal `Γ₁`, `Γ₂` and any
  `W₁ ⊆ Γ₁ᶜ`, `W₂ ⊆ Γ₂ᶜ` that are unions of components ("saturated": a preconnected set missing `Γᵢ`
  that meets `Wᵢ` lies in `Wᵢ`), `Γ₁ ∩ closure (W₁ ∩ W₂)` is polygonal
  (`isPolygonal_inter_closure_inter`). No configuration of two polygons breaks it, and no Jordan
  curve theorem, vertex analysis or half-disk identification is needed. Proof, per segment
  `e = [a, b]` of `Γ₁` (`a ≠ b`), parametrised by `linePt a b t = a + t • (b − a)`:
  - the special parameters `F` are `0`, `1` and the infimum and supremum of
    `{t ∈ [0, 1] | linePt a b t ∈ σ}` for every segment `σ` of `Γ₁` or `Γ₂`;
  - at `t ∈ (0, 1) ∖ F`, every `σ` through `p = linePt a b t` contains parameters on both sides of
    `t`, hence two distinct points of the line `L` of `e`, hence lies on `L`
    (`crossG_eq_zero_of_two`); so a small ball about `p` meets `Γ₁ ∪ Γ₂` only on `L`, and `L` only
    inside `e ⊆ Γ₁`;
  - the two open half-disks are convex and miss `Γ₁ ∪ Γ₂`, so each is inside or outside `W₁` and
    inside or outside `W₂`; if `p ∈ closure (W₁ ∩ W₂)`, a point of `W₁ ∩ W₂` near `p` is off `L`, so
    one half-disk lies in `W₁ ∩ W₂`, and its closure contains the whole chord
    (`eventually_mem_closure_of_not_special`);
  - so `T = {t ∈ [0, 1] | linePt a b t ∈ closure (W₁ ∩ W₂)}` is open (and closed) in every open
    interval between consecutive points of `F`, and `T` is the union of the `[α, β]` (`α ≤ β` in
    `F`) it contains; its image is a finite union of segments and points
    (`isPolygonal_segment_inter_closure`).

## A gap in the commissioned argument for `exists_theta_point`, and the fix

With the commissioned `A := Γ₁ ∩ closure (h₁ ∩ h₂)`, `B := Γ₂ ∩ closure (h₁ ∩ h₂)`, the step
"if there is no `q` then `A ∩ B ⊆ Γ`" does not go through: a common point of `Γ₁`, `Γ₂` and
`closure (h₁ ∩ h₂)` may lie outside `closure U` (`U = polyInterior Γ`), where it is not a candidate
for `q` (nothing in the hypotheses controls `h₁ ∩ h₂` outside `U`). Then `(A ∪ Γ) ∩ (B ∪ Γ)` need not
be `Γ`. The fix: intersect with `U` inside the closure,

  `A := Γ₁ ∩ closure (U ∩ h₁ ∩ h₂)`,  `B := Γ₂ ∩ closure (U ∩ h₁ ∩ h₂)`

(`U ∩ h₁ ∩ h₂` is the open set whose component is `C`). Now `A ∩ B ⊆ closure U = U ∪ Γ`, and the
batch-118 argument gives `A ∩ B = ∅` (a point in `U` is a `q`; a point of `Γ` lies in `β ⊆ V`, and `V`
is open missing `h₁ ∩ h₂`). The other steps are verbatim: a point of `U ∩ closure C` outside `h₁` is
in `frontier h₁ = Γ₁` and in `closure (U ∩ h₁ ∩ h₂)`, i.e. in `A`; `S₂` misses `B ⊆ Γ₂`; `S_V` misses
`A ⊆ closure (h₁ ∩ h₂)`. Polygonality: `isPolygonal_inter_closure_polyInterior₃` — the general lemma
with `W₁ = polyInterior Γ₁` for `Γ₁` and `W₂ = polyInterior Γ ∩ polyInterior Γ₂` for `Γ ∪ Γ₂` (an
intersection of saturated sets is saturated for the union, `IsSaturated.inter`).

## Items

1. **Polygonal sets** (`HPC/Plane/Polygonal.lean`). `IsPolygonal A := ∃ S : Finset (Pt × Pt),
   A = ⋃ s ∈ S, segment ℝ s.1 s.2` — literally the skeleton's `∃ S, A = graphSet S`
   (`isPolygonal_iff_graphSet := Iff.rfl`), but stated without `graphSet`, which is defined later in
   the import order. `IsPolygonal.isCompact`, `.isClosed`, `.union`, `isPolygonal_empty`,
   `isPolygonal_segment`, `isPolygonal_singleton`, `isPolygonal_biUnion`, and additionally
   `IsPolygonal.inter` (`isPolygonal_segment_inter_segment`: the parameters of `[a, b] ∩ [c, d]` form
   a compact convex subset of `[0, 1]`). `IsSimpleClosedPolygon.isPolygonal` (and
   `isPolygonal_polygonOf`) in `HPC/Plane/PolygonalPoly.lean`.
2. **Isolated points** (`HPC/Plane/JanPoly.lean`). `isConnected_diff_singleton_of_isOpen`: a punctured
   ball (an open square minus its centre, the union of four overlapping convex half-squares,
   `isPreconnected_ball_diff_singleton`) lies in `U ∖ {q}`; every component of `U ∖ {q}` meets it
   (otherwise the component misses a ball about `q`, so it is closed in `U` as well as open, and `U`
   connected forces it to contain `q`). `separatesPts_insert_iff`, `separatesPts_union_finite_iff`,
   `IsPolygonal.exists_split`, `inter_split_connected`, `janiszewski_polygonal` as above.
3. **`polyInterior_local_halfDisk`**: from `ball_diff_chord` (the ball minus `Γ` is the two
   half-disks), `side_of_split` (each convex half-disk lies in `U` or in `V` of `jct_polygon`), the
   closure facts `frontier U = frontier V = Γ` (they cannot lie on the same side), and
   `polyInterior_eq_of_split`. `parity_flip_edge` is not needed. This lemma is not used by the
   polygonality proof.
4. **Polygonality.** `isPolygonal_segment_inter_polygon` (`IsPolygonal.inter`);
   `exists_open_pieces` from `exists_open_pieces_of_saturated` (any polygonal `Γ`, any saturated `W`):
   between consecutive special parameters the open piece of `e` either meets `Γ`, and then lies in
   it (`mem_segment_of_gap`: the parameters on a segment form an interval whose ends are special),
   or is a preconnected set missing `Γ`, hence inside or outside `W`; degenerate pieces
   `openSegment ℝ q q = {q}` occur only when `e` is a point. `isPolygonal_frontier_inter_closure`
   as above (`HPC/Plane/PolygonalPoly.lean`).

## Edits

1. **The field** (`HPC/Plane/Tree67.lean`): `janiszewski : ∀ A B, IsPolygonal A → IsPolygonal B →
   (IsConnected (A ∩ B) ∨ A ∩ B = ∅) → ∀ x y, ¬ SeparatesPts A x y → ¬ SeparatesPts B x y →
   ¬ SeparatesPts (A ∪ B) x y`; the compact form kept in a comment with the requested note. `jct`
   and `enclose` unchanged. `Tree67` imports `HPC.Plane.Polygonal`. `planeFacts_of_enclose`
   (`JanPoly.lean`); `planeFacts_of_enclose_janiszewski` (`Jct2.lean`) kept, its `hjan` now polygonal.
2. **`crosscut'`** (`Tree7Cross.lean`): `hPF.janiszewski _ _ hΓ₁.isPolygonal hΓ₂.isPolygonal …` in
   place of the two `isCompact_poly`; nothing else changed. `Tree7Cross` imports
   `HPC.Plane.PolygonalPoly`.
3. **`exists_theta_point`** (`Tree6.lean`): new hypotheses `{Γ₁ Γ₂} (hΓ₁ : IsSimpleClosedPolygon Γ₁)
   (hΓ₂ : IsSimpleClosedPolygon Γ₂)` and `hh₁ : h₁ = polyInterior Γ₁`, `hh₂ : h₂ = polyInterior Γ₂` in
   place of `ho₁`, `ho₂` (the "keep `h₁`, `h₂` and add equations" option); the sets as described
   above; the old statement in a comment with the requested note. `Tree6` imports
   `HPC.Plane.PolygonalPoly`.
4. **`compFamily_no_circular`** (`Tree6.lean`) and **`treeChain_of_cover`** (`Tree7.lean`): the
   hypothesis `hpoly` as commissioned, passed through. **`theorem7_1951`** (`Tree7Comp.lean`): `hpoly`
   proved for the whole family from `component_inter_eq_polyInterior`, `notched_eq_polyInterior`,
   `isSimpleClosedPolygon_notchedPoly` and `finite_inter_notchedPoly_of_gp`; the old per-member
   argument became `hpoly`. **`theorem6_1951`**: moved to `Tree7Comp.lean` (it must follow
   `theorem7_1951`) and re-proved from it, statement unchanged; its docstring explains that Theorem 6
   is now a corollary of Theorem 7, the reverse of Bing's order, and why.
   **Forced, outside the list:** `theorem7_weak` (`Tree7.lean`, batch 119) used `treeChain_of_cover`
   with the plain notched cover, whose components need not be polygon interiors; it was moved to
   `Tree7Comp.lean` and re-proved from `theorem7_1951` (polygon interiors are open, connected,
   bounded, regular open and non-separating: `polyInterior_eq`, `polyInterior_regular`,
   `compl_polyInterior`), statement unchanged. A comment marks each old place.
5. **Audit**: `Axioms.lean` group "Polygonal Janiszewski (batch 129)" (the new theorems, the edited
   ones, `planeFacts_of_enclose`); the Duke §3 note under the batch-117 header ("relative to
   `PlaneFacts`, whose fields `jct` and `janiszewski` are proved; `enclose` remains a hypothesis").
   `OPEN.md` *Relative results* and `README.md` (batch count 129) updated.

## Final file layout

* `HPC/Plane/Polygonal.lean` (new, imports `StdChain`; imported by `Tree67`): `IsPolygonal` and its
  basic lemmas; the line tools (`crossG`, `linePt`, `segParams`, `specialParams`); `IsSaturated`;
  `isPolygonal_inter_closure_inter`; `IsPolygonal.inter`; `exists_open_pieces_of_saturated`.
* `HPC/Plane/PolygonalPoly.lean` (new, imports `Tree67`; imported by `Tree6`, `Tree7Cross`):
  `IsSimpleClosedPolygon.isPolygonal`, `isSaturated_polyInterior`, `IsSaturated.inter`,
  `isPolygonal_inter_closure_polyInterior(₃)`, `isPolygonal_frontier_inter_closure`.
* `HPC/Plane/JanPoly.lean` (new, imports `Cyc2`; last import of `HPC.lean`): items 2–4 under the
  skeleton's names, `planeFacts_of_enclose`.
* edited: `Tree67.lean` (field, import), `Tree6.lean` (`exists_theta_point`,
  `compFamily_no_circular`, import; `theorem6_1951` moved out), `Tree7.lean` (`treeChain_of_cover`;
  `theorem7_weak` moved out), `Tree7Comp.lean` (`theorem7_1951`; `theorem6_1951` and
  `theorem7_weak` moved in), `Tree7Cross.lean` (`crosscut'`, import), `Jct2.lean`
  (`planeFacts_of_enclose_janiszewski`), `HPC.lean`, `Axioms.lean`, `axioms.txt`, `README.md`,
  `OPEN.md`.
* housekeeping: the commission is `doc/batches/COMMISSION-batch129.md`, the skeleton
  `doc/batches/skeletons/JanPoly.lean`; `theorems-3-4-scheduling(35).md` contains all of
  `doc/theorems-3-4-scheduling.md` (a strict extension) and replaces it. Nothing is left at the root.

## For `enclose` (batches 130–132): what can be reused

* **Polygonal bookkeeping** (`Polygonal.lean`): finite unions, intersections, segment ∩ polygonal
  set, open pieces of a segment in a saturated set, and the special-parameter technique
  (`specialParams`, `exists_special_gap`, `mem_segment_of_gap`) for any finite family of segments —
  the boundary of a thickened grid union is a `graphSet` of axis-parallel unit segments, so its
  classification can be done in this language.
* **Saturated sets** (`IsSaturated`, `isSaturated_polyInterior`, `IsSaturated.inter`): unions of
  components (holes, the unbounded component) are handled uniformly.
* **Jordan curve theorem and local structure** (`Jct1`/`Jct2`): `jct_polygon`,
  `polyInterior_eq_of_split`, `ball_diff_chord`, `polyInterior_local_halfDisk`, `local_piece`,
  `vertex_two_pieces`, `sideNbhd`; the crossing parity `parity` and `isOpen_parity_set` for deciding
  which side a grid square lies on.
* **Graphs and cycles** (`Cyc1`/`Cyc2`): `subdiv`, `exists_proper_subdivision`, `IsCycle`,
  `cycParity`, `exists_cycle_decomposition`, `separatingGraphHasOddCycle` — the outer boundary of a
  polyomino is an even-degree graph; a cycle decomposition and the parity function single out the
  outer cycle; `janiszewski_polygonal` and `separatesPts_union_finite_iff` handle the holes.
* **Polygons from vertex lists** (`Tree7`): `IsSimpleVertices`, `isSimpleClosedPolygon_iff`,
  `polyEdge`; the 20-gon (`notchedVertices`) as a worked example of a vertex list with its
  simplicity proof.

## The batch-118 proof of `theorem6_1951` (replaced)

For the record, the proof that `theorem6_1951` had until batch 128 (the notched-square cover
`exists_notched_cover_bdd`, `enclose`, a finite subcover by components, `isCoherent_of_minimal_cover`,
`compFamily_no_triple`, `compFamily_no_circular` without `hpoly`):

```lean
/-- **Bing 1951 (Duke), Theorem 6**, relative to `PlaneFacts`: a bounded plane continuum
containing no continuum that separates the plane is tree-like. (Assembly: the notched-square
cover `D`; a simple closed polygon `J` around `M` inside `⋃ D` (`enclose`); a finite subfamily `H'`
of `compFamily (polyInterior J) D` covering `M`, each member the component of a point of `M`;
`H'` is coherent (`isCoherent_of_minimal_cover`), has no triple points (`compFamily_no_triple`)
and no circular subchain (`compFamily_no_circular`); each member lies in a link of `D`.) -/
theorem theorem6_1951 (hPF : PlaneFacts) {M : Set Pt} (hM : Fold.Q78.IsContinuum M)
    (hns : ∀ K ⊆ M, Fold.Q78.IsContinuum K → ¬ SeparatesPlane K) : IsTreeLike M := by
  refine ⟨hM, fun ε hε => ?_⟩
  obtain ⟨D, hDo, hDdiam, hDb, hDcov, hDt⟩ := exists_notched_cover_bdd hM hns hε
  have hGo : IsOpen (⋃ d ∈ D, d) := isOpen_biUnion fun d hd => hDo d hd
  obtain ⟨J, hJ, -, hMJ, hJG⟩ := hPF.enclose M hM (hns M subset_rfl hM) _ hGo hDcov
  set d₀ := polyInterior J with hd₀
  have hd₀o : IsOpen d₀ := (hPF.polyInterior_eq hJ).1
  have hx : ∀ x ∈ M, ∃ d ∈ D, x ∈ d := fun x hx => by
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.1 (hDcov hx); exact ⟨d, hd, hxd⟩
  choose! dx hdxD hxdx using hx
  set c : Pt → Set Pt := fun x => connectedComponentIn (d₀ ∩ dx x) x with hc
  have hcmem : ∀ x ∈ M, c x ∈ compFamily d₀ D := fun x hx =>
    ⟨dx x, hdxD x hx, x, ⟨hMJ hx, hxdx x hx⟩, rfl⟩
  obtain ⟨t, htM, htfin, htcov⟩ := hM.1.elim_finite_subcover_image (b := M) (c := c)
    (fun x hx => (compFamily_props hd₀o hDo (hcmem x hx)).1)
    (fun x hx => mem_iUnion₂.2 ⟨x, hx, mem_connectedComponentIn ⟨hMJ hx, hxdx x hx⟩⟩)
  set H := htfin.toFinset.image c with hH
  have hHmem : ∀ h ∈ H, ∃ x ∈ M, h = c x := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
    exact ⟨x, htM (htfin.mem_toFinset.1 hx), rfl⟩
  have hHc : ∀ h ∈ H, h ∈ compFamily d₀ D := by
    intro h hh; obtain ⟨x, hx, rfl⟩ := hHmem h hh; exact hcmem x hx
  have hHo : ∀ h ∈ H, IsOpen h := fun h hh => (compFamily_props hd₀o hDo (hHc h hh)).1
  have hHcov : M ⊆ ⋃ h ∈ H, h := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (htcov hy)
    exact mem_iUnion₂.2 ⟨c x, Finset.mem_image.2 ⟨x, htfin.mem_toFinset.2 hx, rfl⟩, hyx⟩
  refine ⟨H, ⟨hHo, ?_, ?_, ?_⟩, ?_, hHcov⟩
  · refine isCoherent_of_minimal_cover hM.2 H hHo hHcov fun h hh => ?_
    obtain ⟨x, hx, rfl⟩ := hHmem h hh
    exact ⟨x, mem_connectedComponentIn ⟨hMJ hx, hxdx x hx⟩, hx⟩
  · intro A hA B hB C hC hAB hBC hAC
    exact compFamily_no_triple hDt (hHc A hA) (hHc B hB) (hHc C hC) hAB hBC hAC
  · intro G' hG'
    exact compFamily_no_circular hPF hJ hDo hDt hJG G' fun h hh => hHc h (hG' hh)
  · intro h hh
    obtain ⟨x, hx, rfl⟩ := hHmem h hh
    refine lt_of_le_of_lt (diam_mono ?_ (hDb _ (hdxD x hx))) (hDdiam _ (hdxD x hx))
    exact (connectedComponentIn_subset _ _).trans inter_subset_right

```
