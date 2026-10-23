import HPC.Plane.Cyc2

/-!
# Batch 129: polygonal Janiszewski, part III — polygonal sets, the field change, the two uses

COMMISSION-batch129.md. The skeleton of the commission (`doc/batches/skeletons/JanPoly.lean`) with
every `sorry` replaced by a proof; nothing in this file is `sorry` and nothing was refuted. Final
layout (the dependency order forced a split, as the commission foresaw):

* `HPC/Plane/Polygonal.lean` (imported by `Tree67`): `IsPolygonal` (stated with pairs of points,
  literally `∃ S, A = graphSet S`; see `isPolygonal_iff_graphSet` below) and its basic lemmas
  (`isCompact`, `union`, `inter`, `isPolygonal_empty`, `isPolygonal_segment`,
  `isPolygonal_singleton`, `isPolygonal_biUnion`), the general polygonality lemma
  `isPolygonal_inter_closure_inter` and the open-pieces lemma `exists_open_pieces_of_saturated`.
* `HPC/Plane/PolygonalPoly.lean` (imported by `Tree6` and `Tree7Cross`):
  `IsSimpleClosedPolygon.isPolygonal`, `isSaturated_polyInterior`,
  `isPolygonal_frontier_inter_closure` and the three-fold form used by `exists_theta_point`.
* this file: the items that need `Cyc2` / `Jct2` — the isolated-point lemmas,
  `janiszewski_polygonal`, `polyInterior_local_halfDisk`, the commission's names
  `isPolygonal_segment_inter_polygon` and `exists_open_pieces`, and `planeFacts_of_enclose`.

Changes of shape: none of the statements below differ from the skeleton. The skeleton's
`IsPolygonal` definition and its basic lemmas, and `isPolygonal_frontier_inter_closure`, live in
the two earlier files (same names, same statements); `isPolygonal_frontier_inter_closure` is proved
without `polyInterior_local_halfDisk` (see `Polygonal.lean`).
-/

namespace HPC.Plane

open Set Metric

/-! ### Isolated points do not separate -/

/-- A punctured ball in the plane (sup metric: a punctured open square) is connected: it is the
union of the four open half-squares right, top, left, bottom of the centre, which are convex and
overlap in consecutive pairs. -/
theorem isPreconnected_ball_diff_singleton (q : Pt) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball q r \ {q}) := by
  set R := ball q r ∩ {z : Pt | q.1 < z.1}
  set T := ball q r ∩ {z : Pt | q.2 < z.2}
  set L := ball q r ∩ {z : Pt | z.1 < q.1}
  set B := ball q r ∩ {z : Pt | z.2 < q.2}
  have hcR : IsPreconnected R := ((convex_ball q r).inter
    (convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear q.1)).isPreconnected
  have hcT : IsPreconnected T := ((convex_ball q r).inter
    (convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear q.2)).isPreconnected
  have hcL : IsPreconnected L := ((convex_ball q r).inter
    (convex_halfSpace_lt (LinearMap.fst ℝ ℝ ℝ).isLinear q.1)).isPreconnected
  have hcB : IsPreconnected B := ((convex_ball q r).inter
    (convex_halfSpace_lt (LinearMap.snd ℝ ℝ ℝ).isLinear q.2)).isPreconnected
  have hmem : ∀ s t : ℝ, |s| < r → |t| < r → ((q.1 + s, q.2 + t) : Pt) ∈ ball q r := by
    intro s t hs ht
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [add_sub_cancel_left]
    exact max_lt hs ht
  have hr2 : |r / 2| < r := by rw [abs_of_pos (by positivity)]; linarith
  have hr2' : |-(r / 2)| < r := by rw [abs_neg]; exact hr2
  have heq : ball q r \ {q} = ((R ∪ T) ∪ L) ∪ B := by
    ext z
    simp only [mem_diff, mem_singleton_iff, mem_union, mem_inter_iff, mem_setOf_eq, R, T, L, B]
    constructor
    · rintro ⟨hz, hzq⟩
      rcases lt_trichotomy q.1 z.1 with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hz, h⟩))
      · rcases lt_trichotomy q.2 z.2 with h' | h' | h'
        · exact Or.inl (Or.inl (Or.inr ⟨hz, h'⟩))
        · exact absurd (Prod.ext h.symm h'.symm) hzq
        · exact Or.inr ⟨hz, h'⟩
      · exact Or.inl (Or.inr ⟨hz, h⟩)
    · rintro (((⟨hz, h⟩ | ⟨hz, h⟩) | ⟨hz, h⟩) | ⟨hz, h⟩) <;> refine ⟨hz, ?_⟩ <;> rintro rfl <;>
        exact lt_irrefl _ h
  rw [heq]
  have h1R : ((q.1 + r / 2, q.2 + r / 2) : Pt) ∈ R :=
    ⟨hmem _ _ hr2 hr2, show q.1 < q.1 + r / 2 by linarith⟩
  have h1T : ((q.1 + r / 2, q.2 + r / 2) : Pt) ∈ T :=
    ⟨hmem _ _ hr2 hr2, show q.2 < q.2 + r / 2 by linarith⟩
  have h2T : ((q.1 + -(r / 2), q.2 + r / 2) : Pt) ∈ T :=
    ⟨hmem _ _ hr2' hr2, show q.2 < q.2 + r / 2 by linarith⟩
  have h2L : ((q.1 + -(r / 2), q.2 + r / 2) : Pt) ∈ L :=
    ⟨hmem _ _ hr2' hr2, show q.1 + -(r / 2) < q.1 by linarith⟩
  have h3L : ((q.1 + -(r / 2), q.2 + -(r / 2)) : Pt) ∈ L :=
    ⟨hmem _ _ hr2' hr2', show q.1 + -(r / 2) < q.1 by linarith⟩
  have h3B : ((q.1 + -(r / 2), q.2 + -(r / 2)) : Pt) ∈ B :=
    ⟨hmem _ _ hr2' hr2', show q.2 + -(r / 2) < q.2 by linarith⟩
  have hRT : IsPreconnected (R ∪ T) := hcR.union _ h1R h1T hcT
  have hRTL : IsPreconnected (R ∪ T ∪ L) := hRT.union _ (Or.inr h2T) h2L hcL
  exact hRTL.union _ (Or.inr h3L) h3B hcB

/-- **An open connected subset of the plane minus a point is connected.** Take a punctured ball
`D` about `q` inside `U`; it is connected (`isPreconnected_ball_diff_singleton`). Every component
`K` of `U ∖ {q}` meets `D`: otherwise `K` misses the ball, so `K` is closed in `U` (a point of
`U ∩ closure K` is not `q` and so lies in `K`) as well as open, and `U` connected forces `K = U ∋ q`.
Hence all components equal the component of `D`. -/
theorem isConnected_diff_singleton_of_isOpen {U : Set Pt} (hU : IsOpen U) (hc : IsConnected U)
    (q : Pt) : IsConnected (U \ {q}) := by
  by_cases hq : q ∈ U
  swap
  · rwa [diff_singleton_eq_self hq]
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU q hq
  set S := U \ {q} with hS
  have hSo : IsOpen S := hU.sdiff isClosed_singleton
  set D := ball q r \ {q} with hD
  have hDS : D ⊆ S := diff_subset_diff_left hrU
  have hDc : IsPreconnected D := isPreconnected_ball_diff_singleton q hr
  set d₀ : Pt := (q.1 + r / 2, q.2) with hd₀
  have hd₀D : d₀ ∈ D := by
    refine ⟨?_, fun h => ?_⟩
    · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [hd₀, add_sub_cancel_left, sub_self, abs_zero]
      rw [abs_of_pos (by positivity)]
      exact max_lt (by linarith) hr
    · have := congrArg Prod.fst h
      simp only [hd₀] at this
      linarith
  have hmeet : ∀ y ∈ S, (connectedComponentIn S y ∩ D).Nonempty := by
    intro y hy
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    set K := connectedComponentIn S y with hK
    have hKS : K ⊆ S := connectedComponentIn_subset _ _
    have hKo : IsOpen K := hSo.connectedComponentIn
    have hKball : Disjoint (ball q r) K := by
      rw [Set.disjoint_left]
      intro z hz hzK
      by_cases hzq : z = q
      · exact (hKS hzK).2 hzq
      · exact (eq_empty_iff_forall_notMem.1 hne) z ⟨hzK, hz, hzq⟩
    have hclK : Disjoint (ball q r) (closure K) := hKball.closure_right isOpen_ball
    have hcov : U ⊆ K ∪ (closure K)ᶜ := by
      intro u hu
      by_cases huc : u ∈ closure K
      · left
        have huq : u ≠ q := fun h => hclK.notMem_of_mem_left (h ▸ mem_ball_self hr) huc
        exact mem_connectedComponentIn_of_mem_closure hSo ⟨hu, huq⟩ huc
      · exact Or.inr huc
    rcases isPreconnected_iff_subset_of_disjoint.1 hc.isPreconnected K (closure K)ᶜ hKo
      isClosed_closure.isOpen_compl hcov (by
        refine eq_empty_of_forall_notMem ?_
        rintro u ⟨-, hu1, hu2⟩; exact hu2 (subset_closure hu1)) with h | h
    · exact (hKS (h hq)).2 rfl
    · exact h (hKS (mem_connectedComponentIn hy)).1 (subset_closure (mem_connectedComponentIn hy))
  have hall : S ⊆ connectedComponentIn S d₀ := by
    intro y hy
    obtain ⟨d, hdK, hdD⟩ := hmeet y hy
    have h1 : d ∈ connectedComponentIn S d₀ := hDc.subset_connectedComponentIn hd₀D hDS hdD
    rw [connectedComponentIn_eq h1, ← connectedComponentIn_eq hdK]
    exact mem_connectedComponentIn hy
  have heq : connectedComponentIn S d₀ = S :=
    subset_antisymm (connectedComponentIn_subset _ _) hall
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.2 (hDS hd₀D)

/-- **Adding a point to a closed set does not change which pairs of other points it separates.**
(`→`: the component of `x` in `Aᶜ` is open and connected, so minus `q` it is still connected and
joins `x` to `y` off `insert q A`; `←`: monotonicity of components.) -/
theorem separatesPts_insert_iff {A : Set Pt} (hA : IsClosed A) {q x y : Pt} (hqx : q ≠ x)
    (hqy : q ≠ y) : SeparatesPts (insert q A) x y ↔ SeparatesPts A x y := by
  constructor
  · rintro ⟨hx, hy, hsep⟩
    refine ⟨fun h => hx (Or.inr h), fun h => hy (Or.inr h), fun hyK => hsep ?_⟩
    have hxA : x ∉ A := fun h => hx (Or.inr h)
    set K := connectedComponentIn Aᶜ x
    have hKc : IsConnected (K \ {q}) := isConnected_diff_singleton_of_isOpen
      hA.isOpen_compl.connectedComponentIn (isConnected_connectedComponentIn_iff.2 hxA) q
    refine hKc.isPreconnected.subset_connectedComponentIn ⟨mem_connectedComponentIn hxA,
      hqx.symm⟩ ?_ ⟨hyK, hqy.symm⟩
    rintro z ⟨hzK, hzq⟩ (h | h)
    · exact hzq h
    · exact connectedComponentIn_subset _ _ hzK h
  · rintro ⟨hx, hy, hsep⟩
    refine ⟨?_, ?_, fun hyK => hsep ?_⟩
    · rintro (h | h)
      · exact hqx h.symm
      · exact hx h
    · rintro (h | h)
      · exact hqy h.symm
      · exact hy h
    · exact connectedComponentIn_mono x (compl_subset_compl.2 (subset_insert q A)) hyK

/-- Adding finitely many points (other than `x`, `y`) to a closed set does not change whether it
separates `x` from `y`. -/
theorem separatesPts_union_finite_iff {C P : Set Pt} (hC : IsClosed C) (hP : P.Finite) {x y : Pt}
    (hx : x ∉ P) (hy : y ∉ P) : SeparatesPts (C ∪ P) x y ↔ SeparatesPts C x y := by
  induction P, hP using Set.Finite.induction_on with
  | empty => rw [union_empty]
  | @insert q P hqP hPf ih =>
    have hx' : x ∉ P := fun h => hx (Or.inr h)
    have hy' : y ∉ P := fun h => hy (Or.inr h)
    rw [union_insert, separatesPts_insert_iff (hC.union hPf.isClosed)
      (fun h => hx (by rw [← h]; exact mem_insert q P))
      (fun h => hy (by rw [← h]; exact mem_insert q P)), ih hx' hy']

/-! ### Polygonal Janiszewski -/

/-- `IsPolygonal` is literally `∃ S, A = graphSet S` (`Seg = Pt × Pt`, `segSet s = segment ℝ s.1 s.2`). -/
theorem isPolygonal_iff_graphSet {A : Set Pt} : IsPolygonal A ↔ ∃ S : Finset Seg, A = graphSet S :=
  Iff.rfl

/-- **Splitting off the isolated points**: a polygonal set is the union of the `graphSet` of its
nondegenerate segments and of finitely many further points. -/
theorem IsPolygonal.exists_split {A : Set Pt} (hA : IsPolygonal A) :
    ∃ S : Finset Seg, (∀ s ∈ S, s.1 ≠ s.2) ∧ graphSet S ⊆ A ∧ (A \ graphSet S).Finite := by
  classical
  obtain ⟨S₀, rfl⟩ := hA
  refine ⟨S₀.filter (fun s => s.1 ≠ s.2), fun s hs => (Finset.mem_filter.1 hs).2, ?_, ?_⟩
  · intro z hz
    obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hz
    exact mem_iUnion₂.2 ⟨s, (Finset.mem_filter.1 hs).1, hzs⟩
  · refine (S₀.image Prod.fst).finite_toSet.subset ?_
    rintro z ⟨hz, hzS⟩
    obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hz
    by_cases h : s.1 = s.2
    · have hzs' : z ∈ segment ℝ s.1 s.2 := hzs
      rw [h, segment_same, mem_singleton_iff] at hzs'
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨s, hs, h.trans hzs'.symm⟩)
    · exact absurd (mem_iUnion₂.2 ⟨s, Finset.mem_filter.2 ⟨hs, h⟩, hzs⟩) hzS

/-- A preconnected set with a relatively isolated point `f` is `⊆ {f}`. -/
theorem subset_singleton_of_isolated {C N : Set Pt} {f : Pt} (hC : IsPreconnected C) (hf : f ∈ C)
    (hN : IsOpen N) (hfN : f ∈ N) (hNC : C ∩ N ⊆ {f}) : C ⊆ {f} := by
  rcases isPreconnected_iff_subset_of_disjoint.1 hC N {f}ᶜ hN isClosed_singleton.isOpen_compl
    (fun z _ => by
      by_cases h : z = f
      · exact Or.inl (h ▸ hfN)
      · exact Or.inr h)
    (by
      refine eq_empty_of_forall_notMem ?_
      rintro z ⟨hzC, hzN, hzf⟩
      exact hzf (hNC ⟨hzC, hzN⟩)) with h | h
  · exact fun z hz => hNC ⟨hz, h hz⟩
  · exact absurd rfl (h hf)

/-- An extra point `f ∈ A ∖ A'` (with `A'` closed and `A ∖ A'` finite) is isolated in `A`. -/
theorem exists_isolating_nbhd {A A' : Set Pt} (hA' : IsClosed A') (hP : (A \ A').Finite) {f : Pt}
    (hf : f ∉ A') : ∃ N : Set Pt, IsOpen N ∧ f ∈ N ∧ A ∩ N ⊆ {f} := by
  refine ⟨A'ᶜ ∩ ((A \ A') \ {f})ᶜ, hA'.isOpen_compl.inter (hP.diff).isClosed.isOpen_compl,
    ⟨hf, fun h => h.2 rfl⟩, ?_⟩
  rintro z ⟨hzA, hzA', hz⟩
  by_contra hzf
  exact hz ⟨⟨hzA, hzA'⟩, hzf⟩

/-- **The intersection after splitting.** If `A ∩ B` is connected or empty, so is `A' ∩ B'`, where
`A' ⊆ A`, `B' ⊆ B` are closed with finite remainders: either `A ∩ B = A' ∩ B'`, or `A ∩ B` has a
point `f` off `A' ∩ B'`; such a point is isolated in `A ∩ B` (it is an extra point of `A` or of
`B`), so a connected `A ∩ B` is `{f}` and `A' ∩ B' = ∅`. This is the subtle case of the
reduction: an isolated point of `A` lying in `B` is an isolated point of `A ∩ B`. -/
theorem inter_split_connected {A B A' B' : Set Pt} (hA' : IsClosed A') (hB' : IsClosed B')
    (hA'A : A' ⊆ A) (hB'B : B' ⊆ B) (hPA : (A \ A').Finite) (hPB : (B \ B').Finite)
    (hAB : IsConnected (A ∩ B) ∨ A ∩ B = ∅) : IsConnected (A' ∩ B') ∨ A' ∩ B' = ∅ := by
  by_cases h : A ∩ B ⊆ A' ∩ B'
  · rwa [subset_antisymm (inter_subset_inter hA'A hB'B) h]
  obtain ⟨f, hfAB, hf'⟩ := not_subset.1 h
  have hc : IsPreconnected (A ∩ B) := by
    rcases hAB with h' | h'
    · exact h'.isPreconnected
    · rw [h'] at hfAB; exact absurd hfAB (notMem_empty f)
  have hsub : A ∩ B ⊆ {f} := by
    by_cases hfA : f ∈ A'
    · have hfB : f ∉ B' := fun hfB => hf' ⟨hfA, hfB⟩
      obtain ⟨N, hN, hfN, hNB⟩ := exists_isolating_nbhd hB' hPB hfB
      exact subset_singleton_of_isolated hc hfAB hN hfN fun z hz => hNB ⟨hz.1.2, hz.2⟩
    · obtain ⟨N, hN, hfN, hNA⟩ := exists_isolating_nbhd hA' hPA hfA
      exact subset_singleton_of_isolated hc hfAB hN hfN fun z hz => hNA ⟨hz.1.1, hz.2⟩
  right
  refine eq_empty_of_forall_notMem fun z hz => hf' ?_
  have := hsub (inter_subset_inter hA'A hB'B hz)
  rw [mem_singleton_iff] at this
  exact this ▸ hz

/-- **Janiszewski for polygonal sets** (degenerate segments allowed), from `janiszewskiPoly_holds`
by the reduction from degenerate segments. Split `A = A' ∪ P_A`, `B = B' ∪ P_B` with `A'`, `B'` the
`graphSet`s of the nondegenerate segments and `P_A`, `P_B` finite (`IsPolygonal.exists_split`).
If `x` or `y` lies in `A ∪ B` there is nothing to prove; otherwise adding or removing the finitely
many points of `P_A`, `P_B` changes no separation of `x` from `y`
(`separatesPts_union_finite_iff`), so `A'`, `B'` do not separate and it suffices that `A' ∪ B'` does
not. `JaniszewskiPoly` applies to `A'`, `B'` because `A' ∩ B'` is connected or empty
(`inter_split_connected`). The subtle case flagged in the commission: an isolated point of `A` that
lies in `B` is an isolated point of `A ∩ B`; so a connected `A ∩ B` with two points contains no
such point and equals `A' ∩ B'`, while a single-point `A ∩ B = {f}` with `f ∉ A' ∩ B'` gives
`A' ∩ B' = ∅` — the empty case of `JaniszewskiPoly`. No extra hypothesis is needed. -/
theorem janiszewski_polygonal {A B : Set Pt} (hA : IsPolygonal A) (hB : IsPolygonal B)
    (hAB : IsConnected (A ∩ B) ∨ A ∩ B = ∅) {x y : Pt} (hx : ¬ SeparatesPts A x y)
    (hy : ¬ SeparatesPts B x y) : ¬ SeparatesPts (A ∪ B) x y := by
  intro hsep
  have hxAB := hsep.1
  have hyAB := hsep.2.1
  obtain ⟨SA, hndA, hSA, hPA⟩ := hA.exists_split
  obtain ⟨SB, hndB, hSB, hPB⟩ := hB.exists_split
  have hA'c : IsClosed (graphSet SA) := isClosed_graphSet SA
  have hB'c : IsClosed (graphSet SB) := isClosed_graphSet SB
  have hAeq : A = graphSet SA ∪ (A \ graphSet SA) := (union_diff_cancel hSA).symm
  have hBeq : B = graphSet SB ∪ (B \ graphSet SB) := (union_diff_cancel hSB).symm
  have hxA : x ∉ A \ graphSet SA := fun h => hxAB (Or.inl h.1)
  have hyA : y ∉ A \ graphSet SA := fun h => hyAB (Or.inl h.1)
  have hxB : x ∉ B \ graphSet SB := fun h => hxAB (Or.inr h.1)
  have hyB : y ∉ B \ graphSet SB := fun h => hyAB (Or.inr h.1)
  have hnA : ¬ SeparatesPts (graphSet SA) x y := fun h => hx (by
    rw [hAeq, separatesPts_union_finite_iff hA'c hPA hxA hyA]; exact h)
  have hnB : ¬ SeparatesPts (graphSet SB) x y := fun h => hy (by
    rw [hBeq, separatesPts_union_finite_iff hB'c hPB hxB hyB]; exact h)
  have hinter := inter_split_connected hA'c hB'c hSA hSB hPA hPB hAB
  apply janiszewskiPoly_holds SA SB hndA hndB hinter x y hnA hnB
  have hU : A ∪ B = (graphSet SA ∪ graphSet SB) ∪ ((A \ graphSet SA) ∪ (B \ graphSet SB)) := by
    conv_lhs => rw [hAeq, hBeq]
    ac_rfl
  rw [← separatesPts_union_finite_iff (hA'c.union hB'c) (hPA.union hPB)
    (fun h => h.elim hxA hxB) (fun h => h.elim hyA hyB), ← hU]
  exact hsep

/-! ### The local half-disk, segments against a polygon -/

/-- At a non-vertex point `p` of an edge of a simple closed polygon `Γ`, the interior
`polyInterior Γ` meets every small ball in exactly one of the two half-disks. Proof: `ball_diff_chord`
splits `ball p ρ ∖ Γ` into the two (convex) half-disks; each lies in the bounded component `U` or
in the unbounded one `V` of `jct_polygon` (`side_of_split`), and since `p` is in the closure of both
(`frontier U = frontier V = Γ`) they lie in different ones; `polyInterior Γ = U`
(`polyInterior_eq_of_split`). (`parity_flip_edge` is not needed.) -/
theorem polyInterior_local_halfDisk {n : ℕ} {v : Fin n → Pt} (hv : IsSimpleVertices v) (i : Fin n)
    {p : Pt} (hp : p ∈ polyEdge v i) (hpv : ∀ k, p ≠ v k) :
    ∃ ρ > 0, ∃ s : Bool, ∀ ρ', 0 < ρ' → ρ' ≤ ρ →
      ball p ρ' ∩ polyInterior (polygonOf v) =
        halfDisk p (v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i) ρ' s := by
  set d := v ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩ - v i with hd
  have hJ : IsSimpleClosedPolygon (polygonOf v) := isSimpleClosedPolygon_iff.2 ⟨n, v, hv, rfl⟩
  obtain ⟨U, V, hU, hV, hJUV, hdUV, hUc, hVc, hUb, hVb, hfU, hfV⟩ := jct_polygon _ hJ
  rw [polyInterior_eq_of_split hU hV hJUV hdUV hUc hVc hUb hVb]
  obtain ⟨ρ, hρ, hchord⟩ := ball_diff_chord hv i hp hpv
  have hpΓ : p ∈ polygonOf v := mem_iUnion.2 ⟨i, hp⟩
  have hUΓ : U ⊆ (polygonOf v)ᶜ := fun z hz => hJUV ▸ Or.inl hz
  have hVΓ : V ⊆ (polygonOf v)ᶜ := fun z hz => hJUV ▸ Or.inr hz
  have hsub : ∀ s : Bool, halfDisk p d ρ s ⊆ ball p ρ \ polygonOf v := by
    intro s z hz
    rw [hchord ρ hρ le_rfl]
    cases s
    · exact Or.inr hz
    · exact Or.inl hz
  have hside : ∀ s : Bool, halfDisk p d ρ s ⊆ U ∨ halfDisk p d ρ s ⊆ V := fun s =>
    side_of_split hU hV hJUV hdUV (halfDisk_convex p d ρ s).isPreconnected
      (Set.disjoint_left.2 fun z hz hzΓ => (hsub s hz).2 hzΓ)
  have hmono : ∀ (s : Bool) (ρ' : ℝ), ρ' ≤ ρ → halfDisk p d ρ' s ⊆ halfDisk p d ρ s :=
    fun s ρ' h z hz => ⟨ball_subset_ball h hz.1, hz.2⟩
  have hreach : ∀ W : Set Pt, W ⊆ (polygonOf v)ᶜ → p ∈ closure W →
      (W ∩ halfDisk p d ρ true).Nonempty ∨ (W ∩ halfDisk p d ρ false).Nonempty := by
    intro W hW hpW
    obtain ⟨w, hwW, hwd⟩ := Metric.mem_closure_iff.1 hpW ρ hρ
    have : w ∈ ball p ρ \ polygonOf v := ⟨by rw [mem_ball, dist_comm]; exact hwd, hW hwW⟩
    rw [hchord ρ hρ le_rfl] at this
    rcases this with h | h
    · exact Or.inl ⟨w, hwW, h⟩
    · exact Or.inr ⟨w, hwW, h⟩
  have hpU : p ∈ closure U := frontier_subset_closure (hfU.symm ▸ hpΓ)
  have hpV : p ∈ closure V := frontier_subset_closure (hfV.symm ▸ hpΓ)
  have key : ∀ s : Bool, halfDisk p d ρ s ⊆ U → halfDisk p d ρ (!s) ⊆ V →
      ∀ ρ', 0 < ρ' → ρ' ≤ ρ → ball p ρ' ∩ U = halfDisk p d ρ' s := by
    intro s hsU hsV ρ' hρ' hle
    ext z
    constructor
    · rintro ⟨hzb, hzU⟩
      have : z ∈ ball p ρ' \ polygonOf v := ⟨hzb, hUΓ hzU⟩
      rw [hchord ρ' hρ' hle] at this
      cases s <;> simp only [Bool.not_false, Bool.not_true] at hsV <;> rcases this with h | h
      · exact absurd (hsV (hmono _ ρ' hle h)) (hdUV.notMem_of_mem_left hzU)
      · exact h
      · exact h
      · exact absurd (hsV (hmono _ ρ' hle h)) (hdUV.notMem_of_mem_left hzU)
    · intro hz
      exact ⟨hz.1, hsU (hmono s ρ' hle hz)⟩
  rcases hside true with hT | hT <;> rcases hside false with hF | hF
  · exfalso
    rcases hreach V hVΓ hpV with ⟨w, hwV, hw⟩ | ⟨w, hwV, hw⟩
    · exact hdUV.notMem_of_mem_left (hT hw) hwV
    · exact hdUV.notMem_of_mem_left (hF hw) hwV
  · exact ⟨ρ, hρ, true, key true hT hF⟩
  · exact ⟨ρ, hρ, false, key false hF hT⟩
  · exfalso
    rcases hreach U hUΓ hpU with ⟨w, hwU, hw⟩ | ⟨w, hwU, hw⟩
    · exact hdUV.notMem_of_mem_left hwU (hT hw)
    · exact hdUV.notMem_of_mem_left hwU (hF hw)

/-- A segment `e` and a simple closed polygon `Γ₂` meet in a finite union of segments and points
(`IsPolygonal.inter`: pairwise intersections of segments are segments, points or empty). -/
theorem isPolygonal_segment_inter_polygon {a b : Pt} {Γ₂ : Set Pt}
    (hΓ₂ : IsSimpleClosedPolygon Γ₂) : IsPolygonal (segment ℝ a b ∩ Γ₂) :=
  isPolygonal_segment_inter a b hΓ₂.isPolygonal

/-- `e ∖ Γ₂` is a finite union of open subsegments, each inside `polyInterior Γ₂` or inside its
exterior; so `e ∩ polyInterior Γ₂` is a finite union of open subsegments (degenerate ones, i.e.
points `openSegment ℝ q q = {q}`, allowed — they occur only for a degenerate `e`). From
`exists_open_pieces_of_saturated`; no Jordan curve theorem is used. -/
theorem exists_open_pieces {a b : Pt} {Γ₂ : Set Pt} (hΓ₂ : IsSimpleClosedPolygon Γ₂) :
    ∃ P : Finset (Pt × Pt), (∀ q ∈ P, q.1 ∈ segment ℝ a b ∧ q.2 ∈ segment ℝ a b) ∧
      segment ℝ a b ∩ polyInterior Γ₂ = ⋃ q ∈ P, openSegment ℝ q.1 q.2 :=
  exists_open_pieces_of_saturated a b hΓ₂.isPolygonal (isSaturated_polyInterior Γ₂)

/-! ### The interface down to one field -/

/-- **`PlaneFacts` from `enclose` alone**: `jct` is `jct_polygon` (batch 126), `janiszewski` (in its
batch-129 polygonal form) is `janiszewski_polygonal`. -/
theorem planeFacts_of_enclose
    (henc : ∀ M : Set Pt, Fold.Q78.IsContinuum M → ¬ SeparatesPlane M →
      ∀ G : Set Pt, IsOpen G → M ⊆ G →
        ∃ J : Set Pt, IsSimpleClosedPolygon J ∧ Disjoint J M ∧ M ⊆ polyInterior J ∧
          polyInterior J ⊆ G) :
    PlaneFacts :=
  ⟨jct_polygon, henc, fun _ _ hA hB hAB _ _ hx hy => janiszewski_polygonal hA hB hAB hx hy⟩

end HPC.Plane
