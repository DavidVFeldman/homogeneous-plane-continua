import HPC.HO16.LadderStair

/-!
# Batch 197: a ladder carries a stairwell structure — (S2)–(S5) and the theorem

Continuation of `LadderStair.lean`: the end sets of the sheets (`endSet_ladderSheet`), the
agreement of consecutive sheets near `π(αᵢ₊₁)` (S3), consistent complements (S4, via the gaps of
`LadderStair.lean`), genericity (S5), and the assembled statement `ladder_isStairwellStr`.
-/

namespace HPC.HO16

open Set Topology Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Ladder

variable {G : Set E} {S : Finset (E × E)} {y : E → List ℝ} {ev : E × E → Option (ℕ × ℝ × ℝ)}

/-- `αᵢ ∪ αᵢ₊₁ ⊆ Sᵢ`. -/
theorem ladderAlphaSet_subset (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    ladderAlphaSet S y ev i ∪ ladderAlphaSet S y ev (i + 1) ⊆ ladderSheet S y ev i := by
  rintro p (hp | hp) <;> obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hp <;>
    refine mem_iUnion₂.2 ⟨s, hs, ladderAlpha_subset (hL.evOK hs) hi ?_⟩
  · exact Or.inl hps
  · exact Or.inr hps

theorem ladderAlphaSet_finite (S : Finset (E × E)) (y : E → List ℝ)
    (ev : E × E → Option (ℕ × ℝ × ℝ)) (i : ℕ) : (ladderAlphaSet S y ev i).Finite :=
  S.finite_toSet.biUnion fun s _ => ladderAlpha_finite y s (ev s) i

/-- A point of `π(αᵢ)` is the point of an interior parameter of an edge. -/
theorem mem_image_fst_ladderAlphaSet {i : ℕ} {z : E}
    (hz : z ∈ Prod.fst '' ladderAlphaSet S y ev i) :
    ∃ s ∈ S, ∃ a ∈ eA (y s.1).length (ev s) i, AffineMap.lineMap s.1 s.2 a = z := by
  rw [image_fst_ladderAlphaSet] at hz
  obtain ⟨s, hs, a, ha, rfl⟩ := mem_iUnion₂.1 hz
  exact ⟨s, hs, a, ha, rfl⟩

/-- The point of an interior parameter of `s` lies on no other edge, and on `s` only once. -/
theorem lineMap_interior_eq (hL : IsLadder G S y ev) {s s' : E × E} (hs : s ∈ S) (hs' : s' ∈ S)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : AffineMap.lineMap s.1 s.2 a = AffineMap.lineMap s'.1 s'.2 b) : s' = s ∧ b = a := by
  by_cases hss : s = s'
  · subst hss
    exact ⟨rfl, lineMap_inj (hL.ne s hs) hab.symm⟩
  · obtain ⟨k1, -⟩ := vertex_of_two hL hs hs' hss (Ioo_subset_Icc_self ha) hb hab
    rcases k1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact absurd ha.1 (lt_irrefl _)
    · exact absurd ha.2 (lt_irrefl _)

/-- `π(αᵢ) ∩ π(αᵢ') = ∅` for `i ≠ i'`. -/
theorem disjoint_image_fst_ladderAlphaSet (hL : IsLadder G S y ev) {i i' : ℕ} (hii : i ≠ i') :
    Disjoint (Prod.fst '' ladderAlphaSet S y ev i) (Prod.fst '' ladderAlphaSet S y ev i') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨s, hs, a, ha, rfl⟩ := mem_image_fst_ladderAlphaSet hz
  obtain ⟨s', hs', b, hb, hab⟩ := mem_image_fst_ladderAlphaSet hz'
  obtain ⟨rfl, rfl⟩ := lineMap_interior_eq hL hs hs' (eA_sub_Ioo (hL.evOK hs) ha)
    (Ioo_subset_Icc_self (eA_sub_Ioo (hL.evOK hs') hb)) hab.symm
  exact Set.disjoint_left.1 (e_A_disj (hL.evOK hs) hii) ha hb

/-- A point of `π(αᵢ) ∪ π(αᵢ₊₁)` is in the closure of `G \ π(Sᵢ)`. -/
theorem mem_closure_diff_sheet (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) {z : E}
    (hz : z ∈ Prod.fst '' ladderAlphaSet S y ev i ∪ Prod.fst '' ladderAlphaSet S y ev (i + 1)) :
    z ∈ closure (G \ Prod.fst '' ladderSheet S y ev i) := by
  have hz' : ∃ s ∈ S, ∃ a ∈ eA (y s.1).length (ev s) i ∪ eA (y s.1).length (ev s) (i + 1),
      AffineMap.lineMap s.1 s.2 a = z := by
    rcases hz with hz | hz
    · obtain ⟨s, hs, a, ha, h⟩ := mem_image_fst_ladderAlphaSet hz
      exact ⟨s, hs, a, Or.inl ha, h⟩
    · obtain ⟨s, hs, a, ha, h⟩ := mem_image_fst_ladderAlphaSet hz
      exact ⟨s, hs, a, Or.inr ha, h⟩
  obtain ⟨s, hs, a, ha, rfl⟩ := hz'
  have hδ := eδ_pos (hL.evOK hs)
  -- a point `μ` of the gap next to `a` is outside `π(Sᵢ)`
  have hout : ∀ μ, μ ∈ Ioo (0 : ℝ) 1 → μ ∉ eP (y s.1).length (ev s) i →
      AffineMap.lineMap s.1 s.2 μ ∈ G \ Prod.fst '' ladderSheet S y ev i := by
    intro μ hμ hμP
    refine ⟨lineMap_mem_of_mem hL.G_eq hs (Ioo_subset_Icc_self hμ), fun h => ?_⟩
    obtain ⟨s', hs', b, hb, hb'⟩ := (mem_image_fst_ladderSheet hL).1 h
    obtain ⟨rfl, rfl⟩ := lineMap_interior_eq hL hs hs' hμ (e_P_sub (hL.evOK hs') hb) hb'.symm
    exact hμP hb
  have hc : Continuous (AffineMap.lineMap (k := ℝ) s.1 s.2 : ℝ → E) :=
    AffineMap.lineMap_continuous
  rcases e_gap (hL.evOK hs) hi ha with h | h
  · have hsub : AffineMap.lineMap s.1 s.2 '' Ioo a (a + 2 * eδ (y s.1).length (ev s)) ⊆
        G \ Prod.fst '' ladderSheet S y ev i := by
      rintro _ ⟨μ, hμ, rfl⟩
      exact hout μ (h μ hμ.1 hμ.2).1 (h μ hμ.1 hμ.2).2
    refine closure_mono hsub (image_closure_subset_closure_image hc ⟨a, ?_, rfl⟩)
    rw [closure_Ioo (by linarith)]
    exact ⟨le_rfl, by linarith⟩
  · have hsub : AffineMap.lineMap s.1 s.2 '' Ioo (a - 2 * eδ (y s.1).length (ev s)) a ⊆
        G \ Prod.fst '' ladderSheet S y ev i := by
      rintro _ ⟨μ, hμ, rfl⟩
      exact hout μ (h μ hμ.1 hμ.2).1 (h μ hμ.1 hμ.2).2
    refine closure_mono hsub (image_closure_subset_closure_image hc ⟨a, ?_, rfl⟩)
    rw [closure_Ioo (by linarith)]
    exact ⟨by linarith, le_rfl⟩

/-- (S2): `∂π(Sᵢ) = π(αᵢ) ∪ π(αᵢ₊₁)`. -/
theorem relFrontier_image_fst_ladderSheet (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    relFrontier G (Prod.fst '' ladderSheet S y ev i) =
      Prod.fst '' ladderAlphaSet S y ev i ∪ Prod.fst '' ladderAlphaSet S y ev (i + 1) := by
  apply Subset.antisymm
  · rintro z ⟨hz1, hz2⟩
    rw [(isCompact_image_fst_ladderSheet S y ev i).isClosed.closure_eq] at hz1
    have hsub : G \ Prod.fst '' ladderSheet S y ev i ⊆ gapA S y ev i ∪ gapB S y ev i := by
      rintro x ⟨hxG, hxT⟩
      rcases subset_sheet_union_gaps hL hi hxG with (h | h) | h
      · exact absurd h hxT
      · exact Or.inl h
      · exact Or.inr h
    have := closure_mono hsub hz2
    rw [((isClosed_gapA S y ev i).union (isClosed_gapB S y ev i)).closure_eq] at this
    rcases this with h | h
    · exact Or.inl (gapA_inter_sheet hL hi ⟨h, hz1⟩)
    · exact Or.inr (gapB_inter_sheet hL hi ⟨h, hz1⟩)
  · intro z hz
    refine ⟨subset_closure ?_, mem_closure_diff_sheet hL hi hz⟩
    rw [← image_union] at hz
    exact image_mono (ladderAlphaSet_subset hL hi) hz

/-- (S2): `𝓔(Sᵢ) = αᵢ ∪ αᵢ₊₁`. -/
theorem endSet_ladderSheet (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    endSet G (ladderSheet S y ev i) = ladderAlphaSet S y ev i ∪ ladderAlphaSet S y ev (i + 1) := by
  rw [endSet, relFrontier_image_fst_ladderSheet hL hi, ← image_union]
  apply Subset.antisymm
  · rintro p ⟨hpT, q, hq, hqp⟩
    have := injOn_fst_ladderSheet hL hi (ladderAlphaSet_subset hL hi hq) hpT hqp
    rw [← this]; exact hq
  · intro p hp
    exact ⟨ladderAlphaSet_subset hL hi hp, p, hp, rfl⟩

/-- (S3): near `π(αᵢ₊₁)`, the projections of `Sᵢ` and `Sᵢ₊₁` agree. -/
theorem ladder_S3 (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    ∃ V ∈ 𝓝ˢ (Prod.fst '' ladderAlphaSet S y ev (i + 1)),
      Prod.fst '' ladderSheet S y ev i ∩ V = Prod.fst '' ladderSheet S y ev (i + 1) ∩ V := by
  set V : Set E := {z | ∀ s ∈ S, ∀ ν ∈ Icc (0 : ℝ) 1, AffineMap.lineMap s.1 s.2 ν = z →
    (ν ∈ eP (y s.1).length (ev s) i ↔ ν ∈ eP (y s.1).length (ev s) (i + 1))} with hV
  refine ⟨V, ?_, ?_⟩
  · rw [mem_nhdsSet_iff_forall]
    intro x hx
    obtain ⟨s, hs, a, ha, rfl⟩ := mem_image_fst_ladderAlphaSet hx
    obtain ⟨r, hr, hball⟩ := exists_ball_param hL.ne hL.dis hs (eA_sub_Ioo (hL.evOK hs) ha)
      (mul_pos two_pos (eδ_pos (hL.evOK hs)))
    refine mem_of_superset (ball_mem_nhds _ hr) fun z hz s' hs' ν hν hνz => ?_
    obtain ⟨rfl, hνa⟩ := hball z hz s' hs' ν hν hνz
    exact e_S3 (hL.evOK hs') hi ha hνa
  · ext z
    simp only [mem_inter_iff, mem_image_fst_ladderSheet hL]
    constructor
    · rintro ⟨⟨s, hs, μ, hμ, rfl⟩, hz⟩
      exact ⟨⟨s, hs, μ, (hz s hs μ (e_P_sub (hL.evOK hs) hμ) rfl).1 hμ, rfl⟩, hz⟩
    · rintro ⟨⟨s, hs, μ, hμ, rfl⟩, hz⟩
      exact ⟨⟨s, hs, μ, (hz s hs μ (e_P_sub (hL.evOK hs) hμ) rfl).2 hμ, rfl⟩, hz⟩

/-- The frontier of the `gapA` lies on the sheet. -/
theorem relFrontier_gapA_subset (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    relFrontier G (gapA S y ev i) ⊆ Prod.fst '' ladderSheet S y ev i := by
  rintro z ⟨hz1, hz2⟩
  rw [(isClosed_gapA S y ev i).closure_eq] at hz1
  by_contra hzT
  have hsub : G \ gapA S y ev i ⊆ Prod.fst '' ladderSheet S y ev i ∪ gapB S y ev i := by
    rintro x ⟨hxG, hxA⟩
    rcases subset_sheet_union_gaps hL hi hxG with (h | h) | h
    · exact Or.inl h
    · exact absurd h hxA
    · exact Or.inr h
  have := closure_mono hsub hz2
  rw [((isCompact_image_fst_ladderSheet S y ev i).isClosed.union
    (isClosed_gapB S y ev i)).closure_eq] at this
  rcases this with h | h
  · exact hzT h
  · exact Set.disjoint_left.1 (disjoint_gapA_gapB hL hi) hz1 h

/-- (S4), in one statement: the frontier of a component of `G \ π(Sᵢ)` lies in `π(αᵢ)` or in
`π(αᵢ₊₁)`. -/
theorem relFrontier_comp_ladder (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) (x : E) :
    relFrontier G (connectedComponentIn (G \ Prod.fst '' ladderSheet S y ev i) x) ⊆
        Prod.fst '' ladderAlphaSet S y ev i ∨
      relFrontier G (connectedComponentIn (G \ Prod.fst '' ladderSheet S y ev i) x) ⊆
        Prod.fst '' ladderAlphaSet S y ev (i + 1) := by
  set T := Prod.fst '' ladderSheet S y ev i
  have hTc : IsClosed T := (isCompact_image_fst_ladderSheet S y ev i).isClosed
  set C := connectedComponentIn (G \ T) x
  have hfrT : relFrontier G C ⊆ T := hL.isPLGraph.relFrontier_comp_subset hTc x
  have hCsub : C ⊆ gapA S y ev i ∪ gapB S y ev i := by
    intro w hw
    have hw' := connectedComponentIn_subset _ _ hw
    rcases subset_sheet_union_gaps hL hi hw'.1 with (h | h) | h
    · exact absurd h hw'.2
    · exact Or.inl h
    · exact Or.inr h
  rcases comp_subset_or_disjoint hTc (isClosed_gapA S y ev i) (gapA_subset hL i)
    (relFrontier_gapA_subset hL hi) x with h | h
  · left
    intro z hz
    have hzA : z ∈ gapA S y ev i := by
      have := closure_mono h hz.1
      rwa [(isClosed_gapA S y ev i).closure_eq] at this
    exact gapA_inter_sheet hL hi ⟨hzA, hfrT hz⟩
  · right
    have hB : C ⊆ gapB S y ev i := by
      intro w hw
      rcases hCsub hw with h' | h'
      · exact absurd h' (Set.disjoint_left.1 h hw)
      · exact h'
    intro z hz
    have hzB : z ∈ gapB S y ev i := by
      have := closure_mono hB hz.1
      rwa [(isClosed_gapB S y ev i).closure_eq] at this
    exact gapB_inter_sheet hL hi ⟨hzB, hfrT hz⟩

/-- (S4). -/
theorem ladder_S4 (hL : IsLadder G S y ev) {i : ℕ} (hi : 1 ≤ i) :
    HasConsCompl G (Prod.fst '' ladderSheet S y ev i) (Prod.fst '' ladderAlphaSet S y ev i) ∧
    HasConsCompl G (Prod.fst '' ladderSheet S y ev i)
      (Prod.fst '' ladderAlphaSet S y ev (i + 1)) := by
  have hd := disjoint_image_fst_ladderAlphaSet hL (i := i) (i' := i + 1) (by omega)
  constructor
  · intro x _
    rcases relFrontier_comp_ladder hL hi x with h | h
    · exact Or.inl h
    · exact Or.inr (hd.symm.mono_left h)
  · intro x _
    rcases relFrontier_comp_ladder hL hi x with h | h
    · exact Or.inr (hd.mono_left h)
    · exact Or.inl h

/-- (S5). -/
theorem ladder_S5 (hL : IsLadder G S y ev) (a n : ℕ) :
    IsGeneric G ((List.range' a n).map fun i => Prod.fst '' ladderAlphaSet S y ev i) := by
  refine ⟨?_, ?_⟩
  · intro B hB
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hB
    refine ⟨(ladderAlphaSet_finite S y ev i).image _, ?_, ?_⟩
    · intro z hz
      obtain ⟨s, hs, a, ha, rfl⟩ := mem_image_fst_ladderAlphaSet hz
      exact lineMap_mem_of_mem hL.G_eq hs (Ioo_subset_Icc_self (eA_sub_Ioo (hL.evOK hs) ha))
    · intro z hz
      obtain ⟨s, hs, a, ha, rfl⟩ := mem_image_fst_ladderAlphaSet hz
      refine isOrdinaryPt_of_mem_openSegment hL.ne hL.G_eq hL.dis hs ?_
      rw [openSegment_eq_image_lineMap]
      exact ⟨a, eA_sub_Ioo (hL.evOK hs) ha, rfl⟩
  · rw [List.pairwise_map]
    exact (List.nodup_range' (s := a) (n := n)).imp fun h =>
      disjoint_image_fst_ladderAlphaSet hL h

/-- **§3 (assembled)**: the sheets of a ladder, with `α = ladderAlphaSet`, form a stairwell
structure of height `ladderHeight S y` for their union. -/
theorem ladder_isStairwellStr (hL : IsLadder G S y ev) (hS : S.Nonempty) :
    IsStairwellStr G (⋃ i ∈ Icc 1 (ladderHeight S y), ladderSheet S y ev i)
      (ladderHeight S y) (ladderSheet S y ev) (ladderAlphaSet S y ev) := by
  have hodd := odd_ladderHeight hL hS
  refine ⟨hodd.pos, fun i hi => ⟨ladderSheet_nonempty hL hS hi.1 hi.2,
    isStraight_ladderSheet hL hi.1⟩, rfl, fun i hi => ⟨endSet_ladderSheet hL hi.1, ?_,
    ladderAlphaSet_finite S y ev i, ladderAlphaSet_finite S y ev (i + 1)⟩, ?_, ?_,
    fun i hi => ladder_S3 hL hi.1, fun i hi => ladder_S4 hL hi.1, ladder_S5 hL _ _⟩
  · exact (disjoint_image_fst_ladderAlphaSet hL (i := i) (i' := i + 1) (by omega)).of_image
  · exact eq_empty_of_subset_empty (iUnion₂_subset fun s hs =>
      (ladderAlpha_one (hL.evOK hs)).subset)
  · refine eq_empty_of_subset_empty (iUnion₂_subset fun s hs =>
      (ladderAlpha_top (hL.evOK hs) ?_).subset)
    rw [hL.eJ2_eq hs]
    have := (length_le_ladderHeight (y := y) hs).2
    omega

end Ladder

end

end HPC.HO16
