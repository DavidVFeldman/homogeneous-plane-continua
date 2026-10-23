import HPC.HO16.PLLib2

/-!
# Batch 195, §3: tools for sides

Facts about components of `G \ X` (`X` closed) in a PL graph `G` and about the sides `σ_B(A)`
(`sideOf G B A`), used for the observations after Definition 9 and Propositions 10 and 11
(`HPC/HO16/Sides.lean`). The workhorses:

* `IsPreconnected.subset_of_relClopenG`: a preconnected subset of `G` meeting a relatively open
  set `C` and meeting `cl C` only inside `C` lies in `C`;
* `IsPLGraph.comp_eq_of_relFrontier_subset`: a component `C` of `G \ A` with `∂C ⊆ B ⊆ A` is a
  component of `G \ B`;
* `IsPLGraph.disjoint_relFrontier_of_meets_sideOf`: if `A` has consistent complement relative to
  `B`, a component `C` of `G \ A` meeting `σ_B(A)` has `∂C ∩ B = ∅`;
* `IsPLGraph.sideOf_char_aux`: the characterization of p. 190 (existence part) with no
  connectedness or non-emptiness hypotheses.
-/

namespace HPC.HO16

open Set Topology Metric Filter

section SidesLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A relatively open subset of `G` is the trace of an open set. -/
theorem exists_open_eq_inter {G C : Set E} (hCG : C ⊆ G) (hC : ∀ y ∈ C, C ∈ 𝓝[G] y) :
    ∃ O, IsOpen O ∧ C = G ∩ O := by
  refine ⟨interior (C ∪ Gᶜ), isOpen_interior, Subset.antisymm (fun y hy => ⟨hCG hy, ?_⟩) ?_⟩
  · rw [mem_interior_iff_mem_nhds]
    have := hC y hy
    rw [mem_nhdsWithin_iff_eventually] at this
    filter_upwards [this] with z hz
    by_cases hzG : z ∈ G
    · exact Or.inl (hz hzG)
    · exact Or.inr hzG
  · rintro z ⟨hzG, hzO⟩
    rcases interior_subset hzO with h | h
    · exact h
    · exact absurd hzG h

omit [NormedSpace ℝ E] in
/-- A preconnected subset of `G` meeting a relatively open `C ⊆ G`, and meeting `cl C` only
inside `C`, lies in `C`. -/
theorem IsPreconnected.subset_of_relClopenG {G C s : Set E} (hs : IsPreconnected s)
    (hsG : s ⊆ G) (hCG : C ⊆ G) (hC : ∀ y ∈ C, C ∈ 𝓝[G] y) (hcl : s ∩ closure C ⊆ C)
    (hne : (s ∩ C).Nonempty) : s ⊆ C := by
  obtain ⟨O, hO, hCO⟩ := exists_open_eq_inter hCG hC
  have hsub : s ⊆ O ∪ (closure C)ᶜ := by
    intro z hz
    by_cases h : z ∈ closure C
    · have := hcl ⟨hz, h⟩
      rw [hCO] at this
      exact Or.inl this.2
    · exact Or.inr h
  have hne' : (s ∩ O).Nonempty := by
    obtain ⟨z, hzs, hzC⟩ := hne
    rw [hCO] at hzC
    exact ⟨z, hzs, hzC.2⟩
  by_contra hns
  have hne'' : (s ∩ (closure C)ᶜ).Nonempty := by
    rw [not_subset] at hns
    obtain ⟨z, hzs, hzC⟩ := hns
    exact ⟨z, hzs, fun h => hzC (hcl ⟨hzs, h⟩)⟩
  obtain ⟨z, hzs, hzO, hzC⟩ := hs O _ hO isClosed_closure.isOpen_compl hsub hne' hne''
  have : z ∈ C := by rw [hCO]; exact ⟨hsG hzs, hzO⟩
  exact hzC (subset_closure this)

omit [NormedSpace ℝ E] in
/-- A relative neighbourhood of a point in the closure of `Y ⊆ G` meets `Y`. -/
theorem inter_nonempty_of_mem_nhdsWithin {G U Y : Set E} {y : E} (hU : U ∈ 𝓝[G] y)
    (hY : y ∈ closure Y) (hYG : Y ⊆ G) : (U ∩ Y).Nonempty := by
  obtain ⟨u, hu, hyu, hut⟩ := mem_nhdsWithin.1 hU
  obtain ⟨w, hwu, hwY⟩ := mem_closure_iff.1 hY u hu hyu
  exact ⟨w, hut ⟨hwu, hYG hwY⟩, hwY⟩

omit [NormedSpace ℝ E] in
theorem comp_subset_G {G X : Set E} (x : E) : _root_.connectedComponentIn (G \ X) x ⊆ G :=
  (connectedComponentIn_subset _ _).trans diff_subset

omit [NormedSpace ℝ E] in
/-- For `C ⊆ G` closed in `E`: `cl C ⊆ C ∪ ∂C`. -/
theorem closure_subset_union_relFrontier {G C : Set E} (hG : IsClosed G) (hCG : C ⊆ G) :
    closure C ⊆ C ∪ relFrontier G C := by
  intro z hz
  by_cases h : z ∈ C
  · exact Or.inl h
  · exact Or.inr ⟨hz, subset_closure ⟨closure_minimal hCG hG hz, h⟩⟩

/-- Components of `G \ X` (`X` closed) are relatively open in `G`. -/
theorem IsPLGraph.compDiff_mem_nhdsWithin {G X : Set E} (hG : IsPLGraph G) (hX : IsClosed X)
    {x y : E} (hy : y ∈ _root_.connectedComponentIn (G \ X) x) :
    _root_.connectedComponentIn (G \ X) x ∈ 𝓝[G] y := by
  rw [diff_eq] at hy ⊢
  exact hG.connectedComponentIn_inter_mem_nhdsWithin hX.isOpen_compl hy

/-- The frontier of a component of `G \ X` (`X` closed) lies in `X`. -/
theorem IsPLGraph.relFrontier_comp_subset {G X : Set E} (hG : IsPLGraph G) (hX : IsClosed X)
    (x : E) : relFrontier G (_root_.connectedComponentIn (G \ X) x) ⊆ X := by
  rintro z ⟨hzC, hzD⟩
  by_contra hz
  have hzG : z ∈ G := closure_minimal (comp_subset_G x) hG.isCompact.isClosed hzC
  have hz' : z ∈ _root_.connectedComponentIn (G \ X) z := mem_connectedComponentIn ⟨hzG, hz⟩
  have hN := hG.compDiff_mem_nhdsWithin hX hz'
  obtain ⟨w, hwz, hwC⟩ := inter_nonempty_of_mem_nhdsWithin hN hzC (comp_subset_G x)
  have hCeq : _root_.connectedComponentIn (G \ X) x = _root_.connectedComponentIn (G \ X) z :=
    (connectedComponentIn_eq hwC).trans (connectedComponentIn_eq hwz).symm
  obtain ⟨v, hvz, hvG, hvC⟩ := inter_nonempty_of_mem_nhdsWithin hN hzD diff_subset
  rw [hCeq] at hvC
  exact hvC hvz

/-- The frontier of a component of `G \ A` lies in `∂A`. -/
theorem IsPLGraph.relFrontier_comp_subset_relFrontier {G A : Set E} (hG : IsPLGraph G)
    (hAc : IsClosed A) (x : E) :
    relFrontier G (_root_.connectedComponentIn (G \ A) x) ⊆ relFrontier G A := fun _ hz =>
  ⟨subset_closure (hG.relFrontier_comp_subset hAc x hz),
    closure_mono (connectedComponentIn_subset _ _) hz.1⟩

/-- In a connected PL graph, a component of `G \ X` (`X` closed, meeting `G`) has non-empty
frontier. -/
theorem IsPLGraph.relFrontier_comp_nonempty {G X : Set E} (hG : IsPLGraph G)
    (hconn : IsConnected G) (hX : IsClosed X) (hGX : (G ∩ X).Nonempty) {x : E}
    (hx : x ∈ G \ X) : (relFrontier G (_root_.connectedComponentIn (G \ X) x)).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hsub := IsPreconnected.subset_of_relClopenG hconn.isPreconnected subset_rfl (comp_subset_G x)
    (fun y hy => hG.compDiff_mem_nhdsWithin hX hy) ?_ ⟨x, hx.1, mem_connectedComponentIn hx⟩
  · obtain ⟨z, hzG, hzX⟩ := hGX
    exact (connectedComponentIn_subset _ _ (hsub hzG)).2 hzX
  · rintro z ⟨-, hz⟩
    rcases closure_subset_union_relFrontier hG.isCompact.isClosed (comp_subset_G x) hz with h' | h'
    · exact h'
    · rw [h] at h'
      exact absurd h' (Set.notMem_empty z)

/-- In a connected PL graph, the closure of a component of `G \ B` (`B ⊆ G` closed, non-empty)
meets `B`. -/
theorem IsPLGraph.closure_comp_inter_nonempty {G B : Set E} (hG : IsPLGraph G)
    (hconn : IsConnected G) (hBc : IsClosed B) (hBG : B ⊆ G) (hBne : B.Nonempty) {x : E}
    (hx : x ∈ G \ B) : (closure (_root_.connectedComponentIn (G \ B) x) ∩ B).Nonempty := by
  obtain ⟨b, hb⟩ := hBne
  obtain ⟨z, hz⟩ := hG.relFrontier_comp_nonempty hconn hBc ⟨b, hBG hb, hb⟩ hx
  exact ⟨z, hz.1, hG.relFrontier_comp_subset hBc x hz⟩

/-- A point in the closure of `Y ⊆ G \ A` lies in the closure of a component of `G \ A` through
a point of `Y` (finitely many components). -/
theorem IsPLGraph.mem_closure_comp {G X Y : Set E} (hG : IsPLGraph G) (hX : IsPLGraph X)
    (hXG : X ⊆ G) (hYX : Y ⊆ G \ X) {y : E} (hy : y ∈ closure Y) :
    ∃ x ∈ Y, y ∈ closure (_root_.connectedComponentIn (G \ X) x) := by
  have hfin := hG.finite_components_diff hX hXG finite_empty (empty_subset _)
  rw [union_empty] at hfin
  have h𝒞 : {C : Set E | ∃ x ∈ Y, C = _root_.connectedComponentIn (G \ X) x}.Finite :=
    hfin.subset fun C ⟨x, hx, hC⟩ => ⟨x, hYX hx, hC⟩
  have hYsub : Y ⊆ ⋃ C ∈ {C : Set E | ∃ x ∈ Y, C = _root_.connectedComponentIn (G \ X) x}, C :=
    fun z hz => mem_biUnion ⟨z, hz, rfl⟩ (mem_connectedComponentIn (hYX hz))
  have := closure_mono hYsub hy
  rw [h𝒞.closure_biUnion] at this
  obtain ⟨C, ⟨x, hx, rfl⟩, hyC⟩ := mem_iUnion₂.1 this
  exact ⟨x, hx, hyC⟩

/-- A component `C` of `G \ A` with `∂C ⊆ B ⊆ A` is the component of `G \ B` at the same point. -/
theorem IsPLGraph.comp_eq_of_relFrontier_subset {G A B : Set E} (hG : IsPLGraph G)
    (hAc : IsClosed A) (hBA : B ⊆ A) {x : E} (hx : x ∈ G \ A)
    (hfr : relFrontier G (_root_.connectedComponentIn (G \ A) x) ⊆ B) :
    _root_.connectedComponentIn (G \ B) x = _root_.connectedComponentIn (G \ A) x := by
  apply Subset.antisymm
  · refine IsPreconnected.subset_of_relClopenG isPreconnected_connectedComponentIn (comp_subset_G x)
      (comp_subset_G x) (fun y hy => hG.compDiff_mem_nhdsWithin hAc hy) ?_
      ⟨x, mem_connectedComponentIn ⟨hx.1, fun h => hx.2 (hBA h)⟩, mem_connectedComponentIn hx⟩
    rintro z ⟨hzK, hzcl⟩
    by_contra hzC
    have hzG := comp_subset_G x hzK
    have : z ∈ B := hfr ⟨hzcl, subset_closure ⟨hzG, hzC⟩⟩
    exact (connectedComponentIn_subset _ _ hzK).2 this
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx)
      ((connectedComponentIn_subset _ _).trans (diff_subset_diff_right hBA))

omit [NormedSpace ℝ E] in
/-- A component of `G \ B` lies in, or misses, a closed `X ⊆ G` with `∂X ⊆ B`. -/
theorem comp_subset_or_disjoint {G B X : Set E} (hBc : IsClosed B)
    (hXc : IsClosed X) (hXG : X ⊆ G) (hfr : relFrontier G X ⊆ B) (z : E) :
    _root_.connectedComponentIn (G \ B) z ⊆ X ∨ Disjoint (_root_.connectedComponentIn (G \ B) z) X := by
  by_cases h : (_root_.connectedComponentIn (G \ B) z ∩ X).Nonempty
  · left
    have hK : _root_.connectedComponentIn (G \ B) z ⊆ X \ B := by
      refine IsPreconnected.subset_of_relClopenG isPreconnected_connectedComponentIn (comp_subset_G z)
        (diff_subset.trans hXG) ?_ ?_ ?_
      · intro y hy
        refine mem_nhdsWithin.2 ⟨(closure (G \ X))ᶜ ∩ Bᶜ,
          isClosed_closure.isOpen_compl.inter hBc.isOpen_compl,
          ⟨fun hy' => hy.2 (hfr ⟨subset_closure hy.1, hy'⟩), hy.2⟩, ?_⟩
        rintro w ⟨⟨hw1, hw2⟩, hwG⟩
        refine ⟨?_, hw2⟩
        by_contra hwX
        exact hw1 (subset_closure ⟨hwG, hwX⟩)
      · rintro w ⟨hwK, hwcl⟩
        refine ⟨?_, (connectedComponentIn_subset _ _ hwK).2⟩
        have := closure_mono diff_subset hwcl
        rwa [hXc.closure_eq] at this
      · obtain ⟨w, hwK, hwX⟩ := h
        exact ⟨w, hwK, hwX, (connectedComponentIn_subset _ _ hwK).2⟩
    exact hK.trans diff_subset
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    exact not_nonempty_iff_eq_empty.1 h

/-! ### Sides -/

omit [NormedSpace ℝ E] in
theorem sideOf_subset {G B A : Set E} (hG : IsClosed G) : sideOf G B A ⊆ G :=
  closure_minimal (iUnion₂_subset fun x _ => iUnion_subset fun _ => comp_subset_G x) hG

omit [NormedSpace ℝ E] in
theorem isClosed_sideOf (G B A : Set E) : IsClosed (sideOf G B A) := isClosed_closure

omit [NormedSpace ℝ E] in
/-- A component of `G \ B` meeting `A` lies in `σ_B(A)`. -/
theorem comp_subset_sideOf {G B A : Set E} {x : E} (hx : x ∈ G \ B)
    (hA : (_root_.connectedComponentIn (G \ B) x ∩ A).Nonempty) :
    _root_.connectedComponentIn (G \ B) x ⊆ sideOf G B A :=
  fun _ hy => subset_closure (mem_iUnion₂.2 ⟨x, hx, mem_iUnion.2 ⟨hA, hy⟩⟩)

/-- A point of `σ_B(A)` outside `B` lies in a component of `G \ B` meeting `A`. -/
theorem IsPLGraph.comp_meets_of_mem_sideOf {G B A : Set E} (hG : IsPLGraph G) (hB : IsClosed B)
    {z : E} (hz : z ∈ sideOf G B A) (hzB : z ∉ B) :
    (_root_.connectedComponentIn (G \ B) z ∩ A).Nonempty := by
  have hzG := sideOf_subset hG.isCompact.isClosed hz
  have hz' : z ∈ _root_.connectedComponentIn (G \ B) z := mem_connectedComponentIn ⟨hzG, hzB⟩
  obtain ⟨w, hwz, hwU⟩ := inter_nonempty_of_mem_nhdsWithin (hG.compDiff_mem_nhdsWithin hB hz') hz
    (iUnion₂_subset fun x _ => iUnion_subset fun _ => comp_subset_G x)
  simp only [mem_iUnion] at hwU
  obtain ⟨x, -, hxA, hwx⟩ := hwU
  rwa [connectedComponentIn_eq hwz, ← connectedComponentIn_eq hwx]

/-- A component of `G \ B` missing `A` misses `σ_B(A)`. -/
theorem IsPLGraph.disjoint_comp_sideOf {G B A : Set E} (hG : IsPLGraph G) (hB : IsClosed B)
    {x : E} (hA : Disjoint (_root_.connectedComponentIn (G \ B) x) A) :
    Disjoint (_root_.connectedComponentIn (G \ B) x) (sideOf G B A) := by
  rw [Set.disjoint_left]
  intro z hzC hzS
  have hzB : z ∉ B := ((connectedComponentIn_subset _ _) hzC).2
  obtain ⟨w, hw1, hw2⟩ := hG.comp_meets_of_mem_sideOf hB hzS hzB
  rw [← connectedComponentIn_eq hzC] at hw1
  exact Set.disjoint_left.1 hA hw1 hw2

omit [NormedSpace ℝ E] in
theorem subset_sideOf_diff {G B A : Set E} (hAG : A ⊆ G) : A \ B ⊆ sideOf G B A := by
  rintro z ⟨hzA, hzB⟩
  exact comp_subset_sideOf ⟨hAG hzA, hzB⟩ ⟨z, mem_connectedComponentIn ⟨hAG hzA, hzB⟩, hzA⟩
    (mem_connectedComponentIn ⟨hAG hzA, hzB⟩)

/-- `A ⊆ σ_B(A)` for a PL graph `A ⊆ G` and finite `B` (no isolated points). -/
theorem IsPLGraph.subset_sideOf {G B A : Set E} (hA : IsPLGraph A) (hAG : A ⊆ G)
    (hB : B.Finite) : A ⊆ sideOf G B A := by
  intro a ha
  have := closure_mono (subset_sideOf_diff (B := B) hAG) (hA.mem_closure_diff_finite ha hB)
  rwa [(isClosed_sideOf G B A).closure_eq] at this

/-- `∂σ_B(A) ⊆ B`. -/
theorem IsPLGraph.relFrontier_sideOf_subset {G B A : Set E} (hG : IsPLGraph G)
    (hB : IsClosed B) : relFrontier G (sideOf G B A) ⊆ B := by
  rintro z ⟨hz, hzc⟩
  rw [(isClosed_sideOf G B A).closure_eq] at hz
  by_contra hzB
  have hzG := sideOf_subset hG.isCompact.isClosed hz
  have hK := comp_subset_sideOf ⟨hzG, hzB⟩ (hG.comp_meets_of_mem_sideOf hB hz hzB)
  obtain ⟨v, hvK, hvG, hvS⟩ := inter_nonempty_of_mem_nhdsWithin
    (hG.compDiff_mem_nhdsWithin hB (mem_connectedComponentIn ⟨hzG, hzB⟩)) hzc diff_subset
  exact hvS (hK hvK)

/-- If `A` has consistent complement relative to `B ⊆ A`, a component of `G \ A` meeting
`σ_B(A)` has frontier disjoint from `B`. -/
theorem IsPLGraph.disjoint_relFrontier_of_meets_sideOf {G A B : Set E} (hG : IsPLGraph G)
    (hAc : IsClosed A) (hBc : IsClosed B) (hBA : B ⊆ A) (hc : HasConsCompl G A B) {x : E}
    (hx : x ∈ G \ A) (hmeet : (_root_.connectedComponentIn (G \ A) x ∩ sideOf G B A).Nonempty) :
    Disjoint (relFrontier G (_root_.connectedComponentIn (G \ A) x)) B := by
  rcases hc x hx with h | h
  · exfalso
    have heq := hG.comp_eq_of_relFrontier_subset hAc hBA hx h
    have hdis : Disjoint (_root_.connectedComponentIn (G \ B) x) A := by
      rw [heq]
      exact Set.disjoint_left.2 fun z hz hzA => (connectedComponentIn_subset _ _ hz).2 hzA
    have := hG.disjoint_comp_sideOf hBc hdis
    rw [heq] at this
    obtain ⟨z, hz1, hz2⟩ := hmeet
    exact Set.disjoint_left.1 this hz1 hz2
  · exact h

/-- A point `x ∉ A` whose component of `G \ A` has a frontier point outside `B` (`B ⊆ A`)
lies in `σ_B(A)`. -/
theorem IsPLGraph.mem_sideOf_of_relFrontier {G A B : Set E} (hG : IsPLGraph G)
    (hAc : IsClosed A) (hBc : IsClosed B) (hBA : B ⊆ A) {x w : E} (hx : x ∈ G \ A)
    (hw : w ∈ relFrontier G (_root_.connectedComponentIn (G \ A) x)) (hwB : w ∉ B) :
    x ∈ sideOf G B A := by
  have hxB : x ∈ G \ B := ⟨hx.1, fun h => hx.2 (hBA h)⟩
  have hCK : _root_.connectedComponentIn (G \ A) x ⊆ _root_.connectedComponentIn (G \ B) x :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hx)
      ((connectedComponentIn_subset _ _).trans (diff_subset_diff_right hBA))
  have hwA : w ∈ A := hG.relFrontier_comp_subset hAc x hw
  have hwK : w ∈ _root_.connectedComponentIn (G \ B) x := by
    rcases closure_subset_union_relFrontier hG.isCompact.isClosed (comp_subset_G x)
      (closure_mono hCK hw.1) with h | h
    · exact h
    · exact absurd (hG.relFrontier_comp_subset hBc x h) hwB
  exact comp_subset_sideOf hxB ⟨w, hwK, hwA⟩ (mem_connectedComponentIn hxB)

/-- **The characterization of p. 190, existence part**, without connectedness and
non-emptiness: for `A ⊆ G` regular, `B ⊆ ∂A`, `A` with consistent complement relative to `B`,
`σ_B(A)` is a PL graph in `G` containing `A`, with `∂σ_B(A) = B` and `σ_B(A) ∩ V = A ∩ V` for a
neighbourhood `V` of `B`. -/
theorem IsPLGraph.sideOf_char_aux {G A B : Set E} (hG : IsPLGraph G) (hA : IsPLGraph A)
    (hAG : A ⊆ G) (hB : B ⊆ relFrontier G A) (hc : HasConsCompl G A B) :
    IsPLGraph (sideOf G B A) ∧ sideOf G B A ⊆ G ∧ A ⊆ sideOf G B A ∧
      relFrontier G (sideOf G B A) = B ∧ ∃ V ∈ 𝓝ˢ B, sideOf G B A ∩ V = A ∩ V := by
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hGc : IsClosed G := hG.isCompact.isClosed
  have hBfin : B.Finite := (hG.relFrontier_finite hA hAG).subset hB
  have hBA : B ⊆ A := fun b hb => by
    have := (hB hb).1
    rwa [hAc.closure_eq] at this
  have hBG : B ⊆ G := hBA.trans hAG
  have hAS : A ⊆ sideOf G B A := hA.subset_sideOf hAG hBfin
  have hbfr : ∀ b ∈ B, ∀ x, b ∈ closure (_root_.connectedComponentIn (G \ A) x) →
      b ∈ relFrontier G (_root_.connectedComponentIn (G \ A) x) := fun b hb x hbx =>
    ⟨hbx, subset_closure ⟨hBG hb, fun h => (connectedComponentIn_subset _ _ h).2 (hBA hb)⟩⟩
  refine ⟨?_, sideOf_subset hGc, hAS, ?_, ?_⟩
  · have hfin := hG.finite_components_diff isPLGraph_empty (empty_subset G) hBfin hBG
    rw [empty_union] at hfin
    have h𝒞 : {C : Set E | ∃ x ∈ G \ B, (_root_.connectedComponentIn (G \ B) x ∩ A).Nonempty ∧
        C = _root_.connectedComponentIn (G \ B) x}.Finite :=
      hfin.subset fun C ⟨x, hx, _, hC⟩ => ⟨x, hx, hC⟩
    have hU : (⋃ x ∈ G \ B, ⋃ (_ : (_root_.connectedComponentIn (G \ B) x ∩ A).Nonempty),
        _root_.connectedComponentIn (G \ B) x) = ⋃ C ∈ {C : Set E | ∃ x ∈ G \ B,
          (_root_.connectedComponentIn (G \ B) x ∩ A).Nonempty ∧
          C = _root_.connectedComponentIn (G \ B) x}, C := by
      ext z
      simp only [mem_iUnion, mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨x, hx, hxA, hz⟩
        exact ⟨_, ⟨x, hx, hxA, rfl⟩, hz⟩
      · rintro ⟨_, ⟨x, hx, hxA, rfl⟩, hz⟩
        exact ⟨x, hx, hxA, hz⟩
    unfold sideOf
    rw [hU, h𝒞.closure_biUnion]
    refine IsPLGraph.biUnion_finite h𝒞 ?_
    rintro _ ⟨x, -, -, rfl⟩
    have := hG.closure_comp_diff isPLGraph_empty (empty_subset G) hBfin hBG x
    rwa [empty_union] at this
  · apply Subset.antisymm (hG.relFrontier_sideOf_subset hBfin.isClosed)
    intro b hb
    refine ⟨subset_closure (hAS (hBA hb)), ?_⟩
    obtain ⟨x, hx, hbx⟩ := hG.mem_closure_comp hA hAG subset_rfl (hB hb).2
    have hnot : ¬ (_root_.connectedComponentIn (G \ A) x ∩ sideOf G B A).Nonempty := fun hm =>
      Set.disjoint_left.1 (hG.disjoint_relFrontier_of_meets_sideOf hAc hBfin.isClosed hBA hc hx
        hm) (hbfr b hb x hbx) hb
    refine closure_mono ?_ hbx
    intro z hz
    exact ⟨comp_subset_G x hz, fun hzS => hnot ⟨z, hz, hzS⟩⟩
  · have hfin := hG.finite_components_diff hA hAG finite_empty (empty_subset G)
    rw [union_empty] at hfin
    have h𝒟 : {C : Set E | ∃ x ∈ G \ A,
        Disjoint (relFrontier G (_root_.connectedComponentIn (G \ A) x)) B ∧
        C = _root_.connectedComponentIn (G \ A) x}.Finite :=
      hfin.subset fun C ⟨x, hx, _, hC⟩ => ⟨x, hx, hC⟩
    have hclosed := h𝒟.isClosed_biUnion (f := closure) fun _ _ => isClosed_closure
    refine ⟨_, hclosed.isOpen_compl.mem_nhdsSet.2 ?_, ?_⟩
    · intro b hb hbU
      obtain ⟨_, ⟨x, -, hdis, rfl⟩, hbx⟩ := mem_iUnion₂.1 hbU
      exact Set.disjoint_left.1 hdis (hbfr b hb x hbx) hb
    · apply Subset.antisymm
      · rintro z ⟨hzS, hzV⟩
        refine ⟨?_, hzV⟩
        by_contra hzA
        have hzGA : z ∈ G \ A := ⟨sideOf_subset hGc hzS, hzA⟩
        have hdis := hG.disjoint_relFrontier_of_meets_sideOf hAc hBfin.isClosed hBA hc hzGA
          ⟨z, mem_connectedComponentIn hzGA, hzS⟩
        exact hzV (mem_iUnion₂.2 ⟨_, ⟨z, hzGA, hdis, rfl⟩,
          subset_closure (mem_connectedComponentIn hzGA)⟩)
      · exact inter_subset_inter_left _ hAS

end SidesLib

end HPC.HO16
