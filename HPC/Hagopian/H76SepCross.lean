import HPC.Hagopian.H76OrderConcrete
import HPC.Hagopian.Hagopian76V

/-!
# Batch 178, §4.C (conditional form): `SepByCrossing` from the strand separation lemma

`sepByCrossing_of_sigma_pieces`: in the concrete frame (`lowFrame`, the low vertical over `t₀`),
if every component of `G ∩ π⁻¹[D]` through a point of the vertical is a crossing piece (the part of
`InnerComponentsCross` that the argument uses), and `p`, `q` lie on crossing pieces missing `G`
(equal or disjoint), then `SepByCrossing G … p q` holds. This is the corollary of SSL
(`VFrame.sepByCrossing_of_inner_crossing`) transported to the crossing components of batch 176
(`IsCrossingComponent`, components in `M`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones HPC.Moore.Gen

section SepCross

variable {M : Set Pt}

/-- Components in `M` and in the plane agree (for any `S ⊆ M`). -/
theorem image_val_connectedComponentIn (S : Set M) (y : M) :
    Subtype.val '' connectedComponentIn S y = connectedComponentIn (Subtype.val '' S) (y : Pt) := by
  by_cases hy : y ∈ S
  · refine (continuous_subtype_val.image_connectedComponentIn_subset hy).antisymm ?_
    set C := connectedComponentIn (Subtype.val '' S) (y : Pt) with hC
    have hCS : C ⊆ Subtype.val '' S := connectedComponentIn_subset _ _
    have hCM : C ⊆ M := fun z hz => by
      obtain ⟨m, -, rfl⟩ := hCS hz; exact m.2
    set X : Set M := Subtype.val ⁻¹' C with hX
    have himg : Subtype.val '' X = C := by
      rw [hX, Subtype.image_preimage_coe, inter_eq_right.2 hCM]
    have hXc : IsPreconnected X := by
      rw [← IsInducing.subtypeVal.isPreconnected_image, himg]
      exact isPreconnected_connectedComponentIn
    have hXS : X ⊆ S := fun m hm => by
      obtain ⟨m', hm', hmm'⟩ := hCS hm
      rwa [← Subtype.ext hmm']
    have := hXc.subset_connectedComponentIn
      (show y ∈ X from mem_connectedComponentIn ⟨y, hy, rfl⟩) hXS
    rw [← himg]
    exact image_mono this
  · rw [connectedComponentIn_eq_empty hy, image_empty, connectedComponentIn_eq_empty]
    rintro ⟨m, hm, hmy⟩
    exact hy (Subtype.ext hmy ▸ hm)

theorem toPt_crossSet (G : Set M) (π : Pt → Pt) (F : ℝ × ℝ → Pt) (D' : Set (ℝ × ℝ)) :
    toPt (crossSet G π F D') = toPt G ∩ π ⁻¹' (F '' D') := by
  ext z
  constructor
  · rintro ⟨m, ⟨hmG, hm⟩, rfl⟩; exact ⟨⟨m, hmG, rfl⟩, hm⟩
  · rintro ⟨⟨m, hmG, rfl⟩, hm⟩; exact ⟨m, ⟨hmG, hm⟩, rfl⟩

variable [CompactSpace M]

/-- **`SepByCrossing` from SSL** (commission 178 §4.C, conditional form). -/
theorem sepByCrossing_of_sigma_pieces {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {c₁ : ℝ} (hc1 : c₁ ≤ 1)
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hIs : (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∩
      (({3 / 22, 19 / 22} : Set ℝ) ×ˢ Icc 0 c₁) = {(3 / 22, r₂), (19 / 22, s₂)})
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c₁)
    (hDf : frontier D' = (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂) ∪
        Icc (3 / 22) (19 / 22) ×ˢ {0} ∪ ({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂ ∪
        ({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂)
    {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo (3 / 22) (19 / 22)) (hw₂ : w₂ ∈ Ioc 0 c₁)
    (hFw : F (x₀, w₂) ∈ I₂)
    (hseg : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hOo : IsOpen (π ⁻¹' (F '' D'))) (hOc : IsPreconnected (π ⁻¹' (F '' D')))
    (hsub : ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D') (hπinj : InjOn π (π ⁻¹' (F '' D')))
    (hsurj : Function.Surjective π)
    (hsegc : ∀ J : Set ℝ, IsPreconnected J →
      IsPreconnected (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ (J ∩ Ioo 0 w₂)))))
    {G : Set M} (hG : IsClosed G)
    (hσ : ∀ z ∈ toPt G ∩ π ⁻¹' (F '' D'), π z ∈ F '' (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) →
      IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂
        (connectedComponentIn (toPt G ∩ π ⁻¹' (F '' D')) z))
    {X Y : Set Pt} {p q : Pt}
    (hX : IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ X)
    (hY : IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ Y)
    (hXY : X = Y ∨ Disjoint X Y) (hXG : Disjoint X (toPt G)) (hYG : Disjoint Y (toPt G))
    (hp : p ∈ X) (hq : q ∈ Y) :
    SepByCrossing G π F c₁ D' (π ⁻¹' (F '' D')) p q := by
  have hr₂ : r₂ ≤ c₁ := (hI.left_mem.1.2).2
  have hs₂ : s₂ ≤ c₁ := (hI.right_mem.1.2).2
  set V := lowFrame π F D' x₀ w₂ hOo hOc hsub hπinj hsurj hsegc with hV
  have hpiece := fun {Z : Set Pt} (hZ : IsCrossingPiece π F D' (3 / 22) (19 / 22) r₂ s₂ I₂ Z) =>
    isPiece_of_isCrossingPiece hπc hF (by norm_num) (by norm_num) (by norm_num) hc1 hI hIs hDo hDR
      hDf hx₀ hw₂ hFw hseg hOo hOc hsub hπinj hsurj hsegc hZ
  intro hsep
  have hZ : ∀ z ∈ toPt G ∩ V.O, (∃ v, V.lev z v) →
      V.IsPiece (connectedComponentIn (toPt G ∩ V.O) z) := by
    rintro z hz ⟨v, hv, hπz⟩
    exact hpiece (hσ z hz ⟨(x₀, v), ⟨rfl, hv⟩, hπz.symm⟩)
  obtain ⟨z, ⟨hzG, hzO⟩, ⟨v, hv, hπz⟩, -, hW⟩ := V.sepByCrossing_of_inner_crossing hZ
    (hpiece hX) (hpiece hY) hXY hXG hYG hp hq hsep
  have hMc : IsClosed M := (isCompact_iff_compactSpace.2 ‹CompactSpace M›).isClosed
  have hemb : IsClosedEmbedding (Subtype.val : M → Pt) := hMc.isClosedEmbedding_subtypeVal
  obtain ⟨m, hmG, rfl⟩ := hzG
  set C := connectedComponentIn (crossSet G π F D') m with hCdef
  have hWC : connectedComponentIn (toPt G ∩ V.O) (m : Pt) = toPt C := by
    show _ = Subtype.val '' connectedComponentIn (crossSet G π F D') m
    rw [image_val_connectedComponentIn]
    exact congrArg (fun S => connectedComponentIn S (m : Pt)) (toPt_crossSet G π F D').symm
  have hclW : closure (connectedComponentIn (toPt G ∩ V.O) (m : Pt)) = toPt (closure C) := by
    rw [hWC]; exact hemb.closure_image_eq C
  have hmc : m ∈ crossSet G π F D' := ⟨hmG, hzO⟩
  have hside : ∀ {a t : ℝ}, t ≤ c₁ →
      (closure (connectedComponentIn (toPt G ∩ V.O) (m : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 t))).Nonempty →
      ∃ x ∈ closure C, π (x : Pt) ∈ F '' (({a} : Set ℝ) ×ˢ Icc 0 c₁) := by
    rintro a t ht ⟨P, hPcl, w, ⟨hw1, hw2⟩, hFw'⟩
    rw [hclW] at hPcl
    obtain ⟨x, hx, rfl⟩ := hPcl
    exact ⟨x, hx, w, ⟨hw1, hw2.1.le, hw2.2.le.trans ht⟩, hFw'⟩
  have hcp := hσ (m : Pt) ⟨⟨m, hmG, rfl⟩, hzO⟩ ⟨(x₀, v), ⟨rfl, hv⟩, hπz.symm⟩
  have hCcross : IsCrossingComponent G π F c₁ D' C :=
    ⟨⟨m, hmc, rfl⟩, hside hr₂ hcp.left, hside hs₂ hcp.right⟩
  have hUG : (⋃ C ∈ {C : Set M | IsCrossingComponent G π F c₁ D' C}, toPt (closure C)) ⊆
      toPt G := by
    simp only [mem_setOf_eq, iUnion_subset_iff]
    intro C' hC'
    obtain ⟨⟨z', -, rfl⟩, -, -⟩ := hC'
    exact image_mono (closure_minimal ((connectedComponentIn_subset _ _).trans
      fun m' hm' => hm'.1) hG)
  refine hW.mono ?_ (fun h => hsep.1.2 (hUG h)) (fun h => hsep.2.1.2 (hUG h))
  rw [hclW]
  exact subset_biUnion_of_mem (u := fun C => toPt (closure C)) hCcross

end SepCross

end HPC.Hagopian
