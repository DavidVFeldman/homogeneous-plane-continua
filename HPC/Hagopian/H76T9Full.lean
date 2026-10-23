import HPC.Hagopian.H76Thin

/-!
# Batch 165, item C: property (D) over the thin strip (T8) and T9 in full

* `strip_in_links`: a thin enough closed collar strip over `[3/22, 19/22]` lies in `π[St L]`, and
  every point of `M` over it lies in one of `L₂, …, L₁₀`, with the abscissa bounds of link control.
* `closure_disjoint_E_of_above`: a connected subset of `M` over the open upper strip has closure
  disjoint from `E` (`no_hair_aux`; commission 165 §2, item C).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section T9F

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Property (D) over a thin strip** (commission 165 §2, items B, C). -/
theorem strip_in_links (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLo : ∀ j, IsOpen (L j))
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j) {η : ℝ} (hη : 0 < η)
    (hηε : η ≤ ε₁) :
    ∃ c > 0, c ≤ 1 ∧ F '' (Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c) ⊆ π '' (⋃ j, L j) ∧
      ∀ x : M, π (x : Pt) ∈ F '' (Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c) →
        ∃ z ∈ Icc (3 / 22) (19 / 22) ×ˢ Icc 0 c, π (x : Pt) = F z ∧
          (∃ j : Fin 11, (x : Pt) ∈ L j) ∧
          ∀ j : Fin 11, (x : Pt) ∈ L j → 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 9 ∧
            ((j : ℝ) - 1) / 11 - η < z.1 ∧ z.1 < ((j : ℝ) + 2) / 11 + η := by
  obtain ⟨c₁, hc₁, hc₁1, hU, -⟩ := hagopian76_T7_aux hX hi hE hπ hπS hγπ hF
    (by norm_num : (0 : ℝ) < 3 / 22) (by norm_num : (3 / 22 : ℝ) < 19 / 22)
    (by norm_num : (19 / 22 : ℝ) < 1) (isOpen_iUnion hLo) hEL
  obtain ⟨c₂, hc₂, hc₂1, hlink⟩ := link_control_aux hE he hend hπ.continuous hπS hγπ hF hLG hη hηε
  set c := min c₁ c₂ with hc
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hcc₂ : c ≤ c₂ := min_le_right _ _
  have hsub : Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c ⊆ Icc (3 / 22 : ℝ) (19 / 22) ×ˢ Icc 0 c₁ :=
    Set.prod_mono subset_rfl (Icc_subset_Icc le_rfl hcc₁)
  refine ⟨c, lt_min hc₁ hc₂, hcc₁.trans hc₁1, (image_mono hsub).trans hU, fun x hx => ?_⟩
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨z, hz, hxz.symm, ?_, fun j hj => ?_⟩
  · obtain ⟨u, hu, hux⟩ := hU (image_mono hsub ⟨z, hz, hxz⟩)
    by_cases hxE : (x : Pt) ∈ toPt E
    · exact mem_iUnion.1 (hEL hxE)
    · have h := (hπS u x).1 hux
      change u ∈ HPC.Moore.elt (layerSetoid k) (x : Pt) at h
      rw [elt_layerSetoid_of_notMem k hxE, mem_singleton_iff] at h
      rw [← h]; exact mem_iUnion.1 hu
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    exact hlink x z ⟨⟨h1, h2⟩, by linarith, h4.trans hcc₂⟩ hxz.symm j hj

/-- **No connected set over the open strip has closure meeting `E`** (commission 165 §2, item C:
"`Cl B ∩ E = ∅` for every component `B` of `M ∩ π⁻¹[D]`"). -/
theorem closure_disjoint_E_of_above (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    (hπc : Continuous π) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hb : b < 1) (hc1 : c ≤ 1) {B : Set M} (hBc : IsPreconnected B)
    (hB : ∀ x ∈ B, π (x : Pt) ∈ F '' (Icc a b ×ˢ Ioc 0 c)) : Disjoint (closure B) E := by
  rcases B.eq_empty_or_nonempty with hB0 | hBne
  · rw [hB0, closure_empty]; exact empty_disjoint _
  obtain ⟨hFemb, hF0, -⟩ := hF
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hFemb.continuous
  have hFinj : InjOn F R1 := fun z hz w hw h =>
    congrArg Subtype.val (hFemb.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h)
  have hsub : Icc a b ×ˢ Icc 0 c ⊆ R1 :=
    fun z ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hcomp : IsCompact (F '' (Icc a b ×ˢ Icc 0 c)) :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn (hFc.mono hsub)
  have hcont : Continuous (fun y : M => π (y : Pt)) := hπc.comp continuous_subtype_val
  have hclB : ∀ x ∈ closure B, π (x : Pt) ∈ F '' (Icc a b ×ˢ Icc 0 c) := by
    intro x hx
    have h1 := image_closure_subset_closure_image hcont ⟨x, hx, rfl⟩
    have h2 : (fun y : M => π (y : Pt)) '' B ⊆ F '' (Icc a b ×ˢ Icc 0 c) := by
      rintro _ ⟨y, hy, rfl⟩
      exact image_mono (Set.prod_mono subset_rfl Ioc_subset_Icc_self) (hB y hy)
    exact closure_minimal h2 hcomp.isClosed h1
  have hQ : Fold.Q78.IsContinuum (closure B) :=
    ⟨isClosed_closure.isCompact, hBne.mono subset_closure, hBc.closure⟩
  have hend : ∀ s : unitInterval, ((s : ℝ) < a ∨ b < (s : ℝ)) →
      Disjoint (closure B) (layer k s) := by
    intro s hs
    rw [disjoint_left]
    intro x hx hxs
    obtain ⟨z, hz, hzx⟩ := hclB x hx
    have hπx : π (x : Pt) = γ s := hγπ s x ⟨x, hxs, rfl⟩
    have hzs : z = ((s : ℝ), 0) := hFinj (hsub hz) ⟨⟨s.2.1, s.2.2⟩, by norm_num, by norm_num⟩
      (by rw [hzx, hπx, hF0])
    have h1 := hz.1
    rw [hzs] at h1
    rcases hs with hs | hs
    · exact absurd h1.1 (not_le.2 hs)
    · exact absurd h1.2 (not_le.2 hs)
  rw [disjoint_left]
  intro x₀ hx₀ hx₀E
  have hsubE := no_hair_aux hX hi hE hQ ⟨x₀, hx₀, hx₀E⟩
    (hend 0 (Or.inl (by show (0 : ℝ) < a; exact ha)))
    (hend 1 (Or.inr (by show b < (1 : ℝ); exact hb)))
  obtain ⟨x, hxB⟩ := hBne
  have hxE := hsubE (subset_closure hxB)
  obtain ⟨z, ⟨⟨h1, h2⟩, h3, h4⟩, hzx⟩ := hB x hxB
  set e : E := ⟨x, hxE⟩
  have hπx : π (x : Pt) = γ (k e) := hγπ (k e) x ⟨x, ⟨e, rfl, rfl⟩, rfl⟩
  have := hFinj (hsub ⟨⟨h1, h2⟩, h3.le, h4⟩)
    (⟨⟨(k e).2.1, (k e).2.2⟩, by norm_num, by norm_num⟩ : (((k e : unitInterval) : ℝ), (0 : ℝ)) ∈ R1)
    (by rw [hzx, hπx, hF0])
  have h5 := congrArg Prod.snd this
  simp only at h5
  linarith

/-- **T11, with `K` replaced by the whole of `π⁻¹[D ∩ ⟨p₃, q₃⟩]`** (commission 165 §2, item D). Over
a thin strip over `[3/22, 19/22]`, no connected set that lies over the open strip and misses the
preimage of the vertical over `p₃ = 11/22` contains both a point of `M ∩ L₂` and a point of
`M ∩ L₁₀` (Lean indices `1` and `9`). Every `π⁻¹[D]` with `D` in the open strip is covered. -/
theorem T11_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε₁ : ℝ} (he : IsEps1 k ε₁)
    (hend : EndCtl k ε₁) {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {L : Fin 11 → Set Pt} (hLo : ∀ j, IsOpen (L j))
    (hEL : toPt E ⊆ ⋃ j, L j) (hLG : ∀ j, L j ⊆ chainG k ε₁ j) :
    ∃ c > 0, c ≤ 1 ∧ ∀ S : Set Pt, IsPreconnected S →
      S ⊆ π ⁻¹' (F '' (Ioo (3 / 22) (19 / 22) ×ˢ Ioo 0 c)) →
      Disjoint S (π ⁻¹' (F '' (({11 / 22} : Set ℝ) ×ˢ Ioo 0 c))) →
      ∀ x ∈ S, ∀ y ∈ S, x ∈ M → y ∈ M → x ∈ L 1 → y ∈ L 9 → False := by
  have hη : 0 < min ε₁ (1 / 22) := lt_min he.pos (by norm_num)
  obtain ⟨c, hc, hc1, -, hlink⟩ := strip_in_links hX hi hE he hend hπ hπS hγπ hF hLo hEL hLG hη
    (min_le_left _ _)
  have hη22 : min ε₁ (1 / 22) ≤ 1 / 22 := min_le_right _ _
  refine ⟨c, hc, hc1, fun S hS hSO hSv x hx y hy hxM hyM hxL hyL => ?_⟩
  have hFinj : InjOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := fun z hz w hw h =>
    congrArg Subtype.val (hF.1.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h)
  have hR : ∀ {z : ℝ × ℝ}, z ∈ Ioo (3 / 22 : ℝ) (19 / 22) ×ˢ Ioo 0 c →
      z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun ⟨⟨h1, h2⟩, h3, h4⟩ =>
    ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  set Vl := π ⁻¹' (F '' (Ioo (3 / 22 : ℝ) (11 / 22) ×ˢ Ioo 0 c)) with hVld
  set Vr := π ⁻¹' (F '' (Ioo (11 / 22 : ℝ) (19 / 22) ×ˢ Ioo 0 c)) with hVrd
  have hVl : IsOpen Vl := (hF.isOpen_image (isOpen_Ioo.prod isOpen_Ioo)
    (fun z ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)).preimage
    hπ.continuous
  have hVr : IsOpen Vr := (hF.isOpen_image (isOpen_Ioo.prod isOpen_Ioo)
    (fun z ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)).preimage
    hπ.continuous
  have hcover : S ⊆ Vl ∪ Vr := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := hSO hp
    rcases lt_trichotomy z.1 (11 / 22) with h | h | h
    · exact Or.inl ⟨z, ⟨⟨hz.1.1, h⟩, hz.2⟩, hpz⟩
    · exact absurd ⟨z, ⟨h, hz.2⟩, hpz⟩ (disjoint_left.1 hSv hp)
    · exact Or.inr ⟨z, ⟨⟨h, hz.1.2⟩, hz.2⟩, hpz⟩
  have hlr : ∀ p, p ∈ Vl → p ∈ Vr → False := by
    rintro p ⟨z, hz, hpz⟩ ⟨w, hw, hpw⟩
    have hz' : z ∈ Ioo (3 / 22 : ℝ) (19 / 22) ×ˢ Ioo 0 c :=
      ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩
    have hw' : w ∈ Ioo (3 / 22 : ℝ) (19 / 22) ×ˢ Ioo 0 c :=
      ⟨⟨by linarith [hw.1.1], hw.1.2⟩, hw.2⟩
    have := hFinj (hR hz') (hR hw') (hpz.trans hpw.symm)
    rw [this] at hz
    linarith [hz.1.2, hw.1.1]
  have hdisj : S ∩ (Vl ∩ Vr) = ∅ :=
    eq_empty_iff_forall_notMem.2 fun p ⟨_, h1, h2⟩ => hlr p h1 h2
  -- the abscissa of a point of `M`
  have habs : ∀ p ∈ S, ∀ hp : p ∈ M, ∀ j : Fin 11, p ∈ L j → ∃ z ∈ Ioo (3 / 22 : ℝ) (19 / 22) ×ˢ
      Ioo 0 c, π p = F z ∧ ((j : ℝ) - 1) / 11 - min ε₁ (1 / 22) < z.1 ∧
        z.1 < ((j : ℝ) + 2) / 11 + min ε₁ (1 / 22) := by
    intro p hpS hp j hpj
    obtain ⟨z, hz, hpz⟩ := hSO hpS
    obtain ⟨z', hz', hpz', -, hb⟩ := hlink ⟨p, hp⟩
      ⟨z, ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩, hpz⟩
    obtain ⟨-, -, h1, h2⟩ := hb j hpj
    have hz'R : z' ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
      obtain ⟨⟨h3, h4⟩, h5, h6⟩ := hz'
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    have : z' = z := hFinj hz'R (hR hz) (hpz'.symm.trans hpz.symm)
    rw [this] at h1 h2
    exact ⟨z, hz, hpz.symm, h1, h2⟩
  have hxl : x ∈ Vl := by
    obtain ⟨z, hz, hxz, -, h2⟩ := habs x hx hxM 1 hxL
    have h1' : ((1 : Fin 11) : ℝ) = 1 := by norm_num
    rw [h1'] at h2
    exact ⟨z, ⟨⟨hz.1.1, by linarith⟩, hz.2⟩, hxz.symm⟩
  have hyr : y ∈ Vr := by
    obtain ⟨z, hz, hyz, h1, -⟩ := habs y hy hyM 9 hyL
    have h9' : ((9 : Fin 11) : ℝ) = 9 := by norm_num
    rw [h9'] at h1
    exact ⟨z, ⟨⟨by linarith, hz.1.2⟩, hz.2⟩, hyz.symm⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 hS Vl Vr hVl hVr hcover hdisj with h | h
  · exact hlr y (h hy) hyr
  · exact hlr x hxl (h hx)

end T9F

end HPC.Hagopian
