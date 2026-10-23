import HPC.Hagopian.Hagopian76K
import HPC.Hagopian.Hagopian76J

/-!
# Batch 167, item A: crossing translates (supporting file)

* `exists_mem_closure_component_notMem`: boundary bumping for components of an open subset of a
  continuum (the closure of the component through `p` leaves the open set).
* `isOpen_collar_image`: the collar maps open subsets of the open rectangle onto open sets.
* `collar_uniform`: points of the plane near `F(t, 0)`, `t ∈ [a', b'] ⊆ (0, 1)`, are `F`-images of
  points of the open rectangle near `(t, 0)`, uniformly in `t`.
* `pi_near_collar`: the same for `π`-images of points of `M` near the layers over `[a', b']`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **Boundary bumping for components.** If `Z` is a continuum, `O` is open, `p ∈ Z ∩ O` and
`Z ⊄ O`, then the closure of the component of `Z ∩ O` through `p` contains a point of `Z − O`. -/
theorem exists_mem_closure_component_notMem {X : Type*} [MetricSpace X] {Z O : Set X}
    (hZ : IsCompact Z) (hZc : IsPreconnected Z) (hO : IsOpen O) {p : X} (hpZ : p ∈ Z)
    (hpO : p ∈ O) (hZO : ¬ Z ⊆ O) :
    ∃ q ∈ Z, q ∉ O ∧ q ∈ closure (connectedComponentIn (Z ∩ O) p) := by
  set C := connectedComponentIn (Z ∩ O) p with hCdef
  have hCZ : C ⊆ Z := (connectedComponentIn_subset _ _).trans inter_subset_left
  have hKZ : closure C ⊆ Z := closure_minimal hCZ hZ.isClosed
  have hKc : IsCompact (closure C) := hZ.of_isClosed_subset isClosed_closure hKZ
  by_contra hcon
  push_neg at hcon
  have hKO : closure C ⊆ O := fun q hq => by
    by_contra h
    exact hcon q (hKZ hq) h hq
  obtain ⟨w, hwZ, hwO⟩ := not_subset.1 hZO
  have hOc_ne : (Oᶜ).Nonempty := ⟨w, hwO⟩
  set g : X → ℝ := fun z => infDist z Oᶜ with hgdef
  have hgc : Continuous g := continuous_infDist_pt _
  have hpos : ∀ z ∈ closure C, 0 < g z := fun z hz =>
    (hO.isClosed_compl.notMem_iff_infDist_pos hOc_ne).1 (fun h => h (hKO hz))
  have hpC : p ∈ closure C := subset_closure (mem_connectedComponentIn ⟨hpZ, hpO⟩)
  obtain ⟨z₀, hz₀, hmin⟩ := hKc.exists_isMinOn ⟨p, hpC⟩ hgc.continuousOn
  have hr : 0 < g z₀ := hpos z₀ hz₀
  set F := Z ∩ {z | g z₀ / 2 ≤ g z} with hFdef
  have hFc : IsCompact F := hZ.inter_right (isClosed_le continuous_const hgc)
  have hFZ : F ⊆ Z := inter_subset_left
  have hg0 : ∀ z, z ∉ O → g z = 0 := fun z hz => infDist_zero_of_mem hz
  have hwF : w ∉ F := fun h => by
    have h1 := h.2
    simp only [mem_setOf_eq] at h1
    rw [hg0 w hwO] at h1
    linarith
  have hFne : F ≠ Z := fun h => hwF (h ▸ hwZ)
  have hpF : p ∈ F := ⟨hpZ, by
    have := isMinOn_iff.1 hmin p hpC
    show g z₀ / 2 ≤ g p
    linarith⟩
  obtain ⟨K, -, hKconn, hKF, hpK, v, hvK, hvcl⟩ :=
    exists_continuum_bump_compact hZc hFc hFZ hFne hpF
  have hKO' : K ⊆ Z ∩ O := fun z hz => by
    refine ⟨(hKF hz).1, ?_⟩
    by_contra hzO
    have h1 := (hKF hz).2
    simp only [mem_setOf_eq] at h1
    rw [hg0 z hzO] at h1
    linarith
  have hKC : K ⊆ C := hKconn.isPreconnected.subset_connectedComponentIn hpK hKO'
  have hvC : v ∈ closure C := subset_closure (hKC hvK)
  have h1 : g v ≤ g z₀ / 2 := by
    have hsub : closure (Z \ F) ⊆ {z | g z ≤ g z₀ / 2} := by
      refine closure_minimal (fun z hz => ?_) (isClosed_le hgc continuous_const)
      have : ¬ (g z₀ / 2 ≤ g z) := fun h => hz.2 ⟨hz.1, h⟩
      show g z ≤ g z₀ / 2
      linarith
    exact hsub hvcl
  have h2 := isMinOn_iff.1 hmin v hvC
  linarith

/-- Intervals of parameters are preconnected. -/
theorem isPreconnected_interval_set (a b : ℝ) :
    IsPreconnected {t : unitInterval | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b} :=
  Set.OrdConnected.isPreconnected ⟨fun _ hx _ hy _ hz =>
    ⟨hx.1.trans (Subtype.coe_le_coe.2 hz.1), (Subtype.coe_le_coe.2 hz.2).trans hy.2⟩⟩

/-- The collar is injective on the closed rectangle. -/
theorem collar_injOn {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {z w : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
    (h : F z = F w) : z = w := by
  have := hF.1.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h
  exact congrArg Subtype.val this

theorem openRect_subset_rect :
    Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
  prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

/-- **The collar maps open subsets of the open rectangle onto open sets.** -/
theorem isOpen_collar_image {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hVR : V ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) :
    IsOpen (F '' V) := by
  obtain ⟨hFemb, -, hFo⟩ := hF
  set R := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  have hU : IsOpen ((Subtype.val : R → ℝ × ℝ) ⁻¹' V) := hV.preimage continuous_subtype_val
  obtain ⟨W, hW, hWU⟩ := hFemb.isInducing.isOpen_iff.1 hU
  have : F '' V = W ∩ F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, z, hVR hz, rfl⟩
      have : (⟨z, openRect_subset_rect (hVR hz)⟩ : R) ∈ (R.restrict F) ⁻¹' W := by
        rw [hWU]; exact hz
      exact this
    · rintro ⟨hpW, z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      have : (⟨z, openRect_subset_rect hz⟩ : R) ∈ (R.restrict F) ⁻¹' W := hpW
      rw [hWU] at this
      exact this
  rw [this]
  exact hW.inter hFo

/-- **Uniform collar coordinates near the axis.** -/
theorem collar_uniform {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a' b' : ℝ} (ha' : 0 < a') (hb' : b' < 1) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ t ∈ Icc a' b', ∀ w : Pt, dist w (F (t, 0)) < ρ →
      ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1, F z = w ∧ dist z (t, 0) < η := by
  by_cases hab : a' ≤ b'
  swap
  · exact ⟨1, one_pos, fun t ht => absurd (ht.1.trans ht.2) hab⟩
  set R := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hRdef
  have hFemb := hF.1
  haveI : CompactSpace R := isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  set e := hFemb.toHomeomorph with hedef
  haveI : CompactSpace (range (R.restrict F)) :=
    isCompact_iff_compactSpace.1 (isCompact_range hFemb.continuous)
  have huc := CompactSpace.uniformContinuous_of_continuous e.symm.continuous
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := Metric.uniformContinuous_iff.1 huc η hη
  set η₀ := min a' (1 - b') / 2 with hη₀
  have hη₀0 : 0 < η₀ := by
    have : 0 < min a' (1 - b') := lt_min ha' (by linarith)
    positivity
  have hη₀a : η₀ < a' := by
    have := min_le_left a' (1 - b'); linarith
  have hη₀b : η₀ < 1 - b' := by
    have := min_le_right a' (1 - b'); linarith
  set V := Ioo (a' - η₀) (b' + η₀) ×ˢ Ioo (-η₀) η₀ with hVdef
  have hVR : V ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := fun z ⟨⟨h1, h2⟩, h3, h4⟩ =>
    ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hVo : IsOpen (F '' V) := isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo) hVR
  have hFc : ContinuousOn F R := continuousOn_iff_continuous_restrict.2 hFemb.continuous
  have hKR : Icc a' b' ×ˢ ({0} : Set ℝ) ⊆ R := fun z ⟨⟨h1, h2⟩, h3⟩ => by
    simp only [mem_singleton_iff] at h3
    exact ⟨⟨by linarith, by linarith⟩, by rw [h3]; norm_num, by rw [h3]; norm_num⟩
  have hKc : IsCompact (F '' (Icc a' b' ×ˢ ({0} : Set ℝ))) :=
    (isCompact_Icc.prod isCompact_singleton).image_of_continuousOn (hFc.mono hKR)
  have hKV : F '' (Icc a' b' ×ˢ ({0} : Set ℝ)) ⊆ F '' V := image_mono fun z ⟨⟨h1, h2⟩, h3⟩ => by
    simp only [mem_singleton_iff] at h3
    exact ⟨⟨by linarith, by linarith⟩, by rw [h3]; linarith, by rw [h3]; linarith⟩
  obtain ⟨ρ₁, hρ₁, hρ₁V⟩ := hKc.exists_thickening_subset_open hVo hKV
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun t ht w hw => ?_⟩
  have htK : F (t, 0) ∈ F '' (Icc a' b' ×ˢ ({0} : Set ℝ)) := ⟨(t, 0), ⟨ht, rfl⟩, rfl⟩
  have hwV : w ∈ F '' V := hρ₁V (mem_thickening_iff.2 ⟨_, htK, lt_of_lt_of_le hw (min_le_left _ _)⟩)
  obtain ⟨z, hzV, rfl⟩ := hwV
  refine ⟨z, hVR hzV, rfl, ?_⟩
  have hzR : z ∈ R := openRect_subset_rect (hVR hzV)
  have htR : ((t, 0) : ℝ × ℝ) ∈ R := hKR ⟨ht, rfl⟩
  have hd : dist (e ⟨z, hzR⟩) (e ⟨(t, 0), htR⟩) < ρ₂ := by
    rw [Subtype.dist_eq]
    exact lt_of_lt_of_le hw (min_le_right _ _)
  have := hρ₂' hd
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply, Subtype.dist_eq] at this
  exact this

/-- **Collar coordinates of `π`-images of points of `M` near the layers over `[a', b']`.** -/
theorem pi_near_collar {M : Set Pt} [CompactSpace M] {E : Set M} {k : E → unitInterval}
    {π : Pt → Pt} (hπc : Continuous π) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a' b' : ℝ} (ha' : 0 < a') (hb' : b' < 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ y : E, (k y : ℝ) ∈ Icc a' b' → ∀ q : M, dist q (y : M) < δ →
      ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1, F z = π (q : Pt) ∧ dist z ((k y : ℝ), 0) < η := by
  obtain ⟨ρ, hρ, hρ'⟩ := collar_uniform hF ha' hb' hη
  have huc : UniformContinuous (fun q : M => π (q : Pt)) :=
    CompactSpace.uniformContinuous_of_continuous (hπc.comp continuous_subtype_val)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1 huc ρ hρ
  refine ⟨δ, hδ, fun y hy q hq => ?_⟩
  have hπy : π ((y : M) : Pt) = F ((k y : ℝ), 0) := by
    rw [hγπ (k y) _ ⟨(y : M), ⟨y, rfl, rfl⟩, rfl⟩, hF.2.1 (k y)]
  have := hδ' hq
  rw [hπy] at this
  exact hρ' _ hy _ this

end HPC.Hagopian
