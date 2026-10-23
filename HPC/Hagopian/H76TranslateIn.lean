import HPC.Hagopian.H76TranslateMain

/-!
# Batch 168, item B: Lemma T relative to an ambient set (`crossing_translate_in_aux`)

`crossing_translate_aux` (batch 167) with the component taken in `A ∩ π⁻¹[D]` for any `A`
containing the translate `Q = h[k⁻¹[[a′, b′]]]`. Used with `A = Q` (and then `A = R(E)`) in
Lemma R (`H76RPiece.lean`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section TranslateIn

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

set_option maxHeartbeats 1000000 in
/-- **Lemma T, relative form** (batch 168). `crossing_translate_aux` with the ambient set `M` of
the component replaced by any `A ⊆ R²` containing `Q = h[k⁻¹[[a′, b′]]]`: the component of
`A ∩ π⁻¹[D]` through `h(x)` contains the middle layers, and its closure meets both side edges. Same
proof (steps 3–4 only use that `Q ⊆ A`). -/
theorem crossing_translate_in_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (hab : a < b) (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {a' b' : ℝ} (ha' : 0 < a') (ha'a : a' < a) (hbb' : b < b') (hb' : b' < 1) :
    ∃ c₀ > 0, Ioo a b ×ˢ Ioo 0 c₀ ⊆ D' ∧ c₀ < r₂ ∧ c₀ < s₂ ∧
    ∀ ζ > 0, ∀ η > 0, ∃ δ > 0, ∀ x : E, (k x : ℝ) ∈ Icc (a + ζ) (b - ζ) →
      ∀ h : M ≃ₜ M, (∀ v, dist (h v) v < δ) → h (x : M) ∉ E →
      π (h (x : M) : Pt) ∈ F '' (Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) →
      Disjoint (h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'}) E ∧
      (∀ y : E, (k y : ℝ) ∈ Icc a' b' → ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀,
        F z = π (h (y : M) : Pt) ∧ dist z ((k y : ℝ), 0) < η) ∧
      ∀ A : Set Pt, toPt (h '' layerSet k {t | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'}) ⊆ A →
      toPt (h '' layerSet k {t | a + ζ / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ b - ζ / 2}) ⊆
        connectedComponentIn (A ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt) ∧
      (closure (connectedComponentIn (A ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (A ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty := by
  have hinj : ∀ {z w : ℝ × ℝ}, z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 →
      w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → F z = F w → z = w :=
    fun hz hw h => collar_injOn hF hz hw h
  have hDR' : ∀ d ∈ D', d ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := fun d hd => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hd
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  obtain ⟨c₀, hc₀, hc₀1, hc₀I⟩ := exists_height_below hI.isCompact fun z hz => hz.1.2.1
  have hlow : Ioo a b ×ˢ Ioo 0 c₀ ⊆ D' :=
    rect_domain_low (r := ((a, r₂) : ℝ × ℝ)) (s := ((b, s₂) : ℝ × ℝ)) hab hDR hDf hc₀
      fun z hz => (hc₀I z hz).le
  have hr₂ : c₀ < r₂ := hc₀I _ hI.left_mem
  have hs₂ : c₀ < s₂ := hc₀I _ hI.right_mem
  have hr₂c : r₂ ≤ c := hI.left_mem.1.2.2
  have hs₂c : s₂ ≤ c := hI.right_mem.1.2.2
  have hlowR : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀, z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    fun z hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  refine ⟨c₀, hc₀, hlow, hr₂, hs₂, fun ζ hζ η hη => ?_⟩
  set η' := min (min η (ζ / 2)) (min (min (a - a') (b' - b)) (c₀ / 2)) with hη'def
  have hη'0 : 0 < η' := lt_min (lt_min hη (by linarith))
    (lt_min (lt_min (by linarith) (by linarith)) (by linarith))
  have hη'η : η' ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hη'ζ : η' ≤ ζ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hη'a : η' ≤ a - a' :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hη'b : η' ≤ b' - b :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hη'c : η' ≤ c₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ, hδ, hδ'⟩ := pi_near_collar (M := M) hπc hγπ hF ha' hb' hη'0
  refine ⟨δ, hδ, fun x hx h hmove hxE hup => ?_⟩
  have hab2 : a + ζ ≤ b - ζ := hx.1.trans hx.2
  have hco : ∀ y : E, (k y : ℝ) ∈ Icc a' b' → ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1,
      F z = π (h (y : M) : Pt) ∧ |z.1 - k y| < η' ∧ |z.2| < η' := fun y hy => by
    obtain ⟨z, hz, hFz, hd⟩ := hδ' y hy (h y) (hmove y)
    exact ⟨z, hz, hFz, dist_prod_lt hd⟩
  /- Step 1: `Q ∩ E = ∅`. -/
  set S := {t : unitInterval | a' ≤ (t : ℝ) ∧ (t : ℝ) ≤ b'} with hSdef
  have hkxS : k x ∈ S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hAc : Fold.Q78.IsContinuum (layerSet k S) :=
    isContinuum_img hE.isCompact hE.2.1 (isClosed_interval_set a' b')
      (isPreconnected_interval_set a' b') ⟨_, hkxS⟩
  have hQc := isContinuum_homeo_image h hAc
  have hxQ : h (x : M) ∈ h '' layerSet k S := ⟨(x : M), ⟨x, hkxS, rfl⟩, rfl⟩
  have hend : ∀ y : E, k y ∈ S → ∀ s : unitInterval, ((s : ℝ) = 0 ∨ (s : ℝ) = 1) →
      h (y : M) ∉ layer k s := by
    intro y hy s hs hl
    obtain ⟨z, hz, hFz, -⟩ := hco y hy
    have h1 : π (h (y : M) : Pt) = F ((s : ℝ), 0) := by
      rw [hγπ s _ ⟨_, hl, rfl⟩, hF.2.1 s]
    rw [← hFz] at h1
    have hs' : ((s : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨⟨s.2.1, s.2.2⟩, by norm_num, by norm_num⟩
    have := hinj (openRect_subset_rect hz) hs' h1
    rw [this] at hz
    rcases hs with hs | hs <;> simp [hs] at hz
  have hdis0 : ∀ s : unitInterval, ((s : ℝ) = 0 ∨ (s : ℝ) = 1) →
      Disjoint (h '' layerSet k S) (layer k s) := by
    intro s hs
    rw [disjoint_left]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ hl
    exact hend y hy s hs hl
  have hQE : Disjoint (h '' layerSet k S) E := by
    rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
    intro hne
    have := hagopian76_no_hair hX hi hE hQc hne (hdis0 0 (Or.inl rfl)) (hdis0 1 (Or.inr rfl))
    exact hxE (this hxQ)
  /- Step 2: `π[Q]` lies above the axis. -/
  have hoff : ∀ y : E, k y ∈ S → ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1,
      F z = π (h (y : M) : Pt) → z.2 ≠ 0 := by
    intro y hy z hz hFz hz2
    set t : unitInterval := ⟨z.1, hz.1.1.le, hz.1.2.le⟩
    have h1 : π (h (y : M) : Pt) = γ t := by
      rw [← hFz, ← hF.2.1 t]
      exact congrArg F (Prod.ext rfl hz2)
    obtain ⟨y', hy', -⟩ := mem_layer_of_pi_eq_gamma hE hπS hγπ h1
    have hmem : h (y : M) ∈ E := by rw [← hy']; exact y'.2
    exact disjoint_left.1 hQE ⟨(y : M), ⟨y, hy, rfl⟩, rfl⟩ hmem
  have hUpo : IsOpen (F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo)
      (prod_mono subset_rfl (Ioo_subset_Ioo (by norm_num) le_rfl))
  have hDno : IsOpen (F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0)) :=
    isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo)
      (prod_mono subset_rfl (Ioo_subset_Ioo le_rfl (by norm_num)))
  have hUD : Disjoint (F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))
      (F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0)) := by
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hFw⟩
    have := hinj (openRect_subset_rect ⟨hw.1, hw.2.1, by linarith [hw.2.2]⟩)
      (openRect_subset_rect ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩) hFw
    rw [this] at hw
    linarith [hw.2.2, hz.2.1]
  have hSpre : IsPreconnected (π '' toPt (h '' layerSet k S)) :=
    (hQc.2.2.image _ continuous_subtype_val.continuousOn).image _ hπc.continuousOn
  have hcov : π '' toPt (h '' layerSet k S) ⊆
      F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∪ F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0) := by
    rintro _ ⟨_, ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨z, hz, hFz, -⟩ := hco y hy
    have h2 := hoff y hy z hz hFz
    rcases lt_or_gt_of_ne h2 with h2 | h2
    · exact Or.inr ⟨z, ⟨hz.1, hz.2.1, h2⟩, hFz⟩
    · exact Or.inl ⟨z, ⟨hz.1, h2, hz.2.2⟩, hFz⟩
  have hxUp : π (h (x : M) : Pt) ∈ F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    obtain ⟨z, hz, hFz, -⟩ := hco x hkxS
    obtain ⟨z', hz', hFz'⟩ := hup
    have := hinj (openRect_subset_rect hz) ⟨hz'.1, by linarith [hz'.2.1], hz'.2.2⟩
      (hFz.trans hFz'.symm)
    refine ⟨z, ⟨hz.1, ?_, hz.2.2⟩, hFz⟩
    rw [this]; exact hz'.2.1
  have hSUp : π '' toPt (h '' layerSet k S) ⊆ F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rcases hSpre.subset_or_subset hUpo hDno hUD hcov with h1 | h1
    · exact h1
    · exact absurd (h1 ⟨_, ⟨_, hxQ, rfl⟩, rfl⟩) (disjoint_left.1 hUD hxUp)
  have hco' : ∀ y : E, k y ∈ S → ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀,
      F z = π (h (y : M) : Pt) ∧ |z.1 - k y| < η' ∧ |z.2| < η' := by
    intro y hy
    obtain ⟨z, hz, hFz, h1, h2⟩ := hco y hy
    obtain ⟨w, hw, hFw⟩ := hSUp ⟨_, ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    have := hinj (openRect_subset_rect hz)
      (openRect_subset_rect ⟨hw.1, by linarith [hw.2.1], hw.2.2⟩) (hFz.trans hFw.symm)
    refine ⟨z, ⟨hz.1, ?_, ?_⟩, hFz, h1, h2⟩
    · rw [this]; exact hw.2.1
    · have := (abs_lt.1 h2).2; linarith
  have hband : ∀ y : E, (k y : ℝ) ∈ Icc a' b' → ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀,
      F z = π (h (y : M) : Pt) ∧ dist z ((k y : ℝ), 0) < η := by
    intro y hy
    obtain ⟨z, hz, hFz, h1, h2⟩ := hco' y hy
    refine ⟨z, hz, hFz, ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  /- Step 3: the middle layers lie in the low strip, hence in `D`. -/
  set Sm := {t : unitInterval | a + ζ / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ b - ζ / 2} with hSmdef
  have hSmS : ∀ y : E, k y ∈ Sm → k y ∈ S := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hmidD : ∀ y : E, k y ∈ Sm → π (h (y : M) : Pt) ∈ F '' D' := by
    intro y hy
    obtain ⟨z, hz, hFz, h1, -⟩ := hco' y (hSmS y hy)
    have := abs_lt.1 h1
    exact ⟨z, hlow ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, hz.2⟩, hFz⟩
  refine ⟨hQE, hband, fun A hA => ?_⟩
  set O := π ⁻¹' (F '' D') with hOdef
  have hOo : IsOpen O := hFDo.preimage hπc
  set C := connectedComponentIn (A ∩ O) (h (x : M) : Pt) with hCdef
  have hkxm : k x ∈ Sm := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hPpre : IsPreconnected (toPt (h '' layerSet k Sm)) :=
    ((isContinuum_homeo_image h (isContinuum_img hE.isCompact hE.2.1
      (isClosed_interval_set _ _) (isPreconnected_interval_set _ _) ⟨_, hkxm⟩)).2.2).image _
      continuous_subtype_val.continuousOn
  have hPsub : toPt (h '' layerSet k Sm) ⊆ A ∩ O := by
    rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨hA ⟨_, ⟨_, ⟨y, hSmS y hy, rfl⟩, rfl⟩, rfl⟩, hmidD y hy⟩
  have hPC : toPt (h '' layerSet k Sm) ⊆ C :=
    hPpre.subset_connectedComponentIn ⟨_, ⟨_, ⟨x, hkxm, rfl⟩, rfl⟩, rfl⟩ hPsub
  /- Step 4: crossing. -/
  have hCO : C ⊆ A ∩ O := connectedComponentIn_subset _ _
  have hfr : ∀ q ∈ closure C, q ∉ O → π q ∈ I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪
      F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂) := by
    intro q hq hqO
    rw [← hFDf, hFDo.frontier_eq]
    exact ⟨map_mem_closure hπc hq fun r hr => (hCO hr).2, hqO⟩
  have hbump : ∀ (lo hi : ℝ), 0 ≤ lo → lo ≤ hi → hi ≤ 1 → a' ≤ lo → hi ≤ b' →
      (∃ y₁ : E, k y₁ ∈ Sm ∧ lo ≤ (k y₁ : ℝ) ∧ (k y₁ : ℝ) ≤ hi) →
      (∃ y₀ : E, lo ≤ (k y₀ : ℝ) ∧ (k y₀ : ℝ) ≤ hi ∧ π (h (y₀ : M) : Pt) ∉ F '' D') →
      ∃ y : E, lo ≤ (k y : ℝ) ∧ (k y : ℝ) ≤ hi ∧ (h (y : M) : Pt) ∈ closure C ∧
        (h (y : M) : Pt) ∉ O := by
    intro lo hi hlo hlohi hhi ha'lo hhib' ⟨y₁, hy₁m, hy₁l⟩ ⟨y₀, hy₀1, hy₀2, hy₀O⟩
    set Sl := {t : unitInterval | lo ≤ (t : ℝ) ∧ (t : ℝ) ≤ hi}
    have hZlc : Fold.Q78.IsContinuum (layerSet k Sl) :=
      isContinuum_img hE.isCompact hE.2.1 (isClosed_interval_set _ _)
        (isPreconnected_interval_set _ _) ⟨_, hy₁l⟩
    have hZl := isContinuum_val_image (isContinuum_homeo_image h hZlc)
    have hpZ : (h (y₁ : M) : Pt) ∈ toPt (h '' layerSet k Sl) :=
      ⟨_, ⟨_, ⟨y₁, hy₁l, rfl⟩, rfl⟩, rfl⟩
    have hpC : (h (y₁ : M) : Pt) ∈ C := hPC ⟨_, ⟨_, ⟨y₁, hy₁m, rfl⟩, rfl⟩, rfl⟩
    have hZO : ¬ toPt (h '' layerSet k Sl) ⊆ O := fun hsub =>
      hy₀O (hsub ⟨_, ⟨_, ⟨y₀, ⟨hy₀1, hy₀2⟩, rfl⟩, rfl⟩, rfl⟩)
    obtain ⟨q, hqZ, hqO, hqcl⟩ :=
      exists_mem_closure_component_notMem hZl.1 hZl.2.2 hOo hpZ (hCO hpC).2 hZO
    have hZlM : toPt (h '' layerSet k Sl) ∩ O ⊆ A ∩ O := fun r hr =>
      ⟨by
        obtain ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩ := hr.1
        exact hA ⟨_, ⟨_, ⟨y, ⟨by linarith [hy.1], by linarith [hy.2]⟩, rfl⟩, rfl⟩, rfl⟩, hr.2⟩
    have hqC : q ∈ closure C := by
      have h1 := connectedComponentIn_mono (h (y₁ : M) : Pt) hZlM
      rw [← connectedComponentIn_eq hpC] at h1
      exact closure_mono h1 hqcl
    obtain ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩ := hqZ
    exact ⟨y, hy.1, hy.2, hqC, hqO⟩
  /- Left side. -/
  have hL : (closure C ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty := by
    obtain ⟨y₁, hy₁⟩ := hE.2.1.2.1 ⟨a + ζ / 2, by linarith, by linarith⟩
    obtain ⟨y₀, hy₀⟩ := hE.2.1.2.1 ⟨a', ha'.le, by linarith⟩
    have hk₁ : (k y₁ : ℝ) = a + ζ / 2 := by rw [hy₁]
    have hk₀ : (k y₀ : ℝ) = a' := by rw [hy₀]
    have hy₀S : k y₀ ∈ S := ⟨by rw [hk₀], by rw [hk₀]; linarith⟩
    obtain ⟨y, hy1, hy2, hqC, hqO⟩ := hbump a' (a + ζ / 2) ha'.le (by linarith) (by linarith)
      le_rfl (by linarith)
      ⟨y₁, ⟨by rw [hk₁], by rw [hk₁]; linarith⟩, by rw [hk₁]; linarith, by rw [hk₁]⟩
      ⟨y₀, by rw [hk₀], by rw [hk₀]; linarith, fun ⟨d, hd, hFd⟩ => by
        obtain ⟨z, hz, hFz, h1, -⟩ := hco' y₀ hy₀S
        have := hinj (hDR' d hd) (hlowR z hz) (hFd.trans hFz.symm)
        have hd1 := (hDR hd).1.1
        rw [this] at hd1
        rw [hk₀] at h1
        have := (abs_lt.1 h1).2
        linarith⟩
    refine ⟨_, hqC, ?_⟩
    have hyS : k y ∈ S := ⟨hy1, by linarith⟩
    obtain ⟨z, hz, hFz, h1, -⟩ := hco' y hyS
    have hzR := hlowR z hz
    have h1' := abs_lt.1 h1
    rcases hfr _ hqC hqO with ((hI2 | ⟨w, hw, hFw⟩) | ⟨w, hw, hFw⟩) | ⟨w, hw, hFw⟩
    · obtain ⟨w, hw, hFw⟩ := hIR hI2
      have hwR : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
      have hwz := hinj hwR hzR (hFw.trans hFz.symm)
      have hwI : w ∈ Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂ := ⟨hw, by rw [mem_preimage, hFw]; exact hI2⟩
      have := hc₀I w hwI
      rw [hwz] at this
      linarith [hz.2.2]
    · have hw2 : w.2 = 0 := hw.2
      have hwR : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, by linarith, by linarith⟩
      have hwz := hinj hwR hzR (hFw.trans hFz.symm)
      rw [hwz] at hw2
      linarith [hz.2.1]
    · have hw1 : w.1 = a := hw.1
      have hwR : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith, by linarith⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
      have hwz := hinj hwR hzR (hFw.trans hFz.symm)
      refine ⟨w, ⟨hw.1, ?_, ?_⟩, hFw⟩
      · rw [hwz]; exact hz.2.1
      · rw [hwz]; linarith [hz.2.2]
    · have hw1 : w.1 = b := hw.1
      have hwR : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith, by linarith⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
      have hwz := hinj hwR hzR (hFw.trans hFz.symm)
      rw [hwz] at hw1
      linarith
  /- Right side. -/
  have hR : (closure C ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty := by
    obtain ⟨y₁, hy₁⟩ := hE.2.1.2.1 ⟨b - ζ / 2, by linarith, by linarith⟩
    obtain ⟨y₀, hy₀⟩ := hE.2.1.2.1 ⟨b', by linarith, hb'.le⟩
    have hk₁ : (k y₁ : ℝ) = b - ζ / 2 := by rw [hy₁]
    have hk₀ : (k y₀ : ℝ) = b' := by rw [hy₀]
    have hy₀S : k y₀ ∈ S := ⟨by rw [hk₀]; linarith, by rw [hk₀]⟩
    obtain ⟨y, hy1, hy2, hqC, hqO⟩ := hbump (b - ζ / 2) b' (by linarith) (by linarith) hb'.le
      (by linarith) le_rfl
      ⟨y₁, ⟨by rw [hk₁]; linarith, by rw [hk₁]⟩, by rw [hk₁], by rw [hk₁]; linarith⟩
      ⟨y₀, by rw [hk₀]; linarith, by rw [hk₀], fun ⟨d, hd, hFd⟩ => by
        obtain ⟨z, hz, hFz, h1, -⟩ := hco' y₀ hy₀S
        have := hinj (hDR' d hd) (hlowR z hz) (hFd.trans hFz.symm)
        have hd1 := (hDR hd).1.2
        rw [this] at hd1
        rw [hk₀] at h1
        have := (abs_lt.1 h1).1
        linarith⟩
    refine ⟨_, hqC, ?_⟩
    have hyS : k y ∈ S := ⟨by linarith, hy2⟩
    obtain ⟨z, hz, hFz, h1, -⟩ := hco' y hyS
    have hzR := hlowR z hz
    have h1' := abs_lt.1 h1
    rcases hfr _ hqC hqO with ((hI2 | ⟨w, hw, hFw⟩) | ⟨w, hw, hFw⟩) | ⟨w, hw, hFw⟩
    · obtain ⟨w, hw, hFw⟩ := hIR hI2
      have hwR : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
      have hwz := hinj hwR hzR (hFw.trans hFz.symm)
      have hwI : w ∈ Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂ := ⟨hw, by rw [mem_preimage, hFw]; exact hI2⟩
      have := hc₀I w hwI
      rw [hwz] at this
      linarith [hz.2.2]
    · have hw2 : w.2 = 0 := hw.2
      have hwR : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩, by linarith, by linarith⟩
      have hwz := hinj hwR hzR (hFw.trans hFz.symm)
      rw [hwz] at hw2
      linarith [hz.2.1]
    · have hw1 : w.1 = a := hw.1
      have hwR : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith, by linarith⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
      have hwz := hinj hwR hzR (hFw.trans hFz.symm)
      rw [hwz] at hw1
      linarith
    · have hw1 : w.1 = b := hw.1
      have hwR : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨⟨by linarith, by linarith⟩, by linarith [hw.2.1], by linarith [hw.2.2]⟩
      have hwz := hinj hwR hzR (hFw.trans hFz.symm)
      refine ⟨w, ⟨hw.1, ?_, ?_⟩, hFw⟩
      · rw [hwz]; exact hz.2.1
      · rw [hwz]; linarith [hz.2.2]
  exact ⟨hPC, hL, hR⟩

end TranslateIn

end HPC.Hagopian
