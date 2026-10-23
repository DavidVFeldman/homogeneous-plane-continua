import HPC.Hagopian.H76TranslateMain

/-!
# Batch 167, item A: Lemma T′ (`K0_dense_low_aux`)

Commission 167 §1, Lemma T′: points of `M` on the vertical over `t₀` (Hagopian: `11/22`) at every
small height above the axis, and a point `x` of the layer over `t₀` that they accumulate at.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section K0Dense

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **A point of `M` on the vertical over `t₀` at any small height** (the core of Lemma T′). -/
theorem K0_low_point_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) {η : ℝ} (hη : 0 < η) :
    ∃ q ∈ M, ∃ u ∈ Ioo 0 η, π q = F (t₀, u) := by
  have hinj : ∀ {z w : ℝ × ℝ}, z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 →
      w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → F z = F w → z = w :=
    fun hz hw h => collar_injOn hF hz hw h
  set ζ := min (t₀ - a) (b - t₀) / 4 with hζdef
  have hζ : 0 < ζ := by
    have : 0 < min (t₀ - a) (b - t₀) := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
    positivity
  have hζa : a + 4 * ζ ≤ t₀ := by
    have := min_le_left (t₀ - a) (b - t₀); linarith
  have hζb : t₀ + 4 * ζ ≤ b := by
    have := min_le_right (t₀ - a) (b - t₀); linarith
  obtain ⟨c₀, hc₀, -, hr₂, -, hT⟩ := crossing_translate_aux hX hi hE hπc hπS hγπ hF hab
    hc1 hI hIR hDR hDf hFDo hFDf (a' := a / 2) (b' := (b + 1) / 2) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have hc₀1 : c₀ < 1 := by linarith [hI.left_mem.1.2.2]
  set ηT := min η (ζ / 2) with hηTdef
  have hηT : 0 < ηT := lt_min hη (by linarith)
  have hηTη : ηT ≤ η := min_le_left _ _
  have hηTζ : ηT ≤ ζ / 2 := min_le_right _ _
  obtain ⟨δ, hδ, hT'⟩ := hT ζ hζ ηT hηT
  obtain ⟨δE, hδE, hEff⟩ :=
    HPC.Effros.effros_homogeneous_set (isCompact_iff_compactSpace.2 ‹CompactSpace M›) hX hδ
  obtain ⟨c₁, hc₁, hc₁1, hthin⟩ := pi_thin_near_layer hE hπc hπS hγπ hF
    (a := t₀ - ζ) (b := t₀ + ζ) (by linarith) (by linarith) hδE
  have hbelow' : ∃ c' > 0, Disjoint (F '' (Icc (t₀ - ζ) (t₀ + ζ) ×ˢ Ico (-c') 0)) (π '' M) := by
    obtain ⟨c', hc', hd⟩ := hbelow
    exact ⟨c', hc', hd.mono_left (image_mono (prod_mono
      (Icc_subset_Icc (by linarith) (by linarith)) subset_rfl))⟩
  obtain ⟨p, ⟨z, hz, rfl⟩, ⟨m, hm, hπm⟩⟩ := M_meets_above hi hE hπc hπS hγπ hF
    (a := t₀ - ζ) (b := t₀ + ζ) (by linarith) (by linarith) (by linarith) hbelow' hc₁
  obtain ⟨y, hyI, -, hym⟩ := hthin ⟨m, hm⟩ z
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, by linarith [hz.2.1], hz.2.2.le⟩ hπm
  obtain ⟨h, hhy, hmove⟩ := hEff (y : M) ⟨m, hm⟩ (by rw [dist_comm]; exact hym)
  have hzR : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hmE : h (y : M) ∉ E := by
    rw [hhy]
    intro hmem
    set e : E := ⟨⟨m, hm⟩, hmem⟩
    have h1 : π m = F ((k e : ℝ), 0) := by
      rw [hγπ (k e) m ⟨(e : M), ⟨e, rfl, rfl⟩, rfl⟩, hF.2.1 (k e)]
    have := hinj hzR ⟨⟨(k e).2.1, (k e).2.2⟩, by norm_num, by norm_num⟩ (hπm.symm.trans h1)
    have h2 := hz.2.1
    rw [this] at h2
    exact lt_irrefl _ h2
  have hup : π (h (y : M) : Pt) ∈ F '' (Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
    rw [hhy]
    exact ⟨z, ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2.1, by linarith [hz.2.2]⟩,
      hπm.symm⟩
  obtain ⟨-, hco, -, -, -⟩ := hT' y ⟨by linarith [hyI.1], by linarith [hyI.2]⟩ h hmove hmE hup
  set Sm := {t : unitInterval | a + ζ / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ b - ζ / 2} with hSmdef
  obtain ⟨yL, hyL⟩ := hE.2.1.2.1 ⟨a + ζ / 2, by linarith, by linarith⟩
  obtain ⟨yR, hyR⟩ := hE.2.1.2.1 ⟨b - ζ / 2, by linarith, by linarith⟩
  have hkL : (k yL : ℝ) = a + ζ / 2 := by rw [hyL]
  have hkR : (k yR : ℝ) = b - ζ / 2 := by rw [hyR]
  have hSmI : ∀ y' : E, k y' ∈ Sm → (k y' : ℝ) ∈ Icc (a / 2) ((b + 1) / 2) := fun y' hy' =>
    ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  have hLm : k yL ∈ Sm := ⟨by rw [hkL], by rw [hkL]; linarith⟩
  have hRm : k yR ∈ Sm := ⟨by rw [hkR]; linarith, by rw [hkR]⟩
  by_contra hno
  push_neg at hno
  have hLo : IsOpen (F '' (Ioo 0 t₀ ×ˢ Ioo (0 : ℝ) 1)) :=
    isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo)
      (prod_mono (Ioo_subset_Ioo le_rfl (by linarith)) (Ioo_subset_Ioo (by norm_num) le_rfl))
  have hRo : IsOpen (F '' (Ioo t₀ 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    isOpen_collar_image hF (isOpen_Ioo.prod isOpen_Ioo)
      (prod_mono (Ioo_subset_Ioo (by linarith) le_rfl) (Ioo_subset_Ioo (by norm_num) le_rfl))
  have hLR : Disjoint (F '' (Ioo 0 t₀ ×ˢ Ioo (0 : ℝ) 1)) (F '' (Ioo t₀ 1 ×ˢ Ioo (0 : ℝ) 1)) := by
    rw [disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hFw'⟩
    have := hinj ⟨⟨by linarith [hw'.1.1], hw'.1.2.le⟩, by linarith [hw'.2.1], hw'.2.2.le⟩
      ⟨⟨hw.1.1.le, by linarith [hw.1.2]⟩, by linarith [hw.2.1], hw.2.2.le⟩ hFw'
    rw [this] at hw'
    linarith [hw'.1.1, hw.1.2]
  have hPpre : IsPreconnected (π '' toPt (h '' layerSet k Sm)) :=
    (((isContinuum_homeo_image h (isContinuum_img hE.isCompact hE.2.1
      (isClosed_interval_set _ _) (isPreconnected_interval_set _ _) ⟨_, hLm⟩)).2.2).image _
      continuous_subtype_val.continuousOn).image _ hπc.continuousOn
  have hcoord : ∀ y' : E, k y' ∈ Sm → ∃ w ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀,
      F w = π (h (y' : M) : Pt) ∧ |w.1 - k y'| < ηT ∧ w.1 ≠ t₀ := by
    intro y' hy'
    obtain ⟨w, hw, hFw, hd⟩ := hco y' (hSmI y' hy')
    obtain ⟨h1, h2⟩ := dist_prod_lt hd
    refine ⟨w, hw, hFw, h1, fun hw1 => ?_⟩
    refine hno _ (h y').2 w.2 ⟨hw.2.1, ?_⟩ ?_
    · have := (abs_lt.1 h2).2; linarith
    · rw [← hFw, ← hw1]
  have hcov : π '' toPt (h '' layerSet k Sm) ⊆
      F '' (Ioo 0 t₀ ×ˢ Ioo (0 : ℝ) 1) ∪ F '' (Ioo t₀ 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rintro _ ⟨_, ⟨_, ⟨_, ⟨y', hy', rfl⟩, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨w, hw, hFw, -, hw1⟩ := hcoord y' hy'
    rcases lt_or_gt_of_ne hw1 with h1 | h1
    · exact Or.inl ⟨w, ⟨⟨hw.1.1, h1⟩, hw.2.1, by linarith [hw.2.2]⟩, hFw⟩
    · exact Or.inr ⟨w, ⟨⟨h1, hw.1.2⟩, hw.2.1, by linarith [hw.2.2]⟩, hFw⟩
  have hmemL : π (h (yL : M) : Pt) ∈ F '' (Ioo 0 t₀ ×ˢ Ioo (0 : ℝ) 1) := by
    obtain ⟨w, hw, hFw, h1, -⟩ := hcoord yL hLm
    rw [hkL] at h1
    have := (abs_lt.1 h1).2
    exact ⟨w, ⟨⟨hw.1.1, by linarith⟩, hw.2.1, by linarith [hw.2.2]⟩, hFw⟩
  have hmemR : π (h (yR : M) : Pt) ∈ F '' (Ioo t₀ 1 ×ˢ Ioo (0 : ℝ) 1) := by
    obtain ⟨w, hw, hFw, h1, -⟩ := hcoord yR hRm
    rw [hkR] at h1
    have := (abs_lt.1 h1).1
    exact ⟨w, ⟨⟨by linarith, hw.1.2⟩, hw.2.1, by linarith [hw.2.2]⟩, hFw⟩
  rcases hPpre.subset_or_subset hLo hRo hLR hcov with h1 | h1
  · exact disjoint_left.1 hLR (h1 ⟨_, ⟨_, ⟨_, ⟨yR, hRm, rfl⟩, rfl⟩, rfl⟩, rfl⟩) hmemR
  · exact disjoint_left.1 hLR hmemL (h1 ⟨_, ⟨_, ⟨_, ⟨yL, hLm, rfl⟩, rfl⟩, rfl⟩, rfl⟩)

/-- **Lemma T′** (commission 167 §1): a point `x` of the layer over `t₀` and, arbitrarily close to
it, points of `M` on the vertical over `t₀` at arbitrarily small positive heights. -/
theorem K0_dense_low_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ x : E, (k x : ℝ) = t₀ ∧ ∀ ε > 0, ∃ q ∈ M, dist q ((x : M) : Pt) < ε ∧
      ∃ u ∈ Ioo 0 ε, π q = F (t₀, u) := by
  have hpt : ∀ n : ℕ, ∃ q ∈ M, ∃ u ∈ Ioo 0 (1 / ((n : ℝ) + 1)), π q = F (t₀, u) := fun n =>
    K0_low_point_aux hX hi hE hπc hπS hγπ hF ha hab hb hc1 hbelow hI hIR hDR hDf hFDo hFDf ht₀
      (by positivity)
  choose q hqM u hu hπq using hpt
  have hMc : IsCompact M := isCompact_iff_compactSpace.2 ‹CompactSpace M›
  obtain ⟨x₀, hx₀M, φ, hφ, hlim⟩ := hMc.tendsto_subseq hqM
  have hu0 : Tendsto u atTop (𝓝 0) :=
    squeeze_zero (fun n => (hu n).1.le) (fun n => (hu n).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have huφ : Tendsto (u ∘ φ) atTop (𝓝 0) := hu0.comp hφ.tendsto_atTop
  have hR0 : ((t₀, 0) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, by norm_num, by norm_num⟩
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    continuousOn_iff_continuous_restrict.2 hF.1.continuous
  have hg : Tendsto (fun n => ((t₀, u (φ n)) : ℝ × ℝ)) atTop
      (𝓝[Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1] (t₀, 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds huφ, Eventually.of_forall
      fun n => ?_⟩
    have h1 := hu (φ n)
    have h2 : 1 / ((φ n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg (φ n) : (0 : ℝ) ≤ φ n)]
    exact ⟨⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, by linarith [h1.1], by linarith [h1.2]⟩
  have h1 : Tendsto (fun n => π (q (φ n))) atTop (𝓝 (F (t₀, 0))) := by
    have := (hFc _ hR0).tendsto.comp hg
    refine this.congr fun n => ?_
    simp only [Function.comp, hπq]
  have h2 : Tendsto (fun n => π (q (φ n))) atTop (𝓝 (π x₀)) :=
    (hπc.tendsto x₀).comp hlim
  have hx₀ : π x₀ = F (t₀, 0) := tendsto_nhds_unique h2 h1
  set t : unitInterval := ⟨t₀, by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have hx₀γ : π ((⟨x₀, hx₀M⟩ : M) : Pt) = γ t := by
    rw [← hF.2.1 t]; exact hx₀
  obtain ⟨y, hyx, hyt⟩ := mem_layer_of_pi_eq_gamma hE hπS hγπ hx₀γ
  refine ⟨y, by rw [hyt], fun ε hε => ?_⟩
  have hev1 : ∀ᶠ n in atTop, dist (q (φ n)) x₀ < ε :=
    (Metric.tendsto_nhds.1 hlim) ε hε
  have hev2 : ∀ᶠ n in atTop, u (φ n) < ε := huφ.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  refine ⟨q (φ n), hqM _, ?_, u (φ n), ⟨(hu _).1, hn2⟩, hπq _⟩
  rw [hyx]
  exact hn1

/-- **The `p`-components of T12 cross** (commission 167 §2.B, first bullet). With `x` from Lemma T′:
for every `ε > 0` there is an `ε`-homeomorphism `h` of `M` with `p = h(x)` on the vertical over `t₀`
at height `< ε`, within `ε` of `x`, off `E`, and the component `C` of `M ∩ π⁻¹[D]` through `p`
contains `h[k⁻¹[[a + ζ/2, b − ζ/2]]]` (a fixed `ζ > 0`) and has closure meeting both side edges. -/
theorem T12_crossing_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ x : E, (k x : ℝ) = t₀ ∧ ∃ ζ > 0, ∀ ε > 0, ∃ h : M ≃ₜ M, (∀ v, dist (h v) v < ε) ∧
      dist (h (x : M) : Pt) ((x : M) : Pt) < ε ∧
      (∃ u ∈ Ioo 0 ε, π (h (x : M) : Pt) = F (t₀, u)) ∧ h (x : M) ∉ E ∧
      toPt (h '' layerSet k {t | a + ζ / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ b - ζ / 2}) ⊆
        connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt) ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
      (closure (connectedComponentIn (M ∩ π ⁻¹' (F '' D')) (h (x : M) : Pt)) ∩
        π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty := by
  obtain ⟨x, hkx, hdense⟩ := K0_dense_low_aux hX hi hE hπc hπS hγπ hF ha hab hb hc1 hbelow hI
    hIR hDR hDf hFDo hFDf ht₀
  set ζ := min (t₀ - a) (b - t₀) with hζdef
  have hζ : 0 < ζ := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  have hζa : a + ζ ≤ t₀ := by have := min_le_left (t₀ - a) (b - t₀); linarith
  have hζb : t₀ ≤ b - ζ := by have := min_le_right (t₀ - a) (b - t₀); linarith
  obtain ⟨c₀, -, -, -, -, hT⟩ := crossing_translate_aux hX hi hE hπc hπS hγπ hF hab
    hc1 hI hIR hDR hDf hFDo hFDf (a' := a / 2) (b' := (b + 1) / 2) (by linarith) (by linarith)
    (by linarith) (by linarith)
  refine ⟨x, hkx, ζ, hζ, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hT'⟩ := hT ζ hζ 1 one_pos
  obtain ⟨δE, hδE, hEff⟩ := HPC.Effros.effros_homogeneous_set
    (isCompact_iff_compactSpace.2 ‹CompactSpace M›) hX (lt_min hε hδ)
  obtain ⟨q, hqM, hqx, u, hu, hπq⟩ := hdense (min (min ε δE) 1)
    (lt_min (lt_min hε hδE) one_pos)
  have hm1 : min (min ε δE) 1 ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : min (min ε δE) 1 ≤ δE := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : min (min ε δE) 1 ≤ 1 := min_le_right _ _
  obtain ⟨h, hhx, hmove⟩ := hEff (x : M) ⟨q, hqM⟩
    (by rw [dist_comm]; exact lt_of_lt_of_le hqx hm2)
  have hmove' : ∀ v, dist (h v) v < δ := fun v => lt_of_lt_of_le (hmove v) (min_le_right _ _)
  have hxE : h (x : M) ∉ E := by
    rw [hhx]
    intro hmem
    set e : E := ⟨⟨q, hqM⟩, hmem⟩
    have h1 : π q = F ((k e : ℝ), 0) := by
      rw [hγπ (k e) q ⟨(e : M), ⟨e, rfl, rfl⟩, rfl⟩, hF.2.1 (k e)]
    have := collar_injOn hF ⟨⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, by linarith [hu.1],
      by linarith [hu.2]⟩ ⟨⟨(k e).2.1, (k e).2.2⟩, by norm_num, by norm_num⟩ (hπq.symm.trans h1)
    have h2 := congrArg Prod.snd this
    simp only at h2
    linarith [hu.1]
  have hup : π (h (x : M) : Pt) ∈ F '' (Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
    rw [hhx]
    exact ⟨(t₀, u), ⟨⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, hu.1, by linarith [hu.2]⟩,
      hπq.symm⟩
  obtain ⟨-, -, hPC, hL, hR⟩ := hT' x ⟨by rw [hkx]; exact hζa, by rw [hkx]; exact hζb⟩ h
    hmove' hxE hup
  refine ⟨h, fun v => lt_of_lt_of_le (hmove v) (min_le_left _ _), ?_,
    ⟨u, ⟨hu.1, lt_of_lt_of_le hu.2 hm1⟩, by rw [hhx]; exact hπq⟩, hxE, hPC, hL, hR⟩
  rw [hhx]
  exact lt_of_lt_of_le hqx hm1

end K0Dense

end HPC.Hagopian
