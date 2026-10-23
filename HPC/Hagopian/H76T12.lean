import HPC.Hagopian.H76RPiece
import HPC.Hagopian.H76CrossSep

/-!
# Batch 168, item C: T12 (3) in the form of commission 168 §2.C (`T12_part3_aux`)

Hagopian's `x` (Lemma T′, `K0_dense_low`) and, for every `ε > 0`:
* `q = h₁(x)` on `K₀` at a height `u₂`, `h₁` an `ε`-homeomorphism (Lemma T′ and Lemma 2);
* a crossing continuum `Z = Cl B` of `R(X, E)` (Lemma R with the band below `u₂`), inside one
  extension `H` of `E` away from `X = k⁻¹(0)` and disjoint from `E`;
* `p = h₀(x)` on `K₀` below `Z` (Lemma T′ again, below the lowest point of `Z` over `t₀`);
* `Z` separates `p` from `q` in `π⁻¹[D]` (`crossing_separates_aux`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section T12

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

set_option maxHeartbeats 1000000 in
/-- **T12 (3)**, in the shape of commission 168 §2.C. See `hagopian76_T12` in `Hagopian76M.lean`
for the statement in words. -/
theorem T12_part3_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπc : Continuous π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc1 : c ≤ 1)
    (hbelow : ∃ c' > 0, Disjoint (F '' (Icc a b ×ˢ Ico (-c') 0)) (π '' M))
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c)) {D' : Set (ℝ × ℝ)} (hDo : IsOpen D')
    (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (hFDo : IsOpen (F '' D'))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂))
    {t₀ w₂ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (t₀, w₂) ∈ I₂)
    (hseg : Disjoint (({t₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂)) :
    ∃ x : E, (k x : ℝ) = t₀ ∧ ∀ ε > 0, ∃ (h₀ h₁ : M ≃ₜ M) (u₁ u₂ : ℝ),
      (∀ v, dist (h₀ v) v < ε) ∧ (∀ v, dist (h₁ v) v < ε) ∧
      0 < u₁ ∧ u₁ < u₂ ∧ u₂ < w₂ ∧
      π (h₀ (x : M) : Pt) = F (t₀, u₁) ∧ π (h₁ (x : M) : Pt) = F (t₀, u₂) ∧
      ∃ (H : Set M) (B : Set Pt), IsExtensionAway E (layer k 0) H ∧
        IsPreconnected B ∧ B ⊆ π ⁻¹' (F '' D') ∧ closure B ⊆ toPt (H \ E) ∧
        IsCompact (closure B) ∧
        (closure B ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty ∧
        (closure B ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty ∧
        ∀ S : Set Pt, IsPreconnected S → S ⊆ π ⁻¹' (F '' D') \ closure B →
          (h₀ (x : M) : Pt) ∈ S → (h₁ (x : M) : Pt) ∉ S := by
  obtain ⟨x, hkx, hxq, -⟩ := K0_dense_low hX hi hE hπc hπS hγπ hF ha hab hb hc1 hbelow hI hIR
    hDR hDf hFDo hFDf ht₀
  obtain ⟨c₀, hc₀, hlow, hr, hs, hRp⟩ := crossing_piece_of_R_aux (a' := a / 2) (b' := (b + 1) / 2)
    hX hi hE hπc hπS hγπ hF hab hc1 hbelow hI hIR hDR hDf hFDo hFDf (by linarith) (by linarith)
    (by linarith) (by linarith)
  refine ⟨x, hkx, fun ε hε => ?_⟩
  have hFemb := hF.1
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hFemb.continuous
  have hinj : ∀ {z w : ℝ × ℝ}, z ∈ R1 → w ∈ R1 → F z = F w → z = w :=
    fun hz hw h => collar_injOn hF hz hw h
  have hcc : 0 < c := hw₂.1.trans_le hw₂.2
  set ζ := min (t₀ - a) (b - t₀) / 2 with hζdef
  have hζ0 : 0 < ζ := by
    have := lt_min (sub_pos.2 ht₀.1) (sub_pos.2 ht₀.2); linarith
  have hxζ : (k x : ℝ) ∈ Icc (a + ζ) (b - ζ) := by
    rw [hkx]
    have h1 := min_le_left (t₀ - a) (b - t₀)
    have h2 := min_le_right (t₀ - a) (b - t₀)
    have h3 := lt_min (sub_pos.2 ht₀.1) (sub_pos.2 ht₀.2)
    constructor <;> linarith
  obtain ⟨hWo, hxW⟩ := hagopian76_lemma2 hX hε (x : M)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hWo (x : M) hxW
  have hW : ∀ y ∈ M, dist y ((x : M) : Pt) < ρ →
      ∃ g : M ≃ₜ M, (g (x : M) : Pt) = y ∧ ∀ v, dist (g v) v < ε := by
    intro y hyM hy
    obtain ⟨g, hg, hgv⟩ := hball (show (⟨y, hyM⟩ : M) ∈ ball (x : M) ρ from hy)
    exact ⟨g, by rw [hg], fun v => by rw [dist_comm]; exact hgv v⟩
  -- `q`
  obtain ⟨q, hqM, hqx, u₂, hu₂, hπq⟩ := hxq (min ρ w₂) (lt_min hρ hw₂.1)
  obtain ⟨h₁, hh₁x, hh₁⟩ := hW q hqM (lt_of_lt_of_le hqx (min_le_left _ _))
  have hu₂w : u₂ < w₂ := lt_of_lt_of_le hu₂.2 (min_le_right _ _)
  -- the crossing continuum, with the band below `u₂`
  obtain ⟨h, -, -, -, -, hQE, hband, hA, H, hH, hZH⟩ :=
    hRp ζ hζ0 x hxζ (min ε u₂) (lt_min hε hu₂.1)
  set S0 := {t : unitInterval | a / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ (b + 1) / 2} with hS0def
  set Q := h '' layerSet k S0 with hQdef
  set O := π ⁻¹' (F '' D') with hOdef
  set B := connectedComponentIn (toPt Q ∩ O) (h (x : M) : Pt) with hBdef
  obtain ⟨-, hZL, hZR⟩ := hA (toPt Q) subset_rfl
  have hkxS : k x ∈ S0 := ⟨by rw [hkx]; linarith [ht₀.1], by rw [hkx]; linarith [ht₀.2]⟩
  have hQc : Fold.Q78.IsContinuum Q :=
    isContinuum_homeo_image h (isContinuum_img hE.isCompact hE.2.1
      (isClosed_interval_set _ _) (isPreconnected_interval_set _ _) ⟨_, hkxS⟩)
  have hQc' := isContinuum_val_image hQc
  have hBQ : closure B ⊆ toPt Q :=
    closure_minimal ((connectedComponentIn_subset _ _).trans inter_subset_left) hQc'.1.isClosed
  have hBO : B ⊆ O := (connectedComponentIn_subset _ _).trans inter_subset_right
  have hZc : IsCompact (closure B) := hQc'.1.of_isClosed_subset isClosed_closure hBQ
  have hZband : ∀ z ∈ closure B, ∃ w ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀,
      F w = π z ∧ w.2 < min ε u₂ := by
    intro z hz
    obtain ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩ := hBQ hz
    obtain ⟨w, hw, hFw', hd⟩ := hband y ⟨hy.1, hy.2⟩
    exact ⟨w, hw, hFw', (abs_lt.1 (dist_prod_lt hd).2).2⟩
  have hwR : ∀ w ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 0 c₀, w ∈ R1 := fun w hw =>
    ⟨⟨hw.1.1.le, hw.1.2.le⟩, by linarith [hw.2.1],
      by linarith [hw.2.2, hr, hI.left_mem.1.2.2, hc1]⟩
  have hvR : ∀ v, 0 ≤ v → v ≤ w₂ → ((t₀, v) : ℝ × ℝ) ∈ R1 := fun v h0 h1 =>
    ⟨⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, by linarith, by linarith [hw₂.2]⟩
  -- the lowest point of `Cl B` over `t₀`
  have hnot : F (t₀, 0) ∉ π '' closure B := by
    rintro ⟨z, hz, hπz⟩
    obtain ⟨w, hw, hFw', -⟩ := hZband z hz
    have := hinj (hwR w hw) (hvR 0 le_rfl hw₂.1.le) (hFw'.trans hπz)
    have h2 := hw.2.1
    rw [this] at h2
    exact lt_irrefl _ h2
  obtain ⟨ρ', hρ', hball'⟩ :=
    Metric.isOpen_iff.1 (hZc.image hπc).isClosed.isOpen_compl _ hnot
  obtain ⟨δF, hδF, hδF'⟩ :=
    Metric.continuousOn_iff.1 hFc (t₀, 0) (hvR 0 le_rfl hw₂.1.le) ρ' hρ'
  have hlow' : ∀ v, 0 ≤ v → v < δF → v ≤ w₂ → F (t₀, v) ∉ π '' closure B := by
    intro v hv0 hvδ hvw
    apply hball'
    apply hδF' _ (hvR v hv0 hvw)
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero, sub_zero,
      abs_of_nonneg hv0]
    exact max_lt hδF hvδ
  -- `p`
  obtain ⟨p, hpM, hpx, u₁, hu₁, hπp⟩ := hxq (min ρ (min δF u₂)) (lt_min hρ (lt_min hδF hu₂.1))
  obtain ⟨h₀, hh₀x, hh₀⟩ := hW p hpM (lt_of_lt_of_le hpx (min_le_left _ _))
  have hu₁δ : u₁ < δF := lt_of_lt_of_le hu₁.2 ((min_le_right _ _).trans (min_le_left _ _))
  have hu₁₂ : u₁ < u₂ := lt_of_lt_of_le hu₁.2 ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨h₀, h₁, u₁, u₂, hh₀, hh₁, hu₁.1, hu₁₂, hu₂w, by rw [hh₀x]; exact hπp,
    by rw [hh₁x]; exact hπq, H, B, hH, isPreconnected_connectedComponentIn, hBO, hZH, hZc,
    hZL, hZR, fun S hS hSZ hpS hqS => ?_⟩
  have hlo : Disjoint (closure B) (π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ioc 0 u₁))) := by
    rw [disjoint_left]
    rintro z hz ⟨w, ⟨hw1, hw2⟩, hFw'⟩
    have hw1' : w.1 = t₀ := hw1
    have hwe : w = (t₀, w.2) := Prod.ext hw1' rfl
    rw [hwe] at hFw'
    exact hlow' w.2 hw2.1.le (lt_of_le_of_lt hw2.2 hu₁δ) (by linarith [hw2.2])
      ⟨z, hz, hFw'.symm⟩
  have hhi : Disjoint (closure B) (π ⁻¹' (F '' (({t₀} : Set ℝ) ×ˢ Ico u₂ w₂))) := by
    rw [disjoint_left]
    rintro z hz ⟨w, ⟨hw1, hw2⟩, hFw'⟩
    have hw1' : w.1 = t₀ := hw1
    obtain ⟨w', hw', hFw'', hw'2⟩ := hZband z hz
    have hwR' : w ∈ R1 := by
      rw [show w = (t₀, w.2) from Prod.ext hw1' rfl]
      exact hvR w.2 (by linarith [hw2.1, hu₂.1]) hw2.2.le
    have := hinj hwR' (hwR w' hw') (hFw'.trans hFw''.symm)
    rw [this] at hw2
    linarith [hw2.1, min_le_right ε u₂]
  have hBe : Disjoint (closure B) (π ⁻¹' (I₂ ∪ F '' (Icc a b ×ˢ {0}))) := by
    rw [disjoint_left]
    intro z hz hzI
    obtain ⟨w, hw, hFw', -⟩ := hZband z hz
    rcases hzI with hI2 | ⟨w'', hw'', hFw''⟩
    · obtain ⟨w', hw', hFw'2⟩ := hIR hI2
      have hw'R : w' ∈ R1 := ⟨⟨by linarith [hw'.1.1], by linarith [hw'.1.2]⟩,
        by linarith [hw'.2.1], by linarith [hw'.2.2]⟩
      have hww := hinj (hwR w hw) hw'R (hFw'.trans hFw'2.symm)
      have hwI : w ∈ Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂ :=
        ⟨hww ▸ hw', by rw [mem_preimage, hFw']; exact hI2⟩
      rcases eq_or_lt_of_le hwI.1.1.1 with h1 | h1
      · have : w ∈ (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) :=
          ⟨hwI, Or.inl h1.symm, hwI.1.2.1.le, hwI.1.2.2⟩
        rw [hIs] at this
        rcases this with h' | h'
        · have := congrArg Prod.snd h'; simp only at this; linarith [hw.2.2]
        · have := congrArg Prod.snd h'; simp only at this; linarith [hw.2.2]
      rcases eq_or_lt_of_le hwI.1.1.2 with h2 | h2
      · have : w ∈ (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) :=
          ⟨hwI, Or.inr h2, hwI.1.2.1.le, hwI.1.2.2⟩
        rw [hIs] at this
        rcases this with h' | h'
        · have := congrArg Prod.snd h'; simp only at this; linarith [hw.2.2]
        · have := congrArg Prod.snd h'; simp only at this; linarith [hw.2.2]
      have hwD : w ∈ D' := hlow ⟨⟨h1, h2⟩, hw.2⟩
      have hwf : w ∈ frontier D' := by rw [hDf]; exact Or.inl (Or.inl (Or.inl hwI))
      exact (hDo.frontier_eq ▸ hwf).2 hwD
    · have hw''R : w'' ∈ R1 := ⟨⟨by linarith [hw''.1.1], by linarith [hw''.1.2]⟩,
        by rw [show w''.2 = 0 from hw''.2]; norm_num,
        by rw [show w''.2 = 0 from hw''.2]; norm_num⟩
      have hww := hinj (hwR w hw) hw''R (hFw'.trans hFw''.symm)
      have h2 := hw.2.1
      rw [hww, show w''.2 = 0 from hw''.2] at h2
      exact lt_irrefl _ h2
  have hπinj : InjOn π (π ⁻¹' (F '' D')) := injOn_pi_preimage hπS hγπ hF fun d hd => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hd
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, h3⟩
  rw [hh₀x] at hpS
  rw [hh₁x] at hqS
  exact crossing_separates_aux hπc hF ha hab hb hc1 hI hIs hDo hDR hDf ht₀ hw₂ hFw hseg hπinj
    isPreconnected_connectedComponentIn hBO hZc hBe hZL hZR hu₁.1 hu₁₂ hu₂w hlo hhi hS hSZ
    hpS hqS hπp hπq

end T12

end HPC.Hagopian
