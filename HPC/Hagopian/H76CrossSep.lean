import HPC.Hagopian.H76PairSep
import HPC.Hagopian.H76Translate

/-!
# Batch 168, item B: a crossing set separates `π⁻¹[D]` along `K₀`

`rect_domain_crossing_separates` (`H76PairSep.lean`) carried to `π⁻¹[D]` through the collar `F`
and the map `π`, as `K0_crosscut_aux` does for `rect_domain_crosscut`:
* `injOn_pi_preimage`: `π` is injective on `π⁻¹[F[D′]]` (no point of `E` lies over `D′`);
* `crossing_separates_aux`: a connected `B ⊆ π⁻¹[D]` with compact closure, whose closure misses
  `π⁻¹[I₂]` and the points over the axis, and meets both open side edges, separates in `π⁻¹[D]` any
  point over `(t₀, u₁)` from any point over `(t₀, u₂)`, provided `Cl B` misses `K₀` below `u₁` and
  above `u₂`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section CrossSep

variable {M : Set Pt}

/-- **`π` is injective over `D′`**: points of `E` lie over the axis, and `D′` lies above it. -/
theorem injOn_pi_preimage {E : Set M} {k : E → unitInterval} {π : Pt → Pt}
    {γ : unitInterval → Pt} (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {D' : Set (ℝ × ℝ)} (hDR : ∀ d ∈ D', d ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ∧ 0 < d.2) :
    InjOn π (π ⁻¹' (F '' D')) := by
  intro u hu y _ huy
  have huE : u ∉ toPt E := by
    intro h
    obtain ⟨e, rfl⟩ := mem_toPt_iff.1 h
    obtain ⟨d, hd, hFd⟩ := hu
    have h1 : π ((e : M) : Pt) = F ((k e : ℝ), 0) := by
      rw [hγπ (k e) _ ⟨(e : M), ⟨e, Set.mem_singleton _, rfl⟩, rfl⟩, hF.2.1 (k e)]
    have hke : ((k e : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨⟨(k e).2.1, (k e).2.2⟩, by norm_num, by norm_num⟩
    have := collar_injOn hF (hDR d hd).1 hke (hFd.trans h1)
    have h2 := (hDR d hd).2
    rw [this] at h2
    exact lt_irrefl _ h2
  have h := (hπS y u).1 huy.symm
  change y ∈ HPC.Moore.elt (layerSetoid k) u at h
  rw [elt_layerSetoid_of_notMem k huE] at h
  exact h.symm

/-- **A crossing set separates `π⁻¹[D]` along the vertical over `t₀`.** -/
theorem crossing_separates_aux {π : Pt → Pt} {γ : unitInterval → Pt} (hπc : Continuous π)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hIs : (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) =
      {(a, r₂), (b, s₂)})
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : w₂ ∈ Ioc 0 c) (hFw : F (x₀, w₂) ∈ I₂)
    (hseg : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    (hπinj : InjOn π (π ⁻¹' (F '' D')))
    {B : Set Pt} (hB : IsPreconnected B) (hBD : B ⊆ π ⁻¹' (F '' D'))
    (hBc : IsCompact (closure B))
    (hBe : Disjoint (closure B) (π ⁻¹' (I₂ ∪ F '' (Icc a b ×ˢ {0}))))
    (hL : (closure B ∩ π ⁻¹' (F '' (({a} : Set ℝ) ×ˢ Ioo 0 r₂))).Nonempty)
    (hR : (closure B ∩ π ⁻¹' (F '' (({b} : Set ℝ) ×ˢ Ioo 0 s₂))).Nonempty)
    {u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hu₁₂ : u₁ < u₂) (hu₂ : u₂ < w₂)
    (hlo : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ioc 0 u₁))))
    (hhi : Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ Ico u₂ w₂))))
    {S : Set Pt} (hS : IsPreconnected S) (hSB : S ⊆ π ⁻¹' (F '' D') \ closure B)
    {P Q : Pt} (hP : P ∈ S) (hQ : Q ∈ S) (hπP : π P = F (x₀, u₁)) (hπQ : π Q = F (x₀, u₂)) :
    False := by
  obtain ⟨hFemb, -, -⟩ := hF
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hFemb.continuous
  have hFinj : InjOn F R1 := fun z hz w hw h =>
    congrArg Subtype.val (hFemb.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h)
  have hRR1 : Icc a b ×ˢ Icc 0 c ⊆ R1 :=
    fun z ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hDR1 : D' ⊆ R1 := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hz
    exact hRR1 ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩
  have htrans : ∀ X : Set Pt, IsPreconnected X → X ⊆ π ⁻¹' (F '' D') →
      IsPreconnected (R1 ∩ F ⁻¹' (π '' X)) ∧ R1 ∩ F ⁻¹' (π '' X) ⊆ D' ∧
        F '' (R1 ∩ F ⁻¹' (π '' X)) = π '' X := by
    intro X hX hXD
    have hT'D : π '' X ⊆ F '' D' := by rintro _ ⟨u, hu, rfl⟩; exact hXD hu
    refine ⟨?_, ?_, ?_⟩
    · have hT'r : π '' X ⊆ range (R1.restrict F) := fun p hp => by
        obtain ⟨y, hyD, rfl⟩ := hT'D hp; exact ⟨⟨y, hDR1 hyD⟩, rfl⟩
      have h1 : IsPreconnected (R1.restrict F ⁻¹' (π '' X)) := by
        rw [← hFemb.isInducing.isPreconnected_image, image_preimage_eq_of_subset hT'r]
        exact hX.image _ hπc.continuousOn
      have heq : R1 ∩ F ⁻¹' (π '' X) = Subtype.val '' (R1.restrict F ⁻¹' (π '' X)) := by
        ext z
        constructor
        · rintro ⟨hzR, hzT⟩; exact ⟨⟨z, hzR⟩, hzT, rfl⟩
        · rintro ⟨z, hzT, rfl⟩; exact ⟨z.2, hzT⟩
      rw [heq]; exact h1.image _ continuous_subtype_val.continuousOn
    · rintro z ⟨hzR, hzT⟩
      obtain ⟨y, hyD, hy⟩ := hT'D hzT
      exact hFinj (hDR1 hyD) hzR hy ▸ hyD
    · rw [image_inter_preimage]; exact inter_eq_right.2 (hT'D.trans (image_mono hDR1))
  set B' := R1 ∩ F ⁻¹' (π '' B) with hB'def
  obtain ⟨hB'pc, hB'D, hFB'⟩ := htrans B hB hBD
  have hclB' : closure B' ⊆ Icc a b ×ˢ Icc 0 c :=
    closure_minimal (fun z hz => by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR (hB'D hz)
      exact ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩) (isClosed_Icc.prod isClosed_Icc)
  have hclB'c : IsCompact (closure B') :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure hclB'
  have hcl : ∀ z ∈ closure B, ∀ p ∈ R1, F p = π z → p ∈ closure B' := by
    intro z hz p hpR hzp
    have h1 : π z ∈ closure (π '' B) := image_closure_subset_closure_image hπc ⟨z, hz, rfl⟩
    have h2 : closure (π '' B) ⊆ F '' closure B' := by
      rw [← hFB']
      exact closure_minimal (image_mono subset_closure)
        (hclB'c.image_of_continuousOn (hFc.mono (hclB'.trans hRR1))).isClosed
    obtain ⟨p', hp', hFp'⟩ := h2 h1
    have : p' = p := hFinj (hRR1 (hclB' hp')) hpR (hFp'.trans hzp.symm)
    rw [← this]; exact hp'
  have hcl' : ∀ p ∈ closure B', ∃ y ∈ closure B, π y = F p := by
    intro p hp
    have h1 : F p ∈ closure (F '' B') :=
      (hFc.mono (hclB'.trans hRR1)).image_closure ⟨p, hp, rfl⟩
    rw [hFB'] at h1
    have h2 : closure (π '' B) ⊆ π '' closure B :=
      closure_minimal (image_mono subset_closure) (hBc.image hπc).isClosed
    obtain ⟨y, hy, hyp⟩ := h2 h1
    exact ⟨y, hy, hyp⟩
  set S' := R1 ∩ F ⁻¹' (π '' S) with hS'def
  have hSD : S ⊆ π ⁻¹' (F '' D') := fun z hz => (hSB hz).1
  obtain ⟨hS'pc, hS'D, -⟩ := htrans S hS hSD
  have hS'sub : S' ⊆ D' \ closure B' := by
    intro z hz
    refine ⟨hS'D hz, fun hzB => ?_⟩
    have hzD := hS'D hz
    obtain ⟨-, u, huS, hu⟩ := hz
    obtain ⟨y, hy, hyz⟩ := hcl' z hzB
    have hyD : y ∈ π ⁻¹' (F '' D') := ⟨z, hzD, hyz.symm⟩
    have := hπinj (hSD huS) hyD (hu.trans hyz.symm)
    exact (hSB huS).2 (this ▸ hy)
  have hr₂ := hI.left_mem.1.2
  have hs₂ := hI.right_mem.1.2
  have hPR : ((x₀, u₁) : ℝ × ℝ) ∈ R1 :=
    hRR1 ⟨⟨hx₀.1.le, hx₀.2.le⟩, hu₁.le, by linarith [hw₂.2]⟩
  have hQR : ((x₀, u₂) : ℝ × ℝ) ∈ R1 :=
    hRR1 ⟨⟨hx₀.1.le, hx₀.2.le⟩, by linarith, by linarith [hw₂.2]⟩
  have hP' : ((x₀, u₁) : ℝ × ℝ) ∈ S' := ⟨hPR, P, hP, hπP⟩
  have hQ' : ((x₀, u₂) : ℝ × ℝ) ∈ S' := ⟨hQR, Q, hQ, hπQ⟩
  have hBe' : Disjoint (closure B') ((Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0}) := by
    rw [disjoint_left]
    intro p hp hpe
    obtain ⟨y, hy, hyp⟩ := hcl' p hp
    apply disjoint_left.1 hBe hy
    rcases hpe with hpI | hpb
    · exact Or.inl (show π y ∈ I₂ by rw [hyp]; exact hpI.2)
    · exact Or.inr ⟨p, hpb, hyp.symm⟩
  have hside : ∀ {e h' : ℝ}, e ∈ Icc a b → h' ≤ c →
      (closure B ∩ π ⁻¹' (F '' (({e} : Set ℝ) ×ˢ Ioo 0 h'))).Nonempty →
      (closure B' ∩ ({e} : Set ℝ) ×ˢ Ioo 0 h').Nonempty := by
    intro e h' he hh ⟨z, hz, p, hp, hzp⟩
    have hp1 : p.1 = e := hp.1
    have hpR : p ∈ R1 := hRR1 ⟨hp1 ▸ he, hp.2.1.le, hp.2.2.le.trans hh⟩
    exact ⟨p, hcl z hz p hpR hzp, hp⟩
  have hBl' := hside ⟨le_rfl, hab.le⟩ hr₂.2 hL
  have hBr' := hside ⟨hab.le, le_rfl⟩ hs₂.2 hR
  have hvert : ∀ {V : Set ℝ}, V ⊆ Icc 0 c →
      Disjoint (closure B) (π ⁻¹' (F '' (({x₀} : Set ℝ) ×ˢ V))) →
      Disjoint (closure B') (({x₀} : Set ℝ) ×ˢ V) := by
    intro V hV hd
    rw [disjoint_left]
    intro p hp hpV
    obtain ⟨y, hy, hyp⟩ := hcl' p hp
    exact disjoint_left.1 hd hy ⟨p, hpV, hyp.symm⟩
  have hlo' := hvert (fun v hv => ⟨hv.1.le, by linarith [hv.2, hw₂.2]⟩) hlo
  have hhi' := hvert (fun v hv => ⟨by linarith [hv.1], by linarith [hv.2, hw₂.2]⟩) hhi
  exact rect_domain_crossing_separates (r := ((a, r₂) : ℝ × ℝ)) (s := ((b, s₂) : ℝ × ℝ)) hab hI
    inter_subset_left rfl rfl hIs hDo hDR hDf hx₀ hw₂.1 ⟨⟨⟨hx₀.1.le, hx₀.2.le⟩, hw₂⟩, hFw⟩ hseg
    hB'pc hB'D hBe' hBl' hBr' hu₁ hu₁₂ hu₂ hlo' hhi' hS'pc hS'sub hP' hQ'

end CrossSep

end HPC.Hagopian
