import HPC.Hagopian.H76Domain

/-!
# Batch 166, items A and B: Hagopian's `D` in the plane, and the low part `K₀` of `K`

* `pi_isClosedMap`: `π` is a closed map (the saturation of a closed set `A` is `A` together with the
  union of the layers over the compact set `k[A ∩ E]`).
* `pi_preimage_isPreconnected`: `π` pulls connected sets missing `π[E]` back to connected sets
  (`π` restricted to `R² − E` is an open embedding).
* `tarc_pullback`: an arc in `F[Q]` pulls back to an arc of `Q` (`F` an embedding on `Q`).
* `hagopian76_D_aux`: `D = F[D′]` with `D′` from `rect_domain_aux`, for an arc `I₂` as produced by
  `hagopian76_T7`.
* `K0_aux`: the vertical segment from `p₃` up to the lowest point of `I₂` above it.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section DCollar

variable {M : Set Pt}

/-! ## `π` is closed; connected sets off `π[E]` pull back to connected sets -/

/-- **`π` is a closed map.** -/
theorem pi_isClosedMap {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) :
    IsClosedMap π := by
  intro A hA
  obtain ⟨⟨a, b, hab⟩, hk, -⟩ := hE
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hab.1.1
  set ι : E → Pt := fun e => ((e : M) : Pt) with hι
  have hιc : Continuous ι := continuous_subtype_val.comp continuous_subtype_val
  set A' : Set E := ι ⁻¹' A
  have hA'c : IsClosed A' := hA.preimage hιc
  set P : Set E := k ⁻¹' (k '' A')
  have hPc : IsClosed P := (hA'c.isCompact.image hk.1).isClosed.preimage hk.1
  have hT : IsClosed (ι '' P) := (hPc.isCompact.image hιc).isClosed
  have heq : π ⁻¹' (π '' A) = A ∪ ι '' P := by
    ext z
    constructor
    · rintro ⟨x, hxA, hxz⟩
      by_cases hz : z ∈ toPt E
      · obtain ⟨e, rfl⟩ := mem_toPt_iff.1 hz
        by_cases hx : x ∈ toPt E
        · obtain ⟨e', rfl⟩ := mem_toPt_iff.1 hx
          have h := (hπS _ _).1 hxz
          change layerKey k _ = layerKey k _ at h
          rw [layerKey_of_mem, layerKey_of_mem] at h
          exact Or.inr ⟨e, ⟨e', hxA, Sum.inl_injective h⟩, rfl⟩
        · rw [eq_of_pi_eq_off hπS hx hxz.symm]; exact Or.inl hxA
      · rw [← eq_of_pi_eq_off hπS hz hxz]; exact Or.inl hxA
    · rintro (hz | ⟨e, ⟨e', he'A, he'e⟩, rfl⟩)
      · exact ⟨z, hz, rfl⟩
      · refine ⟨ι e', he'A, (hπS _ _).2 ?_⟩
        change layerKey k _ = layerKey k _
        rw [hι]; simp only
        rw [layerKey_of_mem, layerKey_of_mem, he'e]
  rw [← hπ.isClosed_preimage, heq]
  exact hA.union hT

/-- **`π` pulls connected sets missing `π[E]` back to connected sets.** -/
theorem pi_preimage_isPreconnected {E : Set M} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) {π : Pt → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {V : Set Pt} (hV : IsPreconnected V)
    (hVE : Disjoint V (π '' toPt E)) : IsPreconnected (π ⁻¹' V) := by
  set Ω : Set Pt := (toPt E)ᶜ with hΩ
  have hEc : IsClosed (toPt E) := by
    obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE
    exact (isCompact_toPt hab.1.1).isClosed
  have hΩo : IsOpen Ω := hEc.isOpen_compl
  set e : Ω → Pt := Ω.restrict π with he
  have hec : Continuous e := hπ.continuous.comp continuous_subtype_val
  have hinj : Function.Injective e := fun x y hxy => Subtype.ext (eq_of_pi_eq_off hπS y.2 hxy)
  have hopen : IsOpenMap e := by
    intro U hU
    have : e '' U = π '' (Subtype.val '' U) := by
      ext p; simp [he]
    rw [this]
    refine pi_isOpen_image_off hπ hπS (hΩo.isOpenMap_subtype_val U hU) ?_
    rw [disjoint_left]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hemb : IsEmbedding e :=
    (IsOpenEmbedding.of_continuous_injective_isOpenMap hec hinj hopen).isEmbedding
  have hVr : V ⊆ range e := by
    intro v hv
    obtain ⟨z, rfl⟩ := hπ.surjective v
    have hz : z ∈ Ω := fun hz => disjoint_left.1 hVE hv ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  have hpre : IsPreconnected (e ⁻¹' V) := by
    rw [← hemb.isInducing.isPreconnected_image, image_preimage_eq_of_subset hVr]
    exact hV
  have hsub : π ⁻¹' V = Subtype.val '' (e ⁻¹' V) := by
    ext z
    constructor
    · intro hz
      have hzΩ : z ∈ Ω := fun h => disjoint_left.1 hVE hz ⟨z, h, rfl⟩
      exact ⟨⟨z, hzΩ⟩, hz, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact hx
  rw [hsub]
  exact hpre.image _ continuous_subtype_val.continuousOn

/-! ## Arcs pulled back through an embedding -/

/-- **An arc in `F[Q]` pulls back to an arc in `Q`**, when `F` restricted to `Q` is an embedding. -/
theorem tarc_pullback {Q : Set (ℝ × ℝ)} {F : ℝ × ℝ → Pt} (hF : IsEmbedding (Q.restrict F))
    {r s : Pt} {I₂ : Set Pt} (hI : TArc r s I₂) (hsub : I₂ ⊆ F '' Q) {r' s' : ℝ × ℝ}
    (hr' : r' ∈ Q) (hs' : s' ∈ Q) (hFr : F r' = r) (hFs : F s' = s) :
    TArc r' s' (Q ∩ F ⁻¹' I₂) := by
  obtain ⟨-, f, hf, hfI, hf0, hf1⟩ := hI
  have hinj : InjOn F Q := fun z hz w hw h =>
    congrArg Subtype.val (hF.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h)
  have hmem : ∀ t, f t ∈ range (Q.restrict F) := fun t => by
    obtain ⟨z, hz, hzf⟩ := hsub (hfI ▸ mem_range_self t)
    exact ⟨⟨z, hz⟩, hzf⟩
  set g : unitInterval → ℝ × ℝ := fun t => (hF.toHomeomorph.symm ⟨f t, hmem t⟩ : Q) with hg
  have hgQ : ∀ t, g t ∈ Q := fun t => (hF.toHomeomorph.symm ⟨f t, hmem t⟩).2
  have hFg : ∀ t, F (g t) = f t := fun t => by
    have := congrArg Subtype.val (hF.toHomeomorph.apply_symm_apply ⟨f t, hmem t⟩)
    rw [IsEmbedding.toHomeomorph_apply_coe] at this
    exact this
  have hgc : Continuous g := continuous_subtype_val.comp
    (hF.toHomeomorph.symm.continuous.comp (hf.continuous.subtype_mk _))
  have hg0 : g 0 = r' := hinj (hgQ 0) hr' (by rw [hFg, hf0, hFr])
  have hg1 : g 1 = s' := hinj (hgQ 1) hs' (by rw [hFg, hf1, hFs])
  have hginj : Function.Injective g := fun t u h => hf.injective (by rw [← hFg, ← hFg, h])
  have hrange : range g = Q ∩ F ⁻¹' I₂ := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨hgQ t, show F (g t) ∈ I₂ by rw [hFg, ← hfI]; exact mem_range_self t⟩
    · rintro ⟨hzQ, hzI⟩
      rw [← hfI] at hzI
      obtain ⟨t, ht⟩ := hzI
      exact ⟨t, hinj (hgQ t) hzQ (by rw [hFg, ht])⟩
  have := TArc.of_inj hgc hginj
  rwa [hg0, hg1, hrange] at this

/-! ## Item A: `D` in the plane -/

/-- **Hagopian's `D`** (p. 346), from an arc `I₂` as produced by `hagopian76_T7`: `I₂` pulls back to
an arc `I` of the collar rectangle; `D′` is the domain of `rect_domain_aux` for `I`; `D = F[D′]`. -/
theorem hagopian76_D_aux {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc : 0 < c) (hc1 : c ≤ 1)
    {r s : Pt} {I₂ : Set Pt} (hI : TArc r s I₂) (hIR : I₂ ⊆ F '' (Icc a b ×ˢ Ioc 0 c))
    (hIs : I₂ ∩ F '' (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r, s})
    (hr : r ∈ F '' (({a} : Set ℝ) ×ˢ Ioc 0 c)) (hs : s ∈ F '' (({b} : Set ℝ) ×ˢ Ioc 0 c)) :
    ∃ (r₂ s₂ : ℝ) (D' : Set (ℝ × ℝ)), r₂ ∈ Ioc 0 c ∧ s₂ ∈ Ioc 0 c ∧ F (a, r₂) = r ∧
      F (b, s₂) = s ∧ TArc (a, r₂) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∧
      (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {(a, r₂), (b, s₂)} ∧
      IsOpen D' ∧ IsConnected D' ∧ D' ⊆ Ioo a b ×ˢ Ioo 0 c ∧
      frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂ ∧
      IsOpen (F '' D') ∧ IsConnected (F '' D') ∧ Bornology.IsBounded (F '' D') ∧
      F '' D' ⊆ F '' (Ioo a b ×ˢ Ioo 0 c) ∧
      frontier (F '' D') = I₂ ∪ F '' (Icc a b ×ˢ {0}) ∪ F '' (({a} : Set ℝ) ×ˢ Icc 0 r₂) ∪
        F '' (({b} : Set ℝ) ×ˢ Icc 0 s₂) := by
  obtain ⟨hFemb, -, hFopen⟩ := hF
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hFemb.continuous
  have hFinj : InjOn F R1 := fun z hz w hw h =>
    congrArg Subtype.val (hFemb.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h)
  have hRR1 : Icc a b ×ˢ Icc 0 c ⊆ R1 :=
    fun z ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  set Q : Set (ℝ × ℝ) := Icc a b ×ˢ Ioc 0 c with hQ
  have hQR : Q ⊆ Icc a b ×ˢ Icc 0 c := Set.prod_mono subset_rfl Ioc_subset_Icc_self
  have hQR1 : Q ⊆ R1 := hQR.trans hRR1
  have hQemb : IsEmbedding (Q.restrict F) := by
    have : Q.restrict F = R1.restrict F ∘ Set.inclusion hQR1 := rfl
    rw [this]; exact hFemb.comp (IsEmbedding.inclusion hQR1)
  obtain ⟨r', ⟨hr'1, hr'2⟩, hFr⟩ := hr
  obtain ⟨s', ⟨hs'1, hs'2⟩, hFs⟩ := hs
  have hr'a : r'.1 = a := hr'1
  have hs'b : s'.1 = b := hs'1
  have hr'Q : r' ∈ Q := ⟨by rw [hr'a]; exact ⟨le_rfl, hab.le⟩, hr'2⟩
  have hs'Q : s' ∈ Q := ⟨by rw [hs'b]; exact ⟨hab.le, le_rfl⟩, hs'2⟩
  set I : Set (ℝ × ℝ) := Q ∩ F ⁻¹' I₂ with hIdef
  have hI' : TArc r' s' I := tarc_pullback hQemb hI hIR hr'Q hs'Q hFr hFs
  have hSR1 : ({a, b} : Set ℝ) ×ˢ Icc 0 c ⊆ R1 := by
    rintro z ⟨h1, h2, h3⟩
    rcases h1 with h1 | h1 <;>
      exact ⟨⟨by rw [h1]; linarith, by rw [h1]; linarith⟩, by linarith, by linarith⟩
  have hIs' : I ∩ (({a, b} : Set ℝ) ×ˢ Icc 0 c) = {r', s'} := by
    apply subset_antisymm
    · rintro z ⟨⟨hzQ, hzI⟩, hzS⟩
      have : F z ∈ I₂ ∩ F '' (({a, b} : Set ℝ) ×ˢ Icc 0 c) := ⟨hzI, z, hzS, rfl⟩
      rw [hIs] at this
      rcases this with h | h
      · exact Or.inl (hFinj (hQR1 hzQ) (hQR1 hr'Q) (h.trans hFr.symm))
      · exact Or.inr (hFinj (hQR1 hzQ) (hQR1 hs'Q) (h.trans hFs.symm))
    · rintro z (rfl | rfl)
      · exact ⟨⟨hr'Q, show F z ∈ I₂ by rw [hFr]; exact hI.left_mem⟩,
          Or.inl hr'a, hr'2.1.le, hr'2.2⟩
      · exact ⟨⟨hs'Q, show F z ∈ I₂ by rw [hFs]; exact hI.right_mem⟩,
          Or.inr hs'b, hs'2.1.le, hs'2.2⟩
  obtain ⟨D', hDo, hDc, -, hDR, hDf⟩ :=
    rect_domain_aux hab hc hI' inter_subset_left hr'a hs'b hIs'
  have hr'eq : r' = (a, r'.2) := Prod.ext hr'a rfl
  have hs'eq : s' = (b, s'.2) := Prod.ext hs'b rfl
  have hDR1 : D' ⊆ R1 := hDR.trans ((Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans hRR1)
  have hclR : closure D' ⊆ Icc a b ×ˢ Icc 0 c :=
    closure_minimal (hDR.trans (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
      (isClosed_Icc.prod isClosed_Icc)
  have hclR1 : closure D' ⊆ R1 := hclR.trans hRR1
  -- `F[D′]` is open
  have hFDo : IsOpen (F '' D') := by
    obtain ⟨W, hWo, hW⟩ := hFemb.isInducing.isOpen_iff.1
      (hDo.preimage continuous_subtype_val : IsOpen ((Subtype.val : R1 → ℝ × ℝ) ⁻¹' D'))
    have : F '' D' = W ∩ F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨?_, z, ?_, rfl⟩
        · have : (⟨z, hDR1 hz⟩ : R1) ∈ R1.restrict F ⁻¹' W := by rw [hW]; exact hz
          exact this
        · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hz
          exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      · rintro ⟨hpW, z, hz, rfl⟩
        have hzR1 : z ∈ R1 := ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩
        have : (⟨z, hzR1⟩ : R1) ∈ R1.restrict F ⁻¹' W := hpW
        rw [hW] at this
        exact ⟨z, this, rfl⟩
    rw [this]; exact hWo.inter hFopen
  have hclc : IsCompact (closure D') :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure hclR
  have hcl : closure (F '' D') = F '' closure D' := by
    apply subset_antisymm
    · exact closure_minimal (image_mono subset_closure)
        (hclc.image_of_continuousOn (hFc.mono hclR1)).isClosed
    · exact (hFc.mono hclR1).image_closure
  have hFI : F '' I = I₂ := by
    rw [hIdef, image_inter_preimage]; exact inter_eq_right.2 hIR
  have hfr : frontier (F '' D') = F '' frontier D' := by
    rw [hFDo.frontier_eq, hDo.frontier_eq, hcl]
    ext p
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzD⟩
      exact ⟨z, ⟨hz, fun h => hzD ⟨z, h, rfl⟩⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzD⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rintro ⟨w, hw, hwz⟩
      exact hzD (hFinj (hclR1 hz) (hDR1 hw) hwz.symm ▸ hw)
  refine ⟨r'.2, s'.2, D', hr'2, hs'2, by rw [← hr'eq]; exact hFr, by rw [← hs'eq]; exact hFs,
    by rw [← hr'eq, ← hs'eq]; exact hI', by rw [← hr'eq, ← hs'eq]; exact hIs', hDo, hDc, hDR, hDf, hFDo, hDc.image F (hFc.mono hDR1),
    ?_, image_mono hDR, ?_⟩
  · exact (hclc.image_of_continuousOn (hFc.mono hclR1)).isBounded.subset
      (image_mono subset_closure)
  · rw [hfr, hDf, image_union, image_union, image_union, hFI]

/-! ## Item B: `K₀` -/

/-- A point of the plane over `γ t` lies in the layer `k⁻¹(t)`. -/
theorem mem_toPt_layer_of_pi_eq {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {z : Pt} {t : unitInterval}
    (hz : π z = γ t) : z ∈ toPt (layer k t) := by
  obtain ⟨x₀, hx₀⟩ := layer_nonempty hE.2.1.2.1 t
  obtain ⟨e, he, -⟩ := hx₀
  have he' : k e = t := he
  have h1 : π z = π ((e : M) : Pt) := by
    rw [hz, hγπ t _ ⟨(e : M), ⟨e, he, rfl⟩, rfl⟩]
  have h2 := (hπS _ _).1 h1
  change z ∈ HPC.Moore.elt (layerSetoid k) ((e : M) : Pt) at h2
  rw [elt_layerSetoid_of_mem, he'] at h2
  exact h2

/-- **`K₀`** (commission 166 §1.B). With `w` the lowest point of `I` (the pull-back of `I₂`) on the
vertical over `t₀ ∈ (a, b)`, the open segment `{t₀} × (0, w₂)` lies in `D′`, and
`K₀ = π⁻¹F[{t₀} × (0, w₂)]` is a connected component of `π⁻¹[D ∩ F[{t₀} × (0, c)]]` missing `E`,
whose closure meets the layer `k⁻¹(t₀)` and `π⁻¹[I₂]`. -/
theorem K0_aux {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k)
    {π : Pt → Pt} {γ : unitInterval → Pt} (hπ : IsQuotientMap π)
    (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q) (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t)
    {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc1 : c ≤ 1) {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((a, r₂) : ℝ × ℝ) (b, s₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂))
    {D' : Set (ℝ × ℝ)} (hDo : IsOpen D') (hDR : D' ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D' = (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∪ Icc a b ×ˢ {0} ∪
        ({a} : Set ℝ) ×ˢ Icc 0 r₂ ∪ ({b} : Set ℝ) ×ˢ Icc 0 s₂)
    (t₀ : unitInterval) (ht₀ : (t₀ : ℝ) ∈ Ioo a b) :
    ∃ w₂ ∈ Ioc 0 c, F ((t₀ : ℝ), w₂) ∈ I₂ ∧
      Disjoint (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂) (Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂) ∧
      ({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D' ∧
      π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂)) ⊆
        π ⁻¹' (F '' D' ∩ F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 c)) ∧
      (∀ S ⊆ π ⁻¹' (F '' D' ∩ F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 c)), IsPreconnected S →
        (S ∩ π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))).Nonempty →
        S ⊆ π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) ∧
      IsPreconnected (π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) ∧
      Disjoint (π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) (toPt E) ∧
      (closure (π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) ∩ toPt (layer k t₀)).Nonempty ∧
      (closure (π ⁻¹' (F '' (({(t₀ : ℝ)} : Set ℝ) ×ˢ Ioo 0 w₂))) ∩ π ⁻¹' I₂).Nonempty := by
  obtain ⟨hFemb, hF0, -⟩ := hF
  set R1 : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hR1
  have hFc : ContinuousOn F R1 := continuousOn_iff_continuous_restrict.2 hFemb.continuous
  have hFinj : InjOn F R1 := fun z hz w hw h =>
    congrArg Subtype.val (hFemb.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h)
  set x₀ : ℝ := (t₀ : ℝ) with hx₀
  have hx₀R : x₀ ∈ Icc (0 : ℝ) 1 := ⟨t₀.2.1, t₀.2.2⟩
  set I := Icc a b ×ˢ Ioc 0 c ∩ F ⁻¹' I₂ with hIdef
  have hIc : IsCompact I := hI.isCompact
  have hI0 : ∀ z ∈ I, 0 < z.2 := fun z hz => hz.1.2.1
  have hfst : x₀ ∈ Prod.fst '' I := by
    have hpc : IsPreconnected (Prod.fst '' I) :=
      hI.isPreconnected.image _ continuous_fst.continuousOn
    exact hpc.Icc_subset ⟨_, hI.left_mem, rfl⟩ ⟨_, hI.right_mem, rfl⟩ ⟨ht₀.1.le, ht₀.2.le⟩
  set Iv := I ∩ Prod.fst ⁻¹' {x₀} with hIv
  have hIvc : IsCompact Iv := hIc.inter_right (isClosed_singleton.preimage continuous_fst)
  have hIvne : Iv.Nonempty := by
    obtain ⟨z, hz, hzx⟩ := hfst; exact ⟨z, hz, hzx⟩
  obtain ⟨w, hwIv, hwmin⟩ := hIvc.exists_isMinOn hIvne continuous_snd.continuousOn
  set w₂ := w.2 with hw₂def
  have hwx : w.1 = x₀ := hwIv.2
  have hweq : w = (x₀, w₂) := Prod.ext hwx rfl
  have hw₂ : w₂ ∈ Ioc 0 c := hwIv.1.1.2
  have hwI : (x₀, w₂) ∈ I := hweq ▸ hwIv.1
  have hFw : F (x₀, w₂) ∈ I₂ := hwI.2
  set seg : Set (ℝ × ℝ) := ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂ with hseg
  have hdisj : Disjoint seg I := by
    rw [disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, hy⟩ hzI
    have hx' : x = x₀ := hx
    have := isMinOn_iff.1 hwmin (x, y) ⟨hzI, hx'⟩
    exact absurd this (not_le.2 hy.2)
  have hsegD : seg ⊆ D' :=
    rect_domain_vert (r := ((a, r₂) : ℝ × ℝ)) (s := ((b, s₂) : ℝ × ℝ)) hab hIc hI0 hDR hDf ht₀
      hw₂.1 hdisj
  have hsegR1 : seg ⊆ R1 := fun z ⟨hx, hy⟩ => by
    have hx' : z.1 = x₀ := hx
    exact ⟨by rw [hx']; exact hx₀R, by linarith [hy.1], by linarith [hy.2, hw₂.2]⟩
  have hvertR1 : ({x₀} : Set ℝ) ×ˢ Ioo 0 c ⊆ R1 := fun z ⟨hx, hy⟩ => by
    have hx' : z.1 = x₀ := hx
    exact ⟨by rw [hx']; exact hx₀R, by linarith [hy.1], by linarith [hy.2]⟩
  have hDR1 : D' ⊆ R1 := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hDR hz
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  set V := F '' seg with hV
  have hVpc : IsPreconnected V :=
    ((convex_singleton x₀).prod (convex_Ioo 0 w₂)).isPreconnected.image F (hFc.mono hsegR1)
  have hVE : Disjoint V (π '' toPt E) := by
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨u, hu, hFu⟩
    obtain ⟨e, rfl⟩ := mem_toPt_iff.1 hu
    have h1 : π ((e : M) : Pt) = γ (k e) := hγπ (k e) _ ⟨(e : M), ⟨e, rfl, rfl⟩, rfl⟩
    rw [h1, ← hF0] at hFu
    have := hFinj ⟨⟨(k e).2.1, (k e).2.2⟩, by norm_num, by norm_num⟩ (hsegR1 hz) hFu
    have h2 := congrArg Prod.snd this
    simp only at h2
    linarith [hz.2.1]
  have hclV : closure V ⊆ π '' closure (π ⁻¹' V) := by
    have hcl : IsClosed (π '' closure (π ⁻¹' V)) :=
      pi_isClosedMap hE hπ hπS _ isClosed_closure
    refine closure_minimal ?_ hcl
    intro v hv
    obtain ⟨z, rfl⟩ := hπ.surjective v
    exact ⟨z, subset_closure hv, rfl⟩
  have hseg_cl : ∀ y ∈ Icc 0 w₂, F (x₀, y) ∈ closure V := by
    intro y hy
    have hsc : closure seg = ({x₀} : Set ℝ) ×ˢ Icc 0 w₂ := by
      rw [hseg, closure_prod_eq, closure_singleton, closure_Ioo hw₂.1.ne]
    have hcR1 : closure seg ⊆ R1 := by
      rw [hsc]
      rintro z ⟨hx, hy⟩
      have hx' : z.1 = x₀ := hx
      exact ⟨by rw [hx']; exact hx₀R, by linarith [hy.1], by linarith [hy.2, hw₂.2]⟩
    exact (hFc.mono hcR1).image_closure ⟨(x₀, y), by rw [hsc]; exact ⟨rfl, hy⟩, rfl⟩
  refine ⟨w₂, hw₂, hFw, hdisj, hsegD, ?_, ?_, pi_preimage_isPreconnected hE hπ hπS hVpc hVE,
    ?_, ?_, ?_⟩
  · rintro z ⟨y, hy, hyz⟩
    exact ⟨⟨y, hsegD hy, hyz⟩, ⟨y, ⟨hy.1, hy.2.1, hy.2.2.trans_le hw₂.2⟩, hyz⟩⟩
  · rintro S hS hSc ⟨z₀, hz₀S, hz₀K⟩
    set T' := π '' S with hT'
    have hT'pc : IsPreconnected T' := hSc.image _ hπ.continuous.continuousOn
    set vert : Set (ℝ × ℝ) := ({x₀} : Set ℝ) ×ˢ Ioo 0 c with hvert
    set T := vert ∩ F ⁻¹' T' with hT
    have hTD : T ⊆ D' := by
      rintro z ⟨hzv, u, huS, hu⟩
      obtain ⟨⟨y, hyD, hy⟩, -⟩ := hS huS
      have : y = z := hFinj (hDR1 hyD) (hvertR1 hzv) (hy.trans hu)
      rw [← this]; exact hyD
    have hT'r : T' ⊆ range (R1.restrict F) := by
      rintro _ ⟨u, huS, rfl⟩
      obtain ⟨-, ⟨v, hv, hvu⟩⟩ := hS huS
      exact ⟨⟨v, hvertR1 hv⟩, hvu⟩
    have hTpc : IsPreconnected T := by
      have h1 : IsPreconnected (R1.restrict F ⁻¹' T') := by
        rw [← hFemb.isInducing.isPreconnected_image, image_preimage_eq_of_subset hT'r]
        exact hT'pc
      have heq : T = Subtype.val '' (R1.restrict F ⁻¹' T') := by
        ext z
        constructor
        · rintro ⟨hzv, hzT⟩
          exact ⟨⟨z, hvertR1 hzv⟩, hzT, rfl⟩
        · rintro ⟨z, hzT, rfl⟩
          refine ⟨?_, hzT⟩
          obtain ⟨u, huS, hu⟩ := hzT
          obtain ⟨-, ⟨v, hv, hvu⟩⟩ := hS huS
          have : v = (z : ℝ × ℝ) := hFinj (hvertR1 hv) z.2 (hvu.trans hu)
          rw [← this]; exact hv
      rw [heq]
      exact h1.image _ continuous_subtype_val.continuousOn
    obtain ⟨y₀, hy₀seg, hy₀⟩ := hz₀K
    have hy₀T : y₀ ∈ T :=
      ⟨⟨hy₀seg.1, hy₀seg.2.1, hy₀seg.2.2.trans_le hw₂.2⟩, z₀, hz₀S, hy₀.symm⟩
    have hTseg : T ⊆ seg := by
      intro z hzT
      refine ⟨hzT.1.1, hzT.1.2.1, ?_⟩
      by_contra hge
      rw [not_lt] at hge
      have hpc := hTpc.image _ continuous_snd.continuousOn
      obtain ⟨u, huT, hu2⟩ := hpc.Icc_subset ⟨y₀, hy₀T, rfl⟩ ⟨z, hzT, rfl⟩
        ⟨hy₀seg.2.2.le, hge⟩
      have hu1 : u.1 = x₀ := huT.1.1
      have hu : u = (x₀, w₂) := Prod.ext hu1 hu2
      have huF : u ∈ frontier D' := by
        rw [hDf, hu]; exact Or.inl (Or.inl (Or.inl hwI))
      rw [hDo.frontier_eq] at huF
      exact huF.2 (hTD huT)
    intro u huS
    obtain ⟨-, ⟨v, hv, hvu⟩⟩ := hS huS
    exact ⟨v, hTseg ⟨hv, u, huS, hvu.symm⟩, hvu⟩
  · rw [disjoint_left]
    intro z hzK hzE
    exact disjoint_left.1 hVE hzK ⟨z, hzE, rfl⟩
  · obtain ⟨z, hz, hπz⟩ := hclV (hseg_cl 0 ⟨le_rfl, hw₂.1.le⟩)
    refine ⟨z, hz, mem_toPt_layer_of_pi_eq hE hπS hγπ ?_⟩
    rw [hπz, hx₀, hF0]
  · obtain ⟨z, hz, hπz⟩ := hclV (hseg_cl w₂ ⟨hw₂.1.le, le_rfl⟩)
    refine ⟨z, hz, ?_⟩
    show π z ∈ I₂
    rw [hπz]; exact hFw

end DCollar

end HPC.Hagopian
