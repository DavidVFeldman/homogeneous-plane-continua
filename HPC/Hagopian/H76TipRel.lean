import HPC.Hagopian.H76Tip

/-!
# Batch 181, §1.4: the mirror tip lemmas with the hypothesis relaxed

Commission 181 §1.4.3: `tip_triod_mirror` asks for the extreme point over `D` and uses it only to
bound `σ` (`tip_param_low`, `tip_param_high`). The proof needs exactly `2/n < σ < 1`: the interval
`[σ − δ, σ + δ]` must lie in `(2/n, 1]` (S0 keeps `Q_δ` off `k⁻¹(0)`, and the point at `σ + δ/2`
must exist). Here `δ` is chosen below `(σ − 2/n)/2` and `(1 − σ)/2`; `n ≥ 40` and the cross region
are no longer used. For `σ = τ₁` of §1.4 step 3 the hypotheses are `τ₁ < 1` (the case) and
`τ₁ > τ > 2/n` (the tip of `zⱼ` is over `D`, `tip_param_low`).

The files of batch 180 are unchanged; these are variants.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section TipRel

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§2.1, mirror form, relaxed** (commission 181 §1.4.3): as `tip_meets_end_layer_mirror`, with
the extreme point over `D` replaced by the bound `2/n < σ < 1` that the proof really needs. -/
theorem tip_meets_end_layer_mirror_rel (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) {G : Set M}
    {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0)
    (h : M ≃ₜ M) (hh : ∀ v, dist (h v) v < θ / 4) (b : unitInterval) {σ : unitInterval}
    (hσ : ∃ e₀ : E, k e₀ = σ ∧ b ≤ k e₀ ∧ h e₀ ∈ G)
    (hσl : 2 / (n : ℝ) < σ) (hσ1 : (σ : ℝ) < 1)
    (hσmax : ∀ e' : E, b ≤ k e' → h e' ∈ G → k e' ≤ σ) :
    ∃ e' : E, k e' = σ ∧ h e' ∈ layer d 1 := by
  obtain ⟨e₀, hke₀, hle₀, hG₀⟩ := hσ
  have hc := hS.c_pos
  by_contra hno
  push_neg at hno
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hE.isCompact
  have hkc : Continuous fun e' : E => ((k e' : unitInterval) : ℝ) :=
    continuous_subtype_val.comp hE.2.1.1
  obtain ⟨δ₁, hδ₁, hsep⟩ : ∃ δ₁ > 0, ∀ e' : E, |((k e' : unitInterval) : ℝ) - σ| < δ₁ →
      h e' ∉ layer d 1 := by
    set B : Set E := {e' | h e' ∈ layer d 1} with hB
    have hBc : IsCompact B :=
      ((isClosed_layer hG.isCompact hG.2.1.1 1).preimage
        (h.continuous.comp continuous_subtype_val)).isCompact
    by_cases hBne : B.Nonempty
    · obtain ⟨b', hb', hmin⟩ := hBc.exists_isMinOn hBne
        (continuous_abs.comp (hkc.sub continuous_const)).continuousOn
      have hpos : 0 < |((k b' : unitInterval) : ℝ) - σ| :=
        abs_pos.2 (sub_ne_zero.2 fun h' => hno b' (Subtype.ext h') hb')
      exact ⟨_, hpos, fun e' he' hmem => absurd (hmin hmem) (not_le.2 he')⟩
    · exact ⟨1, one_pos, fun e' _ hmem => hBne ⟨e', hmem⟩⟩
  set δ := min δ₁ (min ((σ : ℝ) - 2 / (n : ℝ)) (1 - σ)) / 2 with hδdef
  have hm0 : 0 < min ((σ : ℝ) - 2 / (n : ℝ)) (1 - σ) := lt_min (by linarith) (by linarith)
  have hδ0 : 0 < δ := by have := lt_min hδ₁ hm0; linarith
  have hδ1 : δ < δ₁ := by have := min_le_left δ₁ (min ((σ : ℝ) - 2 / (n : ℝ)) (1 - σ)); linarith
  have hδ2 : δ ≤ min ((σ : ℝ) - 2 / (n : ℝ)) (1 - σ) / 2 := by
    have := min_le_right δ₁ (min ((σ : ℝ) - 2 / (n : ℝ)) (1 - σ)); linarith
  have hσδ : 2 / (n : ℝ) < (σ : ℝ) - δ := by
    have := min_le_left ((σ : ℝ) - 2 / (n : ℝ)) (1 - σ); linarith
  have hσδ' : (σ : ℝ) + δ < 1 := by
    have := min_le_right ((σ : ℝ) - 2 / (n : ℝ)) (1 - σ); linarith
  set S : Set unitInterval := {t | (σ : ℝ) - δ ≤ (t : ℝ) ∧ (t : ℝ) ≤ σ + δ} with hSdef
  have hσS : σ ∈ S := ⟨by linarith, by linarith⟩
  set Q : Set M := h '' (Subtype.val '' (k ⁻¹' S)) with hQ
  have hQc : Fold.Q78.IsContinuum Q := by
    have h0 := isContinuum_img hE.isCompact hE.2.1 (isClosed_interval_set _ _)
      (isPreconnected_interval_set _ _) ⟨σ, hσS⟩
    exact ⟨h0.1.image h.continuous, h0.2.image _ h.continuous.continuousOn⟩
  have hQG : (Q ∩ G).Nonempty :=
    ⟨h e₀, ⟨_, ⟨e₀, by show k e₀ ∈ S; rw [hke₀]; exact hσS, rfl⟩, rfl⟩, hG₀⟩
  have hQ0 : Disjoint Q (layer d 0) := by
    rw [hX0, disjoint_left]
    rintro _ ⟨_, ⟨e', he'S, rfl⟩, rfl⟩ ⟨e'', he''0, he''eq⟩
    have hk0 : ((k e'' : unitInterval) : ℝ) = 0 := by
      rw [mem_preimage, mem_singleton_iff] at he''0; rw [he''0]; rfl
    have hπ0 : π ((h e' : M) : Pt) = F (0, 0) := by
      rw [← he''eq, pi_E_eq hγπ hF e'', hk0]
    have := hS.fine h hh e' (0, 0) ⟨⟨le_rfl, zero_le_one⟩, by linarith, hc.le⟩ hπ0
    have hS1 := he'S.1
    rw [sub_zero] at this
    linarith [(abs_lt.1 this).2]
  have hQ1 : Disjoint Q (layer d 1) := by
    rw [disjoint_left]
    rintro _ ⟨_, ⟨e', he'S, rfl⟩, rfl⟩ hq
    refine hsep e' ?_ hq
    rw [abs_lt]
    constructor <;> linarith [he'S.1, he'S.2]
  have hQsub := hagopian76_no_hair hX hi hG hQc hQG hQ0 hQ1
  have ht0 : (0 : ℝ) ≤ (σ : ℝ) + δ / 2 := by linarith [σ.2.1]
  have ht1 : (σ : ℝ) + δ / 2 ≤ 1 := by linarith
  obtain ⟨e', he'⟩ := hE.2.1.2.1 ⟨(σ : ℝ) + δ / 2, ht0, ht1⟩
  have hke' : ((k e' : unitInterval) : ℝ) = (σ : ℝ) + δ / 2 := by rw [he']
  have he'G : h e' ∈ G := hQsub ⟨_, ⟨e', ⟨by rw [hke']; linarith, by rw [hke']; linarith⟩, rfl⟩,
    rfl⟩
  have hle : b ≤ k e' := by
    show ((b : unitInterval) : ℝ) ≤ k e'
    have : ((b : unitInterval) : ℝ) ≤ k e₀ := hle₀
    rw [hke₀] at this
    linarith
  have := hσmax e' hle he'G
  have : (k e' : ℝ) ≤ (σ : ℝ) := this
  linarith

/-- **2a, mirror form, relaxed** (commission 181 §1.4.3): as `tip_triod_mirror`, with the extreme
point over `D` replaced by `2/n < σ < 1`. -/
theorem tip_triod_mirror_rel (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (b : unitInterval) {σ : unitInterval}
    (hσ : ∃ e₀ : E, k e₀ = σ ∧ b ≤ k e₀ ∧ h e₀ ∈ G)
    (hσl : 2 / (n : ℝ) < σ) (hσ1 : σ < 1)
    (hσmax : ∀ e' : E, b ≤ k e' → h e' ∈ G → k e' ≤ σ)
    (h_i : ∃ e₁ : E, b ≤ k e₁ ∧ h e₁ ∈ G ∧ h e₁ ∉ layer d 1 ∧ k e₁ ≠ σ)
    (h_iii : ¬ layer d 1 ⊆ h '' E) : False := by
  obtain ⟨e', hke', he'1⟩ := tip_meets_end_layer_mirror_rel hX hi hE hγπ hF hS hG hX0 h hh
    b hσ hσl hσ1 hσmax
  have hZc := tip_Z_continuum hX hi hE hG h hke' he'1
  obtain ⟨e₀, hke₀, hle₀, hG₀⟩ := hσ
  have hAT := (hagopian75_lemma1 hX hi).1
  have hHU := hereditarilyUnicoherent_of_homogeneous_indecomposable hX hi
  have hbσ : b ≤ σ := by rw [← hke₀]; exact hle₀
  have hinj : ∀ a a' : E, h a = h a' → a = a' := fun a a' hab =>
    Subtype.ext (h.injective hab)
  have himg : ∀ {P : Set M}, Fold.Q78.IsContinuum P → Fold.Q78.IsContinuum (h '' P) :=
    fun hP => ⟨hP.1.image h.continuous, hP.2.image _ h.continuous.continuousOn⟩
  set Kset : Set M := G ∩ h '' layerSet k (Icc b 1) with hKset
  set Pset : Set M := h '' layerSet k (Icc σ 1) with hPset
  set Λ : Set M := layer d 1 ∩ h '' E with hΛ
  set tip : Set M := h '' layer k σ with htip
  set A1 : Set M := Kset \ (Λ ∪ tip) with hA1
  set A2 : Set M := h '' layerSet k (Ioc σ 1) with hA2
  set A3 : Set M := layer d 1 \ h '' E with hA3
  have hL1G : layer d 1 ⊆ G := by rintro _ ⟨g, -, rfl⟩; exact g.2
  have hL1c : Fold.Q78.IsContinuum (layer d 1) := isContinuum_layer hG.isCompact hG.2.1 1
  have hPc : Fold.Q78.IsContinuum Pset :=
    himg (isContinuum_img hE.isCompact hE.2.1 isClosed_Icc isPreconnected_Icc
      ⟨1, unitInterval.le_one', le_rfl⟩)
  have hKe : Fold.Q78.IsContinuum (h '' layerSet k (Icc b 1)) :=
    himg (isContinuum_img hE.isCompact hE.2.1 isClosed_Icc isPreconnected_Icc
      ⟨1, unitInterval.le_one', le_rfl⟩)
  have hmem0 : h e₀ ∈ Kset := ⟨hG₀, e₀, ⟨e₀, ⟨hle₀, unitInterval.le_one'⟩, rfl⟩, rfl⟩
  have hmem0P : h e₀ ∈ Pset := ⟨e₀, ⟨e₀, ⟨hke₀.ge, unitInterval.le_one'⟩, rfl⟩, rfl⟩
  have hKc : Fold.Q78.IsContinuum Kset :=
    isContinuum_inter_of_HU hHU (isContinuum_of_minimalAdmissible hG) hKe ⟨_, hmem0⟩
  have hmem' : h e' ∈ layer d 1 ∩ Pset :=
    ⟨he'1, e', ⟨e', ⟨hke'.ge, unitInterval.le_one'⟩, rfl⟩, rfl⟩
  have hTc : Fold.Q78.IsContinuum ((layer d 1 ∪ Pset) ∪ Kset) :=
    isContinuum_union (isContinuum_union hL1c hPc ⟨_, hmem'⟩) hKc
      ⟨_, Or.inr hmem0P, hmem0⟩
  have hKsub : Kset ⊆ h '' E := by
    rintro _ ⟨-, _, ⟨e'', -, rfl⟩, rfl⟩; exact ⟨e'', e''.2, rfl⟩
  have hPsub : Pset ⊆ h '' E := by
    rintro _ ⟨_, ⟨e'', -, rfl⟩, rfl⟩; exact ⟨e'', e''.2, rfl⟩
  have hA2G : Disjoint A2 G := by
    rw [disjoint_left]
    rintro _ ⟨_, ⟨e'', he'', rfl⟩, rfl⟩ hG''
    have hle : b ≤ k e'' := hbσ.trans (le_of_lt he''.1)
    exact absurd (hσmax e'' hle hG'') (not_le.2 he''.1)
  have hA1P : Disjoint A1 Pset := by
    rw [disjoint_left]
    rintro z ⟨⟨hzG, -⟩, hzZ⟩ ⟨_, ⟨e'', he'', rfl⟩, rfl⟩
    have hge := hσmax e'' (hbσ.trans he''.1) hzG
    exact hzZ (Or.inr ⟨e'', ⟨e'', le_antisymm hge he''.1, rfl⟩, rfl⟩)
  have hKcl : IsClosed Kset := hKc.1.isClosed
  have hPcl : IsClosed Pset := hPc.1.isClosed
  have hL1cl : IsClosed (layer d 1) := hL1c.1.isClosed
  have hclA1 : closure A1 ⊆ Kset := closure_minimal (fun z hz => hz.1) hKcl
  have hclA2 : closure A2 ⊆ Pset := closure_minimal
    (image_mono (layerSet_mono k Ioc_subset_Icc_self)) hPcl
  have hclA3 : closure A3 ⊆ layer d 1 := closure_minimal (fun z hz => hz.1) hL1cl
  refine hAT ((layer d 1 ∪ Pset) ∪ Kset) (subset_univ _) ⟨hTc, Λ ∪ tip, hZc, ?_, A1, A2, A3,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z (⟨hz1, -⟩ | ⟨_, ⟨e'', he'', rfl⟩, rfl⟩)
    · exact Or.inl (Or.inl hz1)
    · exact Or.inl (Or.inr ⟨e'', ⟨e'', ⟨le_of_eq he''.symm, unitInterval.le_one'⟩, rfl⟩, rfl⟩)
  · obtain ⟨e₁, hle₁, hG₁, h1₁, hne₁⟩ := h_i
    refine ⟨h e₁, ⟨hG₁, e₁, ⟨e₁, ⟨hle₁, unitInterval.le_one'⟩, rfl⟩, rfl⟩, ?_⟩
    rintro (⟨h1, -⟩ | ⟨_, ⟨e'', he'', rfl⟩, hh''⟩)
    · exact h1₁ h1
    · exact hne₁ (by rw [← hinj _ _ hh'']; exact he'')
  · obtain ⟨e'', he''⟩ := hE.2.1.2.1 1
    exact ⟨h e'', e'', ⟨e'', ⟨by rw [he'']; exact hσ1, le_of_eq he''⟩, rfl⟩, rfl⟩
  · obtain ⟨z, hz1, hzE⟩ := not_subset.1 h_iii
    exact ⟨z, hz1, hzE⟩
  · ext z
    simp only [mem_diff, mem_union]
    constructor
    · rintro ⟨(hz1 | hzP) | hzK, hzZ⟩
      · by_cases hzE : z ∈ h '' E
        · exact absurd (Or.inl ⟨hz1, hzE⟩) hzZ
        · exact Or.inr ⟨hz1, hzE⟩
      · obtain ⟨_, ⟨e'', he'', rfl⟩, rfl⟩ := hzP
        rcases lt_or_eq_of_le he''.1 with hlt | heq
        · exact Or.inl (Or.inr ⟨e'', ⟨e'', ⟨hlt, he''.2⟩, rfl⟩, rfl⟩)
        · exact absurd (Or.inr ⟨e'', ⟨e'', heq.symm, rfl⟩, rfl⟩) hzZ
      · exact Or.inl (Or.inl ⟨hzK, hzZ⟩)
    · rintro ((⟨hzK, hzZ⟩ | hz2) | ⟨hz1, hzE⟩)
      · exact ⟨Or.inr hzK, hzZ⟩
      · refine ⟨Or.inl (Or.inr (hclA2 (subset_closure hz2))), ?_⟩
        rintro (⟨hz1, -⟩ | ⟨_, ⟨e'', he'', rfl⟩, hh''⟩)
        · exact disjoint_left.1 hA2G hz2 (hL1G hz1)
        · obtain ⟨_, ⟨e₃, he₃, rfl⟩, h₃⟩ := hz2
          have := hinj _ _ (h₃.trans hh''.symm)
          subst this
          have h3 : k e₃ = σ := he''
          exact absurd h3 (ne_of_gt he₃.1)
      · refine ⟨Or.inl (Or.inl hz1), ?_⟩
        rintro (⟨-, hzE'⟩ | ⟨_, ⟨e'', -, rfl⟩, rfl⟩)
        · exact hzE hzE'
        · exact hzE ⟨e'', e''.2, rfl⟩
  · exact disjoint_left.2 fun z hz hz2 => disjoint_left.1 hA2G hz2 (hclA1 hz).1
  · exact disjoint_left.2 fun z hz hz2 => disjoint_left.1 hA1P hz (hclA2 hz2)
  · exact disjoint_left.2 fun z hz hz3 => hz3.2 (hKsub (hclA1 hz))
  · exact disjoint_left.2 fun z hz hz3 => hz.2 (Or.inl ⟨hclA3 hz3, hKsub hz.1⟩)
  · exact disjoint_left.2 fun z hz hz3 => hz3.2 (hPsub (hclA2 hz))
  · exact disjoint_left.2 fun z hz hz3 => disjoint_left.1 hA2G hz (hL1G (hclA3 hz3))

/-- **§1.4, step 3** (commission 181 §1.4.3), in parameter form. Let `τ < τ₁ < 1` with `τ > 2/n`,
let `h(e₁)` (`k(e₁) = τ`, the point `zⱼ`) be a point of `F` off `d⁻¹(1)`, let `τ₁` be attained by a
point of `F ∩ h[E]`, and let every point of `F ∩ h[k⁻¹[[τ, 1]]]` have parameter `≤ τ₁` (so `F` misses
`h[k⁻¹((τ₁, 1])]`). Then (iii) `d⁻¹(1) ⊄ h[E]` leads to a contradiction: the mirror triod at
`σ = τ₁` (with `b = τ`, (i) given by `zⱼ` itself) contradicts atriodicity. -/
theorem chunk_edge_case_mirror (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) {τ τ₁ : unitInterval} (hττ₁ : τ < τ₁) (hτn : 2 / (n : ℝ) < τ)
    (hτ₁ : τ₁ < 1) (e₁ : E) (hke₁ : k e₁ = τ) (hG₁ : h e₁ ∈ G) (h1₁ : h e₁ ∉ layer d 1)
    (hτ₁att : ∃ e₀ : E, k e₀ = τ₁ ∧ h e₀ ∈ G)
    (hτ₁max : ∀ e' : E, τ ≤ k e' → h e' ∈ G → k e' ≤ τ₁)
    (h_iii : ¬ layer d 1 ⊆ h '' E) : False := by
  obtain ⟨e₀, hke₀, hG₀⟩ := hτ₁att
  have hτ₁n : 2 / (n : ℝ) < τ₁ := hτn.trans (Subtype.coe_lt_coe.2 hττ₁)
  exact tip_triod_mirror_rel hX hi hE hγπ hF hS hG hX0 h hh τ ⟨e₀, hke₀, hke₀ ▸ hττ₁.le, hG₀⟩
    hτ₁n hτ₁ hτ₁max ⟨e₁, hke₁.ge, hG₁, h1₁, by rw [hke₁]; exact hττ₁.ne⟩ h_iii

end TipRel

end HPC.Hagopian
