import HPC.Hagopian.H76Thm1Setup

/-!
# Batch 180, §2.1: the end layer of `F` meets the tip layer

Commission 180 §2.1 (commission 178 §3b, step 3.1). Notation of commission 179 §2: `F = G` is an
extension of `E` away from `k⁻¹(0)` with decomposition `d` (`d⁻¹(0) = k⁻¹(0)`), `h` is a
`θ/4`-homeomorphism, `e ∈ E`, `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]`, and `τ` is the least parameter of `K⁻`
(the tip; the tip layer is `h[k⁻¹(τ)]`).

* `tip_meets_end_layer`: if the tip point of `K⁻` is over `D` (as when `K⁻ ⊆ O = π⁻¹[D]`), then
  `d⁻¹(1)` meets the tip layer.
* `tip_end_layer_continuum`: consequently `Λ₁ = d⁻¹(1) ∩ h[E]` is a continuum meeting the tip layer,
  and `Z = Λ₁ ∪ h[k⁻¹(τ)]` is a continuum (the core of the triod of 2a).
* `tip_triod` (2a) and `tip_triod_on_tip_layer` (2b): the triods, against atriodicity.

*Proof of `tip_meets_end_layer`* (commission 180 §2.1, steps 1–4, arranged as a contradiction):
1. `τ > 3/22 − 2/n`, by S0 at a point of `K⁻` on the tip layer (it lies over `D`).
2. If `d⁻¹(1)` missed the tip layer, compactness of `E` would give `δ > 0` with
   `h[k⁻¹[[τ − δ, τ + δ]]] =: Q_δ` missing `d⁻¹(1)`. `Q_δ` is a continuum meeting `F` (at the tip),
   and it misses `d⁻¹(0) = k⁻¹(0)`: a point of `Q_δ` in `k⁻¹(0)` lies over `F(0, 0)`, so by S0 its
   parameter is `< 2/n`, while every parameter of `Q_δ` is `≥ τ − δ > 2/n` (here `n ≥ 40` is used:
   `3/22 > 4/n`).
3. No hair for `F` (`hagopian76_no_hair`) gives `Q_δ ⊆ F`, so `F` contains `h(e′)` with
   `k(e′) = τ − δ/2 < τ ≤ k(e)`: a point of `K⁻` below the tip. Contradiction.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Tip

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§2.1, `tip_meets_end_layer`** (commission 180 §2.1; commission 178 §3b, step 3.1). Let `G`
(Hagopian's `F`) be type A′ with `d⁻¹(0) = k⁻¹(0)`, `h` a `θ/4`-homeomorphism (S0), `b` a parameter
(`b = k(e)` for `y = h(e)`), and `K⁻ = G ∩ h[k⁻¹[[0, b]]]`. If `τ` is the least parameter of `K⁻`
(attained at a point over `D`), then `d⁻¹(1)` meets the tip layer `h[k⁻¹(τ)]`.

*Shape (left to me):* `K⁻` is given through its parameters: `hτ` says that `τ` is a parameter of a
point of `K⁻` over `D`, `hτmin` that it is the least one. Of `K⁻ ⊆ O` only the tip point over `D`
is used (step 1), and the point `y = h(e)` need not be over the inner middle; `n ≥ 40` gives
`3/22 > 4/n`. -/
theorem tip_meets_end_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 40 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (b : unitInterval) {τ : unitInterval}
    (hτ : ∃ e₀ : E, k e₀ = τ ∧ k e₀ ≤ b ∧ h e₀ ∈ G ∧ π (h e₀ : Pt) ∈ F '' D')
    (hτmin : ∀ e' : E, k e' ≤ b → h e' ∈ G → τ ≤ k e') :
    ∃ e' : E, k e' = τ ∧ h e' ∈ layer d 1 := by
  obtain ⟨e₀, hke₀, hle₀, hG₀, hD₀⟩ := hτ
  have hn' : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hu : 1 / (n : ℝ) ≤ 1 / 40 := one_div_le_one_div_of_le (by norm_num) hn'
  have h2 : 2 / (n : ℝ) = 2 * (1 / (n : ℝ)) := by ring
  have h4 : 4 / (n : ℝ) = 4 * (1 / (n : ℝ)) := by ring
  have hc := hS.c_pos
  -- step 1: `τ > 3/22 − 2/n`
  have hτlow : 3 / 22 - 2 / (n : ℝ) < (τ : ℝ) := by
    obtain ⟨w, hwD, hFw⟩ := hD₀
    have hwS := hR.sub hwD
    have hw : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-c) c :=
      ⟨⟨by linarith [hwS.1.1], by linarith [hwS.1.2]⟩, by linarith [hwS.2.1],
        by linarith [hwS.2.2]⟩
    have := hS.fine h hh e₀ w hw hFw.symm
    rw [hke₀] at this
    linarith [(abs_lt.1 this).1, hwS.1.1]
  by_contra hno
  push_neg at hno
  -- step 2: a margin `δ₁` around the tip layer missing `d⁻¹(1)`
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hE.isCompact
  have hkc : Continuous fun e' : E => ((k e' : unitInterval) : ℝ) :=
    continuous_subtype_val.comp hE.2.1.1
  obtain ⟨δ₁, hδ₁, hsep⟩ : ∃ δ₁ > 0, ∀ e' : E, |((k e' : unitInterval) : ℝ) - τ| < δ₁ →
      h e' ∉ layer d 1 := by
    set B : Set E := {e' | h e' ∈ layer d 1} with hB
    have hBc : IsCompact B :=
      ((isClosed_layer hG.isCompact hG.2.1.1 1).preimage
        (h.continuous.comp continuous_subtype_val)).isCompact
    by_cases hBne : B.Nonempty
    · obtain ⟨b, hb, hmin⟩ := hBc.exists_isMinOn hBne
        (continuous_abs.comp (hkc.sub continuous_const)).continuousOn
      have hpos : 0 < |((k b : unitInterval) : ℝ) - τ| :=
        abs_pos.2 (sub_ne_zero.2 fun h' => hno b (Subtype.ext h') hb)
      exact ⟨_, hpos, fun e' he' hmem => absurd (hmin hmem) (not_le.2 he')⟩
    · exact ⟨1, one_pos, fun e' _ hmem => hBne ⟨e', hmem⟩⟩
  set δ := min δ₁ (3 / 22 - 4 / (n : ℝ)) / 2 with hδdef
  have hm0 : 0 < 3 / 22 - 4 / (n : ℝ) := by rw [h4]; linarith
  have hδ0 : 0 < δ := by have := lt_min hδ₁ hm0; linarith
  have hδ1 : δ < δ₁ := by have := min_le_left δ₁ (3 / 22 - 4 / (n : ℝ)); linarith
  have hδ2 : δ ≤ (3 / 22 - 4 / (n : ℝ)) / 2 := by
    have := min_le_right δ₁ (3 / 22 - 4 / (n : ℝ)); linarith
  have hτδ : 2 / (n : ℝ) < (τ : ℝ) - δ := by rw [h2] at hτlow ⊢; rw [h4] at hδ2; linarith
  -- the continuum `Q_δ`
  set S : Set unitInterval := {t | (τ : ℝ) - δ ≤ (t : ℝ) ∧ (t : ℝ) ≤ τ + δ} with hSdef
  have hτS : τ ∈ S := ⟨by linarith, by linarith⟩
  set Q : Set M := h '' (Subtype.val '' (k ⁻¹' S)) with hQ
  have hQc : Fold.Q78.IsContinuum Q := by
    have h0 := isContinuum_img hE.isCompact hE.2.1 (isClosed_interval_set _ _)
      (isPreconnected_interval_set _ _) ⟨τ, hτS⟩
    exact ⟨h0.1.image h.continuous, h0.2.image _ h.continuous.continuousOn⟩
  have hQG : (Q ∩ G).Nonempty :=
    ⟨h e₀, ⟨_, ⟨e₀, by show k e₀ ∈ S; rw [hke₀]; exact hτS, rfl⟩, rfl⟩, hG₀⟩
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
  -- step 3: no hair, and a point of `K⁻` below the tip
  have hQsub := hagopian76_no_hair hX hi hG hQc hQG hQ0 hQ1
  have ht0 : (0 : ℝ) ≤ (τ : ℝ) - δ / 2 := by linarith
  have ht1 : (τ : ℝ) - δ / 2 ≤ 1 := by linarith [τ.2.2]
  obtain ⟨e', he'⟩ := hE.2.1.2.1 ⟨(τ : ℝ) - δ / 2, ht0, ht1⟩
  have hke' : ((k e' : unitInterval) : ℝ) = (τ : ℝ) - δ / 2 := by rw [he']
  have he'G : h e' ∈ G := hQsub ⟨_, ⟨e', ⟨by rw [hke']; linarith, by rw [hke']; linarith⟩, rfl⟩,
    rfl⟩
  have hle : k e' ≤ b := by
    show ((k e' : unitInterval) : ℝ) ≤ b
    have : ((k e₀ : unitInterval) : ℝ) ≤ b := hle₀
    rw [hke₀] at this
    linarith
  have := hτmin e' hle he'G
  have : (τ : ℝ) ≤ (k e' : ℝ) := this
  linarith

/-- **§2.1, consequences** (commission 180 §2.1): in the set-up of `tip_meets_end_layer`,
`Λ₁ = d⁻¹(1) ∩ h[E]` is a continuum meeting the tip layer `h[k⁻¹(τ)]`, and
`Z = Λ₁ ∪ h[k⁻¹(τ)]` is a continuum. -/
theorem tip_end_layer_continuum (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 40 ≤ n)
    {c₁ : ℝ} (hc₁ : c₁ ≤ c) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') {G : Set M}
    {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0)
    (h : M ≃ₜ M) (hh : ∀ v, dist (h v) v < θ / 4) (b : unitInterval) {τ : unitInterval}
    (hτ : ∃ e₀ : E, k e₀ = τ ∧ k e₀ ≤ b ∧ h e₀ ∈ G ∧ π (h e₀ : Pt) ∈ F '' D')
    (hτmin : ∀ e' : E, k e' ≤ b → h e' ∈ G → τ ≤ k e') :
    Fold.Q78.IsContinuum (layer d 1 ∩ h '' E) ∧
      (layer d 1 ∩ h '' E ∩ h '' layer k τ).Nonempty ∧
      Fold.Q78.IsContinuum (layer d 1 ∩ h '' E ∪ h '' layer k τ) := by
  obtain ⟨e', hke', he'1⟩ := tip_meets_end_layer hX hi hE hγπ hF hS hn hc₁ hR hG hX0 h hh b
    hτ hτmin
  have hHU := hereditarilyUnicoherent_of_homogeneous_indecomposable hX hi
  have himg : ∀ {P : Set M}, Fold.Q78.IsContinuum P → Fold.Q78.IsContinuum (h '' P) :=
    fun hP => ⟨hP.1.image h.continuous, hP.2.image _ h.continuous.continuousOn⟩
  have hEc : Fold.Q78.IsContinuum E :=
    ⟨hE.isCompact, by
      have := isContinuum_img hE.isCompact hE.2.1 isClosed_univ isPreconnected_univ
        univ_nonempty
      rw [preimage_univ, image_univ, Subtype.range_coe] at this
      exact this.2⟩
  have hmem : h e' ∈ layer d 1 ∩ h '' E := ⟨he'1, e', e'.2, rfl⟩
  have hmemτ : h e' ∈ h '' layer k τ := ⟨e', ⟨e', hke', rfl⟩, rfl⟩
  have hΛ := isContinuum_inter_of_HU hHU (isContinuum_layer hG.isCompact hG.2.1 1) (himg hEc)
    ⟨_, hmem⟩
  exact ⟨hΛ, ⟨_, hmem, hmemτ⟩,
    isContinuum_union hΛ (himg (isContinuum_layer hE.isCompact hE.2.1 τ)) ⟨_, hmem, hmemτ⟩⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- **The tip is high** (step 1 of §2.1): a parameter of a point of `G ∩ h[E]` over `D` exceeds
`3/22 − 2/n` (S0). -/
theorem tip_param_low {E : Set M} {k : E → unitInterval} {π : Pt → Pt} {F : ℝ × ℝ → Pt}
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (e₀ : E) (hD : π (h e₀ : Pt) ∈ F '' D') :
    3 / 22 - 2 / (n : ℝ) < (k e₀ : ℝ) := by
  have hc := hS.c_pos
  obtain ⟨w, hwD, hFw⟩ := hD
  have hwS := hR.sub hwD
  have hw : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-c) c :=
    ⟨⟨by linarith [hwS.1.1], by linarith [hwS.1.2]⟩, by linarith [hwS.2.1],
      by linarith [hwS.2.2]⟩
  have := hS.fine h hh e₀ w hw hFw.symm
  linarith [(abs_lt.1 this).1, hwS.1.1]

omit [CompactSpace M] [ConnectedSpace M] in
theorem isContinuum_of_minimalAdmissible {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) : Fold.Q78.IsContinuum G :=
  ⟨hG.isCompact, by
    have := isContinuum_img hG.isCompact hG.2.1 isClosed_univ isPreconnected_univ univ_nonempty
    rw [preimage_univ, image_univ, Subtype.range_coe] at this
    exact this.2⟩

/-- **2a, the tip triod** (commission 179 §2, 2a, with commission 180 §2.1). In the set-up of
`tip_meets_end_layer` (`K⁻ ⊆ O`, tip `τ`), assume
* (i) some point of `K⁻` lies off `d⁻¹(1)` and off the tip layer `h[k⁻¹(τ)]`;
* (iii) `d⁻¹(1) ⊄ h[E]`.

Then `T := d⁻¹(1) ∪ K⁻ ∪ h[k⁻¹[[0, τ]]]` is a triod over `Z := Λ₁ ∪ h[k⁻¹(τ)]`, against
atriodicity (`hagopian75_lemma1`). The arms are `K⁻ − Z`, `h[k⁻¹([0, τ))]` (it misses `F` by the
choice of `τ`) and `d⁻¹(1) − h[E]`.

*Shape (left to me):* `K⁻ = G ∩ h[k⁻¹[[0, b]]]` for a parameter `b` (`b = k(e)` in 2a; `b = τ + δ`
in 2b, `tip_triod_on_tip_layer`). The third piece of `T` is `h[k⁻¹[[0, τ]]]` (the commission's
`h[k⁻¹[[τ − δ, τ]]]` with `δ = τ`; any `0 < δ ≤ τ` works the same way). Of `K⁻ ⊆ O` only the tip
point over `D` is used. The conclusion is `False`. Mirror form: `tip_triod_mirror`. -/
theorem tip_triod (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 40 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (b : unitInterval) {τ : unitInterval}
    (hτ : ∃ e₀ : E, k e₀ = τ ∧ k e₀ ≤ b ∧ h e₀ ∈ G ∧ π (h e₀ : Pt) ∈ F '' D')
    (hτmin : ∀ e' : E, k e' ≤ b → h e' ∈ G → τ ≤ k e')
    (h_i : ∃ e₁ : E, k e₁ ≤ b ∧ h e₁ ∈ G ∧ h e₁ ∉ layer d 1 ∧ k e₁ ≠ τ)
    (h_iii : ¬ layer d 1 ⊆ h '' E) : False := by
  obtain ⟨-, -, hZc⟩ := tip_end_layer_continuum hX hi hE hγπ hF hS hn hc₁ hR hG hX0 h hh b hτ
    hτmin
  obtain ⟨e', hke', he'1⟩ := tip_meets_end_layer hX hi hE hγπ hF hS hn hc₁ hR hG hX0 h hh b
    hτ hτmin
  obtain ⟨e₀, hke₀, hle₀, hG₀, hD₀⟩ := hτ
  have hAT := (hagopian75_lemma1 hX hi).1
  have hHU := hereditarilyUnicoherent_of_homogeneous_indecomposable hX hi
  have hn' : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : 1 / (n : ℝ) ≤ 1 / 40 := one_div_le_one_div_of_le (by norm_num) hn'
  have h2 : 2 / (n : ℝ) = 2 * (1 / (n : ℝ)) := by ring
  have hτpos : 0 < τ := by
    have := tip_param_low hS hc₁ hR h hh e₀ hD₀
    rw [hke₀, h2] at this
    show (0 : ℝ) < τ
    linarith
  have hτe : τ ≤ b := by rw [← hke₀]; exact hle₀
  -- injectivity of `h` on `E`
  have hinj : ∀ a b : E, h a = h b → a = b := fun a b hab =>
    Subtype.ext (h.injective hab)
  have himg : ∀ {P : Set M}, Fold.Q78.IsContinuum P → Fold.Q78.IsContinuum (h '' P) :=
    fun hP => ⟨hP.1.image h.continuous, hP.2.image _ h.continuous.continuousOn⟩
  -- the pieces
  set Kset : Set M := G ∩ h '' layerSet k (Icc 0 b) with hKset
  set Pset : Set M := h '' layerSet k (Icc 0 τ) with hPset
  set Λ : Set M := layer d 1 ∩ h '' E with hΛ
  set tip : Set M := h '' layer k τ with htip
  set A1 : Set M := Kset \ (Λ ∪ tip) with hA1
  set A2 : Set M := h '' layerSet k (Ico 0 τ) with hA2
  set A3 : Set M := layer d 1 \ h '' E with hA3
  have hL1G : layer d 1 ⊆ G := by rintro _ ⟨g, -, rfl⟩; exact g.2
  have hL1c : Fold.Q78.IsContinuum (layer d 1) := isContinuum_layer hG.isCompact hG.2.1 1
  have hPc : Fold.Q78.IsContinuum Pset :=
    himg (isContinuum_img hE.isCompact hE.2.1 isClosed_Icc isPreconnected_Icc
      ⟨0, le_rfl, unitInterval.nonneg'⟩)
  have hKe : Fold.Q78.IsContinuum (h '' layerSet k (Icc 0 b)) :=
    himg (isContinuum_img hE.isCompact hE.2.1 isClosed_Icc isPreconnected_Icc
      ⟨0, le_rfl, unitInterval.nonneg'⟩)
  have hmem0 : h e₀ ∈ Kset := ⟨hG₀, e₀, ⟨e₀, ⟨unitInterval.nonneg', hle₀⟩, rfl⟩, rfl⟩
  have hmem0P : h e₀ ∈ Pset := ⟨e₀, ⟨e₀, ⟨unitInterval.nonneg', hke₀.le⟩, rfl⟩, rfl⟩
  have hKc : Fold.Q78.IsContinuum Kset :=
    isContinuum_inter_of_HU hHU (isContinuum_of_minimalAdmissible hG) hKe ⟨_, hmem0⟩
  have hmem' : h e' ∈ layer d 1 ∩ Pset := ⟨he'1, e', ⟨e', ⟨unitInterval.nonneg', hke'.le⟩, rfl⟩, rfl⟩
  have hTc : Fold.Q78.IsContinuum ((layer d 1 ∪ Pset) ∪ Kset) :=
    isContinuum_union (isContinuum_union hL1c hPc ⟨_, hmem'⟩) hKc
      ⟨_, Or.inr hmem0P, hmem0⟩
  -- membership facts
  have hKsub : Kset ⊆ h '' E := by
    rintro _ ⟨-, _, ⟨e'', -, rfl⟩, rfl⟩; exact ⟨e'', e''.2, rfl⟩
  have hPsub : Pset ⊆ h '' E := by
    rintro _ ⟨_, ⟨e'', -, rfl⟩, rfl⟩; exact ⟨e'', e''.2, rfl⟩
  have hA2G : Disjoint A2 G := by
    rw [disjoint_left]
    rintro _ ⟨_, ⟨e'', he'', rfl⟩, rfl⟩ hG''
    have hle : k e'' ≤ b := (le_of_lt he''.2).trans hτe
    exact absurd (hτmin e'' hle hG'') (not_le.2 he''.2)
  have hA1P : Disjoint A1 Pset := by
    rw [disjoint_left]
    rintro z ⟨⟨hzG, -⟩, hzZ⟩ ⟨_, ⟨e'', he'', rfl⟩, rfl⟩
    have hge := hτmin e'' (he''.2.trans hτe) hzG
    exact hzZ (Or.inr ⟨e'', ⟨e'', le_antisymm he''.2 hge, rfl⟩, rfl⟩)
  have hKcl : IsClosed Kset := hKc.1.isClosed
  have hPcl : IsClosed Pset := hPc.1.isClosed
  have hL1cl : IsClosed (layer d 1) := hL1c.1.isClosed
  have hclA1 : closure A1 ⊆ Kset := closure_minimal (fun z hz => hz.1) hKcl
  have hclA2 : closure A2 ⊆ Pset := closure_minimal
    (image_mono (layerSet_mono k Ico_subset_Icc_self)) hPcl
  have hclA3 : closure A3 ⊆ layer d 1 := closure_minimal (fun z hz => hz.1) hL1cl
  refine hAT ((layer d 1 ∪ Pset) ∪ Kset) (subset_univ _) ⟨hTc, Λ ∪ tip, hZc, ?_, A1, A2, A3,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z (⟨hz1, -⟩ | ⟨_, ⟨e'', he'', rfl⟩, rfl⟩)
    · exact Or.inl (Or.inl hz1)
    · exact Or.inl (Or.inr ⟨e'', ⟨e'', ⟨unitInterval.nonneg', le_of_eq he''⟩, rfl⟩, rfl⟩)
  · obtain ⟨e₁, hle₁, hG₁, h1₁, hne₁⟩ := h_i
    refine ⟨h e₁, ⟨hG₁, e₁, ⟨e₁, ⟨unitInterval.nonneg', hle₁⟩, rfl⟩, rfl⟩, ?_⟩
    rintro (⟨h1, -⟩ | ⟨_, ⟨e'', he'', rfl⟩, hh''⟩)
    · exact h1₁ h1
    · exact hne₁ (by rw [← hinj _ _ hh'']; exact he'')
  · obtain ⟨e'', he''⟩ := hE.2.1.2.1 0
    exact ⟨h e'', e'', ⟨e'', ⟨le_of_eq he''.symm, by rw [he'']; exact hτpos⟩, rfl⟩, rfl⟩
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
        rcases lt_or_eq_of_le he''.2 with hlt | heq
        · exact Or.inl (Or.inr ⟨e'', ⟨e'', ⟨he''.1, hlt⟩, rfl⟩, rfl⟩)
        · exact absurd (Or.inr ⟨e'', ⟨e'', heq, rfl⟩, rfl⟩) hzZ
      · exact Or.inl (Or.inl ⟨hzK, hzZ⟩)
    · rintro ((⟨hzK, hzZ⟩ | hz2) | ⟨hz1, hzE⟩)
      · exact ⟨Or.inr hzK, hzZ⟩
      · refine ⟨Or.inl (Or.inr (hclA2 (subset_closure hz2))), ?_⟩
        rintro (⟨hz1, -⟩ | ⟨_, ⟨e'', he'', rfl⟩, hh''⟩)
        · exact disjoint_left.1 hA2G hz2 (hL1G hz1)
        · obtain ⟨_, ⟨e₃, he₃, rfl⟩, h₃⟩ := hz2
          have := hinj _ _ (h₃.trans hh''.symm)
          subst this
          have h3 : k e₃ = τ := he''
          exact absurd h3 (ne_of_lt he₃.2)
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

/-- **2b, a point on its own tip layer** (commission 179 §2, 2b). Suppose `K⁻ = G ∩ h[k⁻¹[[0, τ]]]`
lies in the tip layer `h[k⁻¹(τ)]` (that is, `k(e) = τ` and no point of `G ∩ h[E]` has parameter
below `τ`), the tip point is over `D`, (iii) holds, and the third arm of the triod
`T := d⁻¹(1) ∪ h[k⁻¹[[0, τ]]] ∪ K⁺_δ` is nonempty: some `h(e₁) ∈ G − d⁻¹(1)` has
`τ < k(e₁) ≤ τ + δ`. Then `False`.

*Proof:* this is `tip_triod` with `b = τ + δ`: the least parameter of `G ∩ h[k⁻¹[[0, τ + δ]]]` is
still `τ`, and `h(e₁)` gives (i). The case where the third arm is empty for every `δ` is 2b's
hand-over to 2d (open). -/
theorem tip_triod_on_tip_layer (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 40 ≤ n)
    {c₁ : ℝ} (hc₁ : c₁ ≤ c) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') {G : Set M}
    {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0)
    (h : M ≃ₜ M) (hh : ∀ v, dist (h v) v < θ / 4) {τ : unitInterval}
    (hτ : ∃ e₀ : E, k e₀ = τ ∧ h e₀ ∈ G ∧ π (h e₀ : Pt) ∈ F '' D')
    (htip : ∀ e' : E, k e' ≤ τ → h e' ∈ G → k e' = τ) (b : unitInterval) (hτb : τ ≤ b)
    (h_arm : ∃ e₁ : E, τ < k e₁ ∧ k e₁ ≤ b ∧ h e₁ ∈ G ∧ h e₁ ∉ layer d 1)
    (h_iii : ¬ layer d 1 ⊆ h '' E) : False := by
  obtain ⟨e₀, hke₀, hG₀, hD₀⟩ := hτ
  obtain ⟨e₁, hlt₁, hle₁, hG₁, h1₁⟩ := h_arm
  refine tip_triod hX hi hE hγπ hF hS hn hc₁ hR hG hX0 h hh b
    ⟨e₀, hke₀, by rw [hke₀]; exact hτb, hG₀, hD₀⟩ (fun e' _ hG' => ?_)
    ⟨e₁, hle₁, hG₁, h1₁, ne_of_gt hlt₁⟩ h_iii
  by_contra hlt
  push_neg at hlt
  exact absurd (htip e' hlt.le hG') (ne_of_lt hlt)

/-- `Z = Λ₁ ∪ h[k⁻¹(τ)]` is a continuum as soon as `d⁻¹(1)` meets the layer `h[k⁻¹(τ)]`. -/
theorem tip_Z_continuum (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (h : M ≃ₜ M) {τ : unitInterval} {e' : E} (hke' : k e' = τ)
    (he'1 : h e' ∈ layer d 1) :
    Fold.Q78.IsContinuum (layer d 1 ∩ h '' E ∪ h '' layer k τ) := by
  have hHU := hereditarilyUnicoherent_of_homogeneous_indecomposable hX hi
  have himg : ∀ {P : Set M}, Fold.Q78.IsContinuum P → Fold.Q78.IsContinuum (h '' P) :=
    fun hP => ⟨hP.1.image h.continuous, hP.2.image _ h.continuous.continuousOn⟩
  have hmem : h e' ∈ layer d 1 ∩ h '' E := ⟨he'1, e', e'.2, rfl⟩
  have hmemτ : h e' ∈ h '' layer k τ := ⟨e', ⟨e', hke', rfl⟩, rfl⟩
  have hΛ := isContinuum_inter_of_HU hHU (isContinuum_layer hG.isCompact hG.2.1 1)
    (himg (isContinuum_of_minimalAdmissible hE)) ⟨_, hmem⟩
  exact isContinuum_union hΛ (himg (isContinuum_layer hE.isCompact hE.2.1 τ)) ⟨_, hmem, hmemτ⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- **The tip is low** (mirror of `tip_param_low`): a parameter of a point of `G ∩ h[E]` over `D`
is below `19/22 + 2/n` (S0). -/
theorem tip_param_high {E : Set M} {k : E → unitInterval} {π : Pt → Pt} {F : ℝ × ℝ → Pt}
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (e₀ : E) (hD : π (h e₀ : Pt) ∈ F '' D') :
    (k e₀ : ℝ) < 19 / 22 + 2 / (n : ℝ) := by
  have hc := hS.c_pos
  obtain ⟨w, hwD, hFw⟩ := hD
  have hwS := hR.sub hwD
  have hw : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-c) c :=
    ⟨⟨by linarith [hwS.1.1], by linarith [hwS.1.2]⟩, by linarith [hwS.2.1],
      by linarith [hwS.2.2]⟩
  have := hS.fine h hh e₀ w hw hFw.symm
  linarith [(abs_lt.1 this).2, hwS.1.2]

/-- **§2.1, mirror form** (`K⁺ ⊆ O`). With `K⁺ = G ∩ h[k⁻¹[[b, 1]]]` and `σ` its greatest parameter
(attained at a point over `D`), `d⁻¹(1)` meets the tip layer `h[k⁻¹(σ)]`. Same proof as
`tip_meets_end_layer`, with `Q_δ ⊆ G` giving a point of `K⁺` above `σ`. -/
theorem tip_meets_end_layer_mirror (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt}
    {γ : unitInterval → Pt} (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt}
    (hF : IsCollar γ F) {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 40 ≤ n)
    {c₁ : ℝ} (hc₁ : c₁ ≤ c) {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') {G : Set M}
    {d : G → unitInterval} (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0)
    (h : M ≃ₜ M) (hh : ∀ v, dist (h v) v < θ / 4) (b : unitInterval) {σ : unitInterval}
    (hσ : ∃ e₀ : E, k e₀ = σ ∧ b ≤ k e₀ ∧ h e₀ ∈ G ∧ π (h e₀ : Pt) ∈ F '' D')
    (hσmax : ∀ e' : E, b ≤ k e' → h e' ∈ G → k e' ≤ σ) :
    ∃ e' : E, k e' = σ ∧ h e' ∈ layer d 1 := by
  obtain ⟨e₀, hke₀, hle₀, hG₀, hD₀⟩ := hσ
  have hn' : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : 1 / (n : ℝ) ≤ 1 / 40 := one_div_le_one_div_of_le (by norm_num) hn'
  have h2 : 2 / (n : ℝ) = 2 * (1 / (n : ℝ)) := by ring
  have h4 : 4 / (n : ℝ) = 4 * (1 / (n : ℝ)) := by ring
  have hc := hS.c_pos
  have hσlow := tip_param_low hS hc₁ hR h hh e₀ hD₀
  have hσhigh := tip_param_high hS hc₁ hR h hh e₀ hD₀
  rw [hke₀] at hσlow hσhigh
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
  set δ := min δ₁ (3 / 22 - 4 / (n : ℝ)) / 2 with hδdef
  have hm0 : 0 < 3 / 22 - 4 / (n : ℝ) := by rw [h4]; linarith
  have hδ0 : 0 < δ := by have := lt_min hδ₁ hm0; linarith
  have hδ1 : δ < δ₁ := by have := min_le_left δ₁ (3 / 22 - 4 / (n : ℝ)); linarith
  have hδ2 : δ ≤ (3 / 22 - 4 / (n : ℝ)) / 2 := by
    have := min_le_right δ₁ (3 / 22 - 4 / (n : ℝ)); linarith
  have hσδ : 2 / (n : ℝ) < (σ : ℝ) - δ := by rw [h2] at hσlow ⊢; rw [h4] at hδ2; linarith
  have hσδ' : (σ : ℝ) + δ < 1 := by rw [h2] at hσhigh; rw [h4] at hδ2; linarith
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

/-- **2a, mirror form** (`K⁺ ⊆ O`; commission 179 §2, 2a: "State the mirror form for `K⁺ ⊆ O`").
With `K⁺ = G ∩ h[k⁻¹[[b, 1]]]`, `σ` its greatest parameter (attained over `D`), (i) a point of `K⁺`
off `d⁻¹(1)` and off `h[k⁻¹(σ)]`, and (iii) `d⁻¹(1) ⊄ h[E]`: the triod
`T := d⁻¹(1) ∪ K⁺ ∪ h[k⁻¹[[σ, 1]]]` over `Z := Λ₁ ∪ h[k⁻¹(σ)]`, with arms `K⁺ − Z`,
`h[k⁻¹((σ, 1])]` and `d⁻¹(1) − h[E]`, contradicts atriodicity. -/
theorem tip_triod_mirror (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 40 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') {G : Set M} {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hX0 : layer d 0 = layer k 0) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (b : unitInterval) {σ : unitInterval}
    (hσ : ∃ e₀ : E, k e₀ = σ ∧ b ≤ k e₀ ∧ h e₀ ∈ G ∧ π (h e₀ : Pt) ∈ F '' D')
    (hσmax : ∀ e' : E, b ≤ k e' → h e' ∈ G → k e' ≤ σ)
    (h_i : ∃ e₁ : E, b ≤ k e₁ ∧ h e₁ ∈ G ∧ h e₁ ∉ layer d 1 ∧ k e₁ ≠ σ)
    (h_iii : ¬ layer d 1 ⊆ h '' E) : False := by
  obtain ⟨e', hke', he'1⟩ := tip_meets_end_layer_mirror hX hi hE hγπ hF hS hn hc₁ hR hG hX0 h hh
    b hσ hσmax
  have hZc := tip_Z_continuum hX hi hE hG h hke' he'1
  obtain ⟨e₀, hke₀, hle₀, hG₀, hD₀⟩ := hσ
  have hAT := (hagopian75_lemma1 hX hi).1
  have hHU := hereditarilyUnicoherent_of_homogeneous_indecomposable hX hi
  have hn' : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : 1 / (n : ℝ) ≤ 1 / 40 := one_div_le_one_div_of_le (by norm_num) hn'
  have h2 : 2 / (n : ℝ) = 2 * (1 / (n : ℝ)) := by ring
  have hσ1 : σ < 1 := by
    have := tip_param_high hS hc₁ hR h hh e₀ hD₀
    rw [hke₀, h2] at this
    show (σ : ℝ) < 1
    linarith
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

/-- **2c, degenerate chunk** (commission 179 §2, 2c). For a `T12Data` package `D` (Hagopian's
`F = D.G`): let `y = h(e)` be over `D` with `k(e)` in the core `[3/22 + 2/n, 19/22 − 2/n]`, `h` a
`θ/4`-homeomorphism, and suppose `Λ₁ = d⁻¹(1) ∩ h[E]` lies in one translated layer `h[k⁻¹(t)]` of the
open core `(3/22 + 2/n, 19/22 − 2/n)`. Then (iii) holds: `d⁻¹(1) ⊄ h[E]`.

*Proof:* otherwise `d⁻¹(1) = Λ₁ ⊆ h[k⁻¹(t)]`, which lies in the closure of the strand of `y`
(`strand_crossing`), hence over `Cl D`. A point of `d⁻¹(1)` is not over the bottom edge (that is
`E`, `mem_E_of_axis`, and `E = d⁻¹[[0, s]]` with `s < 1`, `ext_layers`; `F ≠ E` by
`hagopian76_property4_base`), not over a side segment (S0: its parameter `t` is more than `2/n`
from `3/22` and `19/22`), and not over `I₂` (T7). So `d⁻¹(1) ⊆ O`, against 3a
(`T12Data.end_layer_not_subset`). -/
theorem degenerate_chunk_iii (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {π : Pt → Pt} {γ : unitInterval → Pt}
    (hπ : IsQuotientMap π) (hπS : ∀ p q, π p = π q ↔ layerSetoid k p q)
    (hγπ : ∀ t, ∀ x ∈ toPt (layer k t), π x = γ t) {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {n : ℕ} {θ c : ℝ} (hS : StrandConst E k π F n θ c) (hn : 15 ≤ n) {c₁ : ℝ} (hc₁ : c₁ ≤ c)
    {D' : Set (ℝ × ℝ)} (hR : IsCrossRegion M π F c₁ D') (hD'c : IsPreconnected D')
    {r₂ s₂ : ℝ} {I₂ : Set Pt}
    (hI : TArc ((3 / 22, r₂) : ℝ × ℝ) (19 / 22, s₂)
      (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁ ∩ F ⁻¹' I₂))
    (hIR : I₂ ⊆ F '' (Icc (3 / 22) (19 / 22) ×ˢ Ioc 0 c₁))
    (hFDf : frontier (F '' D') = I₂ ∪ F '' (Icc (3 / 22) (19 / 22) ×ˢ {0}) ∪
        F '' (({3 / 22} : Set ℝ) ×ˢ Icc 0 r₂) ∪ F '' (({19 / 22} : Set ℝ) ×ˢ Icc 0 s₂))
    (hI2M : Disjoint I₂ (π '' M)) {ε₃ : ℝ} (D : T12Data E k π F D' ε₃) (h : M ≃ₜ M)
    (hh : ∀ v, dist (h v) v < θ / 4) (e : E) (hy : h e ∈ crossSet univ π F D')
    (he1 : 3 / 22 + 2 / (n : ℝ) ≤ (k e : ℝ)) (he2 : (k e : ℝ) ≤ 19 / 22 - 2 / (n : ℝ))
    {t : unitInterval} (ht1 : 3 / 22 + 2 / (n : ℝ) < (t : ℝ))
    (ht2 : (t : ℝ) < 19 / 22 - 2 / (n : ℝ)) (hΛ : layer D.d 1 ∩ h '' E ⊆ h '' layer k t) :
    ¬ layer D.d 1 ⊆ h '' E := by
  intro hsub
  have hc1 : c₁ ≤ 1 := hc₁.trans hS.c_le
  have hc := hS.c_pos
  -- `F ≠ E`, and `E = d⁻¹[[0, s]]` with `s < 1`
  have hGE : D.G ≠ E := by
    intro hGE
    have hall : layerSet D.d (Icc 0 1) = E := by
      ext z
      constructor
      · rintro ⟨g, -, rfl⟩
        exact (Set.ext_iff.1 hGE (g : M)).1 g.2
      · intro hz
        have hz' : z ∈ D.G := by rw [hGE]; exact hz
        exact ⟨⟨z, hz'⟩, ⟨unitInterval.nonneg', unitInterval.le_one'⟩, rfl⟩
    have hsep := D.sep
    rw [show toPt D.G = toPt (layerSet D.d (Icc 0 1)) by rw [hall, hGE]] at hsep
    exact hagopian76_property4_base hπ hπS hγπ hF hc1 hR hD'c hall _ _ hsep
  obtain ⟨s, -, hs1, -, hsE, -, -⟩ := ext_layers hX hi hE D.hG D.hEG D.hX0 hGE
  -- the strand of `y`
  obtain ⟨-, yL, yR, -, -, hL, hR', -, -, hmid⟩ := strand_crossing hX hi hE hπ.continuous hπS hγπ
    hF hS hn hc₁ hR h hh e hy he1 he2
  set C := connectedComponentIn (crossSet univ π F D') (h e) with hC
  have hr₂ : r₂ ≤ c₁ := by
    obtain ⟨-, f, -, hfr, hf0, -⟩ := hI
    have : ((3 / 22 : ℝ), r₂) ∈ range f := ⟨0, hf0⟩
    rw [hfr] at this
    exact this.1.2.2
  have hs₂ : s₂ ≤ c₁ := by
    obtain ⟨-, f, -, hfr, -, hf1⟩ := hI
    have : ((19 / 22 : ℝ), s₂) ∈ range f := ⟨1, hf1⟩
    rw [hfr] at this
    exact this.1.2.2
  apply T12Data.end_layer_not_subset hX hi hE hπ hπS hγπ hF hc1 hR hI hIR hFDf D
  rintro _ ⟨z, hz1, rfl⟩
  obtain ⟨_, ⟨e', he't, rfl⟩, hze'⟩ := hΛ ⟨hz1, hsub hz1⟩
  have hke' : k e' = t := he't
  -- `z` is in the closure of the strand
  have hzC : z ∈ closure C := by
    rw [← hze']
    refine hmid ⟨(e' : M), ⟨e', ⟨?_, ?_⟩, rfl⟩, rfl⟩
    · show (k yL : ℝ) < k e'
      rw [hke']; linarith [(abs_lt.1 hL).2]
    · show (k e' : ℝ) < k yR
      rw [hke']; linarith [(abs_lt.1 hR').1]
  have hcl : π (z : Pt) ∈ closure (F '' D') :=
    closure_minimal (s := C) (t := {m : M | π (m : Pt) ∈ closure (F '' D')})
      (fun m hm => subset_closure (connectedComponentIn_subset (crossSet univ π F D') _ hm).2)
      (isClosed_closure.preimage (hπ.continuous.comp continuous_subtype_val)) hzC
  by_contra hzO
  have hfr : π (z : Pt) ∈ frontier (F '' D') := by
    rw [hR.isOpen.frontier_eq]; exact ⟨hcl, hzO⟩
  rw [hFDf] at hfr
  -- S0 at `z = h e'`
  have hfine : ∀ w : ℝ × ℝ, w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-c) c → π (z : Pt) = F w →
      |(t : ℝ) - w.1| < 2 / (n : ℝ) := by
    intro w hw hzw
    rw [← hze'] at hzw
    have := hS.fine h hh e' w hw hzw
    rwa [hke'] at this
  rcases hfr with ((hI2 | ⟨w, hw, hFw⟩) | ⟨w, hw, hFw⟩) | ⟨w, hw, hFw⟩
  · exact disjoint_left.1 hI2M hI2 ⟨z, z.2, rfl⟩
  · -- the bottom edge: `z ∈ E`, but `E` misses `d⁻¹(1)`
    obtain ⟨⟨hw1, hw2⟩, hw0⟩ := hw
    rw [mem_singleton_iff] at hw0
    have hzE : z ∈ E := mem_E_of_axis hE hπS hγπ hF (t := w.1)
      ⟨by linarith, by linarith⟩ (by rw [← hFw]; rw [← hw0])
    rw [← hsE] at hzE
    obtain ⟨g', hg', hgg'⟩ := hzE
    obtain ⟨g, hg, hgz⟩ := hz1
    have : g' = g := Subtype.ext (hgg'.trans hgz.symm)
    subst this
    have h1 : (1 : unitInterval) ≤ s := by rw [← show D.d g' = 1 from hg]; exact hg'.2
    exact absurd (lt_of_lt_of_le hs1 h1) (lt_irrefl _)
  · obtain ⟨hw1, hw2⟩ := hw
    rw [mem_singleton_iff] at hw1
    have := hfine w ⟨⟨by rw [hw1]; norm_num, by rw [hw1]; norm_num⟩, by linarith [hw2.1],
      by linarith [hw2.2]⟩ hFw.symm
    rw [hw1] at this
    linarith [(abs_lt.1 this).2]
  · obtain ⟨hw1, hw2⟩ := hw
    rw [mem_singleton_iff] at hw1
    have := hfine w ⟨⟨by rw [hw1]; norm_num, by rw [hw1]; norm_num⟩, by linarith [hw2.1],
      by linarith [hw2.2]⟩ hFw.symm
    rw [hw1] at this
    linarith [(abs_lt.1 this).1]

end Tip

end HPC.Hagopian
