import HPC.Hagopian.H75Thm1A

/-!
# Batch 155, item I: Theorem 1, paragraphs 9–11 (the invariance of an interior layer)

`E ⊆ M` has an admissible map `k` with layers of void interior; `0 < r < s < t < 1`;
`Z = k⁻¹[r, t]`, `Y = k⁻¹(s)`; `ε` is at most the distance from `Z` to the end layers; `h` is a
homeomorphism of `M` moving no point by `ε` or more, and `h[Y] ∩ Y ≠ ∅`.

* `homeo_image_subset_of_meets` (**the second inclusion of paragraph 9**, unargued by Hagopian:
  `hᵢk⁻¹[[r,t]] ⊂ E`). `h[Z]` misses the end layers (choice of `ε`) and meets `E`. If `h[Z] ⊄ E`,
  then `J = E ∩ h[Z]` is a continuum (hereditary unicoherence) with `k(J) = [d', e'] ⊆ (0, 1)`, and
  `N = k⁻¹[d', e']`, `X₁ = k⁻¹[0, d']`, `X₂ = k⁻¹[e', 1]`, `X₃ = h[Z] ∪ N` satisfy the hypotheses of
  `isTriod_of_core`: a triod, against atriodicity.
* `homeo_image_layer_subset` (**paragraph 10**). Suppose `h[Y] ⊄ Y`; `k(h[Y]) = [d, e]` with `d < e`,
  and every layer `k⁻¹(u)`, `d < u < e`, lies in `h[Y]` (`layer_subset_of_meets'`). Split
  `E ∖ Y ⊆ k⁻¹[0, r] ∪ k⁻¹[t, 1] ∪ k⁻¹[r, s) ∪ k⁻¹(s, t]`. The images of the first two are closed and
  miss `h[Y]`; the images of the last two are connected subsets of `E` (paragraph 9) missing
  `k⁻¹(d, e) ⊆ h[Y]`, so each lies in `k⁻¹[0, d]` or in `k⁻¹[e, 1]`. Hence a point `y` with
  `k(y) ∈ (d, e)` is not in the closure of `h[E ∖ Y]`: a neighbourhood of `y` meets `h[E]` only in
  `h[Y]`, and pulling it back by `h`, `Y` has nonvoid interior in `E`. (Hagopian's sets `R` and `T`
  are the components of `h[E] − h[Y]` containing the images of `k⁻¹[0, s)` and `k⁻¹(s, 1]`; his
  appeal to the minimal admissible decomposition of `h[E]` is replaced by the invariance of relative
  interiors under the homeomorphism `h`, so `hagopian75_lemma3_unique` is not needed here.)
* `hagopian75_layer_invariant_aux` (**paragraph 11**): the same argument for `h⁻¹`, which moves no
  point by `ε` and also satisfies `h⁻¹[Y] ∩ Y ≠ ∅`, gives `Y ⊆ h[Y]`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Thm1B

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] [CompactSpace M] in
/-- **Paragraph 9, the second inclusion.** -/
theorem homeo_image_subset_of_meets (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E : Set M} (hEc : Fold.Q78.IsContinuum E)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) {Z : Set M} (hZ : Fold.Q78.IsContinuum Z)
    (h : M ≃ₜ M) (hmeet : (E ∩ h '' Z).Nonempty)
    (hends : ∀ z ∈ Z, ∀ w : E, (k w = 0 ∨ k w = 1) → h z ≠ w) : h '' Z ⊆ E := by
  by_contra hnot
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc.1
  have hhZ := isContinuum_homeo_image h hZ
  have hJ := isContinuum_inter_of_HU hHU hEc hhZ hmeet
  set J' : Set E := Subtype.val ⁻¹' (E ∩ h '' Z)
  have hJ'c : IsCompact J' := (hJ.1.isClosed.preimage continuous_subtype_val).isCompact
  have hJ'ne : J'.Nonempty := by
    obtain ⟨z, hzE, hz⟩ := hmeet
    exact ⟨⟨z, hzE⟩, hzE, hz⟩
  obtain ⟨y₁, hy₁, hmin⟩ := hJ'c.exists_isMinOn hJ'ne hk.1.continuousOn
  obtain ⟨y₂, hy₂, hmax⟩ := hJ'c.exists_isMaxOn hJ'ne hk.1.continuousOn
  set d' := k y₁
  set e' := k y₂
  have hnotend : ∀ y ∈ J', k y ≠ 0 ∧ k y ≠ 1 := by
    intro y hy
    obtain ⟨-, z, hz, hzy⟩ := hy
    exact ⟨fun h0 => hends z hz y (Or.inl h0) hzy, fun h1 => hends z hz y (Or.inr h1) hzy⟩
  have hd'0 : 0 < d' := lt_of_le_of_ne (unitInterval.nonneg') (hnotend y₁ hy₁).1.symm
  have he'1 : e' < 1 := lt_of_le_of_ne (unitInterval.le_one') (hnotend y₂ hy₂).2
  have hde : d' ≤ e' := hmin hy₂
  set N := Subtype.val '' (k ⁻¹' Icc d' e')
  set X₁ := Subtype.val '' (k ⁻¹' Icc 0 d')
  set X₂ := Subtype.val '' (k ⁻¹' Icc e' 1)
  have hN : Fold.Q78.IsContinuum N :=
    isContinuum_img hEc.1 hk isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 hde)
  have h₁ : Fold.Q78.IsContinuum X₁ :=
    isContinuum_img hEc.1 hk isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 hd'0.le)
  have h₂ : Fold.Q78.IsContinuum X₂ :=
    isContinuum_img hEc.1 hk isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 he'1.le)
  have hJN : E ∩ h '' Z ⊆ N := by
    intro z hz
    exact ⟨⟨z, hz.1⟩, ⟨hmin hz, hmax hz⟩, rfl⟩
  have hy₁N : (y₁ : M) ∈ N := ⟨y₁, ⟨le_rfl, hde⟩, rfl⟩
  have h₃ : Fold.Q78.IsContinuum (h '' Z ∪ N) :=
    isContinuum_union hhZ hN ⟨y₁, hy₁.2, hy₁N⟩
  obtain ⟨p₀, hp₀⟩ := hk.2.1 0
  obtain ⟨p₁, hp₁⟩ := hk.2.1 1
  have hT := isTriod_of_core hN h₁ h₂ h₃
    ⟨y₁, ⟨y₁, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩, hy₁N⟩
    ⟨y₂, ⟨y₂, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩, ⟨y₂, ⟨hde, le_rfl⟩, rfl⟩⟩
    ⟨y₁, Or.inr hy₁N, hy₁N⟩
    (by
      rintro z ⟨hz1, hz2⟩
      obtain ⟨hzE, hk1⟩ := mem_img_iff.1 hz1
      obtain ⟨_, hk2⟩ := mem_img_iff.1 hz2
      exact mem_img_iff.2 ⟨hzE, hde.trans hk2.1, hk1.2.trans hde⟩)
    (by
      rintro z ⟨hz1, hz3 | hz3⟩
      · exact hJN ⟨img_subset _ hz1, hz3⟩
      · exact hz3)
    (by
      rintro z ⟨hz2, hz3 | hz3⟩
      · exact hJN ⟨img_subset _ hz2, hz3⟩
      · exact hz3)
    (fun hsub => by
      have := hsub ⟨p₀, show k p₀ ∈ Icc 0 d' by rw [hp₀]; exact ⟨le_rfl, hd'0.le⟩, rfl⟩
      obtain ⟨_, hk0⟩ := mem_img_iff.1 this
      have : d' ≤ k p₀ := hk0.1
      rw [hp₀] at this
      exact absurd this (not_le.2 hd'0))
    (fun hsub => by
      have := hsub ⟨p₁, show k p₁ ∈ Icc e' 1 by rw [hp₁]; exact ⟨he'1.le, le_rfl⟩, rfl⟩
      obtain ⟨_, hk1⟩ := mem_img_iff.1 this
      have : k p₁ ≤ e' := hk1.2
      rw [hp₁] at this
      exact absurd this (not_le.2 he'1))
    (fun hsub => hnot fun z hz => img_subset _ (hsub (Or.inl hz)))
  exact hAT _ (subset_univ _) hT

omit [ConnectedSpace M] [CompactSpace M] in
/-- **Paragraph 10**: `h[Y] ⊆ Y`. -/
theorem homeo_image_layer_subset (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    {r s t : unitInterval} (hrs : r < s) (hst : s < t) {ε : ℝ}
    (hε : ∀ u v : E, r ≤ k u → k u ≤ t → (k v = 0 ∨ k v = 1) → ε ≤ dist u v)
    (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε) (hY : (h '' layer k s ∩ layer k s).Nonempty) :
    h '' layer k s ⊆ layer k s := by
  obtain ⟨a, b, hab⟩ := hE
  have hEc := hab.1
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc.1
  set Y := layer k s with hYdef
  have hmemY : ∀ w : E, (w : M) ∈ Y ↔ k w = s := fun w => val_mem_img
  set Z := Subtype.val '' (k ⁻¹' Icc r t)
  have hZ : Fold.Q78.IsContinuum Z :=
    isContinuum_img hEc.1 hk isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 (hrs.trans hst).le)
  have hYZ : Y ⊆ Z := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, show k w ∈ Icc r t from (mem_singleton_iff.1 hw) ▸ ⟨hrs.le, hst.le⟩, rfl⟩
  have hends : ∀ z ∈ Z, ∀ w : E, (k w = 0 ∨ k w = 1) → h z ≠ w := by
    rintro _ ⟨u, hu, rfl⟩ w hw hzw
    have h1 := hε u w hu.1 hu.2 hw
    have h2 := hh u
    rw [Subtype.dist_eq, ← hzw] at h1
    linarith
  have hZE : h '' Z ⊆ E := by
    refine homeo_image_subset_of_meets hHU hAT hEc hk hZ h ?_ hends
    obtain ⟨_, ⟨y, hyY, rfl⟩, hy'⟩ := hY
    exact ⟨h y, img_subset _ hy', y, hYZ hyY, rfl⟩
  by_contra hnot
  have hYc : Fold.Q78.IsContinuum Y := isContinuum_layer hEc.1 hk s
  have hhY := isContinuum_homeo_image h hYc
  have hhYE : h '' Y ⊆ E := (image_mono hYZ).trans hZE
  set P : Set E := Subtype.val ⁻¹' (h '' Y)
  have hPc : IsCompact P := (hhY.1.isClosed.preimage continuous_subtype_val).isCompact
  obtain ⟨_, ⟨y₀, hy₀Y, rfl⟩, hy₀'⟩ := hY
  have hPne : P.Nonempty := ⟨⟨h y₀, hhYE ⟨y₀, hy₀Y, rfl⟩⟩, y₀, hy₀Y, rfl⟩
  obtain ⟨y₁, hy₁, hmin⟩ := hPc.exists_isMinOn hPne hk.1.continuousOn
  obtain ⟨y₂, hy₂, hmax⟩ := hPc.exists_isMaxOn hPne hk.1.continuousOn
  set d := k y₁
  set e := k y₂
  -- `d < e`
  set ys : E := ⟨h y₀, hhYE ⟨y₀, hy₀Y, rfl⟩⟩ with hys
  have hs_mem : ys ∈ P := ⟨y₀, hy₀Y, rfl⟩
  have hks : k ys = s := (hmemY ys).1 hy₀'
  have hde : d < e := by
    by_contra hle
    push_neg at hle
    apply hnot
    intro z hz
    have hzE := hhYE hz
    have hz' : (⟨z, hzE⟩ : E) ∈ P := hz
    have h1 : d ≤ k ⟨z, hzE⟩ := hmin hz'
    have h2 : k ⟨z, hzE⟩ ≤ e := hmax hz'
    have h3 : d ≤ k ys := hmin hs_mem
    have h4 : k ys ≤ e := hmax hs_mem
    rw [hks] at h3 h4
    rw [hmemY ⟨z, hzE⟩]
    exact le_antisymm (h2.trans (hle.trans h3)) (h4.trans (hle.trans h1))
  -- the layers strictly between `d` and `e` lie in `h[Y]`
  have hmid : ∀ u, d < u → u < e → layer k u ⊆ h '' Y := fun u hdu hue =>
    layer_subset_of_meets' hab hk hhYE hhY ⟨y₁, hy₁, y₁, rfl, rfl⟩ ⟨y₂, hy₂, y₂, rfl, rfl⟩ hdu hue
  obtain ⟨u, hdu, hue⟩ := exists_between hde
  obtain ⟨w₀, hw₀⟩ := hk.2.1 u
  have hw₀Y : (w₀ : M) ∈ h '' Y := hmid u hdu hue ⟨w₀, hw₀, rfl⟩
  have hmidY : Subtype.val '' (k ⁻¹' Ioo d e) ⊆ h '' Y := by
    rintro _ ⟨w, hw, rfl⟩
    exact hmid (k w) hw.1 hw.2 ⟨w, rfl, rfl⟩
  -- the pieces of `E ∖ Y`
  have hdisjY : ∀ {S : Set unitInterval}, s ∉ S →
      Disjoint (h '' (Subtype.val '' (k ⁻¹' S))) (h '' Y) := by
    intro S hsS
    rw [Set.disjoint_image_iff h.injective, Set.disjoint_iff]
    rintro _ ⟨⟨w, hw, rfl⟩, hwY⟩
    exact hsS ((hmemY w).1 hwY ▸ hw)
  have hw₀notin : ∀ {S : Set unitInterval}, s ∉ S → (w₀ : M) ∉ h '' (Subtype.val '' (k ⁻¹' S)) :=
    fun hsS hw => (hdisjY hsS).le_bot ⟨hw, hw₀Y⟩
  have key1 : ∀ {S : Set unitInterval}, IsClosed S → s ∉ S →
      (w₀ : M) ∉ closure (h '' (Subtype.val '' (k ⁻¹' S))) := by
    intro S hS hsS
    rw [((isCompact_img hEc.1 hk.1 hS).image h.continuous).isClosed.closure_eq]
    exact hw₀notin hsS
  have key2 : ∀ {S : Set unitInterval}, IsPreconnected S → S ⊆ Icc r t → s ∉ S →
      (w₀ : M) ∉ closure (h '' (Subtype.val '' (k ⁻¹' S))) := by
    intro S hS hSZ hsS
    set G := h '' (Subtype.val '' (k ⁻¹' S))
    have hGp : IsPreconnected G :=
      ((hk.isPreconnected_preimage hEc.1 hS).image _ continuous_subtype_val.continuousOn).image _
        h.continuous.continuousOn
    have hGE : G ⊆ E := by
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact hZE ⟨w, ⟨w, hSZ hw, rfl⟩, rfl⟩
    have hL : IsClosed (Subtype.val '' (k ⁻¹' Iic d)) := (isCompact_img hEc.1 hk.1 isClosed_Iic).isClosed
    have hR : IsClosed (Subtype.val '' (k ⁻¹' Ici e)) := (isCompact_img hEc.1 hk.1 isClosed_Ici).isClosed
    have hsub : G ⊆ Subtype.val '' (k ⁻¹' Iic d) ∪ Subtype.val '' (k ⁻¹' Ici e) := by
      intro z hz
      have hzE := hGE hz
      by_cases h1 : k ⟨z, hzE⟩ ≤ d
      · exact Or.inl ⟨⟨z, hzE⟩, h1, rfl⟩
      by_cases h2 : e ≤ k ⟨z, hzE⟩
      · exact Or.inr ⟨⟨z, hzE⟩, h2, rfl⟩
      push_neg at h1 h2
      exact absurd (hmidY ⟨⟨z, hzE⟩, ⟨h1, h2⟩, rfl⟩) (fun hY' => (hdisjY hsS).le_bot ⟨hz, hY'⟩)
    have hdis : G ∩ (Subtype.val '' (k ⁻¹' Iic d) ∩ Subtype.val '' (k ⁻¹' Ici e)) = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro _ h1 h2
      obtain ⟨hzE, hz1⟩ := mem_img_iff.1 h1
      obtain ⟨_, hz2⟩ := mem_img_iff.1 h2
      exact absurd (le_trans (show e ≤ k ⟨z, hzE⟩ from hz2) hz1) (not_le.2 hde)
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hGp _ _ hL hR hsub hdis with hG | hG
    · intro hw
      have := (closure_minimal hG hL) hw
      have : k w₀ ≤ d := val_mem_img.1 this
      exact absurd (hw₀ ▸ this) (not_le.2 hdu)
    · intro hw
      have := (closure_minimal hG hR) hw
      have : e ≤ k w₀ := val_mem_img.1 this
      exact absurd (hw₀ ▸ this) (not_le.2 hue)
  have hcov : E \ Y ⊆ Subtype.val '' (k ⁻¹' Icc 0 r) ∪ Subtype.val '' (k ⁻¹' Icc t 1) ∪
      Subtype.val '' (k ⁻¹' Ico r s) ∪ Subtype.val '' (k ⁻¹' Ioc s t) := by
    rintro z ⟨hzE, hzY⟩
    have hne : k ⟨z, hzE⟩ ≠ s := fun h' => hzY ((hmemY ⟨z, hzE⟩).2 h')
    by_cases h1 : k ⟨z, hzE⟩ ≤ r
    · exact Or.inl (Or.inl (Or.inl ⟨⟨z, hzE⟩, ⟨unitInterval.nonneg', h1⟩, rfl⟩))
    by_cases h2 : t ≤ k ⟨z, hzE⟩
    · exact Or.inl (Or.inl (Or.inr ⟨⟨z, hzE⟩, ⟨h2, unitInterval.le_one'⟩, rfl⟩))
    push_neg at h1 h2
    rcases lt_or_gt_of_ne hne with h3 | h3
    · exact Or.inl (Or.inr ⟨⟨z, hzE⟩, ⟨h1.le, h3⟩, rfl⟩)
    · exact Or.inr ⟨⟨z, hzE⟩, ⟨h3, h2.le⟩, rfl⟩
  have hnotcl : (w₀ : M) ∉ closure (h '' (E \ Y)) := by
    intro hw
    have := closure_mono (image_mono hcov) hw
    simp only [image_union, closure_union, mem_union] at this
    rcases this with ((h1 | h1) | h1) | h1
    · exact key1 isClosed_Icc (fun h' => absurd h'.2 (not_le.2 hrs)) h1
    · exact key1 isClosed_Icc (fun h' => absurd h'.1 (not_le.2 hst)) h1
    · exact key2 isPreconnected_Ico (fun x hx => ⟨hx.1, hx.2.le.trans hst.le⟩)
        (fun h' => lt_irrefl _ h'.2) h1
    · exact key2 isPreconnected_Ioc (fun x hx => ⟨hrs.le.trans hx.1.le, hx.2⟩)
        (fun h' => lt_irrefl _ h'.1) h1
  -- `Y` has nonvoid interior in `E`
  obtain ⟨v₀, hv₀Y, hv₀⟩ := hw₀Y
  set U : Set E := Subtype.val ⁻¹' (h ⁻¹' (closure (h '' (E \ Y)))ᶜ)
  have hUo : IsOpen U :=
    (isClosed_closure.isOpen_compl.preimage h.continuous).preimage continuous_subtype_val
  have hv₀E : v₀ ∈ E := img_subset _ hv₀Y
  have hU0 : (⟨v₀, hv₀E⟩ : E) ∈ U := by
    show h v₀ ∈ (closure (h '' (E \ Y)))ᶜ
    rw [hv₀]; exact hnotcl
  have hUs : U ⊆ k ⁻¹' {s} := by
    intro w hw
    by_contra hws
    have hwY : (w : M) ∉ Y := fun h' => hws ((hmemY w).1 h')
    exact hw (subset_closure ⟨w, ⟨w.2, hwY⟩, rfl⟩)
  have := interior_maximal hUs hUo hU0
  rw [hk0 s] at this
  exact this

omit [ConnectedSpace M] [CompactSpace M] in
/-- **Paragraphs 9–11.** -/
theorem hagopian75_layer_invariant_aux (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    {r s t : unitInterval} (hrs : r < s) (hst : s < t) {ε : ℝ}
    (hε : ∀ u v : E, r ≤ k u → k u ≤ t → (k v = 0 ∨ k v = 1) → ε ≤ dist u v)
    (h : M ≃ₜ M) (hh : ∀ v, dist v (h v) < ε) (hY : (h '' layer k s ∩ layer k s).Nonempty) :
    h '' layer k s = layer k s := by
  refine Subset.antisymm (homeo_image_layer_subset hHU hAT hE hk hk0 hrs hst hε h hh hY) ?_
  have hh' : ∀ v, dist v (h.symm v) < ε := fun v => by
    have := hh (h.symm v)
    rwa [h.apply_symm_apply, dist_comm] at this
  have hY' : (h.symm '' layer k s ∩ layer k s).Nonempty := by
    obtain ⟨_, ⟨y, hy, rfl⟩, hy'⟩ := hY
    exact ⟨y, ⟨h y, hy', h.symm_apply_apply y⟩, hy⟩
  have := homeo_image_layer_subset hHU hAT hE hk hk0 hrs hst hε h.symm hh' hY'
  intro z hz
  exact ⟨h.symm z, this ⟨z, hz, rfl⟩, h.apply_symm_apply z⟩

end Thm1B

end HPC.Hagopian
