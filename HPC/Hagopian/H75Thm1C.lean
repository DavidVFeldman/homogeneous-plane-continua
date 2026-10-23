import HPC.Hagopian.H75Thm1B
import HPC.Hagopian.H75Jones

/-!
# Batch 155, items I (second part) and K: interior layers are homogeneous; Theorem 1 with
paragraph 4 as a hypothesis

* `layer_homogeneous_aux` (**paragraphs 5–8 and 12**). Fix `r < s < t` in `(0, 1)` and `ε` the
  distance from `k⁻¹[r, t]` to the end layers (positive: disjoint compact sets). By Effros there is
  `δ > 0` such that points closer than `δ` are exchanged by homeomorphisms of `M` moving no point by
  `ε`; by `hagopian75_layer_invariant_aux` each such homeomorphism carrying a point of `Y = k⁻¹(s)`
  into `Y` maps `Y` onto `Y`, and restricts to a homeomorphism of `Y`. "Some homeomorphism of `Y`
  takes `y` to `z`" is an equivalence relation that holds on a neighbourhood of each point, so it
  holds everywhere on the connected `Y` (`PreconnectedSpace.induction₂`) — Hagopian's finite chain
  `W₁, …, Wₙ` from `q` to `p` and the composition `h₁ ∘ ⋯ ∘ hₙ`.
* `theorem1_of_layer_aux` (**paragraph 13**). A nondegenerate interior layer `Y` is a homogeneous
  plane continuum, unicoherent by Lemma 1; by item J (`jones55_theorem2'`) it is indecomposable. The
  passage from `Y ⊆ M` to the plane set `Y ⊆ Pt` is a homeomorphism (`layerHomeo`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Thm1C

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- **Paragraphs 5–8 and 12.** -/
theorem layer_homogeneous_aux (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) {s : unitInterval}
    (hs0 : 0 < s) (hs1 : s < 1) : IsHomogeneous (layer k s) := by
  obtain ⟨a, b, hab⟩ := hE
  have hEc := hab.1
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc.1
  obtain ⟨r, hr0, hrs⟩ := exists_between hs0
  obtain ⟨t, hst, ht1⟩ := exists_between hs1
  -- `ε`
  set Zs : Set E := k ⁻¹' Icc r t
  set Es : Set E := k ⁻¹' {0, 1}
  have hZs : IsCompact Zs := (isClosed_Icc.preimage hk.1).isCompact
  have hEs : IsCompact Es :=
    ((((Set.finite_singleton (1 : unitInterval)).insert 0).isClosed).preimage hk.1).isCompact
  obtain ⟨u₀, hu₀⟩ := hk.2.1 r
  obtain ⟨v₀, hv₀⟩ := hk.2.1 0
  have hne : (Zs ×ˢ Es).Nonempty :=
    ⟨(u₀, v₀), show k u₀ ∈ Icc r t by rw [hu₀]; exact ⟨le_rfl, (hrs.trans hst).le⟩,
      show k v₀ ∈ ({0, 1} : Set unitInterval) by rw [hv₀]; exact Or.inl rfl⟩
  obtain ⟨p, hp, hpmin⟩ := (hZs.prod hEs).exists_isMinOn hne
    (continuous_dist.continuousOn (s := Zs ×ˢ Es))
  set ε := dist p.1 p.2
  have hε : 0 < ε := by
    refine dist_pos.2 fun heq => ?_
    have h1 : k p.1 ∈ Icc r t := hp.1
    have h2 : k p.2 ∈ ({0, 1} : Set unitInterval) := hp.2
    rw [heq] at h1
    rcases h2 with h2 | h2
    · rw [h2] at h1; exact absurd h1.1 (not_le.2 hr0)
    · rw [h2] at h1; exact absurd h1.2 (not_le.2 ht1)
  have hεle : ∀ u v : E, r ≤ k u → k u ≤ t → (k v = 0 ∨ k v = 1) → ε ≤ dist u v :=
    fun u v hu1 hu2 hv => hpmin (show (u, v) ∈ Zs ×ˢ Es from ⟨⟨hu1, hu2⟩, hv⟩)
  obtain ⟨δ, hδ, hhom⟩ := HPC.Effros.effros_homogeneous hX hε
  -- the layer is connected
  have hYc := isContinuum_layer hEc.1 hk s
  haveI : ConnectedSpace (layer k s) := isConnected_iff_connectedSpace.mp hYc.2
  refine PreconnectedSpace.induction₂ (fun y z => ∃ g : layer k s ≃ₜ layer k s, g y = z) ?_ ?_ ?_
  · intro x
    refine Filter.mem_of_superset (ball_mem_nhds x hδ) fun y hy => ?_
    rw [mem_ball, Subtype.dist_eq, dist_comm] at hy
    obtain ⟨h, hxy, hmove⟩ := hhom x y hy
    have hmove' : ∀ v, dist v (h v) < ε := fun v => by rw [dist_comm]; exact hmove v
    have hinv := hagopian75_layer_invariant_aux hHU hAT ⟨a, b, hab⟩ hk hk0 hrs hst hεle h hmove'
      ⟨y, ⟨x, x.2, hxy⟩, y.2⟩
    have hiff : ∀ z : M, z ∈ layer k s ↔ h z ∈ layer k s := fun z => by
      conv_rhs => rw [← hinv]
      exact (h.injective.mem_set_image).symm
    exact ⟨h.subtype hiff, Subtype.ext hxy⟩
  · rintro x y z ⟨g, hg⟩ ⟨g', hg'⟩
    exact ⟨g.trans g', by simp [hg, hg']⟩
  · rintro x y ⟨g, hg⟩
    exact ⟨g.symm, by rw [← hg, g.symm_apply_apply]⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- Preimages of continua under an inducing map onto their range. -/
theorem isContinuum_preimage_of_isInducing {N : Type*} [MetricSpace N] {θ : N → M}
    (hθ : IsInducing θ) {A : Set M} (hA : Fold.Q78.IsContinuum A) (hAr : A ⊆ range θ) :
    Fold.Q78.IsContinuum (θ ⁻¹' A) := by
  have himg : θ '' (θ ⁻¹' A) = A := image_preimage_eq_of_subset hAr
  refine ⟨?_, ?_, ?_⟩
  · rw [hθ.isCompact_iff, himg]; exact hA.1
  · obtain ⟨z, hz⟩ := hA.2.1
    obtain ⟨w, rfl⟩ := hAr hz
    exact ⟨w, hz⟩
  · rw [← hθ.isPreconnected_image, himg]; exact hA.2.2

omit [ConnectedSpace M] in
/-- **Paragraph 13.** A nondegenerate interior layer is a homogeneous indecomposable continuum. -/
theorem theorem1_of_layer_aux (hX : IsHomogeneous M)
    (hHU : IsHereditarilyUnicoherent (univ : Set M)) (hAT : IsAtriodic (univ : Set M))
    {E : Set M} (hE : ∃ a b, IsIrreducibleBetween E a b) {k : E → unitInterval}
    (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    (hnd : ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ (layer k s).Nontrivial) :
    ∃ Y ⊆ E, Fold.Q78.IsContinuum Y ∧ Y.Nontrivial ∧ IsHomogeneous Y ∧
      Fold.Q78.IsIndecomposable Y := by
  obtain ⟨s, hs0, hs1, hnt⟩ := hnd
  obtain ⟨a, b, hab⟩ := hE
  set Y := layer k s with hYdef
  have hYc : Fold.Q78.IsContinuum Y := isContinuum_layer hab.1.1 hk s
  have hYh : IsHomogeneous Y := layer_homogeneous_aux hX hHU hAT ⟨a, b, hab⟩ hk hk0 hs0 hs1
  refine ⟨Y, img_subset _, hYc, hnt, hYh, hYc, fun A B hA hB hAY hBY hAB => ?_⟩
  -- the plane copy `N` of `Y`
  haveI : CompactSpace Y := isCompact_iff_compactSpace.mp hYc.1
  haveI : ConnectedSpace Y := isConnected_iff_connectedSpace.mp hYc.2
  set f : Y → Pt := fun y => ((y : M) : Pt)
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  set N : Set Pt := range f
  set φ : Y ≃ₜ N := hf.toHomeomorph
  haveI : CompactSpace N := isCompact_iff_compactSpace.mp (isCompact_range hf.continuous)
  haveI : ConnectedSpace N :=
    isConnected_iff_connectedSpace.mp (isConnected_range hf.continuous)
  set θ : N → M := fun p => (φ.symm p : M)
  have hθ : IsInducing θ := IsInducing.subtypeVal.comp φ.symm.isInducing
  have hθi : Function.Injective θ := Subtype.val_injective.comp φ.symm.injective
  have hθr : range θ = Y := by
    rw [show θ = Subtype.val ∘ φ.symm from rfl, range_comp, φ.symm.surjective.range_eq,
      image_univ, Subtype.range_coe]
  have hNh : IsHomogeneous N := by
    intro p q
    obtain ⟨g, hg⟩ := hYh (φ.symm p) (φ.symm q)
    exact ⟨φ.symm.trans (g.trans φ), by simp [hg]⟩
  have hNu : IsUnicoherent (univ : Set N) := by
    intro H K hH hK hHK
    have hcont : ∀ {S : Set N}, Fold.Q78.IsContinuum S → Fold.Q78.IsContinuum (θ '' S) :=
      fun hS => ⟨hS.1.image hθ.continuous, hS.2.image _ hθ.continuous.continuousOn⟩
    have hU := hHU Y (subset_univ _) hYc hnt (θ '' H) (θ '' K) (hcont hH) (hcont hK)
      (by rw [← image_union, hHK, image_univ, hθr])
    rw [← image_inter hθi] at hU
    exact ⟨image_nonempty.1 hU.1, hθ.isPreconnected_image.1 hU.2⟩
  have hNi := indecomposable_of_unicoherent_homogeneous_aux hNh hNu
  by_contra hne
  push_neg at hne
  apply hNi
  refine ⟨θ ⁻¹' A, θ ⁻¹' B, isContinuum_preimage_of_isInducing hθ hA (hθr ▸ hAY),
    isContinuum_preimage_of_isInducing hθ hB (hθr ▸ hBY), ?_, ?_, ?_⟩
  · intro h
    apply hne.1
    rw [← image_preimage_eq_of_subset (hθr ▸ hAY : A ⊆ range θ), h, image_univ, hθr]
  · intro h
    apply hne.2
    rw [← image_preimage_eq_of_subset (hθr ▸ hBY : B ⊆ range θ), h, image_univ, hθr]
  · rw [← preimage_union, hAB, ← hθr, preimage_range]

end Thm1C

end HPC.Hagopian
